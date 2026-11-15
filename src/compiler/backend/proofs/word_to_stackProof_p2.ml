(* ========================================================================= *)
(* word_to_stackProof_p2: part 2 of 4 (HOL4 lines 3106-6314) of the port of *)
(* HOL4 compiler/backend/proofs/word_to_stackProofScript.sml (CakeML v3479). *)
(* Correctness proof for word_to_stack.                                      *)
(* The parts _p1 ... _p4 are loaded one after the other (each needs the     *)
(* previous one).  The notes on the rendering in word_to_stackProof_p1.ml   *)
(* apply here.  W2SP2AUX_ names are local helpers of this part.             *)
(* ========================================================================= *)

needs "compiler/backend/proofs/word_to_stackProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 3106-6314 ===== *)

(* W2SP2AUX: the clause of stack_evaluate_def for one constructor (an OCaml *)
(* helper for the tactics), e.g. w2sp2aux_seval "stack_Seq"                  *)
let w2sp2aux_seval c =
  let is_c th =
    try let l = lhs(snd(strip_forall(concl th))) in
        let p = fst(dest_pair(rand l)) in
        fst(dest_const(fst(strip_comb p))) = c
    with Failure _ -> false in
  match filter is_c (CONJUNCTS stack_evaluate_def) with
    [th] -> th
  | _ -> failwith ("w2sp2aux_seval: " ^ c);;

(* W2SP2AUX: stackSem Seq facts used below *)
let W2SP2AUX_evaluate_Seq_cong = prove
 (`!p1 p1' p2 (s:(A,C,FFI)stack_state).
     stack_evaluate (p1,s) = stack_evaluate (p1',s)
     ==> stack_evaluate (stack_Seq p1 p2,s) = stack_evaluate (stack_Seq p1' p2,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[]);;

let W2SP2AUX_evaluate_Seq_Skip = prove
 (`!p (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq p stack_Skip,s) = stack_evaluate (p,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN
  MP_TAC(ISPEC `stack_evaluate (p:(A)stack_prog,s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)stack_result)option` (X_CHOOSE_THEN
    `s1:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[w2sp2aux_seval "stack_Skip"]);;

let W2SP2AUX_evaluate_Seq_assoc = prove
 (`!p1 p2 p3 (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq (stack_Seq p1 p2) p3,s) =
     stack_evaluate (stack_Seq p1 (stack_Seq p2 p3),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN
  MP_TAC(ISPEC `stack_evaluate (p1:(A)stack_prog,s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)stack_result)option` (X_CHOOSE_THEN
    `s1:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: does a theorem mention the constant named c (an OCaml helper) *)
let w2sp2aux_has_const c th =
  can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false)) (concl th);;

(* W2SP2AUX: programs whose evaluation commutes with setting the clock     *)
let W2SP2AUX_clock_Seq = prove
 (`!p1 p2:(A)stack_prog.
     (!(t:(A,C,FFI)stack_state) clk.
        stack_evaluate (p1,stack_state_clock_fupd (K clk) t) =
        (FST (stack_evaluate (p1,t)),
         stack_state_clock_fupd (K clk) (SND (stack_evaluate (p1,t))))) /\
     (!(t:(A,C,FFI)stack_state) clk.
        stack_evaluate (p2,stack_state_clock_fupd (K clk) t) =
        (FST (stack_evaluate (p2,t)),
         stack_state_clock_fupd (K clk) (SND (stack_evaluate (p2,t)))))
     ==> !(t:(A,C,FFI)stack_state) clk.
           stack_evaluate (stack_Seq p1 p2,stack_state_clock_fupd (K clk) t) =
           (FST (stack_evaluate (stack_Seq p1 p2,t)),
            stack_state_clock_fupd (K clk) (SND (stack_evaluate (stack_Seq p1 p2,t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `stack_evaluate (p1:(A)stack_prog,t:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)stack_result)option` (X_CHOOSE_THEN
    `s1:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND]);;

(* W2SP2AUX: the same for the instructions of PushHandler and PopHandler    *)
let W2SP2AUX_clock_basic = prove
 (`!(t:(A,C,FFI)stack_state) clk n k l1 l2 c (r:num) name.
     (stack_evaluate (StackAlloc n,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (StackAlloc n:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (StackAlloc n,t))))) /\
     (stack_evaluate (StackFree n,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (StackFree n:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (StackFree n,t))))) /\
     (stack_evaluate (stack_Inst (asm_Const k c),stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (stack_Inst (asm_Const k c):(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (stack_Inst (asm_Const k c),t))))) /\
     (stack_evaluate (StackStore k n,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (StackStore k n:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (StackStore k n,t))))) /\
     (stack_evaluate (StackLoad k n,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (StackLoad k n:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (StackLoad k n,t))))) /\
     (stack_evaluate (stack_LocValue k l1 l2,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (stack_LocValue k l1 l2:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (stack_LocValue k l1 l2,t))))) /\
     (stack_evaluate (stack_Get k name,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (stack_Get k name:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (stack_Get k name,t))))) /\
     (stack_evaluate (stack_Set name k,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (stack_Set name k:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (stack_Set name k,t))))) /\
     (stack_evaluate (StackGetSize k,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (StackGetSize k:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (StackGetSize k,t))))) /\
     (stack_evaluate (stack_Skip,stack_state_clock_fupd (K clk) t) =
      (FST (stack_evaluate (stack_Skip:(A)stack_prog,t)),
       stack_state_clock_fupd (K clk) (SND (stack_evaluate (stack_Skip,t)))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[w2sp2aux_seval "StackAlloc"; w2sp2aux_seval "StackFree";
              w2sp2aux_seval "stack_Inst"; w2sp2aux_seval "StackStore";
              w2sp2aux_seval "StackLoad"; w2sp2aux_seval "stack_LocValue";
              w2sp2aux_seval "stack_Get"; w2sp2aux_seval "stack_Set";
              w2sp2aux_seval "StackGetSize"; w2sp2aux_seval "stack_Skip"] THEN
  SIMP[stack_inst_def; stack_assign_def; stack_word_exp_def; stack_get_var_def;
       stack_set_var_def; stack_set_store_def; stack_empty_env_def; FLOOKUP_UPDATE] THEN
  REPEAT CONJ_TAC THEN
  REPEAT(COND_CASES_TAC THEN SIMP[]) THEN
  REPEAT(CASE_TAC THEN SIMP[]));;
let W2SP2AUX_evaluate_Seq_cong2 = prove
 (`!p1 p2 p2' (s:(A,C,FFI)stack_state).
     (!s':(A,C,FFI)stack_state. stack_evaluate (p2,s') = stack_evaluate (p2',s'))
     ==> stack_evaluate (stack_Seq p1 p2,s) = stack_evaluate (stack_Seq p1 p2',s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[]);;

let W2SP2AUX_evaluate_Skip_Seq = prove
 (`!p (s:(A,C,FFI)stack_state).
     stack_evaluate (stack_Seq stack_Skip p,s) = stack_evaluate (p,s)`,
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Skip"] THEN
  CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the clause of wl_evaluate_def for one constructor (an OCaml   *)
(* helper for the tactics), e.g. w2sp2aux_weval "wl_Skip"                  *)
let w2sp2aux_weval c =
  let is_c th =
    try let l = lhs(snd(strip_forall(concl th))) in
        let p = fst(dest_pair(rand l)) in
        fst(dest_const(fst(strip_comb p))) = c
    with Failure _ -> false in
  match filter is_c (CONJUNCTS wl_evaluate_def) with
    [th] -> th
  | _ -> failwith ("w2sp2aux_weval: " ^ c);;

(* W2SP2AUX: substitute away every assumption var = t or t = var (an OCaml *)
(* helper for the tactics, like HOL4's rveq)                                *)
let w2sp2aux_rveq_tac =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o (fun th ->
    let l,r = dest_eq(concl th) in
    if is_var l && not (vfree_in l r) then th
    else if is_var r && not (vfree_in r l) then SYM th
    else failwith "w2sp2aux_rveq_tac")));;

(* HOL4 line 3106 *)
let IS_SOME_get_vars_set_var = prove
 (`!ls (s:(A,C,FFI)wl_state) k v.
     IS_SOME (wl_get_vars ls s) ==> IS_SOME (wl_get_vars ls (wl_set_var k v s))`,
  LIST_INDUCT_TAC THEN SIMP[wl_get_vars_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_get_var_def; wl_set_var_def] THEN
  SIMP[lookup_insert] THEN
  CASES_ON `lookup h (wl_state_locals (s:(A,C,FFI)wl_state))` THEN SIMP[] THEN
  CASES_ON `wl_get_vars t (s:(A,C,FFI)wl_state)` THEN SIMP[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:(A,C,FFI)wl_state`; `k:num`; `v:(A)word_loc`]) THEN
  ASM_REWRITE_TAC[IS_SOME_DEF; GSYM wl_set_var_def] THEN
  REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN SIMP[]);;

(* HOL4 line 3118 *)
let IS_SOME_get_vars_EVERY = prove
 (`!xs (s:(A,C,FFI)wl_state).
     IS_SOME (wl_get_vars xs s) <=> ALL (\x. IS_SOME (wl_get_var x s)) xs`,
  LIST_INDUCT_TAC THEN SIMP[wl_get_vars_def; ALL] THEN GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  CASES_ON `wl_get_var h (s:(A,C,FFI)wl_state)` THEN SIMP[] THEN
  CASES_ON `wl_get_vars t (s:(A,C,FFI)wl_state)` THEN SIMP[]);;

(* HOL4 line 3127: EQT_ELIM (SIMP_CONV (srw_ss()) [state_component_equality] *)
(* s with locals := s.locals = s) (a derived theorem)                    *)
let word_to_stackProof_with_same_locals = prove
 (`!(s:(A,B,C)wl_state). wl_state_locals_fupd (K (wl_state_locals s)) s = s`,
  SIMP[wl_state_component_equality]);;

let _ = cake_add_simps [word_to_stackProof_with_same_locals];;

(* W2SP2AUX: set_vars of a list with a last element *)
let W2SP2AUX_set_vars_snoc = prove
 (`!A B x y (s:(A,C,FFI)wl_state).
     LENGTH A = LENGTH B
     ==> wl_set_vars (APPEND A [x]) (APPEND B [y]) s = wl_set_vars A B (wl_set_var x y s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_set_vars_def; wl_set_var_def] THEN
  ASM_SIMP_TAC[alist_insert_append] THEN REWRITE_TAC[alist_insert_def] THEN SIMP[]);;

(* W2SP2AUX: the find_index condition of evaluate_wMoveAux_seqsem, for the tail *)
let W2SP2AUX_find_index_tail = prove
 (CASE_TERM `!q p (ms:(num option#num option)list) (r:num option->B option).
     (match find_index NONE (MAP SND (CONS (q,p) ms)) 0 with
        NONE -> T
      | SOME i ->
          (match find_index NONE (MAP FST (CONS (q,p) ms)) 0 with
             NONE -> IS_SOME (r NONE)
           | SOME j -> i <= j ==> IS_SOME (r NONE))) /\
     (q = NONE ==> IS_SOME (r p))
     ==> (match find_index NONE (MAP SND ms) 0 with
            NONE -> T
          | SOME i ->
              (match find_index NONE (MAP FST ms) 0 with
                 NONE -> IS_SOME (((q =+ r p) r) NONE)
               | SOME j -> i <= j ==> IS_SOME (((q =+ r p) r) NONE)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP; find_index_def] THEN
  ONCE_REWRITE_TAC[find_index_shift_0] THEN
  REWRITE_TAC[APPLY_UPDATE_THM] THEN
  ASM_CASES_TAC `q:num option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN REPEAT CASE_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `p:num option = NONE` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `find_index NONE (MAP SND (ms:(num option#num option)list)) 0` THEN
  CASES_ON `find_index NONE (MAP FST (ms:(num option#num option)list)) 0` THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[ARITH_RULE `0 <= n`; ADD_CLAUSES; LE_ADD_RCANCEL; LE_SUC] THEN MESON_TAC[]);;

(* HOL4 line 3130.  HOL4 (doubling section) o THE is (doubling lambda) o THE. *)
let evaluate_wMoveAux_seqsem = prove
 (CASE_TERM `!ms (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) r ac k f f' lens.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     (!i v. r (SOME i) = SOME v <=> wl_get_var (2 * i) s = SOME v) /\
     (!v. r NONE = SOME v ==> stack_get_var (k + 1) t = SOME v) /\
     IS_SOME (wl_get_vars (MAP ((\x. 2 * x) o THE) (FILTER IS_SOME (MAP SND ms))) s) /\
     (match find_index NONE (MAP SND ms) 0 with
        NONE -> T
      | SOME i ->
          (match find_index NONE (MAP FST ms) 0 with
             NONE -> IS_SOME (r NONE)
           | SOME j -> i <= j ==> IS_SOME (r NONE))) /\
     ALL (\(x,y). !a. x = SOME a \/ y = SOME a ==> a < f' + k) ms /\
     ALL_DISTINCT (FILTER IS_SOME (MAP FST ms))
     ==> ?t'.
           stack_evaluate (wMoveAux (MAP (format_var k ## format_var k) ms) (k,f,f'),t) =
             (NONE,t') /\
           word_to_stackProof_state_rel ac k f f'
             (wl_set_vars
                (MAP ((\x. 2 * x) o THE) (FILTER IS_SOME (MAP FST (REVERSE ms))))
                (MAP THE (MAP (seqsem ms r) (FILTER IS_SOME (MAP FST (REVERSE ms)))))
                s) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[MAP; wMoveAux_thm; REVERSE; FILTER; PAIR_EQ] THEN
    STRIP_TAC THEN EXISTS_TAC `t:(A,C,FFI)stack_state` THEN
    REWRITE_TAC[wl_set_vars_def; alist_insert_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`h:num option#num option`,`h:num option#num option`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num option`; `p:num option`; `s:(A,num#C,FFI)wl_state`;
    `t:(A,C,FFI)stack_state`; `r:num option->((A)word_loc)option`; `ac:(A)asm_config`;
    `k:num`; `f:num`; `f':num`; `lens:num list`] THEN
  REWRITE_TAC[MAP; PAIR_MAP_THM; wMoveAux_thm] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rS")
    (CONJUNCTS_THEN2 (LABEL_TAC "rN") (CONJUNCTS_THEN2 (LABEL_TAC "gv")
      (CONJUNCTS_THEN2 (LABEL_TAC "fi") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
         (LABEL_TAC "ad"))))))) THEN
  (* the value moved *)
  SUBGOAL_THEN (CASE_TERM `?v. r (p:num option) = SOME (v:(A)word_loc) /\
     (match p with NONE -> stack_get_var (k + 1) (t:(A,C,FFI)stack_state) = SOME v
                 | SOME x -> wl_get_var (x * 2) (s:(A,num#C,FFI)wl_state) = SOME v)`)
    STRIP_ASSUME_TAC THENL
   [USE_THEN "fi" MP_TAC THEN USE_THEN "gv" MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `p:num option` (cases "option")) THEN CASE_REWRITE_TAC[] THENL
     [DISCH_THEN(K ALL_TAC) THEN
      SUBGOAL_THEN `find_index NONE (CONS (NONE:num option)
                      (MAP SND (t:(num option#num option)list))) 0 = SOME 0`
        (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[find_index_def]; ALL_TAC] THEN
      CASE_REWRITE_TAC[] THEN
      CASES_ON `find_index NONE (CONS (q:num option)
                  (MAP FST (t:(num option#num option)list))) 0` THEN
      CASE_REWRITE_TAC[LE_0] THEN
      REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN
      EXISTS_TAC `x:(A)word_loc` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MAP; FILTER; IS_SOME_DEF; o_THM; THE_DEF; wl_get_vars_def] THEN
      CASES_ON `wl_get_var (2 * a) (s:(A,num#C,FFI)wl_state)` THEN
      CASE_REWRITE_TAC[IS_SOME_DEF] THEN DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      EXISTS_TAC `a':(A)word_loc` THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "rS" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
                 `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`;
                 `p:num option`; `v:(A)word_loc`; `q:num option`] wMoveSingle_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "bd" MP_TAC THEN REWRITE_TAC[ALL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    STRUCT_CASES_TAC(ISPEC `q:num option` (cases "option")) THEN
    CASE_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  (* the tail, with the environment after the first move *)
  MP_TAC(ISPECL [`q:num option`; `p:num option`; `t:(num option#num option)list`;
                 `r:num option->((A)word_loc)option`] W2SP2AUX_find_index_tail) THEN
  (ANTS_TAC THENL [REWRITE_TAC[MAP] THEN USE_THEN "fi" (fun th -> REWRITE_TAC[th]) THEN
                   ASM_SIMP_TAC[IS_SOME_DEF];
                   DISCH_TAC]) THEN
  (SUBGOAL_THEN `IS_SOME (wl_get_vars (MAP ((\x. 2 * x) o THE)
                  (FILTER IS_SOME (MAP SND (t:(num option#num option)list))))
                  (s:(A,num#C,FFI)wl_state))` ASSUME_TAC THENL
   [USE_THEN "gv" MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `p:num option` (cases "option")) THEN
    REWRITE_TAC[FILTER; IS_SOME_DEF; MAP; wl_get_vars_def] THEN
    REWRITE_TAC[] THEN REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[IS_SOME_DEF]);
    ALL_TAC]) THEN
  REWRITE_TAC[REVERSE; MAP_APPEND; FILTER_APPEND; MAP; FILTER; seqsem_def] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `q:num option` (concl th) && not (is_forall (concl th))))) THEN
  STRUCT_CASES_TAC(ISPEC `q:num option` (cases "option")) THEN
  CASE_REWRITE_TAC[IS_SOME_DEF; APPEND_NIL] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[MAP; APPEND_NIL] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`s:(A,num#C,FFI)wl_state`; `t1:(A,C,FFI)stack_state`;
      `((NONE:num option) =+ (r:num option->((A)word_loc)option) p) r`;
      `ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `lens:num list`] o
      check (fun th -> is_forall (concl th) && w2sp2aux_has_const "wMoveAux" th)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[APPLY_UPDATE_THM; option_DISTINCT] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "ALL")) THEN
        REWRITE_TAC[ALL] THEN SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "ALL_DISTINCT")) THEN
        REWRITE_TAC[FILTER; IS_SOME_DEF]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t2:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (SOME (a:num)) (MAP FST (t:(num option#num option)list))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "ALL_DISTINCT")) THEN
    REWRITE_TAC[FILTER; IS_SOME_DEF; ALL_DISTINCT; MEM_FILTER; IS_SOME_DEF] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[seqsem_move_unchanged; APPLY_UPDATE_THM; o_THM; THE_DEF] THEN
  ASM_SIMP_TAC[W2SP2AUX_set_vars_snoc; LENGTH_MAP] THEN
  SUBST_ALL_TAC(ARITH_RULE `a * 2 = 2 * a`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`wl_set_var (2 * a) (v:(A)word_loc) (s:(A,num#C,FFI)wl_state)`;
      `t1:(A,C,FFI)stack_state`;
      `(SOME (a:num) =+ SOME (v:(A)word_loc)) (r:num option->((A)word_loc)option)`;
      `ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `lens:num list`] o
      check (fun th -> is_forall (concl th) && w2sp2aux_has_const "wMoveAux" th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APPLY_UPDATE_THM; option_DISTINCT; option_INJ] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [X_GEN_TAC `i:num` THEN X_GEN_TAC `w:(A)word_loc` THEN
      REWRITE_TAC[wl_get_var_def; wl_set_var_def] THEN
      CONV_TAC(CAKE_SIMP_CONV[lookup_insert]) THEN
      REWRITE_TAC[ARITH_RULE `2 * a = 2 * i <=> a = i`] THEN
      ASM_CASES_TAC `a = (i:num)` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rS" (fun th -> REWRITE_TAC[th; wl_get_var_def]);
      MATCH_MP_TAC IS_SOME_get_vars_set_var THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(fun th -> if w2sp2aux_has_const "find_index" th &&
         not (can (find_term (fun x -> x = `CONS (p:num option)
               (MAP SND (t:(num option#num option)list))`)) (concl th))
         then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[APPLY_UPDATE_THM; option_DISTINCT];
      FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "ALL")) THEN
      REWRITE_TAC[ALL] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "ALL_DISTINCT")) THEN
      REWRITE_TAC[FILTER; IS_SOME_DEF; ALL_DISTINCT] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t2:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 3286: rebinds evaluate_SeqStackFree (HOL4 line 960, the same   *)
(* statement up to the names of the variables)                              *)
let evaluate_SeqStackFree = prove
 (`!(s:(A,C,FFI)stack_state) n p.
     stack_state_use_stack s /\ stack_state_stack_space s <= LENGTH (stack_state_stack s)
     ==> stack_evaluate (SeqStackFree n p,s) =
         stack_evaluate (stack_Seq (StackFree n) p,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SeqStackFree_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; GSYM NOT_LE] THEN SIMP[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ; stack_state_component_equality] THEN SIMP[]);;

(* HOL4 line 3295 *)
let word_to_stackProof_get_vars_eq = prove
 (`!ls z (st:(A,C,FFI)wl_state).
     wl_get_vars ls st = SOME z
     ==> let lookups = MAP (\x. lookup x (wl_state_locals st)) ls in
         ALL IS_SOME lookups /\ z = MAP THE lookups`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; wl_get_var_def] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN SIMP[MAP; ALL] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `lookup h (wl_state_locals (st:(A,C,FFI)wl_state))` THEN SIMP[] THEN
  CASES_ON `wl_get_vars t (st:(A,C,FFI)wl_state)` THEN SIMP[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a':((A)word_loc)list`; `st:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  SIMP[IS_SOME_DEF; THE_DEF]);;

(* HOL4 line 3307 *)
let LAST_add_ret_loc = prove
 (`!(args':((A)word_loc)list) (ret:(B#C#D#num#num)option).
     ~(args' = []) ==> LAST (add_ret_loc ret args') = LAST args'`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ret:(B#C#D#num#num)option` (cases "option")) THEN
  REWRITE_TAC[add_ret_loc_def] THEN
  TRY(POP_ASSUM_LIST(K ALL_TAC) THEN
      SPEC_TAC(`a:B#C#D#num#num`,`a:B#C#D#num#num`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; add_ret_loc_def] THEN REPEAT GEN_TAC) THEN
  REWRITE_TAC[LAST] THEN SIMP[]);;

(* W2SP2AUX: the conjuncts of state_rel needed for StackStore *)
let W2SP2AUX_state_rel_stack = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> stack_state_use_stack t /\
         stack_state_stack_space t + f <= LENGTH (stack_state_stack t) /\
         (if f' = 0 then f = 0 else f = f' + 1) /\ 4 < k`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* W2SP2AUX: a variable of the word state is below k + f' *)
let W2SP2AUX_state_rel_get_var_bound = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra m v.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     wl_get_var (2 * m) s = SOME v
     ==> m < k + f'`,
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_get_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`2 * m`; `v:(A)word_loc`]) THEN
  ASM_REWRITE_TAC[misc_TWOxDIV2] THEN ARITH_TAC);;

(* W2SP2AUX: HOL4 evaluate_wStackLoad_wReg2 (HOL4 line 4478), needed earlier *)
let W2SP2AUX_wStackLoad_wReg2 = prove
 (`!r k f f' x r' (s:(A,num#C,FFI)wl_state) c ac (t:(A,C,FFI)stack_state) lens.
     wReg2 r (k,f,f') = (x,r') /\
     EVEN r /\
     wl_get_var r s = SOME c /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (wStackLoad x stack_Skip,t) = (NONE,t') /\
           stack_state_clock t = stack_state_clock t' /\
           stack_state_bitmaps t = stack_state_bitmaps t' /\
           word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t /\
           (!r. ~(r = k + 1) ==> stack_get_var r t' = stack_get_var r t) /\
           (!r c. ~(r = k + 1)
                  ==> stack_word_exp t' (wl_Op asm_Add [wl_Var r; wl_Const c]) =
                      stack_word_exp t (wl_Op asm_Add [wl_Var r; wl_Const c])) /\
           stack_get_var r' t' = SOME c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> if is_eq (concl th) &&
     can (find_term (fun t -> t = `wReg2`)) (concl th) then MP_TAC th else ASSUME_TAC th)) THEN
  REWRITE_TAC[wReg2_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_get_var_bound o
    CONJ (ASSUME `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                    (t:(A,C,FFI)stack_state) lens 0`)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THENL
   [EXISTS_TAC `t:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[wStackLoad_def] THEN
    ONCE_REWRITE_TAC[stack_evaluate_def] THEN REWRITE_TAC[stack_get_var_def] THEN
    MATCH_MP_TAC state_rel_get_var_imp THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wStackLoad_def] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stack_state_stack_space (t:(A,C,FFI)stack_state) + (f + k) - (m + 1) <
                LENGTH (stack_state_stack t)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP[] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN SIMP[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`; `m:num`; `c:(A)word_loc`]
         state_rel_get_var_imp2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[stack_word_exp_def; MAP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE] THEN
  ASM_MESON_TAC[state_rel_set_var_k; stack_set_var_def]);;

(* W2SP2AUX: the last of the variables read by get_vars *)
let W2SP2AUX_get_vars_LAST = prove
 (`!args (s:(A,C,FFI)wl_state) args'.
     wl_get_vars args s = SOME args' /\ ~(args = [])
     ==> ~(args' = []) /\ wl_get_var (LAST args) s = SOME (LAST args')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP get_vars_length_lemma) THEN
  CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(args:num list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_MESON_TAC[LENGTH];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP word_to_stackProof_get_vars_eq) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAST_MAP; MAP_EQ_NIL; wl_get_var_def] THEN
  SUBGOAL_THEN `IS_SOME (lookup (LAST args) (wl_state_locals (s:(A,C,FFI)wl_state)))`
    MP_TAC THENL
   [UNDISCH_TAC `ALL IS_SOME (MAP (\x. lookup x (wl_state_locals (s:(A,C,FFI)wl_state)))
                   args)` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `LAST (args:num list)` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[MEM_LAST_NOT_NIL];
    REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF]]);;

(* W2SP2AUX: the code clause of state_rel *)
let W2SP2AUX_state_rel_code = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra n
     arg_count word_prog.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     lookup n (wl_state_code s) = SOME (arg_count,word_prog)
     ==> ?bs i bs2 i2 f0 stack_prog.
           word_to_stack_compile_prog ac F word_prog arg_count k (bs,i) =
             (stack_prog,f0,(bs2,i2)) /\
           LENGTH (append bs) <= i /\
           i - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
           isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) (stack_state_bitmaps t)) /\
           lookup n (stack_state_code t) = SOME stack_prog /\
           the f0 (lookup n (wl_state_stack_size s)) = f0`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_MESON_TAC[]);;
(* W2SP2AUX: the variables of related states are even *)
let W2SP2AUX_state_rel_EVEN = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra n v.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\ wl_get_var n s = SOME v
     ==> EVEN n`,
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_get_var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o
    check (w2sp2aux_has_const "EVEN")) THEN ASM_SIMP_TAC[]);;

(* HOL4 line 3315 *)
let call_dest_lemma = prove
 (`!dest args ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens q0 dest'
     args' (ret:(num list#cutsets#(A)wl_prog#num#num)option).
     ~bad_dest_args dest args /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     call_dest dest args (k,f,f') = (q0,dest') /\
     wl_get_vars args s = SOME args'
     ==> ?t4:(A,C,FFI)stack_state.
           stack_evaluate (q0,t) = (NONE,t4) /\
           word_to_stackProof_state_rel ac k f f' s t4 lens 0 /\
           LENGTH (stack_state_stack t4) = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t4 = stack_state_stack_space t /\
           !real_args prog ssize.
             wl_find_code dest (add_ret_loc ret args':((A)word_loc)list)
               (wl_state_code s) (wl_state_stack_size s) = SOME (real_args,prog,ssize)
             ==> ?bs i bs2 i2 fs stack_prog.
                   word_to_stack_compile_prog ac F prog (LENGTH real_args) k (bs,i) =
                     (stack_prog,fs,(bs2,i2)) /\
                   LENGTH (append bs) <= i /\
                   i - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
                   isPREFIX (append bs2)
                     (DROP (i - LENGTH (append bs)) (stack_state_bitmaps t)) /\
                   the fs ssize = fs /\
                   stack_find_code dest' (stack_state_regs t4) (stack_state_code t4) =
                     SOME stack_prog`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[bad_dest_args_def; call_dest_def] THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC `args:num list = []` THEN ASM_REWRITE_TAC[LENGTH] THEN
    SUBGOAL_THEN `~(LENGTH (args:num list) = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN w2sp2aux_rveq_tac THEN
    MP_TAC(ISPECL [`args:num list`; `s:(A,num#C,FFI)wl_state`; `args':((A)word_loc)list`]
             W2SP2AUX_get_vars_LAST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`LAST (args:num list)`; `k:num`; `f:num`; `f':num`; `x1:(num#num)list`;
                   `r:num`; `s:(A,num#C,FFI)wl_state`; `LAST (args':((A)word_loc)list)`;
                   `ac:(A)asm_config`; `t:(A,C,FFI)stack_state`; `lens:num list`]
           W2SP2AUX_wStackLoad_wReg2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC W2SP2AUX_state_rel_EVEN THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t1:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[wl_find_code_def] THEN
    SUBGOAL_THEN `~(add_ret_loc (ret:(num list#cutsets#(A)wl_prog#num#num)option)
                     (args':((A)word_loc)list) = [])` ASSUME_TAC THENL
     [STRUCT_CASES_TAC(ISPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option`
        (cases "option")) THEN
      ASM_REWRITE_TAC[add_ret_loc_def] THEN
      SPEC_TAC(`a:num list#cutsets#(A)wl_prog#num#num`,
               `a:num list#cutsets#(A)wl_prog#num#num`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; add_ret_loc_def; NOT_CONS_NIL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_add_ret_loc] THEN
    CASES_ON `LAST (args':((A)word_loc)list)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    CASES_ON `lookup a0 (wl_state_code (s:(A,num#C,FFI)wl_state))` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC(ISPEC `a:num#(A)wl_prog` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:(A)wl_prog` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN w2sp2aux_rveq_tac THEN
    MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
                   `s:(A,num#C,FFI)wl_state`; `t1:(A,C,FFI)stack_state`; `lens:num list`;
                   `0`; `a0:num`; `arity:num`; `prog:(A)wl_prog`] W2SP2AUX_state_rel_code) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`bs:(A word)app_list`; `i:num`; `bs2:(A word)app_list`;
                          `i2:num`; `f0:num`; `stack_prog:(A)stack_prog`] THEN
    ASM_SIMP_TAC[LENGTH_FRONT; ARITH_RULE `PRE (n + 1) = n`] THEN
    ASM_REWRITE_TAC[stack_find_code_def; GSYM stack_get_var_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  EXISTS_TAC `t:(A,C,FFI)stack_state` THEN
  ASM_REWRITE_TAC[w2sp2aux_seval "stack_Skip"] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_find_code_def] THEN
  CASES_ON `lookup a (wl_state_code (s:(A,num#C,FFI)wl_state))` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `a':num#(A)wl_prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `exp:(A)wl_prog` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
                 `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`;
                 `0`; `a:num`;
                 `LENGTH (add_ret_loc (ret:(num list#cutsets#(A)wl_prog#num#num)option)
                                      (args':((A)word_loc)list))`;
                 `prog:(A)wl_prog`] W2SP2AUX_state_rel_code) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`bs:(A word)app_list`; `i:num`; `bs2:(A word)app_list`;
                        `i2:num`; `f0:num`; `stack_prog:(A)stack_prog`] THEN
  ASM_REWRITE_TAC[stack_find_code_def]);;

(* HOL4 line 3423 *)
let compile_result_NOT_2 = prove
 (`!(x:(A)wl_result).
     good_dimindex (:A) ==> ~(compile_result x = stackSem_Halt (wl_Word (word 2:A word)))`,
  GEN_TAC THEN CASES_ON `x:(A)wl_result` THEN
  REWRITE_TAC[compile_result_def] THEN SIMP[good_dimindex_def] THEN
  REWRITE_TAC[dimword_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 3431 *)
let MAP_o_THE_FILTER_IS_SOME = prove
 (`!(f:A->B) ls.
     MAP (f o THE) (FILTER IS_SOME ls) = MAP (THE o OPTION_MAP f) (FILTER IS_SOME ls)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER; IS_SOME_EXISTS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM; OPTION_MAP_DEF; THE_DEF]);;

(* HOL4 line 3438 *)
let MAP_OPTION_MAP_FILTER_IS_SOME = prove
 (`!(f:A->A) ls.
     MAP (OPTION_MAP f) (FILTER IS_SOME ls) = FILTER IS_SOME (MAP (OPTION_MAP f) ls)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FILTER] THEN
  CASES_ON `h:A option` THEN ASM_REWRITE_TAC[IS_SOME_DEF; OPTION_MAP_DEF; MAP]);;

(* HOL4 line 3445 *)
let MAP_FILTER_IS_SOME = prove
 (`!(f:A option->B) ls.
     MAP f (FILTER IS_SOME ls) = MAP (f o SOME o THE) (FILTER IS_SOME ls)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER; IS_SOME_EXISTS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM; THE_DEF]);;

(* HOL4 line 3451 *)
let TIMES2_DIV2_lemma = prove
 (`!moves.
     windmill moves /\ ALL EVEN (MAP FST moves) /\ ALL EVEN (MAP SND moves)
     ==> MAP ((\x. 2 * x) o THE)
           (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves)))) =
         MAP THE (FILTER IS_SOME (MAP FST (parmove moves)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_o_THE_FILTER_IS_SOME] THEN
  REWRITE_TAC[MAP_o] THEN REWRITE_TAC[MAP_OPTION_MAP_FILTER_IS_SOME] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`moves:(num#num)list`; `DIV2`] parmove_MAP_INJ) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[MEM_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_MESON_TAC[EVEN_DIV2_INJ];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; PAIR_MAP_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num option`; `b:num option`] THEN DISCH_TAC THEN
  CASES_ON `a:num option` THEN REWRITE_TAC[OPTION_MAP_DEF; option_INJ; DIV2_def] THEN
  SUBGOAL_THEN `MEM (a':num) (MAP FST (moves:(num#num)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC MEM_MAP_FST_parmove THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    ASM_MESON_TAC[FST];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  SUBGOAL_THEN `EVEN a'` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN ARITH_TAC);;

(* HOL4 line 3484 *)
let PAIR_MAP_SOME_SWAP = prove
 (`!(f:A->B) (g:C->D).
     (SOME ## SOME) o (f ## g) = (OPTION_MAP f ## OPTION_MAP g) o (SOME ## SOME)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; PAIR_MAP_THM; OPTION_MAP_DEF]);;

(* HOL4 line 3490 *)
let IS_SOME_o_OPTION_MAP = prove
 (`!(f:A->B). IS_SOME o OPTION_MAP f = IS_SOME`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[OPTION_MAP_DEF; IS_SOME_DEF]);;

(* HOL4 line 3496 *)
let parsem_parmove_DIV2_lemma = prove
 (`!moves (r:num option->B).
     windmill moves /\ ALL EVEN (MAP FST moves) /\ ALL EVEN (MAP SND moves)
     ==> MAP (parsem (MAP (SOME ## SOME) (MAP (DIV2 ## DIV2) moves)) r)
           (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves)))) =
         MAP (parsem (MAP (SOME ## SOME) moves) (r o OPTION_MAP DIV2))
           (FILTER IS_SOME (MAP FST (parmove moves)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`moves:(num#num)list`; `DIV2`] parmove_MAP_INJ) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[MEM_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_MESON_TAC[EVEN_DIV2_INJ];
    DISCH_THEN SUBST1_TAC] THEN
  (SUBGOAL_THEN `!l:(num option#num option)list.
     MAP FST (MAP (OPTION_MAP DIV2 ## OPTION_MAP DIV2) l) = MAP (OPTION_MAP DIV2) (MAP FST l)`
     (fun th -> REWRITE_TAC[th]) THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
    SPEC_TAC(`h:num option#num option`,`h:num option#num option`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MAP_OPTION_MAP_FILTER_IS_SOME] THEN
  REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[IS_SOME_DEF] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN REWRITE_TAC[o_THM]) THEN
  (REWRITE_TAC[PAIR_MAP_SOME_SWAP] THEN REWRITE_TAC[MAP_o] THEN
   MP_TAC(ISPECL [`OPTION_MAP DIV2`; `r:num option->B`;
                  `MAP (SOME ## SOME) (moves:(num#num)list)`] parsem_MAP_INJ) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[windmill_def; GSYM MAP_o] THEN
      SUBGOAL_THEN `FST o ((SOME ## SOME):num#num->num option#num option) = SOME o FST`
        SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; PAIR_MAP_THM]; ALL_TAC] THEN
      REWRITE_TAC[MAP_o] THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
      REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[windmill_def];
      ALL_TAC] THEN
    REWRITE_TAC[INJ; IN_UNIV; IN_SET_OF_LIST; MEM_APPEND; MEM_MAP; EXISTS_PAIR_THM;
                PAIR_MAP_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM]) THEN
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
    ASM_MESON_TAC[EVEN_DIV2_INJ];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `MEM (x:num) (MAP FST (moves:(num#num)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC MEM_MAP_FST_parmove THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `SOME (x:num)`) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM MAP_o] THEN
    SUBGOAL_THEN `FST o ((SOME ## SOME):num#num->num option#num option) = SOME o FST`
      SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; PAIR_MAP_THM]; ALL_TAC] THEN
    REWRITE_TAC[MAP_o] THEN MATCH_MP_TAC MEM_MAP_f THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[GSYM MAP_o; PAIR_MAP_SOME_SWAP]));;

(* W2SP2AUX: recognise an INJ assumption (an OCaml helper for the tactics) *)
let w2sp2aux_is_inj th =
  try fst(dest_const(fst(strip_comb(concl th)))) = "INJ" with Failure _ -> false;;

(* HOL4 line 3548 *)
let ALOOKUP_MAP_any = prove
 (`!(f:A#B->C#D) (k:A->C) (h:C->B->D) ls a x.
     INJ k (a INSERT set_of_list (MAP FST ls)) (:C) /\
     (!x y. MEM (x,y) ls ==> f (x,y) = (k x,h (k x) y)) /\ k a = x
     ==> ALOOKUP (MAP f ls) x = OPTION_MAP (h x) (ALOOKUP ls a)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_def; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h':A#B`,`h':A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `q:B`; `a:A`; `x:C`] THEN
  REWRITE_TAC[MEM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p:A`; `q:B`]) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALOOKUP_def] THEN
  SUBGOAL_THEN `(k:A->C) p = x <=> p = a` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[INJ; IN_INSERT; IN_SET_OF_LIST; MEM; IN_UNIV] o
                check w2sp2aux_is_inj) THEN
    DISCH_THEN(MP_TAC o SPECL [`p:A`; `a:A`]) THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check w2sp2aux_is_inj) THEN
  REWRITE_TAC[INJ; IN_INSERT; IN_SET_OF_LIST; MEM; IN_UNIV] THEN MESON_TAC[]);;

(* HOL4 line 3570 *)
let wf_alist_insert = prove
 (`!xs ys (z:A spt). wf z ==> wf (alist_insert xs ys z)`,
  MATCH_MP_TAC alist_insert_ind THEN REWRITE_TAC[alist_insert_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC wf_insert THEN ASM_SIMP_TAC[]);;

(* HOL4 line 3576 *)
let ALOOKUP_MAP_INJ_FST = prove
 (`!ls (f:A->B#C) x k.
     INJ (FST o f) (x INSERT set_of_list ls) (:B) /\ FST (f x) = k
     ==> ALOOKUP (MAP f ls) k = ALOOKUP (MAP (\x. (x,SND (f x))) ls) x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_def] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B#C`; `x:A`; `k:B`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(f:A->B#C) h` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:B` (X_CHOOSE_THEN `q:C` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[ALOOKUP_def] THEN
  SUBGOAL_THEN `p = (k:B) <=> h = (x:A)` SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[INJ; IN_INSERT; IN_SET_OF_LIST; MEM; o_THM;
                                       IN_UNIV] o check w2sp2aux_is_inj) THEN
    DISCH_THEN(MP_TAC o SPECL [`h:A`; `x:A`]) THEN
    ASM_REWRITE_TAC[FST] THEN ASM_MESON_TAC[FST];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check w2sp2aux_is_inj) THEN
  REWRITE_TAC[INJ; IN_INSERT; IN_SET_OF_LIST; MEM; o_THM; IN_UNIV] THEN MESON_TAC[]);;

(* HOL4 line 3605 *)
let ALOOKUP_ID_TABULATE = prove
 (`!ls (x:A). ALOOKUP (MAP (\x. (x,x)) ls) x = if MEM x ls then SOME x else NONE`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALOOKUP_def; MEM] THEN
  GEN_TAC THEN ASM_CASES_TAC `h = (x:A)` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: ALOOKUP in a zip of the keys THE y and the values g y *)
let W2SP2AUX_ALOOKUP_ZIP_THE = prove
 (`!(L:(num option)list) (g:num option->B) n.
     ALL IS_SOME L
     ==> ALOOKUP (ZIP (MAP THE L) (MAP g L)) n =
         if MEM (SOME n) L then SOME (g (SOME n)) else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ZIP; ALOOKUP_def; MEM; ALL] THEN
  STRUCT_CASES_TAC(ISPEC `h:num option` (cases "option")) THEN
  REWRITE_TAC[IS_SOME_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ALOOKUP_def; THE_DEF; option_INJ] THEN
  ASM_CASES_TAC `a = (n:num)` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: ALOOKUP in a zip of the keys and mapped values of an alist *)
let W2SP2AUX_ALOOKUP_ZIP_FST = prove
 (`!(moves:(A#B)list) (h:B->C) n.
     ALOOKUP (ZIP (MAP FST moves) (MAP h (MAP SND moves))) n =
     OPTION_MAP h (ALOOKUP moves n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ZIP; ALOOKUP_def; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALOOKUP_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

(* HOL4 line 3612 *)
let alist_insert_get_vars = prove
 (`!moves (s:(A,C,FFI)wl_state) x ls.
     ALL_DISTINCT (MAP FST moves) /\
     wl_get_vars (MAP SND moves) s = SOME x /\
     ALL_DISTINCT (FILTER IS_SOME ls) /\
     wf (wl_state_locals s) /\
     (!x. MEM (SOME x) ls ==> MEM x (MAP FST moves)) /\
     (!x y. MEM (x,y) moves /\ ~(x = y) ==> MEM (SOME x) ls)
     ==> alist_insert (MAP THE (FILTER IS_SOME ls))
           (MAP (\x. THE (wl_get_var (THE (ALOOKUP moves (THE x))) s)) (FILTER IS_SOME ls))
           (wl_state_locals s) =
         alist_insert (MAP FST moves) x (wl_state_locals s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP word_to_stackProof_get_vars_eq) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC(ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
  ASM_SIMP_TAC[wf_alist_insert] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `n:num` THEN
  ASM_SIMP_TAC[lookup_alist_insert; LENGTH_MAP] THEN
  SUBGOAL_THEN `ALL IS_SOME (FILTER IS_SOME (ls:(num option)list))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[W2SP2AUX_ALOOKUP_ZIP_THE; MEM_FILTER; IS_SOME_DEF] THEN
  ONCE_REWRITE_TAC[GSYM MAP_o] THEN REWRITE_TAC[W2SP2AUX_ALOOKUP_ZIP_FST; THE_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `ALOOKUP (moves:(num#num)list) n` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; o_THM; THE_DEF; wl_get_var_def] THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ALOOKUP_NONE]) THEN ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN DISCH_TAC THEN
    SUBGOAL_THEN `n = (a:num)` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IS_SOME (lookup a (wl_state_locals (s:(A,C,FFI)wl_state)))` MP_TAC THENL
     [UNDISCH_TAC `ALL IS_SOME (MAP (\x. lookup x (wl_state_locals (s:(A,C,FFI)wl_state)))
                     (MAP SND (moves:(num#num)list)))` THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `a:num` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `(a:num,a)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF]]]);;

(* HOL4 line 3703 *)
let wf_fromList2 = prove
 (`!(ls:A list). wf (fromList2 ls)`,
  SUBGOAL_THEN `!(ls:A list) j tr. wf tr
     ==> wf (SND (FOLDL (\(i,t) a. i + 2,insert i a t) (j,tr) ls))` MP_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC wf_insert THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[fromList2_def] THEN DISCH_TAC THEN GEN_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[wf_def]]);;

(* HOL4 line 3711 *)
let wStackLoad_append = prove
 (`!l1 l2. wStackLoad (APPEND l1 l2) = wStackLoad l1 o wStackLoad l2:(A)stack_prog->(A)stack_prog`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; FUN_EQ_THM; o_THM; wStackLoad_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[wStackLoad_def; o_THM]);;

(* HOL4 line 3722 *)
let wRegWrite1_thm1 = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens m kont v.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     m < f' + k /\
     (!n. n <= k ==> stack_evaluate (kont n,t) = (NONE,stack_set_var n v t))
     ==> ?t'.
           stack_evaluate (wRegWrite1 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var (2 * m) v s) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wRegWrite1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `stack_set_var m (v:(A)word_loc) (t:(A,C,FFI)stack_state)` THEN
    ASM_SIMP_TAC[LT_IMP_LE; word_to_stackProof_state_rel_set_var] THEN
    SIMP[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_SIMP_TAC[LE_REFL] THEN
  SIMP[] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  SIMP[stack_get_var_def; FLOOKUP_UPDATE] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
         stack_state_stack_space t + (f - 1) - (m - k))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP[LENGTH_LUPDATE]] THEN
  MATCH_MP_TAC state_rel_set_var2 THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 3745 *)
let wRegWrite1_thm1_weak = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens m kont v.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     m < f' + k /\
     (!n. n <= k ==> stack_evaluate (kont n,t) = (NONE,stack_set_var n v t))
     ==> ?t'.
           stack_evaluate (wRegWrite1 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var (2 * m) v s) t' lens 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP wRegWrite1_thm1) THEN MESON_TAC[]);;

(* HOL4 line 3758 *)
let wRegWrite1_thm2 = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens m kont v v'.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     m < f' + k /\
     (!n. n <= k
          ==> stack_evaluate (kont n,t) =
              (NONE,stack_set_var 0 v' (stack_set_var n v t)))
     ==> ?t'.
           stack_evaluate (wRegWrite1 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f'
             (wl_set_var 0 v' (wl_set_var (2 * m) v s)) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN
   `!(s1:(A,num#C,FFI)wl_state) (t1:(A,C,FFI)stack_state).
      word_to_stackProof_state_rel ac k f f' s1 t1 lens 0
      ==> word_to_stackProof_state_rel ac k f f' (wl_set_var 0 v' s1)
            (stack_set_var 0 v' t1) lens 0`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
                   `s1:(A,num#C,FFI)wl_state`; `t1:(A,C,FFI)stack_state`;
                   `lens:num list`; `0`; `0`; `v':(A)word_loc`]
           word_to_stackProof_state_rel_set_var) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[wRegWrite1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `stack_set_var 0 v' (stack_set_var m (v:(A)word_loc)
                                    (t:(A,C,FFI)stack_state))` THEN
    ASM_SIMP_TAC[LT_IMP_LE; word_to_stackProof_state_rel_set_var] THEN
    SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(0 = k)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_SIMP_TAC[LE_REFL] THEN
  SIMP[] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  SUBGOAL_THEN `FLOOKUP (stack_state_regs (stack_set_var 0 v'
     (stack_set_var k (v:(A)word_loc) (t:(A,C,FFI)stack_state)))) k = SOME v`
    ASSUME_TAC THENL
   [REWRITE_TAC[stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE]; ALL_TAC] THEN
  SIMP[stack_get_var_def] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
         stack_state_stack_space t + (f - 1) - (m - k))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP[LENGTH_LUPDATE]] THEN
  ONCE_REWRITE_TAC[GSYM(el 3 (CONJUNCTS stack_set_var_with_const))] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC state_rel_set_var2 THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 3814 *)
let wRegWrite2_thm1 = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens m kont v.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     m < f' + k /\
     (!n. n <= k + 1 ==> stack_evaluate (kont n,t) = (NONE,stack_set_var n v t))
     ==> ?t'.
           stack_evaluate (wRegWrite2 kont (2 * m) (k,f,f'),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var (2 * m) v s) t' lens 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wRegWrite2_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `stack_set_var m (v:(A)word_loc) (t:(A,C,FFI)stack_state)` THEN
    ASM_SIMP_TAC[ARITH_RULE `m < k ==> m <= k + 1`;
                 word_to_stackProof_state_rel_set_var];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_SIMP_TAC[LE_REFL] THEN
  SIMP[] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  SIMP[stack_get_var_def; FLOOKUP_UPDATE] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
         stack_state_stack_space t + (f - 1) - (m - k))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  MATCH_MP_TAC state_rel_set_var2 THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* W2SP2AUX: HOL4 state_rel_with_memory (HOL4 line 4387), needed earlier *)
let W2SP2AUX_state_rel_with_memory = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra m.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_memory_fupd (K m) s)
           (stack_state_memory_fupd (K m) t) lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 3836 *)
let word_to_stackProof_state_rel_mem_store = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra a b s'.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     wl_mem_store a b s = SOME s'
     ==> ?t'. stack_mem_store a b t = SOME t' /\
              word_to_stackProof_state_rel ac k f f' s' t' lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_mem_store_def; stack_mem_store_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `stack_state_mdomain (t:(A,C,FFI)stack_state) =
                  wl_state_mdomain (s:(A,num#C,FFI)wl_state) /\
                stack_state_memory t = wl_state_memory (s:(A,num#C,FFI)wl_state)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `word_to_stackProof_state_rel (ac:(A)asm_config) k f f'
                   (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  MATCH_MP_TAC W2SP2AUX_state_rel_with_memory THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4054 (Termination WF_REL_TAC measure (exp_size ARB o SND);      *)
(* here the size with the constant 0 for the words)                          *)
let map_var_def = cake_def_wf
  `measure (\(f:num->num,e:(A)wl_exp). wl_exp_size (\x:A. 0) e)`
  TERM_TAC
  `(map_var f (wl_Var num) = wl_Var (f num)) /\
   (map_var f (wl_Load exp) = wl_Load (map_var f exp)) /\
   (map_var f (wl_Op wop ls) = wl_Op wop (MAP (map_var f) ls)) /\
   (map_var f (wl_Shift sh e1 e2) = wl_Shift sh (map_var f e1) (map_var f e2)) /\
   (map_var f (wl_Const c) = wl_Const c) /\
   (map_var f (Lookup v) = Lookup v:(A)wl_exp)`;;

let map_var_ind = cake_ind "map_var";;

let _ = cake_add_simps [map_var_def];;

(* HOL4 line 4068 *)
let the_words_EVERY_IS_SOME_Word = prove
 (`!ls (x:(A word)list).
     the_words ls = SOME x ==> !a. MEM a ls ==> ?w. a = SOME (wl_Word w)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[the_words_def; MEM] THEN GEN_TAC THEN
  CASES_ON `h:((A)word_loc)option` THEN SIMP[] THEN
  CASES_ON `a:(A)word_loc` THEN SIMP[] THEN
  CASES_ON `the_words (t:(((A)word_loc)option)list)` THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4074 (the case without the other patterns: ARB there) *)
let the_words_SOME_eq = prove
 (CASE_TERM `!ls (x:(A word)list).
     the_words ls = SOME x ==> x = MAP (\x. match x with SOME (wl_Word y) -> y) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[the_words_def; MAP; option_INJ] THEN
  REWRITE_TAC[EQ_SYM_EQ] THEN
  CASES_ON `h:((A)word_loc)option` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `the_words (t:(((A)word_loc)option)list)` THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:(A word)list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[]);;

(* HOL4 line 4080 *)
let the_words_MAP_exists = prove
 (`!ls (x:(A word)list) a (f:B->((A)word_loc)option).
     the_words (MAP f ls) = SOME x /\ MEM a ls ==> ?w. f a = SOME (wl_Word w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP the_words_EVERY_IS_SOME_Word) THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MEM_MAP_f THEN ASM_REWRITE_TAC[]);;

(* HOL4 lines 4090-4386: word_exp_thm1, word_exp_thm2, ... are commented out *)
(* in HOL4.                                                                  *)

(* HOL4 line 4387 *)
let state_rel_with_memory = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra m.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_memory_fupd (K m) s)
           (stack_state_memory_fupd (K m) t) lens extra`,
  REWRITE_TAC[W2SP2AUX_state_rel_with_memory]);;

(* HOL4 line 4396 (wordSem's word_exp, as the HOL4 proof uses) *)
let word_exp_Op_SOME_Word = prove
 (`!(s:(A,C,FFI)wl_state) op wexps x.
     wl_word_exp s (wl_Op op wexps) = SOME x ==> ?w. x = wl_Word w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def] THEN
  CASES_ON `the_words (MAP (wl_word_exp (s:(A,C,FFI)wl_state)) wexps)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `word_op op (a:(A word)list)` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 4402 *)
let word_to_stackProof_state_rel_get_fp_var = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra n.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> wl_get_fp_var n s = stack_get_fp_var n t`,
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_get_fp_var_def;
              stack_get_fp_var_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4409 *)
let word_to_stackProof_state_rel_set_fp_var = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra n v.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_fp_var n v s)
           (stack_set_fp_var n v t) lens extra`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def; wl_set_fp_var_def;
              stack_set_fp_var_def] THEN
  SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4417 *)
let evaluate_wStackLoad_wReg1 = prove
 (`!r k f f' x r' (s:(A,num#C,FFI)wl_state) c ac (t:(A,C,FFI)stack_state) lens.
     wReg1 r (k,f,f') = (x,r') /\
     EVEN r /\
     wl_get_var r s = SOME c /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (wStackLoad x stack_Skip,t) = (NONE,t') /\
           stack_state_clock t = stack_state_clock t' /\
           word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t /\
           stack_state_bitmaps t' = stack_state_bitmaps t /\
           (!r. ~(r = k) ==> stack_get_var r t' = stack_get_var r t) /\
           ~(r' = k + 1) /\
           stack_get_var r' t' = SOME c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> if is_eq (concl th) &&
     can (find_term (fun t -> t = `wReg1`)) (concl th) then MP_TAC th else ASSUME_TAC th)) THEN
  REWRITE_TAC[wReg1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_get_var_bound o
    CONJ (ASSUME `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                    (t:(A,C,FFI)stack_state) lens 0`)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THENL
   [EXISTS_TAC `t:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[wStackLoad_def] THEN
    ONCE_REWRITE_TAC[stack_evaluate_def] THEN REWRITE_TAC[stack_get_var_def] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC state_rel_get_var_imp THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wStackLoad_def] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stack_state_stack_space (t:(A,C,FFI)stack_state) + (f + k) - (m + 1) <
                LENGTH (stack_state_stack t)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP[] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN SIMP[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`; `m:num`; `c:(A)word_loc`]
         state_rel_get_var_imp2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE] THEN
  REWRITE_TAC[ARITH_RULE `~(k = k + 1)`] THEN
  ASM_MESON_TAC[state_rel_set_var_k; stack_set_var_def]);;

(* HOL4 line 4447 *)
let evaluate_wStackLoad_wReg1_with_const = prove
 (`!r k f f' x r' (s:(A,num#C,FFI)wl_state) c w ac (t:(A,C,FFI)stack_state) lens.
     wReg1 r (k,f,f') = (x,r') /\
     EVEN r /\
     wl_word_exp s (wl_Op asm_Add [wl_Var r; wl_Const c]) = SOME (wl_Word w) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (wStackLoad x stack_Skip,t) = (NONE,t') /\
           stack_state_clock t = stack_state_clock t' /\
           word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t /\
           ~(r' = k + 1) /\
           stack_word_exp t' (wl_Op asm_Add [wl_Var r'; wl_Const c]) = SOME w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def; MAP; the_words_def] THEN
  CASES_ON `wl_get_var r (s:(A,num#C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  CASES_ON `word_op asm_Add [a':A word; c]` THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`r:num`; `k:num`; `f:num`; `f':num`; `x:(num#num)list`; `r':num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (a':A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`]
         evaluate_wStackLoad_wReg1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `t':(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_word_exp_def; MAP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 4470 *)
let evaluate_wStackLoad_clock = prove
 (`!x (t:(A,C,FFI)stack_state) clk.
     stack_evaluate (wStackLoad x stack_Skip,stack_state_clock_fupd (K clk) t) =
     (I ## (\s. stack_state_clock_fupd (K clk) s))
       (stack_evaluate (wStackLoad x stack_Skip,t))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wStackLoad_def] THENL
   [ONCE_REWRITE_TAC[stack_evaluate_def] THEN REWRITE_TAC[PAIR_MAP_THM; I_THM];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `i:num`; `t0:(A,C,FFI)stack_state`; `clk:num`] THEN
  REWRITE_TAC[wStackLoad_def] THEN
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [stack_evaluate_def] THEN
  SIMP[] THEN
  REPEAT(COND_CASES_TAC THEN SIMP[PAIR_MAP_THM; I_THM]));;

(* HOL4 line 4478 *)
let evaluate_wStackLoad_wReg2 = prove
 (`!r k f f' x r' (s:(A,num#C,FFI)wl_state) c ac (t:(A,C,FFI)stack_state) lens.
     wReg2 r (k,f,f') = (x,r') /\
     EVEN r /\
     wl_get_var r s = SOME c /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (wStackLoad x stack_Skip,t) = (NONE,t') /\
           stack_state_clock t = stack_state_clock t' /\
           stack_state_bitmaps t = stack_state_bitmaps t' /\
           word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t /\
           (!r. ~(r = k + 1) ==> stack_get_var r t' = stack_get_var r t) /\
           (!r c. ~(r = k + 1)
                  ==> stack_word_exp t' (wl_Op asm_Add [wl_Var r; wl_Const c]) =
                      stack_word_exp t (wl_Op asm_Add [wl_Var r; wl_Const c])) /\
           stack_get_var r' t' = SOME c`,
  MATCH_ACCEPT_TAC W2SP2AUX_wStackLoad_wReg2);;

(* HOL4 line 4512 *)
let evaluate_wStackLoad_seq = prove
 (`!ls prog (s:(A,C,FFI)stack_state).
     stack_evaluate (wStackLoad ls prog,s) =
     stack_evaluate (stack_Seq (wStackLoad ls stack_Skip) prog,s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wStackLoad_def] THENL
   [REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Skip"] THEN SIMP[];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `i:num`; `prog:(A)stack_prog`; `s:(A,C,FFI)stack_state`] THEN
  REWRITE_TAC[wStackLoad_def] THEN
  GEN_REWRITE_TAC (BINOP_CONV o TOP_DEPTH_CONV) [w2sp2aux_seval "stack_Seq"] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [w2sp2aux_seval "stack_Seq"] THEN
  MP_TAC(ISPEC `stack_evaluate (StackLoad r i:(A)stack_prog,s:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option` (X_CHOOSE_THEN
    `s1:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `stack_evaluate (wStackLoad t stack_Skip:(A)stack_prog,s1:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res2:((A)stack_result)option` (X_CHOOSE_THEN
    `s2:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 4527 *)
let evaluate_wStackStore_wReg1 = prove
 (`!r k f f' x r' ac (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens
     LENGTH_t_stack t_stack_space c.
     wReg1 r (k,f,f') = (x,r') /\
     EVEN r /\
     r < 2 * f' + 2 * k /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     LENGTH (stack_state_stack t) = LENGTH_t_stack /\
     stack_state_stack_space t = t_stack_space
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (wStackStore x stack_Skip,stack_set_var r' c t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var r c s) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH_t_stack /\
           stack_state_stack_space t' = t_stack_space`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    (rhs(concl th) = `t_stack_space:num`))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    (rhs(concl th) = `LENGTH_t_stack:num`))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> if is_eq (concl th) &&
     can (find_term (fun t -> t = `wReg1`)) (concl th) then MP_TAC th else ASSUME_TAC th)) THEN
  REWRITE_TAC[wReg1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THENL
   [ASM_SIMP_TAC[wStackStore_def; w2sp2aux_seval "stack_Skip"; PAIR_EQ; UNWIND_THM1;
                 word_to_stackProof_state_rel_set_var] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wStackStore_def; w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Skip"] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[w2sp2aux_seval "StackStore"] THEN SIMP[] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
                  stack_state_stack_space t + (f + k) - (m + 1))`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `stack_get_var k (stack_set_var k (c:(A)word_loc)
                  (t:(A,C,FFI)stack_state)) = SOME c` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN SIMP[LENGTH_LUPDATE] THEN
  MATCH_MP_TAC state_rel_set_var2 THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_ARITH_TAC);;

(* HOL4 line 4550 *)
let evaluate_wStackStore_wReg1_strong = prove
 (`!r k f f' x r' ac (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens c.
     wReg1 r (k,f,f') = (x,r') /\
     EVEN r /\
     r < 2 * f' + 2 * k /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (wStackStore x stack_Skip,stack_set_var r' c t) =
             (NONE,stack_set_var r' c t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var r c s)
             (stack_set_var r' c t') lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> if is_eq (concl th) &&
     can (find_term (fun t -> t = `wReg1`)) (concl th) then MP_TAC th else ASSUME_TAC th)) THEN
  REWRITE_TAC[wReg1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THENL
   [EXISTS_TAC `t:(A,C,FFI)stack_state` THEN
    ASM_SIMP_TAC[wStackStore_def; w2sp2aux_seval "stack_Skip";
                 word_to_stackProof_state_rel_set_var];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wStackStore_def; w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Skip"] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[w2sp2aux_seval "StackStore"] THEN SIMP[] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
                  stack_state_stack_space t + (f + k) - (m + 1))`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN
  SIMP[FLOOKUP_UPDATE] THEN
  EXISTS_TAC `stack_state_stack_fupd (K (LUPDATE (c:(A)word_loc)
     (stack_state_stack_space t + (f + k) - (m + 1)) (stack_state_stack t)))
     (t:(A,C,FFI)stack_state)` THEN
  SIMP[LENGTH_LUPDATE] THEN REWRITE_TAC[GSYM stack_set_var_def] THEN
  REWRITE_TAC[state_rel_set_var_k] THEN
  MATCH_MP_TAC state_rel_set_var2 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 4577 *)
let evaluate_wStackStore_wReg1_new = prove
 (`!r k f f' x r' kont (t:(A,C,FFI)stack_state) c ac (s:(A,num#C,FFI)wl_state) lens
     LENGTH_t_stack t_stack_space.
     wReg1 r (k,f,f') = (x,r') /\
     EVEN r /\
     r < 2 * f' + 2 * k /\
     (?t'. stack_evaluate (kont,t) = (NONE,stack_set_var r' c t') /\
           word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH_t_stack /\
           stack_state_stack_space t' = t_stack_space)
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (stack_Seq kont (wStackStore x stack_Skip),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var r c s) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH_t_stack /\
           stack_state_stack_space t' = t_stack_space`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t0:(A,C,FFI)stack_state`
       STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC evaluate_wStackStore_wReg1 THEN ASM_MESON_TAC[]);;

(* HOL4 line 4603 *)
let evaluate_wStackStore_wReg2_new = prove
 (`!r k f f' x r' kont (t:(A,C,FFI)stack_state) c ac (s:(A,num#C,FFI)wl_state) lens
     LENGTH_t_stack t_stack_space.
     wReg2 r (k,f,f') = (x,r') /\
     EVEN r /\
     r < 2 * f' + 2 * k /\
     (?t'. stack_evaluate (kont,t) = (NONE,stack_set_var r' c t') /\
           word_to_stackProof_state_rel ac k f f' s t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH_t_stack /\
           stack_state_stack_space t' = t_stack_space)
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (stack_Seq kont (wStackStore x stack_Skip),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var r c s) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH_t_stack /\
           stack_state_stack_space t' = t_stack_space`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t0:(A,C,FFI)stack_state`
       STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    (rhs(concl th) = `t_stack_space:num`))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    (rhs(concl th) = `LENGTH_t_stack:num`))) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EVEN_EXISTS] o
    check (fun th -> is_comb(concl th) && rator(concl th) = `EVEN`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[wReg2_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST_ALL_TAC o SYM)) THENL
   [ASM_SIMP_TAC[wStackStore_def; w2sp2aux_seval "stack_Skip"; PAIR_EQ; UNWIND_THM1;
                 word_to_stackProof_state_rel_set_var] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wStackStore_def; w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Skip"] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[w2sp2aux_seval "StackStore"] THEN SIMP[] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t0:(A,C,FFI)stack_state)) <=
                  stack_state_stack_space t0 + (f + k) - (m + 1))`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `stack_get_var (k + 1) (stack_set_var (k + 1) (c:(A)word_loc)
                  (t0:(A,C,FFI)stack_state)) = SOME c` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN SIMP[LENGTH_LUPDATE] THEN
  MATCH_MP_TAC state_rel_set_var2 THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_ARITH_TAC);;

(* HOL4 line 4629 *)
let evaluate_wStackStore_wReg1_0 = prove
 (`!r k f f' x r' ac (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens
     LENGTH_t_stack t_stack_space c1 c.
     wReg1 r (k,f,f') = (x,r') /\
     EVEN r /\
     r < 2 * f' + 2 * k /\
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     LENGTH (stack_state_stack t) = LENGTH_t_stack /\
     stack_state_stack_space t = t_stack_space
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (wStackStore x stack_Skip,
                           stack_set_var 0 c1 (stack_set_var r' c t)) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f'
             (wl_set_var 0 c1 (wl_set_var r c s)) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH_t_stack /\
           stack_state_stack_space t' = t_stack_space`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  ASM_CASES_TAC `r = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `r' = 0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `wReg1 0 (k,f,f') = (x:(num#num)list,r')` THEN
      REWRITE_TAC[wReg1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ARITH_RULE `0 DIV 2 = 0`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[set_var_cancel; set_var_cancel_word] THEN
    MATCH_MP_TAC evaluate_wStackStore_wReg1 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r' = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wReg1 r (k,f,f') = (x:(num#num)list,r')` THEN
    UNDISCH_TAC `EVEN r` THEN UNDISCH_TAC `~(r = 0)` THEN
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[wReg1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[misc_TWOxDIV2] THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[set_var_swap; set_var_swap_word] THEN
  MATCH_MP_TAC evaluate_wStackStore_wReg1 THEN ASM_REWRITE_TAC[] THEN
  SIMP[] THEN
  MATCH_MP_TAC state_rel_set_var' THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 4656 *)
let evaluate_wRegWrite1_seq = prove
 (CASE_TERM `!g r k f f' (t:(A,C,FFI)stack_state).
     stack_evaluate (wRegWrite1 g r (k,f,f'),t) =
     (let (l,n) = wReg1 r (k,f,f') in
      stack_evaluate (stack_Seq (g n) (wStackStore l stack_Skip),t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wRegWrite1_def; wReg1_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THEN
  CASE_REWRITE_TAC[wStackStore_def] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Skip"] THEN
  MP_TAC(ISPEC `stack_evaluate ((g:num->(A)stack_prog) (r DIV 2),t:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  MP_TAC(ISPEC `stack_evaluate ((g:num->(A)stack_prog) k,t:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 4672 *)
let evaluate_wRegWrite2_seq = prove
 (CASE_TERM `!g r k f f' (t:(A,C,FFI)stack_state).
     stack_evaluate (wRegWrite2 g r (k,f,f'),t) =
     (let (l,n) = wReg2 r (k,f,f') in
      stack_evaluate (stack_Seq (g n) (wStackStore l stack_Skip),t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wRegWrite2_def; wReg2_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THEN
  CASE_REWRITE_TAC[wStackStore_def] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Skip"] THEN
  MP_TAC(ISPEC `stack_evaluate ((g:num->(A)stack_prog) (r DIV 2),t:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  MP_TAC(ISPEC `stack_evaluate ((g:num->(A)stack_prog) (k + 1),t:(A,C,FFI)stack_state)`
           PAIR_SURJECTIVE) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* W2SP2AUX: loading a source variable with wReg1, then running P *)
let W2SP2AUX_one_load = prove
 (`!r k f f' l r' (s:(A,num#C,FFI)wl_state) c ac (t:(A,C,FFI)stack_state) lens.
     wReg1 r (k,f,f') = (l,r') /\ EVEN r /\ wl_get_var r s = SOME c /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t1:(A,C,FFI)stack_state.
           (!P. stack_evaluate (wStackLoad l P,t) = stack_evaluate (P,t1)) /\
           stack_state_clock t1 = stack_state_clock t /\
           word_to_stackProof_state_rel ac k f f' s t1 lens 0 /\
           LENGTH (stack_state_stack t1) = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t1 = stack_state_stack_space t /\
           stack_state_bitmaps t1 = stack_state_bitmaps t /\
           (!r. ~(r = k) ==> stack_get_var r t1 = stack_get_var r t) /\
           ~(r' = k + 1) /\ stack_get_var r' t1 = SOME c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP evaluate_wStackLoad_wReg1) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* W2SP2AUX: loading a second source variable with wReg2, then running P *)
let W2SP2AUX_one_load2 = prove
 (`!r k f f' l r' (s:(A,num#C,FFI)wl_state) c ac (t:(A,C,FFI)stack_state) lens.
     wReg2 r (k,f,f') = (l,r') /\ EVEN r /\ wl_get_var r s = SOME c /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t1:(A,C,FFI)stack_state.
           (!P. stack_evaluate (wStackLoad l P,t) = stack_evaluate (P,t1)) /\
           stack_state_clock t1 = stack_state_clock t /\
           word_to_stackProof_state_rel ac k f f' s t1 lens 0 /\
           LENGTH (stack_state_stack t1) = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t1 = stack_state_stack_space t /\
           stack_state_bitmaps t1 = stack_state_bitmaps t /\
           (!r. ~(r = k + 1) ==> stack_get_var r t1 = stack_get_var r t) /\
           (!r c. ~(r = k + 1)
                  ==> stack_word_exp t1 (wl_Op asm_Add [wl_Var r; wl_Const c]) =
                      stack_word_exp t (wl_Op asm_Add [wl_Var r; wl_Const c])) /\
           stack_get_var r' t1 = SOME c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP evaluate_wStackLoad_wReg2) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the statement of evaluate_wInst for one instruction pattern  *)
(* (an OCaml helper: the case lemmas below are stated with it)             *)
let w2sp2aux_winst_body =
 `!(s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) s' f' k ac f lens.
     wl_inst i s = SOME s' /\
     every_var_inst is_phy_var i /\
     max_var_inst i < 2 * f' + 2 * k /\
     inst_arg_convention i /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t'.
           stack_evaluate (wInst i (k,f,f'),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' s' t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`;;

let w2sp2aux_winst_case itm =
  let iv = mk_var("i",`:(A)inst`) in
  list_mk_forall(frees itm, vsubst [itm,iv] w2sp2aux_winst_body);;

(* W2SP2AUX: physical variables are the even ones *)
let W2SP2AUX_is_phy_var = prove
 (`!n. is_phy_var n <=> ?m. n = 2 * m`,
  REWRITE_TAC[is_phy_var_def; GSYM EVEN_MOD2; EVEN_EXISTS]);;

(* W2SP2AUX: the Const case of evaluate_wInst *)
let W2SP2AUX_wInst_Const = prove
 (w2sp2aux_winst_case `asm_Const reg (w:A word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_inst_def; every_var_inst_def; max_var_inst_def; wInst_def] THEN
  CASE_REWRITE_TAC[wl_assign_def; wl_word_exp_def; option_INJ; W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  MATCH_MP_TAC wRegWrite1_thm1 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"] THEN
  REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[stack_assign_def; stack_word_exp_def]);;

(* W2SP2AUX: inversion of wordSem assignments of the instruction shapes *)
let W2SP2AUX_assign_Op_Var = prove
 (`!r1 bop r2 r3 (s:(A,C,FFI)wl_state) s'.
     wl_assign r1 (wl_Op bop [wl_Var r2; wl_Var r3]) s = SOME s' <=>
     ?w2 w3 v. wl_get_var r2 s = SOME (wl_Word w2) /\
               wl_get_var r3 s = SOME (wl_Word w3) /\
               word_op bop [w2; w3] = SOME v /\ s' = wl_set_var r1 (wl_Word v) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_assign_def; wl_word_exp_def; MAP; the_words_def] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; OPTION_MAP_DEF]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_EQ_SOME; OPTION_MAP_EQ_NONE]) THEN
  ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

let W2SP2AUX_assign_Op_Const = prove
 (`!r1 bop r2 w (s:(A,C,FFI)wl_state) s'.
     wl_assign r1 (wl_Op bop [wl_Var r2; wl_Const w]) s = SOME s' <=>
     ?w2 v. wl_get_var r2 s = SOME (wl_Word w2) /\
            word_op bop [w2; w] = SOME v /\ s' = wl_set_var r1 (wl_Word v) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_assign_def; wl_word_exp_def; MAP; the_words_def] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; OPTION_MAP_DEF]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_EQ_SOME; OPTION_MAP_EQ_NONE]) THEN
  ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

let W2SP2AUX_assign_Shift_Var = prove
 (`!r1 sh r2 r3 (s:(A,C,FFI)wl_state) s'.
     wl_assign r1 (wl_Shift sh (wl_Var r2) (wl_Var r3)) s = SOME s' <=>
     ?w2 w3 v. wl_get_var r2 s = SOME (wl_Word w2) /\
               wl_get_var r3 s = SOME (wl_Word w3) /\
               word_sh sh w2 (val w3) = SOME v /\ s' = wl_set_var r1 (wl_Word v) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_assign_def; wl_word_exp_def] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; OPTION_MAP_DEF]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_EQ_SOME; OPTION_MAP_EQ_NONE]) THEN
  ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

let W2SP2AUX_assign_Shift_Const = prove
 (`!r1 sh r2 w (s:(A,C,FFI)wl_state) s'.
     wl_assign r1 (wl_Shift sh (wl_Var r2) (wl_Const w)) s = SOME s' <=>
     ?w2 v. wl_get_var r2 s = SOME (wl_Word w2) /\
            word_sh sh w2 (val w) = SOME v /\ s' = wl_set_var r1 (wl_Word v) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_assign_def; wl_word_exp_def] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; OPTION_MAP_DEF]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_EQ_SOME; OPTION_MAP_EQ_NONE]) THEN
  ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

(* W2SP2AUX: max3 below a bound *)
let W2SP2AUX_max3_LT = prove
 (`!x y z n. max3 x y z < n <=> x < n /\ y < n /\ z < n`,
  REWRITE_TAC[max3_def] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* W2SP2AUX: the stack Binop instruction computes the word Binop *)
let W2SP2AUX_stack_inst_Binop_Reg = prove
 (`!bop n n2 n3 (t:(A,C,FFI)stack_state) w2 w3 v.
     stack_get_var n2 t = SOME (wl_Word w2) /\
     stack_get_var n3 t = SOME (wl_Word w3) /\
     word_op bop [w2; w3] = SOME v
     ==> stack_evaluate (stack_Inst (asm_Arith (Binop bop n n2 (Reg n3))),t) =
         (NONE,stack_set_var n (wl_Word v) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    CASE_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "word_op")) THEN
    SUBGOAL_THEN `w3:A word = w2` SUBST1_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "FLOOKUP"))) THEN
      DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[ITLIST; WORD_OR_0; WORD_OR_IDEM] THEN
    SIMP_TAC[option_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[stack_assign_def; stack_word_exp_def; MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the Binop case of evaluate_wInst, register operand *)
let W2SP2AUX_wInst_Binop_Reg = prove
 (w2sp2aux_winst_case `asm_Arith (Binop bop r1 r2 (Reg r3)):(A)inst`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_inst_def; every_var_inst_def; every_var_imm_def; max_var_inst_def;
              wInst_def] THEN
  CASE_REWRITE_TAC[W2SP2AUX_assign_Op_Var; W2SP2AUX_is_phy_var; W2SP2AUX_max3_LT] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w2:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2 * m''`; `k:num`; `f:num`; `f':num`; `l':(num#num)list`; `n3:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w3:A word)`; `ac:(A)asm_config`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load2) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t2:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (Binop bop n1 n2 (Reg n3))):(A)stack_prog`;
                 `wl_Word (v:A word)`] wRegWrite1_thm1) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_Binop_Reg THEN
    MAP_EVERY EXISTS_TAC [`w2:A word`; `w3:A word`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the stack instructions of the other one-result shapes *)
let W2SP2AUX_stack_inst_Binop_Imm = prove
 (`!bop n n2 w (t:(A,C,FFI)stack_state) w2 v.
     stack_get_var n2 t = SOME (wl_Word w2) /\ word_op bop [w2; w] = SOME v
     ==> stack_evaluate (stack_Inst (asm_Arith (Binop bop n n2 (Imm w))),t) =
         (NONE,stack_set_var n (wl_Word v) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_assign_def; stack_word_exp_def; MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[ALL; IS_SOME_DEF; MAP; THE_DEF] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let W2SP2AUX_stack_inst_Shift_Reg = prove
 (`!sh n n2 n3 (t:(A,C,FFI)stack_state) w2 w3 v.
     stack_get_var n2 t = SOME (wl_Word w2) /\
     stack_get_var n3 t = SOME (wl_Word w3) /\
     word_sh sh w2 (val w3) = SOME v
     ==> stack_evaluate (stack_Inst (asm_Arith (asm_Shift sh n n2 (Reg n3))),t) =
         (NONE,stack_set_var n (wl_Word v) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_assign_def; stack_word_exp_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let W2SP2AUX_stack_inst_Shift_Imm = prove
 (`!sh n n2 w (t:(A,C,FFI)stack_state) w2 v.
     stack_get_var n2 t = SOME (wl_Word w2) /\ word_sh sh w2 (val w) = SOME v
     ==> stack_evaluate (stack_Inst (asm_Arith (asm_Shift sh n n2 (Imm w))),t) =
         (NONE,stack_set_var n (wl_Word v) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_assign_def; stack_word_exp_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let W2SP2AUX_stack_inst_Div = prove
 (`!n n2 n3 (t:(A,C,FFI)stack_state) w2 q.
     stack_get_var n2 t = SOME (wl_Word w2) /\
     stack_get_var n3 t = SOME (wl_Word q) /\ ~(q = word 0)
     ==> stack_evaluate (stack_Inst (asm_Arith (asm_Div n n2 n3)),t) =
         (NONE,stack_set_var n (wl_Word (word_jdiv w2 q)) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_get_vars_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the Binop case of evaluate_wInst, immediate operand *)
let W2SP2AUX_wInst_Binop_Imm = prove
 (w2sp2aux_winst_case `asm_Arith (Binop bop r1 r2 (Imm w)):(A)inst`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_inst_def; every_var_inst_def; every_var_imm_def; max_var_inst_def;
              wInst_def] THEN
  CASE_REWRITE_TAC[W2SP2AUX_assign_Op_Const; W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w2:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (Binop bop n1 n2 (Imm w))):(A)stack_prog`;
                 `wl_Word (v:A word)`] wRegWrite1_thm1) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_Binop_Imm THEN
    EXISTS_TAC `w2:A word` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the Shift case of evaluate_wInst, register operand *)
let W2SP2AUX_wInst_Shift_Reg = prove
 (w2sp2aux_winst_case `asm_Arith (asm_Shift sh r1 r2 (Reg r3)):(A)inst`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_inst_def; every_var_inst_def; every_var_imm_def; max_var_inst_def;
              wInst_def] THEN
  CASE_REWRITE_TAC[W2SP2AUX_assign_Shift_Var; W2SP2AUX_is_phy_var; W2SP2AUX_max3_LT] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w2:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2 * m''`; `k:num`; `f:num`; `f':num`; `l':(num#num)list`; `n3:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w3:A word)`; `ac:(A)asm_config`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load2) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t2:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (asm_Shift sh n1 n2 (Reg n3))):(A)stack_prog`;
                 `wl_Word (v:A word)`] wRegWrite1_thm1) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_Shift_Reg THEN
    MAP_EVERY EXISTS_TAC [`w2:A word`; `w3:A word`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the Shift case of evaluate_wInst, immediate operand *)
let W2SP2AUX_wInst_Shift_Imm = prove
 (w2sp2aux_winst_case `asm_Arith (asm_Shift sh r1 r2 (Imm w)):(A)inst`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_inst_def; every_var_inst_def; every_var_imm_def; max_var_inst_def;
              wInst_def] THEN
  CASE_REWRITE_TAC[W2SP2AUX_assign_Shift_Const; W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w2:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (asm_Shift sh n1 n2 (Imm w))):(A)stack_prog`;
                 `wl_Word (v:A word)`] wRegWrite1_thm1) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_Shift_Imm THEN
    EXISTS_TAC `w2:A word` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: inversion of the wordSem Div instruction *)
let W2SP2AUX_inst_Div = prove
 (`!r1 r2 r3 (s:(A,C,FFI)wl_state) s'.
     wl_inst (asm_Arith (asm_Div r1 r2 r3)) s = SOME s' <=>
     ?q w2. wl_get_var r3 s = SOME (wl_Word q) /\ wl_get_var r2 s = SOME (wl_Word w2) /\
            ~(q = word 0) /\ s' = wl_set_var r1 (wl_Word (word_jdiv w2 q)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT(CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
  ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

(* W2SP2AUX: the Div case of evaluate_wInst *)
let W2SP2AUX_wInst_Div = prove
 (w2sp2aux_winst_case `asm_Arith (asm_Div r1 r2 r3):(A)inst`,
  REPEAT GEN_TAC THEN REWRITE_TAC[W2SP2AUX_inst_Div] THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def] THEN
  CASE_REWRITE_TAC[W2SP2AUX_is_phy_var; W2SP2AUX_max3_LT] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w2:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2 * m''`; `k:num`; `f:num`; `f':num`; `l':(num#num)list`; `n3:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (q:A word)`; `ac:(A)asm_config`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load2) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t2:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (asm_Div n1 n2 n3)):(A)stack_prog`;
                 `wl_Word (word_jdiv (w2:A word) q)`] wRegWrite1_thm1) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_Div THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: inversion of the wordSem AddCarry, AddOverflow and SubOverflow *)
let W2SP2AUX_inst_AddCarry = prove
 (`!r1 r2 r3 r4 (s:(A,C,FFI)wl_state) s'.
     wl_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) s = SOME s' <=>
     ?l r c. wl_get_var r2 s = SOME (wl_Word l) /\ wl_get_var r3 s = SOME (wl_Word r) /\
             wl_get_var r4 s = SOME (wl_Word c) /\
             s' = wl_set_var r4 (wl_Word (SND (word_add_carry l r c)))
                    (wl_set_var r1 (wl_Word (FST (word_add_carry l r c))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASE_REWRITE_TAC[] THEN SIMP[FST; SND] THEN ASM_REWRITE_TAC[FST; SND] THEN
  MESON_TAC[]);;

let W2SP2AUX_inst_AddOverflow = prove
 (`!r1 r2 r3 r4 (s:(A,C,FFI)wl_state) s'.
     wl_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) s = SOME s' <=>
     ?w2 w3. wl_get_var r2 s = SOME (wl_Word w2) /\ wl_get_var r3 s = SOME (wl_Word w3) /\
             s' = wl_set_var r4
                    (wl_Word (if ~(ival (word_add w2 w3) = ival w2 + ival w3)
                              then word 1 else word 0))
                    (wl_set_var r1 (wl_Word (word_add w2 w3)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASE_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[]);;

let W2SP2AUX_inst_SubOverflow = prove
 (`!r1 r2 r3 r4 (s:(A,C,FFI)wl_state) s'.
     wl_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) s = SOME s' <=>
     ?w2 w3. wl_get_var r2 s = SOME (wl_Word w2) /\ wl_get_var r3 s = SOME (wl_Word w3) /\
             s' = wl_set_var r4
                    (wl_Word (if ~(ival (word_sub w2 w3) = ival w2 - ival w3)
                              then word 1 else word 0))
                    (wl_set_var r1 (wl_Word (word_sub w2 w3)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASE_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[]);;

(* W2SP2AUX: the stack AddCarry, AddOverflow and SubOverflow instructions *)
let W2SP2AUX_stack_inst_AddCarry = prove
 (`!n n2 n3 (t:(A,C,FFI)stack_state) l r c.
     stack_get_var n2 t = SOME (wl_Word l) /\ stack_get_var n3 t = SOME (wl_Word r) /\
     stack_get_var 0 t = SOME (wl_Word c)
     ==> stack_evaluate (stack_Inst (asm_Arith (asm_AddCarry n n2 n3 0)),t) =
         (NONE,stack_set_var 0 (wl_Word (SND (word_add_carry l r c)))
                 (stack_set_var n (wl_Word (FST (word_add_carry l r c))) t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_get_vars_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[word_add_carry_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND]);;

let W2SP2AUX_stack_inst_AddOverflow = prove
 (`!n n2 n3 (t:(A,C,FFI)stack_state) w2 w3.
     stack_get_var n2 t = SOME (wl_Word w2) /\ stack_get_var n3 t = SOME (wl_Word w3)
     ==> stack_evaluate (stack_Inst (asm_Arith (AddOverflow n n2 n3 0)),t) =
         (NONE,stack_set_var 0
                 (wl_Word (if ~(ival (word_add w2 w3) = ival w2 + ival w3)
                           then word 1 else word 0))
                 (stack_set_var n (wl_Word (word_add w2 w3)) t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_get_vars_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let W2SP2AUX_stack_inst_SubOverflow = prove
 (`!n n2 n3 (t:(A,C,FFI)stack_state) w2 w3.
     stack_get_var n2 t = SOME (wl_Word w2) /\ stack_get_var n3 t = SOME (wl_Word w3)
     ==> stack_evaluate (stack_Inst (asm_Arith (SubOverflow n n2 n3 0)),t) =
         (NONE,stack_set_var 0
                 (wl_Word (if ~(ival (word_sub w2 w3) = ival w2 - ival w3)
                           then word 1 else word 0))
                 (stack_set_var n (wl_Word (word_sub w2 w3)) t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_get_vars_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* W2SP2AUX: 0 is a physical variable *)
let W2SP2AUX_is_phy_var_0 = prove
 (`is_phy_var 0`,
  REWRITE_TAC[is_phy_var_def] THEN CONV_TAC NUM_REDUCE_CONV);;

(* W2SP2AUX: the AddCarry case of evaluate_wInst *)
let W2SP2AUX_wInst_AddCarry = prove
 (w2sp2aux_winst_case `asm_Arith (asm_AddCarry r1 r2 r3 r4):(A)inst`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r4 = 0` THEN
  ASM_REWRITE_TAC[inst_arg_convention_def] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[W2SP2AUX_inst_AddCarry; W2SP2AUX_is_phy_var_0] THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def; W2SP2AUX_is_phy_var_0] THEN
  CASE_REWRITE_TAC[W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `stack_get_var 0 (t:(A,C,FFI)stack_state) = SOME (wl_Word c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `0`;
      `0`; `wl_Word (c:A word)`] state_rel_get_var_imp') THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[EVEN] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (l:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2 * m''`; `k:num`; `f:num`; `f':num`; `l':(num#num)list`; `n3:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (r:A word)`; `ac:(A)asm_config`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load2) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t2:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (asm_AddCarry n1 n2 n3 0)):(A)stack_prog`;
                 `wl_Word (FST (word_add_carry (l:A word) r c))`;
                 `wl_Word (SND (word_add_carry (l:A word) r c))`] wRegWrite1_thm2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_AddCarry THEN
    ASM_SIMP_TAC[ARITH_RULE `4 < k ==> ~(0 = k) /\ ~(0 = k + 1)`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the AddOverflow case of evaluate_wInst *)
let W2SP2AUX_wInst_AddOverflow = prove
 (w2sp2aux_winst_case `asm_Arith (AddOverflow r1 r2 r3 r4):(A)inst`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r4 = 0` THEN
  ASM_REWRITE_TAC[inst_arg_convention_def] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[W2SP2AUX_inst_AddOverflow; W2SP2AUX_is_phy_var_0] THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def; W2SP2AUX_is_phy_var_0] THEN
  CASE_REWRITE_TAC[W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w2:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2 * m''`; `k:num`; `f:num`; `f':num`; `l':(num#num)list`; `n3:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w3:A word)`; `ac:(A)asm_config`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load2) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t2:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (AddOverflow n1 n2 n3 0)):(A)stack_prog`;
                 `wl_Word (word_add (w2:A word) w3)`;
                 `wl_Word (if ~(ival (word_add (w2:A word) w3) = ival w2 + ival w3)
                           then word 1 else word 0:A word)`] wRegWrite1_thm2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_AddOverflow THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the SubOverflow case of evaluate_wInst *)
let W2SP2AUX_wInst_SubOverflow = prove
 (w2sp2aux_winst_case `asm_Arith (SubOverflow r1 r2 r3 r4):(A)inst`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r4 = 0` THEN
  ASM_REWRITE_TAC[inst_arg_convention_def] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[W2SP2AUX_inst_SubOverflow; W2SP2AUX_is_phy_var_0] THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def; W2SP2AUX_is_phy_var_0] THEN
  CASE_REWRITE_TAC[W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w2:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2 * m''`; `k:num`; `f:num`; `f':num`; `l':(num#num)list`; `n3:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w3:A word)`; `ac:(A)asm_config`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load2) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 `t2:(A,C,FFI)stack_state`; `lens:num list`; `m:num`;
                 `\n1. stack_Inst (asm_Arith (SubOverflow n1 n2 n3 0)):(A)stack_prog`;
                 `wl_Word (word_sub (w2:A word) w3)`;
                 `wl_Word (if ~(ival (word_sub (w2:A word) w3) = ival w2 - ival w3)
                           then word 1 else word 0:A word)`] wRegWrite1_thm2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC W2SP2AUX_stack_inst_SubOverflow THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t3:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: inversion of the wordSem LongMul and LongDiv instructions *)
let W2SP2AUX_inst_LongMul = prove
 (`!r1 r2 r3 r4 (s:(A,C,FFI)wl_state) s'.
     wl_inst (asm_Arith (LongMul r1 r2 r3 r4)) s = SOME s' <=>
     ?w3 w4. wl_get_var r3 s = SOME (wl_Word w3) /\ wl_get_var r4 s = SOME (wl_Word w4) /\
             s' = wl_set_var r2 (wl_Word (word (val w3 * val w4)))
                    (wl_set_var r1 (wl_Word (word ((val w3 * val w4) DIV dimword (:A)))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN MESON_TAC[]);;

let W2SP2AUX_inst_LongDiv = prove
 (`!r1 r2 r3 r4 r5 (s:(A,C,FFI)wl_state) s'.
     wl_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) s = SOME s' <=>
     ?w3 w4 w5. wl_get_var r3 s = SOME (wl_Word w3) /\ wl_get_var r4 s = SOME (wl_Word w4) /\
                wl_get_var r5 s = SOME (wl_Word w5) /\
                ~(val w5 = 0) /\
                (val w3 * dimword (:A) + val w4) DIV val w5 < dimword (:A) /\
                s' = wl_set_var r1 (wl_Word (word ((val w3 * dimword (:A) + val w4) DIV val w5)))
                       (wl_set_var r2
                          (wl_Word (word ((val w3 * dimword (:A) + val w4) MOD val w5))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; EQ_SYM_EQ] THEN ASM_MESON_TAC[]);;

(* W2SP2AUX: the LongMul case of evaluate_wInst *)
let W2SP2AUX_wInst_LongMul = prove
 (w2sp2aux_winst_case `asm_Arith (LongMul r1 r2 r3 r4):(A)inst`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_arg_convention_def] THEN
  ASM_CASES_TAC `r1 = 6 /\ r2 = 0 /\ r3 = 0 /\ r4 = 4` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[W2SP2AUX_inst_LongMul; wInst_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `stack_get_var 0 (t:(A,C,FFI)stack_state) = SOME (wl_Word w3) /\
                stack_get_var 2 t = SOME (wl_Word w4)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
        `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `0`;
        `0`; `wl_Word (w3:A word)`] state_rel_get_var_imp');
      MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
        `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `0`;
        `4`; `wl_Word (w4:A word)`] state_rel_get_var_imp')] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_get_vars_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  SIMP[] THEN
  MATCH_MP_TAC state_rel_set_var' THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC; ARITH_TAC] THEN
  MATCH_MP_TAC state_rel_set_var' THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* W2SP2AUX: the LongDiv case of evaluate_wInst *)
let W2SP2AUX_wInst_LongDiv = prove
 (w2sp2aux_winst_case `asm_Arith (LongDiv r1 r2 r3 r4 r5):(A)inst`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_arg_convention_def] THEN
  ASM_CASES_TAC `r1 = 0 /\ r2 = 6 /\ r3 = 6 /\ r4 = 0` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[W2SP2AUX_inst_LongDiv; wInst_def; every_var_inst_def; max_var_inst_def] THEN
  REWRITE_TAC[is_phy_var_def] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM EVEN_MOD2; EVEN_EXISTS] THEN STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `stack_get_var 0 (t:(A,C,FFI)stack_state) = SOME (wl_Word w4) /\
                stack_get_var 3 t = SOME (wl_Word w3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
        `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `0`;
        `0`; `wl_Word (w4:A word)`] state_rel_get_var_imp');
      MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
        `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `0`;
        `6`; `wl_Word (w3:A word)`] state_rel_get_var_imp')] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2 * m`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n5:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (w5:A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stack_get_var 0 (t1:(A,C,FFI)stack_state) = SOME (wl_Word w4) /\
                stack_get_var 3 t1 = SOME (wl_Word w3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `4 < k ==> ~(0 = k) /\ ~(3 = k)`]; ALL_TAC] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_get_vars_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  SIMP[] THEN
  MATCH_MP_TAC state_rel_set_var' THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC; ARITH_TAC] THEN
  MATCH_MP_TAC state_rel_set_var' THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* W2SP2AUX: loading an address register with wReg1, then running P *)
let W2SP2AUX_one_load_const = prove
 (`!r k f f' l r' (s:(A,num#C,FFI)wl_state) c w ac (t:(A,C,FFI)stack_state) lens.
     wReg1 r (k,f,f') = (l,r') /\ EVEN r /\
     wl_word_exp s (wl_Op asm_Add [wl_Var r; wl_Const c]) = SOME (wl_Word w) /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t1:(A,C,FFI)stack_state.
           (!P. stack_evaluate (wStackLoad l P,t) = stack_evaluate (P,t1)) /\
           stack_state_clock t1 = stack_state_clock t /\
           word_to_stackProof_state_rel ac k f f' s t1 lens 0 /\
           LENGTH (stack_state_stack t1) = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t1 = stack_state_stack_space t /\
           ~(r' = k + 1) /\
           stack_word_exp t1 (wl_Op asm_Add [wl_Var r'; wl_Const c]) = SOME w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP evaluate_wStackLoad_wReg1_with_const) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_wStackLoad_seq] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the memory components of related states *)
let W2SP2AUX_state_rel_mem = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> stack_state_memory t = wl_state_memory s /\
         stack_state_mdomain t = wl_state_mdomain s /\
         stack_state_be t = wl_state_be s`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* W2SP2AUX: inversion of the wordSem memory instructions *)
let W2SP2AUX_inst_Mem = prove
 (`(!r a w (s:(A,C,FFI)wl_state) s'.
     wl_inst (Mem asm_Load r (Addr a w)) s = SOME s' <=>
     ?ad v. wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME (wl_Word ad) /\
            wl_mem_load ad s = SOME v /\ s' = wl_set_var r v s) /\
   (!r a w (s:(A,C,FFI)wl_state) s'.
     wl_inst (Mem Load8 r (Addr a w)) s = SOME s' <=>
     ?ad b. wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME (wl_Word ad) /\
            mem_load_byte_aux (wl_state_memory s) (wl_state_mdomain s) (wl_state_be s) ad =
              SOME b /\
            s' = wl_set_var r (wl_Word (word_zx b)) s) /\
   (!r a w (s:(A,C,FFI)wl_state) s'.
     wl_inst (Mem asm_Load32 r (Addr a w)) s = SOME s' <=>
     ?ad b. wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME (wl_Word ad) /\
            mem_load_32 (wl_state_memory s) (wl_state_mdomain s) (wl_state_be s) ad =
              SOME b /\
            s' = wl_set_var r (wl_Word (word_zx b)) s) /\
   (!r a w (s:(A,C,FFI)wl_state) s'.
     wl_inst (Mem asm_Store r (Addr a w)) s = SOME s' <=>
     ?ad v. wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME (wl_Word ad) /\
            wl_get_var r s = SOME v /\ wl_mem_store ad v s = SOME s') /\
   (!r a w (s:(A,C,FFI)wl_state) s'.
     wl_inst (Mem Store8 r (Addr a w)) s = SOME s' <=>
     ?ad x nm. wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME (wl_Word ad) /\
               wl_get_var r s = SOME (wl_Word x) /\
               mem_store_byte_aux (wl_state_memory s) (wl_state_mdomain s) (wl_state_be s)
                 ad (word_zx x) = SOME nm /\
               s' = wl_state_memory_fupd (K nm) s) /\
   (!r a w (s:(A,C,FFI)wl_state) s'.
     wl_inst (Mem asm_Store32 r (Addr a w)) s = SOME s' <=>
     ?ad x nm. wl_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME (wl_Word ad) /\
               wl_get_var r s = SOME (wl_Word x) /\
               mem_store_32 (wl_state_memory s) (wl_state_mdomain s) (wl_state_be s)
                 ad (word_zx x) = SOME nm /\
               s' = wl_state_memory_fupd (K nm) s)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN
  CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

(* W2SP2AUX: apply wRegWrite1_thm1 to the wRegWrite1 of the goal, from the *)
(* stack state tm (an OCaml helper for the tactics)                         *)
let w2sp2aux_rw1_tac tm : tactic = fun (asl,w as g) ->
  let is_c c t = try fst(dest_const(fst(strip_comb t))) = c with Failure _ -> false in
  let rw = find_term (is_c "wRegWrite1") w in
  let kont,rv = match snd(strip_comb rw) with
      [kont; r; _] -> kont,r | _ -> failwith "w2sp2aux_rw1_tac" in
  let sv = find_term (fun t -> is_c "wl_set_var" t &&
                        (match snd(strip_comb t) with [r;_;_] -> r = rv | _ -> false)) w in
  let v = el 1 (snd(strip_comb sv)) in
  let m = rand rv in
  MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `s:(A,num#C,FFI)wl_state`;
                 tm; `lens:num list`; m; kont; v] wRegWrite1_thm1) g;;

(* W2SP2AUX: the Load, Load8 and Load32 cases of evaluate_wInst *)
let W2SP2AUX_wInst_Load = prove
 (list_mk_conj [w2sp2aux_winst_case `Mem asm_Load r (Addr a w):(A)inst`;
                 w2sp2aux_winst_case `Mem Load8 r (Addr a w):(A)inst`;
                 w2sp2aux_winst_case `Mem asm_Load32 r (Addr a w):(A)inst`],
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[W2SP2AUX_inst_Mem] THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def] THEN
  CASE_REWRITE_TAC[W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_mem) THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `w:A word`; `ad:A word`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load_const) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_mem o
    check (fun th -> w2sp2aux_has_const "word_to_stackProof_state_rel" th &&
                     can (find_term (fun x -> x = `t1:(A,C,FFI)stack_state`)) (concl th))) THEN
  w2sp2aux_rw1_tac `t1:(A,C,FFI)stack_state` THEN
  ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL
   [(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REPEAT STRIP_TAC; MESON_TAC[]]) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_mem_load_def]) THEN
  ASM_REWRITE_TAC[stack_mem_load_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "mem_load_byte_aux"))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "mem_load_32"))) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
  TRY(DISCH_THEN SUBST1_TAC) THEN CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the Store, Store8 and Store32 cases of evaluate_wInst *)
let W2SP2AUX_wInst_Store = prove
 (list_mk_conj [w2sp2aux_winst_case `Mem asm_Store r (Addr a w):(A)inst`;
                 w2sp2aux_winst_case `Mem Store8 r (Addr a w):(A)inst`;
                 w2sp2aux_winst_case `Mem asm_Store32 r (Addr a w):(A)inst`],
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[W2SP2AUX_inst_Mem] THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def] THEN
  CASE_REWRITE_TAC[W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `l1:(num#num)list`; `n2:num`;
                 `s:(A,num#C,FFI)wl_state`; `w:A word`; `ad:A word`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load_const) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (asl,_) -> let gv = find (fun (_,th) -> try
         (let l,r = dest_eq(concl th) in
          fst(dest_const(fst(strip_comb l))) = "wl_get_var" &&
          rand(rator l) = `2 * m`) with Failure _ -> false) asl in
       MP_TAC(ISPECL [`2 * m`; `k:num`; `f:num`; `f':num`; `l2:(num#num)list`; `n1:num`;
                      `s:(A,num#C,FFI)wl_state`; rand(rhs(concl(snd gv)));
                      `ac:(A)asm_config`; `t1:(A,C,FFI)stack_state`; `lens:num list`]
                     W2SP2AUX_one_load2)) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_mem o
    check (fun th -> w2sp2aux_has_const "word_to_stackProof_state_rel" th &&
                     can (find_term (fun x -> x = `t2:(A,C,FFI)stack_state`)) (concl th))) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `t2:(A,C,FFI)stack_state`; `lens:num list`; `0`;
      `ad:A word`; `v:(A)word_loc`; `s':(A,num#C,FFI)wl_state`]
      word_to_stackProof_state_rel_mem_store) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `stack_mem_store ad v (t2:(A,C,FFI)stack_state) = SOME t3` THEN
    REWRITE_TAC[stack_mem_store_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  SIMP[] THEN MATCH_MP_TAC W2SP2AUX_state_rel_with_memory THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the floating-point cases of evaluate_wInst that only use     *)
(* floating-point registers                                                *)
let W2SP2AUX_wInst_FP_pure = prove
 (list_mk_conj (map w2sp2aux_winst_case
   [`FP (FPMov d1 d2):(A)inst`; `FP (FPAbs d1 d2):(A)inst`; `FP (FPNeg d1 d2):(A)inst`;
    `FP (FPSqrt d1 d2):(A)inst`; `FP (FPAdd d1 d2 d3):(A)inst`;
    `FP (FPSub d1 d2 d3):(A)inst`; `FP (FPMul d1 d2 d3):(A)inst`;
    `FP (FPDiv d1 d2 d3):(A)inst`; `FP (FPFma d1 d2 d3):(A)inst`;
    `FP (FPToInt d1 d2):(A)inst`; `FP (FPFromInt d1 d2):(A)inst`]),
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wInst_def; w2sp2aux_seval "stack_Inst"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "wl_inst")) THEN
  REWRITE_TAC[wl_inst_def; stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP
    word_to_stackProof_state_rel_get_fp_var th)]) THEN
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_SIMP_TAC[word_to_stackProof_state_rel_set_fp_var] THEN SIMP[stack_set_fp_var_def]);;

(* W2SP2AUX: the floating-point comparison cases of evaluate_wInst *)
let W2SP2AUX_wInst_FP_cmp = prove
 (list_mk_conj (map w2sp2aux_winst_case
   [`FP (FPLess r d1 d2):(A)inst`; `FP (FPLessEqual r d1 d2):(A)inst`;
    `FP (FPEqual r d1 d2):(A)inst`]),
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def; W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "wl_inst")) THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  w2sp2aux_rw1_tac `t:(A,C,FFI)stack_state` THEN
  ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL
   [(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REPEAT STRIP_TAC; MESON_TAC[]]) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP
    word_to_stackProof_state_rel_get_fp_var th)]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the FPMovFromReg case of evaluate_wInst *)
let W2SP2AUX_wInst_FPMovFromReg = prove
 (w2sp2aux_winst_case `FP (FPMovFromReg d r1 r2):(A)inst`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def] THEN
  ASM_CASES_TAC `dimindex (:A) = 64` THEN ASM_REWRITE_TAC[W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "wl_inst")) THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN w2sp2aux_rveq_tac THEN
  REPEAT PAIRARG_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  w2sp2aux_rveq_tac THEN
  REWRITE_TAC[wStackLoad_append; o_THM] THENL
   [MP_TAC(ISPECL [`2 * m`; `k:num`; `f:num`; `f':num`; `x:(num#num)list`; `y:num`;
                   `s:(A,num#C,FFI)wl_state`; `wl_Word (a':A word)`; `ac:(A)asm_config`;
                   `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
    ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[wStackLoad_def] THEN
    REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    ASM_SIMP_TAC[word_to_stackProof_state_rel_set_fp_var] THEN SIMP[stack_set_fp_var_def];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2 * m`; `k:num`; `f:num`; `f':num`; `x':(num#num)list`; `y':num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (a''':A word)`; `ac:(A)asm_config`;
                 `t:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2 * m'`; `k:num`; `f:num`; `f':num`; `x:(num#num)list`; `y:num`;
                 `s:(A,num#C,FFI)wl_state`; `wl_Word (a':A word)`; `ac:(A)asm_config`;
                 `t1:(A,C,FFI)stack_state`; `lens:num list`] W2SP2AUX_one_load2) THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_SIMP_TAC[word_to_stackProof_state_rel_set_fp_var] THEN SIMP[stack_set_fp_var_def]);;

(* W2SP2AUX: wRegWrite1 under a later write of another register n <> k *)
let W2SP2AUX_wRegWrite1_under = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens m kont n hi lo.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     m < f' + k /\ ~(n = k) /\
     (!n'. n' <= k
           ==> stack_evaluate (kont n',t) =
               (NONE,stack_set_var n hi (stack_set_var n' lo t)))
     ==> ?t'.
           stack_evaluate (wRegWrite1 kont (2 * m) (k,f,f'),t) =
             (NONE,stack_set_var n hi t') /\
           word_to_stackProof_state_rel ac k f f' (wl_set_var (2 * m) lo s) t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[wRegWrite1_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `stack_set_var m (lo:(A)word_loc) (t:(A,C,FFI)stack_state)` THEN
    ASM_SIMP_TAC[LT_IMP_LE; word_to_stackProof_state_rel_set_var] THEN
    SIMP[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ASM_SIMP_TAC[LE_REFL] THEN
  SIMP[] THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  SUBGOAL_THEN `FLOOKUP (stack_state_regs (stack_set_var n hi
     (stack_set_var k (lo:(A)word_loc) (t:(A,C,FFI)stack_state)))) k = SOME lo`
    ASSUME_TAC THENL
   [REWRITE_TAC[stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP[stack_get_var_def] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
         stack_state_stack_space t + (f - 1) - (m - k))` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f - 1) - (m - k) = (f + k) - (m + 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `stack_state_stack_fupd (K (LUPDATE (lo:(A)word_loc)
     (stack_state_stack_space t + (f + k) - (m + 1)) (stack_state_stack t)))
     (stack_set_var k lo (t:(A,C,FFI)stack_state))` THEN
  SIMP[LENGTH_LUPDATE] THEN
  MATCH_MP_TAC state_rel_set_var2 THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* W2SP2AUX: the FPMovToReg case of evaluate_wInst *)
let W2SP2AUX_wInst_FPMovToReg = prove
 (w2sp2aux_winst_case `FP (FPMovToReg r1 r2 d):(A)inst`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; wInst_def] THEN
  ASM_CASES_TAC `dimindex (:A) = 64` THEN ASM_REWRITE_TAC[W2SP2AUX_is_phy_var] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "wl_inst")) THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN w2sp2aux_rveq_tac THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP word_to_stackProof_state_rel_get_fp_var) THENL
   [w2sp2aux_rw1_tac `t:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL
     [(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN REPEAT STRIP_TAC; MESON_TAC[]]) THEN
    REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[evaluate_wRegWrite2_seq] THEN PAIRARG_TAC THEN
  MATCH_MP_TAC evaluate_wStackStore_wReg2_new THEN
  EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[EVEN_DOUBLE] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC W2SP2AUX_wRegWrite1_under THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    UNDISCH_TAC `wReg2 (2 * m') (k,f,f') = (l:(num#num)list,n)` THEN
    REWRITE_TAC[wReg2_def] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* W2SP2AUX: the Skip, Load16 and Store16 cases of evaluate_wInst *)
let W2SP2AUX_wInst_other = prove
 (list_mk_conj (map w2sp2aux_winst_case
   [`asm_Skip:(A)inst`; `Mem Load16 r (ad:(A)addr):(A)inst`;
    `Mem Store16 r (ad:(A)addr):(A)inst`]),
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN EXISTS_TAC `t:(A,C,FFI)stack_state` THEN
  ASM_REWRITE_TAC[wInst_def; w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 4688 *)
let evaluate_wInst = prove
 (`!i (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) s' f' k ac f lens.
     wl_inst i s = SOME s' /\
     every_var_inst is_phy_var i /\
     max_var_inst i < 2 * f' + 2 * k /\
     inst_arg_convention i /\
     word_to_stackProof_state_rel ac k f f' s t lens 0
     ==> ?t'.
           stack_evaluate (wInst i (k,f,f'),t) = (NONE,t') /\
           word_to_stackProof_state_rel ac k f f' s' t' lens 0 /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           stack_state_stack_space t' = stack_state_stack_space t`,
  let cases_tac =
    FIRST (map MATCH_ACCEPT_TAC
      (CONJUNCTS W2SP2AUX_wInst_other @ [W2SP2AUX_wInst_Const;
       W2SP2AUX_wInst_Binop_Reg; W2SP2AUX_wInst_Binop_Imm; W2SP2AUX_wInst_Shift_Reg;
       W2SP2AUX_wInst_Shift_Imm; W2SP2AUX_wInst_Div; W2SP2AUX_wInst_LongMul;
       W2SP2AUX_wInst_LongDiv; W2SP2AUX_wInst_AddCarry; W2SP2AUX_wInst_AddOverflow;
       W2SP2AUX_wInst_SubOverflow] @ CONJUNCTS W2SP2AUX_wInst_Load @
       CONJUNCTS W2SP2AUX_wInst_Store @ CONJUNCTS W2SP2AUX_wInst_FP_pure @
       CONJUNCTS W2SP2AUX_wInst_FP_cmp @
       [W2SP2AUX_wInst_FPMovFromReg; W2SP2AUX_wInst_FPMovToReg])) in
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `i:(A)inst` (cases "inst")) THEN
  TRY cases_tac THENL
   [STRUCT_CASES_TAC(ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
    TRY cases_tac THEN
    STRUCT_CASES_TAC(ISPEC `a3:(A)reg_imm` (cases "reg_imm")) THEN cases_tac;
    STRUCT_CASES_TAC(ISPEC `a0:memop` (cases "memop")) THEN
    TRY cases_tac THEN
    STRUCT_CASES_TAC(ISPEC `a2:(A)addr` (cases "addr")) THEN cases_tac;
    STRUCT_CASES_TAC(ISPEC `a:fp` (cases "fp")) THEN cases_tac]);;

(* HOL4 line 5132 *)
let state_rel_set_store = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra v x.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\ ~(v = Handler)
     ==> word_to_stackProof_state_rel ac k f f' (wl_set_store v x s)
           (stack_set_store v x t) lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  REWRITE_TAC[wl_set_store_def; stack_set_store_def] THEN
  SIMP[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[DOMSUB_FUPDATE_NEQ; FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5149 *)
let get_vars_fromList2_eq = prove
 (`!(args:B list) (s:(A,C,FFI)wl_state) x n y.
     wl_get_vars (list_of_seq (\x. 2 * x) (LENGTH args)) s = SOME x /\
     lookup n (fromList2 x) = SOME y
     ==> lookup n (wl_state_locals s) = SOME y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP word_to_stackProof_get_vars_eq) MP_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[lookup_fromList2; lookup_fromList; LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS] o
    check (fun th -> is_comb(concl th) && rator(concl th) = `EVEN`)) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; MEM_GENLIST] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o SPEC `lookup (2 * m) (wl_state_locals (s:(A,C,FFI)wl_state))`) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `2 * m` THEN REWRITE_TAC[] THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) && not (is_eq(concl th)))) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_MAP; misc_TWOxDIV2];
    ALL_TAC] THEN
  REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF]);;

(* HOL4 line 5168 *)
let get_vars_fromList2_eq_cons = prove
 (`!(args:B list) (s:(A,C,FFI)wl_state) x n x3 x4 y.
     wl_get_vars (list_of_seq (\x. 2 * (x + 1)) (LENGTH args)) s = SOME x /\
     lookup n (fromList2 (CONS (wl_Loc x3 x4) x)) = SOME y /\ ~(n = 0)
     ==> lookup n (wl_state_locals s) = SOME y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP word_to_stackProof_get_vars_eq)
    STRIP_ASSUME_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[lookup_fromList2; lookup_fromList; LENGTH_MAP; LENGTH_LIST_OF_SEQ;
              LENGTH] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS] o
    check (fun th -> is_comb(concl th) && rator(concl th) = `EVEN`)) THEN
  REWRITE_TAC[misc_TWOxDIV2] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC o
    MATCH_MP (MESON[num_CASES; ADD1] `~(m = 0) ==> ?p. m = p + 1`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[misc_TWOxDIV2; GSYM ADD1; LT_SUC]) THEN
  REWRITE_TAC[GSYM ADD1; EL; TL] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[ADD1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; MEM_GENLIST] THEN
  DISCH_THEN(MP_TAC o SPEC `lookup (2 * (p + 1)) (wl_state_locals (s:(A,C,FFI)wl_state))`) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `2 * (p + 1)` THEN REWRITE_TAC[] THEN EXISTS_TAC `p:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF]);;

(* HOL4 line 5190 *)
let lookup_fromList2_prefix = prove
 (`!(x:A list) z y n.
     IS_PREFIX z x /\ lookup n (fromList2 x) = SOME y ==> lookup n (fromList2 z) = SOME y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_PREFIX_DEF; IS_PREFIX_APPEND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:A list` SUBST1_TAC) MP_TAC) THEN
  REWRITE_TAC[lookup_fromList2; lookup_fromList; LENGTH_APPEND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_SIMP_TAC[ARITH_RULE `a < b ==> a < b + c:num`; EL_APPEND1]);;

(* HOL4 line 5234 *)
let evaluate_call_dest_clock = prove
 (`!dest args k f f' (q0:(A)stack_prog) dest' (t:(A,C,FFI)stack_state) clk.
     call_dest dest args (k,f,f') = (q0,dest')
     ==> stack_evaluate (q0,stack_state_clock_fupd (K clk) t) =
         (I ## (\t. stack_state_clock_fupd (K clk) t)) (stack_evaluate (q0,t))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[call_dest_def] THENL
   [COND_CASES_TAC THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
      REWRITE_TAC[w2sp2aux_seval "stack_Skip"; PAIR_MAP_THM; I_THM];
      ALL_TAC] THEN
    MP_TAC(ISPEC `wReg2 (LAST args) (k,f,f')` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:(num#num)list` (X_CHOOSE_THEN `r:num` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    REWRITE_TAC[evaluate_wStackLoad_clock];
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    REWRITE_TAC[w2sp2aux_seval "stack_Skip"; PAIR_MAP_THM; I_THM]]);;

(* HOL4 line 5244 *)
let evaluate_wLive_clock = prove
 (`!x (t:(A,C,FFI)stack_state) q (bs:(A word)app_list#num) bs' kf clk.
     wLive x bs kf = (q,bs')
     ==> stack_evaluate (q,stack_state_clock_fupd (K clk) t) =
         (FST (stack_evaluate (q,t)),
          stack_state_clock_fupd (K clk) (SND (stack_evaluate (q,t))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `kf:num#num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ff:num#num` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ff:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `f':num` SUBST1_TAC)) THEN
  REWRITE_TAC[wLive_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    REWRITE_TAC[w2sp2aux_seval "stack_Skip"; FST; SND];
    ALL_TAC] THEN
  MP_TAC(ISPEC `insert_bitmap (write_bitmap (SND (x:(1)spt#(1)spt)) k f')
                  (bs:(A word)app_list#num)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `nb:(A word)app_list#num` (X_CHOOSE_THEN `i:num` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Inst";
              w2sp2aux_seval "StackStore"] THEN
  SIMP[stack_inst_def; stack_assign_def; stack_word_exp_def; stack_get_var_def;
       stack_set_var_def; stack_empty_env_def; FLOOKUP_UPDATE] THEN
  REPEAT(COND_CASES_TAC THEN SIMP[]) THEN CASE_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 5260 *)
let state_rel_IMP_LENGTH = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> LENGTH lens = LENGTH (wl_state_stack s)`,
  REWRITE_TAC[word_to_stackProof_state_rel_def; word_to_stackProof_stack_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[abs_stack_IMP_LENGTH]);;

(* W2SP2AUX: stack_move copies n stack slots, elementwise *)
let W2SP2AUX_stack_move = prove
 (`!n tar (t:(A,C,FFI)stack_state) offset k.
     stack_state_use_stack t /\
     stack_state_stack_space t + tar + n + offset <= LENGTH (stack_state_stack t) /\
     n <= offset
     ==> ?st rg.
           stack_evaluate (stack_move n tar offset k stack_Skip,t) =
             (NONE,stack_state_stack_fupd (K st) (stack_state_regs_fupd (K rg) t)) /\
           (!i. ~(i = k) ==> FLOOKUP rg i = FLOOKUP (stack_state_regs t) i) /\
           LENGTH st = LENGTH (stack_state_stack t) /\
           (!j. j < LENGTH st
                ==> EL j st =
                    if stack_state_stack_space t + tar <= j /\
                       j < stack_state_stack_space t + tar + n
                    then EL (j + offset) (stack_state_stack t)
                    else EL j (stack_state_stack t))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`stack_state_stack (t:(A,C,FFI)stack_state)`;
                          `stack_state_regs (t:(A,C,FFI)stack_state)`] THEN
    REWRITE_TAC[stack_move_def; w2sp2aux_seval "stack_Skip"; PAIR_EQ] THEN
    CONJ_TAC THENL [SIMP[stack_state_component_equality]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tar + 1`; `t:(A,C,FFI)stack_state`; `offset:num`;
                                `k:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:((A)word_loc)list` (X_CHOOSE_THEN
    `rg1:(num,(A)word_loc)fmap` (CONJUNCTS_THEN2 (LABEL_TAC "E")
      (CONJUNCTS_THEN2 (LABEL_TAC "R") (CONJUNCTS_THEN2 (LABEL_TAC "L")
         (LABEL_TAC "EL")))))) THEN
  REWRITE_TAC[stack_move_def; w2sp2aux_seval "stack_Seq"] THEN
  USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "StackLoad";
              w2sp2aux_seval "StackStore"] THEN
  CONV_TAC(CAKE_SIMP_CONV[]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stack_state_stack_space (t:(A,C,FFI)stack_state) + tar + offset <
                LENGTH (stack_state_stack t)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(CAKE_SIMP_CONV[]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) <=
                  stack_state_stack_space t + tar)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN
  CONV_TAC(CAKE_SIMP_CONV[FLOOKUP_UPDATE]) THEN
  MAP_EVERY EXISTS_TAC
   [`LUPDATE (EL (stack_state_stack_space (t:(A,C,FFI)stack_state) + tar + offset) st1)
             (stack_state_stack_space t + tar) (st1:((A)word_loc)list)`;
    `(rg1:(num,(A)word_loc)fmap) |+ (k,EL (stack_state_stack_space (t:(A,C,FFI)stack_state)
                                          + tar + offset) st1)`] THEN
  REWRITE_TAC[LENGTH_LUPDATE; FLOOKUP_UPDATE] THEN
  CONJ_TAC THENL [USE_THEN "R" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_LUPDATE] THEN USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `j = stack_state_stack_space (t:(A,C,FFI)stack_state) + tar` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `stack_state_stack_space (t:(A,C,FFI)stack_state) + tar <
                  LENGTH (stack_state_stack t)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "EL" (MP_TAC o SPEC `stack_state_stack_space (t:(A,C,FFI)stack_state) + tar +
                                     offset`) THEN
    USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "EL" (MP_TAC o SPEC `j:num`) THEN
  USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 5270 *)
let evaluate_stack_move = prove
 (`!n tar (t:(A,C,FFI)stack_state) offset k.
     stack_state_use_stack t /\
     stack_state_stack_space t + tar + n + offset <= LENGTH (stack_state_stack t) /\
     n <= offset
     ==> ?t'.
           stack_evaluate (stack_move n tar offset k stack_Skip,t) = (NONE,t') /\
           ?t'_stack t'_regs.
             t' = stack_state_stack_fupd (K t'_stack) (stack_state_regs_fupd (K t'_regs) t) /\
             (!i. ~(i = k) ==> stack_get_var i t' = stack_get_var i t) /\
             LENGTH (stack_state_stack t) = LENGTH t'_stack /\
             stack_state_stack_space t' = stack_state_stack_space t /\
             DROP (stack_state_stack_space t' + tar + n) t'_stack =
               DROP (stack_state_stack_space t + tar + n) (stack_state_stack t) /\
             let stack' = DROP (stack_state_stack_space t' + tar) t'_stack in
             let stack = DROP (stack_state_stack_space t + tar) (stack_state_stack t) in
             !x. x < n ==> EL (x + offset) stack = EL x stack'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(SPEC `k:num` (MATCH_MP W2SP2AUX_stack_move th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A)word_loc)list` (X_CHOOSE_THEN
    `rg:(num,(A)word_loc)fmap` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  MAP_EVERY EXISTS_TAC [`st:((A)word_loc)list`; `rg:(num,(A)word_loc)fmap`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[stack_get_var_def] THEN CONV_TAC(CAKE_SIMP_CONV[]) THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_DROP] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_DROP; ARITH_RULE `i < l - m ==> i + m < l`] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x + offset) + stack_state_stack_space (t:(A,C,FFI)stack_state) + tar <
                LENGTH (stack_state_stack t) /\
                x + stack_state_stack_space t + tar < LENGTH (st:((A)word_loc)list)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_DROP] THEN
  COND_CASES_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ASM_ARITH_TAC]);;

(* HOL4 line 5330 *)
let evaluate_stack_move_seq = prove
 (`!a b c d prog (t:(A,C,FFI)stack_state).
     stack_evaluate (stack_move a b c d prog,t) =
     stack_evaluate (stack_Seq prog (stack_move a b c d stack_Skip),t)`,
  INDUCT_TAC THEN REWRITE_TAC[stack_move_def; W2SP2AUX_evaluate_Seq_Skip] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM W2SP2AUX_evaluate_Seq_assoc] THEN
  REPEAT(MATCH_MP_TAC W2SP2AUX_evaluate_Seq_cong) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5349: val evaluate_stack_move_clock = Q.prove(...) *)
let evaluate_stack_move_clock = prove
 (`!a b c d (t:(A,C,FFI)stack_state) clk.
     let prog = stack_move a b c d stack_Skip in
     stack_evaluate (prog,stack_state_clock_fupd (K clk) t) =
     (FST (stack_evaluate (prog,t)),
      stack_state_clock_fupd (K clk) (SND (stack_evaluate (prog,t))))`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  INDUCT_TAC THEN REWRITE_TAC[stack_move_def] THENL
   [REWRITE_TAC[w2sp2aux_seval "stack_Skip"]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `stack_evaluate (stack_move a (b + 1) c d stack_Skip:(A)stack_prog,
                                t:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)stack_result)option` (X_CHOOSE_THEN
    `s1:(A,C,FFI)stack_state` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "StackLoad";
              w2sp2aux_seval "StackStore"] THEN
  SIMP[stack_get_var_def; stack_set_var_def; stack_empty_env_def; FLOOKUP_UPDATE] THEN
  REPEAT(COND_CASES_TAC THEN SIMP[FLOOKUP_UPDATE]));;

(* HOL4 line 5361 *)
let pop_env_ffi = prove
 (`!(s:(A,C,FFI)wl_state) s'. wl_pop_env s = SOME s' ==> wl_state_ffi s = wl_state_ffi s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN
  CASES_ON `wl_state_stack (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `a0:(A)stack_frame` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a3:(num#num#num)option` THEN CASE_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]; ALL_TAC] THEN
  MP_TAC(ISPEC `a:num#num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `y:num#num` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `y:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:num` (X_CHOOSE_THEN `y2:num` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

(* W2SP2AUX: DROP of a cons with a successor written n + 1 *)
let W2SP2AUX_DROP_ADD1_CONS = prove
 (`!n (h:A) t. DROP (n + 1) (CONS h t) = DROP n t`,
  REWRITE_TAC[GSYM ADD1; DROP]);;

(* HOL4 line 5368 *)
let stack_rel_DROP_NONE = prove
 (`!k whandler n l0 l (wstack:((A)stack_frame)list) (shandler:((B)word_loc)option) sstack len
     (bs:(A word)list) f' lens.
     word_to_stackProof_stack_rel k whandler (CONS (StackFrame n l0 l NONE) wstack)
       shandler sstack len bs (CONS f' lens)
     ==> word_to_stackProof_stack_rel k whandler wstack shandler (DROP (f' + 1) sstack)
           len bs lens`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def; ALL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> if can (find_term (fun t -> try fst(dest_const t) =
     "abs_stack" with _ -> false)) (concl th) && is_eq (concl th)
     then MP_TAC th else ASSUME_TAC th)) THEN
  STRUCT_CASES_TAC (ISPEC `sstack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; option_DISTINCT] THEN
  CASES_ON `full_read_bitmap (bs:(A word)list) (h:(A)word_loc)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASES_ON `abs_stack (bs:(A word)list) (wstack:((A)stack_frame)list)
              (DROP f' (t:((A)word_loc)list)) lens` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `a':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
  ASM_REWRITE_TAC[W2SP2AUX_DROP_ADD1_CONS] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP abs_stack_IMP_LENGTH) THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[LENGTH] THEN
    SUBGOAL_THEN `SUC (LENGTH (wstack:((A)stack_frame)list)) - (whandler + 1) =
                  SUC (LENGTH wstack - (whandler + 1))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[EL; TL] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`whandler + 1`;
      `a':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`] LASTN_CONS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN SIMP_TAC[];
    UNDISCH_TAC `stack_rel_aux k len (CONS (StackFrame n l0 l NONE)
                   (wstack:((A)stack_frame)list))
                   (CONS (NONE,a,TAKE f' (t:((A)word_loc)list)) a')` THEN
    REWRITE_TAC[stack_rel_aux_def] THEN SIMP_TAC[]]);;

(* HOL4 line 5384 *)
let stack_rel_DROP_SOME = prove
 (`!k whandler n l0 l whandler' b c (wstack:((A)stack_frame)list)
     (shandler:((B)word_loc)option) sstack len
     (bs:(A word)list) f' lens.
     word_to_stackProof_stack_rel k whandler
       (CONS (StackFrame n l0 l (SOME (whandler',b,c))) wstack)
       shandler sstack len bs (CONS f' lens)
     ==> word_to_stackProof_stack_rel k whandler' wstack (SOME (EL 2 sstack))
           (DROP (f' + 4) sstack) len bs lens`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def; ALL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> if can (find_term (fun t -> try fst(dest_const t) =
     "abs_stack" with _ -> false)) (concl th) && is_eq (concl th)
     then MP_TAC th else ASSUME_TAC th)) THEN
  STRUCT_CASES_TAC (ISPEC `sstack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `t:((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `t':((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `t:((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `full_read_bitmap (bs:(A word)list) (h''':(A)word_loc)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASES_ON `abs_stack (bs:(A word)list) (wstack:((A)stack_frame)list)
              (DROP f' (t':((A)word_loc)list)) lens` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `a':(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list` THEN
  REWRITE_TAC[ARITH_RULE `f' + 4 = (((f' + 1) + 1) + 1) + 1`; W2SP2AUX_DROP_ADD1_CONS] THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC (SUC 0)`; EL; HD; TL] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP abs_stack_IMP_LENGTH) THEN STRIP_TAC THEN
  UNDISCH_TAC `stack_rel_aux k len (CONS (StackFrame n l0 l (SOME (whandler',b,c)))
                 (wstack:((A)stack_frame)list))
                 (CONS (SOME (h':(A)word_loc,h''),a,TAKE f' (t':((A)word_loc)list)) a')` THEN
  REWRITE_TAC[stack_rel_aux_def] THEN ASM_SIMP_TAC[option_INJ]);;

(* HOL4 line 5398 *)
let LAST_GENLIST_evens = prove
 (`!n. ~(n = 0)
       ==> let reg = LAST (list_of_seq (\x. 2 * (x + 1)) n) in
           ~(reg = 0) /\ EVEN reg`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `~(list_of_seq (\x. 2 * (x + 1)) n = [])` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:num list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LAST_EL; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
               ARITH_RULE `~(n = 0) ==> n - 1 < n`] THEN
  REWRITE_TAC[EVEN_DOUBLE] THEN ARITH_TAC);;

(* HOL4 line 5409 *)
let stack_rel_cons_LEN_NONE = prove
 (`!k whandler n l0 l (wstack:((A)stack_frame)list) (shandler:((B)word_loc)option) sstack len
     (bs:(A word)list) f' lens.
     word_to_stackProof_stack_rel k whandler (CONS (StackFrame n l0 l NONE) wstack)
       shandler sstack len bs (CONS f' lens)
     ==> f' + 1 <= LENGTH sstack`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN
    `stk:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
    (MP_TAC o CONJUNCT1))) THEN
  STRUCT_CASES_TAC (ISPEC `sstack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; option_DISTINCT; LENGTH] THEN
  CASES_ON `full_read_bitmap (bs:(A word)list) (h:(A)word_loc)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC);;

(* HOL4 line 5417 *)
let stack_rel_cons_LEN_SOME = prove
 (`!k whandler n l0 l a b c (wstack:((A)stack_frame)list) (shandler:((B)word_loc)option)
     sstack len
     (bs:(A word)list) f' lens.
     word_to_stackProof_stack_rel k whandler
       (CONS (StackFrame n l0 l (SOME (a,b,c))) wstack) shandler sstack len bs (CONS f' lens)
     ==> f' + 4 <= LENGTH sstack`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN
    `stk:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
    (MP_TAC o CONJUNCT1))) THEN
  STRUCT_CASES_TAC (ISPEC `sstack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; option_DISTINCT; LENGTH] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `t:((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT; LENGTH] THEN
  STRUCT_CASES_TAC (ISPEC `t':((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT; LENGTH] THEN
  STRUCT_CASES_TAC (ISPEC `t:((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT; LENGTH] THEN
  CASES_ON `full_read_bitmap (bs:(A word)list) (h''':(A)word_loc)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC);;

(* HOL4 line 5425 *)
let stack_rel_cons_locals_size = prove
 (`!k whandler n l0 l opt (t'':((A)stack_frame)list) (shandler:((B)word_loc)option)
     rest_of_stack len
     (bitmaps:(A word)list) f' lens.
     word_to_stackProof_stack_rel k whandler (CONS (StackFrame n l0 l opt) t'')
       shandler rest_of_stack len bitmaps (CONS f' lens)
     ==> the (f' + 1) n = f' + 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN
    `stk:(((A)word_loc#(A)word_loc)option#bool list#((A)word_loc)list)list`
    (fun th -> MP_TAC (CONJUNCT2 (CONJUNCT2 th)) THEN MP_TAC (CONJUNCT1 th)))) THEN
  STRUCT_CASES_TAC (ISPEC `rest_of_stack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `opt:(num#num#num)option` (cases "option")) THEN
  REWRITE_TAC[abs_stack_def] THENL
   [CASES_ON `full_read_bitmap (bitmaps:(A word)list) (h:(A)word_loc)` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CASES_ON `abs_stack (bitmaps:(A word)list) (t'':((A)stack_frame)list)
                (DROP f' (t:((A)word_loc)list)) lens` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[stack_rel_aux_def] THEN ASM_SIMP_TAC[LENGTH_TAKE; GSYM NOT_LT];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `t:((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `t':((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `t:((A)word_loc)list` list_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `full_read_bitmap (bitmaps:(A word)list) (h''':(A)word_loc)` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASES_ON `abs_stack (bitmaps:(A word)list) (t'':((A)stack_frame)list)
              (DROP f' (t':((A)word_loc)list)) lens` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `a:num#num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `q:num#num` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `q:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num` (X_CHOOSE_THEN `q2:num` SUBST1_TAC)) THEN
  REWRITE_TAC[stack_rel_aux_def] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; GSYM NOT_LT]);;

(* HOL4 line 5439 (HOL4's variables A and B are a and b here) *)
let IS_SOME_OPTION_MAP2_EQ = prove
 (`!(f:A->B->C) a b. IS_SOME (OPTION_MAP2 f a b) <=> IS_SOME a /\ IS_SOME b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPTION_MAP2_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF]);;

(* HOL4 line 5446 *)
let DROP_SUB = prove
 (`!a (ls:A list) b.
     a <= LENGTH ls /\ b <= a
     ==> DROP (a - b) ls = APPEND (DROP (a - b) (TAKE a ls)) (DROP a ls)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(ISPECL [`a:num`; `ls:A list`] TAKE_DROP)] THEN
  MP_TAC(ISPECL [`a - b`; `TAKE a (ls:A list)`] DROP_APPEND1) THEN
  ASM_SIMP_TAC[LENGTH_TAKE] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

(* HOL4 line 5456 *)
let DROP_SUB2 = prove
 (`!a (ls:A list) b.
     b <= a /\ a = LENGTH ls ==> ?rest. DROP (a - b) ls = rest /\ LENGTH rest = b`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `DROP (a - b) (ls:A list)` THEN
  ASM_REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC);;

(* W2SP2AUX: run the first basic instruction of a stackLang Seq (an OCaml   *)
(* helper tactic for the PushHandler code)                                   *)
let w2sp2aux_basic_clauses =
  [w2sp2aux_seval "StackAlloc"; w2sp2aux_seval "stack_Inst"; w2sp2aux_seval "StackStore";
   w2sp2aux_seval "stack_LocValue"; w2sp2aux_seval "stack_Get";
   w2sp2aux_seval "StackGetSize"; w2sp2aux_seval "stack_Set"; w2sp2aux_seval "stack_Skip"];;

let w2sp2aux_basic_tac =
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) w2sp2aux_basic_clauses THEN
  REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[stack_assign_def; stack_word_exp_def] THEN
  ASM_REWRITE_TAC[stack_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_LUPDATE;
                  stack_get_var_def; stack_set_var_def; stack_set_store_def; ADD_0] THEN
  CASE_REWRITE_TAC[];;

let w2sp2aux_seq_step_tac =
  ONCE_REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN w2sp2aux_basic_tac;;

(* W2SP2AUX: the stack code of a PushHandler *)
let W2SP2AUX_PushHandler_eval = prove
 (`!(t:(A,C,FFI)stack_state) l1 l2 k f f' h.
     stack_state_use_stack t /\ stack_state_use_store t /\
     3 <= stack_state_stack_space t /\
     stack_state_stack_space t <= LENGTH (stack_state_stack t) /\
     FLOOKUP (stack_state_store t) Handler = SOME h /\
     loc_check (stack_state_code t) (l1,l2)
     ==> stack_evaluate (PushHandler F l1 l2 (k,f:num,f':num),t) =
         (NONE,
          stack_state_stack_space_fupd (K (stack_state_stack_space t - 3))
            (stack_state_regs_fupd
               (K (stack_state_regs t |+
                     (k,wl_Word (word (stack_state_stack_space t - 3)))))
            (stack_state_stack_fupd
               (K (LUPDATE h (stack_state_stack_space t - 1)
                    (LUPDATE (wl_Loc l1 l2) (stack_state_stack_space t - 2)
                    (LUPDATE (wl_Word (word 1)) (stack_state_stack_space t - 3)
                       (stack_state_stack t)))))
            (stack_state_store_fupd
               (K (stack_state_store t |+
                     (Handler,wl_Word (word (stack_state_stack_space t - 3)))))
            t))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~(stack_state_stack_space (t:(A,C,FFI)stack_state) < 3) /\
    ~(LENGTH (stack_state_stack t) <= stack_state_stack_space t - 3) /\
    ~(LENGTH (stack_state_stack t) <= stack_state_stack_space t - 2) /\
    ~(LENGTH (stack_state_stack t) <= stack_state_stack_space t - 1) /\
    stack_state_stack_space t - 3 + 1 = stack_state_stack_space t - 2 /\
    stack_state_stack_space t - 3 + 2 = stack_state_stack_space t - 1`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PushHandler_F] THEN
  REPLICATE_TAC 9 w2sp2aux_seq_step_tac THEN
  w2sp2aux_basic_tac THEN
  REWRITE_TAC[stack_state_component_equality; stack_state_INFO.ri_accfupds; K_THM;
              FUPDATE_EQ]);;

(* W2SP2AUX: the stack below a pushed handler frame *)
let W2SP2AUX_DROP_LUPDATE3 = prove
 (`!sp (st:A list) x y z.
     3 <= sp /\ sp <= LENGTH st
     ==> DROP (sp - 3) (LUPDATE z (sp - 1) (LUPDATE y (sp - 2) (LUPDATE x (sp - 3) st))) =
         CONS x (CONS y (CONS z (DROP sp st)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[misc_DROP_LUPDATE; LE_REFL;
               ARITH_RULE `3 <= sp ==> sp - 3 <= sp - 1 /\ sp - 3 <= sp - 2`] THEN
  ASM_SIMP_TAC[SUB_REFL;
               ARITH_RULE `3 <= sp ==> (sp - 1) - (sp - 3) = 2 /\ (sp - 2) - (sp - 3) = 1`] THEN
  MP_TAC(ISPECL [`st:A list`; `sp - 3`] DROP_EL_CONS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`st:A list`; `sp - 3 + 1`] DROP_EL_CONS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`st:A list`; `(sp - 3 + 1) + 1`] DROP_EL_CONS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `((sp - 3 + 1) + 1) + 1 = sp` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LUPDATE_compute] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LUPDATE_compute] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LUPDATE_compute]);;

(* W2SP2AUX: the stack size relation after a PushHandler *)
let W2SP2AUX_stack_size_rel_handler = prove
 (`!lim mx ls l0 l (stk:((A)stack_frame)list) (hh:num#num#num)
    (st:((A)word_loc)list) (st':((A)word_loc)list) sp.
     stack_size_rel 0 (SOME 0) lim
       (OPTION_MAP2 MAX mx (wl_stack_size (CONS (StackFrame ls l0 l NONE) stk)))
       (CONS (StackFrame ls l0 l NONE) stk) st sp 0 /\
     LENGTH st' = LENGTH st /\ 3 <= sp /\ sp <= LENGTH st
     ==> stack_size_rel 0 (SOME 0) lim
           (OPTION_MAP2 MAX mx (wl_stack_size (CONS (StackFrame ls l0 l (SOME hh)) stk)))
           (CONS (StackFrame ls l0 l (SOME hh)) stk) st' (sp - 3) 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_size_rel_def; stack_size_eq] THEN
  CASES_ON `ls:num option` THEN CASES_ON `wl_stack_size (stk:((A)stack_frame)list)` THEN
  CASES_ON `mx:num option` THEN
  REWRITE_TAC[OPTION_MAP_DEF; OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF; option_DISTINCT;
              option_INJ; FORALL_UNWIND_THM1; UNWIND_THM1] THEN
  REWRITE_TAC[MAX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* W2SP2AUX: the stack relation after a PushHandler *)
let W2SP2AUX_stack_rel_handler = prove
 (`!k hd (stk:((A)stack_frame)list) ls l0 l a b (h:(A)word_loc) (rest:((A)word_loc)list)
    len (bitmaps:(A word)list) lens.
     word_to_stackProof_stack_rel k hd (CONS (StackFrame ls l0 l NONE) stk) (SOME h)
       rest len bitmaps lens
     ==> word_to_stackProof_stack_rel k (LENGTH stk)
           (CONS (StackFrame ls l0 l (SOME (hd,a,b))) stk)
           (SOME (wl_Word (word (len - (LENGTH rest + 3)):A word)))
           (CONS (wl_Word (word 1)) (CONS (wl_Loc a b) (CONS h rest))) len bitmaps lens`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_stack_rel_def; ALL; sorted_env_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "abs_stack")) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `w0:(A)word_loc`
    (X_CHOOSE_THEN `rest0:((A)word_loc)list` SUBST1_TAC))
    (ISPEC `rest:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; option_DISTINCT] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `len0:num`
    (X_CHOOSE_THEN `lens0:num list` SUBST1_TAC))
    (ISPEC `lens:num list` list_CASES) THEN
  REWRITE_TAC[abs_stack_def; option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `full_read_bitmap (bitmaps:(A word)list) (w0:(A)word_loc)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `bits:bool list` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `LENGTH (bits:bool list) = len0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `LENGTH (rest0:((A)word_loc)list) < len0` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `abs_stack (bitmaps:(A word)list) (stk:((A)stack_frame)list)
                  (DROP len0 (rest0:((A)word_loc)list)) lens0` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN
    `ys:(((A)word_loc#(A)word_loc)option#(bool)list#((A)word_loc)list)list`
    ASSUME_TAC)) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `CONS (SOME (wl_Loc a b,h:(A)word_loc),bits,TAKE len0 (rest0:((A)word_loc)list))
                (ys:(((A)word_loc#(A)word_loc)option#(bool)list#((A)word_loc)list)list)` THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP abs_stack_IMP_LENGTH o
    check (w2sp2aux_has_const "abs_stack")) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP abs_stack_to_stack_LENGTH o
    check (w2sp2aux_has_const "abs_stack")) THEN
  CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
    MP_TAC(ISPEC `CONS (SOME (wl_Loc a b,h:(A)word_loc),bits,TAKE len0 (rest0:((A)word_loc)list))
                    (ys:(((A)word_loc#(A)word_loc)option#(bool)list#((A)word_loc)list)list)`
           LASTN_LENGTH_ID) THEN
    ASM_REWRITE_TAC[LENGTH; ADD1] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `len0 <= LENGTH (rest0:((A)word_loc)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[handler_val_def; LENGTH_TAKE; LENGTH_DROP] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[LENGTH; LENGTH_DROP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `stack_rel_aux k len (CONS (StackFrame ls l0 l NONE) (stk:((A)stack_frame)list))
                 (CONS (NONE,bits,TAKE len0 (rest0:((A)word_loc)list))
                    (ys:(((A)word_loc#(A)word_loc)option#(bool)list#((A)word_loc)list)list))` THEN
  REWRITE_TAC[stack_rel_aux_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
                                w2sp2aux_has_const "handler_val" th)) THEN
  SUBGOAL_THEN `LENGTH (CONS (StackFrame ls l0 l NONE) (stk:((A)stack_frame)list)) - (hd + 1) =
                SUC (LENGTH stk - (hd + 1))` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EL; TL; LENGTH] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hd + 1`;
    `ys:(((A)word_loc#(A)word_loc)option#(bool)list#((A)word_loc)list)list`] LASTN_CONS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; option_INJ]));;

(* W2SP2AUX: the state relation after a PushHandler *)
let W2SP2AUX_PushHandler_state_rel = prove
 (`!ac k (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) x' f' lens x''0 x''1 x''2
    x''3 h.
     3 <= stack_state_stack_space t /\
     word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env x' (NONE:(num#(A)wl_prog#num#num)option) s)))
       t (CONS f' lens) 0 /\
     FLOOKUP (stack_state_store t) Handler = SOME h
     ==> word_to_stackProof_state_rel ac k 0 0
           (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
              (wl_push_env x' (SOME (x''0,x''1:(A)wl_prog,x''2,x''3)) s)))
           (stack_state_stack_space_fupd (K (stack_state_stack_space t - 3))
            (stack_state_regs_fupd
               (K (stack_state_regs t |+
                     (k,wl_Word (word (stack_state_stack_space t - 3)))))
            (stack_state_stack_fupd
               (K (LUPDATE h (stack_state_stack_space t - 1)
                    (LUPDATE (wl_Loc x''2 x''3) (stack_state_stack_space t - 2)
                    (LUPDATE (wl_Word (word 1)) (stack_state_stack_space t - 3)
                       (stack_state_stack t)))))
            (stack_state_store_fupd
               (K (stack_state_store t |+
                     (Handler,wl_Word (word (stack_state_stack_space t - 3)))))
            t))))
           (CONS f' lens) 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `env_to_list (SND (x':((A)word_loc)spt#((A)word_loc)spt))
                  (wl_state_permute (s:(A,num#C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(num#(A)word_loc)list`
    (X_CHOOSE_THEN `perm:num->num->num` ASSUME_TAC)) THEN
  REWRITE_TAC[wl_push_env_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; stack_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stack_state_stack_space (t:(A,C,FFI)stack_state) <=
                LENGTH (stack_state_stack t)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DOMSUB_FUPDATE; FDOM_FUPDATE; IN_INSERT; LENGTH_LUPDATE; lookup_def;
              option_DISTINCT; FLOOKUP_UPDATE; ADD_0; DROP_0] THEN
  ASM_SIMP_TAC[W2SP2AUX_DROP_LUPDATE3] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC W2SP2AUX_stack_size_rel_handler THEN
    EXISTS_TAC `stack_state_stack (t:(A,C,FFI)stack_state)` THEN
    ASM_REWRITE_TAC[LENGTH_LUPDATE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "word_to_stackProof_stack_rel")) THEN
  ASM_REWRITE_TAC[ADD_0; DROP_0] THEN
  DISCH_THEN(MP_TAC o SPECL [`x''2:num`; `x''3:num`] o
             MATCH_MP W2SP2AUX_stack_rel_handler) THEN
  SUBGOAL_THEN `LENGTH (stack_state_stack (t:(A,C,FFI)stack_state)) -
                (LENGTH (DROP (stack_state_stack_space t) (stack_state_stack t)) + 3) =
                stack_state_stack_space t - 3` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* HOL4 line 5468 *)
let evaluate_PushHandler = prove
 (`!(t:(A,C,FFI)stack_state) ac k x' (s:(A,num#C,FFI)wl_state) f' lens x''2 x''3 f
     x''0 x''1.
     3 <= stack_state_stack_space t /\
     word_to_stackProof_state_rel ac k 0 0
       (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
          (wl_push_env x' (NONE:(num#(A)wl_prog#num#num)option) s)))
       t (CONS f' lens) 0 /\
     loc_check (stack_state_code t) (x''2,x''3)
     ==> ?t':(A,C,FFI)stack_state.
           stack_evaluate (PushHandler F (x''2:num) (x''3:num) (k,f:num,f'),t) =
             (NONE,t') /\
           t' = stack_state_stack_space_fupd (K (stack_state_stack_space t'))
                  (stack_state_regs_fupd (K (stack_state_regs t'))
                     (stack_state_stack_fupd (K (stack_state_stack t'))
                        (stack_state_store_fupd (K (stack_state_store t')) t))) /\
           (!n. n < LENGTH (stack_state_stack t) - stack_state_stack_space t
                ==> EL n (DROP (stack_state_stack_space t) (stack_state_stack t)) =
                    EL (n + 3) (DROP (stack_state_stack_space t') (stack_state_stack t'))) /\
           (!i. ~(i = k) ==> stack_get_var i t' = stack_get_var i t) /\
           stack_state_stack_space t' + 3 = stack_state_stack_space t /\
           LENGTH (stack_state_stack t') = LENGTH (stack_state_stack t) /\
           word_to_stackProof_state_rel ac k 0 0
             (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
                (wl_push_env x' (SOME (x''0,x''1:(A)wl_prog,x''2,x''3)) s)))
             t' (CONS f' lens) 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stack_state_use_stack (t:(A,C,FFI)stack_state) /\ stack_state_use_store t /\
                stack_state_stack_space t <= LENGTH (stack_state_stack t) /\
                ?h. FLOOKUP (stack_state_store t) Handler = SOME h` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (w2sp2aux_has_const "word_to_stackProof_state_rel")) THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FLOOKUP_DEF] THEN CONJ_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(A,C,FFI)stack_state`; `x''2:num`; `x''3:num`; `k:num`; `f:num`;
                 `f':num`; `h:(A)word_loc`] W2SP2AUX_PushHandler_eval) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> EXISTS_TAC (rand(rhs(concl th))) THEN REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[stack_state_component_equality; stack_state_INFO.ri_accfupds; K_THM];
    REWRITE_TAC[stack_state_INFO.ri_accfupds; K_THM] THEN
    ASM_SIMP_TAC[W2SP2AUX_DROP_LUPDATE3] THEN
    REWRITE_TAC[ARITH_RULE `!n. n + 3 = SUC (SUC (SUC n))`; EL; TL];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[stack_get_var_def; stack_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[stack_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
    REWRITE_TAC[stack_state_INFO.ri_accfupds; K_THM; LENGTH_LUPDATE];
    MATCH_MP_TAC W2SP2AUX_PushHandler_state_rel THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5542 *)
let evaluate_PushHandler_clock = prove
 (`!(t:(A,C,FFI)stack_state) a b k f f' clk.
     stack_evaluate (PushHandler F a b (k,f:num,f':num),stack_state_clock_fupd (K clk) t) =
     (FST (stack_evaluate (PushHandler F a b (k,f:num,f':num),t)),
      stack_state_clock_fupd (K clk)
        (SND (stack_evaluate (PushHandler F a b (k,f:num,f':num),t))))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`clk:num`,`clk:num`) THEN
  SPEC_TAC(`t:(A,C,FFI)stack_state`,`t:(A,C,FFI)stack_state`) THEN
  REWRITE_TAC[PushHandler_F] THEN
  REPEAT(MATCH_MP_TAC W2SP2AUX_clock_Seq THEN CONJ_TAC THENL
           [REWRITE_TAC[W2SP2AUX_clock_basic]; ALL_TAC]) THEN
  REWRITE_TAC[W2SP2AUX_clock_basic]);;

(* HOL4 line 5554 *)
let evaluate_PopHandler_clock = prove
 (`!(t:(A,C,FFI)stack_state) k f f' clk.
     let prog = PopHandler F (k,f:num,f':num) stack_Skip in
     stack_evaluate (prog,stack_state_clock_fupd (K clk) t) =
     (FST (stack_evaluate (prog,t)),
      stack_state_clock_fupd (K clk) (SND (stack_evaluate (prog,t))))`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN SPEC_TAC(`clk:num`,`clk:num`) THEN
  SPEC_TAC(`t:(A,C,FFI)stack_state`,`t:(A,C,FFI)stack_state`) THEN
  REWRITE_TAC[PopHandler_def] THEN
  REPEAT(MATCH_MP_TAC W2SP2AUX_clock_Seq THEN CONJ_TAC THENL
           [REWRITE_TAC[W2SP2AUX_clock_basic]; ALL_TAC]) THEN
  REWRITE_TAC[W2SP2AUX_clock_basic]);;

(* HOL4 line 5566 *)
let evaluate_PopHandler_seq = prove
 (`!prog (t:(A,C,FFI)stack_state) k (f:B) (f':C).
     stack_evaluate (PopHandler F (k,f,f') prog,t) =
     stack_evaluate (stack_Seq (PopHandler F (k,f,f') stack_Skip) prog,t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PopHandler_def; W2SP2AUX_evaluate_Seq_assoc] THEN
  REPEAT(MATCH_MP_TAC W2SP2AUX_evaluate_Seq_cong2 THEN GEN_TAC THEN
         REWRITE_TAC[W2SP2AUX_evaluate_Seq_assoc]) THEN
  REWRITE_TAC[W2SP2AUX_evaluate_Skip_Seq]);;

(* HOL4 line 5576 *)
let ALL_DISTINCT_MEM_toAList_fromAList = prove
 (`!(ls:(num#A)list) x.
     ALL_DISTINCT (MAP FST ls) ==> (MEM x (toAList (fromAList ls)) <=> MEM x ls)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; MEM_toAList; lookup_fromAList] THEN
  MESON_TAC[ALOOKUP_MEM; ALOOKUP_ALL_DISTINCT_MEM]);;

(* HOL4 line 5586 *)
let state_rel_code_domain = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra
     ==> domain (wl_state_code s) SUBSET domain (stack_state_code t)`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* HOL4 line 5594 *)
let get_labels_wStackLoad = prove
 (`!xs (p:(A)stack_prog). stack_get_labels (wStackLoad xs p) = stack_get_labels p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wStackLoad_def] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[wStackLoad_def; stack_get_labels_def; UNION_EMPTY]);;

(* HOL4 line 5601 *)
let loc_check_SUBSET = prove
 (`!(s:((A)stack_prog)spt) t. subspt s t ==> loc_check s SUBSET loc_check t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subspt_def; domain_lookup] THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[loc_check_def] THEN
  MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup]) THEN REWRITE_TAC[domain_lookup] THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`n:num`; `e:(A)stack_prog`] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 5609 *)
let MAP_FST_compile_word_to_stack = prove
 (`!(ac:(A)asm_config) perf k ps bm ps' bm'.
     compile_word_to_stack ac perf k ps bm = (ps',bm') ==> MAP FST ps' = MAP FST ps`,
  MATCH_MP_TAC compile_word_to_stack_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN REWRITE_TAC[MAP];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_word_to_stack_def] THEN
  REPEAT PAIRARG_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
  REWRITE_TAC[MAP; FST; CONS_11] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`prog:(A)stack_prog`; `f:num`;
                                `bitmaps':(A word)app_list#num`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(fs:num list,bitmaps'':(A word)app_list#num)` THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: insert_bitmap, wLive and comp add the same number to the      *)
(* bitmap index and to the length of the bitmaps                           *)
let W2SP2AUX_insert_bitmap_LENGTH = prove
 (`!(ws:A list) bs bs' i.
     insert_bitmap ws bs = (bs',i)
     ==> LENGTH (append (FST bs')) = LENGTH (append (FST bs)) + (SND bs' - SND bs) /\
         SND bs <= SND bs'`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; insert_bitmap_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    (SUBST1_TAC o SYM)) (K ALL_TAC)) THEN
  REWRITE_TAC[FST; SND; append_thm; LENGTH_APPEND] THEN ARITH_TAC);;

let W2SP2AUX_wLive_LENGTH = prove
 (`!a (bs:(A word)app_list#num) c (q:(A)stack_prog) bs'.
     wLive a bs c = (q,bs')
     ==> LENGTH (append (FST bs')) = LENGTH (append (FST bs)) + (SND bs' - SND bs) /\
         SND bs <= SND bs'`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `c:num#num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ff:num#num` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ff:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `f':num` SUBST1_TAC)) THEN
  REWRITE_TAC[wLive_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN ARITH_TAC;
    ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  ASM_MESON_TAC[W2SP2AUX_insert_bitmap_LENGTH]);;

let W2SP2AUX_comp_LENGTH = prove
 (`!(ac:(A)asm_config) perf c1 bs r q1 bs'.
     word_to_stack_comp ac perf c1 bs r = (q1,bs')
     ==> LENGTH (append (FST bs')) = LENGTH (append (FST bs)) + (SND bs' - SND bs) /\
         SND bs <= SND bs'`,
  MATCH_MP_TAC word_to_stack_comp_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `perf:bool` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    w2sp2aux_has_const "word_to_stack_comp" th && is_pair(rhs(concl th)))) THEN
  ONCE_REWRITE_TAC[word_to_stack_comp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  REPEAT(PAIRARG_TAC ORELSE CASE_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th g -> try CONJUNCTS_THEN2 (K ALL_TAC) (SUBST_ALL_TAC o SYM) th g
                         with Failure _ -> ASSUME_TAC th g) THEN
  TRY(ARITH_TAC THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ] o CAKE_SIMP_RULE[]) THEN
  MP_TAC W2SP2AUX_wLive_LENGTH THEN
  MP_TAC(INST_TYPE [`:A word`,`:A`] W2SP2AUX_insert_bitmap_LENGTH) THEN
  REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun eq ->
    MP_TAC(MATCH_MP ih eq))) THEN STRIP_TAC) THEN
  ASM_ARITH_TAC);;

(* W2SP2AUX: compile_prog and compile_word_to_stack add the same number to *)
(* the bitmap index and to the length of the bitmaps                       *)
let W2SP2AUX_compile_prog_LENGTH = prove
 (`!(ac:(A)asm_config) perf prog arg reg bs prog' fs' bs'.
     word_to_stack_compile_prog ac perf prog arg reg bs = (prog',fs',bs')
     ==> LENGTH (append (FST bs')) = LENGTH (append (FST bs)) + (SND bs' - SND bs) /\
         SND bs <= SND bs'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP2AUX_comp_LENGTH o
    check (w2sp2aux_has_const "word_to_stack_comp")) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_var(rhs(concl th)) &&
    fst(dest_var(rhs(concl th))) = "bs'")) THEN
  REWRITE_TAC[]);;

let W2SP2AUX_compile_word_to_stack_LENGTH = prove
 (`!code (ac:(A)asm_config) perf k bs progs fs bs'.
     compile_word_to_stack ac perf k code bs = (progs,fs,bs')
     ==> LENGTH (append (FST bs')) = LENGTH (append (FST bs)) + (SND bs' - SND bs) /\
         SND bs <= SND bs'`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2 o CONJUNCT2) THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `n:num`; `p:(A)wl_prog`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_word_to_stack_def] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_var(lhs(concl th)) && is_pair(rhs(concl th))
                          then SUBST_ALL_TAC th else failwith "") THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP2AUX_compile_prog_LENGTH o
    check (w2sp2aux_has_const "word_to_stack_compile_prog")) THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "compile_word_to_stack" o
    (fun th -> if is_forall(concl th) then failwith "" else th))) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[FST; SND] THEN
  ARITH_TAC);;

(* HOL4 line 5618 *)
let wLive_LENGTH = prove
 (`!a (bs:(A word)app_list#num) c (q:(A)stack_prog) bs'.
     wLive a bs c = (q,bs') /\
     LENGTH (append (FST bs)) <= SND bs
     ==> LENGTH (append (FST bs')) <= SND bs' /\
         SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append (FST bs'))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `c:num#num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ff:num#num` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ff:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `f':num` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `bs:(A word)app_list#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(A word)app_list` (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  REWRITE_TAC[wLive_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[insert_bitmap_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) ASSUME_TAC) THEN
  REWRITE_TAC[FST; SND; append_thm; LENGTH_APPEND] THEN ASM_ARITH_TAC);;

(* HOL4 line 5636 *)
let comp_IMP_LENGTH = prove
 (`!(ac:(A)asm_config) perf c1 bs r q1 bs'.
     word_to_stack_comp ac perf c1 bs r = (q1,bs') /\
     LENGTH (append (FST bs)) <= SND bs
     ==> LENGTH (append (FST bs')) <= SND bs' /\
         SND bs - LENGTH (append (FST bs)) = SND bs' - LENGTH (append (FST bs'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP W2SP2AUX_comp_LENGTH) ASSUME_TAC) THEN
  ASM_ARITH_TAC);;

(* HOL4 line 5652 *)
let compile_prog_LENGTH = prove
 (`!(ac:(A)asm_config) perf prog arg reg bm i prog' fs' bm' i'.
     word_to_stack_compile_prog ac perf prog arg reg (bm,i) = (prog',fs',bm',i') /\
     LENGTH (append bm) <= i
     ==> LENGTH (append bm') <= i' /\
         i - LENGTH (append bm) = i' - LENGTH (append bm')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP W2SP2AUX_comp_LENGTH o
    check (w2sp2aux_has_const "word_to_stack_comp")) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_pair(rhs(concl th)))) THEN
  REWRITE_TAC[FST; SND] THEN
  UNDISCH_TAC `LENGTH (append (bm:(A word)app_list)) <= i` THEN ARITH_TAC);;

(* HOL4 line 5664 *)
let compile_word_to_stack_IMP_LENGTH = prove
 (`!code k bm i progs fs bm' i' (ac:(A)asm_config) perf.
     compile_word_to_stack ac perf k code (bm,i) = (progs,fs,bm',i') /\
     LENGTH (append bm) <= i
     ==> LENGTH (append bm') <= i' /\
         i - LENGTH (append bm) = i' - LENGTH (append bm')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP W2SP2AUX_compile_word_to_stack_LENGTH)
    MP_TAC) THEN
  REWRITE_TAC[FST; SND] THEN ARITH_TAC);;

(* HOL4 line 5682 *)
let compile_word_to_stack_bitmaps = prove
 (CASE_TERM `!(c:(A)asm_config) p bitmaps c2 prog1.
     word_to_stack_compile c F p = (bitmaps,c2,prog1)
     ==> (match bitmaps with [] -> F | CONS h v1 -> word 4 = h) /\
         word_to_stack_config_bitmaps_length c2 = LENGTH bitmaps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  REPEAT PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    fst(dest_var(rhs(concl th))) = "bitmaps")) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    fst(dest_var(rhs(concl th))) = "c2")) THEN
  SIMP[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP W2SP2AUX_compile_word_to_stack_LENGTH o
    check (w2sp2aux_has_const "compile_word_to_stack")) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP compile_word_to_stack_isPREFIX o
    check (w2sp2aux_has_const "compile_word_to_stack")) THEN
  REWRITE_TAC[FST; SND; append_thm; LENGTH; IS_PREFIX_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(A word)list` (fun th -> REWRITE_TAC[th])) THEN
  REWRITE_TAC[APPEND; LENGTH] THEN CASE_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 5692 *)
let compile_word_to_stack_IMP_ALOOKUP = prove
 (`!code k bs i progs fs bs' i' n arg_count word_prog (x:(A word)list)
     (ac:(A)asm_config) perf.
     compile_word_to_stack ac perf k code (bs,i) = (progs,fs,bs',i') /\
     ALOOKUP code n = SOME (arg_count,word_prog) /\
     LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH x /\
     isPREFIX (append bs') (DROP (i - LENGTH (append bs)) x)
     ==> ?bs i bs2 i2 f stack_prog.
           word_to_stack_compile_prog ac perf word_prog arg_count k (bs,i) =
             (stack_prog,f,(bs2,i2)) /\
           LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH x /\
           isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) x) /\
           ALOOKUP progs n = SOME stack_prog`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_def; option_DISTINCT] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`h0:num`; `h1:num`; `h2:(A)wl_prog`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_word_to_stack_def; ALOOKUP_def] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    fst(dest_var(rhs(concl th))) = "progs")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
    fst(dest_var(lhs(concl th))) = "bitmaps'")) THEN
  MP_TAC(ISPEC `bitmaps:(A word)app_list#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:(A word)app_list` (X_CHOOSE_THEN `j1:num` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP compile_word_to_stack_isPREFIX o
    check (fun th -> w2sp2aux_has_const "compile_word_to_stack" th &&
                     not (is_forall(concl th)))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP W2SP2AUX_compile_prog_LENGTH o
    check (w2sp2aux_has_const "word_to_stack_compile_prog")) THEN
  REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h0 = (n:num)` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl)) THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`bs:(A word)app_list`; `i:num`; `b1:(A word)app_list`;
                          `j1:num`; `f:num`; `prog:(A)stack_prog`] THEN
    ASM_REWRITE_TAC[ALOOKUP_def] THEN MATCH_MP_TAC isPREFIX_TRANS THEN
    EXISTS_TAC `append (bs':(A word)app_list)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `b1:(A word)app_list`; `j1:num`;
    `progs':(num#(A)stack_prog)list`; `fs':num list`; `bs':(A word)app_list`; `i':num`;
    `n:num`; `arg_count:num`; `word_prog:(A)wl_prog`; `x:(A word)list`;
    `ac:(A)asm_config`; `perf:bool`]) THEN
  SUBGOAL_THEN `j1 - LENGTH (append (b1:(A word)app_list)) =
                i - LENGTH (append (bs:(A word)app_list))`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ALOOKUP_def] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MESON_TAC[]);;

(* HOL4 line 5719: val goal = ... (an ML term, here an OCaml one; ac is  *)
(* free in it, as in HOL4).  HOL4 t1.ffi.io_events <<= s1.ffi.io_events.     *)
let word_to_stackProof_goal = CASE_TERM
 `\(prog:(A)wl_prog,s:(A,num#C,FFI)wl_state).
     !k f f' res s1 (t:(A,C,FFI)stack_state) bs n bs' n' sprog lens.
       wl_evaluate (prog,s) = (res,s1) /\ ~(res = SOME wl_Error) /\
       word_to_stackProof_state_rel (ac:(A)asm_config) k f f' s t lens 0 /\
       post_alloc_conventions k prog /\
       flat_exp_conventions prog /\
       word_to_stack_comp ac F prog (bs,n) (k,f,f') = (sprog,(bs',n')) /\
       LENGTH (append bs) <= n /\
       n - LENGTH (append bs) <= LENGTH (stack_state_bitmaps t) /\
       isPREFIX (append bs') (DROP (n - LENGTH (append bs)) (stack_state_bitmaps t)) /\
       stack_get_labels sprog SUBSET loc_check (stack_state_code t) /\
       max_var prog < 2 * f' + 2 * k
       ==> ?ck (t1:(A,C,FFI)stack_state) res1.
             stack_evaluate (sprog,stack_state_clock_fupd (K (stack_state_clock t + ck)) t) =
               (res1,t1) /\
             if ~(OPTION_MAP compile_result res = res1)
             then res1 = SOME (stackSem_Halt (wl_Word (word 2))) /\
                  isPREFIX (ffi_state_io_events (stack_state_ffi t1))
                    (ffi_state_io_events (wl_state_ffi s1)) /\
                  the (wl_state_stack_limit s1 + 1) (wl_state_stack_max s1) >
                    wl_state_stack_limit s1
             else
               match res with
                 NONE -> word_to_stackProof_state_rel ac k f f' s1 t1 lens 0
               | SOME (wl_Result _ ys) ->
                   word_to_stackProof_state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
                   (!i. i < LENGTH ys
                        ==> if i + 1 < k
                            then FLOOKUP (stack_state_regs t1) (i + 1) = SOME (EL i ys)
                            else oEL (LENGTH ys - (i + 1)) (DROP (stack_state_stack_space t1)
                                                (stack_state_stack t1)) = SOME (EL i ys))
               | SOME (wl_Exception _ y) ->
                   ?l0 l.
                     word_to_stackProof_state_rel ac k 0 0 (push_locals l0 l s1) t1
                       (LASTN (wl_state_handler s + 1) lens) 0 /\
                     wl_state_locals s1 = union (fromAList l) (fromAList l0) /\
                     FLOOKUP (stack_state_regs t1) 1 = SOME y
               | SOME (wordSem_Break _) -> word_to_stackProof_state_rel ac k f f' s1 t1 lens 0
               | SOME (wordSem_Continue _) ->
                   word_to_stackProof_state_rel ac k f f' s1 t1 lens 0
               | SOME _ -> wl_state_ffi s1 = stack_state_ffi t1 /\
                           wl_state_clock s1 = stack_state_clock t1`;;

(* HOL4 line 5754: val ind_thm = evaluate_ind |> ISPEC goal |> GEN_BETA_RULE *)
let word_to_stackProof_ind_thm =
  CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (ISPEC word_to_stackProof_goal wl_evaluate_ind);;

(* HOL4 line 5756: Theorem comp_correct: ^(ind_thm |> concl |> rand), proved *)
(* by match_mp_tac ind_thm, with one suspended case per constructor of       *)
(* wordLang's prog (Resume comp_correct[C] below) and Finalise comp_correct  *)
(* at HOL4 line 10063.  Here each case is a theorem                          *)
(* word_to_stackProof_comp_correct_C (at its Resume), whose statement is the *)
(* conjunct of the hypothesis of word_to_stackProof_ind_thm for the          *)
(* constructor C (word_to_stackProof_comp_case "wl_C"; print it in a session *)
(* with  concl word_to_stackProof_comp_correct_C), and                       *)
(* word_to_stackProof_comp_correct (HOL4 comp_correct, at the Finalise) is   *)
(* the conclusion of word_to_stackProof_ind_thm.  The Call case is split as  *)
(* in HOL4 (Resume comp_correct[Call] splits on ret): Call_tail (ret = NONE) *)
(* and Call_returning (ret = SOME x); word_to_stackProof_comp_correct_Call   *)
(* (the whole case, by cases on ret) is stated before the Finalise.          *)
let word_to_stackProof_comp_case_raw c =
  let th = ISPEC word_to_stackProof_goal wl_evaluate_ind in
  let is_c tm =
    let _,body = strip_forall tm in
    let cl = if is_imp body then rand body else body in
    try fst (dest_const (fst (strip_comb (fst (dest_pair (rand cl)))))) = c
    with Failure _ -> false in
  match filter is_c (conjuncts (lhand (concl th))) with
    [tm] -> rhs (concl (DEPTH_CONV GEN_BETA_CONV tm))
  | _ -> failwith ("word_to_stackProof_comp_case: " ^ c);;

let word_to_stackProof_comp_case c =
  mk_forall (`ac:(A)asm_config`, word_to_stackProof_comp_case_raw c);;

(* the Call case with its binder ret instantiated: NONE, or SOME x (x then  *)
(* quantified in place of ret)                                               *)
let word_to_stackProof_comp_call_case some =
  let tm = word_to_stackProof_comp_case_raw "wl_Call" in
  let vs,body = strip_forall tm in
  let rty = `:(num list#cutsets#(A)wl_prog#num#num)option` in
  let ret = match filter (fun v -> type_of v = rty) vs with
      [v] -> v | _ -> failwith "word_to_stackProof_comp_call_case" in
  let ty = hd (snd (dest_type rty)) in
  let x = variant (vs @ frees body) (mk_var("x",ty)) in
  let vs' = map (fun v -> if v = ret then x else v) vs in
  let res =
    if some then
      list_mk_forall (vs', vsubst [mk_comb(mk_const("SOME",[ty,aty]),x),ret] body)
    else
      list_mk_forall (filter (fun v -> not (v = ret)) vs,
                      vsubst [mk_const("NONE",[ty,aty]),ret] body) in
  mk_forall (`ac:(A)asm_config`, res);;

(* HOL4 line 5790: Resume comp_correct[Skip] *)
let word_to_stackProof_comp_correct_Skip = prove
 (word_to_stackProof_comp_case "wl_Skip",
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp2aux_weval "wl_Skip"; PAIR_EQ] THEN
  ONCE_REWRITE_TAC[word_to_stack_comp_def] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; w2sp2aux_seval "stack_Skip"] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; EXISTS_PAIR_THM; PAIR_EQ] THEN
  SIMP[OPTION_MAP_DEF] THEN
  SUBGOAL_THEN `stack_state_clock_fupd (K (stack_state_clock t)) (t:(A,C,FFI)stack_state) = t`
    SUBST1_TAC THENL [SIMP[stack_state_component_equality]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the live variables of a converted Alloc are stack variables *)
let W2SP2AUX_alloc_names = prove
 (`!k n names.
     post_alloc_conventions k (wl_Alloc n names:(A)wl_prog)
     ==> (!x. x IN domain (FST names) ==> EVEN x /\ k <= x DIV 2) /\
         (!x. x IN domain (SND names) ==> EVEN x /\ k <= x DIV 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[post_alloc_conventions_def; wl_every_var_def; every_stack_var_def;
              every_name_def; GSYM ALL_MEM; toAList_domain; is_phy_var_def;
              GSYM EVEN_MOD2; GE] THEN
  STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `2 * k <= x` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  SIMP_TAC[GSYM LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC);;

(* W2SP2AUX: with no stack frame, a converted Alloc has no live variables *)
let W2SP2AUX_alloc_names_empty = prove
 (`!k n names.
     post_alloc_conventions k (wl_Alloc n names:(A)wl_prog) /\
     max_var (wl_Alloc n names:(A)wl_prog) < 2 * k
     ==> domain (FST names) = {} /\ domain (SND names) = {}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[post_alloc_conventions_def; every_stack_var_def; max_var_def;
              every_name_def; cutsets_max_def; GSYM ALL_MEM; toAList_domain; GE] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; GSYM toAList_domain] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> ASSUME_TAC th THEN ASSUME_TAC(MATCH_MP MAX_LIST_PROPERTY th)) THEN
  RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 5798: Resume comp_correct[Alloc] *)
let word_to_stackProof_comp_correct_Alloc = prove
 (word_to_stackProof_comp_case "wl_Alloc",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "wl_evaluate")) THEN
  REWRITE_TAC[w2sp2aux_weval "wl_Alloc"] THEN
  CASES_ON `wl_get_var n (s:(A,num#C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `n = 2` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `post_alloc_conventions k (wl_Alloc n names:(A)wl_prog)` THEN
    SIMP[post_alloc_conventions_def; call_arg_convention_def];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `stack_get_var 1 (t:(A,C,FFI)stack_state) = SOME (wl_Word a')` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `0`;
      `2`; `wl_Word (a':A word)`] state_rel_get_var_imp') THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_alloc_names) THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "word_to_stack_comp")) THEN
  ONCE_REWRITE_TAC[word_to_stack_comp_def] THEN REWRITE_TAC[] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  SUBGOAL_THEN `stack_state_clock_fupd (K (stack_state_clock t)) (t:(A,C,FFI)stack_state) = t`
    ASSUME_TAC THENL [SIMP[stack_state_component_equality]; ALL_TAC] THEN
  CASES_ON `cut_envs names (wl_state_locals (s:(A,num#C,FFI)wl_state))` THENL
   [UNDISCH_TAC `wl_alloc a' names (s:(A,num#C,FFI)wl_state) = (res,s1)` THEN
    ASM_REWRITE_TAC[wl_alloc_def] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `1 <= f` THENL
   [MP_TAC(ISPECL [`names:(1)spt#(1)spt`; `bs:(A word)app_list`; `n':num`; `k:num`;
                   `f:num`; `f':num`; `q1:(A)stack_prog`; `bs':(A word)app_list`;
                   `n'':num`; `ac:(A)asm_config`; `s:(A,num#C,FFI)wl_state`;
                   `t:(A,C,FFI)stack_state`; `lens:num list`;
                   `a'':((A)word_loc)spt#((A)word_loc)spt`] evaluate_wLive) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t5:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`a':A word`; `names:(1)spt#(1)spt`; `s:(A,num#C,FFI)wl_state`;
                   `res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`; `k:num`;
                   `f:num`; `ac:(A)asm_config`; `f':num`; `t5:(A,C,FFI)stack_state`;
                   `lens:num list`; `a'':((A)word_loc)spt#((A)word_loc)spt`]
           alloc_IMP_alloc) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` (X_CHOOSE_THEN
      `res1:((A)stack_result)option` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `stack_evaluate (stack_Seq q1 (stack_Alloc 1),t:(A,C,FFI)stack_state) =
                  (res1,t1)` ASSUME_TAC THENL
     [REWRITE_TAC[w2sp2aux_seval "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[w2sp2aux_seval "stack_Alloc"] THEN
      SUBGOAL_THEN `stack_state_use_alloc (t5:(A,C,FFI)stack_state)` ASSUME_TAC THENL
       [UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                       (t5:(A,C,FFI)stack_state) lens 0` THEN
        REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `stack_get_var 1 (t5:(A,C,FFI)stack_state) = SOME (wl_Word a')`
        (fun th -> ASM_REWRITE_TAC[th]) THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `1` o check (is_forall o concl)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
        CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `0` THEN MAP_EVERY EXISTS_TAC
      [`t1:(A,C,FFI)stack_state`; `res1:((A)stack_result)option`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    COND_CASES_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
    CASE_REWRITE_TAC[compile_result_def] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `f = 0 /\ f' = 0` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl))) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `wLive names (bs,n') (k,0,0) = (q1:(A)stack_prog,bs',n'')` THEN
  REWRITE_TAC[wLive_def; PAIR_EQ] THEN STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  MP_TAC(ISPECL [`k:num`; `2`; `names:(1)spt#(1)spt`]
           (INST_TYPE [`:A`,`:A`] W2SP2AUX_alloc_names_empty)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `max_var (wl_Alloc 2 names:(A)wl_prog) < 2 * 0 + 2 * k` THEN ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`a':A word`; `names:(1)spt#(1)spt`; `s:(A,num#C,FFI)wl_state`;
                 `res:((A)wl_result)option`; `s1:(A,num#C,FFI)wl_state`;
                 `ac:(A)asm_config`; `k:num`; `t:(A,C,FFI)stack_state`; `lens:num list`]
         alloc_IMP_alloc2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,C,FFI)stack_state` (X_CHOOSE_THEN
    `res1:((A)stack_result)option` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `stack_evaluate (stack_Seq stack_Skip (stack_Alloc 1),t:(A,C,FFI)stack_state) =
                (res1,t1)` ASSUME_TAC THENL
   [REWRITE_TAC[W2SP2AUX_evaluate_Skip_Seq; w2sp2aux_seval "stack_Alloc"] THEN
    SUBGOAL_THEN `stack_state_use_alloc (t:(A,C,FFI)stack_state)` ASSUME_TAC THENL
     [UNDISCH_TAC `word_to_stackProof_state_rel ac k 0 0 (s:(A,num#C,FFI)wl_state)
                     (t:(A,C,FFI)stack_state) lens 0` THEN
      REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `0` THEN MAP_EVERY EXISTS_TAC
    [`t1:(A,C,FFI)stack_state`; `res1:((A)stack_result)option`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  CASE_REWRITE_TAC[compile_result_def] THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the bits of chunk_to_bits of a cons *)
let W2SP2AUX_bit_chunk_to_bits_CONS = prove
 (`!b (w:A word) ws i.
     bit i (chunk_to_bits (CONS (b,w) ws):A word) <=>
     i < dimindex (:A) /\ (if i = 0 then b else bit (i - 1) (chunk_to_bits ws:A word))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chunk_to_bits_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `word_add (word_shl (chunk_to_bits ws:A word) 1) (word 1) =
                  word_or (word_shl (chunk_to_bits ws) 1) (word 1)` SUBST1_TAC THENL
     [MATCH_MP_TAC WORD_ADD_OR THEN
      REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD_SHL; BIT_WORD_1] THEN
      ARITH_TAC;
      REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_1] THEN
      ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> 1 <= i`] THEN MESON_TAC[]];
    REWRITE_TAC[BIT_WORD_SHL] THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> 1 <= i`] THEN MESON_TAC[]]);;

(* HOL4 line 5855 *)
let chunk_to_bits_bound = prove
 (`!(ws:(bool#A word)list).
     LENGTH ws < dimindex (:A)
     ==> bit (LENGTH ws) (chunk_to_bits ws:A word) /\
         !i. LENGTH ws < i /\ i < dimindex (:A) ==> ~(bit i (chunk_to_bits ws:A word))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[chunk_to_bits_def; LENGTH; BIT_WORD_1] THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`h:bool#A word`,`h:bool#A word`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:bool`; `w:A word`] THEN
  REWRITE_TAC[LENGTH; W2SP2AUX_bit_chunk_to_bits_CONS; NOT_SUC; SUC_SUB1] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 5870 *)
let chunk_to_bits_0 = prove
 (`!b (w:A word) words. bit 0 (chunk_to_bits (CONS (b,w) words)) <=> b`,
  REWRITE_TAC[W2SP2AUX_bit_chunk_to_bits_CONS; DIMINDEX_GT_0]);;

(* W2SP2AUX: shifting chunk_to_bits of a cons right by one *)
let W2SP2AUX_chunk_to_bits_ushr = prove
 (`!b (w:A word) ws.
     SUC (LENGTH ws) < dimindex (:A)
     ==> word_ushr (chunk_to_bits (CONS (b,w) ws)) 1 = chunk_to_bits ws:A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[W2SP2AUX_bit_chunk_to_bits_CONS; ARITH_RULE `~(i + 1 = 0)`; ADD_SUB] THEN
  ASM_CASES_TAC `i + 1 < dimindex (:A)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `ws:(bool#A word)list` chunk_to_bits_bound) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_ARITH_TAC);;

(* HOL4 line 5881 *)
let copy_words_for_pattern_thm = prove
 (`!(words:(bool#A word)list) xs (a:A word) off ys dm m.
     LENGTH words < dimindex (:A) /\ const_addresses a words dm
     ==> copy_words_for_pattern (chunk_to_bits words) (LENGTH xs) a off
           (APPEND (APPEND xs (MAP SND words)) ys) dm m =
         SOME (LENGTH xs + LENGTH words,
               word_add a (word_mul bytes_in_word (word (LENGTH words))),
               const_writes a off words m)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[copy_words_for_pattern_def] THEN
    REWRITE_TAC[chunk_to_bits_def; LENGTH; const_writes_def; ADD_CLAUSES;
                WORD_MUL_0; WORD_ADD_0; WORD_NE_10];
    ALL_TAC] THEN
  SPEC_TAC(`h:bool#A word`,`h:bool#A word`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:bool`; `w:A word`] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH; const_addresses_def] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[copy_words_for_pattern_def] THEN
  MP_TAC(ISPEC `CONS (b,w) (t:(bool#A word)list)` chunk_to_bits_bound) THEN
  ASM_REWRITE_TAC[LENGTH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(chunk_to_bits (CONS (b,w) t) = word 0:A word) /\
                ~(chunk_to_bits (CONS (b,w) t) = word 1:A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM
      `(bit:num->A word->bool) (SUC (LENGTH (t:(bool#A word)list)))`) THEN
    ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1; NOT_SUC];
    ALL_TAC] THEN
  REWRITE_TAC[MAP; LENGTH_APPEND; LENGTH; GSYM APPEND_ASSOC; APPEND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `x < (x + SUC n) + y`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[chunk_to_bits_0] THEN
  SIMP_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  ASM_SIMP_TAC[W2SP2AUX_chunk_to_bits_ushr] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND xs [w:A word]`; `word_add (a:A word) bytes_in_word`;
    `off:A word`; `ys:(A word)list`; `dm:(A word)->bool`;
    `((a:A word) =+ wl_Word (if b then word_add w off else w)) (m:(A word)->(A)word_loc)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `x + SUC 0 = x + 1`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; const_writes_def] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (a:A word) (word_mul b (word (SUC L))) =
                         word_add (word_add a b) (word_mul b (word L))`]);;

(* HOL4 line 5938 *)
let word_msb_chunk_to_bits = prove
 (`!(words:(bool#A word)list).
     LENGTH words < dimindex (:A) /\ good_dimindex (:A)
     ==> (word_msb (chunk_to_bits words:A word) <=> LENGTH words = dimindex (:A) - 1)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP chunk_to_bits_bound) THEN
  REWRITE_TAC[word_msb_def] THEN STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH (words:(bool#A word)list) = dimindex (:A) - 1` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 5948 *)
let copy_words = prove
 (`!(a:A word) words dm xs off ys m.
     const_addresses a words dm /\ good_dimindex (:A) /\
     LENGTH words < dimindex (:A)
     ==> copy_words (LENGTH xs) a off (APPEND (APPEND xs (chunk_to_bitmap words)) ys) dm m =
         if LENGTH words = dimindex (:A) - 1 then
           copy_words (LENGTH xs + (LENGTH words + 1))
             (word_add a (word_mul bytes_in_word (word (LENGTH words)))) off
             (APPEND (APPEND xs (chunk_to_bitmap words)) ys) dm
             (const_writes a off words m)
         else
           SOME (word_add a (word_mul bytes_in_word (word (LENGTH words))),
                 const_writes a off words m)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [copy_words_def] THEN
  REWRITE_TAC[chunk_to_bitmap_def; LENGTH_APPEND; LENGTH; LENGTH_MAP] THEN
  REWRITE_TAC[ARITH_RULE `~((x + SUC n) + y <= x)`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  SIMP_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  MP_TAC(ISPECL [`words:(bool#A word)list`;
                 `APPEND xs [chunk_to_bits (words:(bool#A word)list):A word]`;
                 `a:A word`; `off:A word`; `ys:(A word)list`; `dm:(A word)->bool`;
                 `m:(A word)->(A)word_loc`] copy_words_for_pattern_thm) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `x + SUC 0 = x + 1`] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[word_msb_chunk_to_bits] THEN
  REWRITE_TAC[ARITH_RULE `(x + 1) + n = x + n + 1`]);;

(* HOL4 line 5973 *)
let const_writes_append = prove
 (`!h t (a:A word) off m.
     const_writes a off (APPEND h t) m =
     const_writes (word_add a (word_mul bytes_in_word (word (LENGTH h)))) off t
       (const_writes a off h m)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; LENGTH; const_writes_def; WORD_MUL_0; WORD_ADD_0] THEN
  SPEC_TAC(`h:bool#A word`,`h:bool#A word`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; const_writes_def] THEN
  REWRITE_TAC[WORD_RULE `word_add (a:A word) (word_mul b (word (SUC L))) =
                         word_add (word_add a b) (word_mul b (word L))`]);;

(* HOL4 line 5983 *)
let const_addresses_append = prove
 (`!(xs:B list) ys dm (a:A word).
     const_addresses a (APPEND xs ys) dm <=>
     const_addresses a xs dm /\
     const_addresses (word_add a (word_mul bytes_in_word (word (LENGTH xs)))) ys dm`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; const_addresses_def; WORD_MUL_0; WORD_ADD_0] THEN
  REWRITE_TAC[WORD_RULE `word_add (a:A word) (word_mul b (word (SUC L))) =
                         word_add (word_add a b) (word_mul b (word L))`; CONJ_ACI]);;

(* HOL4 line 5994 *)
let copy_words_correct = prove
 (`!(words:(bool#A word)list) xs ys (a:A word) off dm m.
     const_addresses a words dm /\ good_dimindex (:A)
     ==> copy_words (LENGTH xs) a off
           (APPEND (APPEND xs (const_words_to_bitmap words (LENGTH words))) ys) dm m =
         SOME (word_add a (word_mul bytes_in_word (word (LENGTH words))),
               const_writes a off words m)`,
  SUBGOAL_THEN `!n (words:(bool#A word)list) xs ys (a:A word) off dm m.
     LENGTH words = n /\ const_addresses a words dm /\ good_dimindex (:A)
     ==> copy_words (LENGTH xs) a off
           (APPEND (APPEND xs (const_words_to_bitmap words (LENGTH words))) ys) dm m =
         SOME (word_add a (word_mul bytes_in_word (word (LENGTH words))),
               const_writes a off words m)` (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `dimindex (:A) = 32 \/ dimindex (:A) = 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[const_words_to_bitmap_def] THEN
  ASM_CASES_TAC `LENGTH (words:(bool#A word)list) < dimindex (:A) - 1` THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`a:A word`; `words:(bool#A word)list`; `dm:(A word)->bool`;
                   `xs:(A word)list`; `off:A word`; `ys:(A word)list`;
                   `m:(A word)->(A)word_loc`] copy_words) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(dimindex (:A) - 1 = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `h = TAKE (dimindex (:A) - 1) (words:(bool#A word)list)` THEN
  ABBREV_TAC `t = DROP (dimindex (:A) - 1) (words:(bool#A word)list)` THEN
  SUBGOAL_THEN `words:(bool#A word)list = APPEND h t` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "t"] THEN REWRITE_TAC[TAKE_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (h:(bool#A word)list) = dimindex (:A) - 1` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (words:(bool#A word)list) - (dimindex (:A) - 1) =
                LENGTH (t:(bool#A word)list)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[LENGTH_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `const_addresses (a:A word) (h:(bool#A word)list) dm /\
                const_addresses (word_add a (word_mul bytes_in_word
                  (word (LENGTH (h:(bool#A word)list))))) (t:(bool#A word)list) dm`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[const_addresses_append]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:A word`; `h:(bool#A word)list`; `dm:(A word)->bool`;
                 `xs:(A word)list`; `off:A word`;
                 `APPEND (const_words_to_bitmap (t:(bool#A word)list)
                   (LENGTH (t:(bool#A word)list))) ys`;
                 `m:(A word)->(A)word_loc`] copy_words) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[APPEND_ASSOC] THEN
  SUBGOAL_THEN `LENGTH (xs:(A word)list) + (dimindex (:A) - 1 + 1) =
                LENGTH (APPEND xs (chunk_to_bitmap (h:(bool#A word)list)))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; chunk_to_bitmap_def; LENGTH; LENGTH_MAP] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (t:(bool#A word)list)` o
    check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:(bool#A word)list`;
    `APPEND xs (chunk_to_bitmap (h:(bool#A word)list))`; `ys:(A word)list`;
    `word_add (a:A word) (word_mul bytes_in_word (word (dimindex (:A) - 1)))`;
    `off:A word`; `dm:(A word)->bool`;
    `const_writes (a:A word) off (h:(bool#A word)list) m`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `words:(bool#A word)list = APPEND h t`
                          then SUBST1_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[const_writes_append; LENGTH_APPEND] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (a:A word) (word_mul b (word x)))
                                   (word_mul b (word y)) =
                         word_add a (word_mul b (word (x + y)))`]);;

(* W2SP2AUX: the word locals of a related state are well formed *)
let W2SP2AUX_state_rel_wf = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra ==> wf (wl_state_locals s)`,
  REWRITE_TAC[word_to_stackProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the state relation survives new word locals and stack registers *)
(* that agree on every local held in a register                              *)
let W2SP2AUX_state_rel_locals_regs = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens extra l r.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\ wf l /\
     (!n v. lookup n l = SOME v
            ==> EVEN n /\
                if n DIV 2 < k then FLOOKUP r (n DIV 2) = SOME v
                else lookup n (wl_state_locals s) = SOME v)
     ==> word_to_stackProof_state_rel ac k f f' (wl_state_locals_fupd (K l) s)
           (stack_state_regs_fupd (K r) t) lens extra`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stackProof_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; stack_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o
    check (fun th -> is_forall (concl th) && w2sp2aux_has_const "FLOOKUP" th &&
                     not (w2sp2aux_has_const "oEL" th))) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o
    check (fun th -> is_forall (concl th) && w2sp2aux_has_const "oEL" th)) THEN
  ASM_REWRITE_TAC[]);;

(* W2SP2AUX: inversion of a successful wordSem StoreConsts *)
let W2SP2AUX_StoreConsts_inv = prove
 (`!t1 t2 addr offset words (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (wl_StoreConsts t1 t2 addr offset words,s) = (res,s1) /\
     ~(res = SOME wl_Error)
     ==> ?w off.
           wl_get_var addr s = SOME (wl_Word w) /\
           wl_get_var offset s = SOME (wl_Word off) /\
           const_addresses w words (wl_state_mdomain s) /\
           res = NONE /\
           s1 = wl_set_var addr
                  (wl_Word (word_add w (word_mul bytes_in_word (word (LENGTH words)))))
                  (wl_set_var offset (wl_Word off)
                     (wl_unset_var t1 (wl_unset_var t2
                        (wl_state_memory_fupd
                           (K (const_writes w off words (wl_state_memory s))) s))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[w2sp2aux_weval "wl_StoreConsts"] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASES_ON `wl_get_var addr (s:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC; MESON_TAC[]] THEN
  CASES_ON `wl_get_var offset (s:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a'':(A)word_loc` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC; MESON_TAC[]] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the bitmaps of the frame around an inserted bitmap *)
let W2SP2AUX_bitmaps_split = prove
 (`!bs n (cw:(A word)list) bms.
     LENGTH (append bs) <= n /\ n - LENGTH (append bs) <= LENGTH bms /\
     APPEND (append bs) cw <<= DROP (n - LENGTH (append bs)) bms
     ==> ?xs ys. bms = APPEND (APPEND xs cw) ys /\ LENGTH xs = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_PREFIX_APPEND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `l:(A word)list`))) THEN
  EXISTS_TAC `APPEND (TAKE (n - LENGTH (append bs)) (bms:(A word)list)) (append bs)` THEN
  EXISTS_TAC `l:(A word)list` THEN
  ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TAKE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  SUBGOAL_THEN `APPEND (append (bs:(A word)app_list)) (APPEND (cw:(A word)list) l) =
                DROP (n - LENGTH (append bs)) (bms:(A word)list)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[APPEND_ASSOC]; REWRITE_TAC[TAKE_DROP]]);;

(* W2SP2AUX: the stack code of a converted StoreConsts *)
let W2SP2AUX_StoreConsts_stack = prove
 (`!k (t:(A,C,FFI)stack_state) n a off words xs ys.
     stack_state_use_store t /\ stack_state_use_alloc t /\ good_dimindex (:A) /\ 4 < k /\
     lookup wl_store_consts_stub_location (stack_state_code t) =
       SOME (store_consts_stub k) /\
     FLOOKUP (stack_state_regs t) 2 = SOME (wl_Word a) /\
     FLOOKUP (stack_state_regs t) 3 = SOME (wl_Word off) /\
     stack_state_bitmaps t =
       APPEND (APPEND xs (const_words_to_bitmap words (LENGTH words))) ys /\
     LENGTH xs = n /\ n < dimword (:A) /\
     const_addresses a words (stack_state_mdomain t)
     ==> stack_evaluate (stack_Seq (stack_Inst (asm_Const 1 (word n)))
           (stack_StoreConsts k (k + 1) (SOME wl_store_consts_stub_location)),t) =
         (NONE,
          stack_unset_var 0 (stack_set_var k (wl_Word (word 1))
            (stack_set_var (k + 1) (wl_Word (word 1))
            (stack_set_var 1 (wl_Word (word 1))
            (stack_set_var 2
               (wl_Word (word_add a (word_mul bytes_in_word (word (LENGTH words)))))
            (stack_state_memory_fupd
               (K (const_writes a off words (stack_state_memory t)))
            (stack_set_var 1 (wl_Word (word n)) t)))))))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     is_var (rhs (concl th)) && w2sp2aux_has_const "LENGTH" th)) THEN
  REWRITE_TAC[w2sp2aux_seval "stack_Seq"; w2sp2aux_seval "stack_Inst"; stack_inst_def] THEN
  CASE_REWRITE_TAC[stack_assign_def; stack_word_exp_def] THEN
  REWRITE_TAC[w2sp2aux_seval "stack_StoreConsts"] THEN
  REWRITE_TAC[stack_set_var_def; stack_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[IS_SOME_DEF; check_store_consts_opt_def; store_consts_stub_def] THEN
  REWRITE_TAC[store_const_sem_def] THEN
  SUBGOAL_THEN `ALL_DISTINCT [0; 1; 2; 3; k; k + 1]` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ALL_DISTINCT; MEM; DE_MORGAN_THM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[stack_get_var_def; stack_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE;
                  ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word (LENGTH (xs:(A word)list)):A word) = LENGTH xs`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_REWRITE_TAC[GSYM dimword_def];
    ALL_TAC] THEN
  ASM_SIMP_TAC[copy_words_correct] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_set_var_def; stack_state_INFO.ri_accfupds; K_THM]);;

(* W2SP2AUX: the same with the new states given up to their locals and registers *)
let W2SP2AUX_state_rel_locals_regs_eq = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) s' t' lens extra.
     word_to_stackProof_state_rel ac k f f' s t lens extra /\
     s' = wl_state_locals_fupd (K (wl_state_locals s')) s /\
     t' = stack_state_regs_fupd (K (stack_state_regs t')) t /\
     wf (wl_state_locals s') /\
     (!n v. lookup n (wl_state_locals s') = SOME v
            ==> EVEN n /\
                if n DIV 2 < k then FLOOKUP (stack_state_regs t') (n DIV 2) = SOME v
                else lookup n (wl_state_locals s) = SOME v)
     ==> word_to_stackProof_state_rel ac k f f' s' t' lens extra`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC
    (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC W2SP2AUX_state_rel_locals_regs THEN ASM_REWRITE_TAC[]);;

(* W2SP2AUX: the state relation after a converted StoreConsts *)
let W2SP2AUX_state_rel_StoreConsts = prove
 (`!ac k f f' (s:(A,num#C,FFI)wl_state) (t:(A,C,FFI)stack_state) lens a off w m
    v0 v1 v2 v3.
     word_to_stackProof_state_rel ac k f f' s t lens 0 /\
     wl_get_var 4 s = SOME (wl_Word a) /\ wl_get_var 6 s = SOME (wl_Word off)
     ==> word_to_stackProof_state_rel ac k f f'
           (wl_set_var 4 (wl_Word w) (wl_set_var 6 (wl_Word off)
              (wl_unset_var 0 (wl_unset_var 2 (wl_state_memory_fupd (K m) s)))))
           (stack_unset_var 0 (stack_set_var k v3 (stack_set_var (k + 1) v2
              (stack_set_var 1 v1 (stack_set_var 2 (wl_Word w)
              (stack_state_memory_fupd (K m) (stack_set_var 1 v0 t)))))))
           lens 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC W2SP2AUX_state_rel_locals_regs_eq THEN
  MAP_EVERY EXISTS_TAC [`wl_state_memory_fupd (K m) (s:(A,num#C,FFI)wl_state)`;
                        `stack_state_memory_fupd (K m) (t:(A,C,FFI)stack_state)`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_wf) THEN
  SUBGOAL_THEN `FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state)) 3 = SOME (wl_Word off)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC state_rel_get_var_imp THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `lens:num list`; `0`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_with_memory THEN ASM_REWRITE_TAC[];
    SIMP[wl_state_component_equality; wl_set_var_def; wl_unset_var_def];
    SIMP[stack_state_component_equality; stack_set_var_def; stack_unset_var_def];
    SIMP[wl_set_var_def; wl_unset_var_def] THEN
    REPEAT(MATCH_MP_TAC wf_insert) THEN REPEAT(MATCH_MP_TAC wf_delete) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[wl_set_var_def; wl_unset_var_def; stack_set_var_def; stack_unset_var_def;
              wl_state_INFO.ri_accfupds; stack_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[lookup_insert; lookup_delete; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN
  ASM_CASES_TAC `n = 4` THENL
   [ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 < k ==> 2 < k /\ ~(k = 2) /\ ~(k + 1 = 2)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 6` THENL
   [ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 < k ==> 3 < k /\ ~(k = 3) /\ ~(k + 1 = 3)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `EVEN n` ASSUME_TAC THENL
   [MATCH_MP_TAC W2SP2AUX_state_rel_EVEN THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`; `lens:num list`; `0`;
      `v:(A)word_loc`] THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(0 = n DIV 2) /\ ~(1 = n DIV 2) /\ ~(2 = n DIV 2) /\
                ~(k = n DIV 2) /\ ~(k + 1 = n DIV 2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `EVEN n` THEN REWRITE_TAC[EVEN_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(SIMP_RULE[DIV_MULT; ARITH_EQ]) THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM stack_get_var_def] THEN
  MATCH_MP_TAC state_rel_get_var_imp' THEN
  MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
    `s:(A,num#C,FFI)wl_state`; `lens:num list`; `0`] THEN
  ASM_REWRITE_TAC[wl_get_var_def]);;

(* HOL4 line 6053: Resume comp_correct[StoreConsts] *)
let word_to_stackProof_comp_correct_StoreConsts = prove
 (word_to_stackProof_comp_case "wl_StoreConsts",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1 = 0 /\ t2 = 2 /\ addr = 4 /\ offset = 6` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `post_alloc_conventions k
      (wl_StoreConsts t1 t2 addr offset words:(A)wl_prog)` THEN
    SIMP[post_alloc_conventions_def; call_arg_convention_def];
    ALL_TAC] THEN
  w2sp2aux_rveq_tac THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "wl_evaluate")) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP W2SP2AUX_StoreConsts_inv
    (CONJ th (ASSUME `~(res = SOME (wl_Error:(A)wl_result))`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `off:A word` STRIP_ASSUME_TAC)) THEN
  w2sp2aux_rveq_tac THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "word_to_stack_comp")) THEN
  ONCE_REWRITE_TAC[word_to_stack_comp_def] THEN REWRITE_TAC[insert_bitmap_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[PAIR_EQ; FST] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_mem) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_state_rel_stack) THEN
  SUBGOAL_THEN `stack_state_use_store (t:(A,C,FFI)stack_state) /\
                stack_state_use_alloc t /\ good_dimindex (:A) /\
                lookup wl_store_consts_stub_location (stack_state_code t) =
                  SOME (store_consts_stub k) /\
                LENGTH (stack_state_bitmaps t) < dimword (:A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `word_to_stackProof_state_rel ac k f f' (s:(A,num#C,FFI)wl_state)
                   (t:(A,C,FFI)stack_state) lens 0` THEN
    REWRITE_TAC[word_to_stackProof_state_rel_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (stack_state_regs (t:(A,C,FFI)stack_state)) 2 = SOME (wl_Word a) /\
                FLOOKUP (stack_state_regs t) 3 = SOME (wl_Word off)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC state_rel_get_var_imp THEN
    MAP_EVERY EXISTS_TAC [`ac:(A)asm_config`; `k:num`; `f:num`; `f':num`;
      `s:(A,num#C,FFI)wl_state`; `lens:num list`; `0`] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bs:(A word)app_list`; `n:num`;
                 `const_words_to_bitmap (words:(bool#A word)list) (LENGTH words)`;
                 `stack_state_bitmaps (t:(A,C,FFI)stack_state)`] W2SP2AUX_bitmaps_split) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `append (misc_Append bs (misc_List (const_words_to_bitmap
      (words:(bool#A word)list) (LENGTH words)))) <<=
      DROP (n - LENGTH (append bs)) (stack_state_bitmaps (t:(A,C,FFI)stack_state))` THEN
    REWRITE_TAC[append_thm];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A word)list` (X_CHOOSE_THEN `ys:(A word)list`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `stack_state_clock_fupd (K (stack_state_clock t)) (t:(A,C,FFI)stack_state) = t`
    SUBST1_TAC THENL [SIMP[stack_state_component_equality]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `t:(A,C,FFI)stack_state`; `n:num`; `a:A word`; `off:A word`;
                 `words:(bool#A word)list`; `xs:(A word)list`; `ys:(A word)list`]
    W2SP2AUX_StoreConsts_stack) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH (stack_state_bitmaps (t:(A,C,FFI)stack_state)) < dimword (:A)` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC W2SP2AUX_state_rel_StoreConsts THEN ASM_MESON_TAC[]);;

(* W2SP2AUX: an even number is twice its half *)
let W2SP2AUX_TIMES2_DIV2 = prove
 (`!n. EVEN n ==> 2 * DIV2 n = n`,
  REWRITE_TAC[EVEN_EXISTS; DIV2_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* W2SP2AUX: the sources and destinations of halved moves *)
let W2SP2AUX_MAP_DIV2_moves = prove
 (`!moves:(num#num)list.
     MAP FST (MAP (DIV2 ## DIV2) moves) = MAP DIV2 (MAP FST moves) /\
     MAP SND (MAP (DIV2 ## DIV2) moves) = MAP DIV2 (MAP SND moves)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN CONJ_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; PAIR_MAP_THM]);;

(* W2SP2AUX: a register move of a converted program moves physical registers *)
let W2SP2AUX_move_conv = prove
 (`!k pri moves.
     post_alloc_conventions k (wl_Move pri moves:(A)wl_prog)
     ==> ALL EVEN (MAP FST moves) /\ ALL EVEN (MAP SND moves)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[post_alloc_conventions_def; wl_every_var_def] THEN
  SUBGOAL_THEN `is_phy_var = EVEN` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; is_phy_var_def; EVEN_MOD2]; ALL_TAC] THEN
  MESON_TAC[]);;

(* W2SP2AUX: halving distinct even destinations keeps them distinct *)
let W2SP2AUX_windmill_DIV2 = prove
 (`!moves:(num#num)list.
     windmill moves /\ ALL EVEN (MAP FST moves)
     ==> windmill (MAP (DIV2 ## DIV2) moves)`,
  REWRITE_TAC[windmill_def; W2SP2AUX_MAP_DIV2_moves; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
  ASM_MESON_TAC[EVEN_DIV2_INJ]);;

(* W2SP2AUX: ALOOKUP through SOME ## SOME *)
let W2SP2AUX_ALOOKUP_SOME_SOME = prove
 (`!(moves:(A#B)list) z.
     ALOOKUP (MAP (SOME ## SOME) moves) (SOME z) = OPTION_MAP SOME (ALOOKUP moves z)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_def; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[ALOOKUP_def; option_INJ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

(* W2SP2AUX: the destinations of SOME ## SOME moves stay distinct *)
let W2SP2AUX_ALL_DISTINCT_SOME_SOME = prove
 (`!moves:(A#B)list.
     ALL_DISTINCT (MAP FST moves) ==> ALL_DISTINCT (MAP FST (MAP (SOME ## SOME) moves))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
  SUBGOAL_THEN `FST o ((SOME ## SOME):A#B->A option#B option) = SOME o FST`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; PAIR_MAP_THM]; ALL_TAC] THEN
  REWRITE_TAC[MAP_o] THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
  ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

(* W2SP2AUX: parsem with distinct destinations, pointwise *)
let W2SP2AUX_parsem_ALOOKUP = prove
 (`!(mu:(A#A)list) (rho:A->B) x.
     ALL_DISTINCT (MAP FST mu)
     ==> parsem mu rho x = rho (match ALOOKUP mu x with NONE -> x | SOME y -> y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[parsem_def; APPLY_UPDATE_LIST_ALOOKUP] THEN
  MP_TAC(ISPECL [`ZIP (MAP FST mu) (MAP ((rho:A->B) o SND) (mu:(A#A)list))`; `x:A`]
    alookup_distinct_reverse) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MAP_o; W2SP2AUX_ALOOKUP_ZIP_FST] THEN
  CASES_ON `ALOOKUP (mu:(A#A)list) x` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF]);;

(* W2SP2AUX: the sources read by the sequentialised halved moves are defined *)
let W2SP2AUX_move_get_vars = prove
 (`!(moves:(num#num)list) (s:(A,C,FFI)wl_state) vs.
     ALL EVEN (MAP SND moves) /\ wl_get_vars (MAP SND moves) s = SOME vs
     ==> IS_SOME (wl_get_vars (MAP ((\x. 2 * x) o THE)
                   (FILTER IS_SOME (MAP SND (parmove (MAP (DIV2 ## DIV2) moves))))) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. MEM x (MAP SND (moves:(num#num)list))
                    ==> IS_SOME (wl_get_var x (s:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`MAP SND (moves:(num#num)list)`; `s:(A,C,FFI)wl_state`]
      IS_SOME_get_vars_EVERY) THEN
    ASM_REWRITE_TAC[IS_SOME_DEF; GSYM ALL_MEM];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[IS_SOME_get_vars_EVERY; GSYM ALL_MEM] THEN
  X_GEN_TAC `x:num` THEN ONCE_REWRITE_TAC[MEM_MAP] THEN REWRITE_TAC[MEM_FILTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num option` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `y:num option` (cases "option")) THEN
  REWRITE_TAC[IS_SOME_DEF; THE_DEF; o_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEM_MAP_SND_parmove) THEN
  REWRITE_TAC[W2SP2AUX_MAP_DIV2_moves] THEN ONCE_REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `EVEN b` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[W2SP2AUX_TIMES2_DIV2]);;

(* W2SP2AUX: the sequentialised halved moves stay below the frame bound *)
let W2SP2AUX_move_bound = prove
 (`!(moves:(num#num)list) k f'.
     MAX_LIST (APPEND (MAP FST moves) (MAP SND moves)) < 2 * f' + 2 * k
     ==> ALL (\(x,y). !a. x = SOME a \/ y = SOME a ==> a < f' + k)
           (parmove (MAP (DIV2 ## DIV2) moves))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!b. MEM b (MAP FST (moves:(num#num)list)) \/ MEM b (MAP SND moves)
                    ==> DIV2 b < f' + k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    (SUBGOAL_THEN `b < 2 * (f' + k)` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `MAX_LIST (APPEND (MAP FST (moves:(num#num)list)) (MAP SND moves))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MAX_LIST_PROPERTY THEN ASM_REWRITE_TAC[MEM_APPEND]; ASM_ARITH_TAC];
      SIMP_TAC[DIV2_def; RDIV_LT_EQ; ARITH_EQ]]);
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`p:num option`; `q:num option`] THEN DISCH_TAC THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `MEM (SOME a) (MAP FST (parmove (MAP (DIV2 ## DIV2) (moves:(num#num)list))))`
      MP_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      MP_TAC(ISPECL [`FST:num option#num option->num option`;
        `parmove (MAP (DIV2 ## DIV2) (moves:(num#num)list))`; `(p:num option,q:num option)`]
        MEM_MAP_f) THEN ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MEM_MAP_FST_parmove);
    SUBGOAL_THEN `MEM (SOME a) (MAP SND (parmove (MAP (DIV2 ## DIV2) (moves:(num#num)list))))`
      MP_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      MP_TAC(ISPECL [`SND:num option#num option->num option`;
        `parmove (MAP (DIV2 ## DIV2) (moves:(num#num)list))`; `(p:num option,q:num option)`]
        MEM_MAP_f) THEN ASM_REWRITE_TAC[SND];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MEM_MAP_SND_parmove)] THEN
  REWRITE_TAC[W2SP2AUX_MAP_DIV2_moves] THEN ONCE_REWRITE_TAC[MEM_MAP] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(* W2SP2AUX: the locals written by the sequentialised halved moves *)
let W2SP2AUX_move_set_vars = prove
 (`!(moves:(num#num)list) (s:(A,C,FFI)wl_state) vs (r:num option->((A)word_loc)option).
     windmill moves /\ ALL EVEN (MAP FST moves) /\ ALL EVEN (MAP SND moves) /\
     wf (wl_state_locals s) /\ wl_get_vars (MAP SND moves) s = SOME vs /\
     (!i. r (SOME i) = wl_get_var (2 * i) s)
     ==> wl_set_vars
           (MAP ((\x. 2 * x) o THE)
              (FILTER IS_SOME (MAP FST (REVERSE (parmove (MAP (DIV2 ## DIV2) moves))))))
           (MAP THE (MAP (seqsem (parmove (MAP (DIV2 ## DIV2) moves)) r)
              (FILTER IS_SOME (MAP FST (REVERSE (parmove (MAP (DIV2 ## DIV2) moves)))))))
           s =
         wl_set_vars (MAP FST moves) vs s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `windmill (MAP (DIV2 ## DIV2) (moves:(num#num)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC W2SP2AUX_windmill_DIV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MAP_REVERSE; FILTER_REVERSE] THEN
  ASM_SIMP_TAC[TIMES2_DIV2_lemma] THEN
  SUBGOAL_THEN
   `MAP (seqsem (parmove (MAP (DIV2 ## DIV2) moves)) (r:num option->((A)word_loc)option))
      (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) (moves:(num#num)list))))) =
    MAP (parsem (MAP (SOME ## SOME) (MAP (DIV2 ## DIV2) moves)) r)
      (FILTER IS_SOME (MAP FST (parmove (MAP (DIV2 ## DIV2) moves))))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
    X_GEN_TAC `x:num option` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o ISPEC `r:num option->((A)word_loc)option` o
                MATCH_MP parmove_correct o
                check (fun th -> rand(concl th) <> `moves:(num#num)list`)) THEN
    REWRITE_TAC[eqenv_def] THEN DISCH_THEN(MP_TAC o SPEC `x:num option`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[parsem_parmove_DIV2_lemma] THEN
  REWRITE_TAC[wl_set_vars_def] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (FILTER IS_SOME (MAP FST (parmove (moves:(num#num)list))))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_parmove THEN ASM_REWRITE_TAC[GSYM windmill_def]; ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [rand(rand(rator(rator(lhs w)))); rand(lhand(lhs w));
      `wl_state_locals (s:(A,C,FFI)wl_state)`] alist_insert_REVERSE)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP] THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
    ASM_REWRITE_TAC[MEM_FILTER; IS_SOME_EXISTS] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[THE_DEF];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`moves:(num#num)list`; `s:(A,C,FFI)wl_state`; `vs:((A)word_loc)list`;
                 `MAP FST (parmove (moves:(num#num)list))`] alist_insert_get_vars) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[windmill_def]) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[MEM_MAP_FST_parmove]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC parmove_preserves_moves THEN
    EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[windmill_def];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[IS_SOME_DEF] THEN
  X_GEN_TAC `z:num` THEN STRIP_TAC THEN REWRITE_TAC[o_THM; THE_DEF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEM_MAP_FST_parmove) THEN
  CASES_ON `ALOOKUP (moves:(num#num)list) z` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ALOOKUP_FAILS]) THEN
    UNDISCH_TAC `MEM (z:num) (MAP FST (moves:(num#num)list))` THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
  SUBGOAL_THEN `EVEN a` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM]) THEN
    ASM_MESON_TAC[SND];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[windmill_def]) THEN
  ASM_SIMP_TAC[W2SP2AUX_parsem_ALOOKUP; W2SP2AUX_ALL_DISTINCT_SOME_SOME;
               W2SP2AUX_ALOOKUP_SOME_SOME] THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF; o_THM; THE_DEF] THEN
  ASM_SIMP_TAC[W2SP2AUX_TIMES2_DIV2]);;

(* HOL4 line 6132: Resume comp_correct[Move] *)
let word_to_stackProof_comp_correct_Move = prove
 (word_to_stackProof_comp_case "wl_Move",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "word_to_stack_comp")) THEN
  ONCE_REWRITE_TAC[word_to_stack_comp_def] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  FIRST_X_ASSUM(MP_TAC o check (w2sp2aux_has_const "wl_evaluate")) THEN
  REWRITE_TAC[w2sp2aux_weval "wl_Move"] THEN
  COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]] THEN
  CASES_ON `wl_get_vars (MAP SND (moves:(num#num)list)) (s:(A,num#C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN w2sp2aux_rveq_tac THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP W2SP2AUX_move_conv) THEN
  SUBGOAL_THEN `windmill (moves:(num#num)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[windmill_def]; ALL_TAC] THEN
  SUBGOAL_THEN `windmill (MAP (DIV2 ## DIV2) (moves:(num#num)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC W2SP2AUX_windmill_DIV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `stack_state_clock_fupd (K (stack_state_clock t)) (t:(A,C,FFI)stack_state) = t`
    SUBST1_TAC THENL [SIMP[stack_state_component_equality]; ALL_TAC] THEN
  REWRITE_TAC[wMove_def] THEN
  MP_TAC(ISPECL [`parmove (MAP (DIV2 ## DIV2) (moves:(num#num)list))`;
                 `s:(A,num#C,FFI)wl_state`; `t:(A,C,FFI)stack_state`;
                 `\x:num option. match x with
                     NONE -> stack_get_var (k + 1) (t:(A,C,FFI)stack_state)
                   | SOME i -> wl_get_var (2 * i) (s:(A,num#C,FFI)wl_state)`;
                 `ac:(A)asm_config`; `k:num`; `f:num`; `f':num`; `lens:num list`]
        evaluate_wMoveAux_seqsem) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC W2SP2AUX_move_get_vars THEN ASM_MESON_TAC[];
      MP_TAC(ISPEC `MAP (DIV2 ## DIV2) (moves:(num#num)list)`
        parmove_not_use_temp_before_assign) THEN
      ASM_REWRITE_TAC[] THEN
      CASES_ON `find_index NONE (MAP SND (parmove (MAP (DIV2 ## DIV2)
                  (moves:(num#num)list)))) 0` THEN
      CASES_ON `find_index NONE (MAP FST (parmove (MAP (DIV2 ## DIV2)
                  (moves:(num#num)list)))) 0` THEN
      CASE_REWRITE_TAC[] THEN MESON_TAC[];
      MATCH_MP_TAC W2SP2AUX_move_bound THEN
      UNDISCH_TAC `max_var (wl_Move pri moves:(A)wl_prog) < 2 * f' + 2 * k` THEN
      REWRITE_TAC[max_var_def];
      MATCH_MP_TAC ALL_DISTINCT_parmove THEN ASM_REWRITE_TAC[GSYM windmill_def]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)stack_state`; `NONE:((A)stack_result)option`] THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`moves:(num#num)list`; `s:(A,num#C,FFI)wl_state`; `a:((A)word_loc)list`;
                 `\x:num option. match x with
                     NONE -> stack_get_var (k + 1) (t:(A,C,FFI)stack_state)
                   | SOME i -> wl_get_var (2 * i) (s:(A,num#C,FFI)wl_state)`]
        W2SP2AUX_move_set_vars) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC W2SP2AUX_state_rel_wf THEN ASM_MESON_TAC[];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN ASM_REWRITE_TAC[]]);;
