(* ========================================================================= *)
(* stack_to_labProof_p2: part 2 of 2 (HOL4 lines 2741-5221) of the port of  *)
(* HOL4 compiler/backend/proofs/stack_to_labProofScript.sml (CakeML v3479).  *)
(* Correctness proof for stack_to_lab.                                       *)
(* The parts stack_to_labProof_p1.ml (HOL4 lines 1-2740) and _p2.ml are      *)
(* loaded one after the other (p2 needs p1).  The notes on the rendering in  *)
(* stack_to_labProof_p1.ml apply here.  S2LP2AUX_ names are local helpers of *)
(* this part.                                                                *)
(* ========================================================================= *)

needs "compiler/backend/proofs/stack_to_labProof_p1.ml";;
needs "compiler/backend/proofs/stack_allocProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 2741-5221 ===== *)

(* helpers for flatten_call_correct: the evaluation of a tail call, the  *)
(* code facts of state_rel, and flatten_correct for a whole procedure     *)

let S2LP2AUX_call_none = prove
 (`!start (s:(A,C,FFI)stack_state) res s2.
     stack_evaluate (stack_Call NONE (INL start) NONE,s) = (res,s2) /\
     ~(res = SOME stack_Error)
     ==> ?prog. lookup start (stack_state_code s) = SOME prog /\
                ((stack_state_clock s = 0 /\ res = SOME stack_TimeOut /\
                  s2 = stack_empty_env s) \/
                 (~(stack_state_clock s = 0) /\
                  stack_evaluate (prog,stack_dec_clock s) = (res,s2) /\
                  ~stack_bad_fun_return res))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN
  CASE_REWRITE_TAC[stack_find_code_def] THEN
  CASES_ON `lookup start (stack_state_code (s:(A,C,FFI)stack_state)):((A)stack_prog)option` THEN
  CASE_REWRITE_TAC[] THENL [MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `stack_evaluate (a:(A)stack_prog,stack_dec_clock (s:(A,C,FFI)stack_state))`
           PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:((A)stack_result)option`; `r:(A,C,FFI)stack_state`] THEN
  DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC th) THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let S2LP2AUX_state_rel_code = prove
 (`!(s:(A,C,FFI)stack_state) (t:(A,C,FFI)lab_state) n prog.
     stack_to_labProof_state_rel s t /\ lookup n (stack_state_code s) = SOME prog
     ==> call_args prog (lab_state_ptr_reg t) (lab_state_len_reg t) (lab_state_ptr2_reg t)
           (lab_state_len2_reg t) (lab_state_link_reg t) /\
         ?pc. stack_to_labProof_code_installed pc
                (append (FST (stack_to_lab_flatten T prog n (next_lab prog 2) [] [])))
                (lab_state_code t) /\
              loc_to_pc n 0 (lab_state_code t) = SOME pc`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN MESON_TAC[]);;
let S2LP2AUX_state_rel_basic = prove
 (`!(s:(A,C,FFI)stack_state) (t:(A,C,FFI)lab_state).
     stack_to_labProof_state_rel s t
     ==> lab_state_clock t = stack_state_clock s /\
         lab_state_ffi t = stack_state_ffi s /\
         lab_state_code_buffer t = stack_state_code_buffer s`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;
let S2LP2AUX_stack_clock_id = prove
 (`!s:(A,C,FFI)stack_state. stack_state_clock_fupd (K (stack_state_clock s)) s = s`,
  REWRITE_TAC[stack_state_component_equality] THEN SIMP[]);;

let S2LP2AUX_body = prove
 (`!prog (s:(A,C,FFI)stack_state) r s' n (t:(A,C,FFI)lab_state).
     stack_evaluate (prog,s) = (r,s') /\ ~(r = SOME stack_Error) /\
     stack_to_labProof_state_rel s t /\
     lookup n (stack_state_code s) = SOME prog /\
     loc_to_pc n 0 (lab_state_code t) = SOME (lab_state_pc t)
     ==> (!w. r = SOME (stackSem_Halt w)
              ==> ?ck t2. lab_evaluate (lab_state_clock_fupd (K (lab_state_clock t + ck)) t) =
                            (halt_word_view w,t2) /\
                          lab_state_ffi t2 = stack_state_ffi s') /\
         (!f. r = SOME (stack_FinalFFI f)
              ==> ?ck t2. lab_evaluate (lab_state_clock_fupd (K (lab_state_clock t + ck)) t) =
                            (target_Halt (FFI_outcome f),t2) /\
                          lab_state_ffi t2 = stack_state_ffi s') /\
         (r = SOME stack_TimeOut
              ==> ?ck t2. lab_evaluate (lab_state_clock_fupd (K (lab_state_clock t + ck)) t) =
                            (target_TimeOut,t2) /\
                          lab_state_ffi t2 = stack_state_ffi s') /\
         (!n1 n2. r = SOME (stack_Result (wl_Loc n1 n2))
              ==> ?ck t2.
                    (!ck1. lab_evaluate
                             (lab_state_clock_fupd (K ((lab_state_clock t + ck) + ck1)) t) =
                           lab_evaluate (lab_state_clock_fupd (K (lab_state_clock t2 + ck1)) t2)) /\
                    (!m. IS_SOME (lookup m (stack_state_code s'))
                         ==> IS_SOME (loc_to_pc m 0 (lab_state_code t2))) /\
                    (!w. loc_to_pc n1 n2 (lab_state_code t2) = SOME w
                         ==> w = lab_state_pc t2 /\ stack_to_labProof_state_rel s' t2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t:(A,C,FFI)lab_state`; `n:num`;
                 `prog:(A)stack_prog`] S2LP2AUX_state_rel_code) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `pc:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pc = lab_state_pc (t:(A,C,FFI)lab_state)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `loc_to_pc n 0 (lab_state_code (t:(A,C,FFI)lab_state)) = SOME pc` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prog:(A)stack_prog`; `s:(A,C,FFI)stack_state`; `T`;
                 `r:((A)stack_result)option`; `s':(A,C,FFI)stack_state`; `n:num`;
                 `next_lab (prog:(A)stack_prog) 2`; `[]:num list`; `[]:num list`;
                 `t:(A,C,FFI)lab_state`] flatten_correct) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND; ALL; IS_SOME_DEF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` MP_TAC)) THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN CASE_REWRITE_TAC[halt_view_def; result_view_def; OPTION_MAP_DEF] THENL
  [MESON_TAC[]; MESON_TAC[];
   STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
   DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[lab_evaluate_def] THEN SIMP[] THEN
   REWRITE_TAC[lab_state_component_equality] THEN SIMP[] THEN ASM_REWRITE_TAC[];
   MESON_TAC[]]);;

(* HOL4 line 2741 (the case on w with the literal pattern Word 0w is a      *)
(* match on wl_Word w1 with a test w1 = word 0) *)
let flatten_call_correct = prove
 (CASE_TERM
  `!start (s1:(A,C,FFI)stack_state) res s2 (t1:(A,C,FFI)lab_state).
     stack_evaluate (stack_Call NONE (INL start) NONE,s1) = (res,s2) /\
     stack_to_labProof_state_rel s1 t1 /\
     loc_to_pc start 0 (lab_state_code t1) = SOME (lab_state_pc t1) /\
     ~(res = SOME stack_Error) /\
     (~(res = SOME stack_TimeOut)
      ==> (?w. res = SOME (stackSem_Halt (wl_Word w))) \/
          (?f. res = SOME (stack_FinalFFI f)) \/
          (?n. res = SOME (stack_Result (wl_Loc n 0)) /\
               (!s:(A,C,FFI)stack_state.
                  subspt (stack_state_code s1) (stack_state_code s) /\
                  ~(stack_state_clock s = 0)
                  ==> ?t. stack_evaluate (stack_Call NONE (INL n) NONE,s) =
                            (SOME (stackSem_Halt (wl_Word (word 0))),t) /\
                          stack_state_ffi t = stack_state_ffi s /\
                          stack_state_clock t = stack_state_clock s - 1)))
     ==> ?ck r2 t2.
           lab_evaluate (lab_state_clock_fupd (K ((lab_state_clock t1 - 1) + ck)) t1) = (r2,t2) /\
           (!f. res = SOME (stack_FinalFFI f) ==> r2 = target_Halt (FFI_outcome f)) /\
           (!w. res = SOME (stackSem_Halt w)
                ==> r2 = (match w with
                            wl_Word w1 -> if w1 = word 0 then target_Halt Success
                                          else target_Halt Resource_limit_hit
                          | _ -> target_Error)) /\
           (!n. res = SOME (stack_Result (wl_Loc n 0)) ==> r2 = target_Halt Success) /\
           lab_state_ffi t2 = stack_state_ffi s2 /\
           ~(r2 = target_Error) /\ (res = SOME stack_TimeOut ==> r2 = target_TimeOut)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hyp"))))) THEN
  MP_TAC(ISPECL [`start:num`; `s1:(A,C,FFI)stack_state`; `res:((A)stack_result)option`;
                 `s2:(A,C,FFI)stack_state`] S2LP2AUX_call_none) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `prog:(A)stack_prog` (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP2AUX_state_rel_basic) THEN
    MAP_EVERY EXISTS_TAC [`0`; `target_TimeOut`;
                          `lab_state_clock_fupd (K 0) (t1:(A,C,FFI)lab_state)`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 - 1 = 0`] THEN
    ONCE_REWRITE_TAC[lab_evaluate_def] THEN SIMP[] THEN
    REWRITE_TAC[stack_empty_env_def] THEN SIMP[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`prog:(A)stack_prog`; `stack_dec_clock (s1:(A,C,FFI)stack_state)`;
                 `res:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`; `start:num`;
                 `lab_dec_clock (t1:(A,C,FFI)lab_state)`] S2LP2AUX_body) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[stack_to_labProof_state_rel_dec_clock] THEN
    REWRITE_TAC[stack_dec_clock_def; lab_dec_clock_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lab_dec_clock_def] THEN SIMP[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "halt") (CONJUNCTS_THEN2 (LABEL_TAC "ffi")
    (CONJUNCTS_THEN2 (LABEL_TAC "to") (LABEL_TAC "res")))) THEN
  ASM_CASES_TAC `res = SOME (stack_TimeOut:(A)stack_result)` THENL
   [REMOVE_THEN "to" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `target_TimeOut`; `t2:(A,C,FFI)lab_state`] THEN
    ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  REMOVE_THEN "hyp" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [(* Halt *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REMOVE_THEN "halt" (MP_TAC o SPEC `wl_Word (w:A word)`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `halt_word_view (wl_Word (w:A word))`;
                          `t2:(A,C,FFI)lab_state`] THEN
    ASM_REWRITE_TAC[] THEN SIMP[halt_word_view_DEF] THEN COND_CASES_TAC THEN SIMP[];
    (* FFI *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REMOVE_THEN "ffi" (MP_TAC o SPEC `f:final_event`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `target_Halt (FFI_outcome f)`;
                          `t2:(A,C,FFI)lab_state`] THEN
    ASM_REWRITE_TAC[] THEN SIMP[];
    (* Result *)
    FIRST_X_ASSUM(LABEL_TAC "cont") THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REMOVE_THEN "res" (MP_TAC o SPECL [`n:num`; `0`]) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "A") (CONJUNCTS_THEN2 (LABEL_TAC "C1") (LABEL_TAC "C2"))))) THEN
    REMOVE_THEN "cont" (MP_TAC o SPEC
      `stack_state_clock_fupd (K (stack_state_clock s2 + 1)) (s2:(A,C,FFI)stack_state)`) THEN
    ANTS_TAC THENL
     [SIMP[ARITH_RULE `~(x + 1 = 0)`] THEN
      MP_TAC(ISPECL [`prog:(A)stack_prog`; `stack_dec_clock (s1:(A,C,FFI)stack_state)`;
                     `SOME (stack_Result (wl_Loc n 0)):((A)stack_result)option`;
                     `s2:(A,C,FFI)stack_state`] stack_evaluate_mono) THEN
      ASM_REWRITE_TAC[stack_dec_clock_def] THEN SIMP[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`n:num`;
                   `stack_state_clock_fupd (K (stack_state_clock s2 + 1)) (s2:(A,C,FFI)stack_state)`;
                   `SOME (stackSem_Halt (wl_Word (word 0))):((A)stack_result)option`;
                   `t:(A,C,FFI)stack_state`] S2LP2AUX_call_none) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CAKE_SIMP_RULE[ARITH_RULE `~(x + 1 = 0)`; ARITH_RULE `(x + 1) - 1 = x`;
                                       S2LP2AUX_stack_clock_id] o
               REWRITE_RULE[stack_dec_clock_def]) THEN
    DISCH_THEN(X_CHOOSE_THEN `prog2:(A)stack_prog` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "C1" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
    REWRITE_TAC[IS_SOME_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num` ASSUME_TAC) THEN
    REMOVE_THEN "C2" (MP_TAC o SPEC `w:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    MP_TAC(ISPECL [`prog2:(A)stack_prog`; `s2:(A,C,FFI)stack_state`;
                   `SOME (stackSem_Halt (wl_Word (word 0))):((A)stack_result)option`;
                   `t:(A,C,FFI)stack_state`; `n:num`; `t2:(A,C,FFI)lab_state`] S2LP2AUX_body) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `wl_Word (word 0):(A)word_loc` o CONJUNCT1) THEN
    REWRITE_TAC[halt_word_view_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t3:(A,C,FFI)lab_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck + ck2:num`; `target_Halt Success`; `t3:(A,C,FFI)lab_state`] THEN
    REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN SIMP[]]);;


(* HOL4 line 2827 (the first argument is the universe (:FFI#C), as for      *)
(* backend_common_word_shift: halt_assum_DEF takes any set, halt_assum_def   *)
(* is the HOL4 statement) *)
let halt_assum_DEF = new_definition
  `halt_assum (u:FFI#C->bool) (code:((A)stack_prog)spt) <=>
     !s:(A,C,FFI)stack_state.
       subspt code (stack_state_code s) /\ ~(stack_state_clock s = 0)
       ==> ?t. stack_evaluate (stack_Call NONE (INL 1) NONE,s) =
                 (SOME (stackSem_Halt (wl_Word (word 0))),t) /\
               stack_state_ffi t = stack_state_ffi s /\
               stack_state_clock t = stack_state_clock s - 1`;;

let halt_assum_def = prove
 (`!(code:((A)stack_prog)spt).
     halt_assum (:FFI#C) code <=>
     !s:(A,C,FFI)stack_state.
       subspt code (stack_state_code s) /\ ~(stack_state_clock s = 0)
       ==> ?t. stack_evaluate (stack_Call NONE (INL 1) NONE,s) =
                 (SOME (stackSem_Halt (wl_Word (word 0))),t) /\
               stack_state_ffi t = stack_state_ffi s /\
               stack_state_clock t = stack_state_clock s - 1`,
  REWRITE_TAC[halt_assum_DEF]);;

(* helpers for flatten_semantics: the runs of a lab state at two clocks that *)
(* do not time out agree; a simulation of the stack runs by lab runs with   *)
(* the same results and ffi gives the same observable semantics             *)

let S2LP2AUX_lab_det = prove
 (`!(t:(A,C,FFI)lab_state) k1 k2 r1 r2 t1 t2.
     lab_evaluate (lab_state_clock_fupd (K k1) t) = (r1,t1) /\
     lab_evaluate (lab_state_clock_fupd (K k2) t) = (r2,t2) /\
     ~(r1 = target_TimeOut) /\ ~(r2 = target_TimeOut)
     ==> r1 = r2 /\ lab_state_ffi t1 = lab_state_ffi t2`,
  SUBGOAL_THEN
   `!(t:(A,C,FFI)lab_state) k1 d r1 r2 t1 t2.
     lab_evaluate (lab_state_clock_fupd (K k1) t) = (r1,t1) /\
     lab_evaluate (lab_state_clock_fupd (K (k1 + d)) t) = (r2,t2) /\
     ~(r1 = target_TimeOut)
     ==> r1 = r2 /\ lab_state_ffi t1 = lab_state_ffi t2`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`lab_state_clock_fupd (K k1) (t:(A,C,FFI)lab_state)`;
                   `r1:machine_result`; `t1:(A,C,FFI)lab_state`; `d:num`]
                  evaluate_ADD_clock) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  ASM_MESON_TAC[]);;

let S2LP2AUX_lab_mono_clock = prove
 (`!(t:(A,C,FFI)lab_state) k1 k2 r1 t1.
     lab_evaluate (lab_state_clock_fupd (K k1) t) = (r1,t1) /\
     ~(r1 = target_TimeOut) /\ k1 <= k2
     ==> FST (lab_evaluate (lab_state_clock_fupd (K k2) t)) = r1 /\
         lab_state_ffi (SND (lab_evaluate (lab_state_clock_fupd (K k2) t))) =
         lab_state_ffi t1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`lab_state_clock_fupd (K k1) (t:(A,C,FFI)lab_state)`;
                 `r1:machine_result`; `t1:(A,C,FFI)lab_state`; `d:num`]
                evaluate_ADD_clock) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let S2LP2AUX_lab_io_mono = prove
 (`!(t:(A,C,FFI)lab_state) k1 k2.
     k1 <= k2 ==>
     isPREFIX
       (ffi_state_io_events (lab_state_ffi
          (SND (lab_evaluate (lab_state_clock_fupd (K k1) t)))))
       (ffi_state_io_events (lab_state_ffi
          (SND (lab_evaluate (lab_state_clock_fupd (K k2) t)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lab_state_clock_fupd (K k1) (t:(A,C,FFI)lab_state)`
          (INST [`d:num`,`extra:num`] lab_evaluate_add_clock_io_events_mono)) THEN
  SIMP[]);;

let S2LP2AUX_lab_io_chain = prove
 (`!(t:(A,C,FFI)lab_state).
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (lab_state_ffi
          (SND (lab_evaluate (lab_state_clock_fupd (K k) t)))))) (:num))`,
  GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[S2LP2AUX_lab_io_mono; LE_CASES]);;
let S2LP2AUX_stack_det = prove
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

let S2LP2AUX_stack_io_mono = prove
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

let S2LP2AUX_stack_io_chain = prove
 (`!p (x:(A,C,FFI)stack_state).
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (stack_state_ffi
          (SND (stack_evaluate (p,stack_state_clock_fupd (K k) x)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[S2LP2AUX_stack_io_mono; LE_CASES]);;

let S2LP2AUX_some_NONE = prove
 (`!P:A->bool. (some) P = NONE <=> !x. ~P x`,
  GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[option_DISTINCT]);;
let S2LP2AUX_oc_cases = prove
 (CASE_TERM
  `!(r0:(A)stack_result) outcome.
     (match r0 with
        stack_FinalFFI e -> outcome = FFI_outcome e
      | stackSem_Halt w -> outcome = (if w = wl_Word (word 0) then Success
                                      else Resource_limit_hit)
      | stack_Result _ -> outcome = Success
      | _ -> F) <=>
     (?e. r0 = stack_FinalFFI e /\ outcome = FFI_outcome e) \/
     (?w. r0 = stackSem_Halt w /\
          outcome = (if w = wl_Word (word 0) then Success else Resource_limit_hit)) \/
     (?x. r0 = stack_Result x /\ outcome = Success)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r0:(A)stack_result` (cases "stack_result")) THEN
  CASE_REWRITE_TAC[] THEN SIMP[]);;
let S2LP2AUX_option_CASE_cong = prove
 (`!(a:B option) b (n1:C) n2 f.
     a = b /\ (b = NONE ==> n1 = n2) ==> option_CASE a n1 f = option_CASE b n2 f`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `b:B option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN MESON_TAC[option_CASE]);;
let S2LP2AUX_FST_EQ = prove
 (`!(p:A#B) a. FST p = a <=> p = (a,SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND]);;
let S2LP2AUX_semantics_sim = prove
 (`!start (s:(A,C,FFI)stack_state) (t:(A,C,FFI)lab_state).
     (!k r s1.
        stack_evaluate (stack_Call NONE (INL start) NONE,stack_state_clock_fupd (K k) s) =
          (r,s1) /\
        (r = SOME stack_TimeOut \/ r = SOME (stack_Result (wl_Loc 1 0)) \/
         (?w. r = SOME (stackSem_Halt (wl_Word w))) \/ (?f. r = SOME (stack_FinalFFI f)))
        ==> ?ck r2 t1.
              lab_evaluate (lab_state_clock_fupd (K ((k - 1) + ck)) t) = (r2,t1) /\
              lab_state_ffi t1 = stack_state_ffi s1 /\
              (r = SOME stack_TimeOut ==> r2 = target_TimeOut) /\
              (r = SOME (stack_Result (wl_Loc 1 0)) ==> r2 = target_Halt Success) /\
              (!w. r = SOME (stackSem_Halt (wl_Word w))
                   ==> r2 = target_Halt (if w = word 0 then Success else Resource_limit_hit)) /\
              (!f. r = SOME (stack_FinalFFI f) ==> r2 = target_Halt (FFI_outcome f))) /\
     ~(stack_semantics start s = Fail)
     ==> lab_semantics t = stack_semantics start s`,
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
   `!k. ?ck r2 t1.
      lab_evaluate (lab_state_clock_fupd (K ((k - 1) + ck)) (t:(A,C,FFI)lab_state)) = (r2,t1) /\
      lab_state_ffi t1 =
        stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)))) /\
      (FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                            stack_state_clock_fupd (K k) s)) = SOME stack_TimeOut
       ==> r2 = target_TimeOut) /\
      (~(FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                              stack_state_clock_fupd (K k) s)) = SOME stack_TimeOut)
       ==> ?r0 outcome.
             FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                  stack_state_clock_fupd (K k) s)) = SOME r0 /\
             ((?e. r0 = stack_FinalFFI e /\ outcome = FFI_outcome e) \/
              (?w. r0 = stackSem_Halt w /\
                   outcome = (if w = wl_Word (word 0) then Success else Resource_limit_hit)) \/
              (?x. r0 = stack_Result x /\ outcome = Success)) /\
             r2 = target_Halt outcome) /\
      (!r0 outcome.
         FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                              stack_state_clock_fupd (K k) s)) = SOME r0 /\
         ((?e. r0 = stack_FinalFFI e /\ outcome = FFI_outcome e) \/
          (?w. r0 = stackSem_Halt w /\
               outcome = (if w = wl_Word (word 0) then Success else Resource_limit_hit)) \/
          (?x. r0 = stack_Result x /\ outcome = Success))
         ==> r2 = target_Halt outcome)`
   (LABEL_TAC "sim2") THENL
   [GEN_TAC THEN
    MP_TAC(ISPEC `stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                    stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`] THEN
    DISCH_THEN(LABEL_TAC "run") THEN
    USE_THEN "run" (fun eqth -> REWRITE_TAC[eqth; FST; SND]) THEN
    USE_THEN "run" (fun eqth -> USE_THEN "oks" (MP_TAC o REWRITE_RULE[eqth; FST] o SPEC `k:num`)) THEN
    DISCH_TAC THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `r:((A)stack_result)option`;
                                    `s1:(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:machine_result`
      (X_CHOOSE_THEN `t1:(A,C,FFI)lab_state` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `r2:machine_result`; `t1:(A,C,FFI)lab_state`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:A word` SUBST_ALL_TAC)
                        (X_CHOOSE_THEN `f:final_event` SUBST_ALL_TAC)))) THEN
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ~(FST (lab_evaluate (lab_state_clock_fupd (K k) (t:(A,C,FFI)lab_state))) =
                      target_Error)`
   (LABEL_TAC "noerr") THENL
   [GEN_TAC THEN
    MP_TAC(ISPEC `lab_evaluate (lab_state_clock_fupd (K k) (t:(A,C,FFI)lab_state))`
             PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:machine_result`; `t0:(A,C,FFI)lab_state`] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "sim2" (MP_TAC o SPEC `k + 1`) THEN REWRITE_TAC[ADD_SUB] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:machine_result`
      (X_CHOOSE_THEN `t1:(A,C,FFI)lab_state` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "to")
          (CONJUNCTS_THEN2 (LABEL_TAC "nto") (LABEL_TAC "all")))))))) THEN
    MP_TAC(ISPECL [`t:(A,C,FFI)lab_state`; `k:num`; `k + ck:num`; `target_Error`;
                   `t0:(A,C,FFI)lab_state`] S2LP2AUX_lab_mono_clock) THEN
    ASM_REWRITE_TAC[LE_ADD; FST] THEN SIMP[] THEN DISCH_THEN(SUBST_ALL_TAC o CONJUNCT1) THEN
    ASM_CASES_TAC
     `FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                           stack_state_clock_fupd (K (k + 1)) (s:(A,C,FFI)stack_state))) =
      SOME stack_TimeOut` THENL
     [REMOVE_THEN "to" MP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
      REMOVE_THEN "nto" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k oc t'.
      lab_evaluate (lab_state_clock_fupd (K k) (t:(A,C,FFI)lab_state)) = (target_Halt oc,t')
      ==> ?r0. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                    stack_state_clock_fupd (K (k + 1)) (s:(A,C,FFI)stack_state))) =
                 SOME r0 /\
               ((?e. r0 = stack_FinalFFI e /\ oc = FFI_outcome e) \/
                (?w. r0 = stackSem_Halt w /\
                     oc = (if w = wl_Word (word 0) then Success else Resource_limit_hit)) \/
                (?x. r0 = stack_Result x /\ oc = Success)) /\
               stack_state_ffi (SND (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                stack_state_clock_fupd (K (k + 1)) s))) = lab_state_ffi t'`
   (LABEL_TAC "labterm") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "sim2" (MP_TAC o SPEC `k + 1`) THEN REWRITE_TAC[ADD_SUB] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:machine_result`
      (X_CHOOSE_THEN `t1:(A,C,FFI)lab_state` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "to")
          (CONJUNCTS_THEN2 (LABEL_TAC "nto") (LABEL_TAC "all")))))))) THEN
    MP_TAC(ISPECL [`t:(A,C,FFI)lab_state`; `k:num`; `k + ck:num`; `target_Halt oc`;
                   `t':(A,C,FFI)lab_state`] S2LP2AUX_lab_mono_clock) THEN
    ASM_REWRITE_TAC[LE_ADD; FST; SND] THEN SIMP[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_CASES_TAC
     `FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                           stack_state_clock_fupd (K (k + 1)) (s:(A,C,FFI)stack_state))) =
      SOME stack_TimeOut` THENL
     [REMOVE_THEN "to" MP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
      REMOVE_THEN "nto" MP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r0:(A)stack_result` (X_CHOOSE_THEN `outcome:outcome`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `r0:(A)stack_result` THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[lab_semantics_def; stack_semantics_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
    USE_THEN "noerr" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
    USE_THEN "oks" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC S2LP2AUX_option_CASE_cong THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[S2LP2AUX_oc_cases] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `t':(A,C,FFI)lab_state`
        (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC))) THEN
      USE_THEN "labterm" (MP_TAC o SPECL [`k:num`; `outcome:outcome`;
                                         `t':(A,C,FFI)lab_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r0:(A)stack_result` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC
       [`k + 1`;
        `SND (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                stack_state_clock_fupd (K (k + 1)) (s:(A,C,FFI)stack_state)))`;
        `r0:(A)stack_result`; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[GSYM S2LP2AUX_FST_EQ] THEN MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `t':(A,C,FFI)stack_state`
        (X_CHOOSE_THEN `r:(A)stack_result` (X_CHOOSE_THEN `outcome:outcome`
          (CONJUNCTS_THEN2 (LABEL_TAC "run") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
      USE_THEN "sim2" (MP_TAC o SPEC `k:num`) THEN
      USE_THEN "run" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:machine_result`
        (X_CHOOSE_THEN `t1:(A,C,FFI)lab_state` (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
            (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPECL [`r:(A)stack_result`;
                                                          `outcome:outcome`])))))))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY EXISTS_TAC [`(k - 1) + ck:num`; `t1:(A,C,FFI)lab_state`; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[S2LP2AUX_some_NONE] THEN DISCH_THEN(LABEL_TAC "nostop") THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `!k. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                               stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))) =
          SOME stack_TimeOut`
     (LABEL_TAC "div") THENL
     [GEN_TAC THEN
      MP_TAC(ISPEC `stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                      stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))` PAIR_SURJECTIVE) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`] THEN
      DISCH_THEN(LABEL_TAC "run") THEN
      USE_THEN "run" (fun eqth -> REWRITE_TAC[eqth; FST]) THEN
      USE_THEN "run" (fun eqth -> USE_THEN "oks" (MP_TAC o REWRITE_RULE[eqth; FST] o SPEC `k:num`)) THEN
      STRIP_TAC THENL
       [MATCH_MP_TAC(TAUT `F ==> p`) THEN USE_THEN "nostop" (MP_TAC o SPEC
          `Terminate Success (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))`) THEN
        REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                              `stack_Result (wl_Loc 1 0):(A)stack_result`; `Success`];
        MATCH_MP_TAC(TAUT `F ==> p`) THEN USE_THEN "nostop" (MP_TAC o SPEC
          `Terminate (if wl_Word (w:A word) = wl_Word (word 0) then Success
                      else Resource_limit_hit)
             (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))`) THEN
        REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                              `stackSem_Halt (wl_Word (w:A word)):(A)stack_result`;
                              `if wl_Word (w:A word) = wl_Word (word 0) then Success
                               else Resource_limit_hit`];
        MATCH_MP_TAC(TAUT `F ==> p`) THEN USE_THEN "nostop" (MP_TAC o SPEC
          `Terminate (FFI_outcome f)
             (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))`) THEN
        REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                              `stack_FinalFFI f:(A)stack_result`; `FFI_outcome f`]] THEN
      USE_THEN "run" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN
    REWRITE_TAC[S2LP2AUX_lab_io_chain; S2LP2AUX_stack_io_chain] THEN
    REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THENL
     [USE_THEN "sim2" (MP_TAC o SPEC `k + 1`) THEN REWRITE_TAC[ADD_SUB] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:machine_result`
        (X_CHOOSE_THEN `t1:(A,C,FFI)lab_state` (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
      EXISTS_TAC `k + 1` THEN
      REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`t:(A,C,FFI)lab_state`; `k:num`; `k + ck:num`] S2LP2AUX_lab_io_mono) THEN
      ASM_REWRITE_TAC[LE_ADD; SND];
      USE_THEN "sim2" (MP_TAC o SPEC `k:num`) THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:machine_result`
        (X_CHOOSE_THEN `t1:(A,C,FFI)lab_state` (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
      EXISTS_TAC `(k - 1) + ck:num` THEN
      REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
      ASM_REWRITE_TAC[SND; IS_PREFIX_REFL]]]);;

(* HOL4 line 2835 (the first semantics is labSem's, the second stackSem's) *)
let flatten_semantics = prove
 (`!(s1:(A,C,FFI)stack_state) (s2:(A,C,FFI)lab_state) start.
     halt_assum (:FFI#C) (stack_state_code s1) /\
     stack_to_labProof_state_rel s1 s2 /\
     loc_to_pc start 0 (lab_state_code s2) = SOME (lab_state_pc s2) /\
     ~(stack_semantics start s1 = Fail)
     ==> lab_semantics s2 = stack_semantics start s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[halt_assum_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "halt") STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC S2LP2AUX_semantics_sim THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `r:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ok")) THEN
  MP_TAC(ISPECL [`start:num`; `stack_state_clock_fupd (K k) (s1:(A,C,FFI)stack_state)`;
                 `r:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`;
                 `lab_state_clock_fupd (K k) (s2:(A,C,FFI)lab_state)`] flatten_call_correct) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[stack_to_labProof_state_rel_with_clock] THEN SIMP[] THEN
    USE_THEN "ok" STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:machine_result`
    (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `r2:machine_result`; `t2:(A,C,FFI)lab_state`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "ok" STRIP_ASSUME_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 3027 (a record literal without the fields store, stack,        *)
(* stack_space, bitmaps, data_buffer and gc_fun: HOL4 leaves them ARB; here *)
(* nested _fupd on ARB, the first field outermost) *)
let stack_to_labProof_make_init_def = cake_def
  `stack_to_labProof_make_init code coracle regs save_regs (s:(A,C,FFI)lab_state) =
     stack_state_regs_fupd (K (FEMPTY |++ MAP (\r. (r,lab_state_regs s r)) regs))
      (stack_state_fp_regs_fupd (K FEMPTY)
       (stack_state_memory_fupd (K (lab_state_mem s))
        (stack_state_mdomain_fupd (K (lab_state_mem_domain s))
         (stack_state_sh_mdomain_fupd (K (lab_state_shared_mem_domain s))
          (stack_state_use_stack_fupd (K F)
           (stack_state_use_store_fupd (K F)
            (stack_state_use_alloc_fupd (K F)
             (stack_state_compile_fupd
                (K (\c p. lab_state_compile s c (MAP prog_to_section p)))
              (stack_state_compile_oracle_fupd (K coracle)
               (stack_state_code_buffer_fupd (K (lab_state_code_buffer s))
                (stack_state_clock_fupd (K (lab_state_clock s))
                 (stack_state_code_fupd (K code)
                  (stack_state_ffi_fupd (K (lab_state_ffi s))
                   (stack_state_ffi_save_regs_fupd (K save_regs)
                    (stack_state_be_fupd (K (lab_state_be s))
                       (ARB:(A,C,FFI)stack_state))))))))))))))))`;;

(* HOL4 line 3047: val make_init_semantics = flatten_semantics |> Q.INST    *)
(* [s1 |-> make_init code coracle regs save_regs s, s2 |-> s] |> SIMP_RULE  *)
(* std_ss [EVAL (make_init ...).code] (its resulting statement) *)
let make_init_semantics = prove
 (`!code coracle regs save_regs (s:(A,C,FFI)lab_state) start.
     halt_assum (:FFI#C) code /\
     stack_to_labProof_state_rel (stack_to_labProof_make_init code coracle regs save_regs s) s /\
     loc_to_pc start 0 (lab_state_code s) = SOME (lab_state_pc s) /\
     ~(stack_semantics start (stack_to_labProof_make_init code coracle regs save_regs s) = Fail)
     ==> lab_semantics s =
         stack_semantics start (stack_to_labProof_make_init code coracle regs save_regs s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC flatten_semantics THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_to_labProof_make_init_def] THEN SIMP[] THEN ASM_REWRITE_TAC[]);;

(* HOL4 lines 3051-3054: Overloads stack_to_lab_compile, stack_names_compile,*)
(* stack_alloc_compile, stack_remove_compile (the compile functions of the   *)
(* four theories; the HOL Light names already are these)                     *)

(* HOL4 line 3056 (make_init of the lab state is this theory's, then        *)
(* stack_namesProof's, stack_removeProof's make_init_any and make_init_opt, *)
(* stack_allocProof's make_init; HOL4 find_name is tlookup) *)
let full_make_init_def = cake_def
  `full_make_init (stack_conf:stack_to_lab_config) (data_conf:data_to_word_config) max_heap sp
     (offset:A word#A word) bitmaps code (s4:(A,C,FFI)lab_state) save_regs data_sp coracle =
     let ggc = is_gen_gc (data_to_word_config_gc_kind data_conf) in
     let jump = stack_to_lab_config_jump stack_conf in
     let code1 = stack_alloc_compile data_conf (stack_rawcall_compile code) in
     let code2 = stack_remove_compile jump offset ggc max_heap sp InitGlobals_location code1 in
     let code3 = fromAList (stack_names_compile (stack_to_lab_config_reg_names stack_conf) code2) in
     let coracle1 = (I ## MAP stack_alloc_prog_comp ## I) o coracle in
     let coracle2 = (I ## MAP (stack_remove_prog_comp jump offset sp) ## I) o coracle1 in
     let coracle3 =
       (I ## stack_names_compile (stack_to_lab_config_reg_names stack_conf) ## I) o coracle2 in
     let s3 = stack_to_labProof_make_init code3 coracle3
                (MAP (tlookup (stack_to_lab_config_reg_names stack_conf)) [2; 3; 4]) save_regs s4 in
     let s2 = stack_namesProof_make_init (stack_to_lab_config_reg_names stack_conf)
                (fromAList code2) coracle2 s3 in
     let s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump offset sp
                (fromAList code1) s2 in
       (stack_allocProof_make_init data_conf (fromAList code) coracle s1,
        make_init_opt ggc max_heap bitmaps data_sp coracle1 jump offset sp (fromAList code1) s2)`;;

(* helpers: make_init_opt and make_init_any of stack_removeProof *)

let S2LP2AUX_make_init_opt_SOME = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state) t.
     make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code s = SOME t
     ==> ?t0. stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s) = (NONE,t0) /\
              t = init_reduce gen_gc' jump off k code bitmaps data_sp coracle t0 /\
              init_prop gen_gc' max_heap data_sp
                (get_stack_heap_limit max_heap (read_pointers s)) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[make_init_opt_def] THEN
  MP_TAC(ISPEC `stack_evaluate (stack_remove_init_code gen_gc' max_heap k:(A)stack_prog,
                                s:(A,C,FFI)stack_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:((A)stack_result)option`; `t0:(A,C,FFI)stack_state`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CASES_ON `q:((A)stack_result)option` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `t0:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]);;

let S2LP2AUX_make_init_any_buffer = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     buffer_buffer (stack_state_code_buffer
       (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k code s)) = [] /\
     buffer_buffer (stack_state_data_buffer
       (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k code s)) = []`,
  REPEAT GEN_TAC THEN REWRITE_TAC[make_init_any_def] THEN
  CASES_ON `make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code
              (s:(A,C,FFI)stack_state)` THEN
  CASE_REWRITE_TAC[] THENL
   [SIMP[];
    FIRST_ASSUM(MP_TAC o MATCH_MP S2LP2AUX_make_init_opt_SOME) THEN
    REWRITE_TAC[init_prop_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 3073 *)
let full_make_init_buffer = prove
 (`!a b c d e f g (h:(A,C,FFI)lab_state) i j k.
     buffer_buffer (stack_state_code_buffer (FST (full_make_init a b c d e f g h i j k))) = [] /\
     buffer_buffer (stack_state_data_buffer (FST (full_make_init a b c d e f g h i j k))) = []`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[full_make_init_def; LET_DEF; LET_END_DEF; stack_allocProof_make_init_def] THEN
  SIMP[S2LP2AUX_make_init_any_buffer]);;

(* HOL4 line 3086 *)
let full_make_init_ffi = prove
 (`!a b c d e f g (h:(A,C,FFI)lab_state) i j k.
     stack_state_ffi (FST (full_make_init a b c d e f g h i j k)) = lab_state_ffi h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[full_make_init_def; LET_DEF; LET_END_DEF; stack_allocProof_make_init_def] THEN
  SIMP[make_init_any_ffi] THEN
  REWRITE_TAC[stack_namesProof_make_init_def; stack_to_labProof_make_init_def] THEN SIMP[]);;

let S2LP2AUX_make_init_any_compile = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     stack_state_compile
       (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k code s) =
     (\c p. stack_state_compile s c (MAP (stack_remove_prog_comp jump off k) p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[make_init_any_def] THEN
  CASES_ON `make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code
              (s:(A,C,FFI)stack_state)` THEN
  CASE_REWRITE_TAC[] THENL
   [SIMP[];
    FIRST_ASSUM(MP_TAC o MATCH_MP S2LP2AUX_make_init_opt_SOME) THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_consts) THEN
    ASM_REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF] THEN SIMP[]]);;

(* HOL4 line 3093 (the bound config of HOL4's \c is cfg here: c is also the *)
(* third argument; prog_comp of a.reg_names is stack_names', of a.jump e d   *)
(* stack_remove', the last one stack_alloc's) *)
let full_make_init_compile = prove
 (`!a b c d e f g (h:(A,C,FFI)lab_state) i j k.
     stack_state_compile (FST (full_make_init a b c d e f g h i j k)) =
     (\cfg. (\p. lab_state_compile h cfg
                   (MAP prog_to_section
                      (MAP (stack_names_prog_comp (stack_to_lab_config_reg_names a))
                         (MAP (stack_remove_prog_comp (stack_to_lab_config_jump a) e d) p)))) o
            MAP stack_alloc_prog_comp)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[full_make_init_def; LET_DEF; LET_END_DEF; stack_allocProof_make_init_def] THEN
  SIMP[S2LP2AUX_make_init_any_compile] THEN
  REWRITE_TAC[stack_namesProof_make_init_def; stack_to_labProof_make_init_def] THEN SIMP[] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; stack_names_compile_def]);;


(* HOL4 line 3106 (HOL4 read_reg (find_name rnames r) t is                  *)
(* lab_state_regs t (tlookup rnames r); word_list is misc's; the separating *)
(* conjunction of sets is STAR; <=+ is word_ule) *)
let memory_assumption_def = cake_def
  `memory_assumption rnames (bitmaps:(A word)list) data_sp (t:(A,C,FFI)lab_state) <=>
     ?ptr2 ptr3 ptr4 bitmap_ptr.
       lab_state_regs t (tlookup rnames 2) = wl_Word ptr2 /\
       lab_state_regs t (tlookup rnames 3) = wl_Word ptr3 /\
       lab_state_regs t (tlookup rnames 4) = wl_Word ptr4 /\
       lab_state_mem t ptr2 = wl_Word bitmap_ptr /\
       lab_state_mem t (word_add ptr2 bytes_in_word) =
         wl_Word (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       lab_state_mem t (word_add ptr2 (word_mul (word 2) bytes_in_word)) =
         wl_Word (word_add (word_add bitmap_ptr (word_mul bytes_in_word (word data_sp)))
                    (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       lab_state_mem t (word_add ptr2 (word_mul (word 3) bytes_in_word)) =
         wl_Word (buffer_position (lab_state_code_buffer t)) /\
       lab_state_mem t (word_add ptr2 (word_mul (word 4) bytes_in_word)) =
         wl_Word (word_add (buffer_position (lab_state_code_buffer t))
                    (word (buffer_space_left (lab_state_code_buffer t)))) /\
       buffer_buffer (lab_state_code_buffer t) = [] /\
       word_ule ptr2 ptr4 /\ byte_aligned ptr2 /\
       byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
       word_ule (word_mul (word 1024) bytes_in_word) (word_sub ptr4 ptr2) /\
       (misc_word_list bitmap_ptr (MAP wl_Word bitmaps) STAR
        word_list_exists (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps))))
          data_sp STAR
        word_list_exists ptr2
          (val (word_add (word_mul (word_neg (word 1)) ptr2) ptr4) DIV
           val (bytes_in_word:A word)))
         (fun2set (lab_state_mem t,lab_state_mem_domain t))`;;

(* the clause of stack_evaluate of a constructor *)
let s2lp2aux_ev (name:string) : thm =
  find (fun th -> try let l = lhs(snd(strip_forall(concl th))) in
                      fst(dest_const(fst(strip_comb(fst(dest_pair(rand l)))))) = name
                  with Failure _ -> false)
       (CONJUNCTS stack_evaluate_def);;

(* HOL4 line 3132 [local] *)
let halt_assum_lemma = prove
 (`!f jump off gen max_heap k l (code:(num#(A)stack_prog)list).
     halt_assum (:FFI#C)
       (fromAList (stack_names_compile f (stack_remove_compile jump off gen max_heap k l code)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[halt_assum_def] THEN X_GEN_TAC `s:(A,C,FFI)stack_state` THEN
  REWRITE_TAC[subspt_lookup] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `stack_names_comp f (halt_inst (word 0):(A)stack_prog)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[lookup_fromAList; stack_names_compile_def; stack_remove_compile_def;
                stack_remove_init_stubs_def; MAP; APPEND; stack_names_prog_comp_def;
                ALOOKUP_THM] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  REWRITE_TAC[s2lp2aux_ev "stack_Call"] THEN CASE_REWRITE_TAC[stack_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[halt_inst_def] THEN ONCE_REWRITE_TAC[stack_names_comp_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[stack_names_comp_def] THEN CASE_REWRITE_TAC[inst_find_name_def] THEN
  REWRITE_TAC[s2lp2aux_ev "stack_Seq"; s2lp2aux_ev "stack_Inst"; s2lp2aux_ev "stack_Halt";
              stack_inst_def; stack_assign_def; stack_word_exp_def; stack_fix_clock_evaluate] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_get_var_def; stack_set_var_def] THEN SIMP[FLOOKUP_UPDATE] THEN
  CASE_REWRITE_TAC[stack_bad_fun_return_def] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1; stack_empty_env_def; stack_dec_clock_def] THEN SIMP[]);;

(* HOL4 line 3152 [local] (HOL4's unused binder f is left out) *)
let FLOOKUP_regs = prove
 (`!regs n v (s:(A,C,FFI)lab_state).
     FLOOKUP (FEMPTY |++ MAP (\r. (r,lab_state_regs s r)) regs) n = SOME v
     ==> lab_state_regs s n = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flookup_fupdate_list; FLOOKUP_EMPTY] THEN
  CASES_ON `ALOOKUP (REVERSE (MAP (\r. (r,lab_state_regs (s:(A,C,FFI)lab_state) r))
                                  (regs:num list))) n` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_REVERSE; MEM_MAP; PAIR_EQ] THEN MESON_TAC[]);;

(* paired lambdas and pair cases of triples, to compare state_rel with *)
(* the statement of state_rel_make_init *)

let S2LP2AUX_GABS3 = prove
 (`!(f:A->B->C->D) (x:A#B#C). (\(a,b,c). f a b c) x = f (FST x) (FST (SND x)) (SND (SND x))`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let S2LP2AUX_pCASE3 = prove
 (CASE_TERM
  `!(f:A->B->C->D) (x:A#B#C). (match x with (a,b,c) -> f a b c) =
                              f (FST x) (FST (SND x)) (SND (SND x))`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 3161 (the third component of the oracle, HOL4 _, is b0) *)
let state_rel_make_init = prove
 (`!code coracle regs save_regs (s:(A,C,FFI)lab_state).
     stack_to_labProof_state_rel (stack_to_labProof_make_init code coracle regs save_regs s) s <=>
     (!n prog.
        lookup n code = SOME prog
        ==> call_args prog (lab_state_ptr_reg s) (lab_state_len_reg s) (lab_state_ptr2_reg s)
              (lab_state_len2_reg s) (lab_state_link_reg s) /\
            ?pc. stack_to_labProof_code_installed pc
                   (append (FST (stack_to_lab_flatten T prog n (next_lab prog 2) [] [])))
                   (lab_state_code s) /\
                 loc_to_pc n 0 (lab_state_code s) = SOME pc) /\
     ~lab_state_failed s /\
     lab_state_compile_oracle s = (\n. (\(c,p,b0). (c,MAP prog_to_section p)) (coracle n)) /\
     (!k. (\(c,ps,b0).
             ALL (\(n,p).
                    call_args p (lab_state_ptr_reg s) (lab_state_len_reg s)
                      (lab_state_ptr2_reg s) (lab_state_len2_reg s) (lab_state_link_reg s) /\
                    ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                    ALL_DISTINCT (stack_extract_labels p)) ps /\
             ALL_DISTINCT (MAP FST ps)) (coracle k)) /\
     ~(lab_state_link_reg s = lab_state_len_reg s) /\
     ~(lab_state_link_reg s = lab_state_ptr_reg s) /\
     ~(lab_state_link_reg s = lab_state_len2_reg s) /\
     ~(lab_state_link_reg s = lab_state_ptr2_reg s) /\
     ~(lab_state_link_reg s IN save_regs) /\
     domain code = set_of_list (MAP Section_num (lab_state_code s)) /\
     ALL sec_labels_ok (lab_state_code s) /\
     (!k i n. k IN save_regs ==> lab_state_io_regs s n i k = NONE) /\
     (!k n. k IN save_regs ==> lab_state_cc_regs s n k = NONE) /\
     (!x. x IN lab_state_mem_domain s ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     (!x. x IN lab_state_shared_mem_domain s ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     good_dimindex (:A)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def; stack_to_labProof_make_init_def] THEN SIMP[] THEN
  REWRITE_TAC[S2LP2AUX_GABS3; S2LP2AUX_pCASE3] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[FLOOKUP_regs]);;

let S2LP2AUX_MAP_FST_remove_prog_comp = prove
 (`!jump off k (l:(num#(A)stack_prog)list).
     MAP FST (MAP (stack_remove_prog_comp jump off k) l) = MAP FST l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; stack_remove_prog_comp_def]);;

let S2LP2AUX_MAP_FST_alloc_prog_comp = prove
 (`!(l:(num#(A)stack_prog)list).
     MAP FST (MAP stack_alloc_prog_comp l) = MAP FST l`,
  GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; stack_alloc_prog_comp_def]);;

let S2LP2AUX_MAP_FST_names_prog_comp = prove
 (`!f (l:(num#(A)stack_prog)list).
     MAP FST (MAP (stack_names_prog_comp f) l) = MAP FST l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; stack_names_prog_comp_def]);;

(* HOL4 line 3194 [local] *)
let MAP_FST_compile_compile = prove
 (`!jump off gen max_heap k c (code:(num#(A)stack_prog)list).
     MAP FST (stack_remove_compile jump off gen max_heap k InitGlobals_location
                (stack_alloc_compile c (stack_rawcall_compile code))) =
     CONS 0 (CONS 1 (CONS 2 (CONS gc_stub_location (MAP FST code))))`,
  REWRITE_TAC[stack_remove_compile_def; stack_remove_init_stubs_def; stack_alloc_compile_def;
              stack_alloc_stubs_def; MAP_APPEND; MAP; APPEND; S2LP2AUX_MAP_FST_remove_prog_comp;
              S2LP2AUX_MAP_FST_alloc_prog_comp; stack_rawcallProof_MAP_FST_compile;
              stack_remove_prog_comp_def; FST]);;

(* HOL4 line 3209: val sextract_labels_def (an abbreviation) *)

(* next_lab p aux is at least aux (HOL4 uses stack_allocProof next_lab_EQ_MAX) *)
let S2LP2AUX_next_lab_ge = prove
 (`!(p:(A)stack_prog) aux. aux <= next_lab p aux`,
  MATCH_MP_TAC next_lab_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[next_lab_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[LE_REFL] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  ASM_MESON_TAC[LE_TRANS; LE_REFL; ARITH_RULE `!x y. x <= MAX x y /\ y <= MAX x y`]);;

(* HOL4 line 3211 [allow_rebind] (rebinds the theorem of HOL4 line 1022) *)
let next_lab_non_zero = prove
 (`!(p:(A)stack_prog). 1 <= next_lab p 1 /\ 2 <= next_lab p 2`,
  REWRITE_TAC[S2LP2AUX_next_lab_ge]);;

(* HOL4 line 3272 [local] (the same statement as at HOL4 line 228) *)
let MAP_prog_to_section_FST = prove
 (CASE_TERM
  `!(prog:(num#(A)stack_prog)list).
     MAP (\s. match s with Section n v -> n) (MAP prog_to_section prog) = MAP FST prog`,
  MATCH_ACCEPT_TAC MAP_prog_to_section_FST);;

(* HOL4 line 3280 [local] *)
let extract_label_store_list_code = prove
 (`!a t ls. stack_extract_labels (store_list_code a t ls:(A)stack_prog) = []`,
  MATCH_MP_TAC store_list_code_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[store_list_code_def; stack_list_Seq_def; stack_extract_labels_def; APPEND]);;

(* labels of the code that stack_remove and stack_alloc add, and the label *)
(* property of stack_to_lab_compile_lab_pres through the four passes      *)

let S2LP2AUX_el_init_code = prove
 (`!gen max_heap k. stack_extract_labels (stack_remove_init_code gen max_heap k:(A)stack_prog) = []`,
  REWRITE_TAC[stack_remove_init_code_def; LET_DEF; LET_END_DEF; stack_list_Seq_def;
              stack_extract_labels_def; APPEND; init_memory_def; extract_label_store_list_code]);;

let S2LP2AUX_el_halt_inst = prove
 (`!w:A word. stack_extract_labels (halt_inst w) = []`,
  REWRITE_TAC[halt_inst_def; stack_extract_labels_def; APPEND]);;

let s2lp2aux_gc_code_defs =
  [memcpy_code_def; clear_top_inst_def; word_gc_move_code_def; word_gc_move_list_code_def;
   word_gc_move_loop_code_def; word_gc_move_bitmap_code_def; word_gc_move_bitmaps_code_def;
   word_gc_move_roots_bitmaps_code_def; word_gen_gc_move_code_def;
   word_gen_gc_partial_move_code_def; word_gen_gc_move_bitmap_code_def;
   word_gen_gc_partial_move_bitmap_code_def; word_gen_gc_move_bitmaps_code_def;
   word_gen_gc_partial_move_bitmaps_code_def; word_gen_gc_move_roots_bitmaps_code_def;
   word_gen_gc_partial_move_roots_bitmaps_code_def; word_gen_gc_move_list_code_def;
   word_gen_gc_partial_move_list_code_def; word_gen_gc_move_data_code_def;
   word_gen_gc_partial_move_ref_list_code_def; word_gen_gc_partial_move_data_code_def;
   word_gen_gc_move_refs_code_def; word_gen_gc_move_loop_code_def;
   word_gc_partial_or_full_def; SetNewTrigger_def];;

let S2LP2AUX_el_word_gc_code = prove
 (`!c. stack_extract_labels (word_gc_code c:(A)stack_prog) = []`,
  GEN_TAC THEN REWRITE_TAC[word_gc_code_def] THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC s2lp2aux_gc_code_defs THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[stack_list_Seq_def; APPEND; LET_DEF; LET_END_DEF;
                                      stack_extract_labels_def])) THEN
  EVERY_CASE_TAC THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[stack_list_Seq_def; APPEND; LET_DEF; LET_END_DEF;
                                      stack_extract_labels_def])));;

let S2LP2AUX_lp_names = prove
 (`!f (l:(num#(A)stack_prog)list).
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) l
     ==> ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                      ALL_DISTINCT (stack_extract_labels p)) (stack_names_compile f l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_names_compile_def; ALL_MAP] THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_names_prog_comp_def] THEN
  REWRITE_TAC[GSYM stack_names_lab_pres]);;

let S2LP2AUX_lp_remove = prove
 (`!jump off gen mh k start (l:(num#(A)stack_prog)list).
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) l
     ==> ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                      ALL_DISTINCT (stack_extract_labels p))
           (stack_remove_compile jump off gen mh k start l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_remove_compile_def; stack_remove_init_stubs_def; ALL_APPEND; ALL_MAP] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [CASE_REWRITE_TAC[ALL; stack_extract_labels_def; APPEND; S2LP2AUX_el_init_code;
                S2LP2AUX_el_halt_inst; ALL_DISTINCT];
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_remove_prog_comp_def] THEN
    REWRITE_TAC[GSYM stack_remove_lab_pres]]);;

let S2LP2AUX_lp_rawcall = prove
 (`!(l:(num#(A)stack_prog)list).
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) l
     ==> ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                      ALL_DISTINCT (stack_extract_labels p)) (stack_rawcall_compile l)`,
  GEN_TAC THEN REWRITE_TAC[stack_rawcall_compile_def; LET_DEF; LET_END_DEF; ALL_MAP] THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[extract_labels_comp]);;

let S2LP2AUX_lp_alloc = prove
 (`!c (l:(num#(A)stack_prog)list).
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) l
     ==> ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                      ALL_DISTINCT (stack_extract_labels p)) (stack_alloc_compile c l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_alloc_compile_def; stack_alloc_stubs_def; ALL_APPEND; ALL_MAP] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [CASE_REWRITE_TAC[ALL; stack_extract_labels_def; APPEND; S2LP2AUX_el_word_gc_code;
                     ALL_DISTINCT];
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_alloc_prog_comp_def] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `p:(A)stack_prog`] THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL(ISPECL [`n:num`; `next_lab (p:(A)stack_prog) 2`; `p:(A)stack_prog`]
                           stack_alloc_lab_pres)) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    MP_TAC(ISPEC `stack_alloc_comp n (next_lab (p:(A)stack_prog) 2) p` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`cp:(A)stack_prog`; `nl:num`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; FST] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    CASE_REWRITE_TAC[] THEN SIMP[]]);;

(* HOL4 line 3288 *)
let stack_to_lab_compile_lab_pres = prove
 (`!(prog:(num#(A)stack_prog)list) c c2 c3 sp offset.
     ALL (\n. ~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = gc_stub_location)) (MAP FST prog) /\
     ALL (\(n,p). let labs = stack_extract_labels p in
                    ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\ ALL_DISTINCT labs)
       prog /\
     ALL_DISTINCT (MAP FST prog)
     ==> labels_ok (stack_to_lab_compile c c2 c3 sp offset prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC prog_to_section_labels_ok THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC S2LP2AUX_lp_names THEN MATCH_MP_TAC S2LP2AUX_lp_remove THEN
    MATCH_MP_TAC S2LP2AUX_lp_alloc THEN MATCH_MP_TAC S2LP2AUX_lp_rawcall THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[stack_names_compile_def; S2LP2AUX_MAP_FST_names_prog_comp;
                MAP_FST_compile_compile] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_REWRITE_TAC[ALL_DISTINCT; MEM; gc_stub_location_eq] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[gc_stub_location_eq]]);;


(* HOL4 line 3349 *)
let stack_to_labProof_good_code_def = cake_def
  `stack_to_labProof_good_code sp (code:(num#(A)stack_prog)list) <=>
     ALL_DISTINCT (MAP FST code) /\
     ALL (\(k,prog). stack_num_stubs <= k /\ alloc_arg prog) code /\
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND code) /\
     ALL (\p. reg_bound p sp) (MAP SND code) /\
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) code`;;

(* HOL4 line 3361 (HOL4 Abbrev b is b) *)
let stack_to_labProof_contain_def = cake_def
  `stack_to_labProof_contain (b:bool) <=> b`;;


(* helpers for full_make_init_semantics: the four compiler passes keep the *)
(* call_args and label properties, the state relation for the made lab state,*)
(* and the assumptions of the make_init_semantics of stack_names,          *)
(* stack_remove and stack_alloc                                             *)

let S2LP2AUX_ca_alloc_map = prove
 (`!(l:(num#(A)stack_prog)list).
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND l)
     ==> ALL (\p. call_args p 1 2 3 4 0) (MAP SND (MAP stack_alloc_prog_comp l))`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `ARB:data_to_word_config` o
             MATCH_MP stack_allocProof_stack_alloc_call_args) THEN
  SIMP[stack_alloc_compile_def; MAP_APPEND; ALL_APPEND]);;

let S2LP2AUX_ca_remove_map = prove
 (`!jump off k (l:(num#(A)stack_prog)list).
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND l)
     ==> ALL (\p. call_args p 1 2 3 4 0) (MAP SND (MAP (stack_remove_prog_comp jump off k) l))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `F`; `0`; `k:num`; `0`;
                 `l:(num#(A)stack_prog)list`;
                 `stack_remove_compile jump (off:A word#A word) F 0 k 0 l`]
         stack_remove_call_args) THEN
  ASM_REWRITE_TAC[stack_remove_compile_def; MAP_APPEND; ALL_APPEND] THEN SIMP[]);;

let S2LP2AUX_ca_code2 = prove
 (`!jump off gen mh k start c (code:(num#(A)stack_prog)list).
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND code)
     ==> ALL (\p. call_args p 1 2 3 4 0)
           (MAP SND (stack_remove_compile jump off gen mh k start
                       (stack_alloc_compile c (stack_rawcall_compile code))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC stack_remove_call_args THEN
  MAP_EVERY EXISTS_TAC [`jump:bool`; `off:A word#A word`; `gen:bool`; `mh:num`; `k:num`;
                        `start:num`;
   `stack_alloc_compile c (stack_rawcall_compile (code:(num#(A)stack_prog)list))`] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC stack_allocProof_stack_alloc_call_args THEN
  ASM_REWRITE_TAC[stack_rawcallProof_stack_alloc_call_args]);;

let S2LP2AUX_lp_remove_map = prove
 (`!jump off k (l:(num#(A)stack_prog)list).
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) l
     ==> ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                      ALL_DISTINCT (stack_extract_labels p))
           (MAP (stack_remove_prog_comp jump off k) l)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`jump:bool`; `off:A word#A word`; `F`; `0`; `k:num`; `0`] o
             MATCH_MP S2LP2AUX_lp_remove) THEN
  SIMP[stack_remove_compile_def; ALL_APPEND]);;

let S2LP2AUX_lp_alloc_map = prove
 (`!(l:(num#(A)stack_prog)list).
     ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                  ALL_DISTINCT (stack_extract_labels p)) l
     ==> ALL (\(n,p). ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                      ALL_DISTINCT (stack_extract_labels p))
           (MAP stack_alloc_prog_comp l)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `ARB:data_to_word_config` o MATCH_MP S2LP2AUX_lp_alloc) THEN
  SIMP[stack_alloc_compile_def; ALL_APPEND]);;

let S2LP2AUX_ALL_SND_PAIR = prove
 (`!(P:B->bool) (Q:A->B->bool) l.
     ALL P (MAP SND l) /\ ALL (\(n,p). Q n p) l ==> ALL (\(n,p). P p /\ Q n p) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]);;

let S2LP2AUX_oracle3 = prove
 (`!f jump (offset:A word#A word) sp (coracle:num->C#(num#(A)stack_prog)list#(A word)list).
     (\n. let (c,p,b) = coracle n in (c,compile_no_stubs f jump offset sp p)) =
     (\n. (\(c,p,b0). (c,MAP prog_to_section p))
            (((I ## stack_names_compile f ## I) o
              (I ## MAP (stack_remove_prog_comp jump offset sp) ## I) o
              (I ## MAP stack_alloc_prog_comp ## I) o coracle) n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `n:num` THEN
  SPEC_TAC(`(coracle:num->C#(num#(A)stack_prog)list#(A word)list) n`,
           `x:C#(num#(A)stack_prog)list#(A word)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; compile_no_stubs_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let S2LP2AUX_names_call_args = prove
 (`!f (l:(num#(A)stack_prog)list).
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND l)
     ==> ALL (\p. call_args p (tlookup f 1) (tlookup f 2) (tlookup f 3) (tlookup f 4)
                    (tlookup f 0)) (MAP SND (stack_names_compile f l))`,
  MESON_TAC[stack_names_call_args]);;

let S2LP2AUX_oracle3_ok = prove
 (`!f jump (offset:A word#A word) sp (p:(num#(A)stack_prog)list) ptr len ptr2 len2 link.
     tlookup f 1 = ptr /\ tlookup f 2 = len /\ tlookup f 3 = ptr2 /\ tlookup f 4 = len2 /\
     tlookup f 0 = link /\ stack_to_labProof_good_code sp p
     ==> ALL (\(n,p). call_args p ptr len ptr2 len2 link /\
                      ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                      ALL_DISTINCT (stack_extract_labels p))
           (stack_names_compile f (MAP (stack_remove_prog_comp jump offset sp)
                                     (MAP stack_alloc_prog_comp p))) /\
         ALL_DISTINCT (MAP FST (stack_names_compile f
                                  (MAP (stack_remove_prog_comp jump offset sp)
                                     (MAP stack_alloc_prog_comp p))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_to_labProof_good_code_def] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC S2LP2AUX_ALL_SND_PAIR THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:num spt`;
         `MAP (stack_remove_prog_comp jump offset sp) (MAP stack_alloc_prog_comp
            (p:(num#(A)stack_prog)list))`] S2LP2AUX_names_call_args) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC S2LP2AUX_ca_remove_map THEN MATCH_MP_TAC S2LP2AUX_ca_alloc_map THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC S2LP2AUX_lp_names THEN MATCH_MP_TAC S2LP2AUX_lp_remove_map THEN
      MATCH_MP_TAC S2LP2AUX_lp_alloc_map THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[stack_names_compile_def; S2LP2AUX_MAP_FST_names_prog_comp;
                    S2LP2AUX_MAP_FST_remove_prog_comp; S2LP2AUX_MAP_FST_alloc_prog_comp]]);;

let s2lp2aux_has (c:string) (th:thm) =
  can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false)) (concl th);;
let S2LP2AUX_fmis_state_rel = prove
 (`!f jump (offset:A word#A word) sp (code2:(num#(A)stack_prog)list) (t:(A,C,FFI)lab_state)
    save_regs coracle regs coracle3.
     coracle3 =
       (I ## stack_names_compile f ## I) o
       ((I ## MAP (stack_remove_prog_comp jump offset sp) ## I) o
        ((I ## MAP stack_alloc_prog_comp ## I) o coracle)) /\
     good_dimindex (:A) /\
     lab_state_code t = MAP prog_to_section (stack_names_compile f code2) /\
     labels_ok (lab_state_code t) /\
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND code2) /\
     lab_state_compile_oracle t =
       (\n. let (c,p,b) = coracle n in (c,compile_no_stubs f jump offset sp p)) /\
     ~lab_state_failed t /\
     ~(lab_state_link_reg t IN save_regs) /\
     (!k i n. k IN save_regs ==> lab_state_io_regs t n i k = NONE) /\
     (!k n. k IN save_regs ==> lab_state_cc_regs t n k = NONE) /\
     (!x. x IN lab_state_mem_domain t ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     (!x. x IN lab_state_shared_mem_domain t ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     (!n. stack_to_labProof_good_code sp (FST (SND (coracle n)))) /\
     tlookup f 4 = lab_state_len2_reg t /\
     tlookup f 3 = lab_state_ptr2_reg t /\
     tlookup f 2 = lab_state_len_reg t /\
     tlookup f 1 = lab_state_ptr_reg t /\
     tlookup f 0 = lab_state_link_reg t /\
     BIJ (tlookup f) UNIV UNIV
     ==> stack_to_labProof_state_rel
           (stack_to_labProof_make_init (fromAList (stack_names_compile f code2))
              coracle3 regs save_regs t) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[state_rel_make_init] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(lab_state_link_reg (t:(A,C,FFI)lab_state) = lab_state_len_reg t) /\
                ~(lab_state_link_reg t = lab_state_ptr_reg t) /\
                ~(lab_state_link_reg t = lab_state_len2_reg t) /\
                ~(lab_state_link_reg t = lab_state_ptr2_reg t)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun tm -> UNDISCH_TAC tm THEN DISCH_THEN(SUBST1_TAC o SYM))
      [`tlookup f 0 = lab_state_link_reg (t:(A,C,FFI)lab_state)`;
       `tlookup f 2 = lab_state_len_reg (t:(A,C,FFI)lab_state)`;
       `tlookup f 1 = lab_state_ptr_reg (t:(A,C,FFI)lab_state)`;
       `tlookup f 4 = lab_state_len2_reg (t:(A,C,FFI)lab_state)`;
       `tlookup f 3 = lab_state_ptr2_reg (t:(A,C,FFI)lab_state)`] THEN
    UNDISCH_TAC `BIJ (tlookup f) (:num) (:num)` THEN
    REWRITE_TAC[BIJ_DEF; INJ_DEF; IN_UNIV] THEN
    MESON_TAC[ARITH_RULE `~(0 = 2) /\ ~(0 = 1) /\ ~(0 = 4) /\ ~(0 = 3)`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[lookup_fromAList] THEN MAP_EVERY X_GEN_TAC [`n:num`; `prog:(A)stack_prog`] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:num spt`; `code2:(num#(A)stack_prog)list`] S2LP2AUX_names_call_args) THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `(n,prog):num#(A)stack_prog` THEN ASM_SIMP_TAC[ALOOKUP_MEM; SND];
      MATCH_MP_TAC code_installed_prog_to_section THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `labels_ok (lab_state_code (t:(A,C,FFI)lab_state))` THEN ASM_REWRITE_TAC[]];
    MATCH_ACCEPT_TAC S2LP2AUX_oracle3;
    X_GEN_TAC `k:num` THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (s2lp2aux_has "stack_to_labProof_good_code")) THEN
    SPEC_TAC(`(coracle:num->C#(num#(A)stack_prog)list#(A word)list) k`,
             `x:C#(num#(A)stack_prog)list#(A word)list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; FST; SND] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC S2LP2AUX_oracle3_ok THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[domain_fromAList; MAP_prog_to_section_Section_num];
    UNDISCH_TAC `labels_ok (lab_state_code (t:(A,C,FFI)lab_state))` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o MATCH_MP labels_ok_imp)]);;

let S2LP2AUX_names_sem = prove
 (`!(s:(A,C,FFI)stack_state) f (code:(num#(A)stack_prog)list) start oracle.
     ~stack_state_use_alloc s /\ ~stack_state_use_store s /\ ~stack_state_use_stack s /\
     BIJ (tlookup f) (:num) (:num) /\ ALL_DISTINCT (MAP FST code) /\
     stack_state_code s = fromAList (stack_names_compile f code) /\
     stack_state_compile_oracle s = (I ## stack_names_compile f ## I) o oracle
     ==> stack_semantics start s =
         stack_semantics start (stack_namesProof_make_init f (fromAList code) oracle s)`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC stack_namesProof_make_init_semantics);;

let S2LP2AUX_fmis_names = prove
 (`!f jump (offset:A word#A word) sp ggc max_heap code1 (code2:(num#(A)stack_prog)list)
    (t:(A,C,FFI)lab_state) save_regs coracle2 coracle3 regs.
     code2 = stack_remove_compile jump offset ggc max_heap sp InitGlobals_location code1 /\
     coracle3 = (I ## stack_names_compile f ## I) o coracle2 /\
     ALL_DISTINCT (MAP FST code2) /\
     lab_state_pc t = 0 /\
     BIJ (tlookup f) UNIV UNIV /\
     stack_to_labProof_state_rel
       (stack_to_labProof_make_init (fromAList (stack_names_compile f code2)) coracle3 regs
          save_regs t) t /\
     lab_state_code t = MAP prog_to_section (stack_names_compile f code2)
     ==> ~(stack_semantics 0
            (stack_namesProof_make_init f (fromAList code2) coracle2
               (stack_to_labProof_make_init (fromAList (stack_names_compile f code2)) coracle3
                  regs save_regs t)) = Fail)
     ==> lab_semantics t =
         stack_semantics 0
           (stack_namesProof_make_init f (fromAList code2) coracle2
              (stack_to_labProof_make_init (fromAList (stack_names_compile f code2)) coracle3
                 regs save_regs t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`stack_to_labProof_make_init (fromAList (stack_names_compile f code2))
                    coracle3 regs save_regs (t:(A,C,FFI)lab_state)`;
                 `f:num spt`; `code2:(num#(A)stack_prog)list`; `0`;
                 `coracle2:num->C#(num#(A)stack_prog)list#(A word)list`] S2LP2AUX_names_sem) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[stack_to_labProof_make_init_def] THEN SIMP[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC make_init_semantics THEN ASM_REWRITE_TAC[halt_assum_lemma] THEN
  REWRITE_TAC[stack_names_compile_def; stack_remove_compile_def; stack_remove_init_stubs_def;
              MAP; APPEND; stack_names_prog_comp_def; prog_to_section_def; LET_DEF;
              LET_END_DEF; S2LP2AUX_pCASE3] THEN
  ONCE_REWRITE_TAC[loc_to_pc_def] THEN REWRITE_TAC[]);;

let S2LP2AUX_ALL_FST_SND_PAIR = prove
 (`!(P:B->bool) (Q:A->bool) l.
     ALL P (MAP SND l) /\ ALL Q (MAP FST l) ==> ALL (\(n,p). P p /\ Q n) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]);;

let S2LP2AUX_fmis_discharge = prove
 (`!f jump (offset:A word#A word) sp ggc max_heap data_conf (code:(num#(A)stack_prog)list)
    code1 code2 coracle coracle1 coracle2 coracle3 regs save_regs (t:(A,C,FFI)lab_state).
     code1 = stack_alloc_compile data_conf (stack_rawcall_compile code) /\
     code2 = stack_remove_compile jump offset ggc max_heap sp InitGlobals_location code1 /\
     coracle1 = (I ## MAP stack_alloc_prog_comp ## I) o coracle /\
     coracle2 = (I ## MAP (stack_remove_prog_comp jump offset sp) ## I) o coracle1 /\
     stack_to_labProof_good_code sp code /\
     (!n. stack_to_labProof_good_code sp (FST (SND (coracle n)))) /\
     10 <= sp /\ max_stack_alloc <= max_heap /\
     ALL (\r. tlookup f ((r + sp) - 2) IN save_regs) [2; 3; 4] /\
     BIJ (tlookup f) UNIV UNIV
     ==> discharge_these jump offset ggc max_heap sp InitGlobals_location coracle1 code1
           (stack_namesProof_make_init f (fromAList code2) coracle2
              (stack_to_labProof_make_init (fromAList (stack_names_compile f code2)) coracle3
                 regs save_regs t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[discharge_these_def; stack_namesProof_make_init_def;
              stack_to_labProof_make_init_def] THEN SIMP[] THEN
  UNDISCH_TAC `stack_to_labProof_good_code sp (code:(num#(A)stack_prog)list)` THEN
  REWRITE_TAC[stack_to_labProof_good_code_def] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC S2LP2AUX_ALL_FST_SND_PAIR THEN CONJ_TAC THENL
     [MATCH_MP_TAC stack_alloc_reg_bound THEN ASM_REWRITE_TAC[stack_rawcall_reg_bound];
      REWRITE_TAC[stack_alloc_compile_def; stack_alloc_stubs_def; MAP_APPEND; MAP;
                  S2LP2AUX_MAP_FST_alloc_prog_comp; stack_rawcallProof_MAP_FST_compile;
                  ALL_APPEND; ALL] THEN
      REWRITE_TAC[ALL_MAP; gc_stub_location_eq; stack_num_stubs_def] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "alloc_arg")) THEN
      REWRITE_TAC[stack_num_stubs_def] THEN MATCH_MP_TAC MONO_ALL THEN
      REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`n:num`; `i:num`; `p:(A)stack_prog`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (s2lp2aux_has "stack_to_labProof_good_code")) THEN
    REWRITE_TAC[stack_to_labProof_good_code_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ALL (\(n,p). reg_bound p sp /\ stack_num_stubs <= n + 1)
                    (MAP stack_alloc_prog_comp
                       (FST (SND ((coracle:num->C#(num#(A)stack_prog)list#(A word)list) n))))`
      MP_TAC THENL
     [MATCH_MP_TAC S2LP2AUX_ALL_FST_SND_PAIR THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`sp:num`;
                       `FST (SND ((coracle:num->C#(num#(A)stack_prog)list#(A word)list) n))`;
                       `ARB:data_to_word_config`] stack_alloc_reg_bound) THEN
        ASM_REWRITE_TAC[stack_alloc_compile_def; MAP_APPEND; ALL_APPEND] THEN SIMP[];
        REWRITE_TAC[S2LP2AUX_MAP_FST_alloc_prog_comp] THEN REWRITE_TAC[ALL_MAP] THEN
        FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "alloc_arg")) THEN
        MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_num_stubs_def] THEN
        ARITH_TAC];
      REWRITE_TAC[GSYM ALL_MEM] THEN
      DISCH_THEN(MP_TAC o SPEC `(i,p):num#(A)stack_prog`) THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]];
    UNDISCH_TAC `10 <= sp` THEN ARITH_TAC;
    REWRITE_TAC[domain_fromAList; stack_remove_compile_def; stack_remove_init_stubs_def; MAP;
                APPEND; set_of_list; IN_INSERT] THEN ARITH_TAC;
    EXISTS_TAC `tlookup f sp` THEN ALL_TAC;
    EXISTS_TAC `tlookup f (sp + 1)` THEN ALL_TAC;
    EXISTS_TAC `tlookup f (sp + 2)` THEN ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; ARITH_RULE `(2 + sp) - 2 = sp /\ (3 + sp) - 2 = sp + 1 /\
                                                (4 + sp) - 2 = sp + 2`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(MATCH_MP LINV_DEF (CONJUNCT1 (REWRITE_RULE[BIJ_DEF]
    (ASSUME `BIJ (tlookup f) (:num) (:num)`)))) THEN REWRITE_TAC[IN_UNIV]);;

let S2LP2AUX_fmis_propagate = prove
 (`!f code2 coracle2 coracle3 code3 save_regs (t:(A,C,FFI)lab_state) (bitmaps:(A word)list)
    data_sp.
     good_dimindex (:A) /\
     memory_assumption f bitmaps data_sp t /\
     BIJ (tlookup f) UNIV UNIV
     ==> propagate_these
           (stack_namesProof_make_init f code2 coracle2
              (stack_to_labProof_make_init code3 coracle3 (MAP (tlookup f) [2; 3; 4]) save_regs t))
           bitmaps data_sp`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[propagate_these_def; stack_namesProof_make_init_def;
              stack_to_labProof_make_init_def; memory_assumption_def] THEN
  SIMP[] THEN STRIP_TAC THEN ASM_SIMP_TAC[BIJ_FLOOKUP_MAP_KEYS] THEN
  REWRITE_TAC[flookup_fupdate_list; MAP; REVERSE; APPEND; ALOOKUP_THM; FLOOKUP_EMPTY] THEN
  SUBGOAL_THEN `~(tlookup f 4 = tlookup f 2) /\ ~(tlookup f 3 = tlookup f 2) /\
                ~(tlookup f 4 = tlookup f 3)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `BIJ (tlookup f) (:num) (:num)` THEN
    REWRITE_TAC[BIJ_DEF; INJ_DEF; IN_UNIV] THEN
    MESON_TAC[ARITH_RULE `~(4 = 2) /\ ~(3 = 2) /\ ~(4 = 3)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
  MAP_EVERY EXISTS_TAC [`ptr2:A word`; `ptr3:A word`; `ptr4:A word`; `bitmap_ptr:A word`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> can (find_term ((=) `word_mul (word 2) bytes_in_word:A word`)) (concl th))) THEN
  REWRITE_TAC[WORD_ADD_AC]);;

let S2LP2AUX_make_init_any_space = prove
 (`!gen_gc' max_heap (bitmaps:(A word)list) data_sp coracle jump off k code
    (s:(A,C,FFI)stack_state).
     good_dimindex (:A)
     ==> LENGTH (stack_state_bitmaps
           (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k code s)) +
         LENGTH (buffer_buffer (stack_state_data_buffer
           (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k code s))) +
         buffer_space_left (stack_state_data_buffer
           (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k code s))
         < dimword (:A) - 1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[make_init_any_def] THEN
  CASES_ON `make_init_opt gen_gc' max_heap bitmaps data_sp coracle jump off k code
              (s:(A,C,FFI)stack_state)` THEN
  CASE_REWRITE_TAC[] THENL
   [SIMP[LENGTH] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    FIRST_ASSUM(MP_TAC o MATCH_MP S2LP2AUX_make_init_opt_SOME) THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `init_prop gen_gc' max_heap data_sp
                   (get_stack_heap_limit max_heap (read_pointers (s:(A,C,FFI)stack_state)))
                   (a:(A,C,FFI)stack_state)` THEN
    ASM_REWRITE_TAC[init_prop_def] THEN STRIP_TAC THEN
    UNDISCH_TAC `LENGTH (stack_state_bitmaps
                   (init_reduce gen_gc' jump off k code bitmaps data_sp coracle
                      (t0:(A,C,FFI)stack_state))) + data_sp + 1 < dimword (:A)` THEN
    REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF] THEN SIMP[LENGTH] THEN ARITH_TAC]);;

let S2LP2AUX_fmis_alloc = prove
 (`!ggc max_heap (bitmaps:(A word)list) data_sp coracle coracle1 jump offset sp data_conf
    (code:(num#(A)stack_prog)list) code1 (s2:(A,C,FFI)stack_state) start.
     code1 = stack_alloc_compile data_conf (stack_rawcall_compile code) /\
     coracle1 = (I ## MAP stack_alloc_prog_comp ## I) o coracle /\
     stack_to_labProof_good_code sp code /\
     (!n. stack_to_labProof_good_code sp (FST (SND (coracle n)))) /\
     good_dimindex (:A) /\
     ~(stack_semantics start
         (stack_allocProof_make_init data_conf (fromAList (stack_rawcall_compile code)) coracle
            (make_init_any ggc max_heap bitmaps data_sp coracle1 jump offset sp
               (fromAList code1) s2)) = Fail)
     ==> stack_semantics start
           (make_init_any ggc max_heap bitmaps data_sp coracle1 jump offset sp
              (fromAList code1) s2) =
         stack_semantics start
           (stack_allocProof_make_init data_conf (fromAList (stack_rawcall_compile code)) coracle
              (make_init_any ggc max_heap bitmaps data_sp coracle1 jump offset sp
                 (fromAList code1) s2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC stack_allocProof_make_init_semantics THEN
  ASM_REWRITE_TAC[make_init_any_use_stack; make_init_any_use_store; make_init_any_use_alloc;
                  make_init_any_code; make_init_any_compile_oracle; make_init_any_stack_limit] THEN
  ASM_SIMP_TAC[S2LP2AUX_make_init_any_space] THEN
  UNDISCH_TAC `stack_to_labProof_good_code sp (code:(num#(A)stack_prog)list)` THEN
  REWRITE_TAC[stack_to_labProof_good_code_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[stack_rawcallProof_MAP_FST_compile] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `prog:(A)stack_prog`] THEN
    REWRITE_TAC[stack_rawcall_compile_def; LET_DEF; LET_END_DEF; ALOOKUP_MAP; o_THM] THEN
    CASES_ON `ALOOKUP (code:(num#(A)stack_prog)list) k` THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[call_arg_comp] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "alloc_arg")) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[gc_stub_location_eq; stack_num_stubs_def] THEN
    MESON_TAC[ARITH_RULE `!k. 5 <= k ==> ~(k = 4)`];
    MAP_EVERY X_GEN_TAC [`n:num`; `k:num`; `p:(A)stack_prog`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (s2lp2aux_has "stack_to_labProof_good_code")) THEN
    REWRITE_TAC[stack_to_labProof_good_code_def] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "alloc_arg")) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[gc_stub_location_eq; stack_num_stubs_def] THEN
    MESON_TAC[ARITH_RULE `!k. 5 <= k ==> ~(k = 4)`]]);;

let S2LP2AUX_full_make_init_eq = prove
 (`!stack_conf data_conf max_heap sp offset (bitmaps:(A word)list) code (t:(A,C,FFI)lab_state)
    save_regs data_sp coracle s opt.
     full_make_init stack_conf data_conf max_heap sp offset bitmaps code t save_regs data_sp
       coracle = (s,opt) <=>
     ?f jump ggc code1 code2 coracle1 coracle2 coracle3 s3 s2 s1.
       f = stack_to_lab_config_reg_names stack_conf /\
       jump = stack_to_lab_config_jump stack_conf /\
       ggc = is_gen_gc (data_to_word_config_gc_kind data_conf) /\
       code1 = stack_alloc_compile data_conf (stack_rawcall_compile code) /\
       code2 = stack_remove_compile jump offset ggc max_heap sp InitGlobals_location code1 /\
       coracle1 = (I ## MAP stack_alloc_prog_comp ## I) o coracle /\
       coracle2 = (I ## MAP (stack_remove_prog_comp jump offset sp) ## I) o coracle1 /\
       coracle3 = (I ## stack_names_compile f ## I) o coracle2 /\
       s3 = stack_to_labProof_make_init (fromAList (stack_names_compile f code2)) coracle3
              (MAP (tlookup f) [2; 3; 4]) save_regs t /\
       s2 = stack_namesProof_make_init f (fromAList code2) coracle2 s3 /\
       s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump offset sp
              (fromAList code1) s2 /\
       s = stack_allocProof_make_init data_conf (fromAList code) coracle s1 /\
       opt = make_init_opt ggc max_heap bitmaps data_sp coracle1 jump offset sp
               (fromAList code1) s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_make_init_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN MESON_TAC[]);;

let S2LP2AUX_rawcall_sem = prove
 (`!(s:(A,C,FFI)stack_state) (code:(num#(A)stack_prog)list) start.
     ALL_DISTINCT (MAP FST code) /\ stack_state_use_stack s /\
     stack_state_code s = fromAList code /\ ~(stack_semantics start s = Fail)
     ==> stack_semantics start
           (stack_state_code_fupd (K (fromAList (stack_rawcall_compile code))) s) =
         stack_semantics start s`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC stack_rawcallProof_compile_semantics);;
let s2lp2aux_fold (v:term) : tactic =
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs(concl th) = v then REWRITE_TAC[SYM th]
                        else NO_TAC);;

(* HOL4 line 3365 (the conclusion Abbrev (...) is the formula itself; the   *)
(* first semantics is stackSem's, the second labSem's; HOL4 r + sp - 2 is   *)
(* (r + sp) - 2) *)
let full_make_init_semantics = prove
 (`!stack_conf data_conf max_heap sp offset (bitmaps:(A word)list) code (t:(A,C,FFI)lab_state)
     save_regs data_sp coracle s opt.
     full_make_init stack_conf data_conf max_heap sp offset bitmaps code t save_regs data_sp
       coracle = (s,opt) /\
     good_dimindex (:A) /\
     lab_state_code t = stack_to_lab_compile stack_conf data_conf max_heap sp offset code /\
     lab_state_compile_oracle t =
       (\n. let (c,p,b) = coracle n in
              (c,compile_no_stubs (stack_to_lab_config_reg_names stack_conf)
                   (stack_to_lab_config_jump stack_conf) offset sp p)) /\
     ~lab_state_failed t /\
     memory_assumption (stack_to_lab_config_reg_names stack_conf) bitmaps data_sp t /\
     max_stack_alloc <= max_heap /\
     ~(lab_state_link_reg t IN save_regs) /\ lab_state_pc t = 0 /\
     (!k i n. k IN save_regs ==> lab_state_io_regs t n i k = NONE) /\
     (!k n. k IN save_regs ==> lab_state_cc_regs t n k = NONE) /\
     (!x. x IN lab_state_mem_domain t ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     (!x. x IN lab_state_shared_mem_domain t ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     stack_to_labProof_good_code sp code /\
     (!n. stack_to_labProof_good_code sp (FST (SND (coracle n)))) /\
     10 <= sp /\
     ALL (\r. tlookup (stack_to_lab_config_reg_names stack_conf) ((r + sp) - 2) IN save_regs)
       [2; 3; 4] /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 4 = lab_state_len2_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 3 = lab_state_ptr2_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 2 = lab_state_len_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 1 = lab_state_ptr_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 0 = lab_state_link_reg t /\
     BIJ (tlookup (stack_to_lab_config_reg_names stack_conf)) UNIV UNIV
     ==> ~(opt = NONE) /\
         (~(stack_semantics InitGlobals_location s = Fail)
          ==> lab_semantics t = stack_semantics InitGlobals_location s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP2AUX_full_make_init_eq] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:num spt` (X_CHOOSE_THEN `jump:bool` (X_CHOOSE_THEN `ggc:bool`
      (X_CHOOSE_THEN `code1:(num#(A)stack_prog)list`
      (X_CHOOSE_THEN `code2:(num#(A)stack_prog)list`
      (X_CHOOSE_THEN `coracle1:num->C#(num#(A)stack_prog)list#(A word)list`
      (X_CHOOSE_THEN `coracle2:num->C#(num#(A)stack_prog)list#(A word)list`
      (X_CHOOSE_THEN `coracle3:num->C#(num#(A)stack_prog)list#(A word)list`
      (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state`
      (X_CHOOSE_THEN `s2:(A,C,FFI)stack_state`
      (X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC)))))))))))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `labels_ok (lab_state_code (t:(A,C,FFI)lab_state))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC stack_to_lab_compile_lab_pres THEN
    UNDISCH_TAC `stack_to_labProof_good_code sp (code:(num#(A)stack_prog)list)` THEN
    REWRITE_TAC[stack_to_labProof_good_code_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ALL_MAP] THEN
    FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "alloc_arg")) THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_num_stubs_def;
                                            gc_stub_location_eq] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lab_state_code (t:(A,C,FFI)lab_state) =
                MAP prog_to_section (stack_names_compile f code2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (code2:(num#(A)stack_prog)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `stack_to_labProof_good_code sp (code:(num#(A)stack_prog)list)` THEN
    REWRITE_TAC[stack_to_labProof_good_code_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MAP_FST_compile_compile; ALL_DISTINCT; MEM; gc_stub_location_eq] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `ALL (\n. 5 <= n) (MAP FST (code:(num#(A)stack_prog)list))` MP_TAC THENL
     [REWRITE_TAC[ALL_MAP] THEN
      FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "alloc_arg")) THEN
      MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_num_stubs_def] THEN
      MESON_TAC[];
      REWRITE_TAC[GSYM ALL_MEM] THEN
      MESON_TAC[ARITH_RULE `~(5 <= 0) /\ ~(5 <= 1) /\ ~(5 <= 2) /\ ~(5 <= 4)`]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num spt`; `jump:bool`; `offset:A word#A word`; `sp:num`;
                 `code2:(num#(A)stack_prog)list`; `t:(A,C,FFI)lab_state`; `save_regs:num->bool`;
                 `coracle:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `MAP (tlookup f) [2; 3; 4]`;
                 `coracle3:num->C#(num#(A)stack_prog)list#(A word)list`]
                S2LP2AUX_fmis_state_rel) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF];
      MATCH_MP_TAC S2LP2AUX_ca_code2 THEN
      UNDISCH_TAC `stack_to_labProof_good_code sp (code:(num#(A)stack_prog)list)` THEN
      SIMP[stack_to_labProof_good_code_def]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`f:num spt`; `jump:bool`; `offset:A word#A word`; `sp:num`; `ggc:bool`;
                 `max_heap:num`; `code1:(num#(A)stack_prog)list`;
                 `code2:(num#(A)stack_prog)list`; `t:(A,C,FFI)lab_state`; `save_regs:num->bool`;
                 `coracle2:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `coracle3:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `MAP (tlookup f) [2; 3; 4]`] S2LP2AUX_fmis_names) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF];
    MAP_EVERY s2lp2aux_fold [`s3:(A,C,FFI)stack_state`; `s2:(A,C,FFI)stack_state`] THEN
    DISCH_THEN(LABEL_TAC "names")] THEN
  MP_TAC(ISPECL [`f:num spt`; `jump:bool`; `offset:A word#A word`; `sp:num`; `ggc:bool`;
                 `max_heap:num`; `data_conf:data_to_word_config`;
                 `code:(num#(A)stack_prog)list`; `code1:(num#(A)stack_prog)list`;
                 `code2:(num#(A)stack_prog)list`;
                 `coracle:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `coracle1:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `coracle2:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `coracle3:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `MAP (tlookup f) [2; 3; 4]`; `save_regs:num->bool`;
                 `t:(A,C,FFI)lab_state`] S2LP2AUX_fmis_discharge) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    MAP_EVERY s2lp2aux_fold [`s3:(A,C,FFI)stack_state`; `s2:(A,C,FFI)stack_state`] THEN
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`f:num spt`; `fromAList (code2:(num#(A)stack_prog)list)`;
                 `coracle2:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `coracle3:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `fromAList (stack_names_compile f (code2:(num#(A)stack_prog)list))`;
                 `save_regs:num->bool`; `t:(A,C,FFI)lab_state`; `bitmaps:(A word)list`;
                 `data_sp:num`] S2LP2AUX_fmis_propagate) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    MAP_EVERY s2lp2aux_fold [`s3:(A,C,FFI)stack_state`; `s2:(A,C,FFI)stack_state`] THEN
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`jump:bool`; `offset:A word#A word`; `ggc:bool`; `max_heap:num`; `sp:num`;
                 `InitGlobals_location`;
                 `coracle1:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `code1:(num#(A)stack_prog)list`; `s2:(A,C,FFI)stack_state`;
                 `bitmaps:(A word)list`; `data_sp:num`] stack_removeProof_make_init_semantics) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1':(A,C,FFI)stack_state`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "remove"))) THEN
  SUBGOAL_THEN `s1':(A,C,FFI)stack_state = s1` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[make_init_any_def] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "nf") THEN
  SUBGOAL_THEN
   `stack_semantics InitGlobals_location
      (stack_allocProof_make_init data_conf
         (fromAList (stack_rawcall_compile (code:(num#(A)stack_prog)list)))
         (coracle:num->C#(num#(A)stack_prog)list#(A word)list) (s1:(A,C,FFI)stack_state)) =
    stack_semantics InitGlobals_location (s:(A,C,FFI)stack_state)` (LABEL_TAC "rc") THENL
   [MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `code:(num#(A)stack_prog)list`;
                   `InitGlobals_location`] S2LP2AUX_rawcall_sem) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[stack_allocProof_make_init_def] THEN SIMP[] THEN
      UNDISCH_TAC `stack_to_labProof_good_code sp (code:(num#(A)stack_prog)list)` THEN
      SIMP[stack_to_labProof_good_code_def];
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[stack_allocProof_make_init_def] THEN SIMP[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ggc:bool`; `max_heap:num`; `bitmaps:(A word)list`; `data_sp:num`;
                 `coracle:num->C#(num#(A)stack_prog)list#(A word)list`;
                 `coracle1:num->C#(num#(A)stack_prog)list#(A word)list`; `jump:bool`;
                 `offset:A word#A word`; `sp:num`; `data_conf:data_to_word_config`;
                 `code:(num#(A)stack_prog)list`; `code1:(num#(A)stack_prog)list`;
                 `s2:(A,C,FFI)stack_state`; `InitGlobals_location`] S2LP2AUX_fmis_alloc) THEN
  ANTS_TAC THENL
   [s2lp2aux_fold `s1:(A,C,FFI)stack_state` THEN USE_THEN "rc" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    s2lp2aux_fold `s1:(A,C,FFI)stack_state` THEN USE_THEN "rc" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(LABEL_TAC "al")] THEN
  USE_THEN "al" (fun al -> USE_THEN "nf" (fun nf ->
    USE_THEN "remove" (fun rm -> USE_THEN "names" (fun nm ->
      let nf1 = REWRITE_RULE[GSYM al] nf in
      let eq2 = MP rm nf1 in
      let nf2 = REWRITE_RULE[GSYM eq2] nf1 in
      let eq3 = MP nm nf2 in
      REWRITE_TAC[eq3; eq2; al])))));;

(* HOL4 line 3617 [allow_rebind]: Theorem full_make_init_semantics =        *)
(* full_make_init_semantics |> REWRITE_RULE [markerTheory.Abbrev_def] (the  *)
(* same statement here, Abbrev being written out) *)
let full_make_init_semantics = prove
 (`!stack_conf data_conf max_heap sp offset (bitmaps:(A word)list) code (t:(A,C,FFI)lab_state)
     save_regs data_sp coracle s opt.
     full_make_init stack_conf data_conf max_heap sp offset bitmaps code t save_regs data_sp
       coracle = (s,opt) /\
     good_dimindex (:A) /\
     lab_state_code t = stack_to_lab_compile stack_conf data_conf max_heap sp offset code /\
     lab_state_compile_oracle t =
       (\n. let (c,p,b) = coracle n in
              (c,compile_no_stubs (stack_to_lab_config_reg_names stack_conf)
                   (stack_to_lab_config_jump stack_conf) offset sp p)) /\
     ~lab_state_failed t /\
     memory_assumption (stack_to_lab_config_reg_names stack_conf) bitmaps data_sp t /\
     max_stack_alloc <= max_heap /\
     ~(lab_state_link_reg t IN save_regs) /\ lab_state_pc t = 0 /\
     (!k i n. k IN save_regs ==> lab_state_io_regs t n i k = NONE) /\
     (!k n. k IN save_regs ==> lab_state_cc_regs t n k = NONE) /\
     (!x. x IN lab_state_mem_domain t ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     (!x. x IN lab_state_shared_mem_domain t ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     stack_to_labProof_good_code sp code /\
     (!n. stack_to_labProof_good_code sp (FST (SND (coracle n)))) /\
     10 <= sp /\
     ALL (\r. tlookup (stack_to_lab_config_reg_names stack_conf) ((r + sp) - 2) IN save_regs)
       [2; 3; 4] /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 4 = lab_state_len2_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 3 = lab_state_ptr2_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 2 = lab_state_len_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 1 = lab_state_ptr_reg t /\
     tlookup (stack_to_lab_config_reg_names stack_conf) 0 = lab_state_link_reg t /\
     BIJ (tlookup (stack_to_lab_config_reg_names stack_conf)) UNIV UNIV
     ==> ~(opt = NONE) /\
         (~(stack_semantics InitGlobals_location s = Fail)
          ==> lab_semantics t = stack_semantics InitGlobals_location s)`,
  ACCEPT_TAC full_make_init_semantics);;


(* HOL4 line 3620 [simp] *)
let EVERY_sec_ends_with_label_MAP_prog_to_section = prove
 (`!(prog:(num#(A)stack_prog)list). ALL sec_ends_with_label (MAP prog_to_section prog)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; prog_to_section_def; LET_DEF; LET_END_DEF; S2LP2AUX_pCASE3] THEN
  REWRITE_TAC[sec_ends_with_label_def; append_thm; LAST_APPEND; NULL_APPEND] THEN
  SIMP[LAST; NULL]);;

let _ = cake_add_simps [EVERY_sec_ends_with_label_MAP_prog_to_section];;

(* HOL4 line 3627: val stack_asm_ok_def = stackPropsTheory.stack_asm_ok_def *)
(* (an abbreviation) *)

(* every line of a flattened program has a property Q, when the property  *)
(* Pr of the program gives Q for the lines of its atomic commands (for       *)
(* flatten_line_ok_pre, flatten_no_share_mem_inst and flatten_no_install)  *)

let s2lp2aux_split_opt : tactic = fun (asl,w as g) ->
  let tms = find_terms (fun t -> is_case_app t &&
                          (let c,x,_ = dest_case_app t in
                           fst(dest_const c) = "option_CASE" && is_var x)) w in
  match tms with
    [] -> failwith "s2lp2aux_split_opt"
  | t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN CASE_REWRITE_TAC[]) g;;

let S2LP2AUX_COND_ALL_FST = prove
 (`!(Q:A->bool) b (x:(A)app_list#B) y.
     ALL Q (append (FST (if b then x else y))) =
     (if b then ALL Q (append (FST x)) else ALL Q (append (FST y)))`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* rewrite the assumptions with each equation flatten ... = (xs,nr,m) made by *)
(* PAIRARG_TAC, then use the hypotheses labelled hs on the assumptions and   *)
(* discharge the implications whose antecedent is an assumption              *)
let s2lp2aux_flat_finish (hs:string list) : tactic =
  let is_fl th = is_eq (concl th) &&
                 (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_to_lab_flatten"
                  with Failure _ -> false) in
  (fun (asl,w as g) ->
     let eqs = filter is_fl (map snd asl) in
     RULE_ASSUM_TAC(CAKE_SIMP_RULE(FST::PAIR_EQ::eqs)) g) THEN
  MAP_EVERY (fun l -> TRY(USE_THEN l (fun h -> FIRST_ASSUM(fun pr ->
                       STRIP_ASSUME_TAC (MATCH_MP h pr))))) (hs @ hs) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp (concl th)
                                 then FIRST_ASSUM(fun pr -> ASSUME_TAC (MP th pr))
                                 else NO_TAC)) THEN
  ASM_REWRITE_TAC[COND_ID];;

let S2LP2AUX_flatten_ALL = prove
 (`!(Q:(A)line->bool) (Pr:(A)stack_prog->bool).
     (!l1 l2 k. Q (lab_Label l1 l2 k)) /\
     (!l. Q (LabAsm (lab_Jump l) (word 0) [] 0)) /\
     (!c r ri l. Q (LabAsm (lab_JumpCmp c r ri l) (word 0) [] 0)) /\
     (!r l. Q (LabAsm (lab_LocValue r l) (word 0) [] 0)) /\
     Q (LabAsm lab_Halt (word 0) [] 0) /\
     (!i. Q (LabAsm (CallFFI i) (word 0) [] 0)) /\
     Q (Asm (Asmi (asm_Inst asm_Skip)) [] 0) /\
     (!a. Pr (stack_Inst a) ==> Q (Asm (Asmi (asm_Inst a)) [] 0)) /\
     (!r. Pr (stack_Raise r) ==> Q (Asm (Asmi (JumpReg r)) [] 0)) /\
     (!r. Pr (stack_Return r) ==> Q (Asm (Asmi (JumpReg r)) [] 0)) /\
     (!ret dest h. Pr (stack_Call ret dest h) ==> Q (compile_jump dest)) /\
     (!p1 lr l1 l2 dest h. Pr (stack_Call (SOME (p1,lr,l1,l2)) dest h) ==> Pr p1) /\
     (!p1 lr l1 l2 dest p2 k1 k2.
        Pr (stack_Call (SOME (p1,lr,l1,l2)) dest (SOME (p2,k1,k2))) ==> Pr p2) /\
     (!a b c d r. Pr (stack_Install a b c d r) ==> Q (LabAsm lab_Install (word 0) [] 0)) /\
     (!op r ad. Pr (ShMemOp op r ad) ==> Q (Asm (ShareMem op r ad) [] 0)) /\
     (!r1 r2. Pr (stack_CodeBufferWrite r1 r2) ==> Q (Asm (Cbw r1 r2) [] 0)) /\
     (!p1 p2. Pr (stack_Seq p1 p2) ==> Pr p1 /\ Pr p2) /\
     (!c r ri p1 p2. Pr (stack_If c r ri p1 p2) ==> Pr p1 /\ Pr p2) /\
     (!p1. Pr (stack_Loop p1) ==> Pr p1)
     ==> !t p n m cs bs. Pr p ==> ALL Q (append (FST (stack_to_lab_flatten t p n m cs bs)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (l,c) -> LABEL_TAC l c)
    (zip ["hl";"hj";"hjc";"hlv";"hh";"hffi";"hsk";"hinst";"hrai";"hret";"hcq";"hc1";"hc2";
          "hins";"hsh";"hcbw";"hseq";"hif";"hloop"] (CONJUNCTS th))) THEN
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (STRIP_ASSUME_TAC o CAKE_SIMP_RULE[]) THEN
  REPEAT s2lp2aux_split_opt THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[PAIR_EQ]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; FST; append_thm; ALL; ALL_APPEND] THEN
  REWRITE_TAC[S2LP2AUX_COND_ALL_FST] THEN
  REWRITE_TAC[FST; append_thm; ALL; ALL_APPEND] THEN
  s2lp2aux_flat_finish ["hinst";"hrai";"hret";"hcq";"hc1";"hc2";"hins";"hsh";"hcbw";
                        "hseq";"hif";"hloop"]);;

let S2LP2AUX_flatten_line_ok_pre = prove
 (`!c. asm_offset_ok 0 (asm_config_byte_offset c) (word 0)
       ==> !t (p:(A)stack_prog) n m cs bs.
             stack_asm_ok c p
             ==> ALL (line_ok_pre c) (append (FST (stack_to_lab_flatten t p n m cs bs)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL
    [`line_ok_pre (c:(A)asm_config)`; `stack_asm_ok (c:(A)asm_config)`]
    S2LP2AUX_flatten_ALL)) THEN
  REWRITE_TAC[line_ok_pre_def; stack_asm_ok_def; cbw_to_asm_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[asm_ok_def; inst_ok_def; reg_ok_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [CASES_ON `dest:num+num` THEN
    CASE_REWRITE_TAC[compile_jump_def; line_ok_pre_def; cbw_to_asm_def] THEN
    REWRITE_TAC[asm_ok_def; reg_ok_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    CASES_ON `ad:(A)addr` THEN REWRITE_TAC[addr_ok_def; inst_ok_def; reg_ok_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; distinctness "memop"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 3629 [local] *)
let flatten_line_ok_pre = prove
 (`!t (p:(A)stack_prog) n m cs bs ls a b c.
     asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
     stack_asm_ok c p /\
     stack_to_lab_flatten t p n m cs bs = (ls,a,b)
     ==> ALL (line_ok_pre c) (append ls)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:bool`; `p:(A)stack_prog`; `n:num`; `m:num`; `cs:num list`; `bs:num list`]
    (MATCH_MP S2LP2AUX_flatten_line_ok_pre
      (ASSUME `asm_offset_ok 0 (asm_config_byte_offset (c:(A)asm_config)) (word 0)`))) THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 line 3663 (HOL4 Overload all_enc_ok_pre c ls is ALL (sec_ok_pre c)  *)
(* ls) *)
let compile_all_enc_ok_pre = prove
 (`!c (prog:(num#(A)stack_prog)list).
     asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
     ALL (\(n,p). stack_asm_ok c p) prog
     ==> ALL (sec_ok_pre c) (MAP prog_to_section prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ALL_MAP] THEN
  FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "stack_asm_ok")) THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM; prog_to_section_def; LET_DEF; LET_END_DEF;
              S2LP2AUX_pCASE3] THEN
  REWRITE_TAC[sec_ok_pre_def; append_thm; ALL_APPEND; ALL; line_ok_pre_def] THEN
  ASM_SIMP_TAC[S2LP2AUX_flatten_line_ok_pre]);;

let S2LP2AUX_names_asm_ok = prove
 (`!f (c:(A)asm_config) (prog:(num#(A)stack_prog)list).
     ALL (\(n,p). stack_asm_name c p) prog /\
     stack_names_names_ok f (asm_config_reg_count c) (asm_config_avoid_regs c) /\
     fixed_names f c
     ==> ALL (\(n,p). stack_asm_ok c p) (stack_names_compile f prog)`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC stack_names_stack_asm_ok);;

(* HOL4 line 3679 (names_ok is stack_names') *)
let stack_to_lab_compile_all_enc_ok = prove
 (`!(prog:(num#(A)stack_prog)list) (c:(A)asm_config) c1 c2 c3 sp.
     ALL (\(n,p). stack_asm_name c p) prog /\
     ALL (\(n,p). stack_asm_remove c p) prog /\
     stack_names_names_ok (stack_to_lab_config_reg_names c1) (asm_config_reg_count c)
       (asm_config_avoid_regs c) /\
     fixed_names (stack_to_lab_config_reg_names c1) c /\
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\ good_dimindex (:A) /\
     asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
     (!n. n <= max_stack_alloc
          ==> asm_config_valid_imm c (INL asm_Sub) (word (n * (dimindex (:A) DIV 8))) /\
              asm_config_valid_imm c (INL asm_Add) (word (n * (dimindex (:A) DIV 8)))) /\
     asm_config_valid_imm c (INL asm_Add) (word 1) /\ asm_config_valid_imm c (INL asm_Sub) (word 1) /\
     asm_config_valid_imm c (INL asm_Add) (word 4) /\ asm_config_valid_imm c (INL asm_Add) (word 8) /\
     (!s. asm_offset_ok 0 (asm_config_addr_offset c) (store_offset s)) /\ reg_name 10 c /\
     reg_name (sp + 2) c /\ reg_name (sp + 1) c /\ reg_name sp c /\
     conf_ok (:A) c2 /\ ~(sp = 0)
     ==> ALL (sec_ok_pre c) (stack_to_lab_compile c1 c2 c3 sp (asm_config_addr_offset c) prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC compile_all_enc_ok_pre THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC S2LP2AUX_names_asm_ok THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `stack_rawcall_compile (prog:(num#(A)stack_prog)list)`;
                 `c2:data_to_word_config`] stack_allocProof_stack_alloc_stack_asm_convs) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[stack_rawcallProof_stack_alloc_stack_asm_convs]; STRIP_TAC] THEN
  MATCH_MP_TAC stack_remove_stack_asm_name THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `reg_name 10 (c:(A)asm_config)` THEN REWRITE_TAC[reg_name_def] THEN ARITH_TAC);;


(* init_store_ok of the state made by make_init_any *)

let S2LP2AUX_FLOOKUP_const_list = prove
 (`!(l:A list) (v:B) fm k.
     FLOOKUP (fm |++ MAP (\x. (x,v)) l) k = if MEM k l then SOME v else FLOOKUP fm k`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; FUPDATE_LIST_THM; MEM; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [`MEM (k:A) t`; `(h:A) = k`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let S2LP2AUX_init_store_ok_any = prove
 (`!gen max_heap (bitmaps:(A word)list) data_sp coracle jump off k code
    (s:(A,C,FFI)stack_state) c1.
     max_heap = 2 * max_heap_limit (:A) c1 - 1 /\
     gen = is_gen_gc (data_to_word_config_gc_kind c1)
     ==> init_store_ok c1
           (fdomsub (stack_state_store
              (make_init_any gen max_heap bitmaps data_sp coracle jump off k code s)) Handler)
           (stack_state_memory
              (make_init_any gen max_heap bitmaps data_sp coracle jump off k code s))
           (stack_state_mdomain
              (make_init_any gen max_heap bitmaps data_sp coracle jump off k code s))
           (stack_state_code_buffer
              (make_init_any gen max_heap bitmaps data_sp coracle jump off k code s))
           (stack_state_data_buffer
              (make_init_any gen max_heap bitmaps data_sp coracle jump off k code s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[make_init_any_def] THEN
  CASES_ON `make_init_opt gen max_heap bitmaps data_sp coracle jump off k code
              (s:(A,C,FFI)stack_state)` THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[init_store_ok_def; DOMSUB_FLOOKUP_THM; (record_info "stack_state").ri_accfupds;
                K_THM; S2LP2AUX_FLOOKUP_const_list] THEN
    REWRITE_TAC[MEM; stack_remove_store_list_def; distinctness "store_name"] THEN
    EXISTS_TAC `0` THEN EXISTS_TAC `word 0:A word` THEN
    CASES_ON `data_to_word_config_gc_kind c1` THEN CASE_REWRITE_TAC[] THEN
    SIMP[WORD_MUL_0; WORD_ADD_0; LE_0; ADD_CLAUSES; stack_removeProof_word_list_exists_thm;
         emp_def; fun2set_EMPTY; byte_aligned_def; aligned_0];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP S2LP2AUX_make_init_opt_SOME) THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `init_prop gen max_heap data_sp
                   (get_stack_heap_limit max_heap (read_pointers (s:(A,C,FFI)stack_state)))
                   (a:(A,C,FFI)stack_state)` THEN
    REWRITE_TAC[init_prop_def] THEN STRIP_TAC THEN
    REWRITE_TAC[init_store_ok_def; DOMSUB_FLOOKUP_THM; distinctness "store_name"] THEN
    MAP_EVERY EXISTS_TAC [`len:num`; `curr:A word`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * n = n + n`; stack_removeProof_word_list_exists_ADD] THEN
    REWRITE_TAC[WORD_MUL_SYM] THEN
    CONJ_TAC THENL [UNDISCH_TAC `len + len <= max_heap` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
                    ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    CASES_ON `data_to_word_config_gc_kind c1` THEN CASE_REWRITE_TAC[is_gen_gc_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[is_gen_gc_def]) THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 3704 (HOL4 fmis.store \\ Handler is fdomsub) *)
let IMP_init_store_ok = prove
 (`!max_heap c1 fmis xxx stack_conf sp offset (bitmaps:(A word)list) code
     (s:(A,C,FFI)lab_state) save_regs data_sp coracle.
     max_heap = 2 * max_heap_limit (:A) c1 - 1 /\
     (fmis,xxx) = full_make_init stack_conf c1 max_heap sp offset bitmaps code s save_regs
                    data_sp coracle
     ==> init_store_ok c1 (fdomsub (stack_state_store fmis) Handler) (stack_state_memory fmis)
           (stack_state_mdomain fmis) (stack_state_code_buffer fmis)
           (stack_state_data_buffer fmis)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SYM)) THEN
  REWRITE_TAC[S2LP2AUX_full_make_init_eq] THEN STRIP_TAC THEN
  UNDISCH_TAC `fmis = stack_allocProof_make_init c1 (fromAList code) coracle
                        (s1:(A,C,FFI)stack_state)` THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[stack_allocProof_make_init_def; (record_info "stack_state").ri_accfupds; K_THM] THEN
  UNDISCH_TAC `s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump offset sp
                      (fromAList code1) (s2:(A,C,FFI)stack_state)` THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC S2LP2AUX_init_store_ok_any THEN ASM_REWRITE_TAC[]);;

(* helpers for IMP_init_state_ok *)

let S2LP2AUX_DROP_LAST = prove
 (`!n (l:A list) x. LENGTH l = SUC n /\ LAST l = x ==> DROP n l = [x]`,
  INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; DROP; LAST] THENL
   [REWRITE_TAC[LENGTH_EQ_NIL] THEN MESON_TAC[];
    GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(t:A list = [])` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; NOT_SUC]) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

let S2LP2AUX_GABS21 = prove
 (`!(f:A->B->C->D) (x:(A#B)#C). (\((a,b),c). f a b c) x = f (FST (FST x)) (SND (FST x)) (SND x)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let S2LP2AUX_pCASE21 = prove
 (CASE_TERM
  `!(f:A->B->C->D) (x:(A#B)#C). (match x with ((a,b),c) -> f a b c) =
                                f (FST (FST x)) (SND (FST x)) (SND x)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 3738 (store_consts_stub_location of the wordLang programs is   *)
(* wordLang's; init_state_ok is word_to_stackProof's) *)
let IMP_init_state_ok = prove
 (`!kkk (bitmaps:(A word)list) t word_oracle stack_oracle ac scc dc max_heap stk stoff p6
     (lab_st:(A,C,FFI)lab_state) save_regs data_sp fmis xxx.
     4 < kkk /\
     bitmaps = CONS (word 4) t /\
     good_dimindex (:A) /\
     (!n. (\((bm0,cfg),progs).
             ALL (post_alloc_conventions kkk o SND o SND) progs /\
             ALL (flat_exp_conventions o SND o SND) progs /\
             ALL ((\y. ~(raise_stub_location = y)) o FST) progs /\
             ALL ((\y. ~(wl_store_consts_stub_location = y)) o FST) progs /\
             (n = 0 ==> bm0 = LENGTH bitmaps)) (word_oracle n)) /\
     stack_oracle =
       (\n. (\((bm0,cfg),progs).
               (\(progs,fs,bm). (cfg,progs,append (FST bm)))
                 (compile_word_to_stack ac F kkk progs (Nil,bm0))) (word_oracle n)) /\
     full_make_init scc dc max_heap stk stoff bitmaps p6 lab_st save_regs data_sp stack_oracle =
       (fmis,SOME xxx)
     ==> init_state_ok ac kkk fmis word_oracle`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP2AUX_full_make_init_eq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(LABEL_TAC "opt" o SYM o
                check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
                                 (try fst(dest_const(rator(lhs(concl th)))) = "SOME"
                                  with Failure _ -> false))) THEN
  USE_THEN "opt" (MP_TAC o MATCH_MP S2LP2AUX_make_init_opt_SOME) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s1:(A,C,FFI)stack_state = xxx` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `s1 = make_init_any ggc max_heap bitmaps data_sp coracle1 jump stoff stk
                        (fromAList code1) (s2:(A,C,FFI)stack_state)` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[make_init_any_def] THEN
    USE_THEN "opt" (fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `init_prop ggc max_heap data_sp
                 (get_stack_heap_limit max_heap (read_pointers (s2:(A,C,FFI)stack_state)))
                 (xxx:(A,C,FFI)stack_state)` THEN
  REWRITE_TAC[init_prop_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stack_state_bitmaps (xxx:(A,C,FFI)stack_state) = CONS (word 4) t /\
                buffer_space_left (stack_state_data_buffer xxx) = data_sp`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `xxx = init_reduce ggc jump stoff stk (fromAList code1) bitmaps data_sp coracle1
                         (t0:(A,C,FFI)stack_state)` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF] THEN SIMP[];
    ALL_TAC] THEN
  UNDISCH_TAC `fmis = stack_allocProof_make_init dc (fromAList (p6:(num#(A)stack_prog)list))
                        (stack_oracle:num->C#(num#(A)stack_prog)list#(A word)list)
                        (xxx:(A,C,FFI)stack_state)` THEN
  DISCH_THEN SUBST1_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
    (let l = lhs (concl th) in
     is_var l && mem (fst(dest_var l)) ["f";"jump";"ggc";"code1";"code2";"coracle1";
                                        "coracle2";"coracle3";"s3";"s2";"xxx"])))) THEN
  REWRITE_TAC[init_state_ok_def; stack_allocProof_make_init_def;
              (record_info "stack_state").ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[gc_fun_ok_word_gc_fun] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try fst(dest_const(rator(lhs(concl th)))) = "stack_state_bitmaps" with Failure _ -> false)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN REWRITE_TAC[LENGTH] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ARITH_TAC;
    ASM_ARITH_TAC;
    REWRITE_TAC[IS_PREFIX];
    MATCH_MP_TAC S2LP2AUX_DROP_LAST THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `Handler`)) (concl th))) THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT];
    ASM_ARITH_TAC;
    REWRITE_TAC[FUN_EQ_THM; S2LP2AUX_GABS21; S2LP2AUX_GABS3; S2LP2AUX_pCASE21;
                S2LP2AUX_pCASE3];
    FIRST_X_ASSUM(MP_TAC o check (s2lp2aux_has "post_alloc_conventions")) THEN
    ASM_REWRITE_TAC[S2LP2AUX_GABS21; S2LP2AUX_pCASE21; LENGTH]]);;

(* HOL4 line 3789 [simp] *)
let full_make_init_has_fp_ops = prove
 (`!stack_conf dconf b1 b2 mheap sp offset bitmaps code (s:(A,C,FFI)lab_state) save_regs
     dsp cor.
     full_make_init stack_conf
       (data_to_word_config_has_fp_ops_fupd (K b1) (data_to_word_config_has_fp_tern_fupd (K b2) dconf))
       mheap sp offset bitmaps code s save_regs dsp cor =
     full_make_init stack_conf dconf mheap sp offset bitmaps code s save_regs dsp cor`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_make_init_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[compile_has_fp_ops; stack_allocProof_make_init_def; word_gc_fun_has_fp_ops] THEN
  SIMP[]);;

let _ = cake_add_simps [full_make_init_has_fp_ops];;


(* HOL4 line 3800 [simp] (Termination: the size of the program; HOL4 UNION  *)
(* binds tighter than INSERT; the handler's (r,l1,l2) is (r',l1',l2'); made  *)
(* with sem1aux_def_wf, as stackProps' stack_get_code_labels: cake_def_wf    *)
(* did not finish in 10 min) *)
let complex_get_code_labels_def = sem1aux_def_wf
  `measure (stack_prog_size (\x:A. 0))`
  SEM1AUX_TC_TAC
  `(complex_get_code_labels (stack_Seq p1 p2:(A)stack_prog) =
      complex_get_code_labels p1 UNION complex_get_code_labels p2) /\
   (complex_get_code_labels (stack_If _ _ _ p1 p2) =
      complex_get_code_labels p1 UNION complex_get_code_labels p2) /\
   (complex_get_code_labels (stack_Call ret dest handler) =
      (match dest with INL x -> {(x,0)} | _ -> {}) UNION
      (match ret with
         NONE -> {}
       | SOME (r,_,l1,l2) ->
           (l1,l2) INSERT
           (complex_get_code_labels r UNION
            (match handler with
               NONE -> {}
             | SOME (r',l1',l2') -> (l1',l2') INSERT complex_get_code_labels r')))) /\
   (complex_get_code_labels (stack_Loop p) = complex_get_code_labels p) /\
   (complex_get_code_labels (stack_LocValue i l1 l2) = {(l1,l2)}) /\
   (complex_get_code_labels (RawCall l) = {(l,1)}) /\
   (complex_get_code_labels (JumpLower n m l) = {(l,0)}) /\
   (complex_get_code_labels _ = {})`;;

let complex_get_code_labels_ind = cake_ind "complex_get_code_labels";;

let _ = cake_add_simps [complex_get_code_labels_def];;

(* helpers for the flatten label lemmas *)

let S2LP2AUX_SUBSET_TRANS_IMP = prove
 (`!(s:A->bool) t u. s SUBSET t ==> t SUBSET u ==> s SUBSET u`,
  SET_TAC[]);;
let s2lp2aux_split_cj : tactic = fun (asl,w as g) ->
  match find_terms (fun t -> is_comb t &&
                     (try fst(dest_const(rator t)) = "compile_jump" with Failure _ -> false)) w with
    [] -> ALL_TAC g
  | t::_ -> (CASES_ON (rand t) THEN REWRITE_TAC[compile_jump_def]) g;;
(* HOL4 line 3818 [local] (HOL4 UNION binds tighter than INSERT) *)
let complex_flatten_labels = prove
 (`!t (p:(A)stack_prog) n m cs bs.
     let pp = set_of_list (append (FST (stack_to_lab_flatten t p n m cs bs))) in
     UNIONS (IMAGE line_get_labels pp) SUBSET
     (n,0) INSERT
     ((n,if t /\ (?p1 p2. p = stack_Seq p1 p2) then 1 else 0) INSERT
      ((set_of_list (MAP (\l. (n,l)) (APPEND cs bs)) UNION
        IMAGE (\n2. (n,n2)) (UNIONS (IMAGE line_get_code_labels pp))) UNION
       complex_get_code_labels p))`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (STRIP_ASSUME_TAC o CAKE_SIMP_RULE[]) THEN
  REPEAT s2lp2aux_split_opt THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[PAIR_EQ]) THEN
  (fun (asl,w as g) ->
     let is_fl th = is_eq (concl th) &&
                 (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_to_lab_flatten"
                  with Failure _ -> false) in
     let eqs = filter is_fl (map snd asl) in
     RULE_ASSUM_TAC(CAKE_SIMP_RULE(FST::PAIR_EQ::eqs)) g) THEN
  REWRITE_TAC[FST; append_thm; set_of_list; SET_OF_LIST_APPEND; IMAGE_CLAUSES; IMAGE_UNION;
              UNIONS_INSERT; UNIONS_UNION; UNIONS_0; line_get_labels_def; labs_of_def;
              line_get_code_labels_def; complex_get_code_labels_def; compile_jump_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[UNION_EMPTY; EMPTY_SUBSET; INSERT_SUBSET; UNION_SUBSET; IN_INSERT; IN_UNION;
              NOT_IN_EMPTY] THEN
  s2lp2aux_split_cj THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[FST; append_thm; set_of_list; SET_OF_LIST_APPEND; IMAGE_CLAUSES; IMAGE_UNION;
              UNIONS_INSERT; UNIONS_UNION; UNIONS_0; line_get_labels_def; labs_of_def;
              line_get_code_labels_def; MAP_APPEND] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[UNION_EMPTY; EMPTY_SUBSET; INSERT_SUBSET; UNION_SUBSET; IN_INSERT; IN_UNION;
              NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(fun ih -> MATCH_MP_TAC (MATCH_MP S2LP2AUX_SUBSET_TRANS_IMP ih) THEN
                            SET_TAC[])) THEN
  REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; PAIR_EQ] THEN MESON_TAC[NOT_MEM_find_lab_IMP]);;


let S2LP2AUX_flatten_labels = prove
 (`!t (m:(A)stack_prog) n p cs bs l.
     FST (stack_to_lab_flatten t m n p cs bs) = l
     ==> ALL (sec_label_ok n) (append l)
     ==> UNIONS (IMAGE line_get_labels (set_of_list (append l))) SUBSET
         (set_of_list (MAP (\j. (n,j)) (APPEND cs bs)) UNION
          sec_get_code_labels (Section n (append l))) UNION
         stack_get_code_labels m`,
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (STRIP_ASSUME_TAC o CAKE_SIMP_RULE[]) THEN
  REPEAT s2lp2aux_split_opt THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[PAIR_EQ]) THEN
  (fun (asl,w as g) ->
     let is_fl th = is_eq (concl th) &&
                 (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_to_lab_flatten"
                  with Failure _ -> false) in
     let eqs = filter is_fl (map snd asl) in
     RULE_ASSUM_TAC(CAKE_SIMP_RULE(FST::PAIR_EQ::eqs)) g) THEN
  s2lp2aux_split_cj THEN REPEAT COND_CASES_TAC THEN
  GEN_TAC THEN REWRITE_TAC[FST] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[append_thm; set_of_list; SET_OF_LIST_APPEND; IMAGE_CLAUSES; IMAGE_UNION;
              UNIONS_INSERT; UNIONS_UNION; UNIONS_0; line_get_labels_def; labs_of_def;
              line_get_code_labels_def; MAP_APPEND; sec_get_code_labels_def; ALL_APPEND; ALL;
              sec_label_ok_def; stack_get_code_labels_def; compile_jump_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[UNION_EMPTY; EMPTY_SUBSET; INSERT_SUBSET; UNION_SUBSET; IN_INSERT; IN_UNION;
              NOT_IN_EMPTY] THEN
  TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp (concl th)
                                 then FIRST_ASSUM(fun pr -> ASSUME_TAC (MP th pr))
                                 else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sec_get_code_labels_def]) THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(fun ih -> MATCH_MP_TAC (MATCH_MP S2LP2AUX_SUBSET_TRANS_IMP ih) THEN
                            SET_TAC[])) THEN
  REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; IN_IMAGE; PAIR_EQ; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
              IN_UNIONS] THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[NOT_MEM_find_lab_IMP]);;

(* HOL4 line 3876 [local] (the lambda-bound l of HOL4 is j: l is also the    *)
(* code) *)
let flatten_labels = prove
 (`!t (m:(A)stack_prog) n p cs bs l x y.
     stack_to_lab_flatten t m n p cs bs = (l,x,y) /\
     ALL (sec_label_ok n) (append l)
     ==> UNIONS (IMAGE line_get_labels (set_of_list (append l))) SUBSET
         (set_of_list (MAP (\j. (n,j)) (APPEND cs bs)) UNION
          sec_get_code_labels (Section n (append l))) UNION
         stack_get_code_labels m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:bool`; `m:(A)stack_prog`; `n:num`; `p:num`; `cs:num list`;
                 `bs:num list`; `l:((A)line)app_list`] S2LP2AUX_flatten_labels) THEN
  ASM_REWRITE_TAC[FST]);;


let S2LP2AUX_set_lemma1 = prove
 (`!(A:B->bool) R G U b B C x.
     R SUBSET G UNION U ==> A SUBSET b INSERT B UNION C
     ==> A UNION R SUBSET ((b INSERT (B UNION {x})) UNION G) UNION C UNION U`,
  SET_TAC[]);;

let S2LP2AUX_prog_to_section_eq = prove
 (`!n (q:(A)stack_prog).
     prog_to_section (n,q) =
     Section n (APPEND (append (FST (stack_to_lab_flatten T q n (next_lab q 2) [] [])))
                 [lab_Label n (if is_Seq q then SND (SND (stack_to_lab_flatten T q n
                                                            (next_lab q 2) [] []))
                               else 1) 0])`,
  REWRITE_TAC[prog_to_section_def; LET_DEF; LET_END_DEF; S2LP2AUX_pCASE3; append_thm]);;

(* HOL4 line 3931 (get_labels and get_code_labels of sections are           *)
(* labProps', of stackLang programs stackProps') *)
let get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma = prove
 (`!(p:(num#(A)stack_prog)list).
     ALL sec_labels_ok (MAP prog_to_section p)
     ==> lab_get_labels (MAP prog_to_section p) SUBSET
         lab_get_code_labels (MAP prog_to_section p) UNION
         UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND p)))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL; lab_get_labels_def; set_of_list; IMAGE_CLAUSES; UNIONS_0; EMPTY_SUBSET] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; S2LP2AUX_prog_to_section_eq] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q:(A)stack_prog`] THEN
  REWRITE_TAC[GSYM lab_get_labels_def; get_labels_cons; get_code_labels_cons; SND; IMAGE_CLAUSES;
              UNIONS_INSERT; sec_labels_ok_def; sec_get_labels_def; SET_OF_LIST_APPEND;
              ALL_APPEND; ALL; set_of_list; IMAGE_UNION; UNIONS_UNION; line_get_labels_def;
              UNION_EMPTY] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`T`; `q:(A)stack_prog`; `n:num`; `next_lab (q:(A)stack_prog) 2`;
                 `[]:num list`; `[]:num list`;
                 `FST (stack_to_lab_flatten T (q:(A)stack_prog) n (next_lab q 2) [] [])`]
                S2LP2AUX_flatten_labels) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[sec_get_code_labels_def; SET_OF_LIST_APPEND; set_of_list; MAP; APPEND;
              IMAGE_UNION; UNIONS_UNION; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0;
              line_get_code_labels_def; UNION_EMPTY] THEN
  MATCH_ACCEPT_TAC S2LP2AUX_set_lemma1);;

(* HOL4 line 3951 [local] *)
let prog_to_section_preserves_MAP_FST = prove
 (`!(p:(num#(A)stack_prog)list).
     IMAGE (\n. (n,0)) (set_of_list (MAP FST p)) SUBSET lab_get_code_labels (MAP prog_to_section p)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; S2LP2AUX_prog_to_section_eq; get_code_labels_cons; FST;
              sec_get_code_labels_def] THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let S2LP2AUX_flatten_Seq_label = prove
 (`!(p1:(A)stack_prog) p2 n m.
     MEM (lab_Label n 1 0) (append (FST (stack_to_lab_flatten T (stack_Seq p1 p2) n m [] [])))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[S2LP2AUX_pCASE3; LET_DEF; LET_END_DEF; FST; append_thm; MEM_APPEND; MEM]);;

let S2LP2AUX_set_lemma2 = prove
 (`!(A:B->bool) x y B D C.
     A SUBSET x INSERT (y INSERT (B UNION C)) /\ y IN x INSERT (B UNION D)
     ==> A SUBSET (x INSERT (B UNION D)) UNION C`,
  SET_TAC[]);;

(* HOL4 line 3963 *)
let prog_to_section_labels = prove
 (`!n (p:(A)stack_prog) pp.
     prog_to_section (n,p) = pp
     ==> sec_get_labels pp SUBSET sec_get_code_labels pp UNION complex_get_code_labels p`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[S2LP2AUX_prog_to_section_eq; sec_get_labels_def; sec_get_code_labels_def;
              SET_OF_LIST_APPEND; set_of_list; IMAGE_UNION; IMAGE_CLAUSES; UNIONS_UNION;
              UNIONS_INSERT; UNIONS_0; line_get_labels_def; line_get_code_labels_def;
              UNION_EMPTY] THEN
  MATCH_MP_TAC S2LP2AUX_set_lemma2 THEN
  EXISTS_TAC `(n:num,if T /\ (?p1 p2. (p:(A)stack_prog) = stack_Seq p1 p2) then 1 else 0)` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`T`; `p:(A)stack_prog`; `n:num`; `next_lab (p:(A)stack_prog) 2`;
                  `[]:num list`; `[]:num list`] complex_flatten_labels) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; APPEND; MAP; set_of_list; UNION_EMPTY];
    ASM_CASES_TAC `?p1 p2. (p:(A)stack_prog) = stack_Seq p1 p2` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `p1:(A)stack_prog` (X_CHOOSE_THEN `p2:(A)stack_prog`
      SUBST_ALL_TAC)) THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; PAIR_EQ; IN_UNIONS; IN_SET_OF_LIST] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `1` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `line_get_code_labels (lab_Label n 1 0:(A)line)` THEN
    REWRITE_TAC[line_get_code_labels_def; IN_SING] THEN
    EXISTS_TAC `lab_Label n 1 0:(A)line` THEN
    REWRITE_TAC[S2LP2AUX_flatten_Seq_label; line_get_code_labels_def]]);;

let S2LP2AUX_flatten_handler = prove
 (`!t (m:(A)stack_prog) n p cs bs l.
     FST (stack_to_lab_flatten t m n p cs bs) = l
     ==> stack_get_handler_labels n m SUBSET sec_get_code_labels (Section n (append l))`,
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (STRIP_ASSUME_TAC o CAKE_SIMP_RULE[]) THEN
  REPEAT s2lp2aux_split_opt THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[PAIR_EQ]) THEN
  (fun (asl,w as g) ->
     let is_fl th = is_eq (concl th) &&
                 (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_to_lab_flatten"
                  with Failure _ -> false) in
     let eqs = filter is_fl (map snd asl) in
     RULE_ASSUM_TAC(CAKE_SIMP_RULE(FST::PAIR_EQ::eqs)) g) THEN
  s2lp2aux_split_cj THEN REPEAT COND_CASES_TAC THEN
  GEN_TAC THEN REWRITE_TAC[FST] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[append_thm; set_of_list; SET_OF_LIST_APPEND; IMAGE_CLAUSES; IMAGE_UNION;
              UNIONS_INSERT; UNIONS_UNION; UNIONS_0; line_get_code_labels_def; MAP_APPEND;
              sec_get_code_labels_def; stack_get_handler_labels_def; compile_jump_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[UNION_EMPTY; EMPTY_SUBSET; INSERT_SUBSET; UNION_SUBSET; IN_INSERT; IN_UNION;
              NOT_IN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sec_get_code_labels_def]) THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(fun ih -> MATCH_MP_TAC (MATCH_MP S2LP2AUX_SUBSET_TRANS_IMP ih) THEN
                            SET_TAC[])) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
           is_var (lhs (concl th)) && rhs (concl th) = `stack_Skip:(A)stack_prog`))) THEN
  REWRITE_TAC[stack_get_handler_labels_def; EMPTY_SUBSET] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN SET_TAC[]);;

(* HOL4 line 3984 *)
let flatten_preserves_handler_labels = prove
 (`!t (m:(A)stack_prog) n p cs bs l x y.
     stack_to_lab_flatten t m n p cs bs = (l,x,y)
     ==> stack_get_handler_labels n m SUBSET sec_get_code_labels (Section n (append l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC S2LP2AUX_flatten_handler THEN
  MAP_EVERY EXISTS_TAC [`t:bool`; `p:num`; `cs:num list`; `bs:num list`] THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 line 4026 *)
let MAP_prog_to_section_preserves_handler_labels = prove
 (`!(p:(num#(A)stack_prog)list).
     UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) p)) SUBSET
     lab_get_code_labels (MAP prog_to_section p)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; set_of_list; UNIONS_0; EMPTY_SUBSET] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `q:(A)stack_prog`] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[UNIONS_INSERT; get_code_labels_cons] THEN
  MP_TAC(ISPECL [`T`; `q:(A)stack_prog`; `n:num`; `next_lab (q:(A)stack_prog) 2`;
                 `[]:num list`; `[]:num list`;
                 `FST (stack_to_lab_flatten T (q:(A)stack_prog) n (next_lab q 2) [] [])`]
                S2LP2AUX_flatten_handler) THEN
  REWRITE_TAC[S2LP2AUX_prog_to_section_eq; sec_get_code_labels_def; SET_OF_LIST_APPEND;
              IMAGE_UNION; UNIONS_UNION] THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

(* HOL4 line 4044 *)
let one_prog_section = prove
 (`!(p:(num#(A)stack_prog)list).
     IMAGE (\n. (n,1)) (set_of_list (MAP FST p)) SUBSET lab_get_code_labels (MAP prog_to_section p)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `q:(A)stack_prog`] THEN
  REWRITE_TAC[FST; get_code_labels_cons; INSERT_SUBSET] THEN
  CONJ_TAC THENL [ALL_TAC; POP_ASSUM MP_TAC THEN SET_TAC[]] THEN
  REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
  REWRITE_TAC[S2LP2AUX_prog_to_section_eq; sec_get_code_labels_def; IN_INSERT; IN_IMAGE;
              PAIR_EQ; IN_UNIONS; IN_SET_OF_LIST; MEM_APPEND; MEM] THEN
  DISJ2_TAC THEN EXISTS_TAC `1` THEN REWRITE_TAC[] THEN
  EXISTS_TAC `{1}` THEN REWRITE_TAC[IN_SING] THEN
  ASM_CASES_TAC `is_Seq (q:(A)stack_prog)` THENL
   [EXISTS_TAC `lab_Label n 1 0:(A)line` THEN REWRITE_TAC[line_get_code_labels_def] THEN
    UNDISCH_TAC `is_Seq (q:(A)stack_prog)` THEN
    CASES_ON `q:(A)stack_prog` THEN REWRITE_TAC[is_Seq_def; S2LP2AUX_flatten_Seq_label];
    EXISTS_TAC `lab_Label n 1 0:(A)line` THEN ASM_REWRITE_TAC[line_get_code_labels_def]]);;

let S2LP2AUX_set_lemma3 = prove
 (`!(GL:A->bool) CL SL H F0 E0 F1 E1.
     GL SUBSET CL UNION SL /\ SL SUBSET (((H UNION F0) UNION E0) UNION F1) UNION E1 /\
     H SUBSET CL /\ F0 SUBSET CL /\ F1 SUBSET CL
     ==> GL SUBSET (CL UNION E0) UNION E1`,
  SET_TAC[]);;

(* HOL4 line 4062 (elabs is free in HOL4) *)
let get_labels_MAP_prog_to_section_SUBSET_code_labels = prove
 (`!(p:(num#(A)stack_prog)list) elabs.
     ALL sec_labels_ok (MAP prog_to_section p) /\ stack_good_code_labels p elabs
     ==> lab_get_labels (MAP prog_to_section p) SUBSET
         (lab_get_code_labels (MAP prog_to_section p) UNION IMAGE (\n. (n,0)) elabs) UNION
         IMAGE (\n. (n,1)) elabs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_good_code_labels_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_set_lemma3 THEN
  EXISTS_TAC `UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND (p:(num#(A)stack_prog)list))))` THEN
  EXISTS_TAC `UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp)
                                      (p:(num#(A)stack_prog)list)))` THEN
  EXISTS_TAC `IMAGE (\n. n,0) (set_of_list (MAP FST (p:(num#(A)stack_prog)list)))` THEN
  EXISTS_TAC `IMAGE (\n. n,1) (set_of_list (MAP FST (p:(num#(A)stack_prog)list)))` THEN
  ASM_SIMP_TAC[get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma;
               MAP_prog_to_section_preserves_handler_labels; prog_to_section_preserves_MAP_FST;
               one_prog_section]);;


(* ---- stack_names ---- *)

(* the clauses of a recursive function c (a curried constant applied to its *)
(* leading arguments args) defined by a match on a stack_prog, one per     *)
(* constructor *)
let s2lp2aux_comp_clauses (c:term) (def:thm) : thm =
  let ci = case_info_of_tyname "stack_prog" in
  let ty = `:(A)stack_prog` in
  end_itlist CONJ
   (map (fun (vs,pat) ->
          let tyi = type_match (type_of pat) ty [] in
          let pat = inst tyi pat in
          let tm = mk_comb(c,pat) in
          GEN_ALL ((REWR_CONV def THENC CASE_REWRITE_CONV[]) tm))
        ci.ci_pats);;

let s2lp2aux_ih_rws =
  [distinctness "stack_prog"; injectivity "stack_prog"; option_INJ;
   option_DISTINCT; PAIR_EQ; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1;
   FORALL_UNWIND_THM2];;

let S2LP2AUX_names_clauses =
  s2lp2aux_comp_clauses `stack_names_comp (f:num spt):(A)stack_prog->(A)stack_prog`
    stack_names_comp_def;;

(* split the argument x of a dest_find_name f x in the goal *)
let s2lp2aux_split_dest : tactic = fun (asl,w as g) ->
  match find_terms (fun t -> is_comb t && length (snd (strip_comb t)) = 2 &&
                     (try fst(dest_const(fst(strip_comb t))) = "dest_find_name"
                      with Failure _ -> false)) w with
    [] -> ALL_TAC g
  | t::_ -> CASES_ON (rand t) g;;

(* HOL4 line 4090 [local] *)
let get_code_labels_comp = prove
 (`!f (p:(A)stack_prog).
     complex_get_code_labels (stack_names_comp f p) = complex_get_code_labels p`,
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_names_clauses] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  SIMP[complex_get_code_labels_def; dest_find_name_def] THEN
  s2lp2aux_split_dest THEN CASE_REWRITE_TAC[dest_find_name_def]);;

(* HOL4 line 4099 (f and prog are free in HOL4) *)
let stack_names_get_code_labels = prove
 (`!f (prog:(num#(A)stack_prog)list).
     ALL2 (\cp p. complex_get_code_labels cp = complex_get_code_labels p)
       (MAP SND (stack_names_compile f prog)) (MAP SND prog)`,
  GEN_TAC THEN REWRITE_TAC[stack_names_compile_def] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2] THEN
  SUBST1_TAC(ISPEC `h:num#(A)stack_prog` (GSYM PAIR)) THEN
  REWRITE_TAC[stack_names_prog_comp_def; SND; get_code_labels_comp]);;


(* ---- stack_remove ---- *)

(* labels of the auxiliary programs of stack_remove *)

let S2LP2AUX_remove_aux = prove
 (`(!jump k n. stack_get_code_labels (stack_alloc jump k n:(A)stack_prog) SUBSET
               {(stack_err_lab,0)} /\
               (!m. stack_get_handler_labels m (stack_alloc jump k n:(A)stack_prog) = {})) /\
   (!k n. stack_get_code_labels (stack_remove_stack_free k n:(A)stack_prog) = {} /\
          (!m. stack_get_handler_labels m (stack_remove_stack_free k n:(A)stack_prog) = {})) /\
   (!r n. stack_get_code_labels (upshift r n:(A)stack_prog) = {} /\
          (!m. stack_get_handler_labels m (upshift r n:(A)stack_prog) = {})) /\
   (!r n. stack_get_code_labels (downshift r n:(A)stack_prog) = {} /\
          (!m. stack_get_handler_labels m (downshift r n:(A)stack_prog) = {}))`,
  SUBGOAL_THEN
   `!jump k n. stack_get_code_labels (single_stack_alloc jump k n:(A)stack_prog) SUBSET
               {(stack_err_lab,0)} /\
               (!m. stack_get_handler_labels m (single_stack_alloc jump k n:(A)stack_prog) = {})`
   ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[single_stack_alloc_def; halt_inst_def] THEN
   COND_CASES_TAC THEN
   SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY;
        EMPTY_SUBSET; SUBSET_REFL];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC stack_alloc_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[stack_alloc_def] THEN
   REPEAT COND_CASES_TAC THEN
   SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY;
        EMPTY_SUBSET; UNION_SUBSET; SUBSET_REFL];
   MATCH_MP_TAC stack_remove_stack_free_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
   REWRITE_TAC[single_stack_free_def] THEN
   REPEAT COND_CASES_TAC THEN
   SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY];
   MATCH_MP_TAC upshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[upshift_def] THEN
   REPEAT COND_CASES_TAC THEN
   SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY];
   MATCH_MP_TAC downshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[downshift_def] THEN
   REPEAT COND_CASES_TAC THEN
   SIMP[stack_get_code_labels_def; stack_get_handler_labels_def; UNION_EMPTY]]);;

let S2LP2AUX_remove_clauses =
  s2lp2aux_comp_clauses `stack_remove_comp s2j (s2o:A word#A word) s2k`
    stack_remove_comp_def;;

(* HOL4 line 4110 [local] (rebinds the name of HOL4 line 4090; comp is      *)
(* stack_remove's) *)
let get_code_labels_comp = prove
 (`!a b c (p:(A)stack_prog).
     stack_get_code_labels (stack_remove_comp a b c p) SUBSET
     (stack_err_lab,0) INSERT stack_get_code_labels p`,
  MATCH_MP_TAC stack_remove_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_remove_clauses; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  SIMP[stack_get_code_labels_def; S2LP2AUX_remove_aux; stack_store_def; stack_load_def;
       copy_loop_def; copy_each_def; stack_list_Seq_def; UNION_EMPTY; EMPTY_SUBSET] THEN
  ASM SET_TAC[]);;

let S2LP2AUX_store_list_code_labels = prove
 (`!a t (xs:(A word+num)list).
     stack_get_code_labels (store_list_code a t xs:(A)stack_prog) = {}`,
  MATCH_MP_TAC store_list_code_ind THEN REPEAT STRIP_TAC THEN
  SIMP[store_list_code_def; stack_list_Seq_def; stack_get_code_labels_def; UNION_EMPTY]);;

let S2LP2AUX_init_code_labels = prove
 (`!ggc mh k. stack_get_code_labels (stack_remove_init_code ggc mh k:(A)stack_prog) = {(1,0)}`,
  REWRITE_TAC[stack_remove_init_code_def; LET_DEF; LET_END_DEF; stack_list_Seq_def;
              init_memory_def] THEN
  SIMP[stack_get_code_labels_def; S2LP2AUX_store_list_code_labels; UNION_EMPTY]);;

(* HOL4 line 4154 [local] *)
let init_stubs_labels = prove
 (`!ggc mh k start.
     ALL (\p. stack_get_code_labels p SUBSET set_of_list [(1,0); (start,0)])
       (MAP SND (stack_remove_init_stubs ggc mh k start:(num#(A)stack_prog)list))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_remove_init_stubs_def; MAP; ALL; set_of_list; halt_inst_def] THEN
  SIMP[stack_get_code_labels_def; S2LP2AUX_init_code_labels; UNION_EMPTY; EMPTY_SUBSET] THEN
  SET_TAC[]);;


(* ---- stack_names ---- *)

(* HOL4 line 4161 [local] *)
let stack_names_get_code_labels_comp = prove
 (`!f (p:(A)stack_prog). stack_get_code_labels (stack_names_comp f p) = stack_get_code_labels p`,
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_names_clauses] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  SIMP[stack_get_code_labels_def; dest_find_name_def] THEN
  s2lp2aux_split_dest THEN CASE_REWRITE_TAC[dest_find_name_def]);;

(* HOL4 line 4170 [local] *)
let stack_names_stack_get_handler_labels_comp = prove
 (`!f (p:(A)stack_prog) n.
     stack_get_handler_labels n (stack_names_comp f p) = stack_get_handler_labels n p`,
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_names_clauses] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  SIMP[stack_get_handler_labels_def]);;

(* HOL4 line 4181 [local] *)
let UNCURRY_PAIR_ETA = prove
 (`!(f:A->B->C). UNCURRY f = (\(p1,p2). f p1 p2)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; UNCURRY_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 4188 (elabs is free in HOL4) *)
let stack_names_stack_good_code_labels = prove
 (`!(prog:(num#(A)stack_prog)list) f elabs.
     stack_good_code_labels prog elabs
     ==> stack_good_code_labels (stack_names_compile f prog) elabs`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `MAP FST (stack_names_compile f (prog:(num#(A)stack_prog)list)) = MAP FST prog /\
    MAP (\(n,pp). stack_get_handler_labels n pp) (stack_names_compile f prog) =
    MAP (\(n,pp). stack_get_handler_labels n pp) prog /\
    MAP stack_get_code_labels (MAP SND (stack_names_compile f prog)) =
    MAP stack_get_code_labels (MAP SND prog)` MP_TAC THENL
  [REWRITE_TAC[stack_names_compile_def] THEN
   SPEC_TAC(`prog:(num#(A)stack_prog)list`,`prog:(num#(A)stack_prog)list`) THEN
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
   SUBST1_TAC(ISPEC `h:num#(A)stack_prog` (GSYM PAIR)) THEN
   REWRITE_TAC[stack_names_prog_comp_def; FST; SND;
               stack_names_get_code_labels_comp;
               stack_names_stack_get_handler_labels_comp] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[stack_names_stack_get_handler_labels_comp];
   STRIP_TAC THEN
   ASM_REWRITE_TAC[stack_good_code_labels_def; GSYM SET_OF_LIST_MAP]]);;

(* ---- stack_remove ---- *)

(* HOL4 line 4200 [local] *)
let stack_remove_get_code_labels_comp = prove
 (`!a b c (p:(A)stack_prog).
     stack_get_code_labels (stack_remove_comp a b c p) SUBSET
     (stack_err_lab,0) INSERT stack_get_code_labels p`,
  REWRITE_TAC[get_code_labels_comp]);;

(* HOL4 line 4245 [local] *)
let stack_remove_stack_get_handler_labels_comp = prove
 (`!a b c (p:(A)stack_prog) m.
     stack_get_handler_labels m (stack_remove_comp a b c p) = stack_get_handler_labels m p`,
  MATCH_MP_TAC stack_remove_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_remove_clauses; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  SIMP[stack_get_handler_labels_def; S2LP2AUX_remove_aux; stack_store_def; stack_load_def;
       copy_loop_def; copy_each_def; stack_list_Seq_def; UNION_EMPTY]);;

(* HOL4 line 4286 [local] *)
let stack_remove_init_code_labels = prove
 (`!x ggc mh sp.
     x IN stack_get_code_labels (stack_remove_init_code ggc mh sp:(A)stack_prog) ==> x = (1,0)`,
  REWRITE_TAC[S2LP2AUX_init_code_labels; IN_SING]);;

(* generic transfer of stack_good_code_labels through a per-function pass *)

let S2LP2AUX_set_lemma5 = prove
 (`!(a:num#num->bool) b c d X.
     a SUBSET X UNION b /\ c SUBSET X UNION d ==> a UNION c SUBSET X UNION (b UNION d)`,
  SET_TAC[]);;

let S2LP2AUX_MAP_pc = prove
 (`!(pc:num#(A)stack_prog->num#(A)stack_prog) (g:num->(A)stack_prog->(A)stack_prog) X.
     (!n p. pc (n,p) = (n,g n p)) /\
     (!n p. stack_get_code_labels (g n p) SUBSET X UNION stack_get_code_labels p) /\
     (!n p. stack_get_handler_labels n (g n p) = stack_get_handler_labels n p)
     ==> !prog. MAP FST (MAP pc prog) = MAP FST prog /\
                MAP (\(n,pp). stack_get_handler_labels n pp) (MAP pc prog) =
                MAP (\(n,pp). stack_get_handler_labels n pp) prog /\
                UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND (MAP pc prog))))
                SUBSET X UNION UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; set_of_list; IMAGE_CLAUSES; UNIONS_0; UNIONS_INSERT; EMPTY_SUBSET] THEN
  SUBST1_TAC(ISPEC `h:num#(A)stack_prog` (GSYM PAIR)) THEN
  ASM_REWRITE_TAC[FST; SND; CONS_11] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC S2LP2AUX_set_lemma5 THEN ASM_REWRITE_TAC[]);;

let S2LP2AUX_set_lemma4 = prove
 (`!(C:num#num->bool) C' X H H' F0 F0' F1 F1' E0 E1.
     C SUBSET (((H UNION F0) UNION E0) UNION F1) UNION E1 /\
     C' SUBSET X UNION C /\ X SUBSET (F0' UNION E0) UNION F1' /\
     F0 SUBSET F0' /\ F1 SUBSET F1' /\ H SUBSET H'
     ==> C' SUBSET (((H' UNION F0') UNION E0) UNION F1') UNION E1`,
  SET_TAC[]);;

let S2LP2AUX_good_code_labels_mono = prove
 (`!(prog:(num#(A)stack_prog)list) (prog':(num#(A)stack_prog)list) elabs X.
     stack_good_code_labels prog elabs /\
     UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog'))) SUBSET
       X UNION UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog))) /\
     X SUBSET (IMAGE (\n. n,0) (set_of_list (MAP FST prog')) UNION IMAGE (\n. n,0) elabs) UNION
              IMAGE (\n. n,1) (set_of_list (MAP FST prog')) /\
     set_of_list (MAP FST prog) SUBSET set_of_list (MAP FST prog') /\
     UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) prog)) SUBSET
       UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) prog'))
     ==> stack_good_code_labels prog' elabs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_good_code_labels_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_set_lemma4 THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND (prog:(num#(A)stack_prog)list))))`;
    `X:num#num->bool`;
    `UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp)
                               (prog:(num#(A)stack_prog)list)))`;
    `IMAGE (\n:num. n,0) (set_of_list (MAP FST (prog:(num#(A)stack_prog)list)))`;
    `IMAGE (\n:num. n,1) (set_of_list (MAP FST (prog:(num#(A)stack_prog)list)))`] THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let S2LP2AUX_remove_pc = prove
 (`!jump (off:A word#A word) sp (prog:(num#(A)stack_prog)list).
     MAP FST (MAP (stack_remove_prog_comp jump off sp) prog) = MAP FST prog /\
     MAP (\(n,pp). stack_get_handler_labels n pp)
         (MAP (stack_remove_prog_comp jump off sp) prog) =
     MAP (\(n,pp). stack_get_handler_labels n pp) prog /\
     UNIONS (IMAGE stack_get_code_labels
               (set_of_list (MAP SND (MAP (stack_remove_prog_comp jump off sp) prog))))
     SUBSET {(stack_err_lab,0)} UNION
            UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`stack_remove_prog_comp jump (off:A word#A word) sp`;
                 `\(n:num) (p:(A)stack_prog). stack_remove_comp jump (off:A word#A word) sp p`;
                 `{(stack_err_lab,0)}`] S2LP2AUX_MAP_pc) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[stack_remove_prog_comp_def; stack_remove_stack_get_handler_labels_comp;
               INSERT_UNION_EQ; UNION_EMPTY; stack_remove_get_code_labels_comp];
   DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let S2LP2AUX_init_stubs_code_labels = prove
 (`!ggc mh sp loc.
     UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND
       (stack_remove_init_stubs ggc mh sp loc:(num#(A)stack_prog)list)))) SUBSET
     {(1,0), (loc,0)} /\
     set_of_list (MAP FST (stack_remove_init_stubs ggc mh sp loc:(num#(A)stack_prog)list)) =
     {0,1,2}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_remove_init_stubs_def; MAP; set_of_list; IMAGE_CLAUSES; UNIONS_0;
              UNIONS_INSERT; halt_inst_def] THEN
  SIMP[stack_get_code_labels_def; S2LP2AUX_init_code_labels; UNION_EMPTY] THEN
  SET_TAC[]);;

(* HOL4 line 4292 *)
let stack_remove_stack_good_code_labels = prove
 (`!(prog:(num#(A)stack_prog)list) loc elabs jump off ggc mh sp.
     MEM loc (MAP FST prog) /\ stack_good_code_labels prog elabs
     ==> stack_good_code_labels (stack_remove_compile jump off ggc mh sp loc prog) elabs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `off:A word#A word`; `sp:num`; `prog:(num#(A)stack_prog)list`]
          S2LP2AUX_remove_pc) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`ggc:bool`; `mh:num`; `sp:num`; `loc:num`] S2LP2AUX_init_stubs_code_labels) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_code_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN
  EXISTS_TAC `{(1,0), (loc,0), (stack_err_lab,0)}` THEN
  ASM_REWRITE_TAC[stack_remove_compile_def; MAP_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
                  UNIONS_UNION] THEN
  REPEAT CONJ_TAC THENL
  [MAP_EVERY UNDISCH_TAC
    [`UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND
       (stack_remove_init_stubs ggc mh sp loc:(num#(A)stack_prog)list)))) SUBSET
      {(1,0), (loc,0)}`;
     `UNIONS (IMAGE stack_get_code_labels
               (set_of_list (MAP SND (MAP (stack_remove_prog_comp jump off sp)
                                          (prog:(num#(A)stack_prog)list)))))
      SUBSET {(stack_err_lab,0)} UNION
             UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog)))`] THEN
   SET_TAC[];
   UNDISCH_TAC `MEM (loc:num) (MAP FST (prog:(num#(A)stack_prog)list))` THEN
   REWRITE_TAC[stack_err_lab_def; INSERT_SUBSET; EMPTY_SUBSET; IN_UNION; IN_IMAGE;
               IN_INSERT; NOT_IN_EMPTY; IN_SET_OF_LIST; PAIR_EQ] THEN
   MESON_TAC[];
   SET_TAC[];
   SET_TAC[]]);;

(* HOL4 line 4326 *)
let stack_remove_stack_good_code_labels_incr = prove
 (`!(prog:(num#(A)stack_prog)list) elabs jump offset sp.
     stack_err_lab IN elabs /\ stack_good_code_labels prog elabs
     ==> stack_good_code_labels (MAP (stack_remove_prog_comp jump offset sp) prog) elabs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `offset:A word#A word`; `sp:num`; `prog:(num#(A)stack_prog)list`]
          S2LP2AUX_remove_pc) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_code_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN
  EXISTS_TAC `{(stack_err_lab,0)}` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_UNION; IN_IMAGE; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* ---- stack_alloc ---- *)

(* rewrite the other assumptions with the assumptions e = (x,y) that       *)
(* EVERY_CASE_TAC leaves for the lets of stack_alloc_comp                   *)
let s2lp2aux_subst_pairs : tactic = fun (asl,w as g) ->
  let eqs = filter (fun th -> let c = concl th in
                     is_eq c && is_pair (rhs c) && not (is_var (lhs c)))
                   (map snd asl) in
  let cs = map concl eqs in
  RULE_ASSUM_TAC(fun th -> if mem (concl th) cs then th
                           else REWRITE_RULE (FST :: SND :: eqs) th) g;;

let S2LP2AUX_alloc_clauses =
  s2lp2aux_comp_clauses `stack_alloc_comp s2lpn s2lpm:(A)stack_prog->(A)stack_prog#num`
    stack_alloc_comp_def;;

(* HOL4 line 4343 [local] (HOL4's unused binders pp and mm are left out) *)
let stack_alloc_get_code_labels_comp = prove
 (`!n m (p:(A)stack_prog).
     stack_get_code_labels (FST (stack_alloc_comp n m p)) SUBSET
     (gc_stub_location,0) INSERT stack_get_code_labels p`,
  MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_alloc_clauses] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  s2lp2aux_subst_pairs THEN RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  s2lp2aux_subst_pairs THEN
  SIMP[stack_get_code_labels_def; UNION_EMPTY; EMPTY_SUBSET] THEN
  ASM SET_TAC[]);;

(* HOL4 line 4355 [local] (HOL4's unused binders pp and mm are left out; i  *)
(* is free) *)
let stack_alloc_stack_get_handler_labels_comp = prove
 (`!n m (p:(A)stack_prog) i.
     stack_get_handler_labels i (FST (stack_alloc_comp n m p)) = stack_get_handler_labels i p`,
  MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_alloc_clauses] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  s2lp2aux_subst_pairs THEN RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  s2lp2aux_subst_pairs THEN
  SIMP[stack_get_handler_labels_def; UNION_EMPTY]);;

(* HOL4 line 4367 [local] *)
let stack_alloc_init_code_labels = prove
 (`!c. stack_get_code_labels (word_gc_code c:(A)stack_prog) = {}`,
  GEN_TAC THEN REWRITE_TAC[word_gc_code_def] THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC s2lp2aux_gc_code_defs THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[stack_list_Seq_def; APPEND; LET_DEF; LET_END_DEF;
                                      stack_get_code_labels_def; UNION_EMPTY])) THEN
  EVERY_CASE_TAC THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[stack_list_Seq_def; APPEND; LET_DEF; LET_END_DEF;
                                      stack_get_code_labels_def; UNION_EMPTY])));;

let S2LP2AUX_alloc_pc = prove
 (`!(prog:(num#(A)stack_prog)list).
     MAP FST (MAP stack_alloc_prog_comp prog) = MAP FST prog /\
     MAP (\(n,pp). stack_get_handler_labels n pp) (MAP stack_alloc_prog_comp prog) =
     MAP (\(n,pp). stack_get_handler_labels n pp) prog /\
     UNIONS (IMAGE stack_get_code_labels
               (set_of_list (MAP SND (MAP stack_alloc_prog_comp prog))))
     SUBSET {(gc_stub_location,0)} UNION
            UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog)))`,
  MP_TAC(ISPECL [`stack_alloc_prog_comp:num#(A)stack_prog->num#(A)stack_prog`;
                 `\(n:num) (p:(A)stack_prog). FST (stack_alloc_comp n (next_lab p 2) p)`;
                 `{(gc_stub_location,0)}`] S2LP2AUX_MAP_pc) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[stack_alloc_prog_comp_def; stack_alloc_stack_get_handler_labels_comp;
               INSERT_UNION_EQ; UNION_EMPTY; stack_alloc_get_code_labels_comp];
   REWRITE_TAC[]]);;

(* HOL4 line 4376 *)
let stack_alloc_stack_good_code_labels = prove
 (`!(prog:(num#(A)stack_prog)list) c elabs.
     stack_good_code_labels prog elabs
     ==> stack_good_code_labels (stack_alloc_compile c prog) elabs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `prog:(num#(A)stack_prog)list` S2LP2AUX_alloc_pc) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_code_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN
  EXISTS_TAC `{(gc_stub_location,0)}` THEN
  ASM_REWRITE_TAC[stack_alloc_compile_def; MAP_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
                  UNIONS_UNION; stack_alloc_stubs_def; MAP; set_of_list; IMAGE_CLAUSES;
                  UNIONS_0; UNIONS_INSERT] THEN
  SIMP[stack_get_code_labels_def; stack_alloc_init_code_labels; UNION_EMPTY] THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_UNION; IN_IMAGE; IN_INSERT; PAIR_EQ] THEN
   MESON_TAC[];
   SET_TAC[];
   SET_TAC[]]);;

(* HOL4 line 4403 *)
let stack_alloc_stack_good_code_labels_incr = prove
 (`!(prog:(num#(A)stack_prog)list) elabs.
     gc_stub_location IN elabs /\ stack_good_code_labels prog elabs
     ==> stack_good_code_labels (MAP stack_alloc_prog_comp prog) elabs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `prog:(num#(A)stack_prog)list` S2LP2AUX_alloc_pc) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_code_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN
  EXISTS_TAC `{(gc_stub_location,0)}` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_UNION; IN_IMAGE; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* the code labels that stack_rawcall adds are (l,1) for a label (l,0) *)
(* with l in the domain of the stack allocation information            *)
let S2LP2AUX_comp_seq_labels = prove
 (`!p1 p2 i (d:(A)stack_prog) p_1 p_2.
     (p_1,p_2) IN stack_get_code_labels (comp_seq p1 p2 i d)
     ==> (p_1,p_2) IN stack_get_code_labels d \/
         (p_2 = 1 /\ (p_1,0) IN stack_get_code_labels (stack_Seq p1 p2) /\ p_1 IN domain i)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `comp_seq p1 p2 i (d:(A)stack_prog) = d` THENL
  [ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP comp_seq_neq_IMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `dest:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `~(comp_seq p1 p2 i (d:(A)stack_prog) = d)` THEN
  ASM_REWRITE_TAC[comp_seq_def; dest_case_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup dest (i:num spt)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN
  SIMP[stack_get_code_labels_def; IN_UNION; NOT_IN_EMPTY; IN_SING; PAIR_EQ; domain_lookup] THEN
  ASM_MESON_TAC[]);;

let S2LP2AUX_rawcall_code_labels = prove
 (`!i (q:(A)stack_prog).
     (!p_1 p_2. (p_1,p_2) IN stack_get_code_labels (stack_rawcall_comp i q)
                ==> (p_1,p_2) IN stack_get_code_labels q \/
                    (p_2 = 1 /\ (p_1,0) IN stack_get_code_labels q /\ p_1 IN domain i)) /\
     (!p_1 p_2. (p_1,p_2) IN stack_get_code_labels (comp_top i q)
                ==> (p_1,p_2) IN stack_get_code_labels q \/
                    (p_2 = 1 /\ (p_1,0) IN stack_get_code_labels q /\ p_1 IN domain i))`,
  let is_cs t = try fst(dest_const t) = "comp_seq" with Failure _ -> false in
  let seq_tac : tactic = fun (asl,w as g) ->
    if not (can (find_term is_cs) w) then failwith "seq_tac" else
    (REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
     SUBGOAL_THEN
      `!p_1 p_2.
         (p_1,p_2) IN stack_get_code_labels
            (stack_Seq (stack_rawcall_comp i a0) (stack_rawcall_comp i (a1:(A)stack_prog)))
         ==> (p_1,p_2) IN stack_get_code_labels (stack_Seq a0 a1) \/
             (p_2 = 1 /\ (p_1,0) IN stack_get_code_labels (stack_Seq a0 a1) /\ p_1 IN domain i)`
      ASSUME_TAC THENL
     [REWRITE_TAC[stack_get_code_labels_def; IN_UNION] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP S2LP2AUX_comp_seq_labels) THEN
      ASM_MESON_TAC[]]) g in
  MATCH_MP_TAC stack_rawcall_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN
  FIRST
   [seq_tac;
    EVERY_CASE_TAC THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    SIMP[stack_get_code_labels_def; IN_UNION; NOT_IN_EMPTY; IN_SING; PAIR_EQ] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 4418 *)
let IN_get_code_labels_comp_top_lemma = prove
 (`!i (q:(A)stack_prog) p_1 p_2.
     ((p_1,p_2) IN stack_get_code_labels (stack_rawcall_comp i q)
      ==> ?k. (p_1,k) IN stack_get_code_labels q /\
              (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain i)) /\
     ((p_1,p_2) IN stack_get_code_labels (comp_top i q)
      ==> ?k. (p_1,k) IN stack_get_code_labels q /\
              (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ p_1 IN domain i))`,
  MESON_TAC[S2LP2AUX_rawcall_code_labels]);;

(* HOL4 line 4454 *)
let IN_domain_collect_info = prove
 (`!(prog:(num#(A)stack_prog)list) f p_1.
     p_1 IN domain (collect_info prog f) ==> MEM p_1 (MAP FST prog) \/ p_1 IN domain f`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[collect_info_def; MAP; MEM] THEN
  SUBST1_TAC(ISPEC `h:num#(A)stack_prog` (GSYM PAIR)) THEN
  REWRITE_TAC[collect_info_def; FST] THEN
  SPEC_TAC(`seq_stack_alloc (SND (h:num#(A)stack_prog))`,`oo:num option`) THEN
  GEN_TAC THEN CASES_ON `oo:num option` THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[domain_insert; IN_INSERT]);;

(* HOL4 line 4464 (prog and q are of any two types, as in HOL4) *)
let IN_get_code_labels_comp_top = prove
 (`!p_1 p_2 (prog:(num#(A)stack_prog)list) (q:(B)stack_prog).
     (p_1,p_2) IN stack_get_code_labels (comp_top (collect_info prog LN) q)
     ==> ?k. (p_1,k) IN stack_get_code_labels q /\
             (~(p_2 = k) ==> p_2 = 1 /\ k = 0 /\ MEM p_1 (MAP FST prog))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`collect_info (prog:(num#(A)stack_prog)list) LN`; `q:(B)stack_prog`;
                 `p_1:num`; `p_2:num`] IN_get_code_labels_comp_top_lemma) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[IN_domain_collect_info; domain_def; NOT_IN_EMPTY]);;

let S2LP2AUX_rawcall_pc = prove
 (`!(prog:(num#(A)stack_prog)list).
     MAP FST (stack_rawcall_compile prog) = MAP FST prog /\
     MAP (\(n,pp). stack_get_handler_labels n pp) (stack_rawcall_compile prog) =
     MAP (\(n,pp). stack_get_handler_labels n pp) prog /\
     UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND (stack_rawcall_compile prog))))
     SUBSET IMAGE (\n. n,1) (set_of_list (MAP FST prog)) UNION
            UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog)))`,
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`\(n:num,b:(A)stack_prog). (n,comp_top (collect_info (prog:(num#(A)stack_prog)list) LN) b)`;
    `\(n:num) (b:(A)stack_prog). comp_top (collect_info (prog:(num#(A)stack_prog)list) LN) b`;
    `IMAGE (\n:num. n,1) (set_of_list (MAP FST (prog:(num#(A)stack_prog)list)))`]
   S2LP2AUX_MAP_pc) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[stack_get_handler_labels_comp] THEN
   REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_UNION; IN_IMAGE; IN_SET_OF_LIST; PAIR_EQ] THEN
   MESON_TAC[IN_get_code_labels_comp_top];
   ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `prog:(num#(A)stack_prog)list`) THEN
  REWRITE_TAC[stack_rawcall_compile_def; LET_DEF; LET_END_DEF]);;

(* HOL4 line 4476 *)
let stack_rawcall_stack_good_code_labels = prove
 (`!(prog:(num#(A)stack_prog)list) elabs.
     stack_good_code_labels prog elabs
     ==> stack_good_code_labels (stack_rawcall_compile prog) elabs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `prog:(num#(A)stack_prog)list` S2LP2AUX_rawcall_pc) THEN STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_code_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN
  EXISTS_TAC `IMAGE (\n:num. n,1) (set_of_list (MAP FST (prog:(num#(A)stack_prog)list)))` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  SET_TAC[]);;

(* HOL4 line 4493 *)
let stack_to_lab_stack_good_code_labels = prove
 (`!stack_conf data_conf max_heap sp offset (prog:(num#(A)stack_prog)list) prog' elabs.
     stack_to_lab_compile stack_conf data_conf max_heap sp offset prog = prog' /\
     MEM InitGlobals_location (MAP FST prog) /\
     stack_good_code_labels prog elabs /\
     ALL sec_labels_ok prog'
     ==> lab_get_labels prog' SUBSET
         (lab_get_code_labels prog' UNION IMAGE (\n. (n,0)) elabs) UNION IMAGE (\n. (n,1)) elabs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC get_labels_MAP_prog_to_section_SUBSET_code_labels THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC stack_names_stack_good_code_labels THEN
  MATCH_MP_TAC stack_remove_stack_good_code_labels THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[stack_alloc_compile_def; MAP_APPEND; MEM_APPEND;
                   S2LP2AUX_MAP_FST_alloc_prog_comp; stack_rawcallProof_MAP_FST_compile];
   MATCH_MP_TAC stack_alloc_stack_good_code_labels THEN
   MATCH_MP_TAC stack_rawcall_stack_good_code_labels THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 4518 *)
let stack_to_lab_stack_good_code_labels_incr = prove
 (`!elabs f jump offset sp (prog:(num#(A)stack_prog)list) prog'.
     stack_err_lab IN elabs /\
     gc_stub_location IN elabs /\
     compile_no_stubs f jump offset sp prog = prog' /\
     stack_good_code_labels prog elabs /\
     ALL sec_labels_ok prog'
     ==> lab_get_labels prog' SUBSET
         (lab_get_code_labels prog' UNION IMAGE (\n. (n,0)) elabs) UNION IMAGE (\n. (n,1)) elabs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[compile_no_stubs_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC get_labels_MAP_prog_to_section_SUBSET_code_labels THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC stack_names_stack_good_code_labels THEN
  MATCH_MP_TAC stack_remove_stack_good_code_labels_incr THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC stack_alloc_stack_good_code_labels_incr THEN
  ASM_REWRITE_TAC[]);;

(* nonzero restricted code labels *)

let S2LP2AUX_set_lemma7 = prove
 (`!(GL:num#num->bool) CL SL H F1.
     GL SUBSET CL UNION SL /\ restrict_nonzero SL SUBSET H UNION F1 /\
     H SUBSET CL /\ F1 SUBSET CL
     ==> restrict_nonzero GL SUBSET CL`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* HOL4 line 4537 *)
let nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels = prove
 (`!(p:(num#(A)stack_prog)list).
     ALL sec_labels_ok (MAP prog_to_section p) /\ stack_good_handler_labels p
     ==> restrict_nonzero (lab_get_labels (MAP prog_to_section p)) SUBSET
         lab_get_code_labels (MAP prog_to_section p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_good_handler_labels_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_set_lemma7 THEN
  EXISTS_TAC `UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND (p:(num#(A)stack_prog)list))))` THEN
  EXISTS_TAC `UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp)
                                      (p:(num#(A)stack_prog)list)))` THEN
  EXISTS_TAC `IMAGE (\n. n,1) (set_of_list (MAP FST (p:(num#(A)stack_prog)list)))` THEN
  ASM_SIMP_TAC[get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma;
               MAP_prog_to_section_preserves_handler_labels; one_prog_section]);;

(* generic transfer of stack_good_handler_labels through a pass *)

let S2LP2AUX_set_lemma6 = prove
 (`!(C:num#num->bool) C' Y H H' F1 F1'.
     restrict_nonzero C SUBSET H UNION F1 /\ C' SUBSET Y UNION C /\
     restrict_nonzero Y SUBSET F1' /\ F1 SUBSET F1' /\ H SUBSET H'
     ==> restrict_nonzero C' SUBSET H' UNION F1'`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

let S2LP2AUX_good_handler_labels_mono = prove
 (`!(prog:(num#(A)stack_prog)list) (prog':(num#(A)stack_prog)list) Y.
     stack_good_handler_labels prog /\
     UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog'))) SUBSET
       Y UNION UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog))) /\
     restrict_nonzero Y SUBSET IMAGE (\n. n,1) (set_of_list (MAP FST prog')) /\
     set_of_list (MAP FST prog) SUBSET set_of_list (MAP FST prog') /\
     UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) prog)) SUBSET
       UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) prog'))
     ==> stack_good_handler_labels prog'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_good_handler_labels_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_set_lemma6 THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND (prog:(num#(A)stack_prog)list))))`;
    `Y:num#num->bool`;
    `UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp)
                               (prog:(num#(A)stack_prog)list)))`;
    `IMAGE (\n:num. n,1) (set_of_list (MAP FST (prog:(num#(A)stack_prog)list)))`] THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let S2LP2AUX_restrict_nonzero_zero = prove
 (`!s t. (!x:num#num. x IN s ==> SND x = 0) ==> restrict_nonzero s SUBSET t`,
  REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let S2LP2AUX_names_pc = prove
 (`!f (prog:(num#(A)stack_prog)list).
     MAP FST (stack_names_compile f prog) = MAP FST prog /\
     MAP (\(n,pp). stack_get_handler_labels n pp) (stack_names_compile f prog) =
     MAP (\(n,pp). stack_get_handler_labels n pp) prog /\
     UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND (stack_names_compile f prog))))
     SUBSET {} UNION UNIONS (IMAGE stack_get_code_labels (set_of_list (MAP SND prog)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`stack_names_prog_comp f:num#(A)stack_prog->num#(A)stack_prog`;
                 `\(n:num) (p:(A)stack_prog). stack_names_comp f p`;
                 `{}:num#num->bool`] S2LP2AUX_MAP_pc) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[stack_names_prog_comp_def; stack_names_stack_get_handler_labels_comp;
               stack_names_get_code_labels_comp; UNION_EMPTY; SUBSET_REFL];
   DISCH_THEN(MP_TAC o SPEC `prog:(num#(A)stack_prog)list`) THEN
   REWRITE_TAC[stack_names_compile_def]]);;

(* HOL4 line 4560 *)
let stack_names_stack_good_handler_labels = prove
 (`!(prog:(num#(A)stack_prog)list) f.
     stack_good_handler_labels prog ==> stack_good_handler_labels (stack_names_compile f prog)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num spt`; `prog:(num#(A)stack_prog)list`] S2LP2AUX_names_pc) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_handler_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN EXISTS_TAC `{}:num#num->bool` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC S2LP2AUX_restrict_nonzero_zero THEN REWRITE_TAC[NOT_IN_EMPTY]);;

(* HOL4 line 4571 *)
let restrict_nonzero_union = prove
 (`!A B. restrict_nonzero (A UNION B) = restrict_nonzero A UNION restrict_nonzero B`,
  REWRITE_TAC[restrict_nonzero_def; EXTENSION; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* HOL4 line 4578 *)
let restrict_nonzero_IN = prove
 (`!x s. x IN restrict_nonzero s <=> x IN s /\ ~(SND x = 0)`,
  REWRITE_TAC[restrict_nonzero_def; IN_ELIM_THM]);;

(* HOL4 line 4584 *)
let stack_good_handler_labels_append = prove
 (`!(xs:(num#(A)stack_prog)list) ys.
     stack_good_handler_labels xs /\ stack_good_handler_labels ys
     ==> stack_good_handler_labels (APPEND xs ys)`,
  REWRITE_TAC[stack_good_handler_labels_def; MAP_APPEND; SET_OF_LIST_APPEND; IMAGE_UNION;
              UNIONS_UNION; restrict_nonzero_union] THEN
  SET_TAC[]);;

(* HOL4 line 4595 *)
let stack_remove_stack_good_handler_labels_incr = prove
 (`!(prog:(num#(A)stack_prog)list) jump offset sp.
     stack_good_handler_labels prog
     ==> stack_good_handler_labels (MAP (stack_remove_prog_comp jump offset sp) prog)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`jump:bool`; `offset:A word#A word`; `sp:num`; `prog:(num#(A)stack_prog)list`]
          S2LP2AUX_remove_pc) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_handler_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN EXISTS_TAC `{(stack_err_lab,0)}` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC S2LP2AUX_restrict_nonzero_zero THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

(* HOL4 line 4623 *)
let stack_remove_stack_good_handler_labels = prove
 (`!(prog:(num#(A)stack_prog)list) jump off ggc mh sp loc.
     stack_good_handler_labels prog
     ==> stack_good_handler_labels (stack_remove_compile jump off ggc mh sp loc prog)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_remove_compile_def] THEN
  MATCH_MP_TAC stack_good_handler_labels_append THEN
  ASM_SIMP_TAC[stack_remove_stack_good_handler_labels_incr] THEN
  REWRITE_TAC[stack_good_handler_labels_def] THEN
  MATCH_MP_TAC S2LP2AUX_restrict_nonzero_zero THEN
  MP_TAC(ISPECL [`ggc:bool`; `mh:num`; `sp:num`; `loc:num`] S2LP2AUX_init_stubs_code_labels) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[SND]);;

(* HOL4 line 4648 *)
let stack_alloc_stack_good_handler_labels_incr = prove
 (`!(prog:(num#(A)stack_prog)list).
     stack_good_handler_labels prog
     ==> stack_good_handler_labels (MAP stack_alloc_prog_comp prog)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `prog:(num#(A)stack_prog)list` S2LP2AUX_alloc_pc) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_handler_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN EXISTS_TAC `{(gc_stub_location,0)}` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC S2LP2AUX_restrict_nonzero_zero THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

(* HOL4 line 4666 *)
let stack_alloc_stack_good_handler_labels = prove
 (`!(prog:(num#(A)stack_prog)list) c.
     stack_good_handler_labels prog ==> stack_good_handler_labels (stack_alloc_compile c prog)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stack_alloc_compile_def] THEN
  MATCH_MP_TAC stack_good_handler_labels_append THEN
  ASM_SIMP_TAC[stack_alloc_stack_good_handler_labels_incr] THEN
  REWRITE_TAC[stack_good_handler_labels_def] THEN
  MATCH_MP_TAC S2LP2AUX_restrict_nonzero_zero THEN
  REWRITE_TAC[stack_alloc_stubs_def; MAP; set_of_list; IMAGE_CLAUSES; UNIONS_0;
              UNIONS_INSERT] THEN
  SIMP[stack_get_code_labels_def; stack_alloc_init_code_labels; UNION_EMPTY; NOT_IN_EMPTY]);;

(* HOL4 line 4682 *)
let stack_rawcall_stack_good_handler_labels = prove
 (`!(prog:(num#(A)stack_prog)list).
     stack_good_handler_labels prog ==> stack_good_handler_labels (stack_rawcall_compile prog)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `prog:(num#(A)stack_prog)list` S2LP2AUX_rawcall_pc) THEN STRIP_TAC THEN
  MATCH_MP_TAC S2LP2AUX_good_handler_labels_mono THEN
  EXISTS_TAC `prog:(num#(A)stack_prog)list` THEN
  EXISTS_TAC `IMAGE (\n:num. n,1) (set_of_list (MAP FST (prog:(num#(A)stack_prog)list)))` THEN
  ASM_REWRITE_TAC[SUBSET_REFL; restrict_nonzero_SUBSET]);;

(* HOL4 line 4699 *)
let stack_to_lab_stack_good_handler_labels = prove
 (`!stack_conf data_conf max_heap sp offset (prog:(num#(A)stack_prog)list) prog'.
     stack_to_lab_compile stack_conf data_conf max_heap sp offset prog = prog' /\
     stack_good_handler_labels prog /\
     ALL sec_labels_ok prog'
     ==> restrict_nonzero (lab_get_labels prog') SUBSET lab_get_code_labels prog'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC stack_names_stack_good_handler_labels THEN
  MATCH_MP_TAC stack_remove_stack_good_handler_labels THEN
  MATCH_MP_TAC stack_alloc_stack_good_handler_labels THEN
  MATCH_MP_TAC stack_rawcall_stack_good_handler_labels THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 4715 *)
let stack_to_lab_stack_good_handler_labels_incr = prove
 (`!f jump offset sp (prog:(num#(A)stack_prog)list) prog'.
     compile_no_stubs f jump offset sp prog = prog' /\
     stack_good_handler_labels prog /\
     ALL sec_labels_ok prog'
     ==> restrict_nonzero (lab_get_labels prog') SUBSET lab_get_code_labels prog'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[compile_no_stubs_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC stack_names_stack_good_handler_labels THEN
  MATCH_MP_TAC stack_remove_stack_good_handler_labels_incr THEN
  MATCH_MP_TAC stack_alloc_stack_good_handler_labels_incr THEN
  ASM_REWRITE_TAC[]);;

(* helpers for the no_shmemop and no_install lemmas *)

let S2LP2AUX_ALL_SND = prove
 (`!(P:B->bool) (l:(A#B)list). ALL (\(a,p). P p) l <=> ALL P (MAP SND l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN
  SUBST1_TAC(ISPEC `h:A#B` (GSYM PAIR)) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[SND]);;

let S2LP2AUX_ALL_MAP_pc = prove
 (`!(P:(A)stack_prog->bool) (pc:num#(A)stack_prog->num#(A)stack_prog) prog.
     (!n p. P p ==> P (SND (pc (n,p)))) /\ ALL (\(a,p). P p) prog
     ==> ALL (\(a,p). P p) (MAP pc prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP2AUX_ALL_SND] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`prog:(num#(A)stack_prog)list`,`prog:(num#(A)stack_prog)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`FST (h:num#(A)stack_prog)`; `SND (h:num#(A)stack_prog)`]) THEN
  ASM_REWRITE_TAC[PAIR]);;

let S2LP2AUX_comp_seq_preds = prove
 (`!p1 p2 i (d:(A)stack_prog).
     (no_shmemop d ==> no_shmemop (comp_seq p1 p2 i d)) /\
     (stack_no_install d ==> stack_no_install (comp_seq p1 p2 i d))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `comp_seq p1 p2 i (d:(A)stack_prog) = d` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP comp_seq_neq_IMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `dest:num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[comp_seq_def; dest_case_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup dest (i:num spt)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN SIMP[no_shmemop_def; stack_no_install_def]);;

let S2LP2AUX_single_preds = prove
 (`(!jump k n. no_shmemop (single_stack_alloc jump k n:(A)stack_prog) /\
               stack_no_install (single_stack_alloc jump k n:(A)stack_prog)) /\
   (!k n. no_shmemop (single_stack_free k n:(A)stack_prog) /\
          stack_no_install (single_stack_free k n:(A)stack_prog))`,
  REWRITE_TAC[single_stack_alloc_def; single_stack_free_def; halt_inst_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY COND_CASES_TAC THEN
  SIMP[no_shmemop_def; stack_no_install_def]);;

let S2LP2AUX_store_list_code_preds = prove
 (`!a t (xs:(A word+num)list).
     no_shmemop (store_list_code a t xs:(A)stack_prog) /\
     stack_no_install (store_list_code a t xs:(A)stack_prog)`,
  MATCH_MP_TAC store_list_code_ind THEN REPEAT STRIP_TAC THEN
  SIMP[store_list_code_def; stack_list_Seq_def; no_shmemop_def; stack_no_install_def]);;

let S2LP2AUX_init_code_preds = prove
 (`!ggc mh k.
     no_shmemop (stack_remove_init_code ggc mh k:(A)stack_prog) /\
     stack_no_install (stack_remove_init_code ggc mh k:(A)stack_prog)`,
  REWRITE_TAC[stack_remove_init_code_def; LET_DEF; LET_END_DEF; stack_list_Seq_def;
              init_memory_def] THEN
  SIMP[no_shmemop_def; stack_no_install_def; S2LP2AUX_store_list_code_preds]);;

let S2LP2AUX_word_gc_code_preds = prove
 (`!c. no_shmemop (word_gc_code c:(A)stack_prog) /\
       stack_no_install (word_gc_code c:(A)stack_prog)`,
  GEN_TAC THEN REWRITE_TAC[word_gc_code_def] THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC s2lp2aux_gc_code_defs THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[stack_list_Seq_def; APPEND; LET_DEF; LET_END_DEF;
                                      no_shmemop_def; stack_no_install_def])) THEN
  EVERY_CASE_TAC THEN
  REPEAT(CHANGED_TAC(CASE_REWRITE_TAC[stack_list_Seq_def; APPEND; LET_DEF; LET_END_DEF;
                                      no_shmemop_def; stack_no_install_def])));;

(* the proofs of the syntactic preservation lemmas of each pass *)

let s2lp2aux_rc_pred_tac (def:thm) : tactic =
  MATCH_MP_TAC stack_rawcall_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REWRITE_TAC[STACKPROPSAUX_rc_comp_thms] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE STACKPROPSAUX_RC_IH_RWS) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  SIMP[def; S2LP2AUX_comp_seq_preds];;

let s2lp2aux_alloc_pred_tac (def:thm) : tactic =
  MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_alloc_clauses] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  s2lp2aux_subst_pairs THEN RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  s2lp2aux_subst_pairs THEN
  SIMP[def];;

let s2lp2aux_remove_pred_tac (def:thm) (aux:thm list) : tactic =
  MATCH_MP_TAC stack_remove_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_remove_clauses; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  SIMP([def; stack_store_def; stack_load_def; copy_loop_def; copy_each_def;
        stack_list_Seq_def] @ aux);;

let s2lp2aux_names_pred_tac (def:thm) : tactic =
  MATCH_MP_TAC stack_names_comp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  REWRITE_TAC[S2LP2AUX_names_clauses] THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE s2lp2aux_ih_rws) THEN
  SIMP[def];;

(*** no_shmemop ***)

(* HOL4 line 4732 *)
let stack_rawcall_comp_no_shmemop = prove
 (`!i (p:(A)stack_prog). no_shmemop p ==> no_shmemop (stack_rawcall_comp i p)`,
  s2lp2aux_rc_pred_tac no_shmemop_def);;

(* HOL4 line 4744 (i is free in HOL4) *)
let stack_rawcall_comp_top_no_shmemop = prove
 (`!(p:(A)stack_prog) i. no_shmemop p ==> no_shmemop (comp_top i p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[comp_top_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  SIMP[no_shmemop_def; stack_rawcall_comp_no_shmemop]);;

(* HOL4 line 4752 *)
let stack_rawcall_compile_no_shmemop = prove
 (`!(prog:(num#(A)stack_prog)list).
     ALL (\(a,p). no_shmemop p) prog ==> ALL (\(a,p). no_shmemop p) (stack_rawcall_compile prog)`,
  GEN_TAC THEN REWRITE_TAC[stack_rawcall_compile_def; LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[SND] THEN MESON_TAC[stack_rawcall_comp_top_no_shmemop]);;

(* HOL4 line 4771 *)
let stack_alloc_comp_no_shmemop = prove
 (`!n m (p:(A)stack_prog). no_shmemop p ==> no_shmemop (FST (stack_alloc_comp n m p))`,
  s2lp2aux_alloc_pred_tac no_shmemop_def);;

(* HOL4 line 4782 *)
let stack_alloc_prog_comp_no_shmemop = prove
 (`!(prog:(num#(A)stack_prog)list).
     ALL (\(a,p). no_shmemop p) prog
     ==> ALL (\(a,p). no_shmemop p) (MAP stack_alloc_prog_comp prog)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN
  ASM_REWRITE_TAC[stack_alloc_prog_comp_def; SND] THEN
  MESON_TAC[stack_alloc_comp_no_shmemop]);;

(* HOL4 line 4793 *)
let stack_alloc_compile_no_shmemop = prove
 (`!(prog:(num#(A)stack_prog)list) data.
     ALL (\(a,p). no_shmemop p) prog
     ==> ALL (\(a,p). no_shmemop p) (stack_alloc_compile data prog)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[stack_alloc_compile_def; ALL_APPEND; stack_alloc_stubs_def; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_SIMP_TAC[stack_alloc_prog_comp_no_shmemop] THEN
  SIMP[no_shmemop_def; S2LP2AUX_word_gc_code_preds]);;

(* HOL4 line 4802 [simp] *)
let upshift_no_shmemop = prove
 (`!k n. no_shmemop (upshift k n:(A)stack_prog)`,
  MATCH_MP_TAC upshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[upshift_def] THEN COND_CASES_TAC THEN SIMP[no_shmemop_def]);;

let _ = cake_add_simps [upshift_no_shmemop];;

(* HOL4 line 4810 [simp] *)
let downshift_no_shmemop = prove
 (`!k n. no_shmemop (downshift k n:(A)stack_prog)`,
  MATCH_MP_TAC downshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[downshift_def] THEN COND_CASES_TAC THEN SIMP[no_shmemop_def]);;

let _ = cake_add_simps [downshift_no_shmemop];;

(* HOL4 line 4818 [simp] (stack_remove's stack_free) *)
let stack_free_no_shmemop = prove
 (`!k n. no_shmemop (stack_remove_stack_free k n:(A)stack_prog)`,
  MATCH_MP_TAC stack_remove_stack_free_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
  REPEAT COND_CASES_TAC THEN SIMP[no_shmemop_def; S2LP2AUX_single_preds]);;

let _ = cake_add_simps [stack_free_no_shmemop];;

(* HOL4 line 4826 [simp] (stack_remove's stack_alloc) *)
let stack_alloc_no_shmemop = prove
 (`!jump k n. no_shmemop (stack_alloc jump k n:(A)stack_prog)`,
  MATCH_MP_TAC stack_alloc_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_def] THEN
  REPEAT COND_CASES_TAC THEN SIMP[no_shmemop_def; S2LP2AUX_single_preds]);;

let _ = cake_add_simps [stack_alloc_no_shmemop];;

(* HOL4 line 4835 *)
let stack_remove_comp_no_shmemop = prove
 (`!jump off k (p:(A)stack_prog). no_shmemop p ==> no_shmemop (stack_remove_comp jump off k p)`,
  s2lp2aux_remove_pred_tac no_shmemop_def
    [upshift_no_shmemop; downshift_no_shmemop; stack_free_no_shmemop;
     stack_alloc_no_shmemop]);;

(* HOL4 line 4851 (jump, off, k and n are free in HOL4) *)
let stack_remove_prog_comp_no_shmemop = prove
 (`!(p:(A)stack_prog) jump off k n.
     no_shmemop p ==> no_shmemop (SND (stack_remove_prog_comp jump off k (n,p)))`,
  REWRITE_TAC[stack_remove_prog_comp_def; SND] THEN
  MESON_TAC[stack_remove_comp_no_shmemop]);;

(* HOL4 line 4858 *)
let stack_remove_compile_no_shmemop = prove
 (`!(prog:(num#(A)stack_prog)list) jump offset gckind mh sp loc.
     ALL (\(a,p). no_shmemop p) prog
     ==> ALL (\(a,p). no_shmemop p) (stack_remove_compile jump offset gckind mh sp loc prog)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[stack_remove_compile_def; ALL_APPEND; stack_remove_init_stubs_def; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL
  [SIMP[no_shmemop_def; halt_inst_def; S2LP2AUX_init_code_preds];
   MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN
   ASM_REWRITE_TAC[stack_remove_prog_comp_no_shmemop]]);;

(* HOL4 line 4874 *)
let stack_names_comp_no_shmemop = prove
 (`!f (p:(A)stack_prog). no_shmemop p ==> no_shmemop (stack_names_comp f p)`,
  s2lp2aux_names_pred_tac no_shmemop_def);;

(* HOL4 line 4885 (f is free in HOL4) *)
let stack_names_prog_comp_no_shmemop = prove
 (`!(prog:(num#(A)stack_prog)list) f.
     ALL (\(a,p). no_shmemop p) prog
     ==> ALL (\(a,p). no_shmemop p) (MAP (stack_names_prog_comp f) prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN
  ASM_REWRITE_TAC[stack_names_prog_comp_def; SND] THEN
  MESON_TAC[stack_names_comp_no_shmemop]);;

(* HOL4 line 4896 *)
let stack_names_compile_no_shmemop = prove
 (`!(prog:(num#(A)stack_prog)list) names.
     ALL (\(a,p). no_shmemop p) prog
     ==> ALL (\(a,p). no_shmemop p) (stack_names_compile names prog)`,
  REWRITE_TAC[stack_names_compile_def; stack_names_prog_comp_no_shmemop]);;

(* HOL4 line 4904 *)
let flatten_no_share_mem_inst = prove
 (`!t (p:(A)stack_prog) n m cs bs.
     no_shmemop p
     ==> ALL (\ln. !op re a inst len. ~(ln = Asm (ShareMem op re a) inst len))
           (append (FST (stack_to_lab_flatten t p n m cs bs)))`,
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL
    [`\ln:(A)line. !op re a inst len. ~(ln = Asm (ShareMem op re a) inst len)`;
     `no_shmemop:(A)stack_prog->bool`] S2LP2AUX_flatten_ALL)) THEN
  REWRITE_TAC[no_shmemop_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "line"; injectivity "line"; distinctness "asm_or_cbw"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY(CASES_ON `dest:num+num`) THEN
  CASE_REWRITE_TAC[compile_jump_def; distinctness "line"; injectivity "line";
                   distinctness "asm_or_cbw"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4919 *)
let asm_fetch_aux_no_share_mem_inst_CONS = prove
 (`!(xs:((A)line)list) ls k.
     ALL (\ln. !op re a inst len. ~(ln = Asm (ShareMem op re a) inst len)) xs /\
     no_share_mem_inst ls
     ==> no_share_mem_inst (CONS (Section k xs) ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; no_share_mem_inst_def; asm_fetch_aux_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[no_share_mem_inst_def]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ls:((A)sec)list`; `k:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ]);;

(* HOL4 line 4930 *)
let prog_to_section_no_share_mem_inst = prove
 (`!(prog:(num#(A)stack_prog)list).
     ALL (\(a,p). no_shmemop p) prog ==> no_share_mem_inst (MAP prog_to_section prog)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THENL
  [REWRITE_TAC[no_share_mem_inst_def; asm_fetch_aux_def; option_DISTINCT];
   SUBST1_TAC(ISPEC `h:num#(A)stack_prog` (GSYM PAIR)) THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   STRIP_TAC THEN REWRITE_TAC[S2LP2AUX_prog_to_section_eq] THEN
   MATCH_MP_TAC asm_fetch_aux_no_share_mem_inst_CONS THEN
   ASM_SIMP_TAC[ALL_APPEND; ALL; flatten_no_share_mem_inst; distinctness "line"]]);;

(* HOL4 line 4947 *)
let compile_no_share_mem_inst = prove
 (`!(prog:(num#(A)stack_prog)list) prog' stack_conf data_conf max_heap sp offset.
     ALL (\(a,p). no_shmemop p) prog /\
     stack_to_lab_compile stack_conf data_conf max_heap sp offset prog = prog'
     ==> no_share_mem_inst prog'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC prog_to_section_no_share_mem_inst THEN
  MATCH_MP_TAC stack_names_compile_no_shmemop THEN
  MATCH_MP_TAC stack_remove_compile_no_shmemop THEN
  MATCH_MP_TAC stack_alloc_compile_no_shmemop THEN
  MATCH_MP_TAC stack_rawcall_compile_no_shmemop THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 4961 *)
let stack_remove_prog_comp_no_shmemop_MAP = prove
 (`!(prog:(num#(A)stack_prog)list) jump offset sp.
     ALL (\(a,p). no_shmemop p) prog
     ==> ALL (\(a,p). no_shmemop p) (MAP (stack_remove_prog_comp jump offset sp) prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN
  ASM_REWRITE_TAC[stack_remove_prog_comp_no_shmemop]);;

(* HOL4 line 4973 *)
let compile_no_stubs_no_share_mem_inst = prove
 (`!(prog:(num#(A)stack_prog)list) prog' f jump offset sp.
     ALL (\(a,p). no_shmemop p) prog /\
     compile_no_stubs f jump offset sp prog = prog'
     ==> no_share_mem_inst prog'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  REWRITE_TAC[compile_no_stubs_def] THEN
  MATCH_MP_TAC prog_to_section_no_share_mem_inst THEN
  MATCH_MP_TAC stack_names_compile_no_shmemop THEN
  MATCH_MP_TAC stack_remove_prog_comp_no_shmemop_MAP THEN
  MATCH_MP_TAC stack_alloc_prog_comp_no_shmemop THEN
  ASM_REWRITE_TAC[]);;

(*** no_install ***)

(* HOL4 line 4987 (no_install of stackLang programs is stackProps') *)
let stack_rawcall_comp_no_install = prove
 (`!i (p:(A)stack_prog). stack_no_install p ==> stack_no_install (stack_rawcall_comp i p)`,
  s2lp2aux_rc_pred_tac stack_no_install_def);;

(* HOL4 line 4999 *)
let stack_rawcall_comp_top_no_install = prove
 (`!(p:(A)stack_prog) i. stack_no_install p ==> stack_no_install (comp_top i p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[comp_top_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CASE_REWRITE_TAC[] THEN
  SIMP[stack_no_install_def; stack_rawcall_comp_no_install]);;

(* HOL4 line 5008 *)
let stack_rawcall_compile_no_install = prove
 (`!(prog:(num#(A)stack_prog)list).
     ALL (\(a,p). stack_no_install p) prog
     ==> ALL (\(a,p). stack_no_install p) (stack_rawcall_compile prog)`,
  GEN_TAC THEN REWRITE_TAC[stack_rawcall_compile_def; LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[SND] THEN MESON_TAC[stack_rawcall_comp_top_no_install]);;

(* HOL4 line 5027 *)
let stack_alloc_comp_no_install = prove
 (`!n m (p:(A)stack_prog).
     stack_no_install p ==> stack_no_install (FST (stack_alloc_comp n m p))`,
  s2lp2aux_alloc_pred_tac stack_no_install_def);;

(* HOL4 line 5038 *)
let stack_alloc_prog_comp_no_install = prove
 (`!(prog:(num#(A)stack_prog)list).
     ALL (\(a,p). stack_no_install p) prog
     ==> ALL (\(a,p). stack_no_install p) (MAP stack_alloc_prog_comp prog)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN
  ASM_REWRITE_TAC[stack_alloc_prog_comp_def; SND] THEN
  MESON_TAC[stack_alloc_comp_no_install]);;

(* HOL4 line 5049 *)
let stack_alloc_compile_no_install = prove
 (`!(prog:(num#(A)stack_prog)list) data.
     ALL (\(a,p). stack_no_install p) prog
     ==> ALL (\(a,p). stack_no_install p) (stack_alloc_compile data prog)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[stack_alloc_compile_def; ALL_APPEND; stack_alloc_stubs_def; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_SIMP_TAC[stack_alloc_prog_comp_no_install] THEN
  SIMP[stack_no_install_def; S2LP2AUX_word_gc_code_preds]);;

(* HOL4 line 5058 [simp] *)
let upshift_no_install = prove
 (`!k n. stack_no_install (upshift k n:(A)stack_prog)`,
  MATCH_MP_TAC upshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[upshift_def] THEN COND_CASES_TAC THEN SIMP[stack_no_install_def]);;

let _ = cake_add_simps [upshift_no_install];;

(* HOL4 line 5066 [simp] *)
let downshift_no_install = prove
 (`!k n. stack_no_install (downshift k n:(A)stack_prog)`,
  MATCH_MP_TAC downshift_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[downshift_def] THEN COND_CASES_TAC THEN SIMP[stack_no_install_def]);;

let _ = cake_add_simps [downshift_no_install];;

(* HOL4 line 5074 [simp] *)
let stack_free_no_install = prove
 (`!k n. stack_no_install (stack_remove_stack_free k n:(A)stack_prog)`,
  MATCH_MP_TAC stack_remove_stack_free_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_remove_stack_free_def] THEN
  REPEAT COND_CASES_TAC THEN SIMP[stack_no_install_def; S2LP2AUX_single_preds]);;

let _ = cake_add_simps [stack_free_no_install];;

(* HOL4 line 5083 [simp] *)
let stack_alloc_no_install = prove
 (`!jump k n. stack_no_install (stack_alloc jump k n:(A)stack_prog)`,
  MATCH_MP_TAC stack_alloc_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_def] THEN
  REPEAT COND_CASES_TAC THEN SIMP[stack_no_install_def; S2LP2AUX_single_preds]);;

let _ = cake_add_simps [stack_alloc_no_install];;

(* HOL4 line 5094 *)
let stack_remove_comp_no_install = prove
 (`!jump off k (p:(A)stack_prog).
     stack_no_install p ==> stack_no_install (stack_remove_comp jump off k p)`,
  s2lp2aux_remove_pred_tac stack_no_install_def
    [upshift_no_install; downshift_no_install; stack_free_no_install;
     stack_alloc_no_install]);;

(* HOL4 line 5112 *)
let stack_remove_prog_comp_no_install = prove
 (`!(p:(A)stack_prog) jump off k n.
     stack_no_install p ==> stack_no_install (SND (stack_remove_prog_comp jump off k (n,p)))`,
  REWRITE_TAC[stack_remove_prog_comp_def; SND] THEN
  MESON_TAC[stack_remove_comp_no_install]);;

(* HOL4 line 5119 *)
let stack_remove_compile_no_install = prove
 (`!(prog:(num#(A)stack_prog)list) jump offset gckind mh sp loc.
     ALL (\(a,p). stack_no_install p) prog
     ==> ALL (\(a,p). stack_no_install p)
           (stack_remove_compile jump offset gckind mh sp loc prog)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[stack_remove_compile_def; ALL_APPEND; stack_remove_init_stubs_def; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CONJ_TAC THENL
  [SIMP[stack_no_install_def; halt_inst_def; S2LP2AUX_init_code_preds];
   MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN
   ASM_REWRITE_TAC[stack_remove_prog_comp_no_install]]);;

(* HOL4 line 5135 *)
let stack_names_comp_no_install = prove
 (`!f (p:(A)stack_prog). stack_no_install p ==> stack_no_install (stack_names_comp f p)`,
  s2lp2aux_names_pred_tac stack_no_install_def);;

(* HOL4 line 5146 *)
let stack_names_prog_comp_no_install = prove
 (`!(prog:(num#(A)stack_prog)list) f.
     ALL (\(a,p). stack_no_install p) prog
     ==> ALL (\(a,p). stack_no_install p) (MAP (stack_names_prog_comp f) prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC S2LP2AUX_ALL_MAP_pc THEN
  ASM_REWRITE_TAC[stack_names_prog_comp_def; SND] THEN
  MESON_TAC[stack_names_comp_no_install]);;

(* HOL4 line 5157 *)
let stack_names_compile_no_install = prove
 (`!(prog:(num#(A)stack_prog)list) names.
     ALL (\(a,p). stack_no_install p) prog
     ==> ALL (\(a,p). stack_no_install p) (stack_names_compile names prog)`,
  REWRITE_TAC[stack_names_compile_def; stack_names_prog_comp_no_install]);;

(* HOL4 line 5165 (labLang's Install) *)
let flatten_no_install = prove
 (`!t (p:(A)stack_prog) n m cs bs.
     stack_no_install p
     ==> ALL (\ln. !w bytes l. ~(ln = LabAsm lab_Install w bytes l))
           (append (FST (stack_to_lab_flatten t p n m cs bs)))`,
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL
    [`\ln:(A)line. !w bytes l. ~(ln = LabAsm lab_Install w bytes l)`;
     `stack_no_install:(A)stack_prog->bool`] S2LP2AUX_flatten_ALL)) THEN
  REWRITE_TAC[stack_no_install_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "line"; injectivity "line"; distinctness "asm_with_lab"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY(CASES_ON `dest:num+num`) THEN
  CASE_REWRITE_TAC[compile_jump_def; distinctness "line"; injectivity "line";
                   distinctness "asm_with_lab"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5181 (no_install of sections is labProps') *)
let asm_fetch_aux_no_install_CONS = prove
 (`!(xs:((A)line)list) ls k.
     ALL (\ln. !w bytes l. ~(ln = LabAsm lab_Install w bytes l)) xs /\
     lab_no_install ls
     ==> lab_no_install (CONS (Section k xs) ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; lab_no_install_def; asm_fetch_aux_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lab_no_install_def]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ls:((A)sec)list`; `k:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ]);;

(* HOL4 line 5192 *)
let prog_to_section_no_install = prove
 (`!(prog:(num#(A)stack_prog)list).
     ALL (\(a,p). stack_no_install p) prog ==> lab_no_install (MAP prog_to_section prog)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THENL
  [REWRITE_TAC[lab_no_install_def; asm_fetch_aux_def; option_DISTINCT];
   SUBST1_TAC(ISPEC `h:num#(A)stack_prog` (GSYM PAIR)) THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   STRIP_TAC THEN REWRITE_TAC[S2LP2AUX_prog_to_section_eq] THEN
   MATCH_MP_TAC asm_fetch_aux_no_install_CONS THEN
   ASM_SIMP_TAC[ALL_APPEND; ALL; flatten_no_install; distinctness "line"]]);;

(* HOL4 line 5209 *)
let stack_to_lab_compile_no_install = prove
 (`!(prog:(num#(A)stack_prog)list) prog' stack_conf data_conf max_heap sp offset.
     ALL (\(a,p). stack_no_install p) prog /\
     stack_to_lab_compile stack_conf data_conf max_heap sp offset prog = prog'
     ==> lab_no_install prog'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  REWRITE_TAC[stack_to_lab_compile_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC prog_to_section_no_install THEN
  MATCH_MP_TAC stack_names_compile_no_install THEN
  MATCH_MP_TAC stack_remove_compile_no_install THEN
  MATCH_MP_TAC stack_alloc_compile_no_install THEN
  MATCH_MP_TAC stack_rawcall_compile_no_install THEN
  ASM_REWRITE_TAC[]);;
