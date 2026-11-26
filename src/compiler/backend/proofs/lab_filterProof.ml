(* ========================================================================= *)
(* lab_filterProof: port of HOL4 compiler/backend/proofs/                   *)
(* lab_filterProofScript.sml (CakeML v3479).                                 *)
(* Correctness proof for lab_filter.                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/lab_filter.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 lists labProps among the Ancestors; labProps is not ported yet.    *)
(*   The script uses its definition sec_ends_with_label (written out in      *)
(*   sec_ends_with_label_filter_skip) and its theorems evaluate_ADD_clock,  *)
(*   evaluate_io_events_mono and evaluate_add_clock_io_events_mono, which    *)
(*   are proved here as local helpers (STACKPROPSAUX_lab_...).               *)
(* - The labProps facts rest on STACKPROPSAUX_lab_step (one step of        *)
(*   lab_evaluate with any extra clock either stops or continues from a     *)
(*   state with a smaller clock, the io events only growing), proved once   *)
(*   by a case split instead of the three inductions of HOL4.               *)
(* - state_rel_IMP_sem_EQ_sem (local in HOL4) is proved from filter_correct *)
(*   with STACKPROPSAUX_lab_semantics_sim: a simulation of every run of s   *)
(*   by a run of t with extra clock gives equal semantics.                  *)
(* - STACKPROPSAUX_ names are local helpers (the unit's helper prefix).      *)

let adjust_pc_def = cake_def_wf
  `MEASURE (\x:num#((A)sec)list. list_size (sec_size (\x:A. 0)) (SND x))`
  TERM_TAC
  `adjust_pc p (xs:((A)sec)list) =
     if p = 0 then 0 else
       match xs with
         [] -> p
       | CONS (Section n []) rest -> adjust_pc p rest
       | CONS (Section n (CONS l lines)) rest ->
           if is_Label l then adjust_pc p (CONS (Section n lines) rest)
           else if not_skip l then adjust_pc (p - 1) (CONS (Section n lines) rest) + 1
           else adjust_pc (p - 1) (CONS (Section n lines) rest)`;;

(* all skips for the next k *)

let all_skips_def = cake_def
  `all_skips pc (code:((A)sec)list) k <=>
     (!x y. ~(asm_fetch_aux (pc + k) code = SOME (Asm (Asmi (asm_Inst asm_Skip)) x y))) /\
     (!i. i < k ==>
          ?x y. asm_fetch_aux (pc + i) code = SOME (Asm (Asmi (asm_Inst asm_Skip)) x y))`;;

(* HOL4 [local] *)

let is_Label_not_skip = prove
 (`!y:(A)line. is_Label y ==> not_skip y`,
  GEN_TAC THEN CASES_ON `y:(A)line` THEN SIMP[is_Label_def; not_skip_def]);;

(* the clauses of adjust_pc, asm_fetch_aux and all_skips on the first line *)

let STACKPROPSAUX_adjust_pc_thms = prove
 (`(!xs. adjust_pc 0 (xs:((A)sec)list) = 0) /\
   (!p. adjust_pc p ([]:((A)sec)list) = p) /\
   (!p n rest. adjust_pc p (CONS (Section n []) rest:((A)sec)list) =
               if p = 0 then 0 else adjust_pc p rest) /\
   (!p n l lines rest.
      adjust_pc p (CONS (Section n (CONS l lines)) rest:((A)sec)list) =
      if p = 0 then 0
      else if is_Label l then adjust_pc p (CONS (Section n lines) rest)
      else if not_skip l then adjust_pc (p - 1) (CONS (Section n lines) rest) + 1
      else adjust_pc (p - 1) (CONS (Section n lines) rest))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [adjust_pc_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_not_skip_eq = prove
 (`!y:(A)line. not_skip y <=> ~(?x z. y = Asm (Asmi (asm_Inst asm_Skip)) x z)`,
  GEN_TAC THEN REWRITE_TAC[not_skip_def] THEN EVERY_CASE_TAC THEN SIMP[] THEN
  MESON_TAC[]);;

let STACKPROPSAUX_fetch_thms = prove
 (`(!p n t. asm_fetch_aux p (CONS (Section n []) t:((A)sec)list) = asm_fetch_aux p t) /\
   (!p n y ys t. is_Label y ==>
      asm_fetch_aux p (CONS (Section n (CONS y ys)) t:((A)sec)list) =
      asm_fetch_aux p (CONS (Section n ys) t)) /\
   (!p n y ys t. ~is_Label y ==>
      asm_fetch_aux (p + 1) (CONS (Section n (CONS y ys)) t:((A)sec)list) =
      asm_fetch_aux p (CONS (Section n ys) t)) /\
   (!n y ys t. ~is_Label y ==>
      asm_fetch_aux 0 (CONS (Section n (CONS y ys)) t:((A)sec)list) = SOME y)`,
  REWRITE_TAC[asm_fetch_aux_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB]);;

let STACKPROPSAUX_num_pred = prove
 (`!i. ~(i = 0) ==> ?j. i = j + 1`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; ADD1] THEN MESON_TAC[]);;

let STACKPROPSAUX_all_skips_thms = prove
 (`(!p n t k. all_skips p (CONS (Section n []) t:((A)sec)list) k <=> all_skips p t k) /\
   (!p n y ys t k. is_Label y ==>
      (all_skips p (CONS (Section n (CONS y ys)) t:((A)sec)list) k <=>
       all_skips p (CONS (Section n ys) t) k)) /\
   (!p n y ys t k. ~is_Label y ==>
      (all_skips (p + 1) (CONS (Section n (CONS y ys)) t:((A)sec)list) k <=>
       all_skips p (CONS (Section n ys) t) k))`,
  REWRITE_TAC[all_skips_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms;
               ARITH_RULE `(p + 1) + k = (p + k) + 1`]);;

let STACKPROPSAUX_adjust_pc_cond = prove
 (`!p (xs:((A)sec)list). (if p = 0 then 0 else adjust_pc p xs) = adjust_pc p xs`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms]);;

let asm_fetch_aux_eq = prove
 (`!pc (code:((A)sec)list).
     ?k. asm_fetch_aux (pc + k) code =
         asm_fetch_aux (adjust_pc pc code) (filter_skip code) /\
         all_skips pc code k`,
  SUBGOAL_THEN
   `!(code:((A)sec)list) pc.
     ?k. asm_fetch_aux (pc + k) code =
         asm_fetch_aux (adjust_pc pc code) (filter_skip code) /\
         all_skips pc code k`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[asm_fetch_aux_def; filter_skip_def; STACKPROPSAUX_adjust_pc_thms;
                all_skips_def; option_DISTINCT; LT];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A)sec` (cases "sec")) THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[STACKPROPSAUX_fetch_thms; filter_skip_def; FILTER;
                STACKPROPSAUX_all_skips_thms; STACKPROPSAUX_adjust_pc_thms;
                STACKPROPSAUX_adjust_pc_cond] THEN
    ASM_REWRITE_TAC[GSYM filter_skip_def];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filter_skip_def]) THEN REWRITE_TAC[filter_skip_def; FILTER] THEN
  ASM_CASES_TAC `is_Label (h:(A)line)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o SPEC `pc:num`) THEN EXISTS_TAC `k:num` THEN
    ASM_SIMP_TAC[is_Label_not_skip; STACKPROPSAUX_fetch_thms; STACKPROPSAUX_all_skips_thms;
                 STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_adjust_pc_cond];
    ALL_TAC] THEN
  ASM_CASES_TAC `pc = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC `not_skip (h:(A)line)` THENL
     [EXISTS_TAC `0` THEN
      ASM_SIMP_TAC[ADD_CLAUSES; STACKPROPSAUX_fetch_thms; STACKPROPSAUX_adjust_pc_thms;
                   all_skips_def; LT; option_INJ] THEN
      UNDISCH_TAC `not_skip (h:(A)line)` THEN REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o SPEC `0`) THEN EXISTS_TAC `k + 1` THEN
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC[ADD_CLAUSES; STACKPROPSAUX_fetch_thms; STACKPROPSAUX_adjust_pc_thms;
                 all_skips_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THENL
    [ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms; option_INJ] THEN
     UNDISCH_TAC `~not_skip (h:(A)line)` THEN REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN
     MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
      MATCH_MP STACKPROPSAUX_num_pred) THEN
   ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms; LT_ADD_RCANCEL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o SPEC `p:num`) THEN EXISTS_TAC `k:num` THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(p + 1) + k = (p + k) + 1`] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms; STACKPROPSAUX_all_skips_thms;
               STACKPROPSAUX_adjust_pc_thms; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms]);;

(* for any adjusted fetch, the original fetch is either equal or is a skip  *)
(* (HOL4 [local]; its unused variable inst is left out)                     *)

let asm_fetch_not_skip_adjust_pc = prove
 (`!pc (code:((A)sec)list).
     (!x y. ~(asm_fetch_aux pc code = SOME (Asm (Asmi (asm_Inst asm_Skip)) x y))) ==>
     asm_fetch_aux pc code = asm_fetch_aux (adjust_pc pc code) (filter_skip code)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC (SPECL [`pc:num`; `code:((A)sec)list`]
    asm_fetch_aux_eq) THEN
  ASM_CASES_TAC `k = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `all_skips pc (code:((A)sec)list) k` THEN REWRITE_TAC[all_skips_def] THEN
    DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_ARITH_TAC]);;

(* HOL4 [local] *)

let state_rw = prove
 (`lab_state_clock_fupd (combin_K (lab_state_clock s)) (s:(A,C,FFI)lab_state) = s /\
   lab_state_pc_fupd (combin_K (lab_state_pc s)) s = s /\
   lab_state_pc_fupd (combin_K (lab_state_pc s))
     (lab_state_clock_fupd (combin_K (lab_state_clock s + k')) s) =
   lab_state_clock_fupd (combin_K (lab_state_clock s + k')) s`,
  REWRITE_TAC[lab_state_component_equality] THEN SIMP[]);;

(* a Skip instruction: one step of the clock and of the pc *)

let STACKPROPSAUX_lab_eval_skip = prove
 (`asm_fetch (s:(A,C,FFI)lab_state) = SOME (Asm (Asmi (asm_Inst asm_Skip)) x y) /\
   ~(lab_state_clock s = 0) /\ ~lab_state_failed s
   ==> lab_evaluate s = lab_evaluate (inc_pc (lab_dec_clock s))`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[asm_inst_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[]);;

(* 2) all_skips allow swapping pc for clock (HOL4 [local]) *)

let all_skips_evaluate = prove
 (`!k (s:(A,C,FFI)lab_state).
     all_skips (lab_state_pc s) (lab_state_code s) k /\ ~lab_state_failed s ==>
     !k'. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock s + k') + k)) s) =
          lab_evaluate (lab_state_pc_fupd (combin_K (lab_state_pc s + k))
                          (lab_state_clock_fupd (combin_K (lab_state_clock s + k')) s))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[lab_state_component_equality] THEN SIMP[ADD_CLAUSES];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `all_skips (lab_state_pc s) (lab_state_code (s:(A,C,FFI)lab_state)) (SUC k)` THEN
  REWRITE_TAC[all_skips_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; ADD_CLAUSES] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`x:byte list`; `y:num`] THEN
  DISCH_TAC THEN
  MP_TAC(INST [`x:byte list`,`x:byte list`; `y:num`,`y:num`]
    (ISPEC `lab_state_clock_fupd (combin_K ((lab_state_clock s + k') + SUC k))
              (s:(A,C,FFI)lab_state)`
       (GEN `s:(A,C,FFI)lab_state` STACKPROPSAUX_lab_eval_skip))) THEN
  ASM_REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; NOT_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lab_state_pc_fupd (combin_K (lab_state_pc s + 1))
                                 (s:(A,C,FFI)lab_state)`) THEN
  SIMP[all_skips_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(p + 1) + k = p + SUC k`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
      ASM_REWRITE_TAC[LT_SUC; ARITH_RULE `p + SUC i = (p + 1) + i`]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `k':num`) THEN
  REWRITE_TAC[inc_pc_def; lab_dec_clock_def] THEN
  SIMP[SUC_SUB1; ARITH_RULE `(p + 1) + k = SUC (p + k)`]);;

let lab_filterProof_state_rel_def = cake_def
  `lab_filterProof_state_rel (s1:(A,C,FFI)lab_state) t1 <=>
     (?s1compile.
        s1 = lab_state_code_fupd (combin_K (filter_skip (lab_state_code t1)))
               (lab_state_pc_fupd (combin_K (adjust_pc (lab_state_pc t1) (lab_state_code t1)))
               (lab_state_compile_oracle_fupd
                  (combin_K (\n. (\(a,b). (a,filter_skip b)) (lab_state_compile_oracle t1 n)))
               (lab_state_compile_fupd (combin_K s1compile) t1))) /\
        lab_state_compile t1 = (\c p. s1compile c (filter_skip p))) /\
     ~lab_state_failed t1`;;

(* adjust_pc one position further: + 1 unless the line there is a skip    *)

let STACKPROPSAUX_adjust_pc_SUC = prove
 (CASE_TERM
  `!(code:((A)sec)list) pc.
     adjust_pc (pc + 1) code =
     adjust_pc pc code +
     (match asm_fetch_aux pc code with
        SOME l -> if not_skip l then 1 else 0
      | NONE -> 1)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms; asm_fetch_aux_def] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A)sec` (cases "sec")) THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THENL
   [ASM_REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_adjust_pc_cond;
                    STACKPROPSAUX_fetch_thms; ADD_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `is_Label (h:(A)line)` THENL
   [ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_adjust_pc_cond;
                 STACKPROPSAUX_fetch_thms; ADD_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `pc = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_fetch_thms; ADD_CLAUSES;
                 ARITH_EQ; SUB_REFL] THEN
    CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
  ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_fetch_thms; ADD_EQ_0; ARITH_EQ;
               ADD_SUB; ARITH_RULE `(p + 1) + 1 = (p + 1) + 1`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let STACKPROPSAUX_adjust_pc_skips = prove
 (`!k pc (code:((A)sec)list).
     all_skips pc code k ==> adjust_pc (pc + k) code = adjust_pc pc code`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[all_skips_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; ADD_CLAUSES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pc + 1`; `code:((A)sec)list`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[all_skips_def; ARITH_RULE `(pc + 1) + k = pc + SUC k`;
                ARITH_RULE `(pc + 1) + i = pc + SUC i`] THEN ASM_SIMP_TAC[LT_SUC];
    REWRITE_TAC[ARITH_RULE `(pc + 1) + k = SUC (pc + k)`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[STACKPROPSAUX_adjust_pc_SUC] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[not_skip_def] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES]]);;

(* HOL4 [local] *)

let adjust_pc_all_skips = prove
 (`!k pc (code:((A)sec)list).
     all_skips pc code k ==> adjust_pc pc code + 1 = adjust_pc ((pc + k) + 1) code`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP STACKPROPSAUX_adjust_pc_skips) THEN
  REWRITE_TAC[STACKPROPSAUX_adjust_pc_SUC; EQ_ADD_LCANCEL] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[all_skips_def]) THEN
  CASES_ON `asm_fetch_aux (pc + k) (code:((A)sec)list)` THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[STACKPROPSAUX_not_skip_eq; option_INJ] THEN
  MESON_TAC[]);;

(* HOL4 [local] *)

let asm_fetch_aux_eq2 = prove
 (`asm_fetch_aux (adjust_pc pc code) (filter_skip (code:((A)sec)list)) = x ==>
   ?k. asm_fetch_aux (pc + k) code = x /\ all_skips pc code k`,
  MESON_TAC[asm_fetch_aux_eq]);;

(* HOL4 [local] *)

let all_skips_evaluate_rw = prove
 (`all_skips (lab_state_pc s) (lab_state_code s) k /\ ~lab_state_failed s /\
   lab_state_clock s = clk + k /\
   t = lab_state_pc_fupd (combin_K (lab_state_pc s + k))
         (lab_state_clock_fupd (combin_K clk) (s:(A,C,FFI)lab_state))
   ==> lab_evaluate s = lab_evaluate t`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `lab_state_clock_fupd (combin_K clk) (s:(A,C,FFI)lab_state)`]
                all_skips_evaluate) THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `lab_state_clock_fupd (combin_K (clk + k)) s = (s:(A,C,FFI)lab_state)`
    SUBST1_TAC THENL
   [REWRITE_TAC[lab_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
  DISCH_THEN ACCEPT_TAC);;

(* for all initial code there is some all_skips (HOL4 [local]) *)

let all_skips_initial_adjust = prove
 (`!code:((A)sec)list. ?k. all_skips 0 code k /\ adjust_pc k code = 0`,
  GEN_TAC THEN
  X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC (SPECL [`0`; `code:((A)sec)list`]
    asm_fetch_aux_eq) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_adjust_pc_skips) THEN
  REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_adjust_pc_thms]);;

(* loc_to_pc in the filtered code *)

let STACKPROPSAUX_loc_to_pc_thms = prove
 (`(!n1 n2 k ys. loc_to_pc n1 n2 (CONS (Section k []) ys:((A)sec)list) =
      if k = n1 /\ n2 = 0 then SOME 0 else loc_to_pc n1 n2 ys) /\
   (!n1 n2 k z zs ys. loc_to_pc n1 n2 (CONS (Section k (CONS z zs)) ys:((A)sec)list) =
      if k = n1 /\ n2 = 0 then SOME 0 else
      if (?k. z = lab_Label n1 n2 k) /\ ~(n2 = 0) then SOME 0 else
      if is_Label z then loc_to_pc n1 n2 (CONS (Section k zs) ys) else
      OPTION_MAP (\pos. pos + 1) (loc_to_pc n1 n2 (CONS (Section k zs) ys)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [loc_to_pc_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CASES_ON `loc_to_pc n1 n2 (CONS (Section k zs) ys:((A)sec)list)` THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CAKE_REWRITE_TAC[]);;

let STACKPROPSAUX_loc_to_pc_head = prove
 (`k = n1 /\ n2 = 0 ==> loc_to_pc n1 n2 (CONS (Section k xs) ys:((A)sec)list) = SOME 0`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [loc_to_pc_def] THEN ASM_REWRITE_TAC[]);;

let STACKPROPSAUX_loc_to_pc_filter = prove
 (`!(code:((A)sec)list) n1 n2.
     (loc_to_pc n1 n2 (filter_skip code) = NONE <=> loc_to_pc n1 n2 code = NONE) /\
     (!pc. loc_to_pc n1 n2 code = SOME pc ==>
           loc_to_pc n1 n2 (filter_skip code) = SOME (adjust_pc pc code))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[filter_skip_def; loc_to_pc_def; option_DISTINCT]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A)sec` (cases "sec")) THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[filter_skip_def; FILTER; STACKPROPSAUX_loc_to_pc_thms] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_INJ; GSYM filter_skip_def] THENL
     [MESON_TAC[STACKPROPSAUX_adjust_pc_thms]; ALL_TAC] THEN
    ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_adjust_pc_cond];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filter_skip_def]) THEN REWRITE_TAC[filter_skip_def; FILTER] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPECL [`n1:num`; `n2:num`]) THEN
  ASM_CASES_TAC `is_Label (h:(A)line)` THENL
   [ASM_SIMP_TAC[is_Label_not_skip; STACKPROPSAUX_loc_to_pc_thms; STACKPROPSAUX_adjust_pc_thms;
                STACKPROPSAUX_adjust_pc_cond] THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
   ASM_MESON_TAC[STACKPROPSAUX_adjust_pc_thms];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?k. (h:(A)line) = lab_Label n1 n2 k)` ASSUME_TAC THENL
    [STRIP_TAC THEN UNDISCH_TAC `~is_Label (h:(A)line)` THEN ASM_REWRITE_TAC[is_Label_def];
     ALL_TAC] THEN
   ASM_CASES_TAC `not_skip (h:(A)line)` THEN ASM_REWRITE_TAC[STACKPROPSAUX_loc_to_pc_thms] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; OPTION_MAP_EQ_NONE] THENL
    [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms];
     ALL_TAC] THEN
   REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
   ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
   ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; OPTION_MAP_EQ_NONE] THENL
    [ASM_SIMP_TAC[STACKPROPSAUX_loc_to_pc_head; option_DISTINCT] THEN
     GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms];
     ALL_TAC] THEN
   REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
   ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; ADD_EQ_0; ARITH_EQ; ADD_SUB]]);;

(* May need strengthening (HOL4 [local]) *)

let loc_to_pc_eq_NONE = prove
 (`!n1 n2 (code:((A)sec)list).
     loc_to_pc n1 n2 (filter_skip code) = NONE ==> loc_to_pc n1 n2 code = NONE`,
  MESON_TAC[STACKPROPSAUX_loc_to_pc_filter]);;

(* HOL4 [local] *)

let loc_to_pc_eq_SOME = prove
 (`!n1 n2 (code:((A)sec)list) pc.
     loc_to_pc n1 n2 (filter_skip code) = SOME pc ==>
     ?pc'. loc_to_pc n1 n2 code = SOME pc' /\ adjust_pc pc' code = pc`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`code:((A)sec)list`; `n1:num`; `n2:num`] STACKPROPSAUX_loc_to_pc_filter) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `loc_to_pc n1 n2 (code:((A)sec)list)` THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let STACKPROPSAUX_next_label_nonlabel = prove
 (`!k y ys xs. ~is_Label y ==>
     next_label (CONS (Section k (CONS y ys)) xs:((A)sec)list) =
     next_label (CONS (Section k ys) xs)`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)line` THEN REWRITE_TAC[is_Label_def; next_label_def]);;

(* HOL4 [local] *)

let next_label_filter_skip = prove
 (`!code:((A)sec)list. next_label code = next_label (filter_skip code)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[filter_skip_def]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A)sec` (cases "sec")) THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN
  LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC[filter_skip_def; FILTER; next_label_def]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filter_skip_def]) THEN REWRITE_TAC[filter_skip_def; FILTER] THEN
  ASM_CASES_TAC `is_Label (h:(A)line)` THENL
   [ASM_SIMP_TAC[is_Label_not_skip] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      (try fst(dest_const(rator(concl th))) = "is_Label" with Failure _ -> false))) THEN
    CASES_ON `h:(A)line` THEN REWRITE_TAC[is_Label_def; next_label_def];
    ASM_SIMP_TAC[STACKPROPSAUX_next_label_nonlabel] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[STACKPROPSAUX_next_label_nonlabel]]);;

let STACKPROPSAUX_lab_after_thms = prove
 (`(!p n t. get_lab_after p (CONS (Section n []) t:((A)sec)list) = get_lab_after p t) /\
   (!p n y ys t. is_Label y ==>
      get_lab_after p (CONS (Section n (CONS y ys)) t:((A)sec)list) =
      get_lab_after p (CONS (Section n ys) t)) /\
   (!p n y ys t. ~is_Label y ==>
      get_lab_after (p + 1) (CONS (Section n (CONS y ys)) t:((A)sec)list) =
      get_lab_after p (CONS (Section n ys) t)) /\
   (!n y ys t. ~is_Label y ==>
      get_lab_after 0 (CONS (Section n (CONS y ys)) t:((A)sec)list) =
      next_label (CONS (Section n ys) t))`,
  REWRITE_TAC[get_lab_after_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB]);;

let STACKPROPSAUX_all_skips_SUC = prove
 (`!p (code:((A)sec)list) k.
     all_skips p code (k + 1) <=>
     (?x y. asm_fetch_aux p code = SOME (Asm (Asmi (asm_Inst asm_Skip)) x y)) /\
     all_skips (p + 1) code k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_skips_def; ARITH_RULE `(p + 1) + k = p + k + 1`] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      MESON_TAC[ARITH_RULE `0 < k + 1`];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
      REWRITE_TAC[ADD_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i = 0` THENL
     [ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
     FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[ADD_ASSOC] THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* get_lab_after in the filtered code (get_lab_after_adjust below) *)

let STACKPROPSAUX_get_lab_after_filter = prove
 (`!(code:((A)sec)list) pc k.
     all_skips pc code k ==>
     get_lab_after (pc + k) code = get_lab_after (adjust_pc pc code) (filter_skip code)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[get_lab_after_def; filter_skip_def]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A)sec` (cases "sec")) THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [ASM_SIMP_TAC[filter_skip_def; FILTER; STACKPROPSAUX_lab_after_thms;
                 STACKPROPSAUX_all_skips_thms; STACKPROPSAUX_adjust_pc_thms;
                 STACKPROPSAUX_adjust_pc_cond];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filter_skip_def]) THEN REWRITE_TAC[filter_skip_def; FILTER] THEN
  ASM_CASES_TAC `is_Label (h:(A)line)` THENL
   [ASM_SIMP_TAC[is_Label_not_skip; STACKPROPSAUX_lab_after_thms;
                 STACKPROPSAUX_all_skips_thms; STACKPROPSAUX_adjust_pc_thms;
                 STACKPROPSAUX_adjust_pc_cond];
    ALL_TAC] THEN
  ASM_CASES_TAC `pc = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC `k = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[all_skips_def; ADD_CLAUSES; LT] THEN ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms; option_INJ] THEN DISCH_TAC THEN
      SUBGOAL_THEN `not_skip (h:(A)line)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[STACKPROPSAUX_not_skip_eq]; ALL_TAC] THEN
      ASM_SIMP_TAC[STACKPROPSAUX_lab_after_thms; STACKPROPSAUX_adjust_pc_thms] THEN
      GEN_REWRITE_TAC LAND_CONV [next_label_filter_skip] THEN REWRITE_TAC[filter_skip_def];
      FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
    REWRITE_TAC[STACKPROPSAUX_all_skips_SUC] THEN
      ASM_SIMP_TAC[SPEC `0` (CONJUNCT2 (CONJUNCT2 STACKPROPSAUX_all_skips_thms))] THEN
      ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms; option_INJ] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~not_skip (h:(A)line)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `h:(A)line`)) THEN
      ASM_SIMP_TAC[ADD_CLAUSES; STACKPROPSAUX_lab_after_thms; STACKPROPSAUX_adjust_pc_thms] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `j:num`]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_adjust_pc_thms]];
    FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
  ASM_SIMP_TAC[STACKPROPSAUX_all_skips_thms] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(p + 1) + k = (p + k) + 1`] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_lab_after_thms; STACKPROPSAUX_adjust_pc_thms;
               ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[STACKPROPSAUX_lab_after_thms]]);;

(* HOL4 [local] *)

let all_skips_get_lab_after = prove
 (`!(code:((A)sec)list) k.
     all_skips 0 code k ==> get_lab_after k code = get_lab_after 0 (filter_skip code)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STACKPROPSAUX_get_lab_after_filter) THEN
  REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_adjust_pc_thms]);;

(* HOL4 [local] *)

let get_lab_after_adjust = prove
 (`!pc (code:((A)sec)list) k.
     all_skips pc code k ==>
     get_lab_after (pc + k) code = get_lab_after (adjust_pc pc code) (filter_skip code)`,
  MESON_TAC[STACKPROPSAUX_get_lab_after_filter]);;

(* HOL4 [local] *)

let loc_to_pc_adjust_pc_append = prove
 (`!n1 n2 (code:((A)sec)list) pc ls.
     loc_to_pc n1 n2 code = SOME pc ==> adjust_pc pc code = adjust_pc pc (APPEND code ls)`,
  SUBGOAL_THEN
   `!(code:((A)sec)list) n1 n2 pc ls.
     loc_to_pc n1 n2 code = SOME pc ==> adjust_pc pc code = adjust_pc pc (APPEND code ls)`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[loc_to_pc_def; option_DISTINCT]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A)sec` (cases "sec")) THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[APPEND; STACKPROPSAUX_loc_to_pc_thms] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_adjust_pc_cond] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n1:num`; `n2:num`]) THEN
  REWRITE_TAC[APPEND] THEN DISCH_TAC THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; STACKPROPSAUX_adjust_pc_cond];
    ALL_TAC] THEN
  REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_adjust_pc_thms; ADD_EQ_0; ARITH_EQ; ADD_SUB]);;

let share_mem_op_NONE_filter_correct = prove
 (`all_skips (lab_state_pc t1) (lab_state_code t1) k /\
   share_mem_op m r a
     (lab_state_pc_fupd (combin_K (adjust_pc (lab_state_pc t1) (lab_state_code t1)))
     (lab_state_code_fupd (combin_K (filter_skip (lab_state_code t1)))
     (lab_state_compile_fupd (combin_K arb_compile)
     (lab_state_compile_oracle_fupd (combin_K arb_oracle) (t1:(A,C,FFI)lab_state))))) = NONE
   ==> share_mem_op m r a (lab_state_pc_fupd (combin_K (k + lab_state_pc t1)) t1) = NONE`,
  CASES_ON `m:memop` THEN CASES_ON `a:(A)addr` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def; lab_addr_def] THEN
  SIMP[] THEN EVERY_CASE_TAC THEN SIMP[option_DISTINCT]);;

(* the witness of a goal ?s2. ... SOME (FFI_return f l,s2) ...: the state  *)
(* of the first such pair with a known state in the goal                   *)

(* the witness of a goal ?s2. !k'. X = s2 /\ ...: the state X *)

let STACKPROPSAUX_EQ_WITNESS_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let bod = snd(strip_forall bod) in
  let c = hd(conjuncts bod) in
  let l,r = dest_eq c in
  if r = v then EXISTS_TAC l g else failwith "EQ_WITNESS_TAC";;

let share_mem_op_FFI_return_filter_correct = prove
 (`all_skips (lab_state_pc t1) (lab_state_code t1) k /\ ~(lab_state_clock t1 = 0) /\
   lab_state_compile t1 = (\c p. s1compile c (filter_skip p)) /\ ~lab_state_failed t1 /\
   share_mem_op m r a
     (lab_state_pc_fupd (combin_K (adjust_pc (lab_state_pc t1) (lab_state_code t1)))
     (lab_state_code_fupd (combin_K (filter_skip (lab_state_code t1)))
     (lab_state_compile_fupd (combin_K s1compile)
     (lab_state_compile_oracle_fupd
        (combin_K (\n. (\(a,b). (a,filter_skip b)) (lab_state_compile_oracle t1 n)))
        (t1:(A,C,FFI)lab_state))))) = SOME (FFI_return f l,s)
   ==> ?s2. !k'.
         share_mem_op m r a (lab_state_pc_fupd (combin_K (k + lab_state_pc t1)) t1) =
           SOME (FFI_return f l,s2) /\
         lab_filterProof_state_rel s s2 /\ ~lab_state_failed s /\ ~lab_state_failed s2 /\
         share_mem_op m r a
           (lab_state_pc_fupd (combin_K (k + lab_state_pc t1))
           (lab_state_clock_fupd (combin_K (k' + lab_state_clock t1)) t1)) =
           SOME (FFI_return f l,lab_state_clock_fupd (combin_K (k' + lab_state_clock s2)) s2)`,
  DISCH_THEN(fun th -> MP_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP adjust_pc_all_skips (CONJUNCT1 th)) THEN
    ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  SUBGOAL_THEN `!k'. (k' + lab_state_clock (t1:(A,C,FFI)lab_state)) - 1 =
                     k' + (lab_state_clock t1 - 1)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ARITH_RULE `(pc + k) + 1 = (k + pc) + 1`]) THEN
  CASES_ON `m:memop` THEN CASES_ON `a:(A)addr` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def; lab_addr_def;
              inc_pc_def; lab_dec_clock_def] THEN
  SIMP[] THEN EVERY_CASE_TAC THEN SIMP[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN STACKPROPSAUX_EQ_WITNESS_TAC THEN
  SIMP[lab_filterProof_state_rel_def] THEN MESON_TAC[]);;

let share_mem_op_FFI_final_filter_correct = prove
 (`all_skips (lab_state_pc t1) (lab_state_code t1) k /\ ~(lab_state_clock t1 = 0) /\
   lab_state_compile t1 = (\c p. s1compile c (filter_skip p)) /\ ~lab_state_failed t1 /\
   share_mem_op m r a
     (lab_state_pc_fupd (combin_K (adjust_pc (lab_state_pc t1) (lab_state_code t1)))
     (lab_state_code_fupd (combin_K (filter_skip (lab_state_code t1)))
     (lab_state_compile_fupd (combin_K s1compile)
     (lab_state_compile_oracle_fupd
        (combin_K (\n. (\(a,b). (a,filter_skip b)) (lab_state_compile_oracle t1 n)))
        (t1:(A,C,FFI)lab_state))))) = SOME (FFI_final f,s)
   ==> ?s2. share_mem_op m r a (lab_state_pc_fupd (combin_K (k + lab_state_pc t1)) t1) =
              SOME (FFI_final f,s2) /\
            lab_state_ffi s = lab_state_ffi s2`,
  CASES_ON `m:memop` THEN CASES_ON `a:(A)addr` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def; lab_addr_def;
              inc_pc_def; lab_dec_clock_def] THEN
  SIMP[] THEN EVERY_CASE_TAC THEN SIMP[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

(* the skips before the instruction of the filtered state: runs from the  *)
(* state at pc + k with clock c + k' are runs with clock c + k' + k        *)

let STACKPROPSAUX_skip_reduce = prove
 (`all_skips (lab_state_pc t1) (lab_state_code t1) k /\ ~lab_state_failed t1 /\
   lab_evaluate (lab_state_pc_fupd (combin_K (lab_state_pc t1 + k))
                  (lab_state_clock_fupd (combin_K (lab_state_clock t1 + k'))
                     (t1:(A,C,FFI)lab_state))) = (res,t2)
   ==> lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t1 + (k' + k))) t1) =
       (res,t2)`,
  STRIP_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`k:num`; `t1:(A,C,FFI)lab_state`] all_skips_evaluate) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SPEC `k':num`));;

(* asm_inst commutes with any function on states that keeps the fields it *)
(* reads and commutes with the updates it makes                            *)

let STACKPROPSAUX_asm_inst_gen = prove
 (`!(g:(A,C,FFI)lab_state->(A,C,FFI)lab_state).
     (!s. lab_state_regs (g s) = lab_state_regs s /\
          lab_state_mem (g s) = lab_state_mem s /\
          lab_state_mem_domain (g s) = lab_state_mem_domain s /\
          lab_state_be (g s) = lab_state_be s /\
          lab_state_fp_regs (g s) = lab_state_fp_regs s /\
          lab_state_failed (g s) = lab_state_failed s) /\
     (!s x. lab_state_regs_fupd (combin_K x) (g s) = g (lab_state_regs_fupd (combin_K x) s)) /\
     (!s x. lab_state_mem_fupd (combin_K x) (g s) = g (lab_state_mem_fupd (combin_K x) s)) /\
     (!s x. lab_state_fp_regs_fupd (combin_K x) (g s) = g (lab_state_fp_regs_fupd (combin_K x) s)) /\
     (!s x. lab_state_failed_fupd (combin_K x) (g s) = g (lab_state_failed_fupd (combin_K x) s))
     ==> !i s. asm_inst i (g s) = g (asm_inst i s)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!r w s. lab_upd_reg r w ((g:(A,C,FFI)lab_state->(A,C,FFI)lab_state) s) =
             g (lab_upd_reg r w s)) /\
    (!a w s. lab_upd_mem a w (g s) = g (lab_upd_mem a w (s:(A,C,FFI)lab_state))) /\
    (!b s. lab_assert b (g s) = g (lab_assert b (s:(A,C,FFI)lab_state))) /\
    (!r v s. lab_upd_fp_reg r v (g s) = g (lab_upd_fp_reg r v (s:(A,C,FFI)lab_state))) /\
    (!r s. lab_read_fp_reg r (g s) = lab_read_fp_reg r (s:(A,C,FFI)lab_state)) /\
    (!ri s. lab_reg_imm ri (g s) = lab_reg_imm ri (s:(A,C,FFI)lab_state)) /\
    (!a s. lab_addr a (g s) = lab_addr a (s:(A,C,FFI)lab_state))`
   STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lab_upd_reg_def; lab_upd_mem_def; lab_assert_def; lab_upd_fp_reg_def;
                    lab_read_fp_reg_def] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THENL
     [CASES_ON `ri:(A)reg_imm` THEN ASM_REWRITE_TAC[lab_reg_imm_def];
      CASES_ON `a:(A)addr` THEN ASM_REWRITE_TAC[lab_addr_def]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `i:(A)inst` THEN
  ASM_REWRITE_TAC[asm_inst_def] THENL
   [STACKPAUX_TYPE_CASES_TAC `:(A)asm_arith` THEN
    ASM_REWRITE_TAC[lab_arith_upd_def] THEN
    TRY (STACKPAUX_TYPE_CASES_TAC `:binop` THEN ASM_REWRITE_TAC[lab_binop_upd_def]) THEN
    EVERY_CASE_TAC THEN ASM_REWRITE_TAC[lab_binop_upd_def; LET_DEF; LET_END_DEF];
    STACKPAUX_TYPE_CASES_TAC `:memop` THEN
    ASM_REWRITE_TAC[lab_mem_op_def; lab_mem_load_def; lab_mem_store_def; mem_load32_def;
                    mem_store32_def; mem_load_byte_def; mem_store_byte_def] THEN
    EVERY_CASE_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF];
    STACKPAUX_TYPE_CASES_TAC `:fp` THEN ASM_REWRITE_TAC[lab_fp_upd_def] THEN
    EVERY_CASE_TAC THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF]]);;

let STACKPROPSAUX_asm_inst_frame =
  let inst g = REWRITE_RULE[] (BETA_RULE (MATCH_MP (ISPEC g STACKPROPSAUX_asm_inst_gen)
    (prove(lhand(concl(ISPEC g STACKPROPSAUX_asm_inst_gen)),
           BETA_TAC THEN SIMP[])))) in
  end_itlist CONJ (map inst
   [`\s:(A,C,FFI)lab_state. lab_state_pc_fupd (combin_K p) s`;
    `\s:(A,C,FFI)lab_state. lab_state_code_fupd (combin_K cd) s`;
    `\s:(A,C,FFI)lab_state. lab_state_clock_fupd (combin_K ck) s`;
    `\s:(A,C,FFI)lab_state. lab_state_compile_fupd (combin_K cp) s`;
    `\s:(A,C,FFI)lab_state. lab_state_compile_oracle_fupd (combin_K co) s`]);;

let STACKPROPSAUX_asm_inst_reads = prove
 (`!i (s:(A,C,FFI)lab_state).
     lab_state_compile_oracle (asm_inst i s) = lab_state_compile_oracle s /\
     lab_state_compile (asm_inst i s) = lab_state_compile s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `lab_state_compile_oracle_fupd (combin_K (lab_state_compile_oracle s)) s = (s:(A,C,FFI)lab_state) /\
    lab_state_compile_fupd (combin_K (lab_state_compile s)) s = s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[lab_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`i:(A)inst`; `s:(A,C,FFI)lab_state`]
      (INST [`lab_state_compile_oracle (s:(A,C,FFI)lab_state)`,
             `co:num->C#((A)sec)list`]
        (el 4 (CONJUNCTS STACKPROPSAUX_asm_inst_frame))));
    MP_TAC(SPECL [`i:(A)inst`; `s:(A,C,FFI)lab_state`]
      (INST [`lab_state_compile (s:(A,C,FFI)lab_state)`,
             `cp:C->((A)sec)list->(byte list#C)option`]
        (el 3 (CONJUNCTS STACKPROPSAUX_asm_inst_frame))))] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  SIMP[]);;

let STACKPROPSAUX_with_clock_self_lab = prove
 (`lab_state_clock_fupd (combin_K (lab_state_clock t)) (t:(A,C,FFI)lab_state) = t`,
  REWRITE_TAC[lab_state_component_equality] THEN SIMP[]);;

let STACKPROPSAUX_lab_clock_fupd_id = prove
 (`lab_state_clock (x:(A,C,FFI)lab_state) = n ==> lab_state_clock_fupd (combin_K n) x = x`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STACKPROPSAUX_with_clock_self_lab]);;

let STACKPROPSAUX_filter_skip_APPEND = prove
 (`!l1 (l2:((A)sec)list). filter_skip (APPEND l1 l2) = APPEND (filter_skip l1) (filter_skip l2)`,
  REWRITE_TAC[filter_skip_MAP; MAP_APPEND]);;

let STACKPROPSAUX_FST_filter_pair = prove
 (`!p:C#((A)sec)list. FST ((\(a,b). (a,filter_skip b)) p) = FST p`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST]);;

(* Tactics for filter_correct (the proof follows HOL4: complete induction  *)
(* on the clock, one case per instruction of the filtered code).            *)

let STACKPROPSAUX_lab_is_eval th =
  is_eq (concl th) &&
  (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "lab_evaluate"
   with Failure _ -> false);;

let STACKPROPSAUX_LAB_SIMPS =
  [asm_inst_consts; STACKPROPSAUX_asm_inst_reads; STACKPROPSAUX_lab_clock_fupd_id];;

(* both sides stop: the target state is the source state up to the fields  *)
(* that the filter changes                                                  *)

let STACKPROPSAUX_LAB_FINAL_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
  (fun (asl,w as g) ->
     let v,bod = dest_exists w in
     let cs = conjuncts bod in
     let eq = find (fun c -> is_eq c && rhs c = v) (flat (map conjuncts cs)) in
     EXISTS_TAC (lhs eq) g) THEN
  REWRITE_TAC[] THEN SIMP[];;

(* both sides take a step and continue: use the induction hypothesis "ih"  *)
(* with the witness wit for the compiler of the filtered state             *)

let STACKPROPSAUX_LAB_REC_WIT_TAC (wit:term) (relproof:tactic) : tactic =
  DISCH_TAC THEN
  (fun (asl,w as g) ->
     let ev = find (fun th -> STACKPROPSAUX_lab_is_eval th) (map snd asl) in
     let x' = rand(lhs(concl ev)) in
     let kv,b1 = dest_exists w in
     let tv,b2 = dest_exists b1 in
     let y' = rand(lhs(hd(conjuncts b2))) in
     let y0 = vsubst [`0`,kv] y' in
     (USE_THEN "ih" (MP_TAC o SPEC (mk_icomb(`lab_state_clock:(A,C,FFI)lab_state->num`,x')))
      THEN ANTS_TAC THENL [SIMP STACKPROPSAUX_LAB_SIMPS THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [x'; y0; `res:machine_result`; `s2:(A,C,FFI)lab_state`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[lab_filterProof_state_rel_def] THEN REPEAT CONJ_TAC THEN
        FIRST [SIMP STACKPROPSAUX_LAB_SIMPS THEN ASM_REWRITE_TAC[] THEN NO_TAC;
               EXISTS_TAC wit THEN
               SIMP STACKPROPSAUX_LAB_SIMPS THEN ASM_REWRITE_TAC[] THEN relproof];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `kk:num` (X_CHOOSE_THEN `tt:(A,C,FFI)lab_state`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`kk:num`; `tt:(A,C,FFI)lab_state`] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th -> if STACKPROPSAUX_lab_is_eval th &&
                                 rand(concl th) = `res:machine_result,(tt:(A,C,FFI)lab_state)`
                              then SUBST1_TAC(SYM th) else failwith "") THEN
      AP_TERM_TAC THEN REWRITE_TAC[lab_state_component_equality] THEN
      SIMP STACKPROPSAUX_LAB_SIMPS THEN ASM_ARITH_TAC) g);;

let STACKPROPSAUX_LAB_REC_TAC (relproof:tactic) : tactic =
  STACKPROPSAUX_LAB_REC_WIT_TAC `s1compile:C->((A)sec)list->(byte list#C)option` relproof;;

(* split on loc_to_pc n1 n2 (filter_skip code), relating it to the         *)
(* unfiltered code by loc_to_pc_eq_NONE and loc_to_pc_eq_SOME              *)

let STACKPROPSAUX_LOC_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let fw = frees w in
  let t = find_term (fun t -> try let h,a = strip_comb t in
                                  fst(dest_const h) = "loc_to_pc" && length a = 3 &&
                                  subset (frees t) fw &&
                                  (try fst(dest_const(fst(strip_comb(el 2 a)))) = "filter_skip"
                                   with Failure _ -> false)
                              with Failure _ -> false) w in
  let h,a = strip_comb t in
  let n1 = el 0 a and n2 = el 1 a and cd = rand(el 2 a) in
  (CASES_ON t THEN CAKE_REWRITE_TAC[] THENL
    [MP_TAC(ISPECL [n1; n2; cd] loc_to_pc_eq_NONE) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[];
     FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs(concl th) = t then
       X_CHOOSE_THEN `pc':num` STRIP_ASSUME_TAC (MATCH_MP loc_to_pc_eq_SOME th)
       else failwith "") THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]]) g;;

(* case split on the first case expression whose scrutinee is a free      *)
(* variable of the goal                                                    *)

let STACKPROPSAUX_VARCASE_TAC : tactic = fun (asl,w as g) ->
  let fv = frees w in
  let tms = find_terms (fun t -> try let _,x,_ = dest_case_app t in is_var x && mem x fv
                                 with Failure _ -> false) w in
  match tms with
    [] -> failwith "VARCASE_TAC"
  | t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN CAKE_REWRITE_TAC[]) g;;

let STACKPROPSAUX_LAB_SPLIT_TAC : tactic =
  FIRST [STACKPROPSAUX_LOC_SPLIT_TAC; TOP_CASE_TAC THEN CAKE_REWRITE_TAC[]];;

let STACKPROPSAUX_LAB_LEAF_TAC (relproof:tactic) : tactic =
  REPEAT (CHANGED_TAC (TOP_CASE_TAC THEN CAKE_REWRITE_TAC[])) THEN
  FIRST [STACKPROPSAUX_LAB_FINAL_TAC THEN NO_TAC;
         REWRITE_TAC[inc_pc_def; lab_dec_clock_def; lab_upd_pc_def; lab_upd_reg_def] THEN
         SIMP STACKPROPSAUX_LAB_SIMPS THEN STACKPROPSAUX_LAB_REC_TAC relproof];;

let STACKPROPSAUX_LAB_LEAF2_TAC : tactic =
  REWRITE_TAC[get_pc_value_def; get_ret_Loc_def; lab_to_loc_def] THEN SIMP[] THEN
  STACKPAUX_TYPE_CASES_TAC `:(A)reg_imm` THEN
  REPEAT STACKPROPSAUX_VARCASE_TAC THEN SIMP[lab_reg_imm_def] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT (CHANGED_TAC STACKPROPSAUX_LAB_SPLIT_TAC) THEN
  FIRST [STACKPROPSAUX_LAB_FINAL_TAC THEN NO_TAC;
         REWRITE_TAC[inc_pc_def; lab_dec_clock_def; lab_upd_pc_def; lab_upd_reg_def] THEN
         SIMP STACKPROPSAUX_LAB_SIMPS THEN STACKPROPSAUX_LAB_REC_TAC ALL_TAC];;

(* the setup: induction, the clock-0 case, skipping the Skip lines of the  *)
(* unfiltered code, unfolding one step of both evaluations                 *)

let STACKPROPSAUX_FC_SETUP_TAC : tactic =
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `c:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`s1:(A,C,FFI)lab_state`; `t1:(A,C,FFI)lab_state`;
                       `res:machine_result`; `s2:(A,C,FFI)lab_state`] THEN
  REWRITE_TAC[lab_filterProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)) &&
    lhs (concl th) = `s1:(A,C,FFI)lab_state`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)) &&
    rhs (concl th) = `c:num`)) THEN
  SIMP[] THEN
  (ASM_CASES_TAC `lab_state_clock (t1:(A,C,FFI)lab_state) = 0` THENL
    [FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[lab_evaluate_def] o
       check STACKPROPSAUX_lab_is_eval) THEN SIMP[] THEN
     ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     MAP_EVERY EXISTS_TAC [`0`; `lab_state_clock_fupd (combin_K 0) (t1:(A,C,FFI)lab_state)`] THEN
     ONCE_REWRITE_TAC[lab_evaluate_def] THEN SIMP[] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN SIMP[];
     ALL_TAC]) THEN
  X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC (SPECL [`lab_state_pc (t1:(A,C,FFI)lab_state)`;
    `lab_state_code (t1:(A,C,FFI)lab_state)`] asm_fetch_aux_eq) THEN
  SUBGOAL_THEN `?k' (t2:(A,C,FFI)lab_state).
     lab_evaluate (lab_state_pc_fupd (combin_K (lab_state_pc t1 + k))
                   (lab_state_clock_fupd (combin_K (lab_state_clock t1 + k')) t1)) = (res,t2) /\
     lab_state_ffi (s2:(A,C,FFI)lab_state) = lab_state_ffi t2`
   (fun th -> X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state`
                STRIP_ASSUME_TAC) th THEN
              MAP_EVERY EXISTS_TAC [`k' + k`; `t2:(A,C,FFI)lab_state`] THEN
              ASM_REWRITE_TAC[] THEN
              MATCH_MP_TAC STACKPROPSAUX_skip_reduce THEN ASM_REWRITE_TAC[]) THEN
  SUBGOAL_THEN `!k'. asm_fetch (lab_state_pc_fupd (combin_K (lab_state_pc t1 + k))
                   (lab_state_clock_fupd (combin_K (lab_state_clock t1 + k'))
                     (t1:(A,C,FFI)lab_state))) =
                 asm_fetch_aux (adjust_pc (lab_state_pc t1) (lab_state_code t1))
                   (filter_skip (lab_state_code t1))` ASSUME_TAC THENL
   [SIMP[asm_fetch_def]; ALL_TAC] THEN
  SUBGOAL_THEN `adjust_pc ((lab_state_pc t1 + k) + 1) (lab_state_code t1) =
                adjust_pc (lab_state_pc (t1:(A,C,FFI)lab_state)) (lab_state_code t1) + 1 /\
                get_lab_after (adjust_pc (lab_state_pc t1) (lab_state_code t1))
                  (filter_skip (lab_state_code t1)) =
                get_lab_after (lab_state_pc t1 + k) (lab_state_code t1)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[adjust_pc_all_skips; get_lab_after_adjust]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[lab_evaluate_def] o
    check STACKPROPSAUX_lab_is_eval) THEN
  SIMP[asm_fetch_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o BINDER_CONV o LAND_CONV o LAND_CONV)
    [lab_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP[ADD_EQ_0] THEN
  CASES_ON `asm_fetch_aux (adjust_pc (lab_state_pc t1) (lab_state_code t1))
              (filter_skip (lab_state_code (t1:(A,C,FFI)lab_state)))` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];;

let STACKPROPSAUX_FC_INST_TAC : tactic =
  REWRITE_TAC[STACKPROPSAUX_asm_inst_frame] THEN SIMP[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [STACKPROPSAUX_LAB_FINAL_TAC;
    REWRITE_TAC[inc_pc_def; lab_dec_clock_def] THEN SIMP STACKPROPSAUX_LAB_SIMPS THEN
    STACKPROPSAUX_LAB_REC_TAC ALL_TAC];;

let STACKPROPSAUX_FC_JUMPREG_TAC : tactic =
  TOP_CASE_TAC THEN CAKE_REWRITE_TAC[] THENL [STACKPROPSAUX_LAB_FINAL_TAC; ALL_TAC] THEN
  STACKPROPSAUX_LOC_SPLIT_TAC THENL
   [STACKPROPSAUX_LAB_FINAL_TAC;
    REWRITE_TAC[lab_upd_pc_def; lab_dec_clock_def] THEN SIMP[] THEN
    STACKPROPSAUX_LAB_REC_TAC ALL_TAC];;
let STACKPROPSAUX_FC_SHAREMEM_TAC : tactic =
  REWRITE_TAC[ISPECL [`lab_state_pc (t1:(A,C,FFI)lab_state)`; `k:num`] ADD_SYM] THEN
  ONCE_REWRITE_TAC[ISPECL [`lab_state_clock (t1:(A,C,FFI)lab_state)`] ADD_SYM] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "share_mem_op" &&
               (try fst(dest_const(fst(strip_comb(rand t)))) = "lab_state_pc_fupd" &&
                    can (find_term (fun u -> try fst(dest_const u) = "filter_skip"
                                             with Failure _ -> false)) (rand t)
                with Failure _ -> false) with Failure _ -> false) w in
     (CASES_ON t THEN CAKE_REWRITE_TAC[]) g) THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_with_clock_self_lab] THEN
    FIRST_ASSUM(fun th -> try MP_TAC (MATCH_MP share_mem_op_NONE_filter_correct
      (CONJ (ASSUME `all_skips (lab_state_pc t1) (lab_state_code (t1:(A,C,FFI)lab_state)) k`)
            th))
      with Failure _ -> failwith "") THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
    EXISTS_TAC `lab_state_pc_fupd (combin_K (k + lab_state_pc t1)) (t1:(A,C,FFI)lab_state)` THEN
    SIMP[];
    STACKPROPSAUX_VARCASE_TAC THEN STACKPROPSAUX_VARCASE_TAC THENL
     [FIRST_ASSUM(fun th -> try MP_TAC (MATCH_MP share_mem_op_FFI_return_filter_correct
        (end_itlist CONJ
          [ASSUME `all_skips (lab_state_pc t1) (lab_state_code (t1:(A,C,FFI)lab_state)) k`;
           ASSUME `~(lab_state_clock (t1:(A,C,FFI)lab_state) = 0)`;
           ASSUME `lab_state_compile (t1:(A,C,FFI)lab_state) =
                   (\c p. s1compile c (filter_skip p))`;
           ASSUME `~lab_state_failed (t1:(A,C,FFI)lab_state)`; th]))
        with Failure _ -> failwith "") THEN
      DISCH_THEN(X_CHOOSE_THEN `s2':(A,C,FFI)lab_state` (fun th ->
        ASSUME_TAC(GEN `k':num` (last (CONJUNCTS (SPEC `k':num` th)))) THEN
        STRIP_ASSUME_TAC (SPEC `0` th))) THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[lab_filterProof_state_rel_def] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                             "lab_filterProof_state_rel" with Failure _ -> false)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `sc:C->((A)sec)list->(byte list#C)option`
        STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `y:(A,C,FFI)lab_state`)) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPAUX_share_mem_op_clock o
        check (fun th -> is_eq (concl th) &&
          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "share_mem_op" &&
               fst(dest_const(fst(strip_comb(rand(lhs(concl th)))))) = "lab_state_pc_fupd" &&
               not (can (find_term (fun u -> try fst(dest_const u) = "filter_skip"
                                             with Failure _ -> false)) (lhs(concl th))) &&
               not (can (find_term (fun u -> try fst(dest_const u) = "lab_state_clock_fupd"
                                             with Failure _ -> false)) (lhs(concl th)))
           with Failure _ -> false))) THEN
      RULE_ASSUM_TAC(SIMP_RULE[]) THEN SIMP[] THEN
      SUBGOAL_THEN `lab_state_clock (s2':(A,C,FFI)lab_state) =
                    lab_state_clock (t1:(A,C,FFI)lab_state) - 1`
        ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
          lhs (concl th) = `lab_state_clock (s2':(A,C,FFI)lab_state)`)) THEN SIMP[];
        ALL_TAC] THEN
      STACKPROPSAUX_LAB_REC_WIT_TAC `sc:C->((A)sec)list->(byte list#C)option` ALL_TAC;
      FIRST_ASSUM(fun th -> try MP_TAC (MATCH_MP share_mem_op_FFI_final_filter_correct
        (end_itlist CONJ
          [ASSUME `all_skips (lab_state_pc t1) (lab_state_code (t1:(A,C,FFI)lab_state)) k`;
           ASSUME `~(lab_state_clock (t1:(A,C,FFI)lab_state) = 0)`;
           ASSUME `lab_state_compile (t1:(A,C,FFI)lab_state) =
                   (\c p. s1compile c (filter_skip p))`;
           ASSUME `~lab_state_failed (t1:(A,C,FFI)lab_state)`; th]))
        with Failure _ -> failwith "") THEN
      DISCH_THEN(X_CHOOSE_THEN `s2':(A,C,FFI)lab_state` STRIP_ASSUME_TAC) THEN
      STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_with_clock_self_lab] THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      EXISTS_TAC `s2':(A,C,FFI)lab_state` THEN ASM_REWRITE_TAC[]]];;
let STACKPROPSAUX_FC_INSTALL_REL_TAC : tactic =
  REWRITE_TAC[STACKPROPSAUX_filter_skip_APPEND; filter_skip_def] THEN
  (fun (asl,w as g) ->
     let ths = mapfilter (fun (_,th) -> GSYM (MATCH_MP loc_to_pc_adjust_pc_append th)) asl in
     REWRITE_TAC ths g) THEN
  ASM_REWRITE_TAC[];;

let STACKPROPSAUX_FC_INSTALL_TAC : tactic =
  REWRITE_TAC[shift_seq_def] THEN
  CASES_ON `lab_state_compile_oracle (t1:(A,C,FFI)lab_state) 0` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CAKE_REWRITE_TAC[] THEN SIMP[STACKPROPSAUX_FST_filter_pair] THEN
  (fun (asl,w as g) ->
     let v = find (fun v -> type_of v = `:((A)sec)list`) (frees w) in
     (CASES_ON v THEN REWRITE_TAC[filter_skip_def] THEN CAKE_REWRITE_TAC[]) g) THENL
   [REPEAT (CHANGED_TAC STACKPROPSAUX_LAB_SPLIT_TAC) THEN STACKPROPSAUX_LAB_FINAL_TAC;
    (fun (asl,w as g) ->
       let v = find (fun v -> type_of v = `:(A)sec`) (frees w) in
       STRUCT_CASES_TAC (ISPEC v (cases "sec")) g) THEN
    REWRITE_TAC[filter_skip_def] THEN CAKE_REWRITE_TAC[] THEN
    REPEAT (CHANGED_TAC STACKPROPSAUX_LAB_SPLIT_TAC) THEN
    FIRST [STACKPROPSAUX_LAB_FINAL_TAC THEN NO_TAC;
           STACKPROPSAUX_LAB_REC_TAC STACKPROPSAUX_FC_INSTALL_REL_TAC]];;

(* HOL4: filter_correct *)

let filter_correct = prove
 (`!c (s1:(A,C,FFI)lab_state) t1 res s2.
     lab_state_clock s1 = c /\
     lab_evaluate s1 = (res,s2) /\ lab_filterProof_state_rel s1 t1 /\ ~lab_state_failed t1
     ==> ?k t2. lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock s1 + k)) t1) =
                (res,t2) /\
                lab_state_ffi s2 = lab_state_ffi t2`,
  STACKPROPSAUX_FC_SETUP_TAC THENL
   [STACKPROPSAUX_LAB_FINAL_TAC;
    CASES_ON `a:(A)line` THEN CAKE_REWRITE_TAC[] THENL
     [STACKPROPSAUX_LAB_FINAL_TAC;
      CASES_ON `a0:(A)asm_or_cbw` THEN CAKE_REWRITE_TAC[] THENL
       [CASES_ON `a':(A)asm` THEN CAKE_REWRITE_TAC[] THENL
         [STACKPROPSAUX_FC_INST_TAC;
          STACKPROPSAUX_LAB_FINAL_TAC;
          STACKPROPSAUX_LAB_FINAL_TAC;
          STACKPROPSAUX_LAB_FINAL_TAC;
          STACKPROPSAUX_FC_JUMPREG_TAC;
          STACKPROPSAUX_LAB_FINAL_TAC];
        STACKPROPSAUX_LAB_LEAF_TAC ALL_TAC;
        STACKPROPSAUX_FC_SHAREMEM_TAC];
      STACKPROPSAUX_VARCASE_TAC THENL
       [STACKPROPSAUX_LAB_LEAF2_TAC;
        STACKPROPSAUX_LAB_LEAF2_TAC;
        STACKPROPSAUX_LAB_LEAF2_TAC;
        STACKPROPSAUX_LAB_LEAF2_TAC;
        STACKPROPSAUX_LAB_LEAF2_TAC;
        STACKPROPSAUX_FC_INSTALL_TAC;
        STACKPROPSAUX_LAB_LEAF2_TAC]]]);;

(* local versions of labProps facts (labProps is not ported yet) and of    *)
(* the ffiProps fact that a returning call_FFI only appends io events      *)

let STACKPROPSAUX_lab_share_mem_op_io = prove
 (`!m r a (s:(A,C,FFI)lab_state) res s1.
     share_mem_op m r a s = SOME (res,s1) ==>
     isPREFIX (ffi_state_io_events (lab_state_ffi s))
              (ffi_state_io_events (lab_state_ffi s1))`,
  REPEAT GEN_TAC THEN CASES_ON `m:memop` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[inc_pc_def; lab_dec_clock_def; IS_PREFIX_REFL] THEN
  FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SEM2AUX_call_FFI_io_events));;

(* HOL4 labProps: share_mem_op_add_clock_same (its three cases in one)     *)

let STACKPROPSAUX_lab_share_mem_op_add_clock = prove
 (`!m r a k (s:(A,C,FFI)lab_state).
     ~(lab_state_clock s = 0) ==>
     share_mem_op m r a (lab_state_clock_fupd (combin_K (lab_state_clock s + k)) s) =
     OPTION_MAP (\(res,s1). (res,lab_state_clock_fupd (combin_K (lab_state_clock s1 + k)) s1))
                (share_mem_op m r a s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(lab_state_clock (s:(A,C,FFI)lab_state) + k) - 1 =
                (lab_state_clock s - 1) + k` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CASES_ON `m:memop` THEN CASES_ON `a:(A)addr` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def; lab_addr_def;
              inc_pc_def; lab_dec_clock_def] THEN
  SIMP[] THEN EVERY_CASE_TAC THEN SIMP[OPTION_MAP_DEF]);;

(* One step of lab_evaluate with any extra clock: the run either stops    *)
(* (result other than TimeOut) or continues from a state with a smaller    *)
(* clock; the io events only grow (local helper behind the labProps facts  *)
(* evaluate_ADD_clock, evaluate_io_events_mono and                         *)
(* evaluate_add_clock_io_events_mono below)                                *)

let STACKPROPSAUX_UNFOLD_EVAL_AT (st:term) : conv = fun t ->
  if is_comb t &&
     (try fst(dest_const(rator t)) = "lab_evaluate" with Failure _ -> false) &&
     rand t = st
  then REWR_CONV lab_evaluate_def t else failwith "UNFOLD_EVAL_AT";;

let STACKPROPSAUX_PAIRVAR_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let v = find (fun v -> try fst(dest_type (type_of v)) = "prod" with Failure _ -> false)
               (frees w) in
  (CASES_ON v THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
   CAKE_REWRITE_TAC[]) g;;

let STACKPROPSAUX_TYVAR_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let v = find (fun v -> let ty = type_of v in ty = `:lab` || ty = `:(A)reg_imm`) (frees w) in
  (CASES_ON v THEN REWRITE_TAC[lab_reg_imm_def; lab_to_loc_def] THEN SIMP[] THEN
   CAKE_REWRITE_TAC[]) g;;

let STACKPROPSAUX_SHMEM_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "share_mem_op" &&
                                  length (snd(strip_comb t)) = 4 && free_in t w
                              with Failure _ -> false) w in
  (CASES_ON t THEN REWRITE_TAC[OPTION_MAP_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   CAKE_REWRITE_TAC[]) g;;

let STACKPROPSAUX_STEP_SPLIT_TAC : tactic =
  FIRST [STACKPROPSAUX_PAIRVAR_SPLIT_TAC;
         STACKPROPSAUX_TYVAR_SPLIT_TAC;
         TOP_CASE_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
         CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CAKE_REWRITE_TAC[];
         STACKPROPSAUX_SHMEM_SPLIT_TAC];;

let STACKPROPSAUX_STEP_DEFS =
  [inc_pc_def; lab_dec_clock_def; lab_upd_pc_def; lab_upd_reg_def; asm_inst_consts;
   STACKPROPSAUX_asm_inst_reads];;

let STACKPROPSAUX_STEP_IO_TAC : tactic =
  SIMP (IS_PREFIX_REFL :: STACKPROPSAUX_STEP_DEFS) THEN
  TRY (FIRST_ASSUM(fun th ->
         FIRST [(fun g -> MATCH_ACCEPT_TAC (MATCH_MP SEM2AUX_call_FFI_io_events th) g);
                (fun g -> MATCH_ACCEPT_TAC (MATCH_MP STACKPROPSAUX_lab_share_mem_op_io th) g)]));;

let STACKPROPSAUX_STEP_FRAME_TAC : tactic =
  REWRITE_TAC[lab_state_component_equality] THEN SIMP STACKPROPSAUX_STEP_DEFS THEN
  ASM_ARITH_TAC;;

let STACKPROPSAUX_STEP_LEAF_TAC : tactic = fun (asl,w as g) ->
  let d2 = rand w in
  let _,b2 = strip_exists d2 in
  let kv,eq = dest_forall (last (conjuncts b2)) in
  let l = lhs eq in
  if is_pair l then
    let res0,st = dest_pair l in
    let st0 = vsubst [`0`,kv] st in
    (DISJ1_TAC THEN EXISTS_TAC res0 THEN EXISTS_TAC st0 THEN
     REWRITE_TAC[distinctness "machine_result"] THEN CONJ_TAC THENL
      [STACKPROPSAUX_STEP_IO_TAC;
       GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STACKPROPSAUX_STEP_FRAME_TAC]) g
  else
    let x0 = vsubst [`0`,kv] (rand l) in
    (DISJ2_TAC THEN EXISTS_TAC x0 THEN
     TRY (FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPAUX_share_mem_op_clock)) THEN
     REPEAT CONJ_TAC THENL
      [SIMP STACKPROPSAUX_STEP_DEFS THEN ASM_ARITH_TAC;
       STACKPROPSAUX_STEP_IO_TAC;
       GEN_TAC THEN AP_TERM_TAC THEN STACKPROPSAUX_STEP_FRAME_TAC]) g;;

let STACKPROPSAUX_lab_step = prove
 (`!s:(A,C,FFI)lab_state.
     ~(lab_state_clock s = 0) ==>
     (?res s1. ~(res = target_TimeOut) /\
               isPREFIX (ffi_state_io_events (lab_state_ffi s))
                        (ffi_state_io_events (lab_state_ffi s1)) /\
               !k. lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock s + k)) s) =
                   (res,lab_state_clock_fupd (combin_K (lab_state_clock s1 + k)) s1)) \/
     (?s1. lab_state_clock s1 < lab_state_clock s /\
           isPREFIX (ffi_state_io_events (lab_state_ffi s))
                    (ffi_state_io_events (lab_state_ffi s1)) /\
           !k. lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock s + k)) s) =
               lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock s1 + k)) s1))`,
  GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV (STACKPROPSAUX_UNFOLD_EVAL_AT
    `lab_state_clock_fupd (combin_K (lab_state_clock s + k)) (s:(A,C,FFI)lab_state)`)) THEN
  ASM_SIMP_TAC[ADD_EQ_0] THEN SIMP[asm_fetch_def] THEN
  REWRITE_TAC[STACKPROPSAUX_asm_inst_frame; get_pc_value_def; get_ret_Loc_def] THEN
  ASM_SIMP_TAC[STACKPROPSAUX_lab_share_mem_op_add_clock] THEN SIMP[] THEN
  REPEAT (CHANGED_TAC STACKPROPSAUX_STEP_SPLIT_TAC) THEN
  STACKPROPSAUX_STEP_LEAF_TAC);;

let STACKPROPSAUX_lab_clock_add_0 = prove
 (`lab_state_clock_fupd (combin_K (lab_state_clock s + 0)) (s:(A,C,FFI)lab_state) = s`,
  REWRITE_TAC[ADD_CLAUSES; STACKPROPSAUX_with_clock_self_lab]);;

(* a run with extra clock k: the same result unless the run timed out, in  *)
(* which case it goes on from the state where it timed out                 *)

let STACKPROPSAUX_lab_evaluate_add_clock_gen = prove
 (`!k (s:(A,C,FFI)lab_state) res r.
     lab_evaluate s = (res,r)
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock s + k)) s) =
         if res = target_TimeOut
         then lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock r + k)) r)
         else (res,lab_state_clock_fupd (combin_K (lab_state_clock r + k)) r)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!n (s:(A,C,FFI)lab_state) res r.
      lab_state_clock s = n /\ lab_evaluate s = (res,r)
      ==> lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock s + k)) s) =
          if res = target_TimeOut
          then lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock r + k)) r)
          else (res,lab_state_clock_fupd (combin_K (lab_state_clock r + k)) r)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`s:(A,C,FFI)lab_state`; `res:machine_result`;
                       `r:(A,C,FFI)lab_state`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `n:num`)) THEN
  ASM_CASES_TAC `lab_state_clock (s:(A,C,FFI)lab_state) = 0` THENL
   [UNDISCH_TAC `lab_evaluate (s:(A,C,FFI)lab_state) = (res,r)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lab_evaluate_def] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:(A,C,FFI)lab_state` STACKPROPSAUX_lab_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `0` th) THEN ASSUME_TAC th) THEN
    REWRITE_TAC[STACKPROPSAUX_lab_clock_add_0] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `0` th) THEN ASSUME_TAC th) THEN
    REWRITE_TAC[STACKPROPSAUX_lab_clock_add_0] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    USE_THEN "ih" (MP_TAC o SPEC `lab_state_clock (s1:(A,C,FFI)lab_state)`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`s1:(A,C,FFI)lab_state`; `res:machine_result`;
                               `r:(A,C,FFI)lab_state`]) THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 labProps: evaluate_ADD_clock *)

let STACKPROPSAUX_lab_evaluate_ADD_clock = prove
 (`!(s:(A,C,FFI)lab_state) res r k.
     lab_evaluate s = (res,r) /\ ~(res = target_TimeOut)
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock s + k)) s) =
         (res,lab_state_clock_fupd (combin_K (lab_state_clock r + k)) r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP
    (ONCE_REWRITE_RULE[SWAP_FORALL_THM] (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
      STACKPROPSAUX_lab_evaluate_add_clock_gen))) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 labProps: evaluate_io_events_mono *)

let STACKPROPSAUX_lab_evaluate_io_events_mono = prove
 (`!(s1:(A,C,FFI)lab_state) r s2.
     lab_evaluate s1 = (r,s2)
     ==> isPREFIX (ffi_state_io_events (lab_state_ffi s1))
                  (ffi_state_io_events (lab_state_ffi s2))`,
  SUBGOAL_THEN
   `!n (s1:(A,C,FFI)lab_state) r s2.
      lab_state_clock s1 = n /\ lab_evaluate s1 = (r,s2)
      ==> isPREFIX (ffi_state_io_events (lab_state_ffi s1))
                   (ffi_state_io_events (lab_state_ffi s2))`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`s:(A,C,FFI)lab_state`; `res:machine_result`;
                       `r:(A,C,FFI)lab_state`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `n:num`)) THEN
  ASM_CASES_TAC `lab_state_clock (s:(A,C,FFI)lab_state) = 0` THENL
   [UNDISCH_TAC `lab_evaluate (s:(A,C,FFI)lab_state) = (res,r)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lab_evaluate_def] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[IS_PREFIX_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:(A,C,FFI)lab_state` STACKPROPSAUX_lab_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[STACKPROPSAUX_lab_clock_add_0] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[STACKPROPSAUX_lab_clock_add_0] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    USE_THEN "ih" (MP_TAC o SPEC `lab_state_clock (s1:(A,C,FFI)lab_state)`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`s1:(A,C,FFI)lab_state`; `res:machine_result`;
                               `r:(A,C,FFI)lab_state`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[isPREFIX_TRANS]]);;

(* HOL4 labProps: evaluate_add_clock_io_events_mono *)

let STACKPROPSAUX_lab_evaluate_add_clock_io_events_mono = prove
 (`!extra (s:(A,C,FFI)lab_state).
     isPREFIX (ffi_state_io_events (lab_state_ffi (SND (lab_evaluate s))))
              (ffi_state_io_events (lab_state_ffi (SND (lab_evaluate
                 (lab_state_clock_fupd (combin_K (lab_state_clock s + extra)) s)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `lab_evaluate (s:(A,C,FFI)lab_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res:machine_result`; `r:(A,C,FFI)lab_state`] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SPEC `extra:num` o MATCH_MP
    (ONCE_REWRITE_RULE[SWAP_FORALL_THM] (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
      STACKPROPSAUX_lab_evaluate_add_clock_gen))) THEN
  ASM_REWRITE_TAC[SND] THEN COND_CASES_TAC THEN SIMP[IS_PREFIX_REFL] THEN
  MP_TAC(ISPEC `lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock r + extra))
                                (r:(A,C,FFI)lab_state))` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`res2:machine_result`; `r2:(A,C,FFI)lab_state`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; SND] THEN
    MP_TAC(MATCH_MP STACKPROPSAUX_lab_evaluate_io_events_mono th)) THEN
  SIMP[]);;

(* the semantics of t is the one of s when every run of s is simulated by  *)
(* a run of t with extra clock, with the same result and ffi               *)

let STACKPROPSAUX_lab_io_mono_le = prove
 (`!(x:(A,C,FFI)lab_state) k1 k2.
     k1 <= k2 ==>
     isPREFIX
       (ffi_state_io_events (lab_state_ffi
          (SND (lab_evaluate (lab_state_clock_fupd (combin_K k1) x)))))
       (ffi_state_io_events (lab_state_ffi
          (SND (lab_evaluate (lab_state_clock_fupd (combin_K k2) x)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:num`; `lab_state_clock_fupd (combin_K k1) (x:(A,C,FFI)lab_state)`]
          STACKPROPSAUX_lab_evaluate_add_clock_io_events_mono) THEN
  SIMP[]);;

let STACKPROPSAUX_lab_io_chain = prove
 (`!x:(A,C,FFI)lab_state.
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (lab_state_ffi
          (SND (lab_evaluate (lab_state_clock_fupd (combin_K k) x)))))) (:num))`,
  GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[STACKPROPSAUX_lab_io_mono_le; LE_CASES]);;

let STACKPROPSAUX_lab_option_CASE_cong = prove
 (`!(x:(behaviour)option) (a:behaviour) b (f:behaviour->behaviour).
     (x = NONE ==> a = b) ==> option_CASE x a f = option_CASE x b f`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:(behaviour)option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT]);;

let STACKPROPSAUX_lab_semantics_sim = prove
 (`!(s:(A,C,FFI)lab_state) (t:(A,C,FFI)lab_state).
     (!k r s1. lab_evaluate (lab_state_clock_fupd (combin_K k) s) = (r,s1)
               ==> ?ck t1. lab_evaluate (lab_state_clock_fupd (combin_K (k + ck)) t) = (r,t1) /\
                           lab_state_ffi t1 = lab_state_ffi s1)
     ==> lab_semantics t = lab_semantics s`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "sim") THEN
  SUBGOAL_THEN
   `!k r (t1:(A,C,FFI)lab_state).
      lab_evaluate (lab_state_clock_fupd (combin_K k) t) = (r,t1) /\ ~(r = target_TimeOut)
      ==> ?s1. lab_evaluate (lab_state_clock_fupd (combin_K k) (s:(A,C,FFI)lab_state)) = (r,s1) /\
               lab_state_ffi t1 = lab_state_ffi s1`
   (LABEL_TAC "back") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPEC `lab_evaluate (lab_state_clock_fupd (combin_K k) (s:(A,C,FFI)lab_state))`
             PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r0:machine_result`; `s0:(A,C,FFI)lab_state`] THEN DISCH_TAC THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `r0:machine_result`;
                                    `s0:(A,C,FFI)lab_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`lab_state_clock_fupd (combin_K k) (t:(A,C,FFI)lab_state)`; `r:machine_result`;
                   `t1:(A,C,FFI)lab_state`; `ck:num`] STACKPROPSAUX_lab_evaluate_ADD_clock) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP[] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rand (concl th) = `lab_state_ffi (s0:(A,C,FFI)lab_state)`)) THEN
    SIMP[];
    ALL_TAC] THEN
  REWRITE_TAC[lab_semantics_def] THEN
  SUBGOAL_THEN
   `(?k. FST (lab_evaluate (lab_state_clock_fupd (combin_K k) (t:(A,C,FFI)lab_state))) =
         target_Error) <=>
    (?k. FST (lab_evaluate (lab_state_clock_fupd (combin_K k) (s:(A,C,FFI)lab_state))) =
         target_Error)`
   SUBST1_TAC THENL
   [EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THENL
     [MP_TAC(ISPEC `lab_evaluate (lab_state_clock_fupd (combin_K k) (t:(A,C,FFI)lab_state))`
               PAIR_SURJECTIVE) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`r:machine_result`; `t1:(A,C,FFI)lab_state`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `r = target_Error` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `FST (lab_evaluate (lab_state_clock_fupd (combin_K k)
                       (t:(A,C,FFI)lab_state))) = target_Error` THEN
        ASM_REWRITE_TAC[FST];
        ALL_TAC] THEN
      USE_THEN "back" (MP_TAC o SPECL [`k:num`; `target_Error`;
                                       `t1:(A,C,FFI)lab_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[distinctness "machine_result"]; ALL_TAC] THEN
      STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[FST];
      MP_TAC(ISPEC `lab_evaluate (lab_state_clock_fupd (combin_K k) (s:(A,C,FFI)lab_state))`
               PAIR_SURJECTIVE) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`r:machine_result`; `s1:(A,C,FFI)lab_state`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `r = target_Error` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `FST (lab_evaluate (lab_state_clock_fupd (combin_K k)
                       (s:(A,C,FFI)lab_state))) = target_Error` THEN
        ASM_REWRITE_TAC[FST];
        ALL_TAC] THEN
      USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `target_Error`;
                                      `s1:(A,C,FFI)lab_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN EXISTS_TAC `k + ck:num` THEN ASM_REWRITE_TAC[FST]];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\res. ?k (t1:(A,C,FFI)lab_state) outcome.
       lab_evaluate (lab_state_clock_fupd (combin_K k) t) = (target_Halt outcome,t1) /\
       res = Terminate outcome (ffi_state_io_events (lab_state_ffi t1))) =
    (\res. ?k (s1:(A,C,FFI)lab_state) outcome.
       lab_evaluate (lab_state_clock_fupd (combin_K k) s) = (target_Halt outcome,s1) /\
       res = Terminate outcome (ffi_state_io_events (lab_state_ffi s1)))`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `res:behaviour` THEN EQ_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `x1:(A,C,FFI)lab_state`; `outcome:outcome`] THEN
    STRIP_TAC THENL
     [USE_THEN "back" (MP_TAC o SPECL [`k:num`; `target_Halt outcome`;
                                       `x1:(A,C,FFI)lab_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[distinctness "machine_result"]; ALL_TAC] THEN
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)lab_state`; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `target_Halt outcome`;
                                      `x1:(A,C,FFI)lab_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`k + ck:num`; `t1:(A,C,FFI)lab_state`; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC STACKPROPSAUX_lab_option_CASE_cong THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REWRITE_TAC[STACKPROPSAUX_lab_io_chain] THEN
  REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `lab_evaluate (lab_state_clock_fupd (combin_K k) (s:(A,C,FFI)lab_state))`
           PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:machine_result`; `s1:(A,C,FFI)lab_state`] THEN DISCH_TAC THEN
  USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `r:machine_result`; `s1:(A,C,FFI)lab_state`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN STRIP_TAC THENL
   [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
    MP_TAC(ISPECL [`t:(A,C,FFI)lab_state`; `k:num`; `k + ck:num`]
             STACKPROPSAUX_lab_io_mono_le) THEN
    ASM_REWRITE_TAC[LE_ADD; SND];
    EXISTS_TAC `k + ck:num` THEN
    ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL; SND]]);;

(* HOL4: state_rel_IMP_sem_EQ_sem (local in HOL4) *)

let state_rel_IMP_sem_EQ_sem = prove
 (`!(s:(A,C,FFI)lab_state) t.
     lab_filterProof_state_rel s t ==> lab_semantics s = lab_semantics t`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC STACKPROPSAUX_lab_semantics_sim THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `r:machine_result`; `s1:(A,C,FFI)lab_state`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `lab_state_clock_fupd (combin_K k) (s:(A,C,FFI)lab_state)`;
                 `lab_state_clock_fupd (combin_K k) (t:(A,C,FFI)lab_state)`;
                 `r:machine_result`; `s1:(A,C,FFI)lab_state`] filter_correct) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `lab_filterProof_state_rel (s:(A,C,FFI)lab_state) t` THEN
    REWRITE_TAC[lab_filterProof_state_rel_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `sc:C->((A)sec)list->(byte list#C)option`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN
    EXISTS_TAC `sc:C->((A)sec)list->(byte list#C)option` THEN SIMP[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rand (concl th) = `r:machine_result,(t2:(A,C,FFI)lab_state)`)) THEN
  SIMP[]);;

(* HOL4: filter_skip_semantics *)

let filter_skip_semantics = prove
 (`!(s:(A,C,FFI)lab_state) t.
     lab_state_pc t = 0 /\ ~lab_state_failed t /\
     (?scompile.
        s = lab_state_code_fupd (combin_K (filter_skip (lab_state_code t)))
              (lab_state_compile_oracle_fupd
                 (combin_K ((\(a,b). (a,filter_skip b)) o lab_state_compile_oracle t))
              (lab_state_compile_fupd (combin_K scompile) t)) /\
        lab_state_compile t = (\c p. scompile c (filter_skip p))) /\
     ~lab_state_failed t
     ==> lab_semantics s = lab_semantics t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC state_rel_IMP_sem_EQ_sem THEN
  ASM_REWRITE_TAC[lab_filterProof_state_rel_def; STACKPROPSAUX_adjust_pc_thms] THEN
  EXISTS_TAC `scompile:C->((A)sec)list->(byte list#C)option` THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  REWRITE_TAC[lab_state_component_equality] THEN SIMP[]);;

(* HOL4: sec_ends_with_label_filter_skip. sec_ends_with_label is a          *)
(* definition of labProps (not ported yet):                                 *)
(*   sec_ends_with_label (Section _ ls) <=> ~NULL ls /\ is_Label (LAST ls)  *)
(* it is written out here as a match.                                       *)

let STACKPROPSAUX_FILTER_ends_with_label = prove
 (`!ls:((A)line)list.
     ~NULL ls /\ is_Label (LAST ls)
     ==> ~NULL (FILTER not_skip ls) /\ is_Label (LAST (FILTER not_skip ls))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; LAST; FILTER] THEN
  ASM_CASES_TAC `t:((A)line)list = []` THEN ASM_REWRITE_TAC[FILTER] THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[is_Label_not_skip; NULL; LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `~NULL (t:((A)line)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(t:((A)line)list = [])` THEN
    STRUCT_CASES_TAC(ISPEC `t:((A)line)list` list_CASES) THEN REWRITE_TAC[NULL; NOT_CONS_NIL];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(FILTER not_skip t = []:((A)line)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~NULL (FILTER not_skip (t:((A)line)list))` THEN
    SPEC_TAC(`FILTER not_skip (t:((A)line)list)`,`l:((A)line)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NULL; LAST]);;

let sec_ends_with_label_filter_skip = prove
 (CASE_TERM
  `!code:((A)sec)list.
     ALL (\s. match s with Section _ ls -> ~NULL ls /\ is_Label (LAST ls)) code
     ==> ALL (\s. match s with Section _ ls -> ~NULL ls /\ is_Label (LAST ls))
             (filter_skip code)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def; ALL] THEN
  STRUCT_CASES_TAC(ISPEC `h:(A)sec` (cases "sec")) THEN
  REWRITE_TAC[filter_skip_def; ALL] THEN CAKE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[STACKPROPSAUX_FILTER_ends_with_label]);;
