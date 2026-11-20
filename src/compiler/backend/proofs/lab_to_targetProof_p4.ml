(* ========================================================================= *)
(* lab_to_targetProof_p4: part 4 of 4 (HOL4 lines 9357-11303) of            *)
(* lab_to_targetProof, port of HOL4                                          *)
(* compiler/backend/proofs/lab_to_targetProofScript.sml (CakeML v3479).      *)
(* Correctness proof for lab_to_target: machine_sem_EQ_sem, the initial      *)
(* state make_init, the shared-memory info of the encoded code, and          *)
(* semantics_compile.  Helpers of this part are named LTTP4AUX_.             *)
(* ========================================================================= *)

needs "compiler/backend/proofs/lab_to_targetProof_p3.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 4: HOL4 lines 9357-11303 ===== *)

(* HOL4 line 9357 *)
let init_ok_def = cake_def
  `init_ok (mc_conf:(A,B,C)machine_config,p:A word)
     (s:(A,lab_to_target_config,FFI)lab_state) (ms:B) <=>
     ?code2 labs t1.
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s t1 ms /\
       oracle_tie mc_conf ms s`;;

(* HOL4 line 9364 *)
let LTTP4AUX_sim = prove
 (`!(mc_conf:(A,B,C)machine_config) p (ms:B) (s1:(A,lab_to_target_config,FFI)lab_state) k
     res s2.
     encoder_correct (machine_config_target mc_conf) /\ init_ok (mc_conf,p) s1 ms /\
     lab_evaluate (lab_state_clock_fupd (K k) s1) = (res,s2) /\ ~(res = target_Error)
     ==> ?k' ms2. target_evaluate mc_conf (lab_state_ffi s1) (k + k') ms =
                  (res,ms2,lab_state_ffi s2)`,
  REWRITE_TAC[init_ok_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lab_state_clock_fupd (K k) (s1:(A,lab_to_target_config,FFI)lab_state)`;
                 `res:machine_result`; `mc_conf:(A,B,C)machine_config`;
                 `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
                 `labs:(num spt)spt`; `t1:(A)asm_state`; `ms:B`; `p:A word`]
         lab_to_targetProof_compile_correct) THEN
  ASM_SIMP_TAC[oracle_tie_clock; lab_to_targetProof_state_rel_clock] THEN
  SIMP[]);;

let LTTP4AUX_machine_sem_Halt = prove
 (`!(mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k o0 ms0 st0.
     target_evaluate mc_conf ffi k ms = (target_Halt o0,ms0,st0)
     ==> machine_sem mc_conf ffi ms = {Terminate o0 (ffi_state_io_events st0)}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING; IN] THEN
  X_GEN_TAC `b:behaviour` THEN CASES_ON `b:behaviour` THEN
  REWRITE_TAC[machine_sem_def; distinctness "behaviour"; injectivity "behaviour"] THENL
   [DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    REWRITE_TAC[distinctness "machine_result"];
    EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ffi:(FFI)ffi_state`; `k:num`; `ms:B`;
        `target_Halt o0`; `ms0:B`; `st0:(FFI)ffi_state`; `k':num`; `target_Halt a0`;
        `ms':B`; `st':(FFI)ffi_state`] evaluate_ignore_clocks) THEN
      ASM_REWRITE_TAC[distinctness "machine_result"; PAIR_EQ; injectivity "machine_result"] THEN
      ASM_MESON_TAC[];
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`k:num`; `ms0:B`; `st0:(FFI)ffi_state`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `k':num` THEN
    SUBGOAL_THEN `?r ms1 st1. target_evaluate (mc_conf:(A,B,C)machine_config)
                    (ffi:(FFI)ffi_state) k' (ms:B) = (r,ms1,st1)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ffi:(FFI)ffi_state`; `k:num`; `ms:B`;
      `target_Halt o0`; `ms0:B`; `st0:(FFI)ffi_state`; `k':num`; `target_Error`;
      `ms1:B`; `st1:(FFI)ffi_state`] evaluate_ignore_clocks) THEN
    ASM_REWRITE_TAC[distinctness "machine_result"; PAIR_EQ]]);;

let LTTP4AUX_lprefix_chain_mono = prove
 (`!f:num->A list. (!k1 k2. k1 <= k2 ==> f k1 <<= f k2)
     ==> lprefix_chain (IMAGE (\k. llist_fromList (f k)) (:num))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\k. llist_fromList ((f:num->A list) k)) (:num) =
                IMAGE llist_fromList (IMAGE f (:num))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IN_IMAGE; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_CASES]);;

let LTTP4AUX_equiv_chain = prove
 (`!(f:num->A list) g.
     (!k1 k2. k1 <= k2 ==> f k1 <<= f k2) /\ (!k1 k2. k1 <= k2 ==> g k1 <<= g k2) /\
     (!k. ?k'. g k = f (k + k'))
     ==> equiv_lprefix_chain (IMAGE (\k. llist_fromList (f k)) (:num))
                             (IMAGE (\k. llist_fromList (g k)) (:num))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[equiv_lprefix_chain_thm; LTTP4AUX_lprefix_chain_mono] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`ll:A llist`; `n:num`; `x:A`; `j:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `k':num` o SPEC `j:num`) THEN
    SUBGOAL_THEN `(f:num->A list) j <<= f (j + k')` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IS_PREFIX_APPEND] THEN DISCH_THEN(X_CHOOSE_TAC `l:A list`) THEN
    REWRITE_TAC[LNTH_fromList] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`llist_fromList ((g:num->A list) j)`; `j:num`] THEN
    ASM_REWRITE_TAC[LNTH_fromList; LENGTH_APPEND] THEN
    ASM_SIMP_TAC[EL_APPEND1; ARITH_RULE `n < a ==> n < a + b:num`];
    FIRST_X_ASSUM(X_CHOOSE_TAC `k':num` o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`llist_fromList ((f:num->A list) (j + k'))`; `j + k':num`] THEN
    ASM_REWRITE_TAC[]]);;

let LTTP4AUX_lub_equiv = prove
 (`!ls1 ls2:(A llist)->bool.
     equiv_lprefix_chain ls1 ls2
     ==> lprefix_chain ls1 ==> lprefix_chain ls2
     ==> !a. lprefix_lub ls1 a <=> a = build_lprefix_lub ls2`,
  MESON_TAC[lprefix_lub_equiv_chain; build_prefix_lub_intro]);;

let LTTP4AUX_machine_sem_Diverge = prove
 (`!(mc_conf:(A,B,C)machine_config) p (ms:B) (s1:(A,lab_to_target_config,FFI)lab_state).
     encoder_correct (machine_config_target mc_conf) /\ init_ok (mc_conf,p) s1 ms /\
     (!k. FST (lab_evaluate (lab_state_clock_fupd (K k) s1)) = target_TimeOut)
     ==> machine_sem mc_conf (lab_state_ffi s1) ms =
         {Diverge (build_lprefix_lub
            (IMAGE (\k. llist_fromList (ffi_state_io_events
               (lab_state_ffi (SND (lab_evaluate (lab_state_clock_fupd (K k) s1)))))) (:num)))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `g = \k. ffi_state_io_events
     (lab_state_ffi (SND (lab_evaluate (lab_state_clock_fupd (K k)
        (s1:(A,lab_to_target_config,FFI)lab_state)))))` THEN
  ABBREV_TAC `f = \k. ffi_state_io_events (SND (SND (target_evaluate
     (mc_conf:(A,B,C)machine_config) (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state))
     k (ms:B))))` THEN
  SUBGOAL_THEN `!k. ?k' ms2. target_evaluate (mc_conf:(A,B,C)machine_config)
      (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)) (k + k') (ms:B) =
      (target_TimeOut,ms2,lab_state_ffi (SND (lab_evaluate (lab_state_clock_fupd (K k) s1))))`
    (LABEL_TAC "sim") THENL
   [GEN_TAC THEN MATCH_MP_TAC LTTP4AUX_sim THEN EXISTS_TAC `p:A word` THEN
    ASM_REWRITE_TAC[distinctness "machine_result"] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
    MESON_TAC[PAIR; FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. FST (target_evaluate (mc_conf:(A,B,C)machine_config)
      (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)) k (ms:B)) = target_TimeOut`
    (LABEL_TAC "to") THENL
   [GEN_TAC THEN USE_THEN "sim" (X_CHOOSE_THEN `k':num` (X_CHOOSE_TAC `ms2:B`) o SPEC `k:num`) THEN
    SUBGOAL_THEN `?r ms1 st1. target_evaluate (mc_conf:(A,B,C)machine_config)
      (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)) k (ms:B) = (r,ms1,st1)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CCONTR_TAC THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`;
      `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `k:num`; `ms:B`; `k':num`;
      `r:machine_result`; `ms1:B`; `st1:(FFI)ffi_state`] target_evaluate_add_clock) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ?k'. (g:num->io_event list) k = f (k + k')` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "sim" (X_CHOOSE_THEN `k':num` (X_CHOOSE_TAC `ms2:B`) o SPEC `k:num`) THEN
    EXISTS_TAC `k':num` THEN EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k1 k2. k1 <= k2 ==> (f:num->io_event list) k1 <<= f k2` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[target_evaluate_add_clock_io_events_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `!k1 k2. k1 <= k2 ==> (g:num->io_event list) k1 <<= g k2` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    MP_TAC(ISPECL [`d:num`;
                   `lab_state_clock_fupd (K k1) (s1:(A,lab_to_target_config,FFI)lab_state)`]
                  (GEN `extra:num` lab_evaluate_add_clock_io_events_mono)) THEN
    SIMP[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f:num->io_event list` LTTP4AUX_lprefix_chain_mono) THEN
  MP_TAC(ISPEC `g:num->io_event list` LTTP4AUX_lprefix_chain_mono) THEN
  MP_TAC(ISPECL [`f:num->io_event list`; `g:num->io_event list`] LTTP4AUX_equiv_chain) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN REPEAT DISCH_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING; IN] THEN
  X_GEN_TAC `b:behaviour` THEN CASES_ON `b:behaviour` THEN
  REWRITE_TAC[machine_sem_def; distinctness "behaviour"; injectivity "behaviour"] THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP4AUX_lub_equiv) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[TAUT `(a /\ b <=> b) <=> (b ==> a)`] THEN DISCH_TAC THEN
    X_GEN_TAC `k:num` THEN USE_THEN "to" (MP_TAC o SPEC `k:num`) THEN MESON_TAC[PAIR; FST];
    REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    USE_THEN "to" (MP_TAC o SPEC `k:num`) THEN MESON_TAC[FST; distinctness "machine_result"];
    REWRITE_TAC[NOT_EXISTS_THM] THEN GEN_TAC THEN
    USE_THEN "to" (fun th -> REWRITE_TAC[th; distinctness "machine_result"])]);;

let LTTP4AUX_some_cases = prove
 (`!P:A->bool. ((some) P = NONE /\ (!x. ~P x)) \/ (?x. (some) P = SOME x /\ P x)`,
  GEN_TAC THEN REWRITE_TAC[some_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN EXISTS_TAC `@x:A. P x` THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let machine_sem_EQ_sem = prove
 (`!(mc_conf:(A,B,C)machine_config) p (ms:B) (s1:(A,lab_to_target_config,FFI)lab_state).
     encoder_correct (machine_config_target mc_conf) /\
     init_ok (mc_conf,p) s1 ms /\ ~(lab_semantics s1 = Fail)
     ==> machine_sem mc_conf (lab_state_ffi s1) ms = {lab_semantics s1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(lab_semantics (s1:(A,lab_to_target_config,FFI)lab_state) = Fail)` THEN
  REWRITE_TAC[lab_semantics_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  W(fun (asl,w) ->
      let tm = find_term (fun t -> is_comb t && is_const(rator t) &&
                                   fst(dest_const(rator t)) = "some") w in
      MP_TAC(ISPEC (rand tm) LTTP4AUX_some_cases)) THEN
  BETA_TAC THEN DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN TRY DISCH_TAC THENL
   [MATCH_MP_TAC LTTP4AUX_machine_sem_Diverge THEN EXISTS_TAC `p:A word` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `?r t. lab_evaluate (lab_state_clock_fupd (K k)
                    (s1:(A,lab_to_target_config,FFI)lab_state)) = (r,t)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `r:machine_result` (cases "machine_result")) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (fun th ->
      if is_exists(concl th) then CHOOSE_THEN SUBST_ALL_TAC th else SUBST_ALL_TAC th)) THEN
    REWRITE_TAC[distinctness "machine_result"] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `Terminate a (ffi_state_io_events
        (lab_state_ffi (t:(A,lab_to_target_config,FFI)lab_state)))` o check (is_forall o concl))
            THEN
      REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `t:(A,lab_to_target_config,FFI)lab_state`; `a:outcome`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        is_forall(concl th) && is_neg(snd(dest_forall(concl th))) &&
        is_eq(dest_neg(snd(dest_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `p:A word`; `ms:B`;
      `s1:(A,lab_to_target_config,FFI)lab_state`; `k:num`; `target_Halt outcome`;
      `t:(A,lab_to_target_config,FFI)lab_state`] LTTP4AUX_sim) THEN
    ASM_REWRITE_TAC[distinctness "machine_result"] THEN
    STRIP_TAC THEN MATCH_MP_TAC LTTP4AUX_machine_sem_Halt THEN
    MAP_EVERY EXISTS_TAC [`k + k':num`; `ms2:B`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 9535 *)
let set_bytes_def = cake_def
  `(set_bytes (a:A word) be ([]:byte list) = word 0:A word) /\
   (set_bytes a be (CONS b bs) = set_byte a b (set_bytes (word_add a (word 1)) be bs) be)`;;

let set_bytes_ind = cake_ind "set_bytes";;

(* HOL4 line 9540 *)
let make_word_def = cake_def
  `make_word be (m:A word->byte) (a:A word) =
     if dimindex (:A) = 32 then
       wl_Word (set_bytes a be [m a; m (word_add a (word 1)); m (word_add a (word 2));
                                m (word_add a (word 3))])
     else
       wl_Word (set_bytes a be [m a; m (word_add a (word 1)); m (word_add a (word 2));
                                m (word_add a (word 3)); m (word_add a (word 4));
                                m (word_add a (word 5)); m (word_add a (word 6));
                                m (word_add a (word 7))])`;;

(* HOL4 line 9549 (the record literal in the field order of lab_state; the *)
(* code buffer <|position; buffer; space_left|> is buffer_REC)               *)
let lab_to_targetProof_make_init_def = cake_def
  `lab_to_targetProof_make_init (mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
     (t:(A)asm_state) (m:A word->(A)word_loc) dm sdm (ms:B) (code:((A)sec)list)
     (comp:D->((A)sec)list->(byte list#D)option) (cbpos:A word) cbspace
     (coracle:num->D#((A)sec)list) =
     lab_state_REC
       (\k. wl_Word (asm_state_regs t k))
       (asm_state_fp_regs t)
       m
       dm
       sdm
       0
       (asm_config_big_endian (target_config (machine_config_target mc_conf)))
       ffi
       (target_io_regs mc_conf ffi ms)
       (target_cc_regs mc_conf ffi ms)
       (target_io_fp_regs mc_conf ffi ms)
       (target_cc_fp_regs mc_conf ffi ms)
       code
       comp
       coracle
       (buffer_REC cbpos [] cbspace)
       0
       F
       (machine_config_ptr_reg mc_conf)
       (machine_config_len_reg mc_conf)
       (machine_config_ptr2_reg mc_conf)
       (machine_config_len2_reg mc_conf)
       (match asm_config_link_reg (target_config (machine_config_target mc_conf)) with
          SOME n -> n
        | _ -> 0)`;;

(* HOL4 line 9579 *)
let oracle_tie_make_init = prove
 (`!(mc_conf:(A,B,C)machine_config) (ms:B) (ffi:(FFI)ffi_state) (t:(A)asm_state) m dm sdm
     (code:((A)sec)list) (cmp:D->((A)sec)list->(byte list#D)option) cbpos cbspace coracle.
     oracle_tie mc_conf ms
       (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code cmp cbpos cbspace coracle)`,
  REWRITE_TAC[oracle_tie_def; lab_to_targetProof_make_init_def] THEN SIMP[]);;

(* HOL4 line 9586: val IMP_LEMMA = METIS_PROVE [] (a ==> b) ==> (b ==> c) *)
(* ==> (a ==> c) (a propositional tautology for the proofs)                *)
let lab_to_targetProof_IMP_LEMMA = prove
 (`!a b c. (a ==> b) ==> (b ==> c) ==> (a ==> c)`,
  MESON_TAC[]);;

(* HOL4 line 9588 *)
let compiler_oracle_ok_def = cake_def
  `compiler_oracle_ok (coracle:num->lab_to_target_config#((A)sec)list) init_labs init_pos
     (c:(A)asm_config) ffis <=>
     (!k:num. let (cfg,code) = coracle k in
              lab_to_targetProof_good_code c (lab_to_target_config_labels cfg) code /\
              no_share_mem_inst code) /\
     (let (cfg,code) = coracle 0 in
      lab_to_target_config_labels cfg = init_labs /\
      lab_to_target_config_pos cfg = init_pos /\
      lab_to_target_config_ffi_names cfg = SOME ffis)`;;

(* HOL4 line 9602 *)
let mc_conf_ok_def = cake_def
  `mc_conf_ok (mc_conf:(A,B,C)machine_config) <=>
     good_dimindex (:A) /\
     encoder_correct (machine_config_target mc_conf) /\
     reg_ok (machine_config_ptr_reg mc_conf) (target_config (machine_config_target mc_conf)) /\
     reg_ok (machine_config_len_reg mc_conf) (target_config (machine_config_target mc_conf)) /\
     reg_ok (machine_config_ptr2_reg mc_conf) (target_config (machine_config_target mc_conf)) /\
     reg_ok (machine_config_len2_reg mc_conf) (target_config (machine_config_target mc_conf)) /\
     reg_ok (match asm_config_link_reg (target_config (machine_config_target mc_conf)) with
               NONE -> 0
             | SOME n -> n)
       (target_config (machine_config_target mc_conf)) /\
     enc_ok (target_config (machine_config_target mc_conf))`;;

(* HOL4 line 9615 *)
let LTTP4AUX_get_shmem_info_APPEND = prove
 (`!(secs:((A)sec)list) pos ffis2 (info2:shmem_info_num list) ffis1 info1.
     get_shmem_info secs pos (APPEND ffis1 ffis2) (APPEND info1 info2) =
     (APPEND ffis1 (FST (get_shmem_info secs pos ffis2 info2)),
      APPEND info1 (SND (get_shmem_info secs pos ffis2 info2)))`,
  MATCH_MP_TAC get_shmem_info_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[get_shmem_info_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?name nb. get_memop_info m = (name,nb:byte)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`name:shmem_op`; `nb:byte`]) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC]);;

let get_shmem_info_APPEND = prove
 (`!(secs:((A)sec)list) pos ffi_names (shmem_info:shmem_info_num list) ffis1 ffis2 info1
     info2 new_ffi_names new_shmem_info.
     get_shmem_info secs pos ffi_names shmem_info = (new_ffi_names,new_shmem_info) /\
     ffi_names = APPEND ffis1 ffis2 /\
     shmem_info = APPEND info1 info2
     ==> new_ffi_names = APPEND ffis1 (FST (get_shmem_info secs pos ffis2 info2)) /\
         new_shmem_info = APPEND info1 (SND (get_shmem_info secs pos ffis2 info2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `get_shmem_info (secs:((A)sec)list) pos ffi_names shmem_info =
               (new_ffi_names,new_shmem_info)` THEN
  ASM_REWRITE_TAC[LTTP4AUX_get_shmem_info_APPEND; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 9631 *)
let get_shmem_info_PREPEND = prove
 (`!(secs:((A)sec)list) pos ffi_names (shmem_info:shmem_info_num list) new_ffi_names
     new_shmem_info.
     get_shmem_info secs pos ffi_names shmem_info = (new_ffi_names,new_shmem_info)
     ==> new_ffi_names = APPEND ffi_names (FST (get_shmem_info secs pos [] [])) /\
         new_shmem_info = APPEND shmem_info (SND (get_shmem_info secs pos [] []))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC get_shmem_info_APPEND THEN
  EXISTS_TAC `ffi_names:ffiname list` THEN EXISTS_TAC `shmem_info:shmem_info_num list` THEN
  ASM_REWRITE_TAC[APPEND_NIL]);;

(* HOL4 line 9642 (the record literal is shmem_info_num_REC; HOL4 binds r *)
(* again in the cases on ad, as here; the cases on ad without the other    *)
(* patterns: Addr is the only constructor)                                  *)
let line_to_info_def = cake_def
  `line_to_info (secs:((A)sec)list) p (x:num#((A)line)option) =
     match SND x with
       SOME (Asm (ShareMem m r ad) bytes l) ->
         let (name,nb) = get_memop_info m in
         [(SharedMem name,
           shmem_info_num_REC (pos_val (FST x) p secs) nb
             (match ad with Addr r off -> r)
             (match ad with Addr r off -> val off)
             r
             (pos_val (FST x) p secs + LENGTH bytes))]
     | _ -> []`;;

(* HOL4 line 9657 (the two conjuncts are about independent types, A and B) *)
let line_to_info_next = prove
 (`!k1 (a:(A)asm_with_lab) b bytes1 len1 xs1 rest1 p1 i1 l1 k2 (c2:(B)asm_or_cbw) bytes2
     len2 xs2 rest2 p2 i2 l2.
     line_to_info (CONS (Section k1 (CONS (LabAsm a b bytes1 len1) xs1)) rest1) p1 (i1 + 1,l1) =
     line_to_info (CONS (Section k1 xs1) rest1) (p1 + LENGTH bytes1) (i1,l1) /\
     line_to_info (CONS (Section k2 (CONS (Asm c2 bytes2 len2) xs2)) rest2) p2 (i2 + 1,l2) =
     line_to_info (CONS (Section k2 xs2) rest2) (p2 + LENGTH bytes2) (i2,l2)`,
  REWRITE_TAC[line_to_info_def; FST; SND; pos_val_def; is_Label_def; line_length_def;
              ADD_EQ_0; ARITH_EQ; ADD_SUB]);;

(* HOL4 line 9671 *)
let line_to_info_hd_empty = prove
 (`!k (rest:((A)sec)list) p t.
     line_to_info (CONS (Section k []) rest) p t = line_to_info rest p t`,
  REWRITE_TAC[line_to_info_def; pos_val_def]);;

(* HOL4 line 9681 *)
let line_to_info_hd_Label = prove
 (`!k a b (xs:((A)line)list) rest p t.
     line_to_info (CONS (Section k (CONS (lab_Label a b 0) xs)) rest) p t =
     line_to_info (CONS (Section k xs) rest) p t`,
  REWRITE_TAC[line_to_info_def; pos_val_def; is_Label_def; line_length_def; ADD_CLAUSES]);;

(* HOL4 line 9694 *)
let LTTP4AUX_line_to_info_next_gen = prove
 (`!(y:(A)line) k xs rest p i l.
     ~is_Label y
     ==> line_to_info (CONS (Section k (CONS y xs)) rest) p (i + 1,l) =
         line_to_info (CONS (Section k xs) rest) (p + line_length y) (i,l)`,
  GEN_TAC THEN CASES_ON `y:(A)line` THEN
  REWRITE_TAC[is_Label_def; line_length_def; line_to_info_next]);;

let LTTP4AUX_MAP_line_to_info = prove
 (`!(y:(A)line) k xs rest p.
     ~is_Label y
     ==> MAP (line_to_info (CONS (Section k (CONS y xs)) rest) p)
           (list_of_seq (\i. (i,asm_fetch_aux i (CONS (Section k (CONS y xs)) rest)))
              (num_pcs (CONS (Section k (CONS y xs)) rest))) =
         CONS (line_to_info (CONS (Section k (CONS y xs)) rest) p (0,SOME y))
           (MAP (line_to_info (CONS (Section k xs) rest) (p + line_length y))
              (list_of_seq (\i. (i,asm_fetch_aux i (CONS (Section k xs) rest)))
                 (num_pcs (CONS (Section k xs) rest))))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[num_pcs_def] THEN
  REWRITE_TAC[ARITH_RULE `1 + n = n + 1`] THEN ASM_SIMP_TAC[GENLIST_asm_fetch_aux_next] THEN
  REWRITE_TAC[MAP; MAP_LIST_OF_SEQ; o_DEF] THEN
  ASM_SIMP_TAC[LTTP4AUX_line_to_info_next_gen]);;

let LTTP4AUX_get_shmem_info_thm = prove
 (`!(c:(A)asm_config) labs ffis (secs:((A)sec)list) p ffi_names shmem_info p'.
     all_enc_ok c labs ffis p' secs
     ==> get_shmem_info secs p ffi_names shmem_info =
         (APPEND ffi_names (MAP FST (FLAT (MAP (line_to_info secs p)
            (list_of_seq (\i. (i,asm_fetch_aux i secs)) (num_pcs secs))))),
          APPEND shmem_info (MAP SND (FLAT (MAP (line_to_info secs p)
            (list_of_seq (\i. (i,asm_fetch_aux i secs)) (num_pcs secs))))))`,
  let tac_other =
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[all_enc_ok_def; line_length_def] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p' + LENGTH (bytes:byte list)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[LTTP4AUX_MAP_line_to_info; is_Label_def] THEN
    REWRITE_TAC[get_shmem_info_def; line_to_info_def; line_length_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[FLAT; APPEND] in
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC get_shmem_info_ind THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[get_shmem_info_def; num_pcs_def; list_of_seq; MAP; FLAT; APPEND_NIL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[all_enc_ok_def; get_shmem_info_def; num_pcs_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN
      `line_to_info (CONS (Section k []) rest) pos = line_to_info (rest:((A)sec)list) pos`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; line_to_info_hd_empty]; ALL_TAC] THEN
    ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[all_enc_ok_def; get_shmem_info_def; line_ok_def; line_length_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `line_to_info (CONS (Section k (CONS (lab_Label x x' 0) xs)) rest) pos =
                  line_to_info (CONS (Section k xs) (rest:((A)sec)list)) pos`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; line_to_info_hd_Label]; ALL_TAC] THEN
    SIMP_TAC[STACKPROPSAUX_fetch_thms; num_pcs_def; is_Label_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `p':num` THEN
    FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN REWRITE_TAC[ADD_CLAUSES];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    SUBGOAL_THEN `?name nb. get_memop_info m = (name,nb:byte)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    REWRITE_TAC[all_enc_ok_def; line_length_def] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`name:shmem_op`; `nb:byte`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `p' + LENGTH (bytes:byte list)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[LTTP4AUX_MAP_line_to_info; is_Label_def] THEN
    ASM_REWRITE_TAC[get_shmem_info_def; line_to_info_def; line_length_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[pos_val_def; is_Label_def; FLAT; MAP; GSYM APPEND_ASSOC; APPEND];
    tac_other; tac_other; tac_other]);;

let get_shmem_info_thm = prove
 (CASE_TERM `!(secs:((A)sec)list) p ffi_names shmem_info p' (c:(A)asm_config) labs ffis.
     all_enc_ok c labs ffis p' secs
     ==> get_shmem_info secs p ffi_names shmem_info =
         (let (new_ffis,new_info) =
            UNZIP (FLAT (MAP (line_to_info secs p)
                           (list_of_seq (\i. (i,asm_fetch_aux i secs)) (num_pcs secs)))) in
          (APPEND ffi_names new_ffis,APPEND shmem_info new_info))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LTTP4AUX_get_shmem_info_thm
      th]) THEN
  REWRITE_TAC[UNZIP_DEF] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 9745 *)
let FILTER_NOT_MEM_Mapped = prove
 (`!l. ~MEM "MappedRead" (FILTER (\x. ~(x = "MappedRead") /\ ~(x = "MappedWrite")) l) /\
       ~MEM "MappedWrite" (FILTER (\x. ~(x = "MappedRead") /\ ~(x = "MappedWrite")) l)`,
  REWRITE_TAC[MEM_FILTER]);;

(* HOL4 line 9752 *)
let LTTP4AUX_some_unique = prove
 (`!P (a:A). P a /\ (!x. P x ==> x = a) ==> (some) P = SOME a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[some_def] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[]);;

let mmio_pcs_min_index_APPEND_thm = prove
 (`!l ffis.
     ALL (\x. !s. ~(x = ExtCall s)) l /\ ALL (\x. ?s. x = ExtCall s) ffis
     ==> mmio_pcs_min_index (APPEND ffis l) = SOME (LENGTH ffis)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVERY_EL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l") (LABEL_TAC "f")) THEN
  REWRITE_TAC[mmio_pcs_min_index_def] THEN MATCH_MP_TAC LTTP4AUX_some_unique THEN
  REWRITE_TAC[LENGTH_APPEND; EL_APPEND_EQN] THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_ADD] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "f" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE] THEN
    USE_THEN "l" (MP_TAC o SPEC `j - LENGTH (ffis:ffiname list)`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`EL (j - LENGTH (ffis:ffiname list)) (l:ffiname list)`,`e:ffiname`) THEN
    GEN_TAC THEN CASES_ON `e:ffiname` THEN SIMP[] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ext") (LABEL_TAC "sh"))) THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `0 < LENGTH (l:ffiname list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ext" (MP_TAC o REWRITE_RULE[LT_REFL; SUB_REFL] o
      C MP (ASSUME `LENGTH (ffis:ffiname list) < x`) o SPEC `LENGTH (ffis:ffiname list)`) THEN
    USE_THEN "l" (MP_TAC o C MP (ASSUME `0 < LENGTH (l:ffiname list)`) o SPEC `0`) THEN
    MESON_TAC[];
    SUBGOAL_THEN `x <= x /\ x < LENGTH (ffis:ffiname list) + LENGTH (l:ffiname list)`
      ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "sh" (MP_TAC o C MP (ASSUME `x <= x /\ x < LENGTH (ffis:ffiname list) +
      LENGTH (l:ffiname list)`) o SPEC `x:num`) THEN
    USE_THEN "f" (MP_TAC o C MP (ASSUME `x < LENGTH (ffis:ffiname list)`) o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[distinctness "ffiname"]]);;

(* HOL4 line 9780.  HOL4 ZIP (get_shmem_info ...) of the pair is ZIP of its *)
(* two components (equal lengths by get_shmem_info_EMPTY_LENGTH_EQ, as      *)
(* all_enc_ok holds); the cases on a without the other patterns.            *)
let MEM_get_shmem_info = prove
 (CASE_TERM `!(c:(A)asm_config) labs ffis p' (code2:((A)sec)list) pc op re a inst' len q
     (r:byte) p.
     all_enc_ok c labs ffis p' code2 /\
     asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a) inst' len) /\
     get_memop_info op = (q,r)
     ==> MEM (SharedMem q,
              shmem_info_num_REC (pos_val pc p code2) r
                (match a with Addr r off -> r)
                (match a with Addr r off -> val off)
                re
                (pos_val pc (p + LENGTH inst') code2))
             (ZIP (FST (get_shmem_info code2 p [] [])) (SND (get_shmem_info code2 p [] [])))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LTTP4AUX_get_shmem_info_thm th]) THEN
  REWRITE_TAC[APPEND; ZIP_MAP_FST_SND_EQ; MEM_FLAT; MEM_MAP; MEM_GENLIST] THEN
  EXISTS_TAC `line_to_info (code2:((A)sec)list) p (pc,asm_fetch_aux pc code2)` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(pc:num,asm_fetch_aux pc (code2:((A)sec)list))` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `pc:num` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC asm_fetch_SOME_IMP_LESS_num_pcs THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[line_to_info_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM pos_val_acc_0] THEN ARITH_TAC);;

(* HOL4 line 9811 *)
let LTTP4AUX_line_to_info_entry = prove
 (`!(code:((A)sec)list) p i l.
     MAP (\rec. shmem_info_num_entry_pc rec) (MAP SND (line_to_info code p (i,l))) = [] \/
     MAP (\rec. shmem_info_num_entry_pc rec) (MAP SND (line_to_info code p (i,l))) =
     [pos_val i p code]`,
  REWRITE_TAC[line_to_info_def; FST; SND] THEN REPEAT GEN_TAC THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[shmem_info_num_INFO.ri_accessors]);;

let get_shmem_info_ALL_DISTINCT = prove
 (`!(c:(A)asm_config) labs ffis p' (code2:((A)sec)list) p.
     LENGTH (prog_to_bytes code2) < dimword (:A) /\
     enc_ok c /\
     all_enc_ok c labs ffis p' code2
     ==> ALL_DISTINCT (MAP (\rec. shmem_info_num_entry_pc rec)
                        (SND (get_shmem_info code2 p [] [])))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LTTP4AUX_get_shmem_info_thm th]) THEN
  REWRITE_TAC[APPEND; MAP_FLAT; GSYM MAP_o; MAP_LIST_OF_SEQ] THEN
  REWRITE_TAC[o_DEF; ALL_DISTINCT_FLAT; MEM_GENLIST; LENGTH_LIST_OF_SEQ] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`code2:((A)sec)list`; `p:num`; `m:num`;
                   `asm_fetch_aux m (code2:((A)sec)list)`] LTTP4AUX_line_to_info_entry) THEN
    REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT; MEM];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < num_pcs (code2:((A)sec)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN GEN_TAC THEN
  SUBGOAL_THEN `pos_val i p (code2:((A)sec)list) < pos_val j p code2` MP_TAC THENL
   [MATCH_MP_TAC pos_val_mono THEN
    MAP_EVERY EXISTS_TAC [`p':num`; `c:(A)asm_config`; `labs:(num spt)spt`;
                          `ffis:ffiname list`] THEN
    ASM_SIMP_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`code2:((A)sec)list`; `p:num`; `i:num`;
                 `asm_fetch_aux i (code2:((A)sec)list)`] LTTP4AUX_line_to_info_entry) THEN
  MP_TAC(ISPECL [`code2:((A)sec)list`; `p:num`; `j:num`;
                 `asm_fetch_aux j (code2:((A)sec)list)`] LTTP4AUX_line_to_info_entry) THEN
  REWRITE_TAC[o_DEF] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC)) THEN REWRITE_TAC[MEM] THEN ARITH_TAC);;

(* HOL4 line 9852 *)
let get_shmem_info_EMPTY_LENGTH_EQ = prove
 (`!(c:(A)asm_config) labs ffis p' (code2:((A)sec)list) p.
     all_enc_ok c labs ffis p' code2
     ==> LENGTH (FST (get_shmem_info code2 p [] [])) =
         LENGTH (SND (get_shmem_info code2 p [] []))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LTTP4AUX_get_shmem_info_thm th]) THEN
  REWRITE_TAC[APPEND; LENGTH_MAP]);;

(* HOL4 line 9864 *)
let line_to_info_offset_FST_eq = prove
 (`!(code:((A)sec)list) p accum.
     MAP FST (line_to_info code p accum) = MAP FST (line_to_info code 0 accum)`,
  REWRITE_TAC[line_to_info_def] THEN REPEAT GEN_TAC THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN TOP_CASE_TAC THEN REWRITE_TAC[MAP]);;

(* HOL4 line 9874 *)
let line_to_info_offset_SND_eq = prove
 (`!(code:((A)sec)list) p accum.
     MAP SND (line_to_info code p accum) =
     MAP (\x. shmem_info_num_entry_pc_fupd (K (p + shmem_info_num_entry_pc (SND x)))
                (shmem_info_num_exit_pc_fupd (K (p + shmem_info_num_exit_pc (SND x))) (SND x)))
       (line_to_info code 0 accum)`,
  REWRITE_TAC[line_to_info_def] THEN REPEAT GEN_TAC THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN TOP_CASE_TAC THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[shmem_info_num_INFO.ri_accessors; shmem_info_num_INFO.ri_fupds; K_THM; SND] THEN
  REWRITE_TAC[ADD_ASSOC; pos_val_acc_0]);;

(* HOL4 line 9889 *)
let get_shmem_info_init_pc_offset = prove
 (`!(c:(A)asm_config) labs ffis p' (code:((A)sec)list) p.
     all_enc_ok c labs ffis p' code
     ==> FST (get_shmem_info code 0 [] []) = FST (get_shmem_info code p [] []) /\
         MAP (\rec. shmem_info_num_entry_pc_fupd (K (p + shmem_info_num_entry_pc rec))
                      (shmem_info_num_exit_pc_fupd (K (p + shmem_info_num_exit_pc rec)) rec))
           (SND (get_shmem_info code 0 [] [])) =
         SND (get_shmem_info code p [] [])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LTTP4AUX_get_shmem_info_thm th]) THEN
  REWRITE_TAC[APPEND; MAP_FLAT; GSYM MAP_o] THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[line_to_info_offset_FST_eq] THEN REWRITE_TAC[];
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [line_to_info_offset_SND_eq] THEN
    REWRITE_TAC[GSYM MAP_o; o_DEF]]);;

(* HOL4 line 9904 *)
let mmio_pcs_min_index_get_shmem_info_ok = prove
 (`!(c:(A)asm_config) labs ffis' p' (code2:((A)sec)list) ffis p new_ffi_names new_shmem_info.
     all_enc_ok c labs ffis' p' code2 /\
     enc_ok c /\ ALL (\x. ?s. x = ExtCall s) ffis /\
     get_shmem_info code2 p ffis [] = (new_ffi_names,new_shmem_info)
     ==> mmio_pcs_min_index new_ffi_names = SOME (LENGTH ffis)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP get_shmem_info_MappedRead_or_MappedWrite) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC mmio_pcs_min_index_APPEND_thm THEN
  ASM_REWRITE_TAC[GSYM Sh_not_Ext]);;

(* HOL4 line 9919 (the cases on a without the other patterns) *)
let LTTP4AUX_MEM_line_to_info = prove
 (`!(code:((A)sec)list) p i l y.
     MEM y (line_to_info code p (i,l))
     ==> (?op re a bytes len. l = SOME (Asm (ShareMem op re a) bytes len)) /\
         shmem_info_num_entry_pc (SND y) = pos_val i p code`,
  REWRITE_TAC[line_to_info_def; FST; SND] THEN REPEAT GEN_TAC THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MEM] THEN TOP_CASE_TAC THEN REWRITE_TAC[MEM] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[MEM] THEN TOP_CASE_TAC THEN REWRITE_TAC[MEM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[shmem_info_num_INFO.ri_accessors; SND] THEN
  ASM_MESON_TAC[]);;

let get_shmem_info_ok_lemma = prove
 (CASE_TERM `!(c:(A)asm_config) labs ffis' p' (code2:((A)sec)list) ffis p new_ffi_names
     new_shmem_info.
     all_enc_ok c labs ffis' p' code2 /\
     enc_ok c /\
     LENGTH (prog_to_bytes code2) < dimword (:A) /\
     ALL (\x. ?s. x = ExtCall s) ffis /\
     get_shmem_info code2 p ffis [] = (new_ffi_names,new_shmem_info)
     ==> (!pc op re a inst len i.
            asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a) inst len) /\
            mmio_pcs_min_index new_ffi_names = SOME i
            ==> ?index.
                  find_index (p + pos_val pc 0 code2)
                    (MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info) 0 = SOME index /\
                  (let (name,nb) = get_memop_info op in
                   EL (index + i) new_ffi_names = SharedMem name /\
                   EL index new_shmem_info =
                   shmem_info_num_REC (shmem_info_num_entry_pc (EL index new_shmem_info)) nb
                     (match a with Addr r off -> r)
                     (match a with Addr r off -> val off)
                     re
                     (p + (pos_val pc 0 code2 + len)))) /\
         (!pc line.
            asm_fetch_aux pc code2 = SOME line /\
            (!op re a inst len. ~(line = Asm (ShareMem op re a) inst len))
            ==> DISJOINT (set_of_list (MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info))
                  {p + a + pos_val pc 0 code2 | a | a < LENGTH (line_bytes line)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mmio_pcs_min_index new_ffi_names = SOME (LENGTH (ffis:ffiname list))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC mmio_pcs_min_index_get_shmem_info_ok THEN
    MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis':ffiname list`;
      `p':num`; `code2:((A)sec)list`; `p:num`; `new_shmem_info:shmem_info_num list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`p:num`; `[]:ffiname list`; `[]:shmem_info_num list`]
    (MATCH_MP LTTP4AUX_get_shmem_info_thm th))) THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`p:num`; `ffis:ffiname list`; `[]:shmem_info_num list`]
    (MATCH_MP LTTP4AUX_get_shmem_info_thm th))) THEN
  ASM_REWRITE_TAC[PAIR_EQ; APPEND] THEN
  ABBREV_TAC `L = FLAT (MAP (line_to_info code2 p)
     (list_of_seq (\i. (i,asm_fetch_aux i (code2:((A)sec)list))) (num_pcs code2)))` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP (\rec. shmem_info_num_entry_pc rec) (MAP SND
      (L:(ffiname#shmem_info_num)list)))`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis':ffiname list`; `p':num`;
                   `code2:((A)sec)list`; `p:num`] get_shmem_info_ALL_DISTINCT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(MAP_EVERY X_GEN_TAC [`pc:num`; `op:memop`; `re:num`; `a:(A)addr`; `inst:byte list`;
     `len:num`; `i:num`] THEN
   REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
   SUBGOAL_THEN `?q r. get_memop_info op = (q,r:byte)` STRIP_ASSUME_TAC THENL
    [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis':ffiname list`; `p':num`;
     `code2:((A)sec)list`; `pc:num`; `op:memop`; `re:num`; `a:(A)addr`; `inst:byte list`;
     `len:num`; `q:shmem_op`; `r:byte`; `p:num`] MEM_get_shmem_info) THEN
   ASM_REWRITE_TAC[ZIP_MAP_FST_SND_EQ; MEM_EXISTS_EL] THEN
   DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `j:num`) THEN
    (FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) && is_pair(lhand(concl
        th)))) THEN
   SUBGOAL_THEN `LENGTH (inst:byte list) = len` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`pc:num`; `p':num`; `code2:((A)sec)list`; `c:(A)asm_config`;
                    `labs:(num spt)spt`; `ffis':ffiname list`;
                    `Asm (ShareMem op re a) inst len:(A)line`]
            all_enc_ok_asm_fetch_aux_IMP_line_ok) THEN
     ASM_REWRITE_TAC[line_ok_def] THEN MESON_TAC[];
     ALL_TAC] THEN
   ASM_SIMP_TAC[find_index_ALL_DISTINCT_EL_eq; LENGTH_MAP; EL_MAP; EL_APPEND_EQN;
     ARITH_RULE `~(j + n < n:num)`; ADD_SUB; shmem_info_num_INFO.ri_accessors] THEN
   CONJ_TAC THENL
    [EXISTS_TAC `j:num` THEN
     ASM_SIMP_TAC[ADD_CLAUSES; pos_val_acc_0; EL_MAP; LENGTH_MAP;
                  shmem_info_num_INFO.ri_accessors];
     ALL_TAC] THEN
   AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM pos_val_acc_0] THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ARITH_TAC);
    (MAP_EVERY X_GEN_TAC [`pc:num`; `line:(A)line`] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST; IN_ELIM_THM] THEN
   X_GEN_TAC `x:num` THEN REWRITE_TAC[MEM_MAP] THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `aa:num` STRIP_ASSUME_TAC))) THEN
    (UNDISCH_TAC `MEM (x:ffiname#shmem_info_num) L` THEN EXPAND_TAC "L" THEN
   REWRITE_TAC[MEM_FLAT; MEM_MAP; MEM_GENLIST] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_pair(rand(concl th)))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
     type_of(lhand(concl th)) = `:(ffiname#shmem_info_num)list`)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP4AUX_MEM_line_to_info) THEN
   DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
    (SUBGOAL_THEN `~(m:num = pc)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN
     UNDISCH_TAC `asm_fetch_aux pc (code2:((A)sec)list) = SOME line` THEN
     ASM_REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis':ffiname list`; `p':num`;
     `code2:((A)sec)list`; `pc:num`; `line:(A)line`; `aa:num`; `p:num`; `m:num`]
     pos_val_asm_fetch_aux_distinct) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`pc:num`; `p:num`; `code2:((A)sec)list`] pos_val_acc_0) THEN
   UNDISCH_TAC `x = p + aa + pos_val pc 0 (code2:((A)sec)list)` THEN
   UNDISCH_TAC `x = shmem_info_num_entry_pc x'` THEN
   UNDISCH_TAC `x' = SND (x:ffiname#shmem_info_num)` THEN
   DISCH_THEN SUBST1_TAC THEN
   UNDISCH_TAC `shmem_info_num_entry_pc (SND (x:ffiname#shmem_info_num)) = pos_val m p
       (code2:((A)sec)list)` THEN
   ARITH_TAC)]);;

(* HOL4 line 10011 (HOL4 -n2w x + y is word_add (word_neg (word x)) y) *)
let asm_fetch_NOT_ffi_entry_pcs = prove
 (`!(code2:((A)sec)list) (mc_conf:(A,B,C)machine_config) i labs ffi_names (ms:B)
     (t:(A)asm_state) dm pos line a.
     LENGTH (prog_to_bytes code2) < dimword (:A) /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
     LENGTH (machine_config_ffi_names mc_conf) = LENGTH (machine_config_ffi_entry_pcs mc_conf) /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     enc_ok (target_config (machine_config_target mc_conf)) /\
     (!index.
        index < i
        ==> ~(word_add (word_neg (word (ffi_offset * (index + 3))))
                (target_get_pc (machine_config_target mc_conf) ms) IN
              machine_config_prog_addresses mc_conf) /\
            ~(word_add (word_neg (word (ffi_offset * (index + 3))))
                (target_get_pc (machine_config_target mc_conf) ms) IN
              machine_config_shared_addresses mc_conf) /\
            ~(word_add (word_neg (word (ffi_offset * (index + 3))))
                (target_get_pc (machine_config_target mc_conf) ms) =
              machine_config_halt_pc mc_conf) /\
            ~(word_add (word_neg (word (ffi_offset * (index + 3))))
                (target_get_pc (machine_config_target mc_conf) ms) =
              machine_config_ccache_pc mc_conf) /\
            find_index
              (word_add (word_neg (word (ffi_offset * (index + 3))))
                 (target_get_pc (machine_config_target mc_conf) ms))
              (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index) /\
     bytes_in_mem (target_get_pc (machine_config_target mc_conf) ms) (prog_to_bytes code2)
       (asm_state_mem t) (machine_config_prog_addresses mc_conf) dm /\
     asm_fetch_aux pos code2 = SOME line /\
     a < LENGTH (line_bytes line)
     ==> ~MEM (word_add (word_add (target_get_pc (machine_config_target mc_conf) ms) (word a))
                 (word (pos_val pos 0 code2)))
              (TAKE i (machine_config_ffi_entry_pcs mc_conf))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `pc = target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)`
      THEN
  ABBREV_TAC `l = machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config)` THEN
  SUBGOAL_THEN `a + pos_val pos 0 (code2:((A)sec)list) < LENGTH (prog_to_bytes code2)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`pos:num`; `0`; `code2:((A)sec)list`; `0`;
                   `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
                   `labs:(num spt)spt`; `ffi_names:ffiname list`; `line:(A)line`]
           asm_fetch_aux_pos_val_SUC) THEN
    MP_TAC(ISPECL [`pos + 1`; `0`; `code2:((A)sec)list`;
                   `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
                   `labs:(num spt)spt`; `ffi_names:ffiname list`; `0`] pos_val_bound) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add pc (word a)) (word (pos_val pos 0 (code2:((A)sec)list))) IN
                machine_config_prog_addresses (mc_conf:(A,B,C)machine_config)`
    ASSUME_TAC THENL
   [REWRITE_TAC[word_arith_lemma1] THEN MATCH_MP_TAC bytes_in_memory_in_domain THEN
    MAP_EVERY EXISTS_TAC [`prog_to_bytes (code2:((A)sec)list)`; `asm_state_mem
        (t:(A)asm_state)`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(ACCEPT_TAC o MATCH_MP bytes_in_mem_IMP);
    ALL_TAC] THEN
  SUBGOAL_THEN `i <= LENGTH (l:(A word)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP mmio_pcs_min_index_is_SOME) THEN
    UNDISCH_TAC `LENGTH (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
                 LENGTH (l:(A word)list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MEM_EXISTS_EL; LENGTH_TAKE] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[EL_TAKE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `n < i`) o SPEC `n:num` o check (is_forall o concl)) THEN
  ABBREV_TAC `y = word_add (word_neg (word (ffi_offset * (n + 3)))) (pc:A word)` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP find_index_is_MEM) THEN
  DISCH_THEN(MP_TAC o SPEC `0` o MATCH_MP find_index_MEM) THEN
  ASM_REWRITE_TAC[option_INJ; ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 10065 *)
let list_subset_refl = prove
 (`!(xs:A list). list_subset xs xs`,
  REWRITE_TAC[list_subset_def; GSYM ALL_MEM] THEN MESON_TAC[]);;

(* HOL4 line 10076 *)
let list_subset_TAKE = prove
 (`!i (xs:A list). list_subset (TAKE i xs) xs`,
  REWRITE_TAC[list_subset_def; GSYM ALL_MEM] THEN MESON_TAC[MEM_TAKE]);;

(* HOL4 line 10090 *)
let list_subset_trans = prove
 (`!(a:A list) b c. list_subset a b /\ list_subset b c ==> list_subset a c`,
  REWRITE_TAC[list_subset_def; GSYM ALL_MEM] THEN MESON_TAC[]);;

(* HOL4 line 10101 *)
let genlist_line_to_info_entry_pc_max = prove
 (`!(c:(A)asm_config) labs ffis p' (code2:((A)sec)list).
     all_enc_ok c labs ffis p' code2 /\ enc_ok c
     ==> ALL (\x. shmem_info_num_entry_pc (SND x) < pos_val (num_pcs code2) 0 code2)
           (FLAT (list_of_seq (\i. line_to_info code2 0 (i,asm_fetch_aux i code2))
                    (num_pcs code2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EVERY_FLAT; EVERY_GENLIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[line_to_info_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[ALL] THEN TOP_CASE_TAC THEN REWRITE_TAC[ALL] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[ALL] THEN TOP_CASE_TAC THEN REWRITE_TAC[ALL] THEN
  REWRITE_TAC[shmem_info_num_INFO.ri_accessors; SND; FST] THEN
  MATCH_MP_TAC pos_val_mono THEN
  MAP_EVERY EXISTS_TAC [`p':num`; `c:(A)asm_config`; `labs:(num spt)spt`;
                        `ffis:ffiname list`] THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* HOL4 line 10127 *)
let find_index_MAP_w2n = prove
 (`!l (x:A word) n. find_index (val x) (MAP val l) n = find_index x l n`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[find_index_def; MAP; VAL_EQ]);;

(* HOL4 line 10134.  The HOL4 proof is spread over Resume                    *)
(* IMP_state_rel_make_init[ISR1..ISR17] blocks (HOL4 lines 10204-10514,      *)
(* Finalise at 10514): one theorem here.  ZIP of equal lengths.              *)
let LTTP4AUX_ALOOKUP_ZIP_GENLIST = prove
 (`!i (l:B list) idx.
     if i <= idx /\ idx < i + LENGTH l
     then ?info. ALOOKUP (ZIP (list_of_seq (\index. index + i) (LENGTH l)) l) idx = SOME info
     else ALOOKUP (ZIP (list_of_seq (\index. index + i) (LENGTH l)) l) idx = NONE`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [EXISTS_TAC `EL (idx - i) (l:B list)` THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    SIMP_TAC[MAP_ZIP; LENGTH_LIST_OF_SEQ; MEM_ZIP; ALL_DISTINCT_GENLIST] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `idx - i` THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ; PAIR_EQ;
      ARITH_RULE `i <= idx /\ idx < i + n ==> idx - i < n`] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ALOOKUP_FAILS] THEN SIMP_TAC[MEM_ZIP; LENGTH_LIST_OF_SEQ] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(k:num,(v:B)) = EL n (list_of_seq (\index. index + i) (LENGTH (l:B list))),EL n
        l` THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; PAIR_EQ] THEN ASM_ARITH_TAC]);;

let LTTP4AUX_word_wrap = prove
 (`!(pc:A word) e l. e < l /\ l < dimword (:A) ==> ~(word_add pc (word l) = word (val pc + e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; GSYM dimword_def] THEN
  MP_TAC(ISPEC `pc:A word` w2n_lt) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`val (pc:A word) + l`; `dimword (:A)`] MOD_CASES) THEN
  MP_TAC(SPECL [`val (pc:A word) + e`; `dimword (:A)`] MOD_CASES) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let LTTP4AUX_shmem_entry_lt = prove
 (`!(c:(A)asm_config) labs ffis (code2:((A)sec)list) ffi_names shmem_info.
     all_enc_ok c labs ffis 0 code2 /\ enc_ok c /\
     get_shmem_info code2 0 [] [] = (ffi_names,shmem_info)
     ==> ALL (\rec. shmem_info_num_entry_pc rec < LENGTH (prog_to_bytes code2)) shmem_info`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`0`; `[]:ffiname list`; `[]:shmem_info_num list`] o
    MATCH_MP LTTP4AUX_get_shmem_info_thm) THEN
  ASM_REWRITE_TAC[PAIR_EQ; APPEND] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`; `0`;
    `code2:((A)sec)list`] genlist_line_to_info_entry_pc_max) THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`; `0`;
    `code2:((A)sec)list`; `0`] pos_val_num_pcs) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF; ALL_MAP] THEN REWRITE_TAC[o_DEF]);;

let LTTP4AUX_get_shmem_info_shift = prove
 (`!(c:(A)asm_config) labs ffis (code2:((A)sec)list) p l new_ffi_names shmem_info.
     all_enc_ok c labs ffis 0 code2 /\
     get_shmem_info code2 0 [] [] = (new_ffi_names,shmem_info)
     ==> get_shmem_info code2 p l [] =
         (APPEND l new_ffi_names,
          MAP (\rec. shmem_info_num_entry_pc_fupd (K (p + shmem_info_num_entry_pc rec))
                       (shmem_info_num_exit_pc_fupd (K (p + shmem_info_num_exit_pc rec)) rec))
              shmem_info)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`code2:((A)sec)list`; `p:num`; `[]:ffiname list`; `[]:shmem_info_num list`;
                 `l:ffiname list`; `[]:shmem_info_num list`] LTTP4AUX_get_shmem_info_APPEND) THEN
  REWRITE_TAC[APPEND_NIL; APPEND] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`; `0`;
                 `code2:((A)sec)list`; `p:num`] get_shmem_info_init_pc_offset) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

let LTTP4AUX_val_add_eq = prove
 (`!(pc:A word) n e. n < dimword (:A) /\ val (word_add pc (word n)) = val pc + e ==> n = e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; GSYM dimword_def] THEN
  STRIP_TAC THEN MP_TAC(ISPEC `pc:A word` w2n_lt) THEN DISCH_TAC THEN
  UNDISCH_TAC `(val (pc:A word) + n MOD dimword (:A)) MOD dimword (:A) = val pc + e` THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`val (pc:A word) + n`; `dimword (:A)`] MOD_CASES) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let LTTP4AUX_neg_off = prove
 (`!(pc:A word) index.
     word_add (word_neg (word (ffi_offset * (index + 3)))) pc =
     word_sub pc (word ((3 + index) * ffi_offset))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `ffi_offset * (index + 3) = (3 + index) * ffi_offset`] THEN
  CONV_TAC WORD_RULE);;

let IMP_state_rel_make_init = prove
 (`!(mc_conf:(A,B,C)machine_config) (code:((A)sec)list) coracle labs code2 i clock (ms:B)
     cbspace (t:(A)asm_state) m dm sdm new_ffi_names shmem_info new_shmem_info
     (ffi:(FFI)ffi_state).
     lab_to_targetProof_good_code (target_config (machine_config_target mc_conf)) LN code /\
     mc_conf_ok mc_conf /\
     (no_share_mem_inst code
      ==> compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes code2))
            (target_config (machine_config_target mc_conf)) (machine_config_ffi_names mc_conf)) /\
     list_subset (FILTER (\x. ?s. x = ExtCall s) (find_ffi_names code))
       (TAKE i (machine_config_ffi_names mc_conf)) /\
     remove_labels clock (target_config (machine_config_target mc_conf)) 0 LN
       (TAKE i (machine_config_ffi_names mc_conf)) code = SOME (code2,labs) /\
     good_init_state mc_conf ms (prog_to_bytes code2) cbspace t m dm sdm /\
     get_shmem_info code2 0 [] [] = (new_ffi_names,shmem_info) /\
     new_shmem_info =
       MAP (\rec. shmem_info_num_entry_pc_fupd
                    (K (val (target_get_pc (machine_config_target mc_conf) ms) +
                        shmem_info_num_entry_pc rec))
                    (shmem_info_num_exit_pc_fupd
                       (K (val (target_get_pc (machine_config_target mc_conf) ms) +
                           shmem_info_num_exit_pc rec)) rec)) shmem_info /\
     DROP i (machine_config_ffi_names mc_conf) = new_ffi_names /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
     MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info =
       DROP i (MAP val (machine_config_ffi_entry_pcs mc_conf)) /\
     machine_config_mmio_info mc_conf =
       ZIP (list_of_seq (\index. index + i) (LENGTH new_shmem_info))
           (MAP (\rec. (shmem_info_num_nbytes rec,
                        Addr (shmem_info_num_addr_reg rec) (word (shmem_info_num_addr_off rec)),
                        shmem_info_num_reg rec,
                        word (shmem_info_num_exit_pc rec))) new_shmem_info) /\
     no_install_or_no_share_mem code (machine_config_ffi_names mc_conf) /\
     (!bn. bn < cbspace
           ==> ~MEM (word_add (word_add (word bn) (word (LENGTH (prog_to_bytes code2))))
                       (target_get_pc (machine_config_target mc_conf) ms))
                    (TAKE i (machine_config_ffi_entry_pcs mc_conf)))
     ==> lab_to_targetProof_state_rel
           (mc_conf,code2,labs,target_get_pc (machine_config_target mc_conf) ms)
           (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
              (compile_lab (target_config (machine_config_target mc_conf)))
              (word_add (target_get_pc (machine_config_target mc_conf) ms)
                 (word (LENGTH (prog_to_bytes code2))))
              cbspace coracle)
           t ms`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`clock:num`; `target_config (machine_config_target
      (mc_conf:(A,B,C)machine_config))`;
    `0`; `LN:(num spt)spt`;
    `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
    `code:((A)sec)list`; `code2:((A)sec)list`; `labs:(num spt)spt`] remove_labels_thm) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `lab_to_targetProof_good_code (target_config (machine_config_target
                   (mc_conf:(A,B,C)machine_config))) LN (code:((A)sec)list)` THEN
    UNDISCH_TAC `mc_conf_ok (mc_conf:(A,B,C)machine_config)` THEN
    ASM_REWRITE_TAC[lab_to_targetProof_good_code_def; mc_conf_ok_def; EVEN] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[lab_lookup_def; lookup_def] THEN CASE_REWRITE_TAC[OPTION_ALL_def];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[good_init_state_def; target_configured_def;
    start_pc_ok_def] o check (fun th -> is_comb(concl th) &&
    (try fst(dest_const(fst(strip_comb(concl th)))) = "good_init_state" with Failure _ ->
        false))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mc_conf_ok_def] o check (fun th -> is_comb(concl
      th) &&
    (try fst(dest_const(fst(strip_comb(concl th)))) = "mc_conf_ok" with Failure _ -> false))) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(rand(concl th)) &&
      is_var(rand(rand(concl th))) && fst(dest_var(rand(rand(concl th)))) = "i'"
      then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[lab_to_targetProof_state_rel_def; lab_to_targetProof_make_init_def;
              lab_state_INFO.ri_accessors; buffer_INFO.ri_accessors] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `asm_state_pc (t:(A)asm_state) =
      target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)`
    then REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  ASM_REWRITE_TAC[THE_DEF; LENGTH; ADD_CLAUSES; option_INJ; UNWIND_THM1] THEN
  SUBGOAL_THEN `i + LENGTH (shmem_info:shmem_info_num list) =
                LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:num list->num` o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "DROP" with Failure _ -> false) &&
      (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "MAP" with Failure _ -> false))) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_DROP] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP mmio_pcs_min_index_is_SOME o check (fun th ->
      is_eq(concl th) && rand(concl th) = `SOME (i:num)`)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `index:num` THEN
    W(fun (asl,w) ->
      let z = find_term (fun t -> is_comb t && is_comb(rator t) &&
                (try fst(dest_const(rator(rator t))) = "ZIP" with Failure _ -> false)) w in
      MP_TAC(ISPECL [`i:num`; rand z; `index:num`] LTTP4AUX_ALOOKUP_ZIP_GENLIST)) THEN
    ASM_REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_eq c && lhand c = `i:num` && is_var(rand c) && not(rand c = `i:num`)
      then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MATCH_MP_TAC(REWRITE_RULE[post_ffi_asm_def]
      (INST [`target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)`,
             `pc:A word`] ffi_interfer_ok_post_ffi_asm)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `index < i` THEN
      UNDISCH_TAC `i + LENGTH (shmem_info:shmem_info_num list) =
                   LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))` THEN
      ARITH_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC call_FFI_LENGTH THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `call_FFI (st:(FFI)ffi_state) (EL index (machine_config_ffi_names
                     (mc_conf:(A,B,C)machine_config))) bytes bytes2 = FFI_return new_st
                         new_bytes` THEN
      ASM_REWRITE_TAC[call_FFI_def; injectivity "ffi_result"] THEN MESON_TAC[];
      REWRITE_TAC[WORD_RULE `word_add (word_neg y) x:A word = word_sub x y`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MATCH_MP_TAC(REWRITE_RULE[post_ccache_asm_def]
      (INST [`target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)`,
             `pc:A word`] ccache_interfer_ok_post_ccache_asm)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_add (word_neg y) x:A word = word_sub x y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `no_share_mem_inst (code:((A)sec)list)` ASSUME_TAC THENL
     [MATCH_MP_TAC code_similar_IMP_both_no_share_mem THEN
      EXISTS_TAC `code2:((A)sec)list` THEN ASM_SIMP_TAC[code_similar_sym];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `no_share_mem_inst (code:((A)sec)list)`)) THEN
    REWRITE_TAC[compiler_oracle_ok_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "all") (LABEL_TAC "zero")) THEN
    X_GEN_TAC `k:num` THEN
    MP_TAC(ISPEC `(coracle:num->lab_to_target_config#((A)sec)list) k` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:lab_to_target_config` (X_CHOOSE_THEN `y:((A)sec)list`
      ASSUME_TAC)) THEN
    USE_THEN "all" (MP_TAC o REWRITE_RULE[ASSUME
      `(coracle:num->lab_to_target_config#((A)sec)list) k = (x,y)`] o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "zero" (MP_TAC o REWRITE_RULE[ASSUME
      `(coracle:num->lab_to_target_config#((A)sec)list) 0 = (x,y)`]) THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC list_subset_trans THEN
    EXISTS_TAC `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))` THEN
    ASM_REWRITE_TAC[list_subset_TAKE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC all_enc_ok_prog_to_bytes_EVEN THEN
    MAP_EVERY EXISTS_TAC [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
      `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
      `0`] THEN
    ASM_REWRITE_TAC[EVEN];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_eq c && lhand c = `i:num` && is_var(rand c) && not(rand c = `i:num`)
      then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
    SUBGOAL_THEN `EL (get_ffi_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) name)
                    (machine_config_ffi_names mc_conf) = name` ASSUME_TAC THENL
     [REWRITE_TAC[get_ffi_index_def] THEN
      FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP find_index_MEM o check (fun th ->
        is_comb(concl th) && (try fst(dest_const(fst(strip_comb(concl th)))) = "MEM"
                              with Failure _ -> false))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[the_eqn; ADD_CLAUSES] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `get_ffi_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) name`
        (CONJUNCT1(CONJUNCT2(MATCH_MP mmio_pcs_min_index_is_SOME (ASSUME
          `mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
           SOME i`))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `get_ffi_index (machine_config_ffi_names
        (mc_conf:(A,B,C)machine_config)) name < i`) o
      SPEC `get_ffi_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) name`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[word_loc_val_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:A word) IN dm` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "byte_align" with Failure _ -> false))
          (concl th) &&
        can (find_term (fun t -> t = `dm:A word->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(dm:A word->bool) SUBSET asm_state_mem_domain (t:(A)asm_state)` THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "get_byte" with Failure _ -> false))
          (concl th) then MP_TAC (SPEC `a:A word` th) else NO_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[word_loc_val_byte_def; word_loc_val_def] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (p:A word) (word l)) (word n) =
                           word_add (word (n + l)) p`] THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `n < cbspace`) o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `cbspace:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[bytes_in_mem_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `cbspace + LENGTH (prog_to_bytes (code2:((A)sec)list)) < dimword (:A)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `bn:num` THEN DISCH_TAC THEN REWRITE_TAC[MEM_EXISTS_EL] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `n < i` THENL
     [FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `bn < cbspace`) o SPEC `bn:num` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "TAKE"
                                                    with Failure _ -> false)) (concl th))) THEN
      REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `n:num` THEN
      SUBGOAL_THEN `i <= LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))`
        ASSUME_TAC THENL
       [UNDISCH_TAC `i + LENGTH (shmem_info:shmem_info_num list) =
                     LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[LENGTH_TAKE; EL_TAKE] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "EL" with Failure _ -> false))) THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    SUBGOAL_THEN `n - i < LENGTH (shmem_info:shmem_info_num list)` ASSUME_TAC THENL
     [UNDISCH_TAC `i + LENGTH (shmem_info:shmem_info_num list) =
                   LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))` THEN
      UNDISCH_TAC `n < LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))` THEN
      UNDISCH_TAC `~(n < i)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val (EL n (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))) =
                  val (target_get_pc (machine_config_target mc_conf) (ms:B)) +
                  shmem_info_num_entry_pc (EL (n - i) shmem_info)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o AP_TERM `EL (n - i):num list->num` o check (fun th ->
        is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "DROP" with Failure _ -> false) &&
        (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "MAP" with Failure _ ->
            false))) THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && is_var(lhand(concl th)) &&
          fst(dest_var(lhand(concl th))) = "new_shmem_info" then REWRITE_TAC[th] else NO_TAC) THEN
      REWRITE_TAC[GSYM MAP_DROP] THEN
      SUBGOAL_THEN `n - i < LENGTH (DROP i (machine_config_ffi_entry_pcs
                      (mc_conf:(A,B,C)machine_config))) /\
                    (n - i) + i < LENGTH (machine_config_ffi_entry_pcs mc_conf) /\
                    (n - i) + i = n` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_DROP] THEN
        UNDISCH_TAC `n < LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))` THEN
        UNDISCH_TAC `~(n < i)` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[EL_MAP; EL_DROP; LENGTH_MAP] THEN
      REWRITE_TAC[shmem_info_num_INFO.ri_accfupds; K_THM] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `shmem_info_num_entry_pc (EL (n - i) shmem_info) <
                  LENGTH (prog_to_bytes (code2:((A)sec)list))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
        `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
        `code2:((A)sec)list`; `new_ffi_names:ffiname list`; `shmem_info:shmem_info_num list`]
        LTTP4AUX_shmem_entry_lt) THEN
      ASM_REWRITE_TAC[EVERY_EL] THEN DISCH_THEN(MP_TAC o SPEC `n - i`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)`;
      `shmem_info_num_entry_pc (EL (n - i) shmem_info)`;
      `LENGTH (prog_to_bytes (code2:((A)sec)list)) + bn`] LTTP4AUX_word_wrap) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `shmem_info_num_entry_pc (EL (n - i) shmem_info) <
                   LENGTH (prog_to_bytes (code2:((A)sec)list))` THEN
      UNDISCH_TAC `bn < cbspace` THEN
      UNDISCH_TAC `cbspace + LENGTH (prog_to_bytes (code2:((A)sec)list)) < dimword (:A)` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && is_comb(lhand(concl th)) &&
      (try fst(dest_const(rator(lhand(concl th)))) = "val" with Failure _ -> false))) THEN
    REWRITE_TAC[WORD_VAL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "EL" with Failure _ -> false))) THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`code2:((A)sec)list`;
      `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`; `labs:(num spt)spt`;
      `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`; `0`] pos_val_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC code_similar_sec_labels_ok THEN EXISTS_TAC `code:((A)sec)list` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lab_to_targetProof_good_code (target_config (machine_config_target
                   (mc_conf:(A,B,C)machine_config))) LN (code:((A)sec)list)` THEN
    SIMP_TAC[lab_to_targetProof_good_code_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `no_install_or_no_share_mem (code2:((A)sec)list)
                  (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))` ASSUME_TAC THENL
   [MATCH_MP_TAC code_similar_IMP_both_no_install_or_no_share_mem THEN
    EXISTS_TAC `code:((A)sec)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[share_mem_state_rel_def; lab_state_INFO.ri_accessors] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> let c = concl th in
        if is_eq c && is_comb(rand c) && is_var(rand(rand c)) && not(rand(rand c) = `i:num`) &&
           (try fst(dest_const(fst(strip_comb(lhand c)))) = "mmio_pcs_min_index"
            with Failure _ -> false)
        then MP_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_ASSUM(MP_TAC o SPECL [`ms2:B`; `k:num`; `index:num`; `new_bytes:byte list`;
        `t1:(A)asm_state`; `[]:byte list`; `[]:byte list`; `i:num`] o
        REWRITE_RULE[ffi_interfer_ok_def] o check (fun th -> is_comb(concl th) &&
        (try fst(dest_const(fst(strip_comb(concl th)))) = "ffi_interfer_ok"
         with Failure _ -> false))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(rand(concl th)) &&
        is_var(rand(rand(concl th))) && is_comb(lhand(concl th)) &&
        (try fst(dest_const(rator(lhand(concl th)))) = "SOME" with Failure _ -> false))) THEN
      REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_ASSUM(MP_TAC o SPEC `index:num` o CONJUNCT2 o CONJUNCT2 o
        MATCH_MP mmio_pcs_min_index_is_SOME o check (fun th ->
          is_eq(concl th) && rand(concl th) = `SOME (i:num)`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `op:shmem_op`) THEN
      EXISTS_TAC `op:shmem_op` THEN ASM_REWRITE_TAC[] THEN
      CASES_ON `op:shmem_op` THEN CASE_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN STRIP_TAC THEN
      FIRST_ASSUM(fun eq -> FIRST_X_ASSUM(fun imp -> MP_TAC (MP imp eq))) THEN
      MESON_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> let c = concl th in
        if is_eq c && is_comb(rand c) && is_var(rand(rand c)) && not(rand(rand c) = `i:num`) &&
           (try fst(dest_const(fst(strip_comb(lhand c)))) = "mmio_pcs_min_index"
            with Failure _ -> false)
        then MP_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `machine_config_halt_pc (mc_conf:(A,B,C)machine_config)`))
          (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th)))
      THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\x. ?s. x = ExtCall s)
                  (TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[EVERY_EL] THEN
    SUBGOAL_THEN `i <= LENGTH (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`
      ASSUME_TAC THENL
     [ACCEPT_TAC(CONJUNCT1(MATCH_MP mmio_pcs_min_index_is_SOME (ASSUME
        `mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
         SOME i`)));
      ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_TAKE; EL_TAKE] THEN
    MATCH_ACCEPT_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP mmio_pcs_min_index_is_SOME (ASSUME
        `mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
         SOME i`))));
    ALL_TAC] THEN
  SUBGOAL_THEN `get_shmem_info (code2:((A)sec)list)
      (val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)))
      (TAKE i (machine_config_ffi_names mc_conf)) [] =
      (machine_config_ffi_names mc_conf, new_shmem_info)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
      `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
      `code2:((A)sec)list`;
      `val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B))`;
      `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
      `new_ffi_names:ffiname list`; `shmem_info:shmem_info_num list`]
      LTTP4AUX_get_shmem_info_shift) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(rand(concl th)) &&
        fst(dest_var(rand(concl th))) = "new_ffi_names" then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[TAKE_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
    `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
    `0`; `code2:((A)sec)list`;
    `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
    `val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B))`;
    `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`;
    `new_shmem_info:shmem_info_num list`] get_shmem_info_ok_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cbspace + LENGTH (prog_to_bytes (code2:((A)sec)list)) < dimword (:A)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A") (LABEL_TAC "B")) THEN
  REWRITE_TAC[share_mem_domain_code_rel_def] THEN
  SUBGOAL_THEN `!xe. MEM xe (MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info)
                    ==> val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                              (ms:B)) <= xe /\ xe < dimword (:A)` (LABEL_TAC "mem") THENL
   [X_GEN_TAC `xe:num` THEN DISCH_THEN(LABEL_TAC "memx") THEN CONJ_TAC THENL
     [USE_THEN "memx" MP_TAC THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && is_var(lhand(concl th)) &&
          fst(dest_var(lhand(concl th))) = "new_shmem_info" then
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
      REWRITE_TAC[MEM_MAP; shmem_info_num_INFO.ri_accfupds; K_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[shmem_info_num_INFO.ri_accfupds; K_THM; LE_ADD];
      ALL_TAC] THEN
    USE_THEN "memx" MP_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhand(concl th)) &&
        (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "MAP" with Failure _ -> false) &&
        (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "DROP" with Failure _ -> false)
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[GSYM MAP_DROP; MEM_MAP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[w2n_lt];
    ALL_TAC] THEN
  SUBGOAL_THEN `!pc' line. asm_fetch_aux pc' (code2:((A)sec)list) = SOME line /\
                  0 < LENGTH (line_bytes line)
       ==> !a. a < LENGTH (line_bytes line)
               ==> a + pos_val pc' 0 code2 < LENGTH (prog_to_bytes code2) /\
                   ~MEM (word_add (word_add (target_get_pc (machine_config_target
                          (mc_conf:(A,B,C)machine_config)) (ms:B)) (word a))
                          (word (pos_val pc' 0 code2)))
                        (TAKE i (machine_config_ffi_entry_pcs mc_conf))` (LABEL_TAC "take")
  THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`pc':num`; `0`; `code2:((A)sec)list`; `0`;
        `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
        `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
        `line:(A)line`] asm_fetch_aux_pos_val_SUC) THEN
      MP_TAC(ISPECL [`pc' + 1`; `0`; `code2:((A)sec)list`;
        `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
        `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
        `0`] pos_val_bound) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `a < LENGTH (line_bytes (line:(A)line))` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`code2:((A)sec)list`; `mc_conf:(A,B,C)machine_config`; `i:num`;
      `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
      `ms:B`; `t:(A)asm_state`; `dm:A word->bool`; `pc':num`; `line:(A)line`; `a:num`]
      asm_fetch_NOT_ffi_entry_pcs) THEN
    REWRITE_TAC[LTTP4AUX_neg_off] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `cbspace + LENGTH (prog_to_bytes (code2:((A)sec)list)) < dimword (:A)` THEN
      ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
        (try fst(dest_const(fst(strip_comb(concl th)))) = "bytes_in_mem" with Failure _ -> false) &&
        (try fst(dest_const(fst(strip_comb(hd(snd(strip_comb(concl th))))))) = "target_get_pc"
         with Failure _ -> false))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`pc':num`; `op:memop`; `re:num`; `a:(A)addr`; `inst:byte list`;
      `len:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> let c = concl th in
      if is_eq c && is_comb(rand c) && is_var(rand(rand c)) && not(rand(rand c) = `i:num`) &&
         (try fst(dest_const(fst(strip_comb(lhand c)))) = "mmio_pcs_min_index"
          with Failure _ -> false)
      then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `0 < LENGTH (line_bytes (Asm (ShareMem op re a) inst len:(A)line))`
      ASSUME_TAC THENL
     [REWRITE_TAC[line_bytes_def] THEN
      MP_TAC(ISPECL [`pc':num`; `0`; `code2:((A)sec)list`;
        `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
        `labs:(num spt)spt`; `TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
        `Asm (ShareMem op re a) inst len:(A)line`] all_enc_ok_asm_fetch_aux_IMP_line_ok) THEN
      ASM_REWRITE_TAC[line_ok_def; enc_with_nop_thm] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
        `cbw_to_asm (ShareMem op re (a:(A)addr))`] enc_ok_LENGTH_GT_0) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) = `inst:byte list`
        then SUBST1_TAC th else NO_TAC) THEN
      REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "take" (MP_TAC o SPEC `0` o C MP (CONJ (ASSUME
      `asm_fetch_aux pc' (code2:((A)sec)list) = SOME (Asm (ShareMem op re a) inst len)`)
      (ASSUME `0 < LENGTH (line_bytes (Asm (ShareMem op re a) inst len:(A)line))`)) o
      SPECL [`pc':num`; `Asm (ShareMem op re a) inst len:(A)line`]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN STRIP_TAC THEN
    USE_THEN "A" (MP_TAC o C MP (CONJ (ASSUME
      `asm_fetch_aux pc' (code2:((A)sec)list) = SOME (Asm (ShareMem op re a) inst len)`)
      (ASSUME `mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
               SOME i`)) o
      SPECL [`pc':num`; `op:memop`; `re:num`; `a:(A)addr`; `inst:byte list`; `len:num`;
             `i:num`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `index:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `index + i` THEN REWRITE_TAC[LE_ADDR] THEN
    SUBGOAL_THEN `i <= LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `i + LENGTH (shmem_info:shmem_info_num list) =
                   LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                          (ms:B)) + pos_val pc' 0 (code2:((A)sec)list) < dimword (:A)`
        ASSUME_TAC THENL
       [USE_THEN "mem" (MP_TAC o SPEC `val (target_get_pc (machine_config_target
           (mc_conf:(A,B,C)machine_config)) (ms:B)) + pos_val pc' 0 (code2:((A)sec)list)`) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC find_index_is_MEM THEN MAP_EVERY EXISTS_TAC [`0`; `index:num`] THEN
          FIRST_ASSUM ACCEPT_TAC;
          SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `find_index (word_add (target_get_pc (machine_config_target
                      (mc_conf:(A,B,C)machine_config)) (ms:B)) (word (pos_val pc' 0
                          (code2:((A)sec)list))))
                      (DROP i (machine_config_ffi_entry_pcs mc_conf)) 0 = SOME index`
        ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[GSYM find_index_MAP_w2n] THEN
        ASM_SIMP_TAC[MISC3AUX_VAL_WORD_ADD_LT; MAP_DROP] THEN
        FIRST_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhand(concl th)) &&
            (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "MAP" with Failure _ ->
                false) &&
            (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "DROP" with Failure _ -> false)
          then REWRITE_TAC[SYM th] else NO_TAC) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [GSYM (ISPECL [`i:num`;
        `machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config)`] TAKE_DROP)] THEN
      REWRITE_TAC[find_index_APPEND] THEN
      MP_TAC(ISPECL [`TAKE i (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))`;
        `word_add (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B))
           (word (pos_val pc' 0 (code2:((A)sec)list)))`; `0`] find_index_NOT_MEM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[find_index_shift_0] THEN ASM_SIMP_TAC[LENGTH_TAKE; ADD_CLAUSES] THEN
      REWRITE_TAC[OPTION_MAP_DEF];
      ALL_TAC] THEN
    SUBGOAL_THEN `?q r. get_memop_info op = (q,r:byte)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhand(concl th)) &&
        fst(dest_var(lhand(concl th))) = "new_shmem_info" then SUBST_ALL_TAC th else NO_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      t = `get_memop_info op`)) (concl th) && not(is_eq(concl th) &&
      lhand(concl th) = `get_memop_info op`))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `index < LENGTH (shmem_info:shmem_info_num list)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP find_index_LESS_LENGTH o check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "find_index" with Failure _ ->
            false) &&
        can (find_term (fun t -> t = `shmem_info:shmem_info_num list`)) (concl th))) THEN
      REWRITE_TAC[LENGTH_MAP] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "shmem_info_num_REC"
       with Failure _ -> false))) THEN
    ASM_SIMP_TAC[EL_MAP] THEN
    DISCH_THEN(fun th -> MAP_EVERY (fun acc -> MP_TAC (AP_TERM acc th))
      [`shmem_info_num_nbytes`; `shmem_info_num_addr_reg`; `shmem_info_num_addr_off`;
       `shmem_info_num_reg`; `shmem_info_num_exit_pc`]) THEN
    REWRITE_TAC[shmem_info_num_INFO.ri_accessors; shmem_info_num_INFO.ri_accfupds; K_THM] THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    SIMP_TAC[MAP_ZIP; MEM_ZIP; LENGTH_LIST_OF_SEQ; LENGTH_MAP; ALL_DISTINCT_GENLIST] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `index:num` THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP; PAIR_EQ; LENGTH_MAP] THEN
    REWRITE_TAC[shmem_info_num_INFO.ri_accessors; shmem_info_num_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [CASES_ON `a:(A)addr` THEN CASE_REWRITE_TAC[WORD_VAL];
      REWRITE_TAC[WORD_ADD; WORD_VAL]];
    MAP_EVERY X_GEN_TAC [`pc':num`; `line:(A)line`] THEN STRIP_TAC THEN
    USE_THEN "B" (MP_TAC o C MP (CONJ (ASSUME
      `asm_fetch_aux pc' (code2:((A)sec)list) = SOME line`) (ASSUME
      `!op re (a:(A)addr) inst len. ~(line = Asm (ShareMem op re a) inst len)`)) o
      SPECL [`pc':num`; `line:(A)line`]) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `x:A word` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `aa:num` STRIP_ASSUME_TAC)) THEN
    USE_THEN "take" (MP_TAC o C MP (ASSUME `aa < LENGTH (line_bytes (line:(A)line))`) o
      SPEC `aa:num` o C MP (CONJ (ASSUME
      `asm_fetch_aux pc' (code2:((A)sec)list) = SOME line`)
      (ARITH_RULE `aa < LENGTH (line_bytes (line:(A)line)) ==> 0 < LENGTH (line_bytes line)`
        |> C MP (ASSUME `aa < LENGTH (line_bytes (line:(A)line))`))) o
      SPECL [`pc':num`; `line:(A)line`]) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `MEM (val (x:A word)) (MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info)`
      ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhand(concl th)) &&
          (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "MAP" with Failure _ -> false) &&
          (try fst(dest_const(fst(strip_comb(rand(concl th))))) = "DROP" with Failure _ -> false)
        then REWRITE_TAC[th] else NO_TAC) THEN
      REWRITE_TAC[GSYM MAP_DROP] THEN MATCH_MP_TAC MEM_MAP_f THEN
      UNDISCH_TAC `MEM (x:A word) (machine_config_ffi_entry_pcs
          (mc_conf:(A,B,C)machine_config))` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM (ISPECL [`i:num`;
        `machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config)`] TAKE_DROP)] THEN
      REWRITE_TAC[MEM_APPEND] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "mem" (STRIP_ASSUME_TAC o C MP (ASSUME
      `MEM (val (x:A word)) (MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info)`) o
      SPEC `val (x:A word)`) THEN
    MP_TAC(ISPECL [`target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)`;
      `aa + pos_val pc' 0 (code2:((A)sec)list)`;
      `val (x:A word) - val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                         (ms:B))`] LTTP4AUX_val_add_eq) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `aa + pos_val pc' 0 (code2:((A)sec)list) < LENGTH (prog_to_bytes code2)` THEN
        UNDISCH_TAC `cbspace + LENGTH (prog_to_bytes (code2:((A)sec)list)) < dimword (:A)` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `word_add (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                      (ms:B)) (word (aa + pos_val pc' 0 (code2:((A)sec)list))) = x` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]; ALL_TAC] THEN
      UNDISCH_TAC `val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                     (ms:B)) <= val (x:A word)` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `val (x:A word)` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `line_bytes (line:(A)line)`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "val" with Failure _ -> false)) (concl th)))
    THEN REWRITE_TAC[ASSUME
      `MEM (val (x:A word)) (MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info)`] THEN
    EXISTS_TAC `aa:num` THEN REWRITE_TAC[ASSUME `aa < LENGTH (line_bytes (line:(A)line))`] THEN
    UNDISCH_TAC `aa + pos_val pc' 0 (code2:((A)sec)list) =
                 val (x:A word) - val (target_get_pc (machine_config_target
                   (mc_conf:(A,B,C)machine_config)) (ms:B))` THEN
    UNDISCH_TAC `val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                   (ms:B)) <= val (x:A word)` THEN ARITH_TAC;
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_var(lhand(concl th)) &&
        fst(dest_var(lhand(concl th))) = "sdm" then SUBST_ALL_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 10516 *)
let make_init_simp = prove
 (`!(a:(A,B,C)machine_config) (b:(FFI)ffi_state) f g h i (j:B) (k:((A)sec)list)
     (l:D->((A)sec)list->(byte list#D)option) m n p.
     lab_state_ffi (lab_to_targetProof_make_init a b f g h i j k l m n p) = b /\
     lab_state_pc (lab_to_targetProof_make_init a b f g h i j k l m n p) = 0 /\
     lab_state_code (lab_to_targetProof_make_init a b f g h i j k l m n p) = k`,
  REWRITE_TAC[lab_to_targetProof_make_init_def] THEN SIMP[]);;

let _ = cake_add_simps [make_init_simp];;

(* HOL4 line 10524: Theorem semantics_make_init = machine_sem_EQ_sem |>     *)
(* ... |> MATCH_MP (MATCH_MP IMP_LEMMA IMP_state_rel_make_init) |> ... (a  *)
(* derived theorem: encoder_correct, the hypotheses of                      *)
(* IMP_state_rel_make_init and that of machine_sem_EQ_sem)                  *)
let semantics_make_init = prove
 (`!(mc_conf:(A,B,C)machine_config) (code:((A)sec)list) coracle labs code2 i clock (ms:B)
     cbspace (t:(A)asm_state) m dm sdm new_ffi_names shmem_info new_shmem_info
     (ffi:(FFI)ffi_state).
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_good_code (target_config (machine_config_target mc_conf)) LN code /\
     mc_conf_ok mc_conf /\
     (no_share_mem_inst code
      ==> compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes code2))
            (target_config (machine_config_target mc_conf)) (machine_config_ffi_names mc_conf)) /\
     list_subset (FILTER (\x. ?s. x = ExtCall s) (find_ffi_names code))
       (TAKE i (machine_config_ffi_names mc_conf)) /\
     remove_labels clock (target_config (machine_config_target mc_conf)) 0 LN
       (TAKE i (machine_config_ffi_names mc_conf)) code = SOME (code2,labs) /\
     good_init_state mc_conf ms (prog_to_bytes code2) cbspace t m dm sdm /\
     get_shmem_info code2 0 [] [] = (new_ffi_names,shmem_info) /\
     new_shmem_info =
       MAP (\rec. shmem_info_num_entry_pc_fupd
                    (K (val (target_get_pc (machine_config_target mc_conf) ms) +
                        shmem_info_num_entry_pc rec))
                    (shmem_info_num_exit_pc_fupd
                       (K (val (target_get_pc (machine_config_target mc_conf) ms) +
                           shmem_info_num_exit_pc rec)) rec)) shmem_info /\
     DROP i (machine_config_ffi_names mc_conf) = new_ffi_names /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
     MAP (\rec. shmem_info_num_entry_pc rec) new_shmem_info =
       DROP i (MAP val (machine_config_ffi_entry_pcs mc_conf)) /\
     machine_config_mmio_info mc_conf =
       ZIP (list_of_seq (\index. index + i) (LENGTH new_shmem_info))
           (MAP (\rec. (shmem_info_num_nbytes rec,
                        Addr (shmem_info_num_addr_reg rec) (word (shmem_info_num_addr_off rec)),
                        shmem_info_num_reg rec,
                        word (shmem_info_num_exit_pc rec))) new_shmem_info) /\
     no_install_or_no_share_mem code (machine_config_ffi_names mc_conf) /\
     (!bn. bn < cbspace
           ==> ~MEM (word_add (word_add (word bn) (word (LENGTH (prog_to_bytes code2))))
                       (target_get_pc (machine_config_target mc_conf) ms))
                    (TAKE i (machine_config_ffi_entry_pcs mc_conf))) /\
     ~(lab_semantics
         (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
            (compile_lab (target_config (machine_config_target mc_conf)))
            (word_add (target_get_pc (machine_config_target mc_conf) ms)
               (word (LENGTH (prog_to_bytes code2))))
            cbspace coracle) = Fail)
     ==> machine_sem mc_conf ffi ms =
         {lab_semantics
            (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
               (compile_lab (target_config (machine_config_target mc_conf)))
               (word_add (target_get_pc (machine_config_target mc_conf) ms)
                  (word (LENGTH (prog_to_bytes code2))))
               cbspace coracle)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`;
    `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms:B)`; `ms:B`;
    `lab_to_targetProof_make_init (mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
       (t:(A)asm_state) m dm sdm (ms:B) (code:((A)sec)list)
       (compile_lab (target_config (machine_config_target mc_conf)))
       (word_add (target_get_pc (machine_config_target mc_conf) ms)
          (word (LENGTH (prog_to_bytes (code2:((A)sec)list))))) cbspace coracle`]
    machine_sem_EQ_sem) THEN
  REWRITE_TAC[make_init_simp] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[init_ok_def; oracle_tie_make_init] THEN
  MAP_EVERY EXISTS_TAC [`code2:((A)sec)list`; `labs:(num spt)spt`; `t:(A)asm_state`] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code:((A)sec)list`;
      `coracle:num->lab_to_target_config#((A)sec)list`;
    `labs:(num spt)spt`; `code2:((A)sec)list`; `i:num`; `clock:num`; `ms:B`; `cbspace:num`;
    `t:(A)asm_state`; `m:A word->(A)word_loc`; `dm:A word->bool`; `sdm:A word->bool`;
    `new_ffi_names:ffiname list`; `shmem_info:shmem_info_num list`;
    `new_shmem_info:shmem_info_num list`; `ffi:(FFI)ffi_state`] IMP_state_rel_make_init) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 10540 *)
let make_init_filter_skip = prove
 (`!(mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (t:(A)asm_state) m dm sdm (ms:B)
     (code:((A)sec)list) cbpos cbspace (coracle:num->lab_to_target_config#((A)sec)list).
     lab_semantics
       (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms (filter_skip code)
          (compile_lab (target_config (machine_config_target mc_conf))) cbpos cbspace
          ((\(a,b). (a,filter_skip b)) o coracle)) =
     lab_semantics
       (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
          (\c p. compile_lab (target_config (machine_config_target mc_conf)) c (filter_skip p))
          cbpos cbspace coracle)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC filter_skip_semantics THEN
  REWRITE_TAC[lab_to_targetProof_make_init_def] THEN SIMP[] THEN
  EXISTS_TAC
    `compile_lab (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))` THEN
  SIMP[]);;

(* HOL4 line 10555 *)
let find_ffi_names_filter_skip = prove
 (`!(code:((A)sec)list). find_ffi_names (filter_skip code) = find_ffi_names code`,
  MATCH_MP_TAC num_pcs_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[filter_skip_def];
    ASM_REWRITE_TAC[filter_skip_def; FILTER; find_ffi_names_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MESON[th]
    `find_ffi_names (filter_skip (CONS (Section k xs) rest)) =
     find_ffi_names (CONS (Section k xs) (rest:((A)sec)list))`)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[filter_skip_def; FILTER] THEN DISCH_TAC THEN
  ASM_CASES_TAC `not_skip (x:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [find_ffi_names_def] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [find_ffi_names_def] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[STACKPROPSAUX_not_skip_eq]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[find_ffi_names_def] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 line 10564 *)
let all_enc_ok_pre_filter_skip = prove
 (`!(code:((A)sec)list) c. ALL (sec_ok_pre c) code ==> ALL (sec_ok_pre c) (filter_skip code)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def; ALL] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[filter_skip_def; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `sec_ok_pre (c:(A)asm_config) (Section a0 a1)` THEN
  REWRITE_TAC[sec_ok_pre_def; GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[]);;

(* HOL4 line 10573 *)
let MAP_Section_num_filter_skip = prove
 (`!(code:((A)sec)list). MAP Section_num (filter_skip code) = MAP Section_num code`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def; MAP] THEN
  CASES_ON `h:(A)sec` THEN ASM_REWRITE_TAC[filter_skip_def; MAP; lab_Section_num_def]);;

let _ = cake_add_simps [MAP_Section_num_filter_skip];;

(* HOL4 line 10580 *)
let filter_skip_extract_labels = prove
 (`!(code:((A)sec)list).
     MAP (lab_extract_labels o Section_lines) (filter_skip code) =
     MAP (lab_extract_labels o Section_lines) code`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def; MAP] THEN
  CASES_ON `h:(A)sec` THEN ASM_REWRITE_TAC[filter_skip_def; MAP; lab_Section_lines_def; o_THM;
    CONS_11] THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CASES_ON `h:(A)line` THEN ASM_REWRITE_TAC[lab_extract_labels_def];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[STACKPROPSAUX_not_skip_eq]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[lab_extract_labels_def]]);;

let _ = cake_add_simps [filter_skip_extract_labels];;

(* HOL4 line 10591 *)
let get_code_labels_filter_skip = prove
 (`!(code:((A)sec)list). lab_get_code_labels (filter_skip code) = lab_get_code_labels code`,
  SUBGOAL_THEN
   `!l. UNIONS (IMAGE line_get_code_labels (set_of_list (FILTER not_skip l))) =
        UNIONS (IMAGE line_get_code_labels (set_of_list (l:((A)line)list)))`
  ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[set_of_list; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[STACKPROPSAUX_not_skip_eq]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[line_get_code_labels_def; UNION_EMPTY];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def] THEN
  CASES_ON `h:(A)sec` THEN
  ASM_REWRITE_TAC[filter_skip_def; get_code_labels_cons; sec_get_code_labels_def]);;

let _ = cake_add_simps [get_code_labels_filter_skip];;

(* HOL4 line 10606 *)
let get_labels_filter_skip = prove
 (`!(code:((A)sec)list). lab_get_labels (filter_skip code) = lab_get_labels code`,
  SUBGOAL_THEN
   `!l. UNIONS (IMAGE line_get_labels (set_of_list (FILTER not_skip l))) =
        UNIONS (IMAGE line_get_labels (set_of_list (l:((A)line)list)))`
  ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[set_of_list; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[STACKPROPSAUX_not_skip_eq]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[line_get_labels_def; UNION_EMPTY];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def] THEN
  CASES_ON `h:(A)sec` THEN
  ASM_REWRITE_TAC[filter_skip_def; get_labels_cons; sec_get_labels_def]);;

let _ = cake_add_simps [get_labels_filter_skip];;

(* HOL4 line 10620 *)
let implements_intro_gen = prove
 (`!b x y. (b /\ ~(x = Fail) ==> y = {x}) ==> b ==> implements' T y {x}`,
  REWRITE_TAC[implements'_def; extend_with_resource_limit'_def] THEN SIMP[] THEN
  MESON_TAC[]);;

(* HOL4 line 10627 *)
let find_ffi_names_ALL_DISTINCT = prove
 (`!(code:((A)sec)list). ALL_DISTINCT (find_ffi_names code)`,
  MATCH_MP_TAC num_pcs_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[find_ffi_names_def; ALL_DISTINCT];
    ASM_REWRITE_TAC[find_ffi_names_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MESON[th]
    `ALL_DISTINCT (find_ffi_names (CONS (Section k xs) (rest:((A)sec)list)))`)) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [find_ffi_names_def] THEN
  REPEAT TOP_CASE_TAC THEN ASM_REWRITE_TAC[list_add_if_fresh_thm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 10637 *)
let not_not_skip_IMP_Skip = prove
 (`!(inst':(A)line). ~not_skip inst' ==> ?l n. inst' = Asm (Asmi (asm_Inst asm_Skip)) l n`,
  REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN MESON_TAC[]);;

(* HOL4 line 10644 *)
let asm_fetch_aux_filter_skip = prove
 (`!(code:((A)sec)list) p inst'.
     asm_fetch_aux p (filter_skip code) = SOME inst' /\ not_skip inst'
     ==> ?p'. asm_fetch_aux p' code = SOME inst'`,
  SUBGOAL_THEN
   `!(inst':(A)line) (code:((A)sec)list) p.
     asm_fetch_aux p (filter_skip code) = SOME inst' /\ not_skip inst'
     ==> ?p'. asm_fetch_aux p' code = SOME inst'`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN MATCH_MP_TAC num_pcs_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[filter_skip_def; asm_fetch_aux_def; option_DISTINCT];
    REWRITE_TAC[filter_skip_def; FILTER; STACKPROPSAUX_fetch_thms] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MESON[th]
   `!p. asm_fetch_aux p (filter_skip (CONS (Section k xs) rest)) = SOME (inst':(A)line) /\
        not_skip inst'
        ==> ?p'. asm_fetch_aux p' (CONS (Section k xs) (rest:((A)sec)list)) = SOME inst'`)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[filter_skip_def; FILTER] THEN DISCH_TAC THEN
  GEN_TAC THEN ASM_CASES_TAC `is_Label (x:(A)line)` THENL
   [ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `not_skip (x:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN EXISTS_TAC `q + 1` THEN
    ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms]] THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms; option_INJ] THEN STRIP_TAC THEN
    EXISTS_TAC `0` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
  ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN EXISTS_TAC `q + 1` THEN
  ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms]);;

(* HOL4 line 10688 *)
let IMP_asm_fetch_aux_filter_skip = prove
 (`!p (code:((A)sec)list) i.
     asm_fetch_aux p code = SOME i /\ not_skip i
     ==> ?p'. asm_fetch_aux p' (filter_skip code) = SOME i`,
  SUBGOAL_THEN
   `!(i:(A)line) (code:((A)sec)list) p.
     asm_fetch_aux p code = SOME i /\ not_skip i
     ==> ?p'. asm_fetch_aux p' (filter_skip code) = SOME i`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN MATCH_MP_TAC num_pcs_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[filter_skip_def; asm_fetch_aux_def; option_DISTINCT];
    REWRITE_TAC[filter_skip_def; FILTER; STACKPROPSAUX_fetch_thms] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MESON[th]
   `!p. asm_fetch_aux p (CONS (Section k xs) (rest:((A)sec)list)) = SOME (i:(A)line) /\
        not_skip i
        ==> ?p'. asm_fetch_aux p' (filter_skip (CONS (Section k xs) rest)) = SOME i`)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[filter_skip_def; FILTER] THEN DISCH_TAC THEN
  GEN_TAC THEN ASM_CASES_TAC `is_Label (x:(A)line)` THENL
   [SUBGOAL_THEN `not_skip (x:(A)line)` ASSUME_TAC THENL
     [REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN STRIP_TAC THEN
      UNDISCH_TAC `is_Label (x:(A)line)` THEN ASM_REWRITE_TAC[is_Label_def];
      ALL_TAC] THEN
    ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms; option_INJ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    EXISTS_TAC `0` THEN ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
  ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  ASM_CASES_TAC `not_skip (x:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `q + 1` THEN ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms];
    EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 10706 *)
let no_share_mem_filter_skip = prove
 (`!(code:((A)sec)list). no_share_mem_inst (filter_skip code) <=> no_share_mem_inst code`,
  GEN_TAC THEN REWRITE_TAC[no_share_mem_inst_def] THEN
  SUBGOAL_THEN `!op re (a:(A)addr) inst len.
    not_skip (Asm (ShareMem op re a) inst len:(A)line)` ASSUME_TAC THENL
   [REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN SIMP[]; ALL_TAC] THEN
  ASM_MESON_TAC[IMP_asm_fetch_aux_filter_skip; asm_fetch_aux_filter_skip]);;

(* HOL4 line 10729 *)
let LTTP4AUX_adjust_pc_thms = prove
 (`(!k n rest. adjust_pc k (CONS (Section n []) rest:((A)sec)list) = adjust_pc k rest) /\
   (!k n l lines rest. is_Label l ==>
      adjust_pc k (CONS (Section n (CONS l lines)) rest:((A)sec)list) =
      adjust_pc k (CONS (Section n lines) rest)) /\
   (!k n l lines rest. ~is_Label l /\ not_skip l ==>
      adjust_pc (k + 1) (CONS (Section n (CONS l lines)) rest:((A)sec)list) =
      adjust_pc k (CONS (Section n lines) rest) + 1) /\
   (!k n l lines rest. ~is_Label l /\ ~not_skip l ==>
      adjust_pc (k + 1) (CONS (Section n (CONS l lines)) rest:((A)sec)list) =
      adjust_pc k (CONS (Section n lines) rest))`,
  REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms]);;

let all_pc_adjust_pc = prove
 (`!(code:((A)sec)list) p. p < num_pcs (filter_skip code) ==> ?k. adjust_pc k code = p`,
  MATCH_MP_TAC num_pcs_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[filter_skip_def; num_pcs_def; LT];
    REWRITE_TAC[filter_skip_def; FILTER; num_pcs_def; LTTP4AUX_adjust_pc_thms] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MESON[th]
   `!p. p < num_pcs (filter_skip (CONS (Section k xs) rest))
        ==> ?k'. adjust_pc k' (CONS (Section k xs) (rest:((A)sec)list)) = p`)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[filter_skip_def; FILTER] THEN DISCH_TAC THEN
  GEN_TAC THEN ASM_CASES_TAC `is_Label (x:(A)line)` THENL
   [SUBGOAL_THEN `not_skip (x:(A)line)` ASSUME_TAC THENL
     [REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN STRIP_TAC THEN
      UNDISCH_TAC `is_Label (x:(A)line)` THEN ASM_REWRITE_TAC[is_Label_def];
      ALL_TAC] THEN
    ASM_SIMP_TAC[num_pcs_def; LTTP4AUX_adjust_pc_thms];
    ALL_TAC] THEN
  ASM_CASES_TAC `p = 0` THENL
   [DISCH_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
  ASM_CASES_TAC `not_skip (x:(A)line)` THEN ASM_REWRITE_TAC[num_pcs_def] THENL
   [REWRITE_TAC[ARITH_RULE `j + 1 < 1 + n <=> j < n`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN EXISTS_TAC `q + 1` THEN
    ASM_SIMP_TAC[LTTP4AUX_adjust_pc_thms];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j + 1`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
    ASM_CASES_TAC `q = 0` THENL
     [UNDISCH_TAC `adjust_pc q (CONS (Section k xs) rest:((A)sec)list) = j + 1` THEN
      ASM_REWRITE_TAC[STACKPROPSAUX_adjust_pc_thms] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC o MATCH_MP STACKPROPSAUX_num_pred) THEN
    EXISTS_TAC `(r + 1) + 1` THEN ASM_SIMP_TAC[LTTP4AUX_adjust_pc_thms]]);;

(* HOL4 line 10801 *)
let no_install_or_no_share_mem_filter_skip = prove
 (`!(code:((A)sec)list) ffi_names.
     no_install_or_no_share_mem code ffi_names
     ==> no_install_or_no_share_mem (filter_skip code) ffi_names`,
  REWRITE_TAC[no_install_or_no_share_mem_def; no_share_mem_filter_skip] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  UNDISCH_TAC `lab_no_install (code:((A)sec)list)` THEN
  REWRITE_TAC[lab_no_install_def] THEN
  SUBGOAL_THEN `!w bytes l. not_skip (LabAsm lab_Install w bytes l:(A)line)` ASSUME_TAC THENL
   [REWRITE_TAC[STACKPROPSAUX_not_skip_eq] THEN SIMP[]; ALL_TAC] THEN
  ASM_MESON_TAC[asm_fetch_aux_filter_skip]);;

(* HOL4 line 10849 *)
let asm_fetch_aux_MEM = prove
 (`!(x:(A)line) l n. MEM x l /\ ~is_Label x ==> ?p. asm_fetch_aux p [Section n l] = SOME x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `0` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  ASM_CASES_TAC `is_Label (h:(A)line)` THENL
   [EXISTS_TAC `q:num` THEN ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms];
    EXISTS_TAC `q + 1` THEN ASM_SIMP_TAC[STACKPROPSAUX_fetch_thms]]);;

(* HOL4 line 10942 *)
let find_ffi_names_EVERY = prove
 (`!(code:((A)sec)list) ls. find_ffi_names code = ls ==> ALL (\x. ?s. x = ExtCall s) ls`,
  SUBGOAL_THEN `!(code:((A)sec)list). ALL (\x. ?s. x = ExtCall s) (find_ffi_names code)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_pcs_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[find_ffi_names_def; ALL];
    ASM_REWRITE_TAC[find_ffi_names_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MESON[th]
    `ALL (\x. ?s. x = ExtCall s) (find_ffi_names (CONS (Section k xs) (rest:((A)sec)list)))`)) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [find_ffi_names_def] THEN
  REPEAT TOP_CASE_TAC THEN ASM_REWRITE_TAC[list_add_if_fresh_thm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL_APPEND; ALL] THEN MESON_TAC[]);;

(* HOL4 line 11012 (lab_to_target$compile is lab_to_target_compile; ZIP of *)
(* equal lengths)                                                             *)
let LTTP4AUX_compile_SOME = prove
 (CASE_TERM `!(asm_conf:(A)asm_config) c (code:((A)sec)list) bytes c'.
     lab_to_target_compile asm_conf c code = SOME (bytes,c')
     ==> ?ffis code2 labs new_ffis shmem_infos.
           (match lab_to_target_config_ffi_names c with
              SOME fs -> ffis = fs /\ list_subset (find_ffi_names code) fs
            | NONE -> ffis = find_ffi_names code) /\
           remove_labels (lab_to_target_config_init_clock c) asm_conf
             (lab_to_target_config_pos c) (lab_to_target_config_labels c) ffis
             (filter_skip code) = SOME (code2,labs) /\
           bytes = prog_to_bytes code2 /\
           get_shmem_info code2 (lab_to_target_config_pos c) [] [] = (new_ffis,shmem_infos) /\
           lab_to_target_config_labels c' = labs /\
           lab_to_target_config_ffi_names c' = SOME (APPEND ffis new_ffis) /\
           lab_to_target_config_shmem_extra c' = shmem_infos`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lab_to_target_compile_def; compile_lab_def; LET_DEF; LET_END_DEF;
              find_ffi_names_filter_skip] THEN
  CASES_ON `lab_to_target_config_ffi_names (c:lab_to_target_config)` THEN CASE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  TOP_CASE_TAC THEN TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rand(concl th))))) THEN
  W(fun (asl,w) ->
    let l = find (fun th -> is_eq(concl th) && is_comb(lhand(concl th)) &&
                  fst(dest_const(fst(strip_comb(lhand(concl th))))) = "get_shmem_info")
                 (map snd asl) in
    let q = hd(snd(strip_comb(lhand(concl l)))) in
    let ab = rand(concl l) in
    let r = find (fun th -> is_eq(concl th) && is_comb(lhand(concl th)) &&
                  fst(dest_const(fst(strip_comb(lhand(concl th))))) = "remove_labels")
                 (map snd asl) in
    let lb = snd(dest_pair(rand(rand(concl r)))) in
    let ffis = hd(tl(rev(snd(strip_comb(lhand(concl r)))))) in
    MAP_EVERY EXISTS_TAC [ffis; q; lb; fst(dest_pair ab); snd(dest_pair ab)]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let LTTP4AUX_sec_labels_ok_filter_skip = prove
 (`!(code:((A)sec)list). ALL sec_labels_ok code ==> ALL sec_labels_ok (filter_skip code)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def; ALL] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[filter_skip_def; ALL; sec_labels_ok_def] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `ALL (sec_label_ok a0) (a1:((A)line)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[]);;

let LTTP4AUX_good_code_filter_skip = prove
 (`!(c:(A)asm_config) labs (code:((A)sec)list).
     lab_to_targetProof_good_code c labs code
     ==> lab_to_targetProof_good_code c labs (filter_skip code)`,
  REWRITE_TAC[lab_to_targetProof_good_code_def; MAP_Section_num_filter_skip;
              get_labels_filter_skip; get_code_labels_filter_skip] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[all_enc_ok_pre_filter_skip; LTTP4AUX_sec_labels_ok_filter_skip] THENL
   [SUBGOAL_THEN (CASE_TERM `sec_ends_with_label:(A)sec->bool =
                  (\s. match s with Section _ ls -> ~NULL ls /\ is_Label (LAST ls))`)
      SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CASES_ON `x:(A)sec` THEN
      CASE_REWRITE_TAC[sec_ends_with_label_def];
      MATCH_MP_TAC sec_ends_with_label_filter_skip THEN
      UNDISCH_TAC `ALL sec_ends_with_label (code:((A)sec)list)` THEN
      MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CASES_ON `x:(A)sec` THEN
      CASE_REWRITE_TAC[sec_ends_with_label_def]];
    UNDISCH_TAC `ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) (code:((A)sec)list)` THEN
    REWRITE_TAC[GSYM ALL_MAP; filter_skip_extract_labels]]);;

let LTTP4AUX_compiler_oracle_ok_filter_skip = prove
 (`!(coracle:num->lab_to_target_config#((A)sec)list) labs n (c:(A)asm_config) ffis.
     compiler_oracle_ok coracle labs n c ffis
     ==> compiler_oracle_ok ((\(a,b). (a,filter_skip b)) o coracle) labs n c ffis`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compiler_oracle_ok_def; o_THM] THEN
  SUBGOAL_THEN `!k. ?x y. (coracle:num->lab_to_target_config#((A)sec)list) k = (x,y)`
    MP_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `xf:num->lab_to_target_config`
    (X_CHOOSE_THEN `yf:num->((A)sec)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[LTTP4AUX_good_code_filter_skip; no_share_mem_filter_skip]);;

let LTTP4AUX_ffi_pc_neq = prove
 (`!(pc:A word) bn l n.
     bn + l + (3 + n) * ffi_offset < dimword (:A)
     ==> ~(word_add (word_add (word bn) (word l)) pc = word_sub pc (word ((3 + n) * ffi_offset)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`bn:num`; `l:num`; `(3 + n) * ffi_offset`; `pc:A word`]
    (WORD_RULE `!a b c (pc:A word). word_sub (word_add (word_add (word a) (word b)) pc)
                   (word_sub pc (word c)) = word (a + b + c):A word`)) THEN
  ASM_REWRITE_TAC[WORD_SUB_REFL] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_0; GSYM dimword_def] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[ffi_offset_def] THEN ARITH_TAC);;

let LTTP4AUX_find_index_EL = prove
 (`!(x:A) l i. find_index x l 0 = SOME i ==> i < LENGTH l /\ EL i l = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP find_index_MEM o MATCH_MP find_index_is_MEM) THEN
  ASM_REWRITE_TAC[option_INJ; ADD_CLAUSES] THEN MESON_TAC[]);;

let semantics_compile_lemma' = prove
 (`!(mc_conf:(A,B,C)machine_config) code coracle (c':lab_to_target_config) bytes
     (asm_conf:(A)asm_config) (c:lab_to_target_config) (ms:B) cbspace (t:(A)asm_state) m dm sdm
     i (ffi:(FFI)ffi_state).
     mc_conf_ok mc_conf /\
     (no_share_mem_inst code
      ==> compiler_oracle_ok coracle (lab_to_target_config_labels c') (LENGTH bytes) asm_conf
            (machine_config_ffi_names mc_conf)) /\
     lab_to_targetProof_good_code (target_config (machine_config_target mc_conf)) LN code /\
     asm_conf = target_config (machine_config_target mc_conf) /\
     lab_to_target_config_labels c = LN /\ lab_to_target_config_pos c = 0 /\
     lab_to_target_compile asm_conf c code = SOME (bytes,c') /\
     lab_to_target_config_ffi_names c' = SOME (machine_config_ffi_names mc_conf) /\
     good_init_state mc_conf ms bytes cbspace t m dm sdm /\
     MAP (\rec. val (target_get_pc (machine_config_target mc_conf) ms) +
                shmem_info_num_entry_pc rec) (lab_to_target_config_shmem_extra c') =
       DROP i (MAP val (machine_config_ffi_entry_pcs mc_conf)) /\
     machine_config_mmio_info mc_conf =
       ZIP (list_of_seq (\index. index + i) (LENGTH (lab_to_target_config_shmem_extra c')))
           (MAP (\rec. (shmem_info_num_nbytes rec,
                        Addr (shmem_info_num_addr_reg rec) (word (shmem_info_num_addr_off rec)),
                        shmem_info_num_reg rec,
                        word_add (word (shmem_info_num_exit_pc rec))
                          (target_get_pc (machine_config_target mc_conf) ms)))
                (lab_to_target_config_shmem_extra c')) /\
     no_install_or_no_share_mem code (machine_config_ffi_names mc_conf) /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
     cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:A) /\
     (!ffis. lab_to_target_config_ffi_names c = SOME ffis
             ==> ALL (\x. ?s. x = ExtCall s) ffis) /\
     ~(lab_semantics
         (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
            (lab_to_target_compile asm_conf)
            (word_add (target_get_pc (machine_config_target mc_conf) ms) (word (LENGTH bytes)))
            cbspace coracle) = Fail)
     ==> machine_sem mc_conf ffi ms =
         {lab_semantics
            (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
               (lab_to_target_compile asm_conf)
               (word_add (target_get_pc (machine_config_target mc_conf) ms) (word (LENGTH bytes)))
               cbspace coracle)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
     fst(dest_var(lhand(concl th))) = "asm_conf")) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LTTP4AUX_compile_SOME) THEN
  DISCH_THEN(X_CHOOSE_THEN `ffis:ffiname list` (X_CHOOSE_THEN `code2:((A)sec)list`
    (X_CHOOSE_THEN `labs:(num spt)spt` (X_CHOOSE_THEN `new_ffis:ffiname list`
    (X_CHOOSE_THEN `shmem_infos:shmem_info_num list` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
     fst(dest_var(lhand(concl th))) = "bytes")) THEN
  SUBGOAL_THEN `machine_config_ffi_names (mc_conf:(A,B,C)machine_config) = APPEND ffis new_ffis`
    ASSUME_TAC THENL
   [UNDISCH_TAC `lab_to_target_config_ffi_names c' =
                 SOME (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\x. ?s. x = ExtCall s) (ffis:ffiname list)` ASSUME_TAC THENL
   [UNDISCH_TAC (CASE_TERM `(match lab_to_target_config_ffi_names c with
                    SOME fs -> ffis = fs /\ list_subset (find_ffi_names (code:((A)sec)list)) fs
                  | NONE -> ffis = find_ffi_names code)`) THEN
    CASES_ON `lab_to_target_config_ffi_names c` THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[find_ffi_names_EVERY];
    ALL_TAC] THEN
  SUBGOAL_THEN `i = LENGTH (ffis:ffiname list)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
                 SOME i` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP get_shmem_info_MappedRead_or_MappedWrite o
      check (fun th -> is_eq(concl th) && is_comb(lhand(concl th)) &&
        fst(dest_const(fst(strip_comb(lhand(concl th))))) = "get_shmem_info")) THEN
    REWRITE_TAC[APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:ffiname list`; `ffis:ffiname list`] mmio_pcs_min_index_APPEND_thm) THEN
    ASM_REWRITE_TAC[GSYM Sh_not_Ext] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lab_to_target_compile (target_config (machine_config_target
      (mc_conf:(A,B,C)machine_config))) =
     (\c p. compile_lab (target_config (machine_config_target mc_conf)) c (filter_skip p)):
       lab_to_target_config->((A)sec)list->(byte list#lab_to_target_config)option`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; lab_to_target_compile_def]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM make_init_filter_skip]) THEN
  REWRITE_TAC[GSYM make_init_filter_skip] THEN
  MATCH_MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `filter_skip (code:((A)sec)list)`;
    `(\(a,b). (a,filter_skip b)) o (coracle:num->lab_to_target_config#((A)sec)list)`;
    `labs:(num spt)spt`; `code2:((A)sec)list`; `LENGTH (ffis:ffiname list)`;
    `lab_to_target_config_init_clock c`; `ms:B`; `cbspace:num`; `t:(A)asm_state`;
    `m:A word->(A)word_loc`; `dm:A word->bool`; `sdm:A word->bool`; `new_ffis:ffiname list`;
    `shmem_infos:shmem_info_num list`;
    `MAP (\rec. shmem_info_num_entry_pc_fupd
                   (K (val (target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                              (ms:B)) +
                       shmem_info_num_entry_pc rec))
                   (shmem_info_num_exit_pc_fupd
                      (K (val (target_get_pc (machine_config_target mc_conf) ms) +
                          shmem_info_num_exit_pc rec)) rec)) shmem_infos`;
    `ffi:(FFI)ffi_state`] semantics_make_init) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `lab_to_target_config_pos c = 0`;
    ASSUME `lab_to_target_config_labels c = LN`; ASSUME `lab_to_target_config_labels c' = labs`;
    ASSUME `lab_to_target_config_shmem_extra c' = shmem_infos`]) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[mc_conf_ok_def]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC LTTP4AUX_good_code_filter_skip THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[no_share_mem_filter_skip] THEN DISCH_TAC THEN
    MATCH_MP_TAC LTTP4AUX_compiler_oracle_ok_filter_skip THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `no_share_mem_inst (code:((A)sec)list)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAKE_LENGTH_APPEND; find_ffi_names_filter_skip] THEN
    SUBGOAL_THEN `FILTER (\x. ?s. x = ExtCall s) (find_ffi_names (code:((A)sec)list)) =
                  find_ffi_names code` SUBST1_TAC THENL
     [REWRITE_TAC[FILTER_EQ_ID] THEN
      MP_TAC(ISPECL [`code:((A)sec)list`; `find_ffi_names (code:((A)sec)list)`]
        find_ffi_names_EVERY) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC (CASE_TERM `(match lab_to_target_config_ffi_names c with
                    SOME fs -> ffis = fs /\ list_subset (find_ffi_names (code:((A)sec)list)) fs
                  | NONE -> ffis = find_ffi_names code)`) THEN
    CASES_ON `lab_to_target_config_ffi_names c` THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[list_subset_refl];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAKE_LENGTH_APPEND] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhand(concl th)) &&
        fst(dest_const(fst(strip_comb(lhand(concl th))))) = "remove_labels"
      then ACCEPT_TAC th else NO_TAC);
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[DROP_LENGTH_APPEND]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAP_o; o_DEF; shmem_info_num_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; GSYM MAP_o; o_DEF; shmem_info_num_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[WORD_ADD; WORD_VAL] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_SYM] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC no_install_or_no_share_mem_filter_skip THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "no_install_or_no_share_mem")) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `bn:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    (try fst(dest_const(fst(strip_comb(concl th)))) = "good_init_state" with Failure _ ->
        false))) THEN
  REWRITE_TAC[good_init_state_def; start_pc_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(rand(concl th)) &&
      is_var(rand(rand(concl th))) &&
      (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "mmio_pcs_min_index"
       with Failure _ -> false) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `LENGTH (ffis:ffiname list) <=
                LENGTH (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhand(concl th)) &&
        fst(dest_const(fst(strip_comb(lhand(concl th))))) = "LENGTH" &&
        rand(lhand(concl th)) = `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MEM_EXISTS_EL; LENGTH_TAKE; NOT_EXISTS_THM] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n < LENGTH (ffis:ffiname list)` THEN ASM_SIMP_TAC[EL_TAKE] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `n < LENGTH (ffis:ffiname list)`) o SPEC `n:num` o
    check (fun th -> is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
      is_comb(lhand(snd(dest_forall(concl th)))) &&
      lhand(snd(dest_forall(concl th))) = mk_comb(mk_comb(`(<):num->num->bool`,
        fst(dest_forall(concl th))), `LENGTH (ffis:ffiname list)`))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP4AUX_find_index_EL o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "find_index"
     with Failure _ -> false))) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) = `asm_state_pc (t:(A)asm_state)`
    then SUBST1_TAC th else NO_TAC) THEN
  MATCH_MP_TAC LTTP4AUX_ffi_pc_neq THEN
  UNDISCH_TAC `bn < cbspace` THEN UNDISCH_TAC `n < LENGTH (ffis:ffiname list)` THEN
  UNDISCH_TAC `cbspace + LENGTH (prog_to_bytes (code2:((A)sec)list)) +
                ffi_offset * (LENGTH (ffis:ffiname list) + 3) < dimword (:A)` THEN
  REWRITE_TAC[ffi_offset_def] THEN ARITH_TAC);;

(* HOL4 line 11167: Theorem semantics_compile_lemma = semantics_compile_lemma' *)
(* |> REWRITE_RULE [CONJ_ASSOC] |> MATCH_MP implements_intro_gen |>          *)
(* REWRITE_RULE [GSYM CONJ_ASSOC] (a derived theorem: the hypotheses of      *)
(* semantics_compile_lemma' without the last, then implements')              *)
let semantics_compile_lemma = prove
 (`!(mc_conf:(A,B,C)machine_config) code coracle (c':lab_to_target_config) bytes
     (asm_conf:(A)asm_config) (c:lab_to_target_config) (ms:B) cbspace (t:(A)asm_state) m dm sdm
     i (ffi:(FFI)ffi_state).
     mc_conf_ok mc_conf /\
     (no_share_mem_inst code
      ==> compiler_oracle_ok coracle (lab_to_target_config_labels c') (LENGTH bytes) asm_conf
            (machine_config_ffi_names mc_conf)) /\
     lab_to_targetProof_good_code (target_config (machine_config_target mc_conf)) LN code /\
     asm_conf = target_config (machine_config_target mc_conf) /\
     lab_to_target_config_labels c = LN /\ lab_to_target_config_pos c = 0 /\
     lab_to_target_compile asm_conf c code = SOME (bytes,c') /\
     lab_to_target_config_ffi_names c' = SOME (machine_config_ffi_names mc_conf) /\
     good_init_state mc_conf ms bytes cbspace t m dm sdm /\
     MAP (\rec. val (target_get_pc (machine_config_target mc_conf) ms) +
                shmem_info_num_entry_pc rec) (lab_to_target_config_shmem_extra c') =
       DROP i (MAP val (machine_config_ffi_entry_pcs mc_conf)) /\
     machine_config_mmio_info mc_conf =
       ZIP (list_of_seq (\index. index + i) (LENGTH (lab_to_target_config_shmem_extra c')))
           (MAP (\rec. (shmem_info_num_nbytes rec,
                        Addr (shmem_info_num_addr_reg rec) (word (shmem_info_num_addr_off rec)),
                        shmem_info_num_reg rec,
                        word_add (word (shmem_info_num_exit_pc rec))
                          (target_get_pc (machine_config_target mc_conf) ms)))
                (lab_to_target_config_shmem_extra c')) /\
     no_install_or_no_share_mem code (machine_config_ffi_names mc_conf) /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
     cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:A) /\
     (!ffis. lab_to_target_config_ffi_names c = SOME ffis
             ==> ALL (\x. ?s. x = ExtCall s) ffis)
     ==> implements' T (machine_sem mc_conf ffi ms)
           {lab_semantics
              (lab_to_targetProof_make_init mc_conf ffi t m dm sdm ms code
                 (lab_to_target_compile asm_conf)
                 (word_add (target_get_pc (machine_config_target mc_conf) ms)
                    (word (LENGTH bytes)))
                 cbspace coracle)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[implements'_def; extend_with_resource_limit'_def; IN_SING] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN
  MP_TAC(SPEC_ALL semantics_compile_lemma') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBSET_REFL]);;

(* HOL4 line 11247 (HOL4 dm INTER byte_aligned: byte_aligned is the set of *)
(* byte-aligned words, as a predicate)                                       *)
let lab_to_targetProof_semantics_compile = prove
 (`!(mc_conf:(A,B,C)machine_config) code coracle (c':lab_to_target_config) bytes
     (asm_conf:(A)asm_config) (c:lab_to_target_config) (ms:B) cbspace (t:(A)asm_state) m dm sdm
     i (ffi:(FFI)ffi_state).
     mc_conf_ok mc_conf /\
     (no_share_mem_inst code
      ==> compiler_oracle_ok coracle (lab_to_target_config_labels c') (LENGTH bytes) asm_conf
            (machine_config_ffi_names mc_conf)) /\
     lab_to_targetProof_good_code asm_conf (lab_to_target_config_labels c) code /\
     asm_conf = target_config (machine_config_target mc_conf) /\
     lab_to_target_config_labels c = LN /\ lab_to_target_config_pos c = 0 /\
     lab_to_target_compile asm_conf c code = SOME (bytes,c') /\
     lab_to_target_config_ffi_names c' = SOME (machine_config_ffi_names mc_conf) /\
     good_init_state mc_conf ms bytes cbspace t m dm sdm /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
     MAP (\rec. val (target_get_pc (machine_config_target mc_conf) ms) +
                shmem_info_num_entry_pc rec) (lab_to_target_config_shmem_extra c') =
       DROP i (MAP val (machine_config_ffi_entry_pcs mc_conf)) /\
     machine_config_mmio_info mc_conf =
       ZIP (list_of_seq (\index. index + i) (LENGTH (lab_to_target_config_shmem_extra c')))
           (MAP (\rec. (shmem_info_num_nbytes rec,
                        Addr (shmem_info_num_addr_reg rec) (word (shmem_info_num_addr_off rec)),
                        shmem_info_num_reg rec,
                        word_add (word (shmem_info_num_exit_pc rec))
                          (target_get_pc (machine_config_target mc_conf) ms)))
                (lab_to_target_config_shmem_extra c')) /\
     no_install_or_no_share_mem code (machine_config_ffi_names mc_conf) /\
     cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:A) /\
     (!ffis. lab_to_target_config_ffi_names c = SOME ffis
             ==> ALL (\x. ?s. x = ExtCall s) ffis)
     ==> implements' T (machine_sem mc_conf ffi ms)
           {lab_semantics
              (lab_to_targetProof_make_init mc_conf ffi t m (dm INTER byte_aligned)
                 (sdm INTER byte_aligned) ms code (lab_to_target_compile asm_conf)
                 (word_add (target_get_pc (machine_config_target mc_conf) ms)
                    (word (LENGTH bytes)))
                 cbspace coracle)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mc_conf_ok_def]; ALL_TAC] THEN
  MATCH_MP_TAC implements'_trans THEN
  EXISTS_TAC
   `{lab_semantics
       (lab_to_targetProof_make_init (mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
          (t:(A)asm_state) m dm (sdm INTER byte_aligned) (ms:B) (code:((A)sec)list)
          (lab_to_target_compile (asm_conf:(A)asm_config))
          (word_add (target_get_pc (machine_config_target mc_conf) ms)
             (word (LENGTH (bytes:byte list))))
          cbspace coracle)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[]
      `!s s'. s' = align_dm s /\ implements' T {lab_semantics s} {lab_semantics (align_dm s)}
              ==> implements' T {lab_semantics (s:(A,lab_to_target_config,FFI)lab_state)}
                                {lab_semantics s'}`) THEN
    ASM_SIMP_TAC[implements_align_dm] THEN
    REWRITE_TAC[align_dm_def; lab_to_targetProof_make_init_def] THEN SIMP[];
    ALL_TAC] THEN
  MATCH_MP_TAC implements'_trans THEN
  EXISTS_TAC
   `{lab_semantics
       (lab_to_targetProof_make_init (mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
          (t:(A)asm_state) m dm sdm (ms:B) (code:((A)sec)list)
          (lab_to_target_compile (asm_conf:(A)asm_config))
          (word_add (target_get_pc (machine_config_target mc_conf) ms)
             (word (LENGTH (bytes:byte list))))
          cbspace coracle)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[]
      `!s s'. s' = align_sdm s /\ implements' T {lab_semantics s} {lab_semantics (align_sdm s)}
              ==> implements' T {lab_semantics (s:(A,lab_to_target_config,FFI)lab_state)}
                                {lab_semantics s'}`) THEN
    ASM_SIMP_TAC[implements_align_sdm] THEN
    REWRITE_TAC[align_sdm_def; lab_to_targetProof_make_init_def] THEN SIMP[];
    ALL_TAC] THEN
  MATCH_MP_TAC semantics_compile_lemma THEN
  EXISTS_TAC `c':lab_to_target_config` THEN EXISTS_TAC `c:lab_to_target_config` THEN
  EXISTS_TAC `i:num` THEN
  UNDISCH_TAC `lab_to_targetProof_good_code (asm_conf:(A)asm_config)
                 (lab_to_target_config_labels c) (code:((A)sec)list)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

