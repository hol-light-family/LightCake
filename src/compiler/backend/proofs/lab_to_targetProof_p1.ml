(* ========================================================================= *)
(* lab_to_targetProof_p1: part 1 of 4 (HOL4 lines 1-2933) of               *)
(* lab_to_targetProof, port of HOL4 compiler/backend/proofs/                 *)
(* lab_to_targetProofScript.sml (CakeML v3479).                              *)
(* Correctness proof for lab_to_target.                                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/backend/lab_filter.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/targetProps.ml";;
needs "compiler/backend/proofs/lab_filterProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering (common to the four parts):                      *)
(* - Records: mc_conf.f is machine_config_f mc_conf, mc.target.f is          *)
(*   target_f (machine_config_target mc), c.f is asm_config_f c, t.f        *)
(*   (asm_state) is asm_state_f t, s.f (labSem state) is lab_state_f s,      *)
(*   cfg.f is lab_to_target_config_f cfg, rec.f is shmem_info_num_f rec;    *)
(*   r with f := v is RECTYPE_f_fupd (K v) r; record literals are            *)
(*   RECTYPE_REC with the fields in declaration order.                       *)
(* - Type variables: (A,B,C)machine_config (A word addresses, B machine     *)
(*   states, HOL4 'a 'state 'b), lab states (A,lab_to_target_config,FFI) or *)
(*   (A,D,FFI)lab_state where HOL4's config type is free.                    *)
(* - Constants of two theories with one HOL4 name: labSem's evaluate and     *)
(*   semantics are lab_evaluate and lab_semantics, targetSem's evaluate is   *)
(*   target_evaluate; HOL4 read_reg r s1 for a labSem state is its Overload  *)
(*   s1.regs r (lab_state_regs s1 r); labSem's word_cmp is wordSem's          *)
(*   wl_word_cmp; labProps' extract_labels, get_labels, get_code_labels and  *)
(*   no_install are lab_ ones; lab_to_target$compile is lab_to_target_compile.*)
(* - HOL4 Overload len_no_lab is written out (see its comment).              *)
(* - Words: hol4/words4.ml (n2w = word, w2n = val, -x = word_neg x, &&  =    *)
(*   word_and, aligned = alignment_aligned, ...); HOL4 a - b on words with   *)
(*   0w is word_sub (word 0) b; $~ o is_Label is (~) o is_Label.             *)
(* - Non-recursive definitions with several clauses: HOL4's NAME_ind (the    *)
(*   case split of its TFL) is stated (line_ok_ind, line_similar_ind);       *)
(*   line_similar is defined by a match (line_similar_DEF), line_similar_def *)
(*   is HOL4's clause theorem (the catch-all over two lines in clause form   *)
(*   is too slow for the kit).                                               *)
(* - Free variables of HOL4 statements are universally quantified, after    *)
(*   HOL4's explicit binders; unused bound variables are left out (comment). *)
(* - HOL4 theorems derived by rules (Theorem X = ..., val X = ... |> RULE)  *)
(*   are stated with their resulting statement.                              *)
(* - LTTP1AUX_ names are local helpers of this part.                         *)

(* ===== PART 1: HOL4 lines 1-2933 ===== *)

(* HOL4 lines 12-16: temp_delsimps, diminish_srw_ss, set_trace, fun say0    *)
(* (simpset settings and an ML printing tactic).                             *)

(* HOL4 line 18 *)
let evaluate_ignore_clocks = prove
 (`!(mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k ms r1 ms1 st1 k' r2 ms2 st2.
     target_evaluate mc_conf ffi k ms = (r1,ms1,st1) /\ ~(r1 = target_TimeOut) /\
     target_evaluate mc_conf ffi k' ms = (r2,ms2,st2) /\ ~(r2 = target_TimeOut)
     ==> (r1,ms1,st1) = (r2,ms2,st2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ffi:(FFI)ffi_state`; `k:num`; `ms:B`;
                 `k':num`; `r1:machine_result`; `ms1:B`; `st1:(FFI)ffi_state`]
         target_evaluate_add_clock) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ffi:(FFI)ffi_state`; `k':num`; `ms:B`;
                 `k:num`; `r2:machine_result`; `ms2:B`; `st2:(FFI)ffi_state`]
         target_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[ADD_SYM]);;

(* HOL4 line 29 *)
let sec_loc_to_pc_def = cake_def
  `sec_loc_to_pc n2 (xs:((A)line)list) =
     if n2 = 0 then SOME 0
     else match xs with
            [] -> NONE
          | CONS z zs ->
              if (?n1 k. z = lab_Label n1 n2 k) then SOME 0
              else if is_Label z then sec_loc_to_pc n2 zs
              else OPTION_MAP SUC (sec_loc_to_pc n2 zs)`;;

(* HOL4 line 39: val sec_loc_to_pc_ind = theorem "sec_loc_to_pc_ind" *)
let sec_loc_to_pc_ind = cake_ind "sec_loc_to_pc";;

(* HOL4 line 41 *)
let sec_loc_to_pc_cons = prove
 (`!n2 (l:(A)line) lines.
     sec_loc_to_pc n2 (CONS l lines) =
     if n2 = 0 \/ (?n1 k. l = lab_Label n1 n2 k) then SOME 0
     else OPTION_MAP (if is_Label l then I else SUC) (sec_loc_to_pc n2 lines)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [sec_loc_to_pc_def] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n2 = 0` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_id]);;

(* HOL4 line 49: Overload len_no_lab[local] =                                *)
(* \xs. LENGTH (FILTER ($~ o is_Label) xs): written out where used, as      *)
(* LENGTH (FILTER ((~) o is_Label) xs)                                       *)

(* HOL4 line 51 *)
let loc_to_pc_thm = prove
 (CASE_TERM `!n1 n2 (ls:((A)sec)list).
     ALL sec_labels_ok ls
     ==> loc_to_pc n1 n2 ls =
         match ls with
           [] -> NONE
         | CONS (Section k xs) ys ->
             if n1 = k then
               (match sec_loc_to_pc n2 xs with
                  NONE -> OPTION_MAP ((+) (LENGTH (FILTER ((~) o is_Label) xs)))
                            (loc_to_pc n1 n2 ys)
                | x -> x)
             else OPTION_MAP ((+) (LENGTH (FILTER ((~) o is_Label) xs))) (loc_to_pc n1 n2 ys)`,
  MATCH_MP_TAC loc_to_pc_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[loc_to_pc_def] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ALL; sec_labels_ok_def] THEN STRIP_TAC THEN CASE_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [loc_to_pc_def] THEN
  CASES_ON `xs:((A)line)list` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[FILTER; LENGTH; plus_0_I; OPTION_MAP_id] THEN
    ONCE_REWRITE_TAC[sec_loc_to_pc_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `n1 = k:num` THEN ASM_CASES_TAC `n2 = 0` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sec_loc_to_pc_cons; FILTER; o_THM] THEN
  RULE_ASSUM_TAC(fun th -> try SPECL [`a0:(A)line`; `a1:((A)line)list`] th
                           with Failure _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; sec_labels_ok_def]) THEN
  CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  ASM_CASES_TAC `k:num = n1 /\ n2 = 0` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(?kk. (a0:(A)line) = lab_Label n1 n2 kk) /\ ~(n2 = 0)` THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 (X_CHOOSE_THEN `kk:num` SUBST_ALL_TAC) ASSUME_TAC) THEN
    UNDISCH_TAC `sec_label_ok k (lab_Label n1 n2 kk:(A)line) /\
                 ALL (sec_label_ok k) (a1:((A)line)list)` THEN
    REWRITE_TAC[sec_label_ok_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP[];
    ALL_TAC] THEN
  ASM_CASES_TAC `k:num = n1` THENL
   [SUBGOAL_THEN `~(n2 = 0 \/ (?n1' k'. (a0:(A)line) = lab_Label n1' n2 k'))`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((?kk. (a0:(A)line) = lab_Label n1 n2 kk) /\ ~(n2 = 0))` THEN
      UNDISCH_TAC `~(n1:num = n1 /\ n2 = 0)` THEN
      UNDISCH_TAC `sec_label_ok n1 (a0:(A)line) /\ ALL (sec_label_ok n1) (a1:((A)line)list)` THEN
      CASES_ON `a0:(A)line` THEN REWRITE_TAC[sec_label_ok_def] THEN
      SIMP[] THEN MESON_TAC[];
      ALL_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `is_Label (a0:(A)line)` THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_imp(rand(concl th))
                                 then MP_TAC th else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[OPTION_MAP_id; LENGTH] THEN
  CASES_ON `sec_loc_to_pc n2 (a1:((A)line)list)` THEN
  CASES_ON `loc_to_pc n1 n2 (ys:((A)sec)list)` THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"] THEN ARITH_TAC);;

(* HOL4 line 93: temp_remove_rules_for_term "step" (a parser setting) *)

(* HOL4 line 95 *)
let enc_with_nop_def = cake_def
  `enc_with_nop (enc:(A)asm->byte list) (b:(A)asm) bytes <=>
     let init = enc b in
     let step = enc (asm_Inst asm_Skip) in
     if LENGTH step = 0 then bytes = init else
       let n = (LENGTH bytes - LENGTH init) DIV LENGTH step in
       bytes = APPEND init (FLAT (REPLICATE n step))`;;

(* HOL4 line 104 *)
let enc_with_nop_thm = prove
 (`!(enc:(A)asm->byte list) (b:(A)asm) bytes.
     enc_with_nop enc b bytes <=>
     ?n. bytes = APPEND (enc b) (FLAT (REPLICATE n (enc (asm_Inst asm_Skip))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[enc_with_nop_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o REWRITE_RULE[LENGTH_EQ_NIL]) THEN
    REWRITE_TAC[FLAT_REPLICATE_NIL; APPEND_NIL];
    ALL_TAC] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_FLAT_REPLICATE; ADD_SUB2] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT]);;

(* HOL4 line 115 *)
let asm_step_nop_def = cake_def
  `asm_step_nop bytes (c:(A)asm_config) (s1:(A)asm_state) i s2 <=>
     bytes_in_memory (asm_state_pc s1) bytes (asm_state_mem s1) (asm_state_mem_domain s1) /\
     enc_with_nop (asm_config_encode c) i bytes /\
     (match asm_config_link_reg c with NONE -> T | SOME r -> asm_state_lr s1 = r) /\
     (asm_state_be s1 <=> asm_config_big_endian c) /\
     asm_state_align s1 = asm_config_code_alignment c /\
     asm_asm i (word_add (asm_state_pc s1) (word (LENGTH bytes))) s1 = s2 /\
     ~asm_state_failed s2 /\
     asm_ok i c`;;

(* HOL4 line 125: val evaluate_nop_step (targetProps'                        *)
(* asm_step_IMP_evaluate_step_find_next |> SIMP_RULE ... for Inst Skip): an *)
(* intermediate step of the proof of evaluate_nop_steps, not stated.         *)

(* HOL4 line 132 *)
let shift_interfer_0 = prove
 (`shift_interfer 0 = (I:(A,B,C)machine_config->(A,B,C)machine_config)`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; shift_interfer_def; shift_seq_def; ADD_CLAUSES; ETA_AX] THEN
  GEN_TAC THEN REWRITE_TAC[machine_config_component_equality] THEN SIMP[]);;

(* HOL4 line 139 *)
let upd_pc_with_pc = prove
 (`!(s1:(A)asm_state). asm_upd_pc (asm_state_pc s1) s1 = s1`,
  GEN_TAC THEN REWRITE_TAC[asm_upd_pc_def; asm_state_component_equality] THEN SIMP[]);;

(* HOL4 line 145 *)
let shift_interfer_twice = prove
 (`!l' l (c:(A,B,C)machine_config).
     shift_interfer l' (shift_interfer l c) = shift_interfer (l + l') c`,
  REWRITE_TAC[shift_interfer_intro] THEN REWRITE_TAC[ADD_SYM]);;

let _ = cake_add_simps [shift_interfer_twice];;

let LTTP1AUX_evaluate_nop_step = prove
 (CASE_TERM `!(c:(A,B,C)machine_config) (s1:(A)asm_state) (ms1:B) (io:(FFI)ffi_state).
     encoder_correct (machine_config_target c) /\
     machine_config_prog_addresses c = asm_state_mem_domain s1 /\
     ffi_entry_pcs_disjoint c s1
       (LENGTH (asm_config_encode (target_config (machine_config_target c))
                  (asm_Inst asm_Skip))) /\
     interference_ok (machine_config_next_interfer c)
       (target_proj (machine_config_target c) (asm_state_mem_domain s1)) /\
     bytes_in_memory (asm_state_pc s1)
       (asm_config_encode (target_config (machine_config_target c)) (asm_Inst asm_Skip))
       (asm_state_mem s1) (asm_state_mem_domain s1) /\
     (match asm_config_link_reg (target_config (machine_config_target c)) with
        NONE -> T
      | SOME r -> asm_state_lr s1 = r) /\
     (asm_state_be s1 <=> asm_config_big_endian (target_config (machine_config_target c))) /\
     asm_state_align s1 = asm_config_code_alignment (target_config (machine_config_target c)) /\
     ~asm_state_failed s1 /\
     target_state_rel (machine_config_target c) s1 ms1
     ==> ?l ms2.
           !k. target_evaluate c io (k + l) ms1 =
               target_evaluate (shift_interfer l c) io k ms2 /\
               find_next_interference c io (k + l) ms1 =
               find_next_interference (shift_interfer l c) io k ms2 /\
               target_state_rel (machine_config_target c)
                 (asm_upd_pc
                    (word_add (asm_state_pc s1)
                       (word (LENGTH (asm_config_encode
                                        (target_config (machine_config_target c))
                                        (asm_Inst asm_Skip))))) s1)
                 ms2 /\ ~(l = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(A,B,C)machine_config`; `s1:(A)asm_state`; `ms1:B`;
                `io:(FFI)ffi_state`; `asm_Inst asm_Skip:(A)asm`]
         asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def; asm_asm_def; asmSem_inst_def; asm_ok_def; inst_ok_def] THEN
  REWRITE_TAC[asm_upd_pc_def] THEN SIMP[]);;

let LTTP1AUX_ffi_entry_pcs_disjoint_shift = prove
 (`!(c:(A,B,C)machine_config) (c':(A,B,C)machine_config) (s1:(A)asm_state) s2 m n.
     machine_config_ffi_entry_pcs c' = machine_config_ffi_entry_pcs c /\
     asm_state_pc s2 = word_add (asm_state_pc s1) (word m) /\
     ffi_entry_pcs_disjoint c s1 (m + n)
     ==> ffi_entry_pcs_disjoint c' s2 n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ffi_entry_pcs_disjoint_def; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
              NOT_IN_EMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A word` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A word`) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  MESON_TAC[ARITH_RULE `a < n ==> m + a < m + n`]);;

let LTTP1AUX_interference_ok_shift = prove
 (`!(c:(A,B,C)machine_config) l (proj:B->D).
     interference_ok (machine_config_next_interfer c) proj
     ==> interference_ok (machine_config_next_interfer (shift_interfer l c)) proj`,
  REWRITE_TAC[interference_ok_def; shift_interfer_def; shift_seq_def;
              (record_info "machine_config").ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

(* HOL4 line 152 *)
let evaluate_nop_steps = prove
 (CASE_TERM `!n (s1:(A)asm_state) (ms1:B) (c:(A,B,C)machine_config) (io:(FFI)ffi_state).
     encoder_correct (machine_config_target c) /\
     machine_config_prog_addresses c = asm_state_mem_domain s1 /\
     ffi_entry_pcs_disjoint c s1
       (n * LENGTH (asm_config_encode (target_config (machine_config_target c))
                      (asm_Inst asm_Skip))) /\
     interference_ok (machine_config_next_interfer c)
       (target_proj (machine_config_target c) (asm_state_mem_domain s1)) /\
     bytes_in_memory (asm_state_pc s1)
       (FLAT (REPLICATE n (asm_config_encode (target_config (machine_config_target c))
                             (asm_Inst asm_Skip))))
       (asm_state_mem s1) (asm_state_mem_domain s1) /\
     (match asm_config_link_reg (target_config (machine_config_target c)) with
        NONE -> T
      | SOME r -> asm_state_lr s1 = r) /\
     (asm_state_be s1 <=> asm_config_big_endian (target_config (machine_config_target c))) /\
     asm_state_align s1 = asm_config_code_alignment (target_config (machine_config_target c)) /\
     ~asm_state_failed s1 /\
     target_state_rel (machine_config_target c) s1 ms1
     ==> ?l ms2.
           !k. target_evaluate c io (k + l) ms1 =
               target_evaluate (shift_interfer l c) io k ms2 /\
               find_next_interference c io (k + l) ms1 =
               find_next_interference (shift_interfer l c) io k ms2 /\
               target_state_rel (machine_config_target c)
                 (asm_upd_pc
                    (word_add (asm_state_pc s1)
                       (word (n * LENGTH (asm_config_encode
                                            (target_config (machine_config_target c))
                                            (asm_Inst asm_Skip))))) s1)
                 ms2`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`0`; `ms1:B`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; shift_interfer_0; I_THM; MULT_CLAUSES; WORD_ADD_0;
                    upd_pc_with_pc];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REPLICATE; FLAT; bytes_in_memory_APPEND]) THEN
  MP_TAC(SPECL [`c:(A,B,C)machine_config`; `s1:(A)asm_state`; `ms1:B`; `io:(FFI)ffi_state`]
    LTTP1AUX_evaluate_nop_step) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "ffi_entry_pcs_disjoint")) (concl th))) THEN
    REWRITE_TAC[ffi_entry_pcs_disjoint_def; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                NOT_IN_EMPTY; MULT_CLAUSES] THEN
    MESON_TAC[ARITH_RULE `a < l ==> a < n * l + l`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `ms2:B` ASSUME_TAC)) THEN
  SUBGOAL_THEN `machine_config_target (shift_interfer l1 (c:(A,B,C)machine_config)) =
                machine_config_target c /\
                machine_config_prog_addresses (shift_interfer l1 c) =
                machine_config_prog_addresses c /\
                machine_config_ffi_entry_pcs (shift_interfer l1 c) =
                machine_config_ffi_entry_pcs c` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[shift_interfer_def] THEN SIMP[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`asm_upd_pc (word_add (asm_state_pc s1)
      (word (LENGTH (asm_config_encode (target_config (machine_config_target
        (c:(A,B,C)machine_config))) (asm_Inst asm_Skip))))) (s1:(A)asm_state)`;
      `ms2:B`; `shift_interfer l1 (c:(A,B,C)machine_config)`; `io:(FFI)ffi_state`] o
      check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[asm_upd_pc_def; (record_info "asm_state").ri_accfupds; K_THM] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LTTP1AUX_ffi_entry_pcs_disjoint_shift THEN
      MAP_EVERY EXISTS_TAC [`c:(A,B,C)machine_config`; `s1:(A)asm_state`;
        `LENGTH (asm_config_encode (target_config (machine_config_target
           (c:(A,B,C)machine_config))) (asm_Inst asm_Skip))`] THEN
      ASM_REWRITE_TAC[(record_info "asm_state").ri_accfupds; K_THM] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "ffi_entry_pcs_disjoint")) (concl th))) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_SYM];
      MATCH_MP_TAC LTTP1AUX_interference_ok_shift THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:num` (X_CHOOSE_THEN `ms3:B` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`l1 + l2:num`; `ms3:B`] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[ARITH_RULE `k + l1 + l2 = (k + l2) + l1`] THEN
  ASM_REWRITE_TAC[shift_interfer_twice] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[asm_upd_pc_def; (record_info "asm_state").ri_accfupds; K_THM] THEN
  SIMP[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; MULT_CLAUSES] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN ARITH_TAC);;

(* HOL4 line 230 *)
let ffi_entry_pcs_disjoint_LENGTH_shorter = prove
 (`!l1 l2 (c:(A,B,C)machine_config) (s1:(A)asm_state).
     ffi_entry_pcs_disjoint c s1 l1 /\ l2 <= l1 ==> ffi_entry_pcs_disjoint c s1 l2`,
  REWRITE_TAC[ffi_entry_pcs_disjoint_def; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
              NOT_IN_EMPTY] THEN
  MESON_TAC[LTE_TRANS]);;

let LTTP1AUX_asm_nonjump = prove
 (`!i (s:(A)asm_state) v w.
     (!x. ~(i = asm_Jump x)) /\ (!r. ~(i = JumpReg r)) /\ (!x. ~(i = asm_Call x)) /\
     (!cmp r ri x. i = asm_JumpCmp cmp r ri x
                   ==> ~asm_word_cmp cmp (read_reg r s) (asm_reg_imm ri s))
     ==> asm_asm i w s = asm_upd_pc w (asm_asm i v s) /\ asm_state_pc (asm_asm i w s) = w`,
  GEN_TAC THEN CASES_ON `i:(A)asm` THEN
  REWRITE_TAC[asm_asm_def; injectivity "asm"; distinctness "asm"] THEN
  SIMP[asm_upd_pc_def] THEN MESON_TAC[]);;

let LTTP1AUX_asm_jump = prove
 (`!i (s:(A)asm_state) v w.
     ~((!x. ~(i = asm_Jump x)) /\ (!r. ~(i = JumpReg r)) /\
       (!cmp r ri x. i = asm_JumpCmp cmp r ri x
                     ==> ~asm_word_cmp cmp (read_reg r s) (asm_reg_imm ri s)))
     ==> asm_asm i w s = asm_asm i v s`,
  GEN_TAC THEN CASES_ON `i:(A)asm` THEN
  REWRITE_TAC[asm_asm_def; injectivity "asm"; distinctness "asm"] THEN
  SIMP[] THEN MESON_TAC[]);;

(* HOL4 line 249 *)
let asm_step_IMP_evaluate_step_nop = prove
 (`!(c:(A,B,C)machine_config) (s1:(A)asm_state) (ms1:B) (io:(FFI)ffi_state) i s2 bytes.
     encoder_correct (machine_config_target c) /\
     machine_config_prog_addresses c = asm_state_mem_domain s1 /\
     ffi_entry_pcs_disjoint c s1 (LENGTH bytes) /\
     interference_ok (machine_config_next_interfer c)
       (target_proj (machine_config_target c) (asm_state_mem_domain s1)) /\
     bytes_in_memory (asm_state_pc s1) bytes (asm_state_mem s2) (asm_state_mem_domain s1) /\
     asm_step_nop bytes (target_config (machine_config_target c)) s1 i s2 /\
     s2 = asm_asm i (word_add (asm_state_pc s1) (word (LENGTH bytes))) s1 /\
     target_state_rel (machine_config_target c) s1 ms1 /\
     (!x. ~(i = asm_Call x))
     ==> ?l ms2.
           !k. target_evaluate c io (k + l) ms1 =
               target_evaluate (shift_interfer l c) io k ms2 /\
               find_next_interference c io (k + l) ms1 =
               find_next_interference (shift_interfer l c) io k ms2 /\
               target_state_rel (machine_config_target c) s2 ms2 /\ ~(l = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[asm_step_nop_def; enc_with_nop_thm] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bytes_in_memory_APPEND; LENGTH_APPEND; LENGTH_FLAT_REPLICATE]) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_FLAT_REPLICATE] THEN
  MP_TAC(SPECL [`c:(A,B,C)machine_config`; `s1:(A)asm_state`; `ms1:B`; `io:(FFI)ffi_state`;
                `i:(A)asm`] asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ffi_entry_pcs_disjoint_LENGTH_shorter THEN
      EXISTS_TAC `LENGTH (asm_config_encode (target_config (machine_config_target
                    (c:(A,B,C)machine_config))) (i:(A)asm)) +
                  n * LENGTH (asm_config_encode (target_config (machine_config_target c))
                                (asm_Inst asm_Skip))` THEN
      ASM_REWRITE_TAC[LE_ADD];
      ASM_MESON_TAC[asm_failed_ignore_new_pc]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` ASSUME_TAC)) THEN
  ASM_CASES_TAC `(!x. ~((i:(A)asm) = asm_Jump x)) /\ (!r. ~(i = JumpReg r)) /\
                 (!cmp r ri x. i = asm_JumpCmp cmp r ri x
                    ==> ~asm_word_cmp cmp (read_reg r (s1:(A)asm_state)) (asm_reg_imm ri s1))`
  THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`i:(A)asm`; `s1:(A)asm_state`;
      `word_add (asm_state_pc (s1:(A)asm_state)) (word (LENGTH (asm_config_encode
         (target_config (machine_config_target (c:(A,B,C)machine_config))) (i:(A)asm))))`;
      `word_add (asm_state_pc (s1:(A)asm_state)) (word (LENGTH (asm_config_encode
         (target_config (machine_config_target (c:(A,B,C)machine_config))) (i:(A)asm)) +
         n * LENGTH (asm_config_encode (target_config (machine_config_target c))
               (asm_Inst asm_Skip))))`] LTTP1AUX_asm_jump) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`l:num`; `ms2:B`] THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`i:(A)asm`; `s1:(A)asm_state`;
      `word_add (asm_state_pc (s1:(A)asm_state)) (word (LENGTH (asm_config_encode
         (target_config (machine_config_target (c:(A,B,C)machine_config))) (i:(A)asm))))`;
      `word_add (asm_state_pc (s1:(A)asm_state)) (word (LENGTH (asm_config_encode
         (target_config (machine_config_target (c:(A,B,C)machine_config))) (i:(A)asm)) +
         n * LENGTH (asm_config_encode (target_config (machine_config_target c))
               (asm_Inst asm_Skip))))`] LTTP1AUX_asm_nonjump) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`i:(A)asm`; `s1:(A)asm_state`;
      `word_add (asm_state_pc (s1:(A)asm_state)) (word (LENGTH (asm_config_encode
         (target_config (machine_config_target (c:(A,B,C)machine_config))) (i:(A)asm))))`;
      `word_add (asm_state_pc (s1:(A)asm_state)) (word (LENGTH (asm_config_encode
         (target_config (machine_config_target (c:(A,B,C)machine_config))) (i:(A)asm))))`]
      LTTP1AUX_asm_nonjump) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s2' = asm_asm i (word_add (asm_state_pc s1) (word (LENGTH (asm_config_encode
         (target_config (machine_config_target (c:(A,B,C)machine_config))) (i:(A)asm)))))
         (s1:(A)asm_state)` THEN
  SUBGOAL_THEN `machine_config_target (shift_interfer l (c:(A,B,C)machine_config)) =
                machine_config_target c /\
                machine_config_prog_addresses (shift_interfer l c) =
                machine_config_prog_addresses c /\
                machine_config_ffi_entry_pcs (shift_interfer l c) =
                machine_config_ffi_entry_pcs c` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[shift_interfer_def] THEN SIMP[]; ALL_TAC] THEN
  SUBGOAL_THEN `asm_state_mem_domain (s2':(A)asm_state) = asm_state_mem_domain s1 /\
                asm_state_lr s2' = asm_state_lr s1 /\
                asm_state_align s2' = asm_state_align s1 /\
                (asm_state_be s2' <=> asm_state_be s1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2'" THEN REWRITE_TAC[asm_consts]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `s2':(A)asm_state`; `ms2:B`; `shift_interfer l (c:(A,B,C)machine_config)`;
                `io:(FFI)ffi_state`] evaluate_nop_steps) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LTTP1AUX_ffi_entry_pcs_disjoint_shift THEN
      MAP_EVERY EXISTS_TAC [`c:(A,B,C)machine_config`; `s1:(A)asm_state`;
        `LENGTH (asm_config_encode (target_config (machine_config_target
           (c:(A,B,C)machine_config))) (i:(A)asm))`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTTP1AUX_interference_ok_shift THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "s2'" THEN ASM_MESON_TAC[asm_mem_ignore_new_pc];
      EXPAND_TAC "s2'" THEN ASM_MESON_TAC[asm_failed_ignore_new_pc]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':num` (X_CHOOSE_THEN `ms3:B` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`l + l':num`; `ms3:B`] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[ARITH_RULE `k + l + l' = (k + l') + l`] THEN
  ASM_REWRITE_TAC[shift_interfer_twice; ADD_EQ_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_REWRITE_TAC[asm_upd_pc_def] THEN SIMP[]);;

(* HOL4 line 349 *)
let lab_lookup_def = cake_def
  `lab_lookup k1 k2 (labs:(num spt)spt) =
     match lookup k1 labs with
       NONE -> NONE
     | SOME f -> lookup k2 f`;;

(* HOL4 line 356 *)
let lab_lookup_IMP = prove
 (`!l1 l2 labs x.
     lab_lookup l1 l2 labs = SOME x ==> find_pos (lab_Lab l1 l2) labs = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lab_lookup_def; find_pos_def; lookup_any_def] THEN
  CASES_ON `lookup l1 (labs:(num spt)spt)` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup l2 (a:num spt)` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 364 *)
let labs_domain_def = cake_def
  `labs_domain (labs:(num spt)spt) = {(n1,n2) | ~(lab_lookup n1 n2 labs = NONE)}`;;

(* HOL4 line 368 *)
let labs_domain_LN = prove
 (`labs_domain LN = {}`,
  REWRITE_TAC[labs_domain_def; lab_lookup_def; lookup_def; EXTENSION; NOT_IN_EMPTY;
              IN_ELIM_THM] THEN
  CASE_REWRITE_TAC[]);;

let _ = cake_add_simps [labs_domain_LN];;

let LTTP1AUX_IN_labs_domain = prove
 (`!labs a b. (a,b) IN labs_domain labs <=> ~(lab_lookup a b labs = NONE)`,
  REWRITE_TAC[labs_domain_def; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 374 *)
let labs_domain_insert = prove
 (`!k (labs:(num spt)spt) (s:num spt).
     ~(k IN domain labs)
     ==> labs_domain (insert k s labs) =
         IMAGE (\n2. (k,n2)) (domain s) UNION labs_domain labs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_UNION; LTTP1AUX_IN_labs_domain; IN_IMAGE;
              PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN REWRITE_TAC[lab_lookup_def; lookup_insert] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[domain_lookup]) THEN
    REWRITE_TAC[domain_lookup] THEN
    CASES_ON `lookup k (labs:(num spt)spt)` THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
    CASES_ON `lookup b (s:num spt)` THEN SIMP[];
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 384 *)
let has_odd_inst_def = cake_def
  `(has_odd_inst ([]:((A)sec)list) <=> F) /\
   (has_odd_inst (CONS (Section k []) xs) <=> has_odd_inst xs) /\
   (has_odd_inst (CONS (Section k (CONS y ys)) xs) <=>
      ~EVEN (line_length y) \/ has_odd_inst (CONS (Section k ys) xs))`;;

let has_odd_inst_ind = cake_ind "has_odd_inst";;

(* HOL4 line 391.  The catch-all clause over two lines makes the clause     *)
(* form slow for the kit: line_similar_DEF is the definition by a match,     *)
(* line_similar_def the HOL4 clause theorem (the three clauses and the six   *)
(* completions of the catch-all, as HOL4's TFL gives them).                  *)
let line_similar_DEF = cake_def
  `line_similar (x:(A)line) (y:(A)line) <=>
     match (x,y) with
       (lab_Label k1 k2 l,lab_Label k1' k2' l') -> k1 = k1' /\ k2 = k2'
     | (Asm b bytes l,Asm b' bytes' l') -> b = b'
     | (LabAsm a w bytes l,LabAsm a' w' bytes' l') -> a = a'
     | _ -> F`;;

let line_similar_def = prove
 (`(!k1 k2 l k1' k2' (l':num).
      line_similar (lab_Label k1 k2 l:(A)line) (lab_Label k1' k2' l') <=>
      k1 = k1' /\ k2 = k2') /\
   (!b bytes l b' bytes' (l':num).
      line_similar (Asm b bytes l:(A)line) (Asm b' bytes' l') <=> b = b') /\
   (!a w bytes l a' w' bytes' (l':num).
      line_similar (LabAsm a w bytes l:(A)line) (LabAsm a' w' bytes' l') <=> a = a') /\
   (!v4 v5 v6 v7 v8 (v9:num).
      line_similar (lab_Label v4 v5 v6:(A)line) (Asm v7 v8 v9) <=> F) /\
   (!v4 v5 v6 v7 v8 v9 (v10:num).
      line_similar (lab_Label v4 v5 v6:(A)line) (LabAsm v7 v8 v9 v10) <=> F) /\
   (!v4 v5 v6 v7 v8 (v9:num).
      line_similar (Asm v4 v5 v6:(A)line) (lab_Label v7 v8 v9) <=> F) /\
   (!v4 v5 v6 v7 v8 v9 (v10:num).
      line_similar (Asm v4 v5 v6:(A)line) (LabAsm v7 v8 v9 v10) <=> F) /\
   (!v4 v5 v6 v7 v8 v9 (v10:num).
      line_similar (LabAsm v4 v5 v6 v7:(A)line) (lab_Label v8 v9 v10) <=> F) /\
   (!v4 v5 v6 v7 v8 v9 (v10:num).
      line_similar (LabAsm v4 v5 v6 v7:(A)line) (Asm v8 v9 v10) <=> F)`,
  REWRITE_TAC[line_similar_DEF] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 398: val line_similar_ind = theorem "line_similar_ind" (the    *)
(* case split of HOL4's TFL, one case per clause of line_similar_def)       *)
let line_similar_ind = prove
 (`!(P:(A)line->(A)line->bool).
     (!k1 k2 l k1' k2' l'. P (lab_Label k1 k2 l) (lab_Label k1' k2' l')) /\
     (!b bytes l b' bytes' l'. P (Asm b bytes l) (Asm b' bytes' l')) /\
     (!a w bytes l a' w' bytes' l'. P (LabAsm a w bytes l) (LabAsm a' w' bytes' l')) /\
     (!v4 v5 v6 v7 v8 v9. P (lab_Label v4 v5 v6) (Asm v7 v8 v9)) /\
     (!v4 v5 v6 v7 v8 v9 v10. P (lab_Label v4 v5 v6) (LabAsm v7 v8 v9 v10)) /\
     (!v4 v5 v6 v7 v8 v9. P (Asm v4 v5 v6) (lab_Label v7 v8 v9)) /\
     (!v4 v5 v6 v7 v8 v9 v10. P (Asm v4 v5 v6) (LabAsm v7 v8 v9 v10)) /\
     (!v4 v5 v6 v7 v8 v9 v10. P (LabAsm v4 v5 v6 v7) (lab_Label v8 v9 v10)) /\
     (!v4 v5 v6 v7 v8 v9 v10. P (LabAsm v4 v5 v6 v7) (Asm v8 v9 v10))
     ==> !v v1. P v v1`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `v:(A)line` THEN CASES_ON `v1:(A)line` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 400 *)
let code_similar_def = cake_def
  `(code_similar ([]:((A)sec)list) ([]:((A)sec)list) <=> T) /\
   (code_similar (CONS (Section s1 lines1) rest1) (CONS (Section s2 lines2) rest2) <=>
      code_similar rest1 rest2 /\ ALL2 line_similar lines1 lines2 /\ s1 = s2) /\
   (code_similar _ _ <=> F)`;;

(* HOL4 line 408: val code_similar_ind = theorem "code_similar_ind" *)
let code_similar_ind = cake_ind "code_similar";;

(* HOL4 line 410 *)
let line_similar_sym = prove
 (`!(l1:(A)line) l2. line_similar l1 l2 ==> line_similar l2 l1`,
  REPEAT GEN_TAC THEN CASES_ON `l1:(A)line` THEN CASES_ON `l2:(A)line` THEN
  REWRITE_TAC[line_similar_def] THEN MESON_TAC[]);;

(* HOL4 line 416 *)
let code_similar_sym = prove
 (`!(code1:((A)sec)list) code2. code_similar code1 code2 ==> code_similar code2 code1`,
  MATCH_MP_TAC code_similar_ind THEN REWRITE_TAC[code_similar_def] THEN
  MESON_TAC[MATCH_MP EVERY2_sym line_similar_sym]);;

(* HOL4 line 428 *)
let line_similar_refl = prove
 (`!(l:(A)line). line_similar l l`,
  GEN_TAC THEN CASES_ON `l:(A)line` THEN REWRITE_TAC[line_similar_def]);;

let _ = cake_add_simps [line_similar_refl];;

(* HOL4 line 434 *)
let code_similar_refl = prove
 (`!(code:((A)sec)list). code_similar code code`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_similar_def] THEN
  CASES_ON `h:(A)sec` THEN ASM_REWRITE_TAC[code_similar_def] THEN
  MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[line_similar_refl]);;

let _ = cake_add_simps [code_similar_refl];;

(* HOL4 line 442 *)
let line_similar_trans = prove
 (`!(x:(A)line) y z. line_similar x y /\ line_similar y z ==> line_similar x z`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)line` THEN CASES_ON `y:(A)line` THEN
  CASES_ON `z:(A)line` THEN REWRITE_TAC[line_similar_def] THEN MESON_TAC[]);;

(* HOL4 line 448 *)
let code_similar_trans = prove
 (`!(c1:((A)sec)list) c2 c3.
     code_similar c1 c2 /\ code_similar c2 c3 ==> code_similar c1 c3`,
  MATCH_MP_TAC code_similar_ind THEN REWRITE_TAC[code_similar_def] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `c3:((A)sec)list` THEN FS[code_similar_def] THEN
  CASES_ON `a0:(A)sec` THEN FS[code_similar_def] THEN
  ASM_MESON_TAC[MATCH_MP EVERY2_trans line_similar_trans]);;

(* HOL4 line 457 *)
let code_similar_nil = prove
 (`!(l:((A)sec)list).
     (code_similar [] l <=> l = []) /\ (code_similar l [] <=> l = [])`,
  GEN_TAC THEN CASES_ON `l:((A)sec)list` THEN REWRITE_TAC[code_similar_def; NOT_CONS_NIL] THEN
  CASES_ON `a0:(A)sec` THEN REWRITE_TAC[code_similar_def]);;

(* HOL4 line 464 *)
let code_similar_append = prove
 (`!(l1:((A)sec)list) l2 r1 r2.
     code_similar l1 l2 /\ code_similar r1 r2
     ==> code_similar (APPEND l1 r1) (APPEND l2 r2)`,
  MATCH_MP_TAC code_similar_ind THEN REWRITE_TAC[code_similar_def; APPEND] THEN
  MESON_TAC[]);;

(* HOL4 line 473 *)
let line_similar_sec_label_ok = prove
 (`!(l1:((A)line)list) l2 s.
     ALL (sec_label_ok s) l1 /\ ALL2 line_similar l1 l2 ==> ALL (sec_label_ok s) l2`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `l2:((A)line)list` THEN
  REWRITE_TAC[ALL; ALL2] THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`sec_label_ok s (h:(A)line)`; `line_similar (h:(A)line) a0`] THEN
    CASES_ON `h:(A)line` THEN CASES_ON `a0:(A)line` THEN
    REWRITE_TAC[line_similar_def; sec_label_ok_def] THEN MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 484 *)
let code_similar_sec_labels_ok = prove
 (`!(c1:((A)sec)list) c2.
     ALL sec_labels_ok c1 /\ code_similar c1 c2 ==> ALL sec_labels_ok c2`,
  MATCH_MP_TAC code_similar_ind THEN REWRITE_TAC[code_similar_def; ALL; sec_labels_ok_def] THEN
  MESON_TAC[line_similar_sec_label_ok]);;

(* HOL4 line 495 *)
let line_similar_len_no_lab = prove
 (`!(l1:((A)line)list) l2.
     ALL2 line_similar l1 l2
     ==> LENGTH (FILTER ((~) o is_Label) l1) = LENGTH (FILTER ((~) o is_Label) l2)`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN CASES_ON `l2:((A)line)list` THEN REWRITE_TAC[ALL2; FILTER; LENGTH];
    ALL_TAC] THEN
  GEN_TAC THEN CASES_ON `l2:((A)line)list` THEN REWRITE_TAC[ALL2] THEN
  STRIP_TAC THEN REWRITE_TAC[FILTER; o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a1:((A)line)list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `is_Label (h:(A)line) <=> is_Label (a0:(A)line)` SUBST1_TAC THENL
   [UNDISCH_TAC `line_similar (h:(A)line) a0` THEN
    CASES_ON `h:(A)line` THEN CASES_ON `a0:(A)line` THEN
    REWRITE_TAC[line_similar_def; is_Label_def];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]]);;

(* HOL4 line 505 *)
let code_similar_len_no_lab = prove
 (`!(c1:((A)sec)list) (c2:((A)sec)list).
     code_similar c1 c2
     ==> MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines) c1 =
         MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines) c2`,
  MATCH_MP_TAC code_similar_ind THEN REWRITE_TAC[code_similar_def; MAP; o_THM] THEN
  SIMP[lab_Section_lines_def] THEN MESON_TAC[line_similar_len_no_lab]);;

(* HOL4 line 516 *)
let word_loc_val_def = cake_def
  `(word_loc_val (p:A word) (labs:(num spt)spt) (wl_Word w) = SOME w) /\
   (word_loc_val p labs (wl_Loc k1 k2) =
      match lab_lookup k1 k2 labs with
        NONE -> NONE
      | SOME q -> SOME (word_add p (word q)))`;;

(* HOL4 line 524 *)
let has_io_name_def = cake_def
  `(has_io_name index ([]:((A)sec)list) <=> F) /\
   (has_io_name index (CONS (Section k []) xs) <=> has_io_name index xs) /\
   (has_io_name index (CONS (Section k (CONS y ys)) xs) <=>
      has_io_name index (CONS (Section k ys) xs) \/
      (match y with LabAsm (CallFFI i) _ _ _ -> i = index | _ -> F))`;;

(* HOL4 line 532: val has_io_name_ind = theorem "has_io_name_ind" *)
let has_io_name_ind = cake_ind "has_io_name";;

(* HOL4 line 534 *)
let word_loc_val_byte_def = cake_def
  `word_loc_val_byte (p:A word) labs (m:A word->(A)word_loc) a be =
     match word_loc_val p labs (m (byte_align a)) with
       SOME w -> SOME (get_byte a w be)
     | NONE -> NONE`;;

(* HOL4 line 541 (HOL4 0w - n2w x is word_sub (word 0) (word x)) *)
let line_ok_def = cake_def
  `(line_ok (c:(A)asm_config) labs ffis pos (lab_Label _ _ l) <=>
      EVEN pos /\ l = 0) /\
   (line_ok c labs ffis pos (Asm b bytes l) <=>
      enc_with_nop (asm_config_encode c) (cbw_to_asm b) bytes /\
      LENGTH bytes = l /\ asm_ok (cbw_to_asm b) c) /\
   (line_ok c labs ffis pos (LabAsm lab_Halt w bytes l) <=>
      let w1 = word_sub (word 0:A word) (word (pos + ffi_offset)) in
      enc_with_nop (asm_config_encode c) (asm_Jump w1) bytes /\
      LENGTH bytes = l /\ asm_ok (asm_Jump w1) c) /\
   (line_ok c labs ffis pos (LabAsm lab_Install w bytes l) <=>
      let w1 = word_sub (word 0:A word) (word (pos + 2 * ffi_offset)) in
      enc_with_nop (asm_config_encode c) (asm_Jump w1) bytes /\
      LENGTH bytes = l /\ asm_ok (asm_Jump w1) c) /\
   (line_ok c labs ffis pos (LabAsm (CallFFI index) w bytes l) <=>
      let w1 = word_sub (word 0:A word)
                 (word (pos + (3 + get_ffi_index ffis (ExtCall index)) * ffi_offset)) in
      enc_with_nop (asm_config_encode c) (asm_Jump w1) bytes /\
      LENGTH bytes = l /\ asm_ok (asm_Jump w1) c) /\
   (line_ok c labs ffis pos (LabAsm (lab_Call v24) w bytes l) <=> F) /\
   (line_ok c labs ffis pos (LabAsm a w bytes l) <=>
      match get_label a with
        lab_Lab l1 l2 ->
          (match lab_lookup l1 l2 labs with
             NONE -> F
           | SOME t ->
               let w1 = word_sub (word t) (word pos) in
               enc_with_nop (asm_config_encode c) (lab_inst w1 a) bytes /\
               LENGTH bytes = l /\ asm_ok (lab_inst w1 a) c))`;;

(* HOL4 line 571: val line_ok_ind = theorem "line_ok_ind" (line_ok is not  *)
(* recursive: HOL4's TFL theorem is the case split, one case per clause of  *)
(* line_ok_def, the catch-all clause completed)                              *)
let line_ok_ind = prove
 (`!(P:(A)asm_config->(num spt)spt->ffiname list->num->(A)line->bool).
     (!c labs ffis pos v1 v2 l. P c labs ffis pos (lab_Label v1 v2 l)) /\
     (!c labs ffis pos b bytes l. P c labs ffis pos (Asm b bytes l)) /\
     (!c labs ffis pos w bytes l. P c labs ffis pos (LabAsm lab_Halt w bytes l)) /\
     (!c labs ffis pos w bytes l. P c labs ffis pos (LabAsm lab_Install w bytes l)) /\
     (!c labs ffis pos index w bytes l. P c labs ffis pos (LabAsm (CallFFI index) w bytes l)) /\
     (!c labs ffis pos v24 w bytes l. P c labs ffis pos (LabAsm (lab_Call v24) w bytes l)) /\
     (!c labs ffis pos v15 w bytes l. P c labs ffis pos (LabAsm (lab_Jump v15) w bytes l)) /\
     (!c labs ffis pos v16 v17 v18 v19 w bytes l.
        P c labs ffis pos (LabAsm (lab_JumpCmp v16 v17 v18 v19) w bytes l)) /\
     (!c labs ffis pos v21 v22 w bytes l.
        P c labs ffis pos (LabAsm (lab_LocValue v21 v22) w bytes l))
     ==> !v v1 v2 v3 v4. P v v1 v2 v3 v4`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN CASES_ON `v4:(A)line` THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `a0:(A)asm_with_lab` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 573 *)
let lines_ok_def = cake_def
  `(lines_ok (c:(A)asm_config) labs ffis pos ([]:((A)line)list) <=> T) /\
   (lines_ok c labs ffis pos (CONS y ys) <=>
      line_ok c labs ffis pos y /\ lines_ok c labs ffis (pos + line_length y) ys)`;;

let lines_ok_ind = cake_ind "lines_ok";;

(* HOL4 line 580 (HOL4 proves termination by itself: the size of the       *)
(* sections; the measure is given here, which is much faster)                *)
let all_enc_ok_def = cake_def_wf
  `MEASURE (\(c:(A)asm_config,labs:(num spt)spt,ffis:ffiname list,pos:num,
              xs:((A)sec)list). list_size (sec_size (\x:A. 0)) xs)`
  TERM_TAC
  `(all_enc_ok (c:(A)asm_config) labs ffis pos ([]:((A)sec)list) <=> T) /\
   (all_enc_ok c labs ffis pos (CONS (Section k []) xs) <=>
      EVEN pos /\ all_enc_ok c labs ffis pos xs) /\
   (all_enc_ok c labs ffis pos (CONS (Section k (CONS y ys)) xs) <=>
      line_ok c labs ffis pos y /\
      all_enc_ok c labs ffis (pos + line_length y) (CONS (Section k ys) xs))`;;

(* HOL4 line 589: val all_enc_ok_ind = theorem "all_enc_ok_ind" *)
let all_enc_ok_ind = cake_ind "all_enc_ok";;

(* HOL4 line 591 *)
let all_enc_ok_cons = prove
 (`!(ls:((A)line)list) pos (c:(A)asm_config) labs ffis k xs.
     all_enc_ok c labs ffis pos (CONS (Section k ls) xs) <=>
     all_enc_ok c labs ffis (pos + SUM (MAP line_length ls)) xs /\
     EVEN (pos + SUM (MAP line_length ls)) /\
     lines_ok c labs ffis pos ls`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[all_enc_ok_def; lines_ok_def; MAP; SUM; ADD_CLAUSES; ADD_ASSOC] THEN
  MESON_TAC[]);;

(* HOL4 line 602 *)
let pos_val_def = cake_def
  `(pos_val i pos ([]:((A)sec)list) = pos:num) /\
   (pos_val i pos (CONS (Section k []) xs) = pos_val i pos xs) /\
   (pos_val i pos (CONS (Section k (CONS y ys)) xs) =
      if is_Label y
      then pos_val i (pos + line_length y) (CONS (Section k ys) xs)
      else if i = 0 then pos
      else pos_val (i - 1) (pos + line_length y) (CONS (Section k ys) xs))`;;

(* HOL4 line 612: val pos_val_ind = theorem "pos_val_ind" *)
let pos_val_ind = cake_ind "pos_val";;

(* HOL4 line 614 (HOL4's binder enc is unused, left out) *)
let pos_val_0 = prove
 (`!(xs:((A)sec)list) (c:(A)asm_config) labs ffis pos.
     all_enc_ok c labs ffis pos xs ==> pos_val 0 pos xs = pos`,
  SUBGOAL_THEN `!(c:(A)asm_config) labs ffis pos (xs:((A)sec)list).
     all_enc_ok c labs ffis pos xs ==> pos_val 0 pos xs = pos` (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC all_enc_ok_ind THEN REWRITE_TAC[all_enc_ok_def; pos_val_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `line_ok c labs ffis pos (y:(A)line)` THEN
  UNDISCH_TAC `is_Label (y:(A)line)` THEN
  CASES_ON `y:(A)line` THEN REWRITE_TAC[is_Label_def; line_ok_def; line_length_def] THEN
  SIMP[]);;

(* HOL4 line 624 *)
let sec_pos_val_def = cake_def
  `(sec_pos_val i pos ([]:((A)line)list) = NONE) /\
   (sec_pos_val i pos (CONS y ys) =
      if is_Label y then sec_pos_val i (pos + line_length y) ys
      else if i = 0 then SOME pos
      else sec_pos_val (i - 1) (pos + line_length y) ys)`;;

let sec_pos_val_ind = cake_ind "sec_pos_val";;

(* HOL4 line 633 *)
let sec_pos_val_too_big = prove
 (`!i pos (lines:((A)line)list).
     LENGTH (FILTER ((~) o is_Label) lines) <= i ==> sec_pos_val i pos lines = NONE`,
  SUBGOAL_THEN `!(lines:((A)line)list) i pos.
     LENGTH (FILTER ((~) o is_Label) lines) <= i ==> sec_pos_val i pos lines = NONE`
    (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[sec_pos_val_def; FILTER; o_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
  DISCH_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 640 *)
let EVERY_is_Label_sec_pos_val = prove
 (`!n pos (lines:((A)line)list). ALL is_Label lines ==> sec_pos_val n pos lines = NONE`,
  SUBGOAL_THEN `!(lines:((A)line)list) n pos.
     ALL is_Label lines ==> sec_pos_val n pos lines = NONE` (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[sec_pos_val_def; ALL]);;

let LTTP1AUX_IH_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp(concl th) then MP_TAC th else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* HOL4 line 646 *)
let pos_val_thm0 = prove
 (CASE_TERM `!i pos (acc:((A)sec)list).
     pos_val i pos acc =
     match acc with
       [] -> pos
     | CONS (Section k s) ss ->
         (match sec_pos_val i pos s with
            NONE -> pos_val (i - LENGTH (FILTER ((~) o is_Label) s))
                      (pos + SUM (MAP line_length s)) ss
          | SOME x -> x)`,
  MATCH_MP_TAC pos_val_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pos_val_def] THEN CASE_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[pos_val_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[sec_pos_val_def; FILTER; LENGTH; MAP; SUM; SUB_0; ADD_CLAUSES] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [pos_val_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[sec_pos_val_def; FILTER; o_THM; MAP; SUM] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THENL
   [LTTP1AUX_IH_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_ASSOC];
    ASM_CASES_TAC `i = 0` THEN LTTP1AUX_IH_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_ASSOC; LENGTH; ARITH_RULE `i - 1 - n = i - SUC n`]]);;

(* HOL4 line 659 *)
let pos_val_thm = prove
 (CASE_TERM `!i pos k (s:((A)line)list) ss.
     pos_val i pos ([]:((A)sec)list) = pos /\
     pos_val i pos (CONS (Section k s) ss) =
     (match sec_pos_val i pos s with
        NONE -> pos_val (i - LENGTH (FILTER ((~) o is_Label) s))
                  (pos + SUM (MAP line_length s)) ss
      | SOME x -> x)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[pos_val_def];
    GEN_REWRITE_TAC LAND_CONV [pos_val_thm0] THEN CASE_REWRITE_TAC[]]);;

(* HOL4 line 669 (HOL4 all_enc_ok_pre c code is ALL (sec_ok_pre c) code) *)
let lab_to_targetProof_good_code_def = cake_def
  `lab_to_targetProof_good_code (c:(A)asm_config) (labs:(num spt)spt) code <=>
     ALL sec_ends_with_label code /\
     ALL sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) code /\
     DISJOINT (domain labs) (set_of_list (MAP Section_num code)) /\
     restrict_nonzero (lab_get_labels code) SUBSET
       lab_get_code_labels code UNION labs_domain labs /\
     ALL (sec_ok_pre c) code`;;

(* HOL4 line 680 *)
let num_pcs_def = cake_def
  `(num_pcs ([]:((A)sec)list) = 0) /\
   (num_pcs (CONS (Section _ []) rest) = num_pcs rest) /\
   (num_pcs (CONS (Section k (CONS x xs)) rest) =
      if is_Label x then num_pcs (CONS (Section k xs) rest)
      else 1 + num_pcs (CONS (Section k xs) rest))`;;

let num_pcs_ind = cake_ind "num_pcs";;

(* HOL4 line 688 *)
let share_mem_domain_code_rel_def = cake_def
  `share_mem_domain_code_rel (mc_conf:(A,B,C)machine_config) (p:A word)
     (code2:((A)sec)list) (s1_shared_mem_domain:A word->bool) <=>
     (!pc op re a inst len i.
        asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a) inst len) /\
        mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i
        ==> ?index.
              i <= index /\
              find_index (word_add p (word (pos_val pc 0 code2)))
                (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index /\
              (let (name,nb) = get_memop_info op in
               EL index (machine_config_ffi_names mc_conf) = SharedMem name /\
               ALOOKUP (machine_config_mmio_info mc_conf) index =
                 SOME (nb,a,re,word_add p (word (pos_val pc 0 code2 + len))))) /\
     (!pc line.
        asm_fetch_aux pc code2 = SOME line /\
        (!op re a inst len. ~(line = Asm (ShareMem op re a) inst len))
        ==> DISJOINT (set_of_list (machine_config_ffi_entry_pcs mc_conf))
              {word_add (word_add p (word a)) (word (pos_val pc 0 code2)) | a |
               a < LENGTH (line_bytes line)}) /\
     (!a. byte_align a IN s1_shared_mem_domain ==> a IN s1_shared_mem_domain) /\
     machine_config_shared_addresses mc_conf = s1_shared_mem_domain`;;

(* HOL4 line 720.  HOL4 binds t1 again inside the first conjunct (shadowing *)
(* the argument t1), as here.                                                 *)
let share_mem_state_rel_def = cake_def
  `share_mem_state_rel (mc_conf:(A,B,C)machine_config)
     (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) (ms1:B) <=>
     (!ms2 k index new_bytes t1 nb ad offs re pc' ad' st new_st i.
        mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
        i <= index /\ index < LENGTH (machine_config_ffi_names mc_conf) /\
        RTC call_FFI_rel (lab_state_ffi s1) st /\
        ALOOKUP (machine_config_mmio_info mc_conf) index = SOME (nb,Addr ad offs,re,pc') /\
        machine_config_prog_addresses mc_conf = asm_state_mem_domain t1 /\
        ad' = word_add (target_get_reg (machine_config_target mc_conf) ms2 ad) offs /\
        target_state_rel (machine_config_target mc_conf)
          (asm_state_pc_fupd (K (EL index (machine_config_ffi_entry_pcs mc_conf))) t1) ms2
        ==> ?op. EL index (machine_config_ffi_names mc_conf) = SharedMem op /\
                 (match op with
                    MappedRead ->
                      (if nb = word 0
                       then val ad' MOD (dimindex (:A) DIV 8) = 0 else T) /\
                      ad' IN machine_config_shared_addresses mc_conf /\
                      is_valid_mapped_read (target_get_pc (machine_config_target mc_conf) ms2)
                        nb (Addr ad offs) re pc' (machine_config_target mc_conf) ms2
                        (machine_config_prog_addresses mc_conf) /\
                      call_FFI st (SharedMem MappedRead) [nb] (word_to_bytes ad' F) =
                        FFI_return new_st new_bytes
                      ==> target_state_rel (machine_config_target mc_conf)
                            (asm_state_pc_fupd (K pc')
                               (asm_state_regs_fupd
                                  (K (\n. if n = re then word_of_bytes F (word 0) new_bytes
                                          else asm_state_regs t1 n)) t1))
                            (machine_config_ffi_interfer mc_conf k (index,new_bytes,ms2))
                  | MappedWrite ->
                      (if nb = word 0
                       then val ad' MOD (dimindex (:A) DIV 8) = 0 else T) /\
                      ad' IN machine_config_shared_addresses mc_conf /\
                      is_valid_mapped_write (target_get_pc (machine_config_target mc_conf) ms2)
                        nb (Addr ad offs) re pc' (machine_config_target mc_conf) ms2
                        (machine_config_prog_addresses mc_conf) /\
                      call_FFI st (SharedMem MappedWrite) [nb]
                        (APPEND
                           (let w = target_get_reg (machine_config_target mc_conf) ms2 re in
                            if nb = word 0 then word_to_bytes w F
                            else word_to_bytes_aux (val nb) w F)
                           (word_to_bytes ad' F)) =
                        FFI_return new_st new_bytes
                      ==> target_state_rel (machine_config_target mc_conf)
                            (asm_state_pc_fupd (K pc') t1)
                            (machine_config_ffi_interfer mc_conf k (index,new_bytes,ms2)))) /\
     (!index i.
        mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
        index < LENGTH (machine_config_ffi_names mc_conf) /\ i <= index
        ==> ~(machine_config_halt_pc mc_conf =
              EL index (machine_config_ffi_entry_pcs mc_conf)) /\
            ~(machine_config_ccache_pc mc_conf =
              EL index (machine_config_ffi_entry_pcs mc_conf)))`;;

(* HOL4 line 776 *)
let no_install_or_no_share_mem_def = cake_def
  `no_install_or_no_share_mem (code:((A)sec)list) ffi_names <=>
     (no_share_mem_inst code /\ ALL (\x. ?s. x = ExtCall s) ffi_names) \/
     lab_no_install code`;;

(* HOL4 line 788 *)
let oracle_tie_def = cake_def
  `oracle_tie (mc_conf:(A,B,C)machine_config) ms (s1:(A,D,FFI)lab_state) <=>
     lab_state_io_regs s1 = target_io_regs mc_conf (lab_state_ffi s1) ms /\
     lab_state_io_fp_regs s1 = target_io_fp_regs mc_conf (lab_state_ffi s1) ms /\
     lab_state_cc_regs s1 = target_cc_regs mc_conf (lab_state_ffi s1) ms /\
     lab_state_cc_fp_regs s1 = target_cc_fp_regs mc_conf (lab_state_ffi s1) ms`;;

(* HOL4 line 797 *)
let oracle_tie_shift_interfer = prove
 (`!(mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state) l ms2.
     oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2)
     ==> oracle_tie (shift_interfer l mc_conf) ms2 s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `next_interference (mc_conf:(A,B,C)machine_config)
                  (lab_state_ffi (s1:(A,D,FFI)lab_state)) ms1 =
                next_interference (shift_interfer l mc_conf) (lab_state_ffi s1) ms2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC next_interference_shift THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DRULE constructed_oracles_EQ THEN SIMP[shift_interfer_def] THEN
  UNDISCH_TAC `oracle_tie (mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state)` THEN
  SIMP[oracle_tie_def]);;

(* HOL4 line 813 *)
let oracle_tie_step = prove
 (`!(mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state) l ms2
     (s2:(A,D,FFI)lab_state).
     oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2) /\
     lab_state_io_regs s2 = lab_state_io_regs s1 /\
     lab_state_io_fp_regs s2 = lab_state_io_fp_regs s1 /\
     lab_state_cc_regs s2 = lab_state_cc_regs s1 /\
     lab_state_cc_fp_regs s2 = lab_state_cc_fp_regs s1 /\
     lab_state_ffi s2 = lab_state_ffi s1
     ==> oracle_tie (shift_interfer l mc_conf) ms2 s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`; `s1:(A,D,FFI)lab_state`;
                `l:num`; `ms2:B`] oracle_tie_shift_interfer) THEN
  ASM_REWRITE_TAC[oracle_tie_def]);;

(* HOL4 line 828 *)
let oracle_tie_ffi_step = prove
 (`!(mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state) index new_bytes ms_pre
     ms_post mc' ffi'.
     oracle_tie mc_conf ms1 s1 /\
     next_interference mc_conf (lab_state_ffi s1) ms1 =
       SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi')
     ==> (!name r.
            lab_state_io_regs s1 0 name r =
            if MEM r (machine_config_callee_saved_regs mc_conf) \/
               ~(r < asm_config_reg_count (target_config (machine_config_target mc_conf))) \/
               MEM r (asm_config_avoid_regs (target_config (machine_config_target mc_conf)))
            then NONE
            else SOME (target_get_reg (machine_config_target mc_conf) ms_post r)) /\
         (!i. lab_state_io_fp_regs s1 0 i =
              target_get_fp_reg (machine_config_target mc_conf) ms_post i) /\
         target_io_regs mc' ffi' ms_post = shift_seq 1 (lab_state_io_regs s1) /\
         target_io_fp_regs mc' ffi' ms_post = shift_seq 1 (lab_state_io_fp_regs s1) /\
         target_cc_regs mc' ffi' ms_post = lab_state_cc_regs s1 /\
         target_cc_fp_regs mc' ffi' ms_post = lab_state_cc_fp_regs s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oracle_tie_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_ALL o MATCH_MP constructed_oracles_ffi_step) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; shift_seq_def; ADD1] THEN SIMP_TAC[]);;

(* HOL4 line 850 *)
let oracle_tie_ccache_step = prove
 (`!(mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state) a1 a2 ms_pre ms_post
     mc' ffi'.
     oracle_tie mc_conf ms1 s1 /\
     next_interference mc_conf (lab_state_ffi s1) ms1 =
       SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi')
     ==> (!r. lab_state_cc_regs s1 0 r =
              if MEM r (machine_config_callee_saved_regs mc_conf) \/
                 r = machine_config_ptr_reg mc_conf \/
                 ~(r < asm_config_reg_count (target_config (machine_config_target mc_conf))) \/
                 MEM r (asm_config_avoid_regs (target_config (machine_config_target mc_conf)))
              then NONE
              else SOME (target_get_reg (machine_config_target mc_conf) ms_post r)) /\
         (!i. lab_state_cc_fp_regs s1 0 i =
              target_get_fp_reg (machine_config_target mc_conf) ms_post i) /\
         target_cc_regs mc' ffi' ms_post = shift_seq 1 (lab_state_cc_regs s1) /\
         target_cc_fp_regs mc' ffi' ms_post = shift_seq 1 (lab_state_cc_fp_regs s1) /\
         target_io_regs mc' ffi' ms_post = lab_state_io_regs s1 /\
         target_io_fp_regs mc' ffi' ms_post = lab_state_io_fp_regs s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oracle_tie_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_ALL o MATCH_MP constructed_oracles_cc_step) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; shift_seq_def; ADD1] THEN SIMP_TAC[]);;

(* HOL4 line 872 *)
let oracle_tie_ffi_next = prove
 (`!(mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state) index new_bytes ms_pre
     ms_post mc' ffi' (s2:(A,D,FFI)lab_state).
     oracle_tie mc_conf ms1 s1 /\
     next_interference mc_conf (lab_state_ffi s1) ms1 =
       SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi') /\
     lab_state_io_regs s2 = shift_seq 1 (lab_state_io_regs s1) /\
     lab_state_io_fp_regs s2 = shift_seq 1 (lab_state_io_fp_regs s1) /\
     lab_state_cc_regs s2 = lab_state_cc_regs s1 /\
     lab_state_cc_fp_regs s2 = lab_state_cc_fp_regs s1 /\
     lab_state_ffi s2 = ffi'
     ==> oracle_tie mc' ms_post s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`; `s1:(A,D,FFI)lab_state`;
    `index:num`; `new_bytes:byte list`; `ms_pre:B`; `ms_post:B`;
    `mc':(A,B,C)machine_config`; `ffi':(FFI)ffi_state`] oracle_tie_ffi_step) THEN
  ASM_REWRITE_TAC[oracle_tie_def] THEN SIMP_TAC[]);;

(* HOL4 line 887 *)
let oracle_tie_ccache_next = prove
 (`!(mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state) a1 a2 ms_pre ms_post
     mc' ffi' (s2:(A,D,FFI)lab_state).
     oracle_tie mc_conf ms1 s1 /\
     next_interference mc_conf (lab_state_ffi s1) ms1 =
       SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') /\
     lab_state_cc_regs s2 = shift_seq 1 (lab_state_cc_regs s1) /\
     lab_state_cc_fp_regs s2 = shift_seq 1 (lab_state_cc_fp_regs s1) /\
     lab_state_io_regs s2 = lab_state_io_regs s1 /\
     lab_state_io_fp_regs s2 = lab_state_io_fp_regs s1 /\
     lab_state_ffi s2 = ffi'
     ==> oracle_tie mc' ms_post s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`; `s1:(A,D,FFI)lab_state`;
    `a1:A word`; `a2:A word`; `ms_pre:B`; `ms_post:B`;
    `mc':(A,B,C)machine_config`; `ffi':(FFI)ffi_state`] oracle_tie_ccache_step) THEN
  ASM_REWRITE_TAC[oracle_tie_def] THEN SIMP_TAC[]);;

(* HOL4 line 902 *)
let oracle_tie_ExtCall_residues = prove
 (`!(mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state) ms2 l index name bytes
     bytes2 new_ffi new_bytes (t1:(A)asm_state).
     oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference
            (machine_config_next_interfer_fupd
               (K (shift_seq l (machine_config_next_interfer mc_conf))) mc_conf)
            (lab_state_ffi s1) k ms2) /\
     ~(target_get_pc (machine_config_target mc_conf) ms2 IN
       machine_config_prog_addresses mc_conf DIFF
       set_of_list (machine_config_ffi_entry_pcs mc_conf)) /\
     ~(target_get_pc (machine_config_target mc_conf) ms2 = machine_config_halt_pc mc_conf) /\
     ~(target_get_pc (machine_config_target mc_conf) ms2 = machine_config_ccache_pc mc_conf) /\
     find_index (target_get_pc (machine_config_target mc_conf) ms2)
       (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index /\
     EL index (machine_config_ffi_names mc_conf) = ExtCall name /\
     ALOOKUP (machine_config_mmio_info mc_conf) index = NONE /\
     read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
     call_FFI (lab_state_ffi s1) (ExtCall name) bytes bytes2 = FFI_return new_ffi new_bytes
     ==> (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall name) a)
                (asm_state_regs t1 a) I) =
         (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
                 ~(a < asm_config_reg_count (target_config (machine_config_target mc_conf))) \/
                 MEM a (asm_config_avoid_regs (target_config (machine_config_target mc_conf)))
              then asm_state_regs t1 a
              else target_get_reg (machine_config_target mc_conf)
                     (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms2)) a) /\
         (\n. lab_state_io_fp_regs s1 0 n) =
         (\n. target_get_fp_reg (machine_config_target mc_conf)
                (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms2)) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mc2 = machine_config_next_interfer_fupd
                      (K (shift_seq l (machine_config_next_interfer mc_conf)))
                      (mc_conf:(A,B,C)machine_config)` THEN
  SUBGOAL_THEN `next_interference (mc_conf:(A,B,C)machine_config)
                  (lab_state_ffi (s1:(A,D,FFI)lab_state)) ms1 =
                next_interference mc2 (lab_state_ffi s1) ms2` ASSUME_TAC THENL
   [MATCH_MP_TAC next_interference_shift THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `next_interference (mc2:(A,B,C)machine_config)
                  (lab_state_ffi (s1:(A,D,FFI)lab_state)) ms2 =
                SOME (FfiApp index new_bytes ms2
                        (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config) 0
                           (index,new_bytes,ms2)),
                      machine_config_ffi_interfer_fupd
                        (K (shift_seq 1 (machine_config_ffi_interfer mc_conf))) mc2,
                      new_ffi)` ASSUME_TAC THENL
   [SUBGOAL_THEN `machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config) =
                  machine_config_ffi_interfer (mc2:(A,B,C)machine_config)` SUBST1_TAC THENL
     [EXPAND_TAC "mc2" THEN SIMP[]; ALL_TAC] THEN
    MATCH_MP_TAC next_interference_ExtCall THEN
    SUBGOAL_THEN `read_ffi_bytearrays (mc2:(A,B,C)machine_config) ms2 =
                  read_ffi_bytearrays (mc_conf:(A,B,C)machine_config) ms2` SUBST1_TAC THENL
     [EXPAND_TAC "mc2" THEN REWRITE_TAC[read_ffi_bytearrays_def; read_ffi_bytearray_def] THEN
      SIMP[];
      ALL_TAC] THEN
    EXPAND_TAC "mc2" THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN SIMP[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`; `s1:(A,D,FFI)lab_state`;
    `index:num`; `new_bytes:byte list`; `ms2:B`;
    `machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config) 0 (index,new_bytes,ms2)`;
    `machine_config_ffi_interfer_fupd
       (K (shift_seq 1 (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config))))
       (mc2:(A,B,C)machine_config)`;
    `new_ffi:(FFI)ffi_state`] oracle_tie_ffi_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[get_reg_value_def; I_THM]);;
(* HOL4 line 959 (HOL4 closure of call_FFI_rel is RTC call_FFI_rel; aligned is *)
(* alignment_aligned; HOL4 r with <| f1 := x; ... |> is nested _fupd, all    *)
(* fields computed from the original record)                                 *)
let lab_to_targetProof_state_rel_def = cake_def
  `lab_to_targetProof_state_rel
     (mc_conf:(A,B,C)machine_config,code2:((A)sec)list,labs:(num spt)spt,p:A word)
     (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) (ms1:B) <=>
     target_state_rel (machine_config_target mc_conf) t1 ms1 /\ good_dimindex (:A) /\
     machine_config_prog_addresses mc_conf = asm_state_mem_domain t1 /\
     ~(machine_config_halt_pc mc_conf IN machine_config_prog_addresses mc_conf) /\
     ~(machine_config_ccache_pc mc_conf IN machine_config_prog_addresses mc_conf) /\
     reg_ok (lab_state_ptr_reg s1) (target_config (machine_config_target mc_conf)) /\
     machine_config_ptr_reg mc_conf = lab_state_ptr_reg s1 /\
     reg_ok (lab_state_len_reg s1) (target_config (machine_config_target mc_conf)) /\
     machine_config_len_reg mc_conf = lab_state_len_reg s1 /\
     reg_ok (lab_state_ptr2_reg s1) (target_config (machine_config_target mc_conf)) /\
     machine_config_ptr2_reg mc_conf = lab_state_ptr2_reg s1 /\
     reg_ok (lab_state_len2_reg s1) (target_config (machine_config_target mc_conf)) /\
     machine_config_len2_reg mc_conf = lab_state_len2_reg s1 /\
     reg_ok (lab_state_link_reg s1) (target_config (machine_config_target mc_conf)) /\
     (?i. mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
          (!index. if i <= index /\ index < LENGTH (machine_config_ffi_names mc_conf)
                   then ?info. ALOOKUP (machine_config_mmio_info mc_conf) index = SOME info
                   else ALOOKUP (machine_config_mmio_info mc_conf) index = NONE)) /\
     (!ms2 k index new_bytes t1 bytes bytes2 st new_st i.
        mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
        index < i /\
        read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
        RTC call_FFI_rel (lab_state_ffi s1) st /\
        call_FFI st (EL index (machine_config_ffi_names mc_conf)) bytes bytes2 =
          FFI_return new_st new_bytes /\
        machine_config_prog_addresses mc_conf = asm_state_mem_domain t1 /\
        target_state_rel (machine_config_target mc_conf)
          (asm_state_pc_fupd (K (word_sub p (word ((3 + index) * ffi_offset)))) t1) ms2 /\
        alignment_aligned
          (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
          (asm_state_regs t1 (lab_state_link_reg s1))
        ==> (let ms' = machine_config_ffi_interfer mc_conf k (index,new_bytes,ms2) in
             target_state_rel (machine_config_target mc_conf)
               (asm_state_regs_fupd
                  (K (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
                             ~(a < asm_config_reg_count
                                     (target_config (machine_config_target mc_conf))) \/
                             MEM a (asm_config_avoid_regs
                                      (target_config (machine_config_target mc_conf)))
                          then asm_state_regs t1 a
                          else target_get_reg (machine_config_target mc_conf) ms' a))
                (asm_state_fp_regs_fupd
                  (K (\n. target_get_fp_reg (machine_config_target mc_conf) ms' n))
                (asm_state_mem_fupd
                  (K (asm_write_bytearray (asm_state_regs t1 (lab_state_ptr2_reg s1))
                        new_bytes (asm_state_mem t1)))
                (asm_state_pc_fupd (K (asm_state_regs t1 (lab_state_link_reg s1))) t1))))
               ms')) /\
     (!ms2 t1 k a1 a2.
        target_state_rel (machine_config_target mc_conf)
          (asm_state_pc_fupd (K (word_sub p (word (2 * ffi_offset)))) t1) ms2 /\
        alignment_aligned
          (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
          (asm_state_regs t1 (lab_state_link_reg s1))
        ==> (let ms' = machine_config_ccache_interfer mc_conf k (a1,a2,ms2) in
             target_state_rel (machine_config_target mc_conf)
               (asm_state_regs_fupd
                  (K (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
                             a = lab_state_ptr_reg s1 \/
                             ~(a < asm_config_reg_count
                                     (target_config (machine_config_target mc_conf))) \/
                             MEM a (asm_config_avoid_regs
                                      (target_config (machine_config_target mc_conf)))
                          then asm_state_regs t1 a
                          else target_get_reg (machine_config_target mc_conf) ms' a))
                (asm_state_fp_regs_fupd
                  (K (\n. target_get_fp_reg (machine_config_target mc_conf) ms' n))
                (asm_state_pc_fupd (K (asm_state_regs t1 (lab_state_link_reg s1))) t1)))
               ms')) /\
     lab_state_compile s1 = compile_lab (target_config (machine_config_target mc_conf)) /\
     (no_share_mem_inst code2
      ==> !k. let (cfg,code) = lab_state_compile_oracle s1 k in
              lab_to_targetProof_good_code (target_config (machine_config_target mc_conf))
                (lab_to_target_config_labels cfg) code /\
              no_share_mem_inst code /\
              (k = 0
               ==> lab_to_target_config_labels cfg = labs /\
                   lab_to_target_config_pos cfg = LENGTH (prog_to_bytes code2) /\
                   lab_to_target_config_ffi_names cfg =
                     SOME (machine_config_ffi_names mc_conf))) /\
     (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
     word_and (word 1) p = word 0 /\
     list_subset (FILTER (\x. ?s. x = ExtCall s) (find_ffi_names (lab_state_code s1)))
       (machine_config_ffi_names mc_conf) /\
     EVEN (LENGTH (prog_to_bytes code2)) /\
     (!name i.
        MEM name (machine_config_ffi_names mc_conf) /\
        mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
        get_ffi_index (machine_config_ffi_names mc_conf) name < i
        ==> (?s. name = ExtCall s) /\
            ~(word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf) name) *
                                ffi_offset)) IN machine_config_prog_addresses mc_conf) /\
            ~(word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf) name) *
                                ffi_offset)) = machine_config_halt_pc mc_conf) /\
            ~(word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf) name) *
                                ffi_offset)) = machine_config_ccache_pc mc_conf) /\
            find_index
              (word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf) name) *
                                 ffi_offset)))
              (machine_config_ffi_entry_pcs mc_conf) 0 =
            SOME (get_ffi_index (machine_config_ffi_names mc_conf) name)) /\
     word_sub p (word ffi_offset) = machine_config_halt_pc mc_conf /\
     word_sub p (word (2 * ffi_offset)) = machine_config_ccache_pc mc_conf /\
     interference_ok (machine_config_next_interfer mc_conf)
       (target_proj (machine_config_target mc_conf) (asm_state_mem_domain t1)) /\
     (!l1 l2 x2.
        loc_to_pc l1 l2 (lab_state_code s1) = SOME x2
        ==> lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2)) /\
     (!r. lab_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     (!n. n < buffer_space_left (lab_state_code_buffer s1)
          ==> let addr = word_add (buffer_position (lab_state_code_buffer s1))
                           (word (LENGTH (buffer_buffer (lab_state_code_buffer s1)) + n)) in
              addr IN asm_state_mem_domain t1 /\ ~(addr IN lab_state_mem_domain s1)) /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     buffer_position (lab_state_code_buffer s1) =
       word_add p (word (LENGTH (prog_to_bytes code2))) /\
     bytes_in_mem (buffer_position (lab_state_code_buffer s1))
       (buffer_buffer (lab_state_code_buffer s1)) (asm_state_mem t1)
       (asm_state_mem_domain t1) (lab_state_mem_domain s1) /\
     LENGTH (prog_to_bytes code2) + LENGTH (buffer_buffer (lab_state_code_buffer s1)) +
       buffer_space_left (lab_state_code_buffer s1) < dimword (:A) /\
     (!bn. bn < LENGTH (buffer_buffer (lab_state_code_buffer s1)) +
                buffer_space_left (lab_state_code_buffer s1)
           ==> ~MEM (word_add (buffer_position (lab_state_code_buffer s1)) (word bn))
                    (machine_config_ffi_entry_pcs mc_conf)) /\
     ~lab_state_failed s1 /\ ~asm_state_failed t1 /\ lab_state_be s1 = asm_state_be t1 /\
     asm_state_pc t1 = word_add p (word (pos_val (lab_state_pc s1) 0 code2)) /\
     word_and p (word (2 EXP asm_state_align t1 - 1)) = word 0 /\
     (match asm_config_link_reg (target_config (machine_config_target mc_conf)) with
        NONE -> T
      | SOME r -> asm_state_lr t1 = r) /\
     (asm_state_be t1 <=> asm_config_big_endian (target_config (machine_config_target mc_conf))) /\
     asm_state_align t1 =
       asm_config_code_alignment (target_config (machine_config_target mc_conf)) /\
     enc_ok (target_config (machine_config_target mc_conf)) /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs
       (TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names mc_conf)))
          (machine_config_ffi_names mc_conf)) 0 code2 /\
     ALL sec_labels_ok code2 /\
     code_similar (lab_state_code s1) code2 /\
     share_mem_state_rel mc_conf s1 t1 ms1 /\
     share_mem_domain_code_rel mc_conf p code2 (lab_state_shared_mem_domain s1) /\
     LENGTH (machine_config_ffi_names mc_conf) = LENGTH (machine_config_ffi_entry_pcs mc_conf) /\
     no_install_or_no_share_mem code2 (machine_config_ffi_names mc_conf)`;;

let LTTP1AUX_CONJ_TAC (p:term->bool) (ttac:thm_tactic) : tactic =
  fun (asl,w as g) ->
    let ths = List.concat (map (CONJUNCTS o snd) asl) in
    ttac (find (p o concl) ths) g;;

(* HOL4 line 1098 *)
let oracle_tie_clock = prove
 (`!(mc_conf:(A,B,C)machine_config) ms (s1:(A,D,FFI)lab_state) k.
     oracle_tie mc_conf ms s1 ==> oracle_tie mc_conf ms (lab_state_clock_fupd (K k) s1)`,
  REWRITE_TAC[oracle_tie_def] THEN SIMP[]);;

(* HOL4 line 1105 *)
let lab_to_targetProof_state_rel_clock = prove
 (`!x (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) (ms:B) k.
     lab_to_targetProof_state_rel (x:(A,B,C)machine_config#((A)sec)list#(num spt)spt#A word)
       s1 t1 ms
     ==> lab_to_targetProof_state_rel x (lab_state_clock_fupd (K k) s1) t1 ms`,
  REWRITE_TAC[FORALL_PAIR_THM; lab_to_targetProof_state_rel_def; share_mem_state_rel_def;
              (record_info "lab_state").ri_accfupds]);;

(* HOL4 line 1120 *)
let share_mem_state_rel_shift_interfer = prove
 (`!(mc_conf:(A,B,C)machine_config) (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) (x:B) l.
     share_mem_state_rel mc_conf s1 t1 x
     ==> share_mem_state_rel
           (machine_config_next_interfer_fupd
              (K (\i. machine_config_next_interfer mc_conf (i + l))) mc_conf) s1 t1 x`,
  REWRITE_TAC[share_mem_state_rel_def; (record_info "machine_config").ri_accfupds]);;

(* HOL4 line 1130 *)
let share_mem_domain_code_rel_shift_interfer = prove
 (`!(mc_conf:(A,B,C)machine_config) (p:A word) code2 (s1:(A,D,FFI)lab_state) l.
     share_mem_domain_code_rel mc_conf p code2 (lab_state_shared_mem_domain s1)
     ==> share_mem_domain_code_rel
           (machine_config_next_interfer_fupd
              (K (\i. machine_config_next_interfer mc_conf (i + l))) mc_conf)
           p code2 (lab_state_shared_mem_domain s1)`,
  REWRITE_TAC[share_mem_domain_code_rel_def; (record_info "machine_config").ri_accfupds]);;

(* HOL4 line 1140 *)
let state_rel_shift_interfer = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) (x:B) l.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 x
     ==> lab_to_targetProof_state_rel (shift_interfer l mc_conf,code2,labs,p) s1 t1 x`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!ms. read_ffi_bytearrays (shift_interfer l (mc_conf:(A,B,C)machine_config)) ms =
                     read_ffi_bytearrays mc_conf ms` ASSUME_TAC THENL
   [REWRITE_TAC[shift_interfer_def; read_ffi_bytearrays_def; read_ffi_bytearray_def] THEN
    SIMP[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN
  REWRITE_TAC[shift_interfer_def; share_mem_state_rel_def; share_mem_domain_code_rel_def;
              (record_info "machine_config").ri_accfupds] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[K_THM] THEN
  LTTP1AUX_CONJ_TAC (can (find_term (fun t -> is_const t &&
                                       fst(dest_const t) = "interference_ok"))) MP_TAC THEN
  REWRITE_TAC[interference_ok_def; shift_seq_def] THEN MESON_TAC[]);;

let LTTP1AUX_code_similar_CONS = prove
 (`!(code1:((A)sec)list) k lines2 rest2.
     code_similar code1 (CONS (Section k lines2) rest2) <=>
     ?lines1 rest1. code1 = CONS (Section k lines1) rest1 /\
                    ALL2 line_similar lines1 lines2 /\ code_similar rest1 rest2`,
  GEN_TAC THEN CASES_ON `code1:((A)sec)list` THEN REWRITE_TAC[code_similar_def; NOT_CONS_NIL] THEN
  CASES_ON `a0:(A)sec` THEN REWRITE_TAC[code_similar_def; CONS_11; injectivity "sec"] THEN
  MESON_TAC[]);;

(* HOL4 line 1155 (rebound at HOL4 line 1210) *)
let prog_to_bytes_lemma = prove
 (`!code2 code1 pc i pos (mc_conf:(A,B,C)machine_config) labs ffi_names.
     code_similar code1 code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names pos code2 /\
     asm_fetch_aux pc code1 = SOME i
     ==> ?bs j bs2.
           prog_to_bytes code2 = APPEND (APPEND bs (line_bytes j)) bs2 /\
           LENGTH bs + pos = pos_val pc pos code2 /\
           LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc + 1) pos code2 /\
           line_similar i j /\
           line_ok (target_config (machine_config_target mc_conf)) labs ffi_names
             (pos_val pc pos code2) j`,
  MATCH_MP_TAC asm_code_length_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[code_similar_nil] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FS[asm_fetch_aux_def];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LTTP1AUX_code_similar_CONS; LIST_REL_NIL; all_enc_ok_def] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[asm_fetch_aux_def]) THEN
    REWRITE_TAC[prog_to_bytes_def; pos_val_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `rest1:((A)sec)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LTTP1AUX_code_similar_CONS; LIST_REL_CONS2; all_enc_ok_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `is_Label (h':(A)line) <=> is_Label (y:(A)line)` ASSUME_TAC THENL
   [UNDISCH_TAC `line_similar (h':(A)line) y` THEN CASES_ON `h':(A)line` THEN
    CASES_ON `y:(A)line` THEN REWRITE_TAC[line_similar_def; is_Label_def];
    ALL_TAC] THEN
  UNDISCH_TAC `asm_fetch_aux pc (CONS (Section k (CONS h' t')) (rest1:((A)sec)list)) = SOME i` THEN
  REWRITE_TAC[asm_fetch_aux_def; prog_to_bytes_def; pos_val_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (Section k t') (rest1:((A)sec)list)`; `pc:num`;
      `i:(A)line`; `pos + line_length (y:(A)line)`; `mc_conf:(A,B,C)machine_config`;
      `labs:(num spt)spt`; `ffi_names:ffiname list`]) THEN
    ASM_REWRITE_TAC[code_similar_def] THEN
    SUBGOAL_THEN `line_length (y:(A)line) = 0 /\ line_bytes y = []`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `is_Label (y:(A)line)` THEN
      UNDISCH_TAC `line_ok (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                     labs ffi_names pos (y:(A)line)` THEN
      CASES_ON `y:(A)line` THEN SIMP[is_Label_def; line_ok_def; line_length_def; line_bytes_def];
      ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; APPEND];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  ASM_CASES_TAC `pc = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`[]:byte list`; `y:(A)line`;
                          `prog_to_bytes (CONS (Section k ys) (xs:((A)sec)list))`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP pos_val_0 th]) THEN
    ASM_SIMP_TAC[LENGTH_line_bytes];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (Section k t') (rest1:((A)sec)list)`; `pc - 1`;
    `i:(A)line`; `pos + line_length (y:(A)line)`; `mc_conf:(A,B,C)machine_config`;
    `labs:(num spt)spt`; `ffi_names:ffiname list`]) THEN
  ASM_REWRITE_TAC[code_similar_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(pc = 0) ==> pc - 1 + 1 = pc`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`APPEND (line_bytes (y:(A)line)) bs`; `j:(A)line`; `bs2:byte list`] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; LENGTH_APPEND] THEN
  ASM_SIMP_TAC[LENGTH_line_bytes] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

(* HOL4 line 1210: val prog_to_bytes_lemma = prog_to_bytes_lemma |> Q.SPECL *)
(* [code2,code1,pc,i,0] |> SIMP_RULE std_ss [] (rebinds it; the   *)
(* remaining variables quantified here)                                      *)
let prog_to_bytes_lemma = prove
 (`!code2 code1 pc i (mc_conf:(A,B,C)machine_config) labs ffi_names.
     code_similar code1 code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     asm_fetch_aux pc code1 = SOME i
     ==> ?bs j bs2.
           prog_to_bytes code2 = APPEND (APPEND bs (line_bytes j)) bs2 /\
           LENGTH bs = pos_val pc 0 code2 /\
           LENGTH bs + LENGTH (line_bytes j) = pos_val (pc + 1) 0 code2 /\
           line_similar i j /\
           line_ok (target_config (machine_config_target mc_conf)) labs ffi_names
             (pos_val pc 0 code2) j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`code2:((A)sec)list`; `code1:((A)sec)list`; `pc:num`; `i:(A)line`; `0`;
                `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`;
                `ffi_names:ffiname list`] prog_to_bytes_lemma) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

(* HOL4 line 1214 *)
let bytes_in_mem_APPEND = prove
 (`!(xs:byte list) ys (a:A word) (m:A word->byte) md md1.
     bytes_in_mem a (APPEND xs ys) m md md1 <=>
     bytes_in_mem a xs m md md1 /\
     bytes_in_mem (word_add a (word (LENGTH xs))) ys m md md1`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; bytes_in_mem_def; WORD_ADD_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w; ARITH_RULE `1 + n = SUC n`] THEN
  REWRITE_TAC[CONJ_ACI]);;

(* HOL4 line 1223 *)
let bytes_in_mem_UPDATE = prove
 (`!(ls:byte list) (a:A word) (m:A word->byte) md md2 w1 w2.
     (!n. n < LENGTH ls ==> ~(word_add a (word n) = w1)) /\
     bytes_in_mem a ls m md md2
     ==> bytes_in_mem a ls ((w1 =+ w2) m) md md2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bytes_in_mem_def; LENGTH] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LT_0; WORD_ADD_0; APPLY_UPDATE_THM] THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n + 1 < SUC m <=> n < m`] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w] THEN REWRITE_TAC[ADD_SYM]]);;

(* HOL4 line 1240: val s1 = s1:('a,lab_to_target$config,'ffi) labSem$state *)
(* (written out where used: (s1:(A,lab_to_target_config,FFI)lab_state))      *)

(* HOL4 line 1242 *)
let IMP_bytes_in_memory = prove
 (`!code1 code2 (mc_conf:(A,B,C)machine_config) labs ffi_names pc i p m
     (dm:A word->bool) dm1.
     code_similar code1 code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     asm_fetch_aux pc code1 = SOME i /\
     bytes_in_mem p (prog_to_bytes code2) m dm dm1
     ==> ?j. bytes_in_mem (word_add p (word (pos_val pc 0 code2))) (line_bytes j) m dm dm1 /\
             line_ok (target_config (machine_config_target mc_conf)) labs ffi_names
               (pos_val pc 0 code2) j /\
             pos_val (pc + 1) 0 code2 = pos_val pc 0 code2 + LENGTH (line_bytes j) /\
             line_similar i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`code2:((A)sec)list`; `code1:((A)sec)list`; `pc:num`; `i:(A)line`;
                `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`;
                `ffi_names:ffiname list`] prog_to_bytes_lemma) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `j:(A)line` THEN
  UNDISCH_TAC `bytes_in_mem (p:A word) (prog_to_bytes (code2:((A)sec)list)) (m:A word->byte)
                 dm dm1` THEN
  ASM_REWRITE_TAC[bytes_in_mem_APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let LTTP1AUX_fetch_bytes = prove
 (`!(s1:(A,D,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs ffi_names
     (p:A word) (t1:(A)asm_state) l.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME l
     ==> ?j. bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
               (line_bytes j) (asm_state_mem t1) (asm_state_mem_domain t1) /\
             bytes_in_mem (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
               (line_bytes j) (asm_state_mem t1) (asm_state_mem_domain t1)
               (lab_state_mem_domain s1) /\
             line_ok (target_config (machine_config_target mc_conf)) labs ffi_names
               (pos_val (lab_state_pc s1) 0 code2) j /\
             pos_val (lab_state_pc s1 + 1) 0 code2 =
               pos_val (lab_state_pc s1) 0 code2 + LENGTH (line_bytes j) /\
             line_similar l j`,
  REWRITE_TAC[asm_fetch_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`lab_state_code (s1:(A,D,FFI)lab_state)`; `code2:((A)sec)list`;
    `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffi_names:ffiname list`;
    `lab_state_pc (s1:(A,D,FFI)lab_state)`; `l:(A)line`; `p:A word`;
    `asm_state_mem (t1:(A)asm_state)`; `asm_state_mem_domain (t1:(A)asm_state)`;
    `lab_state_mem_domain (s1:(A,D,FFI)lab_state)`] IMP_bytes_in_memory) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[bytes_in_mem_IMP]);;

(* HOL4 line 1260 *)
let IMP_bytes_in_memory_JumpReg = prove
 (`!(s1:(A,D,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs ffi_names
     (p:A word) (t1:(A)asm_state) r1 l n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (Asm (Asmi (JumpReg r1)) l n)
     ==> bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
           (asm_config_encode (target_config (machine_config_target mc_conf)) (JumpReg r1))
           (asm_state_mem t1) (asm_state_mem_domain t1) /\
         asm_ok (JumpReg r1) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_ok_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN FS[enc_with_nop_thm; cbw_to_asm_def] THEN RVEQ_TAC THEN
  FS[bytes_in_memory_APPEND]);;

(* HOL4 lines 1281-1282: val case_eq_thms0, val bool_case_eq_thms (lists of *)
(* case theorems for the proofs: all_case_eqs() here)                        *)

(* HOL4 line 1286 *)
let IMP_bytes_in_memory_Jump = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) jtarget l bytes n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm (lab_Jump jtarget) l bytes n)
     ==> ?tt enc.
           tt = word_sub (word (find_pos jtarget labs))
                  (word (pos_val (lab_state_pc s1) 0 code2)) /\
           enc = asm_config_encode (target_config (machine_config_target mc_conf))
                   (asm_Jump tt) /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
           asm_ok (asm_Jump tt) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASES_ON `jtarget:lab` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; get_label_def; lab_inst_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  CASES_ON `lab_lookup a0' a1' (labs:(num spt)spt)` THEN FS[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP lab_lookup_IMP) THEN
  FS[LET_DEF; LET_END_DEF; enc_with_nop_thm] THEN RVEQ_TAC THEN
  FS[bytes_in_memory_APPEND]);;

(* HOL4 line 1314 *)
let IMP_bytes_in_memory_JumpCmp = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) cmp rr ri jtarget l bytes n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jtarget) l bytes n)
     ==> ?tt enc.
           tt = word_sub (word (find_pos jtarget labs))
                  (word (pos_val (lab_state_pc s1) 0 code2)) /\
           enc = asm_config_encode (target_config (machine_config_target mc_conf))
                   (asm_JumpCmp cmp rr ri tt) /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
           asm_ok (asm_JumpCmp cmp rr ri tt) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASES_ON `jtarget:lab` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; get_label_def; lab_inst_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  CASES_ON `lab_lookup a0' a1' (labs:(num spt)spt)` THEN FS[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP lab_lookup_IMP) THEN
  FS[LET_DEF; LET_END_DEF; enc_with_nop_thm] THEN RVEQ_TAC THEN
  FS[bytes_in_memory_APPEND]);;

(* HOL4 line 1342 *)
let IMP_bytes_in_memory_JumpCmp_1 = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) cmp rr ri jtarget l bytes n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jtarget) l bytes n)
     ==> ?tt bytes.
           tt = word_sub (word (find_pos jtarget labs))
                  (word (pos_val (lab_state_pc s1) 0 code2)) /\
           enc_with_nop (asm_config_encode (target_config (machine_config_target mc_conf)))
             (asm_JumpCmp cmp rr ri tt) bytes /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
           pos_val (lab_state_pc s1 + 1) 0 code2 =
             pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes /\
           asm_ok (asm_JumpCmp cmp rr ri tt) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASES_ON `jtarget:lab` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; get_label_def; lab_inst_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  CASES_ON `lab_lookup a0' a1' (labs:(num spt)spt)` THEN FS[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP lab_lookup_IMP) THEN
  FS[LET_DEF; LET_END_DEF] THEN EXISTS_TAC `a2:byte list` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1371 *)
let IMP_bytes_in_memory_Call = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) ww l bytes n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm (lab_Call ww) l bytes n)
     ==> F`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def]) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 1387 *)
let IMP_bytes_in_memory_LocValue = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) reg l1 l2 l bytes n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm (lab_LocValue reg (lab_Lab l1 l2)) l bytes n)
     ==> ?tt bytes.
           tt = word_sub (word (find_pos (lab_Lab l1 l2) labs))
                  (word (pos_val (lab_state_pc s1) 0 code2)) /\
           enc_with_nop (asm_config_encode (target_config (machine_config_target mc_conf)))
             (asm_Loc reg tt) bytes /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
           pos_val (lab_state_pc s1 + 1) 0 code2 =
             pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes /\
           asm_ok (asm_Loc reg tt) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; get_label_def; lab_inst_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  CASES_ON `lab_lookup l1 l2 (labs:(num spt)spt)` THEN FS[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP lab_lookup_IMP) THEN
  FS[LET_DEF; LET_END_DEF] THEN EXISTS_TAC `a2:byte list` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1416 *)
let IMP_bytes_in_memory_Inst = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) i bytes len.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (Asm (Asmi (asm_Inst i)) bytes len)
     ==> ?bytes.
           enc_with_nop (asm_config_encode (target_config (machine_config_target mc_conf)))
             (asm_Inst i) bytes /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
           bytes_in_mem (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) (lab_state_mem_domain s1) /\
           pos_val (lab_state_pc s1 + 1) 0 code2 =
             pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes /\
           asm_ok (asm_Inst i) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; cbw_to_asm_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  EXISTS_TAC `a1:byte list` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1445 *)
let IMP_bytes_in_memory_Cbw = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) r1 r2 bytes len.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (Asm (Cbw r1 r2) bytes len)
     ==> ?bytes.
           enc_with_nop (asm_config_encode (target_config (machine_config_target mc_conf)))
             (asm_Inst (Mem Store8 r2 (Addr r1 (word 0)))) bytes /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
           bytes_in_mem (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) (lab_state_mem_domain s1) /\
           pos_val (lab_state_pc s1 + 1) 0 code2 =
             pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes /\
           asm_ok (asm_Inst (Mem Store8 r2 (Addr r1 (word 0))))
             (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; cbw_to_asm_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  EXISTS_TAC `a1:byte list` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1474 *)
let IMP_bytes_in_memory_CallFFI = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) name l bytes n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm (CallFFI name) l bytes n)
     ==> ?tt enc.
           tt = word_sub (word 0)
                  (word (pos_val (lab_state_pc s1) 0 code2 +
                         (3 + get_ffi_index ffi_names (ExtCall name)) * ffi_offset)) /\
           enc = asm_config_encode (target_config (machine_config_target mc_conf))
                   (asm_Jump tt) /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
           asm_ok (asm_Jump tt) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; LET_DEF; LET_END_DEF; enc_with_nop_thm]) THEN
  FS[] THEN RVEQ_TAC THEN FS[bytes_in_memory_APPEND]);;

(* HOL4 line 1499 *)
let IMP_bytes_in_memory_Halt = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) l bytes n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm lab_Halt l bytes n)
     ==> ?tt enc.
           tt = word_sub (word 0) (word (pos_val (lab_state_pc s1) 0 code2 + ffi_offset)) /\
           enc = asm_config_encode (target_config (machine_config_target mc_conf))
                   (asm_Jump tt) /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
           asm_ok (asm_Jump tt) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; LET_DEF; LET_END_DEF; enc_with_nop_thm]) THEN
  FS[] THEN RVEQ_TAC THEN FS[bytes_in_memory_APPEND]);;

(* HOL4 line 1524 *)
let IMP_bytes_in_memory_Install = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) code2 (mc_conf:(A,B,C)machine_config) labs
     ffi_names (p:A word) (t1:(A)asm_state) c l n.
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     asm_fetch s1 = SOME (LabAsm lab_Install c l n)
     ==> ?tt enc.
           tt = word_sub (word 0)
                  (word (pos_val (lab_state_pc s1) 0 code2 + 2 * ffi_offset)) /\
           enc = asm_config_encode (target_config (machine_config_target mc_conf))
                   (asm_Jump tt) /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             enc (asm_state_mem t1) (asm_state_mem_domain t1) /\
           asm_ok (asm_Jump tt) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LTTP1AUX_fetch_bytes) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; LET_DEF; LET_END_DEF; enc_with_nop_thm]) THEN
  FS[] THEN RVEQ_TAC THEN FS[bytes_in_memory_APPEND]);;

(* HOL4 line 1549 *)
let all_enc_ok_asm_fetch_aux_IMP_line_ok = prove
 (`!pc n code2 (c:(A)asm_config) labs ffis line.
     all_enc_ok c labs ffis n code2 /\ asm_fetch_aux pc code2 = SOME line
     ==> line_ok c labs ffis (pos_val pc n code2) line`,
  MATCH_MP_TAC pos_val_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[asm_fetch_aux_def; option_DISTINCT];
    DISCH_TAC THEN REWRITE_TAC[asm_fetch_aux_def; all_enc_ok_def; pos_val_def] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[asm_fetch_aux_def; all_enc_ok_def; pos_val_def] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [MESON_TAC[]; ASM_MESON_TAC[]]);;

let LTTP1AUX_code_similar_CONS_L = prove
 (`!(code2:((A)sec)list) k lines1 rest1.
     code_similar (CONS (Section k lines1) rest1) code2 <=>
     ?lines2 rest2. code2 = CONS (Section k lines2) rest2 /\
                    ALL2 line_similar lines1 lines2 /\ code_similar rest1 rest2`,
  GEN_TAC THEN CASES_ON `code2:((A)sec)list` THEN REWRITE_TAC[code_similar_def; NOT_CONS_NIL] THEN
  CASES_ON `a0:(A)sec` THEN REWRITE_TAC[code_similar_def; CONS_11; injectivity "sec"] THEN
  MESON_TAC[]);;

(* HOL4 line 1568 *)
let code_similar_IMP_asm_fetch_aux_line_similar = prove
 (`!pc (code1:((A)sec)list) code2.
     code_similar code1 code2
     ==> OPTREL line_similar (asm_fetch_aux pc code1) (asm_fetch_aux pc code2)`,
  MATCH_MP_TAC asm_fetch_aux_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[code_similar_nil] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[asm_fetch_aux_def; OPTREL_THM];
    DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[LTTP1AUX_code_similar_CONS_L; LIST_REL_NIL] THEN
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[asm_fetch_aux_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[LTTP1AUX_code_similar_CONS_L; LIST_REL_CONS1] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `is_Label (y:(A)line) <=> is_Label (h':(A)line)` ASSUME_TAC THENL
   [UNDISCH_TAC `line_similar (y:(A)line) h'` THEN CASES_ON `y:(A)line` THEN
    CASES_ON `h':(A)line` THEN REWRITE_TAC[line_similar_def; is_Label_def];
    ALL_TAC] THEN
  REWRITE_TAC[asm_fetch_aux_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `is_Label (h':(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
                                              not(is_conj(lhand(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[code_similar_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `pos = 0` THEN ASM_REWRITE_TAC[OPTREL_THM] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_conj(lhand(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[code_similar_def]);;

(* HOL4 line 1586 *)
let asm_fetch_aux_pos_val_LENGTH_EQ = prove
 (`!pc n code2 line (conf:(A)asm_config) labs ffi_names bytes'.
     asm_fetch_aux pc code2 = SOME line /\
     all_enc_ok conf labs ffi_names n code2 /\
     pos_val (pc + 1) n code2 = LENGTH bytes' + pos_val pc n code2
     ==> LENGTH (line_bytes line) = LENGTH (bytes':byte list)`,
  MATCH_MP_TAC pos_val_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[asm_fetch_aux_def; option_DISTINCT];
    DISCH_TAC THEN REWRITE_TAC[asm_fetch_aux_def; all_enc_ok_def; pos_val_def] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[asm_fetch_aux_def; all_enc_ok_def; pos_val_def; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP pos_val_0 th]) THEN
    ASM_SIMP_TAC[LENGTH_line_bytes] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i - 1 + 1 = i` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let LTTP1AUX_enc_with_nop_LENGTH = prove
 (`!(enc:(A)asm->byte list) b bytes1 bytes2.
     enc_with_nop enc b bytes1 /\ enc_with_nop enc b bytes2 /\
     LENGTH bytes1 = LENGTH bytes2 ==> bytes1 = bytes2`,
  REWRITE_TAC[enc_with_nop_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MESON_TAC[];
    DISCH_THEN(fun th -> match CONJUNCTS th with
                           [th1; th2; th3] -> ONCE_REWRITE_TAC[th1; th2] THEN REWRITE_TAC[th3]
                         | _ -> failwith "LTTP1AUX_enc_with_nop_LENGTH")]);;

(* HOL4 line 1606 *)
let IMP_bytes_in_memory_ShareMem = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) mop r ad l n code2
     (mc_conf:(A,B,C)machine_config) labs ffi_names (p:A word) (t1:(A)asm_state).
     asm_fetch_aux (lab_state_pc s1) (lab_state_code s1) = SOME (Asm (ShareMem mop r ad) l n) /\
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1)
     ==> ?bytes.
           asm_fetch_aux (lab_state_pc s1) code2 =
             SOME (Asm (ShareMem mop r ad) bytes (LENGTH bytes)) /\
           enc_with_nop (asm_config_encode (target_config (machine_config_target mc_conf)))
             (asm_Inst (Mem mop r ad)) bytes /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) /\
           bytes_in_mem (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             bytes (asm_state_mem t1) (asm_state_mem_domain t1) (lab_state_mem_domain s1) /\
           pos_val (lab_state_pc s1 + 1) 0 code2 =
             pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes /\
           asm_ok (asm_Inst (Mem mop r ad)) (target_config (machine_config_target mc_conf))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
    `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffi_names:ffiname list`;
    `p:A word`; `t1:(A)asm_state`; `Asm (ShareMem mop r ad) l n:(A)line`]
    LTTP1AUX_fetch_bytes) THEN
  ASM_REWRITE_TAC[asm_fetch_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` MP_TAC) THEN
  CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def; cbw_to_asm_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  EXISTS_TAC `a1:byte list` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`;
    `lab_state_code (s1:(A,lab_to_target_config,FFI)lab_state)`; `code2:((A)sec)list`]
    code_similar_IMP_asm_fetch_aux_line_similar) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `asm_fetch_aux (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state))
             (code2:((A)sec)list)` THEN
  ASM_REWRITE_TAC[OPTREL_THM] THEN
  CASES_ON `a:(A)line` THEN REWRITE_TAC[line_similar_def] THEN DISCH_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `0`;
    `code2:((A)sec)list`; `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
    `labs:(num spt)spt`; `ffi_names:ffiname list`;
    `Asm (ShareMem mop r ad) a1' a2':(A)line`] all_enc_ok_asm_fetch_aux_IMP_line_ok) THEN
  ASM_REWRITE_TAC[line_ok_def; cbw_to_asm_def] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `0`;
    `code2:((A)sec)list`; `Asm (ShareMem mop r ad) a1' a2':(A)line`;
    `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
    `labs:(num spt)spt`; `ffi_names:ffiname list`; `a1:byte list`]
    asm_fetch_aux_pos_val_LENGTH_EQ) THEN
  ASM_REWRITE_TAC[line_bytes_def] THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `a1':byte list = a1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC LTTP1AUX_enc_with_nop_LENGTH THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 1655 *)
let bytes_in_mem_IMP_memory = prove
 (`!(xs:byte list) (a:A word) dm1 (m:A word->byte) m1 dm.
     (!a. ~(a IN dm1) ==> m a = m1 a)
     ==> bytes_in_mem a xs m dm dm1
     ==> bytes_in_memory a xs m1 dm`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bytes_in_mem_def; bytes_in_memory_def] THEN
  ASM_MESON_TAC[]);;

let LTTP1AUX_state_rel_mem = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) (ms1:B) a b.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1) a =
       SOME b
     ==> a IN machine_config_prog_addresses mc_conf /\ asm_state_mem t1 a = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[mem_load_byte_aux_def] THEN
  CASES_ON `lab_state_mem (s1:(A,lab_to_target_config,FFI)lab_state) (byte_align (a:A word))` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A word` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "word_loc_val_byte")) (concl th))) THEN
  ASM_REWRITE_TAC[word_loc_val_byte_def; word_loc_val_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 1666 *)
let read_bytearray_state_rel = prove
 (`!n (a:A word) x (mc_conf:(A,B,C)machine_config) code2 labs p
     (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) (ms1:B).
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     read_bytearray a n
       (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME x
     ==> read_bytearray a n
           (\a. if a IN machine_config_prog_addresses mc_conf
                then SOME (asm_state_mem t1 a) else NONE) = SOME x`,
  INDUCT_TAC THEN REWRITE_TAC[read_bytearray_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CASES_ON `mem_load_byte_aux (lab_state_mem (s1:(A,lab_to_target_config,FFI)lab_state))
              (lab_state_mem_domain s1) (lab_state_be s1) (a:A word)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
    `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
    `a:A word`; `a':byte`] LTTP1AUX_state_rel_mem) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `read_bytearray (word_add (a:A word) (word 1)) n
              (mem_load_byte_aux (lab_state_mem (s1:(A,lab_to_target_config,FFI)lab_state))
                 (lab_state_mem_domain s1) (lab_state_be s1))` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:A word) (word 1)`; `a'':byte list`;
    `mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
    `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 1686 *)
let IMP_has_io_name = prove
 (`!(s1:(A,D,FFI)lab_state) index l bytes n.
     asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)
     ==> has_io_name index (lab_state_code s1)`,
  SUBGOAL_THEN `!pc (code:((A)sec)list) index l bytes n.
     asm_fetch_aux pc code = SOME (LabAsm (CallFFI index) l bytes n)
     ==> has_io_name index code` (fun th -> MESON_TAC[th; asm_fetch_def]) THEN
  MATCH_MP_TAC asm_fetch_aux_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[asm_fetch_aux_def; option_DISTINCT];
    DISCH_TAC THEN REWRITE_TAC[asm_fetch_aux_def; has_io_name_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[asm_fetch_aux_def; has_io_name_def] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `pos = 0` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]; ASM_MESON_TAC[]]);;

(* HOL4 line 1700 *)
let bytes_in_mem_asm_write_bytearray_lemma = prove
 (`!(xs:byte list) (p:A word) k (m1:A word->byte) m2 d.
     (!a. ~(a IN k) ==> m1 a = m2 a)
     ==> bytes_in_mem p xs m1 d k
     ==> bytes_in_mem p xs m2 d k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bytes_in_mem_def] THEN ASM_MESON_TAC[]);;

let LTTP1AUX_mem_load_byte_aux_SOME = prove
 (`!(m:A word->(A)word_loc) dm be a b.
     mem_load_byte_aux m dm be a = SOME b ==> byte_align a IN dm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mem_load_byte_aux_def] THEN
  CASES_ON `(m:A word->(A)word_loc) (byte_align a)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 1709 *)
let bytes_in_mem_asm_write_bytearray = prove
 (`!(s1:(A,D,FFI)lab_state) c1 new_bytes x (p:A word) xs (t1:(A)asm_state).
     (!a. byte_align a IN lab_state_mem_domain s1 ==> a IN lab_state_mem_domain s1) /\
     read_bytearray c1 (LENGTH new_bytes)
       (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME x
     ==> bytes_in_mem p xs (asm_state_mem t1) (asm_state_mem_domain t1)
           (lab_state_mem_domain s1)
     ==> bytes_in_mem p xs (asm_write_bytearray c1 new_bytes (asm_state_mem t1))
           (asm_state_mem_domain t1) (lab_state_mem_domain s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC bytes_in_mem_asm_write_bytearray_lemma THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`c1:A word`,`c1:A word`) THEN SPEC_TAC(`x:byte list`,`x:byte list`) THEN
  SPEC_TAC(`asm_state_mem (t1:(A)asm_state)`,`m:A word->byte`) THEN
  SPEC_TAC(`new_bytes:byte list`,`new_bytes:byte list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[asm_write_bytearray_def; LENGTH; read_bytearray_def] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `mem_load_byte_aux (lab_state_mem (s1:(A,D,FFI)lab_state))
              (lab_state_mem_domain s1) (lab_state_be s1) (c1:A word)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `read_bytearray (word_add (c1:A word) (word 1)) (LENGTH (t:byte list))
              (mem_load_byte_aux (lab_state_mem (s1:(A,D,FFI)lab_state))
                 (lab_state_mem_domain s1) (lab_state_be s1))` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `b:A word` THEN DISCH_TAC THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP1AUX_mem_load_byte_aux_SOME) THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let LTTP1AUX_write_bytearray_Word = prove
 (`!xs (c1:A word) (m:A word->(A)word_loc) dm be a.
     (?c. m a = wl_Word c) ==> ?c'. write_bytearray c1 xs m dm be a = wl_Word c'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytearray_def] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (c1:A word) (word 1)`; `m:A word->(A)word_loc`;
    `dm:A word->bool`; `be:bool`; `a:A word`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN
  CASES_ON `write_bytearray (word_add (c1:A word) (word 1)) t (m:A word->(A)word_loc) dm be
              (byte_align c1)` THEN
  CASE_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 1735 *)
let write_bytearray_NOT_Loc = prove
 (`!xs c1 (s1:(A,D,FFI)lab_state) a c n n0.
     lab_state_mem s1 a = wl_Word c
     ==> ~(write_bytearray c1 xs (lab_state_mem s1) (lab_state_mem_domain s1)
             (lab_state_be s1) a = wl_Loc n n0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`xs:byte list`; `c1:A word`; `lab_state_mem (s1:(A,D,FFI)lab_state)`;
    `lab_state_mem_domain (s1:(A,D,FFI)lab_state)`; `lab_state_be (s1:(A,D,FFI)lab_state)`;
    `a:A word`] LTTP1AUX_write_bytearray_Word) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]]);;

let LTTP1AUX_write_bytearray_byte = prove
 (`!new_bytes (c1:A word) (m:A word->(A)word_loc) dm be (tm:A word->byte) x p labs a.
     good_dimindex (:A) /\
     read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux m dm be) = SOME x /\
     word_loc_val_byte p labs m a be = SOME (tm a)
     ==> word_loc_val_byte p labs (write_bytearray c1 new_bytes m dm be) a be =
         SOME (asm_write_bytearray c1 new_bytes tm a)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytearray_def; asm_write_bytearray_def] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; read_bytearray_def] THEN
  CASES_ON `mem_load_byte_aux (m:A word->(A)word_loc) dm be c1` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `read_bytearray (word_add (c1:A word) (word 1)) (LENGTH (t:byte list))
              (mem_load_byte_aux (m:A word->(A)word_loc) dm be)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (c1:A word) (word 1)`; `m:A word->(A)word_loc`;
    `dm:A word->bool`; `be:bool`; `tm:A word->byte`; `a'':byte list`; `p:A word`;
    `labs:(num spt)spt`; `a:A word`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?v0. (m:A word->(A)word_loc) (byte_align c1) = wl_Word v0 /\
                     byte_align c1 IN dm` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mem_load_byte_aux (m:A word->(A)word_loc) dm be c1 = SOME a'` THEN
    REWRITE_TAC[mem_load_byte_aux_def] THEN
    CASES_ON `(m:A word->(A)word_loc) (byte_align c1)` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:byte list`; `word_add (c1:A word) (word 1)`; `m:A word->(A)word_loc`;
    `dm:A word->bool`; `be:bool`; `byte_align (c1:A word)`] LTTP1AUX_write_bytearray_Word) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:A word`) THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  UNDISCH_TAC `write_bytearray (word_add (c1:A word) (word 1)) t (m:A word->(A)word_loc) dm be
                 (byte_align c1) = wl_Word v` THEN
  UNDISCH_TAC `word_loc_val_byte (p:A word) labs
      (write_bytearray (word_add (c1:A word) (word 1)) t (m:A word->(A)word_loc) dm be) a be =
      SOME (asm_write_bytearray (word_add c1 (word 1)) t (tm:A word->byte) a)` THEN
  SPEC_TAC(`write_bytearray (word_add (c1:A word) (word 1)) t (m:A word->(A)word_loc) dm be`,
           `M:A word->(A)word_loc`) THEN
  SPEC_TAC(`asm_write_bytearray (word_add (c1:A word) (word 1)) t (tm:A word->byte)`,
           `TM:A word->byte`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_loc_val_byte_def; APPLY_UPDATE_THM] THEN
  ASM_CASES_TAC `a:A word = c1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[word_loc_val_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[good_dimindex_get_byte_set_byte];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `byte_align (c1:A word) = byte_align a` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_loc_val_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[get_byte_set_byte_diff] THEN
    UNDISCH_TAC `word_loc_val_byte (p:A word) labs (M:A word->(A)word_loc) a be =
                 SOME ((TM:A word->byte) a)` THEN
    REWRITE_TAC[word_loc_val_byte_def] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `byte_align (c1:A word) = byte_align a`)) THEN
    ASM_REWRITE_TAC[word_loc_val_def] THEN CASE_REWRITE_TAC[];
    UNDISCH_TAC `word_loc_val_byte (p:A word) labs (M:A word->(A)word_loc) a be =
                 SOME ((TM:A word->byte) a)` THEN
    REWRITE_TAC[word_loc_val_byte_def]]);;

(* HOL4 line 1747 *)
let CallFFI_bytearray_lemma = prove
 (`!(a:A word) (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) (mc_conf:(A,B,C)machine_config)
     c1 new_bytes x p labs.
     byte_align a IN lab_state_mem_domain s1 /\ good_dimindex (:A) /\
     a IN asm_state_mem_domain t1 /\
     a IN lab_state_mem_domain s1 /\
     lab_state_be s1 = asm_config_big_endian (target_config (machine_config_target mc_conf)) /\
     read_bytearray c1 (LENGTH new_bytes)
       (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME x /\
     word_loc_val_byte p labs (lab_state_mem s1) a
       (asm_config_big_endian (target_config (machine_config_target mc_conf))) =
       SOME (asm_state_mem t1 a)
     ==> word_loc_val_byte p labs
           (write_bytearray c1 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
              (lab_state_be s1)) a
           (asm_config_big_endian (target_config (machine_config_target mc_conf))) =
         SOME (asm_write_bytearray c1 new_bytes (asm_state_mem t1) a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_const(rand(concl th)) = false &&
                             lhs(concl th) = `lab_state_be (s1:(A,D,FFI)lab_state)`
                          then SUBST_ALL_TAC th else NO_TAC) THEN
  MATCH_MP_TAC LTTP1AUX_write_bytearray_byte THEN ASM_MESON_TAC[]);;

(* HOL4 line 1786 *)
let MULT_ADD_LESS_MULT = prove
 (`!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m * j <= m * k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `(m + 1) * k <= l * k` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 1796 *)
let aligned_IMP_ADD_LESS_dimword = prove
 (`!k (x:A word).
     alignment_aligned k x /\ k <= dimindex (:A) ==> val x + (2 EXP k - 1) < dimword (:A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_w2n; dimword_def; MOD_EQ_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:num`) ASSUME_TAC) THEN
  MP_TAC(ISPEC `x:A word` VAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP dimindex(:A) = 2 EXP (dimindex(:A) - k) * 2 EXP k` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LT_MULT_RCANCEL; EXP_2_NE_0] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`q:num`; `2 EXP k - 1`; `2 EXP k`; `2 EXP (dimindex(:A) - k)`; `2 EXP k`]
    MULT_ADD_LESS_MULT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  MP_TAC(SPEC `k:num` EXP_2_NE_0) THEN ARITH_TAC);;

let LTTP1AUX_byte_align_32 = prove
 (`dimindex (:A) = 32 ==> !x:A word. byte_align x = align 2 x`,
  DISCH_TAC THEN ASM_REWRITE_TAC[byte_align_def] THEN
  REWRITE_TAC[(RAND_CONV NUM_REDUCE_CONV THENC LOG2_CONV) `LOG2 (32 DIV 8)`]);;

let LTTP1AUX_byte_align_64 = prove
 (`dimindex (:A) = 64 ==> !x:A word. byte_align x = align 3 x`,
  DISCH_TAC THEN ASM_REWRITE_TAC[byte_align_def] THEN
  REWRITE_TAC[(RAND_CONV NUM_REDUCE_CONV THENC LOG2_CONV) `LOG2 (64 DIV 8)`]);;

(* HOL4 line 1809 *)
let aligned_2_imp = prove
 (`!(x:A word).
     alignment_aligned 2 x /\ dimindex (:A) = 32
     ==> byte_align x = x /\
         byte_align (word_add x (word 1)) = x /\
         byte_align (word_add x (word 2)) = x /\
         byte_align (word_add x (word 3)) = x`,
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[LTTP1AUX_byte_align_32] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[aligned_def];
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC align_add_aligned THEN ASM_REWRITE_TAC[VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1821 *)
let aligned_2_not_eq = prove
 (`!(x:A word) a.
     alignment_aligned 2 x /\ dimindex (:A) = 32 /\ ~(x = byte_align a)
     ==> ~(x = a) /\ ~(word_add x (word 1) = a) /\ ~(word_add x (word 2) = a) /\
         ~(word_add x (word 3) = a)`,
  MESON_TAC[aligned_2_imp]);;

(* HOL4 line 1832 *)
let aligned_3_imp = prove
 (`!(x:A word).
     alignment_aligned 3 x /\ dimindex (:A) = 64
     ==> byte_align x = x /\
         byte_align (word_add x (word 1)) = x /\
         byte_align (word_add x (word 2)) = x /\
         byte_align (word_add x (word 3)) = x /\
         byte_align (word_add x (word 4)) = x /\
         byte_align (word_add x (word 5)) = x /\
         byte_align (word_add x (word 6)) = x /\
         byte_align (word_add x (word 7)) = x`,
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[LTTP1AUX_byte_align_64] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[aligned_def];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC align_add_aligned THEN ASM_REWRITE_TAC[VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1848 *)
let aligned_3_not_eq = prove
 (`!(x:A word) a.
     alignment_aligned 3 x /\ dimindex (:A) = 64 /\ ~(x = byte_align a)
     ==> ~(x = a) /\ ~(word_add x (word 1) = a) /\ ~(word_add x (word 2) = a) /\
         ~(word_add x (word 3) = a) /\ ~(word_add x (word 4) = a) /\
         ~(word_add x (word 5) = a) /\ ~(word_add x (word 6) = a) /\
         ~(word_add x (word 7) = a)`,
  MESON_TAC[aligned_3_imp]);;

(* HOL4 line 1863 (HOL4 || is right-associative here: a || b || c is      *)
(* a || (b || c); << binds tighter than ||)                                  *)
let dimword_eq_32_imp_or_bytes = prove
 (`!(x:A word).
     dimindex (:A) = 32
     ==> word_or (word_zx (word_zx x:byte))
          (word_or (word_shl (word_zx (word_zx (word_ushr x 8):byte)) 8)
          (word_or (word_shl (word_zx (word_zx (word_ushr x 16):byte)) 16)
                   (word_shl (word_zx (word_zx (word_ushr x 24):byte)) 24))) = x`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_USHR; DIMINDEX_8] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1873 *)
let dimword_eq_64_imp_or_bytes = prove
 (`!(x:A word).
     dimindex (:A) = 64
     ==> word_or (word_zx (word_zx x:byte))
          (word_or (word_shl (word_zx (word_zx (word_ushr x 8):byte)) 8)
          (word_or (word_shl (word_zx (word_zx (word_ushr x 16):byte)) 16)
          (word_or (word_shl (word_zx (word_zx (word_ushr x 24):byte)) 24)
          (word_or (word_shl (word_zx (word_zx (word_ushr x 32):byte)) 32)
          (word_or (word_shl (word_zx (word_zx (word_ushr x 40):byte)) 40)
          (word_or (word_shl (word_zx (word_zx (word_ushr x 48):byte)) 48)
                   (word_shl (word_zx (word_zx (word_ushr x 56):byte)) 56))))))) = x`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_USHR; DIMINDEX_8] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1887 *)
let byte_align_32_eq = prove
 (`!(a:A word).
     dimindex (:A) = 32 ==> word_add (byte_align a) (word (val a MOD 4)) = a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LTTP1AUX_byte_align_32; align_w2n] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MP_TAC(SPECL [`val (a:A word)`; `4`] DIVISION) THEN
  REWRITE_TAC[ARITH_RULE `~(4 = 0)`] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[WORD_VAL]);;

(* HOL4 line 1899 *)
let byte_align_64_eq = prove
 (`!(a:A word).
     dimindex (:A) = 64 ==> word_add (byte_align a) (word (val a MOD 8)) = a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LTTP1AUX_byte_align_64; align_w2n] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MP_TAC(SPECL [`val (a:A word)`; `8`] DIVISION) THEN
  REWRITE_TAC[ARITH_RULE `~(8 = 0)`] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[WORD_VAL]);;

(* HOL4 line 1911 *)
let byte_align_32_IMP = prove
 (`!(a:A word).
     dimindex (:A) = 32
     ==> (byte_align a = a ==> val a MOD 4 = 0) /\
         (word_add (byte_align a) (word 1) = a ==> val a MOD 4 = 1) /\
         (word_add (byte_align a) (word 2) = a ==> val a MOD 4 = 2) /\
         (word_add (byte_align a) (word 3) = a ==> val a MOD 4 = 3)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:A word` byte_align_32_eq) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`val (a:A word)`; `4`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_RULE `~(4 = 0)`] THEN
  SPEC_TAC(`val (a:A word) MOD 4`,`k:num`) THEN SPEC_TAC(`byte_align (a:A word)`,`b:A word`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_ADD_CANCEL; WORD_EQ_ADD_LCANCEL] THEN
  REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:A word->num`) THEN
  ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `k < 4 ==> k < 4294967296`] THEN ASM_ARITH_TAC);;

(* HOL4 line 1931 *)
let MOD4_CASES = prove
 (`!n. n MOD 4 = 0 \/ n MOD 4 = 1 \/ n MOD 4 = 2 \/ n MOD 4 = 3`,
  GEN_TAC THEN MP_TAC(SPECL [`n:num`; `4`] MOD_LT_EQ) THEN ARITH_TAC);;

(* HOL4 line 1940 *)
let byte_align_32_CASES = prove
 (`!(a:A word).
     dimindex (:A) = 32
     ==> word_add (byte_align a) (word 3) = a \/ word_add (byte_align a) (word 2) = a \/
         word_add (byte_align a) (word 1) = a \/ byte_align a = a`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:A word` byte_align_32_eq) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `val (a:A word)` MOD4_CASES) THEN
  SPEC_TAC(`val (a:A word) MOD 4`,`k:num`) THEN SPEC_TAC(`byte_align (a:A word)`,`b:A word`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN MESON_TAC[]);;

(* HOL4 line 1953 *)
let MOD8_CASES = prove
 (`!n. n MOD 8 = 0 \/ n MOD 8 = 1 \/ n MOD 8 = 2 \/ n MOD 8 = 3 \/
       n MOD 8 = 4 \/ n MOD 8 = 5 \/ n MOD 8 = 6 \/ n MOD 8 = 7`,
  GEN_TAC THEN MP_TAC(SPECL [`n:num`; `8`] MOD_LT_EQ) THEN ARITH_TAC);;

(* HOL4 line 1964 *)
let byte_align_64_CASES = prove
 (`!(a:A word).
     dimindex (:A) = 64
     ==> word_add (byte_align a) (word 7) = a \/ word_add (byte_align a) (word 6) = a \/
         word_add (byte_align a) (word 5) = a \/ word_add (byte_align a) (word 4) = a \/
         word_add (byte_align a) (word 3) = a \/ word_add (byte_align a) (word 2) = a \/
         word_add (byte_align a) (word 1) = a \/ byte_align a = a`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:A word` byte_align_64_eq) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `val (a:A word)` MOD8_CASES) THEN
  SPEC_TAC(`val (a:A word) MOD 8`,`k:num`) THEN SPEC_TAC(`byte_align (a:A word)`,`b:A word`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0] THEN MESON_TAC[]);;

(* HOL4 line 1981 *)
let byte_align_64_IMP = prove
 (`!(a:A word).
     dimindex (:A) = 64
     ==> (word_add (byte_align a) (word 7) = a ==> val a MOD 8 = 7) /\
         (word_add (byte_align a) (word 6) = a ==> val a MOD 8 = 6) /\
         (word_add (byte_align a) (word 5) = a ==> val a MOD 8 = 5) /\
         (word_add (byte_align a) (word 4) = a ==> val a MOD 8 = 4) /\
         (word_add (byte_align a) (word 3) = a ==> val a MOD 8 = 3) /\
         (word_add (byte_align a) (word 2) = a ==> val a MOD 8 = 2) /\
         (word_add (byte_align a) (word 1) = a ==> val a MOD 8 = 1) /\
         (byte_align a = a ==> val a MOD 8 = 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:A word` byte_align_64_eq) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`val (a:A word)`; `8`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_RULE `~(8 = 0)`] THEN
  SPEC_TAC(`val (a:A word) MOD 8`,`k:num`) THEN SPEC_TAC(`byte_align (a:A word)`,`b:A word`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_ADD_CANCEL; WORD_EQ_ADD_LCANCEL] THEN
  REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `val:A word->num`) THEN
  ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `k < 8 ==> k < 18446744073709551616`] THEN ASM_ARITH_TAC);;

let LTTP1AUX_lab_regs_upd = prove
 (`(!r v (s:(A,D,FFI)lab_state).
      lab_state_regs (lab_upd_reg r v s) = (r =+ v) (lab_state_regs s) /\
      lab_state_failed (lab_upd_reg r v s) = lab_state_failed s) /\
   (!b (s:(A,D,FFI)lab_state).
      lab_state_regs (lab_assert b s) = lab_state_regs s /\
      (lab_state_failed (lab_assert b s) <=> ~b \/ lab_state_failed s)) /\
   (!r v (t:(A)asm_state).
      asm_state_regs (asm_upd_reg r v t) = (r =+ v) (asm_state_regs t)) /\
   (!b (t:(A)asm_state). asm_state_regs (asm_assert b t) = asm_state_regs t)`,
  REWRITE_TAC[lab_upd_reg_def; lab_assert_def; asm_upd_reg_def; asm_assert_def] THEN
  SIMP[]);;

let LTTP1AUX_word_loc_val_upd = prove
 (`!(p:A word) labs (f:num->(A)word_loc) (g:num->A word) (k:num) v w.
     (!r. word_loc_val p labs (f r) = SOME (g r)) /\ word_loc_val p labs v = SOME w
     ==> !r. word_loc_val p labs ((k =+ v) f r) = SOME ((k =+ w) g r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 2005 (labSem's arith_upd and its Overload read_reg r s =       *)
(* s.regs r for s1, asmSem's arith_upd for t1)                               *)
let arith_upd_lemma = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     ~lab_state_failed (lab_arith_upd a s1)
     ==> !r. word_loc_val p labs (lab_state_regs (lab_arith_upd a s1) r) =
             SOME (asm_state_regs (asm_arith_upd a t1) r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r w. lab_state_regs (s1:(A,D,FFI)lab_state) r = wl_Word w ==>
                      asm_state_regs (t1:(A)asm_state) r = w` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    ASM_REWRITE_TAC[word_loc_val_def; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `a:(A)asm_arith` THEN
  TRY(CASES_ON `a0:binop`) THEN TRY(CASES_ON `a3:(A)reg_imm`) THEN
  REWRITE_TAC[lab_arith_upd_def; lab_binop_upd_def; lab_reg_imm_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lab_arith_upd_def; lab_binop_upd_def; lab_reg_imm_def]) THEN
  EVERY_CASE_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LTTP1AUX_lab_regs_upd]) THEN
  TRY(FIRST_X_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  REWRITE_TAC[asm_arith_upd_def; asm_binop_upd_def; asm_reg_imm_def; LTTP1AUX_lab_regs_upd;
              read_reg_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC LTTP1AUX_word_loc_val_upd THEN CONJ_TAC THENL
          [ALL_TAC; TRY(ASM_REWRITE_TAC[word_loc_val_def; WORD_OR_IDEM] THEN NO_TAC)]) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[WORD_OR_IDEM] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2058 *)
let arith_upd_fp_regs = prove
 (`!a (s:(A,D,FFI)lab_state) (t:(A)asm_state).
     lab_state_fp_regs (lab_arith_upd a s) = lab_state_fp_regs s /\
     asm_state_fp_regs (asm_arith_upd a t) = asm_state_fp_regs t`,
  GEN_TAC THEN CASES_ON `a:(A)asm_arith` THEN TRY(CASES_ON `a0:binop`) THEN
  REWRITE_TAC[lab_arith_upd_def; lab_binop_upd_def; asm_arith_upd_def; asm_binop_upd_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN TRY EVERY_CASE_TAC THEN
  SIMP[lab_upd_reg_def; lab_assert_def; asm_upd_reg_def; asm_assert_def]);;

let _ = cake_add_simps [arith_upd_fp_regs];;

let LTTP1AUX_fp_upd_simps = prove
 (`(!r v (s:(A,D,FFI)lab_state).
      lab_state_fp_regs (lab_upd_fp_reg r v s) = (r =+ v) (lab_state_fp_regs s) /\
      lab_state_regs (lab_upd_fp_reg r v s) = lab_state_regs s /\
      lab_state_failed (lab_upd_fp_reg r v s) = lab_state_failed s /\
      lab_state_fp_regs (lab_upd_reg r w s) = lab_state_fp_regs s) /\
   (!b (s:(A,D,FFI)lab_state). lab_state_fp_regs (lab_assert b s) = lab_state_fp_regs s) /\
   (!r v (t:(A)asm_state).
      asm_state_fp_regs (asm_upd_fp_reg r v t) = (r =+ v) (asm_state_fp_regs t) /\
      asm_state_regs (asm_upd_fp_reg r v t) = asm_state_regs t /\
      asm_state_fp_regs (asm_upd_reg r u t) = asm_state_fp_regs t) /\
   (!b (t:(A)asm_state). asm_state_fp_regs (asm_assert b t) = asm_state_fp_regs t) /\
   (!d (s:(A,D,FFI)lab_state). lab_read_fp_reg d s = lab_state_fp_regs s d) /\
   (!d (t:(A)asm_state). asm_read_fp_reg d t = asm_state_fp_regs t d)`,
  REWRITE_TAC[lab_upd_fp_reg_def; lab_upd_reg_def; lab_assert_def; asm_upd_fp_reg_def;
              asm_upd_reg_def; asm_assert_def; lab_read_fp_reg_def; asm_read_fp_reg_def] THEN
  SIMP[]);;

(* HOL4 line 2068 *)
let fp_upd_lemma = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) f.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!r. lab_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
     ~lab_state_failed (lab_fp_upd f s1)
     ==> (!r. lab_state_fp_regs (lab_fp_upd f s1) r = asm_state_fp_regs (asm_fp_upd f t1) r) /\
         !r. word_loc_val p labs (lab_state_regs (lab_fp_upd f s1) r) =
             SOME (asm_state_regs (asm_fp_upd f t1) r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r w. lab_state_regs (s1:(A,D,FFI)lab_state) r = wl_Word w ==>
                      asm_state_regs (t1:(A)asm_state) r = w` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `!r. word_loc_val (p:A word) labs (lab_state_regs (s1:(A,D,FFI)lab_state) r) =
                     SOME (asm_state_regs (t1:(A)asm_state) r)` THEN
    DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
    ASM_REWRITE_TAC[word_loc_val_def; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lab_state_fp_regs (s1:(A,D,FFI)lab_state) = asm_state_fp_regs (t1:(A)asm_state)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  CASES_ON `f:fp` THEN
  REWRITE_TAC[lab_fp_upd_def; LET_DEF; LET_END_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lab_fp_upd_def; LET_DEF; LET_END_DEF]) THEN
  EVERY_CASE_TAC THEN TRY RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LTTP1AUX_lab_regs_upd; LTTP1AUX_fp_upd_simps]) THEN
  TRY(FIRST_X_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  REWRITE_TAC[asm_fp_upd_def; LTTP1AUX_lab_regs_upd; LTTP1AUX_fp_upd_simps;
              read_reg_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
                            lhs(concl th) = `lab_state_fp_regs (s1:(A,D,FFI)lab_state)`
                         then SUBST_ALL_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LTTP1AUX_lab_regs_upd; LTTP1AUX_fp_upd_simps; fpfma_def] THEN
  REPEAT CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC LTTP1AUX_word_loc_val_upd THEN CONJ_TAC THENL
          [ALL_TAC; TRY(ASM_REWRITE_TAC[word_loc_val_def] THEN NO_TAC)]) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 2098 *)
let lab_to_targetProof_Inst_share_mem_pc_update_helper = prove
 (`!(mc_conf:(A,B,C)machine_config) (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 pc' ms2.
     share_mem_state_rel mc_conf s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf) (asm_state_pc_fupd (K pc') t1) ms2
     ==> share_mem_state_rel mc_conf
           (lab_state_pc_fupd (K (lab_state_pc s1 + 1))
              (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))
           (asm_state_pc_fupd (K pc') t1) ms2`,
  REWRITE_TAC[share_mem_state_rel_def; (record_info "lab_state").ri_accfupds] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1));;

(* HOL4 line 2108 *)
let lab_to_targetProof_Inst_share_mem_reg_update_helper = prove
 (`!(mc_conf:(A,B,C)machine_config) (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 n c pc' ms2.
     share_mem_state_rel mc_conf s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf)
       (asm_state_regs_fupd (K ((n =+ c) (asm_state_regs t1)))
          (asm_state_pc_fupd (K pc') t1)) ms2
     ==> share_mem_state_rel mc_conf
           (lab_state_regs_fupd (K ((n =+ wl_Word c) (lab_state_regs s1)))
              (lab_state_pc_fupd (K (lab_state_pc s1 + 1))
                 (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))
           (asm_state_regs_fupd (K ((n =+ c) (asm_state_regs t1)))
              (asm_state_pc_fupd (K pc') t1)) ms2`,
  REWRITE_TAC[share_mem_state_rel_def; (record_info "lab_state").ri_accfupds] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1));;

(* HOL4 line 2120 *)
let arith_upd_share_mem_domain_unchange = prove
 (`!a (s1:(A,D,FFI)lab_state).
     lab_state_shared_mem_domain (lab_arith_upd a s1) = lab_state_shared_mem_domain s1`,
  REWRITE_TAC[lab_arith_upd_consts]);;

(* HOL4 line 2130 *)
let fp_upd_share_mem_domain_unchange = prove
 (`!f (s1:(A,D,FFI)lab_state).
     lab_state_shared_mem_domain (lab_fp_upd f s1) = lab_state_shared_mem_domain s1`,
  REWRITE_TAC[lab_fp_upd_consts]);;

(* HOL4 line 2138: val share_mem_state_rel_tac (a tactic) *)

(* HOL4 line 2146 *)
let align2_not_align3_4w = prove
 (`!(x:A word).
     ~alignment_aligned 3 x /\ alignment_aligned 2 x /\ dimindex (:A) = 64
     ==> x = word_add (byte_align x) (word 4) /\
         word_add x (word 1) = word_add (byte_align x) (word 5) /\
         word_add x (word 2) = word_add (byte_align x) (word 6) /\
         word_add x (word 3) = word_add (byte_align x) (word 7)`,
  GEN_TAC THEN REWRITE_TAC[aligned_w2n] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `val (x:A word) MOD 8 = 4` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (x:A word)`; `4`; `2`] MOD_MOD) THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN UNDISCH_TAC `val (x:A word) MOD 4 = 0` THEN
    UNDISCH_TAC `~(val (x:A word) MOD 8 = 0)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `val (x:A word)` MOD8_CASES) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:A word` byte_align_64_eq) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`byte_align (x:A word)`,`b:A word`) THEN GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Local helpers for Inst_lemma (prefix LTTP1AUX_): a frame lemma for      *)
(* state_rel, the six memory operations, and the per-instruction core.     *)

let LTTP1AUX_FRAME_EQS_TAC (s':term) (s:term) : tactic =
  fun (asl,w as g) ->
    let ok th =
      let c = concl th in
      is_eq c && is_comb (lhs c) && is_comb (rhs c) &&
      rand (lhs c) = s' && rand (rhs c) = s && rator (lhs c) = rator (rhs c) in
    REWRITE_TAC (filter ok (map snd asl)) g;;
let LTTP1AUX_state_rel_frame = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) (ms1:B) s1' t1' ms2.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf) t1' ms2 /\
     lab_state_mem_domain s1' = lab_state_mem_domain s1 /\
     lab_state_shared_mem_domain s1' = lab_state_shared_mem_domain s1 /\
     lab_state_be s1' = lab_state_be s1 /\ lab_state_ffi s1' = lab_state_ffi s1 /\
     lab_state_code s1' = lab_state_code s1 /\
     lab_state_compile s1' = lab_state_compile s1 /\
     lab_state_compile_oracle s1' = lab_state_compile_oracle s1 /\
     lab_state_code_buffer s1' = lab_state_code_buffer s1 /\
     lab_state_ptr_reg s1' = lab_state_ptr_reg s1 /\
     lab_state_len_reg s1' = lab_state_len_reg s1 /\
     lab_state_ptr2_reg s1' = lab_state_ptr2_reg s1 /\
     lab_state_len2_reg s1' = lab_state_len2_reg s1 /\
     lab_state_link_reg s1' = lab_state_link_reg s1 /\
     ~lab_state_failed s1' /\
     asm_state_mem_domain t1' = asm_state_mem_domain t1 /\
     asm_state_lr t1' = asm_state_lr t1 /\
     asm_state_align t1' = asm_state_align t1 /\
     (asm_state_be t1' <=> asm_state_be t1) /\
     ~asm_state_failed t1' /\
     (!r. lab_state_fp_regs s1' r = asm_state_fp_regs t1' r) /\
     (!r. word_loc_val p labs (lab_state_regs s1' r) = SOME (asm_state_regs t1' r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> word_loc_val_byte p labs (lab_state_mem s1') a (lab_state_be s1) =
              SOME (asm_state_mem t1' a)) /\
     (!a. ~(a IN lab_state_mem_domain s1) ==> asm_state_mem t1' a = asm_state_mem t1 a) /\
     asm_state_pc t1' = word_add p (word (pos_val (lab_state_pc s1') 0 code2))
     ==> lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1' t1' ms2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))
    STRIP_ASSUME_TAC) THEN
  LTTP1AUX_FRAME_EQS_TAC `s1':(A,lab_to_target_config,FFI)lab_state`
                         `s1:(A,lab_to_target_config,FFI)lab_state` THEN
  LTTP1AUX_FRAME_EQS_TAC `t1':(A)asm_state` `t1:(A)asm_state` THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> is_const t &&
           fst(dest_const t) = "word_loc_val_byte")) (concl th)
         then MP_TAC (SPEC `a:A word` th) else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] bytes_in_mem_asm_write_bytearray_lemma) THEN
  EXISTS_TAC `asm_state_mem (t1:(A)asm_state)` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] bytes_in_mem_asm_write_bytearray_lemma) THEN
  EXISTS_TAC `asm_state_mem (t1:(A)asm_state)` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "share_mem_state_rel")) (concl th))) THEN
  REWRITE_TAC[share_mem_state_rel_def] THEN
  LTTP1AUX_FRAME_EQS_TAC `s1':(A,lab_to_target_config,FFI)lab_state`
                         `s1:(A,lab_to_target_config,FFI)lab_state` THEN
  DISCH_THEN ACCEPT_TAC]);;
let LTTP1AUX_asm_failed_upd = prove
 (`(!r v (t:(A)asm_state). asm_state_failed (asm_upd_reg r v t) <=> asm_state_failed t) /\
   (!r v (t:(A)asm_state). asm_state_failed (asm_upd_fp_reg r v t) <=> asm_state_failed t) /\
   (!b (t:(A)asm_state). asm_state_failed (asm_assert b t) <=> ~b \/ asm_state_failed t)`,
  REWRITE_TAC[asm_upd_reg_def; asm_upd_fp_reg_def; asm_assert_def] THEN SIMP[]);;

let LTTP1AUX_arith_upd_failed = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     ~asm_state_failed t1 /\ ~lab_state_failed (lab_arith_upd a s1)
     ==> ~asm_state_failed (asm_arith_upd a t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r w. lab_state_regs (s1:(A,D,FFI)lab_state) r = wl_Word w ==>
                      asm_state_regs (t1:(A)asm_state) r = w` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    ASM_REWRITE_TAC[word_loc_val_def; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `a:(A)asm_arith` THEN
  TRY(CASES_ON `a0:binop`) THEN TRY(CASES_ON `a3:(A)reg_imm`) THEN
  REWRITE_TAC[asm_arith_upd_def; asm_binop_upd_def; asm_reg_imm_def; read_reg_def;
              LET_DEF; LET_END_DEF; LTTP1AUX_asm_failed_upd] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lab_arith_upd_def; lab_binop_upd_def; lab_reg_imm_def;
                              LET_DEF; LET_END_DEF]) THEN
  EVERY_CASE_TAC THEN TRY RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LTTP1AUX_lab_regs_upd]) THEN
  TRY(FIRST_X_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN ASM_REWRITE_TAC[]);;

let LTTP1AUX_fp_upd_failed = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) f.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!r. lab_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
     ~asm_state_failed t1 /\ ~lab_state_failed (lab_fp_upd f s1)
     ==> ~asm_state_failed (asm_fp_upd f t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lab_state_fp_regs (s1:(A,D,FFI)lab_state) = asm_state_fp_regs (t1:(A)asm_state)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  CASES_ON `f:fp` THEN
  REWRITE_TAC[asm_fp_upd_def; LET_DEF; LET_END_DEF; LTTP1AUX_asm_failed_upd;
              LTTP1AUX_fp_upd_simps] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lab_fp_upd_def; LET_DEF; LET_END_DEF]) THEN
  EVERY_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LTTP1AUX_lab_regs_upd; LTTP1AUX_fp_upd_simps]) THEN
  TRY(FIRST_X_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
                            lhs(concl th) = `lab_state_fp_regs (s1:(A,D,FFI)lab_state)`
                         then SUBST_ALL_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_asm_failed_upd] THEN ASM_REWRITE_TAC[] THEN
  FS[]);;
let LTTP1AUX_rmw_consts = prove
 (`!n (a:A word) s.
     asm_state_mem (SND (read_mem_word a n s)) = asm_state_mem s /\
     asm_state_mem_domain (SND (read_mem_word a n s)) = asm_state_mem_domain s /\
     (asm_state_be (SND (read_mem_word a n s)) <=> asm_state_be s) /\
     asm_state_regs (SND (read_mem_word a n s)) = asm_state_regs s /\
     asm_state_fp_regs (SND (read_mem_word a n s)) = asm_state_fp_regs s /\
     asm_state_pc (SND (read_mem_word a n s)) = asm_state_pc s /\
     asm_state_lr (SND (read_mem_word a n s)) = asm_state_lr s /\
     asm_state_align (SND (read_mem_word a n s)) = asm_state_align s`,
  INDUCT_TAC THEN REWRITE_TAC[read_mem_word_def; pair_CASE_def] THEN
  ASM_REWRITE_TAC[asm_assert_def] THEN SIMP[]);;

let LTTP1AUX_rmw_SUC = prove
 (`!n (a:A word) s.
     FST (read_mem_word a (SUC n) s) =
       word_or (word_shl (FST (read_mem_word (if asm_state_be s then word_sub a (word 1)
                                              else word_add a (word 1)) n s)) 8)
               (word_zx (asm_state_mem s a)) /\
     (asm_state_failed (SND (read_mem_word a (SUC n) s)) <=>
      ~(a IN asm_state_mem_domain s) \/
      asm_state_failed (SND (read_mem_word (if asm_state_be s then word_sub a (word 1)
                                            else word_add a (word 1)) n s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[read_mem_word_def; pair_CASE_def] THEN
  REWRITE_TAC[asm_read_mem_def; LTTP1AUX_rmw_consts; asm_assert_def] THEN SIMP[] THEN
  MESON_TAC[]);;

let LTTP1AUX_DIV_MOD_8 = prove
 (`!i. 8 <= i ==> (i - 8) MOD 8 = i MOD 8 /\ SUC ((i - 8) DIV 8) = i DIV 8`,
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2] THEN
  SUBGOAL_THEN `8 + m = 1 * 8 + m` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;

let LTTP1AUX_rmw_bit = prove
 (`!n (a:A word) s i.
     bit i (FST (read_mem_word a n s)) <=>
     i < 8 * n /\ i < dimindex(:A) /\
     bit (i MOD 8)
       (asm_state_mem s
          (ITER (i DIV 8) (\b. if asm_state_be s then word_sub b (word 1)
                               else word_add b (word 1)) a))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[read_mem_word_def; BIT_WORD_0; MULT_CLAUSES; LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LTTP1AUX_rmw_SUC; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX] THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN
  ASM_CASES_TAC `i < 8` THENL
   [SUBGOAL_THEN `i < 8 * SUC n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; ITER; ARITH_RULE `i < 8 ==> ~(8 <= i)`] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP1AUX_DIV_MOD_8 o
    MATCH_MP (ARITH_RULE `~(i < 8) ==> 8 <= i`)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[ITER_ALT] THEN
  SUBGOAL_THEN `8 <= i /\ (i - 8 < 8 * n <=> i < 8 * SUC n) /\
                (i < dimindex(:A) ==> i - 8 < dimindex(:A))` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `i < dimindex(:A)` THEN
  ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8]);;
let LTTP1AUX_EXISTS_LT_SUC = prove
 (`!P n. (?k. k < SUC n /\ P k) <=> P 0 \/ (?k. k < n /\ P (SUC k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN REWRITE_TAC[LT_SUC] THEN MESON_TAC[];
    STRIP_TAC THENL [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LT_0];
                     EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[LT_SUC]]]);;

let LTTP1AUX_rmw_failed = prove
 (`!n (a:A word) s.
     asm_state_failed (SND (read_mem_word a n s)) <=>
     asm_state_failed s \/
     ?k. k < n /\
         ~(ITER k (\b. if asm_state_be s then word_sub b (word 1)
                       else word_add b (word 1)) a IN asm_state_mem_domain s)`,
  INDUCT_TAC THENL [REWRITE_TAC[read_mem_word_def; LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LTTP1AUX_rmw_SUC; LTTP1AUX_EXISTS_LT_SUC; ITER; ITER_ALT] THEN
  MESON_TAC[]);;
let LTTP1AUX_wmw_consts = prove
 (`!n (a:A word) w s.
     asm_state_mem_domain (write_mem_word a n w s) = asm_state_mem_domain s /\
     (asm_state_be (write_mem_word a n w s) <=> asm_state_be s) /\
     asm_state_regs (write_mem_word a n w s) = asm_state_regs s /\
     asm_state_fp_regs (write_mem_word a n w s) = asm_state_fp_regs s /\
     asm_state_pc (write_mem_word a n w s) = asm_state_pc s /\
     asm_state_lr (write_mem_word a n w s) = asm_state_lr s /\
     asm_state_align (write_mem_word a n w s) = asm_state_align s`,
  INDUCT_TAC THEN REWRITE_TAC[write_mem_word_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[asm_assert_def; asm_upd_mem_def] THEN SIMP[]);;

let LTTP1AUX_wmw_failed = prove
 (`!n (a:A word) w s.
     asm_state_failed (write_mem_word a n w s) <=>
     asm_state_failed s \/
     ?k. k < n /\
         ~(ITER k (\b. if asm_state_be s then word_sub b (word 1)
                       else word_add b (word 1)) a IN asm_state_mem_domain s)`,
  INDUCT_TAC THENL [REWRITE_TAC[write_mem_word_def; LT]; ALL_TAC] THEN
  REWRITE_TAC[write_mem_word_def; LET_DEF; LET_END_DEF; LTTP1AUX_EXISTS_LT_SUC] THEN
  REWRITE_TAC[asm_assert_def; asm_upd_mem_def; (record_info "asm_state").ri_accfupds;
              K_THM; LTTP1AUX_wmw_consts] THEN
  ASM_REWRITE_TAC[ITER; ITER_ALT] THEN MESON_TAC[]);;

let LTTP1AUX_wmw_mem_out = prove
 (`!n (a:A word) w s x.
     (!k. k < n ==> ~(x = ITER k (\b. if asm_state_be s then word_sub b (word 1)
                                     else word_add b (word 1)) a))
     ==> asm_state_mem (write_mem_word a n w s) x = asm_state_mem s x`,
  INDUCT_TAC THENL [REWRITE_TAC[write_mem_word_def]; ALL_TAC] THEN
  REWRITE_TAC[write_mem_word_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[asm_assert_def; asm_upd_mem_def; (record_info "asm_state").ri_accfupds;
              K_THM; APPLY_UPDATE_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[LT_0; ITER]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LTTP1AUX_wmw_consts] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN ASM_REWRITE_TAC[LT_SUC; ITER_ALT]);;

let LTTP1AUX_wmw_mem_in = prove
 (`!n (a:A word) w s k.
     k < n /\
     (!j. j < k ==> ~(ITER k (\b. if asm_state_be s then word_sub b (word 1)
                                 else word_add b (word 1)) a =
                      ITER j (\b. if asm_state_be s then word_sub b (word 1)
                                 else word_add b (word 1)) a))
     ==> asm_state_mem (write_mem_word a n w s)
           (ITER k (\b. if asm_state_be s then word_sub b (word 1)
                        else word_add b (word 1)) a) =
         word_zx (word_ushr w (8 * k))`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REWRITE_TAC[write_mem_word_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[asm_assert_def; asm_upd_mem_def; (record_info "asm_state").ri_accfupds;
              K_THM; APPLY_UPDATE_THM] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THENL
   [REWRITE_TAC[ITER; MULT_CLAUSES; WORD_USHR_ZERO]; ALL_TAC] THEN
  REWRITE_TAC[LT_SUC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((a:A word) = ITER (SUC n') (\b. if asm_state_be (s:(A)asm_state)
                    then word_sub b (word 1) else word_add b (word 1)) a)`
    (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; ITER] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ITER_ALT] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`if asm_state_be (s:(A)asm_state) then word_sub (a:A word) (word 1)
                                 else word_add a (word 1)`; `word_ushr (w:A word) 8`;
                                `s:(A)asm_state`; `n':num`]) THEN
  ASM_REWRITE_TAC[WORD_USHR_COMPOSE; ARITH_RULE `8 + 8 * k = 8 * SUC k`] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN ASM_REWRITE_TAC[LT_SUC; ITER_ALT]);;
let LTTP1AUX_ITER_step = prove
 (`!k (a:A word) be.
     ITER k (\b. if be then word_sub b (word 1) else word_add b (word 1)) a =
     if be then word_sub a (word k) else word_add a (word k)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[WORD_SUB_0; WORD_ADD_0]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let LTTP1AUX_rmw_value = prove
 (`!n (st:A word) s (V:A word).
     (!k. k < n ==> asm_state_mem s
                      (ITER k (\b. if asm_state_be s then word_sub b (word 1)
                                   else word_add b (word 1)) st) =
                    word_zx (word_ushr V (8 * k)))
     ==> !i. bit i (FST (read_mem_word st n s)) <=> i < 8 * n /\ bit i V`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[LTTP1AUX_rmw_bit] THEN
  ASM_CASES_TAC `i < 8 * n` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i DIV 8 < n` ASSUME_TAC THENL
   [UNDISCH_TAC `i < 8 * n` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BIT_WORD_ZX; BIT_WORD_USHR; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `i MOD 8 + 8 * i DIV 8 = i DIV 8 * 8 + i MOD 8`] THEN
  MP_TAC(SPECL [`i:num`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[BIT_GUARD]);;
let LTTP1AUX_val_add_mod2 = prove
 (`!(w:A word) m e.
     e <= dimindex(:A)
     ==> val (word_add w (word m)) MOD 2 EXP e = (val w + m) MOD 2 EXP e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `e <= d ==> MIN d e = e`] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN ASM_SIMP_TAC[ARITH_RULE `e <= d ==> MIN d e = e`]);;

let LTTP1AUX_byte_layout = prove
 (`!(w0:A word) m be.
     good_dimindex(:A) /\ alignment_aligned (LOG2 (dimindex(:A) DIV 8)) w0 /\
     m < dimindex(:A) DIV 8
     ==> byte_align (word_add w0 (word m)) = w0 /\
         byte_index (word_add w0 (word m)) be =
         (if be then 8 * ((dimindex(:A) DIV 8 - 1) - m) else 8 * m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[(RAND_CONV NUM_REDUCE_CONV THENC LOG2_CONV) `LOG2 (32 DIV 8)`;
              (RAND_CONV NUM_REDUCE_CONV THENC LOG2_CONV) `LOG2 (64 DIV 8)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LTTP1AUX_byte_align_32; LTTP1AUX_byte_align_64; byte_index_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC align_add_aligned THEN ASM_REWRITE_TAC[VAL_WORD] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `m < 4 ==> m < 4294967296`; ARITH_RULE `m < 8 ==> m < 18446744073709551616`] THEN
     ASM_ARITH_TAC;
     ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[aligned_w2n]) THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  MP_TAC(ISPECL [`w0:A word`; `m:num`; `2`] LTTP1AUX_val_add_mod2) THEN
  MP_TAC(ISPECL [`w0:A word`; `m:num`; `3`] LTTP1AUX_val_add_mod2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[ADD_CLAUSES; MOD_MOD_REFL] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;
let LTTP1AUX_be_addr = prove
 (`!(w:A word) d k be.
     k < d
     ==> ITER k (\b. if be then word_sub b (word 1) else word_add b (word 1))
           (if be then word_add w (word (d - 1)) else w) =
         word_add w (word (if be then (d - 1) - k else k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LTTP1AUX_ITER_step] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `d - 1 = ((d - 1) - k) + k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `((a + k) - k) = a`; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let LTTP1AUX_good_dimindex_cases = prove
 (`good_dimindex(:A) ==>
   (dimindex(:A) = 32 /\ dimindex(:A) DIV 8 = 4 /\ LOG2 (dimindex(:A) DIV 8) = 2) \/
   (dimindex(:A) = 64 /\ dimindex(:A) DIV 8 = 8 /\ LOG2 (dimindex(:A) DIV 8) = 3)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[(RAND_CONV NUM_REDUCE_CONV THENC LOG2_CONV) `LOG2 (32 DIV 8)`;
              (RAND_CONV NUM_REDUCE_CONV THENC LOG2_CONV) `LOG2 (64 DIV 8)`] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let LTTP1AUX_word_bytes = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) w.
     good_dimindex(:A) /\ alignment_aligned (LOG2 (dimindex(:A) DIV 8)) w /\
     w IN lab_state_mem_domain s1 /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a))
     ==> ?V. word_loc_val p labs (lab_state_mem s1 w) = SOME V /\
             !m. m < dimindex(:A) DIV 8
                 ==> word_add w (word m) IN asm_state_mem_domain t1 /\
                     asm_state_mem t1 (word_add w (word m)) =
                     word_zx (word_ushr V (if lab_state_be s1
                                           then 8 * ((dimindex(:A) DIV 8 - 1) - m)
                                           else 8 * m))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mem")))) THEN
  SUBGOAL_THEN `!m. m < dimindex(:A) DIV 8
                    ==> byte_align (word_add (w:A word) (word m)) = w /\
                        byte_index (word_add w (word m)) (lab_state_be (s1:(A,D,FFI)lab_state)) =
                        (if lab_state_be s1 then 8 * ((dimindex(:A) DIV 8 - 1) - m) else 8 * m)`
    (LABEL_TAC "lay") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LTTP1AUX_byte_layout THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP LTTP1AUX_good_dimindex_cases) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `byte_align (w:A word) = w` ASSUME_TAC THENL
   [USE_THEN "lay" (MP_TAC o C MP (ASSUME `0 < dimindex(:A) DIV 8`) o SPEC `0`) THEN
    REWRITE_TAC[WORD_ADD_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `byte_align (w:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "mem" (MP_TAC o C MP (ASSUME
    `byte_align (w:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`) o
    SPEC `w:A word`) THEN
  ASM_REWRITE_TAC[word_loc_val_byte_def] THEN
  CASES_ON `word_loc_val (p:A word) labs (lab_state_mem (s1:(A,D,FFI)lab_state) w)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_TAC THEN EXISTS_TAC `a:A word` THEN REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  USE_THEN "lay" (MP_TAC o C MP (ASSUME `m < dimindex(:A) DIV 8`) o SPEC `m:num`) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `byte_align (word_add (w:A word) (word m)) IN
                lab_state_mem_domain (s1:(A,D,FFI)lab_state)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "mem" (MP_TAC o C MP (ASSUME `byte_align (word_add (w:A word) (word m)) IN
                lab_state_mem_domain (s1:(A,D,FFI)lab_state)`) o
    SPEC `word_add (w:A word) (word m)`) THEN
  ASM_REWRITE_TAC[word_loc_val_byte_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; get_byte_def] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
let LTTP1AUX_inst_load = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) r a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     lab_state_be s1 = asm_state_be t1 /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
     ~lab_state_failed (lab_mem_load r a s1)
     ==> ~asm_state_failed (asm_mem_load (dimindex(:A) DIV 8) r a t1) /\
         asm_state_mem (asm_mem_load (dimindex(:A) DIV 8) r a t1) = asm_state_mem t1 /\
         asm_state_fp_regs (asm_mem_load (dimindex(:A) DIV 8) r a t1) = asm_state_fp_regs t1 /\
         (!r'. word_loc_val p labs (lab_state_regs (lab_mem_load r a s1) r') =
               SOME (asm_state_regs (asm_mem_load (dimindex(:A) DIV 8) r a t1) r'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regs") (CONJUNCTS_THEN2 (LABEL_TAC "mem")
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `a:(A)addr` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "lab_mem_load")) (concl th))) THEN
  REWRITE_TAC[lab_mem_load_def; lab_addr_def] THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) a0` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd; DE_MORGAN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  USE_THEN "regs" (MP_TAC o SPEC `a0:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) a0 = wl_Word a`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `w = word_add (a:A word) a1` THEN
  SUBGOAL_THEN `alignment_aligned (LOG2 (dimindex(:A) DIV 8)) (w:A word)` ASSUME_TAC THENL
   [UNDISCH_TAC `val (w:A word) MOD (dimindex(:A) DIV 8) = 0` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP1AUX_good_dimindex_cases) THEN
    ASM_REWRITE_TAC[aligned_w2n] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`; `t1:(A)asm_state`;
                `w:A word`] LTTP1AUX_word_bytes) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A word` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bytes"))) THEN
  REWRITE_TAC[asm_mem_load_def; asm_addr_def; read_reg_def; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = dimindex(:A) DIV 8` THEN
  ABBREV_TAC `st = if asm_state_be (t1:(A)asm_state) then word_add (w:A word) (word (d - 1))
                   else w` THEN
  SUBGOAL_THEN `!k. k < d ==> ITER k (\b. if asm_state_be (t1:(A)asm_state)
                                          then word_sub b (word 1) else word_add b (word 1)) st =
                              word_add (w:A word) (word (if asm_state_be t1 then (d - 1) - k else k)) /\
                              (if asm_state_be t1 then (d - 1) - k else k) < d`
    (LABEL_TAC "iter") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "st" THEN ASM_SIMP_TAC[LTTP1AUX_be_addr] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `8 * d = dimindex(:A)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    FIRST_ASSUM(DISJ_CASES_THEN (fun th -> REWRITE_TAC[th]) o
                MATCH_MP LTTP1AUX_good_dimindex_cases) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `FST (read_mem_word (st:A word) d t1) = V` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`d:num`; `st:A word`; `t1:(A)asm_state`; `V:A word`] LTTP1AUX_rmw_value) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < d`) o SPEC `k:num`) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
      USE_THEN "bytes" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k) < d`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k`) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~asm_state_failed (SND (read_mem_word (st:A word) d t1))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LTTP1AUX_rmw_failed; NOT_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `k < d` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < d`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    USE_THEN "bytes" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k) < d`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LTTP1AUX_asm_failed_upd; LTTP1AUX_lab_regs_upd; LTTP1AUX_rmw_consts] THEN
  REWRITE_TAC[asm_assert_def; asm_upd_reg_def; (record_info "asm_state").ri_accfupds; K_THM;
              LTTP1AUX_rmw_consts] THEN
  MATCH_MP_TAC LTTP1AUX_word_loc_val_upd THEN ASM_REWRITE_TAC[]);;
let LTTP1AUX_byte_align_decomp = prove
 (`good_dimindex(:A)
   ==> !x:A word. x = word_add (byte_align x) (word (val x MOD (dimindex(:A) DIV 8))) /\
                  val x MOD (dimindex(:A) DIV 8) < dimindex(:A) DIV 8`,
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP LTTP1AUX_good_dimindex_cases th)) THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  ASM_SIMP_TAC[byte_align_32_eq; byte_align_64_eq; MOD_LT_EQ; ARITH_EQ]);;

let LTTP1AUX_word_add_inj = prove
 (`!(w:A word) m1 m2.
     m1 < dimindex(:A) DIV 8 /\ m2 < dimindex(:A) DIV 8 /\
     word_add w (word m1) = word_add w (word m2)
     ==> m1 = m2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_ADD_LCANCEL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:A word->num`) THEN REWRITE_TAC[VAL_WORD] THEN
  SUBGOAL_THEN `m1 < 2 EXP dimindex(:A) /\ m2 < 2 EXP dimindex(:A)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `dimindex(:A)` LT_POW2_REFL) THEN
    MP_TAC(SPECL [`dimindex(:A)`; `8`] DIV_LE) THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;
let LTTP1AUX_inst_store = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) r a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     lab_state_be s1 = asm_state_be t1 /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
     ~lab_state_failed (lab_mem_store r a s1)
     ==> ~asm_state_failed (asm_mem_store (dimindex(:A) DIV 8) r a t1) /\
         (!x. ~(x IN lab_state_mem_domain s1)
              ==> asm_state_mem (asm_mem_store (dimindex(:A) DIV 8) r a t1) x =
                  asm_state_mem t1 x) /\
         asm_state_regs (asm_mem_store (dimindex(:A) DIV 8) r a t1) = asm_state_regs t1 /\
         asm_state_fp_regs (asm_mem_store (dimindex(:A) DIV 8) r a t1) = asm_state_fp_regs t1 /\
         (!x. byte_align x IN lab_state_mem_domain s1
              ==> word_loc_val_byte p labs (lab_state_mem (lab_mem_store r a s1)) x
                    (lab_state_be s1) =
                  SOME (asm_state_mem (asm_mem_store (dimindex(:A) DIV 8) r a t1) x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regs") (CONJUNCTS_THEN2 (LABEL_TAC "mem")
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `a:(A)addr` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "lab_mem_store")) (concl th))) THEN
  REWRITE_TAC[lab_mem_store_def; lab_addr_def] THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) a0` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LTTP1AUX_lab_regs_upd; DE_MORGAN_THM; lab_upd_mem_def; lab_assert_def;
              (record_info "lab_state").ri_accfupds; K_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  USE_THEN "regs" (MP_TAC o SPEC `a0:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) a0 = wl_Word a`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `w = word_add (a:A word) a1` THEN
  SUBGOAL_THEN `alignment_aligned (LOG2 (dimindex(:A) DIV 8)) (w:A word)` ASSUME_TAC THENL
   [UNDISCH_TAC `val (w:A word) MOD (dimindex(:A) DIV 8) = 0` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP1AUX_good_dimindex_cases) THEN
    ASM_REWRITE_TAC[aligned_w2n] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`; `t1:(A)asm_state`;
                `w:A word`] LTTP1AUX_word_bytes) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:A word` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bytes"))) THEN
  REWRITE_TAC[asm_mem_store_def; asm_addr_def; read_reg_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = dimindex(:A) DIV 8` THEN
  ABBREV_TAC `st = if asm_state_be (t1:(A)asm_state) then word_add (w:A word) (word (d - 1))
                   else w` THEN
  SUBGOAL_THEN `!k. k < d ==> ITER k (\b. if asm_state_be (t1:(A)asm_state)
                                          then word_sub b (word 1) else word_add b (word 1)) st =
                              word_add (w:A word) (word (if asm_state_be t1 then (d - 1) - k else k)) /\
                              (if asm_state_be t1 then (d - 1) - k else k) < d`
    (LABEL_TAC "iter") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "st" THEN ASM_SIMP_TAC[LTTP1AUX_be_addr] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < d ==> byte_align (word_add (w:A word) (word m)) = w /\
                              byte_index (word_add w (word m)) (asm_state_be (t1:(A)asm_state)) =
                              (if asm_state_be t1 then 8 * ((d - 1) - m) else 8 * m) /\
                              word_add w (word m) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`
    (LABEL_TAC "lay") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w:A word`; `m:num`; `asm_state_be (t1:(A)asm_state)`] LTTP1AUX_byte_layout) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "mem" (MP_TAC o SPEC `word_add (w:A word) (word m)`) THEN
    REWRITE_TAC[ASSUME `byte_align (word_add (w:A word) (word m)) = w`] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k j. k < d /\ j < k
       ==> ~(ITER k (\b. if asm_state_be (t1:(A)asm_state)
                         then word_sub b (word 1) else word_add b (word 1)) st =
             ITER j (\b. if asm_state_be (t1:(A)asm_state)
                         then word_sub b (word 1) else word_add b (word 1)) (st:A word))`
    (LABEL_TAC "dist") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `j < d` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < d`) o SPEC `k:num`) THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `j < d`) o SPEC `j:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`w:A word`; `if asm_state_be (t1:(A)asm_state) then d - 1 - k else k`;
                   `if asm_state_be (t1:(A)asm_state) then d - 1 - j else j`]
           LTTP1AUX_word_add_inj) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[asm_assert_def; (record_info "asm_state").ri_accfupds; K_THM;
              LTTP1AUX_wmw_consts; LTTP1AUX_wmw_failed] THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_CASES_TAC `k < d` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < d`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    USE_THEN "bytes" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k) < d`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k`) THEN
    SIMP_TAC[];
    X_GEN_TAC `x:A word` THEN DISCH_TAC THEN MATCH_MP_TAC LTTP1AUX_wmw_mem_out THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < d`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    USE_THEN "lay" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k) < d`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:A word` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:A word` (MATCH_MP LTTP1AUX_byte_align_decomp (ASSUME `good_dimindex(:A)`))) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `mx = val (x:A word) MOD d` THEN STRIP_TAC THEN
  ASM_CASES_TAC `byte_align (x:A word) = w` THENL
   [REWRITE_TAC[word_loc_val_byte_def; APPLY_UPDATE_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "regs" (fun th -> REWRITE_TAC[SPEC `r:num` th]) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; get_byte_def] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `x:A word`
                            then SUBST1_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "lay" (MP_TAC o C MP (ASSUME `mx < d`) o SPEC `mx:num`) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    SUBGOAL_THEN `(if asm_state_be (t1:(A)asm_state) then d - 1 - mx else mx) < d /\
                  word_add (w:A word) (word mx) =
                  ITER (if asm_state_be t1 then d - 1 - mx else mx)
                    (\b. if asm_state_be t1 then word_sub b (word 1) else word_add b (word 1)) st`
      STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(if asm_state_be (t1:(A)asm_state) then d - 1 - mx else mx) < d`
        ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "iter" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then d - 1 - mx else mx) < d`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then d - 1 - mx else mx`) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `word_add (w:A word) (word mx)`)) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `word_zx (word_ushr (asm_state_regs (t1:(A)asm_state) r)
                  (8 * (if asm_state_be t1 then d - 1 - mx else mx))):byte` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LTTP1AUX_wmw_mem_in THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "dist" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:A word) = byte_align x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[word_loc_val_byte_def; APPLY_UPDATE_THM] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `asm_state_mem (write_mem_word (st:A word) d (asm_state_regs t1 r) t1) x =
                asm_state_mem (t1:(A)asm_state) x` SUBST1_TAC THENL
   [MATCH_MP_TAC LTTP1AUX_wmw_mem_out THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < d`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    USE_THEN "lay" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k) < d`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then d - 1 - k else k`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `~(byte_align (x:A word) = w)` THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "mem" (MP_TAC o SPEC `x:A word`) THEN
  REWRITE_TAC[ASSUME `byte_align (x:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
              word_loc_val_byte_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;
let LTTP1AUX_word_or_shl_0 = prove
 (`!(x:A word). word_or (word_shl (word 0) 8) x = x`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_0] THEN
  MESON_TAC[]);;
let LTTP1AUX_inst_load8 = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) r a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     lab_state_be s1 = asm_state_be t1 /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
     ~lab_state_failed (mem_load_byte r a s1)
     ==> ~asm_state_failed (asm_mem_load 1 r a t1) /\
         asm_state_mem (asm_mem_load 1 r a t1) = asm_state_mem t1 /\
         asm_state_fp_regs (asm_mem_load 1 r a t1) = asm_state_fp_regs t1 /\
         (!r'. word_loc_val p labs (lab_state_regs (mem_load_byte r a s1) r') =
               SOME (asm_state_regs (asm_mem_load 1 r a t1) r'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regs") (CONJUNCTS_THEN2 (LABEL_TAC "mem")
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `a:(A)addr` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "mem_load_byte")) (concl th))) THEN
  REWRITE_TAC[mem_load_byte_def; lab_addr_def] THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) a0` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  USE_THEN "regs" (MP_TAC o SPEC `a0:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) a0 = wl_Word a`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `w = word_add (a:A word) a1` THEN
  REWRITE_TAC[mem_load_byte_aux_def] THEN
  CASES_ON `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  DISCH_TAC THEN
  USE_THEN "mem" (MP_TAC o SPEC `w:A word`) THEN
  REWRITE_TAC[ASSUME `byte_align (w:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
              word_loc_val_byte_def;
              ASSUME `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w) = wl_Word a'`;
              word_loc_val_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN
  REWRITE_TAC[asm_mem_load_def; asm_addr_def; read_reg_def; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0; COND_ID; num_CONV `1`; LTTP1AUX_rmw_SUC; read_mem_word_def;
              LTTP1AUX_rmw_consts] THEN
  REWRITE_TAC[GSYM (num_CONV `1`); LOG2_CONV `LOG2 1`] THEN
  REWRITE_TAC[pair_CASE_def; FST; SND; asm_read_mem_def; LTTP1AUX_word_or_shl_0; aligned_0] THEN
  REWRITE_TAC[asm_assert_def; asm_upd_reg_def; (record_info "asm_state").ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LTTP1AUX_word_loc_val_upd THEN ASM_REWRITE_TAC[word_loc_val_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `lab_state_be (s1:(A,D,FFI)lab_state) <=>
                                      asm_state_be (t1:(A)asm_state)`]) THEN
  ASM_REWRITE_TAC[]);;
let LTTP1AUX_get_byte_set_byte_diff = prove
 (`!(a:A word) a' b w be.
     good_dimindex(:A) /\ ~(a = a') /\ byte_align a = byte_align a'
     ==> get_byte a (set_byte a' b w be) be = get_byte a w be`,
  MESON_TAC[get_byte_set_byte_diff]);;
let LTTP1AUX_inst_store8 = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) r a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     lab_state_be s1 = asm_state_be t1 /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
     ~lab_state_failed (mem_store_byte r a s1)
     ==> ~asm_state_failed (asm_mem_store 1 r a t1) /\
         (!x. ~(x IN lab_state_mem_domain s1)
              ==> asm_state_mem (asm_mem_store 1 r a t1) x = asm_state_mem t1 x) /\
         asm_state_regs (asm_mem_store 1 r a t1) = asm_state_regs t1 /\
         asm_state_fp_regs (asm_mem_store 1 r a t1) = asm_state_fp_regs t1 /\
         lab_state_regs (mem_store_byte r a s1) = lab_state_regs s1 /\
         (!x. byte_align x IN lab_state_mem_domain s1
              ==> word_loc_val_byte p labs (lab_state_mem (mem_store_byte r a s1)) x
                    (lab_state_be s1) =
                  SOME (asm_state_mem (asm_mem_store 1 r a t1) x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regs") (CONJUNCTS_THEN2 (LABEL_TAC "mem")
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `a:(A)addr` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "mem_store_byte")) (concl th))) THEN
  REWRITE_TAC[mem_store_byte_def; lab_addr_def] THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) a0` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  USE_THEN "regs" (MP_TAC o SPEC `a0:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) a0 = wl_Word a`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `w = word_add (a:A word) a1` THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) r` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  USE_THEN "regs" (MP_TAC o SPEC `r:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) r = wl_Word a'`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  REWRITE_TAC[mem_store_byte_aux_def] THEN
  CASES_ON `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LTTP1AUX_lab_regs_upd; (record_info "lab_state").ri_accfupds; K_THM] THEN
  DISCH_TAC THEN
  USE_THEN "mem" (MP_TAC o SPEC `w:A word`) THEN
  REWRITE_TAC[ASSUME `byte_align (w:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[asm_mem_store_def; asm_addr_def; read_reg_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0; COND_ID; num_CONV `1`; write_mem_word_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[GSYM (num_CONV `1`); LOG2_CONV `LOG2 1`; aligned_0] THEN
  REWRITE_TAC[asm_assert_def; asm_upd_mem_def; (record_info "asm_state").ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A word` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((w:A word) = x)` (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:A word` THEN DISCH_TAC THEN
  REWRITE_TAC[word_loc_val_byte_def; APPLY_UPDATE_THM] THEN
  ASM_CASES_TAC `byte_align (w:A word) = byte_align x` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_loc_val_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[good_dimindex_get_byte_set_byte];
      ALL_TAC] THEN
    MP_TAC(SPECL [`x:A word`; `w:A word`; `word_zx (a':A word):byte`; `a'':A word`;
                  `asm_state_be (t1:(A)asm_state)`] LTTP1AUX_get_byte_set_byte_diff) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "mem" (MP_TAC o SPEC `x:A word`) THEN
    REWRITE_TAC[ASSUME `byte_align (x:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
                word_loc_val_byte_def] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      lhs(concl th) = `byte_align (w:A word)` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    ASM_REWRITE_TAC[word_loc_val_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:A word) = x)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "mem" (MP_TAC o SPEC `x:A word`) THEN
  REWRITE_TAC[ASSUME `byte_align (x:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
              word_loc_val_byte_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;
let LTTP1AUX_get_set_byte = prove
 (`!(x:A word) a b v be.
     good_dimindex(:A) /\ byte_align x = byte_align a
     ==> get_byte x (set_byte a b v be) be = if x = a then b else get_byte x v be`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[good_dimindex_get_byte_set_byte];
    MATCH_MP_TAC LTTP1AUX_get_byte_set_byte_diff THEN ASM_REWRITE_TAC[]]);;

let LTTP1AUX_byte_align_add4 = prove
 (`!(w:A word) j.
     good_dimindex(:A) /\ alignment_aligned 2 w /\ j < 4
     ==> byte_align (word_add w (word j)) = byte_align w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC STRIP_ASSUME_TAC) THENL
   [ASM_SIMP_TAC[LTTP1AUX_byte_align_32] THEN
    SUBGOAL_THEN `align 2 (w:A word) = w` SUBST1_TAC THENL
     [ASM_MESON_TAC[aligned_def]; ALL_TAC] THEN
    MATCH_MP_TAC align_add_aligned THEN ASM_REWRITE_TAC[VAL_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `j < 4 ==> j < 4294967296`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LTTP1AUX_byte_align_64; align_w2n] THEN AP_TERM_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[aligned_w2n]) THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `j < 4 ==> j < 18446744073709551616`] THEN
  MP_TAC(ISPEC `w:A word` VAL_BOUND) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val (w:A word) MOD 8 + j < 8` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (w:A word)`; `4`; `2`] MOD_MOD) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPEC `val (w:A word)` MOD8_CASES) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (w:A word) + j < 18446744073709551616` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (w:A word)`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    SUBGOAL_THEN `val (w:A word) DIV 8 < 2305843009213693952` MP_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`val (w:A word)`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [CONJUNCT1 th]) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES]);;
let LTTP1AUX_wob32_bit = prove
 (`!be (b0:byte) b1 b2 b3 i.
     bit i (word_of_bytes be (word 0:int32) [b0;b1;b2;b3]) <=>
     i < 32 /\ bit (i MOD 8) (EL (if be then 3 - i DIV 8 else i DIV 8) [b0;b1;b2;b3])`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < 32` THENL
   [ALL_TAC; ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_32; ARITH_RULE `~(i < 32) ==> 32 <= i`]] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  REWRITE_TAC[WORDSAUX_word_of_bytes_32] THEN
  BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_32; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL; HD; TL; num_CONV `3`; num_CONV `2`;
    num_CONV `1`] THEN
  SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8; ARITH]);;
let LTTP1AUX_get_byte_32_zx = prove
 (`!(V:A word) be j.
     good_dimindex(:A) /\ j < 4
     ==> get_byte (word j:int32) (word_zx V) be =
         word_zx (word_ushr V (8 * (if be then 3 - j else j)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`j:num`,`j:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[WORDSAUX_get_byte_32] THEN BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_USHR; DIMINDEX_8; DIMINDEX_32] THEN
  REWRITE_TAC[WORD_USHR_ZERO; ADD_CLAUSES] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP1AUX_good_dimindex_cases) THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_USHR; DIMINDEX_32] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 8 ==> i + 24 < 32 /\ i + 16 < 32 /\ i + 8 < 32 /\ i < 32`]);;
let LTTP1AUX_inst_load32 = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) r a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     lab_state_be s1 = asm_state_be t1 /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
     ~lab_state_failed (mem_load32 r a s1)
     ==> ~asm_state_failed (asm_mem_load 4 r a t1) /\
         asm_state_mem (asm_mem_load 4 r a t1) = asm_state_mem t1 /\
         asm_state_fp_regs (asm_mem_load 4 r a t1) = asm_state_fp_regs t1 /\
         (!r'. word_loc_val p labs (lab_state_regs (mem_load32 r a s1) r') =
               SOME (asm_state_regs (asm_mem_load 4 r a t1) r'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regs") (CONJUNCTS_THEN2 (LABEL_TAC "mem")
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `a:(A)addr` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "mem_load32")) (concl th))) THEN
  REWRITE_TAC[mem_load32_def; lab_addr_def] THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) a0` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  USE_THEN "regs" (MP_TAC o SPEC `a0:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) a0 = wl_Word a`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `w = word_add (a:A word) a1` THEN
  REWRITE_TAC[mem_load_32_def] THEN
  ASM_CASES_TAC `alignment_aligned 2 (w:A word)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  CASES_ON `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!j. j < 4 ==> word_add (w:A word) (word j) IN asm_state_mem_domain t1 /\
                              asm_state_mem t1 (word_add w (word j)) =
                              get_byte (word_add w (word j)) a' (asm_state_be t1)`
    (LABEL_TAC "bytes") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`w:A word`; `j:num`] LTTP1AUX_byte_align_add4) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "mem" (MP_TAC o SPEC `word_add (w:A word) (word j)`) THEN
    REWRITE_TAC[ASSUME `byte_align (word_add (w:A word) (word j)) = byte_align w`;
                ASSUME `byte_align (w:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
                word_loc_val_byte_def;
                ASSUME `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w) = wl_Word a'`;
                word_loc_val_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[asm_mem_load_def; asm_addr_def; read_reg_def; LET_DEF; LET_END_DEF;
              pair_CASE_def] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LOG2_CONV `LOG2 4`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `st = if asm_state_be (t1:(A)asm_state) then word_add (w:A word) (word 3) else w` THEN
  SUBGOAL_THEN `!k. k < 4 ==> ITER k (\b. if asm_state_be (t1:(A)asm_state)
                                          then word_sub b (word 1) else word_add b (word 1)) st =
                              word_add (w:A word) (word (if asm_state_be t1 then 3 - k else k)) /\
                              (if asm_state_be t1 then 3 - k else k) < 4`
    (LABEL_TAC "iter") THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "st" THEN
    MP_TAC(SPECL [`w:A word`; `4`; `k:num`; `asm_state_be (t1:(A)asm_state)`]
           LTTP1AUX_be_addr) THEN
    REWRITE_TAC[ASSUME `k < 4`] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~asm_state_failed (SND (read_mem_word (st:A word) 4 t1))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LTTP1AUX_rmw_failed; NOT_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `k < 4` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < 4`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    USE_THEN "bytes" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then 3 - k else k) < 4`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then 3 - k else k`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[asm_assert_def; asm_upd_reg_def; (record_info "asm_state").ri_accfupds; K_THM;
              LTTP1AUX_rmw_consts] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LTTP1AUX_word_loc_val_upd THEN ASM_REWRITE_TAC[word_loc_val_def; option_INJ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; LTTP1AUX_wob32_bit; LTTP1AUX_rmw_bit] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[DIMINDEX_32] THEN
  ASM_CASES_TAC `i < 32` THEN ASM_REWRITE_TAC[ARITH_RULE `8 * 4 = 32`] THEN
  SUBGOAL_THEN `i DIV 8 < 4` ASSUME_TAC THENL
   [UNDISCH_TAC `i < 32` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "iter" (MP_TAC o C MP (ASSUME `i DIV 8 < 4`) o SPEC `i DIV 8`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  USE_THEN "bytes" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then 3 - i DIV 8 else i DIV 8) < 4`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then 3 - i DIV 8 else i DIV 8`) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN AP_TERM_TAC THEN
  UNDISCH_TAC `(if asm_state_be (t1:(A)asm_state) then 3 - i DIV 8 else i DIV 8) < 4` THEN
  SPEC_TAC(`if asm_state_be (t1:(A)asm_state) then 3 - i DIV 8 else i DIV 8`,`m:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[EL; HD; TL; num_CONV `3`; num_CONV `2`; num_CONV `1`; WORD_ADD_0]);;
let LTTP1AUX_word_add_eq4 = prove
 (`!(w:A word) i j.
     good_dimindex(:A) /\ i < 4 /\ j < 4
     ==> (word_add w (word i) = word_add w (word j) <=> i = j) /\
         (w = word_add w (word j) <=> j = 0) /\
         (word_add w (word j) = w <=> j = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < dimindex(:A) DIV 8 /\ j < dimindex(:A) DIV 8 /\ 0 < dimindex(:A) DIV 8`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP1AUX_good_dimindex_cases) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN EQ_TAC THEN SIMP_TAC[WORD_ADD_0] THENL
   [ASM_MESON_TAC[LTTP1AUX_word_add_inj];
    DISCH_TAC THEN MATCH_MP_TAC LTTP1AUX_word_add_inj THEN EXISTS_TAC `w:A word` THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC LTTP1AUX_word_add_inj THEN EXISTS_TAC `w:A word` THEN
    ASM_REWRITE_TAC[WORD_ADD_0]]);;
let LTTP1AUX_inst_store32 = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) r a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     lab_state_be s1 = asm_state_be t1 /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
     ~lab_state_failed (mem_store32 r a s1)
     ==> ~asm_state_failed (asm_mem_store 4 r a t1) /\
         (!x. ~(x IN lab_state_mem_domain s1)
              ==> asm_state_mem (asm_mem_store 4 r a t1) x = asm_state_mem t1 x) /\
         asm_state_regs (asm_mem_store 4 r a t1) = asm_state_regs t1 /\
         asm_state_fp_regs (asm_mem_store 4 r a t1) = asm_state_fp_regs t1 /\
         lab_state_regs (mem_store32 r a s1) = lab_state_regs s1 /\
         (!x. byte_align x IN lab_state_mem_domain s1
              ==> word_loc_val_byte p labs (lab_state_mem (mem_store32 r a s1)) x
                    (lab_state_be s1) =
                  SOME (asm_state_mem (asm_mem_store 4 r a t1) x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regs") (CONJUNCTS_THEN2 (LABEL_TAC "mem")
    STRIP_ASSUME_TAC)) THEN
  CASES_ON `a:(A)addr` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "mem_store32")) (concl th))) THEN
  REWRITE_TAC[mem_store32_def; lab_addr_def] THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) a0` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  USE_THEN "regs" (MP_TAC o SPEC `a0:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) a0 = wl_Word a`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `w = word_add (a:A word) a1` THEN
  CASES_ON `lab_state_regs (s1:(A,D,FFI)lab_state) r` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  USE_THEN "regs" (MP_TAC o SPEC `r:num`) THEN
  REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,D,FFI)lab_state) r = wl_Word a'`;
              word_loc_val_def; option_INJ] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  REWRITE_TAC[mem_store_32_def] THEN
  ASM_CASES_TAC `alignment_aligned 2 (w:A word)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  CASES_ON `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LTTP1AUX_lab_regs_upd; (record_info "lab_state").ri_accfupds; K_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!j. j < 4 ==> byte_align (word_add (w:A word) (word j)) = byte_align w /\
                              word_add w (word j) IN asm_state_mem_domain t1 /\
                              word_add w (word j) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state) /\
                              asm_state_mem t1 (word_add w (word j)) =
                              get_byte (word_add w (word j)) a'' (asm_state_be t1)`
    (LABEL_TAC "bytes") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`w:A word`; `j:num`] LTTP1AUX_byte_align_add4) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "mem" (MP_TAC o SPEC `word_add (w:A word) (word j)`) THEN
    REWRITE_TAC[ASSUME `byte_align (word_add (w:A word) (word j)) = byte_align w`;
                ASSUME `byte_align (w:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
                word_loc_val_byte_def;
                ASSUME `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w) = wl_Word a''`;
                word_loc_val_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[asm_mem_store_def; asm_addr_def; read_reg_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LOG2_CONV `LOG2 4`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `st = if asm_state_be (t1:(A)asm_state) then word_add (w:A word) (word 3) else w` THEN
  SUBGOAL_THEN `!k. k < 4 ==> ITER k (\b. if asm_state_be (t1:(A)asm_state)
                                          then word_sub b (word 1) else word_add b (word 1)) st =
                              word_add (w:A word) (word (if asm_state_be t1 then 3 - k else k)) /\
                              (if asm_state_be t1 then 3 - k else k) < 4`
    (LABEL_TAC "iter") THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "st" THEN
    MP_TAC(SPECL [`w:A word`; `4`; `k:num`; `asm_state_be (t1:(A)asm_state)`]
           LTTP1AUX_be_addr) THEN
    REWRITE_TAC[ASSUME `k < 4`] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i < 4 /\ j < 4 /\ word_add (w:A word) (word i) = word_add w (word j)
                      ==> i = j` (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LTTP1AUX_word_add_inj THEN
    EXISTS_TAC `w:A word` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP1AUX_good_dimindex_cases) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[asm_assert_def; (record_info "asm_state").ri_accfupds; K_THM;
              LTTP1AUX_wmw_consts; LTTP1AUX_wmw_failed] THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_CASES_TAC `k < 4` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < 4`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    USE_THEN "bytes" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then 3 - k else k) < 4`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then 3 - k else k`) THEN
    SIMP_TAC[];
    X_GEN_TAC `x:A word` THEN DISCH_TAC THEN MATCH_MP_TAC LTTP1AUX_wmw_mem_out THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < 4`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    USE_THEN "bytes" (MP_TAC o C MP (ASSUME `(if asm_state_be (t1:(A)asm_state)
          then 3 - k else k) < 4`) o SPEC `if asm_state_be (t1:(A)asm_state)
          then 3 - k else k`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `byte_align (word_add (w:A word) (word 1)) = byte_align w /\
                byte_align (word_add w (word 2)) = byte_align w /\
                byte_align (word_add w (word 3)) = byte_align w` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LTTP1AUX_byte_align_add4 THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i k. i < 4 /\ k < 4 /\
         ITER i (\b. if asm_state_be (t1:(A)asm_state)
                     then word_sub b (word 1) else word_add b (word 1)) (st:A word) =
         ITER k (\b. if asm_state_be (t1:(A)asm_state)
                     then word_sub b (word 1) else word_add b (word 1)) st ==> i = k`
    (LABEL_TAC "iterinj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `i < 4`) o SPEC `i:num`) THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < 4`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) ASSUME_TAC) THEN
    SUBGOAL_THEN `(if asm_state_be (t1:(A)asm_state) then 3 - i else i) =
                  (if asm_state_be t1 then 3 - k else k)` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `i < 4` THEN UNDISCH_TAC `k < 4` THEN
    BOOL_CASES_TAC `asm_state_be (t1:(A)asm_state)` THEN REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < 4 ==> asm_state_mem (write_mem_word (st:A word) 4 a' t1)
                                (word_add (w:A word) (word j)) =
                              get_byte (word j:int32) (word_zx (a':A word)) (asm_state_be t1)`
    (LABEL_TAC "asmw") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    ABBREV_TAC `k = if asm_state_be (t1:(A)asm_state) then 3 - j else j` THEN
    SUBGOAL_THEN `k < 4 /\ ITER k (\b. if asm_state_be (t1:(A)asm_state)
                    then word_sub b (word 1) else word_add b (word 1)) st =
                  word_add (w:A word) (word j)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `k < 4` ASSUME_TAC THENL
       [EXPAND_TAC "k" THEN COND_CASES_TAC THEN UNDISCH_TAC `j < 4` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < 4`) o SPEC `k:num`) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      EXPAND_TAC "k" THEN COND_CASES_TAC THEN UNDISCH_TAC `j < 4` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ITER")) (lhs(concl th)))) THEN
    MP_TAC(SPECL [`4`; `st:A word`; `a':A word`; `t1:(A)asm_state`; `k:num`]
           LTTP1AUX_wmw_mem_in) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i < 4` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `k:num = i` MP_TAC THENL
       [USE_THEN "iterinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `i < k` THEN ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "k" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LTTP1AUX_get_byte_32_zx THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. (!j. j < 4 ==> ~(x = word_add (w:A word) (word j)))
                    ==> asm_state_mem (write_mem_word (st:A word) 4 a' t1) x =
                        asm_state_mem t1 x` (LABEL_TAC "asmout") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LTTP1AUX_wmw_mem_out THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "iter" (MP_TAC o C MP (ASSUME `k < 4`) o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:A word` THEN DISCH_TAC THEN
  REWRITE_TAC[word_loc_val_byte_def; APPLY_UPDATE_THM] THEN
  ASM_CASES_TAC `byte_align (w:A word) = byte_align x` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_loc_val_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN
    SIMP_TAC[LTTP1AUX_get_set_byte; ASSUME `good_dimindex(:A)`;
             SYM(ASSUME `byte_align (w:A word) = byte_align x`);
             ASSUME `byte_align (word_add (w:A word) (word 1)) = byte_align w`;
             ASSUME `byte_align (word_add (w:A word) (word 2)) = byte_align w`;
             ASSUME `byte_align (word_add (w:A word) (word 3)) = byte_align w`] THEN
    ASM_CASES_TAC `x = word_add (w:A word) (word 3)` THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "asmw" (MP_TAC o SPEC `3`) THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `x = word_add (w:A word) (word 2)` THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[LTTP1AUX_word_add_eq4; ASSUME `good_dimindex(:A)`; ARITH] THEN
      USE_THEN "asmw" (MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `x = word_add (w:A word) (word 1)` THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[LTTP1AUX_word_add_eq4; ASSUME `good_dimindex(:A)`; ARITH] THEN
      USE_THEN "asmw" (MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:A word = w` THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[LTTP1AUX_word_add_eq4; ASSUME `good_dimindex(:A)`; ARITH] THEN
      USE_THEN "asmw" (MP_TAC o SPEC `0`) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "asmout" (MP_TAC o SPEC `x:A word`) THEN ANTS_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN ASM_REWRITE_TAC[WORD_ADD_0]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "mem" (MP_TAC o SPEC `x:A word`) THEN
    REWRITE_TAC[ASSUME `byte_align (x:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
                word_loc_val_byte_def;
                SYM(ASSUME `byte_align (w:A word) = byte_align x`);
                ASSUME `lab_state_mem (s1:(A,D,FFI)lab_state) (byte_align w) = wl_Word a''`;
                word_loc_val_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    USE_THEN "asmout" (MP_TAC o SPEC `x:A word`) THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "bytes" (MP_TAC o C MP (ASSUME `j < 4`) o SPEC `j:num`) THEN
      ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "mem" (MP_TAC o SPEC `x:A word`) THEN
    REWRITE_TAC[ASSUME `byte_align (x:A word) IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)`;
                word_loc_val_byte_def] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let LTTP1AUX_lab_mem_op_consts = prove
 (`!m r a (s:(A,D,FFI)lab_state).
     lab_state_fp_regs (lab_mem_op m r a s) = lab_state_fp_regs s /\
     lab_state_mem_domain (lab_mem_op m r a s) = lab_state_mem_domain s /\
     lab_state_shared_mem_domain (lab_mem_op m r a s) = lab_state_shared_mem_domain s /\
     lab_state_be (lab_mem_op m r a s) = lab_state_be s /\
     lab_state_compile (lab_mem_op m r a s) = lab_state_compile s /\
     lab_state_compile_oracle (lab_mem_op m r a s) = lab_state_compile_oracle s /\
     lab_state_code_buffer (lab_mem_op m r a s) = lab_state_code_buffer s /\
     ((m = asm_Load \/ m = Load8 \/ m = asm_Load32)
      ==> lab_state_mem (lab_mem_op m r a s) = lab_state_mem s) /\
     ((m = asm_Store \/ m = Store8 \/ m = asm_Store32)
      ==> lab_state_regs (lab_mem_op m r a s) = lab_state_regs s)`,
  GEN_TAC THEN CASES_ON `m:memop` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[distinctness "memop"] THEN
  SIMP LABPROPSAUX_UNFOLD THEN EVERY_CASE_TAC THEN SIMP LABPROPSAUX_UNFOLD);;

let LTTP1AUX_asm_inst_consts2 = prove
 (`!i (s:(A,D,FFI)lab_state).
     lab_state_mem_domain (asm_inst i s) = lab_state_mem_domain s /\
     lab_state_shared_mem_domain (asm_inst i s) = lab_state_shared_mem_domain s /\
     lab_state_be (asm_inst i s) = lab_state_be s /\
     lab_state_compile (asm_inst i s) = lab_state_compile s /\
     lab_state_compile_oracle (asm_inst i s) = lab_state_compile_oracle s /\
     lab_state_code_buffer (asm_inst i s) = lab_state_code_buffer s`,
  GEN_TAC THEN CASES_ON `i:(A)inst` THEN
  REWRITE_TAC[asm_inst_def; lab_arith_upd_consts; lab_fp_upd_consts;
              LTTP1AUX_lab_mem_op_consts] THEN
  REWRITE_TAC[lab_upd_reg_def; (record_info "lab_state").ri_accfupds; K_THM]);;

let LTTP1AUX_inst_mem = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) m r a.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!r. lab_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                SOME (asm_state_mem t1 a)) /\
     lab_state_be s1 = asm_state_be t1 /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
     ~lab_state_failed (lab_mem_op m r a s1)
     ==> ~asm_state_failed (asm_mem_op m r a t1) /\
         (!x. ~(x IN lab_state_mem_domain s1)
              ==> asm_state_mem (asm_mem_op m r a t1) x = asm_state_mem t1 x) /\
         (!r'. lab_state_fp_regs (lab_mem_op m r a s1) r' =
               asm_state_fp_regs (asm_mem_op m r a t1) r') /\
         (!r'. word_loc_val p labs (lab_state_regs (lab_mem_op m r a s1) r') =
               SOME (asm_state_regs (asm_mem_op m r a t1) r')) /\
         (!x. byte_align x IN lab_state_mem_domain s1
              ==> word_loc_val_byte p labs (lab_state_mem (lab_mem_op m r a s1)) x
                    (lab_state_be s1) =
                  SOME (asm_state_mem (asm_mem_op m r a t1) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. byte_align x IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)
                    ==> word_loc_val_byte (p:A word) labs (lab_state_mem s1) x
                          (asm_state_be (t1:(A)asm_state)) =
                        SOME (asm_state_mem t1 x)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      lhs(concl th) = `lab_state_be (s1:(A,D,FFI)lab_state)` then
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else NO_TAC) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:memop`; `r:num`; `a:(A)addr`; `s1:(A,D,FFI)lab_state`]
         LTTP1AUX_lab_mem_op_consts) THEN
  CASES_ON `m:memop` THEN REWRITE_TAC[distinctness "memop"] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lab_mem_op_def]) THEN
  ASM_REWRITE_TAC[lab_mem_op_def; asm_mem_op_def] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
        `~lab_state_failed (lab_assert F (s1:(A,D,FFI)lab_state))`)) THEN
      REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN NO_TAC) THENL
   [(MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                  `t1:(A)asm_state`; `r:num`; `a:(A)addr`] LTTP1AUX_inst_load) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);
    (MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                  `t1:(A)asm_state`; `r:num`; `a:(A)addr`] LTTP1AUX_inst_load8) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);
    (MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                  `t1:(A)asm_state`; `r:num`; `a:(A)addr`] LTTP1AUX_inst_load32) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);
    (MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                  `t1:(A)asm_state`; `r:num`; `a:(A)addr`] LTTP1AUX_inst_store) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);
    (MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                  `t1:(A)asm_state`; `r:num`; `a:(A)addr`] LTTP1AUX_inst_store8) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);
    (MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                  `t1:(A)asm_state`; `r:num`; `a:(A)addr`] LTTP1AUX_inst_store32) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[])]);;

let LTTP1AUX_inst_core = prove
 (`!(p:A word) labs (s1:(A,D,FFI)lab_state) (t1:(A)asm_state) i.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!r. lab_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
              word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
              SOME (asm_state_mem t1 a)) /\
     (lab_state_be s1 <=> asm_state_be t1) /\ good_dimindex(:A) /\
     ~asm_state_failed t1 /\ ~lab_state_failed (asm_inst i s1)
     ==> ~asm_state_failed (asmSem_inst i t1) /\
         (!x. ~(x IN lab_state_mem_domain s1)
              ==> asm_state_mem (asmSem_inst i t1) x = asm_state_mem t1 x) /\
         (!r'. lab_state_fp_regs (asm_inst i s1) r' =
               asm_state_fp_regs (asmSem_inst i t1) r') /\
         (!r'. word_loc_val p labs (lab_state_regs (asm_inst i s1) r') =
               SOME (asm_state_regs (asmSem_inst i t1) r')) /\
         (!x. byte_align x IN lab_state_mem_domain s1
              ==> word_loc_val_byte p labs (lab_state_mem (asm_inst i s1)) x
                    (lab_state_be s1) =
                  SOME (asm_state_mem (asmSem_inst i t1) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. byte_align x IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)
                    ==> word_loc_val_byte (p:A word) labs (lab_state_mem s1) x
                          (lab_state_be s1) = SOME (asm_state_mem (t1:(A)asm_state) x)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. byte_align x IN lab_state_mem_domain (s1:(A,D,FFI)lab_state)
                    ==> word_loc_val_byte (p:A word) labs (lab_state_mem s1) x
                          (asm_state_be (t1:(A)asm_state)) = SOME (asm_state_mem t1 x)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `lab_state_be (s1:(A,D,FFI)lab_state) <=>
                             asm_state_be (t1:(A)asm_state)`)] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~lab_state_failed (asm_inst i (s1:(A,D,FFI)lab_state))` THEN
  CASES_ON `i:(A)inst` THEN REWRITE_TAC[asm_inst_def; asmSem_inst_def] THEN
  DISCH_TAC THENL
  [(* Skip *)
   ASM_REWRITE_TAC[];
   (* Const *)
   REWRITE_TAC[LTTP1AUX_lab_regs_upd] THEN
   SUBGOAL_THEN
     `asm_state_failed (asm_upd_reg a0 a1 (t1:(A)asm_state)) = asm_state_failed t1 /\
      asm_state_mem (asm_upd_reg a0 a1 t1) = asm_state_mem t1 /\
      asm_state_fp_regs (asm_upd_reg a0 a1 t1) = asm_state_fp_regs t1 /\
      lab_state_fp_regs (lab_upd_reg a0 (wl_Word a1) (s1:(A,D,FFI)lab_state)) =
        lab_state_fp_regs s1 /\
      lab_state_mem (lab_upd_reg a0 (wl_Word a1) s1) = lab_state_mem s1`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[lab_upd_reg_def; asm_upd_reg_def] THEN SIMP[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC LTTP1AUX_word_loc_val_upd THEN ASM_REWRITE_TAC[word_loc_val_def];
   (* Arith *)
   MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                 `t1:(A)asm_state`; `a:(A)asm_arith`] arith_upd_lemma) THEN
   MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                 `t1:(A)asm_state`; `a:(A)asm_arith`] LTTP1AUX_arith_upd_failed) THEN
   ASM_REWRITE_TAC[arith_upd_fp_regs; lab_arith_upd_consts; asm_arith_upd_consts] THEN
   REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
   (* Mem *)
   MATCH_MP_TAC LTTP1AUX_inst_mem THEN ASM_REWRITE_TAC[];
   (* FP *)
   MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                 `t1:(A)asm_state`; `a:fp`] fp_upd_lemma) THEN
   MP_TAC(SPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,D,FFI)lab_state`;
                 `t1:(A)asm_state`; `a:fp`] LTTP1AUX_fp_upd_failed) THEN
   ASM_REWRITE_TAC[lab_fp_upd_consts; asm_fp_upd_consts] THEN
   REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2170 (labSem's asm_inst, inc_pc and dec_clock; asmSem's inst  *)
(* and upd_pc)                                                                *)
let lab_to_targetProof_Inst_lemma = prove
 (`!i (s1:(A,lab_to_target_config,FFI)lab_state) (mc_conf:(A,B,C)machine_config) code2 labs
     p (t1:(A)asm_state) ms1 bytes' ms2.
     ~lab_state_failed (asm_inst i s1) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     pos_val (lab_state_pc s1 + 1) 0 code2 = pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes'
     ==> ~asm_state_failed (asmSem_inst i t1) /\
         (!a. ~(a IN lab_state_mem_domain s1)
              ==> asm_state_mem (asmSem_inst i t1) a = asm_state_mem t1 a) /\
         (target_state_rel (machine_config_target mc_conf)
            (asm_upd_pc (word_add (asm_state_pc t1) (word (LENGTH bytes'))) (asmSem_inst i t1))
            ms2
          ==> lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                (inc_pc (lab_dec_clock (asm_inst i s1)))
                (asm_upd_pc (word_add (asm_state_pc t1) (word (LENGTH (bytes':byte list))))
                   (asmSem_inst i t1)) ms2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!r. word_loc_val (p:A word) labs (lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) r) =
         SOME (asm_state_regs (t1:(A)asm_state) r)) /\
    (!r. lab_state_fp_regs s1 r = asm_state_fp_regs t1 r) /\
    (!a. byte_align a IN lab_state_mem_domain s1
         ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
             word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
             SOME (asm_state_mem t1 a)) /\
    (lab_state_be s1 <=> asm_state_be t1) /\ good_dimindex(:A) /\ ~asm_state_failed t1 /\
    asm_state_pc t1 = word_add p (word (pos_val (lab_state_pc s1) 0 (code2:((A)sec)list)))`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lab_to_targetProof_state_rel (mc_conf:(A,B,C)machine_config,code2,labs,p:A word)
                   (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) (ms1:B)` THEN
    REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN
    DISCH_THEN(fun th -> REWRITE_TAC(CONJUNCTS th));
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A word`; `labs:(num spt)spt`; `s1:(A,lab_to_target_config,FFI)lab_state`;
                 `t1:(A)asm_state`; `i:(A)inst`] LTTP1AUX_inst_core) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
                 `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`;
                 `ms1:B`;
                 `inc_pc (lab_dec_clock (asm_inst i (s1:(A,lab_to_target_config,FFI)lab_state)))`;
                 `asm_upd_pc (word_add (asm_state_pc (t1:(A)asm_state))
                                (word (LENGTH (bytes':byte list)))) (asmSem_inst i t1)`;
                 `ms2:B`] LTTP1AUX_state_rel_frame) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[inc_pc_def; lab_dec_clock_def] THEN
  SIMP[asm_inst_consts; LTTP1AUX_asm_inst_consts2; upd_pc_simps; ASMAUX_inst_consts] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `lab_state_be (s1:(A,lab_to_target_config,FFI)lab_state) <=>
                             asm_state_be (t1:(A)asm_state)`)] THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]]);;
