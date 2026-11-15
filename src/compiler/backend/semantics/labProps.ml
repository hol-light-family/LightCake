(* ========================================================================= *)
(* labProps: port of HOL4 compiler/backend/semantics/labPropsScript.sml      *)
(* (CakeML v3479).                                                           *)
(* Properties about labLang and its semantics.                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "semantics/proofs/semanticsProps.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: extract_labels_def [simp] *)

let lab_extract_labels_def = cake_def
  `(lab_extract_labels ([]:((A)line)list) = []) /\
   (lab_extract_labels (CONS (lab_Label l1 l2 _) xs) =
      CONS (l1,l2) (lab_extract_labels xs)) /\
   (lab_extract_labels (CONS x xs) = lab_extract_labels xs)`;;

let lab_extract_labels_ind = cake_ind "lab_extract_labels";;

let _ = cake_add_simps [lab_extract_labels_def];;

let extract_labels_append = prove
 (`!A B:((A)line)list.
     lab_extract_labels (APPEND A B) =
     APPEND (lab_extract_labels A) (lab_extract_labels B)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lab_extract_labels_def; APPEND] THEN
  CASES_ON `h:(A)line` THEN ASM_REWRITE_TAC[lab_extract_labels_def; APPEND]);;

(* HOL4: labs_of_def [simp] *)

let labs_of_def = cake_def
  `(labs_of (lab_LocValue _ (lab_Lab n1 n2):(A)asm_with_lab) = {(n1,n2)}) /\
   (labs_of (lab_Jump (lab_Lab n1 n2):(A)asm_with_lab) = {(n1,n2)}) /\
   (labs_of (lab_JumpCmp _ _ _ (lab_Lab n1 n2):(A)asm_with_lab) = {(n1,n2)}) /\
   (labs_of (_:(A)asm_with_lab) = {})`;;

let _ = cake_add_simps [labs_of_def];;

let line_get_labels_def = cake_def
  `(line_get_labels (LabAsm a _ _ _:(A)line) = labs_of a) /\
   (line_get_labels (_:(A)line) = {})`;;

let sec_get_labels_def = cake_def
  `sec_get_labels (Section _ lines:(A)sec) =
     UNIONS (IMAGE line_get_labels (set_of_list lines))`;;

(* HOL4: get_labels_def *)

let lab_get_labels_def = cake_def
  `lab_get_labels (code:((A)sec)list) =
     UNIONS (IMAGE sec_get_labels (set_of_list code))`;;

let get_labels_cons = prove
 (`lab_get_labels (CONS (x:(A)sec) xs) = sec_get_labels x UNION lab_get_labels xs`,
  REWRITE_TAC[lab_get_labels_def; set_of_list; IMAGE_CLAUSES; UNIONS_INSERT]);;

(* HOL4: line_get_code_labels_def [simp] *)

let line_get_code_labels_def = cake_def
  `(line_get_code_labels (lab_Label _ l _:(A)line) = {l}) /\
   (line_get_code_labels (_:(A)line) = {})`;;

let _ = cake_add_simps [line_get_code_labels_def];;

let sec_get_code_labels_def = cake_def
  `sec_get_code_labels (Section n1 lines:(A)sec) =
     (n1,0) INSERT
     IMAGE (\n2. (n1,n2)) (UNIONS (IMAGE line_get_code_labels (set_of_list lines)))`;;

(* HOL4: get_code_labels_def *)

let lab_get_code_labels_def = cake_def
  `lab_get_code_labels (code:((A)sec)list) =
     UNIONS (IMAGE sec_get_code_labels (set_of_list code))`;;

let get_code_labels_nil = prove
 (`lab_get_code_labels ([]:((A)sec)list) = {}`,
  REWRITE_TAC[lab_get_code_labels_def; set_of_list; IMAGE_CLAUSES; UNIONS_0]);;

let _ = cake_add_simps [get_code_labels_nil];;

let get_code_labels_cons = prove
 (`lab_get_code_labels (CONS (s:(A)sec) secs) =
   sec_get_code_labels s UNION lab_get_code_labels secs`,
  REWRITE_TAC[lab_get_code_labels_def; set_of_list; IMAGE_CLAUSES; UNIONS_INSERT]);;

let sec_ends_with_label_def = cake_def
  `sec_ends_with_label (Section _ ls:(A)sec) <=> ~NULL ls /\ is_Label (LAST ls)`;;

let reg_imm_with_clock = prove
 (`lab_reg_imm r (lab_state_clock_fupd (K z) (s:(A,C,FFI)lab_state)) =
   lab_reg_imm r s`,
  CASES_ON `r:(A)reg_imm` THEN SIMP[lab_reg_imm_def]);;

let _ = cake_add_simps [reg_imm_with_clock];;

(* the definitions of the state updates of asm_inst *)

let LABPROPSAUX_UNFOLD =
  [asm_inst_def; lab_arith_upd_def; lab_binop_upd_def; lab_upd_reg_def;
   lab_assert_def; lab_mem_op_def; lab_mem_load_def; lab_mem_store_def;
   mem_load32_def; mem_store32_def; mem_load_byte_def; mem_store_byte_def;
   lab_addr_def; lab_upd_mem_def; lab_fp_upd_def; lab_upd_fp_reg_def;
   lab_read_fp_reg_def; lab_reg_imm_def];;

let asm_inst_with_clock = prove
 (`asm_inst i (lab_state_clock_fupd (K z) (s:(A,C,FFI)lab_state)) =
   lab_state_clock_fupd (K z) (asm_inst i s)`,
  CASES_ON `i:(A)inst` THEN
  STACKPAUX_TYPE_CASES_TAC `:(A)asm_arith` THEN
  STACKPAUX_TYPE_CASES_TAC `:memop` THEN
  STACKPAUX_TYPE_CASES_TAC `:(A)addr` THEN
  STACKPAUX_TYPE_CASES_TAC `:fp` THEN
  SIMP LABPROPSAUX_UNFOLD THEN
  EVERY_CASE_TAC THEN
  STACKPAUX_TYPE_CASES_TAC `:binop` THEN
  SIMP LABPROPSAUX_UNFOLD);;

let read_reg_inc_pc = prove
 (`lab_state_regs (inc_pc s) r = lab_state_regs (s:(A,C,FFI)lab_state) r`,
  REWRITE_TAC[inc_pc_def] THEN SIMP[]);;

let _ = cake_add_simps [read_reg_inc_pc];;

(* HOL4: with_same_clock [simp] *)

let lab_with_same_clock = prove
 (`lab_state_clock_fupd (K (lab_state_clock s)) (s:(A,C,FFI)lab_state) = s`,
  REWRITE_TAC[lab_state_component_equality] THEN SIMP[]);;

let _ = cake_add_simps [lab_with_same_clock];;

let inc_pc_dec_clock = prove
 (`inc_pc (lab_dec_clock x) = lab_dec_clock (inc_pc (x:(A,C,FFI)lab_state))`,
  REWRITE_TAC[inc_pc_def; lab_dec_clock_def] THEN SIMP[]);;

let update_simps = prove
 (`lab_state_ffi (lab_upd_pc x (s:(A,C,FFI)lab_state)) = lab_state_ffi s /\
   lab_state_ffi (lab_dec_clock s) = lab_state_ffi s /\
   lab_state_pc (lab_upd_pc x s) = x /\
   lab_state_pc (lab_dec_clock s) = lab_state_pc s /\
   lab_state_clock (lab_upd_pc x s) = lab_state_clock s /\
   lab_state_ffi (lab_upd_pc x s) = lab_state_ffi s /\
   lab_state_clock (lab_dec_clock s) = lab_state_clock s - 1 /\
   lab_state_len_reg (lab_dec_clock s) = lab_state_len_reg s /\
   lab_state_len2_reg (lab_dec_clock s) = lab_state_len2_reg s /\
   lab_state_link_reg (lab_dec_clock s) = lab_state_link_reg s /\
   lab_state_code (lab_dec_clock s) = lab_state_code s /\
   lab_state_ptr_reg (lab_dec_clock s) = lab_state_ptr_reg s /\
   lab_state_ptr2_reg (lab_dec_clock s) = lab_state_ptr2_reg s /\
   lab_state_ffi (lab_dec_clock s) = lab_state_ffi s /\
   lab_state_len_reg (lab_upd_pc x s) = lab_state_len_reg s /\
   lab_state_len2_reg (lab_upd_pc x s) = lab_state_len2_reg s /\
   lab_state_link_reg (lab_upd_pc x s) = lab_state_link_reg s /\
   lab_state_code (lab_upd_pc x s) = lab_state_code s /\
   lab_state_ptr_reg (lab_upd_pc x s) = lab_state_ptr_reg s /\
   lab_state_ptr2_reg (lab_upd_pc x s) = lab_state_ptr2_reg s /\
   lab_state_mem_domain (lab_upd_pc x s) = lab_state_mem_domain s /\
   lab_state_shared_mem_domain (lab_upd_pc x s) = lab_state_shared_mem_domain s /\
   lab_state_failed (lab_upd_pc x s) = lab_state_failed s /\
   lab_state_be (lab_upd_pc x s) = lab_state_be s /\
   lab_state_mem (lab_upd_pc x s) = lab_state_mem s /\
   lab_state_regs (lab_upd_pc x s) = lab_state_regs s /\
   lab_state_fp_regs (lab_upd_pc x s) = lab_state_fp_regs s /\
   lab_state_ffi (lab_upd_pc x s) = lab_state_ffi s /\
   lab_state_ptr_reg (inc_pc s) = lab_state_ptr_reg s /\
   lab_state_ptr2_reg (inc_pc s) = lab_state_ptr2_reg s /\
   lab_state_len_reg (inc_pc s) = lab_state_len_reg s /\
   lab_state_len2_reg (inc_pc s) = lab_state_len2_reg s /\
   lab_state_link_reg (inc_pc s) = lab_state_link_reg s /\
   lab_state_code (inc_pc s) = lab_state_code s /\
   lab_state_be (inc_pc s) = lab_state_be s /\
   lab_state_failed (inc_pc s) = lab_state_failed s /\
   lab_state_mem_domain (inc_pc s) = lab_state_mem_domain s /\
   lab_state_shared_mem_domain (inc_pc s) = lab_state_shared_mem_domain s /\
   lab_state_io_regs (inc_pc s) = lab_state_io_regs s /\
   lab_state_io_fp_regs (inc_pc s) = lab_state_io_fp_regs s /\
   lab_state_cc_regs (inc_pc s) = lab_state_cc_regs s /\
   lab_state_cc_fp_regs (inc_pc s) = lab_state_cc_fp_regs s /\
   lab_state_compile (inc_pc s) = lab_state_compile s /\
   lab_state_compile_oracle (inc_pc s) = lab_state_compile_oracle s /\
   lab_state_code_buffer (inc_pc s) = lab_state_code_buffer s /\
   lab_state_mem (inc_pc s) = lab_state_mem s /\
   lab_state_regs (inc_pc s) = lab_state_regs s /\
   lab_state_fp_regs (inc_pc s) = lab_state_fp_regs s /\
   lab_state_pc (inc_pc s) = lab_state_pc s + 1 /\
   lab_state_ffi (inc_pc s) = lab_state_ffi s`,
  REWRITE_TAC[lab_upd_pc_def; lab_dec_clock_def; inc_pc_def] THEN SIMP[]);;

let _ = cake_add_simps [update_simps];;

(* HOL4: binop_upd_consts [simp] *)

let lab_binop_upd_consts = prove
 (`lab_state_mem_domain (lab_binop_upd a b c d (x:(A,C,FFI)lab_state)) = lab_state_mem_domain x /\
   lab_state_shared_mem_domain (lab_binop_upd a b c d x) = lab_state_shared_mem_domain x /\
   lab_state_ptr_reg (lab_binop_upd a b c d x) = lab_state_ptr_reg x /\
   lab_state_ptr2_reg (lab_binop_upd a b c d x) = lab_state_ptr2_reg x /\
   lab_state_len_reg (lab_binop_upd a b c d x) = lab_state_len_reg x /\
   lab_state_len2_reg (lab_binop_upd a b c d x) = lab_state_len2_reg x /\
   lab_state_link_reg (lab_binop_upd a b c d x) = lab_state_link_reg x /\
   lab_state_code (lab_binop_upd a b c d x) = lab_state_code x /\
   lab_state_be (lab_binop_upd a b c d x) = lab_state_be x /\
   lab_state_mem (lab_binop_upd a b c d x) = lab_state_mem x /\
   lab_state_io_regs (lab_binop_upd a b c d x) = lab_state_io_regs x /\
   lab_state_io_fp_regs (lab_binop_upd a b c d x) = lab_state_io_fp_regs x /\
   lab_state_cc_regs (lab_binop_upd a b c d x) = lab_state_cc_regs x /\
   lab_state_cc_fp_regs (lab_binop_upd a b c d x) = lab_state_cc_fp_regs x /\
   lab_state_compile (lab_binop_upd a b c d x) = lab_state_compile x /\
   lab_state_compile_oracle (lab_binop_upd a b c d x) = lab_state_compile_oracle x /\
   lab_state_code_buffer (lab_binop_upd a b c d x) = lab_state_code_buffer x /\
   lab_state_pc (lab_binop_upd a b c d x) = lab_state_pc x /\
   lab_state_ffi (lab_binop_upd a b c d x) = lab_state_ffi x`,
  CASES_ON `b:binop` THEN REWRITE_TAC[lab_binop_upd_def; lab_upd_reg_def] THEN SIMP[]);;

let _ = cake_add_simps [lab_binop_upd_consts];;

(* HOL4: arith_upd_consts [simp] *)

let lab_arith_upd_consts = prove
 (`lab_state_mem_domain (lab_arith_upd a (x:(A,C,FFI)lab_state)) = lab_state_mem_domain x /\
   lab_state_shared_mem_domain (lab_arith_upd a x) = lab_state_shared_mem_domain x /\
   lab_state_ptr_reg (lab_arith_upd a x) = lab_state_ptr_reg x /\
   lab_state_ptr2_reg (lab_arith_upd a x) = lab_state_ptr2_reg x /\
   lab_state_len_reg (lab_arith_upd a x) = lab_state_len_reg x /\
   lab_state_len2_reg (lab_arith_upd a x) = lab_state_len2_reg x /\
   lab_state_link_reg (lab_arith_upd a x) = lab_state_link_reg x /\
   lab_state_code (lab_arith_upd a x) = lab_state_code x /\
   lab_state_be (lab_arith_upd a x) = lab_state_be x /\
   lab_state_mem (lab_arith_upd a x) = lab_state_mem x /\
   lab_state_io_regs (lab_arith_upd a x) = lab_state_io_regs x /\
   lab_state_io_fp_regs (lab_arith_upd a x) = lab_state_io_fp_regs x /\
   lab_state_cc_regs (lab_arith_upd a x) = lab_state_cc_regs x /\
   lab_state_cc_fp_regs (lab_arith_upd a x) = lab_state_cc_fp_regs x /\
   lab_state_compile (lab_arith_upd a x) = lab_state_compile x /\
   lab_state_compile_oracle (lab_arith_upd a x) = lab_state_compile_oracle x /\
   lab_state_code_buffer (lab_arith_upd a x) = lab_state_code_buffer x /\
   lab_state_pc (lab_arith_upd a x) = lab_state_pc x /\
   lab_state_ffi (lab_arith_upd a x) = lab_state_ffi x`,
  CASES_ON `a:(A)asm_arith` THEN SIMP LABPROPSAUX_UNFOLD THEN
  EVERY_CASE_TAC THEN STACKPAUX_TYPE_CASES_TAC `:binop` THEN SIMP LABPROPSAUX_UNFOLD);;

let _ = cake_add_simps [lab_arith_upd_consts];;

(* HOL4: fp_upd_consts [simp] *)

let lab_fp_upd_consts = prove
 (`lab_state_mem_domain (lab_fp_upd f (x:(A,C,FFI)lab_state)) = lab_state_mem_domain x /\
   lab_state_shared_mem_domain (lab_fp_upd f x) = lab_state_shared_mem_domain x /\
   lab_state_ptr_reg (lab_fp_upd f x) = lab_state_ptr_reg x /\
   lab_state_len_reg (lab_fp_upd f x) = lab_state_len_reg x /\
   lab_state_ptr2_reg (lab_fp_upd f x) = lab_state_ptr2_reg x /\
   lab_state_len2_reg (lab_fp_upd f x) = lab_state_len2_reg x /\
   lab_state_link_reg (lab_fp_upd f x) = lab_state_link_reg x /\
   lab_state_code (lab_fp_upd f x) = lab_state_code x /\
   lab_state_cc_regs (lab_fp_upd f x) = lab_state_cc_regs x /\
   lab_state_cc_fp_regs (lab_fp_upd f x) = lab_state_cc_fp_regs x /\
   lab_state_code_buffer (lab_fp_upd f x) = lab_state_code_buffer x /\
   lab_state_compile (lab_fp_upd f x) = lab_state_compile x /\
   lab_state_compile_oracle (lab_fp_upd f x) = lab_state_compile_oracle x /\
   lab_state_be (lab_fp_upd f x) = lab_state_be x /\
   lab_state_mem (lab_fp_upd f x) = lab_state_mem x /\
   lab_state_io_regs (lab_fp_upd f x) = lab_state_io_regs x /\
   lab_state_io_fp_regs (lab_fp_upd f x) = lab_state_io_fp_regs x /\
   lab_state_pc (lab_fp_upd f x) = lab_state_pc x /\
   lab_state_ffi (lab_fp_upd f x) = lab_state_ffi x`,
  CASES_ON `f:fp` THEN SIMP LABPROPSAUX_UNFOLD THEN EVERY_CASE_TAC THEN
  SIMP LABPROPSAUX_UNFOLD);;

let _ = cake_add_simps [lab_fp_upd_consts];;


let line_length_def = cake_def
  `(line_length (lab_Label k1 k2 l:(A)line) = if l = 0 then 0 else 1) /\
   (line_length (Asm b bytes l:(A)line) = LENGTH bytes) /\
   (line_length (LabAsm a w bytes l:(A)line) = LENGTH bytes)`;;

let LENGTH_line_bytes = prove
 (`!x2:(A)line. ~is_Label x2 ==> LENGTH (line_bytes x2) = line_length x2`,
  GEN_TAC THEN CASES_ON `x2:(A)line` THEN
  REWRITE_TAC[is_Label_def; line_bytes_def; line_length_def]);;

let _ = cake_add_simps [LENGTH_line_bytes];;

(* HOL4: case_eq_thms *)

let lab_case_eq_thms = end_itlist CONJ
  ([pair_case_eq; COND_CASE_EQ] @
   map case_eq ["line"; "option"; "asm_with_lab"; "asm_or_cbw"; "asm"; "word_loc";
                "list"; "sec"; "ffi_result"]);;

(* call_FFI and share_mem_op only extend the io_events *)

let LABPROPSAUX_call_FFI_io = prove
 (`call_FFI (st:(FFI)ffi_state) n conf bytes = FFI_return st' t ==>
   ffi_state_io_events st <<= ffi_state_io_events st'`,
  DISCH_TAC THEN
  MP_TAC(ISPECL [`st:(FFI)ffi_state`; `st':(FFI)ffi_state`]
    call_FFI_rel_io_events_mono) THEN
  REWRITE_TAC[io_events_mono_def] THEN ANTS_TAC THENL
   [MATCH_MP_TAC RTC_INC THEN REWRITE_TAC[call_FFI_rel_def] THEN ASM_MESON_TAC[];
    SIMP_TAC[]]);;

let LABPROPSAUX_share_mem_op_io = prove
 (`share_mem_op m r ad (s:(A,C,FFI)lab_state) = SOME (res,s') ==>
   ffi_state_io_events (lab_state_ffi s) <<= ffi_state_io_events (lab_state_ffi s')`,
  CASES_ON `m:memop` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def] THEN
  EVERY_CASE_TAC THEN SIMP[inc_pc_def; lab_dec_clock_def] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[LABPROPSAUX_call_FFI_io]);;

(* complete induction on the clock *)

let LABPROPSAUX_CLOCK_INDUCT = prove
 (`!P. (!s:(A,C,FFI)lab_state.
          (!t. lab_state_clock t < lab_state_clock s ==> P t) ==> P s)
       ==> !s. P s`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n (s:(A,C,FFI)lab_state). lab_state_clock s = n ==> P s`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN ASM_MESON_TAC[]);;

(* the case split of one step of lab_evaluate: complete induction on the   *)
(* clock, one unfolding, then every case of the step                        *)

let LABPROPSAUX_EVAL_SPLIT_TAC : tactic =
  MATCH_MP_TAC LABPROPSAUX_CLOCK_INDUCT THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[lab_evaluate_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT TOP_CASE_TAC;;

(* the clock of the state of a recursive call is smaller *)

let LABPROPSAUX_CLOCK_LT_TAC : tactic =
  REWRITE_TAC[inc_pc_def; lab_dec_clock_def; lab_upd_pc_def; lab_upd_reg_def] THEN
  SIMP[asm_inst_consts] THEN
  TRY(FIRST_ASSUM(MP_TAC o MATCH_MP STACKPAUX_share_mem_op_clock) THEN SIMP[]) THEN
  ASM_ARITH_TAC;;

let LABPROPSAUX_IO_STEP = prove
 (`!(s:(A,C,FFI)lab_state) (t:(A,C,FFI)lab_state).
     ffi_state_io_events (lab_state_ffi s) <<= ffi_state_io_events (lab_state_ffi t) /\
     ffi_state_io_events (lab_state_ffi t) <<=
     ffi_state_io_events (lab_state_ffi (SND (lab_evaluate t)))
     ==> ffi_state_io_events (lab_state_ffi s) <<=
         ffi_state_io_events (lab_state_ffi (SND (lab_evaluate t)))`,
  MESON_TAC[IS_PREFIX_TRANS]);;

let LABPROPSAUX_io_SND = prove
 (`!s:(A,C,FFI)lab_state. ffi_state_io_events (lab_state_ffi s) <<=
     ffi_state_io_events (lab_state_ffi (SND (lab_evaluate s)))`,
  LABPROPSAUX_EVAL_SPLIT_TAC THEN
  FIRST [MATCH_ACCEPT_TAC IS_PREFIX_REFL;
         MATCH_MP_TAC LABPROPSAUX_IO_STEP THEN CONJ_TAC THENL
          [SIMP[asm_inst_consts; IS_PREFIX_REFL; inc_pc_def; lab_dec_clock_def;
                lab_upd_pc_def; lab_upd_reg_def] THEN
           ASM_MESON_TAC[LABPROPSAUX_share_mem_op_io; LABPROPSAUX_call_FFI_io];
           FIRST_X_ASSUM MATCH_MP_TAC THEN LABPROPSAUX_CLOCK_LT_TAC];
         ASM_MESON_TAC[LABPROPSAUX_share_mem_op_io]]);;

(* HOL4: evaluate_io_events_mono *)

let lab_evaluate_io_events_mono = prove
 (`!s1 r s2. lab_evaluate (s1:(A,C,FFI)lab_state) = (r,s2) ==>
     ffi_state_io_events (lab_state_ffi s1) <<= ffi_state_io_events (lab_state_ffi s2)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s1:(A,C,FFI)lab_state` LABPROPSAUX_io_SND) THEN
  ASM_REWRITE_TAC[SND]);;

(* the parts of a step that do not look at the clock *)

let LABPROPSAUX_asm_fetch_clock = prove
 (`asm_fetch (lab_state_clock_fupd f (s:(A,C,FFI)lab_state)) = asm_fetch s`,
  REWRITE_TAC[asm_fetch_def] THEN SIMP[]);;

let LABPROPSAUX_get_pc_value_clock = prove
 (`get_pc_value l (lab_state_clock_fupd f (s:(A,C,FFI)lab_state)) = get_pc_value l s`,
  REWRITE_TAC[get_pc_value_def] THEN SIMP[]);;

let LABPROPSAUX_get_ret_Loc_clock = prove
 (`get_ret_Loc (lab_state_clock_fupd f (s:(A,C,FFI)lab_state)) = get_ret_Loc s`,
  REWRITE_TAC[get_ret_Loc_def] THEN SIMP[]);;

let LABPROPSAUX_addr_clock = prove
 (`lab_addr a (lab_state_clock_fupd f (s:(A,C,FFI)lab_state)) = lab_addr a s`,
  CASES_ON `a:(A)addr` THEN REWRITE_TAC[lab_addr_def] THEN SIMP[]);;

let LABPROPSAUX_share_mem_op_clock = prove
 (CASE_TERM `share_mem_op m r ad (lab_state_clock_fupd (K c) (s:(A,C,FFI)lab_state)) =
   match share_mem_op m r ad s with
     NONE -> NONE
   | SOME (FFI_final f,t) -> SOME (FFI_final f,lab_state_clock_fupd (K c) t)
   | SOME (FFI_return f l,t) -> SOME (FFI_return f l,lab_state_clock_fupd (K (c - 1)) t)`,
  CASES_ON `m:memop` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def] THEN
  SIMP[LABPROPSAUX_addr_clock] THEN EVERY_CASE_TAC THEN
  SIMP[inc_pc_def; lab_dec_clock_def]);;

let LABPROPSAUX_share_mem_op_final = prove
 (`share_mem_op m r ad (s:(A,C,FFI)lab_state) = SOME (FFI_final f,t) ==> t = s`,
  CASES_ON `m:memop` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let LABPROPSAUX_is_eval_eq th =
  let c = concl th in
  is_eq c &&
  (try fst(dest_const(fst(strip_comb(lhs c)))) = "lab_evaluate" with Failure _ -> false);;

let LABPROPSAUX_ADD_CLOCK_LEAF_TAC : tactic =
  FIRST
   [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) ASSUME_TAC) THEN
    TRY(FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP LABPROPSAUX_share_mem_op_final)) THEN
    REWRITE_TAC[] THEN NO_TAC;
    STRIP_TAC THEN
    (fun (asl,w as g) ->
       let th = snd(find (fun (_,th) -> LABPROPSAUX_is_eval_eq th) asl) in
       let x = rand(lhs(concl th)) in
       (TRY(FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPAUX_share_mem_op_clock)) THEN
        USE_THEN "ih" (MP_TAC o SPEC x) THEN
        ANTS_TAC THENL [LABPROPSAUX_CLOCK_LT_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`res:machine_result`; `r:(A,C,FFI)lab_state`;
                                   `k:num`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
        REWRITE_TAC[lab_state_component_equality] THEN
        REWRITE_TAC[inc_pc_def; lab_dec_clock_def; lab_upd_pc_def; lab_upd_reg_def] THEN
        SIMP[asm_inst_consts] THEN ASM_ARITH_TAC) g)];;

let evaluate_ADD_clock = prove
 (`!s res r k.
      lab_evaluate (s:(A,C,FFI)lab_state) = (res,r) /\ ~(res = target_TimeOut) ==>
      lab_evaluate (lab_state_clock_fupd (K (lab_state_clock s + k)) s) =
      (res,lab_state_clock_fupd (K (lab_state_clock r + k)) r)`,
  MATCH_MP_TAC LABPROPSAUX_CLOCK_INDUCT THEN GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [lab_evaluate_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [lab_evaluate_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `lab_state_clock (s:(A,C,FFI)lab_state) = 0` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  SIMP[ADD_EQ_0; LABPROPSAUX_asm_fetch_clock; LABPROPSAUX_get_pc_value_clock;
       LABPROPSAUX_get_ret_Loc_clock; LABPROPSAUX_share_mem_op_clock;
       asm_inst_with_clock; reg_imm_with_clock] THEN
  REPEAT TOP_CASE_TAC THEN LABPROPSAUX_ADD_CLOCK_LEAF_TAC);;

let addr_add_clock_eq = prove
 (`lab_addr a (lab_state_clock_fupd (K (extra + lab_state_clock s))
                 (s:(A,C,FFI)lab_state)) = lab_addr a s`,
  REWRITE_TAC[LABPROPSAUX_addr_clock]);;

let share_mem_op_add_clock_same = prove
 (`(~(lab_state_clock s = 0) /\ share_mem_op m n a (s:(A,C,FFI)lab_state) = NONE ==>
    share_mem_op m n a (lab_state_clock_fupd (K (extra + lab_state_clock s)) s) = NONE) /\
   (~(lab_state_clock s = 0) /\ share_mem_op m n a s = SOME (FFI_return f l',r) ==>
    share_mem_op m n a (lab_state_clock_fupd (K (extra + lab_state_clock s)) s) =
      SOME (FFI_return f l',lab_state_clock_fupd (K (extra + lab_state_clock r)) r)) /\
   (~(lab_state_clock s = 0) /\ share_mem_op m n a s = SOME (FFI_final f2,r2) ==>
    share_mem_op m n a (lab_state_clock_fupd (K (extra + lab_state_clock s)) s) =
      SOME (FFI_final f2,lab_state_clock_fupd (K (extra + lab_state_clock r2)) r2))`,
  REPEAT CONJ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LABPROPSAUX_share_mem_op_clock] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP STACKPAUX_share_mem_op_clock) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP LABPROPSAUX_share_mem_op_final) THEN
    REWRITE_TAC[]]);;

(* HOL4: evaluate_add_clock_io_events_mono *)

let lab_evaluate_add_clock_io_events_mono = prove
 (`!s:(A,C,FFI)lab_state.
     ffi_state_io_events (lab_state_ffi (SND (lab_evaluate s))) <<=
     ffi_state_io_events (lab_state_ffi (SND (lab_evaluate
       (lab_state_clock_fupd (K (lab_state_clock s + extra)) s))))`,
  MATCH_MP_TAC LABPROPSAUX_CLOCK_INDUCT THEN GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [lab_evaluate_def] THEN
  ASM_CASES_TAC `lab_state_clock (s:(A,C,FFI)lab_state) = 0` THEN ASM_REWRITE_TAC[SND] THENL
   [MP_TAC(ISPEC `lab_state_clock_fupd (K (lab_state_clock s + extra))
                    (s:(A,C,FFI)lab_state)` LABPROPSAUX_io_SND) THEN SIMP[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [lab_evaluate_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[ADD_EQ_0; LABPROPSAUX_asm_fetch_clock; LABPROPSAUX_get_pc_value_clock;
       LABPROPSAUX_get_ret_Loc_clock; LABPROPSAUX_share_mem_op_clock;
       asm_inst_with_clock; reg_imm_with_clock] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[SND] THEN
  FIRST
   [SIMP[IS_PREFIX_REFL] THEN NO_TAC;
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP LABPROPSAUX_share_mem_op_final) THEN
    SIMP[IS_PREFIX_REFL] THEN NO_TAC;
    (fun (asl,w as g) ->
       let ev = find_term (fun t -> is_comb t && is_const(rator t) &&
                             fst(dest_const(rator t)) = "lab_evaluate") (lhand w) in
       let x = rand ev in
       (TRY(FIRST_ASSUM(ASSUME_TAC o MATCH_MP STACKPAUX_share_mem_op_clock)) THEN
        USE_THEN "ih" (MP_TAC o SPEC x) THEN
        ANTS_TAC THENL [LABPROPSAUX_CLOCK_LT_TAC; ALL_TAC] THEN
        MATCH_MP_TAC EQ_IMP THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[lab_state_component_equality] THEN
        REWRITE_TAC[inc_pc_def; lab_dec_clock_def; lab_upd_pc_def; lab_upd_reg_def] THEN
        SIMP[asm_inst_consts] THEN ASM_ARITH_TAC) g)]);;

let align_dm_def = cake_def
  `align_dm (s:(A,C,FFI)lab_state) =
     lab_state_mem_domain_fupd (K (lab_state_mem_domain s INTER byte_aligned)) s`;;

let align_dm_const = prove
 (`lab_state_clock (align_dm s) = lab_state_clock (s:(A,C,FFI)lab_state) /\
   lab_state_pc (align_dm s) = lab_state_pc s /\
   lab_state_code (align_dm s) = lab_state_code s /\
   lab_state_mem (align_dm s) = lab_state_mem s /\
   lab_state_shared_mem_domain (align_dm s) = lab_state_shared_mem_domain s /\
   lab_state_be (align_dm s) = lab_state_be s /\
   lab_state_len_reg (align_dm s) = lab_state_len_reg s /\
   lab_state_link_reg (align_dm s) = lab_state_link_reg s /\
   lab_state_ptr_reg (align_dm s) = lab_state_ptr_reg s /\
   lab_state_ptr2_reg (align_dm s) = lab_state_ptr2_reg s /\
   lab_state_len2_reg (align_dm s) = lab_state_len2_reg s /\
   lab_state_io_regs (align_dm s) = lab_state_io_regs s /\
   lab_state_io_fp_regs (align_dm s) = lab_state_io_fp_regs s /\
   lab_state_code_buffer (align_dm s) = lab_state_code_buffer s /\
   lab_state_compile (align_dm s) = lab_state_compile s /\
   lab_state_compile_oracle (align_dm s) = lab_state_compile_oracle s /\
   lab_state_ffi (align_dm s) = lab_state_ffi s /\
   lab_state_failed (align_dm s) = lab_state_failed s`,
  REWRITE_TAC[align_dm_def] THEN SIMP[]);;

let _ = cake_add_simps [align_dm_const];;

let align_dm_with_clock = prove
 (`align_dm (lab_state_clock_fupd (K k) s) =
   lab_state_clock_fupd (K k) (align_dm (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_dm_def] THEN SIMP[]);;

let asm_fetch_align_dm = prove
 (`asm_fetch (align_dm s) = asm_fetch (s:(A,C,FFI)lab_state)`,
  REWRITE_TAC[asm_fetch_def] THEN SIMP[]);;

let _ = cake_add_simps [asm_fetch_align_dm];;

(* HOL4: read_reg n (align_dm s) = read_reg n s *)

let read_reg_align_dm = prove
 (`lab_state_regs (align_dm s) n = lab_state_regs (s:(A,C,FFI)lab_state) n`,
  REWRITE_TAC[align_dm_def] THEN SIMP[]);;

let _ = cake_add_simps [read_reg_align_dm];;

let upd_reg_align_dm = prove
 (`lab_upd_reg x y (align_dm s) = align_dm (lab_upd_reg x y (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_dm_def; lab_upd_reg_def] THEN SIMP[]);;

let _ = cake_add_simps [upd_reg_align_dm];;

let upd_mem_align_dm = prove
 (`lab_upd_mem x y (align_dm s) = align_dm (lab_upd_mem x y (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_dm_def; lab_upd_mem_def] THEN SIMP[]);;

let _ = cake_add_simps [upd_mem_align_dm];;

let binop_upd_align_dm = prove
 (`lab_binop_upd x y z w (align_dm s) =
   align_dm (lab_binop_upd x y z w (s:(A,C,FFI)lab_state))`,
  CASES_ON `y:binop` THEN SIMP[lab_binop_upd_def]);;

let _ = cake_add_simps [binop_upd_align_dm];;

let reg_imm_align_dm = prove
 (`lab_reg_imm r (align_dm s) = lab_reg_imm r (s:(A,C,FFI)lab_state)`,
  CASES_ON `r:(A)reg_imm` THEN SIMP[lab_reg_imm_def]);;

let _ = cake_add_simps [reg_imm_align_dm];;

let assert_align_dm = prove
 (`lab_assert b (align_dm s) = align_dm (lab_assert b (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_dm_def; lab_assert_def] THEN SIMP[]);;

let _ = cake_add_simps [assert_align_dm];;

let arith_upd_align_dm = prove
 (`lab_arith_upd x (align_dm s) = align_dm (lab_arith_upd x (s:(A,C,FFI)lab_state))`,
  CASES_ON `x:(A)asm_arith` THEN SIMP[lab_arith_upd_def] THEN EVERY_CASE_TAC THEN
  SIMP[]);;

let _ = cake_add_simps [arith_upd_align_dm];;

let fp_upd_align_dm = prove
 (`lab_fp_upd f (align_dm s) = align_dm (lab_fp_upd f (s:(A,C,FFI)lab_state))`,
  CASES_ON `f:fp` THEN
  SIMP[lab_fp_upd_def; lab_upd_fp_reg_def; lab_read_fp_reg_def; lab_upd_reg_def;
       lab_assert_def; align_dm_def] THEN
  EVERY_CASE_TAC THEN
  SIMP[lab_upd_fp_reg_def; lab_read_fp_reg_def; lab_upd_reg_def; lab_assert_def]);;

let _ = cake_add_simps [fp_upd_align_dm];;

let addr_align_dm = prove
 (`lab_addr a (align_dm s) = lab_addr a (s:(A,C,FFI)lab_state)`,
  CASES_ON `a:(A)addr` THEN SIMP[lab_addr_def]);;

let _ = cake_add_simps [addr_align_dm];;

(* align_dm s changes only the mem_domain field, to its byte aligned part *)

let LABPROPSAUX_fupd_align_dm = prove
 (`(!g s:(A,C,FFI)lab_state.
      lab_state_regs_fupd g (align_dm s) = align_dm (lab_state_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_fp_regs_fupd g (align_dm s) = align_dm (lab_state_fp_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_mem_fupd g (align_dm s) = align_dm (lab_state_mem_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_shared_mem_domain_fupd g (align_dm s) =
      align_dm (lab_state_shared_mem_domain_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_pc_fupd g (align_dm s) = align_dm (lab_state_pc_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_be_fupd g (align_dm s) = align_dm (lab_state_be_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_ffi_fupd g (align_dm s) = align_dm (lab_state_ffi_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_io_regs_fupd g (align_dm s) = align_dm (lab_state_io_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_cc_regs_fupd g (align_dm s) = align_dm (lab_state_cc_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_io_fp_regs_fupd g (align_dm s) = align_dm (lab_state_io_fp_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_cc_fp_regs_fupd g (align_dm s) = align_dm (lab_state_cc_fp_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_code_fupd g (align_dm s) = align_dm (lab_state_code_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_compile_fupd g (align_dm s) = align_dm (lab_state_compile_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_compile_oracle_fupd g (align_dm s) =
      align_dm (lab_state_compile_oracle_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_code_buffer_fupd g (align_dm s) = align_dm (lab_state_code_buffer_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_clock_fupd g (align_dm s) = align_dm (lab_state_clock_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_failed_fupd g (align_dm s) = align_dm (lab_state_failed_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_ptr_reg_fupd g (align_dm s) = align_dm (lab_state_ptr_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_len_reg_fupd g (align_dm s) = align_dm (lab_state_len_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_ptr2_reg_fupd g (align_dm s) = align_dm (lab_state_ptr2_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_len2_reg_fupd g (align_dm s) = align_dm (lab_state_len2_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_link_reg_fupd g (align_dm s) = align_dm (lab_state_link_reg_fupd g s))`,
  REWRITE_TAC[align_dm_def] THEN SIMP[]);;

let LABPROPSAUX_align_dm_mem_domain = prove
 (`lab_state_mem_domain (align_dm s) =
   lab_state_mem_domain (s:(A,C,FFI)lab_state) INTER byte_aligned`,
  REWRITE_TAC[align_dm_def] THEN SIMP[]);;

let LABPROPSAUX_byte_aligned_MOD = prove
 (`good_dimindex(:A) ==>
   (byte_aligned (w:A word) <=> val w MOD (dimindex(:A) DIV 8) = 0)`,
  REWRITE_TAC[good_dimindex_def; byte_aligned_def; aligned_w2n] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MISC3AUX_LOG2_4; MISC3AUX_LOG2_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let LABPROPSAUX_aligned_IN_INTER = prove
 (`good_dimindex(:A) ==>
   (val (w:A word) MOD (dimindex(:A) DIV 8) = 0 /\ w IN dm INTER byte_aligned <=>
    val w MOD (dimindex(:A) DIV 8) = 0 /\ w IN dm)`,
  DISCH_TAC THEN REWRITE_TAC[IN_INTER] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [IN] THEN
  ASM_SIMP_TAC[LABPROPSAUX_byte_aligned_MOD] THEN CONV_TAC TAUT);;

let LABPROPSAUX_byte_align_IN_INTER = prove
 (`byte_align (w:A word) IN dm INTER byte_aligned <=> byte_align w IN dm`,
  REWRITE_TAC[IN_INTER] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [IN] THEN
  REWRITE_TAC[byte_aligned_def; byte_align_def; aligned_align]);;

(* the memory functions look only at byte aligned addresses of the domain *)

let LABPROPSAUX_mem_load_32_INTER = prove
 (`mem_load_32 m (dm INTER byte_aligned) be = mem_load_32 m dm be:A word->(int32)option`,
  REWRITE_TAC[FUN_EQ_THM; mem_load_32_def; LABPROPSAUX_byte_align_IN_INTER]);;

let LABPROPSAUX_mem_store_32_INTER = prove
 (`mem_store_32 m (dm INTER byte_aligned) be =
   mem_store_32 m dm be:A word->int32->(A word->(A)word_loc)option`,
  REWRITE_TAC[FUN_EQ_THM; mem_store_32_def; LABPROPSAUX_byte_align_IN_INTER]);;

let LABPROPSAUX_mem_load_byte_aux_INTER = prove
 (`mem_load_byte_aux m (dm INTER byte_aligned) be =
   mem_load_byte_aux m dm be:A word->(byte)option`,
  REWRITE_TAC[FUN_EQ_THM; mem_load_byte_aux_def; LABPROPSAUX_byte_align_IN_INTER]);;

let LABPROPSAUX_mem_store_byte_aux_INTER = prove
 (`mem_store_byte_aux m (dm INTER byte_aligned) be =
   mem_store_byte_aux m dm be:A word->byte->(A word->(A)word_loc)option`,
  REWRITE_TAC[FUN_EQ_THM; mem_store_byte_aux_def; LABPROPSAUX_byte_align_IN_INTER]);;

let LABPROPSAUX_write_bytearray_INTER = prove
 (`!bs (a:A word) m dm be.
     write_bytearray a bs m (dm INTER byte_aligned) be = write_bytearray a bs m dm be`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[write_bytearray_def; LABPROPSAUX_mem_store_byte_aux_INTER]);;

(* the fields of align_dm s that align_dm_const does not list *)

let LABPROPSAUX_align_dm_fields = prove
 (`lab_state_regs (align_dm s) = lab_state_regs (s:(A,C,FFI)lab_state) /\
   lab_state_fp_regs (align_dm s) = lab_state_fp_regs s /\
   lab_state_cc_regs (align_dm s) = lab_state_cc_regs s /\
   lab_state_cc_fp_regs (align_dm s) = lab_state_cc_fp_regs s`,
  REWRITE_TAC[align_dm_def] THEN SIMP[]);;

let mem_load_align_dm = prove
 (`good_dimindex(:A) ==>
   lab_mem_load n (a:(A)addr) (align_dm s) =
   align_dm (lab_mem_load n a (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN REWRITE_TAC[lab_mem_load_def; addr_align_dm] THEN
  CASES_ON `lab_addr (a:(A)addr) (s:(A,C,FFI)lab_state)` THEN
  CASE_REWRITE_TAC[assert_align_dm] THEN
  REWRITE_TAC[assert_align_dm; upd_reg_align_dm; align_dm_const;
              LABPROPSAUX_align_dm_mem_domain] THEN
  ASM_SIMP_TAC[LABPROPSAUX_aligned_IN_INTER]);;

let mem_load_32_align_dm = prove
 (`mem_load_32 (lab_state_mem s) (lab_state_mem_domain s) be (x:A word) = SOME y ==>
   mem_load_32 (lab_state_mem s) (lab_state_mem_domain (align_dm (s:(A,C,FFI)lab_state)))
     be x = SOME y`,
  REWRITE_TAC[LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_load_32_INTER]);;

let mem_load32_align_dm = prove
 (`good_dimindex(:A) ==>
   mem_load32 n (a:(A)addr) (align_dm s) =
   align_dm (mem_load32 n a (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN
  REWRITE_TAC[mem_load32_def; addr_align_dm; align_dm_const;
              LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_load_32_INTER] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let mem_load_byte_aux_align_dm = prove
 (`mem_load_byte_aux (lab_state_mem s) (lab_state_mem_domain s) be (x:A word) = SOME y ==>
   mem_load_byte_aux (lab_state_mem s)
     (lab_state_mem_domain (align_dm (s:(A,C,FFI)lab_state))) be x = SOME y`,
  REWRITE_TAC[LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_load_byte_aux_INTER]);;

let mem_load_byte_align_dm = prove
 (`good_dimindex(:A) ==>
   mem_load_byte n (a:(A)addr) (align_dm s) =
   align_dm (mem_load_byte n a (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN
  REWRITE_TAC[mem_load_byte_def; addr_align_dm; align_dm_const;
              LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_load_byte_aux_INTER] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let mem_store_align_dm = prove
 (`good_dimindex(:A) ==>
   lab_mem_store n (a:(A)addr) (align_dm s) =
   align_dm (lab_mem_store n a (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN REWRITE_TAC[lab_mem_store_def; addr_align_dm] THEN
  CASES_ON `lab_addr (a:(A)addr) (s:(A,C,FFI)lab_state)` THEN
  CASE_REWRITE_TAC[assert_align_dm] THEN
  REWRITE_TAC[assert_align_dm; upd_mem_align_dm; read_reg_align_dm;
              LABPROPSAUX_align_dm_mem_domain] THEN
  ASM_SIMP_TAC[LABPROPSAUX_aligned_IN_INTER]);;

let mem_store_32_align_dm = prove
 (`mem_store_32 mem (lab_state_mem_domain s) be (x:A word) c = SOME y ==>
   mem_store_32 mem (lab_state_mem_domain (align_dm (s:(A,C,FFI)lab_state))) be x c =
   SOME y`,
  REWRITE_TAC[LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_store_32_INTER]);;

let mem_store32_align_dm = prove
 (`good_dimindex(:A) ==>
   mem_store32 n (a:(A)addr) (align_dm s) =
   align_dm (mem_store32 n a (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN
  REWRITE_TAC[mem_store32_def; addr_align_dm; align_dm_const; read_reg_align_dm;
              LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_store_32_INTER] THEN
  EVERY_CASE_TAC THEN SIMP[LABPROPSAUX_fupd_align_dm]);;

let mem_store_byte_aux_align_dm = prove
 (`mem_store_byte_aux mem (lab_state_mem_domain s) be (x:A word) c = SOME y ==>
   mem_store_byte_aux mem (lab_state_mem_domain (align_dm (s:(A,C,FFI)lab_state))) be x c =
   SOME y`,
  REWRITE_TAC[LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_store_byte_aux_INTER]);;

let mem_store_byte_align_dm = prove
 (`good_dimindex(:A) ==>
   mem_store_byte n (a:(A)addr) (align_dm s) =
   align_dm (mem_store_byte n a (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN
  REWRITE_TAC[mem_store_byte_def; addr_align_dm; align_dm_const; read_reg_align_dm;
              LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_store_byte_aux_INTER] THEN
  EVERY_CASE_TAC THEN SIMP[LABPROPSAUX_fupd_align_dm]);;

let mem_op_align_dm = prove
 (`good_dimindex(:A) ==>
   lab_mem_op m n (a:(A)addr) (align_dm s) =
   align_dm (lab_mem_op m n a (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN CASES_ON `m:memop` THEN
  ASM_SIMP_TAC[lab_mem_op_def; mem_load_align_dm; mem_load32_align_dm;
               mem_load_byte_align_dm; mem_store_align_dm; mem_store32_align_dm;
               mem_store_byte_align_dm; assert_align_dm]);;

let asm_inst_align_dm = prove
 (`good_dimindex(:A) ==>
   asm_inst (i:(A)inst) (align_dm s) = align_dm (asm_inst i (s:(A,C,FFI)lab_state))`,
  DISCH_TAC THEN CASES_ON `i:(A)inst` THEN
  ASM_SIMP_TAC[asm_inst_def; mem_op_align_dm; upd_reg_align_dm; arith_upd_align_dm;
               fp_upd_align_dm]);;

let dec_clock_align_dm = prove
 (`lab_dec_clock (align_dm s) = align_dm (lab_dec_clock (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_dm_def; lab_dec_clock_def] THEN SIMP[]);;

let _ = cake_add_simps [dec_clock_align_dm];;

let inc_pc_align_dm = prove
 (`inc_pc (align_dm s) = align_dm (inc_pc (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_dm_def; inc_pc_def] THEN SIMP[]);;

let _ = cake_add_simps [inc_pc_align_dm];;

let upd_pc_align_dm = prove
 (`lab_upd_pc p (align_dm s) = align_dm (lab_upd_pc p (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_dm_def; lab_upd_pc_def] THEN SIMP[]);;

let _ = cake_add_simps [upd_pc_align_dm];;

let get_pc_value_align_dm = prove
 (`get_pc_value x (align_dm s) = get_pc_value x (s:(A,C,FFI)lab_state)`,
  REWRITE_TAC[get_pc_value_def; align_dm_const]);;

let _ = cake_add_simps [get_pc_value_align_dm];;

let get_ret_Loc_align_dm = prove
 (`get_ret_Loc (align_dm s) = get_ret_Loc (s:(A,C,FFI)lab_state)`,
  REWRITE_TAC[get_ret_Loc_def; align_dm_const]);;

let _ = cake_add_simps [get_ret_Loc_align_dm];;

let read_bytearray_mem_load_byte_aux_align_dm = prove
 (`!y (x:A word).
     read_bytearray x y (mem_load_byte_aux (lab_state_mem s)
       (lab_state_mem_domain (align_dm s)) (lab_state_be s)) =
     read_bytearray x y (mem_load_byte_aux (lab_state_mem s)
       (lab_state_mem_domain (s:(A,C,FFI)lab_state)) (lab_state_be s))`,
  REWRITE_TAC[LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_mem_load_byte_aux_INTER]);;

let _ = cake_add_simps [read_bytearray_mem_load_byte_aux_align_dm];;

let write_bytearray_align_dm = prove
 (`!y (x:A word).
     write_bytearray x y (lab_state_mem s) (lab_state_mem_domain (align_dm s))
       (lab_state_be s) =
     write_bytearray x y (lab_state_mem s)
       (lab_state_mem_domain (s:(A,C,FFI)lab_state)) (lab_state_be s)`,
  REWRITE_TAC[LABPROPSAUX_align_dm_mem_domain; LABPROPSAUX_write_bytearray_INTER]);;

let _ = cake_add_simps [write_bytearray_align_dm];;

let LABPROPSAUX_share_mem_op_align_dm = prove
 (CASE_TERM `share_mem_op m r a (align_dm (s:(A,C,FFI)lab_state)) =
   match share_mem_op m r a s with
     NONE -> NONE
   | SOME (x,t) -> SOME (x,align_dm t)`,
  CASES_ON `m:memop` THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def] THEN
  SIMP[addr_align_dm; align_dm_const; LABPROPSAUX_align_dm_fields] THEN EVERY_CASE_TAC THEN
  SIMP[inc_pc_def; lab_dec_clock_def; LABPROPSAUX_fupd_align_dm; align_dm_const]);;

let share_mem_op_align_dm_simp = prove
 (`(share_mem_op m r a s = NONE ==>
    share_mem_op m r a (align_dm (s:(A,C,FFI)lab_state)) = NONE) /\
   (share_mem_op m r a s = SOME (FFI_final f,s') ==>
    share_mem_op m r a (align_dm s) = SOME (FFI_final f,align_dm s')) /\
   (share_mem_op m r a s = SOME (FFI_return fs l,s') ==>
    share_mem_op m r a (align_dm s) = SOME (FFI_return fs l,align_dm s'))`,
  REWRITE_TAC[LABPROPSAUX_share_mem_op_align_dm] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let _ = cake_add_simps [share_mem_op_align_dm_simp];;

(* evaluate_align_dm, with FST and SND instead of the paired let *)

let LABPROPSAUX_evaluate_align_dm = prove
 (`good_dimindex(:A) ==>
   !s:(A,C,FFI)lab_state.
     (FST (lab_evaluate s),align_dm (SND (lab_evaluate s))) = lab_evaluate (align_dm s)`,
  DISCH_TAC THEN MATCH_MP_TAC LABPROPSAUX_CLOCK_INDUCT THEN GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  ONCE_REWRITE_TAC[lab_evaluate_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> CONV_TAC(CAKE_SIMP_CONV[MATCH_MP asm_inst_align_dm th;
    LABPROPSAUX_align_dm_fields; LABPROPSAUX_share_mem_op_align_dm;
    LABPROPSAUX_fupd_align_dm])) THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[align_dm_const; LABPROPSAUX_fupd_align_dm] THEN
  USE_THEN "ih" MATCH_MP_TAC THEN LABPROPSAUX_CLOCK_LT_TAC);;

let evaluate_align_dm = prove
 (CASE_TERM `good_dimindex(:A) ==>
   !s:(A,C,FFI)lab_state.
     lab_evaluate (align_dm s) =
     let (r,s') = lab_evaluate s in (r,align_dm s')`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP LABPROPSAUX_evaluate_align_dm) THEN
  GEN_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  CASES_ON `lab_evaluate (s:(A,C,FFI)lab_state)` THEN CASE_REWRITE_TAC[]);;

let LABPROPSAUX_semantics_align_dm = prove
 (`good_dimindex(:A) ==>
   lab_semantics (align_dm s) = lab_semantics (s:(A,C,FFI)lab_state)`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP LABPROPSAUX_evaluate_align_dm) THEN
  REWRITE_TAC[lab_semantics_def; GSYM align_dm_with_clock] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[FST; SND; align_dm_const; PAIR_EQ] THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[PAIR; FST; SND; align_dm_const]);;

let implements_align_dm = prove
 (`good_dimindex(:A) ==>
   implements' T {lab_semantics (s:(A,C,FFI)lab_state)} {lab_semantics (align_dm s)}`,
  SIMP_TAC[LABPROPSAUX_semantics_align_dm; implements'_def;
           extend_with_resource_limit'_def; SUBSET_REFL]);;

(* align_sdm *)

let align_sdm_def = cake_def
  `align_sdm (s:(A,C,FFI)lab_state) =
     lab_state_shared_mem_domain_fupd
       (K (lab_state_shared_mem_domain s INTER byte_aligned)) s`;;

let align_sdm_const = prove
 (`lab_state_clock (align_sdm s) = lab_state_clock (s:(A,C,FFI)lab_state) /\
   lab_state_pc (align_sdm s) = lab_state_pc s /\
   lab_state_code (align_sdm s) = lab_state_code s /\
   lab_state_mem (align_sdm s) = lab_state_mem s /\
   lab_state_mem_domain (align_sdm s) = lab_state_mem_domain s /\
   lab_state_be (align_sdm s) = lab_state_be s /\
   lab_state_len_reg (align_sdm s) = lab_state_len_reg s /\
   lab_state_link_reg (align_sdm s) = lab_state_link_reg s /\
   lab_state_ptr_reg (align_sdm s) = lab_state_ptr_reg s /\
   lab_state_ptr2_reg (align_sdm s) = lab_state_ptr2_reg s /\
   lab_state_len2_reg (align_sdm s) = lab_state_len2_reg s /\
   lab_state_io_regs (align_sdm s) = lab_state_io_regs s /\
   lab_state_io_fp_regs (align_sdm s) = lab_state_io_fp_regs s /\
   lab_state_code_buffer (align_sdm s) = lab_state_code_buffer s /\
   lab_state_compile (align_sdm s) = lab_state_compile s /\
   lab_state_compile_oracle (align_sdm s) = lab_state_compile_oracle s /\
   lab_state_ffi (align_sdm s) = lab_state_ffi s /\
   lab_state_failed (align_sdm s) = lab_state_failed s`,
  REWRITE_TAC[align_sdm_def] THEN SIMP[]);;

let _ = cake_add_simps [align_sdm_const];;

let align_sdm_with_clock = prove
 (`align_sdm (lab_state_clock_fupd (K k) s) =
   lab_state_clock_fupd (K k) (align_sdm (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_sdm_def] THEN SIMP[]);;

let asm_fetch_align_sdm = prove
 (`asm_fetch (align_sdm s) = asm_fetch (s:(A,C,FFI)lab_state)`,
  REWRITE_TAC[asm_fetch_def] THEN SIMP[]);;

let _ = cake_add_simps [asm_fetch_align_sdm];;

(* HOL4: read_reg n (align_sdm s) = read_reg n s *)

let read_reg_align_sdm = prove
 (`lab_state_regs (align_sdm s) n = lab_state_regs (s:(A,C,FFI)lab_state) n`,
  REWRITE_TAC[align_sdm_def] THEN SIMP[]);;

let _ = cake_add_simps [read_reg_align_sdm];;

let upd_reg_align_sdm = prove
 (`lab_upd_reg x y (align_sdm s) = align_sdm (lab_upd_reg x y (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_sdm_def; lab_upd_reg_def] THEN SIMP[]);;

let _ = cake_add_simps [upd_reg_align_sdm];;

let upd_mem_align_sdm = prove
 (`lab_upd_mem x y (align_sdm s) = align_sdm (lab_upd_mem x y (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_sdm_def; lab_upd_mem_def] THEN SIMP[]);;

let _ = cake_add_simps [upd_mem_align_sdm];;

let binop_upd_align_sdm = prove
 (`lab_binop_upd x y z w (align_sdm s) =
   align_sdm (lab_binop_upd x y z w (s:(A,C,FFI)lab_state))`,
  CASES_ON `y:binop` THEN SIMP[lab_binop_upd_def]);;

let _ = cake_add_simps [binop_upd_align_sdm];;

let reg_imm_align_sdm = prove
 (`lab_reg_imm r (align_sdm s) = lab_reg_imm r (s:(A,C,FFI)lab_state)`,
  CASES_ON `r:(A)reg_imm` THEN SIMP[lab_reg_imm_def]);;

let _ = cake_add_simps [reg_imm_align_sdm];;

let assert_align_sdm = prove
 (`lab_assert b (align_sdm s) = align_sdm (lab_assert b (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_sdm_def; lab_assert_def] THEN SIMP[]);;

let _ = cake_add_simps [assert_align_sdm];;

let arith_upd_align_sdm = prove
 (`lab_arith_upd x (align_sdm s) = align_sdm (lab_arith_upd x (s:(A,C,FFI)lab_state))`,
  CASES_ON `x:(A)asm_arith` THEN SIMP[lab_arith_upd_def] THEN EVERY_CASE_TAC THEN
  SIMP[]);;

let _ = cake_add_simps [arith_upd_align_sdm];;

let fp_upd_align_sdm = prove
 (`lab_fp_upd f (align_sdm s) = align_sdm (lab_fp_upd f (s:(A,C,FFI)lab_state))`,
  CASES_ON `f:fp` THEN
  SIMP[lab_fp_upd_def; lab_upd_fp_reg_def; lab_read_fp_reg_def; lab_upd_reg_def;
       lab_assert_def; align_sdm_def] THEN
  EVERY_CASE_TAC THEN
  SIMP[lab_upd_fp_reg_def; lab_read_fp_reg_def; lab_upd_reg_def; lab_assert_def]);;

let _ = cake_add_simps [fp_upd_align_sdm];;

let addr_align_sdm = prove
 (`lab_addr a (align_sdm s) = lab_addr a (s:(A,C,FFI)lab_state)`,
  CASES_ON `a:(A)addr` THEN SIMP[lab_addr_def]);;

let _ = cake_add_simps [addr_align_sdm];;

(* align_sdm s changes only the shared_mem_domain field, to its byte        *)
(* aligned part                                                              *)

let LABPROPSAUX_fupd_align_sdm = prove
 (`(!g s:(A,C,FFI)lab_state.
      lab_state_regs_fupd g (align_sdm s) = align_sdm (lab_state_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_fp_regs_fupd g (align_sdm s) = align_sdm (lab_state_fp_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_mem_fupd g (align_sdm s) = align_sdm (lab_state_mem_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_mem_domain_fupd g (align_sdm s) = align_sdm (lab_state_mem_domain_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_pc_fupd g (align_sdm s) = align_sdm (lab_state_pc_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_be_fupd g (align_sdm s) = align_sdm (lab_state_be_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_ffi_fupd g (align_sdm s) = align_sdm (lab_state_ffi_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_io_regs_fupd g (align_sdm s) = align_sdm (lab_state_io_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_cc_regs_fupd g (align_sdm s) = align_sdm (lab_state_cc_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_io_fp_regs_fupd g (align_sdm s) = align_sdm (lab_state_io_fp_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_cc_fp_regs_fupd g (align_sdm s) = align_sdm (lab_state_cc_fp_regs_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_code_fupd g (align_sdm s) = align_sdm (lab_state_code_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_compile_fupd g (align_sdm s) = align_sdm (lab_state_compile_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_compile_oracle_fupd g (align_sdm s) =
      align_sdm (lab_state_compile_oracle_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_code_buffer_fupd g (align_sdm s) = align_sdm (lab_state_code_buffer_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_clock_fupd g (align_sdm s) = align_sdm (lab_state_clock_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_failed_fupd g (align_sdm s) = align_sdm (lab_state_failed_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_ptr_reg_fupd g (align_sdm s) = align_sdm (lab_state_ptr_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_len_reg_fupd g (align_sdm s) = align_sdm (lab_state_len_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_ptr2_reg_fupd g (align_sdm s) = align_sdm (lab_state_ptr2_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_len2_reg_fupd g (align_sdm s) = align_sdm (lab_state_len2_reg_fupd g s)) /\
   (!g s:(A,C,FFI)lab_state.
      lab_state_link_reg_fupd g (align_sdm s) = align_sdm (lab_state_link_reg_fupd g s))`,
  REWRITE_TAC[align_sdm_def] THEN SIMP[]);;

let LABPROPSAUX_align_sdm_fields = prove
 (`lab_state_regs (align_sdm s) = lab_state_regs (s:(A,C,FFI)lab_state) /\
   lab_state_fp_regs (align_sdm s) = lab_state_fp_regs s /\
   lab_state_cc_regs (align_sdm s) = lab_state_cc_regs s /\
   lab_state_cc_fp_regs (align_sdm s) = lab_state_cc_fp_regs s /\
   lab_state_shared_mem_domain (align_sdm s) =
   lab_state_shared_mem_domain s INTER byte_aligned`,
  REWRITE_TAC[align_sdm_def] THEN SIMP[]);;

let mem_load_align_sdm = prove
 (`lab_mem_load n (a:(A)addr) (align_sdm s) =
   align_sdm (lab_mem_load n a (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[lab_mem_load_def; addr_align_sdm; align_sdm_const] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let mem_load32_align_sdm = prove
 (`mem_load32 n (a:(A)addr) (align_sdm s) =
   align_sdm (mem_load32 n a (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[mem_load32_def; addr_align_sdm; align_sdm_const] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let mem_load_byte_align_sdm = prove
 (`mem_load_byte n (a:(A)addr) (align_sdm s) =
   align_sdm (mem_load_byte n a (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[mem_load_byte_def; addr_align_sdm; align_sdm_const] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let mem_store_align_sdm = prove
 (`lab_mem_store n (a:(A)addr) (align_sdm s) =
   align_sdm (lab_mem_store n a (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[lab_mem_store_def; addr_align_sdm; align_sdm_const; read_reg_align_sdm] THEN
  EVERY_CASE_TAC THEN SIMP[]);;

let mem_store32_align_sdm = prove
 (`mem_store32 n (a:(A)addr) (align_sdm s) =
   align_sdm (mem_store32 n a (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[mem_store32_def; addr_align_sdm; align_sdm_const; read_reg_align_sdm] THEN
  EVERY_CASE_TAC THEN SIMP[LABPROPSAUX_fupd_align_sdm]);;

let mem_store_byte_align_sdm = prove
 (`mem_store_byte n (a:(A)addr) (align_sdm s) =
   align_sdm (mem_store_byte n a (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[mem_store_byte_def; addr_align_sdm; align_sdm_const; read_reg_align_sdm] THEN
  EVERY_CASE_TAC THEN SIMP[LABPROPSAUX_fupd_align_sdm]);;

let mem_op_align_sdm = prove
 (`lab_mem_op m n (a:(A)addr) (align_sdm s) =
   align_sdm (lab_mem_op m n a (s:(A,C,FFI)lab_state))`,
  CASES_ON `m:memop` THEN
  REWRITE_TAC[lab_mem_op_def; mem_load_align_sdm; mem_load32_align_sdm;
              mem_load_byte_align_sdm; mem_store_align_sdm; mem_store32_align_sdm;
              mem_store_byte_align_sdm; assert_align_sdm]);;

let asm_inst_align_sdm = prove
 (`asm_inst (i:(A)inst) (align_sdm s) = align_sdm (asm_inst i (s:(A,C,FFI)lab_state))`,
  CASES_ON `i:(A)inst` THEN
  REWRITE_TAC[asm_inst_def; mem_op_align_sdm; upd_reg_align_sdm; arith_upd_align_sdm;
              fp_upd_align_sdm]);;

let dec_clock_align_sdm = prove
 (`lab_dec_clock (align_sdm s) = align_sdm (lab_dec_clock (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_sdm_def; lab_dec_clock_def] THEN SIMP[]);;

let _ = cake_add_simps [dec_clock_align_sdm];;

let inc_pc_align_sdm = prove
 (`inc_pc (align_sdm s) = align_sdm (inc_pc (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_sdm_def; inc_pc_def] THEN SIMP[]);;

let _ = cake_add_simps [inc_pc_align_sdm];;

let upd_pc_align_sdm = prove
 (`lab_upd_pc p (align_sdm s) = align_sdm (lab_upd_pc p (s:(A,C,FFI)lab_state))`,
  REWRITE_TAC[align_sdm_def; lab_upd_pc_def] THEN SIMP[]);;

let _ = cake_add_simps [upd_pc_align_sdm];;

let get_pc_value_align_sdm = prove
 (`get_pc_value x (align_sdm s) = get_pc_value x (s:(A,C,FFI)lab_state)`,
  REWRITE_TAC[get_pc_value_def; align_sdm_const]);;

let _ = cake_add_simps [get_pc_value_align_sdm];;

let get_ret_Loc_align_sdm = prove
 (`get_ret_Loc (align_sdm s) = get_ret_Loc (s:(A,C,FFI)lab_state)`,
  REWRITE_TAC[get_ret_Loc_def; align_sdm_const]);;

let _ = cake_add_simps [get_ret_Loc_align_sdm];;

let read_bytearray_mem_load_byte_aux_align_sdm = prove
 (`!y (x:A word).
     read_bytearray x y (mem_load_byte_aux (lab_state_mem s)
       (lab_state_mem_domain (align_sdm s)) (lab_state_be s)) =
     read_bytearray x y (mem_load_byte_aux (lab_state_mem s)
       (lab_state_mem_domain (s:(A,C,FFI)lab_state)) (lab_state_be s))`,
  REWRITE_TAC[align_sdm_const]);;

let _ = cake_add_simps [read_bytearray_mem_load_byte_aux_align_sdm];;

let write_bytearray_align_sdm = prove
 (`!y (x:A word).
     write_bytearray x y (lab_state_mem s) (lab_state_mem_domain (align_sdm s))
       (lab_state_be s) =
     write_bytearray x y (lab_state_mem s)
       (lab_state_mem_domain (s:(A,C,FFI)lab_state)) (lab_state_be s)`,
  REWRITE_TAC[align_sdm_const]);;

let _ = cake_add_simps [write_bytearray_align_sdm];;

let align_sdm_aligned = prove
 (`good_dimindex(:A) ==>
   ((x:A word) IN lab_state_shared_mem_domain s /\ val x MOD (dimindex(:A) DIV 8) = 0 <=>
    x IN lab_state_shared_mem_domain (align_sdm (s:(A,C,FFI)lab_state)))`,
  DISCH_TAC THEN REWRITE_TAC[LABPROPSAUX_align_sdm_fields; IN_INTER] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [IN] THEN
  ASM_SIMP_TAC[LABPROPSAUX_byte_aligned_MOD]);;

(* share_mem_load and share_mem_store of align_sdm s *)

let LABPROPSAUX_share_mem_load_align_sdm = prove
 (CASE_TERM `good_dimindex(:A) ==>
   share_mem_load r (ad:(A)addr) (align_sdm (s:(A,C,FFI)lab_state)) n =
   match share_mem_load r ad s n with
     NONE -> NONE
   | SOME (x,t) -> SOME (x,align_sdm t)`,
  DISCH_TAC THEN REWRITE_TAC[share_mem_load_def] THEN
  ASM_SIMP_TAC[addr_align_sdm; align_sdm_const; LABPROPSAUX_align_sdm_fields;
               LABPROPSAUX_aligned_IN_INTER; LABPROPSAUX_byte_align_IN_INTER] THEN
  EVERY_CASE_TAC THEN SIMP[LABPROPSAUX_fupd_align_sdm; align_sdm_const]);;

let LABPROPSAUX_share_mem_store_align_sdm = prove
 (CASE_TERM `good_dimindex(:A) ==>
   share_mem_store r (ad:(A)addr) (align_sdm (s:(A,C,FFI)lab_state)) n =
   match share_mem_store r ad s n with
     NONE -> NONE
   | SOME (x,t) -> SOME (x,align_sdm t)`,
  DISCH_TAC THEN REWRITE_TAC[share_mem_store_def] THEN
  ASM_SIMP_TAC[addr_align_sdm; align_sdm_const; LABPROPSAUX_align_sdm_fields;
               LABPROPSAUX_aligned_IN_INTER; LABPROPSAUX_byte_align_IN_INTER] THEN
  EVERY_CASE_TAC THEN
  SIMP[inc_pc_def; lab_dec_clock_def; LABPROPSAUX_fupd_align_sdm; align_sdm_const]);;

let share_mem_load_align_sdm = prove
 (`good_dimindex(:A) ==>
   (share_mem_load r (ad:(A)addr) (align_sdm s) n = NONE <=>
    share_mem_load r ad (s:(A,C,FFI)lab_state) n = NONE) /\
   (share_mem_load r ad s n = SOME (res,s') ==>
    share_mem_load r ad (align_sdm s) n = SOME (res,align_sdm s'))`,
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LABPROPSAUX_share_mem_load_align_sdm th]) THEN
  CONJ_TAC THENL
   [CASES_ON `share_mem_load r (ad:(A)addr) (s:(A,C,FFI)lab_state) n` THEN
    CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN CASE_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]);;

let share_mem_store_align_sdm = prove
 (`good_dimindex(:A) ==>
   (share_mem_store r (ad:(A)addr) (align_sdm s) n = NONE <=>
    share_mem_store r ad (s:(A,C,FFI)lab_state) n = NONE) /\
   (share_mem_store r ad s n = SOME (res,s') ==>
    share_mem_store r ad (align_sdm s) n = SOME (res,align_sdm s'))`,
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LABPROPSAUX_share_mem_store_align_sdm th]) THEN
  CONJ_TAC THENL
   [CASES_ON `share_mem_store r (ad:(A)addr) (s:(A,C,FFI)lab_state) n` THEN
    CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN CASE_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]);;

let LABPROPSAUX_share_mem_op_align_sdm = prove
 (CASE_TERM `good_dimindex(:A) ==>
   share_mem_op m r (a:(A)addr) (align_sdm (s:(A,C,FFI)lab_state)) =
   match share_mem_op m r a s with
     NONE -> NONE
   | SOME (x,t) -> SOME (x,align_sdm t)`,
  DISCH_TAC THEN CASES_ON `m:memop` THEN REWRITE_TAC[share_mem_op_def] THEN
  ASM_SIMP_TAC[LABPROPSAUX_share_mem_load_align_sdm;
               LABPROPSAUX_share_mem_store_align_sdm]);;

(* HOL4 [simp]: not registered, its first conjunct is a looping rewrite *)

let share_mem_op_align_sdm_simp = prove
 (`good_dimindex(:A) ==>
   (share_mem_op m r (a:(A)addr) s = NONE <=>
    share_mem_op m r a (align_sdm (s:(A,C,FFI)lab_state)) = NONE) /\
   (share_mem_op m r a s = SOME (res,s') ==>
    share_mem_op m r a (align_sdm s) = SOME (res,align_sdm s'))`,
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LABPROPSAUX_share_mem_op_align_sdm th]) THEN
  CONJ_TAC THENL
   [CASES_ON `share_mem_op m r (a:(A)addr) (s:(A,C,FFI)lab_state)` THEN
    CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN CASE_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]);;

(* evaluate_align_sdm, with FST and SND instead of the paired let *)

let LABPROPSAUX_evaluate_align_sdm = prove
 (`good_dimindex(:A) ==>
   !s:(A,C,FFI)lab_state.
     (FST (lab_evaluate s),align_sdm (SND (lab_evaluate s))) =
     lab_evaluate (align_sdm s)`,
  DISCH_TAC THEN MATCH_MP_TAC LABPROPSAUX_CLOCK_INDUCT THEN GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  ONCE_REWRITE_TAC[lab_evaluate_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th -> CONV_TAC(CAKE_SIMP_CONV[asm_inst_align_sdm;
    LABPROPSAUX_align_sdm_fields; MATCH_MP LABPROPSAUX_share_mem_op_align_sdm th;
    LABPROPSAUX_fupd_align_sdm])) THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[align_sdm_const; LABPROPSAUX_fupd_align_sdm] THEN
  USE_THEN "ih" MATCH_MP_TAC THEN LABPROPSAUX_CLOCK_LT_TAC);;

let evaluate_align_sdm = prove
 (CASE_TERM `good_dimindex(:A) ==>
   !s:(A,C,FFI)lab_state.
     lab_evaluate (align_sdm s) =
     let (r,s') = lab_evaluate s in (r,align_sdm s')`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP LABPROPSAUX_evaluate_align_sdm) THEN
  GEN_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  CASES_ON `lab_evaluate (s:(A,C,FFI)lab_state)` THEN CASE_REWRITE_TAC[]);;

let LABPROPSAUX_semantics_align_sdm = prove
 (`good_dimindex(:A) ==>
   lab_semantics (align_sdm s) = lab_semantics (s:(A,C,FFI)lab_state)`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP LABPROPSAUX_evaluate_align_sdm) THEN
  REWRITE_TAC[lab_semantics_def; GSYM align_sdm_with_clock] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[FST; SND; align_sdm_const; PAIR_EQ] THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[PAIR; FST; SND; align_sdm_const]);;

let implements_align_sdm = prove
 (`good_dimindex(:A) ==>
   implements' T {lab_semantics (s:(A,C,FFI)lab_state)} {lab_semantics (align_sdm s)}`,
  SIMP_TAC[LABPROPSAUX_semantics_align_sdm; implements'_def;
           extend_with_resource_limit'_def; SUBSET_REFL]);;

(* asm_ok checks coming into lab_to_target *)

let line_ok_pre_def = cake_def
  `(line_ok_pre (c:(A)asm_config) (Asm b bytes l) <=> asm_ok (cbw_to_asm b) c) /\
   (line_ok_pre c (_:(A)line) <=> T)`;;

let sec_ok_pre_def = cake_def
  `sec_ok_pre (c:(A)asm_config) (Section k ls) <=> ALL (line_ok_pre c) ls`;;

let _ = cake_add_simps [sec_ok_pre_def];;

(* HOL4: Overload all_enc_ok_pre = \c ls. EVERY (sec_ok_pre c) ls        *)
(* (written out where used: ALL (sec_ok_pre c) ls)                        *)

(* invariant: labels have correct section number and are non-zero *)

let sec_label_ok_def = cake_def
  `(sec_label_ok k (lab_Label l1 l2 len:(A)line) <=> l1 = k /\ ~(l2 = 0)) /\
   (sec_label_ok _ (_:(A)line) <=> T)`;;

let _ = cake_add_simps [sec_label_ok_def];;

let sec_labels_ok_def = cake_def
  `sec_labels_ok (Section k ls:(A)sec) <=> ALL (sec_label_ok k) ls`;;

let _ = cake_add_simps [sec_labels_ok_def];;

let sec_label_ok_extract_labels = prove
 (`ALL (sec_label_ok n1) (lines:((A)line)list) /\
   MEM (n1',n2) (lab_extract_labels lines) ==>
   n1' = n1 /\ ~(n2 = 0)`,
  SPEC_TAC(`lines:((A)line)list`,`lines:((A)line)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; MEM; lab_extract_labels_def] THEN
  CASES_ON `h:(A)line` THEN
  REWRITE_TAC[lab_extract_labels_def; sec_label_ok_def; MEM; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let EVERY_sec_label_ok = prove
 (`ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) (lab_extract_labels l) <=>
   ALL (sec_label_ok n) (l:((A)line)list)`,
  SPEC_TAC(`l:((A)line)list`,`l:((A)line)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; lab_extract_labels_def] THEN
  CASES_ON `h:(A)line` THEN
  ASM_REWRITE_TAC[ALL; lab_extract_labels_def; sec_label_ok_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let line_get_code_labels_extract_labels = prove
 (`!l:((A)line)list.
     UNIONS (IMAGE line_get_code_labels (set_of_list l)) =
     IMAGE SND (set_of_list (lab_extract_labels l))`,
  MATCH_MP_TAC lab_extract_labels_ind THEN
  REWRITE_TAC[lab_extract_labels_def; set_of_list; IMAGE_CLAUSES; UNIONS_INSERT;
              UNIONS_0; line_get_code_labels_def; UNION_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let get_code_labels_extract_labels = prove
 (`!code:((A)sec)list.
     ALL sec_labels_ok code ==>
     lab_get_code_labels code =
     IMAGE (\s. (Section_num s,0)) (set_of_list code) UNION
     set_of_list (FLAT (MAP (lab_extract_labels o Section_lines) code))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[get_code_labels_nil; set_of_list; IMAGE_CLAUSES; MAP; FLAT; UNION_EMPTY];
    ALL_TAC] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[ALL; sec_labels_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[get_code_labels_cons; sec_get_code_labels_def; set_of_list;
                  IMAGE_CLAUSES; MAP; FLAT; o_THM; lab_Section_num_def;
                  lab_Section_lines_def; SET_OF_LIST_APPEND;
                  line_get_code_labels_extract_labels] THEN
  SUBGOAL_THEN
   `IMAGE (\n2. (a0,n2)) (IMAGE SND (set_of_list (lab_extract_labels a1))) =
    set_of_list (lab_extract_labels (a1:((A)line)list))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SET_OF_LIST; FORALL_PAIR_THM; EXISTS_PAIR_THM;
                PAIR_EQ] THEN
    ASM_MESON_TAC[sec_label_ok_extract_labels];
    SET_TAC[]]);;

(* HOL4: no_install_def *)

let lab_no_install_def = cake_def
  `lab_no_install (code:((A)sec)list) <=>
     !p w bytes l. ~(asm_fetch_aux p code = SOME (LabAsm lab_Install w bytes l))`;;

let no_share_mem_inst_def = cake_def
  `no_share_mem_inst (code:((A)sec)list) <=>
     !p op re a inst len.
       ~(asm_fetch_aux p code = SOME (Asm (ShareMem op re a) inst len))`;;
