(* ========================================================================= *)
(* lab_to_targetProof_p2: part 2 of 4 (HOL4 lines 2934-6168) of              *)
(* lab_to_targetProof, port of HOL4                                          *)
(* compiler/backend/proofs/lab_to_targetProofScript.sml (CakeML v3479).      *)
(* Correctness proof for lab_to_target: syntactic properties of             *)
(* remove_labels (encodings, lengths, labels, padding).                      *)
(* ========================================================================= *)

needs "compiler/backend/proofs/lab_to_targetProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 2934-6168 ===== *)

(* lengths of enc_with_nop encodings are multiples of the code alignment *)
let LTTP2AUX_enc_with_nop_MOD = prove
 (`!(c:(A)asm_config) i bytes.
     enc_ok c /\ enc_with_nop (asm_config_encode c) i bytes
     ==> LENGTH bytes MOD 2 EXP asm_config_code_alignment c = 0`,
  REWRITE_TAC[enc_ok_def; enc_with_nop_thm] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_FLAT_REPLICATE; MOD_MULT_ADD] THEN
  ASM_MESON_TAC[]);;

let LTTP2AUX_line_length_MOD_0 = prove
 (`!(c:(A)asm_config) p labs ffi_names h.
     enc_ok c /\ line_ok c labs ffi_names p h
     ==> line_length h MOD 2 EXP asm_config_code_alignment c = 0`,
  REPEAT GEN_TAC THEN CASES_ON `h:(A)line` THENL
   [REWRITE_TAC[line_ok_def; line_length_def] THEN SIMP_TAC[MOD_0];
    REWRITE_TAC[line_ok_def; line_length_def] THEN
    MESON_TAC[LTTP2AUX_enc_with_nop_MOD];
    CASES_ON `a0:(A)asm_with_lab` THEN
    REWRITE_TAC[line_ok_def; line_length_def; get_label_def; LET_DEF; LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN
    ASM_MESON_TAC[LTTP2AUX_enc_with_nop_MOD]]);;

(* HOL4 line 2934 *)
let line_length_MOD_0 = prove
 (`!(mc_conf:(A,B,C)machine_config) p labs ffi_names h.
     encoder_correct (machine_config_target mc_conf) /\
     (~EVEN p ==> asm_config_code_alignment (target_config (machine_config_target mc_conf)) = 0) /\
     line_ok (target_config (machine_config_target mc_conf)) labs ffi_names p h
     ==> line_length h MOD
           2 EXP asm_config_code_alignment (target_config (machine_config_target mc_conf)) = 0`,
  REWRITE_TAC[encoder_correct_def; target_ok_def] THEN
  MESON_TAC[LTTP2AUX_line_length_MOD_0]);;

(* HOL4 line 2949 *)
let pos_val_MOD_0_lemma = prove
 (`!(mc_conf:(A,B,C)machine_config).
     0 MOD 2 EXP asm_config_code_alignment (target_config (machine_config_target mc_conf)) = 0`,
  REWRITE_TAC[MOD_0]);;

(* the Q.prove of HOL4's pos_val_MOD_0, before its Q.SPECL [x,0,y] *)
let LTTP2AUX_pos_val_MOD_0 = prove
 (`!x pos (code2:((A)sec)list) (c:(A)asm_config) labs ffi_names.
     enc_ok c /\
     (has_odd_inst code2 ==> asm_config_code_alignment c = 0) /\
     (~EVEN pos ==> asm_config_code_alignment c = 0) /\
     pos MOD 2 EXP asm_config_code_alignment c = 0 /\
     all_enc_ok c labs ffi_names pos code2
     ==> pos_val x pos code2 MOD 2 EXP asm_config_code_alignment c = 0`,
  MATCH_MP_TAC pos_val_ind THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[pos_val_def];
    REWRITE_TAC[pos_val_def; all_enc_ok_def; has_odd_inst_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[pos_val_def; all_enc_ok_def; has_odd_inst_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(pos + line_length (y:(A)line)) MOD 2 EXP asm_config_code_alignment (c:(A)asm_config) = 0 /\
      (~EVEN (pos + line_length y) ==> asm_config_code_alignment c = 0)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN
         `line_length (y:(A)line) MOD 2 EXP asm_config_code_alignment (c:(A)asm_config) = 0`
        ASSUME_TAC THENL
         [MATCH_MP_TAC LTTP2AUX_line_length_MOD_0 THEN ASM_MESON_TAC[];
          ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[ADD_CLAUSES; MOD_0]];
        REWRITE_TAC[EVEN_ADD] THEN ASM_MESON_TAC[]];
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(* HOL4 line 2955: val pos_val_MOD_0 = Q.prove(...) |> Q.SPECL [x,0,y] *)
(* |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO] |> SIMP_RULE std_ss              *)
(* [pos_val_MOD_0_lemma] |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] (a  *)
(* derived theorem; the hypotheses about pos = 0 are discharged)             *)
let pos_val_MOD_0 = prove
 (`!x y (mc_conf:(A,B,C)machine_config) labs ffi_names.
     encoder_correct (machine_config_target mc_conf) /\
     (has_odd_inst y ==>
      asm_config_code_alignment (target_config (machine_config_target mc_conf)) = 0) /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 y
     ==> pos_val x 0 y MOD
           2 EXP asm_config_code_alignment (target_config (machine_config_target mc_conf)) = 0`,
  REWRITE_TAC[encoder_correct_def; target_ok_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LTTP2AUX_pos_val_MOD_0 THEN ASM_REWRITE_TAC[EVEN; MOD_0] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 2981: val IMP_IMP2 = METIS_PROVE [] a /\ (a /\ b ==> c) ==>  *)
(* ((a ==> b) ==> c) (a propositional tautology for the proofs)            *)
let lab_to_targetProof_IMP_IMP2 = prove
 (`!a b c. a /\ (a /\ b ==> c) ==> ((a ==> b) ==> c)`,
  REPEAT GEN_TAC THEN CONV_TAC TAUT);;

(* HOL4 line 2983 *)
let EVEN_add_AND = prove
 (`!(p:A word) x.
     word_and (word 1) p = word 0 /\ EVEN x
     ==> word_and (word 1) (word_add p (word x)) = word 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_AND_1; BIT_LSB; ODD_VAL_WORD_ADD; ODD_VAL_WORD; GSYM NOT_EVEN] THEN
  MAP_EVERY BOOL_CASES_TAC [`EVEN (val (p:A word))`; `EVEN x`] THEN REWRITE_TAC[]);;

(* the facts of state_rel that word_cmp_lemma uses *)
let LTTP2AUX_state_rel_regs = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
         (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
         word_and (word 1) p = word 0`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 3004 (for s1 wordSem's word_cmp of word_locs, as labSem uses,  *)
(* the Overload read_reg r s1 = s1.regs r and labSem's reg_imm; for t1 the  *)
(* asm ones)                                                                  *)
let word_cmp_lemma = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 cmp rr ri x.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     wl_word_cmp cmp (lab_state_regs s1 rr) (lab_reg_imm ri s1) = SOME x
     ==> x = asm_word_cmp cmp (read_reg rr t1) (asm_reg_imm ri t1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    let regs,rest = CONJ_PAIR(MATCH_MP LTTP2AUX_state_rel_regs th) in
    MP_TAC(SPEC `rr:num` regs) THEN ASSUME_TAC regs THEN STRIP_ASSUME_TAC rest) MP_TAC) THEN
  REWRITE_TAC[read_reg_def] THEN
  SUBGOAL_THEN `word_loc_val p labs (lab_reg_imm ri (s1:(A,lab_to_target_config,FFI)lab_state)) =
                SOME (asm_reg_imm ri (t1:(A)asm_state))` MP_TAC THENL
   [CASES_ON `ri:(A)reg_imm` THEN
    ASM_REWRITE_TAC[lab_reg_imm_def; asm_reg_imm_def; read_reg_def; word_loc_val_def];
    ALL_TAC] THEN
  SPEC_TAC(`lab_reg_imm ri (s1:(A,lab_to_target_config,FFI)lab_state)`,`b:(A)word_loc`) THEN
  SPEC_TAC(`lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) rr`,`a:(A)word_loc`) THEN
  SPEC_TAC(`asm_reg_imm ri (t1:(A)asm_state)`,`w2:A word`) THEN
  SPEC_TAC(`asm_state_regs (t1:(A)asm_state) rr`,`w1:A word`) THEN
  REPEAT GEN_TAC THEN
  CASES_ON `a:(A)word_loc` THEN CASES_ON `b:(A)word_loc` THEN CASES_ON `cmp:cmp` THEN
  REWRITE_TAC[word_loc_val_def; wl_word_cmp_def; asm_word_cmp_def; option_INJ;
              option_DISTINCT] THEN
  TRY (REPEAT (DISCH_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_CASES_TAC `a1 = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `(a:A word) = word 1` THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`a0:num`; `0`]
    (ASSUME `!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x`)) THEN
  CASES_ON `lab_lookup a0 0 labs` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_SIMP_TAC[EVEN_add_AND]);;

(* HOL4 line 3027 (rebound at HOL4 line 3052) *)
let list_add_if_fresh_simp = prove
 (`!n (s:A) l.
     list_add_if_fresh s l =
     if find_index s l n = NONE then APPEND l [s] else l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM find_index_NOT_MEM] THEN
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_add_if_fresh_def; MEM; APPEND] THEN
  ASM_CASES_TAC `(s:A) = h` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

(* HOL4 line 3044 *)
let list_add_if_fresh_thm = prove
 (`!(s:A) l. list_add_if_fresh s l = if MEM s l then l else APPEND l [s]`,
  REWRITE_TAC[ISPEC `0` list_add_if_fresh_simp; GSYM find_index_NOT_MEM; COND_SWAP]);;

(* HOL4 line 3052: val list_add_if_fresh_simp = Q.SPECL [n,s]          *)
(* list_add_if_fresh_simp (rebinds it; the same statement, quantified)       *)
let list_add_if_fresh_simp = prove
 (`!n (s:A) l.
     list_add_if_fresh s l =
     if find_index s l n = NONE then APPEND l [s] else l`,
  MATCH_ACCEPT_TAC list_add_if_fresh_simp);;

(* HOL4 line 3054 *)
let find_index_append = prove
 (CASE_TERM `!n (s:A) l l'.
     find_index s (APPEND l l') n =
     (match find_index s l n with
        NONE -> find_index s l' (n + LENGTH l)
      | SOME i -> SOME i)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; find_index_def; LENGTH; ADD_CLAUSES] THEN CASE_REWRITE_TAC[] THEN
  GEN_TAC THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + m = SUC (n + m)`]);;

let LTTP2AUX_has_io_name_MEM = prove
 (`!s (l:((A)sec)list). has_io_name s l ==> MEM (ExtCall s) (find_ffi_names l)`,
  MATCH_MP_TAC has_io_name_ind THEN
  REWRITE_TAC[has_io_name_def; find_ffi_names_def; MEM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASES_ON `y:(A)line` THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `a0:(A)asm_with_lab` THEN CASE_REWRITE_TAC[] THEN
  SIMP[list_add_if_fresh_thm] THEN COND_CASES_TAC THEN SIMP[MEM_APPEND; MEM] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 3068 *)
let has_io_name_find_index = prove
 (`!(l:((A)sec)list) s.
     has_io_name s l ==> ?y. find_index (ExtCall s) (find_ffi_names l) 0 = SOME y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LTTP2AUX_has_io_name_MEM) THEN
  MP_TAC(ISPECL [`find_ffi_names (l:((A)sec)list)`; `ExtCall s`; `0`] find_index_NOT_MEM) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[cases "option"]);;

(* HOL4 line 3084 *)
let find_index_in_range = prove
 (`!n (s:A) l x. find_index s l n = SOME x ==> x < n + LENGTH l /\ x >= n`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP find_index_LESS_LENGTH) THEN
  ARITH_TAC);;

(* HOL4 line 3095 *)
let find_index_in_range0 = prove
 (`!(s:A) l x. find_index s l 0 = SOME x ==> x < LENGTH l /\ x >= 0`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP find_index_in_range) THEN
  ARITH_TAC);;

(* HOL4 line 3101 *)
let EL_get_ffi_index_MEM = prove
 (`!(s:A) ls. MEM s ls ==> EL (get_ffi_index ls s) ls = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ls:A list`; `s:A`; `0`] find_index_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[get_ffi_index_def; misc_the_def; ADD_CLAUSES]);;

(* HOL4 line 3110 *)
let has_io_name_EXISTS = prove
 (CASE_TERM `!name (ls:((A)sec)list).
     has_io_name name ls <=>
     EX (\x. match x with LabAsm (CallFFI i) _ _ _ -> i = name | _ -> F)
        (FLAT (MAP Section_lines ls))`,
  MATCH_MP_TAC has_io_name_ind THEN
  REWRITE_TAC[has_io_name_def; MAP; FLAT; lab_Section_lines_def; APPEND; EX;
              EXISTS_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* HOL4 line 3127 *)
let line_len_def = cake_def
  `(line_len (lab_Label _ _ l:(A)line) = l) /\
   (line_len (Asm _ _ l:(A)line) = l) /\
   (line_len (LabAsm _ _ _ l:(A)line) = l)`;;

let _ = cake_add_simps [line_len_def];;

(* HOL4 line 3135 *)
let sec_length_add = prove
 (`!(ls:((A)line)list) n m. sec_length ls (n + m) = sec_length ls n + m`,
  MATCH_MP_TAC sec_length_ind THEN REWRITE_TAC[sec_length_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(k + m) + l = (k + l) + m:num`] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 3142 *)
let sec_length_sum_line_len = prove
 (`!(ls:((A)line)list) n. sec_length ls n = SUM (MAP line_len ls) + n`,
  MATCH_MP_TAC sec_length_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[sec_length_def; MAP; SUM; line_len_def] THEN ARITH_TAC);;

(* HOL4 line 3151 *)
let enc_lines_again_simp_def = cake_def
  `(enc_lines_again_simp (labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) [] =
      ([],T)) /\
   (enc_lines_again_simp labs ffis pos enc (CONS (LabAsm a w bytes l) xs) =
      let w1 = get_jump_offset a ffis labs pos in
      if w = w1 then
        let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs in
        (CONS (LabAsm a w bytes l) rest,ok)
      else
        let bs = enc (lab_inst w1 a) in
        let l1 = MAX (LENGTH bs) l in
        let (rest,ok) = enc_lines_again_simp labs ffis (pos + l1) enc xs in
        (CONS (LabAsm a w1 bs l1) rest,(l1 = l /\ ok))) /\
   (enc_lines_again_simp labs ffis pos enc (CONS (lab_Label k1 k2 l) xs) =
      let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs in
      (CONS (lab_Label k1 k2 l) rest,ok)) /\
   (enc_lines_again_simp labs ffis pos enc (CONS (Asm x1 x2 l) xs) =
      let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs in
      (CONS (Asm x1 x2 l) rest,ok))`;;

(* HOL4 line 3172: val enc_lines_again_simp_ind = theorem *)
let enc_lines_again_simp_ind = cake_ind "enc_lines_again_simp";;

(* HOL4 line 3174 *)
let enc_lines_again_simp_EQ = prove
 (CASE_TERM `!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) ls acc b.
     let (ls',flag) = enc_lines_again_simp labs ffis pos enc ls in
     enc_lines_again labs ffis pos enc ls (acc,b) =
     (APPEND (REVERSE acc) ls',sec_length ls' pos,(b /\ flag))`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN
  FS[enc_lines_again_simp_def; enc_lines_again_def] THEN RW[sec_length_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[EQ_IMP_THM; sec_length_def] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

(* HOL4 line 3185 *)
let enc_lines_again_simp_len = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines res.
     enc_lines_again_simp labs ffis pos enc lines = (res,T)
     ==> MAP line_len res = MAP line_len lines`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN FS[]);;

(* HOL4 line 3195 *)
let LENGTH_pad_bytes = prove
 (`!nop bytes l.
     0 < LENGTH nop /\ LENGTH bytes <= l ==> LENGTH (pad_bytes bytes l nop) = l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pad_bytes_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_APPEND; LENGTH_FLAT_REPLICATE] THEN
  SUBGOAL_THEN `l * 1 <= l * LENGTH (nop:byte list)` MP_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ARITH_TAC]);;

(* HOL4 line 3205 *)
let section_labels_sec_length = prove
 (`!pos (lines:((A)line)list) acc.
     FST (section_labels pos lines acc) = sec_length lines pos`,
  MATCH_MP_TAC section_labels_ind THEN RW[section_labels_def; sec_length_def]);;

(* HOL4 line 3213 *)
let section_labels_append = prove
 (`!pos (l1:((A)line)list) labs l2.
     section_labels pos (APPEND l1 l2) labs =
     section_labels (pos + SUM (MAP line_len l1)) l2 (SND (section_labels pos l1 labs))`,
  MATCH_MP_TAC section_labels_ind THEN RW[section_labels_def; APPEND; MAP; SUM; ADD_ASSOC]);;

(* HOL4 line 3222 *)
let line_length_add_nop1 = prove
 (`!nop (ls:((A)line)list).
     ~ALL is_Label ls
     ==> SUM (MAP line_length (add_nop nop ls)) = SUM (MAP line_length ls) + LENGTH nop`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  FS[add_nop_def; line_length_def; ALL; MAP; SUM; LENGTH_APPEND] THEN ARITH_TAC);;

(* HOL4 line 3232 *)
let line_length_add_nop = prove
 (`!nop (ls:((A)line)list).
     ALL is_Label ls
     ==> SUM (MAP line_length (add_nop nop ls)) = SUM (MAP line_length ls)`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  FS[add_nop_def; line_length_def; ALL; MAP; SUM; LENGTH_APPEND]);;

(* HOL4 line 3242 *)
let line_len_add_nop1 = prove
 (`!nop (ls:((A)line)list).
     ~ALL is_Label ls
     ==> SUM (MAP line_len (add_nop nop ls)) = SUM (MAP line_len ls) + 1`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  FS[add_nop_def; ALL; MAP; SUM] THEN ARITH_TAC);;

(* HOL4 line 3250 *)
let line_len_add_nop = prove
 (`!nop (ls:((A)line)list).
     ALL is_Label ls ==> SUM (MAP line_len (add_nop nop ls)) = SUM (MAP line_len ls)`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN FS[add_nop_def; ALL; MAP; SUM]);;

(* HOL4 line 3258 *)
let add_nop_append = prove
 (`!nop (l1:((A)line)list) l2.
     add_nop nop (APPEND l1 l2) =
     if ALL is_Label l1 then APPEND l1 (add_nop nop l2) else APPEND (add_nop nop l1) l2`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[add_nop_def; APPEND; ALL; is_Label_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[APPEND]);;

(* HOL4 line 3266 *)
let EXISTS_not_Label_add_nop = prove
 (`!nop (acc:((A)line)list).
     EX ((~) o is_Label) (add_nop nop acc) <=> EX ((~) o is_Label) acc`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[add_nop_def; EX; o_THM; is_Label_def]);;

let _ = cake_add_simps [EXISTS_not_Label_add_nop];;

(* HOL4 line 3273 *)
let EVERY_is_Label_add_nop_preserved = prove
 (`!nop (acc:((A)line)list). ALL is_Label (add_nop nop acc) <=> ALL is_Label acc`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[add_nop_def; ALL; is_Label_def]);;

let _ = cake_add_simps [EVERY_is_Label_add_nop_preserved];;

(* HOL4 line 3280 *)
let EVERY_is_Label_add_nop = prove
 (`!nop (ls:((A)line)list). ALL is_Label ls ==> add_nop nop ls = ls`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  FS[add_nop_def; ALL; is_Label_def]);;

(* HOL4 line 3286 (HOL4 a + b - c is (a + b) - c) *)
let SND_lines_upd_lab_len = prove
 (`!pos (lines:((A)line)list) acc.
     SND (lines_upd_lab_len pos lines acc) =
     (pos + SUM (MAP line_len (FST (lines_upd_lab_len pos lines acc)))) -
     SUM (MAP line_len acc)`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; rich_list_MAP_REVERSE;
                  SUM_REVERSE; MAP; SUM; line_len_def] THEN
  ARITH_TAC);;

let LTTP2AUX_ALL2_line_similar_refl = prove
 (`!(l:((A)line)list). ALL2 line_similar l l`,
  GEN_TAC THEN MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[line_similar_refl]);;

let LTTP2AUX_ALL2_line_similar_trans = prove
 (`!(x:((A)line)list) y z.
     ALL2 line_similar x y /\ ALL2 line_similar y z ==> ALL2 line_similar x z`,
  MATCH_MP_TAC EVERY2_trans THEN MESON_TAC[line_similar_trans]);;

(* HOL4 line 3298 *)
let line_similar_add_nop = prove
 (`!(ls:((A)line)list) ls' h.
     ALL2 line_similar ls ls' ==> ALL2 line_similar ls (add_nop h ls')`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; add_nop_def] THEN
  GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `h':(A)line` THEN REWRITE_TAC[add_nop_def; ALL2] THEN ASM_SIMP_TAC[] THEN
  CASES_ON `h:(A)line` THEN FS[line_similar_def]);;

(* one step of pad_section keeps the lines similar *)
let LTTP2AUX_ALL2_sim_step = prove
 (`!(l1:((A)line)list) aux aux' x x' xs.
     ALL2 line_similar aux aux' /\ line_similar x x'
     ==> ALL2 line_similar l1 (APPEND (REVERSE aux) (CONS x xs))
     ==> ALL2 line_similar l1 (APPEND (REVERSE (CONS x' aux')) xs)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTTP2AUX_ALL2_line_similar_trans THEN
  EXISTS_TAC `APPEND (REVERSE aux) (CONS (x:(A)line) xs)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
  MATCH_MP_TAC EVERY2_APPEND_suff THEN
  ASM_REWRITE_TAC[LIST_REL_REVERSE_EQ; ALL2; LTTP2AUX_ALL2_line_similar_refl]);;

(* HOL4 line 3307 *)
let line_similar_pad_section = prove
 (`!nop (l2:((A)line)list) aux l1.
     ALL2 line_similar l1 (APPEND (REVERSE aux) l2)
     ==> ALL2 line_similar l1 (pad_section nop l2 aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def; APPEND_NIL];
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pad_section_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC LTTP2AUX_ALL2_sim_step THEN REWRITE_TAC[line_similar_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[LTTP2AUX_ALL2_line_similar_refl] THEN
    MATCH_MP_TAC line_similar_add_nop THEN REWRITE_TAC[LTTP2AUX_ALL2_line_similar_refl];
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pad_section_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC LTTP2AUX_ALL2_sim_step THEN
    REWRITE_TAC[line_similar_def; LTTP2AUX_ALL2_line_similar_refl];
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pad_section_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC LTTP2AUX_ALL2_sim_step THEN
    REWRITE_TAC[line_similar_def; LTTP2AUX_ALL2_line_similar_refl]]);;

(* HOL4 line 3338 *)
let code_similar_pad_code = prove
 (`!(code1:((A)sec)list) code2 nop.
     code_similar code1 code2 ==> code_similar code1 (pad_code nop code2)`,
  MATCH_MP_TAC code_similar_ind THEN REWRITE_TAC[code_similar_def; pad_code_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC line_similar_pad_section THEN ASM_REWRITE_TAC[REVERSE; APPEND]);;

let LTTP2AUX_line_similar_enc_line = prove
 (`!(enc:(A)asm->byte list) len (x:(A)line) y.
     line_similar (enc_line enc len x) y <=> line_similar x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)line` THEN CASES_ON `y:(A)line` THEN
  REWRITE_TAC[enc_line_def; LET_DEF; LET_END_DEF; line_similar_def]);;

(* HOL4 line 3353 *)
let LIST_REL_enc_line = prove
 (`!(ls:((A)line)list) ls' enc len.
     ALL2 line_similar ls ls' <=> ALL2 line_similar (MAP (enc_line enc len) ls) ls'`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; MAP; LTTP2AUX_line_similar_enc_line]);;

let LTTP2AUX_code_similar_MAP_enc_sec = prove
 (`!(code1:((A)sec)list) code2 enc len.
     code_similar (MAP (enc_sec enc len) code1) code2 <=> code_similar code1 code2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP] THEN
  TRY(CASES_ON `h:(A)sec`) THEN TRY(CASES_ON `h':(A)sec`) THEN
  ASM_REWRITE_TAC[enc_sec_def; code_similar_def; GSYM LIST_REL_enc_line]);;

(* HOL4 line 3362 *)
let code_similar_enc_sec_list = prove
 (`!(code1:((A)sec)list) code2 n.
     code_similar (enc_sec_list n code1) code2 <=> code_similar code1 code2`,
  REWRITE_TAC[enc_sec_list_def; LET_DEF; LET_END_DEF; LTTP2AUX_code_similar_MAP_enc_sec]);;

let _ = cake_add_simps [code_similar_enc_sec_list];;

let LTTP2AUX_enc_lines_again_IMP_similar = prove
 (`!lines (labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) acc ok lines' ok' curr.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (lines',ok')
     ==> ALL2 line_similar curr (REVERSE acc)
     ==> ALL2 line_similar (APPEND curr lines) lines'`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[enc_lines_again_def; PAIR_EQ; APPEND_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `APPEND curr (CONS (h:(A)line) t) = APPEND (APPEND curr [h]) t`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  CASES_ON `h:(A)line` THEN
  REWRITE_TAC[enc_lines_again_def; LET_DEF; LET_END_DEF] THEN
  TRY COND_CASES_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REVERSE] THEN MATCH_MP_TAC EVERY2_APPEND_suff THEN
  ASM_REWRITE_TAC[ALL2; line_similar_def]);;

(* HOL4 line 3376 *)
let enc_lines_again_IMP_similar = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines acc ok lines' ok' curr.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (lines',ok')
     ==> ALL2 line_similar curr (REVERSE acc)
     ==> ALL2 line_similar (APPEND curr lines) lines'`,
  MESON_TAC[LTTP2AUX_enc_lines_again_IMP_similar]);;

let LTTP2AUX_enc_lines_again_nil_similar = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines ok lines' ok'.
     enc_lines_again labs ffis pos enc lines ([],ok) = (lines',ok')
     ==> ALL2 line_similar lines lines'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lines:((A)line)list`; `labs:(num spt)spt`; `ffis:ffiname list`; `pos:num`;
                 `enc:(A)asm->byte list`; `[]:((A)line)list`; `ok:bool`;
                 `lines':((A)line)list`; `ok':num#bool`; `[]:((A)line)list`]
         LTTP2AUX_enc_lines_again_IMP_similar) THEN
  ASM_REWRITE_TAC[REVERSE; ALL2; APPEND]);;

(* HOL4 line 3391 *)
let enc_secs_again_IMP_similar = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) code code1 ok.
     enc_secs_again pos labs ffis enc code = (code1,ok) ==> code_similar code code1`,
  MATCH_MP_TAC enc_secs_again_ind THEN
  FS[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN FS[code_similar_def] THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP LTTP2AUX_enc_lines_again_nil_similar));;

(* HOL4 line 3402: val lines_upd_lab_len_AUX = Q.prove(...) |> GSYM *)
let lines_upd_lab_len_AUX = prove
 (`!(l:((A)line)list) aux pos.
     FST (lines_upd_lab_len pos l aux) =
     APPEND (REVERSE aux) (FST (lines_upd_lab_len pos l []))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_upd_lab_len_def; REVERSE; APPEND_NIL] THEN
  CASES_ON `h:(A)line` THEN REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[REVERSE; APPEND; GSYM APPEND_ASSOC]);;

let LTTP2AUX_line_similar_label = prove
 (`!k1 k2 l l' (y:(A)line).
     line_similar (lab_Label k1 k2 l) y <=> line_similar (lab_Label k1 k2 l') y`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)line` THEN REWRITE_TAC[line_similar_def]);;

(* HOL4 line 3410 (HOL4's binder aux is unused, left out) *)
let line_similar_lines_upd_lab_len = prove
 (`!(l:((A)line)list) pos l1.
     ALL2 line_similar (FST (lines_upd_lab_len pos l [])) l1 <=> ALL2 line_similar l l1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_upd_lab_len_def; REVERSE] THEN
  CASES_ON `h:(A)line` THEN REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[lines_upd_lab_len_AUX] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2] THEN
  MESON_TAC[LTTP2AUX_line_similar_label]);;

(* HOL4 line 3422 *)
let code_similar_upd_lab_len = prove
 (`!(code:((A)sec)list) pos code1.
     code_similar (upd_lab_len pos code) code1 <=> code_similar code code1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[upd_lab_len_def] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[upd_lab_len_def; pair_CASE_def; LET_DEF; LET_END_DEF] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[code_similar_def] THEN
  CASES_ON `h:(A)sec` THEN
  ASM_REWRITE_TAC[code_similar_def; line_similar_lines_upd_lab_len]);;

(* HOL4 line 3432 *)
let lines_upd_lab_len_similar = prove
 (`!pos (lines:((A)line)list) aux.
     ALL2 line_similar (FST (lines_upd_lab_len pos lines aux))
       (APPEND (REVERSE aux) lines)`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; APPEND_NIL;
              LTTP2AUX_ALL2_line_similar_refl] THEN
  REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LTTP2AUX_ALL2_line_similar_trans THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EVERY2_APPEND_suff THEN
  REWRITE_TAC[ALL2; LTTP2AUX_ALL2_line_similar_refl; line_similar_def]);;

(* HOL4 line 3450 *)
let code_similar_MAP_Section_num = prove
 (`!(c1:((A)sec)list) c2. code_similar c1 c2 ==> MAP Section_num c1 = MAP Section_num c2`,
  MATCH_MP_TAC code_similar_ind THEN
  REWRITE_TAC[code_similar_def; MAP; lab_Section_num_def] THEN MESON_TAC[]);;

let LTTP2AUX_ALL2_similar_extract_labels = prove
 (`!(l1:((A)line)list) l2.
     ALL2 line_similar l1 l2 ==> lab_extract_labels l1 = lab_extract_labels l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2] THEN
  CASES_ON `h:(A)line` THEN CASES_ON `h':(A)line` THEN
  REWRITE_TAC[line_similar_def; lab_extract_labels_def; CONS_11; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 3459 *)
let code_similar_extract_labels = prove
 (`!(code1:((A)sec)list) code2.
     code_similar code1 code2
     ==> MAP (lab_extract_labels o Section_lines) code1 =
         MAP (lab_extract_labels o Section_lines) code2`,
  MATCH_MP_TAC code_similar_ind THEN
  REWRITE_TAC[code_similar_def; MAP; o_THM; lab_Section_lines_def; CONS_11] THEN
  MESON_TAC[LTTP2AUX_ALL2_similar_extract_labels]);;

let LTTP2AUX_line_similar_is_Label = prove
 (`!(z:(A)line) z' n1 n2.
     line_similar z z'
     ==> (is_Label z <=> is_Label z') /\
         ((?k. z = lab_Label n1 n2 k) <=> (?k. z' = lab_Label n1 n2 k))`,
  REPEAT GEN_TAC THEN CASES_ON `z:(A)line` THEN CASES_ON `z':(A)line` THEN
  REWRITE_TAC[line_similar_def; is_Label_def; injectivity "line"; distinctness "line"] THEN
  MESON_TAC[]);;

(* HOL4 line 3475 *)
let code_similar_loc_to_pc = prove
 (`!l1 l2 (c1:((A)sec)list) c2.
     code_similar c1 c2 ==> loc_to_pc l1 l2 c1 = loc_to_pc l1 l2 c2`,
  MATCH_MP_TAC loc_to_pc_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[code_similar_nil] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REFL_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `c2:((A)sec)list` list_CASES) THEN
  REWRITE_TAC[code_similar_def] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[code_similar_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ONCE_REWRITE_TAC[loc_to_pc_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CASES_ON `xs:((A)line)list` THEN CASES_ON `a1:((A)line)list` THEN
  FS[ALL2] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LTTP2AUX_line_similar_is_Label th)]) THEN
  SUBGOAL_THEN `code_similar (CONS (Section k a1') ys) (CONS (Section k a1'') (t:((A)sec)list))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[code_similar_def]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      mem `is_Label (a0:(A)line)` (conjuncts(lhand(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      mem `~is_Label (a0:(A)line)` (conjuncts(lhand(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* enc_lines_again keeps a line property that holds of every re-encoding of *)
(* a LabAsm line                                                             *)
let LTTP2AUX_enc_lines_again_ALL = prove
 (`!(P:(A)line->bool) (labs:(num spt)spt) ffis (enc:(A)asm->byte list).
     (!a w bytes l w1.
        P (LabAsm a w bytes l)
        ==> P (LabAsm a w1 (enc (lab_inst w1 a)) (MAX (LENGTH (enc (lab_inst w1 a))) l)))
     ==> !lines pos acc ok res ok'.
           enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok')
           ==> ALL P acc /\ ALL P lines ==> ALL P res`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[enc_lines_again_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[EVERY_REVERSE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `h:(A)line` THEN
  REWRITE_TAC[enc_lines_again_def; LET_DEF; LET_END_DEF; ALL] THEN
  TRY COND_CASES_TAC THEN
  DISCH_THEN(fun eq -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP eq)) THEN
  REWRITE_TAC[ALL] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;
let LTTP2AUX_sec_label_ok_enc_line = prove
 (`!k (enc:(A)asm->byte list) len x.
     sec_label_ok k (enc_line enc len x) <=> sec_label_ok k x`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)line` THEN
  REWRITE_TAC[enc_line_def; LET_DEF; LET_END_DEF; sec_label_ok_def]);;

(* HOL4 line 3511 *)
let enc_sec_list_sec_labels_ok = prove
 (`!(enc:(A)asm->byte list) code.
     ALL sec_labels_ok code ==> ALL sec_labels_ok (enc_sec_list enc code)`,
  GEN_TAC THEN REWRITE_TAC[enc_sec_list_def; LET_DEF; LET_END_DEF] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN CASES_ON `h:(A)sec` THEN
  ASM_SIMP_TAC[enc_sec_def; sec_labels_ok_def; ALL_MAP; o_DEF;
               LTTP2AUX_sec_label_ok_enc_line; ETA_AX]);;

(* HOL4 line 3524 *)
let enc_lines_again_sec_labels_ok = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines acc ok res ok' k.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
     ALL (sec_label_ok k) acc /\ ALL (sec_label_ok k) lines
     ==> ALL (sec_label_ok k) res`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sec_label_ok k:(A)line->bool`; `labs:(num spt)spt`; `ffis:ffiname list`;
                 `enc:(A)asm->byte list`] LTTP2AUX_enc_lines_again_ALL) THEN
  REWRITE_TAC[sec_label_ok_def; IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 3535 (HOL4's variables ffis and labs stand in the positions   *)
(* of labs and ffis of enc_secs_again, kept so; the binder k is unused, left *)
(* out)                                                                       *)
let enc_secs_again_sec_labels_ok = prove
 (`!pos ffis labs (enc:(A)asm->byte list) ls res ok.
     enc_secs_again pos ffis labs enc ls = (res,ok) /\ ALL sec_labels_ok ls
     ==> ALL sec_labels_ok res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN
  MATCH_MP_TAC enc_lines_again_sec_labels_ok THEN ASM_MESON_TAC[ALL]);;

(* HOL4 line 3547 *)
let lines_upd_lab_len_sec_label_ok = prove
 (`!pos (lines:((A)line)list) acc k.
     ALL (sec_label_ok k) lines /\ ALL (sec_label_ok k) acc
     ==> ALL (sec_label_ok k) (FST (lines_upd_lab_len pos lines acc))`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; ALL; EVERY_REVERSE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL] THEN FS[sec_label_ok_def]);;

(* HOL4 line 3558 *)
let upd_lab_len_sec_labels_ok = prove
 (`!n (ls:((A)sec)list). ALL sec_labels_ok ls ==> ALL sec_labels_ok (upd_lab_len n ls)`,
  MATCH_MP_TAC upd_lab_len_ind THEN RW[upd_lab_len_def; ALL] THEN
  PAIRARG_TAC THEN FS[ALL] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`; `s:num`]
         lines_upd_lab_len_sec_label_ok) THEN
  ASM_REWRITE_TAC[ALL]);;

(* HOL4 line 3568 *)
let add_nop_sec_label_ok = prove
 (`!nop (aux:((A)line)list) k.
     ALL (sec_label_ok k) aux ==> ALL (sec_label_ok k) (add_nop nop aux)`,
  MATCH_MP_TAC add_nop_ind THEN REPEAT STRIP_TAC THEN
  FS[add_nop_def; ALL; sec_label_ok_def]);;

(* HOL4 line 3577 *)
let pad_section_sec_label_ok = prove
 (`!nop (xs:((A)line)list) acc k.
     ALL (sec_label_ok k) xs /\ ALL (sec_label_ok k) acc
     ==> ALL (sec_label_ok k) (pad_section nop xs acc)`,
  MATCH_MP_TAC pad_section_ind THEN
  REWRITE_TAC[pad_section_def; ALL; EVERY_REVERSE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL] THEN FS[sec_label_ok_def] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[add_nop_sec_label_ok]);;

(* HOL4 line 3590 *)
let pad_code_sec_labels_ok = prove
 (`!nop (code:((A)sec)list).
     ALL sec_labels_ok code ==> ALL sec_labels_ok (pad_code nop code)`,
  MATCH_MP_TAC pad_code_ind THEN REPEAT STRIP_TAC THEN
  FS[pad_code_def; ALL; sec_labels_ok_def] THEN
  MATCH_MP_TAC pad_section_sec_label_ok THEN ASM_REWRITE_TAC[ALL]);;

(* HOL4 line 3601 *)
let sec_labels_ok_filter_skip = prove
 (`!(code:((A)sec)list). ALL sec_labels_ok (filter_skip code) <=> ALL sec_labels_ok code`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_skip_def] THEN CASES_ON `h:(A)sec` THEN
  ASM_REWRITE_TAC[filter_skip_def; ALL; sec_labels_ok_def; ALL_FILTER] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
  CASES_ON `x:(A)line` THEN REWRITE_TAC[sec_label_ok_def; not_skip_def] THEN
  CASE_REWRITE_TAC[]);;

let _ = cake_add_simps [sec_labels_ok_filter_skip];;

(* HOL4 line 3615 *)
let line_encd0_def = cake_def
  `(line_encd0 (enc:(A)asm->byte list) (Asm b bytes len) <=>
      enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes) /\
   (line_encd0 enc (LabAsm l w bytes len) <=>
      enc (lab_inst w l) = bytes /\ LENGTH bytes <= len /\
      (?w'. len = LENGTH (enc (lab_inst w' l)))) /\
   (line_encd0 enc (_:(A)line) <=> T)`;;

(* HOL4 line 3624 *)
let sec_encd0_def = cake_def
  `sec_encd0 (enc:(A)asm->byte list) (Section _ ls) <=> ALL (line_encd0 enc) ls`;;

let _ = cake_add_simps [sec_encd0_def];;

(* HOL4 line 3628: Overload all_encd0 = \enc l. EVERY (sec_encd0 enc) l     *)
(* (written out where used: ALL (sec_encd0 enc) l)                           *)

let LTTP2AUX_line_encd0_enc_line = prove
 (`!(enc:(A)asm->byte list) len x. line_encd0 enc (enc_line enc len x)`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)line` THEN
  REWRITE_TAC[enc_line_def; LET_DEF; LET_END_DEF; line_encd0_def; LE_REFL] THEN
  MESON_TAC[]);;

(* HOL4 line 3632 *)
let enc_sec_list_encd0 = prove
 (`!(enc:(A)asm->byte list) ls. ALL (sec_encd0 enc) (enc_sec_list enc ls)`,
  GEN_TAC THEN REWRITE_TAC[enc_sec_list_def; LET_DEF; LET_END_DEF] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN CASES_ON `h:(A)sec` THEN
  ASM_REWRITE_TAC[enc_sec_def; sec_encd0_def; ALL_MAP; o_DEF;
                  LTTP2AUX_line_encd0_enc_line; ALL_T]);;

let LTTP2AUX_line_encd0_reenc = prove
 (`!(enc:(A)asm->byte list) a w bytes l w1.
     line_encd0 enc (LabAsm a w bytes l)
     ==> line_encd0 enc
           (LabAsm a w1 (enc (lab_inst w1 a)) (MAX (LENGTH (enc (lab_inst w1 a))) l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[line_encd0_def; MAX_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN MESON_TAC[]);;

(* HOL4 line 3644 *)
let enc_lines_again_encd0 = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines acc ok res ok'.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
     ALL (line_encd0 enc) lines /\ ALL (line_encd0 enc) acc
     ==> ALL (line_encd0 enc) res`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`line_encd0 (enc:(A)asm->byte list)`; `labs:(num spt)spt`;
                 `ffis:ffiname list`; `enc:(A)asm->byte list`] LTTP2AUX_enc_lines_again_ALL) THEN
  REWRITE_TAC[LTTP2AUX_line_encd0_reenc; IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 3659 *)
let enc_secs_again_encd0 = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) ls res ok.
     enc_secs_again pos labs ffis enc ls = (res,ok) /\ ALL (sec_encd0 enc) ls
     ==> ALL (sec_encd0 enc) res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN
  MATCH_MP_TAC enc_lines_again_encd0 THEN ASM_MESON_TAC[ALL]);;

(* HOL4 line 3674 *)
let lines_upd_lab_len_encd0 = prove
 (`!pos (ls:((A)line)list) acc enc.
     ALL (line_encd0 enc) ls /\ ALL (line_encd0 enc) acc
     ==> ALL (line_encd0 enc) (FST (lines_upd_lab_len pos ls acc))`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; ALL; EVERY_REVERSE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL; line_encd0_def]);;

(* HOL4 line 3685 *)
let upd_lab_len_encd0 = prove
 (`!pos (ss:((A)sec)list) enc.
     ALL (sec_encd0 enc) ss ==> ALL (sec_encd0 enc) (upd_lab_len pos ss)`,
  MATCH_MP_TAC upd_lab_len_ind THEN RW[upd_lab_len_def; ALL] THEN
  PAIRARG_TAC THEN FS[ALL] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`;
                 `enc:(A)asm->byte list`] lines_upd_lab_len_encd0) THEN
  ASM_REWRITE_TAC[ALL]);;

(* HOL4 line 3701 *)
let line_length_leq_def = cake_def
  `(line_length_leq (LabAsm _ _ bytes l:(A)line) <=> LENGTH bytes <= l) /\
   (line_length_leq (Asm _ bytes l:(A)line) <=> LENGTH bytes <= l) /\
   (line_length_leq (_:(A)line) <=> T)`;;

let _ = cake_add_simps [line_length_leq_def];;

(* HOL4 line 3709 *)
let sec_length_leq_def = cake_def
  `sec_length_leq (Section _ ls:(A)sec) <=> ALL line_length_leq ls`;;

let _ = cake_add_simps [sec_length_leq_def];;

(* HOL4 line 3713: Overload all_length_leq = \l. EVERY sec_length_leq l    *)
(* (written out where used)                                                  *)

(* HOL4 line 3717 *)
let label_one_def = cake_def
  `(label_one (lab_Label _ _ n:(A)line) <=> n <= 1) /\
   (label_one (_:(A)line) <=> T)`;;

let _ = cake_add_simps [label_one_def];;

(* HOL4 line 3722 *)
let sec_label_one_def = cake_def
  `sec_label_one (Section _ ls:(A)sec) <=> ALL label_one ls`;;

let _ = cake_add_simps [sec_label_one_def];;

(* HOL4 line 3728 *)
let lines_upd_lab_len_label_one = prove
 (`!pos (ls:((A)line)list) acc.
     ALL label_one acc ==> ALL label_one (FST (lines_upd_lab_len pos ls acc))`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; ALL; EVERY_REVERSE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL; label_one_def] THEN ARITH_TAC);;

(* HOL4 line 3737 *)
let upd_lab_len_label_one = prove
 (`!pos (ss:((A)sec)list). ALL sec_label_one (upd_lab_len pos ss)`,
  MATCH_MP_TAC upd_lab_len_ind THEN RW[upd_lab_len_def; ALL] THEN
  PAIRARG_TAC THEN FS[ALL] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
         lines_upd_lab_len_label_one) THEN
  ASM_REWRITE_TAC[ALL]);;

(* HOL4 line 3748 *)
let enc_lines_again_simp_label_one = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) ls res ok.
     enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\ ALL label_one ls
     ==> ALL label_one res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN FS[ALL; label_one_def]);;

(* enc_lines_again from an empty accumulator is enc_lines_again_simp *)
let LTTP2AUX_enc_lines_again_simp_nil = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines lines1 pos1 ok.
     enc_lines_again labs ffis pos enc lines ([],T) = (lines1,pos1,ok)
     ==> enc_lines_again_simp labs ffis pos enc lines = (lines1,ok) /\
         pos1 = sec_length lines1 pos`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`labs:(num spt)spt`; `ffis:ffiname list`; `pos:num`;
                 `enc:(A)asm->byte list`; `lines:((A)line)list`; `[]:((A)line)list`; `T`]
         enc_lines_again_simp_EQ) THEN
  REWRITE_TAC[pair_CASE_def; REVERSE; APPEND] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[PAIR]);;

(* HOL4 line 3759 *)
let enc_secs_again_label_one = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) lines res ok.
     enc_secs_again pos labs ffis enc lines = (res,ok) /\ ALL sec_label_one lines
     ==> ALL sec_label_one res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  MATCH_MP_TAC enc_lines_again_simp_label_one THEN ASM_MESON_TAC[]);;

(* HOL4 line 3777 *)
let line_length_pad_section1 = prove
 (`!nop (ls:((A)line)list) acc.
     LENGTH nop = 1 /\ ALL label_one ls /\ ALL line_length_leq ls /\
     ~ALL is_Label acc /\ SUM (MAP line_length acc) = SUM (MAP line_len acc)
     ==> SUM (MAP line_length (pad_section nop ls acc)) =
         SUM (MAP line_len ls) + SUM (MAP line_len acc)`,
  MATCH_MP_TAC pad_section_ind THEN RW[pad_section_def] THEN
  FS[rich_list_MAP_REVERSE; SUM_REVERSE; line_length_def; LENGTH_pad_bytes] THEN
  FS[line_length_add_nop1; line_len_add_nop1] THEN ASM_ARITH_TAC);;

(* HOL4 line 3794 *)
let line_len_pad_section1 = prove
 (`!nop (xs:((A)line)list) aux.
     LENGTH nop = 1 /\ ALL label_one xs /\ ~ALL is_Label aux
     ==> SUM (MAP line_len (pad_section nop xs aux)) =
         SUM (MAP line_len xs) + SUM (MAP line_len aux)`,
  MATCH_MP_TAC pad_section_ind THEN RW[pad_section_def] THEN
  FS[rich_list_MAP_REVERSE; SUM_REVERSE; line_len_add_nop1] THEN ASM_ARITH_TAC);;

(* HOL4 line 3809 (HOL4 -n2w x is word_neg (word x); the b of the JumpCmp  *)
(* clause, a register, is r here: one quotation types each name once)        *)
let line_encd_def = cake_def
  `(line_encd (enc:(A)asm->byte list) labs ffis pos (Asm b bytes len) <=>
      enc (cbw_to_asm b) = bytes /\ len = LENGTH bytes) /\
   (line_encd enc labs ffis pos (LabAsm lab_Halt _ bytes len) <=>
      enc (asm_Jump (word_neg (word (pos + ffi_offset)))) = bytes /\ LENGTH bytes <= len) /\
   (line_encd enc labs ffis pos (LabAsm lab_Install _ bytes len) <=>
      enc (asm_Jump (word_neg (word (pos + 2 * ffi_offset)))) = bytes /\
      LENGTH bytes <= len) /\
   (line_encd enc labs ffis pos (LabAsm (CallFFI s) _ bytes len) <=>
      enc (asm_Jump (word_neg (word (pos + (get_ffi_index ffis (ExtCall s) + 3) *
                                           ffi_offset)))) = bytes /\
      LENGTH bytes <= len) /\
   (line_encd enc labs ffis pos (LabAsm (lab_Jump l) _ bytes len) <=>
      enc (asm_Jump (word_add (word (find_pos l labs)) (word_neg (word pos)))) = bytes /\
      LENGTH bytes <= len) /\
   (line_encd enc labs ffis pos (LabAsm (lab_JumpCmp a r c l) _ bytes len) <=>
      enc (asm_JumpCmp a r c (word_add (word (find_pos l labs)) (word_neg (word pos)))) =
        bytes /\
      LENGTH bytes <= len) /\
   (line_encd enc labs ffis pos (LabAsm (lab_LocValue k l) _ bytes len) <=>
      enc (asm_Loc k (word_add (word (find_pos l labs)) (word_neg (word pos)))) = bytes /\
      LENGTH bytes <= len) /\
   (line_encd enc labs ffis pos (LabAsm (lab_Call l) _ bytes len) <=>
      enc (asm_Call (word_add (word (find_pos l labs)) (word_neg (word pos)))) = bytes /\
      LENGTH bytes <= len) /\
   (line_encd enc labs ffis pos (_:(A)line) <=> T)`;;

(* HOL4 line 3836: val line_encd_ind = theorem "line_encd_ind" (line_encd   *)
(* is not recursive: HOL4's TFL theorem is the case split, one case per     *)
(* clause of line_encd_def, the catch-all clause completed)                  *)
let line_encd_ind = prove
 (`!(P:((A)asm->byte list)->(num spt)spt->ffiname list->num->(A)line->bool).
     (!enc labs ffis pos b bytes len. P enc labs ffis pos (Asm b bytes len)) /\
     (!enc labs ffis pos v bytes len. P enc labs ffis pos (LabAsm lab_Halt v bytes len)) /\
     (!enc labs ffis pos v bytes len. P enc labs ffis pos (LabAsm lab_Install v bytes len)) /\
     (!enc labs ffis pos s v bytes len.
        P enc labs ffis pos (LabAsm (CallFFI s) v bytes len)) /\
     (!enc labs ffis pos l v bytes len.
        P enc labs ffis pos (LabAsm (lab_Jump l) v bytes len)) /\
     (!enc labs ffis pos a r c l v bytes len.
        P enc labs ffis pos (LabAsm (lab_JumpCmp a r c l) v bytes len)) /\
     (!enc labs ffis pos k l v bytes len.
        P enc labs ffis pos (LabAsm (lab_LocValue k l) v bytes len)) /\
     (!enc labs ffis pos l v bytes len.
        P enc labs ffis pos (LabAsm (lab_Call l) v bytes len)) /\
     (!enc labs ffis pos v1 v2 v3. P enc labs ffis pos (lab_Label v1 v2 v3))
     ==> !v v1 v2 v3 v4. P v v1 v2 v3 v4`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN CASES_ON `v4:(A)line` THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `a0:(A)asm_with_lab` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 3838 *)
let lines_encd_def = cake_def
  `(lines_encd (enc:(A)asm->byte list) labs ffis pos ([]:((A)line)list) <=> T) /\
   (lines_encd enc labs ffis pos (CONS l ls) <=>
      line_encd enc labs ffis pos l /\ lines_encd enc labs ffis (pos + line_len l) ls)`;;

let lines_encd_ind = cake_ind "lines_encd";;

(* HOL4 line 3845 *)
let all_encd_def = cake_def
  `(all_encd (enc:(A)asm->byte list) labs ffis pos ([]:((A)sec)list) <=> T) /\
   (all_encd enc labs ffis pos (CONS (Section k ls) ss) <=>
      lines_encd enc labs ffis pos ls /\
      all_encd enc labs ffis (pos + SUM (MAP line_len ls)) ss)`;;

let all_encd_ind = cake_ind "all_encd";;

(* HOL4 line 3854 *)
let line_encd_length_leq = prove
 (`!(enc:(A)asm->byte list) labs ffis pos l.
     line_encd enc labs ffis pos l ==> line_length_leq l`,
  REPEAT GEN_TAC THEN CASES_ON `l:(A)line` THEN
  REWRITE_TAC[line_encd_def; line_length_leq_def] THENL
   [ARITH_TAC; CASES_ON `a0:(A)asm_with_lab` THEN
    REWRITE_TAC[line_encd_def; line_length_leq_def] THEN MESON_TAC[]]);;

(* HOL4 line 3860 *)
let lines_encd_length_leq = prove
 (`!(enc:(A)asm->byte list) labs ffis pos ls.
     lines_encd enc labs ffis pos ls ==> ALL line_length_leq ls`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_encd_def; ALL] THEN
  ASM_MESON_TAC[line_encd_length_leq]);;

(* HOL4 line 3867 *)
let all_encd_length_leq = prove
 (`!(enc:(A)asm->byte list) labs ffis pos ls.
     all_encd enc labs ffis pos ls ==> ALL sec_length_leq ls`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[all_encd_def; ALL] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[all_encd_def; sec_length_leq_def] THEN
  ASM_MESON_TAC[lines_encd_length_leq]);;

let LTTP2AUX_MAX_EQ_R = prove
 (`!m n. MAX m n = n <=> m <= n`,
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* HOL4 line 3877 *)
let enc_lines_again_simp_encd = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines res.
     enc_lines_again_simp labs ffis pos enc lines = (res,T) /\
     ALL label_one lines /\ ALL (line_encd0 enc) lines
     ==> lines_encd enc labs ffis pos res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  FS[lines_encd_def] THEN PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN
  SIMP[lines_encd_def] THEN GVS[line_encd0_def; line_encd_def; line_length_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LTTP2AUX_MAX_EQ_R]) THEN
  CASES_ON `a:(A)asm_with_lab` THEN
  ASM_REWRITE_TAC[line_encd_def; get_jump_offset_def; lab_inst_def; get_label_def;
                  WORD_SUB_LZERO; word_sub_def] THEN
  REWRITE_TAC[ADD_SYM]);;

(* HOL4 line 3897 *)
let enc_secs_again_encd = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) ls res.
     enc_secs_again pos labs ffis enc ls = (res,T) /\
     ALL sec_label_one ls /\ ALL (sec_encd0 enc) ls
     ==> all_encd enc labs ffis pos res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN
  FS[all_encd_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  FS[all_encd_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  RVEQ_TAC THEN FS[sec_length_sum_line_len] THEN CONJ_TAC THENL
   [MATCH_MP_TAC enc_lines_again_simp_encd THEN ASM_MESON_TAC[];
    ONCE_REWRITE_TAC[ADD_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 3919 *)
let line_length_ok_def = cake_def
  `line_length_ok (l:(A)line) <=> LENGTH (line_bytes l) = line_len l`;;

(* HOL4 line 3923 *)
let sec_length_ok_def = cake_def
  `sec_length_ok (Section _ ls:(A)sec) <=> ALL line_length_ok ls`;;

(* HOL4 line 3929 *)
let sec_length_sum_line_length = prove
 (`!(ls:((A)line)list) n.
     ALL line_length_ok ls ==> sec_length ls n = SUM (MAP line_length ls) + n`,
  MATCH_MP_TAC sec_length_ind THEN
  REWRITE_TAC[sec_length_def; ALL; MAP; SUM; line_length_ok_def; line_bytes_def;
              line_length_def; line_len_def; LENGTH] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ARITH_TAC);;

(* HOL4 line 3941 *)
let label_zero_def = cake_def
  `(label_zero (lab_Label _ _ n:(A)line) <=> n = 0) /\
   (label_zero (_:(A)line) <=> T)`;;

let _ = cake_add_simps [label_zero_def];;

(* HOL4 line 3946 *)
let sec_label_zero_def = cake_def
  `sec_label_zero (Section _ ls:(A)sec) <=> ALL label_zero ls`;;

(* HOL4 line 3952 *)
let EVERY_label_zero_add_nop = prove
 (`!nop (xs:((A)line)list). ALL label_zero (add_nop nop xs) <=> ALL label_zero xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[add_nop_def; ALL] THEN
  CASES_ON `h:(A)line` THEN ASM_REWRITE_TAC[add_nop_def; ALL; label_zero_def]);;

(* HOL4 line 3959 *)
let EVERY_label_zero_pad_section = prove
 (`!nop (xs:((A)line)list) aux.
     ALL label_zero aux ==> ALL label_zero (pad_section nop xs aux)`,
  MATCH_MP_TAC pad_section_ind THEN
  REWRITE_TAC[pad_section_def; EVERY_REVERSE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL; label_zero_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EVERY_label_zero_add_nop]);;

let _ = cake_add_simps [EVERY_label_zero_pad_section];;

(* HOL4 line 3970 *)
let EVERY_sec_label_zero_pad_code = prove
 (`!nop (ls:((A)sec)list). ALL sec_label_zero (pad_code nop ls)`,
  MATCH_MP_TAC pad_code_ind THEN
  ASM_SIMP_TAC[pad_code_def; ALL; sec_label_zero_def; EVERY_label_zero_pad_section]);;

let _ = cake_add_simps [EVERY_sec_label_zero_pad_code];;

(* HOL4 line 3980 *)
let enc_lines_again_simp_label_zero = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) ls res ok.
     enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\ ALL label_zero ls
     ==> ALL label_zero res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN FS[ALL; label_zero_def]);;

(* HOL4 line 3991 *)
let enc_secs_again_label_zero = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) lines res ok.
     enc_secs_again pos labs ffis enc lines = (res,ok) /\ ALL sec_label_zero lines
     ==> ALL sec_label_zero res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN FS[ALL; sec_label_zero_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  MATCH_MP_TAC enc_lines_again_simp_label_zero THEN ASM_MESON_TAC[]);;

let LTTP2AUX_MOD_2EXP_EVEN = prove
 (`!x n. x MOD 2 EXP n = 0 /\ ~(n = 0) ==> EVEN x`,
  REWRITE_TAC[MOD_EQ_0] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EVEN_MULT; EVEN_EXP; ARITH]);;

let LTTP2AUX_enc_ok_EVEN = prove
 (`!(c:(A)asm_config) w.
     enc_ok c /\ ~(asm_config_code_alignment c = 0)
     ==> EVEN (LENGTH (asm_config_encode c w))`,
  REWRITE_TAC[enc_ok_def] THEN MESON_TAC[LTTP2AUX_MOD_2EXP_EVEN]);;

let LTTP2AUX_lines_upd_lab_len_encd0_label_zero = prove
 (`!(c:(A)asm_config).
     enc_ok c /\ ~(asm_config_code_alignment c = 0)
     ==> !pos (lines:((A)line)list) aux.
           ALL (line_encd0 (asm_config_encode c)) lines /\ EVEN pos /\ ALL label_zero aux
           ==> ALL label_zero (FST (lines_upd_lab_len pos lines aux))`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; ALL; EVERY_REVERSE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL; label_zero_def; ADD_CLAUSES; EVEN_ADD; EVEN] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[line_encd0_def]) THEN ASM_MESON_TAC[LTTP2AUX_enc_ok_EVEN]);;

(* HOL4 line 4007 *)
let lines_upd_lab_len_encd0_label_zero = prove
 (`!pos (lines:((A)line)list) aux c enc.
     enc_ok c /\ enc = asm_config_encode c /\ ~(asm_config_code_alignment c = 0) /\
     ALL (line_encd0 enc) lines /\ EVEN pos /\ ALL label_zero aux
     ==> ALL label_zero (FST (lines_upd_lab_len pos lines aux))`,
  MESON_TAC[LTTP2AUX_lines_upd_lab_len_encd0_label_zero]);;

(* HOL4 line 4023 *)
let EVEN_sec_length_lines_upd_lab_len = prove
 (`!pos (lines:((A)line)list) acc.
     (if NULL lines then EVEN pos /\ EVEN (SUM (MAP line_len acc))
      else is_Label (LAST lines) /\ EVEN (pos + SUM (MAP line_len acc)))
     ==> EVEN (SUM (MAP line_len (FST (lines_upd_lab_len pos lines acc))))`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; NULL; rich_list_MAP_REVERSE;
              SUM_REVERSE] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  CASES_ON `xs:((A)line)list` THEN
  REWRITE_TAC[NULL; LAST; NOT_CONS_NIL; is_Label_def; MAP; SUM; line_len_def; EVEN_ADD] THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[EVEN; ARITH] THEN CONV_TAC TAUT);;

let LTTP2AUX_upd_lab_len_encd0_label_zero = prove
 (`!(c:(A)asm_config).
     enc_ok c /\ ~(asm_config_code_alignment c = 0)
     ==> !pos (code:((A)sec)list).
           ALL (sec_encd0 (asm_config_encode c)) code /\ EVEN pos /\
           ALL sec_ends_with_label code
           ==> ALL sec_label_zero (upd_lab_len pos code)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC upd_lab_len_ind THEN
  RW[upd_lab_len_def; ALL] THEN PAIRARG_TAC THEN FS[ALL; sec_label_zero_def] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
         SND_lines_upd_lab_len) THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
         EVEN_sec_length_lines_upd_lab_len) THEN
  MP_TAC(SPEC `c:(A)asm_config` LTTP2AUX_lines_upd_lab_len_encd0_label_zero) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sec_ends_with_label_def]) THEN
  ASM_REWRITE_TAC[ALL; MAP; SUM; ADD_CLAUSES; SUB_0; NULL] THEN
  REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[EVEN_ADD]]);;

(* HOL4 line 4039 *)
let upd_lab_len_encd0_label_zero = prove
 (`!pos (code:((A)sec)list) c enc.
     enc_ok c /\ enc = asm_config_encode c /\ ~(asm_config_code_alignment c = 0) /\
     ALL (sec_encd0 enc) code /\ EVEN pos /\ ALL sec_ends_with_label code
     ==> ALL sec_label_zero (upd_lab_len pos code)`,
  MESON_TAC[LTTP2AUX_upd_lab_len_encd0_label_zero]);;

(* HOL4 line 4061 *)
let sec_pos_val_0 = prove
 (`!pos (lines:((A)line)list).
     ~ALL is_Label lines /\ ALL label_zero lines ==> sec_pos_val 0 pos lines = SOME pos`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; sec_pos_val_def] THEN
  CASES_ON `h:(A)line` THEN
  ASM_REWRITE_TAC[is_Label_def; label_zero_def; line_length_def] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[ADD_CLAUSES]);;

(* HOL4 line 4068 *)
let line_len_pad_section0 = prove
 (`!nop (ls:((A)line)list) aux.
     ALL label_zero ls
     ==> SUM (MAP line_len (pad_section nop ls aux)) =
         SUM (MAP line_len ls) + SUM (MAP line_len aux)`,
  MATCH_MP_TAC pad_section_ind THEN RW[pad_section_def] THEN
  FS[rich_list_MAP_REVERSE; SUM_REVERSE] THEN ASM_ARITH_TAC);;

let LTTP2AUX_sec_label_zero_pos_val_0 = prove
 (`!i pos (xs:((A)sec)list). i = 0 /\ ALL sec_label_zero xs ==> pos_val i pos xs = pos`,
  MATCH_MP_TAC pos_val_ind THEN REWRITE_TAC[pos_val_def; ALL; sec_label_zero_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `is_Label (y:(A)line)`)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `line_length (y:(A)line) = 0` (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
  UNDISCH_TAC `label_zero (y:(A)line)` THEN UNDISCH_TAC `is_Label (y:(A)line)` THEN
  CASES_ON `y:(A)line` THEN REWRITE_TAC[is_Label_def; label_zero_def; line_length_def] THEN
  SIMP_TAC[]);;

(* HOL4 line 4078 *)
let sec_label_zero_pos_val_0 = prove
 (`!(xs:((A)sec)list) pos. ALL sec_label_zero xs ==> pos_val 0 pos xs = pos`,
  MESON_TAC[LTTP2AUX_sec_label_zero_pos_val_0]);;

(* HOL4 line 4092 *)
let all_enc_ok_imp_sec_label_zero = prove
 (`!(conf:(A)asm_config) labs ffis n code.
     all_enc_ok conf labs ffis n code ==> ALL sec_label_zero code`,
  MATCH_MP_TAC all_enc_ok_ind THEN
  REWRITE_TAC[all_enc_ok_def; ALL; sec_label_zero_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `y:(A)line` THEN RULE_ASSUM_TAC(REWRITE_RULE[line_ok_def]) THEN
  ASM_REWRITE_TAC[label_zero_def]);;

(* HOL4 line 4104 *)
let line_aligned_def = cake_def
  `line_aligned m (l:(A)line) <=> line_len l MOD m = 0 /\ line_length l MOD m = 0`;;

(* HOL4 line 4110 *)
let sec_aligned_def = cake_def
  `sec_aligned noplen (Section _ ls:(A)sec) <=> ALL (line_aligned noplen) ls`;;

let _ = cake_add_simps [sec_aligned_def];;

let LTTP2AUX_line_aligned = prove
 (`!(c:(A)asm_config) x.
     enc_ok c /\ line_encd0 (asm_config_encode c) x /\ label_zero x
     ==> line_aligned (LENGTH (asm_config_encode c (asm_Inst asm_Skip))) x`,
  REWRITE_TAC[enc_ok_def] THEN REPEAT GEN_TAC THEN CASES_ON `x:(A)line` THEN
  REWRITE_TAC[line_encd0_def; label_zero_def; line_aligned_def; line_len_def;
              line_length_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOD_0] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4116 *)
let all_encd0_aligned = prove
 (`!(c:(A)asm_config) enc code.
     enc_ok c /\ enc = asm_config_encode c /\
     ALL (sec_encd0 enc) code /\ ALL sec_label_zero code
     ==> ALL (sec_aligned (LENGTH (enc (asm_Inst asm_Skip)))) code`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    fst(dest_const(fst(strip_comb(concl th)))) = "ALL"))) THEN
  SPEC_TAC(`code:((A)sec)list`,`code:((A)sec)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN CASES_ON `h:(A)sec` THEN
  REWRITE_TAC[sec_aligned_def; sec_encd0_def; sec_label_zero_def] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    fst(dest_const(fst(strip_comb(concl th)))) = "ALL"))) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[LTTP2AUX_line_aligned]);;

(* HOL4 line 4138 *)
let enc_lines_again_simp_aligned = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) ls res ok len.
     (!a. LENGTH (enc a) MOD len = 0) /\
     enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
     ALL (line_aligned len) ls
     ==> ALL (line_aligned len) res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN FS[ALL] THEN
  FS[line_aligned_def; line_length_def; line_len_def; MAX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4152 *)
let enc_secs_again_aligned = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) lines res ok len.
     (!a. LENGTH (enc a) MOD len = 0) /\
     enc_secs_again pos labs ffis enc lines = (res,ok) /\
     ALL (sec_aligned len) lines
     ==> ALL (sec_aligned len) res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN FS[ALL; sec_aligned_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  MATCH_MP_TAC enc_lines_again_simp_aligned THEN ASM_MESON_TAC[]);;

(* HOL4 line 4171 *)
let label_prefix_zero_def = cake_def
  `label_prefix_zero (ls:((A)line)list) <=>
     !n. n < LENGTH ls /\ (!m. m <= n ==> is_Label (EL m ls))
         ==> !m. m <= n ==> line_len (EL m ls) = 0`;;

(* HOL4 line 4177 *)
let sec_label_prefix_zero_def = cake_def
  `sec_label_prefix_zero (Section k ls:(A)sec) <=> label_prefix_zero ls`;;

let _ = cake_add_simps [sec_label_prefix_zero_def];;

let LTTP2AUX_FORALL_LE_0 = prove
 (`!(P:num->bool). (!m. m <= 0 ==> P m) <=> P 0`,
  REWRITE_TAC[LE] THEN MESON_TAC[]);;

let LTTP2AUX_FORALL_LE_SUC = prove
 (`!(P:num->bool) n. (!m. m <= SUC n ==> P m) <=> P 0 /\ (!m. m <= n ==> P (SUC m))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[LE_0; LE_SUC];
    STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LE_SUC]]);;

(* HOL4 line 4181 *)
let label_prefix_zero_cons = prove
 (`!l1 l2 len (ls:((A)line)list) a b c d e f g.
     (label_prefix_zero (CONS (lab_Label l1 l2 len) ls) <=>
      len = 0 /\ label_prefix_zero ls) /\
     (label_prefix_zero (CONS (Asm a b c) ls) <=> T) /\
     (label_prefix_zero (CONS (LabAsm d e f g) ls) <=> T)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[label_prefix_zero_def; LENGTH] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LE_0; EL; HD; is_Label_def];
    GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LE_0; EL; HD; is_Label_def]] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[LTTP2AUX_FORALL_LE_0; LT_0; EL; HD; is_Label_def; line_len_def];
      GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
      REWRITE_TAC[LT_SUC; LTTP2AUX_FORALL_LE_SUC; EL; HD; TL; is_Label_def] THEN
      MESON_TAC[]];
    STRIP_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[LTTP2AUX_FORALL_LE_0; LTTP2AUX_FORALL_LE_SUC; EL; HD; TL;
                    is_Label_def; line_len_def; LT_SUC] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 4209 *)
let label_prefix_zero_append_suff = prove
 (`!(l1:((A)line)list) l2.
     label_prefix_zero l1 /\ label_prefix_zero l2 ==> label_prefix_zero (APPEND l1 l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THEN CASES_ON `h:(A)line` THEN
  ASM_SIMP_TAC[label_prefix_zero_cons]);;

(* HOL4 line 4219 *)
let label_prefix_zero_append_suff2 = prove
 (`!(l1:((A)line)list) l2.
     label_prefix_zero l1 /\ EX ((~) o is_Label) l1 ==> label_prefix_zero (APPEND l1 l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; EX] THEN CASES_ON `h:(A)line` THEN
  ASM_SIMP_TAC[label_prefix_zero_cons; o_THM; is_Label_def]);;

let LTTP2AUX_label_prefix_zero_nil = prove
 (`label_prefix_zero ([]:((A)line)list)`,
  REWRITE_TAC[label_prefix_zero_def; LENGTH; LT]);;

let LTTP2AUX_label_prefix_zero_snoc = prove
 (`!(acc:((A)line)list) x.
     label_prefix_zero (REVERSE acc) /\ (ALL is_Label acc ==> label_prefix_zero [x])
     ==> label_prefix_zero (APPEND (REVERSE acc) [x])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `ALL is_Label (acc:((A)line)list)` THENL
   [MATCH_MP_TAC label_prefix_zero_append_suff THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC label_prefix_zero_append_suff2 THEN
    ASM_REWRITE_TAC[EXISTS_REVERSE; GSYM NOT_EVERY; EVERY_REVERSE]]);;

(* HOL4 line 4229 *)
let lines_upd_lab_len_label_prefix_zero = prove
 (`!pos (ls:((A)line)list) acc.
     (ALL is_Label acc ==> EVEN pos) /\ label_prefix_zero (REVERSE acc)
     ==> label_prefix_zero (FST (lines_upd_lab_len pos ls acc))`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[ALL; is_Label_def; REVERSE] THEN
  REPEAT CONJ_TAC THEN
  TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC[EVEN_ADD; ADD_CLAUSES; EVEN; ARITH] THEN
       NO_TAC) THEN
  MATCH_MP_TAC LTTP2AUX_label_prefix_zero_snoc THEN
  ASM_REWRITE_TAC[label_prefix_zero_cons; LTTP2AUX_label_prefix_zero_nil] THEN
  ASM_SIMP_TAC[]);;

(* HOL4 line 4244 *)
let upd_lab_len_label_prefix_zero = prove
 (`!pos (ss:((A)sec)list).
     EVEN pos /\ ALL sec_ends_with_label ss
     ==> ALL sec_label_prefix_zero (upd_lab_len pos ss)`,
  MATCH_MP_TAC upd_lab_len_ind THEN
  RW[upd_lab_len_def; ALL] THEN PAIRARG_TAC THEN FS[ALL; sec_label_prefix_zero_def] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
         SND_lines_upd_lab_len) THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
         EVEN_sec_length_lines_upd_lab_len) THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
         lines_upd_lab_len_label_prefix_zero) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sec_ends_with_label_def]) THEN
  ASM_REWRITE_TAC[ALL; MAP; SUM; ADD_CLAUSES; SUB_0; NULL; REVERSE;
                  LTTP2AUX_label_prefix_zero_nil] THEN
  REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[EVEN_ADD]]);;

(* HOL4 line 4265 *)
let enc_lines_again_simp_label_prefix_zero = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) ls res ok.
     enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\ label_prefix_zero ls
     ==> label_prefix_zero res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN FS[label_prefix_zero_cons]);;

(* HOL4 line 4277 *)
let enc_secs_again_label_prefix_zero = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) lines res ok.
     enc_secs_again pos labs ffis enc lines = (res,ok) /\
     ALL sec_label_prefix_zero lines
     ==> ALL sec_label_prefix_zero res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN FS[ALL; sec_label_prefix_zero_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  MATCH_MP_TAC enc_lines_again_simp_label_prefix_zero THEN ASM_MESON_TAC[]);;

(* HOL4 line 4294 *)
let line_length_pad_section = prove
 (`!nop (ls:((A)line)list) acc.
     LENGTH nop = 1 /\ ALL label_one ls /\ ALL line_length_leq ls /\
     SUM (MAP line_length acc) = SUM (MAP line_len acc) /\
     ALL is_Label acc /\ label_prefix_zero ls
     ==> SUM (MAP line_length (pad_section nop ls acc)) =
         SUM (MAP line_len ls) + SUM (MAP line_len acc)`,
  MATCH_MP_TAC pad_section_ind THEN RW[pad_section_def] THEN
  FS[rich_list_MAP_REVERSE; SUM_REVERSE; line_length_def; LENGTH_pad_bytes;
     label_prefix_zero_cons] THEN
  FS[line_length_add_nop; line_len_add_nop] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [`nop:byte list`; `xs:((A)line)list`;
                                  rand(rand(rand(lhs w)))] line_length_pad_section1)) THEN
  ASM_SIMP_TAC[ALL; is_Label_def; MAP; SUM; line_length_def; line_len_def;
               LENGTH_pad_bytes; ARITH] THEN
  ARITH_TAC);;

(* HOL4 line 4314 *)
let label_zero_line_length_pad_section = prove
 (`!nop (ls:((A)line)list) acc.
     0 < LENGTH nop /\ ALL label_zero ls /\ MAP line_length acc = MAP line_len acc /\
     ALL line_length_leq ls
     ==> MAP line_length (pad_section nop ls acc) =
         MAP line_len (APPEND (REVERSE acc) ls)`,
  MATCH_MP_TAC pad_section_ind THEN
  REWRITE_TAC[pad_section_def; ALL; label_zero_def; line_length_leq_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[rich_list_MAP_REVERSE; APPEND_NIL] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[MAP; CONS_11; line_length_def; line_len_def; LENGTH_pad_bytes; REVERSE;
               GSYM APPEND_ASSOC; APPEND; MAP_APPEND]);;

(* HOL4 line 4332 (the b of the JumpCmp clause, a register, is r here)     *)
let line_enc_with_nop_def = cake_def
  `(line_enc_with_nop (enc:(A)asm->byte list) labs ffis pos (Asm b bytes len) <=>
      enc_with_nop enc (cbw_to_asm b) bytes /\ LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (LabAsm lab_Halt _ bytes len) <=>
      enc_with_nop enc (asm_Jump (word_neg (word (pos + ffi_offset)))) bytes /\
      LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (LabAsm lab_Install _ bytes len) <=>
      enc_with_nop enc (asm_Jump (word_neg (word (pos + 2 * ffi_offset)))) bytes /\
      LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (LabAsm (CallFFI s) _ bytes len) <=>
      enc_with_nop enc
        (asm_Jump (word_neg (word (pos + (get_ffi_index ffis (ExtCall s) + 3) *
                                         ffi_offset)))) bytes /\
      LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (LabAsm (lab_Jump l) _ bytes len) <=>
      enc_with_nop enc (asm_Jump (word_add (word (find_pos l labs)) (word_neg (word pos))))
        bytes /\
      LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (LabAsm (lab_JumpCmp a r c l) _ bytes len) <=>
      enc_with_nop enc
        (asm_JumpCmp a r c (word_add (word (find_pos l labs)) (word_neg (word pos)))) bytes /\
      LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (LabAsm (lab_LocValue k l) _ bytes len) <=>
      enc_with_nop enc (asm_Loc k (word_add (word (find_pos l labs)) (word_neg (word pos))))
        bytes /\
      LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (LabAsm _ _ bytes len) <=> LENGTH bytes = len) /\
   (line_enc_with_nop enc labs ffis pos (lab_Label _ _ len:(A)line) <=> len = 0)`;;

(* HOL4 line 4357: val line_enc_with_nop_ind = theorem (line_enc_with_nop  *)
(* is not recursive: the case split of HOL4's TFL, one case per clause of   *)
(* line_enc_with_nop_def, the catch-all LabAsm clause completed)             *)
let line_enc_with_nop_ind = prove
 (`!(P:((A)asm->byte list)->(num spt)spt->ffiname list->num->(A)line->bool).
     (!enc labs ffis pos b bytes len. P enc labs ffis pos (Asm b bytes len)) /\
     (!enc labs ffis pos v bytes len. P enc labs ffis pos (LabAsm lab_Halt v bytes len)) /\
     (!enc labs ffis pos v bytes len. P enc labs ffis pos (LabAsm lab_Install v bytes len)) /\
     (!enc labs ffis pos s v bytes len.
        P enc labs ffis pos (LabAsm (CallFFI s) v bytes len)) /\
     (!enc labs ffis pos l v bytes len.
        P enc labs ffis pos (LabAsm (lab_Jump l) v bytes len)) /\
     (!enc labs ffis pos a r c l v bytes len.
        P enc labs ffis pos (LabAsm (lab_JumpCmp a r c l) v bytes len)) /\
     (!enc labs ffis pos k l v bytes len.
        P enc labs ffis pos (LabAsm (lab_LocValue k l) v bytes len)) /\
     (!enc labs ffis pos l v bytes len.
        P enc labs ffis pos (LabAsm (lab_Call l) v bytes len)) /\
     (!enc labs ffis pos v1 v2 len. P enc labs ffis pos (lab_Label v1 v2 len))
     ==> !v v1 v2 v3 v4. P v v1 v2 v3 v4`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN CASES_ON `v4:(A)line` THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `a0:(A)asm_with_lab` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4359 *)
let lines_enc_with_nop_def = cake_def
  `(lines_enc_with_nop (enc:(A)asm->byte list) labs ffis pos ([]:((A)line)list) <=> T) /\
   (lines_enc_with_nop enc labs ffis pos (CONS l ls) <=>
      line_enc_with_nop enc labs ffis pos l /\
      lines_enc_with_nop enc labs ffis (pos + line_length l) ls)`;;

let lines_enc_with_nop_ind = cake_ind "lines_enc_with_nop";;

(* HOL4 line 4366 *)
let lines_enc_with_nop_append = prove
 (`!(enc:(A)asm->byte list) labs ffis pos l1 l2.
     lines_enc_with_nop enc labs ffis pos (APPEND l1 l2) <=>
     lines_enc_with_nop enc labs ffis pos l1 /\
     lines_enc_with_nop enc labs ffis (pos + SUM (MAP line_length l1)) l2`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; lines_enc_with_nop_def; MAP; SUM; ADD_CLAUSES; ADD_ASSOC;
                  CONJ_ACI]);;

(* HOL4 line 4375 (the measure, the size of the sections, is given here)   *)
let all_enc_with_nop_def = cake_def_wf
  `MEASURE (\(enc:(A)asm->byte list,labs:(num spt)spt,ffis:ffiname list,pos:num,
              xs:((A)sec)list). list_size (sec_size (\x:A. 0)) xs)`
  TERM_TAC
  `(all_enc_with_nop (enc:(A)asm->byte list) labs ffis pos ([]:((A)sec)list) <=> T) /\
   (all_enc_with_nop enc labs ffis pos (CONS (Section k []) xs) <=>
      all_enc_with_nop enc labs ffis pos xs) /\
   (all_enc_with_nop enc labs ffis pos (CONS (Section k (CONS y ys)) xs) <=>
      line_enc_with_nop enc labs ffis pos y /\
      all_enc_with_nop enc labs ffis (pos + line_length y) (CONS (Section k ys) xs))`;;

(* HOL4 line 4384: val all_enc_with_nop_ind = theorem "all_enc_with_nop_ind" *)
let all_enc_with_nop_ind = cake_ind "all_enc_with_nop";;

(* HOL4 line 4386 *)
let all_enc_with_nop_alt = prove
 (`!(enc:(A)asm->byte list) labs ffis pos k ls ss.
     (all_enc_with_nop enc labs ffis pos [] <=> T) /\
     (all_enc_with_nop enc labs ffis pos (CONS (Section k ls) ss) <=>
      lines_enc_with_nop enc labs ffis pos ls /\
      all_enc_with_nop enc labs ffis (pos + SUM (MAP line_length ls)) ss)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_enc_with_nop_def] THEN
  SPEC_TAC(`pos:num`,`pos:num`) THEN SPEC_TAC(`ls:((A)line)list`,`ls:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[all_enc_with_nop_def; lines_enc_with_nop_def; MAP; SUM; ADD_CLAUSES;
                  ADD_ASSOC; CONJ_ACI]);;

(* HOL4 line 4400 *)
let line_enc_with_nop_length_ok = prove
 (`!(enc:(A)asm->byte list) labs ffis pos line.
     line_enc_with_nop enc labs ffis pos line ==> line_length_ok line`,
  REPEAT GEN_TAC THEN CASES_ON `line:(A)line` THEN
  REWRITE_TAC[line_enc_with_nop_def; line_length_ok_def; line_bytes_def; line_len_def;
              LENGTH] THEN
  TRY(CASES_ON `a0:(A)asm_with_lab`) THEN
  REWRITE_TAC[line_enc_with_nop_def] THEN MESON_TAC[]);;

(* HOL4 line 4408 *)
let lines_enc_with_nop_length_ok = prove
 (`!(enc:(A)asm->byte list) labs ffis pos ls.
     lines_enc_with_nop enc labs ffis pos ls ==> ALL line_length_ok ls`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_enc_with_nop_def; ALL] THEN
  ASM_MESON_TAC[line_enc_with_nop_length_ok]);;

(* HOL4 line 4420 *)
let line_enc_with_nop_label_zero = prove
 (`!(enc:(A)asm->byte list) labs ffis pos line.
     line_enc_with_nop enc labs ffis pos line ==> label_zero line`,
  REPEAT GEN_TAC THEN CASES_ON `line:(A)line` THEN
  REWRITE_TAC[line_enc_with_nop_def; label_zero_def]);;

(* HOL4 line 4428 *)
let lines_enc_with_nop_label_zero = prove
 (`!(enc:(A)asm->byte list) labs ffis pos lines.
     lines_enc_with_nop enc labs ffis pos lines ==> ALL label_zero lines`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_enc_with_nop_def; ALL] THEN
  ASM_MESON_TAC[line_enc_with_nop_label_zero]);;

(* HOL4 line 4437 *)
let all_enc_with_nop_label_zero = prove
 (`!(enc:(A)asm->byte list) labs ffis pos ls.
     all_enc_with_nop enc labs ffis pos ls ==> ALL sec_label_zero ls`,
  MATCH_MP_TAC all_enc_with_nop_ind THEN
  REWRITE_TAC[all_enc_with_nop_def; ALL; sec_label_zero_def] THEN
  MESON_TAC[line_enc_with_nop_label_zero]);;

(* HOL4 line 4449 *)
let line_ok_line_enc_with_nop = prove
 (`!(c:(A)asm_config) labs ffis pos line.
     line_ok c labs ffis pos line ==> line_enc_with_nop (asm_config_encode c) labs ffis pos line`,
  REPEAT GEN_TAC THEN CASES_ON `line:(A)line` THENL
   [REWRITE_TAC[line_ok_def; line_enc_with_nop_def] THEN MESON_TAC[];
    REWRITE_TAC[line_ok_def; line_enc_with_nop_def] THEN MESON_TAC[];
    CASES_ON `a0:(A)asm_with_lab` THEN
    REWRITE_TAC[line_ok_def; line_enc_with_nop_def; get_label_def; LET_DEF; LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN
    IMP_RES_TAC lab_lookup_IMP THEN
    FS[WORD_SUB_LZERO; word_sub_def; lab_inst_def] THEN FS[ADD_SYM]]);;

(* HOL4 line 4460 *)
let lines_ok_lines_enc_with_nop = prove
 (`!(c:(A)asm_config) labs ffis pos lines.
     lines_ok c labs ffis pos lines
     ==> lines_enc_with_nop (asm_config_encode c) labs ffis pos lines`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_ok_def; lines_enc_with_nop_def] THEN
  ASM_MESON_TAC[line_ok_line_enc_with_nop]);;

(* HOL4 line 4471 *)
let enc_with_nop_pad_bytes_length = prove
 (`!(enc:(A)asm->byte list) x.
     enc_with_nop enc x (pad_bytes (enc x) (LENGTH (enc x)) (enc (asm_Inst asm_Skip)))`,
  REWRITE_TAC[enc_with_nop_thm; pad_bytes_def; LET_DEF; LET_END_DEF; LE_REFL] THEN
  REPEAT GEN_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[REPLICATE; FLAT; APPEND_NIL]);;

(* HOL4 line 4478 *)
let enc_with_nop_pad_bytes = prove
 (`!nop (enc:(A)asm->byte list) x len.
     nop = enc (asm_Inst asm_Skip) /\ LENGTH (enc x) <= len /\
     LENGTH (enc x) MOD LENGTH nop = 0 /\ len MOD LENGTH nop = 0 /\ 0 < LENGTH nop
     ==> enc_with_nop enc x (pad_bytes (enc x) len nop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[enc_with_nop_thm; pad_bytes_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[REPLICATE; FLAT; APPEND_NIL]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))) THEN
  ASM_SIMP_TAC[TAKE_APPEND2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOD_EQ_0]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:num`) THEN
  EXISTS_TAC `b - a` THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB] THEN
  MATCH_MP_TAC TAKE_FLAT_REPLICATE_LEQ THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `b:num` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `b = b * 1`] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let LTTP2AUX_FLAT_REPLICATE_SNOC = prove
 (`!n (s:A list). APPEND (FLAT (REPLICATE n s)) s = FLAT (REPLICATE (SUC n) s)`,
  REWRITE_TAC[GSYM SNOC_REPLICATE; SNOC_APPEND; FLAT_APPEND; FLAT; APPEND_NIL]);;

let LTTP2AUX_enc_with_nop_APPEND_nop = prove
 (`!(enc:(A)asm->byte list) i bytes.
     enc_with_nop enc i bytes
     ==> enc_with_nop enc i (APPEND bytes (enc (asm_Inst asm_Skip)))`,
  REWRITE_TAC[enc_with_nop_thm] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `SUC n` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; LTTP2AUX_FLAT_REPLICATE_SNOC]);;

(* HOL4 line 4505 *)
let lines_enc_with_nop_add_nop = prove
 (`!(enc:(A)asm->byte list) labs ffis pos ls.
     LENGTH (enc (asm_Inst asm_Skip)) = 1 /\
     lines_enc_with_nop enc labs ffis pos (REVERSE ls)
     ==> lines_enc_with_nop enc labs ffis pos
           (REVERSE (add_nop (enc (asm_Inst asm_Skip)) ls))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[add_nop_def; REVERSE] THEN STRIP_TAC THEN
  CASES_ON `h:(A)line` THEN REWRITE_TAC[add_nop_def; REVERSE] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[lines_enc_with_nop_append; lines_enc_with_nop_def] THENL
   [REWRITE_TAC[line_enc_with_nop_def] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[line_enc_with_nop_def] THEN
    ASM_SIMP_TAC[LTTP2AUX_enc_with_nop_APPEND_nop; LENGTH_APPEND];
    CASES_ON `a0:(A)asm_with_lab` THEN REWRITE_TAC[line_enc_with_nop_def] THEN
    ASM_SIMP_TAC[LTTP2AUX_enc_with_nop_APPEND_nop; LENGTH_APPEND]]);;

let LTTP2AUX_lines_enc_with_nop_sum = prove
 (`!(enc:(A)asm->byte list) labs ffis pos ls.
     lines_enc_with_nop enc labs ffis pos ls
     ==> SUM (MAP line_length ls) = SUM (MAP line_len ls)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP lines_enc_with_nop_length_ok) THEN
  DISCH_THEN(MP_TAC o SPEC `0` o MATCH_MP sec_length_sum_line_length) THEN
  REWRITE_TAC[sec_length_sum_line_len; ADD_CLAUSES] THEN MESON_TAC[]);;

let LTTP2AUX_line_encd_pad_Asm = prove
 (`!(enc:(A)asm->byte list) labs ffis p p' x bytes len.
     line_encd enc labs ffis p (Asm x bytes len) /\ 0 < LENGTH (enc (asm_Inst asm_Skip))
     ==> line_enc_with_nop enc labs ffis p'
           (Asm x (pad_bytes bytes len (enc (asm_Inst asm_Skip))) len)`,
  REWRITE_TAC[line_encd_def; line_enc_with_nop_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))) THEN
  ASM_SIMP_TAC[enc_with_nop_pad_bytes_length; LENGTH_pad_bytes; LE_REFL]);;

let LTTP2AUX_line_encd_pad_LabAsm = prove
 (`!(enc:(A)asm->byte list) labs ffis p a w bytes len.
     line_encd enc labs ffis p (LabAsm a w bytes len) /\
     0 < LENGTH (enc (asm_Inst asm_Skip)) /\
     LENGTH bytes MOD LENGTH (enc (asm_Inst asm_Skip)) = 0 /\
     len MOD LENGTH (enc (asm_Inst asm_Skip)) = 0
     ==> line_enc_with_nop enc labs ffis p
           (LabAsm a w (pad_bytes bytes len (enc (asm_Inst asm_Skip))) len)`,
  REPEAT GEN_TAC THEN CASES_ON `a:(A)asm_with_lab` THEN
  REWRITE_TAC[line_encd_def; line_enc_with_nop_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LENGTH_pad_bytes] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)))) THEN
  MATCH_MP_TAC enc_with_nop_pad_bytes THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4532 *)
let lines_enc_with_nop_pad_section1 = prove
 (`!nop (code:((A)line)list) aux pos enc labs ffis.
     nop = enc (asm_Inst asm_Skip) /\ LENGTH nop = 1 /\
     lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
     lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
     ~ALL is_Label aux /\ ALL label_one code
     ==> lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def] THEN MESON_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_one_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    line_enc_with_nop_def; ALL; is_Label_def; MAP; SUM; line_len_def;
                    ADD_CLAUSES] THEN
    COND_CASES_TAC THENL
     [GVS[ADD_CLAUSES];
      SUBGOAL_THEN `len = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH ((enc:(A)asm->byte list) (asm_Inst asm_Skip)) = 1` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[line_len_add_nop1; EVERY_is_Label_add_nop_preserved;
                   lines_enc_with_nop_add_nop] THEN
      ASM_REWRITE_TAC[ADD_ASSOC]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_one_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_Asm THEN
      EXISTS_TAC `pos + SUM (MAP line_len (aux:((A)line)list))` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ARITH_RULE `0 < 1`]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_one_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP LTTP2AUX_lines_enc_with_nop_sum) THEN
      REWRITE_TAC[rich_list_MAP_REVERSE; SUM_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_LabAsm THEN
      ASM_MESON_TAC[ARITH_RULE `0 < 1`; MOD_1]]]);;

(* HOL4 line 4567 *)
let lines_enc_with_nop_pad_section01 = prove
 (`!nop (code:((A)line)list) aux pos enc labs ffis.
     nop = enc (asm_Inst asm_Skip) /\ 0 < LENGTH nop /\
     ALL (line_aligned (LENGTH nop)) code /\
     lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
     lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
     ~ALL is_Label aux /\ ALL label_zero code
     ==> lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def] THEN MESON_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_zero_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    line_enc_with_nop_def; ALL; is_Label_def; MAP; SUM; line_len_def;
                    ADD_CLAUSES] THEN
    GVS[ADD_CLAUSES];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_zero_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_Asm THEN
      EXISTS_TAC `pos + SUM (MAP line_len (aux:((A)line)list))` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_zero_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP LTTP2AUX_lines_enc_with_nop_sum) THEN
      REWRITE_TAC[rich_list_MAP_REVERSE; SUM_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_LabAsm THEN
      RULE_ASSUM_TAC(REWRITE_RULE[line_aligned_def; line_len_def; line_length_def]) THEN
      ASM_MESON_TAC[]]]);;

(* HOL4 line 4595 *)
let lines_enc_with_nop_pad_section0 = prove
 (`!nop (code:((A)line)list) aux pos enc labs ffis.
     nop = enc (asm_Inst asm_Skip) /\ 0 < LENGTH nop /\
     ALL (line_aligned (LENGTH nop)) code /\
     lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
     lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
     ALL is_Label aux /\ ALL label_zero code
     ==> lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def] THEN MESON_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_zero_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    line_enc_with_nop_def; ALL; is_Label_def; MAP; SUM; line_len_def;
                    ADD_CLAUSES] THEN
    GVS[ADD_CLAUSES];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_zero_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN MATCH_MP_TAC lines_enc_with_nop_pad_section01 THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_Asm THEN
      EXISTS_TAC `pos + SUM (MAP line_len (aux:((A)line)list))` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_zero_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN MATCH_MP_TAC lines_enc_with_nop_pad_section01 THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP LTTP2AUX_lines_enc_with_nop_sum) THEN
      REWRITE_TAC[rich_list_MAP_REVERSE; SUM_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_LabAsm THEN
      RULE_ASSUM_TAC(REWRITE_RULE[line_aligned_def; line_len_def; line_length_def]) THEN
      ASM_MESON_TAC[]]]);;

(* HOL4 line 4626 *)
let lines_enc_with_nop_pad_section = prove
 (`!nop (code:((A)line)list) aux pos enc labs ffis.
     nop = enc (asm_Inst asm_Skip) /\ LENGTH nop = 1 /\
     lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code /\
     lines_enc_with_nop enc labs ffis pos (REVERSE aux) /\
     ALL is_Label aux /\ ALL label_one code /\ label_prefix_zero code
     ==> lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def] THEN MESON_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_one_def; line_len_def; pad_section_def;
                label_prefix_zero_cons] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    line_enc_with_nop_def; ALL; is_Label_def; MAP; SUM; line_len_def;
                    ADD_CLAUSES] THEN
    GVS[ADD_CLAUSES];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_one_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN MATCH_MP_TAC lines_enc_with_nop_pad_section1 THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_Asm THEN
      EXISTS_TAC `pos + SUM (MAP line_len (aux:((A)line)list))` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ARITH_RULE `0 < 1`]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[lines_encd_def; ALL; label_one_def; line_len_def; pad_section_def] THEN
    STRIP_TAC THEN MATCH_MP_TAC lines_enc_with_nop_pad_section1 THEN
    ASM_REWRITE_TAC[REVERSE; lines_enc_with_nop_append; lines_enc_with_nop_def;
                    ALL; is_Label_def; MAP; SUM; line_len_def] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP LTTP2AUX_lines_enc_with_nop_sum) THEN
      REWRITE_TAC[rich_list_MAP_REVERSE; SUM_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC LTTP2AUX_line_encd_pad_LabAsm THEN
      ASM_MESON_TAC[ARITH_RULE `0 < 1`; MOD_1]]]);;

(* HOL4 line 4653 *)
let all_enc_with_nop_pad_code = prove
 (`!nop (code:((A)sec)list) pos enc labs ffis.
     0 < LENGTH nop /\ nop = enc (asm_Inst asm_Skip) /\
     (~(LENGTH nop = 1)
      ==> ALL (sec_aligned (LENGTH nop)) code /\ ALL sec_label_zero code) /\
     ALL sec_label_one code /\
     ALL sec_length_leq code /\
     ALL sec_label_prefix_zero code /\
     all_encd enc labs ffis pos code
     ==> all_enc_with_nop enc labs ffis pos (pad_code nop code)`,
  MATCH_MP_TAC pad_code_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[pad_code_def; all_enc_with_nop_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[pad_code_def; all_enc_with_nop_alt; all_encd_def; ALL; sec_aligned_def;
              sec_label_zero_def; sec_label_one_def; sec_length_leq_def;
              sec_label_prefix_zero_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))) THEN
  SUBGOAL_THEN
   `SUM (MAP line_length (pad_section (enc (asm_Inst asm_Skip)) xs ([]:((A)line)list))) =
    SUM (MAP line_len (xs:((A)line)list)) /\
    lines_enc_with_nop enc labs ffis pos (pad_section (enc (asm_Inst asm_Skip)) xs [])`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `LENGTH ((enc:(A)asm->byte list) (asm_Inst asm_Skip)) = 1` THENL
     [MP_TAC(ISPECL [`(enc:(A)asm->byte list) (asm_Inst asm_Skip)`; `xs:((A)line)list`;
                     `[]:((A)line)list`] line_length_pad_section) THEN
      ASM_REWRITE_TAC[ALL; MAP; SUM; ADD_CLAUSES] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lines_enc_with_nop_pad_section THEN
      ASM_REWRITE_TAC[MAP; SUM; ADD_CLAUSES; REVERSE; lines_enc_with_nop_def; ALL];
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`(enc:(A)asm->byte list) (asm_Inst asm_Skip)`; `xs:((A)line)list`;
                     `[]:((A)line)list`] label_zero_line_length_pad_section) THEN
      ASM_REWRITE_TAC[MAP; REVERSE; APPEND] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC lines_enc_with_nop_pad_section0 THEN
      ASM_REWRITE_TAC[MAP; SUM; ADD_CLAUSES; REVERSE; lines_enc_with_nop_def; ALL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4684 *)
let line_lab_len_pos_ok_def = cake_def
  `(line_lab_len_pos_ok pos (lab_Label _ _ l:(A)line) <=>
      if EVEN pos then l = 0 else l = 1) /\
   (line_lab_len_pos_ok _ (_:(A)line) <=> T)`;;

(* HOL4 line 4690 *)
let lab_len_pos_ok_def = cake_def
  `(lab_len_pos_ok pos ([]:((A)line)list) <=> T) /\
   (lab_len_pos_ok pos (CONS l ls) <=>
      line_lab_len_pos_ok pos l /\ lab_len_pos_ok (pos + line_len l) ls)`;;

let lab_len_pos_ok_ind = cake_ind "lab_len_pos_ok";;

(* HOL4 line 4697 *)
let lab_len_pos_ok_append = prove
 (`!(l1:((A)line)list) pos l2.
     lab_len_pos_ok pos (APPEND l1 l2) <=>
     lab_len_pos_ok pos l1 /\ lab_len_pos_ok (pos + SUM (MAP line_len l1)) l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; lab_len_pos_ok_def; MAP; SUM; ADD_CLAUSES; ADD_ASSOC;
                  CONJ_ACI]);;

(* HOL4 line 4707 *)
let all_lab_len_pos_ok_def = cake_def
  `(all_lab_len_pos_ok _ ([]:((A)sec)list) <=> T) /\
   (all_lab_len_pos_ok pos (CONS (Section k ls) ss) <=>
      lab_len_pos_ok pos ls /\ all_lab_len_pos_ok (pos + sec_length ls 0) ss)`;;

(* HOL4 line 4714: val all_lab_len_pos_ok_ind = theorem *)
let all_lab_len_pos_ok_ind = cake_ind "all_lab_len_pos_ok";;

(* HOL4 line 4718 *)
let lines_upd_lab_len_pos_ok = prove
 (`!pos (lines:((A)line)list). lab_len_pos_ok pos (FST (lines_upd_lab_len pos lines []))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[lines_upd_lab_len_def; REVERSE; lab_len_pos_ok_def] THEN
  CASES_ON `h:(A)line` THEN REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[lines_upd_lab_len_AUX] THEN
  ASM_REWRITE_TAC[REVERSE; APPEND; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                  line_len_def] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 4729 *)
let upd_lab_len_pos_ok = prove
 (`!pos (code:((A)sec)list). all_lab_len_pos_ok pos (upd_lab_len pos code)`,
  MATCH_MP_TAC upd_lab_len_ind THEN
  RW[upd_lab_len_def; all_lab_len_pos_ok_def] THEN PAIRARG_TAC THEN
  FS[all_lab_len_pos_ok_def] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
         SND_lines_upd_lab_len) THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`] lines_upd_lab_len_pos_ok) THEN
  ASM_REWRITE_TAC[sec_length_sum_line_len; MAP; SUM; SUB_0; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[]);;

(* HOL4 line 4743 *)
let enc_lines_again_simp_pos_ok = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines res.
     enc_lines_again_simp labs ffis pos enc lines = (res,T) /\ lab_len_pos_ok pos lines
     ==> lab_len_pos_ok pos res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  GVS[lab_len_pos_ok_def; line_lab_len_pos_ok_def; line_len_def]);;

(* HOL4 line 4756 *)
let enc_secs_again_pos_ok = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) code res.
     enc_secs_again pos labs ffis enc code = (res,T) /\ all_lab_len_pos_ok pos code
     ==> all_lab_len_pos_ok pos res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN
  FS[all_lab_len_pos_ok_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  FS[all_lab_len_pos_ok_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  RVEQ_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP enc_lines_again_simp_len) THEN
  FS[sec_length_sum_line_len] THEN CONJ_TAC THENL
   [MATCH_MP_TAC enc_lines_again_simp_pos_ok THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ISPECL [`SUM (MAP line_len (lines:((A)line)list))`; `pos:num`] ADD_SYM] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 4772 *)
let lab_len_pos_ok_even_prefix_zero = prove
 (`!pos (ls:((A)line)list). EVEN pos /\ lab_len_pos_ok pos ls ==> label_prefix_zero ls`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[lab_len_pos_ok_def; LTTP2AUX_label_prefix_zero_nil] THEN
  CASES_ON `h:(A)line` THEN
  REWRITE_TAC[lab_len_pos_ok_def; label_prefix_zero_cons; line_lab_len_pos_ok_def;
              line_len_def] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `pos + a2` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let LTTP2AUX_lab_len_pos_ok_add_nop = prove
 (`!nop (aux:((A)line)list) pos.
     ~NULL aux /\ ~is_Label (HD aux) /\ lab_len_pos_ok pos (REVERSE aux)
     ==> lab_len_pos_ok pos (REVERSE (add_nop nop aux))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD] THEN
  CASES_ON `h:(A)line` THEN
  REWRITE_TAC[is_Label_def; add_nop_def; REVERSE; lab_len_pos_ok_append;
              lab_len_pos_ok_def; line_lab_len_pos_ok_def] THEN
  MESON_TAC[]);;

(* HOL4 line 4785 *)
let pad_section_pos_ok = prove
 (`!nop (lines:((A)line)list) aux pos.
     lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
     lab_len_pos_ok pos (REVERSE aux) /\
     ALL label_zero aux /\
     (NULL aux \/ is_Label (HD aux) ==> label_prefix_zero lines)
     ==> lab_len_pos_ok pos (pad_section nop lines aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def] THEN MESON_TAC[];
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def; label_prefix_zero_cons] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE; ADD_CLAUSES] THEN
    ASM_CASES_TAC `len = 0` THENL
     [SUBGOAL_THEN `EVEN (pos + SUM (MAP line_len (aux:((A)line)list)))` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[ARITH];
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 0`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lab_len_pos_ok_even_prefix_zero THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~EVEN (pos + SUM (MAP line_len (aux:((A)line)list))) /\ len = 1`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~NULL (aux:((A)line)list) /\ ~is_Label (HD aux)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~ALL is_Label (aux:((A)line)list)` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      SPEC_TAC(`aux:((A)line)list`,`aux:((A)line)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD; ALL] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 1`)) THEN
    SUBGOAL_THEN `EVEN ((pos + SUM (MAP line_len (aux:((A)line)list))) + 1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[EVEN_ADD; ARITH]; ALL_TAC] THEN
    SUBGOAL_THEN `label_prefix_zero (xs:((A)line)list)` ASSUME_TAC THENL
     [MATCH_MP_TAC lab_len_pos_ok_even_prefix_zero THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[line_len_add_nop1; EVERY_label_zero_add_nop; LTTP2AUX_lab_len_pos_ok_add_nop;
                 ADD_ASSOC];
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                    lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                    line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                    lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                    line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a + b + c = (a + c) + b:num`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 4821 *)
let line_len_pad_section = prove
 (`!nop (xs:((A)line)list) aux.
     LENGTH nop = 1 /\ ALL label_one xs /\ (ALL is_Label aux ==> label_prefix_zero xs)
     ==> SUM (MAP line_len (pad_section nop xs aux)) =
         SUM (MAP line_len xs) + SUM (MAP line_len aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def; rich_list_MAP_REVERSE; SUM_REVERSE; MAP; SUM;
                ADD_CLAUSES];
    DISCH_TAC THEN
    REWRITE_TAC[pad_section_def; ALL; label_one_def; is_Label_def; label_prefix_zero_cons;
                MAP; SUM; line_len_def] THEN
    STRIP_TAC THEN ASM_CASES_TAC `len = 0` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 0`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        can (find_term ((=) `pad_section:byte list->((A)line)list->((A)line)list->((A)line)list`))
          (concl th))) THEN
      ASM_REWRITE_TAC[ALL; is_Label_def; ADD_CLAUSES; MAP; SUM; line_len_def];
      SUBGOAL_THEN `len = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~ALL is_Label (aux:((A)line)list)` ASSUME_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        can (find_term ((=) `pad_section:byte list->((A)line)list->((A)line)list->((A)line)list`))
          (concl th))) THEN
      ASM_SIMP_TAC[ALL; is_Label_def; EVERY_is_Label_add_nop_preserved; line_len_add_nop1;
                   ARITH_RULE `~(1 = 0)`; MAP; SUM; line_len_def] THEN
      ARITH_TAC];
    DISCH_TAC THEN REWRITE_TAC[pad_section_def; ALL; MAP; SUM; line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term ((=) `pad_section:byte list->((A)line)list->((A)line)list->((A)line)list`))
        (concl th))) THEN
    ASM_REWRITE_TAC[ALL; is_Label_def; MAP; SUM; line_len_def] THEN ARITH_TAC;
    DISCH_TAC THEN REWRITE_TAC[pad_section_def; ALL; MAP; SUM; line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term ((=) `pad_section:byte list->((A)line)list->((A)line)list->((A)line)list`))
        (concl th))) THEN
    ASM_REWRITE_TAC[ALL; is_Label_def; MAP; SUM; line_len_def] THEN ARITH_TAC]);;

(* HOL4 line 4838 *)
let all_lab_len_pos_ok_pad_code = prove
 (`!nop (code:((A)sec)list) pos.
     all_lab_len_pos_ok pos code /\
     (~(LENGTH nop = 1) ==> ALL sec_label_zero code) /\
     ALL sec_label_one code /\
     ALL sec_label_prefix_zero code
     ==> all_lab_len_pos_ok pos (pad_code nop code)`,
  MATCH_MP_TAC pad_code_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[pad_code_def; all_lab_len_pos_ok_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[pad_code_def; all_lab_len_pos_ok_def; ALL; sec_label_zero_def;
              sec_label_one_def; sec_label_prefix_zero_def] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC pad_section_pos_ok THEN
    ASM_REWRITE_TAC[MAP; SUM; ADD_CLAUSES; REVERSE; lab_len_pos_ok_def; ALL; NULL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sec_length (pad_section nop xs ([]:((A)line)list)) 0 = sec_length (xs:((A)line)list) 0`
  SUBST1_TAC THENL
   [REWRITE_TAC[sec_length_sum_line_len] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC `LENGTH (nop:byte list) = 1` THENL
     [MP_TAC(ISPECL [`nop:byte list`; `xs:((A)line)list`; `[]:((A)line)list`]
                    line_len_pad_section) THEN
      ASM_REWRITE_TAC[ALL; MAP; SUM; ADD_CLAUSES];
      MP_TAC(ISPECL [`nop:byte list`; `xs:((A)line)list`; `[]:((A)line)list`]
                    line_len_pad_section0) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        is_neg(lhand(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MAP; SUM; ADD_CLAUSES]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 4863 *)
let line_offset_ok_def = cake_def
  `(line_offset_ok (labs:(num spt)spt) ffis pos (LabAsm a w bytes _:(A)line) <=>
      w = get_jump_offset a ffis labs pos) /\
   (line_offset_ok _ _ _ (_:(A)line) <=> T)`;;

(* HOL4 line 4869 *)
let lines_offset_ok_def = cake_def
  `(lines_offset_ok (labs:(num spt)spt) ffis pos ([]:((A)line)list) <=> T) /\
   (lines_offset_ok labs ffis pos (CONS l ls) <=>
      line_offset_ok labs ffis pos l /\ lines_offset_ok labs ffis (pos + line_len l) ls)`;;

let lines_offset_ok_ind = cake_ind "lines_offset_ok";;

(* HOL4 line 4876 *)
let lines_offset_ok_append = prove
 (`!(labs:(num spt)spt) ffis pos (l1:((A)line)list) l2.
     lines_offset_ok labs ffis pos (APPEND l1 l2) <=>
     lines_offset_ok labs ffis pos l1 /\
     lines_offset_ok labs ffis (pos + SUM (MAP line_len l1)) l2`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; lines_offset_ok_def; MAP; SUM; ADD_CLAUSES; ADD_ASSOC;
                  CONJ_ACI]);;

(* HOL4 line 4885 *)
let lab_to_targetProof_offset_ok_def = cake_def
  `(lab_to_targetProof_offset_ok (labs:(num spt)spt) ffis pos ([]:((A)sec)list) <=> T) /\
   (lab_to_targetProof_offset_ok labs ffis pos (CONS (Section k ls) ss) <=>
      lines_offset_ok labs ffis pos ls /\
      lab_to_targetProof_offset_ok labs ffis (pos + SUM (MAP line_len ls)) ss)`;;

(* HOL4 line 4892: val offset_ok_ind = theorem "offset_ok_ind" *)
let lab_to_targetProof_offset_ok_ind = cake_ind "lab_to_targetProof_offset_ok";;

(* HOL4 line 4896 *)
let enc_lines_again_simp_offset_ok = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines res ok.
     enc_lines_again_simp labs ffis pos enc lines = (res,ok)
     ==> lines_offset_ok labs ffis pos res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  FS[lines_offset_ok_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  GVS[lines_offset_ok_def; line_offset_ok_def; line_len_def]);;

(* HOL4 line 4910 *)
let enc_secs_again_offset_ok = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) ls res ok.
     enc_secs_again pos labs ffis enc ls = (res,ok)
     ==> lab_to_targetProof_offset_ok labs ffis pos res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN
  FS[lab_to_targetProof_offset_ok_def] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN
  RVEQ_TAC THEN FS[lab_to_targetProof_offset_ok_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  RVEQ_TAC THEN FS[sec_length_sum_line_len] THEN CONJ_TAC THENL
   [MATCH_MP_TAC enc_lines_again_simp_offset_ok THEN ASM_MESON_TAC[];
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]]);;

let LTTP2AUX_lines_offset_ok_add_nop = prove
 (`!(labs:(num spt)spt) ffis nop (aux:((A)line)list) pos.
     ~NULL aux /\ ~is_Label (HD aux) /\ lines_offset_ok labs ffis pos (REVERSE aux)
     ==> lines_offset_ok labs ffis pos (REVERSE (add_nop nop aux))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD] THEN
  CASES_ON `h:(A)line` THEN
  REWRITE_TAC[is_Label_def; add_nop_def; REVERSE; lines_offset_ok_append;
              lines_offset_ok_def; line_offset_ok_def] THEN
  MESON_TAC[]);;

(* HOL4 line 4930 *)
let lines_offset_ok_pad_section = prove
 (`!nop (lines:((A)line)list) aux labs ffis pos.
     lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
     lab_len_pos_ok pos (REVERSE aux) /\ ALL label_zero aux /\
     (~NULL lines /\ is_Label (HD lines) /\ line_len (HD lines) = 1
      ==> ~NULL aux /\ ~is_Label (HD aux)) /\
     lines_offset_ok labs ffis pos (APPEND (REVERSE aux) lines)
     ==> lines_offset_ok labs ffis pos (pad_section nop lines aux)`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def; APPEND_NIL] THEN MESON_TAC[];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def; NULL; HD; is_Label_def; lines_offset_ok_append;
                lines_offset_ok_def; line_offset_ok_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE; ADD_CLAUSES;
                lines_offset_ok_append; lines_offset_ok_def; line_offset_ok_def] THEN
    SUBGOAL_THEN `~(~NULL (xs:((A)line)list) /\ is_Label (HD xs) /\ line_len (HD xs) = 1)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `lab_len_pos_ok ((pos + SUM (MAP line_len (aux:((A)line)list))) + len)
                     (xs:((A)line)list)` THEN
      UNDISCH_TAC `if EVEN (pos + SUM (MAP line_len (aux:((A)line)list)))
                   then len = 0 else len = 1` THEN
      SPEC_TAC(`xs:((A)line)list`,`xs:((A)line)list`) THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC[NULL; HD] THEN CASES_ON `h:(A)line` THEN
      REWRITE_TAC[is_Label_def; line_len_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def] THEN
      ASM_CASES_TAC `EVEN (pos + SUM (MAP line_len (aux:((A)line)list)))` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; GSYM ADD1; EVEN] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `len = 0` THENL
     [SUBGOAL_THEN `EVEN (pos + SUM (MAP line_len (aux:((A)line)list)))` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[ARITH];
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 0`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[rich_list_MAP_REVERSE; SUM_REVERSE]) THEN
      ASM_REWRITE_TAC[SUM_APPEND; SUM_REVERSE; SUM; ADD_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN `~EVEN (pos + SUM (MAP line_len (aux:((A)line)list))) /\ len = 1`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 1`)) THEN
    SUBGOAL_THEN `~NULL (aux:((A)line)list) /\ ~is_Label (HD aux)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~ALL is_Label (aux:((A)line)list)` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      SPEC_TAC(`aux:((A)line)list`,`aux:((A)line)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD; ALL] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `EVEN ((pos + SUM (MAP line_len (aux:((A)line)list))) + 1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[EVEN_ADD; ARITH]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rich_list_MAP_REVERSE; SUM_REVERSE]) THEN
    ASM_SIMP_TAC[line_len_add_nop1; EVERY_label_zero_add_nop; LTTP2AUX_lab_len_pos_ok_add_nop;
                 LTTP2AUX_lines_offset_ok_add_nop; ADD_ASSOC; SUM_APPEND; SUM_REVERSE; SUM;
                 ADD_CLAUSES; GSYM rich_list_MAP_REVERSE];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lines_offset_ok_append; lines_offset_ok_def;
                                line_offset_ok_def; line_len_def; rich_list_MAP_REVERSE;
                                SUM_REVERSE]) THEN
    ASM_REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                    lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                    line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE; SUM_APPEND;
                    lines_offset_ok_append; lines_offset_ok_def; line_offset_ok_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_AC; ADD_CLAUSES]) THEN
    ASM_REWRITE_TAC[ADD_AC; ADD_CLAUSES];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lines_offset_ok_append; lines_offset_ok_def;
                                line_offset_ok_def; line_len_def; rich_list_MAP_REVERSE;
                                SUM_REVERSE]) THEN
    ASM_REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                    lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                    line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE; SUM_APPEND;
                    lines_offset_ok_append; lines_offset_ok_def; line_offset_ok_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_AC; ADD_CLAUSES]) THEN
    ASM_REWRITE_TAC[ADD_AC; ADD_CLAUSES]]);;

(* HOL4 line 4963 *)
let offset_ok_pad_code = prove
 (`!(labs:(num spt)spt) ffis pos (code:((A)sec)list) nop.
     (~(LENGTH nop = 1) ==> ALL sec_label_zero code) /\
     ALL sec_label_one code /\
     ALL sec_label_prefix_zero code /\
     all_lab_len_pos_ok pos code /\
     lab_to_targetProof_offset_ok labs ffis pos code
     ==> lab_to_targetProof_offset_ok labs ffis pos (pad_code nop code)`,
  MATCH_MP_TAC lab_to_targetProof_offset_ok_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[pad_code_def; lab_to_targetProof_offset_ok_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[pad_code_def; lab_to_targetProof_offset_ok_def; all_lab_len_pos_ok_def; ALL;
              sec_label_zero_def; sec_label_one_def; sec_label_prefix_zero_def;
              sec_length_sum_line_len; ADD_CLAUSES] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `SUM (MAP line_len (pad_section nop ls ([]:((A)line)list))) =
                SUM (MAP line_len (ls:((A)line)list))` SUBST1_TAC THENL
   [ASM_CASES_TAC `LENGTH (nop:byte list) = 1` THENL
     [MP_TAC(ISPECL [`nop:byte list`; `ls:((A)line)list`; `[]:((A)line)list`]
                    line_len_pad_section) THEN
      ASM_REWRITE_TAC[ALL; MAP; SUM; ADD_CLAUSES];
      MP_TAC(ISPECL [`nop:byte list`; `ls:((A)line)list`; `[]:((A)line)list`]
                    line_len_pad_section0) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        is_neg(lhand(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MAP; SUM; ADD_CLAUSES]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC lines_offset_ok_pad_section THEN
    ASM_REWRITE_TAC[MAP; SUM; ADD_CLAUSES; REVERSE; lab_len_pos_ok_def; ALL; NULL;
                    APPEND] THEN
    UNDISCH_TAC `label_prefix_zero (ls:((A)line)list)` THEN
    SPEC_TAC(`ls:((A)line)list`,`ls:((A)line)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD] THEN CASES_ON `h:(A)line` THEN
    REWRITE_TAC[label_prefix_zero_cons; is_Label_def; line_len_def] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 4992 *)
let line_labs_exist_def = cake_def
  `(line_labs_exist (labs:(num spt)spt) (LabAsm a _ _ _:(A)line) <=>
      !n1 n2. (n1,n2) IN labs_of a ==> ~(lab_lookup n1 n2 labs = NONE)) /\
   (line_labs_exist _ (_:(A)line) <=> T)`;;

let _ = cake_add_simps [line_labs_exist_def];;

(* HOL4 line 4998: val line_labs_exist_ind = theorem (not recursive: the    *)
(* cases of the line argument)                                               *)
let line_labs_exist_ind = prove
 (`!(P:(num spt)spt->(A)line->bool).
     (!labs a w bytes l. P labs (LabAsm a w bytes l)) /\
     (!labs n1 n2 l. P labs (lab_Label n1 n2 l)) /\
     (!labs b bytes l. P labs (Asm b bytes l))
     ==> !labs l. P labs l`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `l:(A)line` THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5000 *)
let sec_labs_exist_def = cake_def
  `sec_labs_exist (labs:(num spt)spt) (Section _ ls:(A)sec) <=>
     ALL (line_labs_exist labs) ls`;;

let _ = cake_add_simps [sec_labs_exist_def];;

(* HOL4 line 5004: Overload all_labs_exist = \labs code. EVERY             *)
(* (sec_labs_exist labs) code (written out where used)                       *)

let LTTP2AUX_restrict_zero_UNION = prove
 (`!s t. restrict_zero (s UNION t) = restrict_zero s UNION restrict_zero t`,
  REWRITE_TAC[restrict_zero_def] THEN SET_TAC[]);;

let LTTP2AUX_restrict_zero_EMPTY = prove
 (`restrict_zero {} = {}`,
  REWRITE_TAC[restrict_zero_def] THEN SET_TAC[]);;

(* HOL4 line 5007 *)
let zero_labs_acc_of_eq_zero_labs_of = prove
 (`!(l:(A)asm_with_lab) acc.
     domain (zero_labs_acc_of l acc) =
     IMAGE FST (restrict_zero (labs_of l)) UNION domain acc`,
  GEN_TAC THEN CASES_ON `l:(A)asm_with_lab` THEN
  REWRITE_TAC[zero_labs_acc_of_def; labs_of_def; LTTP2AUX_restrict_zero_EMPTY;
              IMAGE_CLAUSES; UNION_EMPTY] THENL [CASES_ON `a:lab`; CASES_ON `a3:lab`; CASES_ON `a1:lab`] THEN
  REWRITE_TAC[zero_labs_acc_of_def; labs_of_def; LTTP2AUX_restrict_zero_EMPTY;
              IMAGE_CLAUSES; UNION_EMPTY] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[domain_insert; restrict_zero_def; EXTENSION; IN_IMAGE; IN_UNION;
                  IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FST; SND; PAIR_EQ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5017 *)
let line_get_zero_labs_acc_eq_line_get_zero_labels = prove
 (`!(l:(A)line) acc.
     domain (line_get_zero_labs_acc l acc) =
     IMAGE FST (restrict_zero (line_get_labels l)) UNION domain acc`,
  GEN_TAC THEN CASES_ON `l:(A)line` THEN
  REWRITE_TAC[line_get_zero_labs_acc_def; line_get_labels_def;
              zero_labs_acc_of_eq_zero_labs_of; LTTP2AUX_restrict_zero_EMPTY;
              IMAGE_CLAUSES; UNION_EMPTY]);;

(* HOL4 line 5026 *)
let sec_get_zero_labs_acc_eq_sec_get_zero_labels = prove
 (`!(sec:(A)sec) acc.
     domain (sec_get_zero_labs_acc sec acc) =
     IMAGE FST (restrict_zero (sec_get_labels sec)) UNION domain acc`,
  GEN_TAC THEN CASES_ON `sec:(A)sec` THEN
  REWRITE_TAC[sec_get_zero_labs_acc_def; sec_get_labels_def] THEN
  SPEC_TAC(`a1:((A)line)list`,`l:((A)line)list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; set_of_list; IMAGE_CLAUSES; UNIONS_0; UNIONS_INSERT;
                  LTTP2AUX_restrict_zero_EMPTY; LTTP2AUX_restrict_zero_UNION; IMAGE_UNION;
                  UNION_EMPTY; line_get_zero_labs_acc_eq_line_get_zero_labels] THEN
  REWRITE_TAC[UNION_ACI]);;

(* HOL4 line 5037 (HOL4 FOLDR f e l is ITLIST f l e) *)
let get_zero_labs_acc_eq_get_zero_labels = prove
 (`!(code:((A)sec)list) acc.
     domain (ITLIST sec_get_zero_labs_acc code acc) =
     IMAGE FST (restrict_zero (lab_get_labels code)) UNION domain acc`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ITLIST; lab_get_labels_def; set_of_list; IMAGE_CLAUSES; UNIONS_0;
                LTTP2AUX_restrict_zero_EMPTY; UNION_EMPTY];
    ASM_REWRITE_TAC[ITLIST; get_labels_cons; LTTP2AUX_restrict_zero_UNION; IMAGE_UNION;
                    sec_get_zero_labs_acc_eq_sec_get_zero_labels] THEN
    REWRITE_TAC[UNION_ACI]]);;

let LTTP2AUX_lab_lookup_not_none = prove
 (CASE_TERM `!n1 n2 labs.
     ~(lab_lookup n1 n2 labs = NONE) <=>
     (match lookup n1 labs with NONE -> F | SOME l -> ~(lookup n2 l = NONE))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lab_lookup_def] THEN
  CASES_ON `lookup n1 (labs:(num spt)spt)` THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 5047 *)
let zero_labs_acc_exist_eq = prove
 (`!labs (code:((A)sec)list).
     zero_labs_acc_exist labs code <=>
     restrict_zero (lab_get_labels code) SUBSET labs_domain labs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[zero_labs_acc_exist_def; LET_DEF; LET_END_DEF; GSYM ALL_MEM;
              FORALL_PAIR_THM; MEM_toAList; get_zero_labs_acc_def] THEN
  REWRITE_TAC[GSYM LTTP2AUX_lab_lookup_not_none] THEN
  REWRITE_TAC[SUBSET; restrict_zero_def; labs_domain_def; IN_ELIM_THM;
              FORALL_PAIR_THM; FST; SND] THEN
  SUBGOAL_THEN
   `!p1. (?p2:1. lookup p1 (ITLIST sec_get_zero_labs_acc (code:((A)sec)list) LN) = SOME p2)
         <=> ?n2. (p1,n2) IN lab_get_labels code /\ n2 = 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM domain_lookup; get_zero_labs_acc_eq_get_zero_labels; domain_def;
                UNION_EMPTY; restrict_zero_def; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM;
                FST; SND] THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5066 *)
let line_similar_line_labs_exist = prove
 (`!(l1:(A)line) l2 labs.
     line_similar l1 l2 ==> (line_labs_exist labs l1 <=> line_labs_exist labs l2)`,
  REPEAT GEN_TAC THEN CASES_ON `l1:(A)line` THEN CASES_ON `l2:(A)line` THEN
  REWRITE_TAC[line_similar_def; line_labs_exist_def] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let LTTP2AUX_ALL2_similar_ALL = prove
 (`!(P:(A)line->bool) l1 l2.
     (!x y. line_similar x y ==> (P x <=> P y)) /\ ALL2 line_similar l1 l2
     ==> (ALL P l1 <=> ALL P l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; ALL] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5073 *)
let code_similar_all_labs_exist = prove
 (`!(c1:((A)sec)list) c2 labs.
     code_similar c1 c2
     ==> (ALL (sec_labs_exist labs) c1 <=> ALL (sec_labs_exist labs) c2)`,
  MATCH_MP_TAC code_similar_ind THEN
  REWRITE_TAC[code_similar_def; ALL; sec_labs_exist_def] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THENL
   [MATCH_MP_TAC LTTP2AUX_ALL2_similar_ALL THEN
    ASM_MESON_TAC[line_similar_line_labs_exist];
    ASM_MESON_TAC[]]);;

(* HOL4 line 5082 *)
let all_labs_exist_pad_code = prove
 (`!nop (code:((A)sec)list) labs.
     ALL (sec_labs_exist labs) (pad_code nop code) <=> ALL (sec_labs_exist labs) code`,
  MESON_TAC[code_similar_pad_code; code_similar_all_labs_exist; code_similar_refl]);;

let _ = cake_add_simps [all_labs_exist_pad_code];;

(* HOL4 line 5088 (HOL4's binders labs and k are unused, left out; the     *)
(* labels are labs')                                                          *)
let enc_lines_again_line_labs_exist = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines acc ok res ok' labs'.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
     ALL (line_labs_exist labs') acc /\ ALL (line_labs_exist labs') lines
     ==> ALL (line_labs_exist labs') res`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`line_labs_exist labs':(A)line->bool`; `labs:(num spt)spt`;
                 `ffis:ffiname list`; `enc:(A)asm->byte list`]
                LTTP2AUX_enc_lines_again_ALL) THEN
  REWRITE_TAC[line_labs_exist_def; IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5100 (HOL4's variables ffis and labs stand in the positions   *)
(* of labs and ffis of enc_secs_again, kept so; the binders labs and k are   *)
(* unused, left out; labs' is free in HOL4)                                  *)
let enc_secs_again_all_labs_exist = prove
 (`!pos ffis labs (enc:(A)asm->byte list) ls res ok (labs':(num spt)spt).
     enc_secs_again pos ffis labs enc ls = (res,ok) /\ ALL (sec_labs_exist labs') ls
     ==> ALL (sec_labs_exist labs') res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN FS[ALL; sec_labs_exist_def] THEN
  MATCH_MP_TAC enc_lines_again_line_labs_exist THEN ASM_MESON_TAC[ALL]);;

(* HOL4 line 5112 *)
let upd_lab_len_all_labs_exist = prove
 (`!pos (code:((A)sec)list) labs.
     ALL (sec_labs_exist labs) (upd_lab_len pos code) <=> ALL (sec_labs_exist labs) code`,
  MESON_TAC[code_similar_upd_lab_len; code_similar_all_labs_exist; code_similar_refl]);;

(* HOL4 line 5120 *)
let line_similar_line_get_code_labels = prove
 (`!(l1:(A)line) l2. line_similar l1 l2 ==> line_get_code_labels l1 = line_get_code_labels l2`,
  REPEAT GEN_TAC THEN CASES_ON `l1:(A)line` THEN CASES_ON `l2:(A)line` THEN
  REWRITE_TAC[line_similar_def; line_get_code_labels_def] THEN MESON_TAC[]);;

let LTTP2AUX_ALL2_similar_UNIONS = prove
 (`!(f:(A)line->B->bool) l1 l2.
     (!x y. line_similar x y ==> f x = f y) /\ ALL2 line_similar l1 l2
     ==> UNIONS (IMAGE f (set_of_list l1)) = UNIONS (IMAGE f (set_of_list l2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; set_of_list; IMAGE_CLAUSES; UNIONS_INSERT] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 5127 *)
let code_similar_get_code_labels = prove
 (`!(c1:((A)sec)list) c2.
     code_similar c1 c2 ==> lab_get_code_labels c1 = lab_get_code_labels c2`,
  MATCH_MP_TAC code_similar_ind THEN
  REWRITE_TAC[code_similar_def; get_code_labels_cons] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_REWRITE_TAC[sec_get_code_labels_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LTTP2AUX_ALL2_similar_UNIONS THEN
  ASM_REWRITE_TAC[line_similar_line_get_code_labels]);;

(* HOL4 line 5139 *)
let line_labs_exist_get_labels = prove
 (`!labs (line:(A)line).
     line_labs_exist labs line <=> line_get_labels line SUBSET labs_domain labs`,
  REPEAT GEN_TAC THEN CASES_ON `line:(A)line` THEN
  REWRITE_TAC[line_labs_exist_def; line_get_labels_def; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET; labs_domain_def; IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
  MESON_TAC[]);;

(* HOL4 line 5146 *)
let sec_labs_exist_get_labels = prove
 (`!labs (sec:(A)sec). sec_labs_exist labs sec <=> sec_get_labels sec SUBSET labs_domain labs`,
  REPEAT GEN_TAC THEN CASES_ON `sec:(A)sec` THEN
  REWRITE_TAC[sec_labs_exist_def; sec_get_labels_def; line_labs_exist_get_labels;
              GSYM ALL_MEM; UNIONS_SUBSET; FORALL_IN_IMAGE; IN_SET_OF_LIST]);;

(* HOL4 line 5155 *)
let all_labs_exist_get_labels = prove
 (`!labs (code:((A)sec)list).
     ALL (sec_labs_exist labs) code <=> lab_get_labels code SUBSET labs_domain labs`,
  REWRITE_TAC[lab_get_labels_def; sec_labs_exist_get_labels; GSYM ALL_MEM;
              UNIONS_SUBSET; FORALL_IN_IMAGE; IN_SET_OF_LIST]);;

(* HOL4 line 5163 *)
let line_similar_line_get_labels = prove
 (`!(l1:(A)line) l2. line_similar l1 l2 ==> line_get_labels l1 = line_get_labels l2`,
  REPEAT GEN_TAC THEN CASES_ON `l1:(A)line` THEN CASES_ON `l2:(A)line` THEN
  REWRITE_TAC[line_similar_def; line_get_labels_def] THEN MESON_TAC[]);;

(* HOL4 line 5170 *)
let code_similar_get_labels = prove
 (`!(c1:((A)sec)list) c2. code_similar c1 c2 ==> lab_get_labels c1 = lab_get_labels c2`,
  MATCH_MP_TAC code_similar_ind THEN
  REWRITE_TAC[code_similar_def; get_labels_cons] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_REWRITE_TAC[sec_get_labels_def] THEN
  MATCH_MP_TAC LTTP2AUX_ALL2_similar_UNIONS THEN
  ASM_REWRITE_TAC[line_similar_line_get_labels]);;

(* HOL4 line 5181 *)
let get_labels_upd_lab_len = prove
 (`!pos (code:((A)sec)list). lab_get_labels (upd_lab_len pos code) = lab_get_labels code`,
  MESON_TAC[code_similar_get_labels; code_similar_upd_lab_len; code_similar_refl]);;

let _ = cake_add_simps [get_labels_upd_lab_len];;

(* HOL4 line 5187 (HOL4's UNION binds tighter than INSERT) *)
let section_labels_line_get_code_labels = prove
 (`!pos (lines:((A)line)list) aux new_pos labs.
     section_labels pos lines aux = (new_pos,labs)
     ==> 0 INSERT set_of_list (MAP FST labs) =
         0 INSERT (set_of_list (MAP FST aux) UNION
                   UNIONS (IMAGE line_get_code_labels (set_of_list lines)))`,
  MATCH_MP_TAC section_labels_ind THEN
  REWRITE_TAC[section_labels_def; set_of_list; IMAGE_CLAUSES; UNIONS_0; UNIONS_INSERT;
              UNION_EMPTY; PAIR_EQ; line_get_code_labels_def] THEN
  CONJ_TAC THENL
   [MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[MAP; set_of_list] THEN SET_TAC[]]);;

(* HOL4 line 5197 *)
let labs_domain_compute_labels_alt = prove
 (`!pos (code:((A)sec)list) labs.
     ALL_DISTINCT (MAP Section_num code) /\
     DISJOINT (domain labs) (set_of_list (MAP Section_num code))
     ==> labs_domain (compute_labels_alt pos code labs) =
         lab_get_code_labels code UNION labs_domain labs`,
  MATCH_MP_TAC compute_labels_alt_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[compute_labels_alt_def; get_code_labels_nil; UNION_EMPTY]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[compute_labels_alt_def] THEN PAIRARG_TAC THEN
  REWRITE_TAC[MAP; lab_Section_num_def; ALL_DISTINCT; set_of_list; IN_DISJOINT; IN_INSERT] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`new_pos:num`; `sec_labs:(num#num)list`]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(k IN domain (labs:(num spt)spt))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[labs_domain_insert; domain_insert; domain_fromAList; MAP; set_of_list] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DISJOINT; IN_INSERT; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[IN_SET_OF_LIST];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP section_labels_line_get_code_labels) THEN
  REWRITE_TAC[MAP; set_of_list; UNION_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[get_code_labels_cons; sec_get_code_labels_def; IMAGE_CLAUSES] THEN
  SET_TAC[]);;

(* HOL4 line 5221 *)
let even_labels_def = cake_def
  `(even_labels pos ([]:((A)sec)list) <=> T) /\
   (even_labels pos (CONS (Section _ []) ls) <=> even_labels pos ls) /\
   (even_labels pos (CONS (Section k (CONS y ys)) ls) <=>
      (is_Label y ==> EVEN pos) /\
      even_labels (pos + line_len y) (CONS (Section k ys) ls))`;;

(* HOL4 line 5229: val even_labels_ind = theorem "even_labels_ind" *)
let even_labels_ind = cake_ind "even_labels";;

(* HOL4 line 5231 *)
let lines_even_labels_def = cake_def
  `(lines_even_labels pos ([]:((A)line)list) <=> T) /\
   (lines_even_labels pos (CONS y ys) <=>
      (is_Label y ==> EVEN pos) /\ lines_even_labels (pos + line_len y) ys)`;;

let lines_even_labels_ind = cake_ind "lines_even_labels";;

(* HOL4 line 5238 *)
let even_labels_alt = prove
 (`!pos k (ls:((A)line)list) ss.
     (even_labels pos ([]:((A)sec)list) <=> T) /\
     (even_labels pos (CONS (Section k ls) ss) <=>
      lines_even_labels pos ls /\ even_labels (pos + SUM (MAP line_len ls)) ss)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[even_labels_def] THEN
  SPEC_TAC(`pos:num`,`pos:num`) THEN SPEC_TAC(`ls:((A)line)list`,`ls:((A)line)list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[even_labels_def; lines_even_labels_def; MAP; SUM; ADD_CLAUSES;
                  ADD_ASSOC; CONJ_ACI]);;

(* HOL4 line 5252 *)
let even_labels_strong_def = cake_def
  `(even_labels_strong pos ([]:((A)sec)list) <=> T) /\
   (even_labels_strong pos (CONS (Section _ []) ls) <=>
      EVEN pos /\ even_labels_strong pos ls) /\
   (even_labels_strong pos (CONS (Section k (CONS y ys)) ls) <=>
      (is_Label y ==> EVEN pos) /\
      even_labels_strong (pos + line_len y) (CONS (Section k ys) ls))`;;

let even_labels_strong_ind = cake_ind "even_labels_strong";;

let LTTP2AUX_even_labels_strong_sec = prove
 (`!k rest (ls:((A)line)list) pos.
     ALL label_zero ls /\ (ls = [] ==> EVEN pos) /\ (~(ls = []) ==> is_Label (LAST ls)) /\
     even_labels pos (CONS (Section k ls) rest) /\
     (!p. EVEN p /\ even_labels p rest ==> even_labels_strong p rest)
     ==> even_labels_strong pos (CONS (Section k ls) rest)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; even_labels_def; even_labels_strong_def; NOT_CONS_NIL] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `is_Label (LAST (CONS (h:(A)line) t))` THEN
  REWRITE_TAC[LAST] THEN ASM_CASES_TAC `t:((A)line)list = []` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `label_zero (h:(A)line)` THEN UNDISCH_TAC `is_Label (h:(A)line) ==> EVEN pos` THEN
  CASES_ON `h:(A)line` THEN REWRITE_TAC[is_Label_def; label_zero_def; line_len_def] THEN
  SIMP_TAC[ADD_CLAUSES]);;

(* HOL4 line 5261 *)
let even_labels_ends_imp_strong = prove
 (`!pos (code:((A)sec)list).
     even_labels pos code /\ ALL sec_ends_with_label code /\ ALL sec_label_zero code
     ==> even_labels_strong pos code`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[even_labels_strong_def; ALL] THEN CASES_ON `h:(A)sec` THEN
  REWRITE_TAC[sec_ends_with_label_def; sec_label_zero_def] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTTP2AUX_even_labels_strong_sec THEN
  ASM_REWRITE_TAC[GSYM NULL_EQ] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5278 *)
let ALOOKUP_section_labels_ignore = prove
 (`!pos (lines:((A)line)list) acc n2.
     ~MEM n2 (MAP SND (lab_extract_labels lines))
     ==> ALOOKUP (SND (section_labels pos lines acc)) n2 = ALOOKUP acc n2`,
  MATCH_MP_TAC section_labels_ind THEN
  REWRITE_TAC[section_labels_def; lab_extract_labels_def; MAP; MEM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  ASM_SIMP_TAC[ALOOKUP_DEF] THEN ASM_MESON_TAC[]);;

let LTTP2AUX_line_ok_length = prove
 (`!(c:(A)asm_config) labs ffis pos y.
     line_ok c labs ffis pos y ==> line_length y = line_len y`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)line` THENL
   [REWRITE_TAC[line_ok_def; line_length_def; line_len_def] THEN SIMP_TAC[];
    REWRITE_TAC[line_ok_def; line_length_def; line_len_def] THEN SIMP_TAC[];
    CASES_ON `a0:(A)asm_with_lab` THEN
    REWRITE_TAC[line_ok_def; line_length_def; line_len_def; get_label_def; LET_DEF;
                LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN EVERY_CASE_TAC THEN FS[]]);;

let LTTP2AUX_lines_ok_sum = prove
 (`!(c:(A)asm_config) labs ffis pos lines.
     lines_ok c labs ffis pos lines
     ==> SUM (MAP line_length lines) = SUM (MAP line_len lines)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_ok_def; MAP; SUM] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN ASM_MESON_TAC[LTTP2AUX_line_ok_length]);;

(* HOL4 line 5288 *)
let lines_ok_section_lab_lookup_even = prove
 (`!pos (lines:((A)line)list) acc (c:(A)asm_config) labs ffis l2 x.
     lines_ok c labs ffis pos lines /\
     (!l2 x. ALOOKUP acc l2 = SOME x ==> EVEN x) /\
     ALOOKUP (SND (section_labels pos lines acc)) l2 = SOME x
     ==> EVEN x`,
  MATCH_MP_TAC section_labels_ind THEN
  REWRITE_TAC[section_labels_def; lines_ok_def] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[line_ok_def; line_length_def] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_CASES_TAC `l2 = 0` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `l2 = 0`)) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
        lhand(concl th) = `~(l2 = 0)`)) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `!l2'' x''. ALOOKUP (CONS (l2:num,pos:num) (labs:(num#num)list)) l2'' = SOME x''
                         ==> EVEN x''`
      ASSUME_TAC THENL
       [REWRITE_TAC[ALOOKUP_DEF] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[]]];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> length(fst(strip_forall(concl th))) = 5)) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP LTTP2AUX_line_ok_length th)) THEN
    REWRITE_TAC[line_len_def] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> length(fst(strip_forall(concl th))) = 5)) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP LTTP2AUX_line_ok_length th)) THEN
    REWRITE_TAC[line_len_def] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 5308 *)
let all_enc_ok_split = prove
 (`!(c:(A)asm_config) labs ffis pos k lines xs.
     all_enc_ok c labs ffis pos (CONS (Section k lines) xs)
     ==> all_enc_ok c labs ffis pos [Section k lines] /\
         all_enc_ok c labs ffis (pos + sec_length lines 0) xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_enc_ok_cons; all_enc_ok_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LTTP2AUX_lines_ok_sum) THEN
  ASM_REWRITE_TAC[sec_length_sum_line_len; ADD_CLAUSES] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5322 *)
let all_enc_ok_even = prove
 (`!(lines:((A)line)list) pos (c:(A)asm_config) labs ffis k.
     all_enc_ok c labs ffis pos [Section k lines] ==> EVEN (sec_length lines pos)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_enc_ok_cons] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LTTP2AUX_lines_ok_sum) THEN
  ASM_REWRITE_TAC[sec_length_sum_line_len] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5337 *)
let all_enc_ok_lab_lookup_even = prove
 (`!(c:(A)asm_config) labs ffis pos sec_list l1 l2 acc x.
     all_enc_ok c labs ffis pos sec_list /\
     lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) = SOME x /\
     (!x. lab_lookup l1 l2 acc = SOME x ==> EVEN x) /\
     EVEN pos
     ==> EVEN x`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[compute_labels_alt_def] THEN MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[compute_labels_alt_def] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP all_enc_ok_split) THEN STRIP_TAC THEN
  SUBGOAL_THEN `new_pos = pos + sec_length (a1:((A)line)list) 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`pos:num`; `a1:((A)line)list`; `[]:(num#num)list`]
                  section_labels_sec_length) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[sec_length_sum_line_len] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> length(fst(strip_forall(concl th))) = 5)) THEN
  MAP_EVERY EXISTS_TAC
   [`new_pos:num`; `l1:num`; `l2:num`;
    `insert a0 (fromAList (CONS (0,pos) sec_labs)) (acc:(num spt)spt)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[lab_lookup_def; lookup_insert] THEN GEN_TAC THEN COND_CASES_TAC THENL
     [CASE_REWRITE_TAC[] THEN REWRITE_TAC[lookup_fromAList; ALOOKUP_DEF] THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
       [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN MATCH_MP_TAC lines_ok_section_lab_lookup_even THEN
        MAP_EVERY EXISTS_TAC [`pos:num`; `a1:((A)line)list`; `[]:(num#num)list`;
                              `c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
                              `l2:num`] THEN
        ASM_REWRITE_TAC[ALOOKUP_DEF; option_DISTINCT] THEN
        UNDISCH_TAC `all_enc_ok c labs ffis pos [Section a0 (a1:((A)line)list)]` THEN
        SIMP_TAC[all_enc_ok_cons]];
      ASM_REWRITE_TAC[GSYM lab_lookup_def]];
    MP_TAC(ISPECL [`a1:((A)line)list`; `pos:num`; `c:(A)asm_config`; `labs:(num spt)spt`;
                   `ffis:ffiname list`; `a0:num`] all_enc_ok_even) THEN
    ASM_REWRITE_TAC[sec_length_sum_line_len] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[ADD_SYM]]);;

(* HOL4 line 5367 *)
let line_ok_pre_light_imp_line_ok = prove
 (`!(c:(A)asm_config) labs ffis pos line.
     line_ok_pre c line /\
     line_enc_with_nop (asm_config_encode c) labs ffis pos line /\
     line_offset_ok labs ffis pos line /\
     line_labs_exist labs line /\
     line_ok_light c line /\ (is_Label line ==> EVEN pos)
     ==> line_ok c labs ffis pos line`,
  REPEAT GEN_TAC THEN CASES_ON `line:(A)line` THENL
   [REWRITE_TAC[line_ok_def; line_enc_with_nop_def; is_Label_def] THEN MESON_TAC[];
    REWRITE_TAC[line_ok_def; line_enc_with_nop_def; line_ok_pre_def] THEN MESON_TAC[];
    CASES_ON `a0:(A)asm_with_lab` THEN
    REWRITE_TAC[line_ok_def; line_enc_with_nop_def; line_ok_pre_def; line_offset_ok_def;
                line_labs_exist_def; line_ok_light_def; get_jump_offset_def; get_label_def;
                lab_inst_def; LET_DEF; LET_END_DEF; WORD_SUB_LZERO] THEN
    REPEAT STRIP_TAC THEN TRY TOP_CASE_TAC THEN TRY TOP_CASE_TAC THEN
    FS[labs_of_def; IN_SING; PAIR_EQ] THEN IMP_RES_TAC lab_lookup_IMP THEN
    GVS[word_sub_def; ADD_SYM]]);;

let LTTP2AUX_line_enc_with_nop_length = prove
 (`!(enc:(A)asm->byte list) labs ffis pos y.
     line_enc_with_nop enc labs ffis pos y ==> line_length y = line_len y`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)line` THEN
  REWRITE_TAC[line_enc_with_nop_def; line_length_def; line_len_def] THENL
   [SIMP_TAC[]; SIMP_TAC[]; ALL_TAC] THEN
  CASES_ON `a0:(A)asm_with_lab` THEN REWRITE_TAC[line_enc_with_nop_def] THEN SIMP_TAC[]);;

(* HOL4 line 5383 *)
let all_enc_ok_pre_light_imp_all_enc_ok = prove
 (`!(c:(A)asm_config) labs ffis pos code.
     all_enc_with_nop (asm_config_encode c) labs ffis pos code /\
     ALL (sec_ok_pre c) code /\
     ALL (sec_ok_light c) code /\
     even_labels_strong pos code /\
     ALL (sec_labs_exist labs) code /\
     lab_to_targetProof_offset_ok labs ffis pos code
     ==> all_enc_ok c labs ffis pos code`,
  MATCH_MP_TAC all_enc_ok_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[all_enc_ok_def];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[all_enc_ok_def; all_enc_with_nop_def; ALL; sec_ok_pre_def;
                sec_ok_light_def; even_labels_strong_def; sec_labs_exist_def;
                lab_to_targetProof_offset_ok_def; lines_offset_ok_def; MAP; SUM;
                ADD_CLAUSES] THEN
    ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[all_enc_ok_def; all_enc_with_nop_def; ALL; sec_ok_pre_def;
                sec_ok_light_def; even_labels_strong_def; sec_labs_exist_def;
                lab_to_targetProof_offset_ok_def; lines_offset_ok_def; MAP; SUM] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LTTP2AUX_line_enc_with_nop_length o
      check (fun th -> can (term_match [] `line_enc_with_nop e l f p (y:(A)line)`)
                           (concl th))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC line_ok_pre_light_imp_line_ok THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN
      ASM_REWRITE_TAC[ALL; sec_ok_pre_def; sec_ok_light_def; sec_labs_exist_def;
                      lab_to_targetProof_offset_ok_def; ADD_ASSOC]]]);;

let LTTP2AUX_ALL2_similar_ends = prove
 (`!(l1:((A)line)list) l2.
     ALL2 line_similar l1 l2
     ==> (NULL l1 <=> NULL l2) /\ (~NULL l1 ==> (is_Label (LAST l1) <=> is_Label (LAST l2)))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; NULL; LAST] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':((A)line)list`) THEN
  ASM_REWRITE_TAC[GSYM NULL_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LTTP2AUX_line_similar_is_Label]);;

(* HOL4 line 5415 *)
let upd_lab_len_ends_with_label = prove
 (`!pos (ss:((A)sec)list).
     ALL sec_ends_with_label ss ==> ALL sec_ends_with_label (upd_lab_len pos ss)`,
  MATCH_MP_TAC upd_lab_len_ind THEN RW[upd_lab_len_def; ALL] THEN
  PAIRARG_TAC THEN FS[ALL; sec_ends_with_label_def] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`]
                lines_upd_lab_len_similar) THEN
  ASM_REWRITE_TAC[REVERSE; APPEND] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LTTP2AUX_ALL2_similar_ends) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5432 *)
let lab_lookup_compute_labels_alt_ignore = prove
 (`!pos (secs:((A)sec)list) acc n1 n2.
     ~MEM n1 (MAP Section_num secs)
     ==> lab_lookup n1 n2 (compute_labels_alt pos secs acc) = lab_lookup n1 n2 acc`,
  MATCH_MP_TAC compute_labels_alt_ind THEN
  REWRITE_TAC[compute_labels_alt_def; MAP; MEM; lab_Section_num_def; DE_MORGAN_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN PAIRARG_TAC THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[lab_lookup_def; lookup_insert] THEN ASM_MESON_TAC[]);;

let LTTP2AUX_all_label_zero_sums = prove
 (`!(xs:((A)line)list).
     ALL is_Label xs /\ ALL label_zero xs
     ==> SUM (MAP line_length xs) = 0 /\ FILTER ((~) o is_Label) xs = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; SUM; FILTER] THEN
  CASES_ON `h:(A)line` THEN
  REWRITE_TAC[is_Label_def; label_zero_def; line_length_def; o_THM] THEN
  ASM_SIMP_TAC[ADD_CLAUSES]);;

let LTTP2AUX_ex_lab_eq = prove
 (`!n1:num l2:num n2:num. (?n1' k. n1 = n1' /\ l2 = n2 /\ 0 = k) <=> l2 = n2`,
  MESON_TAC[]);;

(* HOL4 line 5443 *)
let ALOOKUP_section_labels = prove
 (`!pos (lines:((A)line)list) acc pc n1 n2.
     ALL (sec_label_ok n1) lines /\
     ALL line_length_ok lines /\
     ALL label_zero lines /\
     ALL_DISTINCT (lab_extract_labels lines) /\
     sec_loc_to_pc n2 lines = SOME pc /\
     ~(n2 = 0)
     ==> ?i. ALOOKUP (SND (section_labels pos lines acc)) n2 = SOME i /\
             ((sec_pos_val pc pos lines = NONE /\
               i = pos + SUM (MAP line_length lines) /\
               pc = LENGTH (FILTER ((~) o is_Label) lines)) \/
              sec_pos_val pc pos lines = SOME i)`,
  MATCH_MP_TAC section_labels_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[sec_loc_to_pc_def] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[option_DISTINCT];
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[ALL; sec_label_ok_def; line_length_ok_def; line_bytes_def; LENGTH;
                label_zero_def; lab_extract_labels_def; ALL_DISTINCT] THEN
    ONCE_REWRITE_TAC[sec_loc_to_pc_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[section_labels_def; sec_pos_val_def; is_Label_def; line_length_def;
                injectivity "line"; MAP; SUM; FILTER; o_THM] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 0`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(x:num) = n1`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; LTTP2AUX_ex_lab_eq]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_CASES_TAC `l2:num = n2` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `l2:num = n2`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; COND_ID]) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `0 = pc`)) THEN
      EXISTS_TAC `pos:num` THEN
      SUBGOAL_THEN `~MEM n2 (MAP SND (lab_extract_labels (xs:((A)line)list)))` ASSUME_TAC THENL
       [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; SND] THEN
        ASM_MESON_TAC[sec_label_ok_extract_labels];
        ALL_TAC] THEN
      ASM_SIMP_TAC[ALOOKUP_section_labels_ignore; ALOOKUP_DEF] THEN
      ASM_CASES_TAC `ALL is_Label (xs:((A)line)list)` THENL
       [DISJ1_TAC THEN
        ASM_SIMP_TAC[EVERY_is_Label_sec_pos_val; LTTP2AUX_all_label_zero_sums; LENGTH;
                     ADD_CLAUSES];
        DISJ2_TAC THEN ASM_SIMP_TAC[sec_pos_val_0]];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[ALL; sec_label_ok_def; line_length_ok_def; line_bytes_def;
                label_zero_def; lab_extract_labels_def] THEN
    ONCE_REWRITE_TAC[sec_loc_to_pc_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[section_labels_def; sec_pos_val_def; is_Label_def; line_length_def;
                distinctness "line"; MAP; SUM; FILTER; o_THM; line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      is_cond(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:num`; `n1:num`; `n2:num`]) THEN
    ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; LENGTH; SUC_INJ] THEN
    MESON_TAC[ADD_ASSOC];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[ALL; sec_label_ok_def; line_length_ok_def; line_bytes_def;
                label_zero_def; lab_extract_labels_def] THEN
    ONCE_REWRITE_TAC[sec_loc_to_pc_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[section_labels_def; sec_pos_val_def; is_Label_def; line_length_def;
                distinctness "line"; MAP; SUM; FILTER; o_THM; line_len_def] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      is_cond(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:num`; `n1:num`; `n2:num`]) THEN
    ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; LENGTH; SUC_INJ] THEN
    MESON_TAC[ADD_ASSOC]]);;

(* HOL4 line 5488 (HOL4's binders c, labs, ffis and nop are used only by   *)
(* all_enc_ok here; nop is unused, left out)                                  *)
let lab_lookup_compute_labels_test = prove
 (`!pos (sec_list:((A)sec)list) acc l1 l2 x2 (c:(A)asm_config) labs ffis.
     ALL sec_labels_ok sec_list /\
     ALL_DISTINCT (MAP Section_num sec_list) /\
     ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) sec_list /\
     ALL sec_label_zero sec_list /\
     all_enc_ok c labs ffis pos sec_list /\
     loc_to_pc l1 l2 sec_list = SOME x2
     ==> lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
         SOME (pos_val x2 pos sec_list)`,
  MATCH_MP_TAC compute_labels_alt_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[compute_labels_alt_def; loc_to_pc_def; option_DISTINCT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; MAP; lab_Section_num_def; ALL_DISTINCT; o_THM; lab_Section_lines_def;
              sec_label_zero_def; all_enc_ok_cons] THEN
  STRIP_TAC THEN
  REWRITE_TAC[compute_labels_alt_def; pair_CASE_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `ALL line_length_ok (lines:((A)line)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lines_ok_lines_enc_with_nop; lines_enc_with_nop_length_ok]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FST (section_labels pos (lines:((A)line)list) []) = pos + SUM (MAP line_length lines)`
  ASSUME_TAC THENL
   [REWRITE_TAC[section_labels_sec_length] THEN ASM_SIMP_TAC[sec_length_sum_line_length] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pos + SUM (MAP line_length (lines:((A)line)list))`;
                                `SND (section_labels pos (lines:((A)line)list) [])`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR_FST_SND_EQ]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `loc_to_pc l1 l2 (CONS (Section k lines) (rest:((A)sec)list)) = SOME x2` THEN
  MP_TAC(ISPECL [`l1:num`; `l2:num`; `CONS (Section k lines) (rest:((A)sec)list)`]
                loc_to_pc_thm) THEN
  ASM_REWRITE_TAC[ALL] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pos_val_thm] THEN
  ASM_CASES_TAC `l1:num = k` THEN ASM_REWRITE_TAC[] THENL
   [CASES_ON `sec_loc_to_pc l2 (lines:((A)line)list)` THEN CASE_REWRITE_TAC[] THENL
     [ALL_TAC;
      REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `l1:num = k`)) THEN
      ASM_SIMP_TAC[lab_lookup_compute_labels_alt_ignore] THEN
      REWRITE_TAC[lab_lookup_def; lookup_insert] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[lookup_fromAList; ALOOKUP_DEF] THEN
      ASM_CASES_TAC `0 = l2` THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        UNDISCH_TAC `sec_loc_to_pc 0 (lines:((A)line)list) = SOME a` THEN
        ONCE_REWRITE_TAC[sec_loc_to_pc_def] THEN REWRITE_TAC[option_INJ] THEN
        DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        ASM_CASES_TAC `ALL is_Label (lines:((A)line)list)` THENL
         [MP_TAC(ISPEC `lines:((A)line)list` LTTP2AUX_all_label_zero_sums) THEN
          ASM_SIMP_TAC[EVERY_is_Label_sec_pos_val; LENGTH; ADD_CLAUSES; SUB_0] THEN
          STRIP_TAC THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[pos_val_0; ADD_CLAUSES];
          ASM_SIMP_TAC[sec_pos_val_0] THEN CASE_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(l2 = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:(num#num)list`; `a:num`;
                       `k:num`; `l2:num`] ALOOKUP_section_labels) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[sec_labels_ok_def]) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[SUB_REFL] THEN ASM_MESON_TAC[pos_val_0]]];
    ALL_TAC] THEN
  (REWRITE_TAC[OPTION_MAP_EQ_SOME] THEN
   DISCH_THEN(X_CHOOSE_THEN `y:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
   SUBGOAL_THEN `sec_pos_val (LENGTH (FILTER ((~) o is_Label) lines) + y) pos
                   (lines:((A)line)list) = NONE` SUBST1_TAC THENL
    [MATCH_MP_TAC sec_pos_val_too_big THEN ARITH_TAC; ALL_TAC] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_SUB2] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]));;

let LTTP2AUX_enc_lines_again_simp_similar = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) ls res ok.
     enc_lines_again_simp labs ffis pos enc ls = (res,ok) ==> ALL2 line_similar ls res`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def; ALL2] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[ALL2; line_similar_def] THEN ASM_MESON_TAC[line_similar_def]);;

(* HOL4 line 5564 *)
let enc_lines_again_simp_ends_with_label = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) ls res ok.
     enc_lines_again_simp labs ffis pos enc ls = (res,ok) /\
     ~NULL ls /\ is_Label (LAST ls)
     ==> ~NULL res /\ is_Label (LAST res)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP2AUX_ALL2_similar_ends o
                MATCH_MP LTTP2AUX_enc_lines_again_simp_similar) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5579 *)
let enc_secs_again_ends_with_label = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) lines res ok.
     enc_secs_again pos labs ffis enc lines = (res,ok) /\ ALL sec_ends_with_label lines
     ==> ALL sec_ends_with_label res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN FS[ALL; sec_ends_with_label_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  MATCH_MP_TAC enc_lines_again_simp_ends_with_label THEN ASM_MESON_TAC[]);;

(* HOL4 line 5595 *)
let enc_sec_list_ends_with_label = prove
 (`!(enc:(A)asm->byte list) code.
     ALL sec_ends_with_label code ==> ALL sec_ends_with_label (enc_sec_list enc code)`,
  GEN_TAC THEN REWRITE_TAC[enc_sec_list_def; LET_DEF; LET_END_DEF] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN CASES_ON `h:(A)sec` THEN
  REWRITE_TAC[enc_sec_def; sec_ends_with_label_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`MAP (enc_line enc (LENGTH (enc (asm_Inst asm_Skip))))
                   (a1:((A)line)list)`; `a1:((A)line)list`] LTTP2AUX_ALL2_similar_ends) THEN
  REWRITE_TAC[GSYM LIST_REL_enc_line; LTTP2AUX_ALL2_line_similar_refl] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5606 *)
let lines_even_labels_append = prove
 (`!(l1:((A)line)list) l2 pos.
     lines_even_labels pos (APPEND l1 l2) <=>
     lines_even_labels pos l1 /\ lines_even_labels (pos + SUM (MAP line_len l1)) l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; lines_even_labels_def; MAP; SUM; ADD_CLAUSES; ADD_ASSOC;
                  CONJ_ACI]);;

(* HOL4 line 5619 *)
let label_zero_pos_ok_lines_even_labels = prove
 (`!pos (ls:((A)line)list).
     ALL label_zero ls /\ lab_len_pos_ok pos ls ==> lines_even_labels pos ls`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[lines_even_labels_def; lab_len_pos_ok_def; ALL] THEN
  CASES_ON `h:(A)line` THEN
  REWRITE_TAC[label_zero_def; line_lab_len_pos_ok_def; is_Label_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ARITH]);;

(* HOL4 line 5631 *)
let label_zero_pos_ok_even_labels = prove
 (`!pos (code:((A)sec)list).
     ALL sec_label_zero code /\ all_lab_len_pos_ok pos code ==> even_labels pos code`,
  MATCH_MP_TAC all_lab_len_pos_ok_ind THEN
  REWRITE_TAC[all_lab_len_pos_ok_def; even_labels_alt; sec_length_sum_line_len;
              sec_label_zero_def; ALL; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[label_zero_pos_ok_lines_even_labels]);;

(* HOL4 line 5667 *)
let pad_code_ends_with_label = prove
 (`!nop (ls:((A)sec)list).
     ALL sec_ends_with_label ls ==> ALL sec_ends_with_label (pad_code nop ls)`,
  MATCH_MP_TAC pad_code_ind THEN REWRITE_TAC[pad_code_def; ALL; sec_ends_with_label_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`nop:byte list`; `xs:((A)line)list`; `[]:((A)line)list`;
                 `xs:((A)line)list`] line_similar_pad_section) THEN
  REWRITE_TAC[REVERSE; APPEND; LTTP2AUX_ALL2_line_similar_refl] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LTTP2AUX_ALL2_similar_ends) THEN ASM_MESON_TAC[]);;

(* HOL4 line 5684 *)
let enc_lines_again_section_labels = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines res acc.
     enc_lines_again_simp labs ffis pos enc lines = (res,T)
     ==> section_labels pos lines acc = section_labels pos res acc`,
  MATCH_MP_TAC enc_lines_again_simp_ind THEN RW[enc_lines_again_simp_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  GVS[section_labels_def]);;

(* HOL4 line 5695 *)
let enc_secs_again_compute_labels = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) secs res acc.
     enc_secs_again pos labs ffis enc secs = (res,T)
     ==> compute_labels_alt pos res acc = compute_labels_alt pos secs acc`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP2AUX_enc_lines_again_simp_nil) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[compute_labels_alt_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP enc_lines_again_section_labels th)]) THEN
  REWRITE_TAC[pair_CASE_def; LET_DEF; LET_END_DEF; section_labels_sec_length] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP enc_lines_again_simp_len) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sec_length_sum_line_len]) THEN
  REWRITE_TAC[sec_length_sum_line_len] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

(* HOL4 line 5737 *)
let pad_section_labels = prove
 (`!nop (lines:((A)line)list) aux pos labs.
     lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
     lab_len_pos_ok pos (REVERSE aux) /\ ALL label_zero aux /\
     (~NULL lines /\ is_Label (HD lines) /\ line_len (HD lines) = 1
      ==> ~NULL aux /\ ~is_Label (HD aux))
     ==> section_labels pos (pad_section nop lines aux) labs =
         section_labels pos (APPEND (REVERSE aux) lines) labs`,
  MATCH_MP_TAC pad_section_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[pad_section_def; APPEND_NIL];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def; NULL; HD; is_Label_def] THEN
    STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `section_labels pos (APPEND (REVERSE (CONS (lab_Label l1 l2 0)
                  (if len = 0 then aux else add_nop nop aux))) (xs:((A)line)list)) labs` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                  lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                  line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE; ADD_CLAUSES] THEN
      SUBGOAL_THEN `~(~NULL (xs:((A)line)list) /\ is_Label (HD xs) /\ line_len (HD xs) = 1)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `lab_len_pos_ok ((pos + SUM (MAP line_len (aux:((A)line)list))) + len)
                       (xs:((A)line)list)` THEN
        UNDISCH_TAC `if EVEN (pos + SUM (MAP line_len (aux:((A)line)list)))
                     then len = 0 else len = 1` THEN
        SPEC_TAC(`xs:((A)line)list`,`xs:((A)line)list`) THEN LIST_INDUCT_TAC THEN
        REWRITE_TAC[NULL; HD] THEN CASES_ON `h:(A)line` THEN
        REWRITE_TAC[is_Label_def; line_len_def; lab_len_pos_ok_def;
                    line_lab_len_pos_ok_def] THEN
        ASM_CASES_TAC `EVEN (pos + SUM (MAP line_len (aux:((A)line)list)))` THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC[ADD_CLAUSES; GSYM ADD1; EVEN] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `len = 0` THENL
       [SUBGOAL_THEN `EVEN (pos + SUM (MAP line_len (aux:((A)line)list)))` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
          COND_CASES_TAC THEN REWRITE_TAC[ARITH];
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 0`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[rich_list_MAP_REVERSE; SUM_REVERSE]) THEN
        ASM_REWRITE_TAC[SUM_APPEND; SUM_REVERSE; SUM; ADD_CLAUSES];
        ALL_TAC] THEN
      SUBGOAL_THEN `~EVEN (pos + SUM (MAP line_len (aux:((A)line)list))) /\ len = 1`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `len = 1`)) THEN
      SUBGOAL_THEN `~NULL (aux:((A)line)list) /\ ~is_Label (HD aux)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~ALL is_Label (aux:((A)line)list)` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
        SPEC_TAC(`aux:((A)line)list`,`aux:((A)line)list`) THEN
        LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD; ALL] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `EVEN ((pos + SUM (MAP line_len (aux:((A)line)list))) + 1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[EVEN_ADD; ARITH]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[rich_list_MAP_REVERSE; SUM_REVERSE]) THEN
      ASM_SIMP_TAC[line_len_add_nop1; EVERY_label_zero_add_nop; LTTP2AUX_lab_len_pos_ok_add_nop;
                   ADD_ASSOC; SUM_APPEND; SUM_REVERSE; SUM; ADD_CLAUSES;
                   GSYM rich_list_MAP_REVERSE];
      ASM_CASES_TAC `len = 0` THENL
       [ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND];
        ALL_TAC] THEN
      SUBGOAL_THEN `len = 1` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~NULL (aux:((A)line)list) /\ ~is_Label (HD aux)` MP_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`]; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `~(1 = 0)`] THEN
      CASES_ON `aux:((A)line)list` THEN REWRITE_TAC[NULL; HD] THEN
      CASES_ON `a0:(A)line` THEN
      REWRITE_TAC[is_Label_def; add_nop_def; REVERSE; GSYM APPEND_ASSOC; APPEND;
                  section_labels_append; section_labels_def; MAP; SUM; line_len_def;
                  MAP_APPEND; SUM_APPEND] THEN
      COND_CASES_TAC THEN REWRITE_TAC[ADD_AC; ADD_CLAUSES]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def] THEN
    STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `section_labels pos (APPEND (REVERSE (CONS (Asm x (pad_bytes bytes len nop) len)
                  aux)) (xs:((A)line)list)) labs` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE]) THEN
      ASM_REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                      lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                      line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE; SUM_APPEND] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_AC; ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC[ADD_AC; ADD_CLAUSES];
      REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND; section_labels_append;
                  section_labels_def; MAP_APPEND; SUM_APPEND; MAP; SUM; line_len_def] THEN
      REWRITE_TAC[ADD_AC; ADD_CLAUSES]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[pad_section_def; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                line_len_def] THEN
    STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `section_labels pos (APPEND (REVERSE (CONS
                  (LabAsm y w (pad_bytes bytes len nop) len) aux)) (xs:((A)line)list)) labs` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE]) THEN
      ASM_REWRITE_TAC[NULL; HD; is_Label_def; MAP; SUM; ALL; label_zero_def; REVERSE;
                      lab_len_pos_ok_append; lab_len_pos_ok_def; line_lab_len_pos_ok_def;
                      line_len_def; rich_list_MAP_REVERSE; SUM_REVERSE; SUM_APPEND] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_AC; ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC[ADD_AC; ADD_CLAUSES];
      REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND; section_labels_append;
                  section_labels_def; MAP_APPEND; SUM_APPEND; MAP; SUM; line_len_def] THEN
      REWRITE_TAC[ADD_AC; ADD_CLAUSES]]]);;

let LTTP2AUX_label_prefix_zero_HD = prove
 (`!(ls:((A)line)list).
     label_prefix_zero ls ==> ~(~NULL ls /\ is_Label (HD ls) /\ line_len (HD ls) = 1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD] THEN CASES_ON `h:(A)line` THEN
  REWRITE_TAC[label_prefix_zero_cons; is_Label_def; line_len_def] THEN ARITH_TAC);;

(* HOL4 line 5774 *)
let pad_code_compute_labels = prove
 (`!pos (code:((A)sec)list) acc nop.
     ALL sec_label_one code /\
     (~(LENGTH nop = 1) ==> ALL sec_label_zero code) /\
     ALL sec_label_prefix_zero code /\
     all_lab_len_pos_ok pos code
     ==> compute_labels_alt pos (pad_code nop code) acc = compute_labels_alt pos code acc`,
  MATCH_MP_TAC compute_labels_alt_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[pad_code_def; compute_labels_alt_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[pad_code_def; compute_labels_alt_def; all_lab_len_pos_ok_def; ALL;
              sec_label_zero_def; sec_label_one_def; sec_label_prefix_zero_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!slabs. section_labels pos (pad_section nop lines ([]:((A)line)list)) slabs =
                        section_labels pos lines slabs` (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `slabs:(num#num)list` THEN
    MP_TAC(ISPECL [`nop:byte list`; `lines:((A)line)list`; `[]:((A)line)list`; `pos:num`;
                   `slabs:(num#num)list`] pad_section_labels) THEN
    ASM_SIMP_TAC[MAP; SUM; ADD_CLAUSES; REVERSE; lab_len_pos_ok_def; ALL; APPEND;
                 LTTP2AUX_label_prefix_zero_HD];
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE_def; LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`FST (section_labels pos (lines:((A)line)list) ([]:(num#num)list))`;
                                `SND (section_labels pos (lines:((A)line)list) ([]:(num#num)list))`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[section_labels_sec_length] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sec_length_sum_line_len; ADD_CLAUSES; ADD_AC]) THEN
  ASM_REWRITE_TAC[sec_length_sum_line_len; ADD_CLAUSES; ADD_AC] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5807 *)
let enc_lines_again_all_enc_ok_pre = prove
 (`!(labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) lines acc ok res ok' c.
     enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') /\
     ALL (line_ok_pre c) lines /\ ALL (line_ok_pre c) acc
     ==> ALL (line_ok_pre c) res`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`line_ok_pre (c:(A)asm_config)`; `labs:(num spt)spt`;
                 `ffis:ffiname list`; `enc:(A)asm->byte list`]
                LTTP2AUX_enc_lines_again_ALL) THEN
  REWRITE_TAC[line_ok_pre_def; IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5817 *)
let enc_secs_again_all_enc_ok_pre = prove
 (`!pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) ls res ok c.
     enc_secs_again pos labs ffis enc ls = (res,ok) /\ ALL (sec_ok_pre c) ls
     ==> ALL (sec_ok_pre c) res`,
  MATCH_MP_TAC enc_secs_again_ind THEN RW[enc_secs_again_def] THEN RW[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN FS[ALL; sec_ok_pre_def] THEN
  MATCH_MP_TAC enc_lines_again_all_enc_ok_pre THEN ASM_MESON_TAC[ALL]);;

(* HOL4 line 5829 *)
let line_ok_pre_add_nop = prove
 (`!(c:(A)asm_config) xs nop.
     ALL (line_ok_pre c) xs ==> ALL (line_ok_pre c) (add_nop nop xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[add_nop_def; ALL] THEN
  CASES_ON `h:(A)line` THEN ASM_SIMP_TAC[add_nop_def; ALL; line_ok_pre_def]);;

(* HOL4 line 5836 *)
let line_ok_pre_pad_section = prove
 (`!nop (xs:((A)line)list) acc c.
     ALL (line_ok_pre c) xs /\ ALL (line_ok_pre c) acc
     ==> ALL (line_ok_pre c) (pad_section nop xs acc)`,
  MATCH_MP_TAC pad_section_ind THEN
  REWRITE_TAC[pad_section_def; ALL; EVERY_REVERSE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL] THEN FS[line_ok_pre_def] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[line_ok_pre_add_nop]);;

(* HOL4 line 5847 *)
let all_enc_ok_pre_pad_code = prove
 (`!nop (code:((A)sec)list) c.
     ALL (sec_ok_pre c) code ==> ALL (sec_ok_pre c) (pad_code nop code)`,
  MATCH_MP_TAC pad_code_ind THEN REWRITE_TAC[pad_code_def; ALL; sec_ok_pre_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC line_ok_pre_pad_section THEN ASM_REWRITE_TAC[ALL]);;

(* HOL4 line 5857 *)
let all_enc_ok_pre_lines_upd_lab_len = prove
 (`!n (lines:((A)line)list) acc c.
     ALL (line_ok_pre c) lines /\ ALL (line_ok_pre c) acc
     ==> ALL (line_ok_pre c) (FST (lines_upd_lab_len n lines acc))`,
  MATCH_MP_TAC lines_upd_lab_len_ind THEN
  REWRITE_TAC[lines_upd_lab_len_def; LET_DEF; LET_END_DEF; ALL; EVERY_REVERSE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ALL; line_ok_pre_def]);;

(* HOL4 line 5867 *)
let all_enc_ok_pre_upd_lab_len = prove
 (`!n (code:((A)sec)list) c.
     ALL (sec_ok_pre c) code ==> ALL (sec_ok_pre c) (upd_lab_len n code)`,
  MATCH_MP_TAC upd_lab_len_ind THEN RW[upd_lab_len_def; ALL] THEN
  PAIRARG_TAC THEN FS[ALL; sec_ok_pre_def] THEN
  MP_TAC(ISPECL [`pos:num`; `lines:((A)line)list`; `[]:((A)line)list`;
                 `c:(A)asm_config`] all_enc_ok_pre_lines_upd_lab_len) THEN
  ASM_REWRITE_TAC[ALL]);;

(* HOL4 line 5878 *)
let EXP_IMP_ZERO_LT = prove
 (`!y x. 2 EXP y = x ==> 0 < x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LT_NZ; EXP_EQ_0; ARITH]);;

(* HOL4 line 5884 *)
let line_ok_alignment = prove
 (`!(c:(A)asm_config) labs ffis pos line.
     enc_ok c /\ line_ok c labs ffis pos line /\ ODD (line_length line)
     ==> asm_config_code_alignment c = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `pos:num`; `labs:(num spt)spt`; `ffis:ffiname list`;
                 `line:(A)line`] LTTP2AUX_line_length_MOD_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`line_length (line:(A)line)`; `asm_config_code_alignment (c:(A)asm_config)`]
                LTTP2AUX_MOD_2EXP_EVEN) THEN
  ASM_REWRITE_TAC[GSYM NOT_ODD]);;

(* HOL4 line 5909 *)
let has_odd_inst_alignment = prove
 (`!(c:(A)asm_config) labs ffis pos code.
     enc_ok c /\ all_enc_ok c labs ffis pos code /\ has_odd_inst code
     ==> asm_config_code_alignment c = 0`,
  MATCH_MP_TAC all_enc_ok_ind THEN
  REWRITE_TAC[all_enc_ok_def; has_odd_inst_def; GSYM NOT_ODD] THEN
  MESON_TAC[line_ok_alignment]);;

let LTTP2AUX_code_similar_invs = prove
 (`!(code:((A)sec)list) code1.
     code_similar code code1
     ==> MAP Section_num code1 = MAP Section_num code /\
         (ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) code1 <=>
          ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) code) /\
         lab_get_labels code1 = lab_get_labels code /\
         lab_get_code_labels code1 = lab_get_code_labels code`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM ALL_MAP] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP code_similar_extract_labels th;
    MATCH_MP code_similar_MAP_Section_num th; MATCH_MP code_similar_get_labels th;
    MATCH_MP code_similar_get_code_labels th]));;
let LTTP2AUX_remove_labels_done = prove
 (`!(c:(A)asm_config) pos init_labs ffis (code:((A)sec)list) code1 code2 code3 final labs nop.
     enc_secs_again pos (compute_labels_alt pos code init_labs) ffis (asm_config_encode c) code =
       (code1,T) /\
     upd_lab_len pos code1 = code2 /\
     compute_labels_alt pos code2 init_labs = labs /\
     enc_secs_again pos labs ffis (asm_config_encode c) code2 = (code3,T) /\
     asm_config_encode c (asm_Inst asm_Skip) = nop /\
     pad_code nop code3 = final /\
     ALL (sec_ok_light c) final /\ zero_labs_acc_exist labs final /\
     ALL sec_ends_with_label code /\
     ALL sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) code /\
     DISJOINT (domain init_labs) (set_of_list (MAP Section_num code)) /\
     restrict_nonzero (lab_get_labels code) SUBSET
       lab_get_code_labels code UNION labs_domain init_labs /\
     ALL (sec_ok_pre c) code /\
     ALL (sec_encd0 (asm_config_encode c)) code /\
     enc_ok c /\
     EVEN pos /\
     (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs))
     ==> ALL (sec_ok_pre c) final /\
         ALL sec_labels_ok final /\
         all_enc_ok c labs ffis pos final /\
         code_similar code final /\
         (has_odd_inst final ==> asm_config_code_alignment c = 0) /\
         (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
         (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==> lab_lookup l1 l2 labs = SOME x) /\
         !l1 l2 x2.
           loc_to_pc l1 l2 code = SOME x2
           ==> lab_lookup l1 l2 labs = SOME (pos_val x2 pos final)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `code_similar (code:((A)sec)list) (code1:((A)sec)list) /\ code_similar (code1:((A)sec)list) (code2:((A)sec)list) /\
                code_similar (code2:((A)sec)list) (code3:((A)sec)list) /\ code_similar (code3:((A)sec)list) (final:((A)sec)list)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[enc_secs_again_IMP_similar];
      ASM_MESON_TAC[code_similar_upd_lab_len; code_similar_refl; code_similar_sym];
      ASM_MESON_TAC[enc_secs_again_IMP_similar];
      ASM_MESON_TAC[code_similar_pad_code; code_similar_refl]];
    ALL_TAC] THEN
  SUBGOAL_THEN `code_similar (code:((A)sec)list) (code2:((A)sec)list) /\ code_similar code (code3:((A)sec)list) /\
                code_similar code (final:((A)sec)list)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[code_similar_trans]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL sec_ends_with_label (code1:((A)sec)list) /\ ALL sec_ends_with_label (code2:((A)sec)list) /\
                ALL sec_ends_with_label (code3:((A)sec)list) /\ ALL sec_ends_with_label (final:((A)sec)list)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ (b ==> c) /\ (c ==> d) ==> a /\ b /\ c /\ d`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[enc_secs_again_ends_with_label];
      ASM_MESON_TAC[upd_lab_len_ends_with_label];
      ASM_MESON_TAC[enc_secs_again_ends_with_label];
      ASM_MESON_TAC[pad_code_ends_with_label]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (sec_encd0 (asm_config_encode c)) (code1:((A)sec)list) /\
                ALL (sec_encd0 (asm_config_encode c)) (code2:((A)sec)list)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[enc_secs_again_encd0]; ASM_MESON_TAC[upd_lab_len_encd0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL sec_label_one (code2:((A)sec)list) /\ ALL sec_label_one (code3:((A)sec)list)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[upd_lab_len_label_one]; ASM_MESON_TAC[enc_secs_again_label_one]];
    ALL_TAC] THEN
  SUBGOAL_THEN `all_encd (asm_config_encode c) labs ffis pos (code3:((A)sec)list)` ASSUME_TAC
  THENL [ASM_MESON_TAC[enc_secs_again_encd]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL sec_length_leq (code3:((A)sec)list)` ASSUME_TAC
  THENL [ASM_MESON_TAC[all_encd_length_leq]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL sec_label_prefix_zero (code2:((A)sec)list) /\
                ALL sec_label_prefix_zero (code3:((A)sec)list)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[upd_lab_len_label_prefix_zero];
      ASM_MESON_TAC[enc_secs_again_label_prefix_zero]];
    ALL_TAC] THEN
  SUBGOAL_THEN `all_lab_len_pos_ok pos (code3:((A)sec)list)` ASSUME_TAC
  THENL [ASM_MESON_TAC[enc_secs_again_pos_ok; upd_lab_len_pos_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < LENGTH (nop:byte list) /\
                LENGTH nop = 2 EXP asm_config_code_alignment (c:(A)asm_config) /\
                (!a. LENGTH (asm_config_encode c a) MOD LENGTH nop = 0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `enc_ok (c:(A)asm_config)` THEN REWRITE_TAC[enc_ok_def] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `asm_config_encode (c:(A)asm_config) (asm_Inst asm_Skip) = nop`)) THEN
    STRIP_TAC THEN ASM_MESON_TAC[LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(LENGTH (nop:byte list) = 1)
                ==> ALL (sec_aligned (LENGTH nop)) (code3:((A)sec)list) /\
                    ALL sec_label_zero code3`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~(asm_config_code_alignment (c:(A)asm_config) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(LENGTH (nop:byte list) = 1)` THEN
      ASM_REWRITE_TAC[EXP];
      ALL_TAC] THEN
    SUBGOAL_THEN `ALL sec_label_zero (code2:((A)sec)list)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
        concl th = `upd_lab_len pos (code1:((A)sec)list) = code2`)) THEN
      MATCH_MP_TAC upd_lab_len_encd0_label_zero THEN
      MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `asm_config_encode (c:(A)asm_config)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `ALL (sec_aligned (LENGTH (nop:byte list))) (code2:((A)sec)list)`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
          concl th = `asm_config_encode (c:(A)asm_config) (asm_Inst asm_Skip) = nop`)) THEN
        MATCH_MP_TAC all_encd0_aligned THEN EXISTS_TAC `c:(A)asm_config` THEN
        ASM_REWRITE_TAC[ETA_AX];
        ALL_TAC] THEN
      MATCH_MP_TAC enc_secs_again_aligned THEN
      MAP_EVERY EXISTS_TAC [`pos:num`; `labs:(num spt)spt`; `ffis:ffiname list`;
                            `asm_config_encode (c:(A)asm_config)`; `code2:((A)sec)list`;
                            `T`] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[enc_secs_again_label_zero]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (sec_ok_pre (c:(A)asm_config)) (final:((A)sec)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `pad_code nop (code3:((A)sec)list) = final`)) THEN
    MATCH_MP_TAC all_enc_ok_pre_pad_code THEN
    MATCH_MP_TAC enc_secs_again_all_enc_ok_pre THEN
    MAP_EVERY EXISTS_TAC [`pos:num`; `labs:(num spt)spt`; `ffis:ffiname list`;
                          `asm_config_encode (c:(A)asm_config)`; `code2:((A)sec)list`;
                          `T`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `upd_lab_len pos (code1:((A)sec)list) = code2`)) THEN
    MATCH_MP_TAC all_enc_ok_pre_upd_lab_len THEN
    ASM_MESON_TAC[enc_secs_again_all_enc_ok_pre];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL sec_labels_ok (final:((A)sec)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pad_code_sec_labels_ok; enc_secs_again_sec_labels_ok;
                  upd_lab_len_sec_labels_ok];
    ALL_TAC] THEN
  SUBGOAL_THEN `all_enc_with_nop (asm_config_encode (c:(A)asm_config)) labs ffis pos
                  (final:((A)sec)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `pad_code nop (code3:((A)sec)list) = final`)) THEN
    MATCH_MP_TAC all_enc_with_nop_pad_code THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o SYM o check (fun th ->
      concl th = `asm_config_encode (c:(A)asm_config) (asm_Inst asm_Skip) = nop`));
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL sec_label_zero (final:((A)sec)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[all_enc_with_nop_label_zero]; ALL_TAC] THEN
  SUBGOAL_THEN `all_lab_len_pos_ok pos (final:((A)sec)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `pad_code nop (code3:((A)sec)list) = final`)) THEN
    MATCH_MP_TAC all_lab_len_pos_ok_pad_code THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `even_labels_strong pos (final:((A)sec)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC even_labels_ends_imp_strong THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC label_zero_pos_ok_even_labels THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lab_to_targetProof_offset_ok labs ffis pos (final:((A)sec)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `pad_code nop (code3:((A)sec)list) = final`)) THEN
    MATCH_MP_TAC offset_ok_pad_code THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[enc_secs_again_offset_ok];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`code:((A)sec)list`; `code2:((A)sec)list`] LTTP2AUX_code_similar_invs) THEN
  MP_TAC(ISPECL [`code:((A)sec)list`; `final:((A)sec)list`] LTTP2AUX_code_similar_invs) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `labs_domain labs =
                lab_get_code_labels (code:((A)sec)list) UNION labs_domain init_labs`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `compute_labels_alt pos (code2:((A)sec)list) init_labs = labs`)) THEN
    ASM_SIMP_TAC[labs_domain_compute_labels_alt];
    ALL_TAC] THEN
  SUBGOAL_THEN `lab_get_labels (code:((A)sec)list) SUBSET labs_domain labs` ASSUME_TAC THENL
   [UNDISCH_TAC `zero_labs_acc_exist labs (final:((A)sec)list)` THEN
    ASM_REWRITE_TAC[zero_labs_acc_exist_eq] THEN
    UNDISCH_TAC `restrict_nonzero (lab_get_labels (code:((A)sec)list)) SUBSET
                 lab_get_code_labels code UNION labs_domain init_labs` THEN
    REWRITE_TAC[restrict_zero_def; restrict_nonzero_def; SUBSET; IN_ELIM_THM; IN_UNION] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (sec_labs_exist labs) (final:((A)sec)list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `pad_code nop (code3:((A)sec)list) = final`)) THEN
    REWRITE_TAC[all_labs_exist_pad_code] THEN
    MATCH_MP_TAC enc_secs_again_all_labs_exist THEN
    MAP_EVERY EXISTS_TAC [`pos:num`; `labs:(num spt)spt`; `ffis:ffiname list`;
                          `asm_config_encode (c:(A)asm_config)`; `code2:((A)sec)list`;
                          `T`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[all_labs_exist_get_labels] THEN
    UNDISCH_TAC `lab_get_labels (code:((A)sec)list) SUBSET labs_domain labs` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `all_enc_ok (c:(A)asm_config) labs ffis pos (final:((A)sec)list)` ASSUME_TAC
  THENL [MATCH_MP_TAC all_enc_ok_pre_light_imp_all_enc_ok THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compute_labels_alt pos (final:((A)sec)list) init_labs = labs` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `pad_code nop (code3:((A)sec)list) = final`)) THEN
    MP_TAC(ISPECL [`pos:num`; `code3:((A)sec)list`; `init_labs:(num spt)spt`;
                   `nop:byte list`] pad_code_compute_labels) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPECL [`pos:num`; `labs:(num spt)spt`; `ffis:ffiname list`;
                   `asm_config_encode (c:(A)asm_config)`; `code2:((A)sec)list`;
                   `code3:((A)sec)list`; `init_labs:(num spt)spt`]
                  enc_secs_again_compute_labels) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==> EVEN x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l1:num`; `l2:num`] o check (fun th ->
      can (find_term ((=) `OPTION_ALL:(num->bool)->num option->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[OPTION_ALL_def];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC has_odd_inst_alignment THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC all_enc_ok_lab_lookup_even THEN
    MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
                          `pos:num`; `final:((A)sec)list`; `l1:num`; `l2:num`;
                          `init_labs:(num spt)spt`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `compute_labels_alt pos (code2:((A)sec)list) init_labs = labs`)) THEN
    SUBGOAL_THEN `~MEM l1 (MAP Section_num (code2:((A)sec)list))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (domain (init_labs:(num spt)spt))
                     (set_of_list (MAP Section_num (code:((A)sec)list)))` THEN
      UNDISCH_TAC `lab_lookup l1 l2 (init_labs:(num spt)spt) = SOME x` THEN
      REWRITE_TAC[lab_lookup_def; IN_DISJOINT; IN_SET_OF_LIST; domain_lookup] THEN
      CASES_ON `lookup l1 (init_labs:(num spt)spt)` THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[lab_lookup_compute_labels_alt_ignore];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if concl th =
      `compute_labels_alt pos (final:((A)sec)list) init_labs = labs`
      then GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th] else NO_TAC) THEN
    MATCH_MP_TAC lab_lookup_compute_labels_test THEN
    MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP code_similar_loc_to_pc
             (ASSUME `code_similar (code:((A)sec)list) final`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5922 (HOL4 OPTION_ALL P o: OPTION_ALL) *)
let remove_labels_loop_thm = prove
 (`!n (c:(A)asm_config) init_pos init_labs ffis code code2 labs.
     remove_labels_loop n c init_pos init_labs ffis code = SOME (code2,labs) /\
     ALL sec_ends_with_label code /\
     ALL sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) code /\
     DISJOINT (domain init_labs) (set_of_list (MAP Section_num code)) /\
     restrict_nonzero (lab_get_labels code) SUBSET
       lab_get_code_labels code UNION labs_domain init_labs /\
     ALL (sec_ok_pre c) code /\
     ALL (sec_encd0 (asm_config_encode c)) code /\
     enc_ok c /\
     EVEN init_pos /\
     (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs))
     ==> ALL (sec_ok_pre c) code2 /\
         ALL sec_labels_ok code2 /\
         all_enc_ok c labs ffis init_pos code2 /\
         code_similar code code2 /\
         (has_odd_inst code2 ==> asm_config_code_alignment c = 0) /\
         (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
         (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==> lab_lookup l1 l2 labs = SOME x) /\
         !l1 l2 x2.
           loc_to_pc l1 l2 code = SOME x2
           ==> lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)`,
  MATCH_MP_TAC remove_labels_loop_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[remove_labels_loop_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  PAIRARG_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [(PAIRARG_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC) THEN
    (REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                                          is_var(rhs(concl th))))) THEN
  MATCH_MP_TAC LTTP2AUX_remove_labels_done THEN
  MAP_EVERY EXISTS_TAC [`sec_list':((A)sec)list`; `upd_lab_len pos (sec_list':((A)sec)list)`;
                        `sec_list'':((A)sec)list`;
                        `asm_config_encode (c:(A)asm_config) (asm_Inst asm_Skip)`] THEN
  ASM_REWRITE_TAC[]);
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`isdone:bool`; `sec_list':((A)sec)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`code2:((A)sec)list`; `labs:(num spt)spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `code_similar (sec_list:((A)sec)list) sec_list'` ASSUME_TAC THENL
   [ASM_MESON_TAC[enc_secs_again_IMP_similar]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sec_list:((A)sec)list`; `sec_list':((A)sec)list`]
                LTTP2AUX_code_similar_invs) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[enc_secs_again_ends_with_label];
      ASM_MESON_TAC[enc_secs_again_sec_labels_ok];
      ASM_MESON_TAC[enc_secs_again_all_enc_ok_pre];
      ASM_MESON_TAC[enc_secs_again_encd0]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[code_similar_trans];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[code_similar_loc_to_pc]]]);;

(* HOL4 line 6131 *)
let loc_to_pc_enc_sec_list = prove
 (`!l1 l2 (code:((A)sec)list) e.
     loc_to_pc l1 l2 (enc_sec_list e code) = loc_to_pc l1 l2 code`,
  MESON_TAC[code_similar_loc_to_pc; code_similar_enc_sec_list; code_similar_refl]);;

let _ = cake_add_simps [loc_to_pc_enc_sec_list];;

let LTTP2AUX_line_ok_pre_enc_line = prove
 (`!(c:(A)asm_config) enc len x. line_ok_pre c (enc_line enc len x) <=> line_ok_pre c x`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)line` THEN
  REWRITE_TAC[enc_line_def; LET_DEF; LET_END_DEF; line_ok_pre_def]);;

let LTTP2AUX_sec_ok_pre_enc_sec = prove
 (`!(c:(A)asm_config) enc len s. sec_ok_pre c (enc_sec enc len s) <=> sec_ok_pre c s`,
  REPEAT GEN_TAC THEN CASES_ON `s:(A)sec` THEN
  REWRITE_TAC[enc_sec_def; sec_ok_pre_def; ALL_MAP; o_DEF; LTTP2AUX_line_ok_pre_enc_line;
              ETA_AX]);;

(* HOL4 line 6159 *)
let all_enc_ok_pre_enc_sec_list = prove
 (`!(code:((A)sec)list) enc c.
     ALL (sec_ok_pre c) code ==> ALL (sec_ok_pre c) (enc_sec_list enc code)`,
  REWRITE_TAC[enc_sec_list_def; LET_DEF; LET_END_DEF; ALL_MAP; o_DEF;
              LTTP2AUX_sec_ok_pre_enc_sec; ETA_AX]);;
