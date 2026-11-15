(* ========================================================================= *)
(* lab_to_targetProof_p3: part 3 of 4 (HOL4 lines 6169-9356) of              *)
(* lab_to_targetProof, port of HOL4                                          *)
(* compiler/backend/proofs/lab_to_targetProofScript.sml (CakeML v3479).      *)
(* Correctness proof for lab_to_target: lengths and positions of the        *)
(* encoded code, and compile_correct (labSem simulated by the target).      *)
(* ========================================================================= *)

needs "compiler/backend/proofs/lab_to_targetProof_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 3: HOL4 lines 6169-9356 ===== *)
(* HOL4 line 6169 *)
let remove_labels_thm = prove
 (`!clock (conf:(A)asm_config) init_pos init_labs ffi_names code code2 labs.
     remove_labels clock conf init_pos init_labs ffi_names code = SOME (code2,labs) /\
     enc_ok conf /\
     ALL sec_ends_with_label code /\
     ALL sec_labels_ok code /\
     ALL_DISTINCT (MAP Section_num code) /\
     ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) code /\
     DISJOINT (domain init_labs) (set_of_list (MAP Section_num code)) /\
     restrict_nonzero (lab_get_labels code) SUBSET
       lab_get_code_labels code UNION labs_domain init_labs /\
     ALL (sec_ok_pre conf) code /\
     EVEN init_pos /\
     (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs))
     ==> all_enc_ok conf labs ffi_names init_pos code2 /\
         code_similar code code2 /\
         (has_odd_inst code2 ==> asm_config_code_alignment conf = 0) /\
         (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
         (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==> lab_lookup l1 l2 labs = SOME x) /\
         !l1 l2 x2.
           loc_to_pc l1 l2 code = SOME x2
           ==> lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[remove_labels_def] THEN STRIP_TAC THEN
  ABBREV_TAC `ecode = enc_sec_list (asm_config_encode (conf:(A)asm_config)) code` THEN
  SUBGOAL_THEN `code_similar (ecode:((A)sec)list) code` ASSUME_TAC THENL
   [EXPAND_TAC "ecode" THEN REWRITE_TAC[code_similar_enc_sec_list; code_similar_refl];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    MAP_EVERY (fun l -> ASSUME_TAC(MATCH_MP l th))
      [code_similar_MAP_Section_num; code_similar_extract_labels;
       code_similar_get_labels; code_similar_get_code_labels]) THEN
  MP_TAC(ISPECL [`clock:num`; `conf:(A)asm_config`; `init_pos:num`;
                 `init_labs:(num spt)spt`; `ffi_names:ffiname list`;
                 `ecode:((A)sec)list`; `code2:((A)sec)list`; `labs:(num spt)spt`]
         remove_labels_loop_thm) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM ALL_MAP] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ALL_MAP] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXPAND_TAC "ecode" THEN
    ASM_SIMP_TAC[enc_sec_list_ends_with_label; enc_sec_list_sec_labels_ok;
                 all_enc_ok_pre_enc_sec_list; enc_sec_list_encd0];
    ALL_TAC] THEN
  EXPAND_TAC "ecode" THEN REWRITE_TAC[code_similar_enc_sec_list; loc_to_pc_enc_sec_list] THEN
  CONV_TAC TAUT);;

(* HOL4 line 6217 *)
let compute_labels_alt_domain_labs = prove
 (`!pos (code:((A)sec)list) labs.
     domain (compute_labels_alt pos code labs) =
     IMAGE FST (lab_get_code_labels code) UNION domain labs`,
  MATCH_MP_TAC compute_labels_alt_ind THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[compute_labels_alt_def; get_code_labels_nil; IMAGE_CLAUSES; UNION_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[compute_labels_alt_def] THEN PAIRARG_TAC THEN FS[] THEN
  REWRITE_TAC[get_code_labels_cons; sec_get_code_labels_def; domain_insert; IMAGE_UNION;
              IMAGE_CLAUSES; GSYM IMAGE_o; o_DEF; FST] THEN
  SET_TAC[]);;

(* HOL4 line 6232 *)
let remove_labels_loop_domain_labs = prove
 (`!a (b:(A)asm_config) c d e f g h.
     remove_labels_loop a b c d e f = SOME (g,h)
     ==> domain h = IMAGE FST (lab_get_code_labels f) UNION domain d`,
  MATCH_MP_TAC remove_labels_loop_ind THEN
  MAP_EVERY X_GEN_TAC [`clock:num`; `c:(A)asm_config`; `pos:num`; `init_labs:(num spt)spt`;
                       `ffis:ffiname list`; `sec_list:((A)sec)list`] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`g:((A)sec)list`; `h:(num spt)spt`] THEN
  ONCE_REWRITE_TAC[remove_labels_loop_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  PAIRARG_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP enc_secs_again_IMP_similar) THEN
  COND_CASES_TAC THENL
   [PAIRARG_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[compute_labels_alt_domain_labs] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC code_similar_get_code_labels THEN
    REWRITE_TAC[code_similar_upd_lab_len] THEN
    MATCH_MP_TAC code_similar_sym THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[] o SPECL [`isdone:bool`; `sec_list':((A)sec)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`g:((A)sec)list`; `h:(num spt)spt`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC code_similar_get_code_labels THEN
    MATCH_MP_TAC code_similar_sym THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 6256 (HOL4's c and t stand in the positions of the clock and  *)
(* the configuration of remove_labels, kept so)                              *)
let remove_labels_domain_labs = prove
 (`!c (t:(A)asm_config) k init_labs f p q labs.
     remove_labels c t k init_labs f p = SOME (q,labs)
     ==> domain labs = IMAGE FST (lab_get_code_labels p) UNION domain init_labs`,
  REWRITE_TAC[remove_labels_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP remove_labels_loop_domain_labs) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC code_similar_get_code_labels THEN
  REWRITE_TAC[code_similar_enc_sec_list; code_similar_refl]);;

(* the length fields of a line_ok line are its byte counts *)
let LTTP3AUX_line_ok_bytes = prove
 (`!(c:(A)asm_config) labs ffis pos y.
     line_ok c labs ffis pos y
     ==> LENGTH (line_bytes y) = line_length y /\
         !ys k. sec_length (CONS y ys) k = sec_length ys (k + LENGTH (line_bytes y))`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)line` THEN
  REWRITE_TAC[line_bytes_def; line_length_def; sec_length_def; LENGTH] THEN
  TRY (CASES_ON `a0:(A)asm_with_lab`) THEN
  REWRITE_TAC[line_ok_def; get_label_def; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN SIMP_TAC[]);;

(* HOL4 line 6270 (HOL4 FOLDL is FOLDL) *)
let LENGTH_prog_to_bytes = prove
 (`!(code:((A)sec)list) n (c:(A)asm_config) labs ffi pos.
     all_enc_ok c labs ffi pos code
     ==> FOLDL (\pos sec. sec_length (Section_lines sec) pos) n code =
         LENGTH (prog_to_bytes code) + n`,
  MATCH_MP_TAC prog_to_bytes_ind THEN
  SIMP[all_enc_ok_def; prog_to_bytes_def; FOLDL; sec_length_def; LENGTH; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP LTTP3AUX_line_ok_bytes th)]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + LENGTH (line_bytes (y:(A)line))`; `c:(A)asm_config`;
                                  `labs:(num spt)spt`; `ffi:ffiname list`;
                                  `pos + line_length (y:(A)line)`]) THEN
    SIMP[FOLDL; sec_length_def; LENGTH_APPEND] THEN ARITH_TAC]);;

(* HOL4 line 6288 (HOL4's binder n is unused, left out) *)
let LENGTH_prog_to_bytes2 = prove
 (`!(code:((A)sec)list) (c:(A)asm_config) labs ffi pos.
     all_enc_ok c labs ffi pos code
     ==> SUM (MAP (SUM o MAP line_length o Section_lines) code) =
         LENGTH (prog_to_bytes code)`,
  MATCH_MP_TAC prog_to_bytes_ind THEN
  SIMP[all_enc_ok_def; prog_to_bytes_def; MAP; SUM; o_THM; LENGTH; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffi:ffiname list`;
                                  `pos + line_length (y:(A)line)`]) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP LTTP3AUX_line_ok_bytes) THEN
    SIMP[MAP; SUM; o_THM; LENGTH_APPEND] THEN ARITH_TAC]);;

(* HOL4 line 6306 *)
let prog_to_bytes_APPEND = prove
 (`!(c1:((A)sec)list) c2.
     prog_to_bytes (APPEND c1 c2) = APPEND (prog_to_bytes c1) (prog_to_bytes c2)`,
  REWRITE_TAC[prog_to_bytes_MAP; MAP_APPEND; FLAT_APPEND]);;

(* HOL4 line 6312 *)
let line_ok_line_byte_length = prove
 (`!(c:(A)asm_config) labs ffi n l.
     line_ok c labs ffi n l ==> LENGTH (line_bytes l) = line_length l`,
  MESON_TAC[LTTP3AUX_line_ok_bytes]);;

(* HOL4 line 6319 *)
let lines_ok_MAP_line_byte_length = prove
 (`!(ls:((A)line)list) (c:(A)asm_config) labs ffi n.
     lines_ok c labs ffi n ls ==> MAP LENGTH (MAP line_bytes ls) = MAP line_length ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lines_ok_def; MAP; CONS_11] THEN
  ASM_MESON_TAC[line_ok_line_byte_length]);;

(* HOL4 line 6327 (HOL4's binder n is unused, left out) *)
let all_enc_ok_prog_to_bytes_EVEN = prove
 (`!(code:((A)sec)list) (c:(A)asm_config) labs ffi pos.
     EVEN pos /\ all_enc_ok c labs ffi pos code ==> EVEN (LENGTH (prog_to_bytes code))`,
  REWRITE_TAC[prog_to_bytes_MAP] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FLAT; LENGTH; EVEN] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[all_enc_ok_cons] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_FLAT]) THEN
  REWRITE_TAC[o_THM; lab_Section_lines_def; LENGTH_APPEND; EVEN_ADD; LENGTH_FLAT] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP lines_ok_MAP_line_byte_length) THEN
  SUBGOAL_THEN `EVEN (SUM (MAP line_length (a1:((A)line)list)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVEN_ADD]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 6344 (HOL4's binders conf, labs, ffis and pos are unused, left *)
(* out)                                                                       *)
let loc_to_pc_append = prove
 (CASE_TERM `!l1 l2 (c1:((A)sec)list) c2.
     ALL sec_labels_ok (APPEND c1 c2)
     ==> loc_to_pc l1 l2 (APPEND c1 c2) =
         (match loc_to_pc l1 l2 c1 with
            SOME x -> SOME x
          | NONE ->
              (match loc_to_pc l1 l2 c2 with
                 SOME x ->
                   SOME (x + SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
                                       Section_lines) c1))
               | NONE -> NONE))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; loc_to_pc_def; MAP; SUM; ADD_CLAUSES] THEN
    GEN_TAC THEN DISCH_TAC THEN CASES_ON `loc_to_pc l1 l2 (c2:((A)sec)list)` THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c2:((A)sec)list` THEN REWRITE_TAC[APPEND; ALL; ALL_APPEND] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c2:((A)sec)list`) THEN ASM_REWRITE_TAC[ALL_APPEND] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ALL sec_labels_ok (CONS (h:(A)sec) (APPEND t c2)) /\ ALL sec_labels_ok (CONS h t)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[ALL; ALL_APPEND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l1:num`; `l2:num`; `CONS (h:(A)sec) (APPEND t c2)`] loc_to_pc_thm) THEN
  MP_TAC(ISPECL [`l1:num`; `l2:num`; `CONS (h:(A)sec) t`] loc_to_pc_thm) THEN
  ASM_REWRITE_TAC[] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  CASES_ON `h:(A)sec` THEN CASE_REWRITE_TAC[MAP; SUM; o_THM; lab_Section_lines_def] THEN
  COND_CASES_TAC THEN TRY (CASES_ON `sec_loc_to_pc l2 (a1:((A)line)list)`) THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `loc_to_pc l1 l2 (t:((A)sec)list)` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  CASES_ON `loc_to_pc l1 l2 (c2:((A)sec)list)` THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN ARITH_TAC);;

(* HOL4 line 6366 *)
let all_enc_ok_append = prove
 (`!(conf:(A)asm_config) labs ffi n c1 c2.
     all_enc_ok conf labs ffi n c1 /\
     all_enc_ok conf labs ffi (n + LENGTH (prog_to_bytes c1)) c2
     ==> all_enc_ok conf labs ffi n (APPEND c1 c2)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; prog_to_bytes_def; LENGTH; ADD_CLAUSES] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[all_enc_ok_cons] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `c2:((A)sec)list` (concl th))) THEN
  REWRITE_TAC[prog_to_bytes_MAP; MAP; FLAT; o_THM; lab_Section_lines_def; LENGTH_APPEND;
              LENGTH_FLAT] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP lines_ok_MAP_line_byte_length) THEN
  REWRITE_TAC[ADD_ASSOC]);;

(* HOL4 line 6382 *)
let extract_labels_loc_to_pc = prove
 (`!l1 l2 (code:((A)sec)list).
     ALL sec_labels_ok code /\
     MEM (l1,l2) (FLAT (MAP (lab_extract_labels o Section_lines) code))
     ==> ?y. loc_to_pc l1 l2 code = SOME y`,
 MATCH_MP_TAC loc_to_pc_ind THEN
  REWRITE_TAC[MAP; FLAT; MEM; o_THM; lab_Section_lines_def; ALL; MEM_APPEND] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[loc_to_pc_def] THEN
  COND_CASES_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `xs:((A)line)list` THEN CASE_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[lab_extract_labels_def; MEM; NOT_CONS_NIL]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; NOT_CONS_NIL]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)line`; `a1:((A)line)list`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)line`; `a1:((A)line)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  CASES_ON `a0:(A)line` THEN
  REWRITE_TAC[is_Label_def; lab_extract_labels_def; MEM; PAIR_EQ; sec_labels_ok_def; ALL;
              sec_label_ok_def; distinctness "line"; injectivity "line"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ((COND_CASES_TAC THENL [MESON_TAC[]; ALL_TAC]) ORELSE ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* line_ok is monotone in the label table *)
let LTTP3AUX_line_ok_labs_mono = prove
 (`!(c:(A)asm_config) labs labs2 ffis pos y.
     (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> lab_lookup l1 l2 labs2 = SOME x) /\
     line_ok c labs ffis pos y
     ==> line_ok c labs2 ffis pos y`,
 REPEAT GEN_TAC THEN CASES_ON `y:(A)line` THEN REWRITE_TAC[line_ok_def] THEN
  TRY (CASES_ON `a0:(A)asm_with_lab`) THEN REWRITE_TAC[line_ok_def; get_label_def] THEN
  STRIP_TAC THEN EVERY_CASE_TAC THEN RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; option_DISTINCT]) THEN GVS[]);;

(* HOL4 line 6407 *)
let all_enc_ok_labs_mono = prove
 (`!(conf:(A)asm_config) labs ffi n c labs2.
     (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> lab_lookup l1 l2 labs2 = SOME x) /\
     all_enc_ok conf labs ffi n c
     ==> all_enc_ok conf labs2 ffi n c`,
  MATCH_MP_TAC all_enc_ok_ind THEN REWRITE_TAC[all_enc_ok_def] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[LTTP3AUX_line_ok_labs_mono]);;

(* HOL4 line 6423 *)
let pos_val_append = prove
 (`!(c1:((A)sec)list) i pos c2.
     ALL sec_label_zero c2
     ==> pos_val i pos (APPEND c1 c2) =
         if i <= SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines) c1)
         then pos_val i pos c1
         else pos_val (i - SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o
                                     Section_lines) c1))
                (pos + SUM (MAP (SUM o MAP line_length o Section_lines) c1)) c2`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; MAP; SUM; LE; SUB_0; ADD_CLAUSES; pos_val_def] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[sec_label_zero_pos_val_0];
    ALL_TAC] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[APPEND; MAP; SUM; o_THM; lab_Section_lines_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pos_val_thm] THEN
  COND_CASES_TAC THENL
   [CASES_ON `sec_pos_val i pos (a1:((A)line)list)` THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sec_pos_val i pos (a1:((A)line)list) = NONE` SUBST1_TAC THENL
   [MATCH_MP_TAC sec_pos_val_too_big THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_ASSOC; SUB_PLUS]);;

(* HOL4 line 6451 *)
let sec_pos_val_acc = prove
 (`!(l:((A)line)list) n i.
     LENGTH (FILTER ((~) o is_Label) l) <= i ==> sec_pos_val i n l = NONE`,
  MESON_TAC[sec_pos_val_too_big]);;

(* HOL4 line 6460 *)
let pos_val_acc = prove
 (`!(ls:((A)sec)list) n.
     pos_val (SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines) ls)) n ls =
     n + SUM (MAP (SUM o MAP line_length o Section_lines) ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; SUM; pos_val_def; ADD_CLAUSES] THEN
  CASES_ON `h:(A)sec` THEN REWRITE_TAC[pos_val_thm; o_THM; lab_Section_lines_def] THEN
  GEN_TAC THEN
  SUBGOAL_THEN
   `sec_pos_val (LENGTH (FILTER ((~) o is_Label) (a1:((A)line)list)) +
                 SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines)
                      (t:((A)sec)list))) n a1 =
    NONE` SUBST1_TAC THENL
   [MATCH_MP_TAC sec_pos_val_acc THEN ARITH_TAC; ALL_TAC] THEN
  CASE_REWRITE_TAC[ADD_SUB2] THEN ASM_REWRITE_TAC[ADD_ASSOC]);;

(* pos_val_bound by induction on the code, for all i and pos *)
let LTTP3AUX_pos_val_bound = prove
 (`!(conf:(A)asm_config) labs ffi n (code:((A)sec)list).
     all_enc_ok conf labs ffi n code
     ==> !i pos. pos_val i pos code <= pos + LENGTH (prog_to_bytes code)`,
  MATCH_MP_TAC all_enc_ok_ind THEN
  REWRITE_TAC[prog_to_bytes_def; pos_val_def; all_enc_ok_def; LENGTH; ADD_CLAUSES; LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP LTTP3AUX_line_ok_bytes) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN REPEAT COND_CASES_TAC THEN TRY ARITH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`i - 1`; `pos' + line_length (y:(A)line)`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `pos' + line_length (y:(A)line)`]) THEN ARITH_TAC);;

(* HOL4 line 6474 *)
let pos_val_bound = prove
 (`!i pos (code:((A)sec)list) (conf:(A)asm_config) labs ffi n.
     all_enc_ok conf labs ffi n code ==> pos_val i pos code <= pos + LENGTH (prog_to_bytes code)`,
  MESON_TAC[LTTP3AUX_pos_val_bound]);;

(* HOL4 line 6493 *)
let sec_loc_to_pc_bound = prove
 (`!n (xs:((A)line)list) x.
     sec_loc_to_pc n xs = SOME x ==> x <= LENGTH (FILTER ((~) o is_Label) xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[sec_loc_to_pc_def] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sec_loc_to_pc_cons; FILTER; o_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL [ARITH_TAC; ALL_TAC] THEN
  CASES_ON `sec_loc_to_pc n (t:((A)line)list)` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; I_THM] THEN ARITH_TAC);;

(* HOL4 line 6506 *)
let loc_to_pc_bound = prove
 (`!(code:((A)sec)list) l1 l2 x.
     ALL sec_labels_ok code /\ loc_to_pc l1 l2 code = SOME x
     ==> x <= SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines) code)`,
  let rest_tac =
    CASES_ON `loc_to_pc l1 l2 (t:((A)sec)list)` THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l1:num`; `l2:num`; `a:num`]) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC in
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[loc_to_pc_def; option_DISTINCT] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP loc_to_pc_thm) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
  CASES_ON `h:(A)sec` THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN REWRITE_TAC[MAP; SUM; o_THM; lab_Section_lines_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  COND_CASES_TAC THENL
   [CASES_ON `sec_loc_to_pc l2 (a1:((A)line)list)` THEN CASE_REWRITE_TAC[] THENL
     [rest_tac;
      REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP sec_loc_to_pc_bound) THEN ARITH_TAC];
    rest_tac]);;

(* list_add_if_fresh commutes with appending the fresh part of a list *)
let LTTP3AUX_list_add_if_fresh_FILTER = prove
 (`!(e:A) l2 l1.
     list_add_if_fresh e (APPEND l2 (FILTER (\n. ~MEM n l2) l1)) =
     APPEND l2 (FILTER (\n. ~MEM n l2) (list_add_if_fresh e l1))`,
  REWRITE_TAC[list_add_if_fresh_thm] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `MEM (e:A) l1` THEN ASM_CASES_TAC `MEM (e:A) l2` THEN
  ASM_REWRITE_TAC[MEM_APPEND; MEM_FILTER; FILTER_APPEND; FILTER; APPEND_NIL; APPEND_ASSOC]);;

(* HOL4 line 6526 *)
let find_ffi_names_append = prove
 (`!(l1:((A)sec)list) l2.
     find_ffi_names (APPEND l1 l2) =
     APPEND (find_ffi_names l2) (FILTER (\n. ~MEM n (find_ffi_names l2)) (find_ffi_names l1))`,
  MATCH_MP_TAC prog_to_bytes_ind THEN
  REWRITE_TAC[APPEND; find_ffi_names_def; FILTER; APPEND_NIL] THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
  CASES_ON `y:(A)line` THEN TRY (CASES_ON `a0:(A)asm_with_lab`) THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LTTP3AUX_list_add_if_fresh_FILTER]);;

(* tactic helpers: select an assumption by the head constant of its        *)
(* conclusion                                                                 *)
let LTTP3AUX_HEAD_IS (c:string) (th:thm) =
  try fst(dest_const(fst(strip_comb(concl th)))) = c with Failure _ -> false;;

(* HOL4 line 6541 *)
let all_enc_ok_aligned_pos_val = prove
 (`!(mc_conf:(A,B,C)machine_config) labs code2 pc ffi_names.
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     (has_odd_inst code2 ==>
      asm_config_code_alignment (target_config (machine_config_target mc_conf)) = 0) /\
     encoder_correct (machine_config_target mc_conf)
     ==> alignment_aligned
           (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
           (word (pos_val pc 0 code2):A word)`,
  MESON_TAC[MOD_0_aligned; pos_val_MOD_0]);;

(* HOL4 line 6551 *)
let read_ffi_bytearrays_with_next_interfer = prove
 (`!(mc:(A,B,C)machine_config) foo.
     read_ffi_bytearrays (machine_config_next_interfer_fupd (K foo) mc) =
     read_ffi_bytearrays mc`,
  REWRITE_TAC[FUN_EQ_THM; read_ffi_bytearrays_def; read_ffi_bytearray_def] THEN
  REWRITE_TAC[machine_config_INFO.ri_accfupds]);;

let _ = cake_add_simps [read_ffi_bytearrays_with_next_interfer];;

(* HOL4 line 6558 *)
let read_ffi_bytearrays_shift_interfer = prove
 (`!x (y:(A,B,C)machine_config).
     read_ffi_bytearrays (shift_interfer x y) = read_ffi_bytearrays y`,
  REWRITE_TAC[shift_interfer_def; read_ffi_bytearrays_with_next_interfer]);;

let _ = cake_add_simps [read_ffi_bytearrays_shift_interfer];;

(* HOL4 line 6564 *)
let read_ffi_bytearrays_ffi_interfer = prove
 (`!(mc:(A,B,C)machine_config) ffi.
     read_ffi_bytearrays (machine_config_ffi_interfer_fupd (K ffi) mc) =
     read_ffi_bytearrays mc`,
  REWRITE_TAC[FUN_EQ_THM; read_ffi_bytearrays_def; read_ffi_bytearray_def] THEN
  REWRITE_TAC[machine_config_INFO.ri_accfupds]);;

let _ = cake_add_simps [read_ffi_bytearrays_ffi_interfer];;

(* HOL4 line 6570 (HOL4's _bytes and _len are ordinary variables) *)
let IMP_ffi_entry_pcs_disjoint_Asm = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) (mc_conf:(A,B,C)machine_config) code2 labs
     ffi_names instr _bytes _len p bytes' (t1:(A)asm_state).
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     asm_fetch_aux (lab_state_pc s1) (lab_state_code s1) = SOME (Asm instr _bytes _len) /\
     (!op re a. ~(instr = ShareMem op re a)) /\
     share_mem_domain_code_rel mc_conf p code2 (lab_state_shared_mem_domain s1) /\
     bytes_in_mem (word_add p (word (pos_val (lab_state_pc s1) 0 code2))) bytes'
       (asm_state_mem t1) (asm_state_mem_domain t1) (lab_state_mem_domain s1) /\
     pos_val (lab_state_pc s1 + 1) 0 code2 = LENGTH bytes' + pos_val (lab_state_pc s1) 0 code2 /\
     asm_state_pc t1 = word_add p (word (pos_val (lab_state_pc s1) 0 code2))
     ==> ffi_entry_pcs_disjoint mc_conf t1 (LENGTH bytes')`,
 REPEAT STRIP_TAC THEN REWRITE_TAC[ffi_entry_pcs_disjoint_def] THEN
  FIRST_ASSUM(MP_TAC o SPEC `lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)` o
              MATCH_MP code_similar_IMP_asm_fetch_aux_line_similar) THEN
  ASM_REWRITE_TAC[OPTREL_SOME] THEN DISCH_THEN(X_CHOOSE_THEN `y0:(A)line` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (line_bytes (y0:(A)line)) = LENGTH (bytes':byte list)` ASSUME_TAC THENL
   [MATCH_MP_TAC asm_fetch_aux_pos_val_LENGTH_EQ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[share_mem_domain_code_rel_def] o
                check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
  DISCH_THEN(MP_TAC o SPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`;
                             `y0:(A)line`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[line_similar_def]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

(* HOL4 line 6600 *)
let IMP_ffi_entry_pcs_disjoint_LabAsm = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) (mc_conf:(A,B,C)machine_config) code2 labs
     ffi_names instr _pos _bytes _len p bytes' (t1:(A)asm_state).
     code_similar (lab_state_code s1) code2 /\
     all_enc_ok (target_config (machine_config_target mc_conf)) labs ffi_names 0 code2 /\
     asm_fetch_aux (lab_state_pc s1) (lab_state_code s1) =
       SOME (LabAsm instr _pos _bytes _len) /\
     share_mem_domain_code_rel mc_conf p code2 (lab_state_shared_mem_domain s1) /\
     bytes_in_mem (word_add p (word (pos_val (lab_state_pc s1) 0 code2))) bytes'
       (asm_state_mem t1) (asm_state_mem_domain t1) (lab_state_mem_domain s1) /\
     pos_val (lab_state_pc s1 + 1) 0 code2 = LENGTH bytes' + pos_val (lab_state_pc s1) 0 code2 /\
     asm_state_pc t1 = word_add p (word (pos_val (lab_state_pc s1) 0 code2))
     ==> ffi_entry_pcs_disjoint mc_conf t1 (LENGTH bytes')`,
 REPEAT STRIP_TAC THEN REWRITE_TAC[ffi_entry_pcs_disjoint_def] THEN
  FIRST_ASSUM(MP_TAC o SPEC `lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)` o
              MATCH_MP code_similar_IMP_asm_fetch_aux_line_similar) THEN
  ASM_REWRITE_TAC[OPTREL_SOME] THEN DISCH_THEN(X_CHOOSE_THEN `y0:(A)line` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH (line_bytes (y0:(A)line)) = LENGTH (bytes':byte list)` ASSUME_TAC THENL
   [MATCH_MP_TAC asm_fetch_aux_pos_val_LENGTH_EQ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[share_mem_domain_code_rel_def] o
                check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
  DISCH_THEN(MP_TAC o SPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`;
                             `y0:(A)line`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[line_similar_def]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

(* HOL4 line 6629 *)
let asm_fetch_SOME_IMP_LESS_num_pcs = prove
 (`!pc (secs:((A)sec)list) x. asm_fetch_aux pc secs = SOME x ==> pc < num_pcs secs`,
  MATCH_MP_TAC asm_fetch_aux_ind THEN
  REWRITE_TAC[asm_fetch_aux_def; num_pcs_def; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `pos = 0` THEN ASM_REWRITE_TAC[] THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:(A)line`) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

(* HOL4 line 6643 *)
let GENLIST_asm_fetch_aux_next = prove
 (`!(x:(A)line) xs k rest n.
     ~is_Label x
     ==> list_of_seq (\i. (i,asm_fetch_aux i (CONS (Section k (CONS x xs)) rest))) (n + 1) =
         CONS (0,SOME x)
           (list_of_seq (\i. (i + 1,asm_fetch_aux i (CONS (Section k xs) rest))) n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ADD1; LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[asm_fetch_aux_def; o_DEF; NOT_SUC; SUC_SUB1; ADD1]);;

(* HOL4 line 6657 *)
let pos_val_acc_sum = prove
 (`!i pos (secs:((A)sec)list) x y. x + y = pos ==> x + pos_val i y secs = pos_val i pos secs`,
  MATCH_MP_TAC pos_val_ind THEN REWRITE_TAC[pos_val_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[ASSUME `is_Label (y:(A)line)`]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[ASSUME `~is_Label (y:(A)line)`;
                                           ASSUME `~(i = 0)`]) THEN
  ASM_ARITH_TAC);;

(* HOL4 line 6671 *)
let pos_val_acc_0 = prove
 (`!i pos (secs:((A)sec)list). pos + pos_val i 0 secs = pos_val i pos secs`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC pos_val_acc_sum THEN REWRITE_TAC[ADD_CLAUSES]);;

(* HOL4 line 6678 *)
let FILTER_mmio_pcs_min_index = prove
 (`!l ffis.
     ALL (\x. ?op. x = SharedMem op) l
     ==> mmio_pcs_min_index (APPEND (FILTER (\x. ?s. x = ExtCall s) ffis) l) =
         SOME (LENGTH (FILTER (\x. ?s. x = ExtCall s) ffis))`,
 REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "allL" o BETA_RULE o REWRITE_RULE[GSYM ALL_EL]) THEN
  REWRITE_TAC[mmio_pcs_min_index_def] THEN
  ABBREV_TAC `fl = FILTER (\x. ?s. x = ExtCall s) (ffis:ffiname list)` THEN
  SUBGOAL_THEN `ALL (\x. ?s. x = ExtCall s) (fl:ffiname list)`
    (LABEL_TAC "allF" o BETA_RULE o REWRITE_RULE[GSYM ALL_EL]) THENL
   [EXPAND_TAC "fl" THEN REWRITE_TAC[ALL_FILTER; ALL_T]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (x <= LENGTH (APPEND fl l) /\
         (!j. j < x ==> ?s. EL j (APPEND fl l) = ExtCall s) /\
         (!j. x <= j /\ j < LENGTH (APPEND fl l) ==> ?op. EL j (APPEND fl l) = SharedMem op)) <=>
        x = LENGTH (fl:ffiname list)`
   (fun th -> REWRITE_TAC[th; some_EQ]) THEN
  REWRITE_TAC[LENGTH_APPEND; EL_APPEND] THEN GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2"))) THEN
    REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "h1" (MP_TAC o SPEC `LENGTH (fl:ffiname list)`) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th; LT_REFL; SUB_REFL]) o check (is_binary "<" o concl)) THEN
      USE_THEN "allL" (MP_TAC o SPEC `0`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MESON_TAC[distinctness "ffiname"];
      USE_THEN "h2" (MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "allF" (MP_TAC o SPEC `x:num`) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (is_binary "<" o concl)) THEN
      MESON_TAC[distinctness "ffiname"]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_ADD] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM NOT_LE] THEN
    USE_THEN "allL" MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* HOL4 line 6721 *)
let pos_val_GE_pc = prove
 (`!i p (code2:((A)sec)list). p <= pos_val i p code2`,
  MATCH_MP_TAC pos_val_ind THEN REWRITE_TAC[pos_val_def; LE_REFL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(lhand(concl th))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 6730 *)
let enc_ok_LENGTH_GT_0 = prove
 (`!(c:(A)asm_config) l. enc_ok c ==> 0 < LENGTH (asm_config_encode c l)`,
  REWRITE_TAC[enc_ok_def] THEN MESON_TAC[LT_NZ]);;

(* a line_ok line that is not a label has bytes *)
let LTTP3AUX_line_ok_length_pos = prove
 (`!(c:(A)asm_config) labs ffis pos y.
     enc_ok c /\ line_ok c labs ffis pos y /\ ~is_Label y ==> 0 < line_length y`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)line` THEN REWRITE_TAC[is_Label_def; line_length_def] THEN
  TRY (CASES_ON `a0:(A)asm_with_lab`) THEN
  REWRITE_TAC[line_ok_def; get_label_def; LET_DEF; LET_END_DEF; enc_with_nop_thm] THEN
  EVERY_CASE_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)))) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  MATCH_MP_TAC(ARITH_RULE `0 < a ==> 0 < a + b`) THEN ASM_SIMP_TAC[enc_ok_LENGTH_GT_0]);;

(* HOL4 line 6739 *)
let pos_val_mono = prove
 (`!i p (code2:((A)sec)list) j p' (c:(A)asm_config) labs ffis.
     i < j /\ j <= num_pcs code2 /\ all_enc_ok c labs ffis p' code2 /\ enc_ok c
     ==> pos_val i p code2 < pos_val j p code2`,
 MATCH_MP_TAC pos_val_ind THEN REWRITE_TAC[pos_val_def; num_pcs_def; all_enc_ok_def] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(j = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `i < (j:num)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `pos + line_length (y:(A)line)` THEN
    REWRITE_TAC[pos_val_GE_pc; ARITH_RULE `p < p + n <=> 0 < n`] THEN
    MATCH_MP_TAC LTTP3AUX_line_ok_length_pos THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p' + line_length (y:(A)line)`; `c:(A)asm_config`; `labs:(num spt)spt`;
                        `ffis:ffiname list`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`i < (j:num)`; `j <= 1 + num_pcs (CONS (Section k ys) (xs:((A)sec)list))`;
                         `~(i = 0)`] THEN
  ARITH_TAC);;

(* HOL4 line 6782 *)
let pos_val_mono_inv = prove
 (`!i p (code2:((A)sec)list) j (c:(A)asm_config) labs ffis p'.
     pos_val i p code2 < pos_val j p code2 /\ i <= num_pcs code2 /\
     all_enc_ok c labs ffis p' code2 /\ enc_ok c
     ==> i < j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  ASM_CASES_TAC `j:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`j:num`; `p:num`; `code2:((A)sec)list`; `i:num`; `p':num`;
                 `c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`] pos_val_mono) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `pos_val i p code2 < pos_val j p (code2:((A)sec)list)` THEN ARITH_TAC);;

(* HOL4 line 6805 *)
let pos_val_inj = prove
 (`!p (code2:((A)sec)list) j i (c:(A)asm_config) labs ffis p'.
     pos_val i p code2 = pos_val j p code2 /\
     i <= num_pcs code2 /\ j <= num_pcs code2 /\
     all_enc_ok c labs ffis p' code2 /\ enc_ok c
     ==> i = j`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `i < j \/ j < i \/ i = j:num`) THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`i:num`; `p:num`; `code2:((A)sec)list`; `j:num`; `p':num`;
                   `c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`] pos_val_mono);
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`j:num`; `p:num`; `code2:((A)sec)list`; `i:num`; `p':num`;
                   `c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`] pos_val_mono)] THEN
  ASM_REWRITE_TAC[LT_REFL]);;

(* HOL4 line 6829 *)
let pos_val_num_pcs = prove
 (`!(c:(A)asm_config) labs ffis p' code2 p.
     all_enc_ok c labs ffis p' code2
     ==> pos_val (num_pcs code2) p code2 = p + LENGTH (prog_to_bytes code2)`,
  MATCH_MP_TAC all_enc_ok_ind THEN
  REWRITE_TAC[all_enc_ok_def; pos_val_def; num_pcs_def; prog_to_bytes_def; LENGTH;
              ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(1 + n = 0) /\ (1 + n) - 1 = n`] THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP LTTP3AUX_line_ok_bytes) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);;

(* HOL4 line 6847 *)
let pos_val_GE_num_pcs = prove
 (`!pc p (code2:((A)sec)list).
     num_pcs code2 <= pc ==> pos_val (num_pcs code2) p code2 = pos_val pc p code2`,
 MATCH_MP_TAC pos_val_ind THEN REWRITE_TAC[pos_val_def; num_pcs_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(1 + n = 0) /\ (1 + n) - 1 = n`] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(i = 0) /\ num_pcs (CONS (Section k ys) (xs:((A)sec)list)) <= i - 1`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `1 + num_pcs (CONS (Section k ys) (xs:((A)sec)list)) <= i` THEN ARITH_TAC;
    ASM_MESON_TAC[]]);;

(* HOL4 line 6859 *)
let pos_val_0_aux = prove
 (`!(c:(A)asm_config) labs ffis p xs pos.
     all_enc_ok c labs ffis p xs ==> pos_val 0 pos xs = pos`,
 MATCH_MP_TAC all_enc_ok_ind THEN REWRITE_TAC[all_enc_ok_def; pos_val_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `line_ok c labs ffis pos (y:(A)line)` THEN
  CASES_ON `y:(A)line` THEN REWRITE_TAC[is_Label_def; line_ok_def; line_length_def] THEN
  SIMP_TAC[ADD_CLAUSES]);;

(* HOL4 line 6871 *)
let asm_fetch_aux_pos_val_SUC = prove
 (`!pc p (code2:((A)sec)list) p' (c:(A)asm_config) labs ffi line.
     all_enc_ok c labs ffi p' code2 /\ asm_fetch_aux pc code2 = SOME line
     ==> LENGTH (line_bytes line) + pos_val pc p code2 = pos_val (pc + 1) p code2`,
 MATCH_MP_TAC pos_val_ind THEN
  REWRITE_TAC[pos_val_def; asm_fetch_aux_def; all_enc_ok_def; option_DISTINCT] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_RULE `~(1 = 0) /\ (n + 1) - 1 = n`] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                                       type_of(lhs(concl th)) = `:(A)line`)) THEN
    FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o MATCH_MP LTTP3AUX_line_ok_bytes) THEN
    FIRST_ASSUM(SUBST1_TAC o SPEC `pos + line_length (y:(A)line)` o MATCH_MP pos_val_0_aux) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p' + line_length (y:(A)line)`; `c:(A)asm_config`;
                                `labs:(num spt)spt`; `ffi:ffiname list`; `line:(A)line`] o
                check (is_forall o concl)) THEN
  ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(i = 0) ==> 1 <= i`]);;

(* HOL4 line 6889 *)
let pos_val_asm_fetch_aux_distinct = prove
 (`!(c:(A)asm_config) labs ffis p' (code2:((A)sec)list) pc line a p pc'.
     all_enc_ok c labs ffis p' code2 /\
     enc_ok c /\
     asm_fetch_aux pc code2 = SOME line /\
     a < LENGTH (line_bytes line) /\
     LENGTH (prog_to_bytes code2) < dimword (:A) /\
     ~(pc' = pc)
     ==> ~(a + pos_val pc p code2 = pos_val pc' p code2)`,
 REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP asm_fetch_SOME_IMP_LESS_num_pcs) THEN
  MP_TAC(ISPECL [`pc:num`; `p:num`; `code2:((A)sec)list`; `p':num`; `c:(A)asm_config`;
                 `labs:(num spt)spt`; `ffis:ffiname list`; `line:(A)line`]
         asm_fetch_aux_pos_val_SUC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i j. i < j /\ j <= num_pcs (code2:((A)sec)list)
                      ==> pos_val i p code2 < pos_val j p code2` ASSUME_TAC THENL
   [ASM_MESON_TAC[pos_val_mono]; ALL_TAC] THEN
  SUBGOAL_THEN `pos_val (pc + 1) p code2 <= pos_val pc' p (code2:((A)sec)list) \/
                pos_val pc' p code2 < pos_val pc p code2` MP_TAC THENL
   [ALL_TAC; UNDISCH_TAC `a < LENGTH (line_bytes (line:(A)line))` THEN ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `pc' < pc \/ pc + 1 <= pc'` DISJ_CASES_TAC THENL
   [UNDISCH_TAC `~(pc':num = pc)` THEN ARITH_TAC;
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; DISJ1_TAC] THEN
  ASM_CASES_TAC `pc' <= num_pcs (code2:((A)sec)list)` THENL
   [ASM_CASES_TAC `pc + 1 = pc'` THEN ASM_REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pc':num`; `p:num`; `code2:((A)sec)list`] pos_val_GE_num_pcs) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_CASES_TAC `pc + 1 = num_pcs (code2:((A)sec)list)` THEN ASM_REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 6948 *)
let bytes_in_memory_eq_mem = prove
 (`!pc bytes (t1:(A)asm_state) (mc_conf:(A,B,C)machine_config) ms1.
     (!a. a IN asm_state_mem_domain t1
          ==> target_get_byte (machine_config_target mc_conf) ms1 a = asm_state_mem t1 a) /\
     bytes_in_memory pc bytes (asm_state_mem t1) (asm_state_mem_domain t1)
     ==> bytes_in_memory pc bytes (target_get_byte (machine_config_target mc_conf) ms1)
           (asm_state_mem_domain t1)`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`pc:A word`,`pc:A word`) THEN
  SPEC_TAC(`bytes:byte list`,`bytes:byte list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[bytes_in_memory_def] THEN ASM_MESON_TAC[]);;

(* HOL4 lines 6959-7061: fun map_first_cj, val enc_is_valid_mapped_access_tac, *)
(* fun share_mem_load_compile_correct_tac, fun                               *)
(* share_mem_store_compile_correct_tac (tactics)                             *)

(* HOL4 line 7159 *)
let ffi_entry_pcs_NOT_ccache_OR_halt_pc = prove
 (`!pc (mc_conf:(A,B,C)machine_config) index.
     find_index pc (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index /\
     ~(machine_config_halt_pc mc_conf = EL index (machine_config_ffi_entry_pcs mc_conf)) /\
     ~(machine_config_ccache_pc mc_conf = EL index (machine_config_ffi_entry_pcs mc_conf))
     ==> ~(pc = machine_config_ccache_pc mc_conf) /\ ~(pc = machine_config_halt_pc mc_conf)`,
  REWRITE_TAC[find_index_INDEX_OF; INDEX_OF_eq_SOME] THEN MESON_TAC[]);;

(* HOL4 line 7171: val share_mem_eval_expand_tac (a tactic) *)

(* the value of a some that is SOME satisfies the predicate *)
let LTTP3AUX_some_SOME = prove
 (`!(P:A->bool) i. (some) P = SOME i ==> P i`,
  REWRITE_TAC[some_DEF] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 7202 *)
let ffi_name_NOT_Mapped = prove
 (`!ffi_names i s.
     mmio_pcs_min_index ffi_names = SOME i /\ (?str. s = ExtCall str) /\ MEM s ffi_names
     ==> get_ffi_index ffi_names s < i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mmio_pcs_min_index_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o BETA_RULE o MATCH_MP LTTP3AUX_some_SOME) THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC o SPEC `0` o MATCH_MP find_index_MEM) THEN
  ASM_REWRITE_TAC[get_ffi_index_def; ADD_CLAUSES; the_def] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "SharedMem" with _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[distinctness "ffiname"]);;

(* HOL4 line 7226 *)
let mmio_pcs_min_index_is_SOME = prove
 (`!ffi_names i.
     mmio_pcs_min_index ffi_names = SOME i
     ==> i <= LENGTH ffi_names /\
         (!j. j < i ==> ?s. EL j ffi_names = ExtCall s) /\
         (!j. i <= j /\ j < LENGTH ffi_names ==> ?op. EL j ffi_names = SharedMem op)`,
  REWRITE_TAC[mmio_pcs_min_index_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(ACCEPT_TAC o BETA_RULE o MATCH_MP LTTP3AUX_some_SOME));;

(* HOL4 line 7243 *)
let no_share_mem_lemma = prove
 (`!ffi_names i pc (code:((A)sec)list) c l n.
     mmio_pcs_min_index ffi_names = SOME i /\
     asm_fetch_aux pc code = SOME (LabAsm lab_Install c l n) /\
     no_install_or_no_share_mem code ffi_names
     ==> i = LENGTH ffi_names`,
  REPEAT GEN_TAC THEN REWRITE_TAC[no_install_or_no_share_mem_def; lab_no_install_def] THEN
  STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP mmio_pcs_min_index_is_SOME) THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "SharedMem" with _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_EL]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "ExtCall" with _ -> false)) (concl th) &&
     not (can (find_term (fun t -> t = `j:num`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[distinctness "ffiname"]);;

(* HOL4 line 7258 *)
let asm_fetch_aux_APPEND1 = prove
 (`!pc (code:((A)sec)list) sec_list.
     pc < num_pcs code ==> asm_fetch_aux pc (APPEND code sec_list) = asm_fetch_aux pc code`,
  MATCH_MP_TAC asm_fetch_aux_ind THEN
  REWRITE_TAC[asm_fetch_aux_def; num_pcs_def; APPEND; LT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `pos < 1 + num_pcs (CONS (Section k ys) (xs:((A)sec)list))` THEN
  UNDISCH_TAC `~(pos = 0)` THEN ARITH_TAC);;

(* HOL4 line 7270 (for every start position) *)
let LTTP3AUX_pos_val_APPEND1 = prove
 (`!pc pos (code:((A)sec)list) sec_list.
     pc < num_pcs code ==> pos_val pc pos (APPEND code sec_list) = pos_val pc pos code`,
  MATCH_MP_TAC pos_val_ind THEN
  REWRITE_TAC[pos_val_def; num_pcs_def; APPEND; LT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `i < 1 + num_pcs (CONS (Section k ys) (xs:((A)sec)list))` THEN
  UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC);;

let pos_val_APPEND1 = prove
 (`!pc (code:((A)sec)list) sec_list.
     pc < num_pcs code ==> pos_val pc 0 (APPEND code sec_list) = pos_val pc 0 code`,
  MESON_TAC[LTTP3AUX_pos_val_APPEND1]);;

(* HOL4 line 7290 *)
let asm_fetch_aux_APPEND2 = prove
 (`!(code:((A)sec)list) pc sec_list.
     asm_fetch_aux (pc + num_pcs code) (APPEND code sec_list) = asm_fetch_aux pc sec_list`,
  MATCH_MP_TAC num_pcs_ind THEN
  REWRITE_TAC[asm_fetch_aux_def; num_pcs_def; APPEND; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `is_Label (x:(A)line)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `~(pc + 1 + n = 0) /\ (pc + 1 + n) - 1 = pc + n`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 7302 (for every start position) *)
let LTTP3AUX_pos_val_APPEND2 = prove
 (`!(c:(A)asm_config) labs ffis p (code:((A)sec)list).
     all_enc_ok c labs ffis p code
     ==> !pos pc sec_list.
           pos_val (pc + num_pcs code) pos (APPEND code sec_list) =
           pos + LENGTH (prog_to_bytes code) + pos_val pc 0 sec_list`,
 MATCH_MP_TAC all_enc_ok_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[num_pcs_def; prog_to_bytes_def; APPEND; LENGTH; ADD_CLAUSES; pos_val_acc_0];
    REWRITE_TAC[all_enc_ok_def; pos_val_def; num_pcs_def; prog_to_bytes_def; APPEND] THEN
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[all_enc_ok_def; pos_val_def; num_pcs_def; prog_to_bytes_def; APPEND] THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP LTTP3AUX_line_ok_bytes) THEN
  ASM_CASES_TAC `is_Label (y:(A)line)` THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN
  REWRITE_TAC[ARITH_RULE `~(pc + 1 + n = 0) /\ (pc + 1 + n) - 1 = pc + n`] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let pos_val_APPEND2 = prove
 (`!(c:(A)asm_config) labs ffis p code pc sec_list.
     all_enc_ok c labs ffis p code
     ==> pos_val (pc + num_pcs code) 0 (APPEND code sec_list) =
         LENGTH (prog_to_bytes code) + pos_val pc 0 sec_list`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_pos_val_APPEND2) THEN
  SIMP_TAC[ADD_CLAUSES]);;

(* HOL4 line 7317 *)
let get_shmem_info_MappedRead_or_MappedWrite = prove
 (`!(sec:((A)sec)list) pos ffi_names info new_ffi_names new_info.
     get_shmem_info sec pos ffi_names info = (new_ffi_names,new_info)
     ==> ?l. new_ffi_names = APPEND ffi_names l /\ ALL (\x. ?op. x = SharedMem op) l`,
  MATCH_MP_TAC get_shmem_info_ind THEN REWRITE_TAC[get_shmem_info_def; PAIR_EQ] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `[]:ffiname list` THEN ASM_REWRITE_TAC[APPEND_NIL; ALL];
    DISCH_TAC THEN PAIRARG_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`name:shmem_op`; `nb:byte`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`new_ffi_names:ffiname list`; `new_info:shmem_info_num list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l:ffiname list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (SharedMem name) l` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; ALL] THEN MESON_TAC[]]);;

(* HOL4 line 7331 *)
let no_share_mem_APPEND = prove
 (`!(code:((A)sec)list) secs.
     no_share_mem_inst code /\ no_share_mem_inst secs
     ==> no_share_mem_inst (APPEND code secs)`,
  REWRITE_TAC[no_share_mem_inst_def] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `p < num_pcs (code:((A)sec)list)` THENL
   [ASM_MESON_TAC[asm_fetch_aux_APPEND1]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(p < n) ==> p = (p - n) + n`)) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th] THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[th])) THEN
  ASM_MESON_TAC[asm_fetch_aux_APPEND2]);;

(* HOL4 line 7348 *)
let no_install_APPEND_IMP = prove
 (`!(code:((A)sec)list) secs.
     lab_no_install (APPEND code secs) ==> lab_no_install code /\ lab_no_install secs`,
  REWRITE_TAC[lab_no_install_def] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[asm_fetch_aux_APPEND1; asm_fetch_SOME_IMP_LESS_num_pcs];
    ASM_MESON_TAC[asm_fetch_aux_APPEND2]]);;

(* the lines of similar code at one position *)
let LTTP3AUX_code_similar_fetch = prove
 (`!(code:((A)sec)list) sec_list p y.
     code_similar code sec_list /\ asm_fetch_aux p sec_list = SOME y
     ==> ?z. asm_fetch_aux p code = SOME z /\ line_similar z y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `p:num` o MATCH_MP code_similar_IMP_asm_fetch_aux_line_similar) THEN
  ASM_REWRITE_TAC[OPTREL_SOME]);;

(* HOL4 line 7364 *)
let code_similar_IMP_both_no_share_mem = prove
 (`!(code:((A)sec)list) sec_list.
     code_similar code sec_list /\ no_share_mem_inst code ==> no_share_mem_inst sec_list`,
  REWRITE_TAC[no_share_mem_inst_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_code_similar_fetch o
              CONJ (ASSUME `code_similar (code:((A)sec)list) sec_list`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:(A)line` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `line_similar (z:(A)line) (Asm (ShareMem op re a) inst len)` THEN
  CASES_ON `z:(A)line` THEN REWRITE_TAC[line_similar_def] THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 7380 *)
let code_similar_IMP_both_no_install_or_no_share_mem = prove
 (`!(code:((A)sec)list) sec_list ffi_names.
     code_similar code sec_list /\ no_install_or_no_share_mem code ffi_names
     ==> no_install_or_no_share_mem sec_list ffi_names`,
  REWRITE_TAC[no_install_or_no_share_mem_def] THEN REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[code_similar_IMP_both_no_share_mem]; DISJ2_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lab_no_install_def]) THEN
  REWRITE_TAC[lab_no_install_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_code_similar_fetch o
              CONJ (ASSUME `code_similar (code:((A)sec)list) sec_list`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:(A)line` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `line_similar (z:(A)line) (LabAsm lab_Install w bytes l)` THEN
  CASES_ON `z:(A)line` THEN REWRITE_TAC[line_similar_def] THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]);;

(* no_share_mem_inst of the rest of the code *)
let LTTP3AUX_no_share_mem_inst_CONS = prove
 (`(!k (rest:((A)sec)list).
      no_share_mem_inst (CONS (Section k []) rest) ==> no_share_mem_inst rest) /\
   (!k (y:(A)line) ys rest.
      no_share_mem_inst (CONS (Section k (CONS y ys)) rest)
      ==> no_share_mem_inst (CONS (Section k ys) rest)) /\
   (!k m r ad bytes x (xs:((A)line)list) rest.
      ~no_share_mem_inst (CONS (Section k (CONS (Asm (ShareMem m r ad) bytes x) xs)) rest))`,
  REWRITE_TAC[no_share_mem_inst_def] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[asm_fetch_aux_def];
    ASM_CASES_TAC `is_Label (y:(A)line)` THENL
     [ASM_MESON_TAC[asm_fetch_aux_def];
      FIRST_X_ASSUM(MP_TAC o SPEC `p + 1`) THEN
      ASM_REWRITE_TAC[asm_fetch_aux_def; ADD_EQ_0; ARITH_RULE `~(1 = 0) /\ (p + 1) - 1 = p`] THEN
      ASM_MESON_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[asm_fetch_aux_def; is_Label_def] THEN
    MESON_TAC[]]);;

(* HOL4 line 7413 *)
let no_share_mem_IMP_get_shmem_info = prove
 (`!(code:((A)sec)list) p ffi_names shmem_info.
     no_share_mem_inst code
     ==> get_shmem_info code p ffi_names shmem_info = (ffi_names,shmem_info)`,
  MATCH_MP_TAC get_shmem_info_ind THEN REWRITE_TAC[get_shmem_info_def] THEN
  REPEAT STRIP_TAC THEN TRY (ASM_MESON_TAC[LTTP3AUX_no_share_mem_inst_CONS]));;

(* HOL4 line 7441 *)
let Sh_not_Ext = prove
 (`!x. (?s. x = SharedMem s) <=> (!s. ~(x = ExtCall s))`,
  GEN_TAC THEN CASES_ON `x:ffiname` THEN
  REWRITE_TAC[distinctness "ffiname"; injectivity "ffiname"] THEN MESON_TAC[]);;

(* HOL4 line 7447 *)
let not_Sh_Ext = prove
 (`!x. (!s. ~(x = SharedMem s)) <=> (?s. x = ExtCall s)`,
  GEN_TAC THEN CASES_ON `x:ffiname` THEN
  REWRITE_TAC[distinctness "ffiname"; injectivity "ffiname"] THEN MESON_TAC[]);;

(* HOL4 line 7453 *)
let oracle_tie_shift_gen = prove
 (`!(mc_conf:(A,B,C)machine_config) mc2 ms1 (s1:(A,D,FFI)lab_state) ms2 l.
     oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference mc2 (lab_state_ffi s1) k ms2) /\
     machine_config_target mc2 = machine_config_target mc_conf /\
     machine_config_callee_saved_regs mc2 = machine_config_callee_saved_regs mc_conf /\
     machine_config_ptr_reg mc2 = machine_config_ptr_reg mc_conf
     ==> oracle_tie mc2 ms2 s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (GEN_ALL next_interference_shift)) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `lab_state_ffi (s1:(A,D,FFI)lab_state)`;
                 `ms1:B`; `mc2:(A,B,C)machine_config`; `lab_state_ffi (s1:(A,D,FFI)lab_state)`;
                 `ms2:B`] (GENL [`mc1:(A,B,C)machine_config`; `ffi1:(FFI)ffi_state`; `ms1:B`;
                                 `mc2:(A,B,C)machine_config`; `ffi2:(FFI)ffi_state`; `ms2:B`]
                                constructed_oracles_EQ)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `oracle_tie (mc_conf:(A,B,C)machine_config) ms1 (s1:(A,D,FFI)lab_state)` THEN
  ASM_REWRITE_TAC[oracle_tie_def]);;

(* HOL4 line 7472 *)
let oracle_tie_ccache_residues = prove
 (`!(mc_conf:(A,B,C)machine_config) mc2 ms1 (s1:(A,D,FFI)lab_state) ms2 l (t1:(A)asm_state).
     oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference mc2 (lab_state_ffi s1) k ms2) /\
     machine_config_target mc2 = machine_config_target mc_conf /\
     machine_config_ptr_reg mc2 = machine_config_ptr_reg mc_conf /\
     machine_config_len_reg mc2 = machine_config_len_reg mc_conf /\
     machine_config_ccache_interfer mc2 = machine_config_ccache_interfer mc_conf /\
     ~(target_get_pc (machine_config_target mc2) ms2 IN
       machine_config_prog_addresses mc2 DIFF set_of_list (machine_config_ffi_entry_pcs mc2)) /\
     ~(target_get_pc (machine_config_target mc2) ms2 = machine_config_halt_pc mc2) /\
     target_get_pc (machine_config_target mc2) ms2 = machine_config_ccache_pc mc2
     ==> (\a. get_reg_value (lab_state_cc_regs s1 0 a) (asm_state_regs t1 a) I) =
         (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
                 a = machine_config_ptr_reg mc_conf \/
                 ~(a < asm_config_reg_count (target_config (machine_config_target mc_conf))) \/
                 MEM a (asm_config_avoid_regs (target_config (machine_config_target mc_conf)))
              then asm_state_regs t1 a
              else target_get_reg (machine_config_target mc_conf)
                     (machine_config_ccache_interfer mc_conf 0
                        (target_get_reg (machine_config_target mc_conf) ms2
                           (machine_config_ptr_reg mc_conf),
                         target_get_reg (machine_config_target mc_conf) ms2
                           (machine_config_len_reg mc_conf),ms2)) a) /\
         (\n. lab_state_cc_fp_regs s1 0 n) =
         (\n. target_get_fp_reg (machine_config_target mc_conf)
                (machine_config_ccache_interfer mc_conf 0
                   (target_get_reg (machine_config_target mc_conf) ms2
                      (machine_config_ptr_reg mc_conf),
                    target_get_reg (machine_config_target mc_conf) ms2
                      (machine_config_len_reg mc_conf),ms2)) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (GEN_ALL next_interference_shift)) THEN
  MP_TAC(ISPECL [`mc2:(A,B,C)machine_config`; `ms2:B`; `lab_state_ffi (s1:(A,D,FFI)lab_state)`]
           (GENL [`mc:(A,B,C)machine_config`; `ms:B`; `ffi:(FFI)ffi_state`]
                 next_interference_ccache)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`; `s1:(A,D,FFI)lab_state`]
                oracle_tie_ccache_step) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms2:B)
       (machine_config_ptr_reg mc_conf)`;
    `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) (ms2:B)
       (machine_config_len_reg mc_conf)`;
    `ms2:B`;
    `machine_config_ccache_interfer (mc_conf:(A,B,C)machine_config) 0
       (target_get_reg (machine_config_target mc_conf) (ms2:B) (machine_config_ptr_reg mc_conf),
        target_get_reg (machine_config_target mc_conf) ms2 (machine_config_len_reg mc_conf),
        ms2)`;
    `machine_config_ccache_interfer_fupd
       (K (shift_seq 1 (machine_config_ccache_interfer (mc2:(A,B,C)machine_config)))) mc2`;
    `lab_state_ffi (s1:(A,D,FFI)lab_state)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[get_reg_value_def; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* compile_correct (HOL4 line 7528).  The HOL4 proof is an induction on      *)
(* labSem's evaluate with one Resume block per kind of instruction; here     *)
(* each case is a lemma LTTP3AUX_cc_<case> whose hypotheses are the facts    *)
(* of the case split, the induction hypothesis of the case (the conjunct of *)
(* lab_evaluate_ind) and the hypotheses of compile_correct.                  *)
(* ------------------------------------------------------------------------- *)

(* record update theorems of the states and configurations *)
let LTTP3AUX_RECS =
  [(record_info "lab_state").ri_accfupds; (record_info "asm_state").ri_accfupds;
   (record_info "machine_config").ri_accfupds; K_THM];;

(* the parts of state_rel used to run one target step *)
let LTTP3AUX_state_rel_step_facts = prove
 (CASE_TERM `!(mc_conf:(A,B,C)machine_config) code2 labs p
     (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) ms1.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> target_state_rel (machine_config_target mc_conf) t1 ms1 /\
         machine_config_prog_addresses mc_conf = asm_state_mem_domain t1 /\
         interference_ok (machine_config_next_interfer mc_conf)
           (target_proj (machine_config_target mc_conf) (asm_state_mem_domain t1)) /\
         code_similar (lab_state_code s1) code2 /\
         all_enc_ok (target_config (machine_config_target mc_conf)) labs
           (TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names mc_conf)))
              (machine_config_ffi_names mc_conf)) 0 code2 /\
         bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t1) (asm_state_mem_domain t1)
           (lab_state_mem_domain s1) /\
         share_mem_domain_code_rel mc_conf p code2 (lab_state_shared_mem_domain s1) /\
         asm_state_pc t1 = word_add p (word (pos_val (lab_state_pc s1) 0 code2)) /\
         (match asm_config_link_reg (target_config (machine_config_target mc_conf)) with
            NONE -> T
          | SOME r -> asm_state_lr t1 = r) /\
         (asm_state_be t1 <=>
          asm_config_big_endian (target_config (machine_config_target mc_conf))) /\
         asm_state_align t1 =
           asm_config_code_alignment (target_config (machine_config_target mc_conf)) /\
         ~asm_state_failed t1 /\
         enc_ok (target_config (machine_config_target mc_conf))`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* the clock arithmetic of a simulated step that takes l > 0 target steps *)
let LTTP3AUX_step_clock = prove
 (`!c l. ~(c = 0) /\ ~(l = 0) ==> !k. (c - 1 + k) + l = c + (k + l - 1)`,
  ARITH_TAC);;

(* the last step of a simulated step: combine the target runs *)
let LTTP3AUX_STEP_CLOCK_TAC (c:term) (l:term) =
  let nz t = ASSUME(mk_neg(mk_eq(t,`0`))) in
  REWRITE_TAC[MATCH_MP LTTP3AUX_step_clock (CONJ (nz c) (nz l))] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];;


(* state_rel after a jump of the labSem pc to x and of the target pc to    *)
(* the position of x (the target registers and memory unchanged)            *)
let LTTP3AUX_state_rel_upd_pc = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 ms2 x.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf)
       (asm_upd_pc (word_add p (word (pos_val x 0 code2))) t1) ms2
     ==> lab_to_targetProof_state_rel (mc_conf,code2,labs,p) (lab_upd_pc x (lab_dec_clock s1))
           (asm_upd_pc (word_add p (word (pos_val x 0 code2))) t1) ms2`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def; lab_upd_pc_def; lab_dec_clock_def;
              asm_upd_pc_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) ASSUME_TAC) THEN
  REWRITE_TAC LTTP3AUX_RECS THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `share_mem_state_rel (mc_conf:(A,B,C)machine_config)
    (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) (ms1:B)` THEN
  REWRITE_TAC(share_mem_state_rel_def :: LTTP3AUX_RECS));;

(* the code positions are aligned target addresses *)
let LTTP3AUX_state_rel_aligned_pos_val = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 x.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     encoder_correct (machine_config_target mc_conf)
     ==> alignment_aligned
           (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
           (word_add p (word (pos_val x 0 code2)))`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[aligned_add_sub_cor]
   `!k (a:A word) b. alignment_aligned k a /\ alignment_aligned k b
                     ==> alignment_aligned k (word_add a b)`) THEN CONJ_TAC THENL
   [REWRITE_TAC[aligned_bitwise_and] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try fst(dest_const(rator(lhs(concl th)))) = "asm_state_align" with _ -> false)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC all_enc_ok_aligned_pos_val THEN
    MAP_EVERY EXISTS_TAC [`labs:(num spt)spt`;
      `TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
         (machine_config_ffi_names mc_conf)`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC has_odd_inst_alignment THEN
    ASM_MESON_TAC[]]);;

(* a code location in a register: its target value *)
let LTTP3AUX_state_rel_Loc = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 r n1 n2 x.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     lab_state_regs s1 r = wl_Loc n1 n2 /\
     loc_to_pc n1 n2 (lab_state_code s1) = SOME x
     ==> asm_state_regs t1 r = word_add p (word (pos_val x 0 code2))`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "word_loc_val" with _ -> false))
        (concl th))) THEN
  RES_TAC THEN ASM_REWRITE_TAC[word_loc_val_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  MESON_TAC[]);;

(* an encoding padded with nops is at least as long as the encoding *)
let LTTP3AUX_enc_with_nop_LENGTH = prove
 (`!(enc:(A)asm->byte list) i bytes.
     enc_with_nop enc i bytes ==> LENGTH (enc i) <= LENGTH bytes`,
  REWRITE_TAC[enc_with_nop_thm] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);;

(* the line of the target code at the labSem pc, and the ffi entry points *)
(* are not among its bytes                                                   *)
let LTTP3AUX_fetch_disjoint = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 line.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME line /\
     (!op re a l n. ~(line = Asm (ShareMem op re a) l n))
     ==> ?j. asm_fetch_aux (lab_state_pc s1) code2 = SOME j /\ line_similar line j /\
             line_ok (target_config (machine_config_target mc_conf)) labs
               (TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names mc_conf)))
                  (machine_config_ffi_names mc_conf))
               (pos_val (lab_state_pc s1) 0 code2) j /\
             ffi_entry_pcs_disjoint mc_conf t1 (LENGTH (line_bytes j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(MP_TAC o SPEC `lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)` o
              MATCH_MP code_similar_IMP_asm_fetch_aux_line_similar) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[asm_fetch_def]) THEN ASM_REWRITE_TAC[OPTREL_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `j:(A)line` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC all_enc_ok_asm_fetch_aux_IMP_line_ok THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[share_mem_domain_code_rel_def] o
                check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
  DISCH_THEN(MP_TAC o SPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`;
                             `j:(A)line`]) THEN
  ASM_REWRITE_TAC[ffi_entry_pcs_disjoint_def] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `line_similar (line:(A)line) (Asm (ShareMem op re a) inst len)` THEN
    CASES_ON `line:(A)line` THEN REWRITE_TAC[line_similar_def] THEN ASM_MESON_TAC[];
    REWRITE_TAC[WORD_ADD_AC]]);;

(* the end of the simulation of a labSem jump to x: the target ran l > 0   *)
(* steps to the position of x                                                *)
let LTTP3AUX_finish_jump = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) x res (mc_conf:(A,B,C)machine_config) s2 code2
     labs (t1:(A)asm_state) ms1 p l ms2.
     (!res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
        oracle_tie mc_conf ms1 (lab_upd_pc x (lab_dec_clock s1)) /\
        lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2) /\
        ~(res = target_Error) /\
        encoder_correct (machine_config_target mc_conf) /\
        lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
          (lab_upd_pc x (lab_dec_clock s1)) t1 ms1
        ==> ?k ms2.
              target_evaluate mc_conf
                (lab_state_ffi (lab_upd_pc x (lab_dec_clock s1)))
                (lab_state_clock (lab_upd_pc x (lab_dec_clock s1)) + k) ms1 =
              (res,ms2,lab_state_ffi s2)) /\
     ~(lab_state_clock s1 = 0) /\ ~(l = 0) /\
     oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2) /\
     (!k. target_evaluate mc_conf (lab_state_ffi s1) (k + l) ms1 =
          target_evaluate (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2 /\
          find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2) /\
     target_state_rel (machine_config_target mc_conf)
       (asm_upd_pc (word_add p (word (pos_val x 0 code2))) t1) ms2
     ==> ?k ms2.
           target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
           (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`res:machine_result`;
    `shift_interfer l (mc_conf:(A,B,C)machine_config)`;
    `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
    `asm_upd_pc (word_add p (word (pos_val x 0 (code2:((A)sec)list)))) (t1:(A)asm_state)`;
    `ms2:B`; `p:A word`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC oracle_tie_step THEN
      MAP_EVERY EXISTS_TAC [`ms1:B`; `s1:(A,lab_to_target_config,FFI)lab_state`] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC(lab_upd_pc_def :: lab_dec_clock_def :: LTTP3AUX_RECS);
      ASM_REWRITE_TAC[shift_interfer_def; machine_config_INFO.ri_accfupds];
      MATCH_MP_TAC state_rel_shift_interfer THEN MATCH_MP_TAC LTTP3AUX_state_rel_upd_pc THEN
      EXISTS_TAC `ms1:B` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC(lab_upd_pc_def :: lab_dec_clock_def :: LTTP3AUX_RECS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `ms3:B`)) THEN
  MAP_EVERY EXISTS_TAC [`k + l - 1`; `ms3:B`] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o
    SPEC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) - 1 + k`) THEN
  LTTP3AUX_STEP_CLOCK_TAC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state)`
    `l:num`);;

(* HOL4 line 7560, Resume compile_correct[Asm]: Asm Inst *)
let LTTP3AUX_cc_Inst = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) i a1 a2.
     asm_fetch s1 = SOME (Asm (Asmi (asm_Inst i)) a1 a2)
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!a1 a2 i.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (Asm (Asmi (asm_Inst i)) a1 a2) /\
          ~lab_state_failed (asm_inst i s1)
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1 (inc_pc (lab_dec_clock (asm_inst i s1))) /\
                lab_evaluate (inc_pc (lab_dec_clock (asm_inst i s1))) = (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (inc_pc (lab_dec_clock (asm_inst i s1))) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi (inc_pc (lab_dec_clock (asm_inst i s1))))
                        (lab_state_clock (inc_pc (lab_dec_clock (asm_inst i s1))) + k) ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\ ~lab_state_failed (asm_inst i s1) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate (inc_pc (lab_dec_clock (asm_inst i s1))) = (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`;
     `TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
        (machine_config_ffi_names mc_conf)`;
     `p:A word`; `t1:(A)asm_state`; `i:(A)inst`; `a1:byte list`; `a2:num`]
    IMP_bytes_in_memory_Inst) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `bytes':byte list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`i:(A)inst`; `s1:(A,lab_to_target_config,FFI)lab_state`;
     `mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `t1:(A)asm_state`; `ms1:B`; `bytes':byte list`]
    lab_to_targetProof_Inst_lemma) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "instlem") THEN
  USE_THEN "instlem" (STRIP_ASSUME_TAC o SPEC `ms1:B`) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `asm_Inst (i:(A)inst)`;
     `asm (asm_Inst (i:(A)inst))
        (word_add (asm_state_pc t1) (word (LENGTH (bytes':byte list)))) t1`;
     `bytes':byte list`] asm_step_IMP_evaluate_step_nop) THEN
  ASM_REWRITE_TAC[asm_step_nop_def; distinctness "asm"] THEN ANTS_TAC THENL
   [SIMP[asm_def; asm_upd_pc_def] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMP_ffi_entry_pcs_disjoint_Asm THEN
      MAP_EVERY EXISTS_TAC [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
        `labs:(num spt)spt`;
        `TAKE (THE (mmio_pcs_min_index
                      (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
           (machine_config_ffi_names mc_conf)`;
        `Asmi (asm_Inst (i:(A)inst))`; `a1:byte list`; `a2:num`; `p:A word`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[asm_fetch_def]) THEN
      ASM_REWRITE_TAC[distinctness "asm_or_cbw"] THEN ARITH_TAC;
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] bytes_in_mem_IMP_memory) THEN
      EXISTS_TAC `lab_state_mem_domain (s1:(A,lab_to_target_config,FFI)lab_state)` THEN
      EXISTS_TAC `asm_state_mem (t1:(A)asm_state)` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` (LABEL_TAC "step"))) THEN
  USE_THEN "step" (STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `0`) THEN
  REMOVE_THEN "IH" (MP_TAC o SPECL [`a1:byte list`; `a2:num`; `i:(A)inst`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:machine_result`;
    `shift_interfer l (mc_conf:(A,B,C)machine_config)`;
    `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
    `asm (asm_Inst (i:(A)inst))
       (word_add (word_add p (word (pos_val
          (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list))))
        (word (LENGTH (bytes':byte list)))) t1`;
    `ms2:B`; `p:A word`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC oracle_tie_step THEN
      MAP_EVERY EXISTS_TAC [`ms1:B`; `s1:(A,lab_to_target_config,FFI)lab_state`] THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC(inc_pc_def :: lab_dec_clock_def :: asm_inst_consts :: LTTP3AUX_RECS);
      ASM_REWRITE_TAC[shift_interfer_def; machine_config_INFO.ri_accfupds];
      MATCH_MP_TAC state_rel_shift_interfer THEN
      USE_THEN "instlem" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `ms2:B`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[asm_def]) THEN REWRITE_TAC[asm_def] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SIMP_TAC(inc_pc_def :: lab_dec_clock_def :: asm_inst_consts :: LTTP3AUX_RECS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `ms3:B`)) THEN
  MAP_EVERY EXISTS_TAC [`k + l - 1`; `ms3:B`] THEN
  USE_THEN "step" (MP_TAC o CONJUNCT1 o
    SPEC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) - 1 + k`) THEN
  LTTP3AUX_STEP_CLOCK_TAC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state)`
    `l:num`);;

(* HOL4 line 7611, Resume compile_correct[Asm]: Asm JumpReg *)
let LTTP3AUX_cc_JumpReg = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) r a1 a2.
     asm_fetch s1 = SOME (Asm (Asmi (JumpReg r)) a1 a2)
     ==> !n1 n2. lab_state_regs s1 r = wl_Loc n1 n2
     ==> !x. loc_to_pc n1 n2 (lab_state_code s1) = SOME x
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!a1 a2 r n1 n2 x.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (Asm (Asmi (JumpReg r)) a1 a2) /\
          lab_state_regs s1 r = wl_Loc n1 n2 /\
          loc_to_pc n1 n2 (lab_state_code s1) = SOME x
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1 (lab_upd_pc x (lab_dec_clock s1)) /\
                lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (lab_upd_pc x (lab_dec_clock s1)) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi (lab_upd_pc x (lab_dec_clock s1)))
                        (lab_state_clock (lab_upd_pc x (lab_dec_clock s1)) + k) ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `enc = asm_config_encode (target_config (machine_config_target
                      (mc_conf:(A,B,C)machine_config))) (JumpReg r)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `r:num`; `a1:byte list`; `a2:num`]
    IMP_bytes_in_memory_JumpReg) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `r:num`; `n1:num`; `n2:num`; `x:num`] LTTP3AUX_state_rel_Loc) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `x:num`] LTTP3AUX_state_rel_aligned_pos_val) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `asm (JumpReg r) (word_add (word_add p (word pv)) (word (LENGTH (enc:byte list))))
                  t1 =
                asm_upd_pc (word_add p (word (pos_val x 0 (code2:((A)sec)list))))
                  (t1:(A)asm_state)` (LABEL_TAC "asmeq") THENL
   [ASM_REWRITE_TAC[asm_def; read_reg_def; LET_DEF; LET_END_DEF; asm_assert_def] THEN
    AP_TERM_TAC THEN REWRITE_TAC(asm_state_component_equality :: LTTP3AUX_RECS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the run of the target over the encoded JumpReg *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `JumpReg r:(A)asm`]
    asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
        `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
        `Asm (Asmi (JumpReg r)) a1 a2:(A)line`] LTTP3AUX_fetch_disjoint) THEN
      ASM_REWRITE_TAC[distinctness "line"; injectivity "line"; distinctness "asm_or_cbw"] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC ffi_entry_pcs_disjoint_LENGTH_shorter THEN
      EXISTS_TAC `LENGTH (line_bytes (j:(A)line))` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `line_similar (Asm (Asmi (JumpReg r)) a1 a2) (j:(A)line)` THEN
      UNDISCH_TAC `line_ok (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
        labs ffis pv (j:(A)line)` THEN
      CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_ok_def; line_bytes_def] THEN
      STRIP_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN EXPAND_TAC "enc" THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_enc_with_nop_LENGTH) THEN
      REWRITE_TAC[cbw_to_asm_def] THEN CASE_REWRITE_TAC[];
      USE_THEN "asmeq" SUBST1_TAC THEN
      REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC LTTP3AUX_finish_jump THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `code2:((A)sec)list`; `labs:(num spt)spt`; `t1:(A)asm_state`;
                        `p:A word`; `l:num`; `ms2:B`] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "IH" (MATCH_MP_TAC o SPECL [`a1:byte list`; `a2:num`; `r:num`; `n1:num`;
                                             `n2:num`; `x:num`]) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;
(* the labSem pc of a label and the label table *)
let LTTP3AUX_state_rel_lab_lookup = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 l1 l2 x.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     loc_to_pc l1 l2 (lab_state_code s1) = SOME x
     ==> lab_lookup l1 l2 labs = SOME (pos_val x 0 code2) /\
         find_pos (lab_Lab l1 l2) labs = pos_val x 0 code2`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lab_lookup_IMP THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 7967, Resume compile_correct[Jump] *)
let LTTP3AUX_cc_Jump = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) jt a1 a2 a3.
     asm_fetch s1 = SOME (LabAsm (lab_Jump jt) a1 a2 a3)
     ==> !x. get_pc_value jt s1 = SOME x
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!a1 a2 a3 jt x.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (LabAsm (lab_Jump jt) a1 a2 a3) /\
          get_pc_value jt s1 = SOME x
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1 (lab_upd_pc x (lab_dec_clock s1)) /\
                lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (lab_upd_pc x (lab_dec_clock s1)) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi (lab_upd_pc x (lab_dec_clock s1)))
                        (lab_state_clock (lab_upd_pc x (lab_dec_clock s1)) + k) ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  MP_TAC(ISPEC `jt:lab` (nchotomy_of_type `:lab`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `get_pc_value (lab_Lab l1 l2) (s1:(A,lab_to_target_config,FFI)lab_state) = SOME x` THEN
  REWRITE_TAC[get_pc_value_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `l1:num`; `l2:num`; `x:num`] LTTP3AUX_state_rel_lab_lookup) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `lab_Lab l1 l2`; `a1:A word`; `a2:byte list`; `a3:num`]
    IMP_bytes_in_memory_Jump) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `enc:byte list`
                                               with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `tt:A word`
                                               with Failure _ -> false)) THEN
  SUBGOAL_THEN `asm (asm_Jump (word_sub (word (pos_val x 0 (code2:((A)sec)list))) (word pv)))
                  (word_add (word_add p (word pv))
                     (word (LENGTH (asm_config_encode
                        (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                        (asm_Jump (word_sub (word (pos_val x 0 code2)) (word pv)))))))
                  t1 =
                asm_upd_pc (word_add p (word (pos_val x 0 (code2:((A)sec)list))))
                  (t1:(A)asm_state)` (LABEL_TAC "asmeq") THENL
   [ASM_REWRITE_TAC[asm_def; jump_to_offset_def] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC(WORD_RULE
     `!(a:A word) b c. word_add (word_add a b) (word_sub c b) = word_add a c`);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
     `asm_Jump (word_sub (word (pos_val x 0 (code2:((A)sec)list))) (word pv)):(A)asm`]
    asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
        `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
        `LabAsm (lab_Jump (lab_Lab l1 l2)) a1 a2 a3:(A)line`] LTTP3AUX_fetch_disjoint) THEN
      ASM_REWRITE_TAC[distinctness "line"] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC ffi_entry_pcs_disjoint_LENGTH_shorter THEN
      EXISTS_TAC `LENGTH (line_bytes (j:(A)line))` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `line_similar (LabAsm (lab_Jump (lab_Lab l1 l2)) a1 a2 a3) (j:(A)line)` THEN
      UNDISCH_TAC `line_ok (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
        labs ffis pv (j:(A)line)` THEN
      CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
      DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "line_ok")) THEN
      REWRITE_TAC[line_ok_def; get_label_def] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[lab_inst_def] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_enc_with_nop_LENGTH) THEN ASM_REWRITE_TAC[];
      USE_THEN "asmeq" SUBST1_TAC THEN
      REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC LTTP3AUX_finish_jump THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `code2:((A)sec)list`; `labs:(num spt)spt`; `t1:(A)asm_state`;
                        `p:A word`; `l:num`; `ms2:B`] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "IH" (MATCH_MP_TAC o SPECL [`a1:A word`; `a2:byte list`; `a3:num`;
                                             `lab_Lab l1 l2`; `x:num`]) THEN
    ASM_REWRITE_TAC[get_pc_value_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;
(* HOL4 line 8052, Resume compile_correct[JumpCmp]: the comparison holds *)
let LTTP3AUX_cc_JumpCmp_T = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) cmp rr ri jt a1 a2 a3.
     asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jt) a1 a2 a3)
     ==> !v1. wl_word_cmp cmp (lab_state_regs s1 rr) (lab_reg_imm ri s1) = SOME v1
     ==> v1
     ==> !x. get_pc_value jt s1 = SOME x
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!a1 a2 a3 cmp rr ri v1 jt x.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jt) a1 a2 a3) /\
          wl_word_cmp cmp (lab_state_regs s1 rr) (lab_reg_imm ri s1) = SOME v1 /\
          v1 /\
          get_pc_value jt s1 = SOME x
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1 (lab_upd_pc x (lab_dec_clock s1)) /\
                lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (lab_upd_pc x (lab_dec_clock s1)) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi (lab_upd_pc x (lab_dec_clock s1)))
                        (lab_state_clock (lab_upd_pc x (lab_dec_clock s1)) + k) ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `cmp:cmp`; `rr:num`; `ri:(A)reg_imm`; `v1:bool`] word_cmp_lemma) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  MP_TAC(ISPEC `jt:lab` (nchotomy_of_type `:lab`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `get_pc_value (lab_Lab l1 l2) (s1:(A,lab_to_target_config,FFI)lab_state) = SOME x` THEN
  REWRITE_TAC[get_pc_value_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `l1:num`; `l2:num`; `x:num`] LTTP3AUX_state_rel_lab_lookup) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `cmp:cmp`; `rr:num`; `ri:(A)reg_imm`; `lab_Lab l1 l2`;
     `a1:A word`; `a2:byte list`; `a3:num`]
    IMP_bytes_in_memory_JumpCmp) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `enc:byte list`
                                               with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `tt:A word`
                                               with Failure _ -> false)) THEN
  SUBGOAL_THEN `asm (asm_JumpCmp cmp rr ri (word_sub (word (pos_val x 0 (code2:((A)sec)list))) (word pv)))
                  (word_add (word_add p (word pv))
                     (word (LENGTH (asm_config_encode
                        (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                        (asm_JumpCmp cmp rr ri (word_sub (word (pos_val x 0 code2)) (word pv)))))))
                  t1 =
                asm_upd_pc (word_add p (word (pos_val x 0 (code2:((A)sec)list))))
                  (t1:(A)asm_state)` (LABEL_TAC "asmeq") THENL
   [ASM_REWRITE_TAC[asm_def; jump_to_offset_def] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC(WORD_RULE
     `!(a:A word) b c. word_add (word_add a b) (word_sub c b) = word_add a c`);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
     `asm_JumpCmp cmp rr ri (word_sub (word (pos_val x 0 (code2:((A)sec)list))) (word pv)):(A)asm`]
    asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
        `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
        `LabAsm (lab_JumpCmp cmp rr ri (lab_Lab l1 l2)) a1 a2 a3:(A)line`] LTTP3AUX_fetch_disjoint) THEN
      ASM_REWRITE_TAC[distinctness "line"] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC ffi_entry_pcs_disjoint_LENGTH_shorter THEN
      EXISTS_TAC `LENGTH (line_bytes (j:(A)line))` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `line_similar (LabAsm (lab_JumpCmp cmp rr ri (lab_Lab l1 l2)) a1 a2 a3) (j:(A)line)` THEN
      UNDISCH_TAC `line_ok (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
        labs ffis pv (j:(A)line)` THEN
      CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
      DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "line_ok")) THEN
      REWRITE_TAC[line_ok_def; get_label_def] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[lab_inst_def] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_enc_with_nop_LENGTH) THEN ASM_REWRITE_TAC[];
      USE_THEN "asmeq" SUBST1_TAC THEN
      REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC LTTP3AUX_finish_jump THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `code2:((A)sec)list`; `labs:(num spt)spt`; `t1:(A)asm_state`;
                        `p:A word`; `l:num`; `ms2:B`] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "IH" (MATCH_MP_TAC o SPECL [`a1:A word`; `a2:byte list`; `a3:num`;
       `cmp:cmp`; `rr:num`; `ri:(A)reg_imm`; `v1:bool`; `lab_Lab l1 l2`; `x:num`]) THEN
    ASM_REWRITE_TAC[get_pc_value_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;
(* inc_pc as an update of the pc *)
let LTTP3AUX_inc_pc_dec_clock = prove
 (`!(s:(A,C,FFI)lab_state).
     inc_pc (lab_dec_clock s) = lab_upd_pc (lab_state_pc s + 1) (lab_dec_clock s)`,
  REWRITE_TAC(inc_pc_def :: lab_upd_pc_def :: lab_dec_clock_def :: LTTP3AUX_RECS));;

(* HOL4 line 8052, Resume compile_correct[JumpCmp]: the comparison fails *)
let LTTP3AUX_cc_JumpCmp_F = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) cmp rr ri jt a1 a2 a3.
     asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jt) a1 a2 a3)
     ==> !v1. wl_word_cmp cmp (lab_state_regs s1 rr) (lab_reg_imm ri s1) = SOME v1
     ==> ~v1
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!jt a1 a2 a3 cmp rr ri v1.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jt) a1 a2 a3) /\
          wl_word_cmp cmp (lab_state_regs s1 rr) (lab_reg_imm ri s1) = SOME v1 /\
          ~v1
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1 (inc_pc (lab_dec_clock s1)) /\
                lab_evaluate (inc_pc (lab_dec_clock s1)) = (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (inc_pc (lab_dec_clock s1)) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi (inc_pc (lab_dec_clock s1)))
                        (lab_state_clock (inc_pc (lab_dec_clock s1)) + k) ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate (inc_pc (lab_dec_clock s1)) = (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `cmp:cmp`; `rr:num`; `ri:(A)reg_imm`; `v1:bool`] word_cmp_lemma) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `cmp:cmp`; `rr:num`; `ri:(A)reg_imm`; `jt:lab`;
     `a1:A word`; `a2:byte list`; `a3:num`] IMP_bytes_in_memory_JumpCmp_1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `asm (asm_JumpCmp cmp rr ri tt)
                  (word_add (asm_state_pc t1) (word (LENGTH (bytes:byte list)))) t1 =
                asm_upd_pc (word_add p (word (pos_val
                  (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1) 0
                  (code2:((A)sec)list)))) (t1:(A)asm_state)` (LABEL_TAC "asmeq") THENL
   [ASM_REWRITE_TAC[asm_def; GSYM read_reg_def] THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
     `asm_JumpCmp cmp rr ri tt:(A)asm`;
     `asm (asm_JumpCmp cmp rr ri tt) (word_add (asm_state_pc t1) (word (LENGTH (bytes:byte list))))
        (t1:(A)asm_state)`; `bytes:byte list`] asm_step_IMP_evaluate_step_nop) THEN
  USE_THEN "asmeq" SUBST1_TAC THEN
  ASM_REWRITE_TAC[asm_step_nop_def; distinctness "asm"] THEN ANTS_TAC THENL
   [REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
      `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
      `LabAsm (lab_JumpCmp cmp rr ri jt) a1 a2 a3:(A)line`] LTTP3AUX_fetch_disjoint) THEN
    ASM_REWRITE_TAC[distinctness "line"] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `LENGTH (line_bytes (j:(A)line)) = LENGTH (bytes:byte list)`
      (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC asm_fetch_aux_pos_val_LENGTH_EQ THEN
    MAP_EVERY EXISTS_TAC [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `0`;
      `code2:((A)sec)list`;
      `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
      `labs:(num spt)spt`; `ffis:ffiname list`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LTTP3AUX_inc_pc_dec_clock]) THEN
  REWRITE_TAC[LTTP3AUX_inc_pc_dec_clock] THEN
  MATCH_MP_TAC LTTP3AUX_finish_jump THEN
  MAP_EVERY EXISTS_TAC [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1`;
    `code2:((A)sec)list`; `labs:(num spt)spt`; `t1:(A)asm_state`; `p:A word`; `l:num`;
    `ms2:B`] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "IH" (MATCH_MP_TAC o SPECL [`jt:lab`; `a1:A word`; `a2:byte list`; `a3:num`;
       `cmp:cmp`; `rr:num`; `ri:(A)reg_imm`; `v1:bool`]) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;
(* state_rel after setting register r (labSem value v, target value w) and *)
(* moving the pcs to x                                                       *)
let LTTP3AUX_state_rel_upd_reg_pc = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 ms2 x r v w.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     word_loc_val p labs v = SOME w /\
     target_state_rel (machine_config_target mc_conf)
       (asm_upd_pc (word_add p (word (pos_val x 0 code2))) (asm_upd_reg r w t1)) ms2
     ==> lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
           (lab_upd_pc x (lab_dec_clock (lab_upd_reg r v s1)))
           (asm_upd_pc (word_add p (word (pos_val x 0 code2))) (asm_upd_reg r w t1)) ms2`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def; lab_upd_pc_def; lab_dec_clock_def;
              asm_upd_pc_def; lab_upd_reg_def; asm_upd_reg_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
    (CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC LTTP3AUX_RECS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `share_mem_state_rel (mc_conf:(A,B,C)machine_config)
      (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) (ms1:B)` THEN
    REWRITE_TAC(share_mem_state_rel_def :: LTTP3AUX_RECS)]);;
(* the same with an update of register r (labSem value v, target value w) *)
let LTTP3AUX_finish_upd_reg = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) x res (mc_conf:(A,B,C)machine_config) s2 code2
     labs (t1:(A)asm_state) ms1 p l ms2 r v w.
     (!res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
        oracle_tie mc_conf ms1 (lab_upd_pc x (lab_dec_clock (lab_upd_reg r v s1))) /\
        lab_evaluate (lab_upd_pc x (lab_dec_clock (lab_upd_reg r v s1))) = (res,s2) /\
        ~(res = target_Error) /\
        encoder_correct (machine_config_target mc_conf) /\
        lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
          (lab_upd_pc x (lab_dec_clock (lab_upd_reg r v s1))) t1 ms1
        ==> ?k ms2.
              target_evaluate mc_conf
                (lab_state_ffi (lab_upd_pc x (lab_dec_clock (lab_upd_reg r v s1))))
                (lab_state_clock (lab_upd_pc x (lab_dec_clock (lab_upd_reg r v s1))) + k) ms1 =
              (res,ms2,lab_state_ffi s2)) /\
     ~(lab_state_clock s1 = 0) /\ ~(l = 0) /\
     oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     lab_evaluate (lab_upd_pc x (lab_dec_clock (lab_upd_reg r v s1))) = (res,s2) /\
     (!k. target_evaluate mc_conf (lab_state_ffi s1) (k + l) ms1 =
          target_evaluate (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2 /\
          find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2) /\
     word_loc_val p labs v = SOME w /\
     target_state_rel (machine_config_target mc_conf)
       (asm_upd_pc (word_add p (word (pos_val x 0 code2))) (asm_upd_reg r w t1)) ms2
     ==> ?k ms2.
           target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
           (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`res:machine_result`;
    `shift_interfer l (mc_conf:(A,B,C)machine_config)`;
    `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
    `asm_upd_pc (word_add p (word (pos_val x 0 (code2:((A)sec)list))))
       (asm_upd_reg r (w:A word) (t1:(A)asm_state))`;
    `ms2:B`; `p:A word`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC oracle_tie_step THEN
      MAP_EVERY EXISTS_TAC [`ms1:B`; `s1:(A,lab_to_target_config,FFI)lab_state`] THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC(lab_upd_pc_def :: lab_dec_clock_def :: lab_upd_reg_def :: LTTP3AUX_RECS);
      ASM_REWRITE_TAC[shift_interfer_def; machine_config_INFO.ri_accfupds];
      MATCH_MP_TAC state_rel_shift_interfer THEN MATCH_MP_TAC LTTP3AUX_state_rel_upd_reg_pc THEN
      EXISTS_TAC `ms1:B` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC(lab_upd_pc_def :: lab_dec_clock_def :: lab_upd_reg_def :: LTTP3AUX_RECS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `ms3:B`)) THEN
  MAP_EVERY EXISTS_TAC [`k + l - 1`; `ms3:B`] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o
    SPEC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) - 1 + k`) THEN
  LTTP3AUX_STEP_CLOCK_TAC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state)`
    `l:num`);;
let LTTP3AUX_pc_upd_reg = prove
 (`!r v (s:(A,C,FFI)lab_state). lab_state_pc (lab_upd_reg r v s) = lab_state_pc s`,
  REWRITE_TAC(lab_upd_reg_def :: LTTP3AUX_RECS));;

(* HOL4 line 8214, Resume compile_correct[LocValue] *)
let LTTP3AUX_cc_LocValue = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) r lab a1 a2 a3.
     asm_fetch s1 = SOME (LabAsm (lab_LocValue r lab) a1 a2 a3)
     ==> ~(get_pc_value lab s1 = NONE)
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!a1 a2 a3 r lab.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (LabAsm (lab_LocValue r lab) a1 a2 a3) /\
          ~(get_pc_value lab s1 = NONE)
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1 (inc_pc (lab_dec_clock (lab_upd_reg r (lab_to_loc lab) s1))) /\
                lab_evaluate (inc_pc (lab_dec_clock (lab_upd_reg r (lab_to_loc lab) s1))) =
                  (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (inc_pc (lab_dec_clock (lab_upd_reg r (lab_to_loc lab) s1))) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi (inc_pc (lab_dec_clock (lab_upd_reg r (lab_to_loc lab) s1))))
                        (lab_state_clock
                           (inc_pc (lab_dec_clock (lab_upd_reg r (lab_to_loc lab) s1))) + k)
                        ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate (inc_pc (lab_dec_clock (lab_upd_reg r (lab_to_loc lab) s1))) = (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  MP_TAC(ISPEC `lab:lab` (nchotomy_of_type `:lab`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `?x. loc_to_pc l1 l2 (lab_state_code (s1:(A,lab_to_target_config,FFI)lab_state)) =
                    SOME x` (X_CHOOSE_TAC `x:num`) THENL
   [UNDISCH_TAC `~(get_pc_value (lab_Lab l1 l2)
                    (s1:(A,lab_to_target_config,FFI)lab_state) = NONE)` THEN
    REWRITE_TAC[get_pc_value_def] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[option_CASES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `l1:num`; `l2:num`; `x:num`] LTTP3AUX_state_rel_lab_lookup) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `r:num`; `l1:num`; `l2:num`;
     `a1:A word`; `a2:byte list`; `a3:num`] IMP_bytes_in_memory_LocValue) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `tt:A word`
                                               with Failure _ -> false)) THEN
  ABBREV_TAC `w = word_add p (word (pos_val x 0 (code2:((A)sec)list))):A word` THEN
  SUBGOAL_THEN `asm (asm_Loc r (word_sub (word (pos_val x 0 (code2:((A)sec)list))) (word pv)))
                  (word_add (asm_state_pc t1) (word (LENGTH (bytes:byte list)))) t1 =
                asm_upd_pc (word_add p (word (pos_val
                  (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1) 0
                  (code2:((A)sec)list)))) (asm_upd_reg r w (t1:(A)asm_state))`
    (LABEL_TAC "asmeq") THENL
   [ASM_REWRITE_TAC[asm_def] THEN BINOP_TAC THENL
     [REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC];
      EXPAND_TAC "w" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_ACCEPT_TAC(WORD_RULE
       `!(a:A word) b c. word_add (word_add a b) (word_sub c b) = word_add a c`)];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
     `asm_Loc r (word_sub (word (pos_val x 0 (code2:((A)sec)list))) (word pv)):(A)asm`;
     `asm (asm_Loc r (word_sub (word (pos_val x 0 (code2:((A)sec)list))) (word pv)))
        (word_add (asm_state_pc t1) (word (LENGTH (bytes:byte list))))
        (t1:(A)asm_state)`; `bytes:byte list`] asm_step_IMP_evaluate_step_nop) THEN
  USE_THEN "asmeq" SUBST1_TAC THEN
  ASM_REWRITE_TAC[asm_step_nop_def; distinctness "asm"] THEN ANTS_TAC THENL
   [REWRITE_TAC(asm_upd_pc_def :: asm_upd_reg_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
      `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
      `LabAsm (lab_LocValue r (lab_Lab l1 l2)) a1 a2 a3:(A)line`] LTTP3AUX_fetch_disjoint) THEN
    ASM_REWRITE_TAC[distinctness "line"] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `LENGTH (line_bytes (j:(A)line)) = LENGTH (bytes:byte list)`
      (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC asm_fetch_aux_pos_val_LENGTH_EQ THEN
    MAP_EVERY EXISTS_TAC [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `0`;
      `code2:((A)sec)list`;
      `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
      `labs:(num spt)spt`; `ffis:ffiname list`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LTTP3AUX_inc_pc_dec_clock; LTTP3AUX_pc_upd_reg; lab_to_loc_def]) THEN
  REWRITE_TAC[LTTP3AUX_inc_pc_dec_clock; LTTP3AUX_pc_upd_reg; lab_to_loc_def] THEN
  MATCH_MP_TAC LTTP3AUX_finish_upd_reg THEN
  MAP_EVERY EXISTS_TAC [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1`;
    `code2:((A)sec)list`; `labs:(num spt)spt`; `t1:(A)asm_state`; `p:A word`; `l:num`;
    `ms2:B`; `r:num`; `wl_Loc l1 l2:(A)word_loc`; `w:A word`] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "IH" (MP_TAC o SPECL [`a1:A word`; `a2:byte list`; `a3:num`; `r:num`;
       `lab_Lab l1 l2`]) THEN
    ASM_REWRITE_TAC[get_pc_value_def; option_DISTINCT; LTTP3AUX_inc_pc_dec_clock;
                    LTTP3AUX_pc_upd_reg; lab_to_loc_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[option_DISTINCT];
    ASM_REWRITE_TAC[word_loc_val_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
    ASM_REWRITE_TAC[]]);;
(* more parts of state_rel *)
let LTTP3AUX_state_rel_misc_facts = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> good_dimindex (:A) /\
         ~(machine_config_halt_pc mc_conf IN machine_config_prog_addresses mc_conf) /\
         ~(machine_config_ccache_pc mc_conf IN machine_config_prog_addresses mc_conf) /\
         word_sub p (word ffi_offset) = machine_config_halt_pc mc_conf /\
         word_sub p (word (2 * ffi_offset)) = machine_config_ccache_pc mc_conf /\
         reg_ok (lab_state_ptr_reg s1) (target_config (machine_config_target mc_conf)) /\
         machine_config_ptr_reg mc_conf = lab_state_ptr_reg s1 /\
         reg_ok (lab_state_len_reg s1) (target_config (machine_config_target mc_conf)) /\
         machine_config_len_reg mc_conf = lab_state_len_reg s1 /\
         reg_ok (lab_state_ptr2_reg s1) (target_config (machine_config_target mc_conf)) /\
         machine_config_ptr2_reg mc_conf = lab_state_ptr2_reg s1 /\
         reg_ok (lab_state_len2_reg s1) (target_config (machine_config_target mc_conf)) /\
         machine_config_len2_reg mc_conf = lab_state_len2_reg s1 /\
         reg_ok (lab_state_link_reg s1) (target_config (machine_config_target mc_conf)) /\
         (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
         (!l1 l2 x2.
            loc_to_pc l1 l2 (lab_state_code s1) = SOME x2
            ==> lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2))`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 8199, Resume compile_correct[Call]: there are no Call lines *)
let LTTP3AUX_cc_Call = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) l a1 a2 a3.
     asm_fetch s1 = SOME (LabAsm (lab_Call l) a1 a2 a3)
     ==> !(mc_conf:(A,B,C)machine_config) code2 labs p (t1:(A)asm_state) ms1.
           ~lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  MATCH_MP_TAC IMP_bytes_in_memory_Call THEN
  MAP_EVERY EXISTS_TAC [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
    `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`;
    `TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
       (machine_config_ffi_names mc_conf)`;
    `p:A word`; `t1:(A)asm_state`; `l:lab`; `a1:A word`; `a2:byte list`; `a3:num`] THEN
  ASM_REWRITE_TAC[]);;
(* HOL4 line 9282, Resume compile_correct[Halt] *)
let LTTP3AUX_cc_Halt = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) a1 a2 a3.
     asm_fetch s1 = SOME (LabAsm lab_Halt a1 a2 a3)
     ==> !w. lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       ~(lab_state_clock s1 = 0) /\
       res = (if w = word 0 then target_Halt Success else target_Halt Resource_limit_hit) /\
       s2 = s1 /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `a1:A word`; `a2:byte list`; `a3:num`]
    IMP_bytes_in_memory_Halt) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `enc:byte list`
                                               with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `tt:A word`
                                               with Failure _ -> false)) THEN
  ABBREV_TAC `jj = asm_Jump (word_sub (word 0) (word (pv + ffi_offset))):(A)asm` THEN
  SUBGOAL_THEN `asm jj (word_add (word_add p (word pv))
                   (word (LENGTH (asm_config_encode
                      (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                      jj)))) t1 =
                asm_upd_pc (machine_config_halt_pc mc_conf) (t1:(A)asm_state)`
    (LABEL_TAC "asmeq") THENL
   [EXPAND_TAC "jj" THEN ASM_REWRITE_TAC[asm_def; jump_to_offset_def] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) =
      `machine_config_halt_pc (mc_conf:(A,B,C)machine_config)` with Failure _ -> false)) THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `jj:(A)asm`]
    asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
        `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
        `LabAsm lab_Halt a1 a2 a3:(A)line`] LTTP3AUX_fetch_disjoint) THEN
      ASM_REWRITE_TAC[distinctness "line"] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC ffi_entry_pcs_disjoint_LENGTH_shorter THEN
      EXISTS_TAC `LENGTH (line_bytes (j:(A)line))` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `line_similar (LabAsm lab_Halt a1 a2 a3) (j:(A)line)` THEN
      UNDISCH_TAC `line_ok (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
        labs ffis pv (j:(A)line)` THEN
      CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
      DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "line_ok")) THEN
      REWRITE_TAC[line_ok_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_enc_with_nop_LENGTH) THEN
      EXPAND_TAC "jj" THEN REWRITE_TAC[];
      USE_THEN "asmeq" SUBST1_TAC THEN
      REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `ms2:B`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state)` o
    check (fun th -> is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) =
      "target_evaluate" with Failure _ -> false)) (concl th))) THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[target_evaluate_def] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[target_state_rel_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "target_state_rel" &&
      can (find_term (fun t -> try fst(dest_const t) = "asm_upd_pc" with Failure _ -> false))
          (concl th) with Failure _ -> false)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(asm_upd_pc_def :: LTTP3AUX_RECS)) THEN
  SUBGOAL_THEN `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms2
                  (lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state)) = w`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state)` o
      check (fun th -> is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) =
        "target_get_reg" with Failure _ -> false)) (concl th))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[reg_ok_def]) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state)` o
      check (fun th -> is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) =
        "word_loc_val" with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[word_loc_val_def; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(machine_config_halt_pc (mc_conf:(A,B,C)machine_config) IN
                 machine_config_prog_addresses mc_conf)` THEN
  ASM_REWRITE_TAC(shift_interfer_def :: IN_DIFF :: LTTP3AUX_RECS) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;
(* the cases of one step of labSem's evaluate that do not end in Error *)
let LTTP3AUX_lab_evaluate_cases = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) res s2.
     lab_evaluate s1 = (res,s2) /\ ~(res = target_Error)
     ==> (lab_state_clock s1 = 0 /\ res = target_TimeOut /\ s2 = s1) \/
         (?i a1 a2.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (Asm (Asmi (asm_Inst i)) a1 a2) /\
            ~lab_state_failed (asm_inst i s1) /\
            lab_evaluate (inc_pc (lab_dec_clock (asm_inst i s1))) = (res,s2)) \/
         (?r a1 a2 n1 n2 x.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (Asm (Asmi (JumpReg r)) a1 a2) /\
            lab_state_regs s1 r = wl_Loc n1 n2 /\
            loc_to_pc n1 n2 (lab_state_code s1) = SOME x /\
            lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2)) \/
         (?r1 r2 a1 a2 w1 w2 cb.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (Asm (Cbw r1 r2) a1 a2) /\
            lab_state_regs s1 r1 = wl_Word w1 /\
            lab_state_regs s1 r2 = wl_Word w2 /\
            buffer_write (lab_state_code_buffer s1) w1 (word_zx w2) = SOME cb /\
            lab_evaluate (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K cb) s1))) =
              (res,s2)) \/
         (?m r ad a1 a2 new_ffi new_bytes s'.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (Asm (ShareMem m r ad) a1 a2) /\
            share_mem_op m r ad s1 = SOME (FFI_return new_ffi new_bytes,s') /\
            lab_evaluate
              (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
                 (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s'))) s')) =
              (res,s2)) \/
         (?m r ad a1 a2 outcome.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (Asm (ShareMem m r ad) a1 a2) /\
            share_mem_op m r ad s1 = SOME (FFI_final outcome,s2) /\
            res = target_Halt (FFI_outcome outcome)) \/
         (?jt a1 a2 a3 x.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm (lab_Jump jt) a1 a2 a3) /\
            get_pc_value jt s1 = SOME x /\
            lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2)) \/
         (?cmp rr ri jt a1 a2 a3 v1 x.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jt) a1 a2 a3) /\
            wl_word_cmp cmp (lab_state_regs s1 rr) (lab_reg_imm ri s1) = SOME v1 /\ v1 /\
            get_pc_value jt s1 = SOME x /\
            lab_evaluate (lab_upd_pc x (lab_dec_clock s1)) = (res,s2)) \/
         (?cmp rr ri jt a1 a2 a3 v1.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm (lab_JumpCmp cmp rr ri jt) a1 a2 a3) /\
            wl_word_cmp cmp (lab_state_regs s1 rr) (lab_reg_imm ri s1) = SOME v1 /\ ~v1 /\
            lab_evaluate (inc_pc (lab_dec_clock s1)) = (res,s2)) \/
         (?l a1 a2 a3. asm_fetch s1 = SOME (LabAsm (lab_Call l) a1 a2 a3)) \/
         (?r lab a1 a2 a3.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm (lab_LocValue r lab) a1 a2 a3) /\
            ~(get_pc_value lab s1 = NONE) /\
            lab_evaluate (inc_pc (lab_dec_clock (lab_upd_reg r (lab_to_loc lab) s1))) =
              (res,s2)) \/
         (?a1 a2 a3 w.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm lab_Halt a1 a2 a3) /\
            lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w /\
            res = (if w = word 0 then target_Halt Success else target_Halt Resource_limit_hit) /\
            s2 = s1) \/
         (?ffi_index a1 a2 a3 w w2 w3 w4 n1 n2 bytes bytes2 new_pc new_ffi new_bytes.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm (CallFFI ffi_index) a1 a2 a3) /\
            lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w /\
            lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w2 /\
            lab_state_regs s1 (lab_state_len2_reg s1) = wl_Word w3 /\
            lab_state_regs s1 (lab_state_ptr2_reg s1) = wl_Word w4 /\
            lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
            read_bytearray w2 (val w)
              (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1)
                 (lab_state_be s1)) = SOME bytes /\
            read_bytearray w4 (val w3)
              (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1)
                 (lab_state_be s1)) = SOME bytes2 /\
            loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
            call_FFI (lab_state_ffi s1) (ExtCall ffi_index) bytes bytes2 =
              FFI_return new_ffi new_bytes /\
            lab_evaluate
              (lab_state_mem_fupd
                 (K (write_bytearray w4 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
                       (lab_state_be s1)))
              (lab_state_ffi_fupd (K new_ffi)
              (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s1)))
              (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s1)))
              (lab_state_regs_fupd
                 (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                           (lab_state_regs s1 a) wl_Word))
              (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n))
              (lab_state_pc_fupd (K new_pc)
              (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))))))) =
              (res,s2)) \/
         (?ffi_index a1 a2 a3 w w2 w3 w4 n1 n2 bytes bytes2 new_pc outcome.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm (CallFFI ffi_index) a1 a2 a3) /\
            lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w /\
            lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w2 /\
            lab_state_regs s1 (lab_state_len2_reg s1) = wl_Word w3 /\
            lab_state_regs s1 (lab_state_ptr2_reg s1) = wl_Word w4 /\
            lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
            read_bytearray w2 (val w)
              (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1)
                 (lab_state_be s1)) = SOME bytes /\
            read_bytearray w4 (val w3)
              (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1)
                 (lab_state_be s1)) = SOME bytes2 /\
            loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
            call_FFI (lab_state_ffi s1) (ExtCall ffi_index) bytes bytes2 = FFI_final outcome /\
            res = target_Halt (FFI_outcome outcome) /\ s2 = s1) \/
         (?a1 a2 a3 w1 w2 n1 n2 cfg bytes new_pc cb k lines rest.
            ~(lab_state_clock s1 = 0) /\
            asm_fetch s1 = SOME (LabAsm lab_Install a1 a2 a3) /\
            lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w1 /\
            lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w2 /\
            lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
            buffer_flush (lab_state_code_buffer s1) w1 w2 = SOME (bytes,cb) /\
            loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
            lab_state_compile_oracle s1 0 = (cfg,CONS (Section k lines) rest) /\
            lab_state_compile s1 cfg (CONS (Section k lines) rest) =
              SOME (bytes,FST (shift_seq 1 (lab_state_compile_oracle s1) 0)) /\
            lab_evaluate
              (lab_state_pc_fupd (K new_pc)
              (lab_state_code_buffer_fupd (K cb)
              (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
              (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
              (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
              (lab_state_regs_fupd
                 (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                       (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
              (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
              (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
              (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) =
              (res,s2))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lab_evaluate_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
  ASM_REWRITE_TAC[] THEN
  TRY (ASM_MESON_TAC[]));;
(* distinct small offsets give distinct addresses *)
let LTTP3AUX_word_add_neq = prove
 (`!(p:A word) m n.
     m < dimword(:A) /\ n < dimword(:A) /\ ~(m = n)
     ==> ~(word_add p (word m) = word_add p (word n))`,
  REWRITE_TAC[WORD_EQ_ADD_LCANCEL; n2w_11] THEN SIMP_TAC[MOD_LT]);;

(* buffer_write on the code buffer (bytes) *)
let LTTP3AUX_buffer_write_byte = prove
 (`!(cb:(A,8)buffer) w b cb'.
     buffer_write cb w b = SOME cb'
     ==> w = word_add (buffer_position cb) (word (LENGTH (buffer_buffer cb))) /\
         0 < buffer_space_left cb /\
         cb' = buffer_buffer_fupd (K (APPEND (buffer_buffer cb) [b]))
                 (buffer_space_left_fupd (K (buffer_space_left cb - 1)) cb)`,
  REWRITE_TAC[buffer_write_def; DIMINDEX_8] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[WORD_MULT_CLAUSES] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;
(* ARITH_TAC with only the arithmetic assumptions (ASM_ARITH_TAC with the   *)
(* big assumption lists of state_rel is slow)                                *)
let LTTP3AUX_ARITH_TAC : tactic = fun (asl,w as g) ->
  let isnum t = try type_of t = `:num` with Failure _ -> false in
  let rec ok t =
    if is_neg t then ok (rand t)
    else if is_eq t then isnum (lhs t)
    else (is_binary "<" t || is_binary "<=" t) && isnum (lhand t) in
  let ths = map snd (filter (fun (_,th) -> ok (concl th)) asl) in
  (MAP_EVERY MP_TAC ths THEN ARITH_TAC) g;;
(* state_rel after a Cbw: the byte b is written at w1, the end of the code  *)
(* buffer, and both pcs move to the next line                               *)
let LTTP3AUX_state_rel_cbw = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 ms2 w1 b cb.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     buffer_write (lab_state_code_buffer s1) w1 b = SOME cb /\
     target_state_rel (machine_config_target mc_conf)
       (asm_upd_pc (word_add p (word (pos_val (lab_state_pc s1 + 1) 0 code2)))
          (asm_state_mem_fupd (K ((w1 =+ b) (asm_state_mem t1))) t1)) ms2
     ==> lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
           (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K cb) s1)))
           (asm_upd_pc (word_add p (word (pos_val (lab_state_pc s1 + 1) 0 code2)))
              (asm_state_mem_fupd (K ((w1 =+ b) (asm_state_mem t1))) t1)) ms2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_buffer_write_byte) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN
  REWRITE_TAC[lab_to_targetProof_state_rel_def; inc_pc_def; lab_dec_clock_def;
              asm_upd_pc_def] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC((record_info "buffer").ri_accfupds :: LTTP3AUX_RECS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add p (word (LENGTH (prog_to_bytes (code2:((A)sec)list)))))
       (word (LENGTH (buffer_buffer (lab_state_code_buffer
          (s1:(A,lab_to_target_config,FFI)lab_state))))) IN asm_state_mem_domain (t1:(A)asm_state) /\
    ~(word_add (word_add p (word (LENGTH (prog_to_bytes code2))))
       (word (LENGTH (buffer_buffer (lab_state_code_buffer s1)))) IN
      lab_state_mem_domain s1)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "buffer_space_left"
                               with Failure _ -> false)) (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "MEM"
                                    with Failure _ -> false)) (concl th)))) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; LET_DEF; LET_END_DEF];
    ALL_TAC] THEN
  ABBREV_TAC `LP = LENGTH (prog_to_bytes (code2:((A)sec)list))` THEN
  ABBREV_TAC `LB = LENGTH (buffer_buffer
                 (lab_state_code_buffer (s1:(A,lab_to_target_config,FFI)lab_state)))` THEN
  ABBREV_TAC `sl = buffer_space_left
                 (lab_state_code_buffer (s1:(A,lab_to_target_config,FFI)lab_state))` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
      can (find_term ((=) `ms2:B`)) (concl th))) THEN
    ASM_REWRITE_TAC[asm_upd_pc_def];
    X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A word` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "word_loc_val_byte"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(word_add (word_add p (word LP)) (word LB) IN
                   lab_state_mem_domain (s1:(A,lab_to_target_config,FFI)lab_state))` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "asm_state_mem_domain"
                               with Failure _ -> false)) (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "word_loc_val_byte"
                                    with Failure _ -> false)) (concl th)))) THEN
    ANTS_TAC THENL [LTTP3AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH_APPEND; LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `LB + n + 1 = (LB + SUC 0) + n`];
    MATCH_MP_TAC bytes_in_mem_UPDATE THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w] THEN
    MATCH_MP_TAC LTTP3AUX_word_add_neq THEN LTTP3AUX_ARITH_TAC;
    REWRITE_TAC[bytes_in_mem_APPEND] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC bytes_in_mem_UPDATE THEN CONJ_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LTTP3AUX_word_add_neq THEN LTTP3AUX_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "bytes_in_mem" th &&
          can (find_term (fun t -> try fst(dest_const t) = "buffer_buffer"
                                   with Failure _ -> false)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[bytes_in_mem_def; APPLY_UPDATE_THM]];
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN LTTP3AUX_ARITH_TAC;
    X_GEN_TAC `bn:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `bn:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "MEM"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `bn < LENGTH (APPEND (buffer_buffer (lab_state_code_buffer
                   (s1:(A,lab_to_target_config,FFI)lab_state))) [b:byte]) + sl - 1` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN LTTP3AUX_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "share_mem_state_rel")) THEN
    REWRITE_TAC(share_mem_state_rel_def :: LTTP3AUX_RECS)]);;
(* the target store of the byte of a Cbw *)
let LTTP3AUX_write_mem_word_1 = prove
 (`!(a:A word) w (s:(A)asm_state).
     write_mem_word a 1 w s =
     asm_assert (a IN asm_state_mem_domain s) (asm_upd_mem a (word_zx w) s)`,
  REWRITE_TAC[ONE; write_mem_word_def; LET_DEF; LET_END_DEF]);;

let LTTP3AUX_inst_store8 = prove
 (`!(t1:(A)asm_state) r1 r2.
     asm_state_regs t1 r1 IN asm_state_mem_domain t1 /\ ~asm_state_failed t1
     ==> asmSem_inst (Mem Store8 r2 (Addr r1 (word 0))) t1 =
         asm_state_mem_fupd
           (K ((asm_state_regs t1 r1 =+ word_zx (asm_state_regs t1 r2)) (asm_state_mem t1)))
           t1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[asmSem_inst_def; asm_mem_op_def; asm_mem_store_def; asm_addr_def; read_reg_def;
              LET_DEF; LET_END_DEF; WORD_ADD_0; SUB_REFL; LTTP3AUX_write_mem_word_1;
              COND_ID; asm_assert_def; asm_upd_mem_def] THEN
  REWRITE_TAC(REWRITE_RULE[EXP] (SPEC `0` LOG2_TWOEXP) :: aligned_0 :: LTTP3AUX_RECS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[asm_state_component_equality] THEN
  REWRITE_TAC LTTP3AUX_RECS THEN ASM_REWRITE_TAC[]);;
(* the code buffer parts of state_rel *)
let LTTP3AUX_state_rel_buffer_facts = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> (!n. n < buffer_space_left (lab_state_code_buffer s1)
              ==> word_add (buffer_position (lab_state_code_buffer s1))
                    (word (LENGTH (buffer_buffer (lab_state_code_buffer s1)) + n))
                    IN asm_state_mem_domain t1 /\
                  ~(word_add (buffer_position (lab_state_code_buffer s1))
                      (word (LENGTH (buffer_buffer (lab_state_code_buffer s1)) + n))
                    IN lab_state_mem_domain s1)) /\
         buffer_position (lab_state_code_buffer s1) =
           word_add p (word (LENGTH (prog_to_bytes code2))) /\
         LENGTH (prog_to_bytes code2) + LENGTH (buffer_buffer (lab_state_code_buffer s1)) +
           buffer_space_left (lab_state_code_buffer s1) < dimword (:A)`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
(* HOL4 line 7719, Resume compile_correct[CBW] *)
let LTTP3AUX_cc_Cbw = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) r1 r2 a1 a2.
     asm_fetch s1 = SOME (Asm (Cbw r1 r2) a1 a2)
     ==> !w1. lab_state_regs s1 r1 = wl_Word w1
     ==> !w2. lab_state_regs s1 r2 = wl_Word w2
     ==> !cb. buffer_write (lab_state_code_buffer s1) w1 (word_zx w2) = SOME cb
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!a1 a2 r1 r2 w1 w2 new_cb.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (Asm (Cbw r1 r2) a1 a2) /\
          lab_state_regs s1 r1 = wl_Word w1 /\
          lab_state_regs s1 r2 = wl_Word w2 /\
          buffer_write (lab_state_code_buffer s1) w1 (word_zx w2) = SOME new_cb
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1
                  (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K new_cb) s1))) /\
                lab_evaluate (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K new_cb) s1))) =
                  (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K new_cb) s1))) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi
                           (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K new_cb) s1))))
                        (lab_state_clock
                           (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K new_cb) s1))) +
                         k) ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate (inc_pc (lab_dec_clock (lab_state_code_buffer_fupd (K cb) s1))) = (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT(GEN_TAC THEN DISCH_TAC) THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  SUBGOAL_THEN `asm_state_regs (t1:(A)asm_state) r1 = w1 /\ asm_state_regs t1 r2 = w2`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> MP_TAC(SPEC `r1:num` th) THEN MP_TAC(SPEC `r2:num` th)) o
      check (fun th -> is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) =
        "word_loc_val" with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) r1 =
                          wl_Word w1`;
                ASSUME `lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) r2 =
                          wl_Word w2`; word_loc_val_def; option_INJ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_buffer_facts) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_write_byte) THEN
  FIRST_ASSUM(fun th -> if lhs(concl th) =
      `buffer_position (lab_state_code_buffer (s1:(A,lab_to_target_config,FFI)lab_state))`
      then REWRITE_TAC[th] else NO_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `w1 IN asm_state_mem_domain (t1:(A)asm_state) /\
                ~(w1 IN lab_state_mem_domain (s1:(A,lab_to_target_config,FFI)lab_state))`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "buffer_space_left"
                               with Failure _ -> false)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "asm_state_mem_domain"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `r1:num`; `r2:num`; `a1:byte list`; `a2:num`]
    IMP_bytes_in_memory_Cbw) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `bytes':byte list` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `jj = Mem Store8 r2 (Addr r1 (word 0)):(A)inst` THEN
  ABBREV_TAC `t2 = asm_state_mem_fupd (K ((w1 =+ (word_zx (w2:A word):byte))
                     (asm_state_mem t1))) (t1:(A)asm_state)` THEN
  SUBGOAL_THEN `asm (asm_Inst jj) (word_add (asm_state_pc t1) (word (LENGTH (bytes':byte list))))
                  t1 =
                asm_upd_pc (word_add p (word (pos_val
                  (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1) 0
                  (code2:((A)sec)list)))) (t2:(A)asm_state)` (LABEL_TAC "asmeq") THENL
   [REWRITE_TAC[asm_def] THEN BINOP_TAC THENL
     [ASM_REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC];
      MAP_EVERY EXPAND_TAC ["jj"; "t2"] THEN
      MP_TAC(ISPECL [`t1:(A)asm_state`; `r1:num`; `r2:num`] LTTP3AUX_inst_store8) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `asm_Inst jj:(A)asm`;
     `asm (asm_Inst jj) (word_add (asm_state_pc t1) (word (LENGTH (bytes':byte list))))
        (t1:(A)asm_state)`; `bytes':byte list`] asm_step_IMP_evaluate_step_nop) THEN
  USE_THEN "asmeq" SUBST1_TAC THEN
  ASM_REWRITE_TAC[asm_step_nop_def; distinctness "asm"] THEN ANTS_TAC THENL
   [EXPAND_TAC "t2" THEN REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
        `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
        `Asm (Cbw r1 r2) a1 a2:(A)line`] LTTP3AUX_fetch_disjoint) THEN
      ASM_REWRITE_TAC[injectivity "line"; distinctness "asm_or_cbw"] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `LENGTH (line_bytes (j:(A)line)) = LENGTH (bytes':byte list)`
        (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
      MATCH_MP_TAC asm_fetch_aux_pos_val_LENGTH_EQ THEN
      MAP_EVERY EXISTS_TAC [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `0`;
        `code2:((A)sec)list`;
        `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
        `labs:(num spt)spt`; `ffis:ffiname list`] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC(GEN_ALL bytes_in_mem_IMP) THEN
      EXISTS_TAC `lab_state_mem_domain (s1:(A,lab_to_target_config,FFI)lab_state)` THEN
      MATCH_MP_TAC bytes_in_mem_UPDATE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `w1 = word_add (p:A word) (word (LENGTH (prog_to_bytes (code2:((A)sec)list)) +
                      LENGTH (buffer_buffer (lab_state_code_buffer
                        (s1:(A,lab_to_target_config,FFI)lab_state)))))` SUBST1_TAC THENL
       [FIRST_ASSUM(fun th -> if rhs(concl th) = `w1:A word`
                              then GEN_REWRITE_TAC LAND_CONV [SYM th] else NO_TAC) THEN
        REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1`; `0`;
        `code2:((A)sec)list`;
        `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
        `labs:(num spt)spt`; `ffis:ffiname list`; `0`] pos_val_bound) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; GSYM WORD_ADD_ASSOC; word_add_n2w] THEN DISCH_TAC THEN
      MATCH_MP_TAC LTTP3AUX_word_add_neq THEN LTTP3AUX_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  REMOVE_THEN "IH" (MP_TAC o SPECL [`a1:byte list`; `a2:num`; `r1:num`; `r2:num`; `w1:A word`;
                                     `w2:A word`; `cb:(A,8)buffer`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:machine_result`;
    `shift_interfer l (mc_conf:(A,B,C)machine_config)`;
    `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
    `asm_upd_pc (word_add p (word (pos_val
       (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1) 0 (code2:((A)sec)list))))
       (t2:(A)asm_state)`; `ms2:B`; `p:A word`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC oracle_tie_step THEN
      MAP_EVERY EXISTS_TAC [`ms1:B`; `s1:(A,lab_to_target_config,FFI)lab_state`] THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC(inc_pc_def :: lab_dec_clock_def :: LTTP3AUX_RECS);
      REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[shift_interfer_def; machine_config_INFO.ri_accfupds];
      MATCH_MP_TAC state_rel_shift_interfer THEN EXPAND_TAC "t2" THEN
      MATCH_MP_TAC LTTP3AUX_state_rel_cbw THEN
      EXISTS_TAC `ms1:B` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `target_state_rel (machine_config_target (mc_conf:(A,B,C)machine_config))
        (asm_upd_pc (word_add p (word (pos_val
           (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state) + 1) 0
           (code2:((A)sec)list)))) (t2:(A)asm_state)) (ms2:B)` THEN
      EXPAND_TAC "t2" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC(inc_pc_def :: lab_dec_clock_def :: LTTP3AUX_RECS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `ms3:B`)) THEN
  MAP_EVERY EXISTS_TAC [`k + l - 1`; `ms3:B`] THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) - 1 + k` o
    check (fun th -> is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) =
      "target_evaluate" with Failure _ -> false)) (concl th))) THEN
  LTTP3AUX_STEP_CLOCK_TAC `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state)`
    `l:num`);;
(* one run of the target from an ffi entry point of a shared memory access *)
let LTTP3AUX_target_evaluate_SharedMem = prove
 (`!(mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k ms index op nb r off reg pc'.
     ~(k = 0) /\
     ~(target_get_pc (machine_config_target mc) ms IN
       machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
     ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
     ~(target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc) /\
     find_index (target_get_pc (machine_config_target mc) ms)
       (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
     EL index (machine_config_ffi_names mc) = SharedMem op /\
     ALOOKUP (machine_config_mmio_info mc) index = SOME (nb,Addr r off,reg,pc') /\
     (nb = word 0 ==>
      val (word_add (target_get_reg (machine_config_target mc) ms r) off) MOD
        (dimindex (:A) DIV 8) = 0) /\
     word_add (target_get_reg (machine_config_target mc) ms r) off IN
       machine_config_shared_addresses mc /\
     (op = MappedRead ==>
      is_valid_mapped_read (target_get_pc (machine_config_target mc) ms) nb (Addr r off)
        reg pc' (machine_config_target mc) ms (machine_config_prog_addresses mc)) /\
     (op = MappedWrite ==>
      is_valid_mapped_write (target_get_pc (machine_config_target mc) ms) nb (Addr r off)
        reg pc' (machine_config_target mc) ms (machine_config_prog_addresses mc))
     ==> target_evaluate mc ffi k ms =
         (match call_FFI ffi (SharedMem op) [nb]
                  (if op = MappedRead
                   then word_to_bytes
                          (word_add (target_get_reg (machine_config_target mc) ms r) off) F
                   else APPEND (let w = target_get_reg (machine_config_target mc) ms reg in
                                if nb = word 0 then word_to_bytes w F
                                else word_to_bytes_aux (val nb) w F)
                          (word_to_bytes
                             (word_add (target_get_reg (machine_config_target mc) ms r) off) F))
          with
            FFI_final outcome -> (target_Halt (FFI_outcome outcome),ms,ffi)
          | FFI_return new_ffi new_bytes ->
              target_evaluate
                (machine_config_ffi_interfer_fupd
                   (K (shift_seq 1 (machine_config_ffi_interfer mc))) mc)
                new_ffi (k - 1)
                (machine_config_ffi_interfer mc 0 (index,new_bytes,ms)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [target_evaluate_def] THEN
  CASES_ON `op:shmem_op` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "shmem_op"]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; distinctness "shmem_op"] THEN CASE_REWRITE_TAC[] THEN
  (COND_CASES_TAC THENL
    [CASE_REWRITE_TAC[apply_oracle_def] THEN TOP_CASE_TAC THEN CASE_REWRITE_TAC[]; ASM_MESON_TAC[]]));;
(* the first k bytes of a word *)
let LTTP3AUX_LENGTH_word_to_bytes_aux = prove
 (`!n (w:N word) be. LENGTH (word_to_bytes_aux n w be) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[word_to_bytes_aux_def; LENGTH; LENGTH_APPEND] THEN
  ARITH_TAC);;

let LTTP3AUX_TAKE_word_to_bytes_aux = prove
 (`!k n (w:N word) be. k <= n ==> TAKE k (word_to_bytes_aux n w be) = word_to_bytes_aux k w be`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[word_to_bytes_aux_def] THEN
    MATCH_MP_TAC TAKE_LENGTH_ID_rwt THEN REWRITE_TAC[LENGTH];
    REPEAT STRIP_TAC THEN REWRITE_TAC[word_to_bytes_aux_def] THEN
    ASM_CASES_TAC `k = SUC n` THENL
     [ASM_REWRITE_TAC[GSYM word_to_bytes_aux_def] THEN
      MATCH_MP_TAC TAKE_LENGTH_ID_rwt THEN
      REWRITE_TAC[LTTP3AUX_LENGTH_word_to_bytes_aux];
      ASM_SIMP_TAC[TAKE_APPEND1; LTTP3AUX_LENGTH_word_to_bytes_aux;
                   ARITH_RULE `k <= SUC n /\ ~(k = SUC n) ==> k <= n`]]]);;
(* the byte constants of the shared memory accesses *)
let LTTP3AUX_byte_consts = prove
 (`~(word 1 = word 0:byte) /\ ~(word 2 = word 0:byte) /\ ~(word 4 = word 0:byte) /\
   ~(word 2 = word 1:byte) /\ ~(word 4 = word 1:byte) /\ ~(word 4 = word 2:byte) /\
   val (word 1:byte) = 1 /\ val (word 2:byte) = 2 /\ val (word 4:byte) = 4`,
  REWRITE_TAC[n2w_11; dimword_def; DIMINDEX_8; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* the first 1, 2 or 4 bytes of a word *)
let LTTP3AUX_TAKE_word_to_bytes = prove
 (`!n (w:A word) be.
     good_dimindex(:A) /\ n <= 4
     ==> TAKE n (word_to_bytes w be) = word_to_bytes_aux n w be`,
  REWRITE_TAC[good_dimindex_def; word_to_bytes_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LTTP3AUX_TAKE_word_to_bytes_aux THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
(* the labSem shared memory accesses that return *)
let LTTP3AUX_share_mem_op_return = prove
 (`!m r ad (s:(A,C,FFI)lab_state) new_ffi new_bytes s' name nb.
     good_dimindex(:A) /\
     get_memop_info m = (name,nb) /\
     share_mem_op m r ad s = SOME (FFI_return new_ffi new_bytes,s')
     ==> ?r0 off w0.
           ad = Addr r0 off /\ lab_state_regs s r0 = wl_Word w0 /\
           (if nb = word 0
            then val (word_add w0 off) MOD (dimindex(:A) DIV 8) = 0 /\
                 word_add w0 off IN lab_state_shared_mem_domain s
            else byte_align (word_add w0 off) IN lab_state_shared_mem_domain s) /\
           (name = MappedRead ==>
            call_FFI (lab_state_ffi s) (SharedMem MappedRead) [nb]
              (word_to_bytes (word_add w0 off) F) = FFI_return new_ffi new_bytes /\
            s' = lab_state_ffi_fupd (K new_ffi)
                   (lab_state_regs_fupd
                      (K ((r =+ wl_Word (word_of_bytes F (word 0) new_bytes))
                            (lab_state_regs s)))
                   (lab_state_pc_fupd (K (lab_state_pc s + 1))
                   (lab_state_clock_fupd (K (lab_state_clock s - 1)) s)))) /\
           (name = MappedWrite ==>
            ?w. lab_state_regs s r = wl_Word w /\
                call_FFI (lab_state_ffi s) (SharedMem MappedWrite) [nb]
                  (APPEND (if nb = word 0 then word_to_bytes w F
                           else word_to_bytes_aux (val nb) w F)
                          (word_to_bytes (word_add w0 off) F)) =
                  FFI_return new_ffi new_bytes /\
                s' = inc_pc (lab_dec_clock (lab_state_ffi_fupd (K new_ffi) s)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> MP_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th))) THEN
  MP_TAC(ISPEC `ad:(A)addr` (nchotomy_of_type `:(A)addr`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num` (X_CHOOSE_THEN `off:A word` SUBST1_TAC)) THEN
  CASES_ON `m:memop` THEN REWRITE_TAC[get_memop_info_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def; lab_addr_def;
              distinctness "shmem_op"; LTTP3AUX_byte_consts] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `lab_state_regs (s:(A,C,FFI)lab_state) r0` (nchotomy_of_type `:(A)word_loc`)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w0:A word` ASSUME_TAC)
    (X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `n2:num` ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ; injectivity "ffi_result";
              distinctness "ffi_result"] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(SIMP_RULE[LTTP3AUX_TAKE_word_to_bytes; ASSUME `good_dimindex(:A)`;
                           ARITH_RULE `1 <= 4 /\ 2 <= 4 /\ 4 <= 4`]) THEN
  MAP_EVERY EXISTS_TAC [`r0:num`; `off:A word`; `w0:A word`] THEN
  ASM_REWRITE_TAC[injectivity "word_loc"; LTTP3AUX_byte_consts] THEN ASM_MESON_TAC[]);;
(* the labSem shared memory accesses that end the program *)
let LTTP3AUX_share_mem_op_final = prove
 (`!m r ad (s:(A,C,FFI)lab_state) outcome s' name nb.
     good_dimindex(:A) /\
     get_memop_info m = (name,nb) /\
     share_mem_op m r ad s = SOME (FFI_final outcome,s')
     ==> ?r0 off w0.
           ad = Addr r0 off /\ lab_state_regs s r0 = wl_Word w0 /\
           (if nb = word 0
            then val (word_add w0 off) MOD (dimindex(:A) DIV 8) = 0 /\
                 word_add w0 off IN lab_state_shared_mem_domain s
            else byte_align (word_add w0 off) IN lab_state_shared_mem_domain s) /\
           s' = s /\
           (name = MappedRead ==>
            call_FFI (lab_state_ffi s) (SharedMem MappedRead) [nb]
              (word_to_bytes (word_add w0 off) F) = FFI_final outcome) /\
           (name = MappedWrite ==>
            ?w. lab_state_regs s r = wl_Word w /\
                call_FFI (lab_state_ffi s) (SharedMem MappedWrite) [nb]
                  (APPEND (if nb = word 0 then word_to_bytes w F
                           else word_to_bytes_aux (val nb) w F)
                          (word_to_bytes (word_add w0 off) F)) =
                  FFI_final outcome)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> MP_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th))) THEN
  MP_TAC(ISPEC `ad:(A)addr` (nchotomy_of_type `:(A)addr`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num` (X_CHOOSE_THEN `off:A word` SUBST1_TAC)) THEN
  CASES_ON `m:memop` THEN REWRITE_TAC[get_memop_info_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[share_mem_op_def; share_mem_load_def; share_mem_store_def; lab_addr_def;
              distinctness "shmem_op"; LTTP3AUX_byte_consts] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `lab_state_regs (s:(A,C,FFI)lab_state) r0` (nchotomy_of_type `:(A)word_loc`)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w0:A word` ASSUME_TAC)
    (X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `n2:num` ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ; injectivity "ffi_result";
              distinctness "ffi_result"] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(SIMP_RULE[LTTP3AUX_TAKE_word_to_bytes; ASSUME `good_dimindex(:A)`;
                           ARITH_RULE `1 <= 4 /\ 2 <= 4 /\ 4 <= 4`]) THEN
  MAP_EVERY EXISTS_TAC [`r0:num`; `off:A word`; `w0:A word`] THEN
  ASM_REWRITE_TAC[injectivity "word_loc"; LTTP3AUX_byte_consts] THEN ASM_MESON_TAC[]);;
(* state_rel after a shared memory access: the ffi state makes one call_FFI *)
(* step, the next ffi interference is used up, a register may change, both  *)
(* pcs move to the next line                                                 *)
let LTTP3AUX_state_rel_share_mem = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 S t2 ms2.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     lab_state_mem S = lab_state_mem s1 /\
     lab_state_mem_domain S = lab_state_mem_domain s1 /\
     lab_state_shared_mem_domain S = lab_state_shared_mem_domain s1 /\
     lab_state_be S = lab_state_be s1 /\ lab_state_code S = lab_state_code s1 /\
     lab_state_compile S = lab_state_compile s1 /\
     lab_state_compile_oracle S = lab_state_compile_oracle s1 /\
     lab_state_code_buffer S = lab_state_code_buffer s1 /\
     lab_state_failed S = lab_state_failed s1 /\
     lab_state_ptr_reg S = lab_state_ptr_reg s1 /\
     lab_state_len_reg S = lab_state_len_reg s1 /\
     lab_state_ptr2_reg S = lab_state_ptr2_reg s1 /\
     lab_state_len2_reg S = lab_state_len2_reg s1 /\
     lab_state_link_reg S = lab_state_link_reg s1 /\
     lab_state_fp_regs S = lab_state_fp_regs s1 /\
     lab_state_pc S = lab_state_pc s1 + 1 /\
     call_FFI_rel (lab_state_ffi s1) (lab_state_ffi S) /\
     (!r. word_loc_val p labs (lab_state_regs S r) = SOME (asm_state_regs t2 r)) /\
     asm_state_mem t2 = asm_state_mem t1 /\
     asm_state_mem_domain t2 = asm_state_mem_domain t1 /\
     asm_state_fp_regs t2 = asm_state_fp_regs t1 /\
     asm_state_be t2 = asm_state_be t1 /\ asm_state_align t2 = asm_state_align t1 /\
     asm_state_lr t2 = asm_state_lr t1 /\ asm_state_failed t2 = asm_state_failed t1 /\
     asm_state_pc t2 = word_add p (word (pos_val (lab_state_pc s1 + 1) 0 code2)) /\
     target_state_rel (machine_config_target mc_conf) t2 ms2
     ==> lab_to_targetProof_state_rel
           (machine_config_ffi_interfer_fupd
              (K (shift_seq 1 (machine_config_ffi_interfer mc_conf))) mc_conf,code2,labs,p)
           S t2 ms2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (fun (asl,w as g) ->
     let S = `S:(A,lab_to_target_config,FFI)lab_state` and t2 = `t2:(A)asm_state` in
     let flds = filter (fun th -> is_eq(concl th) &&
                  (let l = lhs(concl th) in is_comb l && (rand l = S || rand l = t2)))
                (map snd asl) in
     REWRITE_TAC(flds @ (record_info "machine_config").ri_accfupds :: K_THM ::
                 read_ffi_bytearrays_ffi_interfer :: []) g) THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY X_GEN_TAC [`ms:B`; `k:num`; `index:num`; `nbytes:byte list`; `tt:(A)asm_state`;
      `bytes:byte list`; `bytes2:byte list`; `st:(FFI)ffi_state`; `nst:(FFI)ffi_state`;
      `i:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ms:B`; `k + 1`; `index:num`; `nbytes:byte list`;
      `tt:(A)asm_state`; `bytes:byte list`; `bytes2:byte list`; `st:(FFI)ffi_state`;
      `nst:(FFI)ffi_state`; `i:num`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "read_ffi_bytearrays"
                                 with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[shift_seq_def] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC RTC_TRANS THEN
      EXISTS_TAC `lab_state_ffi (S:(A,lab_to_target_config,FFI)lab_state)` THEN
      ASM_SIMP_TAC[RTC_INC];
      REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "share_mem_state_rel")) THEN
    REWRITE_TAC[share_mem_state_rel_def; shift_seq_def] THEN
    REWRITE_TAC[(record_info "machine_config").ri_accfupds; K_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MAP_EVERY X_GEN_TAC [`ms:B`; `k:num`; `index:num`; `nbytes:byte list`; `tt:(A)asm_state`;
      `nb:byte`; `ad:num`; `offs:A word`; `re:num`; `pc':A word`; `ad':A word`;
      `st:(FFI)ffi_state`; `nst:(FFI)ffi_state`; `i:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ms:B`; `k + 1`; `index:num`; `nbytes:byte list`;
      `tt:(A)asm_state`; `nb:byte`; `ad:num`; `offs:A word`; `re:num`; `pc':A word`;
      `ad':A word`; `st:(FFI)ffi_state`; `nst:(FFI)ffi_state`; `i:num`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "is_valid_mapped_read"
                                 with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC RTC_TRANS THEN
      EXISTS_TAC `lab_state_ffi (S:(A,lab_to_target_config,FFI)lab_state)` THEN
      ASM_SIMP_TAC[RTC_INC];
      REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
    REWRITE_TAC[share_mem_domain_code_rel_def] THEN
    REWRITE_TAC[(record_info "machine_config").ri_accfupds; K_THM]]);;
(* the target facts of a shared memory line: its ffi entry point *)
let LTTP3AUX_state_rel_share_mem_line = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 m r ad a1 a2 name nb.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME (Asm (ShareMem m r ad) a1 a2) /\
     get_memop_info m = (name,nb)
     ==> ?bytes index i.
           enc_with_nop (asm_config_encode (target_config (machine_config_target mc_conf)))
             (asm_Inst (Mem m r ad)) bytes /\
           bytes_in_memory (word_add p (word (pos_val (lab_state_pc s1) 0 code2))) bytes
             (asm_state_mem t1) (asm_state_mem_domain t1) /\
           pos_val (lab_state_pc s1 + 1) 0 code2 =
             pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes /\
           asm_ok (asm_Inst (Mem m r ad)) (target_config (machine_config_target mc_conf)) /\
           find_index (word_add p (word (pos_val (lab_state_pc s1) 0 code2)))
             (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index /\
           EL index (machine_config_ffi_names mc_conf) = SharedMem name /\
           ALOOKUP (machine_config_mmio_info mc_conf) index =
             SOME (nb,ad,r,word_add p (word (pos_val (lab_state_pc s1) 0 code2 + LENGTH bytes))) /\
           mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\ i <= index /\
           index < LENGTH (machine_config_ffi_names mc_conf) /\
           EL index (machine_config_ffi_entry_pcs mc_conf) =
             word_add p (word (pos_val (lab_state_pc s1) 0 code2)) /\
           ~(word_add p (word (pos_val (lab_state_pc s1) 0 code2)) =
             machine_config_halt_pc mc_conf) /\
           ~(word_add p (word (pos_val (lab_state_pc s1) 0 code2)) =
             machine_config_ccache_pc mc_conf) /\
           ~(word_add p (word (pos_val (lab_state_pc s1) 0 code2)) IN
             machine_config_prog_addresses mc_conf DIFF
             set_of_list (machine_config_ffi_entry_pcs mc_conf))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `m:memop`; `r:num`;
     `ad:(A)addr`; `a1:byte list`; `a2:num`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`;
     `TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
        (machine_config_ffi_names mc_conf)`;
     `p:A word`; `t1:(A)asm_state`] IMP_bytes_in_memory_ShareMem) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[asm_fetch_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `bytes:byte list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_state_rel_def] o
    check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[share_mem_domain_code_rel_def] o
    check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
  DISCH_THEN(MP_TAC o SPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`;
    `m:memop`; `r:num`; `ad:(A)addr`; `bytes:byte list`; `LENGTH (bytes:byte list)`;
    `i:num`]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `index:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`bytes:byte list`; `index:num`; `i:num`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `index < LENGTH (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) /\
                EL index (machine_config_ffi_entry_pcs mc_conf) =
                word_add p (word (pos_val (lab_state_pc
                  (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list)))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `find_index (word_add p (word (pos_val (lab_state_pc
       (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list))))
       (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config)) 0 = SOME index` THEN
    REWRITE_TAC[find_index_INDEX_OF; INDEX_OF_eq_SOME] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`index:num`; `i:num`] o CONJUNCT2 o
    REWRITE_RULE[share_mem_state_rel_def] o check (LTTP3AUX_HEAD_IS "share_mem_state_rel")) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP find_index_LESS_LENGTH o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "find_index"
      with Failure _ -> false)) THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP find_index_is_MEM o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "find_index"
      with Failure _ -> false)) THEN
    SIMP_TAC[IN_DIFF; IN_SET_OF_LIST]]);;
(* the target check of a shared memory access holds for its encoding *)
let LTTP3AUX_valid_mapped = prove
 (`!m name nb (pc:A word) r ad (pc':D) (t:(A,B,C)target) ms md.
     get_memop_info m = (name,nb) /\
     bytes_in_memory pc (asm_config_encode (target_config t) (asm_Inst (Mem m r ad)))
       (target_get_byte t ms) md
     ==> (name = MappedRead ==> is_valid_mapped_read pc nb ad r pc' t ms md) /\
         (name = MappedWrite ==> is_valid_mapped_write pc nb ad r pc' t ms md)`,
  GEN_TAC THEN CASES_ON `m:memop` THEN
  REWRITE_TAC[get_memop_info_def; PAIR_EQ; is_valid_mapped_read_def;
              is_valid_mapped_write_def] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST1_TAC o SYM))
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[distinctness "shmem_op"; LTTP3AUX_byte_consts]);;
(* instantiate the free variables of a theorem by name *)
let LTTP3AUX_INSTN (prs:(string*term) list) (th:thm) =
  let fvs = frees (concl th) in
  INST (map (fun (n,t) -> (t, find (fun v -> fst(dest_var v) = n) fvs)) prs) th;;

(* the shared memory relation of state_rel at the current machine state *)
let LTTP3AUX_share_mem_target_rel = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 index i nb r0 off r pc' new_bytes new_ffi.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\ i <= index /\
     index < LENGTH (machine_config_ffi_names mc_conf) /\
     ALOOKUP (machine_config_mmio_info mc_conf) index = SOME (nb,Addr r0 off,r,pc') /\
     EL index (machine_config_ffi_entry_pcs mc_conf) = asm_state_pc t1 /\
     (nb = word 0 ==>
      val (word_add (target_get_reg (machine_config_target mc_conf) ms1 r0) off) MOD
        (dimindex (:A) DIV 8) = 0) /\
     word_add (target_get_reg (machine_config_target mc_conf) ms1 r0) off IN
       machine_config_shared_addresses mc_conf
     ==> (EL index (machine_config_ffi_names mc_conf) = SharedMem MappedRead /\
          is_valid_mapped_read (target_get_pc (machine_config_target mc_conf) ms1)
            nb (Addr r0 off) r pc' (machine_config_target mc_conf) ms1
            (machine_config_prog_addresses mc_conf) /\
          call_FFI (lab_state_ffi s1) (SharedMem MappedRead) [nb]
            (word_to_bytes
               (word_add (target_get_reg (machine_config_target mc_conf) ms1 r0) off) F) =
            FFI_return new_ffi new_bytes
          ==> target_state_rel (machine_config_target mc_conf)
                (asm_state_pc_fupd (K pc')
                   (asm_state_regs_fupd
                      (K (\n. if n = r then word_of_bytes F (word 0) new_bytes
                              else asm_state_regs t1 n)) t1))
                (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms1))) /\
         (EL index (machine_config_ffi_names mc_conf) = SharedMem MappedWrite /\
          is_valid_mapped_write (target_get_pc (machine_config_target mc_conf) ms1)
            nb (Addr r0 off) r pc' (machine_config_target mc_conf) ms1
            (machine_config_prog_addresses mc_conf) /\
          call_FFI (lab_state_ffi s1) (SharedMem MappedWrite) [nb]
            (APPEND
               (let w = target_get_reg (machine_config_target mc_conf) ms1 r in
                if nb = word 0 then word_to_bytes w F
                else word_to_bytes_aux (val nb) w F)
               (word_to_bytes
                  (word_add (target_get_reg (machine_config_target mc_conf) ms1 r0) off) F)) =
            FFI_return new_ffi new_bytes
          ==> target_state_rel (machine_config_target mc_conf)
                (asm_state_pc_fupd (K pc') t1)
                (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_state_rel_def] o
    check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o REWRITE_RULE[share_mem_state_rel_def] o
     find (LTTP3AUX_HEAD_IS "share_mem_state_rel") o CONJUNCTS) THEN
  DISCH_THEN(MP_TAC o SPECL [`ms1:B`; `0`; `index:num`; `new_bytes:byte list`;
    `t1:(A)asm_state`; `nb:byte`; `r0:num`; `off:A word`; `r:num`; `pc':A word`;
    `word_add (target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r0)
       off`;
    `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `new_ffi:(FFI)ffi_state`;
    `i:num`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(MATCH_ACCEPT_TAC RTC_REFL) THEN
    TRY REFL_TAC THEN
    UNDISCH_TAC `target_state_rel (machine_config_target (mc_conf:(A,B,C)machine_config))
                   t1 ms1` THEN
    REWRITE_TAC[ASSUME `EL index (machine_config_ffi_entry_pcs
                   (mc_conf:(A,B,C)machine_config)) = asm_state_pc (t1:(A)asm_state)`] THEN
    REWRITE_TAC[target_state_rel_def; K_THM; (record_info "asm_state").ri_accfupds];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `op:shmem_op` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "m"))) THEN
  CONJ_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `EL index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
               SharedMem op` THEN
  ASM_REWRITE_TAC[injectivity "ffiname"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  USE_THEN "m" MP_TAC THEN CASE_REWRITE_TAC[] THEN
  ANTS_TAC THEN TRY(DISCH_THEN ACCEPT_TAC) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;
(* select an assumption by the head constant of the left side of its      *)
(* conclusion                                                                 *)
let LTTP3AUX_LHS_IS (c:string) (th:thm) =
  try fst(dest_const(fst(strip_comb(lhs(concl th))))) = c with Failure _ -> false;;
(* HOL4 line 7829, Resume compile_correct[ShareMemOp]: the access returns *)
let LTTP3AUX_cc_ShareMem = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) m r ad a1 a2.
     asm_fetch s1 = SOME (Asm (ShareMem m r ad) a1 a2)
     ==> !new_ffi new_bytes s'.
       share_mem_op m r ad s1 = SOME (FFI_return new_ffi new_bytes,s')
     ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       (!a1 a2 m r ad new_ffi new_bytes s'.
          ~(lab_state_clock s1 = 0) /\
          asm_fetch s1 = SOME (Asm (ShareMem m r ad) a1 a2) /\
          share_mem_op m r ad s1 = SOME (FFI_return new_ffi new_bytes,s')
          ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
                oracle_tie mc_conf ms1
                  (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
                     (lab_state_io_fp_regs_fupd
                        (K (shift_seq 1 (lab_state_io_fp_regs s'))) s')) /\
                lab_evaluate
                  (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
                     (lab_state_io_fp_regs_fupd
                        (K (shift_seq 1 (lab_state_io_fp_regs s'))) s')) = (res,s2) /\
                ~(res = target_Error) /\
                encoder_correct (machine_config_target mc_conf) /\
                lab_to_targetProof_state_rel (mc_conf,code2,labs,p)
                  (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
                     (lab_state_io_fp_regs_fupd
                        (K (shift_seq 1 (lab_state_io_fp_regs s'))) s')) t1 ms1
                ==> ?k ms2.
                      target_evaluate mc_conf
                        (lab_state_ffi
                          (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
                             (lab_state_io_fp_regs_fupd
                                (K (shift_seq 1 (lab_state_io_fp_regs s'))) s')))
                        (lab_state_clock
                          (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
                             (lab_state_io_fp_regs_fupd
                                (K (shift_seq 1 (lab_state_io_fp_regs s'))) s')) + k) ms1 =
                      (res,ms2,lab_state_ffi s2)) /\
       ~(lab_state_clock s1 = 0) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
       lab_evaluate
         (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s')))
            (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s'))) s')) =
         (res,s2)
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  MP_TAC(ISPEC `get_memop_info m` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:shmem_op` (X_CHOOSE_THEN `nb:byte` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`m:memop`; `r:num`; `ad:(A)addr`; `s1:(A,lab_to_target_config,FFI)lab_state`;
     `new_ffi:(FFI)ffi_state`; `new_bytes:byte list`;
     `s':(A,lab_to_target_config,FFI)lab_state`; `name:shmem_op`; `nb:byte`]
    LTTP3AUX_share_mem_op_return) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num` (X_CHOOSE_THEN `off:A word` (X_CHOOSE_THEN `w0:A word`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "cond") (LABEL_TAC "rw"))))))) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `m:memop`; `r:num`; `Addr r0 off:(A)addr`; `a1:byte list`; `a2:num`; `name:shmem_op`;
     `nb:byte`] LTTP3AUX_state_rel_share_mem_line) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bytes:byte list` (X_CHOOSE_THEN `index:num`
    (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))) THEN
  (* the registers of the access *)
  SUBGOAL_THEN `reg_ok r0 (target_config (machine_config_target (mc_conf:(A,B,C)machine_config))) /\
                reg_ok r (target_config (machine_config_target mc_conf))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `asm_ok (asm_Inst (Mem m r (Addr r0 off)))
                   (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))` THEN
    REWRITE_TAC[asm_ok_def; inst_ok_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. reg_ok x (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                    ==> target_get_reg (machine_config_target mc_conf) ms1 x =
                        asm_state_regs (t1:(A)asm_state) x` (LABEL_TAC "regs") THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def] o check (fun th ->
      LTTP3AUX_HEAD_IS "target_state_rel" th && can (find_term ((=) `ms1:B`)) (concl th))) THEN
    SIMP_TAC[reg_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r0 =
                w0` ASSUME_TAC THENL
   [USE_THEN "regs" (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `r0:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "word_loc_val" with Failure _ -> false))
        (concl th))) THEN
    REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) r0 = wl_Word w0`;
                word_loc_val_def; option_INJ] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  (* the access is aligned and in the shared addresses *)
  SUBGOAL_THEN `word_add w0 off IN
                  machine_config_shared_addresses (mc_conf:(A,B,C)machine_config) /\
                ((nb:byte) = word 0 ==> val (word_add (w0:A word) off) MOD (dimindex(:A) DIV 8) = 0)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[share_mem_domain_code_rel_def] o
      check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      MP_TAC(el 2 cs) THEN REWRITE_TAC[el 3 cs]) THEN
    USE_THEN "cond" MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the encoding of the access is in the target memory *)
  SUBGOAL_THEN `bytes_in_memory
      (word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list))))
      (asm_config_encode (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
         (asm_Inst (Mem m r (Addr r0 off))))
      (target_get_byte (machine_config_target mc_conf) ms1)
      (machine_config_prog_addresses mc_conf)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "machine_config_prog_addresses"
       with Failure _ -> false))) THEN
    MATCH_MP_TAC bytes_in_memory_eq_mem THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def] o check (fun th ->
        LTTP3AUX_HEAD_IS "target_state_rel" th && can (find_term ((=) `ms1:B`)) (concl th))) THEN
      STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "bytes_in_memory" th &&
        can (find_term ((=) `bytes:byte list`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "enc_with_nop")) THEN
      REWRITE_TAC[enc_with_nop_thm] THEN DISCH_THEN(X_CHOOSE_THEN `nn:num` SUBST1_TAC) THEN
      SIMP_TAC[bytes_in_memory_APPEND]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:memop`; `name:shmem_op`; `nb:byte`;
     `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list)))`;
     `r:num`; `Addr r0 off:(A)addr`;
     `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
        LENGTH (bytes:byte list)))`;
     `machine_config_target (mc_conf:(A,B,C)machine_config)`; `ms1:B`;
     `machine_config_prog_addresses (mc_conf:(A,B,C)machine_config)`] LTTP3AUX_valid_mapped) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 =
                word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list)))`
    (LABEL_TAC "pc") THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def] o check (fun th ->
      LTTP3AUX_HEAD_IS "target_state_rel" th && can (find_term ((=) `ms1:B`)) (concl th))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EL index (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config)) =
                asm_state_pc (t1:(A)asm_state)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `index:num`; `i:num`; `nb:byte`; `r0:num`; `off:A word`; `r:num`;
     `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
        LENGTH (bytes:byte list)))`;
     `new_bytes:byte list`; `new_ffi:(FFI)ffi_state`] LTTP3AUX_share_mem_target_rel) THEN
  REWRITE_TAC[ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config))
                 ms1 r0 = w0`] THEN
  USE_THEN "pc" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rel_read") (LABEL_TAC "rel_write")) THEN
  (* the two kinds of access *)
  MP_TAC(ISPEC `name:shmem_op` (nchotomy_of_type `:shmem_op`)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "shmem_op"])
  THENL
   [(* MappedRead *)
    USE_THEN "rw" (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s'")) THEN
    USE_THEN "rel_read" MP_TAC THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `!k. target_evaluate (mc_conf:(A,B,C)machine_config)
          (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)) (lab_state_clock s1 + k) ms1 =
        target_evaluate (machine_config_ffi_interfer_fupd
            (K (shift_seq 1 (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config)))) mc_conf)
          new_ffi (lab_state_clock s1 - 1 + k)
          (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms1))` (LABEL_TAC "step") THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
        `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) + k`; `ms1:B`; `index:num`;
        `MappedRead`; `nb:byte`; `r0:num`; `off:A word`; `r:num`;
        `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list)))`] LTTP3AUX_target_evaluate_SharedMem) THEN
      USE_THEN "pc" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config))
                    ms1 r0 = w0`; distinctness "shmem_op"] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "rw" (fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
      CASE_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `next_interference (mc_conf:(A,B,C)machine_config)
          (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)) ms1 =
        SOME (FfiApp index new_bytes ms1
                (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms1)),
              machine_config_ffi_interfer_fupd
            (K (shift_seq 1 (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config)))) mc_conf,
              new_ffi)` ASSUME_TAC THENL
     [MATCH_MP_TAC(LTTP3AUX_INSTN [("op",`MappedRead`); ("nb",`nb:byte`); ("r",`r0:num`);
         ("off",`off:A word`); ("reg",`r:num`); ("pc'",`word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list)))`)] next_interference_SharedMem) THEN
      USE_THEN "pc" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config))
                    ms1 r0 = w0`;
        ASSUME `EL index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
                SharedMem MappedRead`; distinctness "shmem_op"] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "IH" (MP_TAC o SPECL [`a1:byte list`; `a2:num`; `m:memop`; `r:num`;
       `Addr r0 off:(A)addr`; `new_ffi:(FFI)ffi_state`; `new_bytes:byte list`;
       `s':(A,lab_to_target_config,FFI)lab_state`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:machine_result`; `machine_config_ffi_interfer_fupd
            (K (shift_seq 1 (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config)))) mc_conf`;
       `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
       `asm_state_pc_fupd (K (word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list)))))
          (asm_state_regs_fupd (K (\n. if n = r then word_of_bytes F (word 0) new_bytes
                                       else asm_state_regs (t1:(A)asm_state) n)) t1)`;
       `machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config) 0 (index,new_bytes,ms1)`;
       `p:A word`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `index:num`;
          `new_bytes:byte list`; `ms1:B`] oracle_tie_ffi_next) THEN
        EXISTS_TAC `new_ffi:(FFI)ffi_state` THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        USE_THEN "s'" SUBST1_TAC THEN REWRITE_TAC LTTP3AUX_RECS;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC LTTP3AUX_RECS THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`;
          `labs:(num spt)spt`; `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`;
          `t1:(A)asm_state`; `ms1:B`] LTTP3AUX_state_rel_share_mem) THEN
        USE_THEN "s'" SUBST1_TAC THEN
        REWRITE_TAC((record_info "asm_state").ri_accfupds :: LTTP3AUX_RECS) THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [REWRITE_TAC[call_FFI_rel_def] THEN
          MAP_EVERY EXISTS_TAC [`SharedMem MappedRead`; `[nb:byte]`;
            `word_to_bytes (word_add (w0:A word) off) F`; `new_bytes:byte list`] THEN
          USE_THEN "rw" (ACCEPT_TAC o CONJUNCT1);
          X_GEN_TAC `q:num` THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
          ASM_CASES_TAC `q:num = r` THENL
           [ASM_REWRITE_TAC[word_loc_val_def];
            SUBGOAL_THEN `~(r:num = q)` ASSUME_TAC THENL
             [UNDISCH_TAC `~(q:num = r)` THEN MESON_TAC[]; ASM_REWRITE_TAC[]]];
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    USE_THEN "s'" SUBST1_TAC THEN REWRITE_TAC LTTP3AUX_RECS THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `ms2:B`)) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `ms2:B`] THEN
    USE_THEN "step" (fun th -> REWRITE_TAC[th]) THEN FIRST_ASSUM ACCEPT_TAC;
    (* MappedWrite *)
    USE_THEN "rw" (X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s'")))) THEN
    SUBGOAL_THEN `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r =
                  (w:A word)` ASSUME_TAC THENL
     [USE_THEN "regs" (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "word_loc_val" with Failure _ -> false))
          (concl th))) THEN
      REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) r = wl_Word (w:A word)`;
                  word_loc_val_def; option_INJ] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    USE_THEN "rel_write" MP_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r = (w:A word)`] THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `!k. target_evaluate (mc_conf:(A,B,C)machine_config)
          (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)) (lab_state_clock s1 + k) ms1 =
        target_evaluate (machine_config_ffi_interfer_fupd
            (K (shift_seq 1 (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config)))) mc_conf)
          new_ffi (lab_state_clock s1 - 1 + k)
          (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms1))` (LABEL_TAC "step") THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
        `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) + k`; `ms1:B`; `index:num`;
        `MappedWrite`; `nb:byte`; `r0:num`; `off:A word`; `r:num`;
        `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list)))`] LTTP3AUX_target_evaluate_SharedMem) THEN
      USE_THEN "pc" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config))
                    ms1 r0 = w0`; distinctness "shmem_op"] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF; ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r = (w:A word)`] THEN
      FIRST_ASSUM(fun th -> if LTTP3AUX_LHS_IS "call_FFI" th then REWRITE_TAC[th]
                            else NO_TAC) THEN
      CASE_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `next_interference (mc_conf:(A,B,C)machine_config)
          (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)) ms1 =
        SOME (FfiApp index new_bytes ms1
                (machine_config_ffi_interfer mc_conf 0 (index,new_bytes,ms1)),
              machine_config_ffi_interfer_fupd
            (K (shift_seq 1 (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config)))) mc_conf,
              new_ffi)` ASSUME_TAC THENL
     [MATCH_MP_TAC(LTTP3AUX_INSTN [("op",`MappedWrite`); ("nb",`nb:byte`); ("r",`r0:num`);
         ("off",`off:A word`); ("reg",`r:num`); ("pc'",`word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list)))`)] next_interference_SharedMem) THEN
      USE_THEN "pc" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config))
                    ms1 r0 = w0`; ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r = (w:A word)`; LET_DEF; LET_END_DEF;
        ASSUME `EL index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
                SharedMem MappedWrite`; distinctness "shmem_op"] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "IH" (MP_TAC o SPECL [`a1:byte list`; `a2:num`; `m:memop`; `r:num`;
       `Addr r0 off:(A)addr`; `new_ffi:(FFI)ffi_state`; `new_bytes:byte list`;
       `s':(A,lab_to_target_config,FFI)lab_state`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:machine_result`; `machine_config_ffi_interfer_fupd
            (K (shift_seq 1 (machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config)))) mc_conf`;
       `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
       `asm_state_pc_fupd (K (word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list))))) (t1:(A)asm_state)`;
       `machine_config_ffi_interfer (mc_conf:(A,B,C)machine_config) 0 (index,new_bytes,ms1)`;
       `p:A word`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `index:num`;
          `new_bytes:byte list`; `ms1:B`] oracle_tie_ffi_next) THEN
        EXISTS_TAC `new_ffi:(FFI)ffi_state` THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        USE_THEN "s'" SUBST1_TAC THEN
        REWRITE_TAC(inc_pc_def :: lab_dec_clock_def :: LTTP3AUX_RECS);
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC LTTP3AUX_RECS THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`;
          `labs:(num spt)spt`; `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`;
          `t1:(A)asm_state`; `ms1:B`] LTTP3AUX_state_rel_share_mem) THEN
        USE_THEN "s'" SUBST1_TAC THEN
        REWRITE_TAC((record_info "asm_state").ri_accfupds :: inc_pc_def :: lab_dec_clock_def ::
                    LTTP3AUX_RECS) THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [REWRITE_TAC[call_FFI_rel_def] THEN
          MAP_EVERY EXISTS_TAC [`SharedMem MappedWrite`; `[nb:byte]`;
            `APPEND (if (nb:byte) = word 0 then word_to_bytes (w:A word) F
                     else word_to_bytes_aux (val nb) w F)
                    (word_to_bytes (word_add (w0:A word) off) F)`; `new_bytes:byte list`] THEN
          FIRST_ASSUM ACCEPT_TAC;
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    USE_THEN "s'" SUBST1_TAC THEN REWRITE_TAC(inc_pc_def :: lab_dec_clock_def :: LTTP3AUX_RECS) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `ms2:B`)) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `ms2:B`] THEN
    USE_THEN "step" (fun th -> REWRITE_TAC[th]) THEN FIRST_ASSUM ACCEPT_TAC]);;
(* HOL4 line 7829, Resume compile_correct[ShareMemOp]: the access ends the run *)
let LTTP3AUX_cc_ShareMem_final = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) m r ad a1 a2.
     asm_fetch s1 = SOME (Asm (ShareMem m r ad) a1 a2)
     ==> !outcome res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
       ~(lab_state_clock s1 = 0) /\
       share_mem_op m r ad s1 = SOME (FFI_final outcome,s2) /\
       res = target_Halt (FFI_outcome outcome) /\
       oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
       encoder_correct (machine_config_target mc_conf) /\
       lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
       ==> ?k ms2.
             target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
             (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  MP_TAC(ISPEC `get_memop_info m` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:shmem_op` (X_CHOOSE_THEN `nb:byte` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`m:memop`; `r:num`; `ad:(A)addr`; `s1:(A,lab_to_target_config,FFI)lab_state`;
     `outcome:final_event`; `s2:(A,lab_to_target_config,FFI)lab_state`; `name:shmem_op`;
     `nb:byte`] LTTP3AUX_share_mem_op_final) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num` (X_CHOOSE_THEN `off:A word` (X_CHOOSE_THEN `w0:A word`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "cond") (CONJUNCTS_THEN2 SUBST_ALL_TAC
         (LABEL_TAC "rw")))))))) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `m:memop`; `r:num`; `Addr r0 off:(A)addr`; `a1:byte list`; `a2:num`; `name:shmem_op`;
     `nb:byte`] LTTP3AUX_state_rel_share_mem_line) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bytes:byte list` (X_CHOOSE_THEN `index:num`
    (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))) THEN
  (* the registers of the access *)
  SUBGOAL_THEN `reg_ok r0 (target_config (machine_config_target (mc_conf:(A,B,C)machine_config))) /\
                reg_ok r (target_config (machine_config_target mc_conf))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `asm_ok (asm_Inst (Mem m r (Addr r0 off)))
                   (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))` THEN
    REWRITE_TAC[asm_ok_def; inst_ok_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. reg_ok x (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                    ==> target_get_reg (machine_config_target mc_conf) ms1 x =
                        asm_state_regs (t1:(A)asm_state) x` (LABEL_TAC "regs") THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def] o check (fun th ->
      LTTP3AUX_HEAD_IS "target_state_rel" th && can (find_term ((=) `ms1:B`)) (concl th))) THEN
    SIMP_TAC[reg_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r0 =
                w0` ASSUME_TAC THENL
   [USE_THEN "regs" (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `r0:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "word_loc_val" with Failure _ -> false))
        (concl th))) THEN
    REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) r0 = wl_Word w0`;
                word_loc_val_def; option_INJ] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  (* the access is aligned and in the shared addresses *)
  SUBGOAL_THEN `word_add w0 off IN
                  machine_config_shared_addresses (mc_conf:(A,B,C)machine_config) /\
                ((nb:byte) = word 0 ==> val (word_add (w0:A word) off) MOD (dimindex(:A) DIV 8) = 0)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[share_mem_domain_code_rel_def] o
      check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      MP_TAC(el 2 cs) THEN REWRITE_TAC[el 3 cs]) THEN
    USE_THEN "cond" MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the encoding of the access is in the target memory *)
  SUBGOAL_THEN `bytes_in_memory
      (word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list))))
      (asm_config_encode (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
         (asm_Inst (Mem m r (Addr r0 off))))
      (target_get_byte (machine_config_target mc_conf) ms1)
      (machine_config_prog_addresses mc_conf)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "machine_config_prog_addresses"
       with Failure _ -> false))) THEN
    MATCH_MP_TAC bytes_in_memory_eq_mem THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def] o check (fun th ->
        LTTP3AUX_HEAD_IS "target_state_rel" th && can (find_term ((=) `ms1:B`)) (concl th))) THEN
      STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "bytes_in_memory" th &&
        can (find_term ((=) `bytes:byte list`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "enc_with_nop")) THEN
      REWRITE_TAC[enc_with_nop_thm] THEN DISCH_THEN(X_CHOOSE_THEN `nn:num` SUBST1_TAC) THEN
      SIMP_TAC[bytes_in_memory_APPEND]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:memop`; `name:shmem_op`; `nb:byte`;
     `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list)))`;
     `r:num`; `Addr r0 off:(A)addr`;
     `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
        LENGTH (bytes:byte list)))`;
     `machine_config_target (mc_conf:(A,B,C)machine_config)`; `ms1:B`;
     `machine_config_prog_addresses (mc_conf:(A,B,C)machine_config)`] LTTP3AUX_valid_mapped) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 =
                word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list)))`
    (LABEL_TAC "pc") THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def] o check (fun th ->
      LTTP3AUX_HEAD_IS "target_state_rel" th && can (find_term ((=) `ms1:B`)) (concl th))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EL index (machine_config_ffi_entry_pcs (mc_conf:(A,B,C)machine_config)) =
                asm_state_pc (t1:(A)asm_state)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the two kinds of access *)
  MP_TAC(ISPEC `name:shmem_op` (nchotomy_of_type `:shmem_op`)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "shmem_op"]) THENL
   [(* MappedRead *)
    MAP_EVERY EXISTS_TAC [`0`; `ms1:B`] THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
      `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) + 0`; `ms1:B`; `index:num`;
      `MappedRead`; `nb:byte`; `r0:num`; `off:A word`; `r:num`;
      `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list)))`] LTTP3AUX_target_evaluate_SharedMem) THEN
    USE_THEN "pc" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config))
                    ms1 r0 = w0`; distinctness "shmem_op"] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    
    FIRST_ASSUM(fun th -> if LTTP3AUX_LHS_IS "call_FFI" th then REWRITE_TAC[th]
                          else NO_TAC) THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    (* MappedWrite *)
    USE_THEN "rw" (X_CHOOSE_THEN `w:A word` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r =
                  (w:A word)` ASSUME_TAC THENL
     [USE_THEN "regs" (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "word_loc_val" with Failure _ -> false))
          (concl th))) THEN
      REWRITE_TAC[ASSUME `lab_state_regs (s1:(A,lab_to_target_config,FFI)lab_state) r = wl_Word (w:A word)`;
                  word_loc_val_def; option_INJ] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`0`; `ms1:B`] THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
      `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) + 0`; `ms1:B`; `index:num`;
      `MappedWrite`; `nb:byte`; `r0:num`; `off:A word`; `r:num`;
      `word_add (p:A word) (word (pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0 (code2:((A)sec)list) +
           LENGTH (bytes:byte list)))`] LTTP3AUX_target_evaluate_SharedMem) THEN
    USE_THEN "pc" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config))
                    ms1 r0 = w0`; distinctness "shmem_op"] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; ASSUME `target_get_reg (machine_config_target (mc_conf:(A,B,C)machine_config)) ms1 r = (w:A word)`] THEN
    FIRST_ASSUM(fun th -> if LTTP3AUX_LHS_IS "call_FFI" th then REWRITE_TAC[th]
                          else NO_TAC) THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;
(* HOL4 line 8292, Resume compile_correct[CallFFI]: the ffi index of the call *)
let LTTP3AUX_callffi_index = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 name a1 a2 a3.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME (LabAsm (CallFFI name) a1 a2 a3)
     ==> ?i. mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
             get_ffi_index (machine_config_ffi_names mc_conf) (ExtCall name) < i /\
             get_ffi_index (TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names mc_conf)))
                              (machine_config_ffi_names mc_conf)) (ExtCall name) =
               get_ffi_index (machine_config_ffi_names mc_conf) (ExtCall name) /\
             EL (get_ffi_index (machine_config_ffi_names mc_conf) (ExtCall name))
                (machine_config_ffi_names mc_conf) = ExtCall name /\
             ALOOKUP (machine_config_mmio_info mc_conf)
               (get_ffi_index (machine_config_ffi_names mc_conf) (ExtCall name)) = NONE /\
             ~(word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf)
                                        (ExtCall name)) * ffi_offset)) IN
               machine_config_prog_addresses mc_conf) /\
             ~(word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf)
                                        (ExtCall name)) * ffi_offset)) =
               machine_config_halt_pc mc_conf) /\
             ~(word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf)
                                        (ExtCall name)) * ffi_offset)) =
               machine_config_ccache_pc mc_conf) /\
             find_index
               (word_sub p (word ((3 + get_ffi_index (machine_config_ffi_names mc_conf)
                                         (ExtCall name)) * ffi_offset)))
               (machine_config_ffi_entry_pcs mc_conf) 0 =
             SOME (get_ffi_index (machine_config_ffi_names mc_conf) (ExtCall name))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_state_rel_def] o
    check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (ExtCall name) (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP IMP_has_io_name o check (LTTP3AUX_LHS_IS "asm_fetch")) THEN
    DISCH_THEN(MP_TAC o MATCH_MP has_io_name_find_index) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` (MP_TAC o MATCH_MP find_index_is_MEM)) THEN
    FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "list_subset")) THEN
    REWRITE_TAC[list_subset_def; GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[THE_DEF] THEN
  SUBGOAL_THEN `get_ffi_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))
                  (ExtCall name) < i` ASSUME_TAC THENL
   [MATCH_MP_TAC ffi_name_NOT_Mapped THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ExtCall name`; `i:num`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "get_ffi_index" with Failure _ -> false))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP mmio_pcs_min_index_is_SOME) THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`; `ExtCall name`;
      `0`] find_index_MEM) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `find_index (ExtCall name)
        (TAKE i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))) 0 = SOME j`
      ASSUME_TAC THENL
     [MATCH_MP_TAC find_index_APPEND1 THEN
      EXISTS_TAC `DROP i (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))` THEN
      UNDISCH_TAC `get_ffi_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))
                    (ExtCall name) < i` THEN
      ASM_SIMP_TAC[TAKE_DROP; LENGTH_TAKE; ADD_CLAUSES; get_ffi_index_def; the_def];
      ASM_REWRITE_TAC[get_ffi_index_def; the_def]];
    MATCH_MP_TAC EL_get_ffi_index_MEM THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `get_ffi_index (machine_config_ffi_names
        (mc_conf:(A,B,C)machine_config)) (ExtCall name)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "ALOOKUP" with Failure _ -> false))
        (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "read_ffi_bytearrays"
                                     with Failure _ -> false)) (concl th)))) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT]]);;
(* one step of the target at an ffi entry point of an external call *)
let LTTP3AUX_target_evaluate_ExtCall = prove
 (`!(mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k ms index name bytes bytes2.
     ~(k = 0) /\
     ~(target_get_pc (machine_config_target mc) ms IN
       machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
     ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
     ~(target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc) /\
     find_index (target_get_pc (machine_config_target mc) ms)
       (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
     EL index (machine_config_ffi_names mc) = ExtCall name /\
     ALOOKUP (machine_config_mmio_info mc) index = NONE /\
     read_ffi_bytearrays mc ms = (SOME bytes,SOME bytes2)
     ==> target_evaluate mc ffi k ms =
         (match call_FFI ffi (ExtCall name) bytes bytes2 with
            FFI_final outcome -> (target_Halt (FFI_outcome outcome),ms,ffi)
          | FFI_return new_ffi new_bytes ->
              target_evaluate
                (machine_config_ffi_interfer_fupd
                   (K (shift_seq 1 (machine_config_ffi_interfer mc))) mc)
                new_ffi (k - 1)
                (machine_config_ffi_interfer mc 0 (index,new_bytes,ms)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [target_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN CASE_REWRITE_TAC[apply_oracle_def]);;
(* the jump of a CallFFI line to the ffi entry point of its name *)
let LTTP3AUX_callffi_jump = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 (ffi:(FFI)ffi_state) name a1 a2 a3.
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME (LabAsm (CallFFI name) a1 a2 a3)
     ==> ?l ms2. ~(l = 0) /\
           (!k. target_evaluate mc_conf ffi (k + l) ms1 =
                target_evaluate (shift_interfer l mc_conf) ffi k ms2) /\
           (!k. find_next_interference mc_conf ffi (k + l) ms1 =
                find_next_interference (shift_interfer l mc_conf) ffi k ms2) /\
           target_state_rel (machine_config_target mc_conf)
             (asm_state_pc_fupd
                (K (word_sub p (word ((3 + get_ffi_index
                      (TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names mc_conf)))
                         (machine_config_ffi_names mc_conf)) (ExtCall name)) * ffi_offset))))
                t1) ms2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `name:mlstring`; `a1:A word`; `a2:byte list`; `a3:num`]
    IMP_bytes_in_memory_CallFFI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `enc:byte list`
                                               with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `tt:A word`
                                               with Failure _ -> false)) THEN
  ABBREV_TAC `jj = asm_Jump (word_sub (word 0)
     (word (pv + (3 + get_ffi_index ffis (ExtCall name)) * ffi_offset))):(A)asm` THEN
  SUBGOAL_THEN `asm jj (word_add (word_add p (word pv))
                   (word (LENGTH (asm_config_encode
                      (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                      jj)))) t1 =
                asm_upd_pc (word_sub p (word ((3 + get_ffi_index ffis (ExtCall name)) *
                  ffi_offset))) (t1:(A)asm_state)`
    (LABEL_TAC "asmeq") THENL
   [EXPAND_TAC "jj" THEN ASM_REWRITE_TAC[asm_def; jump_to_offset_def] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `ffi:(FFI)ffi_state`; `jj:(A)asm`] asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
        `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
        `LabAsm (CallFFI name) a1 a2 a3:(A)line`] LTTP3AUX_fetch_disjoint) THEN
      ASM_REWRITE_TAC[distinctness "line"] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC ffi_entry_pcs_disjoint_LENGTH_shorter THEN
      EXISTS_TAC `LENGTH (line_bytes (j:(A)line))` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `line_similar (LabAsm (CallFFI name) a1 a2 a3) (j:(A)line)` THEN
      UNDISCH_TAC `line_ok (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
        labs ffis pv (j:(A)line)` THEN
      CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
      DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "line_ok")) THEN
      REWRITE_TAC[line_ok_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_enc_with_nop_LENGTH) THEN
      EXPAND_TAC "jj" THEN REWRITE_TAC[];
      USE_THEN "asmeq" SUBST1_TAC THEN
      REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `ms2:B`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
    can (find_term ((=) `ms2:B`)) (concl th))) THEN
  USE_THEN "asmeq" SUBST1_TAC THEN REWRITE_TAC[asm_upd_pc_def]);;
(* the state relation after an ffi call that returns: the general form *)
let LTTP3AUX_state_rel_ffi_return = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 S t2 ms2.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     lab_state_mem_domain S = lab_state_mem_domain s1 /\
     lab_state_shared_mem_domain S = lab_state_shared_mem_domain s1 /\
     lab_state_be S = lab_state_be s1 /\ lab_state_code S = lab_state_code s1 /\
     lab_state_compile S = lab_state_compile s1 /\
     lab_state_compile_oracle S = lab_state_compile_oracle s1 /\
     lab_state_code_buffer S = lab_state_code_buffer s1 /\
     lab_state_failed S = lab_state_failed s1 /\
     lab_state_ptr_reg S = lab_state_ptr_reg s1 /\
     lab_state_len_reg S = lab_state_len_reg s1 /\
     lab_state_ptr2_reg S = lab_state_ptr2_reg s1 /\
     lab_state_len2_reg S = lab_state_len2_reg s1 /\
     lab_state_link_reg S = lab_state_link_reg s1 /\
     call_FFI_rel (lab_state_ffi s1) (lab_state_ffi S) /\
     (!r. lab_state_fp_regs S r = asm_state_fp_regs t2 r) /\
     (!r. word_loc_val p labs (lab_state_regs S r) = SOME (asm_state_regs t2 r)) /\
     (!a. byte_align a IN lab_state_mem_domain s1
          ==> word_loc_val_byte p labs (lab_state_mem S) a (lab_state_be s1) =
              SOME (asm_state_mem t2 a)) /\
     bytes_in_mem p (prog_to_bytes code2) (asm_state_mem t2) (asm_state_mem_domain t1)
       (lab_state_mem_domain s1) /\
     bytes_in_mem (buffer_position (lab_state_code_buffer s1))
       (buffer_buffer (lab_state_code_buffer s1)) (asm_state_mem t2)
       (asm_state_mem_domain t1) (lab_state_mem_domain s1) /\
     asm_state_mem_domain t2 = asm_state_mem_domain t1 /\
     asm_state_be t2 = asm_state_be t1 /\ asm_state_align t2 = asm_state_align t1 /\
     asm_state_lr t2 = asm_state_lr t1 /\ asm_state_failed t2 = asm_state_failed t1 /\
     asm_state_pc t2 = word_add p (word (pos_val (lab_state_pc S) 0 code2)) /\
     target_state_rel (machine_config_target mc_conf) t2 ms2
     ==> lab_to_targetProof_state_rel
           (machine_config_ffi_interfer_fupd
              (K (shift_seq 1 (machine_config_ffi_interfer mc_conf))) mc_conf,code2,labs,p)
           S t2 ms2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (fun (asl,w as g) ->
     let S = `S:(A,lab_to_target_config,FFI)lab_state` and t2 = `t2:(A)asm_state` in
     let flds = filter (fun th -> is_eq(concl th) &&
                  (let l = lhs(concl th) in is_comb l && (rand l = S || rand l = t2) &&
                   not (can (find_term (fun t -> try fst(dest_const t) = "lab_state_pc"
                                                  with Failure _ -> false)) l)))
                (map snd asl) in
     REWRITE_TAC(flds @ (record_info "machine_config").ri_accfupds :: K_THM ::
                 read_ffi_bytearrays_ffi_interfer :: []) g) THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY X_GEN_TAC [`ms:B`; `k:num`; `index:num`; `nbytes:byte list`; `tt:(A)asm_state`;
      `bytes:byte list`; `bytes2:byte list`; `st:(FFI)ffi_state`; `nst:(FFI)ffi_state`;
      `i:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ms:B`; `k + 1`; `index:num`; `nbytes:byte list`;
      `tt:(A)asm_state`; `bytes:byte list`; `bytes2:byte list`; `st:(FFI)ffi_state`;
      `nst:(FFI)ffi_state`; `i:num`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "read_ffi_bytearrays"
                                 with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[shift_seq_def] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC RTC_TRANS THEN
      EXISTS_TAC `lab_state_ffi (S:(A,lab_to_target_config,FFI)lab_state)` THEN
      ASM_SIMP_TAC[RTC_INC];
      REWRITE_TAC[]];
    X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A word` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "word_loc_val_byte"
                               with Failure _ -> false)) (concl th) &&
      can (find_term ((=) `S:(A,lab_to_target_config,FFI)lab_state`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A word` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "word_loc_val_byte"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "share_mem_state_rel")) THEN
    REWRITE_TAC[share_mem_state_rel_def; shift_seq_def] THEN
    REWRITE_TAC[(record_info "machine_config").ri_accfupds; K_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MAP_EVERY X_GEN_TAC [`ms:B`; `k:num`; `index:num`; `nbytes:byte list`; `tt:(A)asm_state`;
      `nb:byte`; `ad:num`; `offs:A word`; `re:num`; `pc':A word`; `ad':A word`;
      `st:(FFI)ffi_state`; `nst:(FFI)ffi_state`; `i:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ms:B`; `k + 1`; `index:num`; `nbytes:byte list`;
      `tt:(A)asm_state`; `nb:byte`; `ad:num`; `offs:A word`; `re:num`; `pc':A word`;
      `ad':A word`; `st:(FFI)ffi_state`; `nst:(FFI)ffi_state`; `i:num`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "is_valid_mapped_read"
                                 with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC RTC_TRANS THEN
      EXISTS_TAC `lab_state_ffi (S:(A,lab_to_target_config,FFI)lab_state)` THEN
      ASM_SIMP_TAC[RTC_INC];
      REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "share_mem_domain_code_rel")) THEN
    REWRITE_TAC[share_mem_domain_code_rel_def] THEN
    REWRITE_TAC[(record_info "machine_config").ri_accfupds; K_THM]]);;
(* the target value of a register that holds a word *)
let LTTP3AUX_state_rel_Word = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 r v.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     lab_state_regs s1 r = wl_Word v
     ==> asm_state_regs t1 r = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "word_loc_val" with Failure _ -> false))
      (concl th))) THEN
  ASM_REWRITE_TAC[word_loc_val_def; option_INJ] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* the target registers at a machine state related to t1 up to its pc *)
let LTTP3AUX_state_rel_pc_regs = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 pc ms2 r v.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf) (asm_state_pc_fupd (K pc) t1) ms2 /\
     reg_ok r (target_config (machine_config_target mc_conf)) /\
     lab_state_regs s1 r = wl_Word v
     ==> target_get_reg (machine_config_target mc_conf) ms2 r = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `r:num`; `v:A word`] LTTP3AUX_state_rel_Word) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[target_state_rel_def; (record_info "asm_state").ri_accfupds; K_THM] o
    check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
                     can (find_term ((=) `ms2:B`)) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[reg_ok_def]) THEN ASM_REWRITE_TAC[]);;

(* the ffi byte arrays at the ffi entry point of a CallFFI line *)
let LTTP3AUX_callffi_read_ffi = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 pc ms2 w w2 w3 w4 bytes bytes2.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     target_state_rel (machine_config_target mc_conf) (asm_state_pc_fupd (K pc) t1) ms2 /\
     lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w /\
     lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w2 /\
     lab_state_regs s1 (lab_state_len2_reg s1) = wl_Word w3 /\
     lab_state_regs s1 (lab_state_ptr2_reg s1) = wl_Word w4 /\
     read_bytearray w2 (val w)
       (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME bytes /\
     read_bytearray w4 (val w3)
       (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME bytes2
     ==> read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  REWRITE_TAC[read_ffi_bytearrays_def; read_ffi_bytearray_def; PAIR_EQ] THEN
  SUBGOAL_THEN `(\a. if a IN machine_config_prog_addresses (mc_conf:(A,B,C)machine_config)
                     then SOME (target_get_byte (machine_config_target mc_conf) ms2 a)
                     else NONE) =
                (\a. if a IN machine_config_prog_addresses mc_conf
                     then SOME (asm_state_mem (t1:(A)asm_state) a) else NONE)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:A word` THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A word` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      REWRITE_RULE[target_state_rel_def; (record_info "asm_state").ri_accfupds; K_THM] o
      check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
                       can (find_term ((=) `ms2:B`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY (fun f -> FIRST_ASSUM(fun th ->
      if is_eq(concl th) && (try fst(dest_const(rator(lhs(concl th)))) = f
                             with Failure _ -> false)
      then REWRITE_TAC[th] else NO_TAC))
    ["machine_config_ptr_reg"; "machine_config_len_reg"; "machine_config_ptr2_reg";
     "machine_config_len2_reg"] THEN
  MAP_EVERY (fun (r,v) ->
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
       `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
       `pc:A word`; `ms2:B`; r; v] LTTP3AUX_state_rel_pc_regs) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                    DISCH_THEN(fun th -> REWRITE_TAC[th])])
   [`lab_state_len_reg (s1:(A,lab_to_target_config,FFI)lab_state)`,`w:A word`;
    `lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state)`,`w2:A word`;
    `lab_state_len2_reg (s1:(A,lab_to_target_config,FFI)lab_state)`,`w3:A word`;
    `lab_state_ptr2_reg (s1:(A,lab_to_target_config,FFI)lab_state)`,`w4:A word`] THEN
  CONJ_TAC THEN MATCH_MP_TAC read_bytearray_state_rel THEN
  MAP_EVERY EXISTS_TAC [`code2:((A)sec)list`; `labs:(num spt)spt`; `p:A word`;
    `s1:(A,lab_to_target_config,FFI)lab_state`; `ms1:B`] THEN
  ASM_REWRITE_TAC[]);;
(* the target state after the ffi call of a CallFFI line *)
let LTTP3AUX_callffi_target_rel = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 l ms2 ffi_index idx i w4 n1 n2 bytes bytes2 new_pc new_ffi
     new_bytes.
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2) /\
     target_state_rel (machine_config_target mc_conf)
       (asm_state_pc_fupd (K (word_sub p (word ((3 + idx) * ffi_offset)))) t1) ms2 /\
     mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\ idx < i /\
     ~(word_sub p (word ((3 + idx) * ffi_offset)) IN machine_config_prog_addresses mc_conf) /\
     ~(word_sub p (word ((3 + idx) * ffi_offset)) = machine_config_halt_pc mc_conf) /\
     ~(word_sub p (word ((3 + idx) * ffi_offset)) = machine_config_ccache_pc mc_conf) /\
     find_index (word_sub p (word ((3 + idx) * ffi_offset)))
       (machine_config_ffi_entry_pcs mc_conf) 0 = SOME idx /\
     EL idx (machine_config_ffi_names mc_conf) = ExtCall ffi_index /\
     ALOOKUP (machine_config_mmio_info mc_conf) idx = NONE /\
     read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
     call_FFI (lab_state_ffi s1) (ExtCall ffi_index) bytes bytes2 =
       FFI_return new_ffi new_bytes /\
     lab_state_regs s1 (lab_state_ptr2_reg s1) = wl_Word w4 /\
     lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
     loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc
     ==> target_state_rel (machine_config_target mc_conf)
           (asm_state_pc_fupd (K (word_add p (word (pos_val new_pc 0 code2))))
           (asm_state_mem_fupd (K (asm_write_bytearray w4 new_bytes (asm_state_mem t1)))
           (asm_state_regs_fupd
              (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                        (asm_state_regs t1 a) I))
           (asm_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n)) t1))))
           (machine_config_ffi_interfer mc_conf 0 (idx,new_bytes,ms2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  SUBGOAL_THEN `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms2 =
                word_sub p (word ((3 + idx) * ffi_offset))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def;
      (record_info "asm_state").ri_accfupds; K_THM] o
      check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
                       can (find_term ((=) `ms2:B`)) (concl th))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
    ALL_TAC] THEN
  (* the registers after the call are those of the oracle *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `ms1:B`;
     `s1:(A,lab_to_target_config,FFI)lab_state`; `ms2:B`; `l:num`; `idx:num`;
     `ffi_index:mlstring`; `bytes:byte list`; `bytes2:byte list`; `new_ffi:(FFI)ffi_state`;
     `new_bytes:byte list`; `t1:(A)asm_state`] oracle_tie_ExtCall_residues) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; ASSUME `target_get_pc (machine_config_target
       (mc_conf:(A,B,C)machine_config)) ms2 = word_sub p (word ((3 + idx) * ffi_offset))`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "find_next_interference"
                               with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[shift_interfer_def];
    DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[th]))] THEN
  (* the relation that state_rel gives for the call *)
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_state_rel_def] o
    check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN
  DISCH_THEN(MP_TAC o SPECL [`ms2:B`; `0`; `idx:num`; `new_bytes:byte list`; `t1:(A)asm_state`;
    `bytes:byte list`; `bytes2:byte list`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
    `new_ffi:(FFI)ffi_state`; `i:num`] o
    find (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "read_ffi_bytearrays"
                               with Failure _ -> false)) (concl th)) o CONJUNCTS) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_link_reg (s1:(A,lab_to_target_config,FFI)lab_state)`; `n1:num`; `n2:num`;
     `new_pc:num`] LTTP3AUX_state_rel_Loc) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_ptr2_reg (s1:(A,lab_to_target_config,FFI)lab_state)`; `w4:A word`]
    LTTP3AUX_state_rel_Word) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RTC_REFL] THEN
    MATCH_MP_TAC LTTP3AUX_state_rel_aligned_pos_val THEN
    MAP_EVERY EXISTS_TAC [`labs:(num spt)spt`; `s1:(A,lab_to_target_config,FFI)lab_state`;
      `t1:(A)asm_state`; `ms1:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[target_state_rel_def; (record_info "asm_state").ri_accfupds; K_THM]);;
(* the memory facts of the state relation *)
let LTTP3AUX_state_rel_mem_facts = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> (!a. byte_align a IN lab_state_mem_domain s1
              ==> a IN asm_state_mem_domain t1 /\ a IN lab_state_mem_domain s1 /\
                  word_loc_val_byte p labs (lab_state_mem s1) a (lab_state_be s1) =
                    SOME (asm_state_mem t1 a)) /\
         (lab_state_be s1 <=>
          asm_config_big_endian (target_config (machine_config_target mc_conf))) /\
         bytes_in_mem (buffer_position (lab_state_code_buffer s1))
           (buffer_buffer (lab_state_code_buffer s1)) (asm_state_mem t1)
           (asm_state_mem_domain t1) (lab_state_mem_domain s1)`,
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;
(* HOL4 line 8292, Resume compile_correct[CallFFI]: the call returns *)
let LTTP3AUX_cc_CallFFI = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) ffi_index a1 a2 a3 w w2 w3 w4 n1 n2 bytes bytes2
     new_pc new_ffi new_bytes res (mc_conf:(A,B,C)machine_config) s2 code2 labs
     (t1:(A)asm_state) ms1 p.
     (!a1 a2 a3 w2 w w3 n1 n2 bytes bytes2 w4 new_bytes new_ffi ffi_index new_pc.
        ~(lab_state_clock s1 = 0) /\
        asm_fetch s1 = SOME (LabAsm (CallFFI ffi_index) a1 a2 a3) /\
        lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w /\
        lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w2 /\
        lab_state_regs s1 (lab_state_len2_reg s1) = wl_Word w3 /\
        lab_state_regs s1 (lab_state_ptr2_reg s1) = wl_Word w4 /\
        lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
        read_bytearray w2 (val w)
          (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
          SOME bytes /\
        read_bytearray w4 (val w3)
          (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
          SOME bytes2 /\
        loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
        call_FFI (lab_state_ffi s1) (ExtCall ffi_index) bytes bytes2 =
          FFI_return new_ffi new_bytes
        ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
              oracle_tie mc_conf ms1 (lab_state_mem_fupd
              (K (write_bytearray w4 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
                    (lab_state_be s1)))
            (lab_state_ffi_fupd (K new_ffi)
            (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s1)))
            (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s1)))
            (lab_state_regs_fupd
              (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                         (lab_state_regs s1 a) wl_Word))
            (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n))
            (lab_state_pc_fupd (K new_pc)
            (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))))))) /\
              lab_evaluate (lab_state_mem_fupd
              (K (write_bytearray w4 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
                    (lab_state_be s1)))
            (lab_state_ffi_fupd (K new_ffi)
            (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s1)))
            (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s1)))
            (lab_state_regs_fupd
              (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                         (lab_state_regs s1 a) wl_Word))
            (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n))
            (lab_state_pc_fupd (K new_pc)
            (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))))))) = (res,s2) /\
              ~(res = target_Error) /\
              encoder_correct (machine_config_target mc_conf) /\
              lab_to_targetProof_state_rel (mc_conf,code2,labs,p) (lab_state_mem_fupd
              (K (write_bytearray w4 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
                    (lab_state_be s1)))
            (lab_state_ffi_fupd (K new_ffi)
            (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s1)))
            (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s1)))
            (lab_state_regs_fupd
              (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                         (lab_state_regs s1 a) wl_Word))
            (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n))
            (lab_state_pc_fupd (K new_pc)
            (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))))))) t1 ms1
              ==> ?k ms2.
                    target_evaluate mc_conf (lab_state_ffi (lab_state_mem_fupd
              (K (write_bytearray w4 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
                    (lab_state_be s1)))
            (lab_state_ffi_fupd (K new_ffi)
            (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s1)))
            (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s1)))
            (lab_state_regs_fupd
              (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                         (lab_state_regs s1 a) wl_Word))
            (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n))
            (lab_state_pc_fupd (K new_pc)
            (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) (lab_state_clock (lab_state_mem_fupd
              (K (write_bytearray w4 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
                    (lab_state_be s1)))
            (lab_state_ffi_fupd (K new_ffi)
            (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s1)))
            (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s1)))
            (lab_state_regs_fupd
              (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                         (lab_state_regs s1 a) wl_Word))
            (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n))
            (lab_state_pc_fupd (K new_pc)
            (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))))))) + k) ms1 =
                    (res,ms2,lab_state_ffi s2)) /\
     ~(lab_state_clock s1 = 0) /\
        asm_fetch s1 = SOME (LabAsm (CallFFI ffi_index) a1 a2 a3) /\
        lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w /\
        lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w2 /\
        lab_state_regs s1 (lab_state_len2_reg s1) = wl_Word w3 /\
        lab_state_regs s1 (lab_state_ptr2_reg s1) = wl_Word w4 /\
        lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
        read_bytearray w2 (val w)
          (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
          SOME bytes /\
        read_bytearray w4 (val w3)
          (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
          SOME bytes2 /\
        loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
        call_FFI (lab_state_ffi s1) (ExtCall ffi_index) bytes bytes2 =
          FFI_return new_ffi new_bytes /\
     lab_evaluate (lab_state_mem_fupd
              (K (write_bytearray w4 new_bytes (lab_state_mem s1) (lab_state_mem_domain s1)
                    (lab_state_be s1)))
            (lab_state_ffi_fupd (K new_ffi)
            (lab_state_io_regs_fupd (K (shift_seq 1 (lab_state_io_regs s1)))
            (lab_state_io_fp_regs_fupd (K (shift_seq 1 (lab_state_io_fp_regs s1)))
            (lab_state_regs_fupd
              (K (\a. get_reg_value (lab_state_io_regs s1 0 (ExtCall ffi_index) a)
                         (lab_state_regs s1 a) wl_Word))
            (lab_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs s1 0 n))
            (lab_state_pc_fupd (K new_pc)
            (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))))))) = (res,s2) /\
     oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> ?k ms2.
           target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
           (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  (* the ffi index of the call *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `ffi_index:mlstring`; `a1:A word`;
     `a2:byte list`; `a3:num`] LTTP3AUX_callffi_index) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "take") STRIP_ASSUME_TAC)))) THEN
  (* the jump to the ffi entry point *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `ffi_index:mlstring`;
     `a1:A word`; `a2:byte list`; `a3:num`] LTTP3AUX_callffi_jump) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "take" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eval") (CONJUNCTS_THEN2 (LABEL_TAC "fni") ASSUME_TAC))))) THEN
  ABBREV_TAC `idx = get_ffi_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))
                      (ExtCall ffi_index)` THEN
  SUBGOAL_THEN `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms2 =
                word_sub p (word ((3 + idx) * ffi_offset))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def;
      (record_info "asm_state").ri_accfupds; K_THM] o
      check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
                       can (find_term ((=) `ms2:B`)) (concl th))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `word_sub (p:A word) (word ((3 + idx) * ffi_offset))`;
     `ms2:B`; `w:A word`; `w2:A word`; `w3:A word`; `w4:A word`; `bytes:byte list`;
     `bytes2:byte list`] LTTP3AUX_callffi_read_ffi) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  (* the facts of the ffi entry point in the shifted configuration *)
  SUBGOAL_THEN
   `~(target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2 IN
      machine_config_prog_addresses (shift_interfer l (mc_conf:(A,B,C)machine_config)) DIFF
      set_of_list (machine_config_ffi_entry_pcs (shift_interfer l (mc_conf:(A,B,C)machine_config)))) /\
    ~(target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2 = machine_config_halt_pc (shift_interfer l (mc_conf:(A,B,C)machine_config))) /\
    ~(target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2 = machine_config_ccache_pc (shift_interfer l (mc_conf:(A,B,C)machine_config))) /\
    find_index (target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2)
      (machine_config_ffi_entry_pcs (shift_interfer l (mc_conf:(A,B,C)machine_config))) 0 = SOME idx /\
    EL idx (machine_config_ffi_names (shift_interfer l (mc_conf:(A,B,C)machine_config))) = ExtCall ffi_index /\
    ALOOKUP (machine_config_mmio_info (shift_interfer l (mc_conf:(A,B,C)machine_config))) idx = NONE /\
    read_ffi_bytearrays (shift_interfer l (mc_conf:(A,B,C)machine_config)) ms2 = (SOME bytes,SOME bytes2)` (LABEL_TAC "entry") THENL
   [REWRITE_TAC[read_ffi_bytearrays_shift_interfer] THEN
    REWRITE_TAC(shift_interfer_def :: IN_DIFF :: LTTP3AUX_RECS) THEN
    REWRITE_TAC[ASSUME `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                  ms2 = word_sub p (word ((3 + idx) * ffi_offset))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the run of the target *)
  SUBGOAL_THEN `!k. target_evaluate (mc_conf:(A,B,C)machine_config) (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state))
        ((lab_state_clock s1 + k) + l) ms1 =
      target_evaluate (machine_config_ffi_interfer_fupd
         (K (shift_seq 1 (machine_config_ffi_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)))))
         (shift_interfer l mc_conf)) new_ffi (lab_state_clock s1 - 1 + k) (machine_config_ffi_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)) 0
         (idx,new_bytes,ms2))` (LABEL_TAC "step") THENL
   [GEN_TAC THEN USE_THEN "eval" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`shift_interfer l (mc_conf:(A,B,C)machine_config)`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) + k`; `ms2:B`; `idx:num`;
      `ffi_index:mlstring`; `bytes:byte list`; `bytes2:byte list`]
      LTTP3AUX_target_evaluate_ExtCall) THEN
    ANTS_TAC THENL
     [USE_THEN "entry" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(fun th -> if LTTP3AUX_LHS_IS "call_FFI" th then REWRITE_TAC[th]
                          else NO_TAC) THEN
    CASE_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the memory facts *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_mem_facts) THEN
  SUBGOAL_THEN `read_bytearray (w4:A word) (LENGTH (new_bytes:byte list))
       (mem_load_byte_aux (lab_state_mem (s1:(A,lab_to_target_config,FFI)lab_state)) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME bytes2` ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (new_bytes:byte list) = val (w3:A word)` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP call_FFI_LENGTH o check (LTTP3AUX_LHS_IS "call_FFI")) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP read_bytearray_LENGTH o check (fun th ->
        LTTP3AUX_LHS_IS "read_bytearray" th && can (find_term ((=) `w4:A word`)) (concl th))) THEN
      ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. byte_align a IN lab_state_mem_domain (s1:(A,lab_to_target_config,FFI)lab_state) ==> a IN lab_state_mem_domain s1`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "word_loc_val_byte"
                               with Failure _ -> false)) (concl th))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* the induction hypothesis *)
  USE_THEN "IH" (MP_TAC o SPECL [`a1:A word`; `a2:byte list`; `a3:num`; `w2:A word`; `w:A word`;
     `w3:A word`; `n1:num`; `n2:num`; `bytes:byte list`; `bytes2:byte list`; `w4:A word`;
     `new_bytes:byte list`; `new_ffi:(FFI)ffi_state`; `ffi_index:mlstring`; `new_pc:num`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:machine_result`; `machine_config_ffi_interfer_fupd
         (K (shift_seq 1 (machine_config_ffi_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)))))
         (shift_interfer l mc_conf)`;
     `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `asm_state_pc_fupd (K (word_add (p:A word) (word (pos_val new_pc 0 (code2:((A)sec)list)))))
         (asm_state_mem_fupd (K (asm_write_bytearray (w4:A word) new_bytes (asm_state_mem (t1:(A)asm_state))))
         (asm_state_regs_fupd
            (K (\a. get_reg_value (lab_state_io_regs (s1:(A,lab_to_target_config,FFI)lab_state) 0 (ExtCall ffi_index) a)
                      (asm_state_regs t1 a) I))
         (asm_state_fp_regs_fupd (K (\n. lab_state_io_fp_regs (s1:(A,lab_to_target_config,FFI)lab_state) 0 n)) t1)))`; `machine_config_ffi_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)) 0
         (idx,new_bytes,ms2)`; `p:A word`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [(* the oracle *)
      MATCH_MP_TAC(ISPECL [`shift_interfer l (mc_conf:(A,B,C)machine_config)`; `ms2:B`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `idx:num`; `new_bytes:byte list`; `ms2:B`]
        oracle_tie_ffi_next) THEN
      EXISTS_TAC `new_ffi:(FFI)ffi_state` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC oracle_tie_shift_interfer THEN EXISTS_TAC `ms1:B` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(LTTP3AUX_INSTN [("name",`ffi_index:mlstring`); ("bytes",`bytes:byte list`);
          ("bytes2",`bytes2:byte list`)] next_interference_ExtCall) THEN
        USE_THEN "entry" (fun th -> REWRITE_TAC[th]) THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC(shift_interfer_def :: LTTP3AUX_RECS) THEN FIRST_ASSUM ACCEPT_TAC;
      (* the state relation *)
      MATCH_MP_TAC(ISPECL [`shift_interfer l (mc_conf:(A,B,C)machine_config)`; `code2:((A)sec)list`; `labs:(num spt)spt`; `p:A word`;
        `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`] LTTP3AUX_state_rel_ffi_return) THEN
      REWRITE_TAC(shift_interfer_def :: (record_info "asm_state").ri_accfupds :: LTTP3AUX_RECS) THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [REWRITE_TAC[GSYM shift_interfer_def] THEN MATCH_MP_TAC state_rel_shift_interfer THEN
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[call_FFI_rel_def] THEN
        MAP_EVERY EXISTS_TAC [`ExtCall ffi_index`; `bytes:byte list`; `bytes2:byte list`;
          `new_bytes:byte list`] THEN FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `q:num` THEN
        STRUCT_CASES_TAC(ISPEC `lab_state_io_regs (s1:(A,lab_to_target_config,FFI)lab_state) 0 (ExtCall ffi_index) q`
          (cases "option")) THEN
        REWRITE_TAC[get_reg_value_def; word_loc_val_def; I_THM] THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`a:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `mc_conf:(A,B,C)machine_config`;
          `w4:A word`; `new_bytes:byte list`; `bytes2:byte list`; `p:A word`;
          `labs:(num spt)spt`] CallFFI_bytearray_lemma) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `a:A word` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "word_loc_val_byte"
                                   with Failure _ -> false)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhand(concl th) = `lab_state_be (s1:(A,lab_to_target_config,FFI)lab_state)`
          then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th else NO_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
        MP_TAC(ISPECL [`(s1:(A,lab_to_target_config,FFI)lab_state)`; `w4:A word`; `new_bytes:byte list`; `bytes2:byte list`;
          `p:A word`; `prog_to_bytes (code2:((A)sec)list)`; `t1:(A)asm_state`]
          bytes_in_mem_asm_write_bytearray) THEN
        ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPECL [`(s1:(A,lab_to_target_config,FFI)lab_state)`; `w4:A word`; `new_bytes:byte list`; `bytes2:byte list`;
          `buffer_position (lab_state_code_buffer (s1:(A,lab_to_target_config,FFI)lab_state))`;
          `buffer_buffer (lab_state_code_buffer (s1:(A,lab_to_target_config,FFI)lab_state))`; `t1:(A)asm_state`]
          bytes_in_mem_asm_write_bytearray) THEN
        ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`;
          `labs:(num spt)spt`; `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `l:num`; `ms2:B`;
          `ffi_index:mlstring`; `idx:num`; `i:num`; `w4:A word`; `n1:num`; `n2:num`;
          `bytes:byte list`; `bytes2:byte list`; `new_pc:num`; `new_ffi:(FFI)ffi_state`;
          `new_bytes:byte list`] LTTP3AUX_callffi_target_rel) THEN
        ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]];
    ALL_TAC] THEN
  REWRITE_TAC LTTP3AUX_RECS THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `ms3:B`)) THEN
  MAP_EVERY EXISTS_TAC [`k + l`; `ms3:B`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN USE_THEN "step" (fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM ACCEPT_TAC);;(* HOL4 line 8292, Resume compile_correct[CallFFI]: the call ends the run *)
let LTTP3AUX_cc_CallFFI_final = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) ffi_index a1 a2 a3 w w2 w3 w4 n1 n2 bytes bytes2
     new_pc outcome res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
     ~(lab_state_clock s1 = 0) /\
     asm_fetch s1 = SOME (LabAsm (CallFFI ffi_index) a1 a2 a3) /\
     lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w /\
     lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w2 /\
     lab_state_regs s1 (lab_state_len2_reg s1) = wl_Word w3 /\
     lab_state_regs s1 (lab_state_ptr2_reg s1) = wl_Word w4 /\
     lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
     read_bytearray w2 (val w)
       (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME bytes /\
     read_bytearray w4 (val w3)
       (mem_load_byte_aux (lab_state_mem s1) (lab_state_mem_domain s1) (lab_state_be s1)) =
       SOME bytes2 /\
     loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
     call_FFI (lab_state_ffi s1) (ExtCall ffi_index) bytes bytes2 = FFI_final outcome /\
     res = target_Halt (FFI_outcome outcome) /\ s2 = s1 /\
     oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> ?k ms2.
           target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
           (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  (* the ffi index of the call *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `ffi_index:mlstring`; `a1:A word`;
     `a2:byte list`; `a3:num`] LTTP3AUX_callffi_index) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "take") STRIP_ASSUME_TAC)))) THEN
  (* the jump to the ffi entry point *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `ffi_index:mlstring`;
     `a1:A word`; `a2:byte list`; `a3:num`] LTTP3AUX_callffi_jump) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "take" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eval") (CONJUNCTS_THEN2 (LABEL_TAC "fni") ASSUME_TAC))))) THEN
  ABBREV_TAC `idx = get_ffi_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))
                      (ExtCall ffi_index)` THEN
  SUBGOAL_THEN `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms2 =
                word_sub p (word ((3 + idx) * ffi_offset))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def;
      (record_info "asm_state").ri_accfupds; K_THM] o
      check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
                       can (find_term ((=) `ms2:B`)) (concl th))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `word_sub (p:A word) (word ((3 + idx) * ffi_offset))`;
     `ms2:B`; `w:A word`; `w2:A word`; `w3:A word`; `w4:A word`; `bytes:byte list`;
     `bytes2:byte list`] LTTP3AUX_callffi_read_ffi) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  (* the facts of the ffi entry point in the shifted configuration *)
  SUBGOAL_THEN
   `~(target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2 IN
      machine_config_prog_addresses (shift_interfer l (mc_conf:(A,B,C)machine_config)) DIFF
      set_of_list (machine_config_ffi_entry_pcs (shift_interfer l (mc_conf:(A,B,C)machine_config)))) /\
    ~(target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2 = machine_config_halt_pc (shift_interfer l (mc_conf:(A,B,C)machine_config))) /\
    ~(target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2 = machine_config_ccache_pc (shift_interfer l (mc_conf:(A,B,C)machine_config))) /\
    find_index (target_get_pc (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2)
      (machine_config_ffi_entry_pcs (shift_interfer l (mc_conf:(A,B,C)machine_config))) 0 = SOME idx /\
    EL idx (machine_config_ffi_names (shift_interfer l (mc_conf:(A,B,C)machine_config))) = ExtCall ffi_index /\
    ALOOKUP (machine_config_mmio_info (shift_interfer l (mc_conf:(A,B,C)machine_config))) idx = NONE /\
    read_ffi_bytearrays (shift_interfer l (mc_conf:(A,B,C)machine_config)) ms2 = (SOME bytes,SOME bytes2)` (LABEL_TAC "entry") THENL
   [REWRITE_TAC[read_ffi_bytearrays_shift_interfer] THEN
    REWRITE_TAC(shift_interfer_def :: IN_DIFF :: LTTP3AUX_RECS) THEN
    REWRITE_TAC[ASSUME `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                  ms2 = word_sub p (word ((3 + idx) * ffi_offset))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `ms2:B`] THEN
  USE_THEN "eval" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`shift_interfer l (mc_conf:(A,B,C)machine_config)`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state)`; `ms2:B`; `idx:num`;
    `ffi_index:mlstring`; `bytes:byte list`; `bytes2:byte list`]
    LTTP3AUX_target_evaluate_ExtCall) THEN
  ANTS_TAC THENL
   [USE_THEN "entry" (fun th -> REWRITE_TAC[th]) THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th -> if LTTP3AUX_LHS_IS "call_FFI" th then REWRITE_TAC[th]
                        else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;(* HOL4 line 8754, Resume compile_correct[Install]: the jump of an Install  *)
(* line to the code cache entry point                                         *)
let LTTP3AUX_install_jump = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 (ffi:(FFI)ffi_state) a1 a2 a3.
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME (LabAsm lab_Install a1 a2 a3)
     ==> ?l ms2. ~(l = 0) /\
           (!k. target_evaluate mc_conf ffi (k + l) ms1 =
                target_evaluate (shift_interfer l mc_conf) ffi k ms2) /\
           (!k. find_next_interference mc_conf ffi (k + l) ms1 =
                find_next_interference (shift_interfer l mc_conf) ffi k ms2) /\
           target_state_rel (machine_config_target mc_conf)
             (asm_state_pc_fupd (K (machine_config_ccache_pc mc_conf)) t1) ms2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  ABBREV_TAC `ffis = TAKE (THE (mmio_pcs_min_index
                       (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
                      (machine_config_ffi_names mc_conf)` THEN
  ABBREV_TAC `pv = pos_val (lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)) 0
                     (code2:((A)sec)list)` THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`;
     `mc_conf:(A,B,C)machine_config`; `labs:(num spt)spt`; `ffis:ffiname list`;
     `p:A word`; `t1:(A)asm_state`; `a1:A word`; `a2:byte list`; `a3:num`]
    IMP_bytes_in_memory_Install) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `enc:byte list`
                                               with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `tt:A word`
                                               with Failure _ -> false)) THEN
  ABBREV_TAC `jj = asm_Jump (word_sub (word 0) (word (pv + 2 * ffi_offset))):(A)asm` THEN
  SUBGOAL_THEN `asm jj (word_add (word_add p (word pv))
                   (word (LENGTH (asm_config_encode
                      (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
                      jj)))) t1 =
                asm_upd_pc (machine_config_ccache_pc mc_conf) (t1:(A)asm_state)`
    (LABEL_TAC "asmeq") THENL
   [EXPAND_TAC "jj" THEN ASM_REWRITE_TAC[asm_def; jump_to_offset_def] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) =
      `machine_config_ccache_pc (mc_conf:(A,B,C)machine_config)` with Failure _ -> false)) THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `t1:(A)asm_state`; `ms1:B`;
     `ffi:(FFI)ffi_state`; `jj:(A)asm`] asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[asm_step_def] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
        `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
        `LabAsm lab_Install a1 a2 a3:(A)line`] LTTP3AUX_fetch_disjoint) THEN
      ASM_REWRITE_TAC[distinctness "line"] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:(A)line` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC ffi_entry_pcs_disjoint_LENGTH_shorter THEN
      EXISTS_TAC `LENGTH (line_bytes (j:(A)line))` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `line_similar (LabAsm lab_Install a1 a2 a3) (j:(A)line)` THEN
      UNDISCH_TAC `line_ok (target_config (machine_config_target (mc_conf:(A,B,C)machine_config)))
        labs ffis pv (j:(A)line)` THEN
      CASES_ON `j:(A)line` THEN REWRITE_TAC[line_similar_def; line_bytes_def] THEN
      DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "line_ok")) THEN
      REWRITE_TAC[line_ok_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_enc_with_nop_LENGTH) THEN
      EXPAND_TAC "jj" THEN REWRITE_TAC[];
      USE_THEN "asmeq" SUBST1_TAC THEN
      REWRITE_TAC(asm_upd_pc_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`l:num`; `ms2:B`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
    can (find_term ((=) `ms2:B`)) (concl th))) THEN
  USE_THEN "asmeq" SUBST1_TAC THEN REWRITE_TAC[asm_upd_pc_def]);;
(* one step of the target at the code cache entry point *)
let LTTP3AUX_target_evaluate_ccache = prove
 (`!(mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k ms.
     ~(k = 0) /\
     ~(target_get_pc (machine_config_target mc) ms IN
       machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
     ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
     target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc
     ==> target_evaluate mc ffi k ms =
         target_evaluate
           (machine_config_ccache_interfer_fupd
              (K (shift_seq 1 (machine_config_ccache_interfer mc))) mc)
           ffi (k - 1)
           (machine_config_ccache_interfer mc 0
              (target_get_reg (machine_config_target mc) ms (machine_config_ptr_reg mc),
               target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc),ms))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [target_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[apply_oracle_def; LET_DEF; LET_END_DEF]);;
(* the code cache entry point is not the halt entry point *)
let LTTP3AUX_ccache_ne_halt = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> ~(machine_config_ccache_pc mc_conf = machine_config_halt_pc mc_conf)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) =
    `machine_config_halt_pc (mc_conf:(A,B,C)machine_config)` with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs(concl th) =
    `machine_config_ccache_pc (mc_conf:(A,B,C)machine_config)` with Failure _ -> false)) THEN
  REWRITE_TAC[ffi_offset_def; WORD_RULE
    `word_sub (p:A word) x = word_sub p y <=> x = y`] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "good_dimindex"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[n2w_11; dimword_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;
(* the target state after the code cache call of an Install line *)
let LTTP3AUX_install_target_rel = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 l ms2 w1 w2 n1 n2 new_pc.
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     oracle_tie mc_conf ms1 s1 /\
     (!k. find_next_interference mc_conf (lab_state_ffi s1) (k + l) ms1 =
          find_next_interference (shift_interfer l mc_conf) (lab_state_ffi s1) k ms2) /\
     target_state_rel (machine_config_target mc_conf)
       (asm_state_pc_fupd (K (machine_config_ccache_pc mc_conf)) t1) ms2 /\
     lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w1 /\
     lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w2 /\
     lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
     loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc
     ==> target_get_reg (machine_config_target mc_conf) ms2 (machine_config_ptr_reg mc_conf) =
           w1 /\
         target_get_reg (machine_config_target mc_conf) ms2 (machine_config_len_reg mc_conf) =
           w2 /\
         target_state_rel (machine_config_target mc_conf)
           (asm_state_regs_fupd
              (K ((lab_state_ptr_reg s1 =+ w1)
                  (\a. get_reg_value (lab_state_cc_regs s1 0 a) (asm_state_regs t1 a) I)))
           (asm_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
           (asm_state_pc_fupd (K (word_add p (word (pos_val new_pc 0 code2)))) t1)))
           (machine_config_ccache_interfer mc_conf 0 (w1,w2,ms2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LTTP3AUX_ccache_ne_halt) THEN
  SUBGOAL_THEN `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms2 =
                machine_config_ccache_pc mc_conf` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def;
      (record_info "asm_state").ri_accfupds; K_THM] o
      check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
                       can (find_term ((=) `ms2:B`)) (concl th))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
    ALL_TAC] THEN
  (* the registers of the call *)
  MAP_EVERY (fun f -> FIRST_ASSUM(fun th ->
      if is_eq(concl th) && (try fst(dest_const(rator(lhs(concl th)))) = f
                             with Failure _ -> false)
      then REWRITE_TAC[th] else NO_TAC))
    ["machine_config_ptr_reg"; "machine_config_len_reg"] THEN
  MAP_EVERY (fun (r,v) ->
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
       `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
       `machine_config_ccache_pc (mc_conf:(A,B,C)machine_config)`; `ms2:B`; r; v]
      LTTP3AUX_state_rel_pc_regs) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                    DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)])
   [`lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state)`,`w1:A word`;
    `lab_state_len_reg (s1:(A,lab_to_target_config,FFI)lab_state)`,`w2:A word`] THEN
  (* the registers after the call are those of the oracle *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `shift_interfer l (mc_conf:(A,B,C)machine_config)`;
     `ms1:B`; `s1:(A,lab_to_target_config,FFI)lab_state`; `ms2:B`; `l:num`;
     `t1:(A)asm_state`] oracle_tie_ccache_residues) THEN
  ANTS_TAC THENL
   [REWRITE_TAC(shift_interfer_def :: IN_DIFF :: LTTP3AUX_RECS) THEN
    REWRITE_TAC[ASSUME `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms2 =
                machine_config_ccache_pc mc_conf`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "find_next_interference"
                               with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[shift_interfer_def];
    ALL_TAC] THEN
  MAP_EVERY (fun f -> FIRST_ASSUM(fun th ->
      if is_eq(concl th) && (try fst(dest_const(rator(lhs(concl th)))) = f
                             with Failure _ -> false)
      then REWRITE_TAC[th] else NO_TAC))
    ["machine_config_ptr_reg"; "machine_config_len_reg"] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THEN
  (* the update of the pointer register does not change the regs *)
  SUBGOAL_THEN `!(f:num->A word).
      (lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state) =+ (w1:A word))
        (\a. if MEM a (machine_config_callee_saved_regs (mc_conf:(A,B,C)machine_config)) \/
                a = lab_state_ptr_reg s1 \/
                ~(a < asm_config_reg_count (target_config (machine_config_target mc_conf))) \/
                MEM a (asm_config_avoid_regs (target_config (machine_config_target mc_conf)))
             then asm_state_regs (t1:(A)asm_state) a else f a) =
      (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
              a = lab_state_ptr_reg s1 \/
              ~(a < asm_config_reg_count (target_config (machine_config_target mc_conf))) \/
              MEM a (asm_config_avoid_regs (target_config (machine_config_target mc_conf)))
           then asm_state_regs t1 a else f a)` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN X_GEN_TAC `a:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
       `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
       `lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state)`; `w1:A word`]
      LTTP3AUX_state_rel_Word) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the relation that state_rel gives for the call *)
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_state_rel_def] o
    check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN
  DISCH_THEN(MP_TAC o SPECL [`ms2:B`; `t1:(A)asm_state`; `0`; `w1:A word`; `w2:A word`] o
    find (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "machine_config_ccache_interfer"
                               with Failure _ -> false)) (concl th)) o CONJUNCTS) THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `s1:(A,lab_to_target_config,FFI)lab_state`; `t1:(A)asm_state`; `ms1:B`;
     `lab_state_link_reg (s1:(A,lab_to_target_config,FFI)lab_state)`; `n1:num`; `n2:num`;
     `new_pc:num`] LTTP3AUX_state_rel_Loc) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LTTP3AUX_state_rel_aligned_pos_val THEN
    MAP_EVERY EXISTS_TAC [`labs:(num spt)spt`; `s1:(A,lab_to_target_config,FFI)lab_state`;
      `t1:(A)asm_state`; `ms1:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[target_state_rel_def; (record_info "asm_state").ri_accfupds; K_THM]);;
(* the target code of an Install line is an Install line *)
let LTTP3AUX_install_code2 = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 a1 a2 a3.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME (LabAsm lab_Install a1 a2 a3)
     ==> ?b c d. asm_fetch_aux (lab_state_pc s1) code2 = SOME (LabAsm lab_Install b c d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  MP_TAC(ISPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`;
     `lab_state_code (s1:(A,lab_to_target_config,FFI)lab_state)`; `code2:((A)sec)list`]
    code_similar_IMP_asm_fetch_aux_line_similar) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `asm_fetch (s1:(A,lab_to_target_config,FFI)lab_state) =
               SOME (LabAsm lab_Install a1 a2 a3)` THEN
  REWRITE_TAC[asm_fetch_def] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[OPTREL_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:(A)line` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  STRUCT_CASES_TAC(ISPEC `j:(A)line` (cases "line")) THEN
  REWRITE_TAC[line_similar_def; option_INJ; injectivity "line"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;
(* the compilation of the code that an Install line installs *)
let LTTP3AUX_install_compile = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 a1 a2 a3 cfg new_code bytes.
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME (LabAsm lab_Install a1 a2 a3) /\
     lab_state_compile_oracle s1 0 = (cfg,new_code) /\
     lab_state_compile s1 cfg new_code =
       SOME (bytes,FST (shift_seq 1 (lab_state_compile_oracle s1) 0))
     ==> ?sec_list.
           bytes = prog_to_bytes sec_list /\
           mmio_pcs_min_index (machine_config_ffi_names mc_conf) =
             SOME (LENGTH (machine_config_ffi_names mc_conf)) /\
           no_share_mem_inst code2 /\ no_share_mem_inst new_code /\
           no_share_mem_inst sec_list /\
           lab_to_targetProof_good_code (target_config (machine_config_target mc_conf)) labs
             new_code /\
           list_subset (find_ffi_names new_code) (machine_config_ffi_names mc_conf) /\
           all_enc_ok (target_config (machine_config_target mc_conf))
             (lab_to_target_config_labels (FST (shift_seq 1 (lab_state_compile_oracle s1) 0)))
             (machine_config_ffi_names mc_conf) (LENGTH (prog_to_bytes code2)) sec_list /\
           code_similar new_code sec_list /\
           (has_odd_inst sec_list
            ==> asm_config_code_alignment (target_config (machine_config_target mc_conf)) = 0) /\
           (!l1 l2 x.
              lab_lookup l1 l2
                (lab_to_target_config_labels (FST (shift_seq 1 (lab_state_compile_oracle s1) 0))) =
                SOME x ==> EVEN x) /\
           (!l1 l2 x.
              lab_lookup l1 l2 labs = SOME x
              ==> lab_lookup l1 l2
                    (lab_to_target_config_labels
                       (FST (shift_seq 1 (lab_state_compile_oracle s1) 0))) = SOME x) /\
           (!l1 l2 x2.
              loc_to_pc l1 l2 new_code = SOME x2
              ==> lab_lookup l1 l2
                    (lab_to_target_config_labels
                       (FST (shift_seq 1 (lab_state_compile_oracle s1) 0))) =
                  SOME (pos_val x2 (LENGTH (prog_to_bytes code2)) sec_list)) /\
           lab_to_target_config_pos (FST (shift_seq 1 (lab_state_compile_oracle s1) 0)) =
             LENGTH (prog_to_bytes (APPEND code2 sec_list)) /\
           lab_to_target_config_ffi_names (FST (shift_seq 1 (lab_state_compile_oracle s1) 0)) =
             SOME (machine_config_ffi_names mc_conf)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `a1:A word`; `a2:byte list`; `a3:num`]
    LTTP3AUX_install_code2) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A word` (X_CHOOSE_THEN `c:byte list`
    (X_CHOOSE_THEN `d:num` ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_state_rel_def] o
    check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN STRIP_TAC THEN
  (* the target code has no shared memory lines *)
  SUBGOAL_THEN `no_share_mem_inst (code2:((A)sec)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `no_install_or_no_share_mem (code2:((A)sec)list)
                   (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))` THEN
    REWRITE_TAC[no_install_or_no_share_mem_def; lab_no_install_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `b:A word`; `c:byte list`; `d:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* all the ffi names are external calls *)
  MP_TAC(ISPECL [`machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`; `i:num`;
     `lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `code2:((A)sec)list`; `b:A word`; `c:byte list`; `d:num`]
    no_share_mem_lemma) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  (* the oracle at 0 *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "lab_state_compile_oracle"
                             with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if LTTP3AUX_HEAD_IS "lab_to_targetProof_good_code" th
                          then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the compilation *)
  UNDISCH_TAC `lab_state_compile (s1:(A,lab_to_target_config,FFI)lab_state) cfg new_code =
       SOME (bytes,FST (shift_seq 1 (lab_state_compile_oracle (s1:(A,lab_to_target_config,FFI)lab_state)) 0))` THEN
  ASM_REWRITE_TAC[compile_lab_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  TOP_CASE_TAC THEN TOP_CASE_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (ASSUME_TAC o SYM)) THEN
  EXISTS_TAC `x:((A)sec)list` THEN
  MP_TAC(ISPECL [`lab_to_target_config_init_clock cfg`;
    `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
    `LENGTH (prog_to_bytes (code2:((A)sec)list))`; `labs:(num spt)spt`;
    `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`; `new_code:((A)sec)list`;
    `x:((A)sec)list`; `y:(num spt)spt`] remove_labels_thm) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_good_code_def] o
      check (LTTP3AUX_HEAD_IS "lab_to_targetProof_good_code")) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`l1:num`; `l2:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l1:num`; `l2:num`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "EVEN"
                                               with Failure _ -> false)) (concl th) &&
      can (find_term ((=) `labs:(num spt)spt`)) (concl th))) THEN
    STRUCT_CASES_TAC(ISPEC `lab_lookup l1 l2 (labs:(num spt)spt)` (cases "option")) THEN
    REWRITE_TAC[OPTION_ALL_def; option_INJ] THEN MESON_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `no_share_mem_inst (x:((A)sec)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC code_similar_IMP_both_no_share_mem THEN
    EXISTS_TAC `new_code:((A)sec)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try LTTP3AUX_LHS_IS "get_shmem_info" th
                                           with Failure _ -> false)) THEN
  ASM_SIMP_TAC[no_share_mem_IMP_get_shmem_info; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try fst(dest_const(rator(lhs(concl th)))) = "FST"
                                                 with Failure _ -> false)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[(record_info "lab_to_target_config").ri_accfupds; K_THM; APPEND_NIL;
              prog_to_bytes_APPEND; LENGTH_APPEND] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;(* the values of word_loc_val only grow with the label map *)
let LTTP3AUX_word_loc_val_mono = prove
 (`!(p:A word) labs nlabs x v.
     (!l1 l2 y. lab_lookup l1 l2 labs = SOME y ==> lab_lookup l1 l2 nlabs = SOME y) /\
     word_loc_val p labs x = SOME v
     ==> word_loc_val p nlabs x = SOME v`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[word_loc_val_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC(ISPEC `lab_lookup a0 a1 (labs:(num spt)spt)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let LTTP3AUX_word_loc_val_byte_mono = prove
 (`!(p:A word) labs nlabs m a be v.
     (!l1 l2 y. lab_lookup l1 l2 labs = SOME y ==> lab_lookup l1 l2 nlabs = SOME y) /\
     word_loc_val_byte p labs m a be = SOME v
     ==> word_loc_val_byte p nlabs m a be = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_loc_val_byte_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC(ISPEC `word_loc_val (p:A word) labs ((m:A word->(A)word_loc) (byte_align a))`
    (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_loc_val (p:A word) nlabs ((m:A word->(A)word_loc) (byte_align a)) = SOME a'`
    SUBST1_TAC THENL
   [MATCH_MP_TAC LTTP3AUX_word_loc_val_mono THEN EXISTS_TAC `labs:(num spt)spt` THEN
    ASM_REWRITE_TAC[];
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

(* the ffi byte arrays do not depend on the code cache oracle *)
let LTTP3AUX_read_ffi_bytearrays_ccache = prove
 (`!(mc:(A,B,C)machine_config) f.
     read_ffi_bytearrays (machine_config_ccache_interfer_fupd f mc) = read_ffi_bytearrays mc`,
  REWRITE_TAC[FUN_EQ_THM; read_ffi_bytearrays_def; read_ffi_bytearray_def;
              (record_info "machine_config").ri_accfupds]);;

(* the facts of a buffer flush *)
let LTTP3AUX_buffer_flush = prove
 (`!(cb0:(A,8)buffer) w1 w2 bytes cb.
     buffer_flush cb0 w1 w2 = SOME (bytes,cb)
     ==> w1 = buffer_position cb0 /\ bytes = buffer_buffer cb0 /\
         buffer_position cb = word_add (buffer_position cb0) (word (LENGTH (buffer_buffer cb0))) /\
         buffer_buffer cb = [] /\ buffer_space_left cb = buffer_space_left cb0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[buffer_flush_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[(record_info "buffer").ri_accfupds; K_THM; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_RULE `word_mul (word 1) (x:A word) = x`]);;
(* the label positions of the code after an installation *)
let LTTP3AUX_install_loc_to_pc = prove
 (`!(c:(A)asm_config) labs nlabs ffis ffis2 (code1:((A)sec)list) code2 new_code sec_list
     l1 l2 x2.
     code_similar code1 code2 /\ ALL sec_labels_ok code2 /\
     all_enc_ok c labs ffis 0 code2 /\
     ALL sec_labels_ok new_code /\
     all_enc_ok c nlabs ffis2 (LENGTH (prog_to_bytes code2)) sec_list /\
     (!l1 l2 x2. loc_to_pc l1 l2 code1 = SOME x2
                 ==> lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2)) /\
     (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> lab_lookup l1 l2 nlabs = SOME x) /\
     (!l1 l2 x2. loc_to_pc l1 l2 new_code = SOME x2
                 ==> lab_lookup l1 l2 nlabs =
                     SOME (pos_val x2 (LENGTH (prog_to_bytes code2)) sec_list)) /\
     loc_to_pc l1 l2 (APPEND code1 new_code) = SOME x2
     ==> lab_lookup l1 l2 nlabs = SOME (pos_val x2 0 (APPEND code2 sec_list))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL sec_labels_ok (code1:((A)sec)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC code_similar_sec_labels_ok THEN EXISTS_TAC `code2:((A)sec)list` THEN
    ASM_SIMP_TAC[code_similar_sym];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP all_enc_ok_imp_sec_label_zero o
    check (fun th -> LTTP3AUX_HEAD_IS "all_enc_ok" th &&
                     can (find_term ((=) `sec_list:((A)sec)list`)) (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LENGTH_prog_to_bytes2 o
    check (fun th -> LTTP3AUX_HEAD_IS "all_enc_ok" th &&
                     can (find_term ((=) `code2:((A)sec)list`)) (concl th) &&
                     not (can (find_term ((=) `sec_list:((A)sec)list`)) (concl th)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP code_similar_len_no_lab o
    check (LTTP3AUX_HEAD_IS "code_similar")) THEN
  UNDISCH_TAC `loc_to_pc l1 l2 (APPEND (code1:((A)sec)list) new_code) = SOME x2` THEN
  ASM_SIMP_TAC[loc_to_pc_append; ALL_APPEND; pos_val_append] THEN
  MP_TAC(ISPEC `loc_to_pc l1 l2 (code1:((A)sec)list)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_INJ] THENL
   [ALL_TAC;
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `a <= SUM (MAP ((\xs. LENGTH (FILTER ((~) o is_Label) xs)) o Section_lines)
                    (code2:((A)sec)list))` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "MAP" with Failure _ -> false)) THEN
      MATCH_MP_TAC loc_to_pc_bound THEN
      MAP_EVERY EXISTS_TAC [`l1:num`; `l2:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `loc_to_pc l1 l2 (new_code:((A)sec)list)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l1:num`; `l2:num`; `a:num`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `new_code:((A)sec)list`)) (concl th) &&
    can (find_term ((=) `sec_list:((A)sec)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_INJ; ADD_SUB; ADD_CLAUSES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `a = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; pos_val_acc] THEN
  MATCH_MP_TAC pos_val_0 THEN
  MAP_EVERY EXISTS_TAC [`c:(A)asm_config`; `nlabs:(num spt)spt`; `ffis2:ffiname list`] THEN
  ASM_REWRITE_TAC[]);;(* the register relation after an installation *)
let LTTP3AUX_install_regs = prove
 (`!(p:A word) labs nlabs (s1:(A,lab_to_target_config,FFI)lab_state) (t1:(A)asm_state) k w1.
     (!r. word_loc_val p labs (lab_state_regs s1 r) = SOME (asm_state_regs t1 r)) /\
     (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> lab_lookup l1 l2 nlabs = SOME x) /\
     word_loc_val p nlabs (wl_Loc k 0) = SOME w1
     ==> !r. word_loc_val p nlabs
               ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                  (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)
                  r) =
             SOME ((lab_state_ptr_reg s1 =+ w1)
                     (\a. get_reg_value (lab_state_cc_regs s1 0 a) (asm_state_regs t1 a) I) r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN
  REWRITE_TAC[APPLY_UPDATE_THM] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lab_state_cc_regs (s1:(A,lab_to_target_config,FFI)lab_state) 0 r`
    (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[get_reg_value_def; word_loc_val_def; I_THM] THEN
  MATCH_MP_TAC LTTP3AUX_word_loc_val_mono THEN EXISTS_TAC `labs:(num spt)spt` THEN
  ASM_REWRITE_TAC[]);;
(* the shared memory relation of the code after an installation *)
let LTTP3AUX_install_share_mem_domain = prove
 (`!(mc_conf:(A,B,C)machine_config) f p code2 sec_list dom (cb0:(A,8)buffer) (c:(A)asm_config)
     labs ffis nlabs ffis2.
     share_mem_domain_code_rel mc_conf p code2 dom /\
     no_share_mem_inst (APPEND code2 sec_list) /\
     all_enc_ok c labs ffis 0 code2 /\
     all_enc_ok c nlabs ffis2 (LENGTH (prog_to_bytes code2)) sec_list /\
     buffer_position cb0 = word_add p (word (LENGTH (prog_to_bytes code2))) /\
     prog_to_bytes sec_list = buffer_buffer cb0 /\
     (!bn. bn < LENGTH (buffer_buffer cb0) + buffer_space_left cb0
           ==> ~MEM (word_add (buffer_position cb0) (word bn))
                    (machine_config_ffi_entry_pcs mc_conf))
     ==> share_mem_domain_code_rel (machine_config_ccache_interfer_fupd f mc_conf) p
           (APPEND code2 sec_list) dom`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[share_mem_domain_code_rel_def; (record_info "machine_config").ri_accfupds] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `no_share_mem_inst (APPEND (code2:((A)sec)list) sec_list)` THEN
    REWRITE_TAC[no_share_mem_inst_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`; `line:(A)line`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `pc < num_pcs (code2:((A)sec)list)` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`pc:num`; `line:(A)line`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "DISJOINT"
                                               with Failure _ -> false)) (concl th))) THEN
    UNDISCH_TAC `asm_fetch_aux pc (APPEND (code2:((A)sec)list) sec_list) = SOME line` THEN
    ASM_SIMP_TAC[asm_fetch_aux_APPEND1; pos_val_APPEND1];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `pc':num` SUBST_ALL_TAC o
    REWRITE_RULE[NOT_LT; LE_EXISTS]) THEN
  SUBGOAL_THEN `num_pcs (code2:((A)sec)list) + pc' = pc' + num_pcs code2` SUBST_ALL_TAC
  THENL [ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `asm_fetch_aux (pc' + num_pcs code2) (APPEND (code2:((A)sec)list) sec_list) =
               SOME line` THEN
  REWRITE_TAC[asm_fetch_aux_APPEND2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `labs:(num spt)spt`; `ffis:ffiname list`; `0`;
     `code2:((A)sec)list`; `pc':num`; `sec_list:((A)sec)list`] pos_val_APPEND2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`pc':num`; `0`; `sec_list:((A)sec)list`;
     `LENGTH (prog_to_bytes (code2:((A)sec)list))`; `c:(A)asm_config`; `nlabs:(num spt)spt`;
     `ffis2:ffiname list`; `line:(A)line`] asm_fetch_aux_pos_val_SUC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`pc' + 1`; `0`; `sec_list:((A)sec)list`; `c:(A)asm_config`;
     `nlabs:(num spt)spt`; `ffis2:ffiname list`;
     `LENGTH (prog_to_bytes (code2:((A)sec)list))`] pos_val_bound) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `x:A word` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a + pos_val pc' 0 (sec_list:((A)sec)list)` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "MEM"
                                             with Failure _ -> false)) (concl th))) THEN
  ANTS_TAC THENL
   [LTTP3AUX_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RULE) THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> ~a ==> ~b`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;
(* the code after an installation has no shared memory lines *)
let LTTP3AUX_install_no_install_or = prove
 (`!(code2:((A)sec)list) sec_list ffi_names pc b c d.
     no_install_or_no_share_mem code2 ffi_names /\
     asm_fetch_aux pc code2 = SOME (LabAsm lab_Install b c d) /\
     no_share_mem_inst sec_list
     ==> no_install_or_no_share_mem (APPEND code2 sec_list) ffi_names`,
  REWRITE_TAC[no_install_or_no_share_mem_def; lab_no_install_def] THEN
  REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_SIMP_TAC[no_share_mem_APPEND];
    ASM_MESON_TAC[]]);;
(* the state relation after the installation of new code *)
let LTTP3AUX_state_rel_install = prove
 (`!(mc_conf:(A,B,C)machine_config) code2 labs p (s1:(A,lab_to_target_config,FFI)lab_state)
     (t1:(A)asm_state) ms1 a1 a2 a3 w1 w2 n1 n2 cfg bytes new_pc cb k lines rest ms2.
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
     asm_fetch s1 = SOME (LabAsm lab_Install a1 a2 a3) /\
     lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w1 /\
     lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w2 /\
     lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
     buffer_flush (lab_state_code_buffer s1) w1 w2 = SOME (bytes,cb) /\
     loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
     lab_state_compile_oracle s1 0 = (cfg,CONS (Section k lines) rest) /\
     lab_state_compile s1 cfg (CONS (Section k lines) rest) =
       SOME (bytes,FST (shift_seq 1 (lab_state_compile_oracle s1) 0)) /\
     target_state_rel (machine_config_target mc_conf) (asm_state_regs_fupd
            (K ((lab_state_ptr_reg s1 =+ w1)
                (\a. get_reg_value (lab_state_cc_regs s1 0 a) (asm_state_regs t1 a) I)))
          (asm_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (asm_state_pc_fupd (K (word_add p (word (pos_val new_pc 0 code2)))) t1))) ms2
     ==> ?sec_list.
           lab_to_targetProof_state_rel
             (machine_config_ccache_interfer_fupd
                (K (shift_seq 1 (machine_config_ccache_interfer mc_conf))) mc_conf,
              APPEND code2 sec_list,
              lab_to_target_config_labels (FST (shift_seq 1 (lab_state_compile_oracle s1) 0)),
              p)
             (lab_state_pc_fupd (K new_pc)
          (lab_state_code_buffer_fupd (K cb)
          (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
          (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
          (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
          (lab_state_regs_fupd
             (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                   (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
          (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
          (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) (asm_state_regs_fupd
            (K ((lab_state_ptr_reg s1 =+ w1)
                (\a. get_reg_value (lab_state_cc_regs s1 0 a) (asm_state_regs t1 a) I)))
          (asm_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (asm_state_pc_fupd (K (word_add p (word (pos_val new_pc 0 code2)))) t1))) ms2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `a1:A word`; `a2:byte list`; `a3:num`;
     `cfg:lab_to_target_config`; `CONS (Section k lines) rest:((A)sec)list`;
     `bytes:byte list`] LTTP3AUX_install_compile) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sec_list:((A)sec)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bytes:byte list`)) THEN
  EXISTS_TAC `sec_list:((A)sec)list` THEN
  ABBREV_TAC `nlabs = lab_to_target_config_labels
                        (FST (shift_seq 1 (lab_state_compile_oracle (s1:(A,lab_to_target_config,FFI)lab_state)) 0))` THEN
  FIRST_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS "lab_to_targetProof_state_rel")) THEN
  REWRITE_TAC[lab_to_targetProof_state_rel_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i = LENGTH (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`
    SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
       SOME i`;
      `mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
       SOME (LENGTH (machine_config_ffi_names mc_conf))`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun lens ->
    if is_eq(concl lens) &&
       (try fst(dest_const(rator(lhs(concl lens)))) = "LENGTH" with Failure _ -> false)
    then REWRITE_TAC((record_info "asm_state").ri_accfupds :: LTTP3AUX_RECS) THEN
         ASM_REWRITE_TAC[] THEN ASSUME_TAC lens
    else NO_TAC) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* the mmio indices *)
    EXISTS_TAC `LENGTH (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))` THEN ASM_REWRITE_TAC[];
    (* the ffi calls *)
    MAP_EVERY X_GEN_TAC [`ms:B`; `kk:num`; `index:num`; `nbytes:byte list`;
      `tt:(A)asm_state`; `bs:byte list`; `bs2:byte list`; `st:(FFI)ffi_state`;
      `nst:(FFI)ffi_state`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ms:B`; `kk:num`; `index:num`; `nbytes:byte list`;
      `tt:(A)asm_state`; `bs:byte list`; `bs2:byte list`; `st:(FFI)ffi_state`;
      `nst:(FFI)ffi_state`; `j:num`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "read_ffi_bytearrays"
                                 with Failure _ -> false)) (concl th))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LTTP3AUX_read_ffi_bytearrays_ccache]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    (* the code cache calls *)
    MAP_EVERY X_GEN_TAC [`ms:B`; `tt:(A)asm_state`; `kk:num`; `x1:A word`; `x2:A word`] THEN
    STRIP_TAC THEN REWRITE_TAC[shift_seq_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ms:B`; `tt:(A)asm_state`; `kk + 1`; `x1:A word`;
      `x2:A word`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "machine_config_ccache_interfer"
                                 with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    (* the compile oracle *)
    DISCH_TAC THEN X_GEN_TAC `kk:num` THEN REWRITE_TAC[shift_seq_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "lab_state_compile_oracle"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `kk + 1`) THEN
    MP_TAC(ISPEC `lab_state_compile_oracle (s1:(A,lab_to_target_config,FFI)lab_state) (kk + 1)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `cfg1:lab_to_target_config`
      (X_CHOOSE_THEN `code1:((A)sec)list` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `FST (shift_seq 1 (lab_state_compile_oracle (s1:(A,lab_to_target_config,FFI)lab_state)) 0) = cfg1` ASSUME_TAC THENL
     [REWRITE_TAC[shift_seq_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
      `FST (shift_seq 1 (lab_state_compile_oracle (s1:(A,lab_to_target_config,FFI)lab_state)) 0) = cfg1`]) THEN
    ASM_REWRITE_TAC[];
    (* the ffi names of the code *)
    MAP_EVERY (fun f -> FIRST_X_ASSUM(MP_TAC o check (LTTP3AUX_HEAD_IS f)))
      ["list_subset"; "list_subset"] THEN
    REWRITE_TAC[list_subset_def; GSYM ALL_MEM; find_ffi_names_append; MEM_FILTER;
                MEM_APPEND] THEN
    MESON_TAC[];
    (* the code length is even *)
    REWRITE_TAC[prog_to_bytes_APPEND; LENGTH_APPEND; EVEN_ADD] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC all_enc_ok_prog_to_bytes_EVEN THEN
    MAP_EVERY EXISTS_TAC [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`; `nlabs:(num spt)spt`;
      `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`; `LENGTH (prog_to_bytes (code2:((A)sec)list))`] THEN
    ASM_REWRITE_TAC[];
    (* the labels *)
    MAP_EVERY X_GEN_TAC [`l1:num`; `l2:num`; `x2:num`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LTTP3AUX_install_loc_to_pc THEN
    MAP_EVERY EXISTS_TAC [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`; `labs:(num spt)spt`;
      `TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
         (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`; `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`;
      `lab_state_code (s1:(A,lab_to_target_config,FFI)lab_state)`; `CONS (Section k lines) rest:((A)sec)list`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_good_code_def] o
      check (LTTP3AUX_HEAD_IS "lab_to_targetProof_good_code")) THEN SIMP_TAC[];
    (* the registers *)
    MATCH_MP_TAC LTTP3AUX_install_regs THEN EXISTS_TAC `labs:(num spt)spt` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[word_loc_val_def] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`k:num`; `0`; `0`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "loc_to_pc" with Failure _ -> false))
        (concl th) &&
      can (find_term ((=) `sec_list:((A)sec)list`)) (concl th))) THEN
    ONCE_REWRITE_TAC[loc_to_pc_def] THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CASE_REWRITE_TAC[option_INJ] THEN
    MP_TAC(ISPECL [`sec_list:((A)sec)list`; `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
      `nlabs:(num spt)spt`; `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`;
      `LENGTH (prog_to_bytes (code2:((A)sec)list))`] pos_val_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    ASM_MESON_TAC[];
    (* the memory *)
    X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A word` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "word_loc_val_byte"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LTTP3AUX_word_loc_val_byte_mono THEN EXISTS_TAC `labs:(num spt)spt` THEN
    ASM_REWRITE_TAC[];
    (* the space of the code buffer *)
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "buffer_space_left"
                               with Failure _ -> false)) (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "MEM"
                                    with Failure _ -> false)) (concl th)))) THEN
    ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC];
    (* the code bytes *)
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    REWRITE_TAC[prog_to_bytes_APPEND; bytes_in_mem_APPEND] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "bytes_in_mem" th &&
      can (find_term (fun t -> try fst(dest_const t) = "buffer_buffer"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    (* the position of the code buffer *)
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[prog_to_bytes_APPEND; LENGTH_APPEND; WORD_ADD; WORD_ADD_ASSOC];
    (* the bytes of the code buffer *)
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[bytes_in_mem_def];
    (* the size of the code buffer *)
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[prog_to_bytes_APPEND; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
    LTTP3AUX_ARITH_TAC;
    (* the ffi entry points are not in the code buffer *)
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN X_GEN_TAC `bn:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (prog_to_bytes (sec_list:((A)sec)list)) + bn` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "MEM"
                                 with Failure _ -> false)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "buffer_space_left"
                                 with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[LT_ADD_LCANCEL; WORD_ADD; WORD_ADD_ASSOC];
    (* the pc *)
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`code2:((A)sec)list`; `new_pc:num`; `0`; `sec_list:((A)sec)list`]
      pos_val_append) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC all_enc_ok_imp_sec_label_zero THEN
      MAP_EVERY EXISTS_TAC [`target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`; `nlabs:(num spt)spt`;
        `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`; `LENGTH (prog_to_bytes (code2:((A)sec)list))`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term ((=) `new_pc:num`)) (concl th))) THEN
    MATCH_MP_TAC(TAUT `!a b. a ==> ~a ==> b`) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP code_similar_len_no_lab o
      check (LTTP3AUX_HEAD_IS "code_similar")) THEN
    MATCH_MP_TAC loc_to_pc_bound THEN MAP_EVERY EXISTS_TAC [`n1:num`; `n2:num`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC code_similar_sec_labels_ok THEN
    EXISTS_TAC `code2:((A)sec)list` THEN ASM_SIMP_TAC[code_similar_sym];
    (* the encodings *)
    REWRITE_TAC[THE_DEF; TAKE_LENGTH_ID] THEN MATCH_MP_TAC all_enc_ok_append THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
     [MATCH_MP_TAC all_enc_ok_labs_mono THEN EXISTS_TAC `labs:(num spt)spt` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> LTTP3AUX_HEAD_IS "all_enc_ok" th &&
        can (find_term (fun t -> try fst(dest_const t) = "TAKE" with Failure _ -> false))
          (concl th))) THEN
      REWRITE_TAC[ASSUME `mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)) =
                          SOME (LENGTH (machine_config_ffi_names (mc_conf:(A,B,C)machine_config)))`;
                  THE_DEF; TAKE_LENGTH_ID];
      FIRST_ASSUM ACCEPT_TAC];
    (* the section labels *)
    REWRITE_TAC[ALL_APPEND] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC code_similar_sec_labels_ok THEN
    EXISTS_TAC `CONS (Section k lines) rest:((A)sec)list` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[lab_to_targetProof_good_code_def] o
      check (LTTP3AUX_HEAD_IS "lab_to_targetProof_good_code")) THEN SIMP_TAC[];
    (* the code *)
    MATCH_MP_TAC code_similar_append THEN ASM_REWRITE_TAC[];
    (* there are no shared memory entry points *)
    REWRITE_TAC(share_mem_state_rel_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[option_INJ] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN LTTP3AUX_ARITH_TAC;
    (* the shared memory domain *)
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_buffer_flush o check (LTTP3AUX_LHS_IS "buffer_flush")) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC LTTP3AUX_install_share_mem_domain THEN
    MAP_EVERY EXISTS_TAC [`lab_state_code_buffer (s1:(A,lab_to_target_config,FFI)lab_state)`; `target_config (machine_config_target (mc_conf:(A,B,C)machine_config))`;
      `labs:(num spt)spt`;
      `TAKE (THE (mmio_pcs_min_index (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))))
         (machine_config_ffi_names (mc_conf:(A,B,C)machine_config))`;
      `nlabs:(num spt)spt`; `machine_config_ffi_names (mc_conf:(A,B,C)machine_config)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC no_share_mem_APPEND THEN ASM_REWRITE_TAC[];
    (* no installation or no shared memory *)
    MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`; `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`;
      `t1:(A)asm_state`; `ms1:B`; `a1:A word`; `a2:byte list`; `a3:num`]
      LTTP3AUX_install_code2) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC LTTP3AUX_install_no_install_or THEN
    MAP_EVERY EXISTS_TAC [`lab_state_pc (s1:(A,lab_to_target_config,FFI)lab_state)`; `b:A word`; `c:byte list`; `d:num`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
(* HOL4 line 8754, Resume compile_correct[Install] *)
let LTTP3AUX_cc_Install = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) a1 a2 a3 w1 w2 n1 n2 cfg bytes new_pc cb k
     lines rest res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
     (!a1 a2 a3 w1 w2 n1 n2 cfg bytes new_pc cb lines rest k.
        ~(lab_state_clock s1 = 0) /\
        asm_fetch s1 = SOME (LabAsm lab_Install a1 a2 a3) /\
        lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w1 /\
        lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w2 /\
        lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
        buffer_flush (lab_state_code_buffer s1) w1 w2 = SOME (bytes,cb) /\
        loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
        lab_state_compile_oracle s1 0 = (cfg,CONS (Section k lines) rest) /\
        lab_state_compile s1 cfg (CONS (Section k lines) rest) =
          SOME (bytes,FST (shift_seq 1 (lab_state_compile_oracle s1) 0))
        ==> !res (mc_conf:(A,B,C)machine_config) s2 code2 labs (t1:(A)asm_state) ms1 p.
              oracle_tie mc_conf ms1 (lab_state_pc_fupd (K new_pc)
          (lab_state_code_buffer_fupd (K cb)
          (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
          (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
          (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
          (lab_state_regs_fupd
             (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                   (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
          (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
          (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) /\
              lab_evaluate (lab_state_pc_fupd (K new_pc)
          (lab_state_code_buffer_fupd (K cb)
          (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
          (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
          (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
          (lab_state_regs_fupd
             (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                   (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
          (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
          (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) = (res,s2) /\
              ~(res = target_Error) /\
              encoder_correct (machine_config_target mc_conf) /\
              lab_to_targetProof_state_rel (mc_conf,code2,labs,p) (lab_state_pc_fupd (K new_pc)
          (lab_state_code_buffer_fupd (K cb)
          (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
          (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
          (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
          (lab_state_regs_fupd
             (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                   (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
          (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
          (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) t1 ms1
              ==> ?kk ms2.
                    target_evaluate mc_conf (lab_state_ffi (lab_state_pc_fupd (K new_pc)
          (lab_state_code_buffer_fupd (K cb)
          (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
          (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
          (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
          (lab_state_regs_fupd
             (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                   (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
          (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
          (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1)))))))))) (lab_state_clock (lab_state_pc_fupd (K new_pc)
          (lab_state_code_buffer_fupd (K cb)
          (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
          (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
          (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
          (lab_state_regs_fupd
             (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                   (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
          (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
          (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) + kk) ms1 =
                    (res,ms2,lab_state_ffi s2)) /\
     ~(lab_state_clock s1 = 0) /\
        asm_fetch s1 = SOME (LabAsm lab_Install a1 a2 a3) /\
        lab_state_regs s1 (lab_state_ptr_reg s1) = wl_Word w1 /\
        lab_state_regs s1 (lab_state_len_reg s1) = wl_Word w2 /\
        lab_state_regs s1 (lab_state_link_reg s1) = wl_Loc n1 n2 /\
        buffer_flush (lab_state_code_buffer s1) w1 w2 = SOME (bytes,cb) /\
        loc_to_pc n1 n2 (lab_state_code s1) = SOME new_pc /\
        lab_state_compile_oracle s1 0 = (cfg,CONS (Section k lines) rest) /\
        lab_state_compile s1 cfg (CONS (Section k lines) rest) =
          SOME (bytes,FST (shift_seq 1 (lab_state_compile_oracle s1) 0)) /\
     lab_evaluate (lab_state_pc_fupd (K new_pc)
          (lab_state_code_buffer_fupd (K cb)
          (lab_state_code_fupd (K (APPEND (lab_state_code s1) (CONS (Section k lines) rest)))
          (lab_state_cc_regs_fupd (K (shift_seq 1 (lab_state_cc_regs s1)))
          (lab_state_cc_fp_regs_fupd (K (shift_seq 1 (lab_state_cc_fp_regs s1)))
          (lab_state_regs_fupd
             (K ((lab_state_ptr_reg s1 =+ wl_Loc k 0)
                   (\a. get_reg_value (lab_state_cc_regs s1 0 a) (lab_state_regs s1 a) wl_Word)))
          (lab_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (lab_state_compile_oracle_fupd (K (shift_seq 1 (lab_state_compile_oracle s1)))
          (lab_state_clock_fupd (K (lab_state_clock s1 - 1)) s1))))))))) = (res,s2) /\
     oracle_tie mc_conf ms1 s1 /\ ~(res = target_Error) /\
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> ?k ms2.
           target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
           (res,ms2,lab_state_ffi s2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_step_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LTTP3AUX_state_rel_misc_facts) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LTTP3AUX_ccache_ne_halt) THEN
  (* the jump to the code cache entry point *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`;
     `a1:A word`; `a2:byte list`; `a3:num`] LTTP3AUX_install_jump) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `ms2:B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eval") (CONJUNCTS_THEN2 (LABEL_TAC "fni") ASSUME_TAC))))) THEN
  SUBGOAL_THEN `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config)) ms2 =
                machine_config_ccache_pc mc_conf` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[target_state_rel_def;
      (record_info "asm_state").ri_accfupds; K_THM] o
      check (fun th -> LTTP3AUX_HEAD_IS "target_state_rel" th &&
                       can (find_term ((=) `ms2:B`)) (concl th))) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
    ALL_TAC] THEN
  (* the target state after the code cache call *)
  MP_TAC(ISPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `l:num`; `ms2:B`; `w1:A word`;
     `w2:A word`; `n1:num`; `n2:num`; `new_pc:num`] LTTP3AUX_install_target_rel) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  (* the registers of the call in the shifted configuration *)
  SUBGOAL_THEN `target_get_reg (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2
                  (machine_config_ptr_reg (shift_interfer l (mc_conf:(A,B,C)machine_config))) = (w1:A word) /\
                target_get_reg (machine_config_target (shift_interfer l (mc_conf:(A,B,C)machine_config))) ms2
                  (machine_config_len_reg (shift_interfer l (mc_conf:(A,B,C)machine_config))) = (w2:A word)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC(shift_interfer_def :: LTTP3AUX_RECS) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the state relation after the installation *)
  MP_TAC(ISPECL [`shift_interfer l (mc_conf:(A,B,C)machine_config)`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `p:A word`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `t1:(A)asm_state`; `ms1:B`; `a1:A word`; `a2:byte list`; `a3:num`;
     `w1:A word`; `w2:A word`; `n1:num`; `n2:num`; `cfg:lab_to_target_config`;
     `bytes:byte list`; `new_pc:num`; `cb:(A,8)buffer`; `k:num`; `lines:((A)line)list`;
     `rest:((A)sec)list`; `machine_config_ccache_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)) 0
         (w1,w2,ms2)`] LTTP3AUX_state_rel_install) THEN
  ANTS_TAC THENL
   [REWRITE_TAC(shift_interfer_def :: LTTP3AUX_RECS) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[GSYM shift_interfer_def] THEN MATCH_MP_TAC state_rel_shift_interfer THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_TAC `sec_list:((A)sec)list`)] THEN
  (* the run of the target *)
  SUBGOAL_THEN `!kk. target_evaluate (mc_conf:(A,B,C)machine_config) (lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state))
        ((lab_state_clock s1 + kk) + l) ms1 =
      target_evaluate (machine_config_ccache_interfer_fupd
         (K (shift_seq 1 (machine_config_ccache_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)))))
         (shift_interfer l mc_conf)) (lab_state_ffi s1) (lab_state_clock s1 - 1 + kk) (machine_config_ccache_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)) 0
         (w1,w2,ms2))`
    (LABEL_TAC "step") THENL
   [GEN_TAC THEN USE_THEN "eval" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`shift_interfer l (mc_conf:(A,B,C)machine_config)`; `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`; `lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) + kk`; `ms2:B`]
      LTTP3AUX_target_evaluate_ccache) THEN
    ANTS_TAC THENL
     [REWRITE_TAC(shift_interfer_def :: IN_DIFF :: LTTP3AUX_RECS) THEN
      REWRITE_TAC[ASSUME `target_get_pc (machine_config_target (mc_conf:(A,B,C)machine_config))
                    ms2 = machine_config_ccache_pc mc_conf`] THEN
      ASM_REWRITE_TAC[ADD_EQ_0];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(lab_state_clock (s1:(A,lab_to_target_config,FFI)lab_state) = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the induction hypothesis *)
  USE_THEN "IH" (MP_TAC o SPECL [`a1:A word`; `a2:byte list`; `a3:num`; `w1:A word`;
     `w2:A word`; `n1:num`; `n2:num`; `cfg:lab_to_target_config`; `bytes:byte list`;
     `new_pc:num`; `cb:(A,8)buffer`; `lines:((A)line)list`; `rest:((A)sec)list`; `k:num`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:machine_result`; `machine_config_ccache_interfer_fupd
         (K (shift_seq 1 (machine_config_ccache_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)))))
         (shift_interfer l mc_conf)`;
     `s2:(A,lab_to_target_config,FFI)lab_state`; `APPEND code2 sec_list:((A)sec)list`;
     `lab_to_target_config_labels (FST (shift_seq 1 (lab_state_compile_oracle (s1:(A,lab_to_target_config,FFI)lab_state)) 0))`; `asm_state_regs_fupd
            (K ((lab_state_ptr_reg (s1:(A,lab_to_target_config,FFI)lab_state) =+ (w1:A word))
                (\a. get_reg_value (lab_state_cc_regs s1 0 a) (asm_state_regs (t1:(A)asm_state) a) I)))
          (asm_state_fp_regs_fupd (K (\n. lab_state_cc_fp_regs s1 0 n))
          (asm_state_pc_fupd (K (word_add (p:A word) (word (pos_val new_pc 0 (code2:((A)sec)list))))) t1))`; `machine_config_ccache_interfer (shift_interfer l (mc_conf:(A,B,C)machine_config)) 0
         (w1,w2,ms2)`; `p:A word`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [(* the oracle *)
      MATCH_MP_TAC(ISPECL [`shift_interfer l (mc_conf:(A,B,C)machine_config)`; `ms2:B`; `(s1:(A,lab_to_target_config,FFI)lab_state)`; `w1:A word`; `w2:A word`; `ms2:B`]
        oracle_tie_ccache_next) THEN
      EXISTS_TAC `lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC oracle_tie_shift_interfer THEN EXISTS_TAC `ms1:B` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(LTTP3AUX_INSTN [("mc",`shift_interfer l (mc_conf:(A,B,C)machine_config)`); ("ms",`ms2:B`); ("ffi",`lab_state_ffi (s1:(A,lab_to_target_config,FFI)lab_state)`)]
          next_interference_ccache) THEN
        ANTS_TAC THENL
         [REWRITE_TAC(shift_interfer_def :: IN_DIFF :: LTTP3AUX_RECS) THEN
          REWRITE_TAC[ASSUME `target_get_pc (machine_config_target
            (mc_conf:(A,B,C)machine_config)) ms2 = machine_config_ccache_pc mc_conf`] THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS;
        REWRITE_TAC LTTP3AUX_RECS];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC(shift_interfer_def :: LTTP3AUX_RECS) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC LTTP3AUX_RECS THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num` (X_CHOOSE_TAC `ms3:B`)) THEN
  MAP_EVERY EXISTS_TAC [`kk + l`; `ms3:B`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN USE_THEN "step" (fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* compile_correct itself                                                     *)
(* ------------------------------------------------------------------------- *)

(* tactic: prove a case of compile_correct by its case lemma, whose leading  *)
(* implications are discharged by the assumptions of the case               *)
let LTTP3AUX_DISPATCH_TAC (lem:thm) : tactic =
  fun (asl,w as g) ->
    let rec chase th =
      try chase (tryfind (fun (_,a) -> MATCH_MP th a) asl) with Failure _ -> th in
    (MATCH_MP_TAC (SPEC_ALL (chase lem)) THEN REPEAT CONJ_TAC THEN
     TRY (FIRST_ASSUM ACCEPT_TAC) THEN ASM_REWRITE_TAC[]) g;;

(* HOL4 line 7526: val say = say0 "compile_correct" (a printing tactic) *)

(* HOL4 line 7528.  The HOL4 proof is spread over Resume compile_correct[C] *)
(* blocks (HOL4 lines 7560-9356, one per kind of line: Asm, CBW, ShareMemOp, *)
(* Jump, JumpCmp, Call, LocValue, CallFFI, Install, Halt), suspended after   *)
(* an induction on labSem's evaluate and case splits on asm_fetch s1: one    *)
(* theorem here, proved by one part agent.  HOL4's existential t2 is unused  *)
(* (left out); p is free in HOL4.                                            *)
let lab_to_targetProof_compile_correct = prove
 (`!(s1:(A,lab_to_target_config,FFI)lab_state) res (mc_conf:(A,B,C)machine_config) s2
     code2 labs (t1:(A)asm_state) ms1 p.
     oracle_tie mc_conf ms1 s1 /\
     lab_evaluate s1 = (res,s2) /\ ~(res = target_Error) /\
     encoder_correct (machine_config_target mc_conf) /\
     lab_to_targetProof_state_rel (mc_conf,code2,labs,p) s1 t1 ms1
     ==> ?k ms2.
           target_evaluate mc_conf (lab_state_ffi s1) (lab_state_clock s1 + k) ms1 =
           (res,ms2,lab_state_ffi s2)`,
  MATCH_MP_TAC lab_evaluate_ind THEN X_GEN_TAC `s1:(A,lab_to_target_config,FFI)lab_state` THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`res:machine_result`; `mc_conf:(A,B,C)machine_config`;
     `s2:(A,lab_to_target_config,FFI)lab_state`; `code2:((A)sec)list`; `labs:(num spt)spt`;
     `t1:(A)asm_state`; `ms1:B`; `p:A word`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s1:(A,lab_to_target_config,FFI)lab_state`; `res:machine_result`;
                 `s2:(A,lab_to_target_config,FFI)lab_state`] LTTP3AUX_lab_evaluate_cases) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`0`; `ms1:B`] THEN ONCE_REWRITE_TAC[target_evaluate_def] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_Inst;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_JumpReg;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_Cbw;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_ShareMem;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_ShareMem_final;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_Jump;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_JumpCmp_T;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_JumpCmp_F;
    FIRST_ASSUM(MP_TAC o MATCH_MP LTTP3AUX_cc_Call) THEN
    DISCH_THEN(MP_TAC o SPECL [`mc_conf:(A,B,C)machine_config`; `code2:((A)sec)list`;
      `labs:(num spt)spt`; `p:A word`; `t1:(A)asm_state`; `ms1:B`]) THEN
    ASM_REWRITE_TAC[];
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_LocValue;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_Halt;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_CallFFI;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_CallFFI_final;
    LTTP3AUX_DISPATCH_TAC LTTP3AUX_cc_Install]);;
