(* ========================================================================= *)
(* pan_to_targetProof: port of HOL4 pancake/proofs/pan_to_targetProofScript  *)
(* .sml (CakeML v3479).                                                      *)
(* Composing semantics correctness from pan to target.                      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says; HOL4's local Overloads           *)
(*   stack_remove_prog_comp, ..., pan_to_word_compile_prog are the port's    *)
(*   constant names.  The headline theorem pan_to_target_compile_semantics  *)
(*   is checked against the term of pan_to_target_statement.ml, which also *)
(*   holds the definitions its statement uses (pancake_good_code,          *)
(*   pan_installed, compile_prog_max, option_lt).                           *)
(* - wordSem's names have the prefix wl_ (wl_evaluate, wl_get_var, ...); the *)
(*   record wl_state has the fields wl_state_memory, ...; HOL4               *)
(*   s with memory := m is wl_state_memory_fupd (K m) s.                     *)
(* - Words: n2w = word, w2n = val, <+ = word_ult, <=+ = word_ule.            *)
(* - The proof of the headline is split into lemmas (PTOPAUX_lab_step,      *)
(*   PTOPAUX_stack_step, PTOPAUX_word_step, PTOPAUX_w2w_step,               *)
(*   PTOPAUX_pan_step, PTOPAUX_limit_step) and uses helpers of backendProof  *)
(*   (BKP2AUX_compose, BKP2AUX_mem_assumption, BKP2AUX_fmi_SOME,             *)
(*   BKP2AUX_labels_transfer, BKP2AUX_names_target_regs, ...).  The facts   *)
(*   about the heap and the stack of the initial stackLang state come from  *)
(*   stack_removeProof's init_prop (PTOPAUX_fmi_facts, PTOPAUX_heap_facts)  *)
(*   where HOL4 computes the registers after the init code.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/targetProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/proofs/wordConvsProof.ml";;
needs "compiler/backend/proofs/word_to_wordProof.ml";;
needs "compiler/backend/proofs/word_depthProof.ml";;
needs "compiler/backend/proofs/word_to_stackProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/proofs/stack_allocProof.ml";;
needs "compiler/backend/proofs/stack_namesProof.ml";;
needs "compiler/backend/proofs/stack_rawcallProof.ml";;
needs "compiler/backend/proofs/stack_to_labProof.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_wordProof.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "pancake/pan_to_target.ml";;
needs "pancake/proofs/pan_to_wordProof.ml";;
needs "pancake/proofs/pan_to_target_statement.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 pancake_good_code_def (line 22) is in pan_to_target_statement.ml *)

let pan_to_lab_good_code_lemma = prove
 (`!(c:backend_config) lim1 lim2 (offs:A word#A word)
    (stack_prog:(num#(A)stack_prog)list) code (asm_conf3:(A)asm_config)
    (word_prog:(num#num#(A)wl_prog)list) bm wc fs word_conf
    (word_prog0:(num#num#(A)wl_prog)list) col (pan_prog:((A)decl)list)
    (conf:(A)asm_config).
     stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
       lim1 lim2 offs stack_prog = code /\
     word_to_stack_compile asm_conf3 F word_prog = (bm,wc,fs,stack_prog) /\
     word_to_word_compile word_conf asm_conf3 word_prog0 = (col,word_prog) /\
     pan_to_word_compile_prog (asm_config_ISA asm_conf3) pan_prog = word_prog0 /\
     labels_ok code /\
     ALL (sec_ok_pre conf) code
     ==> lab_to_targetProof_good_code conf LN code`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[lab_to_targetProof_good_code_def] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ALL (sec_labels_ok:(A)sec->bool) code /\
    ALL_DISTINCT (MAP Section_num (code:((A)sec)list)) /\
    ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) (code:((A)sec)list)`
   STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `labels_ok (code:((A)sec)list)` THEN REWRITE_TAC[labels_ok_def] THEN
   SUBGOAL_THEN (CASE_TERM `(\s. match s with Section n _ -> n) = (Section_num:(A)sec->num)`)
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CASES_ON `x:(A)sec` THEN
    CASE_REWRITE_TAC[] THEN SIMP[lab_Section_num_def]; ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN MATCH_MP_TAC MONO_ALL THEN
   GEN_TAC THEN CASES_ON `x:(A)sec` THEN CASE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[EVERY_sec_label_ok; o_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[labs_domain_LN; UNION_EMPTY; domain_def; DISJOINT_EMPTY] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> is_eq (concl th) &&
                fst (strip_comb (lhs (concl th))) = `stack_to_lab_compile:stack_to_lab_config->data_to_word_config->num->num->A word#A word->(num#(A)stack_prog)list->((A)sec)list`)) THEN
   REWRITE_TAC[stack_to_lab_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[EVERY_sec_ends_with_label_MAP_prog_to_section];
   ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\(n,m,pp). good_handlers n pp) (word_prog:(num#num#(A)wl_prog)list)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `word_prog:(num#num#(A)wl_prog)list =
                 SND (word_to_word_compile word_conf asm_conf3 word_prog0)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC word_good_handlers_word_to_word THEN
   ASM_MESON_TAC[pan_to_word_good_handlers]; ALL_TAC] THEN
  SUBGOAL_THEN `stack_good_handler_labels (stack_prog:(num#(A)stack_prog)list)` ASSUME_TAC THENL
  [ASM_MESON_TAC[word_to_stack_good_handler_labels]; ALL_TAC] THEN
  MATCH_MP_TAC stack_to_lab_stack_good_handler_labels THEN ASM_MESON_TAC[]);;

(* HOL4 [move] *)
let word_to_stack_compile_FST = prove
 (`!(mc:(A,B,C)machine_config) (wprog:(num#num#(A)wl_prog)list) bitmaps c'' fs p.
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) ==>
     MAP FST p =
       CONS raise_stub_location (CONS wl_store_consts_stub_location (MAP FST wprog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[MAP; FST; CONS_11] THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP MAP_FST_compile_word_to_stack));;

(* the side condition of compile_to_word_conventions2 when the ISA is not Ag32 *)
let PTOPAUX_ALL_no_share_Ag32 = prove
 (`!(ac:(A)asm_config) (p:(num#num#(A)wl_prog)list).
     ~(asm_config_ISA ac = Ag32) ==>
     ALL (\(x1,x2,prg). no_share_inst prg \/ ~(asm_config_ISA ac = Ag32)) p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]);;

(* names of at least 60 are not the stub names below 60 *)
let PTOPAUX_lab_min_not_MEM = prove
 (`!(l:(num#B)list) n. ALL (\prog. 60 <= FST prog) l /\ n < 60 ==> ~MEM n (MAP FST l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; ALL] THEN
  ASM_MESON_TAC[ARITH_RULE `60 <= a /\ n < 60 ==> ~(n = a)`]);;

let pan_to_stack_first_ALL_DISTINCT = prove
 (`!(mc:(A,B,C)machine_config) (pan_code:((A)decl)list) wprog0 (c:backend_config) col
    wprog bitmaps c'' fs p.
     pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
       pan_code = wprog0 /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc)) wprog0 = (col,wprog) /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) /\
     ALL_DISTINCT (MAP FST (functions pan_code))
     ==> ALL_DISTINCT (MAP FST p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAP FST (wprog:(num#num#(A)wl_prog)list) = MAP FST (wprog0:(num#num#(A)wl_prog)list)`
    ASSUME_TAC THENL
  [MP_TAC (MATCH_MP compile_to_word_conventions2
     (CONJ (ASSUME `word_to_word_compile (backend_config_word_to_word_conf c)
                      (target_config (machine_config_target (mc:(A,B,C)machine_config)))
                      (wprog0:(num#num#(A)wl_prog)list) = (col,wprog)`)
           (SPEC `wprog0:(num#num#(A)wl_prog)list` (MATCH_MP PTOPAUX_ALL_no_share_Ag32
              (ASSUME `~(asm_config_ISA (target_config (machine_config_target
                          (mc:(A,B,C)machine_config))) = Ag32)`))))) THEN
   SIMP_TAC[];
   ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP word_to_stack_compile_FST) THEN
  ASM_REWRITE_TAC[ALL_DISTINCT] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (wprog0:(num#num#(A)wl_prog)list))` ASSUME_TAC THENL
  [UNDISCH_TAC `pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target
                  (mc:(A,B,C)machine_config)))) pan_code = (wprog0:(num#num#(A)wl_prog)list)` THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC pan_to_wordProof_first_compile_prog_all_distinct THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\prog. 60 <= FST prog) (wprog0:(num#num#(A)wl_prog)list)` ASSUME_TAC THENL
  [MATCH_MP_TAC pan_to_word_compile_prog_lab_min THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MEM; raise_stub_location_def; wl_store_consts_stub_location_def;
                  word_num_stubs_def; stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THEN MATCH_MP_TAC PTOPAUX_lab_min_not_MEM THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let pan_to_stack_compile_lab_pres = prove
 (`!(mc:(A,B,C)machine_config) (pan_code:((A)decl)list) wprog0 (c:backend_config) col
    wprog bitmaps c'' fs p.
     pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
       pan_code = wprog0 /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc)) wprog0 = (col,wprog) /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) /\
     ALL_DISTINCT (MAP FST (functions pan_code))
     ==> ALL_DISTINCT (MAP FST p) /\
         ALL (\n. ~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = gc_stub_location)) (MAP FST p) /\
         ALL (\(n,p). let labs = stack_extract_labels p in
                      ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\
                      ALL_DISTINCT labs) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (MATCH_MP compile_to_word_conventions2
     (CONJ (ASSUME `word_to_word_compile (backend_config_word_to_word_conf c)
                      (target_config (machine_config_target (mc:(A,B,C)machine_config)))
                      (wprog0:(num#num#(A)wl_prog)list) = (col,wprog)`)
           (SPEC `wprog0:(num#num#(A)wl_prog)list` (MATCH_MP PTOPAUX_ALL_no_share_Ag32
              (ASSUME `~(asm_config_ISA (target_config (machine_config_target
                          (mc:(A,B,C)machine_config))) = Ag32)`))))) THEN
  STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[pan_to_stack_first_ALL_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\prog. 60 <= FST prog) (wprog0:(num#num#(A)wl_prog)list)` ASSUME_TAC THENL
  [MATCH_MP_TAC pan_to_word_compile_prog_lab_min THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [FIRST_ASSUM(SUBST1_TAC o MATCH_MP word_to_stack_compile_FST) THEN
   ASM_REWRITE_TAC[ALL; raise_stub_location_def; wl_store_consts_stub_location_def;
                   word_num_stubs_def; stack_num_stubs_def; gc_stub_location_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   UNDISCH_TAC `ALL (\prog. 60 <= FST prog) (wprog0:(num#num#(A)wl_prog)list)` THEN
   REWRITE_TAC[ALL_MAP; o_DEF] THEN MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC (ISPECL [`wprog:(num#num#(A)wl_prog)list`;
                  `target_config (machine_config_target (mc:(A,B,C)machine_config))`]
                 word_to_stack_compile_lab_pres) THEN
  ANTS_TAC THENL
  [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN MATCH_MP_TAC BKP2AUX_labels_transfer THEN
   EXISTS_TAC `wprog0:(num#num#(A)wl_prog)list` THEN ASM_REWRITE_TAC[] THEN
   MP_TAC (ISPECL [`asm_config_ISA (target_config (machine_config_target
                      (mc:(A,B,C)machine_config)))`;
                   `pan_code:((A)decl)list`; `wprog0:(num#num#(A)wl_prog)list`]
                  pan_to_word_compile_lab_pres) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SIMP_TAC[]]);;

let pan_to_lab_labels_ok = prove
 (`!(mc:(A,B,C)machine_config) (pan_code:((A)decl)list) wprog0 (c:backend_config) col
    wprog bitmaps c'' fs p max_heap sp lprog.
     pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
       pan_code = wprog0 /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc)) wprog0 = (col,wprog) /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) /\
     stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c) max_heap sp
       (asm_config_addr_offset (target_config (machine_config_target mc))) p = lprog /\
     ALL_DISTINCT (MAP FST (functions pan_code))
     ==> labels_ok lprog`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> is_eq (concl th) && is_var (rhs (concl th)) &&
               fst (dest_var (rhs (concl th))) = "lprog")) THEN
  MATCH_MP_TAC stack_to_lab_compile_lab_pres THEN
  MP_TAC (SPEC_ALL pan_to_stack_compile_lab_pres) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

(** stack_to_lab good_code **)

let word_to_stack_good_code_lemma = prove
 (`!(c:backend_config) (mc:(A,B,C)machine_config) (pan_code:((A)decl)list) col wprog bitmaps
    c'' fs p.
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc))
       (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
          pan_code) = (col,wprog) /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) /\
     LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 13 <=
       asm_config_reg_count (target_config (machine_config_target mc)) /\
     ALL_DISTINCT (MAP FST (functions pan_code))
     ==> stack_to_labProof_good_code
           (asm_config_reg_count (target_config (machine_config_target mc)) -
            (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `wprog0 = pan_to_word_compile_prog (asm_config_ISA (target_config
                 (machine_config_target (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)` THEN
  MP_TAC (ISPECL [`mc:(A,B,C)machine_config`; `pan_code:((A)decl)list`;
                  `wprog0:(num#num#(A)wl_prog)list`; `c:backend_config`] pan_to_stack_compile_lab_pres) THEN
  DISCH_THEN(MP_TAC o SPECL [`col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
                             `bitmaps:(A word)list`; `c'':word_to_stack_config`; `fs:num list`;
                             `p:(num#(A)stack_prog)list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (MATCH_MP compile_to_word_conventions2
     (CONJ (ASSUME `word_to_word_compile (backend_config_word_to_word_conf c)
                      (target_config (machine_config_target (mc:(A,B,C)machine_config)))
                      (wprog0:(num#num#(A)wl_prog)list) = (col,wprog)`)
           (SPEC `wprog0:(num#num#(A)wl_prog)list` (MATCH_MP PTOPAUX_ALL_no_share_Ag32
              (ASSUME `~(asm_config_ISA (target_config (machine_config_target
                          (mc:(A,B,C)machine_config))) = Ag32)`))))) THEN
  STRIP_TAC THEN
  MP_TAC (ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`;
                  `wprog:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`;
                  `c'':word_to_stack_config`; `fs:num list`; `p:(num#(A)stack_prog)list`;
                  `asm_config_reg_count (target_config (machine_config_target
                     (mc:(A,B,C)machine_config))) -
                   (5 + LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))))`]
                 word_to_stack_stack_convs) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> try fst (dest_const t) =
                      "flat_exp_conventions" with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN SIMP_TAC[];
    UNDISCH_TAC `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                   (mc:(A,B,C)machine_config)))) + 13 <=
                 asm_config_reg_count (target_config (machine_config_target mc))` THEN
    ARITH_TAC];
   STRIP_TAC] THEN
  REWRITE_TAC[stack_to_labProof_good_code_def] THEN
  SUBGOAL_THEN `(asm_config_reg_count (target_config (machine_config_target
                   (mc:(A,B,C)machine_config))) -
                 (5 + LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))))) + 2 =
                asm_config_reg_count (target_config (machine_config_target mc)) -
                (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [UNDISCH_TAC `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                  (mc:(A,B,C)machine_config)))) + 13 <=
                asm_config_reg_count (target_config (machine_config_target mc))` THEN
   ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [REWRITE_TAC[EVERY_FST_SND] THEN ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(SUBST1_TAC o MATCH_MP word_to_stack_compile_FST) THEN
   ASM_REWRITE_TAC[ALL; raise_stub_location_def; wl_store_consts_stub_location_def;
                   word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   SUBGOAL_THEN `ALL (\prog. 60 <= FST prog) (wprog0:(num#num#(A)wl_prog)list)` MP_TAC THENL
   [MATCH_MP_TAC pan_to_word_compile_prog_lab_min THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[ALL_MAP; o_DEF] THEN MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> try fst (dest_const t) =
                      "stack_extract_labels" with Failure _ -> false)) (concl th))) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]]);;

(* HOL4 [move] *)
let good_dimindex_0w_8w = prove
 (`good_dimindex (:A) ==>
   word_ile (word 0:A word) (word 8) /\ word_ile (word_neg (word 8)) (word 0:A word)`,
  REWRITE_TAC[good_dimindex_def] THEN MESON_TAC[bounds_lem]);;

(* HOL4 [move]; f PERMUTES UNIV is BIJ f UNIV UNIV *)
let FLOOKUP_MAP_KEYS_LINV = prove
 (`!(f:A->A) (m:(A,B)fmap) i.
     BIJ f (UNIV:A->bool) UNIV ==>
     FLOOKUP (MAP_KEYS (LINV f UNIV) m) i = FLOOKUP m (f i)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BIJ_LINV_BIJ) THEN
  MP_TAC (ISPECL [`LINV (f:A->A) UNIV`; `m:(A,B)fmap`; `(f:A->A) i`]
                 FLOOKUP_MAP_KEYS_MAPPED) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[BIJ]; ALL_TAC] THEN
  SUBGOAL_THEN `LINV (f:A->A) UNIV (f i) = i` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[LINV_DEF; BIJ; IN_UNIV]);;

(* the be field is kept by make_init_any *)
let PTOPAUX_make_init_any_be = prove
 (`!gen_gc' max_heap bitmaps data_sp coracle jump off k code (s:(A,C,FFI)stack_state).
     (stack_state_be (make_init_any gen_gc' max_heap bitmaps data_sp coracle jump off k
                                    code s) <=> stack_state_be s)`,
  REWRITE_TAC[make_init_any_def; make_init_opt_def] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[init_reduce_def; LET_DEF; LET_END_DEF; STACKPROPSAUX_SR_ACC] THEN
  ASM_MESON_TAC[stack_evaluate_consts]);;

(* HOL4 [move to stack_to_labProof] *)
let full_make_init_be = prove
 (`!a b c d e f g (h:(A,C,FFI)lab_state) i j k.
     (stack_state_be (FST (full_make_init a b c d e f g h i j k)) <=> lab_state_be h)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[full_make_init_def; LET_DEF; LET_END_DEF; stack_allocProof_make_init_def] THEN
  SIMP[PTOPAUX_make_init_any_be] THEN
  REWRITE_TAC[stack_namesProof_make_init_def; stack_to_labProof_make_init_def] THEN SIMP[]);;

(* HOL4 pan_installed_def (line 290) is in pan_to_target_statement.ml *)

let pan_installed_imp_installed = prove
 (`!bytes cbspace (bitmaps:(A word)list) data_sp ffi_names r1 r2
    (mc_conf:(A,B,C)machine_config) shmem_extra ms (p_mem:A word->(A)word_loc) p_dom sdm.
     pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms
       p_mem p_dom sdm ==>
     installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_installed_def; installed_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(A)asm_state` (X_CHOOSE_THEN `m:A word->(A)word_loc`
    (X_CHOOSE_THEN `bitmap_ptr:A word` (X_CHOOSE_THEN `bitmaps_dm:A word->bool`
    (X_CHOOSE_THEN `sdm0:A word->bool` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`t:(A)asm_state`; `m:A word->(A)word_loc`; `bitmap_ptr:A word`;
                        `bitmaps_dm:A word->bool`; `sdm0:A word->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* memory update *)

let fun2set_update_eq = prove
 (`!(m:A->B) m' md x a.
     fun2set (m,md) = fun2set (m',md) ==>
     fun2set ((x =+ a) m,md) = fun2set ((x =+ a) m',md)`,
  REWRITE_TAC[fun2set_eq; APPLY_UPDATE_THM] THEN MESON_TAC[]);;

(* HOL4 [simp]; not registered here: its condition or right side has a  *)
(* variable that the left side does not bind, and the kit's simplifier  *)
(* then loops (it instantiates such variables from the context)        *)

let get_var_const_memory = prove
 (`!x m (y:(A,C,FFI)wl_state).
     wl_get_var x (wl_state_memory_fupd (K m) y) = wl_get_var x y`,
  SIMP[wl_get_var_def]);;

let _ = cake_add_simps [get_var_const_memory];;

let set_var_const_memory = prove
 (`!v x m (y:(A,C,FFI)wl_state).
     wl_set_var v x (wl_state_memory_fupd (K m) y) =
     wl_state_memory_fupd (K m) (wl_set_var v x y)`,
  SIMP[wl_set_var_def]);;

let _ = cake_add_simps [set_var_const_memory];;

let unset_var_const_memory = prove
 (`!v m (y:(A,C,FFI)wl_state).
     wl_unset_var v (wl_state_memory_fupd (K m) y) =
     wl_state_memory_fupd (K m) (wl_unset_var v y)`,
  SIMP[wl_unset_var_def]);;

let _ = cake_add_simps [unset_var_const_memory];;

let get_vars_const_memory = prove
 (`!x m (y:(A,C,FFI)wl_state).
     wl_get_vars x (wl_state_memory_fupd (K m) y) = wl_get_vars x y`,
  LIST_INDUCT_TAC THEN SIMP[wl_get_vars_def]);;

let _ = cake_add_simps [get_vars_const_memory];;

let set_vars_const_memory = prove
 (`!vs xs m (y:(A,C,FFI)wl_state).
     wl_set_vars vs xs (wl_state_memory_fupd (K m) y) =
     wl_state_memory_fupd (K m) (wl_set_vars vs xs y)`,
  SIMP[wl_set_vars_def]);;

let _ = cake_add_simps [set_vars_const_memory];;

let get_var_imm_const_memory = prove
 (`!ri m (s:(A,C,FFI)wl_state).
     wl_get_var_imm ri (wl_state_memory_fupd (K m) s) = wl_get_var_imm ri s`,
  GEN_TAC THEN QCASES_ON "ri:(A)reg_imm" THEN SIMP[wl_get_var_imm_def]);;

let _ = cake_add_simps [get_var_imm_const_memory];;

let mem_load_const_memory = prove
 (`!(s:(A,C,FFI)wl_state) m ad.
     fun2set (wl_state_memory s,wl_state_mdomain s) =
     fun2set (m,wl_state_mdomain s) ==>
     wl_mem_load ad (wl_state_memory_fupd (K m) s) = wl_mem_load ad s`,
  REWRITE_TAC[fun2set_eq] THEN REPEAT STRIP_TAC THEN
  SIMP[wl_mem_load_def] THEN COND_CASES_TAC THEN SIMP[]);;

let _ = cake_add_simps [mem_load_const_memory];;

let mem_store_const_memory = prove
 (`!(s:(A,C,FFI)wl_state) m ad w.
     fun2set (wl_state_memory s,wl_state_mdomain s) =
     fun2set (m,wl_state_mdomain s) ==>
     (wl_mem_store ad w s = NONE <=>
      wl_mem_store ad w (wl_state_memory_fupd (K m) s) = NONE) /\
     (wl_mem_store ad w s =
        SOME (wl_state_memory_fupd (K ((ad =+ w) (wl_state_memory s))) s) <=>
      wl_mem_store ad w (wl_state_memory_fupd (K m) s) =
        SOME (wl_state_memory_fupd (K ((ad =+ w) m)) s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SIMP[wl_mem_store_def] THEN
  COND_CASES_TAC THEN SIMP[]);;

(* HOL4 [simp]; not registered here: its condition or right side has a  *)
(* variable that the left side does not bind, and the kit's simplifier  *)
(* then loops (it instantiates such variables from the context)        *)

let mem_load_32_const_memory = prove
 (`!(m:A word->(A)word_loc) m' dm be ad.
     fun2set (m,dm) = fun2set (m',dm) ==>
     mem_load_32 m dm be ad = mem_load_32 m' dm be ad`,
  REWRITE_TAC[fun2set_eq; mem_load_32_def] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `byte_align (ad:A word) IN dm` THEN ASM_SIMP_TAC[] THEN
  QCASES_ON "(m:A word->(A)word_loc) (byte_align ad)" THEN
  QCASES_ON "(m':A word->(A)word_loc) (byte_align ad)" THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 [simp]; not registered here: its condition or right side has a  *)
(* variable that the left side does not bind, and the kit's simplifier  *)
(* then loops (it instantiates such variables from the context)        *)

let mem_store_32_const_memory = prove
 (`!(m:A word->(A)word_loc) m' dm be ad hw.
     fun2set (m,dm) = fun2set (m',dm) ==>
     (mem_store_32 m dm be ad hw = NONE <=> mem_store_32 m' dm be ad hw = NONE) /\
     fun2set (THE (mem_store_32 m dm be ad hw),dm) =
     fun2set (THE (mem_store_32 m' dm be ad hw),dm)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o REWRITE_RULE[fun2set_eq]) THEN
  DISCH_TAC THEN REWRITE_TAC[mem_store_32_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `byte_align (ad:A word) IN dm` THEN ASM_SIMP_TAC[] THENL
   [ALL_TAC;
    QCASES_ON "(m:A word->(A)word_loc) (byte_align ad)" THEN
    QCASES_ON "(m':A word->(A)word_loc) (byte_align ad)" THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]] THEN
  QCASES_ON "(m':A word->(A)word_loc) (byte_align ad)" THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[THE_DEF; option_DISTINCT] THEN
  MATCH_MP_TAC fun2set_update_eq THEN ASM_REWRITE_TAC[]);;

let word_exp_const_memory = prove
 (`!(s:(A,C,FFI)wl_state) exp m.
     fun2set (wl_state_memory s,wl_state_mdomain s) =
     fun2set (m,wl_state_mdomain s) ==>
     wl_word_exp (wl_state_memory_fupd (K m) s) exp = wl_word_exp s exp`,
  REC_IND_TAC wl_word_exp_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[wl_word_exp_def] THEN SIMP[wl_get_store_def] THEN
  SUBGOAL_THEN
    `MAP (wl_word_exp (wl_state_memory_fupd (K (m:A word->(A)word_loc)) s)) wexps =
     MAP (wl_word_exp (s:(A,C,FFI)wl_state)) wexps`
    SUBST1_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let _ = cake_add_simps [word_exp_const_memory];;

let mem_load_byte_aux_const_memory = prove
 (`!(m:A word->(A)word_loc) m' dm be w.
     fun2set (m,dm) = fun2set (m',dm) ==>
     mem_load_byte_aux m' dm be w = mem_load_byte_aux m dm be w`,
  REWRITE_TAC[fun2set_eq; mem_load_byte_aux_def] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `byte_align (w:A word) IN dm` THEN ASM_SIMP_TAC[] THEN
  QCASES_ON "(m:A word->(A)word_loc) (byte_align w)" THEN
  QCASES_ON "(m':A word->(A)word_loc) (byte_align w)" THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 [simp]; not registered here: its condition or right side has a  *)
(* variable that the left side does not bind, and the kit's simplifier  *)
(* then loops (it instantiates such variables from the context)        *)

let mem_store_byte_aux_const_memory = prove
 (`!(m:A word->(A)word_loc) m' dm be w b.
     fun2set (m,dm) = fun2set (m',dm) ==>
     (mem_store_byte_aux m dm be w b = NONE <=>
      mem_store_byte_aux m' dm be w b = NONE) /\
     fun2set (THE (mem_store_byte_aux m' dm be w b),dm) =
     fun2set (THE (mem_store_byte_aux m dm be w b),dm)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o REWRITE_RULE[fun2set_eq]) THEN
  DISCH_TAC THEN REWRITE_TAC[mem_store_byte_aux_def] THEN
  ASM_CASES_TAC `byte_align (w:A word) IN dm` THEN ASM_SIMP_TAC[] THENL
   [ALL_TAC;
    QCASES_ON "(m:A word->(A)word_loc) (byte_align w)" THEN
    QCASES_ON "(m':A word->(A)word_loc) (byte_align w)" THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]] THEN
  QCASES_ON "(m':A word->(A)word_loc) (byte_align w)" THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[THE_DEF; option_DISTINCT] THEN
  MATCH_MP_TAC fun2set_update_eq THEN ASM_MESON_TAC[fun2set_eq]);;

let read_bytearray_const_memory = prove
 (`!(m:A word->(A)word_loc) m' dm be ptr len.
     fun2set (m,dm) = fun2set (m',dm) ==>
     read_bytearray ptr len (mem_load_byte_aux m dm be) =
     read_bytearray ptr len (mem_load_byte_aux m' dm be)`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_MESON_TAC[mem_load_byte_aux_const_memory]);;

(* HOL4 [simp]; not registered here: its condition or right side has a  *)
(* variable that the left side does not bind, and the kit's simplifier  *)
(* then loops (it instantiates such variables from the context)        *)

let write_bytearray_const_memory = prove
 (`!ls ptr (m:A word->(A)word_loc) m' dm be.
     fun2set (m,dm) = fun2set (m',dm) ==>
     fun2set (write_bytearray ptr ls m dm be,dm) =
     fun2set (write_bytearray ptr ls m' dm be,dm)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[write_bytearray_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`word_add ptr (word 1):A word`;
                                 `m:A word->(A)word_loc`; `m':A word->(A)word_loc`;
                                 `dm:A word->bool`; `be:bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o SPECL [`be:bool`; `ptr:A word`; `h:byte`] o
               MATCH_MP mem_store_byte_aux_const_memory) THEN
  STRIP_TAC THEN
  QCASES_ON "mem_store_byte_aux (write_bytearray (word_add ptr (word 1)) t (m:A word->(A)word_loc) dm be) dm be ptr h" THEN
  QCASES_ON "mem_store_byte_aux (write_bytearray (word_add ptr (word 1)) t (m':A word->(A)word_loc) dm be) dm be ptr h" THEN
  RULE_ASSUM_TAC (REWRITE_RULE[option_DISTINCT; THE_DEF]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 [simp]; not registered here: its condition or right side has a  *)
(* variable that the left side does not bind, and the kit's simplifier  *)
(* then loops (it instantiates such variables from the context)        *)

(* the instructions keep a memory that agrees with the old one on its     *)
(* domain (HOL4 proves this by Induct_on i and automation; here: a case    *)
(* split on the instruction, the generic simplification, and the three     *)
(* stores apart)                                                           *)

let PTOPAUX_CASES_IF_FREE (v:term) : tactic =
  fun (asl,w as g) -> if mem v (frees w) then CASES_ON v g else ALL_TAC g;;

let PTOPAUX_INST_MEM_RW_TAC : tactic =
  FIRST_ASSUM (fun th ->
    let l1 = MATCH_MP mem_load_byte_aux_const_memory th in
    let l2 = GSYM (MATCH_MP mem_load_32_const_memory th) in
    REWRITE_TAC[l1; l2]);;

let PTOPAUX_EXISTS_MEM_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let l = lhs (lhand bod) in
  EXISTS_TAC (mk_icomb(mk_const("wl_state_memory",[]), l)) g;;

let PTOPAUX_INST_STORE_TAC : tactic =
  let is_ms t = try let h,args = strip_comb (lhs t) in
                    mem (fst(dest_const h)) ["mem_store_byte_aux";"mem_store_32"]
                with Failure _ -> false in
  let aux_tac : tactic = fun (asl,w as g) ->
    let _,a = find (fun (_,th) -> is_ms (concl th)) asl in
    let h,args = strip_comb (lhs (concl a)) in
    let lemma = if fst(dest_const h) = "mem_store_byte_aux"
                then mem_store_byte_aux_const_memory else mem_store_32_const_memory in
    (FIRST_ASSUM (fun th -> MP_TAC (SPECL (tl (tl args)) (MATCH_MP lemma th))) THEN
     ASM_REWRITE_TAC[THE_DEF; option_DISTINCT] THEN DISCH_TAC THEN
     PTOPAUX_EXISTS_MEM_TAC THEN SIMP[] THEN
     (FIRST_ASSUM (ACCEPT_TAC o SYM) ORELSE FIRST_ASSUM ACCEPT_TAC)) g in
  let cond_tac : tactic =
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th -> is_cond (lhs (concl th))))) THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REPEAT (DISCH_THEN (SUBST_ALL_TAC o SYM)) THEN
    PTOPAUX_EXISTS_MEM_TAC THEN SIMP[] THEN
    MATCH_MP_TAC fun2set_update_eq THEN ASM_REWRITE_TAC[] in
  FIRST [aux_tac; cond_tac];;

let inst_const_memory = prove
 (`!i (s:(A,C,FFI)wl_state) m.
     fun2set (wl_state_memory s,wl_state_mdomain s) =
     fun2set (m,wl_state_mdomain s) ==>
     (wl_inst i s = NONE <=> wl_inst i (wl_state_memory_fupd (K m) s) = NONE) /\
     (~(wl_inst i s = NONE) ==>
      ?m'. THE (wl_inst i (wl_state_memory_fupd (K m) s)) =
           wl_state_memory_fupd (K m') (THE (wl_inst i s)) /\
           (let x = THE (wl_inst i s) in
            fun2set (wl_state_memory x,wl_state_mdomain x) =
            fun2set (m',wl_state_mdomain x)))`,
  GEN_TAC THEN QCASES_ON "i:(A)inst" THEN
  PTOPAUX_CASES_IF_FREE `a:(A)asm_arith` THEN PTOPAUX_CASES_IF_FREE `a:fp` THEN
  PTOPAUX_CASES_IF_FREE `a0:memop` THEN PTOPAUX_CASES_IF_FREE `a2:(A)addr` THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[] THEN PTOPAUX_INST_MEM_RW_TAC THEN
  SIMP[THE_DEF; wl_assign_def; wl_get_fp_var_def; wl_set_fp_var_def; wl_get_var_def;
       wl_set_var_def; wl_get_vars_def; wl_mem_load_def; wl_mem_store_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[THE_DEF]) THEN
  TRY (REPEAT DISCH_TAC THEN QEXISTS_TAC "m" THEN SIMP[] THEN NO_TAC) THEN
  PTOPAUX_INST_STORE_TAC);;

let const_writes_const_memory = prove
 (`!(c':A word) c words (m:A word->(A)word_loc) m' md.
     fun2set (m,md) = fun2set (m',md) ==>
     fun2set (const_writes c' c words m,md) = fun2set (const_writes c' c words m',md)`,
  SUBGOAL_THEN
   `!words (c':A word) c (m:A word->(A)word_loc) m' md.
      fun2set (m,md) = fun2set (m',md) ==>
      fun2set (const_writes c' c words m,md) = fun2set (const_writes c' c words m',md)`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[const_writes_def] THEN
  PAIR_CASES_ON `h:bool#A word` THEN REWRITE_TAC[const_writes_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC fun2set_update_eq THEN ASM_REWRITE_TAC[]);;

let PTOPAUX_FFI_CASES_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "call_FFI" &&
                                  length (snd (strip_comb t)) = 4
                              with Failure _ -> false) w in
  CASES_ON t g;;

let share_inst_const_memory = prove
 (`!(s:(A,C,FFI)wl_state) op v c m (res:((W)wl_result)option) t.
     fun2set (wl_state_memory s,wl_state_mdomain s) =
     fun2set (m,wl_state_mdomain s) /\
     share_inst op v c s = (res,t) ==>
     wl_state_memory t = wl_state_memory s /\ wl_state_mdomain t = wl_state_mdomain s /\
     share_inst op v c (wl_state_memory_fupd (K m) s) =
       (res,wl_state_memory_fupd (K m) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN QCASES_ON "op:memop" THEN
  POP_ASSUM MP_TAC THEN
  SIMP[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def; wl_sh_mem_load16_def;
       wl_sh_mem_load32_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
       wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[sh_mem_set_var_def]) THEN
  TRY (PTOPAUX_FFI_CASES_TAC THEN SIMP[sh_mem_set_var_def]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[wl_set_var_def; wl_flush_state_def]);;

(* HOL4 [simp]; not registered here: its condition or right side has a  *)
(* variable that the left side does not bind, and the kit's simplifier  *)
(* then loops (it instantiates such variables from the context)        *)

(* HOL4 [local] *)
let mem_upd_lemma = prove
 (`!(s:(A,B,C)wl_state) t.
     wl_state_memory_fupd (K ARB) s = wl_state_memory_fupd (K ARB) t ==>
     ?m. s = wl_state_memory_fupd (K m) t`,
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  QEXISTS_TAC "wl_state_memory (s:(A,B,C)wl_state)" THEN ASM_SIMP_TAC[]);;

(* HOL4 [local] *)
let push_env_mem_upd = prove
 (`!env params (s:(A,C,FFI)wl_state) m.
     wl_push_env env params (wl_state_memory_fupd (K m) s) =
     wl_state_memory_fupd (K m) (wl_push_env env params s)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN PAIRARG_TAC THEN SIMP[]);;

(* HOL4 [local] *)
let push_env_mem_const = prove
 (`!env params (s:(A,C,FFI)wl_state).
     wl_state_memory (wl_push_env env params s) = wl_state_memory s /\
     wl_state_mdomain (wl_push_env env params s) = wl_state_mdomain s`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN PAIRARG_TAC THEN SIMP[]);;

(* HOL4 [local] *)
let cut_state_with_mem_const = prove
 (`!x (s:(A,C,FFI)wl_state) m.
     wl_cut_state x (wl_state_memory_fupd (K m) s) =
     OPTION_MAP (\s'. wl_state_memory_fupd (K m) s') (wl_cut_state x s)`,
  REPEAT GEN_TAC THEN SIMP[wl_cut_state_def] THEN
  QCASES_ON "wl_cut_env x (wl_state_locals (s:(A,C,FFI)wl_state))" THEN SIMP[OPTION_MAP_DEF]);;

(* memory update lemma for evaluate.  HOL4 proves it by recInduct           *)
(* evaluate_ind and per-statement automation (suspend/resume for Loop).     *)
(* Here: the same induction; the statements without recursive calls by     *)
(* simplification; the others by following the two evaluations (the        *)
(* original and the one with memory m) in step, using the induction         *)
(* hypotheses on the sub-evaluations (PTOPAUX_MS_SPLIT_TAC).               *)

let PTOPAUX_jump_exc_mem = prove
 (`!(s:(A,C,FFI)wl_state) m.
     wl_jump_exc (wl_state_memory_fupd (K m) s) =
     OPTION_MAP (\(t,l1,l2). (wl_state_memory_fupd (K m) t,l1,l2)) (wl_jump_exc s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[OPTION_MAP_DEF] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]));;

let PTOPAUX_jump_exc_memory = prove
 (`!(s:(A,C,FFI)wl_state) t l1 l2.
     wl_jump_exc s = SOME (t,l1,l2) ==> wl_state_memory t = wl_state_memory s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  COND_CASES_TAC THEN SIMP[] THEN REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

let PTOPAUX_call_env_mem = prove
 (`!args sz (s:(A,C,FFI)wl_state) m.
     wl_call_env args sz (wl_state_memory_fupd (K m) s) =
     wl_state_memory_fupd (K m) (wl_call_env args sz s)`,
  SIMP[wl_call_env_def]);;

let PTOPAUX_pop_env_mem = prove
 (`!(s:(A,C,FFI)wl_state) m.
     wl_pop_env (wl_state_memory_fupd (K m) s) =
     OPTION_MAP (wl_state_memory_fupd (K m)) (wl_pop_env s)`,
  REPEAT GEN_TAC THEN SIMP[wl_pop_env_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]));;

let PTOPAUX_MS_RWS = DE_MORGAN_THM :: distinctness "wl_prog" ::
                     wordConvs_no_install_def :: no_alloc_def :: IL2AUX_dec_rws;;

(* the facts about code, for the MESON calls below *)
let PTOPAUX_code_fact th =
  let c = concl th in
  (try mem (fst(dest_const(fst(strip_comb c))))
         ["no_install_code"; "no_alloc_code"; "wordConvs_no_install"; "no_alloc"]
   with Failure _ -> false) ||
  (is_eq c && (try fst(dest_const(fst(strip_comb (lhs c)))) = "wl_state_code"
               with Failure _ -> false));;

let PTOPAUX_mem_eq th =
  let c = concl th in
  is_eq c &&
  (try mem (fst(dest_const(fst(strip_comb (lhs c))))) ["wl_state_memory"; "wl_state_mdomain"] &&
       not (lhs c = rhs c)
   with Failure _ -> false);;

(* strip an existential theorem with fresh genvars *)
let rec PTOPAUX_GSTRIP_TAC (th:thm) : tactic =
  if is_exists (concl th) then
    let v,_ = dest_exists (concl th) in
    X_CHOOSE_THEN (genvar (type_of v)) PTOPAUX_GSTRIP_TAC th
  else if is_conj (concl th) then CONJUNCTS_THEN PTOPAUX_GSTRIP_TAC th
  else ASSUME_TAC th;;

(* IL2AUX_fwd_m and IL2AUX_IH_FWD_M_TAC of wordProps.ml: an induction       *)
(* hypothesis used forward, its antecedents matched with the assumptions,  *)
(* instantiated by equations, or (no_install_code and no_alloc_code of a   *)
(* code) proved by MESON from the code facts; the memory equations of the  *)
(* assumptions rewrite it first                                             *)

let PTOPAUX_fwd_m (rws:thm list) (facts:thm list) (ih:thm) : thm =
  let simple = filter PTOPAUX_code_fact facts in
  let rec go th =
    let vs,bod = strip_forall (concl th) in
    if not (is_imp bod) then th else
    let ant = fst (dest_imp bod) in
    try tryfind (fun f -> go (REWRITE_RULE rws (MATCH_MP th f))) facts
    with Failure _ ->
    try go (IL2AUX_fwd_eq th) with Failure _ ->
      if exists (fun v -> vfree_in v ant) vs then failwith "PTOPAUX_fwd_m" else
      let ath = try EQT_ELIM (REWRITE_CONV IL2AUX_res_rws ant)
                with Failure _ ->
                  if (try mem (fst(dest_const(fst(strip_comb ant))))
                            ["no_install_code"; "no_alloc_code"]
                      with Failure _ -> false)
                  then MESON simple ant else failwith "PTOPAUX_fwd_m" in
      go (MP (SPEC_ALL th) ath) in
  go (REWRITE_RULE[IMP_CONJ] ih);;

let PTOPAUX_IH_FWD_M_TAC (rws:thm list) : tactic =
  REPEAT (FIRST_X_ASSUM (fun ih (asl,w as g) ->
    if not (is_forall (concl ih) || is_imp (concl ih)) then failwith "" else
    let meqs = filter PTOPAUX_mem_eq (map snd asl) in
    let rws' = rws @ meqs in
    let th = PTOPAUX_fwd_m rws' (map snd asl) (REWRITE_RULE rws' ih) in
    PTOPAUX_GSTRIP_TAC (CAKE_SIMP_RULE [] th) g));;

(* the code facts wl_state_code s0 = wl_state_code s1 of the evaluations    *)
(* wl_evaluate (p,s0) = (r,s1) of the assumptions                          *)

let PTOPAUX_CODE_FWD_TAC : tactic = fun (asl,w as g) ->
  let simple = filter PTOPAUX_code_fact (map snd asl) in
  let rws = wordConvs_no_install_def :: no_alloc_def :: IL2AUX_dec_rws in
  let derive th =
    let l,r = dest_eq (concl th) in
    let p,s0 = dest_pair (rand l) in
    let res,s1 = dest_pair r in
    let lem = ISPECL [p; s0; res; s1] no_install_evaluate_const_code in
    let ant = fst (dest_imp (concl lem)) in
    let ath = TAC_PROOF((asl,ant), REWRITE_TAC (th :: rws) THEN MESON_TAC simple) in
    let r = REWRITE_RULE rws (MP lem ath) in
    if exists (fun (_,a) -> aconv (concl a) (concl r)) asl then failwith "known" else r in
  let new_facts = mapfilter (fun (_,th) ->
      if IL2AUX_is_eval_eq (concl th) then derive th else failwith "") asl in
  MAP_EVERY ASSUME_TAC new_facts g;;

(* name the pair of the first evaluation of the antecedent (genvars)        *)
let PTOPAUX_PAIR_EVAL_TAC : tactic = fun (asl,w as g) ->
  let ev = find_term (fun t -> try fst(dest_const(rator t)) = "wl_evaluate"
                               with Failure _ -> false) (lhand w) in
  let ty1,ty2 = (match dest_type (type_of ev) with (_,[a;b]) -> a,b
                                                 | _ -> failwith "PTOPAUX_PAIR_EVAL_TAC") in
  let r = genvar ty1 and t = genvar ty2 in
  X_CHOOSE_THEN r (X_CHOOSE_THEN t (fun th -> ASSUME_TAC th THEN PURE_REWRITE_TAC[th]))
    (ISPEC ev PAIR_SURJECTIVE) g;;

let PTOPAUX_MEM_UPD_TAC : tactic =
  ASSUM_LIST (fun ths -> MAP_EVERY (PTOPAUX_GSTRIP_TAC o MATCH_MP mem_upd_lemma)
    (filter (can (MATCH_MP mem_upd_lemma)) ths));;

let PTOPAUX_MS_NORM_ASM_TAC : tactic =
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else REWRITE_RULE PTOPAUX_MS_RWS th) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* the goal ?st'. wl_evaluate X = (r,st') /\ P st' with an assumption      *)
(* wl_evaluate X = (r',t): the witness t                                    *)
let PTOPAUX_EVAL_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let ev = lhs (hd (conjuncts bod)) in
  let _,th = find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = ev) asl in
  let t = rand (rhs (concl th)) in
  (EXISTS_TAC t THEN REWRITE_TAC[th; PAIR_EQ]) g;;

(* the induction hypotheses on the evaluations of the assumptions; the     *)
(* states st' they give for the evaluations with the other memory are      *)
(* written t with memory := m' (mem_upd_lemma)                             *)
let PTOPAUX_MS_STEP_TAC : tactic =
  PTOPAUX_MS_NORM_ASM_TAC THEN RVEQ_TAC THEN
  IL2AUX_POP_CONST_TAC THEN
  IL2AUX_LEMMA_FWD_TAC [no_install_find_code; no_alloc_find_code] THEN
  PTOPAUX_CODE_FWD_TAC THEN
  PTOPAUX_IH_FWD_M_TAC PTOPAUX_MS_RWS THEN
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else CAKE_SIMP_RULE [] th) THEN
  PTOPAUX_MEM_UPD_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else CAKE_SIMP_RULE [] th) THEN
  TRY (PTOPAUX_EVAL_EXISTS_TAC THEN REWRITE_TAC IL2AUX_dec_rws THEN ASM_REWRITE_TAC[] THEN
       NO_TAC) THEN
  SIMP[IGNASM "!x. _"];;

let PTOPAUX_MS_START_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC PTOPAUX_MS_RWS;;

let PTOPAUX_MS_SIMP_TAC : tactic =
  SIMP[IGNASM "!x. _"; PTOPAUX_call_env_mem; push_env_mem_upd; PTOPAUX_pop_env_mem;
       wl_dec_clock_def; OPTION_MAP_DEF; wl_flush_state_def];;

(* the first case scrutinee of the antecedent is an evaluation *)
let PTOPAUX_ANT_EVAL_FIRST w =
  let a = lhand w in
  let ev = find_term (fun t -> try fst(dest_const(rator t)) = "wl_evaluate"
                               with Failure _ -> false) a in
  let sc = try first_case_scrutinee a a with Failure _ -> ev in
  sc = ev;;

let PTOPAUX_MS_EVAL_STEP_TAC : tactic = fun (asl,w as g) ->
  if not (PTOPAUX_ANT_EVAL_FIRST w) then failwith "PTOPAUX_MS_EVAL_STEP_TAC" else
  (PTOPAUX_PAIR_EVAL_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN PTOPAUX_MS_STEP_TAC THEN
   TRY (FIRST_X_ASSUM (MP_TAC o check (fun th -> is_eq (concl th) &&
                         rhs (concl th) = rand (lhand w))))) g;;

let PTOPAUX_MS_CLOSE_TAC : tactic =
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_FACTS_TAC [cut_state_const] THEN IL2AUX_POP_CONST_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[] THEN
  SIMP[IGNASM "!x. _"; wl_flush_state_def; wl_dec_clock_def; cut_state_with_mem_const;
       OPTION_MAP_DEF] THEN NO_TAC;;

(* one step of following the two evaluations: close a final branch, split *)
(* a condition or a case, or use the induction hypotheses on an evaluation *)
let PTOPAUX_MS_SPLIT_TAC : tactic =
  FIRST [PTOPAUX_MS_CLOSE_TAC;
         COND_CASES_TAC THEN PTOPAUX_MS_SIMP_TAC;
         PTOPAUX_MS_EVAL_STEP_TAC;
         TOP_CASE_TAC THEN PTOPAUX_MS_SIMP_TAC];;

let PTOPAUX_MS_REC_TAC : tactic =
  PTOPAUX_MS_START_TAC THEN
  SIMP[IGNASM "!x. _"; PTOPAUX_call_env_mem; push_env_mem_upd; PTOPAUX_pop_env_mem;
       cut_state_with_mem_const; wl_dec_clock_def; OPTION_MAP_DEF] THEN
  REPEAT PTOPAUX_MS_SPLIT_TAC;;

(* the statements without recursive calls *)
let PTOPAUX_MS_SIMPLE_TAC : tactic =
  RW[wl_evaluate_def; no_alloc_def; wordConvs_no_install_def] THEN
  FS[wl_call_env_def; wl_flush_state_def; wl_dec_clock_def] THEN
  GVS(all_case_eqs()) THEN
  GVS[wl_set_vars_def; wl_set_store_def; wl_get_var_def; wl_set_var_def; wl_unset_var_def;
      wl_mem_store_def; wl_get_store_def; const_writes_const_memory] THEN
  TRY (MATCH_MP_TAC const_writes_const_memory THEN ASM_REWRITE_TAC[]);;

let PTOPAUX_MS_STORE_TAC : tactic =
  PTOPAUX_MS_SIMPLE_TAC THEN
  TRY (FIRST_X_ASSUM (MP_TAC o check (fun th -> is_eq (concl th) &&
                                                is_cond (lhs (concl th)))) THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
       REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[]) THEN
  MATCH_MP_TAC fun2set_update_eq THEN ASM_REWRITE_TAC[];;

let PTOPAUX_MS_INST_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`i:(A)inst`; `s:(A,C,FFI)wl_state`; `m:A word->(A)word_loc`]
                 inst_const_memory) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  QCASES_ON "wl_inst (i:(A)inst) (s:(A,C,FFI)wl_state)" THEN
  CASE_REWRITE_TAC[THE_DEF; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV let_CONV)) THEN
  QCASES_ON "wl_inst (i:(A)inst) (wl_state_memory_fupd (K (m:A word->(A)word_loc)) s)" THEN
  FS[THE_DEF] THEN GVS[];;

let PTOPAUX_MS_RAISE_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[PTOPAUX_jump_exc_mem; wl_get_var_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF; wl_flush_state_def]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  IMP_RES_TAC jump_exc_const THEN IMP_RES_TAC PTOPAUX_jump_exc_memory THEN ASM_SIMP_TAC[];;

let PTOPAUX_MS_FFI_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  FIRST_ASSUM (fun th ->
    let l = GSYM (MATCH_MP read_bytearray_const_memory th) in
    RW[wl_evaluate_def; no_alloc_def; wordConvs_no_install_def; l] THEN
    FS[wl_call_env_def; wl_flush_state_def; wl_dec_clock_def] THEN
    GVS(all_case_eqs()) THEN
    GVS[wl_get_var_def; l]) THEN
  TRY (MATCH_MP_TAC write_bytearray_const_memory THEN ASM_REWRITE_TAC[]);;

let PTOPAUX_MS_SHARE_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP word_exp_const_memory th]) THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN
  TRY (STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN NO_TAC) THEN
  DISCH_TAC THEN
  FIRST_ASSUM (fun th -> FIRST_ASSUM (fun th2 ->
    STRIP_ASSUME_TAC (MATCH_MP share_inst_const_memory (CONJ th2 th)))) THEN
  SIMP[];;

let PTOPAUX_MS_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_FACTS_TAC [cut_state_const] THEN RVEQ_TAC THEN
  SIMP[IGNASM "!x. _"; wl_flush_state_def; wl_dec_clock_def; cut_state_with_mem_const;
       OPTION_MAP_DEF];;

let PTOPAUX_MS_LOOP_TAC : tactic =
  PTOPAUX_MS_START_TAC THEN SIMP[cut_state_with_mem_const; OPTION_MAP_DEF] THEN
  TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF] THEN TRY (PTOPAUX_MS_FIN_TAC THEN NO_TAC) THEN
  IL2AUX_FACTS_TAC [cut_state_const] THEN RVEQ_TAC THEN
  PTOPAUX_PAIR_EVAL_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN PTOPAUX_MS_STEP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [PTOPAUX_MS_FIN_TAC;
      DISCH_TAC THEN PTOPAUX_MS_STEP_TAC];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [SIMP[IGNASM "!x. _"; cut_state_with_mem_const] THEN TOP_CASE_TAC THEN
      SIMP[IGNASM "!x. _"; OPTION_MAP_DEF] THEN PTOPAUX_MS_FIN_TAC;
      PTOPAUX_MS_FIN_TAC]];;
let memory_swap_lemma1 = prove
 (`!prog (st:(A,C,FFI)wl_state) res rst m.
     wl_evaluate (prog,st) = (res,rst) /\
     fun2set (wl_state_memory st,wl_state_mdomain st) =
     fun2set (m,wl_state_mdomain st) /\
     no_alloc_code (wl_state_code st) /\ no_install_code (wl_state_code st) /\
     no_alloc prog /\ wordConvs_no_install prog ==>
     ?st'. wl_evaluate (prog,wl_state_memory_fupd (K m) st) = (res,st') /\
           wl_state_memory_fupd (K ARB) st' = wl_state_memory_fupd (K ARB) rst /\
           fun2set (wl_state_memory rst,wl_state_mdomain rst) =
           fun2set (wl_state_memory st',wl_state_mdomain rst)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (replicate PTOPAUX_MS_SIMPLE_TAC 4 @         (* Skip Alloc StoreConsts Move *)
    [PTOPAUX_MS_INST_TAC] @                    (* Inst *)
    replicate PTOPAUX_MS_SIMPLE_TAC 4 @         (* Assign Get Set OpCurrHeap *)
    [PTOPAUX_MS_STORE_TAC; PTOPAUX_MS_SIMPLE_TAC] @ (* Store Tick *)
    [PTOPAUX_MS_REC_TAC; PTOPAUX_MS_REC_TAC;    (* MustTerminate Seq *)
     PTOPAUX_MS_SIMPLE_TAC; PTOPAUX_MS_RAISE_TAC; (* Return Raise *)
     PTOPAUX_MS_SIMPLE_TAC; PTOPAUX_MS_SIMPLE_TAC; (* Break Continue *)
     PTOPAUX_MS_REC_TAC; PTOPAUX_MS_LOOP_TAC] @   (* If Loop *)
    replicate PTOPAUX_MS_SIMPLE_TAC 4 @         (* LocValue Install CodeBufferWrite DataBufferWrite *)
    [PTOPAUX_MS_FFI_TAC; PTOPAUX_MS_SHARE_TAC; PTOPAUX_MS_REC_TAC]));; (* FFI ShareInst Call *)

(* avoid changing subsequent proof by rephrasing back into earlier form *)
(* HOL4 [local] *)
let memory_swap_lemma = prove
 (`!prog (st:(A,C,FFI)wl_state) res rst m.
     wl_evaluate (prog,st) = (res,rst) /\
     fun2set (wl_state_memory st,wl_state_mdomain st) =
     fun2set (m,wl_state_mdomain st) /\
     no_alloc_code (wl_state_code st) /\ no_install_code (wl_state_code st) /\
     no_alloc prog /\ wordConvs_no_install prog ==>
     ?m'. wl_evaluate (prog,wl_state_memory_fupd (K m) st) =
          (res,wl_state_memory_fupd (K m') rst) /\
          fun2set (wl_state_memory rst,wl_state_mdomain rst) =
          fun2set (m',wl_state_mdomain rst)`,
  REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP memory_swap_lemma1) THEN
  DISCH_THEN (X_CHOOSE_THEN `st':(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM (X_CHOOSE_THEN `m':A word->(A)word_loc` SUBST_ALL_TAC o
               MATCH_MP mem_upd_lemma) THEN
  EXISTS_TAC `m':A word->(A)word_loc` THEN
  RULE_ASSUM_TAC (CAKE_SIMP_RULE []) THEN ASM_REWRITE_TAC[]);;

(* wordSem's semantics depends only on the results and the ffi states of   *)
(* the runs                                                                 *)
let PTOPAUX_wl_semantics_cong = prove
 (`!(s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state) start.
     (!k. FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                            wl_state_clock_fupd (K k) s1)) =
          FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                            wl_state_clock_fupd (K k) s2)) /\
          wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                          wl_state_clock_fupd (K k) s1))) =
          wl_state_ffi (SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                                          wl_state_clock_fupd (K k) s2)))) ==>
     wl_semantics s1 start = wl_semantics s2 start`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wl_semantics_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!(p:((A)wl_result)option#(A,C,FFI)wl_state) r t.
                  p = (r,t) <=> FST p = r /\ SND p = t`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1; UNWIND_THM2;
              GSYM CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[]);;

let word_semantics_memory_update = prove
 (`!(s:(A,C,FFI)wl_state) m start.
     fun2set (wl_state_memory s,wl_state_mdomain s) = fun2set (m,wl_state_mdomain s) /\
     no_alloc_code (wl_state_code s) /\ no_install_code (wl_state_code s) ==>
     ~(wl_semantics (wl_state_memory_fupd (K m) s) start = Fail) ==>
     wl_semantics s start = wl_semantics (wl_state_memory_fupd (K m) s) start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`s:(A,C,FFI)wl_state`;
                        `wl_state_memory_fupd (K (m:A word->(A)word_loc)) (s:(A,C,FFI)wl_state)`;
                        `start:num`] PTOPAUX_wl_semantics_cong) THEN
  X_GEN_TAC `k:num` THEN
  MP_TAC (ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                  `wl_state_clock_fupd (K k) (s:(A,C,FFI)wl_state)`;
                  `FST (wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                                     wl_state_clock_fupd (K k) (s:(A,C,FFI)wl_state)))`;
                  `SND (wl_evaluate (wl_Call NONE (SOME start) [0] NONE:(A)wl_prog,
                                     wl_state_clock_fupd (K k) (s:(A,C,FFI)wl_state)))`;
                  `m:A word->(A)word_loc`] memory_swap_lemma) THEN
  ANTS_TAC THENL [SIMP[no_alloc_def; wordConvs_no_install_def] THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  STRIP_TAC THEN SIMP[]);;

(* the functions of word_to_word_compile_single keep the subprograms they do *)
(* not create (compile_single_not_created_subprogs), for every function of   *)
(* the compiled list                                                         *)

let PTOPAUX_compile_single_names = prove
 (`!tt kk aa (co:(A)asm_config) a b q c.
     FST (word_to_word_compile_single tt kk aa co ((a,b,q),c)) = a /\
     FST (SND (word_to_word_compile_single tt kk aa co ((a,b,q),c))) = b`,
  REWRITE_TAC[word_to_word_compile_single_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND]);;

let PTOPAUX_compile_single_subprogs = prove
 (`!P (progs0:(num#num#(A)wl_prog)list) x tt kk aa (co:(A)asm_config).
     ALL_DISTINCT (MAP FST progs0) /\ LENGTH progs0 = LENGTH x /\
     (!k n p. lookup k (fromAList progs0) = SOME (n,p) ==> not_created_subprogs P p) ==>
     !k n p. lookup k (fromAList (MAP (word_to_word_compile_single tt kk aa co)
                                      (ZIP progs0 x))) = SOME (n,p) ==>
             not_created_subprogs P p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lookup_fromAList] THEN
  REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
  DISCH_THEN (X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `q:(A)wl_prog`
    (X_CHOOSE_THEN `c:(num spt)option` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM (fun th ->
    let th1 = CONV_RULE (BINOP_CONV BETA_CONV)
                (AP_TERM `\x:num#num#(A)wl_prog. SND (SND x)` th) in
    let th2 = CONV_RULE (BINOP_CONV BETA_CONV) (AP_TERM `\x:num#num#(A)wl_prog. FST x` th) in
    SUBST1_TAC (REWRITE_RULE[SND] th1) THEN
    ASSUME_TAC (REWRITE_RULE[FST; PTOPAUX_compile_single_names] th2)) THEN
  MATCH_MP_TAC compile_single_not_created_subprogs THEN
  REWRITE_TAC[FST; SND] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN REWRITE_TAC[lookup_fromAList] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb (concl th)))) = "MEM" with Failure _ -> false)) THEN
  ASM_SIMP_TAC[MEM_ZIP; PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[]);;

let word_to_word_compile_no_install_no_alloc = prove
 (`!wconf (aconf:(A)asm_config) progs0 col progs.
     word_to_word_compile wconf aconf progs0 = (col,progs) /\
     ALL_DISTINCT (MAP FST progs0) /\
     no_mt_code (fromAList progs0) /\
     no_install_code (fromAList progs0) ==>
     no_install_code (fromAList progs) /\
     (no_alloc_code (fromAList progs0) ==> no_alloc_code (fromAList progs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_word_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIR_CASES_ON `next_n_oracle (LENGTH (progs0:(num#num#(A)wl_prog)list))
                   (word_to_word_config_col_oracle wconf)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP BACKDEFAUX_LENGTH_next_n_oracle) THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> is_var (rhs (concl th)) && 
     (try fst(dest_const(fst(strip_comb (lhs (concl th))))) = "MAP" with Failure _ -> false))) THEN
  W(fun (asl,w) -> MP_TAC (ISPECL
     [`progs0:(num#num#(A)wl_prog)list`; `p0:((num spt)option)list`;
      `asm_config_two_reg_arith (aconf:(A)asm_config)`;
      `asm_config_reg_count (aconf:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs aconf))`;
      `word_to_word_config_reg_alg wconf`; `aconf:(A)asm_config`]
     no_mt_code_full_compile_single)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[no_install_code_def; no_alloc_code_def;
                                wordConvs_no_install_subprogs_def; no_alloc_subprogs_def]) THEN
  REWRITE_TAC[no_install_code_def; no_alloc_code_def; wordConvs_no_install_subprogs_def;
              no_alloc_subprogs_def] THEN
  CONJ_TAC THENL [ALL_TAC; DISCH_TAC] THEN MATCH_MP_TAC PTOPAUX_compile_single_subprogs THEN
  ASM_REWRITE_TAC[]);;


(* the evaluate cases of a fact about the final state, as IL2AUX_NI_TAC:   *)
(* split the evaluation, the facts of the steps, the induction hypotheses *)
(* (after the code facts of no_install_evaluate_const_code)                *)

let PTOPAUX_EVAL_FWD_TAC (facts:thm list) (fin:tactic) : tactic =
  let rws = wordConvs_no_install_def :: no_alloc_def :: IL2AUX_dec_rws in
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM (MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  DISCH_THEN(REPEAT_TCL STRIP_THM_THEN ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (fun th -> if is_forall (concl th) || is_imp (concl th) then th
                            else CASE_REWRITE_RULE []
                                   (REWRITE_RULE rws (CASE_REWRITE_RULE [] th))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE (injectivity "wl_prog" :: distinctness "wl_prog" ::
                               IL2AUX_res_rws)) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  IL2AUX_POP_CONST_TAC THEN
  IL2AUX_FACTS_TAC facts THEN
  IL2AUX_LEMMA_FWD_TAC [no_install_find_code; no_alloc_find_code] THEN
  IL2AUX_SUBST_VARS_TAC THEN
  PTOPAUX_CODE_FWD_TAC THEN PTOPAUX_IH_FWD_M_TAC rws THEN
  PTOPAUX_CODE_FWD_TAC THEN PTOPAUX_IH_FWD_M_TAC rws THEN
  IL2AUX_DROP_IHS_TAC THEN fin;;

let PTOPAUX_exit_loop_NES = prove
 (`!x:((W)wl_result)option.
     wl_exit_loop x = SOME NotEnoughSpace ==> x = SOME NotEnoughSpace`,
  GEN_TAC THEN QCASES_ON "x:((W)wl_result)option" THEN SIMP[wl_exit_loop_def] THEN
  QCASES_ON "a:(W)wl_result" THEN SIMP[wl_exit_loop_def]);;

let PTOPAUX_share_inst_NES = prove
 (`!op v ad (s:(A,C,FFI)wl_state) (res:((W)wl_result)option) t.
     share_inst op v ad s = (res,t) ==> ~(res = SOME NotEnoughSpace)`,
  REPEAT GEN_TAC THEN QCASES_ON "op:memop" THEN
  SIMP[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def; wl_sh_mem_load16_def;
       wl_sh_mem_load32_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
       wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[sh_mem_set_var_def]) THEN
  TRY (PTOPAUX_FFI_CASES_TAC THEN SIMP[sh_mem_set_var_def]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN FS[]);;

let PTOPAUX_NES_TAC : tactic =
  PTOPAUX_EVAL_FWD_TAC [inst_const_full; mem_store_const; jump_exc_const; cut_state_const;
                        PTOPAUX_share_inst_NES; PTOPAUX_exit_loop_NES]
    (FS[wl_flush_state_def; wl_dec_clock_def; wl_call_env_def] THEN
     RULE_ASSUM_TAC (REWRITE_RULE IL2AUX_res_rws) THEN ASM_MESON_TAC IL2AUX_res_rws);;

let no_alloc_word_evaluate = prove
 (`!prog (s:(A,C,FFI)wl_state) res t.
     wl_evaluate (prog,s) = (res,t) /\
     no_install_code (wl_state_code s) /\ no_alloc_code (wl_state_code s) /\
     wordConvs_no_install prog /\ no_alloc prog ==>
     ~(res = SOME NotEnoughSpace)`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN PTOPAUX_NES_TAC);;

let panLang_wordSem_neq_NotEnoughSpace = prove
 (`!start (s:(A,C,FFI)wl_state) k res t (pan_code:((A)decl)list) (c:backend_config)
    (mc:(A,B,D)machine_config) col wprog.
     wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K k) s) =
       (res,t) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc))
       (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
          pan_code) = (col,wprog) /\
     wl_state_code s = fromAList wprog ==>
     ~(res = SOME NotEnoughSpace)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`backend_config_word_to_word_conf c`;
                  `target_config (machine_config_target (mc:(A,B,D)machine_config))`;
                  `pan_to_word_compile_prog (asm_config_ISA (target_config
                     (machine_config_target (mc:(A,B,D)machine_config)))) (pan_code:((A)decl)list)`;
                  `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`]
                 word_to_word_compile_no_install_no_alloc) THEN
  ANTS_TAC THENL
  [ASM_MESON_TAC[pan_to_wordProof_first_compile_prog_all_distinct;
                 pan_to_word_compile_prog_no_mt_code; pan_to_word_compile_prog_no_install_code];
   ALL_TAC] THEN
  SUBGOAL_THEN `no_alloc_code (fromAList (pan_to_word_compile_prog (asm_config_ISA
                  (target_config (machine_config_target (mc:(A,B,D)machine_config))))
                  (pan_code:((A)decl)list)))` ASSUME_TAC THENL
  [ASM_MESON_TAC[pan_to_word_compile_prog_no_alloc_code]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC no_alloc_word_evaluate THEN
  MAP_EVERY EXISTS_TAC [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                        `wl_state_clock_fupd (K k) (s:(A,C,FFI)wl_state)`;
                        `t:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN SIMP[no_alloc_def; wordConvs_no_install_def] THEN
  ASM_REWRITE_TAC[]);;

let inst_stack_size_const_panLang = prove
 (`!i (s:(A,C,FFI)wl_state) t.
     wl_inst i s = SOME t ==> wl_state_stack_size t = wl_state_stack_size s`,
  MESON_TAC[inst_const_full]);;

let inst_stack_limit_const_panLang = prove
 (`!i (s:(A,C,FFI)wl_state) t.
     wl_inst i s = SOME t ==> wl_state_stack_limit t = wl_state_stack_limit s`,
  MESON_TAC[inst_const_full]);;

let inst_stack_max_const_panLang = prove
 (`!i (s:(A,C,FFI)wl_state) t.
     wl_inst i s = SOME t ==> wl_state_stack_max t = wl_state_stack_max s`,
  MESON_TAC[inst_const_full]);;

let share_inst_modifies = prove
 (`!op v ad (s:(A,C,FFI)wl_state) (res:((W)wl_result)option) t.
     share_inst op v ad s = (res,t) ==>
     ?ls ffi stk lsz st.
       t = wl_state_locals_fupd (K ls) (wl_state_ffi_fupd (K ffi)
             (wl_state_stack_fupd (K stk) (wl_state_locals_size_fupd (K lsz)
               (wl_state_store_fupd (K st) s))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`wl_state_locals (t:(A,C,FFI)wl_state)`; `wl_state_ffi (t:(A,C,FFI)wl_state)`;
                        `wl_state_stack (t:(A,C,FFI)wl_state)`;
                        `wl_state_locals_size (t:(A,C,FFI)wl_state)`;
                        `wl_state_store (t:(A,C,FFI)wl_state)`] THEN
  POP_ASSUM MP_TAC THEN QCASES_ON "op:memop" THEN
  SIMP[share_inst_def; wl_sh_mem_load_def; wl_sh_mem_load_byte_def; wl_sh_mem_load16_def;
       wl_sh_mem_load32_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
       wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[sh_mem_set_var_def]) THEN
  TRY (PTOPAUX_FFI_CASES_TAC THEN SIMP[sh_mem_set_var_def]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  SIMP[wl_set_var_def; wl_flush_state_def; wl_state_component_equality]);;

let PTOPAUX_share_inst_stack_size = prove
 (`!op v ad (s:(A,C,FFI)wl_state) (res:((W)wl_result)option) t.
     share_inst op v ad s = (res,t) ==>
     wl_state_stack_size t = wl_state_stack_size s /\
     wl_state_stack_limit t = wl_state_stack_limit s`,
  REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP share_inst_modifies) THEN
  ASM_SIMP_TAC[] THEN SIMP[]);;

let PTOPAUX_SS_TAC : tactic =
  PTOPAUX_EVAL_FWD_TAC
    [inst_const_full; mem_store_const; jump_exc_const;
     PTOPAUX_share_inst_stack_size; cut_state_const]
    (FS[wl_flush_state_def; wl_dec_clock_def; wl_call_env_def; wl_set_var_def;
        wl_set_vars_def; wl_unset_var_def; wl_set_store_def; wl_mem_store_def] THEN
     ASM_MESON_TAC[]);;

let evaluate_stack_size_limit_const_panLang = prove
 (`!prog (s:(A,C,FFI)wl_state) res t.
     wl_evaluate (prog,s) = (res,t) /\
     wordConvs_no_install prog /\ no_install_code (wl_state_code s) /\
     no_alloc prog /\ no_alloc_code (wl_state_code s) ==>
     wl_state_stack_size t = wl_state_stack_size s /\
     wl_state_stack_limit t = wl_state_stack_limit s`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THEN PTOPAUX_SS_TAC);;

let option_lt_SOME = prove
 (`!x n. option_lt x (SOME n) <=> (?m. x = SOME m /\ m < n)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:num option` (cases "option")) THEN
  REWRITE_TAC[option_lt_def; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let from_pan_to_lab_no_install = prove
 (`!(pan_code:((A)decl)list) (ac:(A)asm_config) isa wprog0 wc col wprog bm c fs p scc dc lim
    regc off.
     ALL_DISTINCT (MAP FST (functions pan_code)) /\ ~(asm_config_ISA ac = Ag32) /\
     pan_to_word_compile_prog isa pan_code = wprog0 /\
     word_to_word_compile wc ac wprog0 = (col,wprog) /\
     word_to_stack_compile ac F wprog = (bm,c,fs,p)
     ==> lab_no_install (stack_to_lab_compile scc dc lim regc off p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (wprog0:(num#num#(A)wl_prog)list)) /\
                no_install_code (fromAList wprog0) /\ no_mt_code (fromAList wprog0)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC[pan_to_wordProof_first_compile_prog_all_distinct;
                 pan_to_word_compile_prog_no_install_code; pan_to_word_compile_prog_no_mt_code];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`wc:word_to_word_config`; `ac:(A)asm_config`;
                  `wprog0:(num#num#(A)wl_prog)list`; `col:(((num)spt)option)list`;
                  `wprog:(num#num#(A)wl_prog)list`] word_to_word_compile_no_install_no_alloc) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAP FST (wprog:(num#num#(A)wl_prog)list) = MAP FST (wprog0:(num#num#(A)wl_prog)list)`
    ASSUME_TAC THENL
  [MP_TAC (MATCH_MP compile_to_word_conventions2
     (CONJ (ASSUME `word_to_word_compile wc (ac:(A)asm_config) wprog0 = (col,wprog)`)
           (SPEC `wprog0:(num#num#(A)wl_prog)list` (MATCH_MP PTOPAUX_ALL_no_share_Ag32
              (ASSUME `~(asm_config_ISA (ac:(A)asm_config) = Ag32)`))))) THEN
   SIMP_TAC[];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`wprog:(num#num#(A)wl_prog)list`; `ac:(A)asm_config`; `bm:(A word)list`;
                  `c:word_to_stack_config`; `fs:num list`; `p:(num#(A)stack_prog)list`]
                 word_to_stack_compile_no_install) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC (ISPECL [`p:(num#(A)stack_prog)list`;
                        `stack_to_lab_compile scc dc lim regc off (p:(num#(A)stack_prog)list)`;
                        `scc:stack_to_lab_config`; `dc:data_to_word_config`; `lim:num`;
                        `regc:num`; `off:A word#A word`] stack_to_lab_compile_no_install) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let n2w_sub_alt = prove
 (`!a b. b <= a ==>
         word (a - b):A word = word_add (word a) (word_mul (word_neg (word 1)) (word b))`,
  SIMP_TAC[n2w_sub] THEN REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* HOL4 [local] *)
let aligned_n2w_IMP = prove
 (`!k n. alignment_aligned k (word n:A word) /\ n < dimword(:A) ==> (2 EXP k) divides n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_w2n; w2n_n2w] THEN STRIP_TAC THEN
  REWRITE_TAC[DIVIDES_MOD] THEN ASM_MESON_TAC[MOD_LT]);;

(* the main step of word_list_exists_addresses, by induction on n *)
let PTOPAUX_wle_addresses = prove
 (`!n m (a:A word) (d:A word->B).
     good_dimindex(:A) /\ m < dimword(:A) DIV (dimindex(:A) DIV 8) /\
     word_list_exists a n (fun2set (d,addresses a m)) ==> n = m`,
  INDUCT_TAC THEN REWRITE_TAC[stack_removeProof_word_list_exists_thm] THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[emp_def; fun2set_EMPTY] THEN
   STRUCT_CASES_TAC (SPEC `m:num` num_CASES) THEN
   REWRITE_TAC[addresses_def; NOT_INSERT_EMPTY; NOT_SUC];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SEP_EXISTS_THM; one_fun2set] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(dimindex(:A) DIV 8 = 0)` ASSUME_TAC THENL
  [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
   ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m':num` SUBST_ALL_TAC)
    (SPEC `m:num` num_CASES) THENL
  [UNDISCH_TAC `(a:A word) IN addresses a 0` THEN REWRITE_TAC[addresses_def; NOT_IN_EMPTY];
   ALL_TAC] THEN
  REWRITE_TAC[SUC_INJ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`word_add (a:A word) bytes_in_word`; `d:A word->B`] THEN
  SUBGOAL_THEN `m' < dimword(:A) DIV (dimindex(:A) DIV 8) /\
                m' * (dimindex(:A) DIV 8) < dimword(:A)` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `SUC m' < dimword(:A) DIV (dimindex(:A) DIV 8)` THEN
   ASM_SIMP_TAC[GSYM LE_SUC_LT; LE_RDIV_EQ] THEN REWRITE_TAC[MULT_CLAUSES] THEN
   MP_TAC (SPECL [`m':num`; `dimindex(:A) DIV 8`] MULT_SYM) THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `addresses (a:A word) (SUC m') DELETE a = addresses (word_add a bytes_in_word) m'`
    (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[addresses_def] THEN
  MP_TAC (ISPECL [`a:A word`; `m':num`] STACKPROPSAUX_not_in_addresses) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* HOL4 word_list_exists_addresses (TODO: move) *)
let pan_to_targetProof_word_list_exists_addresses = prove
 (`!(a:A word) n (d:A word->B) m.
     word_list_exists a n (fun2set (d,addresses a m)) /\ good_dimindex(:A) /\
     m < dimword(:A) DIV val(bytes_in_word:A word) ==> n = m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PTOPAUX_wle_addresses THEN
  MAP_EVERY EXISTS_TAC [`a:A word`; `d:A word->B`] THEN
  ASM_MESON_TAC[BKP2AUX_val_bytes_in_word]);;

let good_dimindex_div_mul = prove
 (`!a. good_dimindex(:A) ==> (a * dimindex(:A)) DIV 8 = a * (dimindex (:A) DIV 8)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `a * 32 = 8 * (a * 4)`; ARITH_RULE `a * 64 = 8 * (a * 8)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let InitGlobals_location_eq_first_name = prove
 (`InitGlobals_location = first_name`,
  REWRITE_TAC[InitGlobals_location_def; CopyGlobals_location_def; AllocGlobal_location_def;
              data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def; first_name_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* helpers of pan_to_target_compile_semantics *)

(* the passes of a successful compile_prog_max *)
let PTOPAUX_compile_prog_max_SOME = prove
 (`!(c:backend_config) (mc:(A,B,C)machine_config) (pan_code:((A)decl)list) bytes
    (bitmaps:(A word)list) c' stack_max.
     compile_prog_max c mc pan_code = (SOME (bytes,bitmaps,c'),stack_max) ==>
     ?col wprog c'' fs p.
       word_to_word_compile (backend_config_word_to_word_conf c)
         (target_config (machine_config_target mc))
         (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
            pan_code) = (col,wprog) /\
       word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
         (bitmaps,c'',fs,p) /\
       lab_to_target_compile (target_config (machine_config_target mc))
         (backend_config_lab_conf c)
         (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
            (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
            (asm_config_reg_count (target_config (machine_config_target mc)) -
             (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
            (asm_config_addr_offset (target_config (machine_config_target mc))) p) =
         SOME (bytes,backend_config_lab_conf c') /\
       stack_max = max_depth (word_to_stack_config_stack_frame_size c'')
                     (full_call_graph InitGlobals_location (fromAList wprog))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_prog_max_def; from_stack_def; from_lab_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIR_CASES_ON `word_to_word_compile (backend_config_word_to_word_conf c)
                   (target_config (machine_config_target (mc:(A,B,C)machine_config)))
                   (pan_to_word_compile_prog (asm_config_ISA (target_config
                      (machine_config_target mc))) (pan_code:((A)decl)list))` THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PAIR_CASES_ON `word_to_stack_compile (target_config (machine_config_target
                   (mc:(A,B,C)machine_config))) F (p1:(num#num#(A)wl_prog)list)` THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> try let h,args = strip_comb t in
                                   fst(dest_const h) = "lab_to_target_compile" &&
                                   length args = 3 with Failure _ -> false) (lhand w) in
    DISJ_CASES_THEN2
      (X_CHOOSE_THEN `r:byte list#lab_to_target_config`
         (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))
      SUBST1_TAC
      (ISPEC t option_CASES)) THEN
  REWRITE_TAC[attach_bitmaps_def; option_DISTINCT] THEN
  SUBGOAL_THEN `?b1 c1. (r:byte list#lab_to_target_config) = (b1,c1)` STRIP_ASSUME_TAC THENL
  [MESON_TAC[PAIR]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[attach_bitmaps_def; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p0:(((num)spt)option)list`; `p1:(num#num#(A)wl_prog)list`;
                        `p1':word_to_stack_config`; `p2:num list`;
                        `p3:(num#(A)stack_prog)list`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
           is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  ASM_REWRITE_TAC[(record_info "backend_config").ri_accfupds; K_THM]);;

(* the trivial labLang compiler oracle of the Pancake compiler (HOL4: sorac *)
(* in pan_to_target_compile_semantics) *)
let PTOPAUX_sorac_ok = prove
 (`!(ltconf:lab_to_target_config) (ac:(A)asm_config) n0 ffis.
     lab_to_target_config_pos ltconf = n0 /\
     lab_to_target_config_ffi_names ltconf = SOME ffis ==>
     compiler_oracle_ok (\n:num. (ltconf,[]:((A)sec)list)) (lab_to_target_config_labels ltconf)
       n0 ac ffis`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compiler_oracle_ok_def] THEN
  BETA_TAC THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[lab_to_targetProof_good_code_def; ALL; ALL_DISTINCT; MAP; set_of_list;
                  DISJOINT_EMPTY; no_share_mem_inst_def; asm_fetch_aux_def; option_DISTINCT;
                  lab_get_labels_def; IMAGE_CLAUSES; UNIONS_0; restrict_nonzero_def;
                  NOT_IN_EMPTY; EMPTY_GSPEC; EMPTY_SUBSET]);;

(* the labLang program of the Pancake compiler satisfies labels_ok and the *)
(* encoding precondition (HOL4: inline in pan_to_target_compile_semantics) *)
let PTOPAUX_lprog_syntax = prove
 (`!(c:backend_config) (mc:(A,B,C)machine_config) (pan_code:((A)decl)list) col wprog
    bitmaps c'' fs p.
     backend_config_ok (target_config (machine_config_target mc)) c /\ mc_conf_ok mc /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     pancake_good_code pan_code /\ ALL_DISTINCT (MAP FST (functions pan_code)) /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc))
       (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
          pan_code) = (col,wprog) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p)
     ==> labels_ok
           (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
              (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
              (asm_config_reg_count (target_config (machine_config_target mc)) -
               (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
              (asm_config_addr_offset (target_config (machine_config_target mc))) p) /\
         ALL (sec_ok_pre (target_config (machine_config_target mc)))
           (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
              (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
              (asm_config_reg_count (target_config (machine_config_target mc)) -
               (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
              (asm_config_addr_offset (target_config (machine_config_target mc))) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [MP_TAC (ISPECL [`mc:(A,B,C)machine_config`; `pan_code:((A)decl)list`;
                   `pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target
                      (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)`;
                   `c:backend_config`; `col:(((num)spt)option)list`;
                   `wprog:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`;
                   `c'':word_to_stack_config`; `fs:num list`; `p:(num#(A)stack_prog)list`;
                   `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
                   `asm_config_reg_count (target_config (machine_config_target
                      (mc:(A,B,C)machine_config))) -
                    (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)`;
                   `stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
                      (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
                      (asm_config_reg_count (target_config (machine_config_target
                         (mc:(A,B,C)machine_config))) -
                       (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
                      (asm_config_addr_offset (target_config (machine_config_target mc)))
                      (p:(num#(A)stack_prog)list)`]
                  pan_to_lab_labels_ok) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def] o
              check (fun th -> can (term_match [] `backend_config_ok (ac:(A)asm_config) c`)
                                   (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mc_conf_ok_def] o
              check (fun th -> can (term_match [] `mc_conf_ok (mc:(A,B,C)machine_config)`)
                                   (concl th))) THEN
  SUBGOAL_THEN `asm_offset_ok 0 (asm_config_byte_offset (target_config (machine_config_target
                  (mc:(A,B,C)machine_config)))) (word 0)` ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[BKP2AUX_ile_0]; ALL_TAC] THEN
  MP_TAC (MATCH_MP compile_to_word_conventions2
     (CONJ (ASSUME `word_to_word_compile (backend_config_word_to_word_conf c)
                      (target_config (machine_config_target (mc:(A,B,C)machine_config)))
                      (pan_to_word_compile_prog (asm_config_ISA (target_config
                         (machine_config_target mc))) (pan_code:((A)decl)list)) = (col,wprog)`)
           (SPEC `pan_to_word_compile_prog (asm_config_ISA (target_config
                    (machine_config_target (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)`
              (MATCH_MP PTOPAUX_ALL_no_share_Ag32
                (ASSUME `~(asm_config_ISA (target_config (machine_config_target
                            (mc:(A,B,C)machine_config))) = Ag32)`))))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\(n,m,p). every_inst (inst_ok_less (target_config (machine_config_target
                   (mc:(A,B,C)machine_config)))) p)
                (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
                   (pan_code:((A)decl)list))` ASSUME_TAC THENL
  [MATCH_MP_TAC pan_to_word_every_inst_ok_less THEN
   EXISTS_TAC `pan_code:((A)decl)list` THEN
   ASM_REWRITE_TAC[GSYM pancake_good_code_def];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`;
                  `wprog:(num#num#(A)wl_prog)list`] word_to_stack_stack_asm_convs) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> try fst (dest_const t) =
                      "flat_exp_conventions" with Failure _ -> false)) (concl th))) THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `a - (5 + b) = a - (b + 5)`] THEN MESON_TAC[];
    UNDISCH_TAC `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                   (mc:(A,B,C)machine_config)))) + 13 <=
                 asm_config_reg_count (target_config (machine_config_target mc))` THEN
    ARITH_TAC];
   ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `ALL (\(n,p). stack_asm_name (target_config (machine_config_target
                   (mc:(A,B,C)machine_config))) p) (p:(num#(A)stack_prog)list) /\
                ALL (\(n,p). stack_asm_remove (target_config (machine_config_target mc)) p) p`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> try fst (dest_const t) =
                      "stack_asm_remove" with Failure _ -> false)) (concl th))) THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC stack_to_lab_compile_all_enc_ok THEN
  ASM_REWRITE_TAC[reg_name_def] THEN
  UNDISCH_TAC `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                 (mc:(A,B,C)machine_config)))) + 13 <=
               asm_config_reg_count (target_config (machine_config_target mc))` THEN
  ARITH_TAC);;

(* the lab_to_target step of pan_to_target_compile_semantics *)
let PTOPAUX_lab_step = prove
 (`!(c:backend_config) (mc:(A,B,C)machine_config) (pan_code:((A)decl)list) col wprog bitmaps
    c'' fs p bytes ltconf (ffi:(FFI)ffi_state) ms cbspace t m dm sdm.
     backend_config_ok (target_config (machine_config_target mc)) c /\ mc_conf_ok mc /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     pancake_good_code pan_code /\ ALL_DISTINCT (MAP FST (functions pan_code)) /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc))
       (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
          pan_code) = (col,wprog) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) /\
     lab_to_target_compile (target_config (machine_config_target mc)) (backend_config_lab_conf c)
       (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
          (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
          (asm_config_reg_count (target_config (machine_config_target mc)) -
           (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
          (asm_config_addr_offset (target_config (machine_config_target mc))) p) =
       SOME (bytes,ltconf) /\
     good_init_state mc ms bytes cbspace t m dm sdm /\
     lab_to_target_config_ffi_names ltconf = SOME (machine_config_ffi_names mc) /\
     (!i. mmio_pcs_min_index (machine_config_ffi_names mc) = SOME i ==>
          MAP (\rec. val (target_get_pc (machine_config_target mc) ms) +
                     shmem_info_num_entry_pc rec) (lab_to_target_config_shmem_extra ltconf) =
          DROP i (MAP val (machine_config_ffi_entry_pcs mc)) /\
          machine_config_mmio_info mc =
          ZIP (list_of_seq (\index. index + i) (LENGTH (lab_to_target_config_shmem_extra ltconf)))
              (MAP (\rec. (shmem_info_num_nbytes rec,
                           Addr (shmem_info_num_addr_reg rec)
                                (word (shmem_info_num_addr_off rec)),
                           shmem_info_num_reg rec,
                           word_add (word (shmem_info_num_exit_pc rec))
                             (target_get_pc (machine_config_target mc) ms)))
                   (lab_to_target_config_shmem_extra ltconf)) /\
          (cbspace + LENGTH bytes) + ffi_offset * (i + 3) < dimword(:A))
     ==> implements' T (machine_sem mc ffi ms)
           {lab_semantics
              (lab_to_targetProof_make_init mc ffi t m (dm INTER byte_aligned)
                 (sdm INTER byte_aligned) ms
                 (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
                    (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
                    (asm_config_reg_count (target_config (machine_config_target mc)) -
                     (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
                    (asm_config_addr_offset (target_config (machine_config_target mc))) p)
                 (lab_to_target_compile (target_config (machine_config_target mc)))
                 (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes)))
                 cbspace (\n:num. (ltconf,[]:((A)sec)list)))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `lprog = stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
          (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
          (asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
           (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
          (asm_config_addr_offset (target_config (machine_config_target mc)))
          (p:(num#(A)stack_prog)list)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def] o
              check (fun th -> can (term_match [] `backend_config_ok (ac:(A)asm_config) c`)
                                   (concl th))) THEN
  SUBGOAL_THEN `?i. mmio_pcs_min_index (machine_config_ffi_names (mc:(A,B,C)machine_config)) =
                    SOME i` STRIP_ASSUME_TAC THENL
  [MP_TAC (ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`;
                   `backend_config_lab_conf c`; `filter_skip (lprog:((A)sec)list)`;
                   `bytes:byte list`; `ltconf:lab_to_target_config`]
                  compile_lab_IMP_mmio_pcs_min_index) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM lab_to_target_compile_def]; ALL_TAC] THEN
   ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
     can (find_term (fun t -> try fst (dest_const t) = "mmio_pcs_min_index"
                              with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`mc:(A,B,C)machine_config`; `lprog:((A)sec)list`;
                  `\n:num. (ltconf:lab_to_target_config,[]:((A)sec)list)`;
                  `ltconf:lab_to_target_config`; `bytes:byte list`;
                  `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
                  `backend_config_lab_conf c`; `ms:B`; `cbspace:num`; `t:(A)asm_state`;
                  `m:A word->(A)word_loc`; `dm:A word->bool`; `sdm:A word->bool`; `i:num`;
                  `ffi:(FFI)ffi_state`] lab_to_targetProof_semantics_compile) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [DISCH_TAC THEN MATCH_MP_TAC PTOPAUX_sorac_ok THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `lab_to_target_compile (target_config (machine_config_target
                  (mc:(A,B,C)machine_config))) (backend_config_lab_conf c) lprog =
                SOME (bytes,ltconf)` THEN
   REWRITE_TAC[lab_to_target_compile_def] THEN
   DISCH_THEN(MP_TAC o MATCH_MP compile_lab_LENGTH) THEN ASM_REWRITE_TAC[ADD_CLAUSES];
   MATCH_MP_TAC pan_to_lab_good_code_lemma THEN
   MP_TAC (ISPECL [`c:backend_config`; `mc:(A,B,C)machine_config`; `pan_code:((A)decl)list`;
                   `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
                   `bitmaps:(A word)list`; `c'':word_to_stack_config`; `fs:num list`;
                   `p:(num#(A)stack_prog)list`] PTOPAUX_lprog_syntax) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC
     [`c:backend_config`; `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
      `asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
       (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)`;
      `asm_config_addr_offset (target_config (machine_config_target (mc:(A,B,C)machine_config)))`;
      `p:(num#(A)stack_prog)list`;
      `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
      `wprog:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`; `c'':word_to_stack_config`;
      `fs:num list`; `backend_config_word_to_word_conf c`;
      `pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target
         (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)`;
      `col:(((num)spt)option)list`; `pan_code:((A)decl)list`] THEN
   ASM_REWRITE_TAC[];
   REWRITE_TAC[no_install_or_no_share_mem_def] THEN DISJ2_TAC THEN
   EXPAND_TAC "lprog" THEN MATCH_MP_TAC from_pan_to_lab_no_install THEN
   MAP_EVERY EXISTS_TAC
     [`pan_code:((A)decl)list`; `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
      `asm_config_ISA (target_config (machine_config_target (mc:(A,B,C)machine_config)))`;
      `pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target
         (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)`;
      `backend_config_word_to_word_conf c`; `col:(((num)spt)option)list`;
      `wprog:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`; `c'':word_to_stack_config`;
      `fs:num list`] THEN
   ASM_REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN
   UNDISCH_TAC `OPTION_ALL (ALL (\x. ?s. x = ExtCall s))
                  (lab_to_target_config_ffi_names (backend_config_lab_conf c))` THEN
   ASM_REWRITE_TAC[OPTION_ALL_def]]);;

(* the stack_to_lab step of pan_to_target_compile_semantics *)
let PTOPAUX_stack_step = prove
 (`!(c:backend_config) (mc:(A,B,C)machine_config) (pan_code:((A)decl)list) col wprog bitmaps
    c'' fs p bytes ltconf (ffi:(FFI)ffi_state) ms cbspace t m dm sdm data_sp s opt.
     backend_config_ok (target_config (machine_config_target mc)) c /\ mc_conf_ok mc /\
     mc_init_ok (target_config (machine_config_target mc)) c mc /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc))
       (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
          pan_code) = (col,wprog) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) /\
     memory_assumption (stack_to_lab_config_reg_names (backend_config_stack_conf c)) bitmaps
       data_sp
       (lab_to_targetProof_make_init mc ffi t m (dm INTER byte_aligned)
          (sdm INTER byte_aligned) ms
          (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
             (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
             (asm_config_reg_count (target_config (machine_config_target mc)) -
              (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
             (asm_config_addr_offset (target_config (machine_config_target mc))) p)
          (lab_to_target_compile (target_config (machine_config_target mc)))
          (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH (bytes:byte list))))
          cbspace (\n:num. (ltconf,[]:((A)sec)list))) /\
     full_make_init (backend_config_stack_conf c) (backend_config_data_conf c)
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
       (asm_config_reg_count (target_config (machine_config_target mc)) -
        (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
       (asm_config_addr_offset (target_config (machine_config_target mc))) bitmaps p
       (lab_to_targetProof_make_init mc ffi t m (dm INTER byte_aligned)
          (sdm INTER byte_aligned) ms
          (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
             (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
             (asm_config_reg_count (target_config (machine_config_target mc)) -
              (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
             (asm_config_addr_offset (target_config (machine_config_target mc))) p)
          (lab_to_target_compile (target_config (machine_config_target mc)))
          (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes)))
          cbspace (\n:num. (ltconf,[]:((A)sec)list)))
       (set_of_list (machine_config_callee_saved_regs mc)) data_sp
       (\n:num. (ltconf,[]:(num#(A)stack_prog)list,[]:(A word)list)) = (s,opt)
     ==> ~(opt = NONE) /\
         (~(stack_semantics InitGlobals_location s = Fail)
          ==> lab_semantics
                (lab_to_targetProof_make_init mc ffi t m (dm INTER byte_aligned)
                   (sdm INTER byte_aligned) ms
                   (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
                      (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
                      (asm_config_reg_count (target_config (machine_config_target mc)) -
                       (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
                      (asm_config_addr_offset (target_config (machine_config_target mc))) p)
                   (lab_to_target_compile (target_config (machine_config_target mc)))
                   (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes)))
                   cbspace (\n:num. (ltconf,[]:((A)sec)list))) =
              stack_semantics InitGlobals_location s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq (concl th) in
    if not (is_comb l && fst (dest_const (fst (strip_comb l))) = "full_make_init")
    then failwith "" else
    let args = snd (strip_comb l) in
    let s,opt = dest_pair r in
    MP_TAC (ISPECL (args @ [s; opt]) full_make_init_semantics)) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lab_to_targetProof_make_init_def; (record_info "lab_state").ri_accessors;
              IN_INTER] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mc_conf_ok_def] o
              check (fun th -> can (term_match [] `mc_conf_ok (mc:(A,B,C)machine_config)`)
                                   (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mc_init_ok_def] o
              check (fun th -> can (term_match [] `mc_init_ok (ac:(A)asm_config) (c:backend_config) (mc:(A,B,C)machine_config)`)
                                   (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def] o
              check (fun th -> can (term_match [] `backend_config_ok (ac:(A)asm_config) c`)
                                   (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[compile_no_stubs_def; stack_names_compile_def; MAP];
   ASM_REWRITE_TAC[IN_SET_OF_LIST];
   REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[target_io_regs_callee_saved];
   REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[target_cc_regs_callee_saved];
   FIRST_ASSUM(fun th -> MESON_TAC[MATCH_MP byte_aligned_MOD th]);
   FIRST_ASSUM(fun th -> MESON_TAC[MATCH_MP byte_aligned_MOD th]);
   MATCH_MP_TAC word_to_stack_good_code_lemma THEN
   MAP_EVERY EXISTS_TAC [`c:backend_config`; `pan_code:((A)decl)list`;
                         `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
                         `bitmaps:(A word)list`; `c'':word_to_stack_config`; `fs:num list`] THEN
   ASM_REWRITE_TAC[];
   REWRITE_TAC[stack_to_labProof_good_code_def; MAP; ALL; ALL_DISTINCT];
   MP_TAC(ASSUME `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                    (mc:(A,B,C)machine_config)))) + 13 <=
                  asm_config_reg_count (target_config (machine_config_target mc))`) THEN
   ARITH_TAC;
   SUBGOAL_THEN `!r. (r + (asm_config_reg_count (target_config (machine_config_target
                       (mc:(A,B,C)machine_config))) -
                      (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))) - 2 =
                     (r + asm_config_reg_count (target_config (machine_config_target mc))) -
                     (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 5)`
    (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ASSUME `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                    (mc:(A,B,C)machine_config)))) + 13 <=
                  asm_config_reg_count (target_config (machine_config_target mc))`) THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[IN_SET_OF_LIST]]]);;

(* the word_to_stack step of pan_to_target_compile_semantics *)
let PTOPAUX_word_step = prove
 (`!(c:backend_config) (mc:(A,B,C)machine_config) (pan_code:((A)decl)list) col wprog bitmaps
    c'' fs p ltconf (lab_st:(A,lab_to_target_config,FFI)lab_state) save_regs data_sp s opt.
     backend_config_ok (target_config (machine_config_target mc)) c /\ mc_conf_ok mc /\
     ~(asm_config_ISA (target_config (machine_config_target mc)) = Ag32) /\
     word_to_word_compile (backend_config_word_to_word_conf c)
       (target_config (machine_config_target mc))
       (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target mc)))
          pan_code) = (col,wprog) /\
     word_to_stack_compile (target_config (machine_config_target mc)) F wprog =
       (bitmaps,c'',fs,p) /\
     full_make_init (backend_config_stack_conf c) (backend_config_data_conf c)
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
       (asm_config_reg_count (target_config (machine_config_target mc)) -
        (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
       (asm_config_addr_offset (target_config (machine_config_target mc))) bitmaps p lab_st
       save_regs data_sp
       (\n:num. (ltconf,[]:(num#(A)stack_prog)list,[]:(A word)list)) = (s,opt) /\
     ~(opt = NONE) /\
     ~(wl_semantics
         (word_to_stackProof_make_init (target_config (machine_config_target mc))
            (asm_config_reg_count (target_config (machine_config_target mc)) -
             (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 5))
            s (fromAList wprog)
            (\n:num. ((LENGTH bitmaps,ltconf),[]:(num#num#(A)wl_prog)list)))
         InitGlobals_location = Fail)
     ==> stack_semantics InitGlobals_location s IN
         extend_with_resource_limit'
           (word_lang_safe_for_space
              (word_to_stackProof_make_init (target_config (machine_config_target mc))
                 (asm_config_reg_count (target_config (machine_config_target mc)) -
                  (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 5))
                 s (fromAList wprog)
                 (\n:num. ((LENGTH bitmaps,ltconf),[]:(num#num#(A)wl_prog)list)))
              InitGlobals_location)
           {wl_semantics
              (word_to_stackProof_make_init (target_config (machine_config_target mc))
                 (asm_config_reg_count (target_config (machine_config_target mc)) -
                  (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 5))
                 s (fromAList wprog)
                 (\n:num. ((LENGTH bitmaps,ltconf),[]:(num#num#(A)wl_prog)list)))
              InitGlobals_location}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `xxx:(A,lab_to_target_config,FFI)stack_state` SUBST_ALL_TAC o
    REWRITE_RULE[GSYM IS_SOME_EQ_NOT_NONE; IS_SOME_EXISTS] o
    check (fun th -> concl th = `~(opt:((A,lab_to_target_config,FFI)stack_state)option = NONE)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def] o
              check (fun th -> can (term_match [] `backend_config_ok (ac:(A)asm_config) c`)
                                   (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mc_conf_ok_def] o
              check (fun th -> can (term_match [] `mc_conf_ok (mc:(A,B,C)machine_config)`)
                                   (concl th))) THEN
  MP_TAC(ISPECL [`s:(A,lab_to_target_config,FFI)stack_state`;
   `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
   `wprog:(num#num#(A)wl_prog)list`;
   `asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
    (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 5)`;
   `\n:num. ((LENGTH (bitmaps:(A word)list),ltconf:lab_to_target_config),
             []:(num#num#(A)wl_prog)list)`;
   `InitGlobals_location`] word_to_stackProof_compile_semantics) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `stack_state_code (s:(A,lab_to_target_config,FFI)stack_state) = fromAList p /\
                stack_state_bitmaps s = bitmaps` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[full_make_init_def] o check (fun th ->
     is_eq (concl th) && is_comb (lhs (concl th)) &&
     (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "full_make_init"
      with Failure _ -> false))) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
   REWRITE_TAC[stack_allocProof_make_init_def; (record_info "stack_state").ri_accfupds; K_THM;
               make_init_any_bitmaps] THEN
   ASM_REWRITE_TAC[IS_SOME_DEF];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[IS_PREFIX_REFL; ARITH_RULE `a - (b + 5) = a - (5 + b)`] THEN
  MP_TAC (MATCH_MP compile_to_word_conventions2
     (CONJ (ASSUME `word_to_word_compile (backend_config_word_to_word_conf c)
                      (target_config (machine_config_target (mc:(A,B,C)machine_config)))
                      (pan_to_word_compile_prog (asm_config_ISA (target_config
                         (machine_config_target mc))) (pan_code:((A)decl)list)) = (col,wprog)`)
           (SPEC `pan_to_word_compile_prog (asm_config_ISA (target_config
                    (machine_config_target (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)`
              (MATCH_MP PTOPAUX_ALL_no_share_Ag32
                (ASSUME `~(asm_config_ISA (target_config (machine_config_target
                            (mc:(A,B,C)machine_config))) = Ag32)`))))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (wprog:(num#num#(A)wl_prog)list) raise_stub_location = NONE /\
                ALOOKUP wprog wl_store_consts_stub_location = NONE`
    (fun th -> REWRITE_TAC[th]) THENL
  [ASM_REWRITE_TAC[ALOOKUP_NONE; raise_stub_location_def; wl_store_consts_stub_location_def;
                   word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   SUBGOAL_THEN `ALL (\prog. 60 <= FST prog)
                   (pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target
                      (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC pan_to_word_compile_prog_lab_min THEN MESON_TAC[]; ALL_TAC] THEN
   CONJ_TAC THEN MATCH_MP_TAC PTOPAUX_lab_min_not_MEM THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV;
   ALL_TAC] THEN
  CONJ_TAC THENL
  [ALL_TAC;
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> try fst (dest_const t) =
                      "flat_exp_conventions" with Failure _ -> false)) (concl th))) THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`asm_config_reg_count (target_config (machine_config_target
                    (mc:(A,B,C)machine_config))) -
                  (5 + LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))))`;
   `bitmaps:(A word)list`; `TL (bitmaps:(A word)list)`;
   `\n:num. ((LENGTH (bitmaps:(A word)list),ltconf:lab_to_target_config),
             []:(num#num#(A)wl_prog)list)`;
   `\n:num. (ltconf:lab_to_target_config,[]:(num#(A)stack_prog)list,[]:(A word)list)`;
   `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
   `backend_config_stack_conf c`; `backend_config_data_conf c`;
   `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
   `asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
    (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)`;
   `asm_config_addr_offset (target_config (machine_config_target (mc:(A,B,C)machine_config)))`;
   `p:(num#(A)stack_prog)list`;
   `lab_st:(A,lab_to_target_config,FFI)lab_state`; `save_regs:num->bool`; `data_sp:num`;
   `s:(A,lab_to_target_config,FFI)stack_state`; `xxx:(A,lab_to_target_config,FFI)stack_state`]
   IMP_init_state_ok) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`;
                 `wprog:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`;
                 `c'':word_to_stack_config`; `(fs:num list,p:(num#(A)stack_prog)list)`]
         compile_word_to_stack_bitmaps) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                  (mc:(A,B,C)machine_config)))) + 13 <=
                asm_config_reg_count (target_config (machine_config_target mc))` THEN
   ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> try fst (dest_const t) =
                      "list_CASE" with Failure _ -> false)) (concl th))) THEN
   SPEC_TAC(`bitmaps:(A word)list`,`l:(A word)list`) THEN
   LIST_INDUCT_TAC THEN CASE_REWRITE_TAC[TL; CONS_11] THEN MESON_TAC[];
   ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ALL; FUN_EQ_THM; compile_word_to_stack_def; append_def; append_aux_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* consequences of stack_removeProof's init_code_thm under discharge_these *)
(* and propagate_these (as in stack_removeProof_make_init_semantics)      *)
let PTOPAUX_init_code = prove
 (`!jump off gen_gc' max_heap k start
    (coracle:num->C#(num#(A)stack_prog)list#(A word)list) (code:(num#(A)stack_prog)list)
    (s2:(A,C,FFI)stack_state) (bitmaps:(A word)list) data_sp t.
     discharge_these jump off gen_gc' max_heap k start coracle code s2 /\
     propagate_these s2 bitmaps data_sp /\
     stack_evaluate (stack_remove_init_code gen_gc' max_heap k,s2) = (NONE,t)
     ==> (!w2. FLOOKUP (stack_state_regs s2) 2 = SOME (wl_Word w2)
               ==> FLOOKUP (stack_state_regs t) (k + 2) = SOME (wl_Word w2)) /\
         FLOOKUP (stack_state_store
                    (init_reduce gen_gc' jump off k (fromAList code) bitmaps data_sp coracle t))
           CurrHeap = FLOOKUP (stack_state_regs t) (k + 2) /\
         stack_state_sh_mdomain s2 = stack_state_sh_mdomain t /\
         fun2set (stack_state_memory s2,
                  stack_state_mdomain
                    (init_reduce gen_gc' jump off k (fromAList code) bitmaps data_sp coracle t)) =
         fun2set (stack_state_memory t,
                  stack_state_mdomain
                    (init_reduce gen_gc' jump off k (fromAList code) bitmaps data_sp coracle t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[discharge_these_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "discharge_these"
                     with Failure _ -> false)) THEN
  MP_TAC (ISPECL [`k:num`; `bitmaps:(A word)list`; `data_sp:num`; `s2:(A,C,FFI)stack_state`;
                  `jump:bool`; `off:A word#A word`; `fromAList (code:(num#(A)stack_prog)list)`;
                  `coracle:num->C#(num#(A)stack_prog)list#(A word)list`; `gen_gc':bool`;
                  `max_heap:num`] init_code_thm) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[init_code_pre_def] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[propagate_these_def] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "propagate_these"
                       with Failure _ -> false)) THEN
    REWRITE_TAC[WORD_RULE `word_add (word_mul (word_neg (word 1)) (x:A word)) y =
                           word_sub y x`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`ptr2:A word`; `ptr3:A word`; `ptr4:A word`; `bitmap_ptr:A word`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMP_code_rel THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ASM_REWRITE_TAC[lookup_fromAList; stack_remove_compile_def; stack_remove_init_stubs_def;
                    APPEND; ALOOKUP_THM; stack_err_lab_def] THEN
    CONV_TAC NUM_REDUCE_CONV];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV let_CONV) o
     REWRITE_RULE[stack_removeProof_state_rel_def] o
     check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                          "stack_removeProof_state_rel" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `FLOOKUP (stack_state_regs (s2:(A,C,FFI)stack_state)) 2 =
                                      SOME (wl_Word w2)`; option_INJ; injectivity "word_loc"]) THEN
  ASM_MESON_TAC[]);;

let PTOPAUX_init_prop_alloc = prove
 (`!g mh dsp lim dc code oracle (s:(A,C,FFI)stack_state).
     init_prop g mh dsp lim s ==>
     init_prop g mh dsp lim (stack_allocProof_make_init dc code oracle s)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`lim:num#num`,`lim:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[init_prop_def; stack_heap_limit_ok_def; stack_allocProof_make_init_def;
              (record_info "stack_state").ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`; `bitmap_base:A word`; `len:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* a value DIV the word size in bytes is below dimword DIV it *)
let PTOPAUX_val_div_lt = prove
 (`!(x:A word) n. good_dimindex(:A) ==>
     val x DIV (dimindex(:A) DIV 8) - n < dimword(:A) DIV (dimindex(:A) DIV 8)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ARITH_RULE `a < b ==> a - n < b:num`) THEN
  SUBGOAL_THEN `~(dimindex(:A) DIV 8 = 0) /\
                dimindex(:A) DIV 8 * dimword(:A) DIV (dimindex(:A) DIV 8) = dimword(:A)`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
   ALL_TAC] THEN
  ASM_SIMP_TAC[RDIV_LT_EQ] THEN REWRITE_TAC[dimword_def; VAL_BOUND]);;

(* facts about the stackLang state of a successful full_make_init *)
let PTOPAUX_fmi_facts = prove
 (`!scc dc mh sp (off:A word#A word) (bitmaps:(A word)list) code (s4:(A,C,FFI)lab_state)
    save_regs data_sp (coracle:num->C#(num#(A)stack_prog)list#(A word)list) s xxx.
     full_make_init scc dc mh sp off bitmaps code s4 save_regs data_sp coracle = (s,SOME xxx) /\
     good_dimindex (:A) /\
     memory_assumption (stack_to_lab_config_reg_names scc) bitmaps data_sp s4 /\
     max_stack_alloc <= mh /\
     stack_to_labProof_good_code sp code /\
     (!n. stack_to_labProof_good_code sp (FST (SND (coracle n)))) /\
     10 <= sp /\
     ALL (\r. tlookup (stack_to_lab_config_reg_names scc) ((r + sp) - 2) IN save_regs) [2; 3; 4] /\
     BIJ (tlookup (stack_to_lab_config_reg_names scc)) UNIV UNIV
     ==> FLOOKUP (stack_state_store s) CurrHeap =
           SOME (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 2)) /\
         stack_state_sh_mdomain s = lab_state_shared_mem_domain s4 /\
         (!a. a IN stack_state_mdomain s ==> stack_state_memory s a = lab_state_mem s4 a) /\
         (?hsp. stack_state_mdomain s =
                  addresses (theWord (lab_state_regs s4
                                        (tlookup (stack_to_lab_config_reg_names scc) 2))) hsp /\
                hsp < dimword (:A) DIV (dimindex (:A) DIV 8)) /\
         stack_state_gc_fun s = word_gc_fun dc /\
         (stack_state_be s <=> lab_state_be s4) /\
         init_prop (is_gen_gc (data_to_word_config_gc_kind dc)) mh data_sp
           (get_stack_heap_limit mh
              (theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 2)),
               theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 3)),
               theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 4)))) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`scc:stack_to_lab_config`; `dc:data_to_word_config`; `mh:num`; `sp:num`;
                  `off:A word#A word`; `bitmaps:(A word)list`; `code:(num#(A)stack_prog)list`;
                  `s4:(A,C,FFI)lab_state`; `save_regs:num->bool`; `data_sp:num`;
                  `coracle:num->C#(num#(A)stack_prog)list#(A word)list`;
                  `s:(A,C,FFI)stack_state`; `xxx:(A,C,FFI)stack_state`] BKP2AUX_fmi_SOME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
     (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "full_make_init"
      with Failure _ -> false))) THEN
  REWRITE_TAC[full_make_init_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    let mio = lhs (concl th) in
    let h,margs = strip_comb mio in
    if fst (dest_const h) <> "make_init_opt" then failwith "" else
    let [ggc; mh0; bm0; dsp0; o1; jump; off0; sp0; c1spt; s2] = margs in
    let _,[f;c2spt;o2;s3] = strip_comb s2 in
    let _,[c3spt;o3;regs;sr;t4] = strip_comb s3 in
    let code2 = rand c2spt in
    let code1 = last (snd (strip_comb code2)) in
    MP_TAC (ISPECL [f; jump; off0; sp0; ggc; mh0; `dc:data_to_word_config`;
                    `code:(num#(A)stack_prog)list`; code1; code2;
                    `coracle:num->C#(num#(A)stack_prog)list#(A word)list`;
                    o1; o2; o3; regs; sr; t4] S2LP2AUX_fmis_discharge) THEN
    MP_TAC (ISPECL [f; c2spt; o2; o3; c3spt; sr; t4; bm0; dsp0] S2LP2AUX_fmis_propagate) THEN
    MP_TAC (MATCH_MP S2LP2AUX_make_init_opt_SOME th) THEN
    MP_TAC (ISPECL [f; `lab_state_regs (s4:(A,C,FFI)lab_state)`; `2`] BKP2AUX_names_regs)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun d -> FIRST_ASSUM(fun p -> FIRST_ASSUM(fun ev ->
    MP_TAC (MATCH_MP PTOPAUX_init_code (CONJ d (CONJ p ev)))))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
     (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "stack_allocProof_make_init"
      with Failure _ -> false))) THEN
  REWRITE_TAC[make_init_any_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[memory_assumption_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "memory_assumption"
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `FLOOKUP (stack_state_regs (t0:(A,C,FFI)stack_state)) (sp + 2) =
                SOME (lab_state_regs (s4:(A,C,FFI)lab_state)
                        (tlookup (stack_to_lab_config_reg_names scc) 2))` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `ptr2:A word` o check (fun th -> is_forall (concl th) &&
     fst (dest_var (fst (dest_forall (concl th)))) = "w2")) THEN
   REWRITE_TAC[stack_namesProof_make_init_def; stack_to_labProof_make_init_def;
               (record_info "stack_state").ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `FAPPLY (stack_state_regs (t0:(A,C,FFI)stack_state)) (sp + 2) = wl_Word ptr2`
    ASSUME_TAC THENL
  [UNDISCH_TAC `FLOOKUP (stack_state_regs (t0:(A,C,FFI)stack_state)) (sp + 2) =
                SOME (lab_state_regs (s4:(A,C,FFI)lab_state)
                        (tlookup (stack_to_lab_config_reg_names scc) 2))` THEN
   ASM_REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
   REWRITE_TAC[option_DISTINCT; option_INJ];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[stack_allocProof_make_init_def; init_reduce_def;
               (record_info "stack_state").ri_accfupds; K_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[(record_info "stack_state").ri_accfupds; K_THM] THEN
   FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq (concl th) &&
     (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "stack_state_sh_mdomain"
      with Failure _ -> false))) THEN
   REWRITE_TAC[stack_namesProof_make_init_def; stack_to_labProof_make_init_def;
               (record_info "stack_state").ri_accfupds; K_THM];
   REWRITE_TAC[stack_allocProof_make_init_def; (record_info "stack_state").ri_accfupds;
               K_THM] THEN
   X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "fun2set"
      with Failure _ -> false))) THEN
   REWRITE_TAC[fun2set_eq] THEN DISCH_THEN(MP_TAC o SPEC `a:A word`) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[init_reduce_def; stack_namesProof_make_init_def; stack_to_labProof_make_init_def]
     THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[(record_info "stack_state").ri_accfupds; K_THM] THEN MESON_TAC[];
   REWRITE_TAC[stack_allocProof_make_init_def; init_reduce_def;
               (record_info "stack_state").ri_accfupds; K_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[(record_info "stack_state").ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[theWord_def] THEN
   W(fun (asl,w) -> let v,bod = dest_exists w in
       EXISTS_TAC (rand (lhand (lhand bod)))) THEN
   ASM_SIMP_TAC[PTOPAUX_val_div_lt];
   MATCH_MP_TAC PTOPAUX_init_prop_alloc THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th ->
     (try fst(dest_const(fst(strip_comb(concl th)))) = "init_prop" with Failure _ -> false) &&
     can (find_term (fun t -> try fst(dest_const t) = "lab_state_regs" with Failure _ -> false))
         (concl th))) THEN
   ASM_REWRITE_TAC[]]);;

(* exact divisions: the heap of stack_remove has twice the half length *)
let PTOPAUX_div_arith = prove
 (`!d v2 v3. ~(d = 0) /\ v2 MOD d = 0 /\ (v3 - v2) MOD (2 * d) = 0 /\ v2 <= v3 ==>
             2 * ((v3 DIV d - v2 DIV d) DIV 2) = (v3 - v2) DIV d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOD_EQ_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `a:num` ASSUME_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `b:num` ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `v3 = d * (a + 2 * b)` SUBST1_TAC THENL
  [UNDISCH_TAC `v3 - v2 = b * 2 * d` THEN UNDISCH_TAC `v2 <= v3` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
   MP_TAC (SPECL [`a:num`; `d:num`] MULT_SYM) THEN
   MP_TAC (SPECL [`b * 2`; `d:num`] MULT_SYM) THEN
   REWRITE_TAC[GSYM MULT_ASSOC] THEN ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d * (a + 2 * b) - a * d = d * (2 * b)` SUBST1_TAC THENL
  [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
   MP_TAC (SPECL [`a:num`; `d:num`] MULT_SYM) THEN ARITH_TAC;
   ALL_TAC] THEN
  SUBST1_TAC (SPECL [`a:num`; `d:num`] MULT_SYM) THEN
  ASM_SIMP_TAC[DIV_MULT; ARITH_RULE `(a + 2 * b) - a = 2 * b`; ARITH_EQ]);;

(* the heap length of the initial stack state, from the registers *)
let PTOPAUX_heap_lim_arith = prove
 (`!mh (w2:A word) w3 w4.
     good_dimindex (:A) /\ byte_aligned w2 /\ word_ult w2 w3 /\
     alignment_aligned (backend_common_word_shift (:A) + 1)
       (word_add w3 (word_mul (word_neg (word 1)) w2)) /\
     word_ule (word_add w2 (word_mul bytes_in_word (word max_stack_alloc))) w3 /\
     word_ule w3 (word_sub w4 (word_mul bytes_in_word (word max_stack_alloc))) /\
     val (word_add w3 (word_mul (word_neg (word 1)) w2)) <= val (bytes_in_word:A word) * mh /\
     val (bytes_in_word:A word) * mh < dimword (:A)
     ==> 2 * SND (get_stack_heap_limit mh (w2,w3,w4)) =
         val (word_add w3 (word_mul (word_neg (word 1)) w2)) DIV (dimindex (:A) DIV 8)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add (w3:A word) (word_mul (word_neg (word 1)) w2) =
                         word_sub w3 w2`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[get_stack_heap_limit_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[get_stack_heap_limit'_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_VAL] THEN
  SUBGOAL_THEN `~(dimindex(:A) DIV 8 = 0) /\ val (bytes_in_word:A word) = dimindex(:A) DIV 8 /\
                2 EXP (backend_common_word_shift (:A) + 1) = 2 * (dimindex(:A) DIV 8)`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `good_dimindex(:A)` THEN
   SIMP_TAC[BKP2AUX_val_bytes_in_word] THEN REWRITE_TAC[good_dimindex_def] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[backend_common_word_shift_def] THEN CONV_TAC NUM_REDUCE_CONV;
   ALL_TAC] THEN
  SUBGOAL_THEN `mh * val (bytes_in_word:A word) < dimword (:A)` (fun th -> REWRITE_TAC[th]) THENL
  [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_mul (word_neg (word 1)) (w2:A word)) w3 =
                         word_sub w3 w2`] THEN
  SUBGOAL_THEN `~(word_ult (word_mul bytes_in_word (word mh)) (word_sub (w3:A word) w2))`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[WORD_ULT; NOT_LT] THEN
   SUBGOAL_THEN `val (word_mul bytes_in_word (word mh):A word) = val (bytes_in_word:A word) * mh`
     SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; GSYM dimword_def] THEN
    SUBGOAL_THEN `mh < dimword(:A)` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
    [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val (bytes_in_word:A word) * mh` THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC (ARITH_RULE `1 * m <= b * m ==> m <= b * m:num`) THEN
     REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_mul (word_neg (word 1)) (w2:A word)) w3 =
                         word_sub w3 w2`] THEN
  SUBGOAL_THEN `word_shl (word_ushr (word_sub (w3:A word) w2) (backend_common_word_shift (:A) + 1))
                  (backend_common_word_shift (:A) + 1) = word_sub w3 w2` SUBST1_TAC THENL
  [MATCH_MP_TAC lsr_lsl THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (w2:A word) (word_sub w3 w2) = w3`;
              get_stack_heap_limit''_def] THEN
  SUBGOAL_THEN `val (word_sub (w3:A word) w2) = val w3 - val w2 /\ val w2 <= val w3`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `word_ult (w2:A word) w3` THEN REWRITE_TAC[WORD_ULT] THEN DISCH_TAC THEN
   CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
   MATCH_MP_TAC word_sub_w2n THEN REWRITE_TAC[WORD_ULE] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PTOPAUX_div_arith THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [MP_TAC (MATCH_MP byte_aligned_MOD (ASSUME `good_dimindex(:A)`)) THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN];
   UNDISCH_TAC `alignment_aligned (backend_common_word_shift (:A) + 1)
                  (word_sub (w3:A word) w2)` THEN
   ASM_REWRITE_TAC[aligned_w2n]]);;

(* the pan_to_word step of pan_to_target_compile_semantics: state_rel_imp_ *)
(* semantics for the wordLang state that word_to_stack's make_init builds   *)
let PTOPAUX_pan_step = prove
 (`!(s:(A,FFI)pan_state) (sst:(A,C,FFI)stack_state) (ac:(A)asm_config) k wcode
    (coracle:num->(num#C)#(num#num#(A)wl_prog)list) (pan_code:((A)decl)list) isa start
    globals_size hl.
     (!a. a IN pan_state_memaddrs s ==>
          stack_state_memory sst a = wlab_wloc (pan_state_memory s a)) /\
     no_labels (stack_state_memory sst) (stack_state_mdomain sst) /\
     start = implode "main" /\
     globals_size = (let dec_shs = dec_shapes pan_code in
                     let struct_ctxt = decs_stcnames [] pan_code in
                     SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) /\
     distinct_params (functions pan_code) /\
     stack_state_mdomain sst =
       pan_state_memaddrs s UNION addresses (pan_state_top_addr s) globals_size /\
     stack_state_sh_mdomain sst = pan_state_sh_memaddrs s /\
     (stack_state_be sst <=> pan_state_be s) /\
     stack_state_ffi sst = pan_state_ffi s /\
     FLOOKUP (stack_state_store sst) CurrHeap = SOME (wl_Word (pan_state_base_addr s)) /\
     FLOOKUP (stack_state_store sst) HeapLength = SOME (wl_Word hl) /\
     pan_state_top_addr s =
       word_sub (word_add (pan_state_base_addr s) (word_mul (word 2) hl))
                (word_mul bytes_in_word (word globals_size)) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     byte_aligned (pan_state_top_addr s) /\
     globals_allocatable s pan_code /\
     pan_state_code s = FEMPTY /\ pan_state_globals s = FEMPTY /\
     pan_state_locals s = FEMPTY /\ size_of_eids pan_code < dimword (:A) /\
     pan_state_eshapes s = FEMPTY /\ good_dimindex (:A) /\
     ~(semantics_decls s start pan_code = Fail)
     ==> wl_semantics
           (wl_state_code_fupd (K (fromAList (pan_to_word_compile_prog isa pan_code)))
              (word_to_stackProof_make_init ac k sst wcode coracle))
           first_name =
         semantics_decls s start pan_code`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC pan_to_wordProof_state_rel_imp_semantics THEN
  MAP_EVERY EXISTS_TAC [`globals_size:num`; `hl:A word`; `isa:architecture`] THEN
  REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM; BKP2AUX_w2s_make_init_fields;
              ALOOKUP_EQ_FLOOKUP; DOMSUB_FLOOKUP_THM; distinctness "store_name"] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  REWRITE_TAC[word_to_stackProof_make_init_def; (record_info "wl_state").ri_accessors] THEN
  ASM_REWRITE_TAC[]);;

(* the word_to_word step of pan_to_target_compile_semantics *)
let PTOPAUX_w2w_step = prove
 (`!wconf (ac:(A)asm_config) isa (pan_code:((A)decl)list) col wprog (wst:(A,C,FFI)wl_state)
    start.
     word_to_word_compile wconf ac (pan_to_word_compile_prog isa pan_code) = (col,wprog) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     gc_fun_const_ok (wl_state_gc_fun wst) /\ wl_state_stack wst = [] /\
     wl_state_code wst = fromAList wprog /\
     lookup 0 (wl_state_locals wst) = SOME (wl_Loc 1 0) /\
     ~(wl_semantics
         (wl_state_code_fupd (K (fromAList (pan_to_word_compile_prog isa pan_code))) wst)
         start = Fail)
     ==> wl_semantics
           (wl_state_code_fupd (K (fromAList (pan_to_word_compile_prog isa pan_code))) wst)
           start =
         wl_semantics wst start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC word_to_word_compile_semantics THEN
  MAP_EVERY EXISTS_TAC [`wconf:word_to_word_config`; `ac:(A)asm_config`;
                        `pan_to_word_compile_prog isa (pan_code:((A)decl)list)`;
                        `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`] THEN
  ASM_REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC pan_to_word_compile_prog_no_install_code THEN MESON_TAC[];
   MATCH_MP_TAC pan_to_word_compile_prog_no_alloc_code THEN MESON_TAC[];
   MATCH_MP_TAC pan_to_word_compile_prog_no_install_code THEN MESON_TAC[];
   MATCH_MP_TAC pan_to_word_compile_prog_no_alloc_code THEN MESON_TAC[];
   MATCH_MP_TAC pan_to_word_compile_prog_no_mt_code THEN MESON_TAC[];
   MATCH_MP_TAC pan_to_wordProof_first_compile_prog_all_distinct THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[(record_info "wl_state").ri_component_equality;
               (record_info "wl_state").ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[]]);;

(* the stack frame sizes of word_to_stack_compile *)
let PTOPAUX_sfs_eq = prove
 (`!(ac:(A)asm_config) wprog bitmaps c'' fs p.
     word_to_stack_compile ac F wprog = (bitmaps,c'',fs,p) /\ ALL_DISTINCT (MAP FST wprog)
     ==> compute_stack_frame_sizes ac wprog = word_to_stack_config_stack_frame_size c''`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BACKDEFAUX_PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  REWRITE_TAC[compute_stack_frame_sizes_thm; mapi_Alist] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  W(fun (asl,w) ->
      MP_TAC (PART_MATCH (lhand o rand) BKP2AUX_fromAList_MAP_toAList (lhs w))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `!a b. a - (5 + b) = (a - b) - 5`]) THEN
  MATCH_MP_TAC compile_word_to_stack_sfs_aux THEN ASM_MESON_TAC[]);;

(* the resource bound of pan_to_target_compile_semantics *)
let PTOPAUX_limit_step = prove
 (`!(wst:(A,C,FFI)wl_state) start m.
     wl_state_stack_max wst = SOME 1 /\ wl_state_stack wst = [] /\
     no_install_code (wl_state_code wst) /\ no_alloc_code (wl_state_code wst) /\
     (!kk res t. wl_evaluate (wl_Call NONE (SOME start) [0] NONE,
                              wl_state_clock_fupd (K kk) wst) = (res,t)
                 ==> ~(res = SOME wl_Error)) /\
     max_depth (wl_state_stack_size wst) (full_call_graph start (wl_state_code wst)) =
       SOME m /\
     m < wl_state_stack_limit wst
     ==> word_lang_safe_for_space wst start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[word_lang_safe_for_space_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MAP_EVERY X_GEN_TAC [`kk:num`; `res:((A)wl_result)option`;
                       `t:(A,C,FFI)wl_state`] THEN DISCH_TAC THEN
  MP_TAC (ISPECL [`start:num`; `[0]`; `wl_state_clock_fupd (K kk) (wst:(A,C,FFI)wl_state)`;
                  `res:((A)wl_result)option`; `t:(A,C,FFI)wl_state`;
                  `wl_state_code (wst:(A,C,FFI)wl_state)`] max_depth_Call_NONE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM; subspt_refl] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`wl_Call NONE (SOME start) [0] NONE:(A)wl_prog`;
                  `wl_state_clock_fupd (K kk) (wst:(A,C,FFI)wl_state)`;
                  `res:((A)wl_result)option`; `t:(A,C,FFI)wl_state`]
                 evaluate_stack_size_limit_const_panLang) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM] THEN
   SIMP[no_alloc_def; wordConvs_no_install_def];
   ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM; wl_stack_size_def; ITLIST;
                  OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF; option_le_SOME] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  UNDISCH_TAC `m < wl_state_stack_limit (wst:(A,C,FFI)wl_state)` THEN
  UNDISCH_TAC `m' <= MAX 1 (1 + m)` THEN ARITH_TAC);;

(* a wordLang program whose semantics is not Fail does not end in Error *)
let PTOPAUX_wl_sem_no_error = prove
 (`!(s:(A,C,FFI)wl_state) start.
     ~(wl_semantics s start = Fail) ==>
     !k res t. wl_evaluate (wl_Call NONE (SOME start) [0] NONE,wl_state_clock_fupd (K k) s) =
                 (res,t)
               ==> ~(res = SOME wl_Error)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~(wl_semantics (s:(A,C,FFI)wl_state) start = Fail)` THEN
  REWRITE_TAC[wl_semantics_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* splitting a range of word addresses *)
let PTOPAUX_addresses_split = prove
 (`!(a:A word) n k.
     k <= n ==>
     addresses a n =
     addresses a k UNION addresses (word_add a (word_mul bytes_in_word (word k))) (n - k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_addresses] THEN
  X_GEN_TAC `x:A word` THEN EQ_TAC THENL
  [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
   ASM_CASES_TAC `i < k` THENL
   [DISJ1_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `i - k` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i = k + (i - k)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
   STRIP_TAC THENL
   [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    EXISTS_TAC `k + i` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]]);;

(* the addresses from a byte-aligned base are byte-aligned *)
let PTOPAUX_addresses_aligned = prove
 (`!(a:A word) n x.
     good_dimindex (:A) /\ byte_aligned a /\ x IN addresses a n ==> byte_aligned x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_addresses] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC byte_aligned_add THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN ASM_SIMP_TAC[byte_aligned_bytes_in_word_MULT]);;

(* the heap of the initial stackLang state: its length and the stack length *)
let PTOPAUX_heap_facts = prove
 (`!(sst:(A,C,FFI)stack_state) ggc mh dsp (w2:A word) w3 w4 hsp.
     good_dimindex(:A) /\
     init_prop ggc mh dsp (get_stack_heap_limit mh (w2,w3,w4)) sst /\
     FLOOKUP (stack_state_store sst) CurrHeap = SOME (wl_Word w2) /\
     stack_state_mdomain sst = addresses w2 hsp /\
     hsp < dimword(:A) DIV (dimindex(:A) DIV 8)
     ==> FLOOKUP (stack_state_store sst) HeapLength =
           SOME (wl_Word (word_mul (word (SND (get_stack_heap_limit mh (w2,w3,w4))))
                                   bytes_in_word)) /\
         hsp = 2 * SND (get_stack_heap_limit mh (w2,w3,w4)) /\
         LENGTH (stack_state_stack sst) = FST (get_stack_heap_limit mh (w2,w3,w4))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`get_stack_heap_limit mh (w2,w3,w4:A word)`,`lim:num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`sl:num`; `hl:num`] THEN
  REWRITE_TAC[init_prop_def; stack_heap_limit_ok_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `curr:A word = w2` SUBST_ALL_TAC THENL
  [UNDISCH_TAC `FLOOKUP (stack_state_store (sst:(A,C,FFI)stack_state)) CurrHeap =
                SOME (wl_Word w2)` THEN
   ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(dimindex(:A) DIV 8 = 0)` ASSUME_TAC THENL
  [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
   ALL_TAC] THEN
  SUBGOAL_THEN `len + len = hsp` ASSUME_TAC THENL
  [MATCH_MP_TAC (INST_TYPE [`:(A)word_loc`,`:B`] PTOPAUX_wle_addresses) THEN
   MAP_EVERY EXISTS_TAC [`w2:A word`; `stack_state_memory (sst:(A,C,FFI)stack_state)`] THEN
   ASM_REWRITE_TAC[stack_removeProof_word_list_exists_ADD] THEN
   UNDISCH_TAC `(word_list_exists (w2:A word) len STAR word_list_exists other len)
                  (fun2set (stack_state_memory (sst:(A,C,FFI)stack_state),
                            stack_state_mdomain sst))` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `len * dimindex(:A) DIV 8 < dimword(:A)` ASSUME_TAC THENL
  [UNDISCH_TAC `hsp < dimword(:A) DIV (dimindex(:A) DIV 8)` THEN
   UNDISCH_TAC `len + len = hsp` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   ASM_SIMP_TAC[GSYM LE_SUC_LT; LE_RDIV_EQ] THEN REWRITE_TAC[MULT_CLAUSES; LEFT_ADD_DISTRIB] THEN
   MP_TAC (SPECL [`len:num`; `dimindex(:A) DIV 8`] MULT_SYM) THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `len:num = hl` SUBST_ALL_TAC THENL
  [SUBGOAL_THEN `word_mul (word len) bytes_in_word:A word = word_mul (word hl) bytes_in_word`
     MP_TAC THENL
   [UNDISCH_TAC `FLOOKUP (stack_state_store (sst:(A,C,FFI)stack_state)) HeapLength =
                 SOME (wl_Word (word_mul (word hl) bytes_in_word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"];
    ALL_TAC] THEN
   REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL; WORD_EQ; dimword_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
   ASM_SIMP_TAC[MOD_LT; CONG] THEN ASM_REWRITE_TAC[EQ_MULT_RCANCEL];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* the address of the globals of the Pancake state *)
let PTOPAUX_top_addr_eq = prove
 (`!(base:A word) top heap_len gs.
     good_dimindex(:A) /\ gs <= heap_len /\
     top = word_sub (word_add base (word_mul bytes_in_word (word heap_len)))
                    (word ((gs * dimindex(:A)) DIV 8))
     ==> top = word_add base (word_mul bytes_in_word (word (heap_len - gs))) /\
         !hl0. heap_len = 2 * hl0 ==>
               top = word_sub (word_add base (word_mul (word 2) (word_mul (word hl0) bytes_in_word)))
                              (word_mul bytes_in_word (word gs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[good_dimindex_div_mul; n2w_sub] THEN
  REWRITE_TAC[bytes_in_word_def; WORD_MUL] THEN CONJ_TAC THENL
  [CONV_TAC WORD_RULE; GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[WORD_MUL] THEN CONV_TAC WORD_RULE]);;

(* terms of the proof of pan_to_target_compile_semantics (HOL4: lprog, the *)
(* initial labLang state labst, the compiler oracles lorac and worac, the   *)
(* initial wordLang state wst; free variables as in the statement)         *)
let PTOPAUX_tm_lprog =
  `stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
     (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
     (asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
      (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
     (asm_config_addr_offset (target_config (machine_config_target mc)))
     (p:(num#(A)stack_prog)list)`;;

let PTOPAUX_tm_dm =
  `{w | word_ule (asm_state_regs (t:(A)asm_state)
                    (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2)) w /\
        word_ult w (asm_state_regs t
                    (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4))}
   UNION (bitmaps_dm:A word->bool)`;;

let PTOPAUX_tm_labst =
  vsubst [PTOPAUX_tm_lprog,`lprog:((A)sec)list`; PTOPAUX_tm_dm,`dm:A word->bool`]
  `lab_to_targetProof_make_init (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (t:(A)asm_state)
     (m:A word->(A)word_loc) ((dm:A word->bool) INTER byte_aligned)
     ((sdm:A word->bool) INTER byte_aligned) (ms:B) (lprog:((A)sec)list)
     (lab_to_target_compile (target_config (machine_config_target mc)))
     (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH (bytes:byte list))))
     (cbspace:num) (\n:num. (backend_config_lab_conf (c':backend_config),[]:((A)sec)list))`;;

let PTOPAUX_tm_lorac =
  `\n:num. (backend_config_lab_conf (c':backend_config),[]:(num#(A)stack_prog)list,
            []:(A word)list)`;;

let PTOPAUX_tm_worac =
  `\n:num. ((LENGTH (bitmaps:(A word)list),backend_config_lab_conf (c':backend_config)),
            []:(num#num#(A)wl_prog)list)`;;

let PTOPAUX_tm_fmi =
  vsubst [PTOPAUX_tm_labst,`labst:(A,lab_to_target_config,FFI)lab_state`;
          PTOPAUX_tm_lorac,`lorac:num->lab_to_target_config#(num#(A)stack_prog)list#(A word)list`]
  `full_make_init (backend_config_stack_conf c) (backend_config_data_conf c)
     (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
     (asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
      (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3))
     (asm_config_addr_offset (target_config (machine_config_target mc)))
     (bitmaps:(A word)list) (p:(num#(A)stack_prog)list)
     (labst:(A,lab_to_target_config,FFI)lab_state)
     (set_of_list (machine_config_callee_saved_regs mc)) (data_sp:num)
     (lorac:num->lab_to_target_config#(num#(A)stack_prog)list#(A word)list)`;;

let PTOPAUX_tm_wst =
  vsubst [PTOPAUX_tm_worac,
          `worac:num->(num#lab_to_target_config)#(num#num#(A)wl_prog)list`]
  `word_to_stackProof_make_init (target_config (machine_config_target (mc:(A,B,C)machine_config)))
     (asm_config_reg_count (target_config (machine_config_target mc)) -
      (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 5))
     (sst:(A,lab_to_target_config,FFI)stack_state) (fromAList (wprog:(num#num#(A)wl_prog)list))
     (worac:num->(num#lab_to_target_config)#(num#num#(A)wl_prog)list)`;;

(* tactics of the proof of pan_to_target_compile_semantics *)
let PTOPAUX_EQ_HD name rname (th:thm) =
  let c = concl th in
  is_eq c &&
  (try fst (dest_const (fst (strip_comb (lhs c)))) = name with Failure _ -> false) &&
  (rname = "" ||
   (try fst (dest_const (fst (strip_comb (rhs c)))) = rname with Failure _ -> false));;

let PTOPAUX_MENTIONS name tm =
  can (find_term (fun t -> try fst (dest_const t) = name with Failure _ -> false)) tm;;

(* the alignment of the heap base and the memory domain of the stack state *)
let PTOPAUX_PAN_PREP_TAC : tactic =
  SUBGOAL_THEN `byte_aligned (pan_state_base_addr (s:(A,FFI)pan_state))` ASSUME_TAC THENL
  [FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "asm_state_regs" "pan_state_base_addr" th
     then SUBST1_TAC (SYM th) else failwith "") THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `stack_state_mdomain (sst:(A,lab_to_target_config,FFI)stack_state) =
                addresses (pan_state_base_addr (s:(A,FFI)pan_state)) heap_len` ASSUME_TAC THENL
  [FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "stack_state_mdomain" "addresses" th
     then SUBST1_TAC th else failwith "") THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `stack_state_mdomain (sst:(A,lab_to_target_config,FFI)stack_state) =
                pan_state_memaddrs (s:(A,FFI)pan_state) UNION
                addresses (pan_state_top_addr s) globals_size` ASSUME_TAC THENL
  [FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "stack_state_mdomain" "addresses" th &&
       (try fst (dest_const (fst (strip_comb (rand (rator (rhs (concl th))))))) =
            "pan_state_base_addr" with Failure _ -> false)
     then SUBST1_TAC th else failwith "") THEN
   FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "pan_state_memaddrs" "" th
     then SUBST1_TAC th else failwith "") THEN
   FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "pan_state_top_addr" "word_add" th
     then SUBST1_TAC th else failwith "") THEN
   FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "target_get_reg" "pan_state_base_addr" th
     then SUBST1_TAC th else failwith "") THEN
   MP_TAC (ISPECL [`pan_state_base_addr (s:(A,FFI)pan_state)`; `heap_len:num`;
                   `heap_len - globals_size`] PTOPAUX_addresses_split) THEN
   ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   SUBGOAL_THEN `heap_len - (heap_len - globals_size) = globals_size` SUBST1_TAC THENL
   [UNDISCH_TAC `globals_size <= heap_len` THEN ARITH_TAC; REWRITE_TAC[]];
   ALL_TAC];;

(* the memory of the stack state agrees with the original one on mdomain *)
let PTOPAUX_PAN_MEM_TAC (a:term) : tactic =
  FIRST_ASSUM(fun th -> if is_forall (concl th) &&
      PTOPAUX_MENTIONS "stack_state_memory" (concl th) &&
      PTOPAUX_MENTIONS "stack_state_mdomain" (concl th)
    then MP_TAC (SPEC a th) else failwith "") THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC];;

(* the premises of PTOPAUX_pan_step, by their form *)
let PTOPAUX_PAN_PREM_TAC : tactic = fun (asl,w as g) ->
  let lhs_is name = is_eq w &&
    (try fst (dest_const (fst (strip_comb (lhs w)))) = name with Failure _ -> false) in
  if PTOPAUX_MENTIONS "wlab_wloc" w then
   (X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:A word) IN stack_state_mdomain (sst:(A,lab_to_target_config,FFI)stack_state)`
      ASSUME_TAC THENL
    [FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "stack_state_mdomain" "UNION" th
       then SUBST1_TAC th else failwith "") THEN
     ASM_REWRITE_TAC[IN_UNION];
     ALL_TAC] THEN
    PTOPAUX_PAN_MEM_TAC `a:A word` THEN
    FIRST_X_ASSUM(fun th -> if is_forall (concl th) && PTOPAUX_MENTIONS "wlab_wloc" (concl th)
      then MP_TAC (SPEC `a:A word` th) else failwith "") THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[o_THM]]) g
  else if PTOPAUX_MENTIONS "no_labels" w then
   (REWRITE_TAC[no_labels_def] THEN X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
    PTOPAUX_PAN_MEM_TAC `a:A word` THEN
    SUBGOAL_THEN `byte_align (a:A word) = a`
      (fun th -> GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o RAND_CONV) [GSYM th]) THENL
    [REWRITE_TAC[GSYM byte_align_aligned] THEN MATCH_MP_TAC PTOPAUX_addresses_aligned THEN
     MAP_EVERY EXISTS_TAC [`pan_state_base_addr (s:(A,FFI)pan_state)`; `heap_len:num`] THEN
     FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "stack_state_mdomain" "addresses" th &&
         (try fst (dest_const (fst (strip_comb (rand (rator (rhs (concl th))))))) =
              "pan_state_base_addr" with Failure _ -> false)
       then (RULE_ASSUM_TAC (REWRITE_RULE[th])) else failwith "") THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall (concl th) && PTOPAUX_MENTIONS "get_byte" (concl th)
      then MP_TAC (SPEC `a:A word` th) else failwith "") THEN
    MESON_TAC[]) g
  else if lhs_is "stack_state_mdomain" then
   FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "stack_state_mdomain" "UNION" th
     then ACCEPT_TAC th else failwith "") g
  else if lhs_is "stack_state_ffi" then
   (FIRST_ASSUM(MP_TAC o AP_TERM `FST:(A,lab_to_target_config,FFI)stack_state#
                                       ((A,lab_to_target_config,FFI)stack_state)option->
                                       (A,lab_to_target_config,FFI)stack_state` o
                check (PTOPAUX_EQ_HD "full_make_init" "")) THEN
    REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[full_make_init_ffi; lab_to_targetProof_make_init_def;
                (record_info "lab_state").ri_accessors] THEN
    ASM_REWRITE_TAC[]) g
  else if lhs_is "pan_state_top_addr" then
   (FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
       fst (dest_var (fst (dest_forall (concl th)))) = "hl0")) THEN
    FIRST_ASSUM(fun th -> let c = concl th in
      if is_eq c && is_var (lhs c) && fst (dest_var (lhs c)) = "hsp" && is_var (rhs c)
      then SUBST1_TAC (SYM th) else failwith "") THEN
    FIRST_ASSUM ACCEPT_TAC) g
  else if PTOPAUX_MENTIONS "byte_aligned" w && PTOPAUX_MENTIONS "pan_state_top_addr" w then
   (FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "pan_state_top_addr" "word_add" th
      then SUBST1_TAC th else failwith "") THEN
    MATCH_MP_TAC byte_aligned_add THEN ASM_SIMP_TAC[byte_aligned_bytes_in_word_MULT]) g
  else (FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC)) g;;

(* the wordLang semantics is the Pancake semantics *)
let PTOPAUX_W_EQ_D_TAC : tactic =
  FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "wl_semantics" "wl_semantics" th
    then SUBST1_TAC (SYM th) else failwith "") THEN
  FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "wl_semantics" "semantics_decls" th
    then SUBST1_TAC th else failwith "");;

(* the resource limit: the stack bound of compile_prog_max *)
let PTOPAUX_LIMIT_TAC : tactic =
  REWRITE_TAC[option_lt_SOME] THEN DISCH_THEN(X_CHOOSE_THEN `mm:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC PTOPAUX_limit_step THEN EXISTS_TAC `mm:num` THEN
  REWRITE_TAC[BKP2AUX_w2s_make_init_fields; BKP2AUX_stack_size] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC PTOPAUX_wl_sem_no_error THEN PTOPAUX_W_EQ_D_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   FIRST_ASSUM(fun th -> if PTOPAUX_EQ_HD "word_to_stack_compile" "" th then
       MP_TAC (MATCH_MP PTOPAUX_sfs_eq (CONJ th
         (ASSUME `ALL_DISTINCT (MAP FST (wprog:(num#num#(A)wl_prog)list))`)))
     else failwith "") THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
   FIRST_X_ASSUM(fun th -> if is_binary "<" (concl th) && lhand (concl th) = `mm:num`
     then MP_TAC th else failwith "") THEN
   ASM_REWRITE_TAC[]];;

(* HOL4 line 1257 (resource_limit'): the headline theorem, its statement in *)
(* pan_to_target_statement.ml.  The proof follows HOL4's: lab_to_target    *)
(* (PTOPAUX_lab_step), stack_to_lab (PTOPAUX_stack_step), word_to_stack    *)
(* (PTOPAUX_word_step), word_to_word (PTOPAUX_w2w_step), pan_to_word      *)
(* (PTOPAUX_pan_step) and the stack bound (PTOPAUX_LIMIT_TAC), composed by *)
(* backendProof's BKP2AUX_compose; the heap facts come from init_prop      *)
(* (PTOPAUX_fmi_facts, PTOPAUX_heap_facts) instead of HOL4's direct        *)
(* computation of the registers after the init code                        *)
let pan_to_target_compile_semantics = prove
 (pan_to_target_compile_semantics_statement,
  (REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst (dest_var (lhs (concl th))) = "start"))) THEN
  (FIRST_X_ASSUM(X_CHOOSE_THEN `col:(((num)spt)option)list`
    (X_CHOOSE_THEN `wprog:(num#num#(A)wl_prog)list`
    (X_CHOOSE_THEN `c'':word_to_stack_config` (X_CHOOSE_THEN `fs:num list`
    (X_CHOOSE_THEN `p:(num#(A)stack_prog)list` STRIP_ASSUME_TAC)))) o
    MATCH_MP PTOPAUX_compile_prog_max_SOME)) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "pan_installed" with Failure _ -> false))) THEN
  (REWRITE_TAC[pan_installed_def; heap_regs_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV)) THEN
  (DISCH_THEN(X_CHOOSE_THEN `t:(A)asm_state` (X_CHOOSE_THEN `m:A word->(A)word_loc`
    (X_CHOOSE_THEN `bitmap_ptr:A word` (X_CHOOSE_THEN `bitmaps_dm:A word->bool`
    (X_CHOOSE_THEN `sdm:A word->bool` STRIP_ASSUME_TAC)))))) THEN
  (SUBGOAL_THEN `good_dimindex (:A)` ASSUME_TAC THENL
  [FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[mc_conf_ok_def]
     (check (fun th -> can (term_match [] `mc_conf_ok (mc:(A,B,C)machine_config)`) (concl th))
        th)]);
   ALL_TAC]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def] o
     check (fun th -> can (term_match [] `backend_config_ok (ac:(A)asm_config) c`) (concl th)))) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mc_init_ok_def] o
     check (fun th -> can (term_match []
       `mc_init_ok (ac:(A)asm_config) (c:backend_config) (mc:(A,B,C)machine_config)`) (concl th)))) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[good_init_state_def] o
     check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "good_init_state"
                      with Failure _ -> false))) THEN
  (SUBGOAL_THEN `!i. i < 13 ==>
     asm_state_regs (t:(A)asm_state)
       (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) i) =
     target_get_reg (machine_config_target (mc:(A,B,C)machine_config)) ms
       (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) i)`
   ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC BKP2AUX_names_target_regs THEN ASM_REWRITE_TAC[];
   ALL_TAC]) THEN
  (MP_TAC (ISPECL [`stack_to_lab_config_reg_names (backend_config_stack_conf c)`;
                  `bitmaps:(A word)list`; `data_sp:num`; `mc:(A,B,C)machine_config`;
                  `ffi:(FFI)ffi_state`; `t:(A)asm_state`; `m:A word->(A)word_loc`;
                  `bitmap_ptr:A word`; `bitmaps_dm:A word->bool`; `sdm:A word->bool`; `ms:B`;
                  PTOPAUX_tm_lprog;
                  `lab_to_target_compile (target_config (machine_config_target
                     (mc:(A,B,C)machine_config)))`;
                  `cbspace:num`;
                  `\n:num. (backend_config_lab_conf (c':backend_config),[]:((A)sec)list)`;
                  `bytes:byte list`] BKP2AUX_mem_assumption)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  (SUBGOAL_THEN (mk_exists(`sst:(A,lab_to_target_config,FFI)stack_state`,
     mk_exists(`opt:((A,lab_to_target_config,FFI)stack_state)option`,
       mk_eq(PTOPAUX_tm_fmi, `(sst:(A,lab_to_target_config,FFI)stack_state,
                              opt:((A,lab_to_target_config,FFI)stack_state)option)`))))
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC]) THEN
  (MP_TAC (ISPECL [`c:backend_config`; `mc:(A,B,C)machine_config`; `pan_code:((A)decl)list`;
                  `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
                  `bitmaps:(A word)list`; `c'':word_to_stack_config`; `fs:num list`;
                  `p:(num#(A)stack_prog)list`; `bytes:byte list`;
                  `backend_config_lab_conf c'`; `ffi:(FFI)ffi_state`; `ms:B`; `cbspace:num`;
                  `t:(A)asm_state`; `m:A word->(A)word_loc`; PTOPAUX_tm_dm; `sdm:A word->bool`;
                  `data_sp:num`; `sst:(A,lab_to_target_config,FFI)stack_state`;
                  `opt:((A,lab_to_target_config,FFI)stack_state)option`] PTOPAUX_stack_step)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  (FIRST_X_ASSUM(X_CHOOSE_THEN `xxx:(A,lab_to_target_config,FFI)stack_state` SUBST_ALL_TAC o
    REWRITE_RULE[GSYM IS_SOME_EQ_NOT_NONE; IS_SOME_EXISTS] o
    check (fun th -> concl th =
      `~(opt:((A,lab_to_target_config,FFI)stack_state)option = NONE)`))) THEN
  (MP_TAC (ISPECL [`c:backend_config`; `mc:(A,B,C)machine_config`; `pan_code:((A)decl)list`;
                  `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
                  `bitmaps:(A word)list`; `c'':word_to_stack_config`; `fs:num list`;
                  `p:(num#(A)stack_prog)list`; `bytes:byte list`;
                  `backend_config_lab_conf c'`; `ffi:(FFI)ffi_state`; `ms:B`; `cbspace:num`;
                  `t:(A)asm_state`; `m:A word->(A)word_loc`; PTOPAUX_tm_dm; `sdm:A word->bool`]
                 PTOPAUX_lab_step)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC]) THEN
  (MP_TAC (ISPECL [`backend_config_stack_conf c`; `backend_config_data_conf c`;
                  `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
                  `asm_config_reg_count (target_config (machine_config_target
                     (mc:(A,B,C)machine_config))) -
                   (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)`;
                  `asm_config_addr_offset (target_config (machine_config_target
                     (mc:(A,B,C)machine_config)))`;
                  `bitmaps:(A word)list`; `p:(num#(A)stack_prog)list`; PTOPAUX_tm_labst;
                  `set_of_list (machine_config_callee_saved_regs (mc:(A,B,C)machine_config))`;
                  `data_sp:num`; PTOPAUX_tm_lorac;
                  `sst:(A,lab_to_target_config,FFI)stack_state`;
                  `xxx:(A,lab_to_target_config,FFI)stack_state`] PTOPAUX_fmi_facts)) THEN
  (ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC word_to_stack_good_code_lemma THEN
    MAP_EVERY EXISTS_TAC [`c:backend_config`; `pan_code:((A)decl)list`;
                          `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
                          `bitmaps:(A word)list`; `c'':word_to_stack_config`; `fs:num list`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[stack_to_labProof_good_code_def; MAP; ALL; ALL_DISTINCT];
    UNDISCH_TAC `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                   (mc:(A,B,C)machine_config)))) + 13 <=
                 asm_config_reg_count (target_config (machine_config_target mc))` THEN
    ARITH_TAC;
    SUBGOAL_THEN `!r. (r + (asm_config_reg_count (target_config (machine_config_target
                        (mc:(A,B,C)machine_config))) -
                       (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) +
                        3))) - 2 =
                      (r + asm_config_reg_count (target_config (machine_config_target mc))) -
                      (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) +
                       5)`
      (fun th -> REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `LENGTH (asm_config_avoid_regs (target_config (machine_config_target
                    (mc:(A,B,C)machine_config)))) + 13 <=
                  asm_config_reg_count (target_config (machine_config_target mc))` THEN
     ARITH_TAC;
     ASM_REWRITE_TAC[IN_SET_OF_LIST]]];
   DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[lab_to_targetProof_make_init_def;
     (record_info "lab_state").ri_accessors; theWord_def])]) THEN
  (MP_TAC (ISPECL [`c:backend_config`; `mc:(A,B,C)machine_config`; `pan_code:((A)decl)list`;
                  `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
                  `bitmaps:(A word)list`; `c'':word_to_stack_config`; `fs:num list`;
                  `p:(num#(A)stack_prog)list`; `backend_config_lab_conf c'`; PTOPAUX_tm_labst;
                  `set_of_list (machine_config_callee_saved_regs (mc:(A,B,C)machine_config))`;
                  `data_sp:num`; `sst:(A,lab_to_target_config,FFI)stack_state`;
                  `SOME (xxx:(A,lab_to_target_config,FFI)stack_state)`] PTOPAUX_word_step)) THEN
  (ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC) THEN
  (SUBGOAL_THEN
   `asm_state_regs (t:(A)asm_state)
      (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2) =
    pan_state_base_addr (s:(A,FFI)pan_state) /\
    asm_state_regs t (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 3) =
    target_get_reg (machine_config_target (mc:(A,B,C)machine_config)) ms
      (machine_config_ptr2_reg mc) /\
    asm_state_regs t (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4) =
    target_get_reg (machine_config_target mc) ms (machine_config_len2_reg mc)`
   STRIP_ASSUME_TAC THENL
  [FIRST_ASSUM(fun th -> if is_forall (concl th) &&
       fst (dest_var (fst (dest_forall (concl th)))) = "i"
     then MP_TAC (CONJ (SPEC `2` th) (CONJ (SPEC `3` th) (SPEC `4` th))) else failwith "") THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC]) THEN
  (MP_TAC (ISPECL [`sst:(A,lab_to_target_config,FFI)stack_state`;
   `is_gen_gc (data_to_word_config_gc_kind (backend_config_data_conf c))`;
   `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`; `data_sp:num`;
   `asm_state_regs (t:(A)asm_state)
      (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2)`;
   `asm_state_regs (t:(A)asm_state)
      (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 3)`;
   `asm_state_regs (t:(A)asm_state)
      (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4)`;
   `hsp:num`] PTOPAUX_heap_facts)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  (MP_TAC (ISPECL [`2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
   `asm_state_regs (t:(A)asm_state)
      (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2)`;
   `asm_state_regs (t:(A)asm_state)
      (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 3)`;
   `asm_state_regs (t:(A)asm_state)
      (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4)`]
   PTOPAUX_heap_lim_arith)) THEN
  (ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     is_var (lhs (concl th)) && mem (fst (dest_var (lhs (concl th)))) ["adj_ptr2"; "adj_ptr4"]))) THEN
   ASM_MESON_TAC[];
   DISCH_TAC]) THEN
  (SUBGOAL_THEN `FST (backendProof_read_limits (target_config (machine_config_target
                  (mc:(A,B,C)machine_config))) c mc ms) =
                LENGTH (stack_state_stack (sst:(A,lab_to_target_config,FFI)stack_state))`
   ASSUME_TAC THENL
  [FIRST_ASSUM(fun th -> if is_forall (concl th) &&
       fst (dest_var (fst (dest_forall (concl th)))) = "i"
     then MP_TAC (CONJ (SPEC `2` th) (CONJ (SPEC `3` th) (SPEC `4` th))) else failwith "") THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[backendProof_read_limits_def; GSYM th]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC]) THEN
  (SUBGOAL_THEN `hsp:num = heap_len` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_comb (lhs (concl th)) &&
       (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "*" with Failure _ -> false)
     then SUBST1_TAC th else failwith "") THEN
   ASM_REWRITE_TAC[];
   ALL_TAC]) THEN
  (W(fun (asl,w) ->
    let th = snd (find (fun (_,th) -> let c = concl th in is_eq c && is_var (lhs c) &&
                        fst (dest_var (lhs c)) = "hsp" && not (is_var (rhs c))) asl) in
    let sndt = rand (rhs (concl th)) in
    SUBGOAL_THEN (mk_exists(`hl0:num`, mk_eq(sndt, `hl0:num`)))
      (X_CHOOSE_THEN `hl0:num` (fun eq -> RULE_ASSUM_TAC (REWRITE_RULE [eq]))) THENL
    [MESON_TAC[]; ALL_TAC])) THEN
  (MP_TAC (ISPECL [`pan_state_base_addr (s:(A,FFI)pan_state)`; `pan_state_top_addr (s:(A,FFI)pan_state)`;
                  `heap_len:num`; `globals_size:num`] PTOPAUX_top_addr_eq)) THEN
  (ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(fun th -> if is_eq (concl th) &&
       (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "pan_state_top_addr"
        with Failure _ -> false) then ACCEPT_TAC th else failwith "");
   STRIP_TAC]) THEN
  (MP_TAC (ISPECL [`s:(A,FFI)pan_state`; `sst:(A,lab_to_target_config,FFI)stack_state`;
   `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
   `asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
    (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 5)`;
   `fromAList (wprog:(num#num#(A)wl_prog)list)`; PTOPAUX_tm_worac; `pan_code:((A)decl)list`;
   `asm_config_ISA (target_config (machine_config_target (mc:(A,B,C)machine_config)))`;
   `implode "main"`; `globals_size:num`; `word_mul (word hl0) bytes_in_word:A word`]
   PTOPAUX_pan_step) THEN
   ANTS_TAC THENL
   [PTOPAUX_PAN_PREP_TAC THEN REPEAT CONJ_TAC THEN PTOPAUX_PAN_PREM_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM InitGlobals_location_eq_first_name])]) THEN
  (MP_TAC (ISPECL [`backend_config_word_to_word_conf c`;
   `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
   `asm_config_ISA (target_config (machine_config_target (mc:(A,B,C)machine_config)))`;
   `pan_code:((A)decl)list`; `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`;
   PTOPAUX_tm_wst; `InitGlobals_location`] PTOPAUX_w2w_step) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[BKP2AUX_w2s_make_init_fields; lookup_insert; gc_fun_const_ok_word_gc_fun];
    DISCH_TAC]) THEN
  (SUBGOAL_THEN `ALL_DISTINCT (MAP FST (wprog:(num#num#(A)wl_prog)list)) /\
                no_install_code (fromAList wprog) /\ no_alloc_code (fromAList wprog)`
   STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `ALL_DISTINCT (MAP FST (pan_to_word_compile_prog (asm_config_ISA
       (target_config (machine_config_target (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC pan_to_wordProof_first_compile_prog_all_distinct THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC (ISPECL [`backend_config_word_to_word_conf c`;
                   `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
                   `pan_to_word_compile_prog (asm_config_ISA (target_config (machine_config_target
                      (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)`;
                   `col:(((num)spt)option)list`; `wprog:(num#num#(A)wl_prog)list`]
                  word_to_word_compile_no_install_no_alloc) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC pan_to_word_compile_prog_no_mt_code THEN MESON_TAC[];
     MATCH_MP_TAC pan_to_word_compile_prog_no_install_code THEN MESON_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `no_alloc_code (fromAList (pan_to_word_compile_prog (asm_config_ISA
       (target_config (machine_config_target (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)))`
     (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC pan_to_word_compile_prog_no_alloc_code THEN MESON_TAC[]; ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC (MATCH_MP compile_to_word_conventions2
     (CONJ (ASSUME `word_to_word_compile (backend_config_word_to_word_conf c)
                      (target_config (machine_config_target (mc:(A,B,C)machine_config)))
                      (pan_to_word_compile_prog (asm_config_ISA (target_config
                         (machine_config_target mc))) (pan_code:((A)decl)list)) = (col,wprog)`)
           (SPEC `pan_to_word_compile_prog (asm_config_ISA (target_config
                    (machine_config_target (mc:(A,B,C)machine_config)))) (pan_code:((A)decl)list)`
              (MATCH_MP PTOPAUX_ALL_no_share_Ag32
                (ASSUME `~(asm_config_ISA (target_config (machine_config_target
                            (mc:(A,B,C)machine_config))) = Ag32)`))))) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC]) THEN
  (MATCH_MP_TAC BKP2AUX_compose THEN
   MAP_EVERY EXISTS_TAC
     [mk_comb(`lab_semantics:(A,lab_to_target_config,FFI)lab_state->behaviour`,
              PTOPAUX_tm_labst);
      `stack_semantics InitGlobals_location (sst:(A,lab_to_target_config,FFI)stack_state)`;
      mk_comb(mk_comb(`wl_semantics:(A,num#lab_to_target_config,FFI)wl_state->num->behaviour`,
                      PTOPAUX_tm_wst), `InitGlobals_location`);
      mk_comb(mk_comb(`word_lang_safe_for_space:(A,num#lab_to_target_config,FFI)wl_state->num->bool`,
                      PTOPAUX_tm_wst), `InitGlobals_location`)] THEN
   REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    PTOPAUX_W_EQ_D_TAC THEN REWRITE_TAC[extend_with_resource_limit'_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_SING];
    FIRST_ASSUM ACCEPT_TAC;
    PTOPAUX_LIMIT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]));;

(* the headline check: the theorem is the statement of the statement file *)
let () =
  if hyp pan_to_target_compile_semantics = [] &&
     aconv (concl pan_to_target_compile_semantics) pan_to_target_compile_semantics_statement
  then () else failwith "pan_to_target_compile_semantics is not the headline statement";;

