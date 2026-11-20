(* ========================================================================= *)
(* backendProof_p2: part 2 of 2 (HOL4 lines 2279-4502) of the port of HOL4  *)
(* compiler/backend/proofs/backendProofScript.sml (CakeML v3479).           *)
(* Composes the correctness theorems for all of the compiler phases.        *)
(* The parts _p1 and _p2 are loaded one after the other (this one needs     *)
(* _p1, whose notes on the rendering apply here too).  BKP2AUX_ names are   *)
(* local helpers of this part.                                               *)
(*                                                                           *)
(* Notes:                                                                    *)
(* - The long HOL4 proofs (good_code_lab_oracle, oracle_stack_good_code and *)
(*   compile_correct') are split into BKP2AUX_ lemmas, one per step of the  *)
(*   HOL4 proof (the oracle programs of each phase, the data_to_word,       *)
(*   word_to_stack, stack_to_lab and lab_to_target steps, the limits and    *)
(*   the composition of the refinements), placed before the theorem.        *)
(* - BKP2AUX_d2w_orac_eq_sym is derived from data_to_word_orac_eq exactly   *)
(*   as data_to_word_orac_eq_sym_std (HOL4 line 2673) is, because the       *)
(*   oracle theorems at HOL4 line 2330 need it before that binding.          *)
(* ========================================================================= *)

needs "compiler/backend/proofs/backendProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 2279-4502 ===== *)

(* Local proof helpers (BKP2AUX_) *)

(* HOL4 qhdtm_x_assum / qhdtm_assum: select the assumption whose conclusion *)
(* (under a negation, the left side of an equation) has the constant NAME   *)
(* at its head                                                               *)
let BKP2AUX_head_is name t =
  let t = if is_neg t then dest_neg t else t in
  let t = if is_eq t then lhs t else t in
  let h = fst (strip_comb t) in
  is_const h && fst (dest_const h) = name;;

let BKP2AUX_HDTM_X_ASSUM name (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th -> if BKP2AUX_head_is name (concl th) then ttac th
                           else failwith "BKP2AUX_HDTM_X_ASSUM");;

let BKP2AUX_HDTM_ASSUM name (ttac:thm_tactic) : tactic =
  FIRST_ASSUM (fun th -> if BKP2AUX_head_is name (concl th) then ttac th
                         else failwith "BKP2AUX_HDTM_ASSUM");;

(* generalise the first subterm of the goal that applies the constant NAME *)
(* to N arguments (to case-split on it)                                     *)
let BKP2AUX_GEN_CONST_TAC name n : tactic =
  W(fun (asl,w) ->
     let t = find_term (fun t -> try let h,args = strip_comb t in
                                     fst(dest_const h) = name && length args = n
                                 with Failure _ -> false) w in
     SPEC_TAC(t, mk_var("t", type_of t)));;

(* select an assumption whose conclusion mentions the constant NAME *)
let BKP2AUX_mentions name t =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) t;;

let BKP2AUX_ASSUM_MENTIONS name (ttac:thm_tactic) : tactic =
  FIRST_ASSUM (fun th -> if BKP2AUX_mentions name (concl th) then ttac th
                         else failwith "BKP2AUX_ASSUM_MENTIONS");;

let BKP2AUX_X_ASSUM_MENTIONS name (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th -> if BKP2AUX_mentions name (concl th) then ttac th
                           else failwith "BKP2AUX_X_ASSUM_MENTIONS");;

(* HOL4 line 2279 *)
let backendProof_syntax_oracle_ok_start = prove
 (`!c f c' es co.
     clos_to_bvlProof_syntax_oracle_ok c (clos_to_bvl_config_start_fupd f c') es
     (co:num->(num#(val_approx)spt#num_set#B)#clos_prog) <=>
   clos_to_bvlProof_syntax_oracle_ok c c' es co`,
  SIMP[clos_to_bvlProof_syntax_oracle_ok_def]);;

(* the closLang configuration in the configuration returned by compile *)
let BKP2AUX_compile_clos_conf = prove
 (`!asm_conf c prog b bm c'.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> ?st. backend_config_clos_conf c' =
              clos_to_bvl_config_start_fupd (K st)
                (FST (clos_to_bvl_compile (backend_config_clos_conf c)
                        (SND (to_clos c prog))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_eq_to_target; to_target_def; to_lab_def; to_stack_def; to_word_def;
              to_data_def; to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
  BACKDEFAUX_LETS_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  EXISTS_TAC `p1''':num` THEN AP_TERM_TAC THEN
  BKP2AUX_HDTM_ASSUM "clos_to_bvl_compile"
    (fun th -> REWRITE_TAC[REWRITE_RULE[(record_info "backend_config").ri_accfupds] th]));;

(* oracle_monotonic for a smaller initial set *)
let BKP2AUX_oracle_monotonic_init_subset = prove
 (`!(f:A->B->bool) R St St' co.
     St' SUBSET St /\ oracle_monotonic f R St co ==> oracle_monotonic f R St' co`,
  REWRITE_TAC[oracle_monotonic_def; SUBSET] THEN MESON_TAC[]);;

(* the BVL program of to_bvl *)
let BKP2AUX_to_bvl_prog = prove
 (`!c prog. FST (SND (to_bvl c prog)) =
            FST (SND (clos_to_bvl_compile (backend_config_clos_conf c) (SND (to_clos c prog))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[to_bvl_def] THEN
  SUBGOAL_THEN `backend_config_clos_conf (FST (to_clos c prog)) = backend_config_clos_conf c`
   MP_TAC THENL
  [REWRITE_TAC[to_clos_def; to_flat_def] THEN BACKDEFAUX_LETS_TAC THEN SIMP[]; ALL_TAC] THEN
  W(fun (asl,w) -> let t = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "to_clos"
                                               with Failure _ -> false) w in
                   SPEC_TAC(t, mk_var("q", type_of t))) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 2286 *)
let monotonic_labels_bvl = prove
 (`!asm_conf c prog b bm c' syntax.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   backend_config_ok asm_conf c
   ==> oracle_monotonic (set_of_list o MAP FST o SND) (\x y. ~(x = y))
         (set_of_list (MAP FST (FST (SND (to_bvl c prog)))))
         (cake_orac asm_conf c' syntax config_tuple2 (\ps. backend_progs_bvl_prog ps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `st:num` o MATCH_MP BKP2AUX_compile_clos_conf) THEN
  SUBGOAL_THEN `?clos_c' p names. clos_to_bvl_compile (backend_config_clos_conf c)
                   (SND (to_clos c prog)) =
                 (clos_c',p:(num#num#bvl_exp)list,names:mlstring spt)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                 `bm:(A word)list`; `c':backend_config`; `backend_config_clos_conf c`;
                 `SND (to_clos c prog)`; `clos_c':clos_to_bvl_config`;
                 `(p:(num#num#bvl_exp)list,names:mlstring spt)`;
                 `syntax:num->(num#num)#dec list`] cake_orac_clos_syntax_oracle_ok) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `backend_config_ok (asm_conf:(A)asm_config) c` THEN
   REWRITE_TAC[backend_config_ok_def] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[FST]; ASM_ARITH_TAC];
   DISCH_TAC] THEN
  MATCH_MP_TAC (ISPEC `(<):num->num->bool` oracle_monotonic_rel_mono) THEN
  CONJ_TAC THENL [REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`backend_config_clos_conf c`; `clos_c':clos_to_bvl_config`;
                 `SND (to_clos c prog)`;
                 `cake_orac (asm_conf:(A)asm_config) c' syntax (SND o config_tuple1)
                    (\ps. backend_progs_clos_prog ps)`;
                 `(p:(num#num#bvl_exp)list,names:mlstring spt)`]
          syntax_oracle_ok_bvl_FST_monotonic) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[clos_to_bvl_orac_eq] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prog:dec list`; `b:byte list`; `bm:(A word)list`; `c:backend_config`;
                 `backend_config_clos_conf c`; `asm_conf:(A)asm_config`; `c':backend_config`;
                 `syntax:num->(num#num)#dec list`] clos_to_bvl_orac_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MATCH_MP_TAC BKP2AUX_oracle_monotonic_init_subset THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th)))) THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  REWRITE_TAC[cake_orac_0; o_THM; config_tuple1_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  REWRITE_TAC[BKP2AUX_to_bvl_prog] THEN ASM_REWRITE_TAC[] THEN
  BKP2AUX_HDTM_X_ASSUM "clos_to_bvl_compile" MP_TAC THEN
  REWRITE_TAC[clos_to_bvl_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_common_max_app) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_common_MAP_FST_compile_prog) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[set_MAP_code_sort] THEN SIMP[] THEN
  REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; UNION_SUBSET] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_SET_OF_LIST; toAList_domain; IN_COUNT] THEN
   MESON_TAC[domain_init_code_lt_num_stubs; ARITH_RULE `x < n ==> x < m + n:num`];
   REWRITE_TAC[num_stubs_def] THEN ARITH_TAC;
   REWRITE_TAC[num_stubs_def] THEN ARITH_TAC]);;

let BKP2AUX_ile_0 = prove
 (`good_dimindex (:A) ==> word_ile (word_neg (word 8)) (word 0:A word) /\ word_ile (word 0:A word) (word 8)`,
  REWRITE_TAC[good_dimindex_def] THEN MESON_TAC[bounds_lem]);;

(* the data_to_word configuration of a backend_config_ok configuration    *)
(* already has the floating-point flags of the target                      *)
let BKP2AUX_ensure_fp_id = prove
 (`!(asm_conf:(A)asm_config) c.
     backend_config_ok asm_conf c
     ==> ensure_fp_conf_ok asm_conf (backend_config_data_conf c) = backend_config_data_conf c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backend_config_ok_def] THEN STRIP_TAC THEN
  REWRITE_TAC[ensure_fp_conf_ok_def; (record_info "data_to_word_config").ri_component_equality;
              (record_info "data_to_word_config").ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* the equation of the wordLang oracle, derived from data_to_word_orac_eq as *)
(* data_to_word_orac_eq_sym_std (HOL4 line 2673) is, needed before it here    *)
let BKP2AUX_d2w_orac_eq_sym =
  GEN_ALL (DISCH_ALL (GSYM (UNDISCH_ALL (SPEC_ALL
    (let th = SPEC_ALL data_to_word_orac_eq in
     let f4 = find (fun v -> fst (dest_var v) = "f4") (frees (concl th)) in
     GEN_ALL (ISPEC `SND o SND o SND o SND o SND o config_tuple2` (GEN f4 th)))))));;

(* labels of the wordLang programs through word_to_word *)
let BKP2AUX_labels_transfer = prove
 (`!(p:(num#num#(A)wl_prog)list) (ps:(num#num#(A)wl_prog)list).
     MAP FST ps = MAP FST p /\
     ALL2 labels_rel (MAP (wordConvs_extract_labels o SND o SND) p)
                     (MAP (wordConvs_extract_labels o SND o SND) ps) /\
     ALL (\(l,m,e). ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (wordConvs_extract_labels e) /\
                    ALL_DISTINCT (wordConvs_extract_labels e)) p
     ==> ALL (\(l,m,e). ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (wordConvs_extract_labels e) /\
                        ALL_DISTINCT (wordConvs_extract_labels e)) ps`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ps:(num#num#(A)wl_prog)list` THEN
  STRUCT_CASES_TAC (ISPEC `ps:(num#num#(A)wl_prog)list` list_CASES) THEN
  REWRITE_TAC[MAP; ALL2; ALL; NOT_CONS_NIL; CONS_11] THEN
  SPEC_TAC(`h':num#num#(A)wl_prog`,`q:num#num#(A)wl_prog`) THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`r:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[o_THM; FST; SND; labels_rel_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
  [UNDISCH_TAC `set_of_list (wordConvs_extract_labels (p2':(A)wl_prog)) SUBSET
                set_of_list (wordConvs_extract_labels (p2:(A)wl_prog))` THEN
   UNDISCH_TAC `ALL (\(l1,l2). l1 = p1 /\ ~(l2 = 0) /\ ~(l2 = 1))
                  (wordConvs_extract_labels (p2:(A)wl_prog))` THEN
   ASM_REWRITE_TAC[GSYM ALL_MEM; SUBSET; IN_SET_OF_LIST] THEN MESON_TAC[];
   ASM_MESON_TAC[];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* properties of the programs of the wordLang oracle used for the code of *)
(* the stackLang and labLang oracles *)
let BKP2AUX_word_oracle_full = prove
 (`!asm_conf c prog b bm c' syn n.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
  backend_config_ok asm_conf c /\ good_dimindex (:A)
  ==> ALL (\(l,m,p). full_inst_ok_less asm_conf p /\
                     (asm_config_two_reg_arith asm_conf ==> every_inst two_reg_inst p) /\
                     (no_share_inst p \/ ~(asm_config_ISA asm_conf = Ag32)) /\
                     post_alloc_conventions
                       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) p)
        (SND (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps) n)) /\
      ALL (\(l,m,p). good_handlers l p)
        (SND (cake_orac asm_conf c' syn
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps) n)) /\
      ALL (\(l,m,e). ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (wordConvs_extract_labels e) /\
                     ALL_DISTINCT (wordConvs_extract_labels e))
        (SND (cake_orac asm_conf c' syn
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps) n)) /\
      MAP FST (SND (cake_orac asm_conf c' syn
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps) n)) =
      MAP FST (SND (cake_orac asm_conf c' syn
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_bvi_prog ps) n))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:dec list`; `b:byte list`; `bm:(A word)list`; `c:backend_config`;
                  `asm_config_two_reg_arith (asm_conf:(A)asm_config)`;
                  `asm_config_reg_count (asm_conf:(A)asm_config) -
                     (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
                  `word_to_word_config_reg_alg (backend_config_word_to_word_conf c)`;
                  `ensure_fp_conf_ok (asm_conf:(A)asm_config) (backend_config_data_conf c)`;
                  `asm_conf:(A)asm_config`; `c':backend_config`; `syn:num->(num#num)#dec list`]
           BKP2AUX_d2w_orac_eq_sym) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_THM; SND_pure_co; GSYM bvi_to_data_orac_eq] THEN
  SPEC_TAC(`SND (cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
              (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_bvi_prog ps) n)`,
           `z:(num#num#bvi_exp)list`) THEN
  GEN_TAC THEN
  ABBREV_TAC `(pp0:(num#num#(A)wl_prog)list) = MAP (data_to_word_compile_part
                   (ensure_fp_conf_ok (asm_conf:(A)asm_config) (backend_config_data_conf c)))
                   (bvi_to_data_compile_prog z)` THEN
  ABBREV_TAC `pp = MAP (\p. full_compile_single (asm_config_two_reg_arith (asm_conf:(A)asm_config))
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
       (word_to_word_config_reg_alg (backend_config_word_to_word_conf c)) asm_conf (p,NONE))
       (pp0:(num#num#(A)wl_prog)list)`) THEN
  (MP_TAC(ISPECL [`pp:(num#num#(A)wl_prog)list`; `asm_conf:(A)asm_config`;
                 `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
                 `word_to_word_config_reg_alg (backend_config_word_to_word_conf c)`;
                 `pp0:(num#num#(A)wl_prog)list`] MAP_full_compile_single_to_compile) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  BKP2AUX_HDTM_ASSUM "word_to_word_compile" (fun th ->
    let l,r = dest_eq(concl th) in
    let args = snd(strip_comb l) in
    let ign,pp = dest_pair r in
    MP_TAC (ISPECL [el 0 args; el 1 args; el 2 args; ign; pp] compile_to_word_conventions2)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pp0" THEN REWRITE_TAC[ALL_MAP] THEN
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; data_to_word_compile_part_def] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[comp_no_share_inst; PAIR];
   STRIP_TAC] THEN
  SUBGOAL_THEN `MAP FST (pp:(num#num#(A)wl_prog)list) = MAP FST (z:(num#num#bvi_exp)list)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pp0" THEN
   REWRITE_TAC[MAP_FST_MAP_compile_part; bvi_to_dataProof_MAP_FST_compile_prog];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[]) THEN
  (BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th ->
    STRIP_ASSUME_TAC (REWRITE_RULE[backend_config_ok_def] th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP BKP2AUX_ensure_fp_id th])) THEN
  SUBGOAL_THEN `asm_offset_ok 0 (asm_config_byte_offset (asm_conf:(A)asm_config)) (word 0)` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
     BKP2AUX_mentions "asm_config_byte_offset" (concl th))) THEN
   ASM_SIMP_TAC[BKP2AUX_ile_0];
   ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\(n,m,prog). every_inst (inst_ok_less (asm_conf:(A)asm_config)) prog)
                  (pp0:(num#num#(A)wl_prog)list)` ASSUME_TAC THENL
  [EXPAND_TAC "pp0" THEN
   REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; data_to_word_compile_part_def] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC comp_no_inst THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
   REWRITE_TAC[CONJ_ACI] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_mentions "flat_exp_conventions" (concl th))) THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[ARITH_RULE `a - (5 + b) = a - (b + 5)`] THEN MESON_TAC[];
   EXPAND_TAC "pp" THEN MATCH_MP_TAC word_good_handlers_word_to_word_incr THEN
   EXPAND_TAC "pp0" THEN REWRITE_TAC[data_to_word_good_handlers_incr];
   MATCH_MP_TAC BKP2AUX_labels_transfer THEN EXISTS_TAC `pp0:(num#num#(A)wl_prog)list` THEN
   ASM_REWRITE_TAC[] THEN EXPAND_TAC "pp0" THEN REWRITE_TAC[D2WPAUX_parts_labels];
   EXPAND_TAC "pp0" THEN
   REWRITE_TAC[MAP_FST_MAP_compile_part; bvi_to_dataProof_MAP_FST_compile_prog]]));;

(* properties of the programs of the stackLang oracle *)
let BKP2AUX_stack_oracle_full = prove
 (`!asm_conf c prog b bm c' syn n.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
  backend_config_ok asm_conf c /\ good_dimindex (:A)
  ==> ALL (\(x,y). stack_asm_name asm_conf y /\ stack_asm_remove asm_conf y /\ alloc_arg y /\
                   reg_bound y (asm_config_reg_count asm_conf -
                                  (LENGTH (asm_config_avoid_regs asm_conf) + 5) + 2) /\
                   call_args y 1 2 3 4 0)
        (FST (SND (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
                     (SND o SND o SND o SND o SND o SND o config_tuple2)
                     (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) n))) /\
      stack_good_handler_labels
        (FST (SND (cake_orac asm_conf c' syn
                     (SND o SND o SND o SND o SND o SND o config_tuple2)
                     (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) n))) /\
      ALL (\(l,e). ALL (\(l1,l2). l1 = l /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels e) /\
                   ALL_DISTINCT (stack_extract_labels e))
        (FST (SND (cake_orac asm_conf c' syn
                     (SND o SND o SND o SND o SND o SND o config_tuple2)
                     (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) n))) /\
      MAP FST (FST (SND (cake_orac asm_conf c' syn
                     (SND o SND o SND o SND o SND o SND o config_tuple2)
                     (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) n))) =
      MAP FST (SND (cake_orac asm_conf c' syn
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_bvi_prog ps) n))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[backend_config_ok_def] th]);
   ALL_TAC] THEN
  MP_TAC(MATCH_MP word_to_stack_orac_eq
     (CONJ (ASSUME `backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')`)
           (ASSUME `stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F`))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[o_THM] THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`; `n:num`]
         BKP2AUX_word_oracle_full) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
              (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps) n`,
           `w:(num#lab_to_target_config)#(num#num#(A)wl_prog)list`) THEN
  X_GEN_TAC `w:(num#lab_to_target_config)#(num#num#(A)wl_prog)list` THEN
  SUBGOAL_THEN `?bm0 cfg prg. w = ((bm0:num,cfg:lab_to_target_config),prg:(num#num#(A)wl_prog)list)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[SND] THEN
  SUBGOAL_THEN `?q fs bs. compile_word_to_stack (asm_conf:(A)asm_config) F
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) prg (Nil,bm0) =
       (q:(num#(A)stack_prog)list,fs:num list,bs:(A word)app_list#num)` STRIP_ASSUME_TAC THENL
  [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  STRIP_TAC) THEN
  (BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC compile_word_to_stack_convs THEN
   MAP_EVERY EXISTS_TAC [`prg:(num#num#(A)wl_prog)list`; `(Nil:(A word)app_list,bm0:num)`;
                         `(fs:num list,bs:(A word)app_list#num)`] THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
                asm_config_reg_count asm_conf` THEN ARITH_TAC;
   MP_TAC(ISPECL [`prg:(num#num#(A)wl_prog)list`; `asm_conf:(A)asm_config`;
     `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
     `(Nil:(A word)app_list,bm0:num)`; `q:(num#(A)stack_prog)list`; `fs:num list`;
     `bs:(A word)app_list#num`] word_to_stack_good_handler_labels_incr) THEN
   ASM_REWRITE_TAC[];
   MP_TAC(ISPECL [`prg:(num#num#(A)wl_prog)list`; `F`; `(Nil:(A word)app_list,bm0:num)`;
     `q:(num#(A)stack_prog)list`; `(fs:num list,bs:(A word)app_list#num)`; `asm_conf:(A)asm_config`;
     `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`]
     compile_word_to_stack_lab_pres) THEN
   ASM_REWRITE_TAC[];
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MAP_FST_compile_word_to_stack th]) THEN
   ASM_REWRITE_TAC[]]));;

(* the program part of an oracle does not depend on its configuration part *)
let BKP2AUX_SND_cake_orac_f = prove
 (`!asm_conf c syntax (f:backend_config->B) (f':backend_config->E) (g:(A)backend_progs->D) n.
     SND (cake_orac (asm_conf:(A)asm_config) c syntax f g n) =
     SND (cake_orac asm_conf c syntax f' g n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cake_orac_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BKP2AUX_GEN_CONST_TAC "compile_inc_progs" 4 THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]);;

(* the labLang code made from stackLang programs with stack_asm_name and   *)
(* stack_asm_remove satisfies sec_ok_pre *)
let BKP2AUX_lab_code_asm_ok = prove
 (`!(asm_conf:(A)asm_config) c (q:(num#(A)stack_prog)list).
     backend_config_ok asm_conf c /\ good_dimindex (:A) /\
     ALL (\(x,y). stack_asm_name asm_conf y /\ stack_asm_remove asm_conf y) q
     ==> ALL (sec_ok_pre asm_conf)
           (compile_no_stubs (stack_to_lab_config_reg_names (backend_config_stack_conf c))
              (stack_to_lab_config_jump (backend_config_stack_conf c))
              (asm_config_addr_offset asm_conf)
              (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3)) q)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  REWRITE_TAC[compile_no_stubs_def] THEN MATCH_MP_TAC compile_all_enc_ok_pre THEN CONJ_TAC THENL
  [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
     BKP2AUX_mentions "asm_config_byte_offset" (concl th))) THEN
   ASM_SIMP_TAC[BKP2AUX_ile_0];
   ALL_TAC] THEN
  MATCH_MP_TAC stack_names_stack_asm_ok THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL_MAP] THEN
  UNDISCH_TAC `ALL (\(x,y). stack_asm_name (asm_conf:(A)asm_config) y /\ stack_asm_remove asm_conf y)
                 (q:(num#(A)stack_prog)list)` THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM; stack_alloc_prog_comp_def;
                                         stack_remove_prog_comp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `p:(A)stack_prog`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stack_asm_name (asm_conf:(A)asm_config)
                  (FST (stack_alloc_comp n (next_lab (p:(A)stack_prog) 2) p)) /\
                stack_asm_remove asm_conf (FST (stack_alloc_comp n (next_lab p 2) p))`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`n:num`; `next_lab (p:(A)stack_prog) 2`; `p:(A)stack_prog`; `asm_conf:(A)asm_config`]
     stack_alloc_comp_stack_asm_name) THEN
   ASM_REWRITE_TAC[] THEN
   SPEC_TAC(`stack_alloc_comp n (next_lab (p:(A)stack_prog) 2) p`, `r:(A)stack_prog#num`) THEN
   REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[FST];
   ALL_TAC] THEN
  MATCH_MP_TAC stack_remove_comp_stack_asm_name THEN ASM_REWRITE_TAC[reg_name_def] THEN
  UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
               asm_config_reg_count asm_conf` THEN ARITH_TAC));;
let BKP2AUX_FST_cake_orac = prove
 (`!asm_conf c syntax (f:backend_config->B) (g:(A)backend_progs->D) n.
     FST (cake_orac (asm_conf:(A)asm_config) c syntax f g n) = f (cake_configs asm_conf c syntax n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cake_orac_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BKP2AUX_GEN_CONST_TAC "compile_inc_progs" 4 THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2330 *)
let good_code_lab_oracle = prove
 (`!asm_conf c prog b bm c' syntax i cfg code mc.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   cake_orac asm_conf c' syntax (SND o SND o SND o SND o SND o SND o config_tuple2)
     (\ps. backend_progs_lab_prog ps) i = (cfg,code) /\
   backend_config_ok asm_conf c /\
   asm_conf = target_config (machine_config_target (mc:(A,B,C)machine_config)) /\
   mc_conf_ok mc
   ==> lab_to_targetProof_good_code asm_conf (lab_to_target_config_labels cfg) code`,
    (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex (:A)` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "mc_conf_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[mc_conf_ok_def] th]); ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
                                     lhs (concl th) = `asm_conf:(A)asm_config`)) THEN
  SUBGOAL_THEN `labels_ok (code:((A)sec)list)` ASSUME_TAC THENL
  [MATCH_MP_TAC lab_labels_ok_oracle THEN
   MAP_EVERY EXISTS_TAC [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`;
     `b:byte list`; `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`;
     `i:num`; `cfg:lab_to_target_config`] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  BKP2AUX_HDTM_X_ASSUM "cake_orac" (fun th ->
    MP_TAC (AP_TERM `FST:lab_to_target_config#((A)sec)list->lab_to_target_config` th) THEN
    MP_TAC (AP_TERM `SND:lab_to_target_config#((A)sec)list->((A)sec)list` th)) THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[BKP2AUX_FST_cake_orac; o_THM; config_tuple2_def; SND]) THEN
  (SUBGOAL_THEN `oracle_monotonic (set_of_list o MAP Section_num o SND) (\x y. ~(x = y))
     (domain (lab_to_target_config_labels (backend_config_lab_conf c')))
     (cake_orac (asm_conf:(A)asm_config) c' (syntax:num->(num#num)#dec list)
        (SND o SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_lab_prog ps))`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
     `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`]
     monotonic_labels_stack_to_lab) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
     `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`]
     monotonic_labels_bvi_down_to_stack) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
     `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`]
     monotonic_labels_bvl_to_bvi) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
     `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`]
     monotonic_labels_bvl) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
     `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`; `i:num`]
     monotonic_DISJOINT_labels_lab) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP labels_ok_imp) THEN
  REWRITE_TAC[lab_to_targetProof_good_code_def] THEN ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[backend_config_ok_def] th]);
   ALL_TAC] THEN
  MP_TAC(ISPECL [`prog:dec list`; `b:byte list`; `bm:(A word)list`; `c:backend_config`;
                 `stack_to_lab_config_reg_names (backend_config_stack_conf c)`;
                 `stack_to_lab_config_jump (backend_config_stack_conf c)`;
                 `asm_config_addr_offset (asm_conf:(A)asm_config)`;
                 `asm_config_reg_count (asm_conf:(A)asm_config) -
                    (LENGTH (asm_config_avoid_regs asm_conf) + 3)`;
                 `asm_conf:(A)asm_config`; `c':backend_config`; `syntax:num->(num#num)#dec list`;
                 `SND o SND o SND o SND o SND o SND o config_tuple2`] stack_to_lab_orac_eq_std_sym) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; o_THM; SND_pure_co]) THEN
                       REWRITE_TAC[th; o_THM; SND_pure_co]) THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`; `i:num`]
         BKP2AUX_stack_oracle_full) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[compile_no_stubs_def; EVERY_sec_ends_with_label_MAP_prog_to_section];
   MATCH_MP_TAC(SET_RULE `(a:num#num->bool) SUBSET b ==> a SUBSET b UNION c`) THEN
   MATCH_MP_TAC stack_to_lab_stack_good_handler_labels_incr THEN
   MAP_EVERY EXISTS_TAC [`stack_to_lab_config_reg_names (backend_config_stack_conf c)`;
     `stack_to_lab_config_jump (backend_config_stack_conf c)`;
     `asm_config_addr_offset (asm_conf:(A)asm_config)`;
     `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3)`;
     `FST (SND (cake_orac (asm_conf:(A)asm_config) c' (syntax:num->(num#num)#dec list)
              (SND o SND o SND o SND o SND o SND o config_tuple2)
              (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) i))`] THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC BKP2AUX_lab_code_asm_ok THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_mentions "stack_asm_name" (concl th))) THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[]]));;

(* HOL4 line 2486 *)
let oracle_stack_good_code = prove
 (`!asm_conf c prog b bm c' reg_count_sub mc syntax f n.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
   reg_count_sub = asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3) /\
   backend_config_ok asm_conf c /\ mc_conf_ok (mc:(A,B,C)machine_config) /\
   asm_conf = target_config (machine_config_target mc)
   ==> stack_to_labProof_good_code reg_count_sub
         (FST (SND (cake_orac asm_conf c' syntax (f:backend_config->D)
                      (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) n)))`,
    (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
                                     lhs (concl th) = `asm_conf:(A)asm_config`)) THEN
  ONCE_REWRITE_TAC[ISPECL [`asm_conf:(A)asm_config`; `c':backend_config`;
    `syntax:num->(num#num)#dec list`; `f:backend_config->D`;
    `SND o SND o SND o SND o SND o SND o config_tuple2`;
    `\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm (ps:(A)backend_progs))`;
    `n:num`] BKP2AUX_SND_cake_orac_f] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)) &&
                                              fst(dest_var(lhs(concl th))) = "reg_count_sub")) THEN
  SUBGOAL_THEN `good_dimindex (:A)` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "mc_conf_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[mc_conf_ok_def] th]); ALL_TAC] THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`; `n:num`]
         BKP2AUX_stack_oracle_full) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`; `n:num`]
         cake_orac_stack_ALL_DISTINCT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                `bm:(A word)list`; `c':backend_config`; `syntax:num->(num#num)#dec list`;
                `SND o SND o SND o SND o SND o config_tuple2`; `n:num`]
         bvl_num_stubs_LE_bvi_prog) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`SND (cake_orac (asm_conf:(A)asm_config) c' (syntax:num->(num#num)#dec list)
              (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_bvi_prog ps) n)`,
           `z:(num#num#bvi_exp)list`) THEN
  SPEC_TAC(`FST (SND (cake_orac (asm_conf:(A)asm_config) c' (syntax:num->(num#num)#dec list)
              (SND o SND o SND o SND o SND o SND o config_tuple2)
              (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps)) n))`,
           `q:(num#(A)stack_prog)list`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[stack_to_labProof_good_code_def] THEN ASM_REWRITE_TAC[]) THEN
  (BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  SUBGOAL_THEN `ALL (\x. stack_num_stubs <= x) (MAP FST (q:(num#(A)stack_prog)list))` MP_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `ALL (\x. bvl_num_stubs <= x) (MAP FST (z:(num#num#bvi_exp)list))` THEN
   MATCH_MP_TAC MONO_ALL THEN
   REWRITE_TAC[bvl_num_stubs_def; stack_num_stubs_def; word_num_stubs_def; data_num_stubs_def] THEN
   ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `asm_config_reg_count (asm_conf:(A)asm_config) -
                  (LENGTH (asm_config_avoid_regs asm_conf) + 5) + 2 =
                asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3)`
    MP_TAC THENL
  [UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
                asm_config_reg_count asm_conf` THEN ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_mentions "stack_asm_name" (concl th))) THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; MEM_MAP; FORALL_PAIR_THM; o_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN MESON_TAC[FST]));;

(* HOL4 line 2626 (all_enc_ok_pre conf code, an Overload, is               *)
(* ALL (sec_ok_pre conf) code)                                               *)
let to_lab_good_code_lemma = prove
 (`!c lim1 lim2 offs stack_prog code asm_conf3 word_prog bm wc fs data_conf word_conf asm_conf2 data_prog col conf.
     stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c) lim1 lim2
     offs stack_prog = code /\
   word_to_stack_compile asm_conf3 F word_prog = (bm,wc,fs,stack_prog) /\
   data_to_word_compile data_conf word_conf (asm_conf2:(A)asm_config) data_prog =
     (col,word_prog) /\
   labels_ok code /\
   ALL (sec_ok_pre conf) code
   ==> lab_to_targetProof_good_code conf LN code`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[lab_to_targetProof_good_code_def] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL (sec_labels_ok:(A)sec->bool) code /\ ALL_DISTINCT (MAP Section_num (code:((A)sec)list)) /\
                ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) (code:((A)sec)list)`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `labels_ok (code:((A)sec)list)` THEN REWRITE_TAC[labels_ok_def] THEN
   SUBGOAL_THEN (CASE_TERM `(\s. match s with Section n _ -> n) = (Section_num:(A)sec->num)`) SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CASES_ON `x:(A)sec` THEN CASE_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN MATCH_MP_TAC MONO_ALL THEN
   GEN_TAC THEN CASES_ON `x:(A)sec` THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SIMP[EVERY_sec_label_ok; o_THM];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[labs_domain_LN; UNION_EMPTY; domain_def; DISJOINT_EMPTY] THEN
  CONJ_TAC THENL
  [BKP2AUX_HDTM_ASSUM "stack_to_lab_compile" (SUBST1_TAC o SYM) THEN
   REWRITE_TAC[stack_to_lab_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[EVERY_sec_ends_with_label_MAP_prog_to_section];
   MATCH_MP_TAC stack_to_lab_stack_good_handler_labels THEN
   ASM_MESON_TAC[word_to_stack_good_handler_labels; data_to_word_good_handlers]]);;

(* HOL4 line 2670: data_to_word_orac_eq |> SPEC_ALL |> Q.GEN `f4` |>       *)
(* Q.ISPEC (SND o SND o SND o SND o SND o config_tuple2) |> GEN_ALL (derived *)
(* here in the same way)                                                     *)
let data_to_word_orac_eq_std =
  let th = SPEC_ALL data_to_word_orac_eq in
  let f4 = find (fun v -> fst (dest_var v) = "f4") (frees (concl th)) in
  GEN_ALL (ISPEC `SND o SND o SND o SND o SND o config_tuple2` (GEN f4 th));;

(* HOL4 line 2673: data_to_word_orac_eq_std |> SIMP_RULE bool_ss [] |>      *)
(* SPEC_ALL |> UNDISCH_ALL |> GSYM |> DISCH_ALL |> GEN_ALL (derived here in  *)
(* the same way; the SIMP_RULE bool_ss [] is left out: in HOL4 it            *)
(* eliminates the variables fixed by equations among the hypotheses, which  *)
(* stay hypotheses here, an equivalent statement)                            *)
let data_to_word_orac_eq_sym_std =
  GEN_ALL (DISCH_ALL (GSYM (UNDISCH_ALL (SPEC_ALL data_to_word_orac_eq_std))));;

(* HOL4 line 2681 *)
let compute_stack_frame_sizes_def = cake_def
  `compute_stack_frame_sizes (c:(A)asm_config) (word_prog:(num#num#(A)wl_prog)list) =
     let reg_count = (asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)) - 5 in
     mapi (\n (arg_count,prog).
             let stack_arg_count = arg_count - reg_count in
             let stack_var_count =
               MAX (((max_var prog DIV 2) + 1) - reg_count) stack_arg_count in
             if stack_var_count = 0 then 0 else stack_var_count + 1)
          (fromAList word_prog)`;;

(* HOL4 line 2691 *)
let compute_stack_frame_sizes_thm = prove
 (`!c word_prog.
     compute_stack_frame_sizes (c:(A)asm_config) word_prog =
   let k = (asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)) - 5 in
   mapi (\n (arg_count,prog).
           FST (SND (word_to_stack_compile_prog c F prog arg_count k (Nil,0))))
        (fromAList word_prog)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compute_stack_frame_sizes_def; word_to_stack_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN PAIRARG_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2709 (the argument is the universe (:A), as for              *)
(* max_heap_limit)                                                           *)
let is_64_bits_def = cake_def
  `is_64_bits (s:A->bool) <=> dimindex (:A) = 64`;;

(* HOL4 line 2713 *)
let backendProof_is_safe_for_space_def = cake_def
  `backendProof_is_safe_for_space (ffi:(FFI)ffi_state) (asm_conf:(A)asm_config)
                                  (c:backend_config) prog stack_heap_limit <=>
     let data_prog = FST (SND (to_data c prog)) in
     let word_prog = FST (SND (to_word asm_conf c prog)) in
     data_lang_safe_for_space ffi (fromAList data_prog)
       (compute_limits (data_to_word_config_len_size (backend_config_data_conf c))
          (is_64_bits (:A)) (data_to_word_config_has_fp_ops (backend_config_data_conf c))
          (data_to_word_config_has_fp_tern (backend_config_data_conf c)) stack_heap_limit)
       (compute_stack_frame_sizes asm_conf word_prog) InitGlobals_location /\
     ~(data_to_word_config_gc_kind (backend_config_data_conf c) = data_to_word_None)`;;

(* HOL4 line 2723 *)
let compile_word_conf_eq = prove
 (`!c prog code data conf w_conf stack_prog stack_names asm_conf bm.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (code,data,conf) /\
     to_stack asm_conf c prog = (bm,w_conf,stack_prog,stack_names)
     ==> word_to_stack_config_stack_frame_size (backend_config_word_conf conf) =
         word_to_stack_config_stack_frame_size (backend_config_word_conf w_conf)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `backend_compile (asm_conf:(A)asm_config) c prog = SOME (code,data,conf)` THEN
  REWRITE_TAC[compile_eq_to_target; to_target_def; to_lab_def] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ]) THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 2752 *)
let to_word_lab_conf = prove
 (`!c c' prog p n asm_conf.
     to_word (asm_conf:(A)asm_config) c prog = (c',p,n)
     ==> backend_config_lab_conf c = backend_config_lab_conf c'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[to_word_def; to_data_def; to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
  BACKDEFAUX_LETS_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

(* HOL4 line 2773 *)
let PERM_toAList_fromAList = prove
 (`!p:(num#A)list. ALL_DISTINCT (MAP FST p) ==> PERM (toAList (fromAList p)) p`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PERM_ALL_DISTINCT THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC (ISPEC `FST:num#A->num` ALL_DISTINCT_MAP) THEN
   REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList];
   ASM_MESON_TAC[ALL_DISTINCT_MAP];
   REWRITE_TAC[FORALL_PAIR_THM; MEM_toAList; lookup_fromAList] THEN
   ASM_MESON_TAC[MEM_ALOOKUP]]);;

(* the frame size computed by compile_prog does not depend on the bitmaps *)
let BKP2AUX_compile_prog_frame = prove
 (`!(ac:(A)asm_config) perf p n k bm q f bm' bm2.
     word_to_stack_compile_prog ac perf p n k bm = (q,f,bm')
     ==> FST (SND (word_to_stack_compile_prog ac perf p n k bm2)) = f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_to_stack_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 2788 (the ZIP zips lists of equal lengths) *)
let compile_word_to_stack_sfs_aux = prove
 (`!ac perf k p bm progs' fs' bitmaps.
     compile_word_to_stack (ac:(A)asm_config) perf k p bm = (progs',fs',bitmaps) /\
     perf = F
     ==> fromAList
           (MAP (\kv. (FST kv,
                       (\(arg_count,prog).
                          FST (SND (word_to_stack_compile_prog ac perf prog arg_count k
                                      (Nil,0)))) (SND kv))) p) =
         fromAList (MAP (\((i,x),n). (i,n)) (ZIP progs' fs'))`,
  MATCH_MP_TAC compile_word_to_stack_ind THEN CONJ_TAC THENL
  [REWRITE_TAC[compile_word_to_stack_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
   RVEQ_TAC THEN REWRITE_TAC[MAP; ZIP; fromAList_def];
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[compile_word_to_stack_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REPEAT BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
   RVEQ_TAC THEN REWRITE_TAC[MAP; ZIP; fromAList_def] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
   BINOP_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP BKP2AUX_compile_prog_frame);
    FIRST_X_ASSUM DRULE THEN DISCH_THEN DRULE THEN ASM_REWRITE_TAC[]]]);;

(* fromAList of a MAP over toAList (fromAList p), for a key-preserving map *)
let BKP2AUX_fromAList_MAP_toAList = prove
 (`!(f:num#A->num#B) p.
     ALL_DISTINCT (MAP FST p) /\ (!x. FST (f x) = FST x)
     ==> fromAList (MAP f (toAList (fromAList p))) = fromAList (MAP f p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] PERM_IMP_fromAList_EQ_fromAList) THEN CONJ_TAC THENL
  [MATCH_MP_TAC PERM_MAP THEN MATCH_MP_TAC PERM_toAList_fromAList THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `(FST:num#B->num) o (f:num#A->num#B) = FST` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
   REWRITE_TAC[GSYM MAP_o] THEN ASM_REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]]);;

(* HOL4 line 2813 *)
let IMP_is_safe_for_space = prove
 (`!asm_conf c prog code data conf bvi_conf data_prog names ffi stack_heap_limit.
     backend_config_ok (asm_conf:(A)asm_config) c
   ==> backend_compile asm_conf c prog = SOME (code,data,conf)
   ==> to_data c prog = (bvi_conf,data_prog,names)
   ==> ~(data_to_word_config_gc_kind (backend_config_data_conf c) = data_to_word_None)
   ==> data_lang_safe_for_space (ffi:(FFI)ffi_state) (fromAList data_prog)
         (compute_limits (data_to_word_config_len_size (backend_config_data_conf c))
            (is_64_bits (:A)) (data_to_word_config_has_fp_ops (backend_config_data_conf c))
            (data_to_word_config_has_fp_tern (backend_config_data_conf c)) stack_heap_limit)
         (word_to_stack_config_stack_frame_size (backend_config_word_conf conf))
         InitGlobals_location
   ==> backendProof_is_safe_for_space ffi asm_conf c prog stack_heap_limit`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[backendProof_is_safe_for_space_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `compute_stack_frame_sizes asm_conf (FST (SND (to_word (asm_conf:(A)asm_config) c prog))) =
    word_to_stack_config_stack_frame_size (backend_config_word_conf conf)`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC (ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`;
                  `code:byte list`; `data:(A word)list`; `conf:backend_config`]
          to_word_labels_ok) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?x1 wp x2. to_word (asm_conf:(A)asm_config) c prog = (x1,wp,x2)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?bm wc fs sp.
      word_to_stack_compile (asm_conf:(A)asm_config)
        (stack_to_lab_config_perf_calls (backend_config_stack_conf x1)) wp =
      (bm:(A word)list,wc:word_to_stack_config,fs:num list,sp:(num#(A)stack_prog)list)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:backend_config`; `prog:dec list`; `code:byte list`; `data:(A word)list`;
                 `conf:backend_config`;
                 `backend_config_word_conf_fupd (K (wc:word_to_stack_config)) x1`;
                 `sp:(num#(A)stack_prog)list`; `x2:mlstring spt`;
                 `asm_conf:(A)asm_config`; `bm:(A word)list`] compile_word_conf_eq) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[to_stack_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SIMP[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `stack_to_lab_config_perf_calls (backend_config_stack_conf x1) = F`
   ASSUME_TAC THENL
  [(* to_word keeps perf_calls, which backend_config_ok sets to F (ASM_MESON_TAC: 42 s) *)
   FIRST_ASSUM(MP_TAC o MATCH_MP to_word_perf_calls) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   UNDISCH_TAC `backend_config_ok (asm_conf:(A)asm_config) c` THEN
   REWRITE_TAC[backend_config_ok_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  BKP2AUX_HDTM_X_ASSUM "word_to_stack_compile" MP_TAC THEN
  ASM_REWRITE_TAC[word_to_stack_compile_def] THEN
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

(* HOL4 line 2871 *)
let backendProof_read_limits_def = cake_def
  `backendProof_read_limits (asm_conf:(A)asm_config) (c:backend_config)
                            (mc:(A,B,C)machine_config) ms =
     get_stack_heap_limit ((2 * max_heap_limit (:A) (backend_config_data_conf c)) - 1)
       (target_get_reg (machine_config_target mc) ms
          (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2):A word,
        target_get_reg (machine_config_target mc) ms
          (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 3):A word,
        target_get_reg (machine_config_target mc) ms
          (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4):A word)`;;

(* HOL4 line 2880 *)
let FST_SND_EQ = prove
 (`!x y z.
     (FST x = y /\ SND x = z <=> x = (y:A,z:B)) /\
   (SND x = z /\ FST x = y <=> x = (y,z))`,
  REPEAT GEN_TAC THEN CASES_ON `x:A#B` THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 2887 *)
let PERMUTE_IMP_LINV = prove
 (`!f.
     BIJ (f:A->A) UNIV UNIV ==> !x y. y = LINV f UNIV x <=> x = f y`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [ASM_MESON_TAC[BIJ_LINV_INV; IN_UNIV];
   ASM_MESON_TAC[LINV_DEF; BIJ_DEF; IN_UNIV]]);;

(* inc_compile_prog keeps the pattern configuration *)
let BKP2AUX_inc_compile_prog_pattern_cfg = prove
 (`!env_id c p.
     source_to_flat_config_pattern_cfg (FST (inc_compile_prog env_id c p)) =
     source_to_flat_config_pattern_cfg c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BACKDEFAUX_PAIRARG_TAC THEN SIMP[]);;

(* HOL4 line 2895 *)
let state_co_inc_compile_has_flat_comp = prove
 (`!asm_conf c prog b bm c' f src g.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
   ==> state_co (\c (env_id,decs:dec list). inc_compile env_id c (f decs))
         (cake_orac asm_conf c' src config_tuple1 (g:(A)backend_progs->(num#num)#dec list)) =
       pure_co (MAP (compile_dec (source_to_flat_config_pattern_cfg
                                    (backend_config_source_conf c)))) o
       state_co (\c (env_id,decs). inc_compile_prog env_id c (f decs))
         (cake_orac asm_conf c' src config_tuple1 g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[state_co_def; cake_orac_def; LAMBDA_PAIR] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[config_tuple1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[inc_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BACKDEFAUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[pure_co_def; PAIR_MAP_THM; I_THM; PAIR_EQ] THEN
  BKP2AUX_HDTM_ASSUM "inc_compile_prog"
    (MP_TAC o AP_TERM `source_to_flat_config_pattern_cfg o
                       (FST:source_to_flat_config#(flat_exp)list->source_to_flat_config)`) THEN
  REWRITE_TAC[o_THM; BKP2AUX_inc_compile_prog_pattern_cfg] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[cake_orac_config_eqs]);;

(* HOL4 line 2910 *)
let add_eval_state_def = cake_def
  `(add_eval_state (NONE:((C)compiler_instance)option) (s0:(FFI)state) = s0) /\
   (add_eval_state (SOME ci) s0 =
      state_eval_state_fupd (K (SOME (mk_init_eval_state ci))) s0)`;;

(* HOL4 line 2916 *)
let add_eval_state_ffi = prove
 (`!opt_ev s0.
     state_ffi (add_eval_state (opt_ev:((C)compiler_instance)option) (s0:(FFI)state)) =
   state_ffi s0`,
  GEN_TAC THEN CASES_ON `opt_ev:((C)compiler_instance)option` THEN
  SIMP[add_eval_state_def]);;

(* HOL4 line 2923 *)
let opt_eval_config_wf_def = cake_def
  `(opt_eval_config_wf (asm_conf:(A)asm_config) c' (SOME ci) <=>
      compiler_instance_compiler_fun ci = compile_inc_progs_for_eval asm_conf /\
      INJ (compiler_instance_config_v ci) UNIV UNIV /\
      compiler_instance_init_state ci = c') /\
   (opt_eval_config_wf asm_conf c' NONE <=> T)`;;

(* HOL4 line 2930 *)
let backend_from_data_tuple_cc_def = cake_def
  `backend_from_data_tuple_cc (asm_conf:(A)asm_config) (c:backend_config) cfg =
     OPTION_MAP (I ## (MAP upper_w2w ## I)) o
     (\progs.
        (\(bm0,cfg) progs.
           (\(progs,fs,bm).
              OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND bm,cfg)))
                (lab_to_target_compile asm_conf cfg
                   (MAP prog_to_section
                      (MAP (stack_names_prog_comp
                              (stack_to_lab_config_reg_names (backend_config_stack_conf c)))
                         (MAP (stack_remove_prog_comp
                                 (stack_to_lab_config_jump (backend_config_stack_conf c))
                                 (asm_config_addr_offset asm_conf)
                                 (asm_config_reg_count asm_conf -
                                  (LENGTH (asm_config_avoid_regs asm_conf) + 3)))
                            (MAP stack_alloc_prog_comp progs))))))
             (compile_word_to_stack asm_conf F
                ((asm_config_reg_count asm_conf -
                  (LENGTH (asm_config_avoid_regs asm_conf) + 3)) - 2)
                progs (Nil,bm0)))
          cfg
          (MAP (\p. full_compile_single (asm_config_two_reg_arith asm_conf)
                      (asm_config_reg_count asm_conf -
                       (LENGTH (asm_config_avoid_regs asm_conf) + 5))
                      (word_to_word_config_reg_alg (backend_config_word_to_word_conf c))
                      asm_conf (p,NONE)) progs)) o
     MAP (data_to_word_compile_part
            (ensure_fp_conf_ok asm_conf (backend_config_data_conf c)))`;;

(* HOL4 line 2956 *)
let backend_from_flat_tuple_cc_def = cake_def
  `backend_from_flat_tuple_cc (asm_conf:(A)asm_config) (c:backend_config) =
     pure_cc inc_compile_decs
       (compile_common_inc (backend_config_clos_conf c)
          (pure_cc (clos_to_bvl_compile_inc'
                      (clos_to_bvl_config_max_app (backend_config_clos_conf c)))
             (full_cc (backend_config_bvl_conf c)
                (pure_cc bvi_to_data_compile_prog
                   (backend_from_data_tuple_cc asm_conf c)))))`;;

(* clos_known_compile_inc with the static configuration of c is the same   *)
(* as with c                                                                 *)
let BKP2AUX_known_compile_inc_static = prove
 (`!c g (p:clos_exp list#A).
     clos_known_compile_inc
       (clos_known_config_val_approx_spt_fupd (K LN) (reset_inline_factor c)) g p =
     clos_known_compile_inc c g p`,
  let ri = record_info "clos_known_config" in
  SUBGOAL_THEN
   `!f g c. clos_known_config_inline_factor_fupd f
              (clos_known_config_val_approx_spt_fupd g c) =
            clos_known_config_val_approx_spt_fupd g
              (clos_known_config_inline_factor_fupd f c)`
   ASSUME_TAC THENL
  [REWRITE_TAC[ri.ri_component_equality; ri.ri_accfupds]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[kcompile_inc_uncurry; reset_inline_factor_def] THEN
  REWRITE_TAC[ri.ri_fupdcanon; ri.ri_accfupds; ri.ri_fupdfupds] THEN
  ASM_REWRITE_TAC[known_reset_spt] THEN
  REWRITE_TAC[prove(`!x y:num. (K x o K y) = (K x:num->num)`,
                    REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM])]);;

(* HOL4 line 2965 *)
let known_cc_eq_state_cc_inc = prove
 (`!kc cc.
     known_cc kc (cc:B->clos_prog->(byte list#int64 list#B)option) =
   state_cc (known_compile_inc (known_static_conf kc)) cc`,
  GEN_TAC THEN CASES_ON `kc:clos_known_config option` THEN
  REWRITE_TAC[known_cc_def; known_static_conf_def] THEN CASE_REWRITE_TAC[] THEN GEN_TAC THEN
  REWRITE_TAC[pure_cc_def; state_cc_def; FUN_EQ_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[known_compile_inc_def; CURRY_DEF; I_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[BKP2AUX_known_compile_inc_static] THEN
  BACKDEFAUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2979 *)
let known_compile_inc_retreive_spt = prove
 (`!kcfg1 kcfg2 p spt p'.
     known_compile_inc (known_static_conf kcfg1) (option_val_approx_spt kcfg2) p = (spt,p') /\
   (IS_SOME kcfg2 <=> IS_SOME kcfg1)
   ==> option_val_approx_spt (option_upd_val_spt spt kcfg2) = spt`,
  REPEAT GEN_TAC THEN CASES_ON `kcfg2:clos_known_config option` THEN
  CASES_ON `kcfg1:clos_known_config option` THEN
  REWRITE_TAC[option_val_approx_spt_def; option_upd_val_spt_def; known_static_conf_def;
              known_compile_inc_def; IS_SOME_DEF] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[known_compile_inc_def; PAIR_EQ] THEN SIMP[]);;

(* HOL4 line 2992 (^cake_orac_config_inv_f c' = ^cake_orac_config_inv_f c  *)
(* is written out as the equality of the twelve components)                  *)
let backend_from_flat_tuple_cc_eq_compile_inc_progs = prove
 (CASE_TERM
  `!c' asm_conf c src_cfg env_id decs.
     (source_to_flat_config_pattern_cfg (backend_config_source_conf c'),
    clos_to_bvl_config_max_app (backend_config_clos_conf c'),
    clos_to_bvl_config_do_call (backend_config_clos_conf c'),
    IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c')),
    known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c')),
    clos_to_bvl_config_do_mti (backend_config_clos_conf c'),
    bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c'),
    bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c'),
    bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c'),
    bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c'),
    bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c'),
    backend_config_data_conf c',
    word_to_word_config_reg_alg (backend_config_word_to_word_conf c'),
    backend_config_stack_conf c',(asm_conf:(A)asm_config)) =
   (source_to_flat_config_pattern_cfg (backend_config_source_conf c),
    clos_to_bvl_config_max_app (backend_config_clos_conf c),
    clos_to_bvl_config_do_call (backend_config_clos_conf c),
    IS_SOME (clos_to_bvl_config_known_conf (backend_config_clos_conf c)),
    known_static_conf (clos_to_bvl_config_known_conf (backend_config_clos_conf c)),
    clos_to_bvl_config_do_mti (backend_config_clos_conf c),
    bvl_to_bvi_config_inline_size_limit (backend_config_bvl_conf c),
    bvl_to_bvi_config_split_main_at_seq (backend_config_bvl_conf c),
    bvl_to_bvi_config_exp_cut (backend_config_bvl_conf c),
    bvl_to_bvi_config_do_tailrec (backend_config_bvl_conf c),
    bvl_to_bvi_config_do_tmc (backend_config_bvl_conf c),
    backend_config_data_conf c,
    word_to_word_config_reg_alg (backend_config_word_to_word_conf c),
    backend_config_stack_conf c,asm_conf) /\
   src_cfg = backend_config_source_conf c' /\
   stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F /\
   source_to_flat_config_pattern_cfg (backend_config_source_conf c) =
     source_to_flat_config_pattern_cfg prim_src_config
   ==> backend_from_flat_tuple_cc asm_conf c (SND (config_tuple1 c'))
         (MAP (compile_dec (source_to_flat_config_pattern_cfg prim_src_config))
            (SND (inc_compile_prog env_id src_cfg (source_to_source_compile decs)))) =
       (let (c'',ps) = compile_inc_progs T asm_conf c' (env_id,decs) in
        OPTION_MAP (\(bs,ws). (bs,MAP upper_w2w ws,SND (config_tuple1 c'')))
          (backend_progs_target_prog ps))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[compile_inc_progs_def] THEN
  BACKDEFAUX_LETS_RW_TAC [(record_info "backend_config").ri_accfupds;
     (record_info "backend_progs").ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `MAP (compile_dec (source_to_flat_config_pattern_cfg prim_src_config))
                 (SND (inc_compile_prog env_id src_cfg (source_to_source_compile decs))) = p2`
   SUBST1_TAC THENL
  [BKP2AUX_HDTM_ASSUM "inc_compile" (MP_TAC o REWRITE_RULE[inc_compile_def]) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`env_id:num#num`; `backend_config_source_conf c'`;
                  `source_to_source_compile decs`] BKP2AUX_inc_compile_prog_pattern_cfg) THEN
   SPEC_TAC(`inc_compile_prog env_id (backend_config_source_conf c') (source_to_source_compile decs)`,
            `q:source_to_flat_config#(flat_exp)list`) THEN
   REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[backend_from_flat_tuple_cc_def; pure_cc_def; compile_common_inc_def;
              known_cc_eq_state_cc_inc; full_cc_def; config_tuple1_def; config_tuple2_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[state_cc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  SIMP[(record_info "backend_config").ri_accfupds; K_THM] THEN
  BKP2AUX_HDTM_X_ASSUM "clos_to_bvl_compile_inc" MP_TAC THEN
  REWRITE_TAC[clos_to_bvl_compile_inc_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[(record_info "clos_to_bvl_config").ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  BKP2AUX_HDTM_X_ASSUM "bvl_to_bvi_compile_inc_all" MP_TAC THEN
  REWRITE_TAC[bvl_to_bvi_compile_inc_all_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[(record_info "bvl_to_bvi_config").ri_accfupds; K_THM] THEN
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[] THEN TRY (CASE_REWRITE_TAC[]))) THEN
  REPEAT BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[(record_info "clos_to_bvl_config").ri_accfupds;
              (record_info "bvl_to_bvi_config").ri_accfupds; K_THM] THEN
  REWRITE_TAC[backend_from_data_tuple_cc_def; o_THM] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `!a b. a - (b + 3) - 2 = a - (5 + b)`;
              ARITH_RULE `!a b. a - (b + 5) = a - (5 + b)`] THEN
  BKP2AUX_HDTM_X_ASSUM "compile_word_to_stack" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[compile_no_stubs_def; stack_names_compile_def;
              ARITH_RULE `!a b. a - (3 + b) = a - (b + 3)`] THEN
  BKP2AUX_GEN_CONST_TAC "lab_to_target_compile" 3 THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[OPTION_MAP_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_MAP_THM; I_THM; injectivity "option"; PAIR_EQ; K_THM] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM] THEN
     CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN TRY (CASE_REWRITE_TAC[]))) THEN
  REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC known_compile_inc_retreive_spt THEN ASM_MESON_TAC[]);;

(* HOL4 line 3033 *)
let compile_inc_progs_src_env = prove
 (`!asm_conf c env_decs.
     backend_progs_env_id (SND (compile_inc_progs T (asm_conf:(A)asm_config) c env_decs)) =
     FST env_decs /\
   backend_progs_source_prog (SND (compile_inc_progs T asm_conf c env_decs)) = SND env_decs`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC compile_inc_progs_src_env_tup THEN
  MESON_TAC[PAIR]);;

(* HOL4 line 3040 *)
let cake_orac_cfg_f_eq_I = prove
 (`!f g asm_conf c syntax. cake_orac (asm_conf:(A)asm_config) c syntax (f:backend_config->B)
           (g:(A)backend_progs->D) =
         (f ## I) o cake_orac asm_conf c syntax I g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; cake_orac_def] THEN REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BACKDEFAUX_PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM]);;

(* HOL4 lines 3046-3048: Overload mk_flat_install_conf and an alias of     *)
(* flatProps' mk_flat_install_conf_def                                       *)

(* HOL4 line 3050 *)
let config_wf_abs_conc = prove
 (`!asm_conf c' ci dom cfg.
     opt_eval_config_wf (asm_conf:(A)asm_config) c' (SOME ci)
   ==> v_fun_abs dom (compiler_instance_config_v ci) (compiler_instance_config_v ci cfg) =
       (if cfg IN dom then SOME cfg else NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[opt_eval_config_wf_def; INJ_IFF; IN_UNIV] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[v_fun_abs_def; some_DEF; UNWIND_THM2] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

(* HOL4 line 3061 *)
let cake_orac_extended_wf = prove
 (`!asm_conf c prog b bm c' ci syntax.
     backend_compile (asm_conf:(A)asm_config) (c:backend_config) prog = SOME (b,bm,c') /\
   opt_eval_config_wf asm_conf c' (SOME ci)
   ==> orac_extended_wf (mk_compiler_fun_from_ci ci)
         ((\(cfg,id,ds). (id,compiler_instance_config_v ci cfg,ds)) o
          cake_orac asm_conf c' syntax I
            (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[cake_orac_eq_I] THEN
  REWRITE_TAC[orac_extended_wf_def; o_THM] THEN X_GEN_TAC `i:num` THEN GEN_TAC THEN
  REWRITE_TAC[cake_orac_SUC2] THEN
  SUBGOAL_THEN `?cfg ps. cake_orac (asm_conf:(A)asm_config) c' syntax I I i =
                         (cfg:backend_config, ps:(A)backend_progs)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[mk_compiler_fun_from_ci_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP config_wf_abs_conc th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_BIND_DEF; distinctness "option"] THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf"
    (STRIP_ASSUME_TAC o REWRITE_RULE[opt_eval_config_wf_def]) THEN
  ASM_REWRITE_TAC[compile_inc_progs_for_eval_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASE_REWRITE_TAC[] THEN BACKDEFAUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`backend_progs_target_prog (p2:(A)backend_progs)`,
           `t:(byte list#(A word)list)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[OPTION_MAP_DEF; OPTION_BIND_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* HOL4 line 3081 *)
let cake_orac_eq_get_oracle = prove
 (CASE_TERM
  `!s env prog asm_conf c' ci syntax s'.
     ~semantics_prog (s:(FFI)state) env prog Fail /\
   opt_eval_config_wf (asm_conf:(A)asm_config) (c':backend_config) (SOME ci) /\
   nsAll (K concrete_v) (sem_env_v env) /\ state_refs s = [] /\
   state_eval_state s = SOME (mk_init_eval_state ci) /\
   (!i r. get_oracle ci s env prog i = SOME r ==> syntax i = (I ## SND) r) /\
   s' = s
   ==> !i r x.
         get_oracle ci s' env prog i = SOME r /\
         cake_orac asm_conf c' syntax I
           (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps)) i = x
         ==> (match r with
                (id,cfg_v,ds) -> ?cfg. cfg_v = compiler_instance_config_v ci cfg /\
                                       x = (cfg,id,ds))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "syn" o check (is_forall o concl)) THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf" (LABEL_TAC "wf") THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf"
    (STRIP_ASSUME_TAC o REWRITE_RULE[opt_eval_config_wf_def]) THEN
  MP_TAC(INST [`prog:dec list`,`decs:dec list`]
          (INST_TYPE [`:backend_config`,`:C`] get_oracle_props)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g0") (LABEL_TAC "gS")) THEN
  SUBGOAL_THEN
   `!i r. get_oracle ci (s:(FFI)state) env prog i = SOME r ==>
          FST (SND r) =
          compiler_instance_config_v ci (cake_configs (asm_conf:(A)asm_config) c' syntax i)`
   (LABEL_TAC "inv") THENL
  [INDUCT_TAC THENL
   [ASM_SIMP_TAC[cake_configs_def; state_orac_states_def];
    X_GEN_TAC `r':(num#num)#v#dec list` THEN DISCH_TAC THEN
    REMOVE_THEN "gS" (MP_TAC o SPECL [`i:num`; `r':(num#num)#v#dec list`]) THEN
    ASM_REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN
    USE_THEN "syn" (fun th -> BKP2AUX_HDTM_ASSUM "get_oracle"
      (ASSUME_TAC o REWRITE_RULE[PAIR_MAP_THM; I_THM] o MATCH_MP th)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `((p1,p2),p1',p2'):(num#num)#v#dec list`) THEN
    BKP2AUX_HDTM_ASSUM "get_oracle" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[BKP1AUX_cake_configs_SUC] THEN
    BKP2AUX_HDTM_X_ASSUM "mk_compiler_fun_from_ci" MP_TAC THEN
    REWRITE_TAC[mk_compiler_fun_from_ci_def] THEN
    USE_THEN "wf" (fun th -> REWRITE_TAC[MATCH_MP config_wf_abs_conc th]) THEN
    COND_CASES_TAC THEN REWRITE_TAC[OPTION_BIND_DEF; distinctness "option"] THEN
    ASM_REWRITE_TAC[compile_inc_progs_for_eval_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CASE_REWRITE_TAC[] THEN BACKDEFAUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
    SPEC_TAC(`backend_progs_target_prog (p2''':(A)backend_progs)`,
             `t:(byte list#(A word)list)option`) THEN
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[OPTION_MAP_DEF; OPTION_BIND_DEF] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; distinctness "option"; PAIR_EQ] THEN
    MESON_TAC[]];
   ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `cake_configs (asm_conf:(A)asm_config) c' syntax i` THEN CONJ_TAC THENL
  [USE_THEN "inv" (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN REWRITE_TAC[FST; SND];
   BKP2AUX_HDTM_X_ASSUM "cake_orac" MP_TAC THEN REWRITE_TAC[cake_orac_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BACKDEFAUX_PAIRARG_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_inc_progs_src_env_tup) THEN
   ASM_REWRITE_TAC[I_THM; PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   REMOVE_THEN "syn" (MP_TAC o SPECL [`i:num`; `((p1,p2),p1',p2'):(num#num)#v#dec list`]) THEN
   ASM_REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; PAIR_EQ])) THEN
   ASM_REWRITE_TAC[]]);;

(* the source configuration after compile_inc_progs *)
let BKP2AUX_compile_inc_progs_source_conf = prove
 (`!k asm_conf c env_id decs.
     backend_config_source_conf
       (FST (compile_inc_progs k (asm_conf:(A)asm_config) c (env_id,decs))) =
     FST (inc_compile_prog env_id (backend_config_source_conf c)
            (source_to_source_compile decs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inc_progs_def] THEN
  BACKDEFAUX_LETS_RW_TAC [(record_info "backend_config").ri_accfupds; K_THM] THEN
  BKP2AUX_HDTM_X_ASSUM "inc_compile" MP_TAC THEN REWRITE_TAC[inc_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BACKDEFAUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 3127 *)
let step_invs_cake_orac = prove
 (`!st f asm_conf c' syn decf.
     eval_oracle_state_oracle st =
     (f:backend_config#(A)backend_progs->(num#num)#v#dec list) o
     cake_orac (asm_conf:(A)asm_config) c' syn I I
   ==> (!x k env_id st decs.
          x = cake_orac asm_conf c' syn I I k
          ==> f x = (env_id,st,decs)
          ==> decs = backend_progs_source_prog (SND x) /\
              env_id = backend_progs_env_id (SND x) /\
              (?d_st. (decf:v->(source_to_flat_config#C)option) st = SOME d_st /\
                      FST d_st = backend_config_source_conf (FST x)))
   ==> src_orac_step_invs (SOME decf) source_to_source_compile (SOME (EvalOracle st))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN (LABEL_TAC "h") THEN
  REWRITE_TAC[src_orac_step_invs_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN
   USE_THEN "h" (MP_TAC o SPECL [`cake_orac (asm_conf:(A)asm_config) c' syn I I k`; `k:num`;
                                 `env_id:num#num`; `state_v:v`; `decs:dec list`]) THEN
   FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "option"] THEN MESON_TAC[PAIR];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  USE_THEN "h" (MP_TAC o SPECL [`cake_orac (asm_conf:(A)asm_config) c' syn I I k`; `k:num`;
                                `env_id:num#num`; `state_v:v`; `decs:dec list`]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
  SUBGOAL_THEN `?e2 s2 d2. (f:backend_config#(A)backend_progs->(num#num)#v#dec list)
                  (cake_orac (asm_conf:(A)asm_config) c' syn I I (SUC k)) = (e2,s2,d2)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  USE_THEN "h" (MP_TAC o SPECL [`cake_orac (asm_conf:(A)asm_config) c' syn I I (SUC k)`;
                                `SUC k`; `e2:num#num`; `s2:v`; `d2:dec list`]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
  REWRITE_TAC[cake_orac_SUC2] THEN
  SUBGOAL_THEN `?cfg ps. cake_orac (asm_conf:(A)asm_config) c' syn I I k =
                         (cfg:backend_config, ps:(A)backend_progs)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[I_THM; BKP2AUX_compile_inc_progs_source_conf]);;

(* HOL4 line 3156 *)
let source_to_source_semantics_prog_equiv = prove
 (`!s0 env prog res.
     ~semantics_prog (s0:(FFI)state) env prog Fail
   ==> (semantics_prog s0 env (source_to_source_compile prog) res <=>
        semantics_prog s0 env prog res)`,
  MESON_TAC[semantics_prog_deterministic; semantics_prog_total;
            source_to_sourceProof_compile_semantics]);;

(* HOL4 line 3165 *)
let source_to_source_semantics_prog_intro = prove
 (`!s0 env prog res.
     ~semantics_prog (s0:(FFI)state) env prog Fail
   ==> (~semantics_prog s0 env (source_to_source_compile prog) Fail
        ==> semantics_prog s0 env (source_to_source_compile prog) res)
   ==> semantics_prog s0 env prog res`,
  MESON_TAC[semantics_prog_deterministic; semantics_prog_total;
            source_to_sourceProof_compile_semantics]);;

(* HOL4 line 3175 *)
let eval_oracle_semantics_prog_intro = prove
 (`!ci s1 env decs orac res. ~semantics_prog (s1:(FFI)state) env decs Fail /\
        precond_eval_state orac (ci:(C)compiler_instance) s1 env decs /\
        state_refs s1 = [] /\
        nsAll (K concrete_v) (sem_env_v env) /\
        (~semantics_prog (state_eval_state_fupd (K (put_oracle ci orac)) s1) env decs Fail
         ==> semantics_prog (state_eval_state_fupd (K (put_oracle ci orac)) s1) env decs res)
        ==> semantics_prog s1 env decs res`,
  MESON_TAC[semantics_prog_deterministic; semantics_prog_total; oracle_semantics_prog]);;

(* HOL4 line 3187 *)
let source_to_source_semantics_prog_oracle_intro = prove
 (`!ev sf orac es s0 env prog res.
     ~semantics_prog
      (state_eval_state_fupd (K (insert_gen_oracle (ev:(C)compiler_instance) I sf orac es))
         (s0:(FFI)state)) env prog Fail
   ==> (~semantics_prog
          (state_eval_state_fupd
             (K (insert_gen_oracle ev source_to_source_compile sf orac es)) s0)
          env prog Fail
        ==> semantics_prog
              (state_eval_state_fupd
                 (K (insert_gen_oracle ev source_to_source_compile sf orac es)) s0)
              env prog res)
   ==> semantics_prog
         (state_eval_state_fupd (K (insert_gen_oracle ev I sf orac es)) s0) env prog res`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!outcome.
      semantics_prog
        (state_eval_state_fupd (K (insert_gen_oracle (ev:(C)compiler_instance) I sf orac es))
           (s0:(FFI)state)) env prog outcome
      ==> semantics_prog
            (state_eval_state_fupd
               (K (insert_gen_oracle ev source_to_source_compile sf orac es)) s0)
            env prog outcome`
   ASSUME_TAC THENL
  [X_GEN_TAC `outcome:behaviour` THEN DISCH_TAC THEN
   MP_TAC(SPEC `I:dec list->dec list`
     (INST [`ev:(C)compiler_instance`,`ci:(C)compiler_instance`;
            `state_eval_state_fupd (K (insert_gen_oracle (ev:(C)compiler_instance) I sf orac es))
               (s0:(FFI)state)`,`s:(FFI)state`]
        source_to_sourceProof_compile_semantics_oracle)) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[is_insert_oracle_def] THEN SIMP[] THEN MESON_TAC[];
    SIMP[adjust_oracle_insert_gen_oracle; I_O_ID]];
   ASM_MESON_TAC[semantics_prog_deterministic; semantics_prog_total]]);;

(* source_to_flat's configuration after the primitive types program,     *)
(* computed (HOL4: prim_src_config_eq, by EVAL)                              *)
let BKP2AUX_prim_src_config_eq =
  let th1 = REWRITE_CONV[prim_src_config_def; prim_types_program_def] `prim_src_config` in
  let th2 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV
              [source_to_flat_compile_decs_def; empty_config_def; source_to_flat_empty_env_def;
               extend_env_def; alloc_tags_def; alloc_tags1_def; MAPi_def;
               injectivity "char"])) th1 in
  CONV_RULE (RAND_CONV (CAKE_SIMP_CONV
              [lookup_inc_def; lookup_insert; lookup_def; nsMap_def; nsAppend_def; nsBind_def;
               nsSing_def; nsEmpty_def; REVERSE; APPEND])) th2;;

(* evaluation of the concrete lookups of init_global_env_inv (HOL4 EVAL_TAC) *)
let BKP2AUX_EVAL_TAC thl =
  REPEAT (CHANGED_TAC
   (REWRITE_TAC ([(record_info "sem_env").ri_accessors; (record_info "global_env").ri_accessors;
                  (record_info "source_to_flat_environment").ri_accessors;
                  (record_info "source_to_flat_config").ri_accessors;
                  nsEmpty_def; ALL; nsLookup_def; ALOOKUP_def; injectivity "mlstring";
                  flookup_fupdate_list; REVERSE; APPEND; MAP; PAIR_MAP_THM; I_THM; FST; SND;
                  OPTION_MAP_DEF; FLOOKUP_EMPTY; PAIR_EQ; injectivity "option";
                  distinctness "option"] @ thl) THEN
    CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[] THEN TRY (CASE_REWRITE_TAC[])));;

(* facts about prim_src_config used by source_to_flatProof's precondition *)
let BKP2AUX_prim_src_facts = prove
 (`next_indices_vidx (source_to_flat_config_next prim_src_config) = 0 /\
   idx_prev init_genv_next (source_to_flat_config_next prim_src_config) /\
   source_to_flat_config_envs prim_src_config = source_to_flat_config_envs empty_config`,
  REWRITE_TAC[BKP2AUX_prim_src_config_eq; empty_config_def; idx_prev_def; init_genv_next] THEN
  SIMP[] THEN
  REWRITE_TAC[FLATP2AUX_init_genv_els_eval; MAP; MAX_LIST] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* the primitive environment satisfies init_global_env_inv *)
let BKP2AUX_prim_env_facts = prove
 (`!ffi s0 env. THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env) ==>
     init_global_env_inv init_genv (source_to_flat_config_mod_env prim_src_config) env`,
  REWRITE_TAC[prim_sem_env_eq; THE_DEF; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[init_global_env_inv_def; BKP2AUX_prim_src_config_eq; init_genv_def;
              FLATP2AUX_init_genv_els_eval; init_genv_ty_els_def] THEN
  BKP2AUX_EVAL_TAC [bool_id_def; list_id_def; false_tag_def; true_tag_def; nil_tag_def;
                    cons_tag_def; bool_type_num_def; list_type_num_def]);;

(* instantiate an existential over an option type with NONE *)
let BKP2AUX_EXISTS_NONE_TAC : tactic =
  W(fun (asl,w) -> let v = fst(dest_exists w) in
     EXISTS_TAC (mk_const("NONE",[hd(snd(dest_type(type_of v))),aty])));;

(* the oracle of the source programs *)
let BKP2AUX_cake_orac_src = prove
 (`!asm_conf c' syntax f i.
     cake_orac (asm_conf:(A)asm_config) c' syntax (f:backend_config->B)
       (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps)) i =
     (f (cake_configs asm_conf c' syntax i), syntax i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cake_orac_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BACKDEFAUX_PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_inc_progs_src_env_tup) THEN
  ASM_REWRITE_TAC[PAIR_EQ]);;

(* the source and flatLang compile oracles of source_eval_to_flat_semantics *)
(* are related by orac_rel                                                   *)
let BKP2AUX_orac_rel_lemma = prove
 (`!asm_conf c prog b bm c' a syn st0.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
  opt_eval_config_wf asm_conf c' (SOME a) /\
  stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F /\
  backend_config_source_conf c = prim_src_config
  ==> orac_rel (SOME (OPTION_MAP config_tuple1 o v_fun_abs UNIV (compiler_instance_config_v a)))
        source_to_source_compile
        (SOME (EvalOracle
          (eval_oracle_state_custom_do_eval_fupd
             (K (do_eval_oracle (mk_compiler_fun_from_ci a) source_to_source_compile))
             (eval_oracle_state_oracle_fupd
                (K ((\(cfg,id,ds). (id,compiler_instance_config_v a cfg,ds)) o
                    cake_orac asm_conf c' syn I
                      (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps))))
                st0))))
        (mk_flat_install_conf
           (pure_cc (MAP (compile_dec (source_to_flat_config_pattern_cfg prim_src_config)))
              (backend_from_flat_tuple_cc asm_conf c))
           (state_co (\c (env_id,decs). inc_compile_prog env_id c (source_to_source_compile decs))
              (cake_orac asm_conf c' syn config_tuple1
                 (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[orac_rel_def] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `mk_compiler_fun_from_ci (a:(backend_config)compiler_instance)` THEN
  REWRITE_TAC[(record_info "eval_oracle_state").ri_accfupds; K_THM] THEN
  REWRITE_TAC[orac_rel_inner_def; (record_info "eval_oracle_state").ri_accfupds; K_THM; o_THM;
              BKP2AUX_cake_orac_src; I_THM; LAMBDA_TRIPLE] THEN
  X_GEN_TAC `k:num` THEN REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf" (fun th -> REWRITE_TAC[MATCH_MP config_wf_abs_conc th]) THEN
  REWRITE_TAC[IN_UNIV; OPTION_MAP_DEF; THE_DEF] THEN
  REWRITE_TAC[mk_flat_install_conf_def; (record_info "install_config").ri_accessors] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[state_co_def; BKP2AUX_cake_orac_src; config_tuple1_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[LAMBDA_PAIR] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ];
   ALL_TAC] THEN
  REWRITE_TAC[pure_cc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  W(fun (asl,w) -> let t = find_term (fun t -> try let h,args = strip_comb t in
                fst(dest_const h) = "backend_from_flat_tuple_cc" && length args = 4 with Failure _ -> false) w in
     MP_TAC (PART_MATCH (lhand o rand) backend_from_flat_tuple_cc_eq_compile_inc_progs t)) THEN
  ANTS_TAC THENL
  [MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                 `bm:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`; `k:num`]
           cake_orac_config_eqs) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; config_tuple1_def];
   DISCH_THEN SUBST1_TAC] THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf"
    (STRIP_ASSUME_TAC o REWRITE_RULE[opt_eval_config_wf_def]) THEN
  REWRITE_TAC[mk_compiler_fun_from_ci_def] THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf" (fun th -> REWRITE_TAC[MATCH_MP config_wf_abs_conc th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_BIND_DEF] THEN
  ASM_REWRITE_TAC[compile_inc_progs_for_eval_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR] THEN
  BACKDEFAUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[] THEN
  BKP2AUX_GEN_CONST_TAC "backend_progs_target_prog" 1 THEN
  GEN_REWRITE_TAC I [FORALL_OPTION_THM] THEN REWRITE_TAC[OPTION_MAP_DEF; OPTION_BIND_DEF] THEN
  X_GEN_TAC `bw:byte list#(A word)list` THEN
  STRUCT_CASES_TAC (ISPEC `bw:byte list#(A word)list` PAIR_SURJECTIVE) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`x:byte list`; `MAP upper_w2w (y:(A word)list)`;
                        `SND (config_tuple1 (p1:backend_config))`; `compiler_instance_config_v (a:(backend_config)compiler_instance) p1`] THEN
  REWRITE_TAC[] THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf" (fun th -> REWRITE_TAC[MATCH_MP config_wf_abs_conc th]) THEN
  REWRITE_TAC[IN_UNIV; OPTION_MAP_DEF; injectivity "option"; config_tuple1_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* the next configuration of the source oracle of source_eval_to_flat_semantics *)
let BKP2AUX_next_cfg_lemma = prove
 (CASE_TERM `!asm_conf c prog b bm c' a syn st0 X.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
  opt_eval_config_wf asm_conf c' (SOME a) /\
  backend_config_source_conf c = prim_src_config
  ==> match src_orac_next_cfg
          (SOME (OPTION_MAP config_tuple1 o v_fun_abs UNIV (compiler_instance_config_v a)))
          (SOME (EvalOracle
            (eval_oracle_state_custom_do_eval_fupd (K X)
               (eval_oracle_state_oracle_fupd
                  (K ((\(cfg,id,ds). (id,compiler_instance_config_v a cfg,ds)) o
                      cake_orac asm_conf c' syn I
                        (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps))))
                  st0)))) with
        NONE -> T
      | SOME cfg -> cfg = FST (source_to_flat_compile_prog prim_src_config
                                 (source_to_source_compile prog))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[src_orac_next_cfg_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[(record_info "eval_oracle_state").ri_accfupds; K_THM; o_THM;
              BKP2AUX_cake_orac_src; I_THM; LAMBDA_TRIPLE] THEN
  REWRITE_TAC[src_orac_next_cfg_inner_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[cake_configs_def; state_orac_states_def; o_THM] THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf" (fun th -> REWRITE_TAC[MATCH_MP config_wf_abs_conc th]) THEN
  REWRITE_TAC[IN_UNIV; OPTION_MAP_DEF; config_tuple1_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP BKP1AUX_backend_compile_source_conf) THEN
  ASM_REWRITE_TAC[source_to_flat_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 3203 *)
let source_eval_to_flat_semantics = prove
 (`!ev s0 env prog asm_conf c b bm c' src_c' p' ffi.
     ~semantics_prog (add_eval_state ev s0) env prog Fail /\
   backend_compile (asm_conf:(A)asm_config) (c:backend_config) prog = SOME (b,bm,c') /\
   source_to_flat_compile prim_src_config (source_to_source_compile prog) = (src_c',p') /\
   THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env) /\
   opt_eval_config_wf asm_conf c' ev /\
   stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F /\
   backend_config_source_conf c = prim_src_config
   ==> ?syntax_oracle.
         semantics_prog (add_eval_state ev s0) env prog
           (flat_semantics
              (mk_flat_install_conf (backend_from_flat_tuple_cc asm_conf c)
                 (cake_orac asm_conf c' syntax_oracle (SND o config_tuple1)
                    (\ps. backend_progs_flat_prog ps)))
              (state_ffi s0) p')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC (CASE_TERM
   `orac = (\(cfg,id,ds). (id,compiler_instance_config_v (THE ev) cfg,ds)) o
           cake_orac (asm_conf:(A)asm_config) c'
             (\i. match get_oracle (THE ev) (add_eval_state ev (s0:(FFI)state)) env prog i with
                    SOME (id,(v:v),ds) -> (id,ds)
                  | _ -> ((0,0),[]))
             I (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps))`) THEN
  ABBREV_TAC `es = put_oracle (THE (ev:((backend_config)compiler_instance)option)) orac` THEN
  EXISTS_TAC `(I ## SND) o eval_oracle_state_oracle (orac_s es)` THEN
  ABBREV_TAC `syn = (I ## SND) o eval_oracle_state_oracle (orac_s es)` THEN
  SUBGOAL_THEN
   `install_conf_rel (source_to_flat_config_pattern_cfg prim_src_config)
      (mk_flat_install_conf
         (pure_cc (MAP (compile_dec (source_to_flat_config_pattern_cfg prim_src_config)))
            (backend_from_flat_tuple_cc (asm_conf:(A)asm_config) c))
         (state_co (\c (env_id,decs). inc_compile_prog env_id c (source_to_source_compile decs))
            (cake_orac asm_conf c' syn config_tuple1
               (\ps. (backend_progs_env_id ps,backend_progs_source_prog ps)))))
      (mk_flat_install_conf (backend_from_flat_tuple_cc asm_conf c)
         (cake_orac asm_conf c' syn (SND o config_tuple1) (\ps. backend_progs_flat_prog ps)))`
   (LABEL_TAC "icr") THENL
  [REWRITE_TAC[install_conf_rel_def; mk_flat_install_conf_def] THEN SIMP[] THEN
   REWRITE_TAC[GSYM source_to_flat_orac_eq] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP state_co_inc_compile_has_flat_comp) THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `p' = SND (source_to_flat_compile prim_src_config (source_to_source_compile prog))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `ev:((backend_config)compiler_instance)option` THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[add_eval_state_def]) THEN REWRITE_TAC[add_eval_state_def] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM (MATCH_MP source_to_source_semantics_prog_equiv th)]) THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] source_to_flatProof_compile_semantics) THEN
  BKP2AUX_EXISTS_NONE_TAC THEN CONJ_TAC THENL
  [REWRITE_TAC[precondition_def] THEN
   USE_THEN "icr" (fun th -> EXISTS_TAC (rand(rator(concl th)))) THEN
   EXISTS_TAC `I:dec list->dec list` THEN USE_THEN "icr" (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[precondition1_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BKP2AUX_prim_env_facts) THEN
  UNDISCH_TAC `THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env)` THEN
  REWRITE_TAC[prim_sem_env_eq; THE_DEF; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[BKP2AUX_prim_src_facts] THEN
  REWRITE_TAC[(record_info "state").ri_accessors] THEN
  REWRITE_TAC[src_orac_step_invs_def; orac_rel_def; src_orac_next_cfg_def;
              init_eval_state_ok_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FLATP2AUX_init_genv_els_eval; ALL] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV;
   ASM_MESON_TAC[source_to_source_semantics_prog_equiv]];
   REWRITE_TAC[add_eval_state_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[add_eval_state_def; THE_DEF]) THEN
  MATCH_MP_TAC (ISPEC `a:(backend_config)compiler_instance` eval_oracle_semantics_prog_intro) THEN
  EXISTS_TAC `orac:num->(num#num)#v#dec list` THEN
  SUBGOAL_THEN `state_refs (s0:(FFI)state) = [] /\ state_eval_state s0 = NONE /\
                nsAll (K concrete_v) (sem_env_v (env:(v)sem_env))` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env)` THEN
   REWRITE_TAC[prim_sem_env_eq; THE_DEF; PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[(record_info "state").ri_accessors; (record_info "sem_env").ri_accessors] THEN
   REWRITE_TAC[GSYM nsEmpty_def; nsAll_nsEmpty];
   ALL_TAC] THEN
  REWRITE_TAC[(record_info "state").ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[precond_eval_state_def; (record_info "state").ri_accfupds; K_THM] THEN
  CASE_REWRITE_TAC[mk_init_eval_state_def] THEN REWRITE_TAC[GSYM mk_init_eval_state_def] THEN
      CONJ_TAC THENL
  [EXPAND_TAC "orac" THEN MATCH_MP_TAC cake_orac_extended_wf THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
      FIRST_ASSUM(fun th -> let l,r = dest_eq (concl th) in
   if r = `orac:num->(num#num)#v#dec list` then
     let co = find_term (fun t -> try let h,args = strip_comb t in
                fst(dest_const h) = "cake_orac" && length args = 5 with Failure _ -> false) l in
     let syn = el 2 (snd (strip_comb co)) in
     let s1 = `state_eval_state_fupd (K (SOME (mk_init_eval_state (a:(backend_config)compiler_instance)))) (s0:(FFI)state)` in
     MP_TAC (ISPECL [s1; `env:(v)sem_env`; `prog:dec list`; `asm_conf:(A)asm_config`; `c':backend_config`;
                     `a:(backend_config)compiler_instance`; syn; s1] cake_orac_eq_get_oracle)
   else failwith "") THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[(record_info "state").ri_accfupds; K_THM] THEN
   REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   SPEC_TAC(`r:(num#num)#v#dec list`,`r:(num#num)#v#dec list`) THEN
   REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_MAP_THM; I_THM];
   ALL_TAC] THEN
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN EXPAND_TAC "orac" THEN REWRITE_TAC[o_THM] THEN
  W(fun (asl,w) -> let co = find_term (fun t -> try let h,args = strip_comb t in
                fst(dest_const h) = "cake_orac" && length args = 6 with Failure _ -> false) w in
     FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `((p1,p2),p1',p2'):(num#num)#v#dec list`; co])) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
      DISCH_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] source_to_source_semantics_prog_intro) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `~semantics_prog
        (state_eval_state_fupd (K es)
        (state_eval_state_fupd (K (SOME (mk_init_eval_state (a:(backend_config)compiler_instance)))) (s0:(FFI)state)))
        env (source_to_source_compile prog) Fail` THEN
  EXPAND_TAC "es" THEN REWRITE_TAC[put_oracle_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] source_to_source_semantics_prog_oracle_intro) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `p' = SND (source_to_flat_compile prim_src_config (source_to_source_compile prog))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      W(fun (asl,w) -> let _,args = strip_comb w in
     let s3 = el 0 args and e = el 1 args and p = el 2 args and r = el 3 args in
     let ec = hd (snd (strip_comb r)) in
     MP_TAC (ISPECL [`SOME (OPTION_MAP config_tuple1 o
                            v_fun_abs UNIV (compiler_instance_config_v (a:(backend_config)compiler_instance)))`;
                     s3; e; `prim_src_config`; ec; p] source_to_flatProof_compile_semantics)) THEN
  REWRITE_TAC[(record_info "state").ri_accfupds] THEN
  DISCH_THEN (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[precondition_def] THEN
  USE_THEN "icr" (fun th -> EXISTS_TAC (rand(rator(concl th)))) THEN
  EXISTS_TAC `source_to_source_compile` THEN USE_THEN "icr" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[precondition1_def; (record_info "state").ri_accfupds; K_THM] THEN
      SUBGOAL_THEN `state_next_type_stamp (s0:(FFI)state) = 2 /\ state_next_exn_stamp s0 = 4`
   STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env)` THEN
   REWRITE_TAC[prim_sem_env_eq; THE_DEF; PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[(record_info "state").ri_accessors];
   ALL_TAC] THEN
  SUBGOAL_THEN `init_global_env_inv init_genv (source_to_flat_config_mod_env prim_src_config)
                  (env:(v)sem_env)` ASSUME_TAC THENL
  [ASM_MESON_TAC[BKP2AUX_prim_env_facts]; ALL_TAC] THEN
  ASM_REWRITE_TAC[BKP2AUX_prim_src_facts] THEN
  REWRITE_TAC[FLATP2AUX_init_genv_els_eval; ALL] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[insert_gen_oracle_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[init_eval_state_ok_def; (record_info "eval_oracle_state").ri_accessors;
              (record_info "eval_oracle_state").ri_accfupds] THEN
      REWRITE_TAC[o_THM; K_THM; FST; shift_seq_zero] THEN REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] step_invs_cake_orac) THEN
  FIRST_ASSUM(fun th -> let l,r = dest_eq (concl th) in
   if r = `orac:num->(num#num)#v#dec list` then
     let f0,co = dest_binop `(o):(backend_config#(num#num)#dec list->(num#num)#v#dec list)->(num->backend_config#(num#num)#dec list)->num->(num#num)#v#dec list` l in
     let args = snd (strip_comb co) in
     let syn0 = el 2 args and g = el 4 args in
     let f = mk_comb(mk_comb(`(o):(backend_config#(num#num)#dec list->(num#num)#v#dec list)->(backend_config#(A)backend_progs->backend_config#(num#num)#dec list)->backend_config#(A)backend_progs->(num#num)#v#dec list`, f0),
                     mk_comb(mk_comb(`(##):(backend_config->backend_config)->((A)backend_progs->(num#num)#dec list)->backend_config#(A)backend_progs->backend_config#(num#num)#dec list`, `I:backend_config->backend_config`), g)) in
     MAP_EVERY EXISTS_TAC [f; `asm_conf:(A)asm_config`; `c':backend_config`; syn0]
   else failwith "") THEN
  CONJ_TAC THENL
  [REWRITE_TAC[(record_info "eval_oracle_state").ri_accfupds; K_THM] THEN
   EXPAND_TAC "orac" THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [cake_orac_eq_I] THEN
   REWRITE_TAC[o_ASSOC];
   ALL_TAC] THEN
        X_GEN_TAC `x:backend_config#(A)backend_progs` THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `x:backend_config#(A)backend_progs` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[o_THM; PAIR_MAP_THM; I_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[FST; SND] THEN
  BKP2AUX_HDTM_ASSUM "opt_eval_config_wf" (fun th -> REWRITE_TAC[MATCH_MP config_wf_abs_conc th]) THEN
  REWRITE_TAC[IN_UNIV; OPTION_MAP_DEF; injectivity "option"; config_tuple1_def] THEN
  MESON_TAC[FST];
       FIRST_ASSUM(fun th -> let l,r = dest_eq (concl th) in
   if r = `orac:num->(num#num)#v#dec list` then
     let co = find_term (fun t -> try let h,args = strip_comb t in
                fst(dest_const h) = "cake_orac" && length args = 5 with Failure _ -> false) l in
     let syn0 = el 2 (snd (strip_comb co)) in
     SUBGOAL_THEN (mk_eq(`syn:num->(num#num)#dec list`, syn0)) ASSUME_TAC THENL [EXPAND_TAC "syn" THEN EXPAND_TAC "es" THEN
  REWRITE_TAC[put_oracle_def; insert_gen_oracle_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[orac_s_def; (record_info "eval_oracle_state").ri_accfupds;
              (record_info "eval_oracle_state").ri_accessors; K_THM; o_THM; FST;
              shift_seq_zero] THEN
  EXPAND_TAC "orac" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; BKP2AUX_cake_orac_src; I_THM] THEN
  REWRITE_TAC[LAMBDA_TRIPLE; FST; SND; PAIR_MAP_THM; I_THM; PAIR]; ALL_TAC]
   else failwith "") THEN
        FIRST_X_ASSUM(fun th -> if lhs(concl th) = `syn:num->(num#num)#dec list` then
            RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else failwith "") THEN
        EXPAND_TAC "orac" THEN MATCH_MP_TAC BKP2AUX_orac_rel_lemma THEN ASM_MESON_TAC[];
       EXPAND_TAC "orac" THEN MATCH_MP_TAC BKP2AUX_next_cfg_lemma THEN ASM_MESON_TAC[]]]]);;

(* HOL4 line 3401 *)
let flat_semantics = prove
 (`!asm_conf c' syn cc ffi ds cconf.
     let co = cake_orac (asm_conf:(A)asm_config) c' syn (SND o config_tuple1)
              (\ps. backend_progs_flat_prog ps) in
   let f_inst = mk_flat_install_conf (pure_cc inc_compile_decs cc) co in
   ~(flat_semantics f_inst (ffi:(FFI)ffi_state) ds = Fail) /\
   0 < clos_to_bvl_config_max_app cconf /\ no_Mat_decs ds
   ==> clos_semantics ffi (clos_to_bvl_config_max_app cconf) FEMPTY
         (pure_co inc_compile_decs o co) cc (flat_to_clos_compile_prog ds) =
       flat_semantics f_inst ffi ds`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] flat_to_closProof_compile_semantics) THEN
  ASM_REWRITE_TAC[install_config_rel_def; mk_flat_install_conf_def] THEN SIMP[] THEN
  REWRITE_TAC[GSYM source_to_flat_orac_eq; SND_state_co] THEN
  REWRITE_TAC[LAMBDA_PAIR; inc_compile_no_Mat]);;

(* HOL4 line 3419 *)
let pad_code_no_share_mem_inst = prove
 (`!sec_list nop.
     no_share_mem_inst (sec_list:((A)sec)list)
   ==> no_share_mem_inst (pad_code nop sec_list)`,
  MESON_TAC[code_similar_IMP_both_no_share_mem; code_similar_pad_code; code_similar_refl]);;

(* HOL4 line 3430 *)
let enc_sec_list_no_share_mem_inst = prove
 (`!code enc.
     no_share_mem_inst (code:((A)sec)list)
   ==> no_share_mem_inst (enc_sec_list enc code)`,
  MESON_TAC[code_similar_IMP_both_no_share_mem; code_similar_sym;
            code_similar_enc_sec_list; code_similar_refl]);;

(* HOL4 line 3441 *)
let enc_secs_again_no_share_mem_inst = prove
 (`!done pos labs ffi_names enc sec_list code.
     enc_secs_again pos labs ffi_names enc (sec_list:((A)sec)list) = (code,done) /\
     no_share_mem_inst sec_list
     ==> no_share_mem_inst code`,
  MESON_TAC[code_similar_IMP_both_no_share_mem; enc_secs_again_IMP_similar]);;

(* HOL4 line 3453 *)
let upd_lab_len_no_share_mem_inst = prove
 (`!pos sec_list. no_share_mem_inst (sec_list:((A)sec)list)
         ==> no_share_mem_inst (upd_lab_len pos sec_list)`,
  MESON_TAC[code_similar_IMP_both_no_share_mem; code_similar_sym;
            code_similar_upd_lab_len; code_similar_refl]);;

(* HOL4 line 3465 *)
let remove_labels_loop_no_share_mem_inst = prove
 (`!cl conf pos init_labs ffi_names sec_list code labs.
     remove_labels_loop cl (conf:(A)asm_config) pos init_labs ffi_names sec_list =
       SOME (code,labs) /\
     no_share_mem_inst sec_list
     ==> no_share_mem_inst code`,
  MATCH_MP_TAC remove_labels_loop_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[remove_labels_loop_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BACKDEFAUX_PAIRARG_TAC THEN
  COND_CASES_TAC THENL
  [BACKDEFAUX_PAIRARG_TAC THEN COND_CASES_TAC THEN
   REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   MATCH_MP_TAC pad_code_no_share_mem_inst THEN
   ASM_MESON_TAC[enc_secs_again_no_share_mem_inst; upd_lab_len_no_share_mem_inst];
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`p2:bool`; `p1:((A)sec)list`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC[enc_secs_again_no_share_mem_inst]]);;

(* mmio_pcs_min_index of ExtCall names followed by SharedMem names *)
let BKP2AUX_mmio_APPEND = prove
 (`!ffis l. ALL (\x. ?s. x = ExtCall s) ffis /\ ALL (\x. ?op. x = SharedMem op) l
            ==> mmio_pcs_min_index (APPEND ffis l) = SOME (LENGTH ffis)`,
  REWRITE_TAC[Sh_not_Ext] THEN MESON_TAC[mmio_pcs_min_index_APPEND_thm]);;

let BKP2AUX_mmio_ALL = prove
 (`!ffis. ALL (\x. ?s. x = ExtCall s) ffis
          ==> mmio_pcs_min_index ffis = SOME (LENGTH ffis)`,
  MESON_TAC[BKP2AUX_mmio_APPEND; APPEND_NIL; ALL]);;

(* HOL4 line 3500 *)
let compile_lab_IMP_mmio_pcs_min_index = prove
 (`!asm_conf c sec_list bytes c'.
     compile_lab (asm_conf:(A)asm_config) c sec_list = SOME (bytes,c') /\
   OPTION_ALL (ALL (\x. ?s. x = ExtCall s)) (lab_to_target_config_ffi_names c)
   ==> ?ffi_names. lab_to_target_config_ffi_names c' = SOME ffi_names /\
                   ?x. mmio_pcs_min_index ffi_names = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_lab_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASES_ON `lab_to_target_config_ffi_names c` THEN CASE_REWRITE_TAC[OPTION_ALL_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_shmem_info_MappedRead_or_MappedWrite) THEN
  ASM_REWRITE_TAC[APPEND] THEN ASM_MESON_TAC[BKP2AUX_mmio_APPEND; find_ffi_names_EVERY]);;

(* HOL4 line 3520 *)
let compile_lab_no_share_mem_IMP_mmio_pcs_min_index = prove
 (`!asm_conf c sec_list bytes c'.
     compile_lab (asm_conf:(A)asm_config) c sec_list = SOME (bytes,c') /\
   no_share_mem_inst sec_list /\
   OPTION_ALL (ALL (\x. ?s. x = ExtCall s)) (lab_to_target_config_ffi_names c)
   ==> ?ffi_names. lab_to_target_config_ffi_names c' = SOME ffi_names /\
                   mmio_pcs_min_index ffi_names = SOME (LENGTH ffi_names)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_lab_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASES_ON `lab_to_target_config_ffi_names c` THEN CASE_REWRITE_TAC[OPTION_ALL_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  BKP2AUX_HDTM_X_ASSUM "remove_labels"
    (MP_TAC o MATCH_MP_CURRIED remove_labels_loop_no_share_mem_inst o
     REWRITE_RULE[remove_labels_def]) THEN
  ASM_SIMP_TAC[enc_sec_list_no_share_mem_inst] THEN DISCH_TAC THEN
  BKP2AUX_HDTM_X_ASSUM "get_shmem_info" MP_TAC THEN
  ASM_SIMP_TAC[no_share_mem_IMP_get_shmem_info; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[APPEND_NIL; LENGTH; ADD_CLAUSES] THEN
  ASM_MESON_TAC[BKP2AUX_mmio_ALL; find_ffi_names_EVERY]);;

(* the intermediate programs and configurations of compile *)
let BKP2AUX_compile_phases = prove
 (`!asm_conf c prog bytes bitmaps c'.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c')
  ==> ?sc' p_flat cc' p_bvl names1 s p_bvi l bl n1 n2 n3 names2 col p_word bm wc fs p_stack lc.
      source_to_flat_compile (backend_config_source_conf c) (source_to_source_compile prog) =
        (sc',p_flat) /\
      clos_to_bvl_compile (backend_config_clos_conf c) (flat_to_clos_compile_prog p_flat) =
        (cc',p_bvl,names1) /\
      bvl_to_bvi_compile (clos_to_bvl_config_start cc') (backend_config_bvl_conf c) names1 p_bvl =
        (s,p_bvi,l,bl,n1,n2,n3,names2) /\
      data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
        asm_conf (bvi_to_data_compile_prog p_bvi) = (col,p_word) /\
      word_to_stack_compile asm_conf
        (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p_word =
        (bm,wc,fs,p_stack) /\
      lab_to_target_compile asm_conf (backend_config_lab_conf c)
        (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
           (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
           (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
           (asm_config_addr_offset asm_conf) p_stack) = SOME (bytes,lc) /\
      bitmaps = bm /\
      backend_config_lab_conf c' = lc /\
      backend_config_source_conf c' = sc' /\
      backend_config_clos_conf c' = clos_to_bvl_config_start_fupd (K s) cc' /\
      backend_config_bvl_conf c' =
        bvl_to_bvi_config_inlines_fupd (K l)
          (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
            (bvl_to_bvi_config_next_name1_fupd (K n1)
              (bvl_to_bvi_config_next_name2_fupd (K n2)
                (bvl_to_bvi_config_next_name3_fupd (K n3) (backend_config_bvl_conf c))))) /\
      backend_config_word_to_word_conf c' =
        word_to_word_config_col_oracle_fupd (K col) (backend_config_word_to_word_conf c) /\
      backend_config_word_conf c' = wc /\
      backend_config_stack_conf c' = backend_config_stack_conf c /\
      backend_config_data_conf c' = backend_config_data_conf c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compile_eq_from_source; from_source_def; from_flat_def; from_clos_def;
              from_bvl_def; from_bvi_def; from_data_def; from_word_def; from_stack_def;
              from_lab_def] THEN
  BACKDEFAUX_LETS_TAC THEN SIMP[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP attach_bitmaps_SOME) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ]) THEN RVEQ_TAC THEN SIMP[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[(record_info "backend_config").ri_accfupds; K_THM]) THEN
  ASM_MESON_TAC[]);;

(* the semantics of the flatLang program is that of the dataLang program *)
let BKP2AUX_flat_to_data = prove
 (`!asm_conf c prog bytes bitmaps c' syn ffi sc' p_flat cc' p_bvl names1 s p_bvi l bl n1 n2 n3 names2 lim ss.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c') /\
  backend_config_ok asm_conf c /\
  source_to_flat_compile (backend_config_source_conf c) (source_to_source_compile prog) =
    (sc',p_flat) /\
  clos_to_bvl_compile (backend_config_clos_conf c) (flat_to_clos_compile_prog p_flat) =
    (cc',p_bvl,names1) /\
  bvl_to_bvi_compile (clos_to_bvl_config_start cc') (backend_config_bvl_conf c) names1 p_bvl =
    (s,p_bvi,l,bl,n1,n2,n3,names2) /\
  backend_config_clos_conf c' = clos_to_bvl_config_start_fupd (K s) cc' /\
  backend_config_bvl_conf c' =
    bvl_to_bvi_config_inlines_fupd (K l)
      (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
        (bvl_to_bvi_config_next_name1_fupd (K n1)
          (bvl_to_bvi_config_next_name2_fupd (K n2)
            (bvl_to_bvi_config_next_name3_fupd (K n3) (backend_config_bvl_conf c))))) /\
  ~(flat_semantics
      (mk_flat_install_conf (backend_from_flat_tuple_cc asm_conf c)
         (cake_orac asm_conf c' syn (SND o config_tuple1) (\ps. backend_progs_flat_prog ps)))
      (ffi:(FFI)ffi_state) p_flat = Fail)
  ==> data_semantics ffi (fromAList (bvi_to_data_compile_prog p_bvi))
        (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
           (\ps. backend_progs_data_prog ps))
        (backend_from_data_tuple_cc asm_conf c) lim ss s =
      flat_semantics
        (mk_flat_install_conf (backend_from_flat_tuple_cc asm_conf c)
           (cake_orac asm_conf c' syn (SND o config_tuple1) (\ps. backend_progs_flat_prog ps)))
        ffi p_flat`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c':backend_config`; `syn:num->(num#num)#dec list`;
                 `compile_common_inc (backend_config_clos_conf c)
                    (pure_cc (clos_to_bvl_compile_inc'
                                (clos_to_bvl_config_max_app (backend_config_clos_conf c)))
                       (full_cc (backend_config_bvl_conf c)
                          (pure_cc bvi_to_data_compile_prog
                             (backend_from_data_tuple_cc (asm_conf:(A)asm_config) c))))`;
                 `ffi:(FFI)ffi_state`; `p_flat:(flat_exp)list`; `backend_config_clos_conf c`]
          flat_semantics) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[GSYM backend_from_flat_tuple_cc_def] THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `backend_config_ok (asm_conf:(A)asm_config) c` THEN
    SIMP[backend_config_ok_def];
    MP_TAC(ISPECL [`backend_config_source_conf c`; `source_to_source_compile prog`] compile_no_Mat) THEN
    ASM_REWRITE_TAC[]];
   DISCH_THEN(fun th -> LABEL_TAC "fc" th THEN REWRITE_TAC[SYM th])] THEN
  REWRITE_TAC[flat_to_clos_orac_eq] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_to_clos_orac_eq]) THEN
  SUBGOAL_THEN `SND (to_clos c prog) = flat_to_clos_compile_prog p_flat` ASSUME_TAC THENL
  [REWRITE_TAC[to_clos_def; to_flat_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
                 `bitmaps:(A word)list`; `c':backend_config`; `backend_config_clos_conf c`;
                 `flat_to_clos_compile_prog p_flat`; `cc':clos_to_bvl_config`;
                 `(p_bvl:(num#num#bvl_exp)list,names1:mlstring spt)`;
                 `syn:num->(num#num)#dec list`] cake_orac_clos_syntax_oracle_ok) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `backend_config_ok (asm_conf:(A)asm_config) c` THEN
   REWRITE_TAC[backend_config_ok_def] THEN STRIP_TAC THEN
   ASM_SIMP_TAC[ARITH_RULE `0 < n ==> 1 <= n`] THEN
   MESON_TAC[];
   DISCH_TAC] THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `backend_config_clos_conf c`;
                 `cake_orac (asm_conf:(A)asm_config) c' syn (SND o config_tuple1)
                    (\ps. backend_progs_clos_prog ps)`;
                 `full_cc (backend_config_bvl_conf c)
                    (pure_cc bvi_to_data_compile_prog
                       (backend_from_data_tuple_cc (asm_conf:(A)asm_config) c))`;
                 `flat_to_clos_compile_prog p_flat`; `cc':clos_to_bvl_config`;
                 `p_bvl:(num#num#bvl_exp)list`; `names1:mlstring spt`]
          clos_to_bvlProof_compile_semantics) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN USE_THEN "fc" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
   DISCH_THEN(fun th -> LABEL_TAC "cb" th THEN REWRITE_TAC[SYM th])] THEN
  MP_TAC(ISPECL [`prog:dec list`; `bytes:byte list`; `bitmaps:(A word)list`; `c:backend_config`;
                 `backend_config_clos_conf c`; `asm_conf:(A)asm_config`; `c':backend_config`;
                 `syn:num->(num#num)#dec list`] clos_to_bvl_orac_eq) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(ISPECL [`clos_to_bvl_config_start cc'`; `backend_config_bvl_conf c`; `names1:mlstring spt`;
                 `p_bvl:(num#num#bvl_exp)list`; `s:num`; `p_bvi:(num#num#bvi_exp)list`;
                 `l:(num#bvl_exp)spt`; `bl:(num#bvi_exp)spt`; `n1:num`; `n2:num`; `n3:num`;
                 `names2:mlstring spt`;
                 `cake_orac (asm_conf:(A)asm_config) c' syn config_tuple2
                    (\ps. backend_progs_bvl_prog ps)`;
                 `ffi:(FFI)ffi_state`;
                 `pure_cc bvi_to_data_compile_prog
                    (backend_from_data_tuple_cc (asm_conf:(A)asm_config) c)`]
          bvl_to_bvi_compile_semantics2) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[cake_orac_0; config_tuple2_def] THEN
   REPEAT CONJ_TAC THENL
   [SIMP[] THEN MESON_TAC[];
    ASM_MESON_TAC[cake_orac_bvl_ALL_DISTINCT];
    ASM_MESON_TAC[compile_all_distinct_locs];
    ASM_MESON_TAC[is_state_oracle_tailrec_cake_orac];
    ASM_MESON_TAC[is_state_oracle_tmc_cake_orac]];
   ALL_TAC] THEN
  ANTS_TAC THENL
  [USE_THEN "cb" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fc" (fun th -> REWRITE_TAC[th]) THEN
   ASM_REWRITE_TAC[];
   DISCH_THEN(fun th -> LABEL_TAC "bb" th THEN REWRITE_TAC[SYM th])] THEN
  MP_TAC(ISPECL [`prog:dec list`; `bytes:byte list`; `bitmaps:(A word)list`; `c:backend_config`;
                 `backend_config_bvl_conf c`; `asm_conf:(A)asm_config`; `c':backend_config`;
                 `syn:num->(num#num)#dec list`] bvl_to_bvi_orac_eq) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  REWRITE_TAC[pure_cc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `data_semantics (ffi:(FFI)ffi_state) (fromAList (bvi_to_data_compile_prog p_bvi))
                ((I ## bvi_to_data_compile_prog) o
                 cake_orac (asm_conf:(A)asm_config) c' syn (SND o SND o SND o SND o SND o config_tuple2)
                   (\ps. backend_progs_bvi_prog ps))
                (backend_from_data_tuple_cc asm_conf c) lim ss s` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM pure_co_def; bvi_to_data_orac_eq];
   MATCH_MP_TAC bvi_to_dataProof_compile_prog_semantics] THEN
  REWRITE_TAC[GSYM(CONV_RULE(TOP_DEPTH_CONV let_CONV) pure_cc_def)] THEN
  REWRITE_TAC[ETA_AX] THEN
  USE_THEN "bb" (fun th -> REWRITE_TAC[REWRITE_RULE[ETA_AX] th]) THEN
  USE_THEN "cb" (fun th -> REWRITE_TAC[REWRITE_RULE[ETA_AX] th]) THEN
  USE_THEN "fc" (fun th -> REWRITE_TAC[REWRITE_RULE[ETA_AX] th]) THEN
  FIRST_X_ASSUM(fun th -> if is_neg (concl th) then MP_TAC th else failwith "") THEN
  REWRITE_TAC[ETA_AX]);;

let BKP2AUX_ewrl_not_fail = prove
 (`!x y. x IN extend_with_resource_limit {y} /\ ~(y = Fail) ==> ~(x = Fail)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (INST [`x:behaviour`,`x:behaviour`; `{y:behaviour}`,`y:behaviour->bool`]
                  extend_with_resource_limit_not_fail) THEN
  ASM_REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[]);;
(* composition of the backend's semantic refinements *)
let BKP2AUX_compose = prove
 (`!M L S W D b1 b2.
     ~(D = Fail) /\ W IN extend_with_resource_limit' b1 {D} /\
     (~(W = Fail) ==> S IN extend_with_resource_limit' b2 {W}) /\ (b1 ==> b2) /\
     (~(S = Fail) ==> L = S) /\ implements' T M {L}
     ==> M SUBSET extend_with_resource_limit' b1 {D}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(W = Fail)` ASSUME_TAC THENL
  [UNDISCH_TAC `W IN extend_with_resource_limit' b1 {D}` THEN
   REWRITE_TAC[extend_with_resource_limit'_def] THEN COND_CASES_TAC THEN
   REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[BKP2AUX_ewrl_not_fail];
   ALL_TAC] THEN
  SUBGOAL_THEN `S IN extend_with_resource_limit' b2 {W}` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(S = Fail)` ASSUME_TAC THENL
  [UNDISCH_TAC `S IN extend_with_resource_limit' b2 {W}` THEN
   REWRITE_TAC[extend_with_resource_limit'_def] THEN COND_CASES_TAC THEN
   REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[BKP2AUX_ewrl_not_fail];
   ALL_TAC] THEN
  UNDISCH_TAC `implements' T M {L}` THEN
  ASM_SIMP_TAC[implements'_def; extend_with_resource_limit'_def; IN_SING] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `{S:behaviour}` THEN
  ASM_REWRITE_TAC[SING_SUBSET] THEN
  UNDISCH_TAC `W IN extend_with_resource_limit' b1 {D}` THEN
  UNDISCH_TAC `S IN extend_with_resource_limit' b2 {W}` THEN
  ASM_CASES_TAC `b1:bool` THENL
  [SUBGOAL_THEN `b2:bool` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[extend_with_resource_limit'_def; IN_SING] THEN MESON_TAC[];
   ASM_REWRITE_TAC[extend_with_resource_limit'_def; IN_SING] THEN
   ASM_CASES_TAC `b2:bool` THEN ASM_REWRITE_TAC[IN_SING] THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`{W:behaviour}`; `extend_with_resource_limit {D}`] SEMPROPSAUX_extend_mono) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN
    MP_TAC(ISPEC `{D:behaviour}` SEMPROPSAUX_extend_extend) THEN
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]]]);;

let BKP2AUX_compile_no_stubs_nsm = prove
 (`!f jump (offset:A word#A word) sp (prog:(num#(A)stack_prog)list).
     ALL (\(a,p). no_shmemop p) prog ==> no_share_mem_inst (compile_no_stubs f jump offset sp prog)`,
  MESON_TAC[compile_no_stubs_no_share_mem_inst]);;
let BKP2AUX_cwts_nsm = prove
 (`!ac perf k (prog:(num#num#(A)wl_prog)list) bs.
     ALL (\(n,m,pp). no_share_inst pp) prog
     ==> ALL (\(a,p). no_shmemop p) (FST (compile_word_to_stack ac perf k prog bs))`,
  MESON_TAC[compile_word_to_stack_no_share_inst; PAIR]);;

(* the code of the labLang oracle has no shared memory instructions *)
let BKP2AUX_lab_oracle_no_share = prove
 (`!asm_conf c prog b bm c' syn k.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c') /\
  stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F
  ==> no_share_mem_inst
        (SND (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o SND o config_tuple2)
                (\ps. backend_progs_lab_prog ps) k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:dec list`; `b:byte list`; `bm:(A word)list`; `c:backend_config`;
                 `stack_to_lab_config_reg_names (backend_config_stack_conf c)`;
                 `stack_to_lab_config_jump (backend_config_stack_conf c)`;
                 `asm_config_addr_offset (asm_conf:(A)asm_config)`;
                 `asm_config_reg_count (asm_conf:(A)asm_config) -
                    (LENGTH (asm_config_avoid_regs asm_conf) + 3)`;
                 `asm_conf:(A)asm_config`; `c':backend_config`; `syn:num->(num#num)#dec list`;
                 `SND o SND o SND o SND o SND o SND o config_tuple2`] stack_to_lab_orac_eq_std_sym) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_THM; SND_pure_co] THEN
  MATCH_MP_TAC BKP2AUX_compile_no_stubs_nsm THEN
  MP_TAC(ISPECL [`prog:dec list`; `b:byte list`; `bm:(A word)list`; `c:backend_config`;
                 `asm_conf:(A)asm_config`; `c':backend_config`; `syn:num->(num#num)#dec list`]
          word_to_stack_orac_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `ALL (\(n,m,pp). no_share_inst pp)
                  (SND (cake_orac (asm_conf:(A)asm_config) c' syn
                          (SND o SND o SND o SND o SND o config_tuple2)
                          (\ps. backend_progs_word_prog ps) k))` MP_TAC THENL
  [MP_TAC(ISPECL [`prog:dec list`; `b:byte list`; `bm:(A word)list`; `c:backend_config`;
                  `asm_config_two_reg_arith (asm_conf:(A)asm_config)`;
                  `asm_config_reg_count (asm_conf:(A)asm_config) -
                     (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
                  `word_to_word_config_reg_alg (backend_config_word_to_word_conf c)`;
                  `ensure_fp_conf_ok (asm_conf:(A)asm_config) (backend_config_data_conf c)`;
                  `asm_conf:(A)asm_config`; `c':backend_config`; `syn:num->(num#num)#dec list`]
           data_to_word_orac_eq_sym_std) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[o_THM; SND_pure_co] THEN REWRITE_TAC[ALL_MAP] THEN
   REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
   REWRITE_TAC[LAMBDA_TRIPLE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC full_compile_single_no_share_inst THEN REWRITE_TAC[FST] THEN
  SPEC_TAC(`x:num#num#data_prog`,`x:num#num#data_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; data_to_word_compile_part_def] THEN
  MESON_TAC[comp_no_share_inst; PAIR];
   ALL_TAC] THEN
  BKP2AUX_GEN_CONST_TAC "cake_orac" 6 THEN
  X_GEN_TAC `w:(num#lab_to_target_config)#(num#num#(A)wl_prog)list` THEN
  STRUCT_CASES_TAC (ISPEC `w:(num#lab_to_target_config)#(num#num#(A)wl_prog)list` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC (ISPEC `x:num#lab_to_target_config` PAIR_SURJECTIVE) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[LAMBDA_TRIPLE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND] THEN
  DISCH_TAC THEN MATCH_MP_TAC BKP2AUX_cwts_nsm THEN ASM_REWRITE_TAC[LAMBDA_TRIPLE]);;

let BKP2AUX_data_names = prove
 (`!l. ALL (\n. data_num_stubs <= n) l
       ==> ALL (\n. ~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = 4)) l /\
           (!e. e < 62 ==> ~MEM e l)`,
  REWRITE_TAC[GSYM ALL_MEM; data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[ARITH_RULE `62 <= n ==> ~(n = 0) /\ ~(n = 1) /\ ~(n = 2) /\ ~(n = 4)`;
                                          ARITH_RULE `e < 62 ==> ~(62 <= e)`]);;

(* syntactic properties of the initial labLang program *)
let BKP2AUX_syntax_p7 = prove
 (`!asm_conf c p_data col p_word bm wc fs p_stack.
  backend_config_ok (asm_conf:(A)asm_config) c /\ good_dimindex (:A) /\
  data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
    asm_conf p_data = (col,p_word) /\
  word_to_stack_compile asm_conf F p_word = (bm,wc,fs,p_stack) /\
  ALL (\n. data_num_stubs <= n) (MAP FST p_data) /\ ALL_DISTINCT (MAP FST p_data)
  ==> labels_ok (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
         (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
         (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
         (asm_config_addr_offset asm_conf) p_stack) /\
      ALL (sec_ok_pre asm_conf)
        (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
         (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
         (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
         (asm_config_addr_offset asm_conf) p_stack)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`backend_config_data_conf c`; `backend_config_word_to_word_conf c`;
                 `asm_conf:(A)asm_config`; `p_data:(num#num#data_prog)list`]
          data_to_word_compile_conventions) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`backend_config_data_conf c`; `backend_config_word_to_word_conf c`;
                 `asm_conf:(A)asm_config`; `p_data:(num#num#data_prog)list`]
          data_to_word_compile_lab_pres) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p_word:(num#num#(A)wl_prog)list`; `asm_conf:(A)asm_config`]
          word_to_stack_compile_lab_pres) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `p_word:(num#num#(A)wl_prog)list`]
          word_to_stack_stack_asm_convs) THEN
  ASM_REWRITE_TAC[] THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [BKP2AUX_ASSUM_MENTIONS "flat_exp_conventions" MP_TAC THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_RULE `a - (5 + b) = a - (b + 5)`] THEN
    MESON_TAC[];
    UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
                 asm_config_reg_count asm_conf` THEN ARITH_TAC];
   DISCH_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC stack_to_lab_compile_lab_pres THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[D2WPAUX_MAP_FST_stubs; ALL; ALL_APPEND; ALL_DISTINCT; ALL_DISTINCT_APPEND;
               MEM; MEM_APPEND; raise_stub_location_def; wl_store_consts_stub_location_def;
               gc_stub_location_def; word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BKP2AUX_data_names) THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
   X_GEN_TAC `e:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   POP_ASSUM MP_TAC THEN ARITH_TAC;
   SUBGOAL_THEN `ALL (\(n,p). stack_asm_name (asm_conf:(A)asm_config) p) (p_stack:(num#(A)stack_prog)list) /\
                ALL (\(n,p). stack_asm_remove asm_conf p) p_stack` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN BKP2AUX_ASSUM_MENTIONS "stack_asm_remove" MP_TAC THEN MATCH_MP_TAC MONO_ALL THEN
   REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC stack_to_lab_compile_all_enc_ok THEN
  ASM_REWRITE_TAC[reg_name_def] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
     BKP2AUX_mentions "asm_config_byte_offset" (concl th))) THEN
   ASM_SIMP_TAC[BKP2AUX_ile_0];
   UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
                asm_config_reg_count asm_conf` THEN ARITH_TAC]]);;

let BKP2AUX_p7_no_share = prove
 (`!dc wc (ac:(A)asm_config) p_data col p_word bm wc' fs p_stack sc dc' mh sp off.
     data_to_word_compile dc wc ac p_data = (col,p_word) /\
     word_to_stack_compile ac F p_word = (bm,wc',fs,p_stack)
     ==> no_share_mem_inst (stack_to_lab_compile sc dc' mh sp off p_stack)`,
  MESON_TAC[compile_no_share_mem_inst; compile_no_shmemop; compile_no_share_inst]);;

(* the lab_to_target step of the backend correctness proof *)
let BKP2AUX_lab_step = prove
 (`!asm_conf c prog bytes bitmaps c' syn mc ffi ms cbspace p_data col p_word bm wc fs p_stack lc
    tar_st m dm sdm.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c') /\
  backend_config_ok asm_conf c /\ mc_conf_ok (mc:(A,B,C)machine_config) /\
  asm_conf = target_config (machine_config_target mc) /\
  data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
    asm_conf p_data = (col,p_word) /\
  word_to_stack_compile asm_conf F p_word = (bm,wc,fs,p_stack) /\
  lab_to_target_compile asm_conf (backend_config_lab_conf c)
    (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
       (asm_config_addr_offset asm_conf) p_stack) = SOME (bytes,lc) /\
  backend_config_lab_conf c' = lc /\
  good_init_state mc ms bytes cbspace tar_st m dm sdm /\
  lab_to_target_config_ffi_names lc = SOME (machine_config_ffi_names mc) /\
  (!i. mmio_pcs_min_index (machine_config_ffi_names mc) = SOME i ==>
       MAP (\rec. val (target_get_pc (machine_config_target mc) ms) +
                  shmem_info_num_entry_pc rec) (lab_to_target_config_shmem_extra lc) =
       DROP i (MAP val (machine_config_ffi_entry_pcs mc)) /\
       machine_config_mmio_info mc =
       ZIP (list_of_seq (\index. index + i) (LENGTH (lab_to_target_config_shmem_extra lc)))
           (MAP (\rec. (shmem_info_num_nbytes rec,
                        Addr (shmem_info_num_addr_reg rec)
                             (word (shmem_info_num_addr_off rec)),
                        shmem_info_num_reg rec,
                        word_add (word (shmem_info_num_exit_pc rec))
                          (target_get_pc (machine_config_target mc) ms)))
                (lab_to_target_config_shmem_extra lc)) /\
       (cbspace + LENGTH bytes) + ffi_offset * (i + 3) < dimword(:A)) /\
  labels_ok (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
       (asm_config_addr_offset asm_conf) p_stack) /\
  ALL (sec_ok_pre asm_conf)
    (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
       (asm_config_addr_offset asm_conf) p_stack)
  ==> implements' T (machine_sem mc (ffi:(FFI)ffi_state) ms)
        {lab_semantics
           (lab_to_targetProof_make_init mc ffi tar_st m (dm INTER byte_aligned)
              (sdm INTER byte_aligned) ms
              (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
                 (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
                 (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
                 (asm_config_addr_offset asm_conf) p_stack)
              (lab_to_target_compile asm_conf)
              (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes)))
              cbspace
              (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o SND o config_tuple2)
                 (\ps. backend_progs_lab_prog ps)))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `asm_conf:(A)asm_config`
                          then SUBST_ALL_TAC th else failwith "") THEN
  ABBREV_TAC `p7 = stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
       (asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
        (LENGTH (asm_config_avoid_regs (target_config (machine_config_target (mc:(A,B,C)machine_config)))) + 3))
       (asm_config_addr_offset (target_config (machine_config_target (mc:(A,B,C)machine_config)))) p_stack` THEN
  SUBGOAL_THEN `no_share_mem_inst (p7:((A)sec)list)` ASSUME_TAC THENL
  [EXPAND_TAC "p7" THEN MATCH_MP_TAC BKP2AUX_p7_no_share THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mmio_pcs_min_index (machine_config_ffi_names (mc:(A,B,C)machine_config)) =
                SOME (LENGTH (machine_config_ffi_names mc))` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`; `backend_config_lab_conf c`; `filter_skip (p7:((A)sec)list)`;
                  `bytes:byte list`; `lc:lab_to_target_config`]
           compile_lab_no_share_mem_IMP_mmio_pcs_min_index) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[no_share_mem_filter_skip; GSYM lab_to_target_compile_def] THEN
    BKP2AUX_HDTM_ASSUM "backend_config_ok" (MP_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
    SIMP[];
    ASM_REWRITE_TAC[injectivity "option"] THEN MESON_TAC[]];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`mc:(A,B,C)machine_config`; `p7:((A)sec)list`; `cake_orac (target_config (machine_config_target (mc:(A,B,C)machine_config))) c' syn
                   (SND o SND o SND o SND o SND o SND o config_tuple2)
                   (\ps. backend_progs_lab_prog ps)`;
                 `lc:lab_to_target_config`; `bytes:byte list`; `target_config (machine_config_target (mc:(A,B,C)machine_config))`;
                 `backend_config_lab_conf c`; `ms:B`; `cbspace:num`; `tar_st:(A)asm_state`;
                 `m:A word->(A)word_loc`; `dm:A word->bool`; `sdm:A word->bool`;
                 `LENGTH (machine_config_ffi_names (mc:(A,B,C)machine_config))`;
                 `ffi:(FFI)ffi_state`] lab_to_targetProof_semantics_compile) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  BKP2AUX_HDTM_ASSUM "mmio_pcs_min_index" (fun mm ->
    BKP2AUX_ASSUM_MENTIONS "machine_config_mmio_info" (fun th ->
      STRIP_ASSUME_TAC (MP (SPEC `LENGTH (machine_config_ffi_names (mc:(A,B,C)machine_config))` th) mm))) THEN
  REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok"
    (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[compiler_oracle_ok_def] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`; `c:backend_config`; `prog:dec list`;
                   `bytes:byte list`; `bitmaps:(A word)list`; `c':backend_config`;
                   `syn:num->(num#num)#dec list`; `k:num`] BKP2AUX_lab_oracle_no_share) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`; `c:backend_config`; `prog:dec list`;
                   `bytes:byte list`; `bitmaps:(A word)list`; `c':backend_config`;
                   `syn:num->(num#num)#dec list`; `k:num`] good_code_lab_oracle) THEN
    SPEC_TAC(`cake_orac (target_config (machine_config_target (mc:(A,B,C)machine_config))) c' syn
                   (SND o SND o SND o SND o SND o SND o config_tuple2)
                   (\ps. backend_progs_lab_prog ps) k`,`q:lab_to_target_config#((A)sec)list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPECL [`p1:lab_to_target_config`; `p2:((A)sec)list`;
       `mc:(A,B,C)machine_config`]) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[cake_orac_0; config_tuple2_def; o_THM] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lab_to_target_compile (target_config (machine_config_target (mc:(A,B,C)machine_config))) (backend_config_lab_conf c) p7 = SOME (bytes,lc)` THEN
    REWRITE_TAC[lab_to_target_compile_def] THEN
    DISCH_THEN(MP_TAC o MATCH_MP compile_lab_LENGTH) THEN ASM_REWRITE_TAC[ADD_CLAUSES]];
   MATCH_MP_TAC to_lab_good_code_lemma THEN ASM_MESON_TAC[];
   REWRITE_TAC[no_install_or_no_share_mem_def] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP mmio_pcs_min_index_is_SOME) THEN
   REWRITE_TAC[GSYM ALL_EL] THEN MESON_TAC[];
   GEN_TAC THEN DISCH_TAC THEN
   UNDISCH_TAC `OPTION_ALL (ALL (\x. ?s. x = ExtCall s))
                  (lab_to_target_config_ffi_names (backend_config_lab_conf c))` THEN
   ASM_REWRITE_TAC[OPTION_ALL_def]]);;

(* the stackLang program satisfies stack_to_labProof's good_code *)
let BKP2AUX_good_code_p6 = prove
 (`!asm_conf c p_data col p_word bm wc fs p_stack.
  backend_config_ok (asm_conf:(A)asm_config) c /\ good_dimindex (:A) /\
  data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
    asm_conf p_data = (col,p_word) /\
  word_to_stack_compile asm_conf F p_word = (bm,wc,fs,p_stack) /\
  ALL (\n. data_num_stubs <= n) (MAP FST p_data) /\ ALL_DISTINCT (MAP FST p_data)
  ==> stack_to_labProof_good_code
        (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3)) p_stack`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`backend_config_data_conf c`; `backend_config_word_to_word_conf c`;
                 `asm_conf:(A)asm_config`; `p_data:(num#num#data_prog)list`]
          data_to_word_compile_conventions) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`backend_config_data_conf c`; `backend_config_word_to_word_conf c`;
                 `asm_conf:(A)asm_config`; `p_data:(num#num#data_prog)list`]
          data_to_word_compile_lab_pres) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p_word:(num#num#(A)wl_prog)list`; `asm_conf:(A)asm_config`]
          word_to_stack_compile_lab_pres) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `p_word:(num#num#(A)wl_prog)list`; `bm:(A word)list`;
                 `wc:word_to_stack_config`; `fs:num list`; `p_stack:(num#(A)stack_prog)list`;
                 `asm_config_reg_count (asm_conf:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs asm_conf))`]
          word_to_stack_stack_convs) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [BKP2AUX_ASSUM_MENTIONS "flat_exp_conventions" MP_TAC THEN
    REWRITE_TAC[ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN SIMP_TAC[];
    UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
                 asm_config_reg_count asm_conf` THEN ARITH_TAC];
   STRIP_TAC] THEN
  REWRITE_TAC[stack_to_labProof_good_code_def] THEN
  SUBGOAL_THEN `(asm_config_reg_count (asm_conf:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs asm_conf))) + 2 =
                asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
                asm_config_reg_count asm_conf` THEN ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BKP2AUX_data_names) THEN
  CONJ_TAC THENL
  [REWRITE_TAC[D2WPAUX_MAP_FST_stubs; ALL; ALL_APPEND; ALL_DISTINCT; ALL_DISTINCT_APPEND;
               MEM; MEM_APPEND; raise_stub_location_def; wl_store_consts_stub_location_def;
               word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
   X_GEN_TAC `e:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   POP_ASSUM MP_TAC THEN ARITH_TAC;
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVERY_FST_SND] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[D2WPAUX_MAP_FST_stubs; ALL; ALL_APPEND; raise_stub_location_def;
               wl_store_consts_stub_location_def; word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   UNDISCH_TAC `ALL (\n. data_num_stubs <= n) (MAP FST (p_data:(num#num#data_prog)list))` THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
   ARITH_TAC;
   BKP2AUX_ASSUM_MENTIONS "stack_extract_labels"
     (ACCEPT_TAC o CONV_RULE(TOP_DEPTH_CONV let_CONV))]);;

let BKP2AUX_val_bytes_in_word = prove
 (`good_dimindex(:A) ==> val (bytes_in_word:A word) = dimindex(:A) DIV 8`,
  REWRITE_TAC[good_dimindex_def; bytes_in_word_def] THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let BKP2AUX_heap_addresses = prove
 (`!(a:A word) b. good_dimindex (:A) /\ byte_aligned a /\ byte_aligned b /\ word_ule a b
  ==> {w | word_ule a w /\ word_ult w b} INTER byte_aligned =
      addresses a (val (word_sub b a) DIV (dimindex (:A) DIV 8))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:A word. byte_aligned w <=> val w MOD (dimindex(:A) DIV 8) = 0`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
  [ASM_MESON_TAC[STACKPROPSAUX_byte_aligned_val]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
  [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[addresses_thm; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `w:A word` THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [IN] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ULE]) THEN
  ASM_REWRITE_TAC[WORD_ULE; WORD_ULT] THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES] THEN
  SUBGOAL_THEN `!i. word_add a (word_mul (word i) bytes_in_word) =
                    word (val (a:A word) + i * (dimindex(:A) DIV 8)):A word`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[bytes_in_word_def; WORD_ADD; WORD_MUL; WORD_VAL]; ALL_TAC] THEN
  ABBREV_TAC `k = dimindex(:A) DIV 8` THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `val (a:A word) MOD k = 0` THEN UNDISCH_TAC `val (b:A word) MOD k = 0` THEN
  ASM_SIMP_TAC[MOD_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN DISCH_THEN(X_CHOOSE_TAC `A0:num`) THEN
  ASM_REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB] THEN
  SUBGOAL_THEN `((B - A0) * k) DIV k = B - A0` SUBST1_TAC THENL
  [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT]; ALL_TAC] THEN
  MP_TAC(ISPEC `b:A word` VAL_BOUND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EQ_TAC THENL
  [DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_TAC `V:num`)) THEN
   EXISTS_TAC `V - A0:num` THEN
   SUBGOAL_THEN `A0 <= V /\ V < B` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val (w:A word) = V * k`]) THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[LE_MULT_RCANCEL]; ASM_MESON_TAC[LT_MULT_RCANCEL]];
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `A0 * k + (V - A0) * k = V * k` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try lhs(concl th) = `val (w:A word)` with _ -> false)) THEN
   REWRITE_TAC[WORD_VAL];
   DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `A0 * k + i * k < B * k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN ASM_SIMP_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `val (w:A word) = A0 * k + i * k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ARITH_TAC; EXISTS_TAC `A0 + i:num` THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]]]);;

(* the memory assumption of stack_to_labProof for the initial labLang state *)
let BKP2AUX_mem_assumption = prove
 (`!names (bitmaps:(A word)list) data_sp (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
   tar_st m bitmap_ptr bitmaps_dm sdm ms code (comp:D->((A)sec)list->(byte list#D)option)
   cbspace coracle bytes.
  good_dimindex (:A) /\
  byte_aligned (asm_state_regs tar_st (tlookup names 2)) /\ byte_aligned (asm_state_regs tar_st (tlookup names 4)) /\ byte_aligned bitmap_ptr /\
  word_ule (asm_state_regs tar_st (tlookup names 2)) (asm_state_regs tar_st (tlookup names 4)) /\
  word_ule (word_mul (word 1024) bytes_in_word) (word_sub (asm_state_regs tar_st (tlookup names 4)) (asm_state_regs tar_st (tlookup names 2))) /\
  DISJOINT {w | word_ule (asm_state_regs tar_st (tlookup names 2)) w /\ word_ult w (asm_state_regs tar_st (tlookup names 4))} bitmaps_dm /\
  m (asm_state_regs tar_st (tlookup names 2)) = wl_Word bitmap_ptr /\
  m (word_add (asm_state_regs tar_st (tlookup names 2)) bytes_in_word) =
    wl_Word (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
  m (word_add (asm_state_regs tar_st (tlookup names 2)) (word_mul (word 2) bytes_in_word)) =
    wl_Word (word_add (word_add bitmap_ptr (word_mul bytes_in_word (word data_sp)))
              (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
  m (word_add (asm_state_regs tar_st (tlookup names 2)) (word_mul (word 3) bytes_in_word)) =
    wl_Word (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH (bytes:byte list)))) /\
  m (word_add (asm_state_regs tar_st (tlookup names 2)) (word_mul (word 4) bytes_in_word)) =
    wl_Word (word_add (word_add (target_get_pc (machine_config_target mc) ms) (word cbspace)) (word (LENGTH bytes))) /\
  (misc_word_list bitmap_ptr (MAP wl_Word bitmaps) STAR
   word_list_exists (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) data_sp)
    (fun2set (m,byte_aligned INTER bitmaps_dm))
  ==> memory_assumption names bitmaps data_sp
        (lab_to_targetProof_make_init mc ffi tar_st m (({w | word_ule (asm_state_regs tar_st (tlookup names 2)) w /\ word_ult w (asm_state_regs tar_st (tlookup names 4))} UNION bitmaps_dm) INTER byte_aligned)
           (sdm INTER byte_aligned) ms code comp
           (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes))) cbspace coracle)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[memory_assumption_def; lab_to_targetProof_make_init_def;
              (record_info "lab_state").ri_accessors; (record_info "buffer").ri_accessors] THEN
  MAP_EVERY EXISTS_TAC [`asm_state_regs (tar_st:(A)asm_state) (tlookup names 2)`; `asm_state_regs (tar_st:(A)asm_state) (tlookup names 3)`;
                        `asm_state_regs (tar_st:(A)asm_state) (tlookup names 4)`; `bitmap_ptr:A word`] THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN CONJ_TAC THENL
  [REWRITE_TAC[WORD_ADD_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `({w | word_ule (asm_state_regs (tar_st:(A)asm_state) (tlookup names 2)) w /\ word_ult w (asm_state_regs tar_st (tlookup names 4))} UNION bitmaps_dm) INTER byte_aligned =
                (byte_aligned INTER bitmaps_dm) UNION ({w | word_ule (asm_state_regs (tar_st:(A)asm_state) (tlookup names 2)) w /\ word_ult w (asm_state_regs tar_st (tlookup names 4))} INTER byte_aligned:A word->bool)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC fun2set_disjoint_union THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [UNDISCH_TAC `DISJOINT {w | word_ule (asm_state_regs (tar_st:(A)asm_state) (tlookup names 2)) w /\ word_ult w (asm_state_regs tar_st (tlookup names 4))} (bitmaps_dm:A word->bool)` THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC word_list_exists_imp THEN ASM_SIMP_TAC[BKP2AUX_heap_addresses] THEN
  ASM_SIMP_TAC[BKP2AUX_val_bytes_in_word] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_mul (word_neg (word 1)) a) b = word_sub b a:A word`] THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val (word_sub (asm_state_regs (tar_st:(A)asm_state) (tlookup names 4)) (asm_state_regs tar_st (tlookup names 2)):A word)` THEN
  REWRITE_TAC[DIV_MUL_LE; dimword_def; VAL_BOUND]);;

(* the stack_to_lab step of the backend correctness proof *)
let BKP2AUX_stack_step = prove
 (`!asm_conf c prog bytes bitmaps c' syn mc ffi ms cbspace data_sp p_stack tar_st m dm sdm s opt.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c') /\
  backend_config_ok asm_conf c /\ mc_conf_ok (mc:(A,B,C)machine_config) /\
  mc_init_ok asm_conf c mc /\ asm_conf = target_config (machine_config_target mc) /\
  full_make_init (backend_config_stack_conf c) (backend_config_data_conf c)
    (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1) (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
    (asm_config_addr_offset asm_conf) bitmaps p_stack
    (lab_to_targetProof_make_init mc (ffi:(FFI)ffi_state) tar_st m (dm INTER byte_aligned)
          (sdm INTER byte_aligned) ms
          (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
            (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
            (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
            (asm_config_addr_offset asm_conf) p_stack)
          (lab_to_target_compile asm_conf)
          (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes)))
          cbspace
          (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_lab_prog ps)))
    (set_of_list (machine_config_callee_saved_regs mc)) data_sp
    (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o SND o config_tuple2)
            (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))) = (s,opt) /\
  memory_assumption (stack_to_lab_config_reg_names (backend_config_stack_conf c)) bitmaps data_sp
    (lab_to_targetProof_make_init mc (ffi:(FFI)ffi_state) tar_st m (dm INTER byte_aligned)
          (sdm INTER byte_aligned) ms
          (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
            (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
            (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
            (asm_config_addr_offset asm_conf) p_stack)
          (lab_to_target_compile asm_conf)
          (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes)))
          cbspace
          (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_lab_prog ps))) /\
  stack_to_labProof_good_code (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3)) p_stack
  ==> ~(opt = NONE) /\
      (~(stack_semantics InitGlobals_location s = Fail)
       ==> lab_semantics (lab_to_targetProof_make_init mc (ffi:(FFI)ffi_state) tar_st m (dm INTER byte_aligned)
          (sdm INTER byte_aligned) ms
          (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
            (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
            (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
            (asm_config_addr_offset asm_conf) p_stack)
          (lab_to_target_compile asm_conf)
          (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH bytes)))
          cbspace
          (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_lab_prog ps))) =
           stack_semantics InitGlobals_location s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `asm_conf:(A)asm_config`
                          then SUBST_ALL_TAC th else failwith "") THEN
  BKP2AUX_HDTM_ASSUM "full_make_init" (fun th ->
    let l,r = dest_eq (concl th) in
    let args = snd (strip_comb l) in
    let s,opt = dest_pair r in
    MP_TAC (ISPECL (args @ [s; opt]) full_make_init_semantics2)) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lab_to_targetProof_make_init_def; (record_info "lab_state").ri_accessors; IN_INTER] THEN
  BKP2AUX_HDTM_ASSUM "mc_conf_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[mc_conf_ok_def]) THEN
  BKP2AUX_HDTM_ASSUM "mc_init_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[mc_init_ok_def]) THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [MP_TAC(ISPECL [`prog:dec list`; `bytes:byte list`; `bitmaps:(A word)list`; `c:backend_config`;
                  `stack_to_lab_config_reg_names (backend_config_stack_conf c)`;
                  `stack_to_lab_config_jump (backend_config_stack_conf c)`;
                  `asm_config_addr_offset (target_config (machine_config_target (mc:(A,B,C)machine_config)))`;
                  `asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
                     (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)`;
                  `target_config (machine_config_target (mc:(A,B,C)machine_config))`; `c':backend_config`;
                  `syn:num->(num#num)#dec list`;
                  `SND o SND o SND o SND o SND o SND o config_tuple2`] stack_to_lab_orac_eq_std_sym) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
   ASM_REWRITE_TAC[IN_SET_OF_LIST];
   REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[target_io_regs_callee_saved];
   REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[target_cc_regs_callee_saved];
   (* byte_aligned_MOD at the good_dimindex assumption (ASM_MESON_TAC: 12 s each) *)
   FIRST_ASSUM(fun th -> MESON_TAC[MATCH_MP byte_aligned_MOD th]);
   FIRST_ASSUM(fun th -> MESON_TAC[MATCH_MP byte_aligned_MOD th]);
   GEN_TAC THEN
   MP_TAC(ISPECL [`target_config (machine_config_target (mc:(A,B,C)machine_config))`; `c:backend_config`;
                  `prog:dec list`; `bytes:byte list`; `bitmaps:(A word)list`; `c':backend_config`;
                  `asm_config_reg_count (target_config (machine_config_target (mc:(A,B,C)machine_config))) -
                     (LENGTH (asm_config_avoid_regs (target_config (machine_config_target mc))) + 3)`;
                  `mc:(A,B,C)machine_config`; `syn:num->(num#num)#dec list`;
                  `SND o SND o SND o SND o SND o SND o config_tuple2`; `n:num`] oracle_stack_good_code) THEN
   ASM_REWRITE_TAC[];
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

let BKP2AUX_data_oracle_names = prove
 (`!asm_conf c prog b bm c' syn f n.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
     ==> ALL (\n. data_num_stubs <= n)
           (MAP FST (SND (cake_orac asm_conf c' syn (f:backend_config->B)
                            (\ps. backend_progs_data_prog ps) n)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM bvi_to_data_orac_eq; o_THM; SND_pure_co; bvi_to_dataProof_MAP_FST_compile_prog] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`syn:num->(num#num)#dec list`; `f:backend_config->B`; `n:num`] o
              MATCH_MP bvl_num_stubs_LE_bvi_prog) THEN
  MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
  ARITH_TAC);;

(* properties of the programs of the wordLang oracle *)
let BKP2AUX_word_oracle_props = prove
 (`!asm_conf c prog b bm c' syn n.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (b,bm,c')
  ==> (\((bm0,cfg),progs).
         ALL (post_alloc_conventions (asm_config_reg_count asm_conf -
                (5 + LENGTH (asm_config_avoid_regs asm_conf))) o SND o SND) progs /\
         ALL (flat_exp_conventions o SND o SND) progs /\
         ALL ((\y. ~(raise_stub_location = y)) o FST) progs /\
         ALL ((\y. ~(wl_store_consts_stub_location = y)) o FST) progs)
      (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
         (\ps. backend_progs_word_prog ps) n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prog:dec list`; `b:byte list`; `bm:(A word)list`; `c:backend_config`;
                  `asm_config_two_reg_arith (asm_conf:(A)asm_config)`;
                  `asm_config_reg_count (asm_conf:(A)asm_config) -
                     (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
                  `word_to_word_config_reg_alg (backend_config_word_to_word_conf c)`;
                  `ensure_fp_conf_ok (asm_conf:(A)asm_config) (backend_config_data_conf c)`;
                  `asm_conf:(A)asm_config`; `c':backend_config`; `syn:num->(num#num)#dec list`]
           data_to_word_orac_eq_sym_std) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `b:byte list`;
                 `bm:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`;
                 `SND o SND o SND o SND o SND o config_tuple2`; `n:num`] BKP2AUX_data_oracle_names) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM] THEN
  SPEC_TAC(`cake_orac (asm_conf:(A)asm_config) c' syn (SND o SND o SND o SND o SND o config_tuple2)
              (\ps. backend_progs_data_prog ps) n`,
           `q:(num#lab_to_target_config)#(num#num#data_prog)list`) THEN
  X_GEN_TAC `q:(num#lab_to_target_config)#(num#num#data_prog)list` THEN
  STRUCT_CASES_TAC (ISPEC `q:(num#lab_to_target_config)#(num#num#data_prog)list` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC (ISPEC `x:num#lab_to_target_config` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[pure_co_def; PAIR_MAP_THM; I_THM; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN DISCH_TAC THEN
  ABBREV_TAC `(pp0:(num#num#(A)wl_prog)list) = MAP (data_to_word_compile_part
                   (ensure_fp_conf_ok (asm_conf:(A)asm_config) (backend_config_data_conf c)))
                   (y:(num#num#data_prog)list)` THEN
  ABBREV_TAC `pp = MAP (\p. full_compile_single (asm_config_two_reg_arith (asm_conf:(A)asm_config))
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
       (word_to_word_config_reg_alg (backend_config_word_to_word_conf c)) asm_conf (p,NONE))
       (pp0:(num#num#(A)wl_prog)list)` THEN
  MP_TAC(ISPECL [`pp:(num#num#(A)wl_prog)list`; `asm_conf:(A)asm_config`;
                 `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
                 `word_to_word_config_reg_alg (backend_config_word_to_word_conf c)`;
                 `pp0:(num#num#(A)wl_prog)list`] MAP_full_compile_single_to_compile) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  BKP2AUX_HDTM_ASSUM "word_to_word_compile" (fun th ->
    let l,r = dest_eq(concl th) in
    let args = snd(strip_comb l) in
    let ign,pp = dest_pair r in
    MP_TAC (ISPECL [el 0 args; el 1 args; el 2 args; ign; pp] compile_to_word_conventions2)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pp0" THEN REWRITE_TAC[ALL_MAP] THEN
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; data_to_word_compile_part_def] THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[comp_no_share_inst; PAIR];
   STRIP_TAC] THEN
  SUBGOAL_THEN `MAP FST (pp:(num#num#(A)wl_prog)list) = MAP FST (y:(num#num#data_prog)list)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pp0" THEN
   REWRITE_TAC[MAP_MAP_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; data_to_word_compile_part_def; FST];
   ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\n. 62 <= n) (MAP FST (y:(num#num#data_prog)list))` ASSUME_TAC THENL
  [UNDISCH_TAC `ALL (\n. data_num_stubs <= n) (MAP FST (y:(num#num#data_prog)list))` THEN
   REWRITE_TAC[data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [BKP2AUX_ASSUM_MENTIONS "flat_exp_conventions" MP_TAC THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN SIMP_TAC[];
   BKP2AUX_ASSUM_MENTIONS "flat_exp_conventions" MP_TAC THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN SIMP_TAC[];
   REWRITE_TAC[GSYM ALL_MAP] THEN
   REWRITE_TAC[ASSUME `MAP FST (pp:(num#num#(A)wl_prog)list) = MAP FST (y:(num#num#data_prog)list)`] THEN
   REWRITE_TAC[raise_stub_location_def; word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   UNDISCH_TAC `ALL (\n. 62 <= n) (MAP FST (y:(num#num#data_prog)list))` THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[] THEN ARITH_TAC;
   REWRITE_TAC[GSYM ALL_MAP] THEN
   REWRITE_TAC[ASSUME `MAP FST (pp:(num#num#(A)wl_prog)list) = MAP FST (y:(num#num#data_prog)list)`] THEN
   REWRITE_TAC[wl_store_consts_stub_location_def; word_num_stubs_def; stack_num_stubs_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   UNDISCH_TAC `ALL (\n. 62 <= n) (MAP FST (y:(num#num#data_prog)list))` THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[] THEN ARITH_TAC]);;

(* the names of the wordLang program avoid the two wordLang stubs *)
let BKP2AUX_word_stub_names = prove
 (`!c (ac:(A)asm_config) p_data col p_word.
     data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
       ac p_data = (col,p_word) /\
     ALL (\n. data_num_stubs <= n) (MAP FST p_data)
     ==> ALOOKUP p_word raise_stub_location = NONE /\
         ALOOKUP p_word wl_store_consts_stub_location = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[(record_info "backend_config").ri_accfupds; K_THM]
   (ISPECL
    [`backend_config_word_to_word_conf c`; `ac:(A)asm_config`;
     `backend_config_data_conf_fupd
        (K (data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count (ac:(A)asm_config)))
             (data_to_word_config_has_fp_tern_fupd
               (K (asm_config_ISA ac = ARMv7 /\ 2 < asm_config_fp_reg_count ac))
               (backend_config_data_conf c)))) c`]
    data_to_word_names))) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[ALOOKUP_NONE; MEM_APPEND; D2WPAUX_MAP_FST_stubs; MEM;
    raise_stub_location_def; wl_store_consts_stub_location_def; word_num_stubs_def;
    stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP BKP2AUX_data_names) THEN
  MESON_TAC[ARITH_RULE `5 < 62 /\ 6 < 62`]);;

(* the word_to_stack step of the backend correctness proof *)
let BKP2AUX_word_step = prove
 (`!asm_conf c prog bytes bitmaps c' syn p_data col p_word wc fs p_stack
    (lab_st:(A,lab_to_target_config,FFI)lab_state) save_regs data_sp s opt.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c') /\
  backend_config_ok asm_conf c /\ good_dimindex (:A) /\
  data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
    asm_conf p_data = (col,p_word) /\
  ALL (\n. data_num_stubs <= n) (MAP FST p_data) /\
  word_to_stack_compile asm_conf F p_word = (bitmaps,wc,fs,p_stack) /\
  backend_config_word_conf c' = wc /\
  full_make_init (backend_config_stack_conf c) (backend_config_data_conf c)
    (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
    (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
    (asm_config_addr_offset asm_conf) bitmaps p_stack lab_st save_regs data_sp
    (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
       (SND o SND o SND o SND o SND o SND o config_tuple2)
       (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))) = (s,opt) /\
  ~(opt = NONE) /\
  ~(wl_semantics (word_to_stackProof_make_init asm_conf
        (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
        (fromAList p_word)
        (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
           (\ps. backend_progs_word_prog ps))) InitGlobals_location = Fail)
  ==> stack_semantics InitGlobals_location s IN
      extend_with_resource_limit'
        (word_lang_safe_for_space (word_to_stackProof_make_init asm_conf
           (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
           (fromAList p_word)
           (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
              (\ps. backend_progs_word_prog ps))) InitGlobals_location)
        {wl_semantics (word_to_stackProof_make_init asm_conf
           (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
           (fromAList p_word)
           (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
              (\ps. backend_progs_word_prog ps))) InitGlobals_location}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `xxx:(A,lab_to_target_config,FFI)stack_state` SUBST_ALL_TAC o
    REWRITE_RULE[GSYM IS_SOME_EQ_NOT_NONE; IS_SOME_EXISTS] o
    check (fun th -> concl th = `~(opt:((A,lab_to_target_config,FFI)stack_state)option = NONE)`)) THEN
  MP_TAC(ISPECL [`s:(A,lab_to_target_config,FFI)stack_state`; `asm_conf:(A)asm_config`;
   `p_word:(num#num#(A)wl_prog)list`;
   `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
   `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
      (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps)`;
   `InitGlobals_location`] word_to_stackProof_compile_semantics) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `stack_state_code (s:(A,lab_to_target_config,FFI)stack_state) = fromAList p_stack /\
                stack_state_bitmaps s = bitmaps` STRIP_ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "full_make_init" (MP_TAC o REWRITE_RULE[full_make_init_def]) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
   REWRITE_TAC[stack_allocProof_make_init_def; (record_info "stack_state").ri_accfupds; K_THM;
               make_init_any_bitmaps] THEN
   ASM_REWRITE_TAC[IS_SOME_DEF];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[IS_PREFIX_REFL; ARITH_RULE `a - (b + 5) = a - (5 + b)`] THEN
  MP_TAC(ISPECL [`c:backend_config`; `asm_conf:(A)asm_config`; `p_data:(num#num#data_prog)list`;
                 `col:(((num)spt)option)list`; `p_word:(num#num#(A)wl_prog)list`]
         BKP2AUX_word_stub_names) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
  [ALL_TAC;
   MP_TAC(ISPECL [`backend_config_data_conf c`; `backend_config_word_to_word_conf c`;
                  `asm_conf:(A)asm_config`; `p_data:(num#num#data_prog)list`]
          data_to_word_compile_conventions) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`asm_config_reg_count (asm_conf:(A)asm_config) - (5 + LENGTH (asm_config_avoid_regs asm_conf))`;
   `bitmaps:(A word)list`; `TL (bitmaps:(A word)list)`;
   `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
      (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps)`;
   `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
      (SND o SND o SND o SND o SND o SND o config_tuple2)
      (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))`;
   `asm_conf:(A)asm_config`; `backend_config_stack_conf c`; `backend_config_data_conf c`;
   `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
   `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3)`;
   `asm_config_addr_offset (asm_conf:(A)asm_config)`; `p_stack:(num#(A)stack_prog)list`;
   `lab_st:(A,lab_to_target_config,FFI)lab_state`; `save_regs:num->bool`; `data_sp:num`;
   `s:(A,lab_to_target_config,FFI)stack_state`; `xxx:(A,lab_to_target_config,FFI)stack_state`]
   IMP_init_state_ok) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `p_word:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`;
                 `wc:word_to_stack_config`; `(fs:num list,p_stack:(num#(A)stack_prog)list)`]
         compile_word_to_stack_bitmaps) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `LENGTH (asm_config_avoid_regs (asm_conf:(A)asm_config)) + 13 <=
                asm_config_reg_count asm_conf` THEN
   ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_mentions "list_CASE" (concl th))) THEN
   SPEC_TAC(`bitmaps:(A word)list`,`l:(A word)list`) THEN
   LIST_INDUCT_TAC THEN CASE_REWRITE_TAC[TL; CONS_11] THEN MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [X_GEN_TAC `n:num` THEN
   MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
                 `bitmaps:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`; `n:num`]
          BKP2AUX_word_oracle_props) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `?bm0 cfg progs. cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
       (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps) n =
       ((bm0,cfg),progs)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_mentions "cake_orac" (concl th) &&
                                           is_eq (concl th))) THEN
   REWRITE_TAC[cake_orac_0; config_tuple2_def; o_THM; PAIR_EQ] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP word_to_stack_orac_eq
     (CONJ (ASSUME `backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c')`)
           (ASSUME `stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F`))) THEN
  REWRITE_TAC[ARITH_RULE `a - (b + 5) = a - (5 + b)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* the first subterm of TM that applies the constant NAME to N arguments *)
let BKP2AUX_find_app name n tm =
  find_term (fun t -> try let h,args = strip_comb t in
                          fst(dest_const h) = name && length args = n
                      with Failure _ -> false) tm;;

(* name the components A and B of the first pair-valued subterm of the   *)
(* goal that applies the constant NAME to N arguments                     *)
let BKP2AUX_PAIR_SPLIT_TAC name n a b : tactic =
  W(fun (asl,w) ->
     let t = BKP2AUX_find_app name n w in
     let ty1,ty2 = dest_type (type_of t) |> (fun (_,l) -> hd l, hd (tl l)) in
     let va = mk_var(a,ty1) and vb = mk_var(b,ty2) in
     SUBGOAL_THEN (list_mk_exists([va;vb], mk_eq(t, mk_pair(va,vb)))) STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC]);;

let BKP2AUX_ALOOKUP_compile_part = prove
 (`!(dc:data_to_word_config) (p:(num#num#data_prog)list) n.
     ALOOKUP (MAP (data_to_word_compile_part dc:num#num#data_prog->num#num#(A)wl_prog) p) n =
     OPTION_MAP (\(a,q). (a + 1, FST (data_to_word_comp dc n 2 q):(A)wl_prog)) (ALOOKUP p n)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:num#num#data_prog`,`h:num#num#data_prog`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[data_to_word_compile_part_def; ALOOKUP_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* the dataLang and wordLang programs (the latter before word_to_word) are *)
(* related by data_to_word_gcProof's code_rel                               *)
let BKP2AUX_code_rel = prove
 (`!dc (p_data:(num#num#data_prog)list).
     ALL (\n. data_num_stubs <= n) (MAP FST p_data)
     ==> data_to_word_gcProof_code_rel dc (fromAList p_data)
           (fromAList (APPEND (data_to_word_stubs (:A) dc)
                              (MAP (data_to_word_compile_part dc) p_data)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_code_rel_def; domain_fromAList; lookup_fromAList; MAP_APPEND;
              SET_OF_LIST_APPEND; MAP_FST_MAP_compile_part] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[UNION_COMM];
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[ALOOKUP_APPEND] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_ALL_DISTINCT_MEM o
     CONJ (ISPECL [`(:A)`; `dc:data_to_word_config`] ALL_DISTINCT_MAP_FST_stubs)) THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE];
   REPEAT STRIP_TAC THEN REWRITE_TAC[ALOOKUP_APPEND] THEN
   SUBGOAL_THEN `ALOOKUP (data_to_word_stubs (:A) dc) n = NONE` SUBST1_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE] THEN DISCH_THEN(MP_TAC o MATCH_MP MAP_FST_stubs_bound) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (\n. data_num_stubs <= n) (MAP FST (p_data:(num#num#data_prog)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM] THEN
    MESON_TAC[FST; NOT_LE];
    ASM_REWRITE_TAC[option_CASE; BKP2AUX_ALOOKUP_compile_part; OPTION_MAP_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]]]);;

(* the registers 2, 3, 4 of the stack_names initial state *)
let BKP2AUX_names_regs = prove
 (`!f (v:num->B) i.
     BIJ (tlookup f) UNIV UNIV /\ (i = 2 \/ i = 3 \/ i = 4)
     ==> FLOOKUP (MAP_KEYS (LINV (tlookup f) UNIV)
                   (FEMPTY |++ MAP (\r. (r,v r)) (MAP (tlookup f) [2; 3; 4]))) i =
         SOME (v (tlookup f i))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BIJ_LINV_BIJ) THEN
  SUBGOAL_THEN `INJ (tlookup f) (:num) (:num) /\ INJ (LINV (tlookup f) (:num)) (:num) (:num)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[BIJ]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. LINV (tlookup f) (:num) (tlookup f x) = x` ASSUME_TAC THENL
  [ASM_MESON_TAC[LINV_DEF; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. tlookup f x = tlookup f y <=> x = y` ASSUME_TAC THENL
  [UNDISCH_TAC `INJ (tlookup f) (:num) (:num)` THEN REWRITE_TAC[INJ; IN_UNIV] THEN MESON_TAC[];
   ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM (SPEC `i:num` th)]) THEN
  ASM_SIMP_TAC[FLOOKUP_MAP_KEYS_MAPPED] THEN
  REWRITE_TAC[MAP; FUPDATE_LIST_THM; FLOOKUP_UPDATE] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN SUBST1_TAC)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* facts about the initial stackLang state when full_make_init succeeds *)
let BKP2AUX_fmi_SOME = prove
 (`!scc dc mh sp off (bitmaps:(A word)list) code (s4:(A,C,FFI)lab_state) save_regs data_sp
    coracle s xxx.
     full_make_init scc dc mh sp off bitmaps code s4 save_regs data_sp coracle = (s,SOME xxx) /\
     BIJ (tlookup (stack_to_lab_config_reg_names scc)) UNIV UNIV
     ==> stack_state_gc_fun s = word_gc_fun dc /\
         stack_state_be s = lab_state_be s4 /\
         stack_state_store s = stack_state_store xxx /\
         stack_state_stack s = stack_state_stack xxx /\
         init_prop (is_gen_gc (data_to_word_config_gc_kind dc)) mh data_sp
           (get_stack_heap_limit mh
              (theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 2)),
               theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 3)),
               theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 4)))) xxx`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_make_init_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> BKP2AUX_head_is "stack_allocProof_make_init" (concl th))) THEN
  REWRITE_TAC[stack_allocProof_make_init_def; (record_info "stack_state").ri_accfupds; K_THM] THEN
  REWRITE_TAC[make_init_any_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_head_is "make_init_opt" (concl th))) THEN
  W(fun (asl,w) ->
    let t = BKP2AUX_find_app "stack_namesProof_make_init" 4 w in
    SUBGOAL_THEN (subst [t,`s2:(A,C,FFI)stack_state`]
      `stack_state_be (s2:(A,C,FFI)stack_state) = lab_state_be (s4:(A,C,FFI)lab_state) /\
       read_pointers s2 =
         (theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 2)),
          theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 3)),
          theWord (lab_state_regs s4 (tlookup (stack_to_lab_config_reg_names scc) 4)))`)
      MP_TAC THENL
    [REWRITE_TAC[stack_namesProof_make_init_def; stack_to_labProof_make_init_def; read_pointers_def;
                 (record_info "stack_state").ri_accfupds; K_THM] THEN
     ASM_SIMP_TAC[BKP2AUX_names_regs; THE_DEF];
     SPEC_TAC(t,`s2:(A,C,FFI)stack_state`)]) THEN
  X_GEN_TAC `s2:(A,C,FFI)stack_state` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[make_init_opt_def] THEN
  BKP2AUX_PAIR_SPLIT_TAC "stack_evaluate" 1 "r" "t" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_evaluate_consts) THEN
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `rr:(A)stack_result` SUBST_ALL_TAC) SUBST_ALL_TAC
    (ISPEC `r:((A)stack_result)option` option_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[init_reduce_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[(record_info "stack_state").ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[]);;
let BKP2AUX_limits = prove
 (`!ggc mh data_sp w2 w3 w4 (xxx:(A,C,FFI)stack_state) (st:(A,C,FFI)stack_state) dc
    (ac:(A)asm_config) k code (coracle:num->(num#C)#(num#num#(A)wl_prog)list).
     init_prop ggc mh data_sp (get_stack_heap_limit mh (w2,w3,w4:A word)) xxx /\
     stack_state_store st = stack_state_store xxx /\
     stack_state_stack st = stack_state_stack xxx /\ good_dimindex (:A)
     ==> get_limits dc (word_to_stackProof_make_init ac k st code coracle) =
         compute_limits (data_to_word_config_len_size dc) (is_64_bits (:A))
           (data_to_word_config_has_fp_ops dc) (data_to_word_config_has_fp_tern dc)
           (get_stack_heap_limit mh (w2,w3,w4))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`get_stack_heap_limit mh (w2,w3,w4:A word)`,`shl:num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`sl:num`; `hl:num`] THEN
  REWRITE_TAC[init_prop_def; stack_heap_limit_ok_def] THEN STRIP_TAC THEN
  REWRITE_TAC[get_limits_def; compute_limits_def; is_64_bits_def; word_to_stackProof_make_init_def;
              (record_info "wl_state").ri_accessors] THEN
  ASM_REWRITE_TAC[DOMSUB_FAPPLY_THM; distinctness "store_name"] THEN
  SUBGOAL_THEN `FAPPLY (stack_state_store (xxx:(A,C,FFI)stack_state)) HeapLength =
                wl_Word (word_mul (word hl) bytes_in_word)` SUBST1_TAC THENL
  [UNDISCH_TAC `FLOOKUP (stack_state_store (xxx:(A,C,FFI)stack_state)) HeapLength =
                SOME (wl_Word (word_mul (word hl) bytes_in_word))` THEN
   REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ];
   ALL_TAC] THEN
  REWRITE_TAC[theWord_def; bytes_in_word_def; GSYM WORD_MUL] THEN
  SUBGOAL_THEN `val (word (hl * dimindex (:A) DIV 8):A word) = hl * dimindex (:A) DIV 8`
    SUBST1_TAC THENL
  [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_MESON_TAC[dimword_def]; ALL_TAC] THEN
  SUBGOAL_THEN `~(dimindex (:A) DIV 8 = 0)` ASSUME_TAC THENL
  [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT]);;
let BKP2AUX_names_target_regs = prove
 (`!names (t:(A,B,C)target) (ms:B) (tar_st:(A)asm_state) i.
     stack_names_names_ok names (asm_config_reg_count (target_config t))
       (asm_config_avoid_regs (target_config t)) /\
     LENGTH (asm_config_avoid_regs (target_config t)) + 13 <= asm_config_reg_count (target_config t) /\
     target_state_rel t tar_st ms /\ i < 13
     ==> asm_state_regs tar_st (tlookup names i) = target_get_reg t ms (tlookup names i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_names_names_ok_def; target_state_rel_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[GSYM ALL_MEM; MEM_GENLIST] THEN
  STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `i:num` THEN REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;
(* the compiler configuration of the data_to_word theorem is the one of   *)
(* the backend                                                             *)
let BKP2AUX_cc_eq = prove
 (`!asm_conf c mh bitmaps p_stack (s4:(A,lab_to_target_config,FFI)lab_state) save_regs data_sp
    stack_oracle s p_word word_oracle.
     backend_config_ok (asm_conf:(A)asm_config) c /\
     FST (full_make_init (backend_config_stack_conf c) (backend_config_data_conf c) mh
           (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
           (asm_config_addr_offset asm_conf) bitmaps p_stack s4 save_regs data_sp stack_oracle) = s /\
     lab_state_compile s4 = lab_to_target_compile asm_conf
     ==> backend_from_data_tuple_cc asm_conf c =
         (\cfg. OPTION_MAP (I ## MAP upper_w2w ## I) o
                (\conf progs.
                   wl_state_compile
                     (word_to_stackProof_make_init asm_conf
                        (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
                        s (fromAList p_word) word_oracle) conf
                     (MAP (\p. full_compile_single (asm_config_two_reg_arith asm_conf)
                                 (asm_config_reg_count asm_conf -
                                  (LENGTH (asm_config_avoid_regs asm_conf) + 5))
                                 (word_to_word_config_reg_alg (backend_config_word_to_word_conf c))
                                 asm_conf (p,NONE)) progs)) cfg o
                MAP (data_to_word_compile_part (backend_config_data_conf c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[backend_from_data_tuple_cc_def; FUN_EQ_THM; o_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP BKP2AUX_ensure_fp_id th]) THEN
  X_GEN_TAC `cfg:num#lab_to_target_config` THEN X_GEN_TAC `progs:(num#num#data_prog)list` THEN
  SUBGOAL_THEN `?a b. cfg = (a:num,b:lab_to_target_config)` STRIP_ASSUME_TAC THENL
  [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  REWRITE_TAC[word_to_stackProof_make_init_def; (record_info "wl_state").ri_accessors] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> BKP2AUX_mentions "full_make_init" (concl th))) THEN
  ASM_REWRITE_TAC[full_make_init_compile; o_THM; LET_DEF; LET_END_DEF;
                  ARITH_RULE `(a - (b + 3)) - 2 = a - (b + 5)`] THEN
  BKP2AUX_GEN_CONST_TAC "compile_word_to_stack" 5 THEN
  X_GEN_TAC `t:((num#(A)stack_prog)list#num list#((A word)app_list#num))` THEN
  SUBGOAL_THEN `?x y z. t = (x:(num#(A)stack_prog)list,y:num list,z:(A word)app_list#num)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[]);;
let BKP2AUX_w2s_make_init_fields = prove
 (`!(ac:(A)asm_config) k (t:(A,C,FFI)stack_state) code coracle.
     wl_state_handler (word_to_stackProof_make_init ac k t code coracle) = 0 /\
     wl_state_gc_fun (word_to_stackProof_make_init ac k t code coracle) = stack_state_gc_fun t /\
     wl_state_store (word_to_stackProof_make_init ac k t code coracle) =
       fdomsub (stack_state_store t) Handler /\
     wl_state_memory (word_to_stackProof_make_init ac k t code coracle) = stack_state_memory t /\
     wl_state_mdomain (word_to_stackProof_make_init ac k t code coracle) = stack_state_mdomain t /\
     wl_state_code_buffer (word_to_stackProof_make_init ac k t code coracle) =
       stack_state_code_buffer t /\
     wl_state_data_buffer (word_to_stackProof_make_init ac k t code coracle) =
       stack_state_data_buffer t /\
     wl_state_locals (word_to_stackProof_make_init ac k t code coracle) = insert 0 (wl_Loc 1 0) LN /\
     wl_state_stack (word_to_stackProof_make_init ac k t code coracle) = [] /\
     wl_state_termdep (word_to_stackProof_make_init ac k t code coracle) = 0 /\
     wl_state_code (word_to_stackProof_make_init ac k t code coracle) = code /\
     wl_state_be (word_to_stackProof_make_init ac k t code coracle) = stack_state_be t /\
     wl_state_stack_max (word_to_stackProof_make_init ac k t code coracle) = SOME 1 /\
     wl_state_locals_size (word_to_stackProof_make_init ac k t code coracle) = SOME 0 /\
     wl_state_stack_limit (word_to_stackProof_make_init ac k t code coracle) =
       LENGTH (stack_state_stack t) /\
     wl_state_compile_oracle (word_to_stackProof_make_init ac k t code coracle) = coracle /\
     wl_state_ffi (word_to_stackProof_make_init ac k t code coracle) = stack_state_ffi t`,
  REWRITE_TAC[word_to_stackProof_make_init_def; (record_info "wl_state").ri_accessors;
              wl_stack_size_def; ITLIST]);;
let BKP2AUX_MAP_FST_p_word = prove
 (`!c (ac:(A)asm_config) p_data col p_word.
     data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
       ac p_data = (col,p_word)
     ==> MAP FST p_word =
         APPEND (MAP FST (data_to_word_stubs (:A) (backend_config_data_conf c))) (MAP FST p_data)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_compile_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[(record_info "backend_config").ri_accfupds; K_THM]
   (ISPECL
    [`backend_config_word_to_word_conf c`; `ac:(A)asm_config`;
     `backend_config_data_conf_fupd
        (K (data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count (ac:(A)asm_config)))
             (data_to_word_config_has_fp_tern_fupd
               (K (asm_config_ISA ac = ARMv7 /\ 2 < asm_config_fp_reg_count ac))
               (backend_config_data_conf c)))) c`]
    data_to_word_names))) THEN
  REWRITE_TAC[D2WPAUX_MAP_FST_stubs]);;
let BKP2AUX_ALL_FST = prove
 (`!(P:A->bool) (l:(A#B)list). ALL P (MAP FST l) ==> ALL (\(n,x). P n) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  STRUCT_CASES_TAC (ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST] THEN ASM_MESON_TAC[]);;
(* the data_to_word step of the backend correctness proof *)
let BKP2AUX_data_step = prove
 (`!asm_conf c prog bytes bitmaps c' syn p_data col p_word p_stack
    (s4:(A,lab_to_target_config,FFI)lab_state) save_regs data_sp s xxx.
  backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c') /\
  backend_config_ok asm_conf c /\ good_dimindex (:A) /\
  data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
    asm_conf p_data = (col,p_word) /\
  ALL (\n. data_num_stubs <= n) (MAP FST p_data) /\
  full_make_init (backend_config_stack_conf c) (backend_config_data_conf c)
    (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
    (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
    (asm_config_addr_offset asm_conf) bitmaps p_stack s4 save_regs data_sp
    (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
       (SND o SND o SND o SND o SND o SND o config_tuple2)
       (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))) = (s,SOME xxx) /\
  lab_state_compile s4 = lab_to_target_compile asm_conf /\
  lab_state_be s4 = data_to_word_config_be (backend_config_data_conf c) /\
  ~(data_semantics (lab_state_ffi s4) (fromAList p_data)
      (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
         (\ps. backend_progs_data_prog ps))
      (backend_from_data_tuple_cc asm_conf c) zero_limits LN InitGlobals_location = Fail)
  ==> (data_lang_safe_for_space (lab_state_ffi s4) (fromAList p_data)
         (get_limits (backend_config_data_conf c)
            (word_to_stackProof_make_init asm_conf
               (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
               (fromAList p_word)
               (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
                  (\ps. backend_progs_word_prog ps))))
         (wl_state_stack_size
            (word_to_stackProof_make_init asm_conf
               (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
               (fromAList p_word)
               (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
                  (\ps. backend_progs_word_prog ps)))) InitGlobals_location /\
       ~(data_to_word_config_gc_kind (backend_config_data_conf c) = data_to_word_None)
       ==> word_lang_safe_for_space
             (word_to_stackProof_make_init asm_conf
                (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
                (fromAList p_word)
                (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
                   (\ps. backend_progs_word_prog ps))) InitGlobals_location) /\
      wl_semantics
        (word_to_stackProof_make_init asm_conf
           (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
           (fromAList p_word)
           (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
              (\ps. backend_progs_word_prog ps))) InitGlobals_location IN
      extend_with_resource_limit'
        (data_lang_safe_for_space (lab_state_ffi s4) (fromAList p_data)
           (get_limits (backend_config_data_conf c)
              (word_to_stackProof_make_init asm_conf
                 (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
                 (fromAList p_word)
                 (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
                    (\ps. backend_progs_word_prog ps))))
           (wl_state_stack_size
              (word_to_stackProof_make_init asm_conf
                 (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
                 (fromAList p_word)
                 (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
                    (\ps. backend_progs_word_prog ps)))) InitGlobals_location /\
         ~(data_to_word_config_gc_kind (backend_config_data_conf c) = data_to_word_None))
        {data_semantics (lab_state_ffi s4) (fromAList p_data)
           (cake_orac asm_conf c' syn (SND o SND o SND o SND o SND o config_tuple2)
              (\ps. backend_progs_data_prog ps))
           (backend_from_data_tuple_cc asm_conf c) zero_limits LN InitGlobals_location}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`word_to_stackProof_make_init (asm_conf:(A)asm_config)
     (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
     (s:(A,lab_to_target_config,FFI)stack_state)
     (fromAList p_word)
     (cake_orac asm_conf c' (syn:num->(num#num)#dec list) (SND o SND o SND o SND o SND o config_tuple2)
        (\ps. backend_progs_word_prog ps))`; `backend_config_data_conf c`;
    `fromAList (APPEND (data_to_word_stubs (:A) (backend_config_data_conf c))
                       (MAP (data_to_word_compile_part (backend_config_data_conf c)) p_data))`;
    `p_data:(num#num#data_prog)list`; `backend_from_data_tuple_cc (asm_conf:(A)asm_config) c`;
    `\conf progs. wl_state_compile (word_to_stackProof_make_init (asm_conf:(A)asm_config)
         (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
         (s:(A,lab_to_target_config,FFI)stack_state)
         (fromAList p_word)
         (cake_orac asm_conf c' (syn:num->(num#num)#dec list) (SND o SND o SND o SND o SND o config_tuple2)
            (\ps. backend_progs_word_prog ps))) conf
        (MAP (\p. full_compile_single (asm_config_two_reg_arith (asm_conf:(A)asm_config))
                    (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
                    (word_to_word_config_reg_alg (backend_config_word_to_word_conf c))
                    asm_conf (p,NONE)) progs)`;
    `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
       (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_data_prog ps)`;
    `(I ## MAP (data_to_word_compile_part (backend_config_data_conf c)
                  :num#num#data_prog->num#num#(A)wl_prog)) o
       cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
       (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_data_prog ps)`;
    `asm_config_two_reg_arith (asm_conf:(A)asm_config)`;
    `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
    `word_to_word_config_reg_alg (backend_config_word_to_word_conf c)`; `asm_conf:(A)asm_config`;
    `wl_state_stack_size (word_to_stackProof_make_init (asm_conf:(A)asm_config)
     (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
     (s:(A,lab_to_target_config,FFI)stack_state)
     (fromAList p_word)
     (cake_orac asm_conf c' (syn:num->(num#num)#dec list) (SND o SND o SND o SND o SND o config_tuple2)
        (\ps. backend_progs_word_prog ps)))`;
    `InitGlobals_location`] data_to_wordProof_compile_semantics) THEN
  REWRITE_TAC[BKP2AUX_w2s_make_init_fields] THEN
  BKP2AUX_HDTM_ASSUM "full_make_init" (ASSUME_TAC o REWRITE_RULE[FST] o
    AP_TERM `FST:(A,lab_to_target_config,FFI)stack_state#((A,lab_to_target_config,FFI)stack_state)option
                 ->(A,lab_to_target_config,FFI)stack_state`) THEN
  SUBGOAL_THEN `stack_state_ffi (s:(A,lab_to_target_config,FFI)stack_state) =
                lab_state_ffi (s4:(A,lab_to_target_config,FFI)lab_state)`
    SUBST1_TAC THENL
  [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[full_make_init_ffi]; ALL_TAC] THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  MP_TAC(ISPECL [`backend_config_stack_conf c`; `backend_config_data_conf c`;
    `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
    `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3)`;
    `asm_config_addr_offset (asm_conf:(A)asm_config)`; `bitmaps:(A word)list`;
    `p_stack:(num#(A)stack_prog)list`; `s4:(A,lab_to_target_config,FFI)lab_state`;
    `save_regs:num->bool`; `data_sp:num`;
    `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
       (SND o SND o SND o SND o SND o SND o config_tuple2)
       (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))`;
    `s:(A,lab_to_target_config,FFI)stack_state`; `xxx:(A,lab_to_target_config,FFI)stack_state`]
    BKP2AUX_fmi_SOME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_to_word_compile (backend_config_word_to_word_conf c) (asm_conf:(A)asm_config)
     (APPEND (data_to_word_stubs (:A) (backend_config_data_conf c))
             (MAP (data_to_word_compile_part (backend_config_data_conf c)) p_data)) = (col,p_word)`
    ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "data_to_word_compile" (MP_TAC o REWRITE_RULE[data_to_word_compile_def]) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[GSYM ensure_fp_conf_ok_def] THEN
   BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[MATCH_MP BKP2AUX_ensure_fp_id th]);
   ALL_TAC] THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`;
      `backend_config_data_conf c`; `s:(A,lab_to_target_config,FFI)stack_state`;
      `SOME (xxx:(A,lab_to_target_config,FFI)stack_state)`; `backend_config_stack_conf c`;
      `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3)`;
      `asm_config_addr_offset (asm_conf:(A)asm_config)`; `bitmaps:(A word)list`;
      `p_stack:(num#(A)stack_prog)list`; `s4:(A,lab_to_target_config,FFI)lab_state`;
      `save_regs:num->bool`; `data_sp:num`;
      `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
         (SND o SND o SND o SND o SND o SND o config_tuple2)
         (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))`] IMP_init_store_ok) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[lookup_insert];
    MATCH_MP_TAC BKP2AUX_code_rel THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`;
      `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`; `bitmaps:(A word)list`;
      `p_stack:(num#(A)stack_prog)list`; `s4:(A,lab_to_target_config,FFI)lab_state`;
      `save_regs:num->bool`; `data_sp:num`;
      `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
         (SND o SND o SND o SND o SND o SND o config_tuple2)
         (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))`;
      `s:(A,lab_to_target_config,FFI)stack_state`; `p_word:(num#num#(A)wl_prog)list`;
      `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
         (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps)`]
      BKP2AUX_cc_eq) THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC BKP2AUX_ALL_FST THEN
    MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
      `bitmaps:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`;
      `SND o SND o SND o SND o SND o config_tuple2`; `n:num`] BKP2AUX_data_oracle_names) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC code_rel_ext_word_to_word THEN
    MAP_EVERY EXISTS_TAC [`backend_config_word_to_word_conf c`; `col:(((num)spt)option)list`;
                          `asm_conf:(A)asm_config`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[domain_fromAList; MAP_APPEND; MAP_FST_MAP_compile_part] THEN
    BKP2AUX_HDTM_ASSUM "data_to_word_compile" (fun th -> REWRITE_TAC[MATCH_MP BKP2AUX_MAP_FST_p_word th]);
    BKP2AUX_HDTM_ASSUM "init_prop" (STRIP_ASSUME_TAC o REWRITE_RULE[init_prop_def]) THEN
    ASM_REWRITE_TAC[NOT_SUC];
    MP_TAC(ISPECL [`prog:dec list`; `bytes:byte list`; `bitmaps:(A word)list`; `c:backend_config`;
                   `asm_config_two_reg_arith (asm_conf:(A)asm_config)`;
                   `asm_config_reg_count (asm_conf:(A)asm_config) -
                      (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
                   `word_to_word_config_reg_alg (backend_config_word_to_word_conf c)`;
                   `ensure_fp_conf_ok (asm_conf:(A)asm_config) (backend_config_data_conf c)`;
                   `asm_conf:(A)asm_config`; `c':backend_config`; `syn:num->(num#num)#dec list`]
            data_to_word_orac_eq_sym_std) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[MATCH_MP BKP2AUX_ensure_fp_id th]) THEN
    REWRITE_TAC[pure_co_def];
    ONCE_REWRITE_TAC[semantics_zero_limits] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC[semantics_zero_limits] THEN REWRITE_TAC[]);;

let BKP2AUX_prim_ffi = prove
 (`!(ffi:(FFI)ffi_state) s0 env. THE (prim_sem_env ffi) = (s0,env) ==> state_ffi s0 = ffi`,
  REWRITE_TAC[prim_sem_env_eq; THE_DEF; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) && rhs (concl th) = `s0:(FFI)state`)) THEN
  REWRITE_TAC[(record_info "state").ri_accessors; (record_info "state").ri_accfupds; K_THM]);;

let BKP2AUX_bvl_to_bvi_start = prove
 (`!start c names prog s p l bl n1 n2 n3 nm.
     bvl_to_bvi_compile start c names prog = (s,p,l,bl,n1,n2,n3,nm) ==> s = InitGlobals_location`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_def] THEN
  BACKDEFAUX_PAIRARG_TAC THEN BACKDEFAUX_PAIRARG_TAC THEN BACKDEFAUX_PAIRARG_TAC THEN
  BACKDEFAUX_PAIRARG_TAC THEN BACKDEFAUX_PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_mentions "bvl_to_bvi_compile_prog" (concl th))) THEN
  REWRITE_TAC[bvl_to_bvi_compile_prog_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BACKDEFAUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;
let BKP2AUX_to_word_progs = prove
 (`!(asm_conf:(A)asm_config) c prog sc' p_flat cc' p_bvl names1 s p_bvi l bl n1 n2 n3 names2 col p_word.
  source_to_flat_compile (backend_config_source_conf c) (source_to_source_compile prog) =
    (sc',p_flat) /\
  clos_to_bvl_compile (backend_config_clos_conf c) (flat_to_clos_compile_prog p_flat) =
    (cc',p_bvl,names1) /\
  bvl_to_bvi_compile (clos_to_bvl_config_start cc') (backend_config_bvl_conf c) names1 p_bvl =
    (s,p_bvi,l,bl,n1,n2,n3,names2) /\
  data_to_word_compile (backend_config_data_conf c) (backend_config_word_to_word_conf c)
    asm_conf (bvi_to_data_compile_prog p_bvi) = (col,p_word)
  ==> FST (SND (to_data c prog)) = bvi_to_data_compile_prog p_bvi /\
      FST (SND (to_word asm_conf c prog)) = p_word`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    REWRITE_TAC[to_word_def; to_data_def; to_bvi_def; to_bvl_def; to_clos_def; to_flat_def] THEN
    BACKDEFAUX_LETS_RW_TAC (CONJUNCTS th @ [(record_info "backend_config").ri_accfupds; K_THM])));;
let BKP2AUX_stack_size = prove
 (`!(asm_conf:(A)asm_config) (s:(A,C,FFI)stack_state) p_word
    (coracle:num->(num#C)#(num#num#(A)wl_prog)list).
     wl_state_stack_size
       (word_to_stackProof_make_init asm_conf
          (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5)) s
          (fromAList p_word) coracle) =
     compute_stack_frame_sizes asm_conf p_word`,
  REWRITE_TAC[word_to_stackProof_make_init_def; (record_info "wl_state").ri_accessors;
              compute_stack_frame_sizes_thm] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `(a - b) - 5 = a - (b + 5)`]);;
(* the limits of the data_to_word theorem are the backend's read_limits *)
let BKP2AUX_limits_eq = prove
 (`!asm_conf c (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) tar_st m dm sdm ms
    (code:((A)sec)list) comp pc cbspace lab_oracle mh bitmaps p_stack save_regs data_sp
    stack_oracle s xxx k code' coracle.
     full_make_init (backend_config_stack_conf c) (backend_config_data_conf c) mh
       (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
       (asm_config_addr_offset asm_conf) bitmaps p_stack
       (lab_to_targetProof_make_init mc ffi tar_st m dm sdm ms code comp pc cbspace lab_oracle)
       save_regs data_sp stack_oracle = (s,SOME xxx) /\
     backend_config_ok asm_conf c /\ good_dimindex (:A) /\
     asm_conf = target_config (machine_config_target mc) /\
     target_state_rel (machine_config_target mc) tar_st ms /\
     mh = 2 * max_heap_limit (:A) (backend_config_data_conf c) - 1
     ==> get_limits (backend_config_data_conf c)
           (word_to_stackProof_make_init asm_conf k s code'
              (coracle:num->(num#lab_to_target_config)#(num#num#(A)wl_prog)list)) =
         compute_limits (data_to_word_config_len_size (backend_config_data_conf c)) (is_64_bits (:A))
           (data_to_word_config_has_fp_ops (backend_config_data_conf c))
           (data_to_word_config_has_fp_tern (backend_config_data_conf c))
           (backendProof_read_limits asm_conf c mc ms)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  BKP2AUX_HDTM_ASSUM "backend_config_ok" (STRIP_ASSUME_TAC o REWRITE_RULE[backend_config_ok_def]) THEN
  BKP2AUX_HDTM_ASSUM "full_make_init" (fun th ->
    let l,r = dest_eq (concl th) in
    let args = snd (strip_comb l) in
    let s,opt = dest_pair r in
    MP_TAC (ISPECL (args @ [s; rand opt]) BKP2AUX_fmi_SOME)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] BKP2AUX_limits) o
    check (fun th -> BKP2AUX_head_is "init_prop" (concl th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:(A,lab_to_target_config,FFI)stack_state`; `backend_config_data_conf c`;
     `asm_conf:(A)asm_config`; `k:num`; `code':(num#(A)wl_prog)spt`;
     `coracle:num->(num#lab_to_target_config)#(num#num#(A)wl_prog)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[backendProof_read_limits_def; lab_to_targetProof_make_init_def;
              (record_info "lab_state").ri_accessors; theWord_def] THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `asm_conf:(A)asm_config`
                          then SUBST_ALL_TAC th else failwith "") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  ASM_SIMP_TAC[ISPECL [`stack_to_lab_config_reg_names (backend_config_stack_conf c)`;
    `machine_config_target (mc:(A,B,C)machine_config)`; `ms:B`; `tar_st:(A)asm_state`]
    BKP2AUX_names_target_regs; ARITH_RULE `2 < 13 /\ 3 < 13 /\ 4 < 13`]);;

(* HOL4 line 3547 *)
let compile_correct' = prove
 (CASE_TERM
  `!asm_conf c prog bytes bitmaps c' ffi ev mc cbspace data_sp ms.
     backend_compile (asm_conf:(A)asm_config) (c:backend_config) prog = SOME (bytes,bitmaps,c')
   ==> let (s0,env) = THE (prim_sem_env (ffi:(FFI)ffi_state)) in
       let s = add_eval_state ev s0 in
       ~semantics_prog s env prog Fail /\
       backend_config_ok asm_conf c /\ mc_conf_ok mc /\ mc_init_ok asm_conf c mc /\
       opt_eval_config_wf asm_conf c' ev /\
       installed bytes cbspace bitmaps data_sp
         (lab_to_target_config_ffi_names (backend_config_lab_conf c'))
         (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf c))) mc
         (lab_to_target_config_shmem_extra (backend_config_lab_conf c')) ms
       ==> machine_sem (mc:(A,B,C)machine_config) ffi ms SUBSET
           extend_with_resource_limit'
             (backendProof_is_safe_for_space ffi asm_conf c prog
                (backendProof_read_limits asm_conf c mc ms))
             (semantics_prog s env prog)`,
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?s0 env. THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env)` STRIP_ASSUME_TAC THENL
  [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `target_config (machine_config_target (mc:(A,B,C)machine_config)) = asm_conf` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "mc_init_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[mc_init_ok_def] th]); ALL_TAC] THEN
  SUBGOAL_THEN `stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[backend_config_ok_def] th]);
   ALL_TAC] THEN
  SUBGOAL_THEN `backend_config_source_conf c = prim_src_config` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[backend_config_ok_def] th]);
   ALL_TAC] THEN
  BKP2AUX_HDTM_ASSUM "backend_compile" (STRIP_ASSUME_TAC o MATCH_MP BKP2AUX_compile_phases) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `bitmaps:(A word)list = bm`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `stack_to_lab_config_perf_calls (backend_config_stack_conf c) = F`])) THEN
  (FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP BKP2AUX_bvl_to_bvi_start o
    check (fun th -> BKP2AUX_head_is "bvl_to_bvi_compile" (concl th))) THEN
  MP_TAC(ISPECL [`ev:((backend_config)compiler_instance)option`; `s0:(FFI)state`; `env:(v)sem_env`;
    `prog:dec list`; `asm_conf:(A)asm_config`; `c:backend_config`; `bytes:byte list`;
    `bitmaps:(A word)list`; `c':backend_config`; `sc':source_to_flat_config`;
    `p_flat:flat_exp list`; `ffi:(FFI)ffi_state`] source_eval_to_flat_semantics) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[backend_config_ok_def] th]);
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `syn:num->(num#num)#dec list`) THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP BKP2AUX_prim_ffi th]))) THEN
  (ABBREV_TAC `sem2 = flat_semantics (mk_flat_install_conf (backend_from_flat_tuple_cc (asm_conf:(A)asm_config) c)
     (cake_orac asm_conf c' (syn:num->(num#num)#dec list) (SND o config_tuple1)
        (\ps. backend_progs_flat_prog ps))) (ffi:(FFI)ffi_state) p_flat` THEN
  SUBGOAL_THEN `~(sem2 = Fail)` ASSUME_TAC THENL
  [DISCH_THEN SUBST_ALL_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> BKP2AUX_head_is "semantics_prog" (concl th))) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `semantics_prog (add_eval_state (ev:((backend_config)compiler_instance)option) (s0:(FFI)state)) env prog = {sem2}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_SING; IN] THEN
   FIRST_ASSUM(MP_TAC o check (fun th -> BKP2AUX_head_is "semantics_prog" (concl th))) THEN
   MESON_TAC[semantics_prog_deterministic];
   ALL_TAC]) THEN
  (MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
    `bitmaps:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`; `ffi:(FFI)ffi_state`;
    `sc':source_to_flat_config`; `p_flat:flat_exp list`; `cc':clos_to_bvl_config`;
    `p_bvl:(num#num#bvl_exp)list`; `names1:(mlstring)spt`; `InitGlobals_location`;
    `p_bvi:(num#num#bvi_exp)list`; `l:(num#bvl_exp)spt`; `bl:(num#bvi_exp)spt`;
    `n1:num`; `n2:num`; `n3:num`; `names2:(mlstring)spt`; `zero_limits`; `LN:(num)spt`]
    BKP2AUX_flat_to_data) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (SUBGOAL_THEN `ALL (\n. data_num_stubs <= n) (MAP FST (bvi_to_data_compile_prog p_bvi)) /\
                ALL_DISTINCT (MAP FST (bvi_to_data_compile_prog p_bvi))` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[bvi_to_dataProof_MAP_FST_compile_prog] THEN
   MATCH_MP_TAC compile_distinct_names THEN
   MAP_EVERY EXISTS_TAC [`clos_to_bvl_config_start cc'`; `backend_config_bvl_conf c`;
     `names1:(mlstring)spt`; `p_bvl:(num#num#bvl_exp)list`; `InitGlobals_location`;
     `l:(num#bvl_exp)spt`; `bl:(num#bvi_exp)spt`; `n1:num`; `n2:num`;
     `(n3:num,names2:(mlstring)spt)`; `0`] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP compile_all_distinct_locs o
      check (fun th -> BKP2AUX_head_is "clos_to_bvl_compile" (concl th)));
    BKP2AUX_HDTM_ASSUM "backend_config_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[backend_config_ok_def] th]) THEN
    ARITH_TAC];
   ALL_TAC]) THEN
  (BKP2AUX_HDTM_X_ASSUM "installed" (MP_TAC o REWRITE_RULE[heap_regs_def; installed_def]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `tar_st:(A)asm_state` (X_CHOOSE_THEN `m:A word->(A)word_loc`
    (X_CHOOSE_THEN `bitmap_ptr:A word` (X_CHOOSE_THEN `bitmaps_dm:A word->bool`
    (X_CHOOSE_THEN `sdm:A word->bool` STRIP_ASSUME_TAC)))))) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `backend_config_lab_conf c' = lc`)) THEN
  ABBREV_TAC `lab_st = lab_to_targetProof_make_init (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
     tar_st m
     (({w | word_ule (asm_state_regs tar_st
                        (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2)) w /\
            word_ult w (asm_state_regs tar_st
                        (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4))}
       UNION bitmaps_dm) INTER byte_aligned)
     (sdm INTER byte_aligned) ms
     (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
        (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
        (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
        (asm_config_addr_offset asm_conf) p_stack)
     (lab_to_target_compile asm_conf)
     (word_add (target_get_pc (machine_config_target mc) ms) (word (LENGTH (bytes:byte list))))
     cbspace
     (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
        (SND o SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_lab_prog ps))` THEN
  SUBGOAL_THEN `lab_state_compile (lab_st:(A,lab_to_target_config,FFI)lab_state) =
                  lab_to_target_compile (asm_conf:(A)asm_config) /\
                lab_state_ffi lab_st = ffi /\
                lab_state_be lab_st = data_to_word_config_be (backend_config_data_conf c)`
    STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "lab_st" THEN
   REWRITE_TAC[lab_to_targetProof_make_init_def; (record_info "lab_state").ri_accessors] THEN
   BKP2AUX_HDTM_ASSUM "mc_init_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[mc_init_ok_def] th]);
   ALL_TAC] THEN
  SUBGOAL_THEN `?stack_st opt.
     full_make_init (backend_config_stack_conf c) (backend_config_data_conf c)
       (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
       (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
       (asm_config_addr_offset asm_conf) bitmaps p_stack lab_st
       (set_of_list (machine_config_callee_saved_regs (mc:(A,B,C)machine_config))) data_sp
       (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
          (SND o SND o SND o SND o SND o SND o config_tuple2)
          (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))) =
     (stack_st:(A,lab_to_target_config,FFI)stack_state,opt)` STRIP_ASSUME_TAC THENL
  [MESON_TAC[PAIR]; ALL_TAC]) THEN
  (SUBGOAL_THEN `good_dimindex (:A)` ASSUME_TAC THENL
  [BKP2AUX_HDTM_ASSUM "mc_conf_ok" (fun th -> REWRITE_TAC[REWRITE_RULE[mc_conf_ok_def] th]); ALL_TAC] THEN
  SUBGOAL_THEN `stack_to_labProof_good_code
     (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
     (p_stack:(num#(A)stack_prog)list)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`;
     `bvi_to_data_compile_prog p_bvi`; `col:(((num)spt)option)list`;
     `p_word:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`; `wc:word_to_stack_config`;
     `fs:num list`; `p_stack:(num#(A)stack_prog)list`] BKP2AUX_good_code_p6) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
    `bitmaps:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`;
    `mc:(A,B,C)machine_config`; `ffi:(FFI)ffi_state`; `ms:B`; `cbspace:num`; `data_sp:num`;
    `p_stack:(num#(A)stack_prog)list`; `tar_st:(A)asm_state`; `m:A word->(A)word_loc`;
    `{w | word_ule (asm_state_regs tar_st
                     (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2)) w /\
          word_ult w (asm_state_regs (tar_st:(A)asm_state)
                     (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4))}
       UNION bitmaps_dm`;
    `sdm:A word->bool`; `stack_st:(A,lab_to_target_config,FFI)stack_state`;
    `opt:((A,lab_to_target_config,FFI)stack_state)option`] BKP2AUX_stack_step) THEN
  ASM_REWRITE_TAC[]) THEN
  (ANTS_TAC THENL
  [MP_TAC(ISPECL [`stack_to_lab_config_reg_names (backend_config_stack_conf c)`;
     `bitmaps:(A word)list`; `data_sp:num`; `mc:(A,B,C)machine_config`; `ffi:(FFI)ffi_state`;
     `tar_st:(A)asm_state`; `m:A word->(A)word_loc`; `bitmap_ptr:A word`;
     `bitmaps_dm:A word->bool`; `sdm:A word->bool`; `ms:B`;
     `stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
        (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
        (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
        (asm_config_addr_offset asm_conf) p_stack`;
     `lab_to_target_compile (asm_conf:(A)asm_config)`; `cbspace:num`;
     `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
        (SND o SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_lab_prog ps)`;
     `bytes:byte list`] BKP2AUX_mem_assumption) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `xxx:(A,lab_to_target_config,FFI)stack_state` SUBST_ALL_TAC o
    REWRITE_RULE[GSYM IS_SOME_EQ_NOT_NONE; IS_SOME_EXISTS]) ASSUME_TAC)) THEN
  (MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
    `bitmaps:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`;
    `bvi_to_data_compile_prog p_bvi`; `col:(((num)spt)option)list`;
    `p_word:(num#num#(A)wl_prog)list`; `p_stack:(num#(A)stack_prog)list`;
    `lab_st:(A,lab_to_target_config,FFI)lab_state`;
    `set_of_list (machine_config_callee_saved_regs (mc:(A,B,C)machine_config))`; `data_sp:num`;
    `stack_st:(A,lab_to_target_config,FFI)stack_state`;
    `xxx:(A,lab_to_target_config,FFI)stack_state`] BKP2AUX_data_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `labels_ok (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
         (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
         (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
         (asm_config_addr_offset asm_conf) p_stack) /\
      ALL (sec_ok_pre asm_conf)
        (stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
         (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
         (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
         (asm_config_addr_offset asm_conf) p_stack)` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC BKP2AUX_syntax_p7 THEN
   MAP_EVERY EXISTS_TAC [`bvi_to_data_compile_prog p_bvi`; `col:(((num)spt)option)list`;
     `p_word:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`; `wc:word_to_stack_config`;
     `fs:num list`] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
    `bitmaps:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`;
    `mc:(A,B,C)machine_config`; `ffi:(FFI)ffi_state`; `ms:B`; `cbspace:num`;
    `bvi_to_data_compile_prog p_bvi`; `col:(((num)spt)option)list`;
    `p_word:(num#num#(A)wl_prog)list`; `bitmaps:(A word)list`; `wc:word_to_stack_config`;
    `fs:num list`; `p_stack:(num#(A)stack_prog)list`; `backend_config_lab_conf c'`;
    `tar_st:(A)asm_state`; `m:A word->(A)word_loc`;
    `{w | word_ule (asm_state_regs tar_st
                     (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2)) w /\
          word_ult w (asm_state_regs (tar_st:(A)asm_state)
                     (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4))}
       UNION bitmaps_dm`;
    `sdm:A word->bool`] BKP2AUX_lab_step) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`; `bytes:byte list`;
    `bitmaps:(A word)list`; `c':backend_config`; `syn:num->(num#num)#dec list`;
    `bvi_to_data_compile_prog p_bvi`; `col:(((num)spt)option)list`;
    `p_word:(num#num#(A)wl_prog)list`; `wc:word_to_stack_config`;
    `fs:num list`; `p_stack:(num#(A)stack_prog)list`;
    `lab_st:(A,lab_to_target_config,FFI)lab_state`;
    `set_of_list (machine_config_callee_saved_regs (mc:(A,B,C)machine_config))`; `data_sp:num`;
    `stack_st:(A,lab_to_target_config,FFI)stack_state`;
    `SOME (xxx:(A,lab_to_target_config,FFI)stack_state)`] BKP2AUX_word_step) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC) THEN
  (BKP2AUX_HDTM_ASSUM "good_init_state" (ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[good_init_state_def]) THEN
  SUBGOAL_THEN `backendProof_is_safe_for_space (ffi:(FFI)ffi_state) (asm_conf:(A)asm_config) c prog
                  (backendProof_read_limits asm_conf c (mc:(A,B,C)machine_config) ms) <=>
     data_lang_safe_for_space ffi (fromAList (bvi_to_data_compile_prog p_bvi))
       (get_limits (backend_config_data_conf c)
          (word_to_stackProof_make_init asm_conf
             (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
             (stack_st:(A,lab_to_target_config,FFI)stack_state) (fromAList p_word)
             (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps))))
       (wl_state_stack_size
          (word_to_stackProof_make_init asm_conf
             (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
             stack_st (fromAList p_word)
             (cake_orac asm_conf c' syn
                (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps))))
       InitGlobals_location /\
     ~(data_to_word_config_gc_kind (backend_config_data_conf c) = data_to_word_None)`
    SUBST1_TAC THENL
  [REWRITE_TAC[backendProof_is_safe_for_space_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`;
     `sc':source_to_flat_config`; `p_flat:flat_exp list`; `cc':clos_to_bvl_config`;
     `p_bvl:(num#num#bvl_exp)list`; `names1:(mlstring)spt`; `InitGlobals_location`;
     `p_bvi:(num#num#bvi_exp)list`; `l:(num#bvl_exp)spt`; `bl:(num#bvi_exp)spt`;
     `n1:num`; `n2:num`; `n3:num`; `names2:(mlstring)spt`; `col:(((num)spt)option)list`;
     `p_word:(num#num#(A)wl_prog)list`] BKP2AUX_to_word_progs) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[BKP2AUX_stack_size] THEN
   MP_TAC(ISPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `mc:(A,B,C)machine_config`;
     `ffi:(FFI)ffi_state`; `tar_st:(A)asm_state`; `m:A word->(A)word_loc`;
     `({w | word_ule (asm_state_regs tar_st
                     (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 2)) w /\
          word_ult w (asm_state_regs (tar_st:(A)asm_state)
                     (tlookup (stack_to_lab_config_reg_names (backend_config_stack_conf c)) 4))}
       UNION bitmaps_dm) INTER byte_aligned`;
     `(sdm:A word->bool) INTER byte_aligned`; `ms:B`;
     `stack_to_lab_compile (backend_config_stack_conf c) (backend_config_data_conf c)
        (2 * max_heap_limit (:A) (backend_config_data_conf c) - 1)
        (asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 3))
        (asm_config_addr_offset asm_conf) p_stack`;
     `lab_to_target_compile (asm_conf:(A)asm_config)`;
     `word_add (target_get_pc (machine_config_target (mc:(A,B,C)machine_config)) ms)
        (word (LENGTH (bytes:byte list)))`;
     `cbspace:num`;
     `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
        (SND o SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_lab_prog ps)`;
     `2 * max_heap_limit (:A) (backend_config_data_conf c) - 1`; `bitmaps:(A word)list`;
     `p_stack:(num#(A)stack_prog)list`;
     `set_of_list (machine_config_callee_saved_regs (mc:(A,B,C)machine_config))`; `data_sp:num`;
     `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
        (SND o SND o SND o SND o SND o SND o config_tuple2)
        (\ps. (backend_progs_stack_prog ps,backend_progs_cur_bm ps))`;
     `stack_st:(A,lab_to_target_config,FFI)stack_state`;
     `xxx:(A,lab_to_target_config,FFI)stack_state`;
     `asm_config_reg_count (asm_conf:(A)asm_config) - (LENGTH (asm_config_avoid_regs asm_conf) + 5)`;
     `fromAList (p_word:(num#num#(A)wl_prog)list)`;
     `cake_orac (asm_conf:(A)asm_config) c' (syn:num->(num#num)#dec list)
        (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps)`]
     BKP2AUX_limits_eq) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
   ALL_TAC]) THEN
  (MATCH_MP_TAC BKP2AUX_compose THEN
  MAP_EVERY EXISTS_TAC [`lab_semantics (lab_st:(A,lab_to_target_config,FFI)lab_state)`;
    `stack_semantics InitGlobals_location (stack_st:(A,lab_to_target_config,FFI)stack_state)`;
    `wl_semantics (word_to_stackProof_make_init (asm_conf:(A)asm_config)
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
       (stack_st:(A,lab_to_target_config,FFI)stack_state) (fromAList p_word)
       (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
          (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps)))
       InitGlobals_location`;
    `word_lang_safe_for_space (word_to_stackProof_make_init (asm_conf:(A)asm_config)
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs asm_conf) + 5))
       (stack_st:(A,lab_to_target_config,FFI)stack_state) (fromAList p_word)
       (cake_orac asm_conf c' (syn:num->(num#num)#dec list)
          (SND o SND o SND o SND o SND o config_tuple2) (\ps. backend_progs_word_prog ps)))
       InitGlobals_location`] THEN
  ASM_REWRITE_TAC[]));;

(* HOL4 line 4429: compile_correct' |> Q.INST [`ev` |-> `NONE`] |>         *)
(* SIMP_RULE bool_ss [add_eval_state_def, opt_eval_config_wf_def], stated   *)
(* with the simplification made by hand (the let s = s0 reduced)             *)
let compile_correct_no_eval = prove
 (CASE_TERM
  `!asm_conf c prog bytes bitmaps c' ffi mc cbspace data_sp ms.
     backend_compile (asm_conf:(A)asm_config) (c:backend_config) prog = SOME (bytes,bitmaps,c')
   ==> let (s0,env) = THE (prim_sem_env (ffi:(FFI)ffi_state)) in
       ~semantics_prog s0 env prog Fail /\
       backend_config_ok asm_conf c /\ mc_conf_ok mc /\ mc_init_ok asm_conf c mc /\
       installed bytes cbspace bitmaps data_sp
         (lab_to_target_config_ffi_names (backend_config_lab_conf c'))
         (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf c))) mc
         (lab_to_target_config_shmem_extra (backend_config_lab_conf c')) ms
       ==> machine_sem (mc:(A,B,C)machine_config) ffi ms SUBSET
           extend_with_resource_limit'
             (backendProof_is_safe_for_space ffi asm_conf c prog
                (backendProof_read_limits asm_conf c mc ms))
             (semantics_prog s0 env prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`asm_conf:(A)asm_config`; `c:backend_config`; `prog:dec list`;
                `bytes:byte list`; `bitmaps:(A word)list`; `c':backend_config`;
                `ffi:(FFI)ffi_state`; `NONE:((backend_config)compiler_instance)option`;
                `mc:(A,B,C)machine_config`; `cbspace:num`; `data_sp:num`; `ms:B`]
          compile_correct') THEN
  ASM_REWRITE_TAC[add_eval_state_def; opt_eval_config_wf_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 4433 *)
let backendProof_compile_correct = prove
 (CASE_TERM
  `!asm_conf c prog bytes bitmaps c' ffi mc cbspace data_sp ms.
     backend_compile (asm_conf:(A)asm_config) (c:backend_config) prog = SOME (bytes,bitmaps,c')
   ==> let (s,env) = THE (prim_sem_env (ffi:(FFI)ffi_state)) in
       ~semantics_prog s env prog Fail /\
       backend_config_ok asm_conf c /\ mc_conf_ok mc /\ mc_init_ok asm_conf c mc /\
       installed bytes cbspace bitmaps data_sp
         (lab_to_target_config_ffi_names (backend_config_lab_conf c'))
         (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf c))) mc
         (lab_to_target_config_shmem_extra (backend_config_lab_conf c')) ms
       ==> machine_sem (mc:(A,B,C)machine_config) ffi ms SUBSET
           extend_with_resource_limit (semantics_prog s env prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL compile_correct_no_eval) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?s0 env. THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  MATCH_MP_TAC(SET_RULE `(t:behaviour->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  REWRITE_TAC[extend_with_resource_limit'_SUBSET]);;

(* HOL4 line 4451 *)
let semantics_prog_sing = prove
 (`!s env prog.
     ?x. semantics_prog (s:(FFI)state) env prog = {x}`,
  REWRITE_TAC[EXTENSION; IN_SING] THEN REWRITE_TAC[IN] THEN
  MESON_TAC[semantics_prog_total; semantics_prog_deterministic]);;

(* HOL4 line 4459 *)
let compile_correct_is_safe_for_space = prove
 (CASE_TERM
  `!asm_conf c prog bytes bitmaps c' ffi stack_limit heap_limit mc ms cbspace data_sp.
     backend_compile (asm_conf:(A)asm_config) (c:backend_config) prog = SOME (bytes,bitmaps,c')
   ==> backendProof_is_safe_for_space (ffi:(FFI)ffi_state) asm_conf c prog
         (stack_limit,heap_limit)
   ==> backendProof_read_limits asm_conf c (mc:(A,B,C)machine_config) ms =
         (stack_limit,heap_limit)
   ==> let (s,env) = THE (prim_sem_env ffi) in
       ~semantics_prog s env prog Fail /\
       backend_config_ok asm_conf c /\ mc_conf_ok mc /\ mc_init_ok asm_conf c mc /\
       installed bytes cbspace bitmaps data_sp
         (lab_to_target_config_ffi_names (backend_config_lab_conf c'))
         (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf c))) mc
         (lab_to_target_config_shmem_extra (backend_config_lab_conf c')) ms
       ==> machine_sem mc ffi ms = semantics_prog s env prog`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC_ALL compile_correct_no_eval) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?s0 env. THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  ASM_REWRITE_TAC[extend_with_resource_limit'_def] THEN
  X_CHOOSE_THEN `x:behaviour` SUBST1_TAC
    (ISPECL [`s0:(FFI)state`; `env:(v)sem_env`; `prog:dec list`] semantics_prog_sing) THEN
  X_CHOOSE_TAC `y:behaviour`
    (INST [`ffi:(FFI)ffi_state`,`st:(FFI)ffi_state`] machine_sem_total) THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_SING] THEN REWRITE_TAC[IN] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4482 (the EvalOracle case is unspecified, as in HOL4) *)
let the_EvalDecs_def = cake_def
  `the_EvalDecs (EvalDecs x) = x`;;

(* HOL4 line 4486 *)
let compile_correct_eval = prove
 (CASE_TERM
  `!asm_conf c prog bytes bitmaps c' ffi ev mc cbspace data_sp ms.
     backend_compile (asm_conf:(A)asm_config) c prog = SOME (bytes,bitmaps,c')
   ==> let (s0,env) = THE (prim_sem_env (ffi:(FFI)ffi_state)) in
       ~semantics_prog (add_eval_state ev s0) env prog Fail /\
       backend_config_ok asm_conf c /\
       mc_conf_ok mc /\ mc_init_ok asm_conf c mc /\ opt_eval_config_wf asm_conf c' ev /\
       installed bytes cbspace bitmaps data_sp
         (lab_to_target_config_ffi_names (backend_config_lab_conf c'))
         (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf c)))
         (mc:(A,B,C)machine_config)
         (lab_to_target_config_shmem_extra (backend_config_lab_conf c')) ms
       ==> machine_sem mc ffi ms SUBSET
           extend_with_resource_limit (semantics_prog (add_eval_state ev s0) env prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL compile_correct') THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?s0 env. THE (prim_sem_env (ffi:(FFI)ffi_state)) = (s0,env)`
   STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  MATCH_MP_TAC(SET_RULE `(t:behaviour->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  REWRITE_TAC[extend_with_resource_limit'_SUBSET]);;
