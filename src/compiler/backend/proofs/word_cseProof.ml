(* ========================================================================= *)
(* word_cseProof: port of HOL4 compiler/backend/proofs/word_cseProofScript.sml *)
(* (CakeML v3479).                                                           *)
(* Correctness proof for word_cse.                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang, wordSem and wordProps are those of their files  *)
(*   (wl_evaluate, wl_get_var, wl_state_locals, ...); the knowledge record  *)
(*   of word_cse has the fields knowledge_to_canonical, ..., and HOL4       *)
(*   data with f := v is knowledge_f_fupd (K v) data.  A multi-field update *)
(*   nests its fupds with the first field outermost, as in word_cse.ml.     *)
(* - HOL4 wf_data (:'a) data: the itself argument is a set (u:A->bool),     *)
(*   applied to (:A).  HOL4 () is one.                                      *)
(* - comp_correct (word_cseProof_comp_correct) is proved by induction with  *)
(*   wl_evaluate_ind, one local tactic per clause of evaluate (the HOL4     *)
(*   suspend/Resume cases); word_cse_wf_data and the syntactic convention   *)
(*   theorems by induction with word_cse_ind.  WPROOF1AUX_CSE_ names are     *)
(*   local helpers.                                                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/word_cse.ml";;
needs "hol4/alist.ml";;
needs "hol4/toto.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;

type_invention_error := true;;

let in_names_set_def = cake_def
  `in_names_set (a:(A)asm_arith) (tc:num spt) <=>
     ALL (\r. lookup r tc = SOME r) (arithReads a)`;;

let wf_data_def = cake_def
  `wf_data (u:A->bool) (data:knowledge) <=>
     (!r v. lookup r (knowledge_to_canonical data) = SOME v ==>
            lookup v (knowledge_to_canonical data) = SOME v /\ ODD r /\ ODD v) /\
     (!r v. lookup r (knowledge_to_latest data) = SOME v ==>
            r IN domain (knowledge_to_canonical data) /\
            v IN domain (knowledge_to_canonical data)) /\
     (!k v. balanced_map_lookup listCmp k (knowledge_instrs_mem data) = SOME v ==>
            lookup v (knowledge_to_canonical data) = SOME v) /\
     (!(a:(A)asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (asm_Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        in_names_set a (knowledge_to_canonical data) /\ can_mem_arith a) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==>
        lookup src (knowledge_to_canonical data) = SOME src) /\
     (!x v. ALOOKUP (knowledge_gets_mem data) x = SOME v ==>
            lookup v (knowledge_to_canonical data) = SOME v) /\
     ALL_DISTINCT (MAP FST (knowledge_gets_mem data)) /\
     balanced_map_invariant listCmp (knowledge_instrs_mem data) /\
     (!k v. balanced_map_lookup listCmp k (knowledge_loads_mem data) = SOME v ==>
            lookup v (knowledge_to_canonical data) = SOME v) /\
     (!op a (ofs:A word) v.
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==>
        lookup a (knowledge_to_canonical data) = SOME a) /\
     balanced_map_invariant listCmp (knowledge_loads_mem data)`;;

let sem_inv_def = cake_def
  `sem_inv (data:knowledge) (s:(A,C,FFI)wl_state) <=>
     (!r v. lookup r (knowledge_to_canonical data) = SOME v ==>
            wl_get_var r s = wl_get_var v s) /\
     (!r v. lookup r (knowledge_to_latest data) = SOME v ==>
            wl_get_var r s = wl_get_var v s) /\
     (!n c v.
        balanced_map_lookup listCmp (instToNumList (asm_Const n c:(A)inst))
          (knowledge_instrs_mem data) = SOME v ==>
        lookup v (wl_state_locals s) = SOME (wl_Word c)) /\
     (!(a:(A)asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (asm_Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        ?w. wl_get_var v s = SOME w /\
            wl_evaluate (wl_Inst (asm_Arith a), s) =
            (NONE, wl_set_var (firstRegOfArith a) w s)) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==>
        ?w. wl_word_exp s (wl_Op op [wl_Var src; Lookup CurrHeap]) = SOME w /\
            wl_get_var v s = SOME w) /\
     (!l v. balanced_map_lookup listCmp [48; l] (knowledge_instrs_mem data) = SOME v ==>
            lookup v (wl_state_locals s) = SOME (wl_Loc l 0)) /\
     (!x v. ALOOKUP (knowledge_gets_mem data) x = SOME v ==>
            ?w. FLOOKUP (wl_state_store s) x = SOME w /\ wl_get_var v s = SOME w) /\
     (!op a ofs v.
        ~is_store op /\
        balanced_map_lookup listCmp (loadToNumList op a (ofs:A word))
          (knowledge_loads_mem data) = SOME v ==>
        ?w. wl_get_var v s = SOME w /\
            !r. wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s) =
                (NONE, wl_set_var r w s))`;;

let data_inv_def = cake_def
  `data_inv (data:knowledge) (s:(A,C,FFI)wl_state) <=>
     wf_data (:A) data /\ sem_inv data s`;;

(* ------------------------------------------------------------------------- *)
(* Local helpers (WPROOF1AUX_CSE_ names)                                      *)
(* ------------------------------------------------------------------------- *)

(* the clause of wl_evaluate_def for the constructor named c *)

let WPROOF1AUX_CSE_eval_clause (c:string) =
  find (fun th -> let l = lhs (snd (strip_forall (concl th))) in
                  let p = fst (dest_pair (rand l)) in
                  fst (dest_const (fst (strip_comb p))) = c)
       (CONJUNCTS wl_evaluate_def);;

let canonicalRegs_correct = prove
 (`!data r (s:(A,C,FFI)wl_state).
     data_inv data s ==> wl_get_var (canonicalRegs data r) s = wl_get_var r s`,
  REWRITE_TAC[data_inv_def; sem_inv_def; canonicalRegs_def; lookup_any_def] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `lookup r (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;
let _ = cake_add_simps [canonicalRegs_correct];;

let canonicalRegs'_correct = prove
 (`!a data r (s:(A,C,FFI)wl_state).
     data_inv data s ==> wl_get_var (canonicalRegs' a data r) s = wl_get_var r s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[canonicalRegs'_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[canonicalRegs_correct]);;
let _ = cake_add_simps [canonicalRegs'_correct];;

let canonicalRegs_correct_bis = prove
 (`!data r (s:(A,C,FFI)wl_state).
     data_inv data s ==>
     lookup (canonicalRegs data r) (wl_state_locals s) = lookup r (wl_state_locals s)`,
  REWRITE_TAC[GSYM wl_get_var_def] THEN REWRITE_TAC[canonicalRegs_correct]);;
let _ = cake_add_simps [canonicalRegs_correct_bis];;

let canonicalArith_correct = prove
 (`!data (s:(A,C,FFI)wl_state) a.
     data_inv data s ==>
     wl_inst (asm_Arith (canonicalArith data a)) s = wl_inst (asm_Arith a) s`,
  REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  REWRITE_TAC[canonicalArith_def; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; the_words_def; MAP; wl_get_vars_def;
              LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[canonicalRegs_correct; canonicalRegs'_correct] THEN
  TRY(MP_TAC(ISPEC `a3:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[canonicalImmReg'_def] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[wl_word_exp_def] THEN ASM_SIMP_TAC[canonicalRegs'_correct]));;
let _ = cake_add_simps [canonicalArith_correct];;

let wordToNum_unique = prove
 (`!c1 c2:A word. wordToNum c1 = wordToNum c2 <=> c1 = c2`,
  REWRITE_TAC[wordToNum_def; VAL_EQ]);;
let _ = cake_add_simps [wordToNum_unique];;

let arithOpToNum_eq = prove
 (`!op1 op2. arithOpToNum op1 = arithOpToNum op2 <=> op1 = op2`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `op1:binop` (cases "binop")) THEN
  STRUCT_CASES_TAC (ISPEC `op2:binop` (cases "binop")) THEN
  REWRITE_TAC[arithOpToNum_def] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP[]);;
let _ = cake_add_simps [arithOpToNum_eq];;

let memOpToNum_eq = prove
 (`!op1 op2. memOpToNum op1 = memOpToNum op2 <=> op1 = op2`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `op1:memop` (cases "memop")) THEN
  STRUCT_CASES_TAC (ISPEC `op2:memop` (cases "memop")) THEN
  REWRITE_TAC[memOpToNum_def] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP[]);;
let _ = cake_add_simps [memOpToNum_eq];;

let firstRegOfArith_canonicalArith = prove
 (`!data a:(A)asm_arith. firstRegOfArith (canonicalArith data a) = firstRegOfArith a`,
  GEN_TAC THEN MATCH_MP_TAC asm_arith_INDUCT THEN
  REWRITE_TAC[canonicalArith_def; firstRegOfArith_def]);;
let _ = cake_add_simps [firstRegOfArith_canonicalArith];;

let data_inv_locals = prove
 (`!s:(A,C,FFI)wl_state. wl_state_locals_fupd (K (wl_state_locals s)) s = s`,
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;
let _ = cake_add_simps [data_inv_locals];;

let insert_eq = prove
 (`!(n1:num) (n2:num) (v1:A) v2 l. insert n1 v1 l = insert n1 v2 l <=> v1 = v2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lookup n1 (insert n1 (v1:A) l) = lookup n1 (insert n1 v2 l)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[lookup_insert; option_INJ]]);;

let WPROOF1AUX_CSE_lookup_insert_sym = prove
 (`!k1 k2 (v:A) t. lookup k1 (insert k2 v t) = if k2 = k1 then SOME v else lookup k1 t`,
  REWRITE_TAC[lookup_insert] THEN MESON_TAC[]);;

(* the cases of an arith instruction a with can_mem_arith a, split by the   *)
(* reg_imm argument; the evaluation of wl_Inst unfolded                    *)

let WPROOF1AUX_CSE_ARITH_CASES_TAC : tactic =
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[can_mem_arith_def; arithReads_def; firstRegOfArith_def; MEM;
              DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; the_words_def; MAP; wl_get_vars_def;
              LET_DEF; LET_END_DEF];;

let evaluate_arith_set_var = prove
 (`!a r u w (s:(A,C,FFI)wl_state).
     can_mem_arith a /\ ~MEM r (arithReads a) ==>
     (wl_evaluate (wl_Inst (asm_Arith a), wl_set_var r u s) =
        (NONE, wl_set_var (firstRegOfArith a) w (wl_set_var r u s)) <=>
      wl_evaluate (wl_Inst (asm_Arith a), s) =
        (NONE, wl_set_var (firstRegOfArith a) w s))`,
  WPROOF1AUX_CSE_ARITH_CASES_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def; WPROOF1AUX_CSE_lookup_insert_sym] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

let WPROOF1AUX_CSE_LOAD_CASES_TAC : tactic =
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[is_store_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_exp_def; the_words_def; MAP; LET_DEF; LET_END_DEF];;

let evaluate_load_any_dest = prove
 (`!op r0 a ofs w (s:(A,C,FFI)wl_state) r.
     ~is_store op /\
     wl_evaluate (wl_Inst (Mem op r0 (Addr a ofs)), s) = (NONE, wl_set_var r0 w s) ==>
     wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s) = (NONE, wl_set_var r w s)`,
  WPROOF1AUX_CSE_LOAD_CASES_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def; wl_mem_load_def; word_op_def] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

let evaluate_load_set_var = prove
 (`!op r a ofs n u w (s:(A,C,FFI)wl_state).
     ~is_store op /\ ~(a = n) ==>
     (wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), wl_set_var n u s) =
        (NONE, wl_set_var r w (wl_set_var n u s)) <=>
      wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s) = (NONE, wl_set_var r w s))`,
  WPROOF1AUX_CSE_LOAD_CASES_TAC THEN STRIP_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def; wl_mem_load_def; word_op_def;
       WPROOF1AUX_CSE_lookup_insert_sym] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

let evaluate_load_change_addr = prove
 (`!op r a a' ofs w (s:(A,C,FFI)wl_state).
     ~is_store op /\
     lookup a' (wl_state_locals s) = lookup a (wl_state_locals s) /\
     wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s) = (NONE, wl_set_var r w s) ==>
     wl_evaluate (wl_Inst (Mem op r (Addr a' ofs)), s) = (NONE, wl_set_var r w s)`,
  WPROOF1AUX_CSE_LOAD_CASES_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def; wl_mem_load_def; word_op_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let evaluate_arith_memory = prove
 (`!a w (s:(A,C,FFI)wl_state) m.
     can_mem_arith a ==>
     (wl_evaluate (wl_Inst (asm_Arith a), wl_state_memory_fupd (K m) s) =
        (NONE, wl_state_memory_fupd (K m) (wl_set_var (firstRegOfArith a) w s)) <=>
      wl_evaluate (wl_Inst (asm_Arith a), s) =
        (NONE, wl_set_var (firstRegOfArith a) w s))`,
  WPROOF1AUX_CSE_ARITH_CASES_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

let wf_data_untracked = prove
 (`!data n.
     wf_data (:A) data /\ lookup n (knowledge_to_canonical data) = NONE ==>
     (!r v. lookup r (knowledge_to_canonical data) = SOME v ==> ~(r = n) /\ ~(v = n)) /\
     (!r v. lookup r (knowledge_to_latest data) = SOME v ==> ~(r = n) /\ ~(v = n)) /\
     (!k v. balanced_map_lookup listCmp k (knowledge_instrs_mem data) = SOME v ==>
            ~(v = n)) /\
     (!(a:(A)asm_arith) v.
        balanced_map_lookup listCmp (instToNumList (asm_Arith a))
          (knowledge_instrs_mem data) = SOME v ==>
        ~MEM n (arithReads a) /\ can_mem_arith a) /\
     (!op src v.
        balanced_map_lookup listCmp (OpCurrHeapToNumList op src)
          (knowledge_instrs_mem data) = SOME v ==> ~(src = n)) /\
     (!x v. ALOOKUP (knowledge_gets_mem data) x = SOME v ==> ~(v = n)) /\
     (!k v. balanced_map_lookup listCmp k (knowledge_loads_mem data) = SOME v ==>
            ~(v = n)) /\
     (!op a (ofs:A word) v.
        balanced_map_lookup listCmp (loadToNumList op a ofs)
          (knowledge_loads_mem data) = SOME v ==> ~(a = n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wf_data_def; in_names_set_def; GSYM ALL_MEM; domain_lookup] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  RES_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  DISCH_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_MESON_TAC[option_DISTINCT]);;

(* reduce an equivalence between two conjunctions of quantified implications *)
(* with the same antecedents to the equivalences of their conclusions        *)

let WPROOF1AUX_CSE_CONG_TAC : tactic =
  let iff_parts w = let l,r = dest_eq w in
                    if type_of l = bool_ty then l,r else failwith "iff_parts" in
  REPEAT (FIRST [
    (fun (asl,w as g) -> let l,r = iff_parts w in
                         if is_conj l && is_conj r then BINOP_TAC g else failwith "");
    (fun (asl,w as g) -> let l,r = iff_parts w in
                         if is_forall l && is_forall r then (AP_TERM_TAC THEN ABS_TAC) g
                         else failwith "");
    (fun (asl,w as g) -> let l,r = iff_parts w in
                         if is_exists l && is_exists r then (AP_TERM_TAC THEN ABS_TAC) g
                         else failwith "");
    (fun (asl,w as g) -> let l,r = iff_parts w in
                         if is_imp l && is_imp r && fst(dest_imp l) = fst(dest_imp r) then
                           (MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> ((p ==> q) <=> (p ==> r))`)
                            THEN DISCH_THEN STRIP_ASSUME_TAC) g
                         else failwith "")]);;

let data_inv_set_var = prove
 (`!data (s:(A,C,FFI)wl_state) n v.
     lookup n (knowledge_to_canonical data) = NONE ==>
     (data_inv data (wl_set_var n v s) <=> data_inv data s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[data_inv_def] THEN
  ASM_CASES_TAC `wf_data (:A) data` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`data:knowledge`; `n:num`] (INST_TYPE [`:A`,`:A`] wf_data_untracked)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[sem_inv_def] THEN WPROOF1AUX_CSE_CONG_TAC THEN
  RES_TAC THEN ASM_SIMP_TAC[evaluate_arith_set_var; evaluate_load_set_var] THEN
  SIMP[wl_get_var_set_var; wl_set_var_def; lookup_insert; wl_word_exp_def; the_words_def;
       MAP; wl_get_store_def]);;

let WPROOF1AUX_CSE_lookup_delete_sym = prove
 (`!k1 k2 (t:A spt). lookup k1 (delete k2 t) = if k2 = k1 then NONE else lookup k1 t`,
  REWRITE_TAC[lookup_delete] THEN MESON_TAC[]);;

let evaluate_arith_unset_var = prove
 (`!a r w (s:(A,C,FFI)wl_state).
     can_mem_arith a /\ ~MEM r (arithReads a) ==>
     (wl_evaluate (wl_Inst (asm_Arith a), wl_unset_var r s) =
        (NONE, wl_set_var (firstRegOfArith a) w (wl_unset_var r s)) <=>
      wl_evaluate (wl_Inst (asm_Arith a), s) =
        (NONE, wl_set_var (firstRegOfArith a) w s))`,
  WPROOF1AUX_CSE_ARITH_CASES_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def; wl_unset_var_def; WPROOF1AUX_CSE_lookup_delete_sym] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

let evaluate_load_unset_var = prove
 (`!op r a ofs n w (s:(A,C,FFI)wl_state).
     ~is_store op /\ ~(a = n) ==>
     (wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), wl_unset_var n s) =
        (NONE, wl_set_var r w (wl_unset_var n s)) <=>
      wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s) = (NONE, wl_set_var r w s))`,
  WPROOF1AUX_CSE_LOAD_CASES_TAC THEN STRIP_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def; wl_unset_var_def; wl_mem_load_def; word_op_def;
       WPROOF1AUX_CSE_lookup_delete_sym] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

let data_inv_unset_var = prove
 (`!data (s:(A,C,FFI)wl_state) n.
     lookup n (knowledge_to_canonical data) = NONE ==>
     (data_inv data (wl_unset_var n s) <=> data_inv data s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[data_inv_def] THEN
  ASM_CASES_TAC `wf_data (:A) data` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`data:knowledge`; `n:num`] (INST_TYPE [`:A`,`:A`] wf_data_untracked)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[sem_inv_def] THEN WPROOF1AUX_CSE_CONG_TAC THEN
  RES_TAC THEN ASM_SIMP_TAC[evaluate_arith_unset_var; evaluate_load_unset_var] THEN
  SIMP[wl_get_var_def; wl_unset_var_def; WPROOF1AUX_CSE_lookup_delete_sym; wl_word_exp_def;
       the_words_def; MAP; wl_get_store_def]);;

let not_seen_data_inv_alist_insert = prove
 (`!data (s:(A,C,FFI)wl_state) l r v.
     lookup r (knowledge_to_canonical data) = NONE ==>
     data_inv data (wl_state_locals_fupd (K l) s) ==>
     data_inv data (wl_state_locals_fupd (K (insert r v l)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_locals_fupd (K (insert r v l)) (s:(A,C,FFI)wl_state) =
                wl_set_var r v (wl_state_locals_fupd (K l) s)` SUBST1_TAC THENL
   [SIMP[wl_set_var_def]; ASM_SIMP_TAC[data_inv_set_var]]);;
let _ = cake_add_simps [not_seen_data_inv_alist_insert];;

let listCmpEq_correct = prove
 (`!L1 L2. listCmp L1 L2 = EQUAL <=> L1 = L2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[listCmp_def; NOT_CONS_NIL; CONS_11] THEN SIMP[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN SIMP[]);;

let antisym_listCmp = prove
 (`!x y. listCmp x y = GREATER <=> listCmp y x = LESS`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[listCmp_def] THEN SIMP[] THEN
  ASM_CASES_TAC `h:num = h'` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(h':num = h)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `h > h'` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(h' > h)` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN SIMP[]];
    SUBGOAL_THEN `h' > h` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN SIMP[]]]);;

let transit_listCmp = prove
 (`!x y z. listCmp x y = LESS /\ listCmp y z = LESS ==> listCmp x z = LESS`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[listCmp_def] THEN SIMP[] THEN
  REPEAT COND_CASES_TAC THEN SIMP[] THEN
  TRY(FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (is_forall o concl))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_forall (concl th))))) THEN
  ARITH_TAC);;

let TotOrd_listCmp = prove
 (`TotOrd listCmp`,
  REWRITE_TAC[TotOrd; listCmpEq_correct; antisym_listCmp] THEN
  MESON_TAC[transit_listCmp]);;
let _ = cake_add_simps [TotOrd_listCmp];;

let good_cmp_listCmp = prove
 (`good_cmp listCmp`,
  MATCH_MP_TAC TotOrder_imp_good_cmp THEN REWRITE_TAC[TotOrd_listCmp]);;
let _ = cake_add_simps [good_cmp_listCmp];;

let lookup_listCmp_empty = prove
 (`balanced_map_lookup listCmp k (balanced_map_empty:(num list,V)balanced_map) = NONE`,
  REWRITE_TAC[balanced_map_empty_def; balanced_map_lookup_def]);;
let _ = cake_add_simps [lookup_listCmp_empty];;

let data_inv_empty = prove
 (`!s:(A,C,FFI)wl_state. data_inv empty_data s`,
  REWRITE_TAC[data_inv_def; wf_data_def; sem_inv_def; empty_data_def] THEN SIMP[] THEN
  REWRITE_TAC[lookup_def; balanced_map_empty_def; balanced_map_lookup_def;
              balanced_map_invariant_def; ALOOKUP_DEF; ALL_DISTINCT; MAP; option_DISTINCT;
              domain_def; NOT_IN_EMPTY]);;
let _ = cake_add_simps [data_inv_empty];;

let invariant_listCmp_empty = prove
 (`balanced_map_invariant listCmp (balanced_map_empty:(num list,V)balanced_map)`,
  REWRITE_TAC[balanced_map_empty_def; balanced_map_invariant_def]);;
let _ = cake_add_simps [invariant_listCmp_empty];;

(* the OpCurrHeap expression reads only locals and store *)

let WPROOF1AUX_CSE_och_agree = prove
 (`!op src (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     wl_state_locals s2 = wl_state_locals s1 /\ wl_state_store s2 = wl_state_store s1 ==>
     wl_word_exp s2 (wl_Op op [wl_Var src; Lookup CurrHeap]) =
     wl_word_exp s1 (wl_Op op [wl_Var src; Lookup CurrHeap])`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_word_exp_def; the_words_def; MAP; wl_get_var_def; wl_get_store_def]);;

let data_inv_memory = prove
 (`!data (s:(A,C,FFI)wl_state) m.
     data_inv data s ==>
     data_inv (knowledge_loads_mem_fupd (K balanced_map_empty) data)
              (wl_state_memory_fupd (K m) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_inv_def; wf_data_def; sem_inv_def] THEN
  SIMP[lookup_listCmp_empty; invariant_listCmp_empty; option_DISTINCT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:(A)word_loc` THEN ASM_SIMP_TAC[evaluate_arith_memory] THEN
  MP_TAC(ISPECL [`op:binop`; `src:num`; `s:(A,C,FFI)wl_state`;
                 `wl_state_memory_fupd (K m) (s:(A,C,FFI)wl_state)`]
                WPROOF1AUX_CSE_och_agree) THEN
  SIMP[]);;

let WPROOF1AUX_CSE_is_eval_eq th =
  let c = concl th in
  is_eq c && (let l = lhs c in is_comb l && is_const (rator l) &&
                               fst(dest_const(rator l)) = "wl_evaluate");;

(* as WPROOF1AUX_CSE_ARITH_CASES_TAC, the evaluations in the assumptions   *)
(* unfolded too                                                             *)

let WPROOF1AUX_CSE_ARITH_CASES2_TAC : tactic =
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[can_mem_arith_def; arithReads_def; firstRegOfArith_def; MEM;
              DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq)) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; the_words_def; MAP; wl_get_vars_def;
              LET_DEF; LET_END_DEF];;

let evaluate_arith_agree = prove
 (`!a w (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     wl_evaluate (wl_Inst (asm_Arith a), s1) =
       (NONE, wl_set_var (firstRegOfArith a) w s1) /\
     can_mem_arith a /\ wl_state_locals s2 = wl_state_locals s1 ==>
     wl_evaluate (wl_Inst (asm_Arith a), s2) =
       (NONE, wl_set_var (firstRegOfArith a) w s2)`,
  WPROOF1AUX_CSE_ARITH_CASES2_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

let WPROOF1AUX_CSE_LOAD_CASES2_TAC : tactic =
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[is_store_def] THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq)) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_exp_def; the_words_def; MAP; LET_DEF; LET_END_DEF];;

let evaluate_load_agree = prove
 (`!op r a ofs w (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s1) = (NONE, wl_set_var r w s1) /\
     ~is_store op /\ wl_state_locals s2 = wl_state_locals s1 /\
     wl_state_memory s2 = wl_state_memory s1 /\
     wl_state_mdomain s2 = wl_state_mdomain s1 /\ wl_state_be s2 = wl_state_be s1 ==>
     wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s2) = (NONE, wl_set_var r w s2)`,
  WPROOF1AUX_CSE_LOAD_CASES2_TAC THEN
  SIMP[wl_get_var_def; wl_set_var_def; wl_mem_load_def; word_op_def] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;


let WPROOF1AUX_CSE_arith_agree_iff = prove
 (`!a w (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     can_mem_arith a /\ wl_state_locals s2 = wl_state_locals s1 ==>
     (wl_evaluate (wl_Inst (asm_Arith a), s2) =
        (NONE, wl_set_var (firstRegOfArith a) w s2) <=>
      wl_evaluate (wl_Inst (asm_Arith a), s1) =
        (NONE, wl_set_var (firstRegOfArith a) w s1))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC evaluate_arith_agree THEN
  ASM_MESON_TAC[]);;

let WPROOF1AUX_CSE_load_agree_iff = prove
 (`!op r a ofs w (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     ~is_store op /\ wl_state_locals s2 = wl_state_locals s1 /\
     wl_state_memory s2 = wl_state_memory s1 /\
     wl_state_mdomain s2 = wl_state_mdomain s1 /\ wl_state_be s2 = wl_state_be s1 ==>
     (wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s2) = (NONE, wl_set_var r w s2) <=>
      wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s1) = (NONE, wl_set_var r w s1))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC evaluate_load_agree THEN
  ASM_MESON_TAC[]);;

let data_inv_state_agree = prove
 (`!data (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     data_inv data s1 /\
     wl_state_locals s2 = wl_state_locals s1 /\ wl_state_store s2 = wl_state_store s1 /\
     wl_state_memory s2 = wl_state_memory s1 /\
     wl_state_mdomain s2 = wl_state_mdomain s1 /\ wl_state_be s2 = wl_state_be s1 ==>
     data_inv data s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_inv_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sem_inv data (s2:(A,C,FFI)wl_state) <=> sem_inv data (s1:(A,C,FFI)wl_state)`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wf_data_def] o
                check (fun th -> can (term_match [] `wf_data (:A) d`) (concl th))) THEN
  REWRITE_TAC[sem_inv_def] THEN WPROOF1AUX_CSE_CONG_TAC THEN
  RES_TAC THEN
  ASM_SIMP_TAC[WPROOF1AUX_CSE_arith_agree_iff; WPROOF1AUX_CSE_load_agree_iff;
               WPROOF1AUX_CSE_och_agree; wl_get_var_def]);;

let bm_inter_eq_acc_thm = prove
 (CASE_TERM
  `!m2 m1 (acc:(num list,V)balanced_map).
     balanced_map_invariant listCmp m2 /\ balanced_map_invariant listCmp m1 /\
     balanced_map_invariant listCmp acc ==>
     balanced_map_invariant listCmp (bm_inter_eq_acc m2 m1 acc) /\
     !ks. FLOOKUP (to_fmap listCmp (bm_inter_eq_acc m2 m1 acc)) ks =
          match FLOOKUP (to_fmap listCmp m1) ks with
            NONE -> FLOOKUP (to_fmap listCmp acc) ks
          | SOME v -> if FLOOKUP (to_fmap listCmp m2) ks = SOME v then SOME v
                      else FLOOKUP (to_fmap listCmp acc) ks`,
  GEN_TAC THEN MATCH_MP_TAC balanced_map_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[bm_inter_eq_acc_def; to_fmap_def; FLOOKUP_EMPTY] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `k:num list`; `v:V`; `l:(num list,V)balanced_map`;
                       `r:(num list,V)balanced_map`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  X_GEN_TAC `acc:(num list,V)balanced_map` THEN
  REWRITE_TAC[invariant_eq; good_cmp_listCmp] THEN STRIP_TAC THEN
  REWRITE_TAC[bm_inter_eq_acc_def] THEN
  ABBREV_TAC `acc1 = if balanced_map_lookup listCmp k m2 = SOME (v:V)
                     then balanced_map_insert listCmp k v acc else acc` THEN
  SUBGOAL_THEN
   `balanced_map_invariant listCmp (acc1:(num list,V)balanced_map) /\
    !ks. FLOOKUP (to_fmap listCmp acc1) ks =
         if ks = key_set listCmp k /\ balanced_map_lookup listCmp k m2 = SOME v
         then SOME v else FLOOKUP (to_fmap listCmp acc) ks`
   STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "acc1" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`acc:(num list,V)balanced_map`; `listCmp`; `k:num list`; `v:V`]
                  insert_thm) THEN
    ASM_REWRITE_TAC[good_cmp_listCmp] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ihr" (MP_TAC o SPEC `acc1:(num list,V)balanced_map`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihl" (MP_TAC o SPEC `bm_inter_eq_acc m2 r (acc1:(num list,V)balanced_map)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `ks:(num list->bool)` THEN
  REWRITE_TAC[to_fmap_def; FLOOKUP_UPDATE; FLOOKUP_FUNION] THEN
  ASM_CASES_TAC `ks = key_set listCmp k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `FLOOKUP (to_fmap listCmp (l:(num list,V)balanced_map)) (key_set listCmp k) = NONE /\
                  FLOOKUP (to_fmap listCmp (r:(num list,V)balanced_map)) (key_set listCmp k) = NONE`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`listCmp`; `k:num list`; `m2:(num list,V)balanced_map`] lookup_thm) THEN
    ASM_REWRITE_TAC[good_cmp_listCmp] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(key_set listCmp k = ks)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `FLOOKUP (to_fmap listCmp (l:(num list,V)balanced_map)) ks` THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FLOOKUP (to_fmap listCmp (r:(num list,V)balanced_map)) ks = NONE`
    (fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
  UNDISCH_TAC `FLOOKUP (to_fmap listCmp (l:(num list,V)balanced_map)) ks = SOME a` THEN
  UNDISCH_TAC `DISJOINT (FDOM (to_fmap listCmp (l:(num list,V)balanced_map)))
                        (FDOM (to_fmap listCmp (r:(num list,V)balanced_map)))` THEN
  REWRITE_TAC[FLOOKUP_DEF; IN_DISJOINT] THEN MESON_TAC[option_DISTINCT]);;

let invariant_bm_inter_eq = prove
 (`!m1 m2:(num list,V)balanced_map.
     balanced_map_invariant listCmp m1 /\ balanced_map_invariant listCmp m2 ==>
     balanced_map_invariant listCmp (bm_inter_eq m1 m2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bm_inter_eq_def] THEN
  MP_TAC(ISPECL [`m2:(num list,V)balanced_map`; `m1:(num list,V)balanced_map`;
                 `balanced_map_empty:(num list,V)balanced_map`] bm_inter_eq_acc_thm) THEN
  ASM_SIMP_TAC[invariant_listCmp_empty]);;

let lookup_bm_inter_eq = prove
 (`!m1 m2:(num list,V)balanced_map k v.
     balanced_map_invariant listCmp m1 /\ balanced_map_invariant listCmp m2 ==>
     (balanced_map_lookup listCmp k (bm_inter_eq m1 m2) = SOME v <=>
      balanced_map_lookup listCmp k m1 = SOME v /\
      balanced_map_lookup listCmp k m2 = SOME v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bm_inter_eq_def] THEN
  MP_TAC(ISPECL [`m2:(num list,V)balanced_map`; `m1:(num list,V)balanced_map`;
                 `balanced_map_empty:(num list,V)balanced_map`] bm_inter_eq_acc_thm) THEN
  ASM_SIMP_TAC[invariant_listCmp_empty] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[lookup_thm; good_cmp_listCmp] THEN
  REWRITE_TAC[balanced_map_empty_def; to_fmap_def; FLOOKUP_EMPTY] THEN
  CASES_ON `FLOOKUP (to_fmap listCmp (m1:(num list,V)balanced_map)) (key_set listCmp k)` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ASM_MESON_TAC[option_INJ]);;

let ALL_DISTINCT_MAP_FST_FILTER = prove
 (`!l:(A#B)list P. ALL_DISTINCT (MAP FST l) ==> ALL_DISTINCT (MAP FST (FILTER P l))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP; ALL_DISTINCT] THEN
  GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[MAP; ALL_DISTINCT] THEN
  REWRITE_TAC[MEM_MAP; MEM_FILTER] THEN
  UNDISCH_TAC `~MEM (FST (h:A#B)) (MAP FST (t:(A#B)list))` THEN REWRITE_TAC[MEM_MAP] THEN
  MESON_TAC[]);;

let WPROOF1AUX_CSE_lookup_inter_eq_SOME = prove
 (`!m1 m2:A spt k v.
     lookup k (inter_eq m1 m2) = SOME v <=> lookup k m1 = SOME v /\ lookup k m2 = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_inter_eq] THEN
  CASES_ON `lookup k (m1:A spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN ASM_MESON_TAC[option_INJ]);;

let WPROOF1AUX_CSE_merge_gets = prove
 (`!gm1 gm2 (x:store_name) (v:num).
     ALL_DISTINCT (MAP FST gm1) /\
     ALOOKUP (FILTER (\(x,v). ALOOKUP gm2 x = SOME v) gm1) x = SOME v ==>
     ALOOKUP gm1 x = SOME v /\ ALOOKUP gm2 x = SOME v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN REWRITE_TAC[MEM_FILTER] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[]);;

let WPROOF1AUX_CSE_in_names_set_inter = prove
 (`!a:(A)asm_arith tc1 tc2.
     in_names_set a tc1 /\ in_names_set a tc2 ==> in_names_set a (inter_eq tc1 tc2)`,
  REWRITE_TAC[in_names_set_def; GSYM ALL_MEM; WPROOF1AUX_CSE_lookup_inter_eq_SOME] THEN
  MESON_TAC[]);;

(* the facts of merge_data d1 d2 are those of both d1 and d2 *)

let WPROOF1AUX_CSE_MERGE_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[data_inv_def] THEN STRIP_TAC THEN
  REWRITE_TAC[wf_data_def; sem_inv_def; merge_data_def; knowledge_INFO.ri_accessors] THEN
  REWRITE_TAC[WPROOF1AUX_CSE_lookup_inter_eq_SOME; lookup_rwts; option_DISTINCT] THEN
  SUBGOAL_THEN
   `balanced_map_invariant listCmp (knowledge_instrs_mem d1) /\
    balanced_map_invariant listCmp (knowledge_instrs_mem d2) /\
    balanced_map_invariant listCmp (knowledge_loads_mem d1) /\
    balanced_map_invariant listCmp (knowledge_loads_mem d2) /\
    ALL_DISTINCT (MAP FST (knowledge_gets_mem d1))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[wf_data_def]; ALL_TAC] THEN
  ASM_SIMP_TAC[lookup_bm_inter_eq; invariant_bm_inter_eq; ALL_DISTINCT_MAP_FST_FILTER] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wf_data_def; sem_inv_def] o
         check (fun th -> let h = fst(strip_comb(concl th)) in
                          is_const h && mem (fst(dest_const h)) ["wf_data"; "sem_inv"]))) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_merge_gets o
        CONJ (ASSUME `ALL_DISTINCT (MAP FST (knowledge_gets_mem d1))`))) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC WPROOF1AUX_CSE_in_names_set_inter THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MESON_TAC[];;

let data_inv_merge_l = prove
 (`!d1 d2 (s:(A,C,FFI)wl_state).
     wf_data (:A) d1 /\ wf_data (:A) d2 /\ sem_inv d1 s ==>
     data_inv (merge_data d1 d2) s`,
  WPROOF1AUX_CSE_MERGE_TAC);;

let data_inv_merge_r = prove
 (`!d1 d2 (s:(A,C,FFI)wl_state).
     wf_data (:A) d1 /\ wf_data (:A) d2 /\ sem_inv d2 s ==>
     data_inv (merge_data d1 d2) s`,
  WPROOF1AUX_CSE_MERGE_TAC);;

let lookup_insert_listCmp = prove
 (`!k i (v:V) m.
     balanced_map_invariant listCmp m ==>
     balanced_map_invariant listCmp (balanced_map_insert listCmp i v m) /\
     balanced_map_lookup listCmp k (balanced_map_insert listCmp i v m) =
     (if k = i then SOME v else balanced_map_lookup listCmp k m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(num list,V)balanced_map`; `listCmp`; `i:num list`; `v:V`] insert_thm) THEN
  ASM_REWRITE_TAC[good_cmp_listCmp] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[lookup_thm; good_cmp_listCmp; FLOOKUP_UPDATE; key_set_eq; listCmpEq_correct] THEN
  MESON_TAC[]);;

let register_read_simps = prove
 (`knowledge_instrs_mem (register_read data r) = knowledge_instrs_mem data /\
   knowledge_to_latest (register_read data r) = knowledge_to_latest data /\
   knowledge_gets_mem (register_read data r) = knowledge_gets_mem data /\
   knowledge_loads_mem (register_read data r) = knowledge_loads_mem data`,
  REWRITE_TAC[register_read_def] THEN COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [register_read_simps];;

let register_reads_simps = prove
 (`!rs data.
     knowledge_instrs_mem (register_reads data rs) = knowledge_instrs_mem data /\
     knowledge_to_latest (register_reads data rs) = knowledge_to_latest data /\
     knowledge_gets_mem (register_reads data rs) = knowledge_gets_mem data /\
     knowledge_loads_mem (register_reads data rs) = knowledge_loads_mem data`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[register_reads_def; register_read_simps]);;
let _ = cake_add_simps [register_reads_simps];;

let lookup_register_read = prove
 (`lookup x (knowledge_to_canonical (register_read data r)) =
   if x = r /\ ~EVEN r /\ lookup r (knowledge_to_canonical data) = NONE
   then SOME r else lookup x (knowledge_to_canonical data)`,
  REWRITE_TAC[register_read_def; keep_data_def] THEN
  CASES_ON `lookup r (knowledge_to_canonical data)` THEN
  REWRITE_TAC[IS_NONE_DEF; option_DISTINCT] THEN
  COND_CASES_TAC THEN SIMP[lookup_insert] THEN MESON_TAC[]);;

let lookup_register_reads = prove
 (`!rs data x.
     lookup x (knowledge_to_canonical (register_reads data rs)) =
     if MEM x rs /\ ~EVEN x /\ lookup x (knowledge_to_canonical data) = NONE
     then SOME x else lookup x (knowledge_to_canonical data)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[register_reads_def; MEM] THEN
  REWRITE_TAC[lookup_register_read] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[option_DISTINCT]);;

let WPROOF1AUX_CSE_UNFOLD_ASMS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
         REWRITE_RULE[data_inv_def; wf_data_def; sem_inv_def; in_names_set_def; GSYM ALL_MEM] o
         check (fun th -> let h = fst(strip_comb(concl th)) in
                          is_const h &&
                          mem (fst(dest_const h)) ["data_inv"; "wf_data"; "sem_inv"])));;

let WPROOF1AUX_CSE_lookup_insert_fresh = prove
 (`!x y k v (t:A spt). lookup x t = NONE /\ lookup k t = SOME v ==>
                       lookup k (insert x y t) = SOME v`,
  REWRITE_TAC[lookup_insert] THEN MESON_TAC[option_DISTINCT]);;

let WPROOF1AUX_CSE_ALOOKUP_FILTER_NEQ = prove
 (`!(l:(A#B)list) x y.
     ALOOKUP (FILTER (\(m,n). ~(m = x)) l) y = if y = x then NONE else ALOOKUP l y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALOOKUP_THM; COND_ID] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALOOKUP_THM] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let WPROOF1AUX_CSE_KEY_EQ_CONV : conv = fun tm ->
  let is_key t =
    (let h,_ = strip_comb t in
     is_const h && mem (fst(dest_const h))
       ["instToNumList"; "OpCurrHeapToNumList"; "loadToNumList"]) ||
    (is_list t && t <> `[]:num list`) in
  if is_eq tm && type_of (lhs tm) = `:num list` && is_key (lhs tm) && is_key (rhs tm) then
    let th = REWRITE_CONV [instToNumList_def; OpCurrHeapToNumList_def; loadToNumList_def;
                           arithToNumList_def; APPEND; CONS_11; NOT_CONS_NIL; ARITH_EQ;
                           wordToNum_unique; arithOpToNum_eq; memOpToNum_eq;
                           EQ_ADD_RCANCEL] tm in
    if rand(concl th) = tm then failwith "KEY_EQ_CONV" else th
  else failwith "KEY_EQ_CONV";;

let WPROOF1AUX_CSE_KEY_RWS =
  [lookup_insert; ALOOKUP_THM; WPROOF1AUX_CSE_ALOOKUP_FILTER_NEQ];;

let WPROOF1AUX_CSE_KEY_RULE th =
  CONV_RULE (DEPTH_CONV WPROOF1AUX_CSE_KEY_EQ_CONV THENC
             REWRITE_CONV WPROOF1AUX_CSE_KEY_RWS) th;;

(* MESON with the assumptions that are not universally quantified *)

let WPROOF1AUX_CSE_ATOM_MESON_TAC : tactic = fun (asl,w as g) ->
  MESON_TAC (filter (fun th -> not (is_forall (concl th))) (map snd asl)) g;;

let WPROOF1AUX_CSE_FRESH_TAC : tactic =
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(MATCH_MP_TAC WPROOF1AUX_CSE_lookup_insert_fresh THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN
      MATCH_MP_TAC WPROOF1AUX_CSE_lookup_insert_fresh THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(WPROOF1AUX_CSE_ATOM_MESON_TAC THEN NO_TAC);;

let WPROOF1AUX_CSE_CL_INS_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o WPROOF1AUX_CSE_KEY_RULE) THEN
  COND_CASES_TAC THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    TRY(DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[] THEN
    TRY(REWRITE_TAC[lookup_insert] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(WPROOF1AUX_CSE_ATOM_MESON_TAC THEN NO_TAC);
    DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN WPROOF1AUX_CSE_FRESH_TAC];;

let WPROOF1AUX_CSE_CL_OLD_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o WPROOF1AUX_CSE_KEY_RULE) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN WPROOF1AUX_CSE_FRESH_TAC;;

let WPROOF1AUX_CSE_CLAUSE_TAC : tactic =
  FIRST [WPROOF1AUX_CSE_CL_INS_TAC THEN NO_TAC; WPROOF1AUX_CSE_CL_OLD_TAC THEN NO_TAC];;

(* the invariant of an updated knowledge: unfold, split into the clauses *)

let WPROOF1AUX_CSE_INV_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF1AUX_CSE_UNFOLD_ASMS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[in_names_set_def; GSYM ALL_MEM]) THEN
  REWRITE_TAC[data_inv_def; wf_data_def; sem_inv_def; in_names_set_def; GSYM ALL_MEM] THEN
  REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[domain_insert; IN_INSERT] THEN
  REPEAT CONJ_TAC;;

let data_inv_insert_to_canonical = prove
 (`!data (s:(A,C,FFI)wl_state) x y.
     data_inv data s /\
     lookup x (knowledge_to_canonical data) = NONE /\
     lookup y (insert x y (knowledge_to_canonical data)) = SOME y /\
     ODD x /\ ODD y /\
     wl_get_var x s = wl_get_var y s ==>
     data_inv (knowledge_to_canonical_fupd
                 (K (insert x y (knowledge_to_canonical data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN WPROOF1AUX_CSE_CLAUSE_TAC);;

let data_inv_insert_to_latest = prove
 (`!data (s:(A,C,FFI)wl_state) x y.
     data_inv data s /\
     x IN domain (knowledge_to_canonical data) /\
     y IN domain (knowledge_to_canonical data) /\
     wl_get_var x s = wl_get_var y s ==>
     data_inv (knowledge_to_latest_fupd
                 (K (insert x y (knowledge_to_latest data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN WPROOF1AUX_CSE_CLAUSE_TAC);;


let data_inv_insert_gets = prove
 (`!data (s:(A,C,FFI)wl_state) name v w.
     data_inv data s /\
     lookup v (knowledge_to_canonical data) = NONE /\ ODD v /\
     ALOOKUP (knowledge_gets_mem data) name = NONE /\
     FLOOKUP (wl_state_store s) name = SOME w /\ wl_get_var v s = SOME w ==>
     data_inv (knowledge_to_canonical_fupd (K (insert v v (knowledge_to_canonical data)))
                (knowledge_to_latest_fupd (K (insert v v (knowledge_to_latest data)))
                  (knowledge_gets_mem_fupd (K (CONS (name,v) (knowledge_gets_mem data)))
                     data))) s`,
  WPROOF1AUX_CSE_INV_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  ASM_REWRITE_TAC[GSYM ALOOKUP_NONE] THEN WPROOF1AUX_CSE_CLAUSE_TAC);;

let data_inv_filter_gets = prove
 (`!data (s:(A,C,FFI)wl_state) x.
     data_inv data s ==>
     data_inv (knowledge_gets_mem_fupd
                 (K (FILTER (\(m,n). ~(m = x)) (knowledge_gets_mem data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[ALL_DISTINCT_MAP_FST_FILTER] THEN
  WPROOF1AUX_CSE_CLAUSE_TAC);;

let data_inv_cons_gets = prove
 (`!data (s:(A,C,FFI)wl_state) x h w.
     data_inv data s /\
     ALOOKUP (knowledge_gets_mem data) x = NONE /\
     lookup h (knowledge_to_canonical data) = SOME h /\
     FLOOKUP (wl_state_store s) x = SOME w /\ wl_get_var h s = SOME w ==>
     data_inv (knowledge_gets_mem_fupd (K (CONS (x,h) (knowledge_gets_mem data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  ASM_REWRITE_TAC[GSYM ALOOKUP_NONE] THEN WPROOF1AUX_CSE_CLAUSE_TAC);;

let WPROOF1AUX_CSE_och_set_store = prove
 (`!op src x w (s:(A,C,FFI)wl_state).
     ~(x = CurrHeap) ==>
     wl_word_exp (wl_set_store x w s) (wl_Op op [wl_Var src; Lookup CurrHeap]) =
     wl_word_exp s (wl_Op op [wl_Var src; Lookup CurrHeap])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wl_word_exp_def; the_words_def; MAP; wl_get_var_def; wl_get_store_def;
              wl_set_store_def] THEN
  SIMP[FLOOKUP_UPDATE]);;

let data_inv_set_store = prove
 (`!data (s:(A,C,FFI)wl_state) x w.
     data_inv data s /\ ~(x = CurrHeap) /\ ALOOKUP (knowledge_gets_mem data) x = NONE ==>
     data_inv data (wl_set_store x w s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_inv_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sem_inv data (wl_set_store x w (s:(A,C,FFI)wl_state)) <=> sem_inv data s`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wf_data_def] o
                check (fun th -> can (term_match [] `wf_data (:A) d`) (concl th))) THEN
  REWRITE_TAC[sem_inv_def] THEN WPROOF1AUX_CSE_CONG_TAC THEN
  RES_TAC THEN
  TRY(MATCH_MP_TAC WPROOF1AUX_CSE_arith_agree_iff THEN
      ASM_REWRITE_TAC[] THEN SIMP[wl_set_store_def] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC WPROOF1AUX_CSE_load_agree_iff THEN
      ASM_REWRITE_TAC[] THEN SIMP[wl_set_store_def] THEN NO_TAC) THEN
  ASM_SIMP_TAC[WPROOF1AUX_CSE_och_set_store] THEN
  SIMP[wl_get_var_def; wl_set_store_def; FLOOKUP_UPDATE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]);;

let data_inv_reinsert_canonical = prove
 (`!data (s:(A,C,FFI)wl_state) v.
     data_inv data s /\ ODD v ==>
     data_inv (knowledge_to_canonical_fupd
                 (K (insert v (lookup_any v (knowledge_to_canonical data) v)
                       (knowledge_to_canonical data))) data) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_any_def] THEN
  CASES_ON `lookup v (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THENL
   [MATCH_MP_TAC data_inv_insert_to_canonical THEN ASM_REWRITE_TAC[lookup_insert];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP insert_unchanged th]) THEN
    SUBGOAL_THEN `knowledge_to_canonical_fupd (K (knowledge_to_canonical data)) data = data`
      SUBST1_TAC THENL
     [REWRITE_TAC[knowledge_component_equality] THEN SIMP[]; ASM_REWRITE_TAC[]]]);;

let empty_data_loads_wipe = prove
 (`knowledge_loads_mem_fupd (K balanced_map_empty) empty_data = empty_data`,
  REWRITE_TAC[empty_data_def] THEN SIMP[]);;
let _ = cake_add_simps [empty_data_loads_wipe];;

let lookup_empty_data = prove
 (`lookup r (knowledge_to_canonical empty_data) = NONE`,
  REWRITE_TAC[empty_data_def] THEN SIMP[lookup_rwts]);;
let _ = cake_add_simps [lookup_empty_data];;

let data_inv_register_read = prove
 (`!data (s:(A,C,FFI)wl_state) r.
     data_inv data s ==> data_inv (register_read data r) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[register_read_def; keep_data_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC data_inv_insert_to_canonical THEN
  ASM_REWRITE_TAC[lookup_insert; GSYM NOT_EVEN] THEN
  POP_ASSUM MP_TAC THEN
  CASES_ON `lookup r (knowledge_to_canonical data)` THEN REWRITE_TAC[IS_NONE_DEF]);;

let data_inv_register_reads = prove
 (`!rs data (s:(A,C,FFI)wl_state).
     data_inv data s ==> data_inv (register_reads data rs) s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[register_reads_def] THEN
  ASM_MESON_TAC[data_inv_register_read]);;

let lookup_invalidate_regs_mono = prove
 (`!ws data r.
     lookup r (knowledge_to_canonical data) = NONE ==>
     lookup r (knowledge_to_canonical (invalidate_regs data ws)) = NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[invalidate_regs_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[invalidate_data_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[lookup_empty_data]);;

let lookup_invalidate_regs = prove
 (`!ws data r.
     MEM r ws ==>
     lookup r (knowledge_to_canonical (invalidate_regs data ws)) = NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; invalidate_regs_def] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC lookup_invalidate_regs_mono THEN
  REWRITE_TAC[invalidate_data_def; keep_data_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[lookup_empty_data] THEN POP_ASSUM MP_TAC THEN
  CASES_ON `lookup h (knowledge_to_canonical data)` THEN REWRITE_TAC[IS_NONE_DEF]);;

let data_inv_invalidate_regs = prove
 (`!ws data (s:(A,C,FFI)wl_state).
     data_inv data s ==> data_inv (invalidate_regs data ws) s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[invalidate_regs_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[invalidate_data_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[data_inv_empty]);;

(* the invariant only reads locals, store and the memory fields *)

let WPROOF1AUX_CSE_sem_inv_agree = prove
 (`!data (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     wf_data (:A) data /\
     wl_state_locals s2 = wl_state_locals s1 /\ wl_state_store s2 = wl_state_store s1 /\
     wl_state_memory s2 = wl_state_memory s1 /\
     wl_state_mdomain s2 = wl_state_mdomain s1 /\ wl_state_be s2 = wl_state_be s1 ==>
     (sem_inv data s2 <=> sem_inv data s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wf_data_def] o
                check (fun th -> can (term_match [] `wf_data (:A) d`) (concl th))) THEN
  REWRITE_TAC[sem_inv_def] THEN WPROOF1AUX_CSE_CONG_TAC THEN
  RES_TAC THEN
  ASM_SIMP_TAC[WPROOF1AUX_CSE_arith_agree_iff; WPROOF1AUX_CSE_load_agree_iff;
               WPROOF1AUX_CSE_och_agree; wl_get_var_def]);;

let data_inv_set_fp_var = prove
 (`!data v x (s:(A,C,FFI)wl_state).
     data_inv data (wl_set_fp_var v x s) <=> data_inv data s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_inv_def] THEN
  ASM_CASES_TAC `wf_data (:A) data` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WPROOF1AUX_CSE_sem_inv_agree THEN ASM_REWRITE_TAC[] THEN
  SIMP[wl_set_fp_var_def]);;
let _ = cake_add_simps [data_inv_set_fp_var];;

let with_locals_insert = prove
 (`wl_state_locals_fupd (K (insert r v l)) (s:(A,C,FFI)wl_state) =
   wl_set_var r v (wl_state_locals_fupd (K l) s)`,
  SIMP[wl_set_var_def]);;

let data_inv_alist_insert_locals = prove
 (`!xs ys data (s:(A,C,FFI)wl_state) l.
     ALL (\x. lookup x (knowledge_to_canonical data) = NONE) xs ==>
     (data_inv data (wl_state_locals_fupd (K (alist_insert xs ys l)) s) <=>
      data_inv data (wl_state_locals_fupd (K l) s))`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[alist_insert_def]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_insert_def; ALL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[with_locals_insert] THEN
  ASM_SIMP_TAC[data_inv_set_var]);;

let data_inv_set_vars = prove
 (`!xs ys data (s:(A,C,FFI)wl_state).
     ALL (\x. lookup x (knowledge_to_canonical data) = NONE) xs ==>
     (data_inv data (wl_set_vars xs ys s) <=> data_inv data s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_set_vars_def] THEN
  ASM_SIMP_TAC[data_inv_alist_insert_locals; data_inv_locals]);;

let evaluate_Move1 = prove
 (`!pri r k w (s:(A,C,FFI)wl_state).
     wl_get_var k s = SOME w ==>
     wl_evaluate (wl_Move pri [(r,k)], s) = (NONE, wl_set_var r w s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Move"] THEN
  ASM_REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_set_vars_def; wl_set_var_def; alist_insert_def]);;

let shiftToNum_eq = prove
 (`!s1 s2. shiftToNum s1 = shiftToNum s2 <=> s1 = s2`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `s1:shift` (cases "shift")) THEN
  STRUCT_CASES_TAC (ISPEC `s2:shift` (cases "shift")) THEN
  REWRITE_TAC[shiftToNum_def] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP[]);;
let _ = cake_add_simps [shiftToNum_eq];;

let arith_keys_eq = prove
 (`!a1 a2:(A)asm_arith.
     can_mem_arith a1 /\ arithToNumList a1 = arithToNumList a2 ==>
     can_mem_arith a2 /\ arithReads a2 = arithReads a1 /\
     !(s:(A,C,FFI)wl_state) w.
       wl_evaluate (wl_Inst (asm_Arith a1), s) =
         (NONE, wl_set_var (firstRegOfArith a1) w s) ==>
       wl_evaluate (wl_Inst (asm_Arith a2), s) =
         (NONE, wl_set_var (firstRegOfArith a2) w s)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a1:(A)asm_arith` (cases "asm_arith")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[can_mem_arith_def] THEN
  STRUCT_CASES_TAC (ISPEC `a2:(A)asm_arith` (cases "asm_arith")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[arithToNumList_def; regImmToNumList_def; APPEND; CONS_11] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EQ_ADD_RCANCEL; arithOpToNum_eq; shiftToNum_eq;
                                            wordToNum_unique] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[can_mem_arith_def; arithReads_def; firstRegOfArith_def] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; the_words_def; MAP; wl_get_vars_def;
              LET_DEF; LET_END_DEF] THEN
  SIMP[wl_get_var_def; wl_set_var_def] THEN
  REPEAT (CASE_TAC THEN SIMP[insert_eq]));;

(* the key equations of the clause tactics, now with shiftToNum_eq *)

let WPROOF1AUX_CSE_KEY_EQ2_CONV : conv = fun tm ->
  let is_key t =
    (let h,_ = strip_comb t in
     is_const h && mem (fst(dest_const h))
       ["instToNumList"; "OpCurrHeapToNumList"; "loadToNumList"]) ||
    (is_list t && t <> `[]:num list`) in
  if is_eq tm && type_of (lhs tm) = `:num list` && is_key (lhs tm) && is_key (rhs tm) then
    let th = REWRITE_CONV [instToNumList_def; OpCurrHeapToNumList_def; loadToNumList_def;
                           arithToNumList_def; APPEND; CONS_11; NOT_CONS_NIL; ARITH_EQ;
                           wordToNum_unique; arithOpToNum_eq; memOpToNum_eq; shiftToNum_eq;
                           EQ_ADD_RCANCEL] tm in
    if rand(concl th) = tm then failwith "KEY_EQ2_CONV" else th
  else failwith "KEY_EQ2_CONV";;

let WPROOF1AUX_CSE_KEY_RULE2 th =
  CONV_RULE (DEPTH_CONV WPROOF1AUX_CSE_KEY_EQ2_CONV THENC
             REWRITE_CONV WPROOF1AUX_CSE_KEY_RWS) th;;

let WPROOF1AUX_CSE_CL_OLD2_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o WPROOF1AUX_CSE_KEY_RULE2) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN WPROOF1AUX_CSE_FRESH_TAC;;

(* two arith instructions with the same key: arith_keys_eq *)

let WPROOF1AUX_CSE_ARITH_KEY_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_comb (lhs c) && is_const (rator (lhs c)) &&
       fst (dest_const (rator (lhs c))) = "arithToNumList" then
      let a1 = rand (rhs c) in
      let cm = mk_icomb(mk_const("can_mem_arith",[]), a1) in
      MP_TAC (MATCH_MP arith_keys_eq (CONJ (ASSUME cm) (SYM th))) THEN STRIP_TAC
    else NO_TAC);;

let WPROOF1AUX_CSE_CL_INS2_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o WPROOF1AUX_CSE_KEY_RULE2) THEN
  COND_CASES_TAC THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN RVEQ_TAC THEN
    TRY WPROOF1AUX_CSE_ARITH_KEY_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    TRY(DISCH_THEN STRIP_ASSUME_TAC THEN RVEQ_TAC) THEN ASM_REWRITE_TAC[] THEN
    RES_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(REWRITE_TAC[lookup_insert] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(WPROOF1AUX_CSE_ATOM_MESON_TAC THEN NO_TAC) THEN
    TRY(ASM_MESON_TAC[] THEN NO_TAC);
    DISCH_THEN STRIP_ASSUME_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN WPROOF1AUX_CSE_FRESH_TAC THEN
    TRY(ASM_MESON_TAC[] THEN NO_TAC)];;

let WPROOF1AUX_CSE_CLAUSE2_TAC : tactic =
  FIRST [WPROOF1AUX_CSE_CL_INS2_TAC THEN NO_TAC; WPROOF1AUX_CSE_CL_OLD2_TAC THEN NO_TAC];;


let data_inv_insert_instrs_Const = prove
 (`!data (s:(A,C,FFI)wl_state) r n (w:A word).
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     lookup r (wl_state_locals s) = SOME (wl_Word w) ==>
     data_inv (knowledge_instrs_mem_fupd
                 (K (balanced_map_insert listCmp (instToNumList (asm_Const n w:(A)inst)) r
                       (knowledge_instrs_mem data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let data_inv_insert_instrs_Arith = prove
 (`!data (s:(A,C,FFI)wl_state) r (a:(A)asm_arith) w.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     can_mem_arith a /\ in_names_set a (knowledge_to_canonical data) /\
     wl_get_var r s = SOME w /\
     wl_evaluate (wl_Inst (asm_Arith a), s) =
       (NONE, wl_set_var (firstRegOfArith a) w s) ==>
     data_inv (knowledge_instrs_mem_fupd
                 (K (balanced_map_insert listCmp (instToNumList (asm_Arith a)) r
                       (knowledge_instrs_mem data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let data_inv_insert_instrs_OpCurrHeap = prove
 (`!data (s:(A,C,FFI)wl_state) r op src w.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     lookup src (knowledge_to_canonical data) = SOME src /\
     wl_word_exp s (wl_Op op [wl_Var src; Lookup CurrHeap]) = SOME w /\
     wl_get_var r s = SOME w ==>
     data_inv (knowledge_instrs_mem_fupd
                 (K (balanced_map_insert listCmp (OpCurrHeapToNumList op src) r
                       (knowledge_instrs_mem data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let data_inv_insert_instrs_LocValue = prove
 (`!data (s:(A,C,FFI)wl_state) r l.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     lookup r (wl_state_locals s) = SOME (wl_Loc l 0) ==>
     data_inv (knowledge_instrs_mem_fupd
                 (K (balanced_map_insert listCmp [48; l] r
                       (knowledge_instrs_mem data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let WPROOF1AUX_CSE_get_var_latest = prove
 (`!data (s:(A,C,FFI)wl_state) a w.
     data_inv data s /\ wl_get_var a s = SOME w ==>
     wl_get_var (lookup_any a (knowledge_to_latest data) a) s = SOME w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_inv_def; sem_inv_def; lookup_any_def] THEN
  STRIP_TAC THEN CASES_ON `lookup a (knowledge_to_latest data)` THEN
  CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let WPROOF1AUX_CSE_add_to_latest_eq = prove
 (`!data i r.
     knowledge_to_latest_fupd
       (K (insert r r (knowledge_to_latest
            (knowledge_instrs_mem_fupd
              (K (balanced_map_insert listCmp i r
                    (knowledge_instrs_mem
                       (knowledge_to_canonical_fupd
                          (K (insert r r (knowledge_to_canonical data))) data))))
              (knowledge_to_canonical_fupd
                 (K (insert r r (knowledge_to_canonical data))) data)))))
       (knowledge_instrs_mem_fupd
          (K (balanced_map_insert listCmp i r
                (knowledge_instrs_mem
                   (knowledge_to_canonical_fupd
                      (K (insert r r (knowledge_to_canonical data))) data))))
          (knowledge_to_canonical_fupd
             (K (insert r r (knowledge_to_canonical data))) data)) =
     knowledge_instrs_mem_fupd
       (K (balanced_map_insert listCmp i r (knowledge_instrs_mem data)))
       (knowledge_to_canonical_fupd (K (insert r r (knowledge_to_canonical data)))
          (knowledge_to_latest_fupd (K (insert r r (knowledge_to_latest data))) data))`,
  REWRITE_TAC[knowledge_component_equality] THEN SIMP[]);;

let WPROOF1AUX_CSE_reorder_eq = prove
 (`!data r a.
     knowledge_to_latest_fupd
       (K (insert a r (knowledge_to_latest
            (knowledge_to_canonical_fupd (K (insert r a (knowledge_to_canonical data))) data))))
       (knowledge_to_canonical_fupd (K (insert r a (knowledge_to_canonical data))) data) =
     knowledge_to_canonical_fupd (K (insert r a (knowledge_to_canonical data)))
       (knowledge_to_latest_fupd (K (insert a r (knowledge_to_latest data))) data)`,
  REWRITE_TAC[knowledge_component_equality] THEN SIMP[]);;

let WPROOF1AUX_CSE_wf_facts = prove
 (`!data (s:(A,C,FFI)wl_state) i a.
     data_inv data s /\ balanced_map_lookup listCmp i (knowledge_instrs_mem data) = SOME a ==>
     lookup a (knowledge_to_canonical data) = SOME a /\ ODD a`,
  REWRITE_TAC[data_inv_def; wf_data_def] THEN MESON_TAC[]);;

let add_to_data_aux_correct = prove
 (`!data (s:(A,C,FFI)wl_state) r i p w data' p'.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = NONE /\
     add_to_data_aux data r i p = (data', p') /\
     wl_evaluate (p, s) = (NONE, wl_set_var r w s) /\
     (!v. balanced_map_lookup listCmp i (knowledge_instrs_mem data) = SOME v ==>
          wl_get_var v s = SOME w) /\
     (~EVEN r ==>
        data_inv (knowledge_instrs_mem_fupd
                    (K (balanced_map_insert listCmp i r
                          (knowledge_instrs_mem
                             (knowledge_to_canonical_fupd
                                (K (insert r r (knowledge_to_canonical data))) data))))
                    (knowledge_to_canonical_fupd
                       (K (insert r r (knowledge_to_canonical data))) data))
                 (wl_set_var r w s)) ==>
     wl_evaluate (p', s) = (NONE, wl_set_var r w s) /\
     data_inv data' (wl_set_var r w s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `add_to_data_aux data r i (p:(A)wl_prog) = (data',p')` THEN
  REWRITE_TAC[add_to_data_aux_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `balanced_map_lookup listCmp i (knowledge_instrs_mem data)` THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_SIMP_TAC[data_inv_set_var] THEN
  (TRY(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_add_to_latest_eq] THEN
      MATCH_MP_TAC data_inv_insert_to_latest THEN ASM_REWRITE_TAC[] THEN
      SIMP[domain_insert; IN_INSERT] THEN NO_TAC) THEN
  SUBGOAL_THEN `wl_get_var a (s:(A,C,FFI)wl_state) = SOME w` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Move 0 [r,lookup_any a (knowledge_to_latest data) a],
                             s:(A,C,FFI)wl_state) = (NONE,wl_set_var r w s)` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_Move1 THEN MATCH_MP_TAC WPROOF1AUX_CSE_get_var_latest THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_wf_facts o
              CONJ (ASSUME `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
  SUBGOAL_THEN `~(a:num = r)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `a IN domain (knowledge_to_canonical data)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
  MATCH_MP_TAC data_inv_insert_to_latest THEN
  SIMP[domain_insert; IN_INSERT; wl_get_var_set_var] THEN
  MATCH_MP_TAC data_inv_insert_to_canonical THEN
  ASM_SIMP_TAC[data_inv_set_var; lookup_insert; wl_get_var_set_var; GSYM NOT_EVEN]));;

(* the canonical register of a tracked register is canonical *)

let WPROOF1AUX_CSE_tc_facts = prove
 (`!data (s:(A,C,FFI)wl_state) x y.
     data_inv data s /\ lookup x (knowledge_to_canonical data) = SOME y ==>
     lookup y (knowledge_to_canonical data) = SOME y /\ ODD x /\ ODD y`,
  REWRITE_TAC[data_inv_def; wf_data_def] THEN MESON_TAC[]);;

let canonicalRegs_self_or_fresh = prove
 (`!data (s:(A,C,FFI)wl_state) x.
     data_inv data s ==>
     lookup (canonicalRegs data x) (knowledge_to_canonical data) =
       SOME (canonicalRegs data x) \/
     lookup (canonicalRegs data x) (knowledge_to_canonical data) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[canonicalRegs_def; lookup_any_def] THEN DISCH_TAC THEN
  CASES_ON `lookup x (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF1AUX_CSE_tc_facts o
              CONJ (ASSUME `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
  SIMP_TAC[]);;

let canonicalRegs'_self_or_fresh = prove
 (`!data (s:(A,C,FFI)wl_state) r1 x.
     data_inv data s /\ lookup r1 (knowledge_to_canonical data) = NONE ==>
     lookup (canonicalRegs' r1 data x) (knowledge_to_canonical data) =
       SOME (canonicalRegs' r1 data x) \/
     lookup (canonicalRegs' r1 data x) (knowledge_to_canonical data) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[canonicalRegs'_def; canonicalRegs_def; lookup_any_def;
                                  LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  CASES_ON `lookup x (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF1AUX_CSE_tc_facts o
              CONJ (ASSUME `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `lookup r1 (knowledge_to_canonical data) = NONE` THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let can_mem_arith_ODD_reads = prove
 (`!a:(A)asm_arith. can_mem_arith a ==> ALL ODD (arithReads a)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[can_mem_arith_def; arithReads_def; ALL] THEN MESON_TAC[]);;

(* replace the knowledge of a data_inv goal by an equal record expression *)

let WPROOF1AUX_CSE_REC_TAC (r:term) : tactic = fun (asl,w as g) ->
  let rd = rand (rator w) in
  (SUBGOAL_THEN (mk_eq(rd, r)) SUBST1_TAC THENL
    [REWRITE_TAC[knowledge_component_equality] THEN SIMP[]; ALL_TAC]) g;;

let WPROOF1AUX_CSE_eval_const = prove
 (`!r (w:A word) (s:(A,C,FFI)wl_state).
     wl_evaluate (wl_Inst (asm_Const r w), s) = (NONE, wl_set_var r (wl_Word w) s)`,
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def] THEN CASE_REWRITE_TAC[]);;

let add_to_data_const_correct = prove
 (`!data (s:(A,C,FFI)wl_state) r (w:A word) data' p'.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = NONE /\ ~EVEN r /\
     add_to_data_const data r w = (data', p') ==>
     wl_evaluate (p', s) = (NONE, wl_set_var r (wl_Word w) s) /\
     data_inv data' (wl_set_var r (wl_Word w) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `data_inv data (wl_set_var r (wl_Word (w:A word)) (s:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[data_inv_set_var]; ALL_TAC] THEN
  UNDISCH_TAC `add_to_data_const data r (w:A word) = (data',p')` THEN
  REWRITE_TAC[add_to_data_const_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `balanced_map_lookup listCmp (instToNumList (asm_Const r (w:A word)))
              (knowledge_instrs_mem data)` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_const] THEN
  ALL_TAC THENL
   [(* miss *)
    WPROOF1AUX_CSE_REC_TAC
     `knowledge_to_latest_fupd
        (K (insert r r (knowledge_to_latest
           (knowledge_instrs_mem_fupd
             (K (balanced_map_insert listCmp (instToNumList (asm_Const r (w:A word))) r
                   (knowledge_instrs_mem
                     (knowledge_to_canonical_fupd
                        (K (insert r r (knowledge_to_canonical data))) data))))
             (knowledge_to_canonical_fupd
                (K (insert r r (knowledge_to_canonical data))) data)))))
        (knowledge_instrs_mem_fupd
           (K (balanced_map_insert listCmp (instToNumList (asm_Const r (w:A word))) r
                 (knowledge_instrs_mem
                   (knowledge_to_canonical_fupd
                      (K (insert r r (knowledge_to_canonical data))) data))))
           (knowledge_to_canonical_fupd
              (K (insert r r (knowledge_to_canonical data))) data))` THEN
    MATCH_MP_TAC data_inv_insert_to_latest THEN
    REPEAT CONJ_TAC THENL [ALL_TAC; SIMP[domain_insert; IN_INSERT];
                           SIMP[domain_insert; IN_INSERT]; REWRITE_TAC[]] THEN
    MATCH_MP_TAC data_inv_insert_instrs_Const THEN
    REPEAT CONJ_TAC THENL [ALL_TAC; SIMP[lookup_insert]; SIMP[lookup_insert; wl_set_var_def]] THEN
    MATCH_MP_TAC data_inv_insert_to_canonical THEN
    ASM_REWRITE_TAC[lookup_insert; GSYM NOT_EVEN];
    (* hit *)
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_wf_facts o
                CONJ (ASSUME `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
    SUBGOAL_THEN `~(a:num = r)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
    SUBGOAL_THEN `lookup a (wl_state_locals (s:(A,C,FFI)wl_state)) = SOME (wl_Word (w:A word))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `data_inv data (s:(A,C,FFI)wl_state)` THEN
      REWRITE_TAC[data_inv_def; sem_inv_def] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `a IN domain (knowledge_to_canonical data)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
    MATCH_MP_TAC data_inv_insert_to_latest THEN
    SIMP[domain_insert; IN_INSERT; wl_get_var_set_var; wl_get_var_def] THEN
    MATCH_MP_TAC data_inv_insert_to_canonical THEN
    ASM_SIMP_TAC[lookup_insert; wl_get_var_set_var; GSYM NOT_EVEN; wl_get_var_def]]);;

let add_to_data_LocValue_correct = prove
 (`!data (s:(A,C,FFI)wl_state) r l data' p'.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = NONE /\
     l IN domain (wl_state_code s) /\
     add_to_data_aux data r [48; l] (wl_LocValue r l) = (data', p') ==>
     wl_evaluate (p', s) = (NONE, wl_set_var r (wl_Loc l 0) s) /\
     data_inv data' (wl_set_var r (wl_Loc l 0) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC add_to_data_aux_correct THEN
  MAP_EVERY EXISTS_TAC [`data:knowledge`; `[48; l]`; `wl_LocValue r l:(A)wl_prog`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_LocValue"];
    UNDISCH_TAC `data_inv data (s:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[data_inv_def; sem_inv_def; wl_get_var_def] THEN MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC data_inv_insert_instrs_LocValue THEN
    REPEAT CONJ_TAC THENL [ALL_TAC; SIMP[lookup_insert]; SIMP[lookup_insert; wl_set_var_def]] THEN
    MATCH_MP_TAC data_inv_insert_to_canonical THEN
    ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN; data_inv_set_var]]);;

let WPROOF1AUX_CSE_och_vars = prove
 (`!b r r' (s1:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state).
     wl_get_var r s2 = wl_get_var r' s1 /\ wl_state_store s2 = wl_state_store s1 ==>
     wl_word_exp s2 (wl_Op b [wl_Var r; Lookup CurrHeap]) =
     wl_word_exp s1 (wl_Op b [wl_Var r'; Lookup CurrHeap])`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_word_exp_def; the_words_def; MAP; wl_get_store_def]);;

(* the facts about the canonical source register of OpCurrHeap and loads *)

let WPROOF1AUX_CSE_canon_src = prove
 (`!data (s:(A,C,FFI)wl_state) r1 r2.
     data_inv data s /\ lookup r1 (knowledge_to_canonical data) = NONE /\
     ~EVEN r2 /\ ~(r2 = r1) ==>
     ODD (canonicalRegs' r1 data r2) /\ ~(canonicalRegs' r1 data r2 = r1) /\
     lookup (canonicalRegs' r1 data r2)
       (knowledge_to_canonical (register_read data (canonicalRegs' r1 data r2))) =
       SOME (canonicalRegs' r1 data r2) /\
     lookup r1 (knowledge_to_canonical (register_read data (canonicalRegs' r1 data r2))) =
       NONE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[canonicalRegs'_def; canonicalRegs_def; lookup_any_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `lookup r2 (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[lookup_register_read; GSYM NOT_EVEN] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_tc_facts o
                CONJ (ASSUME `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
    SUBGOAL_THEN `~(a:num = r1)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_register_read] THEN ASM_MESON_TAC[]]);;

let add_to_data_OpCurrHeap_correct = prove
 (`!data (s:(A,C,FFI)wl_state) b r1 r2 r2' w data' p'.
     data_inv data s /\
     lookup r1 (knowledge_to_canonical data) = NONE /\
     r2' = canonicalRegs' r1 data r2 /\
     ~EVEN r2 /\ ~(r2 = r1) /\
     wl_word_exp s (wl_Op b [wl_Var r2; Lookup CurrHeap]) = SOME w /\
     add_to_data_aux (register_read data r2') r1 (OpCurrHeapToNumList b r2')
       (wl_OpCurrHeap b r1 r2) = (data', p') ==>
     wl_evaluate (p', s) = (NONE, wl_set_var r1 w s) /\
     data_inv data' (wl_set_var r1 w s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) = `r2':num`)) THEN
  MP_TAC(SPECL [`data:knowledge`; `s:(A,C,FFI)wl_state`; `r1:num`; `r2:num`]
               WPROOF1AUX_CSE_canon_src) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC add_to_data_aux_correct THEN
  MAP_EVERY EXISTS_TAC [`register_read data (canonicalRegs' r1 data r2)`;
                        `OpCurrHeapToNumList b (canonicalRegs' r1 data r2)`;
                        `wl_OpCurrHeap b r1 r2:(A)wl_prog`] THEN
  ASM_SIMP_TAC[data_inv_register_read; register_read_simps] THEN REPEAT CONJ_TAC THEN
  FIRST
   [ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_OpCurrHeap"] THEN CASE_REWRITE_TAC[] THEN
    NO_TAC;
    X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `wl_get_var (canonicalRegs' r1 data r2) s = wl_get_var r2 (s:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[canonicalRegs'_correct]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_inv_def; sem_inv_def] o
                check (fun th -> concl th = `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:binop`; `canonicalRegs' r1 data r2`; `v:num`] o
                  check (fun th -> can (find_term (fun t -> is_const t &&
                    fst(dest_const t) = "OpCurrHeapToNumList")) (concl th) &&
                    can (find_term (fun t -> is_const t &&
                    fst(dest_const t) = "wl_word_exp")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `wl_word_exp s (wl_Op b [wl_Var (canonicalRegs' r1 data r2); Lookup CurrHeap]) =
                  wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op b [wl_Var r2; Lookup CurrHeap])`
      MP_TAC THENL
     [MATCH_MP_TAC WPROOF1AUX_CSE_och_vars THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[] THEN NO_TAC;
    DISCH_TAC THEN MATCH_MP_TAC data_inv_insert_instrs_OpCurrHeap THEN
    EXISTS_TAC `w:(A)word_loc` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC data_inv_insert_to_canonical THEN
      ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN; data_inv_set_var; data_inv_register_read];
      SIMP[lookup_insert];
      SIMP[lookup_insert] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op b [wl_Var r2; Lookup CurrHeap])` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC WPROOF1AUX_CSE_och_vars THEN
      ASM_SIMP_TAC[wl_get_var_set_var; canonicalRegs'_correct] THEN SIMP[wl_set_var_def];
      SIMP[wl_get_var_set_var]] THEN NO_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* the reads of a canonicalised storable arith instruction are canonical    *)
(* or untracked                                                             *)

let WPROOF1AUX_CSE_arith_reads_sof = prove
 (`!data (s:(A,C,FFI)wl_state) (a:(A)asm_arith).
     data_inv data s /\
     can_mem_arith (canonicalArith data a) /\
     lookup (firstRegOfArith a) (knowledge_to_canonical data) = NONE ==>
     ALL (\x. lookup x (knowledge_to_canonical data) = SOME x \/
              lookup x (knowledge_to_canonical data) = NONE)
         (arithReads (canonicalArith data a))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  REWRITE_TAC[canonicalArith_def; firstRegOfArith_def] THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[canonicalImmReg'_def; can_mem_arith_def; arithReads_def; ALL] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[canonicalRegs_self_or_fresh; canonicalRegs'_self_or_fresh]);;

let WPROOF1AUX_CSE_CA (tm:term) =
  vsubst [`canonicalArith data (a:(A)asm_arith)`, `a':(A)asm_arith`] tm;;

let add_to_data_Arith_correct = prove
 (`!data (s:(A,C,FFI)wl_state) a a' r w data' p'.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = NONE /\
     a' = canonicalArith data a /\
     can_mem_arith a' /\ ~MEM r (arithReads a') /\
     r = firstRegOfArith a /\
     wl_evaluate (wl_Inst (asm_Arith a), s) = (NONE, wl_set_var r w s) /\
     add_to_data (register_reads data (arithReads a')) r (asm_Arith a') (asm_Arith a)
       = (data', p') ==>
     wl_evaluate (p', s) = (NONE, wl_set_var r w s) /\
     data_inv data' (wl_set_var r w s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                        lhs (concl th) = `r:num`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                        lhs (concl th) = `a':(A)asm_arith`)) THEN
  SUBGOAL_THEN (WPROOF1AUX_CSE_CA `wl_evaluate (wl_Inst (asm_Arith a'), s:(A,C,FFI)wl_state) =
                (NONE, wl_set_var (firstRegOfArith (a:(A)asm_arith)) w s)`) ASSUME_TAC THENL
   [UNDISCH_TAC
      `wl_evaluate (wl_Inst (asm_Arith a), s:(A,C,FFI)wl_state) =
       (NONE, wl_set_var (firstRegOfArith (a:(A)asm_arith)) w s)` THEN
    REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN
    ASM_SIMP_TAC[canonicalArith_correct]; ALL_TAC] THEN
  SUBGOAL_THEN (WPROOF1AUX_CSE_CA
   `ALL (\x. lookup x (knowledge_to_canonical
               (register_reads data (arithReads (a':(A)asm_arith)))) = SOME x)
        (arithReads a')`) ASSUME_TAC THENL
   [MP_TAC(SPECL [`data:knowledge`; `s:(A,C,FFI)wl_state`; `a:(A)asm_arith`]
                 WPROOF1AUX_CSE_arith_reads_sof) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `canonicalArith data (a:(A)asm_arith)` can_mem_arith_ODD_reads) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ALL_MEM; lookup_register_reads; GSYM NOT_EVEN] THEN
    MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (WPROOF1AUX_CSE_CA
   `lookup (firstRegOfArith (a:(A)asm_arith))
      (knowledge_to_canonical (register_reads data (arithReads (a':(A)asm_arith)))) = NONE`)
    ASSUME_TAC THENL [ASM_REWRITE_TAC[lookup_register_reads]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "add_to_data")) (concl th))) THEN
  REWRITE_TAC[add_to_data_def; LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC add_to_data_aux_correct THEN
  MAP_EVERY EXISTS_TAC [WPROOF1AUX_CSE_CA `register_reads data (arithReads (a':(A)asm_arith))`;
                        WPROOF1AUX_CSE_CA `instToNumList (asm_Arith (a':(A)asm_arith))`;
                        `wl_Inst (asm_Arith (a:(A)asm_arith))`] THEN
  ASM_SIMP_TAC[data_inv_register_reads; register_reads_simps] THEN REPEAT CONJ_TAC THEN
  FIRST
   [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_inv_def; sem_inv_def] o
                check (fun th -> concl th = `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`canonicalArith data (a:(A)asm_arith)`; `v:num`] o
                  check (fun th -> can (find_term (fun t -> is_const t &&
                    fst(dest_const t) = "firstRegOfArith")) (concl th) &&
                    is_forall (concl th))) THEN
    ASM_REWRITE_TAC[firstRegOfArith_canonicalArith] THEN
    DISCH_THEN(X_CHOOSE_THEN `w':(A)word_loc` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (lhs (concl th)))) THEN
    SIMP[PAIR_EQ; wl_set_var_def; insert_eq] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    DISCH_TAC THEN MATCH_MP_TAC data_inv_insert_instrs_Arith THEN
    EXISTS_TAC `w:(A)word_loc` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC data_inv_insert_to_canonical THEN
      ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN; data_inv_set_var; data_inv_register_reads];
      SIMP[lookup_insert];
      ASM_REWRITE_TAC[];
      UNDISCH_TAC (WPROOF1AUX_CSE_CA
        `ALL (\x. lookup x (knowledge_to_canonical
               (register_reads data (arithReads (a':(A)asm_arith)))) = SOME x)
        (arithReads a')`) THEN
      UNDISCH_TAC (WPROOF1AUX_CSE_CA
        `~MEM (firstRegOfArith (a:(A)asm_arith)) (arithReads (a':(A)asm_arith))`) THEN
      SIMP[in_names_set_def; GSYM ALL_MEM; lookup_insert] THEN MESON_TAC[];
      SIMP[wl_get_var_set_var];
      MP_TAC(SPECL [`canonicalArith data (a:(A)asm_arith)`; `firstRegOfArith (a:(A)asm_arith)`;
                    `w:(A)word_loc`; `w:(A)word_loc`; `s:(A,C,FFI)wl_state`]
                   evaluate_arith_set_var) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[firstRegOfArith_canonicalArith]] THEN NO_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let data_inv_insert_loads = prove
 (`!data (s:(A,C,FFI)wl_state) r op a (ofs:A word) w.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     lookup a (knowledge_to_canonical data) = SOME a /\
     ~is_store op /\
     wl_get_var r s = SOME w /\
     (!r'. wl_evaluate (wl_Inst (Mem op r' (Addr a ofs)), s) =
           (NONE, wl_set_var r' w s)) ==>
     data_inv (knowledge_loads_mem_fupd
                 (K (balanced_map_insert listCmp (loadToNumList op a ofs) r
                       (knowledge_loads_mem data))) data) s`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let WPROOF1AUX_CSE_add_to_latest_eq2 = prove
 (`!data i r.
     knowledge_to_latest_fupd
       (K (insert r r (knowledge_to_latest
            (knowledge_loads_mem_fupd
              (K (balanced_map_insert listCmp i r
                    (knowledge_loads_mem
                       (knowledge_to_canonical_fupd
                          (K (insert r r (knowledge_to_canonical data))) data))))
              (knowledge_to_canonical_fupd
                 (K (insert r r (knowledge_to_canonical data))) data)))))
       (knowledge_loads_mem_fupd
          (K (balanced_map_insert listCmp i r
                (knowledge_loads_mem
                   (knowledge_to_canonical_fupd
                      (K (insert r r (knowledge_to_canonical data))) data))))
          (knowledge_to_canonical_fupd
             (K (insert r r (knowledge_to_canonical data))) data)) =
     knowledge_loads_mem_fupd
       (K (balanced_map_insert listCmp i r (knowledge_loads_mem data)))
       (knowledge_to_canonical_fupd (K (insert r r (knowledge_to_canonical data)))
          (knowledge_to_latest_fupd (K (insert r r (knowledge_to_latest data))) data))`,
  REWRITE_TAC[knowledge_component_equality] THEN SIMP[]);;

let WPROOF1AUX_CSE_wf_facts2 = prove
 (`!data (s:(A,C,FFI)wl_state) i a.
     data_inv data s /\ balanced_map_lookup listCmp i (knowledge_loads_mem data) = SOME a ==>
     lookup a (knowledge_to_canonical data) = SOME a /\ ODD a`,
  REWRITE_TAC[data_inv_def; wf_data_def] THEN MESON_TAC[]);;

let add_to_load_aux_correct = prove
 (`!data (s:(A,C,FFI)wl_state) r i p w data' p'.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = NONE /\
     add_to_load_aux data r i p = (data', p') /\
     wl_evaluate (p, s) = (NONE, wl_set_var r w s) /\
     (!v. balanced_map_lookup listCmp i (knowledge_loads_mem data) = SOME v ==>
          wl_get_var v s = SOME w) /\
     (~EVEN r ==>
        data_inv (knowledge_loads_mem_fupd
                    (K (balanced_map_insert listCmp i r
                          (knowledge_loads_mem
                             (knowledge_to_canonical_fupd
                                (K (insert r r (knowledge_to_canonical data))) data))))
                    (knowledge_to_canonical_fupd
                       (K (insert r r (knowledge_to_canonical data))) data))
                 (wl_set_var r w s)) ==>
     wl_evaluate (p', s) = (NONE, wl_set_var r w s) /\
     data_inv data' (wl_set_var r w s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `add_to_load_aux data r i (p:(A)wl_prog) = (data',p')` THEN
  REWRITE_TAC[add_to_load_aux_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `balanced_map_lookup listCmp i (knowledge_loads_mem data)` THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_SIMP_TAC[data_inv_set_var] THEN
  (TRY(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_add_to_latest_eq2] THEN
      MATCH_MP_TAC data_inv_insert_to_latest THEN ASM_REWRITE_TAC[] THEN
      SIMP[domain_insert; IN_INSERT] THEN NO_TAC) THEN
  SUBGOAL_THEN `wl_get_var a (s:(A,C,FFI)wl_state) = SOME w` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Move 0 [r,lookup_any a (knowledge_to_latest data) a],
                             s:(A,C,FFI)wl_state) = (NONE,wl_set_var r w s)` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_Move1 THEN MATCH_MP_TAC WPROOF1AUX_CSE_get_var_latest THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_wf_facts2 o
              CONJ (ASSUME `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
  SUBGOAL_THEN `~(a:num = r)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `a IN domain (knowledge_to_canonical data)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
  MATCH_MP_TAC data_inv_insert_to_latest THEN
  SIMP[domain_insert; IN_INSERT; wl_get_var_set_var] THEN
  MATCH_MP_TAC data_inv_insert_to_canonical THEN
  ASM_SIMP_TAC[data_inv_set_var; lookup_insert; wl_get_var_set_var; GSYM NOT_EVEN]));;

let add_to_load_correct = prove
 (`!data (s:(A,C,FFI)wl_state) op r a a' (ofs:A word) w data' p'.
     data_inv data s /\
     lookup r (knowledge_to_canonical data) = NONE /\
     a' = canonicalRegs' r data a /\
     ~is_store op /\ ~EVEN r /\ ~EVEN a /\ ~(a = r) /\
     wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s) = (NONE, wl_set_var r w s) /\
     add_to_load_aux (register_read data a') r (loadToNumList op a' ofs)
       (wl_Inst (Mem op r (Addr a ofs))) = (data', p') ==>
     wl_evaluate (p', s) = (NONE, wl_set_var r w s) /\
     data_inv data' (wl_set_var r w s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                        lhs (concl th) = `a':num`)) THEN
  MP_TAC(SPECL [`data:knowledge`; `s:(A,C,FFI)wl_state`; `r:num`; `a:num`]
               WPROOF1AUX_CSE_canon_src) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lookup (canonicalRegs' r data a) (wl_state_locals (s:(A,C,FFI)wl_state)) =
                lookup a (wl_state_locals s)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM wl_get_var_def] THEN ASM_SIMP_TAC[canonicalRegs'_correct]; ALL_TAC] THEN
  SUBGOAL_THEN `!r2. wl_evaluate (wl_Inst (Mem op r2 (Addr (canonicalRegs' r data a) ofs)),
                                  s:(A,C,FFI)wl_state) = (NONE, wl_set_var r2 w s)`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC evaluate_load_any_dest THEN
    MAP_EVERY EXISTS_TAC [`r:num`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC evaluate_load_change_addr THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC add_to_load_aux_correct THEN
  MAP_EVERY EXISTS_TAC [`register_read data (canonicalRegs' r data a)`;
                        `loadToNumList op (canonicalRegs' r data a) (ofs:A word)`;
                        `wl_Inst (Mem op r (Addr a (ofs:A word)))`] THEN
  ASM_SIMP_TAC[data_inv_register_read; register_read_simps] THEN REPEAT CONJ_TAC THEN
  FIRST
   [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_inv_def; sem_inv_def] o
                check (fun th -> concl th = `data_inv data (s:(A,C,FFI)wl_state)`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`op:memop`; `canonicalRegs' r data a`; `ofs:A word`;
                                  `v:num`] o
                  check (fun th -> can (find_term (fun t -> is_const t &&
                    fst(dest_const t) = "loadToNumList")) (concl th) &&
                    can (find_term (fun t -> is_const t &&
                    fst(dest_const t) = "wl_evaluate")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w':(A)word_loc` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `w':(A)word_loc`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP[PAIR_EQ; wl_set_var_def; insert_eq] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    TRY DISCH_TAC THEN MATCH_MP_TAC data_inv_insert_loads THEN
    EXISTS_TAC `w:(A)word_loc` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC data_inv_insert_to_canonical THEN
      ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN; data_inv_set_var; data_inv_register_read];
      SIMP[lookup_insert];
      SIMP[lookup_insert] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      SIMP[wl_get_var_set_var];
      GEN_TAC THEN ASM_SIMP_TAC[evaluate_load_set_var]] THEN NO_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let MAP_FST_lemma = prove
 (`!moves:(A#num)list.
     MAP FST (MAP (\(a,b). (a,canonicalRegs data b)) moves) = MAP FST moves`,
  REWRITE_TAC[MAP_MAP_o] THEN GEN_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN SIMP[]);;

let MAP_SND_lemma = prove
 (`!(moves:(B#num)list) x.
     wl_get_vars (MAP SND moves) (s:(A,C,FFI)wl_state) = SOME x /\ data_inv data s ==>
     wl_get_vars (MAP SND (MAP (\(a,b). (a,canonicalRegs data b)) moves)) s = SOME x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAP SND (MAP (\(a,b). (a,canonicalRegs data b)) (moves:(B#num)list)) =
                MAP (canonicalRegs data) (MAP SND moves)` SUBST1_TAC THENL
  [REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN SIMP[]; ALL_TAC] THEN
  SUBGOAL_THEN `!l. wl_get_vars (MAP (canonicalRegs data) l) (s:(A,C,FFI)wl_state) =
                    wl_get_vars l s` (fun th -> ASM_REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; wl_get_vars_def; canonicalRegs_correct]);;

let lookup_map_insert0 = prove
 (CASE_TERM
  `!xs r. lookup r (map_insert xs (m:A spt)) =
          match ALOOKUP xs r with NONE -> lookup r m | SOME r' -> SOME r'`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[map_insert_def; ALOOKUP_THM] THEN CASE_REWRITE_TAC[];
   SPEC_TAC(`h:num#A`,`h:num#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
   ASM_REWRITE_TAC[map_insert_def; ALOOKUP_THM; lookup_insert] THEN
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let WPROOF1AUX_CSE_get_vars_CONS = prove
 (`!v vs x (s:(A,C,FFI)wl_state).
     wl_get_vars (CONS v vs) s = SOME x <=>
     ?y ys. wl_get_var v s = SOME y /\ wl_get_vars vs s = SOME ys /\ x = CONS y ys`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  CASES_ON `wl_get_var v (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  CASES_ON `wl_get_vars vs (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let WPROOF1AUX_CSE_lookup_alist_insert_notin = prove
 (`!xs (ys:A list) (m:A spt) r.
     ~MEM r xs ==> lookup r (alist_insert xs ys m) = lookup r m`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_insert_def; MEM; DE_MORGAN_THM] THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[alist_insert_def; lookup_insert]);;

let get_set_vars_lemma = prove
 (`!xs xs' x y (s:(A,C,FFI)wl_state).
     ~MEM x xs /\ ~MEM y xs ==>
     wl_get_var x s = wl_get_var y s ==>
     wl_get_var x (wl_set_vars xs xs' s) = wl_get_var y (wl_set_vars xs xs' s)`,
  REWRITE_TAC[wl_get_var_def; wl_set_vars_def] THEN SIMP[] THEN
  SIMP_TAC[WPROOF1AUX_CSE_lookup_alist_insert_notin]);;

let get_set_vars_not_in = prove
 (`!rs vs r (s:(A,C,FFI)wl_state).
     ~MEM r rs ==> wl_get_var r (wl_set_vars rs vs s) = wl_get_var r s`,
  REWRITE_TAC[wl_get_var_def; wl_set_vars_def] THEN SIMP[] THEN
  SIMP_TAC[WPROOF1AUX_CSE_lookup_alist_insert_notin]);;

let MEM_FST_reduc = prove
 (`!moves r (p_2:B). MEM (r,p_2) moves ==> MEM (r:A) (MAP FST moves)`,
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[FST]);;

let get_set_vars_in = prove
 (`!moves r p_2 x (s:(A,C,FFI)wl_state).
     MEM (r,p_2) moves ==>
     ALL_DISTINCT (MAP FST moves) ==>
     wl_get_vars (MAP SND moves) s = SOME x ==>
     wl_get_var r (wl_set_vars (MAP FST moves) x s) = wl_get_var p_2 s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `p:num`; `r:num`; `p_2:num`;
                       `x:((A)word_loc)list`; `s:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; WPROOF1AUX_CSE_get_vars_CONS; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[wl_get_var_def; wl_set_vars_def; alist_insert_def] THEN SIMP[lookup_insert] THENL
  [ASM_MESON_TAC[wl_get_var_def]; ALL_TAC] THEN
  SUBGOAL_THEN `~(r:num = q)` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_MESON_TAC[MEM_FST_reduc]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `p_2:num`; `ys:((A)word_loc)list`; `s:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[wl_get_var_def; wl_set_vars_def] THEN SIMP[]);;

let get_set_vars_in_2 = prove
 (`!moves r p_2 x' x data (s:(A,C,FFI)wl_state).
     MEM (r,p_2) moves ==>
     ALL_DISTINCT (MAP FST moves) ==>
     lookup p_2 (knowledge_to_canonical data) = SOME x' ==>
     wl_get_vars (MAP SND (MAP (\(a,b). (a,canonicalRegs data b)) moves)) s = SOME x ==>
     wl_get_var r (wl_set_vars (MAP FST moves) x s) = wl_get_var x' s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `canonicalRegs data p_2 = x'` ASSUME_TAC THENL
  [REWRITE_TAC[canonicalRegs_def; lookup_any_def] THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`MAP (\(a,b). (a,canonicalRegs data b)) (moves:(num#num)list)`;
                 `r:num`; `x':num`; `x:((A)word_loc)list`; `s:(A,C,FFI)wl_state`]
                get_set_vars_in) THEN
  ASM_REWRITE_TAC[MAP_FST_lemma] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(r:num,p_2:num)` THEN SIMP[]);;

let lookup_set_vars_not_in = prove
 (`!(moves:(num#B)list) v (data:knowledge) c x.
     ~MEM v (MAP FST moves) ==>
     lookup v (wl_state_locals (s:(A,C,FFI)wl_state)) = SOME (wl_Word c) ==>
     lookup v (wl_state_locals (wl_set_vars (MAP FST moves) x s)) = SOME (wl_Word c)`,
  REWRITE_TAC[wl_set_vars_def] THEN SIMP[WPROOF1AUX_CSE_lookup_alist_insert_notin]);;

let list_insert_insert = prove
 (`!l n an. list_insert l (insert n one an) = insert n one (list_insert l an)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_insert_def] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [insert_insert] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[insert_shadow]);;

let data_inv_insert_canonical_pair = prove
 (`!data (s:(A,C,FFI)wl_state) x y tc tl.
     data_inv (knowledge_to_canonical_fupd (K tc) (knowledge_to_latest_fupd (K tl) data)) s /\
     lookup x tc = NONE /\
     lookup y (insert x y tc) = SOME y /\
     ODD x /\ ODD y /\
     wl_get_var x s = wl_get_var y s ==>
     data_inv (knowledge_to_canonical_fupd (K (insert x y tc))
                 (knowledge_to_latest_fupd (K tl) data)) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`knowledge_to_canonical_fupd (K tc) (knowledge_to_latest_fupd (K tl) data)`;
                 `s:(A,C,FFI)wl_state`; `x:num`; `y:num`] data_inv_insert_to_canonical) THEN
  SIMP_NOASM[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let data_inv_insert_pair = prove
 (`!data (s:(A,C,FFI)wl_state) x y tc tl.
     data_inv (knowledge_to_canonical_fupd (K tc) (knowledge_to_latest_fupd (K tl) data)) s /\
     lookup x tc = NONE /\ lookup y tc = SOME y /\
     ODD x /\ ODD y /\ wl_get_var x s = wl_get_var y s ==>
     data_inv (knowledge_to_canonical_fupd (K (insert x y tc))
                 (knowledge_to_latest_fupd (K (insert y x tl)) data)) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(y:num = x)` ASSUME_TAC THENL
  [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`knowledge_to_canonical_fupd (K (insert x y tc))
                    (knowledge_to_latest_fupd (K tl) data)`;
                 `s:(A,C,FFI)wl_state`; `y:num`; `x:num`] data_inv_insert_to_latest) THEN
  SIMP_NOASM[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[domain_lookup; lookup_insert] THEN CONJ_TAC THENL
  [MATCH_MP_TAC data_inv_insert_canonical_pair THEN ASM_REWRITE_TAC[lookup_insert];
   MESON_TAC[]]);;

let data_inv_move_pairs = prove
 (`!ps data (s:(A,C,FFI)wl_state).
     data_inv data s /\
     ALL_DISTINCT (MAP FST ps) /\
     ALL (\(x,y). lookup x (knowledge_to_canonical data) = NONE /\
                  lookup y (knowledge_to_canonical data) = SOME y /\
                  ODD x /\ wl_get_var x s = wl_get_var y s) ps ==>
     data_inv (knowledge_to_canonical_fupd (K (map_insert ps (knowledge_to_canonical data)))
                (knowledge_to_latest_fupd
                   (K (map_insert (MAP (\(a,b). (b,a)) ps) (knowledge_to_latest data)))
                   data)) s`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[map_insert_def; MAP] THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `knowledge_to_canonical_fupd (K (knowledge_to_canonical data))
       (knowledge_to_latest_fupd (K (knowledge_to_latest data)) data) = data`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   SIMP[knowledge_component_equality]; ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `data:knowledge`; `s:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; ALL; map_insert_def] THEN SIMP_NOASM[] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN SIMP_NOASM[] THEN STRIP_TAC THEN
  MATCH_MP_TAC data_inv_insert_pair THEN
  SUBGOAL_THEN `ALOOKUP (t:(num#num)list) x = NONE /\ ALOOKUP t y = NONE`
    STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; EXISTS_PAIR_THM] THEN
   ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `ODD y` ASSUME_TAC THENL
  [MP_TAC(ASSUME `data_inv data (s:(A,C,FFI)wl_state)`) THEN
   REWRITE_TAC[data_inv_def; wf_data_def] THEN
   DISCH_THEN(MP_TAC o SPECL [`y:num`;`y:num`] o CONJUNCT1 o CONJUNCT1) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_map_insert0] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN SIMP_NOASM[] THEN ASM_REWRITE_TAC[]);;


let canonicalMoveRegs_lemma = prove
 (`!data (s:(A,C,FFI)wl_state) rs vs.
     data_inv data s /\
     ALL_DISTINCT (MAP FST rs) /\
     wl_get_vars (MAP SND rs) s = SOME vs ==>
     data_inv (canonicalMoveRegs data rs) (wl_set_vars (MAP FST rs) vs s)`,
  (REPEAT STRIP_TAC THEN REWRITE_TAC[canonicalMoveRegs_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[data_inv_empty]]) THEN
  (SUBGOAL_THEN `data_inv (register_reads data (MAP SND (rs:(num#num)list))) (s:(A,C,FFI)wl_state)` ASSUME_TAC THENL
  [MATCH_MP_TAC data_inv_register_reads THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. MEM a (MAP FST (rs:(num#num)list)) ==>
       lookup a (knowledge_to_canonical (register_reads data (MAP SND rs))) = NONE`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM ALL_MEM; keep_data_def; IS_NONE_EQ_NONE] o
     check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false)) THEN
   REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC data_inv_move_pairs THEN REPEAT CONJ_TAC THENL
  [ASM_SIMP_TAC[data_inv_set_vars; GSYM ALL_MEM];
   REWRITE_TAC[MAP_FST_lemma] THEN MATCH_MP_TAC ALL_DISTINCT_MAP_FST_FILTER THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM] THEN
  SIMP_NOASM[PAIR_EQ]) THEN
  (MAP_EVERY X_GEN_TAC [`a:num`; `c:num`] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `MEM (b:num) (MAP SND (rs:(num#num)list))` ASSUME_TAC THENL
  [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(a:num,b:num)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (a:num) (MAP FST (rs:(num#num)list))` ASSUME_TAC THENL
  [ASM_MESON_TAC[MEM_FST_reduc]; ALL_TAC] THEN
  SUBGOAL_THEN `!r v. lookup r (knowledge_to_canonical data) = SOME v ==>
                      lookup v (knowledge_to_canonical data) = SOME v` ASSUME_TAC THENL
  [MP_TAC(ASSUME `data_inv data (s:(A,C,FFI)wl_state)`) THEN
   REWRITE_TAC[data_inv_def; wf_data_def] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lookup (canonicalRegs (register_reads data (MAP SND rs)) b)
       (knowledge_to_canonical (register_reads data (MAP SND (rs:(num#num)list)))) =
       SOME (canonicalRegs (register_reads data (MAP SND rs)) b)` ASSUME_TAC THENL
  [REWRITE_TAC[canonicalRegs_def; lookup_any_def; lookup_register_reads] THEN
   ASM_REWRITE_TAC[] THEN
   CASES_ON `lookup b (knowledge_to_canonical data)` THEN
   ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
   RES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (canonicalRegs (register_reads data (MAP SND rs)) b)
                     (MAP FST (rs:(num#num)list))` ASSUME_TAC THENL
  [DISCH_TAC THEN RES_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  ASM_SIMP_TAC[get_set_vars_not_in; canonicalRegs_correct] THEN
  MP_TAC(ISPECL [`rs:(num#num)list`; `a:num`; `b:num`; `vs:((A)word_loc)list`;
                 `s:(A,C,FFI)wl_state`] get_set_vars_in) THEN
  ASM_REWRITE_TAC[]));;

let if_eq_rw = prove
 (`(if (x:A) = y then y else x) = x`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let _ = cake_add_simps [if_eq_rw];;

let evaluate_arith_clock = prove
 (`!a w (s:(A,C,FFI)wl_state) c td.
     can_mem_arith a ==>
     (wl_evaluate (wl_Inst (asm_Arith a),
                   wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td) s)) =
        (NONE, wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td)
                 (wl_set_var (firstRegOfArith a) w s))) <=>
      wl_evaluate (wl_Inst (asm_Arith a), s) =
        (NONE, wl_set_var (firstRegOfArith a) w s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td)
      (wl_set_var (firstRegOfArith (a:(A)asm_arith)) w (s:(A,C,FFI)wl_state))) =
    wl_set_var (firstRegOfArith a) w
      (wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td) s))` SUBST1_TAC THENL
  [REWRITE_TAC[wl_set_var_def] THEN SIMP[]; ALL_TAC] THEN
  MATCH_MP_TAC WPROOF1AUX_CSE_arith_agree_iff THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let evaluate_load_clock = prove
 (`!op r a ofs w (s:(A,C,FFI)wl_state) c td.
     ~is_store op ==>
     (wl_evaluate (wl_Inst (Mem op r (Addr a ofs)),
                   wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td) s)) =
        (NONE, wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td)
                 (wl_set_var r w s))) <=>
      wl_evaluate (wl_Inst (Mem op r (Addr a ofs)), s) = (NONE, wl_set_var r w s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td)
      (wl_set_var r w (s:(A,C,FFI)wl_state))) =
    wl_set_var r w (wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td) s))`
    SUBST1_TAC THENL
  [REWRITE_TAC[wl_set_var_def] THEN SIMP[]; ALL_TAC] THEN
  MATCH_MP_TAC WPROOF1AUX_CSE_load_agree_iff THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let data_inv_clock = prove
 (`!data (s:(A,C,FFI)wl_state) c td.
     data_inv data s ==>
     data_inv data (wl_state_clock_fupd (K c) (wl_state_termdep_fupd (K td) s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC data_inv_state_agree THEN
  EXISTS_TAC `s:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let wf_data_empty = prove
 (`wf_data (:A) empty_data`,
  REWRITE_TAC[wf_data_def; empty_data_def] THEN SIMP[] THEN
  REWRITE_TAC[lookup_def; balanced_map_empty_def; balanced_map_lookup_def;
              balanced_map_invariant_def; ALOOKUP_DEF; ALL_DISTINCT; MAP; option_DISTINCT;
              domain_def; NOT_IN_EMPTY]);;
let _ = cake_add_simps [wf_data_empty];;

let wf_data_loads_wipe = prove
 (`!data. wf_data (:A) data ==>
          wf_data (:A) (knowledge_loads_mem_fupd (K balanced_map_empty) data)`,
  GEN_TAC THEN
  REWRITE_TAC[wf_data_def; knowledge_INFO.ri_accfupds; K_THM; lookup_listCmp_empty;
              invariant_listCmp_empty; option_DISTINCT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let wf_data_invalidate = prove
 (`!data r. wf_data (:A) data ==> wf_data (:A) (invalidate_data data r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invalidate_data_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[wf_data_empty]);;

let wf_data_invalidate_regs = prove
 (`!rs data. wf_data (:A) data ==> wf_data (:A) (invalidate_regs data rs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[invalidate_regs_def] THEN
  ASM_MESON_TAC[wf_data_invalidate]);;

let wf_data_insert_to_canonical = prove
 (`!data x y.
     wf_data (:A) data /\
     lookup x (knowledge_to_canonical data) = NONE /\
     lookup y (insert x y (knowledge_to_canonical data)) = SOME y /\
     ODD x /\ ODD y ==>
     wf_data (:A) (knowledge_to_canonical_fupd
                     (K (insert x y (knowledge_to_canonical data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN WPROOF1AUX_CSE_CLAUSE_TAC);;

let wf_data_insert_to_latest = prove
 (`!data x y.
     wf_data (:A) data /\
     x IN domain (knowledge_to_canonical data) /\
     y IN domain (knowledge_to_canonical data) ==>
     wf_data (:A) (knowledge_to_latest_fupd
                     (K (insert x y (knowledge_to_latest data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN WPROOF1AUX_CSE_CLAUSE_TAC);;

let wf_data_register_read = prove
 (`!data r. wf_data (:A) data ==> wf_data (:A) (register_read data r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[register_read_def; keep_data_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC wf_data_insert_to_canonical THEN
  ASM_REWRITE_TAC[lookup_insert; GSYM NOT_EVEN] THEN
  POP_ASSUM MP_TAC THEN
  CASES_ON `lookup r (knowledge_to_canonical data)` THEN REWRITE_TAC[IS_NONE_DEF]);;

let wf_data_register_reads = prove
 (`!rs data. wf_data (:A) data ==> wf_data (:A) (register_reads data rs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[register_reads_def] THEN
  ASM_MESON_TAC[wf_data_register_read]);;

let wf_data_insert_instrs_Const = prove
 (`!data r n (w:A word).
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = SOME r ==>
     wf_data (:A) (knowledge_instrs_mem_fupd
                     (K (balanced_map_insert listCmp (instToNumList (asm_Const n w:(A)inst)) r
                           (knowledge_instrs_mem data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let wf_data_insert_instrs_Arith = prove
 (`!data r (a:(A)asm_arith).
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     can_mem_arith a /\ in_names_set a (knowledge_to_canonical data) ==>
     wf_data (:A) (knowledge_instrs_mem_fupd
                     (K (balanced_map_insert listCmp (instToNumList (asm_Arith a)) r
                           (knowledge_instrs_mem data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let wf_data_insert_instrs_OpCurrHeap = prove
 (`!data r op src.
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     lookup src (knowledge_to_canonical data) = SOME src ==>
     wf_data (:A) (knowledge_instrs_mem_fupd
                     (K (balanced_map_insert listCmp (OpCurrHeapToNumList op src) r
                           (knowledge_instrs_mem data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let wf_data_insert_instrs_LocValue = prove
 (`!data r l.
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = SOME r ==>
     wf_data (:A) (knowledge_instrs_mem_fupd
                     (K (balanced_map_insert listCmp [48; l] r
                           (knowledge_instrs_mem data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;

let wf_data_insert_loads = prove
 (`!data r op a (ofs:A word).
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = SOME r /\
     lookup a (knowledge_to_canonical data) = SOME a ==>
     wf_data (:A) (knowledge_loads_mem_fupd
                     (K (balanced_map_insert listCmp (loadToNumList op a ofs) r
                           (knowledge_loads_mem data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[lookup_insert_listCmp] THEN
  WPROOF1AUX_CSE_CLAUSE2_TAC);;


let WPROOF1AUX_CSE_wf_facts_wf = prove
 (`!data i a.
     wf_data (:A) data /\
     balanced_map_lookup listCmp i (knowledge_instrs_mem data) = SOME a ==>
     lookup a (knowledge_to_canonical data) = SOME a /\ ODD a`,
  REWRITE_TAC[wf_data_def] THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_wf_facts2_wf = prove
 (`!data i a.
     wf_data (:A) data /\
     balanced_map_lookup listCmp i (knowledge_loads_mem data) = SOME a ==>
     lookup a (knowledge_to_canonical data) = SOME a /\ ODD a`,
  REWRITE_TAC[wf_data_def] THEN MESON_TAC[]);;

let wf_add_to_data_aux = prove
 (`!data r i (p:(A)wl_prog) data' p'.
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = NONE /\
     add_to_data_aux data r i p = (data', p') /\
     (~EVEN r ==>
        wf_data (:A)
          (knowledge_instrs_mem_fupd
             (K (balanced_map_insert listCmp i r
                   (knowledge_instrs_mem
                      (knowledge_to_canonical_fupd
                         (K (insert r r (knowledge_to_canonical data))) data))))
             (knowledge_to_canonical_fupd
                (K (insert r r (knowledge_to_canonical data))) data))) ==>
     wf_data (:A) data'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `add_to_data_aux data r i (p:(A)wl_prog) = (data',p')` THEN
  REWRITE_TAC[add_to_data_aux_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `balanced_map_lookup listCmp i (knowledge_instrs_mem data)` THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[] THEN
  (TRY(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_add_to_latest_eq] THEN
      MATCH_MP_TAC wf_data_insert_to_latest THEN ASM_REWRITE_TAC[] THEN
      SIMP[domain_insert; IN_INSERT] THEN NO_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_wf_facts_wf o
              CONJ (ASSUME `wf_data (:A) data`)) THEN
  SUBGOAL_THEN `~(a:num = r)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `a IN domain (knowledge_to_canonical data)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
  MATCH_MP_TAC wf_data_insert_to_latest THEN
  SIMP[domain_insert; IN_INSERT] THEN
  MATCH_MP_TAC wf_data_insert_to_canonical THEN
  ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN]));;

(* as WPROOF1AUX_CSE_REC_TAC, for a wf_data goal *)

let WPROOF1AUX_CSE_REC_WF_TAC (r:term) : tactic = fun (asl,w as g) ->
  let rd = rand w in
  (SUBGOAL_THEN (mk_eq(rd, r)) SUBST1_TAC THENL
    [REWRITE_TAC[knowledge_component_equality] THEN SIMP[]; ALL_TAC]) g;;

let wf_add_to_data_const = prove
 (`!data r (w:A word) data' p'.
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = NONE /\ ~EVEN r /\
     add_to_data_const data r w = (data', p') ==>
     wf_data (:A) data'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `add_to_data_const data r (w:A word) = (data',p')` THEN
  REWRITE_TAC[add_to_data_const_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `balanced_map_lookup listCmp (instToNumList (asm_Const r (w:A word)))
              (knowledge_instrs_mem data)` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THENL
   [(* miss *)
    WPROOF1AUX_CSE_REC_WF_TAC
     `knowledge_to_latest_fupd
        (K (insert r r (knowledge_to_latest
           (knowledge_instrs_mem_fupd
             (K (balanced_map_insert listCmp (instToNumList (asm_Const r (w:A word))) r
                   (knowledge_instrs_mem
                     (knowledge_to_canonical_fupd
                        (K (insert r r (knowledge_to_canonical data))) data))))
             (knowledge_to_canonical_fupd
                (K (insert r r (knowledge_to_canonical data))) data)))))
        (knowledge_instrs_mem_fupd
           (K (balanced_map_insert listCmp (instToNumList (asm_Const r (w:A word))) r
                 (knowledge_instrs_mem
                   (knowledge_to_canonical_fupd
                      (K (insert r r (knowledge_to_canonical data))) data))))
           (knowledge_to_canonical_fupd
              (K (insert r r (knowledge_to_canonical data))) data))` THEN
    MATCH_MP_TAC wf_data_insert_to_latest THEN
    REPEAT CONJ_TAC THENL [ALL_TAC; SIMP[domain_insert; IN_INSERT];
                           SIMP[domain_insert; IN_INSERT]] THEN
    MATCH_MP_TAC wf_data_insert_instrs_Const THEN
    CONJ_TAC THENL [ALL_TAC; SIMP[lookup_insert]] THEN
    MATCH_MP_TAC wf_data_insert_to_canonical THEN
    ASM_REWRITE_TAC[lookup_insert; GSYM NOT_EVEN];
    (* hit *)
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_wf_facts_wf o
                CONJ (ASSUME `wf_data (:A) data`)) THEN
    SUBGOAL_THEN `~(a:num = r)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
    SUBGOAL_THEN `a IN domain (knowledge_to_canonical data)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
    MATCH_MP_TAC wf_data_insert_to_latest THEN
    SIMP[domain_insert; IN_INSERT] THEN
    MATCH_MP_TAC wf_data_insert_to_canonical THEN
    ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN]]);;

let wf_add_to_load_aux = prove
 (`!data r i (p:(A)wl_prog) data' p'.
     wf_data (:A) data /\
     lookup r (knowledge_to_canonical data) = NONE /\
     add_to_load_aux data r i p = (data', p') /\
     (~EVEN r ==>
        wf_data (:A)
          (knowledge_loads_mem_fupd
             (K (balanced_map_insert listCmp i r
                   (knowledge_loads_mem
                      (knowledge_to_canonical_fupd
                         (K (insert r r (knowledge_to_canonical data))) data))))
             (knowledge_to_canonical_fupd
                (K (insert r r (knowledge_to_canonical data))) data))) ==>
     wf_data (:A) data'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `add_to_load_aux data r i (p:(A)wl_prog) = (data',p')` THEN
  REWRITE_TAC[add_to_load_aux_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `balanced_map_lookup listCmp i (knowledge_loads_mem data)` THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[] THEN
  (TRY(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_add_to_latest_eq2] THEN
      MATCH_MP_TAC wf_data_insert_to_latest THEN ASM_REWRITE_TAC[] THEN
      SIMP[domain_insert; IN_INSERT] THEN NO_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_wf_facts2_wf o
              CONJ (ASSUME `wf_data (:A) data`)) THEN
  SUBGOAL_THEN `~(a:num = r)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `a IN domain (knowledge_to_canonical data)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
  MATCH_MP_TAC wf_data_insert_to_latest THEN
  SIMP[domain_insert; IN_INSERT] THEN
  MATCH_MP_TAC wf_data_insert_to_canonical THEN
  ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN]));;

let wf_data_insert_gets = prove
 (`!data name v.
     wf_data (:A) data /\
     lookup v (knowledge_to_canonical data) = NONE /\ ODD v /\
     ALOOKUP (knowledge_gets_mem data) name = NONE ==>
     wf_data (:A)
       (knowledge_to_canonical_fupd (K (insert v v (knowledge_to_canonical data)))
          (knowledge_to_latest_fupd (K (insert v v (knowledge_to_latest data)))
             (knowledge_gets_mem_fupd (K (CONS (name,v) (knowledge_gets_mem data)))
                data)))`,
  WPROOF1AUX_CSE_INV_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  ASM_REWRITE_TAC[GSYM ALOOKUP_NONE] THEN WPROOF1AUX_CSE_CLAUSE_TAC);;

let wf_data_filter_gets = prove
 (`!data x.
     wf_data (:A) data ==>
     wf_data (:A) (knowledge_gets_mem_fupd
                     (K (FILTER (\(m,n). ~(m = x)) (knowledge_gets_mem data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN ASM_SIMP_TAC[ALL_DISTINCT_MAP_FST_FILTER] THEN
  WPROOF1AUX_CSE_CLAUSE_TAC);;

let wf_data_cons_gets = prove
 (`!data x h.
     wf_data (:A) data /\
     ALOOKUP (knowledge_gets_mem data) x = NONE /\
     lookup h (knowledge_to_canonical data) = SOME h ==>
     wf_data (:A) (knowledge_gets_mem_fupd (K (CONS (x,h) (knowledge_gets_mem data))) data)`,
  WPROOF1AUX_CSE_INV_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  ASM_REWRITE_TAC[GSYM ALOOKUP_NONE] THEN WPROOF1AUX_CSE_CLAUSE_TAC);;

let wf_data_reinsert_canonical = prove
 (`!data v.
     wf_data (:A) data /\ ODD v ==>
     wf_data (:A) (knowledge_to_canonical_fupd
                     (K (insert v (lookup_any v (knowledge_to_canonical data) v)
                           (knowledge_to_canonical data))) data)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_any_def] THEN
  CASES_ON `lookup v (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THENL
   [MATCH_MP_TAC wf_data_insert_to_canonical THEN ASM_REWRITE_TAC[lookup_insert];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP insert_unchanged th]) THEN
    SUBGOAL_THEN `knowledge_to_canonical_fupd (K (knowledge_to_canonical data)) data = data`
      SUBST1_TAC THENL
     [REWRITE_TAC[knowledge_component_equality] THEN SIMP[]; ASM_REWRITE_TAC[]]]);;

let wf_data_merge = prove
 (`!d1 d2. wf_data (:A) d1 /\ wf_data (:A) d2 ==> wf_data (:A) (merge_data d1 d2)`,
  WPROOF1AUX_CSE_MERGE_TAC);;

let wf_data_move_pairs = prove
 (`!ps data.
     wf_data (:A) data /\
     ALL (\(x,y). lookup x (knowledge_to_canonical data) = NONE /\
                  lookup y (knowledge_to_canonical data) = SOME y /\
                  ODD x /\ ODD y) ps ==>
     wf_data (:A)
       (knowledge_to_canonical_fupd (K (map_insert ps (knowledge_to_canonical data)))
          (knowledge_to_latest_fupd
             (K (map_insert (MAP (\(a,b). (b,a)) ps) (knowledge_to_latest data))) data))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN SIMP_NOASM[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x y. ALOOKUP (ps:(num#num)list) x = SOME y ==>
       lookup x (knowledge_to_canonical data) = NONE /\
       lookup y (knowledge_to_canonical data) = SOME y /\ ODD x /\ ODD y` ASSUME_TAC THENL
  [ASM_MESON_TAC[ALOOKUP_MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. lookup v (knowledge_to_canonical data) = SOME v ==>
                    ALOOKUP (ps:(num#num)list) v = NONE` ASSUME_TAC THENL
  [REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; EXISTS_PAIR_THM; FST] THEN
   ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. ALOOKUP (MAP (\(a,b). (b,a)) (ps:(num#num)list)) x = SOME y ==>
       lookup x (knowledge_to_canonical data) = SOME x /\ ?z. ALOOKUP ps y = SOME z`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
   REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN SIMP_NOASM[PAIR_EQ] THEN STRIP_TAC THEN
   RVEQ_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(MESON[cases "option"] `~(x:num option = NONE) ==> ?z. x = SOME z`) THEN
   REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; EXISTS_PAIR_THM; FST] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k v. lookup k (map_insert ps (knowledge_to_canonical data)) = SOME v <=>
       ALOOKUP (ps:(num#num)list) k = SOME v \/
       (ALOOKUP ps k = NONE /\ lookup k (knowledge_to_canonical data) = SOME v)` ASSUME_TAC THENL
  [REWRITE_TAC[lookup_map_insert0] THEN REPEAT GEN_TAC THEN
   CASES_ON `ALOOKUP (ps:(num#num)list) k` THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[option_DISTINCT; option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `!k v. lookup k (map_insert (MAP (\(a,b). (b,a)) ps) (knowledge_to_latest data)) = SOME v <=>
       ALOOKUP (MAP (\(a,b). (b,a)) (ps:(num#num)list)) k = SOME v \/
       (ALOOKUP (MAP (\(a,b). (b,a)) ps) k = NONE /\ lookup k (knowledge_to_latest data) = SOME v)` ASSUME_TAC THENL
  [REWRITE_TAC[lookup_map_insert0] THEN REPEAT GEN_TAC THEN
   CASES_ON `ALOOKUP (MAP (\(a,b). (b,a)) (ps:(num#num)list)) k` THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[option_DISTINCT; option_INJ]; ALL_TAC]) THEN
  (FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wf_data_def; in_names_set_def; GSYM ALL_MEM; domain_lookup] o check (fun th -> can (term_match [] `wf_data (:A) d`) (concl th))) THEN
  REWRITE_TAC[wf_data_def; in_names_set_def; GSYM ALL_MEM; domain_lookup; knowledge_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THEN
  ASM_MESON_TAC[cases "option"]);;

let wf_canonicalMoveRegs = prove
 (`!data rs. wf_data (:A) data ==> wf_data (:A) (canonicalMoveRegs data rs)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[canonicalMoveRegs_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[wf_data_empty]] THEN
  SUBGOAL_THEN `wf_data (:A) (register_reads data (MAP SND (rs:(num#num)list)))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC wf_data_register_reads THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. MEM a (MAP FST (rs:(num#num)list)) ==>
       lookup a (knowledge_to_canonical (register_reads data (MAP SND rs))) = NONE`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM ALL_MEM; keep_data_def; IS_NONE_EQ_NONE] o
     check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL"
                      with Failure _ -> false)) THEN
   REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC wf_data_move_pairs THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM] THEN
  SIMP_NOASM[PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `c:num`] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `MEM (b:num) (MAP SND (rs:(num#num)list))` ASSUME_TAC THENL
  [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(a:num,b:num)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (a:num) (MAP FST (rs:(num#num)list))` ASSUME_TAC THENL
  [ASM_MESON_TAC[MEM_FST_reduc]; ALL_TAC] THEN
  SUBGOAL_THEN `!r v. lookup r (knowledge_to_canonical data) = SOME v ==>
                      lookup v (knowledge_to_canonical data) = SOME v` ASSUME_TAC THENL
  [UNDISCH_TAC `wf_data (:A) data` THEN REWRITE_TAC[wf_data_def] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `lookup (canonicalRegs (register_reads data (MAP SND rs)) b)
       (knowledge_to_canonical (register_reads data (MAP SND (rs:(num#num)list)))) =
       SOME (canonicalRegs (register_reads data (MAP SND rs)) b)` ASSUME_TAC THENL
  [REWRITE_TAC[canonicalRegs_def; lookup_any_def; lookup_register_reads] THEN
   ASM_REWRITE_TAC[] THEN
   CASES_ON `lookup b (knowledge_to_canonical data)` THEN
   ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
   RES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM NOT_EVEN] THEN
  MP_TAC(ASSUME `wf_data (:A) (register_reads data (MAP SND (rs:(num#num)list)))`) THEN
  REWRITE_TAC[wf_data_def] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`canonicalRegs (register_reads data (MAP SND (rs:(num#num)list))) b`;
     `canonicalRegs (register_reads data (MAP SND (rs:(num#num)list))) b`] o
             CONJUNCT1) THEN
  ASM_REWRITE_TAC[NOT_EVEN] THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_tc_facts_wf = prove
 (`!data x y.
     wf_data (:A) data /\ lookup x (knowledge_to_canonical data) = SOME y ==>
     lookup y (knowledge_to_canonical data) = SOME y /\ ODD x /\ ODD y`,
  REWRITE_TAC[wf_data_def] THEN MESON_TAC[]);;

let canonicalRegs_self_or_fresh_wf = prove
 (`!data x.
     wf_data (:A) data ==>
     lookup (canonicalRegs data x) (knowledge_to_canonical data) =
       SOME (canonicalRegs data x) \/
     lookup (canonicalRegs data x) (knowledge_to_canonical data) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[canonicalRegs_def; lookup_any_def] THEN DISCH_TAC THEN
  CASES_ON `lookup x (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF1AUX_CSE_tc_facts_wf o
              CONJ (ASSUME `wf_data (:A) data`)) THEN
  SIMP_TAC[]);;

let canonicalRegs'_self_or_fresh_wf = prove
 (`!data r1 x.
     wf_data (:A) data /\ lookup r1 (knowledge_to_canonical data) = NONE ==>
     lookup (canonicalRegs' r1 data x) (knowledge_to_canonical data) =
       SOME (canonicalRegs' r1 data x) \/
     lookup (canonicalRegs' r1 data x) (knowledge_to_canonical data) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[canonicalRegs'_def; canonicalRegs_def; lookup_any_def;
                                  LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  CASES_ON `lookup x (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF1AUX_CSE_tc_facts_wf o
              CONJ (ASSUME `wf_data (:A) data`)) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `lookup r1 (knowledge_to_canonical data) = NONE` THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let in_names_set_insert_self = prove
 (`!a:(A)asm_arith tc x. in_names_set a tc ==> in_names_set a (insert x x tc)`,
  REWRITE_TAC[in_names_set_def; GSYM ALL_MEM; lookup_insert] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let in_names_set_register_reads = prove
 (`!a:(A)asm_arith data.
     ALL ODD (arithReads a) /\
     ALL (\w. lookup w (knowledge_to_canonical data) = NONE \/
              lookup w (knowledge_to_canonical data) = SOME w) (arithReads a) ==>
     in_names_set a (knowledge_to_canonical (register_reads data (arithReads a)))`,
  REWRITE_TAC[in_names_set_def; GSYM ALL_MEM; lookup_register_reads; GSYM NOT_EVEN] THEN
  MESON_TAC[]);;

let canonicalArith_reads_self_or_fresh = prove
 (`!data (a:(A)asm_arith).
     wf_data (:A) data /\
     can_mem_arith (canonicalArith data a) /\
     lookup (firstRegOfArith a) (knowledge_to_canonical data) = NONE ==>
     ALL (\w. lookup w (knowledge_to_canonical data) = NONE \/
              lookup w (knowledge_to_canonical data) = SOME w)
         (arithReads (canonicalArith data a))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  REWRITE_TAC[canonicalArith_def; firstRegOfArith_def] THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[canonicalImmReg'_def; can_mem_arith_def; arithReads_def; ALL] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[canonicalRegs_self_or_fresh_wf; canonicalRegs'_self_or_fresh_wf]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers for word_cse_wf_data: the knowledge updates of the cases   *)
(* ------------------------------------------------------------------------- *)

let WPROOF1AUX_CSE_lookup_invalidate_self = prove
 (`!data n. lookup n (knowledge_to_canonical (invalidate_data data n)) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[invalidate_data_def; keep_data_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[lookup_empty_data] THEN POP_ASSUM MP_TAC THEN
  CASES_ON `lookup n (knowledge_to_canonical data)` THEN REWRITE_TAC[IS_NONE_DEF]);;

let WPROOF1AUX_CSE_canon_src_wf = prove
 (`!data r1 r2.
     wf_data (:A) data /\ lookup r1 (knowledge_to_canonical data) = NONE /\
     ~EVEN r2 /\ ~(r2 = r1) ==>
     ODD (canonicalRegs' r1 data r2) /\ ~(canonicalRegs' r1 data r2 = r1) /\
     lookup (canonicalRegs' r1 data r2)
       (knowledge_to_canonical (register_read data (canonicalRegs' r1 data r2))) =
       SOME (canonicalRegs' r1 data r2) /\
     lookup r1 (knowledge_to_canonical (register_read data (canonicalRegs' r1 data r2))) =
       NONE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[canonicalRegs'_def; canonicalRegs_def; lookup_any_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `lookup r2 (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[lookup_register_read; GSYM NOT_EVEN] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_tc_facts_wf o
                CONJ (ASSUME `wf_data (:A) data`)) THEN
    SUBGOAL_THEN `~(a:num = r1)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_register_read] THEN ASM_MESON_TAC[]]);;

let WPROOF1AUX_CSE_wf_OpCurrHeap = prove
 (`!data b r1 r2 (p:(A)wl_prog) data' p'.
     wf_data (:A) data /\ lookup r1 (knowledge_to_canonical data) = NONE /\
     ~EVEN r2 /\ ~(r2 = r1) /\
     add_to_data_aux (register_read data (canonicalRegs' r1 data r2)) r1
       (OpCurrHeapToNumList b (canonicalRegs' r1 data r2)) p = (data', p') ==>
     wf_data (:A) data'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`data:knowledge`; `r1:num`; `r2:num`]
               (INST_TYPE [`:A`,`:A`] WPROOF1AUX_CSE_canon_src_wf)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC wf_add_to_data_aux THEN
  MAP_EVERY EXISTS_TAC [`register_read data (canonicalRegs' r1 data r2)`; `r1:num`;
                        `OpCurrHeapToNumList b (canonicalRegs' r1 data r2)`;
                        `p:(A)wl_prog`; `p':(A)wl_prog`] THEN
  ASM_SIMP_TAC[wf_data_register_read] THEN DISCH_TAC THEN
  MATCH_MP_TAC wf_data_insert_instrs_OpCurrHeap THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; SIMP[lookup_insert]; SIMP[lookup_insert]] THEN
  MATCH_MP_TAC wf_data_insert_to_canonical THEN
  ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN; wf_data_register_read]);;

let WPROOF1AUX_CSE_wf_LocValue = prove
 (`!data r l (p:(A)wl_prog) data' p'.
     wf_data (:A) data /\ lookup r (knowledge_to_canonical data) = NONE /\
     add_to_data_aux data r [48; l] p = (data', p') ==>
     wf_data (:A) data'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC wf_add_to_data_aux THEN
  MAP_EVERY EXISTS_TAC [`data:knowledge`; `r:num`; `[48; l]`;
                        `p:(A)wl_prog`; `p':(A)wl_prog`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC wf_data_insert_instrs_LocValue THEN
  CONJ_TAC THENL [ALL_TAC; SIMP[lookup_insert]] THEN
  MATCH_MP_TAC wf_data_insert_to_canonical THEN
  ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN]);;

let WPROOF1AUX_CSE_wf_load = prove
 (`!data op r a (ofs:A word) (p:(A)wl_prog) data' p'.
     wf_data (:A) data /\ lookup r (knowledge_to_canonical data) = NONE /\
     ~EVEN r /\ ~EVEN a /\ ~(a = r) /\
     add_to_load_aux (register_read data (canonicalRegs' r data a)) r
       (loadToNumList op (canonicalRegs' r data a) ofs) p = (data', p') ==>
     wf_data (:A) data'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`data:knowledge`; `r:num`; `a:num`]
               (INST_TYPE [`:A`,`:A`] WPROOF1AUX_CSE_canon_src_wf)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC wf_add_to_load_aux THEN
  MAP_EVERY EXISTS_TAC [`register_read data (canonicalRegs' r data a)`; `r:num`;
                        `loadToNumList op (canonicalRegs' r data a) (ofs:A word)`;
                        `p:(A)wl_prog`; `p':(A)wl_prog`] THEN
  ASM_SIMP_TAC[wf_data_register_read] THEN TRY DISCH_TAC THEN
  MATCH_MP_TAC wf_data_insert_loads THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; SIMP[lookup_insert]; SIMP[lookup_insert]] THEN
  MATCH_MP_TAC wf_data_insert_to_canonical THEN
  ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN; wf_data_register_read]);;

let WPROOF1AUX_CSE_wf_Arith = prove
 (`!data (a:(A)asm_arith) data' p'.
     wf_data (:A) data /\
     lookup (firstRegOfArith a) (knowledge_to_canonical data) = NONE /\
     can_mem_arith (canonicalArith data a) /\
     ~MEM (firstRegOfArith a) (arithReads (canonicalArith data a)) /\
     add_to_data (register_reads data (arithReads (canonicalArith data a)))
       (firstRegOfArith a) (asm_Arith (canonicalArith data a)) (asm_Arith a) =
       (data', p') ==>
     wf_data (:A) data'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `in_names_set (canonicalArith data (a:(A)asm_arith))
     (knowledge_to_canonical (register_reads data (arithReads (canonicalArith data a))))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC in_names_set_register_reads THEN
    ASM_SIMP_TAC[can_mem_arith_ODD_reads; canonicalArith_reads_self_or_fresh]; ALL_TAC] THEN
  SUBGOAL_THEN `lookup (firstRegOfArith (a:(A)asm_arith))
     (knowledge_to_canonical (register_reads data (arithReads (canonicalArith data a)))) =
     NONE` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lookup_register_reads]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term (fun t -> is_const t && fst(dest_const t) = "add_to_data")) (concl th))) THEN
  REWRITE_TAC[add_to_data_def; LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC wf_add_to_data_aux THEN
  MAP_EVERY EXISTS_TAC
   [`register_reads data (arithReads (canonicalArith data (a:(A)asm_arith)))`;
    `firstRegOfArith (a:(A)asm_arith)`;
    `instToNumList (asm_Arith (canonicalArith data (a:(A)asm_arith)))`;
    `wl_Inst (asm_Arith (a:(A)asm_arith))`; `p':(A)wl_prog`] THEN
  ASM_SIMP_TAC[wf_data_register_reads] THEN DISCH_TAC THEN
  MATCH_MP_TAC wf_data_insert_instrs_Arith THEN
  ASM_REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM; lookup_insert] THEN
  ASM_SIMP_TAC[in_names_set_insert_self] THEN
  MATCH_MP_TAC wf_data_insert_to_canonical THEN
  ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN; wf_data_register_reads]);;

let WPROOF1AUX_CSE_firstReg_writes = prove
 (`!a:(A)asm_arith. MEM (firstRegOfArith a) (arithWrites a)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  REWRITE_TAC[firstRegOfArith_def; arithWrites_def; MEM]);;

let WPROOF1AUX_CSE_FST_INTRO = prove
 (`!(P:A->bool) (x:A#B). (!a b. x = (a,b) ==> P a) ==> P (FST x)`,
  MESON_TAC[PAIR]);;

let WPROOF1AUX_CSE_wf_cseInst = prove
 (`!data (i:(A)inst). wf_data (:A) data ==> wf_data (:A) (FST (word_cseInst data i))`,
  GEN_TAC THEN MATCH_MP_TAC inst_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Skip *)
    REWRITE_TAC[word_cseInst_def; FST];
    (* Const *)
    MAP_EVERY X_GEN_TAC [`r:num`; `w:A word`] THEN DISCH_TAC THEN
    REWRITE_TAC[word_cseInst_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[FST; wf_data_invalidate] THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_FST_INTRO THEN
    MAP_EVERY X_GEN_TAC [`d':knowledge`; `q':(A)wl_prog`] THEN DISCH_TAC THEN
    MATCH_MP_TAC wf_add_to_data_const THEN
    MAP_EVERY EXISTS_TAC [`invalidate_data data r`; `r:num`; `w:A word`; `q':(A)wl_prog`] THEN
    ASM_SIMP_TAC[wf_data_invalidate; WPROOF1AUX_CSE_lookup_invalidate_self];
    (* Arith *)
    X_GEN_TAC `a:(A)asm_arith` THEN DISCH_TAC THEN
    REWRITE_TAC[word_cseInst_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[FST; wf_data_invalidate_regs] THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_FST_INTRO THEN
    MAP_EVERY X_GEN_TAC [`d':knowledge`; `q':(A)wl_prog`] THEN DISCH_TAC THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_wf_Arith THEN
    MAP_EVERY EXISTS_TAC [`invalidate_regs data (arithWrites (a:(A)asm_arith))`;
                          `a:(A)asm_arith`; `q':(A)wl_prog`] THEN
    ASM_SIMP_TAC[wf_data_invalidate_regs; lookup_invalidate_regs;
                 WPROOF1AUX_CSE_firstReg_writes];
    (* Mem *)
    MAP_EVERY X_GEN_TAC [`op:memop`; `r:num`; `ad:(A)addr`] THEN
    STRUCT_CASES_TAC (ISPEC `ad:(A)addr` (cases "addr")) THEN DISCH_TAC THEN
    REWRITE_TAC[word_cseInst_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[FST; wf_data_loads_wipe] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[FST; wf_data_invalidate] THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_FST_INTRO THEN
    MAP_EVERY X_GEN_TAC [`d':knowledge`; `q':(A)wl_prog`] THEN DISCH_TAC THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_wf_load THEN
    MAP_EVERY EXISTS_TAC [`invalidate_data data r`; `op:memop`; `r:num`; `a0:num`;
                          `a1:A word`; `wl_Inst (Mem op r (Addr a0 a1)):(A)wl_prog`;
                          `q':(A)wl_prog`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[wf_data_invalidate; WPROOF1AUX_CSE_lookup_invalidate_self];
    (* FP *)
    X_GEN_TAC `fp:fp` THEN DISCH_TAC THEN
    REWRITE_TAC[word_cseInst_def; FST] THEN ASM_SIMP_TAC[wf_data_invalidate_regs]]);;

let WPROOF1AUX_CSE_wf_gets_facts = prove
 (`!data x k.
     wf_data (:A) data /\ ALOOKUP (knowledge_gets_mem data) x = SOME k ==>
     lookup k (knowledge_to_canonical data) = SOME k /\ ODD k`,
  REWRITE_TAC[wf_data_def] THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_wf_Get = prove
 (`!data r x.
     wf_data (:A) data ==> wf_data (:A) (FST (word_cse data (wl_Get r x:(A)wl_prog)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cse_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `wf_data (:A) (invalidate_data data r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[wf_data_invalidate]; ALL_TAC] THEN
  MP_TAC(SPECL [`data:knowledge`; `r:num`] WPROOF1AUX_CSE_lookup_invalidate_self) THEN
  DISCH_TAC THEN
  CASES_ON `ALOOKUP (knowledge_gets_mem (invalidate_data data r)) x` THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FST] THENL
   [REWRITE_TAC[knowledge_INFO.ri_fupdcanon] THEN
    MATCH_MP_TAC wf_data_insert_gets THEN ASM_REWRITE_TAC[GSYM NOT_EVEN];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_wf_gets_facts o
                CONJ (ASSUME `wf_data (:A) (invalidate_data data r)`)) THEN
    SUBGOAL_THEN `~(a:num = r)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
    MATCH_MP_TAC wf_data_insert_to_latest THEN
    SIMP[domain_insert; IN_INSERT; domain_lookup; lookup_insert] THEN
    MATCH_MP_TAC wf_data_insert_to_canonical THEN
    ASM_SIMP_TAC[lookup_insert; GSYM NOT_EVEN]]);;

let WPROOF1AUX_CSE_canon_reinsert_wf = prove
 (`!data v.
     wf_data (:A) data ==>
     lookup (canonicalRegs data v)
       (insert v (lookup_any v (knowledge_to_canonical data) v)
          (knowledge_to_canonical data)) = SOME (canonicalRegs data v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[canonicalRegs_def; lookup_any_def] THEN
  CASES_ON `lookup v (knowledge_to_canonical data)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF1AUX_CSE_tc_facts_wf o
              CONJ (ASSUME `wf_data (:A) data`)));;

let WPROOF1AUX_CSE_wf_Set = prove
 (`!data x e.
     wf_data (:A) data ==> wf_data (:A) (FST (word_cse data (wl_Set x e:(A)wl_prog)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cse_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[FST; wf_data_empty] THEN
  CASES_ON `dest_Var (e:(A)wl_exp)` THEN CASE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN ASM_SIMP_TAC[FST; wf_data_filter_gets] THEN
  WPROOF1AUX_CSE_REC_WF_TAC
   `knowledge_gets_mem_fupd
      (K (CONS (x,canonicalRegs data a)
           (knowledge_gets_mem
             (knowledge_gets_mem_fupd
               (K (FILTER (\(m,n). ~(m = x))
                    (knowledge_gets_mem
                      (knowledge_to_canonical_fupd
                        (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                              (knowledge_to_canonical data))) data))))
               (knowledge_to_canonical_fupd
                 (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                       (knowledge_to_canonical data))) data)))))
      (knowledge_gets_mem_fupd
         (K (FILTER (\(m,n). ~(m = x))
              (knowledge_gets_mem
                (knowledge_to_canonical_fupd
                  (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                        (knowledge_to_canonical data))) data))))
         (knowledge_to_canonical_fupd
           (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                 (knowledge_to_canonical data))) data))` THEN
  MATCH_MP_TAC wf_data_cons_gets THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC wf_data_filter_gets THEN MATCH_MP_TAC wf_data_reinsert_canonical THEN
    ASM_REWRITE_TAC[GSYM NOT_EVEN];
    REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM; WPROOF1AUX_CSE_ALOOKUP_FILTER_NEQ];
    REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM] THEN
    ASM_SIMP_TAC[WPROOF1AUX_CSE_canon_reinsert_wf]]);;

let WPROOF1AUX_CSE_FST_word_cse = prove
 (`(!data (i:(A)inst). FST (word_cse data (wl_Inst i)) = FST (word_cseInst data i)) /\
   (!data (p:(A)wl_prog).
      FST (word_cse data (MustTerminate p)) = FST (word_cse data p)) /\
   (!data (p1:(A)wl_prog) p2.
      FST (word_cse data (wl_Seq p1 p2)) = FST (word_cse (FST (word_cse data p1)) p2)) /\
   (!data c r1 r2 (p1:(A)wl_prog) p2.
      FST (word_cse data (wl_If c r1 r2 p1 p2)) =
      merge_data (FST (word_cse data p1)) (FST (word_cse data p2))) /\
   (!data names (c:(A)wl_prog) exit_names.
      FST (word_cse data (wl_Loop names c exit_names)) = empty_data)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[word_cse_def] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST]);;

let WPROOF1AUX_CSE_WF_TRIV_TAC : tactic =
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cse_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[FST; wf_data_empty; wf_data_invalidate; wf_data_invalidate_regs;
               wf_data_loads_wipe; wf_canonicalMoveRegs];;

let word_cse_wf_data = prove
 (`!p data. wf_data (:A) data ==> wf_data (:A) (FST (word_cse data (p:(A)wl_prog)))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC word_cse_ind THEN
  (* the MustTerminate and Loop cases are closed by the rewriting *)
  REWRITE_TAC[WPROOF1AUX_CSE_FST_word_cse; wf_data_empty] THEN REPEAT CONJ_TAC THENL
   [(* Move *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Inst *) REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WPROOF1AUX_CSE_wf_cseInst];
    (* Get *) REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WPROOF1AUX_CSE_wf_Get];
    (* Set *) REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WPROOF1AUX_CSE_wf_Set];
    (* Call *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Seq *)
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`SND (word_cse data (p1:(A)wl_prog))`;
                                  `FST (word_cse data (p1:(A)wl_prog))`]) THEN
    REWRITE_TAC[PAIR] THEN ASM_MESON_TAC[];
    (* If *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC wf_data_merge THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`FST (word_cse data (p1:(A)wl_prog))`;
                                    `SND (word_cse data (p1:(A)wl_prog))`]) THEN
      REWRITE_TAC[PAIR] THEN ASM_MESON_TAC[]];
    (* OpCurrHeap *)
    MAP_EVERY X_GEN_TAC [`data:knowledge`; `b:binop`; `r1:num`; `r2:num`] THEN
    DISCH_TAC THEN REWRITE_TAC[word_cse_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[FST; wf_data_invalidate] THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_FST_INTRO THEN
    MAP_EVERY X_GEN_TAC [`d':knowledge`; `q':(A)wl_prog`] THEN DISCH_TAC THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_wf_OpCurrHeap THEN
    MAP_EVERY EXISTS_TAC [`invalidate_data data r1`; `b:binop`; `r1:num`; `r2:num`;
                          `wl_OpCurrHeap b r1 r2:(A)wl_prog`; `q':(A)wl_prog`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[wf_data_invalidate; WPROOF1AUX_CSE_lookup_invalidate_self];
    (* LocValue *)
    MAP_EVERY X_GEN_TAC [`data:knowledge`; `r:num`; `l:num`] THEN
    DISCH_TAC THEN REWRITE_TAC[word_cse_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_FST_INTRO THEN
    MAP_EVERY X_GEN_TAC [`d':knowledge`; `q':(A)wl_prog`] THEN DISCH_TAC THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_wf_LocValue THEN
    MAP_EVERY EXISTS_TAC [`invalidate_data data r`; `r:num`; `l:num`;
                          `wl_LocValue r l:(A)wl_prog`; `q':(A)wl_prog`] THEN
    ASM_SIMP_TAC[wf_data_invalidate; WPROOF1AUX_CSE_lookup_invalidate_self];
    (* Skip *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Store *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Assign *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Raise *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Return *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Tick *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Alloc *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Install *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* CodeBufferWrite *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* DataBufferWrite *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* FFI *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* StoreConsts *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* ShareInst *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Break *) WPROOF1AUX_CSE_WF_TRIV_TAC;
    (* Continue *) WPROOF1AUX_CSE_WF_TRIV_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The cases of comp_correct (word_cseProof_comp_correct)                   *)
(* ------------------------------------------------------------------------- *)

let WPROOF1AUX_CSE_is_cse_eq th =
  let c = concl th in
  is_eq c && (let h,_ = strip_comb (lhs c) in
              is_const h && fst(dest_const h) = "word_cse");;

(* substitute the knowledge and program computed by word_cse *)

let WPROOF1AUX_CSE_CC_START_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[word_cse_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV);;

let WPROOF1AUX_CSE_CC_SUBST_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[data_inv_empty];;

(* the result of an evaluation that is not NONE *)

let WPROOF1AUX_CSE_CC_NOT_NONE_TAC (c:string) : tactic =
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause c] THEN
  REPEAT (CASE_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT]) THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let WPROOF1AUX_CSE_CC_SIMPLE_TAC : tactic =
  WPROOF1AUX_CSE_CC_START_TAC THEN WPROOF1AUX_CSE_CC_SUBST_TAC;;

(* split the evaluation of the assumptions into its outcomes; the NONE      *)
(* outcomes leave res and s' substituted                                    *)

let WPROOF1AUX_CSE_CC_EVAL_CASES_TAC (c:string) : tactic =
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause c; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT (CASE_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT; GSYM option_DISTINCT]) THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT; GSYM option_DISTINCT] THEN
  TRY(DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[option_DISTINCT; GSYM option_DISTINCT]);;

let WPROOF1AUX_CSE_data_inv_invalidate = prove
 (`!data (s:(A,C,FFI)wl_state) r.
     data_inv data s ==> data_inv (invalidate_data data r) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[invalidate_data_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[data_inv_empty]);;

let WPROOF1AUX_CSE_CC_MOVE_TAC : tactic =
  WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN WPROOF1AUX_CSE_CC_EVAL_CASES_TAC "wl_Move" THEN
  MATCH_MP_TAC canonicalMoveRegs_lemma THEN ASM_REWRITE_TAC[];;

(* the outcome NONE leaves a state that agrees with s on the invariant *)

let WPROOF1AUX_CSE_CC_AGREE_TAC (c:string) : tactic =
  WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN WPROOF1AUX_CSE_CC_EVAL_CASES_TAC c THEN
  MATCH_MP_TAC data_inv_state_agree THEN EXISTS_TAC `s:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[] THEN SIMP[wl_dec_clock_def];;

let WPROOF1AUX_CSE_CC_STORECONSTS_TAC : tactic =
  WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN WPROOF1AUX_CSE_CC_EVAL_CASES_TAC "wl_StoreConsts" THEN
  ASM_SIMP_TAC[data_inv_set_var; data_inv_unset_var; lookup_invalidate_regs; MEM;
               knowledge_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC data_inv_memory THEN MATCH_MP_TAC data_inv_invalidate_regs THEN
  ASM_REWRITE_TAC[];;

let WPROOF1AUX_CSE_CC_LOCVALUE_TAC : tactic =
  WPROOF1AUX_CSE_CC_START_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_LocValue"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC add_to_data_LocValue_correct THEN
  EXISTS_TAC `invalidate_data data r` THEN
  ASM_SIMP_TAC[WPROOF1AUX_CSE_data_inv_invalidate; WPROOF1AUX_CSE_lookup_invalidate_self];;

let WPROOF1AUX_CSE_CC_OPCURRHEAP_TAC : tactic =
  WPROOF1AUX_CSE_CC_START_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_OpCurrHeap"] THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op b [wl_Var src; Lookup CurrHeap])` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_OpCurrHeap"] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[data_inv_set_var; WPROOF1AUX_CSE_lookup_invalidate_self;
                 WPROOF1AUX_CSE_data_inv_invalidate];
    DISCH_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC add_to_data_OpCurrHeap_correct THEN
    MAP_EVERY EXISTS_TAC [`invalidate_data data dst`; `b:binop`; `src:num`;
                          `canonicalRegs' dst (invalidate_data data dst) src`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[WPROOF1AUX_CSE_data_inv_invalidate; WPROOF1AUX_CSE_lookup_invalidate_self]];;

(* split an option term tm into NONE and SOME v everywhere *)

let WPROOF1AUX_CSE_OCASES_TAC (tm:term) (v:term) : tactic =
  DISJ_CASES_THEN2
    (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)
    (X_CHOOSE_THEN v (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th))
    (ISPEC tm (cases "option"));;

let WPROOF1AUX_CSE_gets_facts = prove
 (`!data (s:(A,C,FFI)wl_state) x k.
     data_inv data s /\ ALOOKUP (knowledge_gets_mem data) x = SOME k ==>
     lookup k (knowledge_to_canonical data) = SOME k /\ ODD k`,
  REWRITE_TAC[data_inv_def; wf_data_def] THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_gets_var = prove
 (`!data (s:(A,C,FFI)wl_state) x k w.
     data_inv data s /\ ALOOKUP (knowledge_gets_mem data) x = SOME k /\
     wl_get_store x s = SOME w ==>
     wl_get_var k s = SOME w`,
  REWRITE_TAC[data_inv_def; sem_inv_def; wl_get_store_def] THEN
  MESON_TAC[option_INJ]);;

let WPROOF1AUX_CSE_CC_GET_TAC : tactic =
  WPROOF1AUX_CSE_CC_START_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Get"] THEN
  WPROOF1AUX_CSE_OCASES_TAC `wl_get_store name (s:(A,C,FFI)wl_state)` `w:(A)word_loc` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `data_inv (invalidate_data data v) (s:(A,C,FFI)wl_state)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WPROOF1AUX_CSE_data_inv_invalidate]; ALL_TAC] THEN
  MP_TAC(SPECL [`data:knowledge`; `v:num`] WPROOF1AUX_CSE_lookup_invalidate_self) THEN
  DISCH_TAC THEN
  WPROOF1AUX_CSE_OCASES_TAC `ALOOKUP (knowledge_gets_mem (invalidate_data data v)) name`
    `k:num` THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[] THENL
   [(* NONE, EVEN *)
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Get"] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[data_inv_set_var];
    (* NONE, ODD *)
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Get"] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[knowledge_INFO.ri_fupdcanon] THEN
    MATCH_MP_TAC data_inv_insert_gets THEN EXISTS_TAC `w:(A)word_loc` THEN
    ASM_SIMP_TAC[data_inv_set_var; GSYM NOT_EVEN; wl_get_var_set_var] THEN
    UNDISCH_TAC `wl_get_store name (s:(A,C,FFI)wl_state) = SOME w` THEN
    REWRITE_TAC[wl_get_store_def; wl_set_var_def] THEN SIMP[];
    (* SOME k, EVEN *)
    SUBGOAL_THEN `wl_get_var k (s:(A,C,FFI)wl_state) = SOME w` ASSUME_TAC THENL
     [MATCH_MP_TAC WPROOF1AUX_CSE_gets_var THEN
      MAP_EVERY EXISTS_TAC [`invalidate_data data v`; `name:store_name`] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[data_inv_set_var] THEN MATCH_MP_TAC evaluate_Move1 THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_get_var_latest THEN ASM_REWRITE_TAC[];
    (* SOME k, ODD *)
    SUBGOAL_THEN `wl_get_var k (s:(A,C,FFI)wl_state) = SOME w` ASSUME_TAC THENL
     [MATCH_MP_TAC WPROOF1AUX_CSE_gets_var THEN
      MAP_EVERY EXISTS_TAC [`invalidate_data data v`; `name:store_name`] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC evaluate_Move1 THEN
      MATCH_MP_TAC WPROOF1AUX_CSE_get_var_latest THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`invalidate_data data v`; `s:(A,C,FFI)wl_state`; `name:store_name`;
                  `k:num`] WPROOF1AUX_CSE_gets_facts) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(k:num = v)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
    SUBGOAL_THEN `k IN domain (knowledge_to_canonical (invalidate_data data v))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM WPROOF1AUX_CSE_reorder_eq] THEN
    MATCH_MP_TAC data_inv_insert_to_latest THEN
    SIMP[domain_insert; IN_INSERT; wl_get_var_set_var] THEN
    MATCH_MP_TAC data_inv_insert_to_canonical THEN
    ASM_SIMP_TAC[data_inv_set_var; lookup_insert; wl_get_var_set_var; GSYM NOT_EVEN]];;

let WPROOF1AUX_CSE_canon_reinsert = prove
 (`!data (s:(A,C,FFI)wl_state) v.
     data_inv data s ==>
     lookup (canonicalRegs data v)
       (insert v (lookup_any v (knowledge_to_canonical data) v)
          (knowledge_to_canonical data)) = SOME (canonicalRegs data v)`,
  REWRITE_TAC[data_inv_def] THEN MESON_TAC[WPROOF1AUX_CSE_canon_reinsert_wf]);;

let WPROOF1AUX_CSE_CC_SET_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `exp:(A)wl_exp` (nchotomy_of_type `:(A)wl_exp`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_exp_conventions_def]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[word_cse_def; LET_DEF; LET_END_DEF; dest_Var_def] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Set"; wl_word_exp_def] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
  WPROOF1AUX_CSE_OCASES_TAC `wl_get_var a (s:(A,C,FFI)wl_state)` `w:(A)word_loc` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[data_inv_empty] THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Set"; wl_word_exp_def] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[] THEN
  (CONJ_TAC THENL
   [ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Set"; wl_word_exp_def] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC]) THENL
   [(* EVEN: only the gets of v are dropped *)
    MATCH_MP_TAC data_inv_set_store THEN
    ASM_SIMP_TAC[data_inv_filter_gets] THEN
    REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM; WPROOF1AUX_CSE_ALOOKUP_FILTER_NEQ];
    (* ODD: the new fact v -> canonical register of a *)
    WPROOF1AUX_CSE_REC_TAC
     `knowledge_gets_mem_fupd
        (K (CONS (v,canonicalRegs data a)
             (knowledge_gets_mem
               (knowledge_gets_mem_fupd
                 (K (FILTER (\(m,n). ~(m = v))
                      (knowledge_gets_mem
                        (knowledge_to_canonical_fupd
                          (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                                (knowledge_to_canonical data))) data))))
                 (knowledge_to_canonical_fupd
                   (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                         (knowledge_to_canonical data))) data)))))
        (knowledge_gets_mem_fupd
           (K (FILTER (\(m,n). ~(m = v))
                (knowledge_gets_mem
                  (knowledge_to_canonical_fupd
                    (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                          (knowledge_to_canonical data))) data))))
           (knowledge_to_canonical_fupd
             (K (insert a (lookup_any a (knowledge_to_canonical data) a)
                   (knowledge_to_canonical data))) data))` THEN
    MATCH_MP_TAC data_inv_cons_gets THEN EXISTS_TAC `w:(A)word_loc` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC data_inv_set_store THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC data_inv_filter_gets THEN MATCH_MP_TAC data_inv_reinsert_canonical THEN
        ASM_REWRITE_TAC[GSYM NOT_EVEN];
        REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM; WPROOF1AUX_CSE_ALOOKUP_FILTER_NEQ]];
      REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM; WPROOF1AUX_CSE_ALOOKUP_FILTER_NEQ];
      REWRITE_TAC[knowledge_INFO.ri_accfupds; K_THM] THEN
      ASM_MESON_TAC[WPROOF1AUX_CSE_canon_reinsert];
      REWRITE_TAC[wl_set_store_def] THEN SIMP[FLOOKUP_UPDATE];
      REWRITE_TAC[wl_get_var_def; wl_set_store_def] THEN SIMP[] THEN
      REWRITE_TAC[GSYM wl_get_var_def] THEN ASM_SIMP_TAC[canonicalRegs_correct]]];;

(* the instructions whose written registers are all untracked keep the      *)
(* invariant                                                                *)

let WPROOF1AUX_CSE_arith_untracked = prove
 (`!a (s:(A,C,FFI)wl_state) s1 data.
     wl_inst (asm_Arith a) s = SOME s1 /\ data_inv data s /\
     ALL (\r. lookup r (knowledge_to_canonical data) = NONE) (arithWrites a) ==>
     data_inv data s1`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[wl_inst_def; arithWrites_def; ALL] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REPEAT (CASE_TAC ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; GSYM option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[data_inv_set_var]);;

let WPROOF1AUX_CSE_fp_untracked = prove
 (`!fp (s:(A,C,FFI)wl_state) s1 data.
     wl_inst (FP fp) s = SOME s1 /\ data_inv data s /\
     ALL (\r. lookup r (knowledge_to_canonical data) = NONE) (fpWrites fp) ==>
     data_inv data s1`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `fp:fp` (cases "fp")) THEN
  REWRITE_TAC[wl_inst_def; fpWrites_def; ALL] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REPEAT (CASE_TAC ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; GSYM option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[data_inv_set_var; data_inv_set_fp_var]);;

(* the shape of the result of the storable instructions *)

let WPROOF1AUX_CSE_arith_set_first = prove
 (`!data a (s:(A,C,FFI)wl_state) s1.
     can_mem_arith (canonicalArith data a) /\ wl_inst (asm_Arith a) s = SOME s1 ==>
     ?w. s1 = wl_set_var (firstRegOfArith a) w s`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:(A)asm_arith` (cases "asm_arith")) THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a3:(A)reg_imm` (cases "reg_imm"))) THEN
  REWRITE_TAC[canonicalArith_def; canonicalImmReg'_def; can_mem_arith_def; wl_inst_def;
              firstRegOfArith_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT (CASE_TAC ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; GSYM option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_load_set = prove
 (`!op r a ofs (s:(A,C,FFI)wl_state) s1.
     ~is_store op /\ wl_inst (Mem op r (Addr a ofs)) s = SOME s1 ==>
     ?w. s1 = wl_set_var r w s`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[is_store_def; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  REPEAT (CASE_TAC ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; GSYM option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_store_mem = prove
 (`!op r a ofs (s:(A,C,FFI)wl_state) s1.
     is_store op /\ wl_inst (Mem op r (Addr a ofs)) s = SOME s1 ==>
     ?m. s1 = wl_state_memory_fupd (K m) s`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[is_store_def; wl_inst_def; wl_mem_store_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  REPEAT (CASE_TAC ORELSE PAIRARG_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; GSYM option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_pair_case_id = prove
 (CASE_TERM `!x:A#B. (match x with (a,b) -> (a,b)) = x`,
  GEN_TAC THEN MP_TAC(ISPEC `x:A#B` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* the Inst case of comp_correct, for a successful instruction *)

let WPROOF1AUX_CSE_cc_inst = prove
 (`!i (s:(A,C,FFI)wl_state) s1 data p' data'.
     wl_inst i s = SOME s1 /\ data_inv data s /\ word_cseInst data i = (data',p') ==>
     wl_evaluate (p',s) = (NONE,s1) /\ data_inv data' s1`,
  MATCH_MP_TAC inst_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Skip *)
    REPEAT GEN_TAC THEN REWRITE_TAC[word_cseInst_def; wl_inst_def; PAIR_EQ] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"; wl_inst_def] THEN
    CASE_REWRITE_TAC[];
    (* Const *)
    MAP_EVERY X_GEN_TAC [`r:num`; `w:A word`; `s:(A,C,FFI)wl_state`;
                         `s1:(A,C,FFI)wl_state`; `data:knowledge`; `p':(A)wl_prog`;
                         `data':knowledge`] THEN
    REWRITE_TAC[word_cseInst_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[wl_assign_def; wl_word_exp_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      ASM_SIMP_TAC[WPROOF1AUX_CSE_eval_const; data_inv_set_var;
                   WPROOF1AUX_CSE_lookup_invalidate_self; WPROOF1AUX_CSE_data_inv_invalidate];
      DISCH_TAC THEN MATCH_MP_TAC add_to_data_const_correct THEN
      EXISTS_TAC `invalidate_data data r` THEN
      ASM_SIMP_TAC[WPROOF1AUX_CSE_lookup_invalidate_self; WPROOF1AUX_CSE_data_inv_invalidate]];
    (* Arith *)
    MAP_EVERY X_GEN_TAC [`a:(A)asm_arith`; `s:(A,C,FFI)wl_state`;
                         `s1:(A,C,FFI)wl_state`; `data:knowledge`; `p':(A)wl_prog`;
                         `data':knowledge`] THEN
    REWRITE_TAC[word_cseInst_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN `data_inv (invalidate_regs data (arithWrites (a:(A)asm_arith)))
                           (s:(A,C,FFI)wl_state)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[data_inv_invalidate_regs]; ALL_TAC] THEN
    SUBGOAL_THEN `lookup (firstRegOfArith (a:(A)asm_arith))
       (knowledge_to_canonical (invalidate_regs data (arithWrites a))) = NONE`
      ASSUME_TAC THENL
     [ASM_SIMP_TAC[lookup_invalidate_regs; WPROOF1AUX_CSE_firstReg_writes]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPECL [`invalidate_regs data (arithWrites (a:(A)asm_arith))`; `a:(A)asm_arith`;
                    `s:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`]
                   WPROOF1AUX_CSE_arith_set_first) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:(A)word_loc` SUBST_ALL_TAC) THEN
      MATCH_MP_TAC add_to_data_Arith_correct THEN
      MAP_EVERY EXISTS_TAC [`invalidate_regs data (arithWrites (a:(A)asm_arith))`;
                            `a:(A)asm_arith`;
                            `canonicalArith (invalidate_regs data (arithWrites a))
                               (a:(A)asm_arith)`] THEN
      ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN CASE_REWRITE_TAC[];
      REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN CASE_REWRITE_TAC[] THEN
      MATCH_MP_TAC WPROOF1AUX_CSE_arith_untracked THEN
      MAP_EVERY EXISTS_TAC [`a:(A)asm_arith`; `s:(A,C,FFI)wl_state`] THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM] THEN SIMP_TAC[lookup_invalidate_regs]];
    (* Mem *)
    MAP_EVERY X_GEN_TAC [`op:memop`; `r:num`; `ad:(A)addr`] THEN
    STRUCT_CASES_TAC (ISPEC `ad:(A)addr` (cases "addr")) THEN
    MAP_EVERY X_GEN_TAC [`s:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`; `data:knowledge`;
                         `p':(A)wl_prog`; `data':knowledge`] THEN
    REWRITE_TAC[word_cseInst_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      MP_TAC(SPECL [`op:memop`; `r:num`; `a0:num`; `a1:A word`; `s:(A,C,FFI)wl_state`;
                    `s1:(A,C,FFI)wl_state`] WPROOF1AUX_CSE_store_mem) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:A word->(A)word_loc` SUBST_ALL_TAC) THEN
      ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN CASE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[data_inv_memory];
      ALL_TAC] THEN
    MP_TAC(SPECL [`op:memop`; `r:num`; `a0:num`; `a1:A word`; `s:(A,C,FFI)wl_state`;
                  `s1:(A,C,FFI)wl_state`] WPROOF1AUX_CSE_load_set) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:(A)word_loc` SUBST_ALL_TAC) THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN CASE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[data_inv_set_var; WPROOF1AUX_CSE_lookup_invalidate_self;
                   WPROOF1AUX_CSE_data_inv_invalidate];
      DISCH_TAC THEN MATCH_MP_TAC add_to_load_correct THEN
      MAP_EVERY EXISTS_TAC [`invalidate_data data r`; `op:memop`; `a0:num`;
                            `canonicalRegs' r (invalidate_data data r) a0`; `a1:A word`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
      ASM_SIMP_TAC[WPROOF1AUX_CSE_lookup_invalidate_self; WPROOF1AUX_CSE_data_inv_invalidate] THEN
      ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN CASE_REWRITE_TAC[]];
    (* FP *)
    MAP_EVERY X_GEN_TAC [`fp:fp`; `s:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`;
                         `data:knowledge`; `p':(A)wl_prog`; `data':knowledge`] THEN
    REWRITE_TAC[word_cseInst_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC WPROOF1AUX_CSE_fp_untracked THEN
    MAP_EVERY EXISTS_TAC [`fp:fp`; `s:(A,C,FFI)wl_state`] THEN
    ASM_SIMP_TAC[data_inv_invalidate_regs; GSYM ALL_MEM; lookup_invalidate_regs]]);;

let WPROOF1AUX_CSE_CC_INST_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[word_cse_def; WPROOF1AUX_CSE_pair_case_id] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Inst"] THEN
  WPROOF1AUX_CSE_OCASES_TAC `wl_inst (i:(A)inst) (s:(A,C,FFI)wl_state)`
    `s1:(A,C,FFI)wl_state` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC WPROOF1AUX_CSE_cc_inst THEN
  MAP_EVERY EXISTS_TAC [`i:(A)inst`; `data:knowledge`] THEN ASM_REWRITE_TAC[];;

(* the result of a successful ShareInst: the ffi state, and for a load the  *)
(* written register, change                                                 *)

let WPROOF1AUX_CSE_FFI_CASES_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> let h,args = strip_comb t in
                              is_const h && fst(dest_const h) = "call_FFI" &&
                              length args = 4) w in
  CASES_ON t g;;

let WPROOF1AUX_CSE_share_shape = prove
 (`!op v (ad:A word) (s:(A,C,FFI)wl_state) s1.
     share_inst op v ad s = ((NONE:((A)wl_result)option), s1) ==>
     ?f. (is_store op /\ s1 = wl_state_ffi_fupd (K f) s) \/
         (~is_store op /\ ?w. s1 = wl_set_var v w (wl_state_ffi_fupd (K f) s))`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def; is_store_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_sh_mem_load_def; wl_sh_mem_load_byte_def; wl_sh_mem_load16_def;
              wl_sh_mem_load32_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
              wl_sh_mem_store16_def; wl_sh_mem_store32_def] THEN
  REPEAT (CASE_TAC ORELSE COND_CASES_TAC ORELSE WPROOF1AUX_CSE_FFI_CASES_TAC) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ; option_DISTINCT; GSYM option_DISTINCT] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ; option_DISTINCT; GSYM option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_CC_SHAREINST_TAC : tactic =
  WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "ShareInst"] THEN
  REPEAT CASE_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT; GSYM option_DISTINCT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WPROOF1AUX_CSE_share_shape) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(FFI)ffi_state` MP_TAC) THEN
  ASM_CASES_TAC `is_store op` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[data_inv_set_var; WPROOF1AUX_CSE_lookup_invalidate_self] THEN
  MATCH_MP_TAC data_inv_state_agree THEN EXISTS_TAC `s:(A,C,FFI)wl_state` THEN
  ASM_SIMP_TAC[WPROOF1AUX_CSE_data_inv_invalidate] THEN SIMP[];;

(* the recursive cases of comp_correct *)

let WPROOF1AUX_CSE_CC_ERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;;

let WPROOF1AUX_CSE_CC_MUSTTERMINATE_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_exp_conventions_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[word_cse_def] THEN
  MP_TAC(ISPEC `word_cse data (p:(A)wl_prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:knowledge` (X_CHOOSE_THEN `q1:(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "MustTerminate"] THEN
  COND_CASES_TAC THENL [WPROOF1AUX_CSE_CC_ERR_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (p:(A)wl_prog,
                   wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                     (wl_state_termdep_fupd (K (wl_state_termdep s - 1))
                        (s:(A,C,FFI)wl_state)))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
    (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [WPROOF1AUX_CSE_CC_ERR_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(fun th ->
    if is_imp (concl th) then
      MP_TAC(SPECL [`r1:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`;
                    `data:knowledge`; `q1:(A)wl_prog`; `d1:knowledge`]
               (MP th (ASSUME `~(wl_state_termdep (s:(A,C,FFI)wl_state) = 0)`)))
    else NO_TAC) THEN
  ASM_SIMP_TAC[data_inv_clock] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "MustTerminate"] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[data_inv_clock];;

let WPROOF1AUX_CSE_CC_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_exp_conventions_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[word_cse_def] THEN
  MP_TAC(ISPEC `word_cse data (c1:(A)wl_prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:knowledge` (X_CHOOSE_THEN `q1:(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `word_cse d1 (c2:(A)wl_prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:knowledge` (X_CHOOSE_THEN `q2:(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Seq"] THEN
  MP_TAC(ISPEC `wl_evaluate (c1:(A)wl_prog, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
    (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`NONE:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`;
                                       `data:knowledge`; `q1:(A)wl_prog`; `d1:knowledge`]) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `t1:(A,C,FFI)wl_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `s':(A,C,FFI)wl_state`;
                               `d1:knowledge`; `q2:(A)wl_prog`; `d2:knowledge`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Seq"] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`r1:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`;
                                       `data:knowledge`; `q1:(A)wl_prog`; `d1:knowledge`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Seq"] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]];;

let WPROOF1AUX_CSE_CC_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_exp_conventions_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[word_cse_def] THEN
  MP_TAC(ISPEC `word_cse data (c1:(A)wl_prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:knowledge` (X_CHOOSE_THEN `q1:(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `word_cse data (c2:(A)wl_prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:knowledge` (X_CHOOSE_THEN `q2:(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `wf_data (:A) d1 /\ wf_data (:A) d2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c1:(A)wl_prog`; `data:knowledge`] word_cse_wf_data) THEN
    MP_TAC(ISPECL [`c2:(A)wl_prog`; `data:knowledge`] word_cse_wf_data) THEN
    ASM_REWRITE_TAC[FST] THEN UNDISCH_TAC `data_inv data (s:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[data_inv_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_If"] THEN
  WPROOF1AUX_CSE_OCASES_TAC `wl_get_var r1 (s:(A,C,FFI)wl_state)` `x:(A)word_loc` THEN
  CASE_REWRITE_TAC[] THEN TRY WPROOF1AUX_CSE_CC_ERR_TAC THEN
  WPROOF1AUX_CSE_OCASES_TAC `wl_get_var_imm (ri:(A)reg_imm) (s:(A,C,FFI)wl_state)`
    `y:(A)word_loc` THEN
  CASE_REWRITE_TAC[] THEN TRY WPROOF1AUX_CSE_CC_ERR_TAC THEN
  WPROOF1AUX_CSE_OCASES_TAC `wl_word_cmp cmp (x:(A)word_loc) y` `b:bool` THEN
  CASE_REWRITE_TAC[] THEN TRY WPROOF1AUX_CSE_CC_ERR_TAC THEN
  COND_CASES_TAC THEN DISCH_TAC THENL
   [REMOVE_THEN "ih1" (MP_TAC o SPECL [`x:(A)word_loc`; `y:(A)word_loc`; `b:bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `s':(A,C,FFI)wl_state`;
                               `data:knowledge`; `q1:(A)wl_prog`; `d1:knowledge`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_If"] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RES_TAC THEN
    MATCH_MP_TAC data_inv_merge_l THEN RULE_ASSUM_TAC(REWRITE_RULE[data_inv_def]) THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`x:(A)word_loc`; `y:(A)word_loc`; `b:bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `s':(A,C,FFI)wl_state`;
                               `data:knowledge`; `q2:(A)wl_prog`; `d2:knowledge`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_If"] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RES_TAC THEN
    MATCH_MP_TAC data_inv_merge_r THEN RULE_ASSUM_TAC(REWRITE_RULE[data_inv_def]) THEN
    ASM_REWRITE_TAC[]];;

let WPROOF1AUX_CSE_CC_LOOP_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_exp_conventions_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[word_cse_def] THEN
  MP_TAC(ISPEC `word_cse empty_data (c:(A)wl_prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:knowledge` (X_CHOOSE_THEN `q1:(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN REWRITE_TAC[data_inv_empty] THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  ONCE_REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Loop"] THEN
  WPROOF1AUX_CSE_OCASES_TAC `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)`
    `s0:(A,C,FFI)wl_state` THEN
  CASE_REWRITE_TAC[] THEN TRY WPROOF1AUX_CSE_CC_ERR_TAC THEN
  MP_TAC(ISPEC `wl_evaluate (c:(A)wl_prog, s0:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option`
    (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = SOME (wl_Error:(A)wl_result)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[wl_cont_loop_def; wl_exit_loop_def; option_INJ] THEN
    REWRITE_TAC[distinctness "wl_result"] THEN WPROOF1AUX_CSE_CC_ERR_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (q1:(A)wl_prog, s0:(A,C,FFI)wl_state) = (r,s1)` ASSUME_TAC THENL
   [REMOVE_THEN "ih2" (MP_TAC o SPEC `s0:(A,C,FFI)wl_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`;
                               `empty_data`; `q1:(A)wl_prog`; `d1:knowledge`]) THEN
    ASM_REWRITE_TAC[data_inv_empty] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`s0:(A,C,FFI)wl_state`; `r:((A)wl_result)option`;
                                     `s1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `s':(A,C,FFI)wl_state`;
                             `empty_data`; `wl_Loop names q1 exit_names:(A)wl_prog`;
                             `empty_data`]) THEN
  ASM_REWRITE_TAC[wl_STOP_def; flat_exp_conventions_def; data_inv_empty; word_cse_def] THEN
  CASE_REWRITE_TAC[] THEN SIMP_TAC[];;

let WPROOF1AUX_CSE_CC_SKIP_TAC : tactic =
  WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WPROOF1AUX_CSE_is_eval_eq) THEN
  REWRITE_TAC[WPROOF1AUX_CSE_eval_clause "wl_Skip"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[];;

(* HOL4: comp_correct *)

let word_cseProof_comp_correct = prove
 (`!v (v1:(A,C,FFI)wl_state) res s' data p' data'.
     wl_evaluate (v,v1) = (res,s') /\ flat_exp_conventions v /\ data_inv data v1 /\
     ~(res = SOME wl_Error) /\ word_cse data v = (data',p') ==>
     wl_evaluate (p',v1) = (res,s') /\ (res = NONE ==> data_inv data' s')`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   [(* Skip *) WPROOF1AUX_CSE_CC_SKIP_TAC;
    (* Alloc *) WPROOF1AUX_CSE_CC_SIMPLE_TAC;
    (* StoreConsts *) WPROOF1AUX_CSE_CC_STORECONSTS_TAC;
    (* Move *) WPROOF1AUX_CSE_CC_MOVE_TAC;
    (* Inst *) WPROOF1AUX_CSE_CC_INST_TAC;
    (* Assign *) REWRITE_TAC[flat_exp_conventions_def];
    (* Get *) WPROOF1AUX_CSE_CC_GET_TAC;
    (* Set *) WPROOF1AUX_CSE_CC_SET_TAC;
    (* OpCurrHeap *) WPROOF1AUX_CSE_CC_OPCURRHEAP_TAC;
    (* Store *) REWRITE_TAC[flat_exp_conventions_def];
    (* Tick *) WPROOF1AUX_CSE_CC_AGREE_TAC "wl_Tick";
    (* MustTerminate *) WPROOF1AUX_CSE_CC_MUSTTERMINATE_TAC;
    (* Seq *) WPROOF1AUX_CSE_CC_SEQ_TAC;
    (* Return *)
    WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN WPROOF1AUX_CSE_CC_NOT_NONE_TAC "wl_Return";
    (* Raise *)
    WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN WPROOF1AUX_CSE_CC_NOT_NONE_TAC "wl_Raise";
    (* Break *)
    WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN WPROOF1AUX_CSE_CC_NOT_NONE_TAC "wl_Break";
    (* Continue *)
    WPROOF1AUX_CSE_CC_SIMPLE_TAC THEN WPROOF1AUX_CSE_CC_NOT_NONE_TAC "wl_Continue";
    (* If *) WPROOF1AUX_CSE_CC_IF_TAC;
    (* Loop *) WPROOF1AUX_CSE_CC_LOOP_TAC;
    (* LocValue *) WPROOF1AUX_CSE_CC_LOCVALUE_TAC;
    (* Install *) WPROOF1AUX_CSE_CC_SIMPLE_TAC;
    (* CodeBufferWrite *) WPROOF1AUX_CSE_CC_AGREE_TAC "wl_CodeBufferWrite";
    (* DataBufferWrite *) WPROOF1AUX_CSE_CC_AGREE_TAC "wl_DataBufferWrite";
    (* FFI *) WPROOF1AUX_CSE_CC_SIMPLE_TAC;
    (* ShareInst *) WPROOF1AUX_CSE_CC_SHAREINST_TAC;
    (* Call *) REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN WPROOF1AUX_CSE_CC_SIMPLE_TAC]);;

let word_common_subexp_elim_correct = prove
 (`wl_evaluate (p, s:(A,C,FFI)wl_state) = (res,s1) /\
   flat_exp_conventions p /\ ~(res = SOME wl_Error) ==>
   wl_evaluate (word_common_subexp_elim p, s) = (res,s1)`,
  REWRITE_TAC[word_common_subexp_elim_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `word_cse empty_data (p:(A)wl_prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:knowledge` (X_CHOOSE_THEN `q:(A)wl_prog` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `s:(A,C,FFI)wl_state`; `res:((A)wl_result)option`;
                 `s1:(A,C,FFI)wl_state`; `empty_data`; `q:(A)wl_prog`; `d:knowledge`]
                word_cseProof_comp_correct) THEN
  ASM_REWRITE_TAC[data_inv_empty] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Syntactic conventions: word_cse emits the original instructions or Moves *)
(* ------------------------------------------------------------------------- *)

let WPROOF1AUX_CSE_cseInst_shape = prove
 (`!data (i:(A)inst).
     SND (word_cseInst data i) = wl_Inst i \/
     ?pri r k. SND (word_cseInst data i) = wl_Move pri [(r,k)]`,
  GEN_TAC THEN MATCH_MP_TAC inst_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a2:(A)addr` (cases "addr"))) THEN
  REWRITE_TAC[word_cseInst_def; add_to_data_def; add_to_data_aux_def; add_to_data_const_def;
              add_to_load_aux_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT (COND_CASES_TAC ORELSE CASE_TAC) THEN REWRITE_TAC[SND] THEN MESON_TAC[]);;

let WPROOF1AUX_CSE_SND_word_cse = prove
 (`(!data (i:(A)inst). SND (word_cse data (wl_Inst i)) = SND (word_cseInst data i)) /\
   (!data (p:(A)wl_prog).
      SND (word_cse data (MustTerminate p)) = MustTerminate (SND (word_cse data p))) /\
   (!data (p1:(A)wl_prog) p2.
      SND (word_cse data (wl_Seq p1 p2)) =
      wl_Seq (SND (word_cse data p1)) (SND (word_cse (FST (word_cse data p1)) p2))) /\
   (!data c r1 r2 (p1:(A)wl_prog) p2.
      SND (word_cse data (wl_If c r1 r2 p1 p2)) =
      wl_If c r1 r2 (SND (word_cse data p1)) (SND (word_cse data p2))) /\
   (!data names (c:(A)wl_prog) exit_names.
      SND (word_cse data (wl_Loop names c exit_names)) =
      wl_Loop names (SND (word_cse empty_data c)) exit_names)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[word_cse_def] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST; SND]);;

(* a syntactic property Q, with the definitions defs, of the programs that  *)
(* holds of every Move: the goal is !data p. Q p ==> Q (SND (word_cse data p)) *)

let WPROOF1AUX_CSE_SYN_TAC (defs:thm list) : tactic =
  MATCH_MP_TAC word_cse_ind THEN REWRITE_TAC[WPROOF1AUX_CSE_SND_word_cse] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [(* Inst *)
    MAP_EVERY X_GEN_TAC [`data:knowledge`; `i:(A)inst`] THEN
    MP_TAC(SPECL [`data:knowledge`; `i:(A)inst`] WPROOF1AUX_CSE_cseInst_shape) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC defs THEN NO_TAC;
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`data:knowledge`; `p1:(A)wl_prog`; `p2:(A)wl_prog`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`SND (word_cse data (p1:(A)wl_prog))`;
                                               `FST (word_cse data (p1:(A)wl_prog))`])
                               ASSUME_TAC) THEN
    REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE defs) THEN REWRITE_TAC defs THEN
    ASM_MESON_TAC[] THEN NO_TAC;
    (* If *)
    MAP_EVERY X_GEN_TAC [`data:knowledge`; `c:cmp`; `r1:num`; `r2:(A)reg_imm`;
                         `p1:(A)wl_prog`; `p2:(A)wl_prog`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
                 (MP_TAC o SPECL [`FST (word_cse data (p1:(A)wl_prog))`;
                                  `SND (word_cse data (p1:(A)wl_prog))`])) THEN
    REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE defs) THEN REWRITE_TAC defs THEN
    ASM_MESON_TAC[] THEN NO_TAC;
    (* the others *)
    REPEAT GEN_TAC THEN
    REWRITE_TAC[word_cse_def; add_to_data_aux_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REPEAT (COND_CASES_TAC ORELSE CASE_TAC) THEN REWRITE_TAC[SND] THEN
    REWRITE_TAC defs THEN NO_TAC;
    (* MustTerminate, Loop *)
    REPEAT GEN_TAC THEN REWRITE_TAC defs THEN MESON_TAC[]];;

let WPROOF1AUX_CSE_SYN_PAIR_TAC (th:thm) : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `SND:knowledge#(A)wl_prog->(A)wl_prog` o
                check WPROOF1AUX_CSE_is_cse_eq) THEN
  REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC th THEN ASM_REWRITE_TAC[];;

let WPROOF1AUX_CSE_full_inst_ok_less = prove
 (`!c data (p:(A)wl_prog).
     full_inst_ok_less c p ==> full_inst_ok_less c (SND (word_cse data p))`,
  GEN_TAC THEN WPROOF1AUX_CSE_SYN_TAC [full_inst_ok_less_def]);;

let word_cse_full_inst_ok_less = prove
 (`!p data c data' (q:(A)wl_prog).
     full_inst_ok_less c p /\ word_cse data p = (data',q) ==> full_inst_ok_less c q`,
  WPROOF1AUX_CSE_SYN_PAIR_TAC WPROOF1AUX_CSE_full_inst_ok_less);;

let WPROOF1AUX_CSE_pre_alloc_conventions = prove
 (`!data (p:(A)wl_prog).
     pre_alloc_conventions p ==> pre_alloc_conventions (SND (word_cse data p))`,
  WPROOF1AUX_CSE_SYN_TAC [pre_alloc_conventions_def; every_stack_var_def;
                          call_arg_convention_def]);;

let word_cse_pre_alloc_conventions = prove
 (`!p data data' (q:(A)wl_prog).
     pre_alloc_conventions p /\ word_cse data p = (data',q) ==> pre_alloc_conventions q`,
  WPROOF1AUX_CSE_SYN_PAIR_TAC WPROOF1AUX_CSE_pre_alloc_conventions);;

let WPROOF1AUX_CSE_every_inst_distinct_tar_reg = prove
 (`!data (p:(A)wl_prog).
     every_inst distinct_tar_reg p ==>
     every_inst distinct_tar_reg (SND (word_cse data p))`,
  WPROOF1AUX_CSE_SYN_TAC [every_inst_def]);;

let word_cse_every_inst_distinct_tar_reg = prove
 (`!p data data' (q:(A)wl_prog).
     every_inst distinct_tar_reg p /\ word_cse data p = (data',q) ==>
     every_inst distinct_tar_reg q`,
  WPROOF1AUX_CSE_SYN_PAIR_TAC WPROOF1AUX_CSE_every_inst_distinct_tar_reg);;

let WPROOF1AUX_CSE_every_inst_two_reg = prove
 (`!data (p:(A)wl_prog).
     every_inst two_reg_inst p ==> every_inst two_reg_inst (SND (word_cse data p))`,
  WPROOF1AUX_CSE_SYN_TAC [every_inst_def]);;

let word_cse_every_inst_two_reg = prove
 (`!p data data' (q:(A)wl_prog).
     every_inst two_reg_inst p /\ word_cse data p = (data',q) ==>
     every_inst two_reg_inst q`,
  WPROOF1AUX_CSE_SYN_PAIR_TAC WPROOF1AUX_CSE_every_inst_two_reg);;

let WPROOF1AUX_CSE_wcse_SND = prove
 (`!p:(A)wl_prog. word_common_subexp_elim p = SND (word_cse empty_data p)`,
  GEN_TAC THEN REWRITE_TAC[word_common_subexp_elim_def; LET_DEF; LET_END_DEF] THEN
  PAIRARG_TAC THEN ASM_REWRITE_TAC[SND]);;

let every_inst_distinct_tar_reg_word_common_subexp_elim = prove
 (`every_inst distinct_tar_reg (p:(A)wl_prog) ==>
   every_inst distinct_tar_reg (word_common_subexp_elim p)`,
  REWRITE_TAC[WPROOF1AUX_CSE_wcse_SND; WPROOF1AUX_CSE_every_inst_distinct_tar_reg]);;

let pre_alloc_conventions_word_common_subexp_elim = prove
 (`pre_alloc_conventions (p:(A)wl_prog) ==>
   pre_alloc_conventions (word_common_subexp_elim p)`,
  REWRITE_TAC[WPROOF1AUX_CSE_wcse_SND; WPROOF1AUX_CSE_pre_alloc_conventions]);;

let full_inst_ok_less_word_common_subexp_elim = prove
 (`full_inst_ok_less ac (p:(A)wl_prog) ==>
   full_inst_ok_less ac (word_common_subexp_elim p)`,
  REWRITE_TAC[WPROOF1AUX_CSE_wcse_SND; WPROOF1AUX_CSE_full_inst_ok_less]);;

