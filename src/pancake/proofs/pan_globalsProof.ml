(* ========================================================================= *)
(* pan_globalsProof: port of HOL4 pancake/proofs/pan_globalsProofScript.sml  *)
(* (CakeML v3479).  Correctness proof for pan_globals.                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/semantics/panSem.ml";;
needs "pancake/pan_globals.ml";;
needs "pancake/semantics/panProps.ml";;
needs "pancake/panLang.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 [local] theorems are bound like the others; PPASS2AUX_ names are   *)
(* local helpers.                                                            *)

let disjoint_globals_def = cake_def
  `disjoint_globals (top_addr:A word) (cglobals:(mlstring,shape#A word)fmap)
                    (globals:(mlstring,B)fmap) <=>
     !v v' sh addr sh' addr'.
       ~(v = v') /\ IS_SOME (FLOOKUP globals v) /\ IS_SOME (FLOOKUP globals v') /\
       FLOOKUP cglobals v = SOME (sh,addr) /\
       FLOOKUP cglobals v' = SOME (sh',addr')
       ==> DISJOINT (addresses (word_sub top_addr addr) (size_of_shape sh))
                    (addresses (word_sub top_addr addr') (size_of_shape sh'))`;;

(* HOL4 is_wf_shape_nil (an Overload of panProps) is                         *)
(* is_wf_shape ([]:(mlstring#struct_info)list); the bound variable val of    *)
(* HOL4 (a constant here) is value                                           *)

let pan_globalsProof_state_rel_def = cake_def
  `pan_globalsProof_state_rel ls (ctxt:(A)pan_globals_context)
     (s:(A,FFI)pan_state) (t:(A,FFI)pan_state) <=>
   pan_state_top_addr s =
     word_sub (pan_state_top_addr t) (pan_globals_context_max_globals_size ctxt) /\
   (ls ==> pan_state_locals s = pan_state_locals t) /\
   pan_state_base_addr s = pan_state_base_addr t /\
   pan_state_be s = pan_state_be t /\
   pan_state_eshapes s = pan_state_eshapes t /\
   pan_state_clock s = pan_state_clock t /\
   pan_state_structs s = [] /\ pan_state_structs t = [] /\
   (!v value.
      FLOOKUP (pan_state_globals s) v = SOME value
      ==> ?addr. FLOOKUP (pan_globals_context_globals ctxt) v =
                   SOME (shape_of value,addr) /\
                 is_wf_shape ([]:(mlstring#struct_info)list) (shape_of value) /\
                 pan_mem_load (shape_of value) (word_sub (pan_state_top_addr t) addr)
                   (pan_state_memaddrs t) (pan_state_memory t) [] = SOME value /\
                 DISJOINT (pan_state_memaddrs s)
                   (addresses (word_sub (pan_state_top_addr t) addr)
                      (size_of_shape (shape_of value))) /\
                 byte_aligned addr) /\
   FEVERY (\(nm,(sh,addr)). is_wf_shape ([]:(mlstring#struct_info)list) sh)
          (pan_globals_context_globals ctxt) /\
   pan_state_memaddrs s SUBSET pan_state_memaddrs t /\
   pan_state_sh_memaddrs s = pan_state_sh_memaddrs t /\
   (!addr. addr IN pan_state_memaddrs s
           ==> pan_state_memory s addr = pan_state_memory t addr) /\
   pan_state_ffi s = pan_state_ffi t /\
   (!fname vshapes prog rshape.
      FLOOKUP (pan_state_code s) fname = SOME (vshapes,prog,rshape)
      ==> FLOOKUP (pan_state_code t) fname =
            SOME (vshapes,pan_globals_compile ctxt prog,rshape)) /\
   disjoint_globals (pan_state_top_addr t) (pan_globals_context_globals ctxt)
                    (pan_state_globals s) /\
   ~(pan_state_top_addr t IN pan_state_memaddrs t) /\
   byte_aligned (pan_state_top_addr t) /\
   good_dimindex(:A)`;;

let pan_globalsProof_state_rel_structs = prove
 (`pan_globalsProof_state_rel ls ctxt (s:(A,FFI)pan_state) t
   ==> pan_state_structs s = [] /\ pan_state_structs t = []`,
  SIMP[pan_globalsProof_state_rel_def]);;

let state_rel_globals_wf = prove
 (`FLOOKUP (pan_globals_context_globals ctxt) nm = SOME x /\
   pan_globalsProof_state_rel ls ctxt (s:(A,FFI)pan_state) t
   ==> is_wf_shape ([]:(mlstring#struct_info)list) (FST x)`,
  RW[pan_globalsProof_state_rel_def] THEN
  IMP_RES_TAC FEVERY_FLOOKUP THEN
  POP_ASSUM MP_TAC THEN PAIR_CASES_ON `x:shape#A word` THEN SIMP[]);;

(* the memory part of HOL4's generalised statement in state_rel_mem_load *)

let PPASS2AUX_mem_load_mono = prove
 (`!dm' (m':A word->(A)word_lab).
   (!sh addr dm (m:A word->(A)word_lab) stcs v.
      pan_mem_load sh addr dm m stcs = SOME v /\ stcs = [] /\
      dm SUBSET dm' /\ (!a. a IN dm ==> m a = m' a)
      ==> pan_mem_load sh addr dm' m' stcs = SOME v) /\
   (!shs addr dm (m:A word->(A)word_lab) stcs vs.
      mem_loads shs addr dm m stcs = SOME vs /\ stcs = [] /\
      dm SUBSET dm' /\ (!a. a IN dm ==> m a = m' a)
      ==> mem_loads shs addr dm' m' stcs = SOME vs) /\
   (!flds addr dm (m:A word->(A)word_lab) stcs vs.
      mem_load_flds flds addr dm m stcs = SOME vs ==> T)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC pan_mem_load_ind THEN RW[] THEN
  GVS(pan_mem_load_def::dropWhile_def::all_case_eqs()) THEN ASM SET_TAC[]);;

let state_rel_mem_load = prove
 (`pan_globalsProof_state_rel ls ctxt (s:(A,FFI)pan_state) t /\
   pan_mem_load shape w (pan_state_memaddrs s) (pan_state_memory s) [] = SOME v
   ==> pan_mem_load shape w (pan_state_memaddrs t) (pan_state_memory t) [] =
       SOME v`,
  RW[pan_globalsProof_state_rel_def] THEN
  MATCH_MP_TAC(CONJUNCT1(SPEC_ALL PPASS2AUX_mem_load_mono)) THEN
  MAP_EVERY EXISTS_TAC [`pan_state_memaddrs (s:(A,FFI)pan_state)`;
                        `pan_state_memory (s:(A,FFI)pan_state)`] THEN
  ASM_REWRITE_TAC[]);;

let pan_globalsProof_compile_exp_correct = prove
 (`!s e v ctxt t.
     pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t /\
     pan_eval s e = SOME v
     ==> pan_eval t (pan_globals_compile_exp ctxt e) = SOME v`,
  let defs = pan_eval_def::pan_globals_compile_exp_def::all_case_eqs() in
  let mmap_tac =
    SIMP[OPT_MMAP_MAP_o] THEN IRULE EQ_TRANS THEN
    FIRST_ASSUM(IRULE_AT (Pos last)) THEN IRULE OPT_MMAP_CONG THEN RW[] THEN
    FIRST_X_ASSUM(DRULE_THEN DRULE) THEN DRULE_ALL opt_mmap_mem_func THEN
    STRIP_TAC THEN GVS[] in
  let ih_tac = GVS defs THEN RES_TAC THEN GVS[] in
  let structs_tac =
    IMP_RES_TAC pan_globalsProof_state_rel_structs THEN GVS(ALOOKUP_DEF::defs) in
  let sr_tac =
    GVS(pan_globalsProof_state_rel_def::OPT_MMAP_def::OPTION_BIND_DEF::
        OPTION_MAP_DEF::word_op_def::defs) in
  let mem_tac th =
    GVS(th::defs) THEN RES_TAC THEN
    GVS(pan_globalsProof_state_rel_def::SUBSET::all_case_eqs()) in
  MATCH_MP_TAC pan_eval_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [(* Const *) GVS defs;
    (* Var Local *) sr_tac;
    (* Var Global *)
    GVS(pan_globalsProof_state_rel_def::defs) THEN FIRST_X_ASSUM DRULE THEN
    RW[] THEN RW[OPT_MMAP_def; OPTION_BIND_DEF; OPTION_MAP_DEF; pan_eval_def;
                 word_op_def];
    (* RStruct *) GVS defs THEN mmap_tac;
    (* RField *) ih_tac;
    (* NStruct *) structs_tac;
    (* NField *) structs_tac;
    (* Load *)
    GVS defs THEN IMP_RES_TAC pan_globalsProof_state_rel_structs THEN
    ASM_MESON_TAC[state_rel_mem_load];
    (* Load32 *) mem_tac pan_mem_load_32_alt;
    (* LoadByte *) mem_tac pan_mem_load_byte_def;
    (* Op *) GVS defs THEN FIRST_ASSUM(IRULE_AT (Pos last)) THEN mmap_tac;
    (* Panop *) GVS defs THEN FIRST_ASSUM(IRULE_AT (Pos last)) THEN mmap_tac;
    (* Cmp *) ih_tac THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    (* Shift *) ih_tac;
    (* BaseAddr *) sr_tac;
    (* TopAddr *) sr_tac;
    (* BytesInWord *) sr_tac]);;

let good_res_def = cake_def
  `(good_res (SOME pan_TimeOut:((A)pan_result)option) <=> F) /\
   (good_res (SOME (pan_Return v)) <=> F) /\
   (good_res (SOME (pan_Exception l v)) <=> F) /\
   (good_res (SOME (pan_FinalFFI ev)) <=> F) /\
   (good_res _ <=> T)`;;

(* HOL4 compile_correct is proved by induction on evaluate_ind with the     *)
(* goal below, case by case (suspend/Resume): PPASS2AUX_compile_correct_ind *)
(* is the instance of pan_evaluate_ind, PPASS2AUX_cc_case "C" the case of   *)
(* the program constructor C; each case is proved where HOL4 resumes it,    *)
(* and compile_correct is assembled after the last one.                     *)

let PPASS2AUX_compile_correct_ind =
  let goal = `\(p:(A)panLang_prog,s:(A,FFI)pan_state).
      !res ctxt t s'.
        pan_globalsProof_state_rel T ctxt s t /\
        pan_evaluate (p,s) = (res,s') /\
        ~(res = SOME pan_Error)
        ==> ?t'. pan_evaluate (pan_globals_compile ctxt p,t) = (res,t') /\
                 pan_globalsProof_state_rel (good_res res) ctxt s' t'` in
  CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (ISPEC goal pan_evaluate_ind);;

let PPASS2AUX_cc_case name =
  let cases = conjuncts (lhand (concl PPASS2AUX_compile_correct_ind)) in
  let prog_of c =
    let body = snd (strip_forall c) in
    let ab = if is_forall (rand body) then snd (strip_forall (rand body))
             else body in
    let ev = lhand (el 1 (conjuncts (lhand ab))) in
    fst (dest_pair (rand ev)) in
  find (fun c -> let h = fst (strip_comb (prog_of c)) in
                 is_const h && fst (dest_const h) = name) cases;;

let PPASS2AUX_simple_tac =
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::pan_dec_clock_def::
      pan_globalsProof_state_rel_def::pan_empty_locals_def::good_res_def::
      all_case_eqs());;

let PPASS2AUX_cc_Skip =
  prove(PPASS2AUX_cc_case "panLang_Skip", PPASS2AUX_simple_tac);;

let PPASS2AUX_cc_Break =
  prove(PPASS2AUX_cc_case "panLang_Break", PPASS2AUX_simple_tac);;

let PPASS2AUX_cc_Continue =
  prove(PPASS2AUX_cc_case "panLang_Continue", PPASS2AUX_simple_tac);;

let PPASS2AUX_cc_Annot =
  prove(PPASS2AUX_cc_case "Annot", PPASS2AUX_simple_tac);;

let PPASS2AUX_cc_Tick =
  prove(PPASS2AUX_cc_case "panLang_Tick", PPASS2AUX_simple_tac);;

(* HOL4 names the memory variables memory, memory' (memory was a constant  *)
(* of stack_removeProof, now stack_removeProof_memory): mem, mem'          *)

let mem_stores_append = prove
 (CASE_TERM
  `!addr vs addrs (mem:A word->(A)word_lab) vs'.
     mem_stores addr (APPEND vs vs') addrs mem =
     match mem_stores addr vs addrs mem with
       NONE -> NONE
     | SOME mem' ->
         mem_stores (word_add addr (word_mul bytes_in_word (word (LENGTH vs))))
                    vs' addrs mem'`,
  QINDUCT_ON "vs" THEN RW[mem_stores_def] THEN
  REPEAT(TOP_CASE_TAC THEN GVS[n2w_SUC; WORD_LEFT_ADD_DISTRIB]) THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN CONV_TAC WORD_RULE);;

let mem_stores_memory_swap = prove
 (`!addr vs addrs (mem:A word->(A)word_lab) mem' m.
     mem_stores addr vs addrs mem = SOME m
     ==> ?m'. mem_stores addr vs addrs mem' = SOME m'`,
  QINDUCT_ON "vs" THEN RW(mem_stores_def::pan_mem_store_def::all_case_eqs()) THEN
  ASM_MESON_TAC[]);;

let mem_load_mem_store = prove
 (`(!s (addr:A word) addrs mem sctxt v (w:(A)pan_v).
     pan_mem_load s addr addrs mem sctxt = SOME v /\
     sctxt = [] /\ is_wf_shape sctxt s /\ shape_of w = s
     ==> ?m. mem_stores addr (flatten w) addrs mem = SOME m) /\
   (!ss (addr:A word) addrs mem sctxt vs (ws:((A)pan_v)list).
     mem_loads ss addr addrs mem sctxt = SOME vs /\
     sctxt = [] /\ ALL (is_wf_shape sctxt) ss /\ ss = MAP shape_of ws
     ==> ?m. mem_stores addr (FLAT (MAP (\a. flatten a) ws)) addrs mem = SOME m) /\
   (!fs (addr:A word) addrs (mem:A word->(A)word_lab) sctxt vfs.
     mem_load_flds fs addr addrs mem sctxt = SOME vfs /\ sctxt = [] /\ T ==> T)`,
  let mls_cons = el 2 (CONJUNCTS pan_mem_load_def) in
  MATCH_MP_TAC pan_mem_load_ind THEN REPEAT CONJ_TAC THEN REWRITE_TAC[] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    NAMED_CASES_ON "w" ["wl"; "vs"; "nm flds"] THEN
    REWRITE_TAC[shape_of_def; flatten_def] THENL
     [QCASES_ON "wl" THEN
      RW(shape_of_def::pan_mem_load_def::mem_stores_def::pan_mem_store_def::
         all_case_eqs());
      STRIP_TAC THEN RVEQ_TAC THEN FS(pan_mem_load_def::all_case_eqs()) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:((A)pan_v)list`; `vs:((A)pan_v)list`]) THEN
      FS[is_wf_shape_def; ETA_AX];
      STRIP_TAC THEN RVEQ_TAC THEN FS[is_wf_shape_def; ALOOKUP_DEF]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN QCASES_ON "ws" THEN FS[FLAT; mem_stores_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RVEQ_TAC THEN QCASES_ON "ws" THEN FS[] THEN RVEQ_TAC THEN
    FS(mls_cons::all_case_eqs()) THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:((A)pan_v)list`; `a1:((A)pan_v)list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:(A)pan_v`; `a0:(A)pan_v`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FLAT; mem_stores_append; option_CASE] THEN
    ASM_SIMP_TAC[length_flatten_eq_size_of_shape] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `size_of_sh_with_ctxt`) o rator) (lhs (concl th)))) THEN
    ASM_SIMP_TAC[size_of_sh_with_ctxt_eq] THEN
    MESON_TAC[mem_stores_memory_swap]]);;

let mem_stores_lookup = prove
 (`!addr vs addrs (mem:A word->(A)word_lab) m addr'.
     mem_stores addr vs addrs mem = SOME m /\
     ~(addr' IN addresses addr (LENGTH vs))
     ==> m addr' = mem addr'`,
  QINDUCT_ON "vs" THEN RW(mem_stores_def::addresses_def::all_case_eqs()) THEN
  FS[IN_INSERT; DE_MORGAN_THM] THEN RES_TAC THEN SIMP[] THEN
  GVS(pan_mem_store_def::APPLY_UPDATE_THM::all_case_eqs()));;

(* the addresses of a block of m + n words are those of its first m words  *)
(* and of its last n                                                        *)

let PPASS2AUX_addresses_add = prove
 (`!m n (a:A word).
     addresses a (m + n) =
     addresses a m UNION addresses (word_add a (word_mul bytes_in_word (word m))) n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; addresses_def; UNION_EMPTY] THENL
   [REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[INSERT_UNION_EQ; n2w_SUC] THEN REPEAT GEN_TAC THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN CONV_TAC WORD_RULE]);;

let PPASS2AUX_addresses_1 = prove
 (`!a:A word. addresses a 1 = {a}`,
  REWRITE_TAC[num_CONV `1`; addresses_def]);;

let mem_stores_load_disjoint = prove
 (`(!sh (addr:A word) vs addrs (mem:A word->(A)word_lab) m stcs addr'.
     mem_stores addr vs addrs mem = SOME m /\
     stcs = [] /\ is_wf_shape stcs sh /\
     DISJOINT (addresses addr' (size_of_shape sh)) (addresses addr (LENGTH vs))
     ==> pan_mem_load sh addr' addrs m stcs = pan_mem_load sh addr' addrs mem []) /\
   (!shs (addr:A word) vs addrs (mem:A word->(A)word_lab) m stcs addr'.
     mem_stores addr vs addrs mem = SOME m /\
     stcs = [] /\ ALL (is_wf_shape stcs) shs /\
     DISJOINT (addresses addr' (SUM (MAP size_of_shape shs)))
              (addresses addr (LENGTH vs))
     ==> mem_loads shs addr' addrs m stcs = mem_loads shs addr' addrs mem [])`,
  let ih_tac a' =
    FIRST_X_ASSUM(MP_TAC o SPECL [`addr:A word`; `vs:((A)word_lab)list`;
      `addrs:A word->bool`; `mem:A word->(A)word_lab`; `m:A word->(A)word_lab`; a']) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC in
  MATCH_MP_TAC shape_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN ONCE_REWRITE_TAC[pan_mem_load_def] THEN
  FS[is_wf_shape_def; size_of_shape_def; ALOOKUP_DEF; PPASS2AUX_addresses_1] THENL
   [SUBGOAL_THEN `~((addr':A word) IN addresses addr (LENGTH (vs:((A)word_lab)list)))`
      ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    IMP_RES_TAC mem_stores_lookup THEN ASM_REWRITE_TAC[];
    ih_tac `addr':A word` THEN REFL_TAC;
    QPAT_X_ASSUM "DISJOINT _ _"
      (STRIP_ASSUME_TAC o REWRITE_RULE[SUM; PPASS2AUX_addresses_add; DISJOINT_UNION]) THEN
    ASM_SIMP_TAC[size_of_sh_with_ctxt_eq] THEN
    ih_tac `word_add addr' (word_mul bytes_in_word (word (size_of_shape a0))):A word` THEN
    ih_tac `addr':A word` THEN REFL_TAC]);;

let PPASS2AUX_good_dimindex_bytes = prove
 (`good_dimindex(:A) ==>
   val(bytes_in_word:A word) = dimindex(:A) DIV 8 /\
   ~(dimindex(:A) DIV 8 = 0) /\
   dimindex(:A) DIV 8 < 2 EXP dimindex(:A) /\
   (!w:A word. byte_aligned w <=> val w MOD (dimindex(:A) DIV 8) = 0)`,
  REWRITE_TAC[good_dimindex_def; bytes_in_word_def; byte_aligned_def;
              aligned_w2n; VAL_WORD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV LOG2_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;


(* HOL4: proved later (before evaluate_decls_init_globals_lemma); here it is *)
(* also used for mem_stores_mem_load_back                                   *)

let DISJOINT_addresses_lemma = prove
 (`word_add (addr1:A word) (word_mul bytes_in_word (word offs)) = addr2 /\
   good_dimindex(:A) /\
   val(bytes_in_word:A word) * (offs + offs') < dimword(:A)
   ==> DISJOINT (addresses addr1 offs) (addresses addr2 offs')`,
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS2AUX_good_dimindex_bytes) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_addresses] THEN
  X_GEN_TAC `x:A word` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "word_add _ _ = word_add _ _"
    (MP_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; WORD_EQ_ADD_LCANCEL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  ASM_REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL; GSYM WORD_ADD; GSYM VAL_EQ;
                  VAL_WORD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(bytes_in_word:A word) = dimindex(:A) DIV 8`]) THEN
  SUBGOAL_THEN `i * dimindex(:A) DIV 8 < offs * dimindex(:A) DIV 8 /\
                j * dimindex(:A) DIV 8 < offs' * dimindex(:A) DIV 8`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[LT_MULT_RCANCEL]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LEFT_ADD_DISTRIB]) THEN
  SUBGOAL_THEN `i * dimindex(:A) DIV 8 < 2 EXP dimindex(:A) /\
                dimindex(:A) DIV 8 * offs + j * dimindex(:A) DIV 8 < 2 EXP dimindex(:A)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

(* HOL4 Induct on a value with a statement for v and one for v list: the   *)
(* induction of pan_v with the predicates of the field lists true           *)

let PPASS2AUX_V_INDUCT_TAC : tactic = fun (asl,w as g) ->
  let c1,c2 = dest_conj w in
  let v,b1 = dest_forall c1 and vs,b2 = dest_forall c2 in
  let vty = type_of v in
  let pty = mk_type("prod",[`:mlstring`; vty]) in
  let th = ISPECL [mk_abs(v,b1); mk_abs(mk_var("x",mk_type("list",[pty])),`T`);
                   mk_abs(mk_var("x",pty),`T`); mk_abs(vs,b2)] pan_v_INDUCT in
  MATCH_MP_TAC (REWRITE_RULE[] (BETA_RULE th)) g;;

let mem_stores_mem_load_back = prove
 (`(!vl (addr:A word) addrs (mem:A word->(A)word_lab) m sctxt.
     mem_stores addr (flatten vl) addrs mem = SOME m /\
     LENGTH (flatten vl) * val(bytes_in_word:A word) < dimword(:A) /\
     is_wf_shape sctxt (shape_of vl) /\ sctxt = [] /\ good_dimindex(:A)
     ==> pan_mem_load (shape_of vl) addr addrs m sctxt = SOME vl) /\
   (!vls (addr:A word) addrs (mem:A word->(A)word_lab) m sctxt.
     mem_stores addr (FLAT (MAP (\a. flatten a) vls)) addrs mem = SOME m /\
     LENGTH (FLAT (MAP (\a. flatten a) vls)) * val(bytes_in_word:A word) <
       dimword(:A) /\
     ALL (is_wf_shape sctxt) (MAP shape_of vls) /\ sctxt = [] /\ good_dimindex(:A)
     ==> mem_loads (MAP shape_of vls) addr addrs m sctxt = SOME vls)`,
  let mls_cons = el 2 (CONJUNCTS pan_mem_load_def) in
  PPASS2AUX_V_INDUCT_TAC THEN REPEAT CONJ_TAC THENL
   [(* Val *)
    GEN_TAC THEN QCASES_ON "a" THEN
    RW(flatten_def::shape_of_def::mem_stores_def::pan_mem_store_def::
       pan_mem_load_def::all_case_eqs()) THEN RW[APPLY_UPDATE_THM];
    (* RStruct *)
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[flatten_def; shape_of_def; is_wf_shape_def; ETA_AX]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`addr:A word`; `addrs:A word->bool`;
      `mem:A word->(A)word_lab`; `m:A word->(A)word_lab`;
      `[]:(mlstring#struct_info)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[pan_mem_load_def] THEN SIMP[shape_of_def];
    (* NStruct *)
    SIMP[shape_of_def; is_wf_shape_def; ALOOKUP_DEF];
    (* [] *)
    SIMP[pan_mem_load_def];
    (* CONS *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; FLAT; ALL; LENGTH_APPEND; ETA_AX;
                                mem_stores_append]) THEN
    FS(all_case_eqs()) THEN REWRITE_TAC[MAP; mls_cons] THEN
    SUBGOAL_THEN `LENGTH (flatten (a0:(A)pan_v)) = size_of_shape (shape_of a0) /\
                  size_of_sh_with_ctxt [] (shape_of a0) = size_of_shape (shape_of a0)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[length_flatten_eq_size_of_shape;
                   size_of_sh_with_ctxt_eq]; ALL_TAC] THEN
    SUBGOAL_THEN `pan_mem_load (shape_of a0) addr addrs m [] = SOME (a0:(A)pan_v)`
      SUBST1_TAC THENL
     [MP_TAC(ISPECL [`shape_of (a0:(A)pan_v)`;
        `word_add addr (word_mul bytes_in_word
                          (word (size_of_shape (shape_of (a0:(A)pan_v))))):A word`;
        `FLAT (MAP flatten (a1:((A)pan_v)list))`; `addrs:A word->bool`;
        `a:A word->(A)word_lab`; `m:A word->(A)word_lab`;
        `[]:(mlstring#struct_info)list`; `addr:A word`]
        (CONJUNCT1 mem_stores_load_disjoint)) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MATCH_MP_TAC DISJOINT_addresses_lemma THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC `mem:A word->(A)word_lab` THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[option_CASE] THEN
    SUBGOAL_THEN
     `mem_loads (MAP shape_of a1)
        (word_add addr (word_mul bytes_in_word
                          (word (size_of_shape (shape_of (a0:(A)pan_v))))))
        addrs m [] = SOME (a1:((A)pan_v)list)`
      (fun th -> REWRITE_TAC[th; option_CASE]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `a:A word->(A)word_lab` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let LESS_MULT_MONO' = prove
 (`0 < a ==> (a * m < a * n <=> m < n)`,
  SIMP_TAC[LT_MULT_LCANCEL; ARITH_RULE `0 < a <=> ~(a = 0)`]);;

let byte_aligned_mul_bytes_in_word = prove
 (`good_dimindex(:A) /\ byte_aligned(a:A word)
   ==> ?b. a = word_mul b bytes_in_word /\
           val b * val(bytes_in_word:A word) < dimword(:A)`,
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS2AUX_good_dimindex_bytes) THEN
  EXISTS_TAC `word (val (a:A word) DIV (dimindex(:A) DIV 8)):A word` THEN
  SUBGOAL_THEN
   `val (a:A word) DIV (dimindex(:A) DIV 8) * (dimindex(:A) DIV 8) = val a`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (a:A word)`; `dimindex(:A) DIV 8`] DIVISION) THEN
    ASM_MESON_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val (a:A word) DIV (dimindex(:A) DIV 8) < 2 EXP dimindex(:A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `a:A word` VAL_BOUND) THEN
    MP_TAC(SPECL [`val (a:A word)`; `dimindex(:A) DIV 8`] DIV_LE) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VAL_WORD; MOD_LT; dimword_def; VAL_BOUND] THEN
  REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL] THEN
  ASM_REWRITE_TAC[WORD_VAL]);;

let w2n_add_alt = prove
 (`!a b. val(a:A word) + val(b:A word) < dimword(:A)
         ==> val a + val b = val(word_add a b)`,
  SIMP_TAC[VAL_WORD_ADD; dimword_def; MOD_LT]);;

let PPASS2AUX_add_lt = prove
 (`!x k n. ~(k = 0) /\ x MOD k = 0 /\ n MOD k = 0 /\ x < n /\ ~(x = n - k)
           ==> x + k < n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOD_EQ_0] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `q < q':num` MP_TAC THENL
   [ASM_MESON_TAC[LT_MULT_RCANCEL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o REWRITE_RULE[LT_EXISTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_ADD_DISTRIB; MULT_CLAUSES]) THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC);;

let good_dimindex_w2n_add = prove
 (`good_dimindex(:A) /\ byte_aligned(a:A word) /\
   ~(a = word_mul (word_neg (word 1)) bytes_in_word)
   ==> val a + val(bytes_in_word:A word) = val(word_add a bytes_in_word)`,
  STRIP_TAC THEN MATCH_MP_TAC w2n_add_alt THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS2AUX_good_dimindex_bytes) THEN
  ASM_REWRITE_TAC[dimword_def] THEN MATCH_MP_TAC PPASS2AUX_add_lt THEN
  ASM_REWRITE_TAC[VAL_BOUND] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    UNDISCH_TAC `~(a = word_mul (word_neg (word 1)) (bytes_in_word:A word))` THEN
    REWRITE_TAC[GSYM WORD_NEG_MUL; GSYM VAL_EQ; VAL_WORD_NEG_CASES] THEN
    ASM_REWRITE_TAC[]]);;

(* the addresses of a successful mem_stores are memory addresses *)

let PPASS2AUX_mem_stores_SUBSET = prove
 (`!addr ws addrs (mem:A word->(A)word_lab) m.
     mem_stores addr ws addrs mem = SOME m
     ==> addresses addr (LENGTH ws) SUBSET addrs`,
  QINDUCT_ON "ws" THEN
  RW(mem_stores_def::pan_mem_store_def::addresses_def::EMPTY_SUBSET::
     INSERT_SUBSET::all_case_eqs()) THEN
  ASM_MESON_TAC[]);;

(* HOL4's proof goes by induction on ws; here: addr' - addr is a multiple   *)
(* q of the word size, and q < LENGTH ws would put addr' among the stored   *)
(* addresses                                                                 *)

let mem_stores_bounded_length = prove
 (`!addr ws addrs (mem:A word->(A)word_lab) m addr'.
     mem_stores addr ws addrs mem = SOME m /\
     ~(addr' IN addrs) /\ byte_aligned addr /\ byte_aligned (addr':A word) /\
     good_dimindex(:A)
     ==> val(bytes_in_word:A word) * LENGTH ws <= val(word_sub addr' addr)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS2AUX_good_dimindex_bytes) THEN
  SUBGOAL_THEN `byte_aligned (word_sub addr' addr:A word)` MP_TAC THENL
   [ASM_MESON_TAC[aligned_add_sub_cor; byte_aligned_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOD_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `q < LENGTH (ws:((A)word_lab)list)` THENL
   [SUBGOAL_THEN `(addr':A word) IN addrs` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
                MATCH_MP PPASS2AUX_mem_stores_SUBSET) THEN
    REWRITE_TAC[IN_addresses] THEN EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    MATCH_MP_TAC(ARITH_RULE `k * l <= k * q ==> k * l <= q * k`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL]]);;

(* a successful store below the top address fits in the address space     *)
(* (HOL4 repeats this argument: mem_stores_bounded_length, w2n_lt)        *)

let PPASS2AUX_store_bound = prove
 (`!top addr ws addrs (mem:A word->(A)word_lab) m.
   mem_stores (word_sub top addr) ws addrs mem = SOME m /\
   ~(top IN addrs) /\ byte_aligned top /\ byte_aligned addr /\ good_dimindex(:A)
   ==> LENGTH ws * val(bytes_in_word:A word) < dimword(:A)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_sub top addr:A word`; `ws:((A)word_lab)list`;
                 `addrs:A word->bool`; `mem:A word->(A)word_lab`;
                 `m:A word->(A)word_lab`; `top:A word`] mem_stores_bounded_length) THEN
  ASM_REWRITE_TAC[WORD_RULE `word_sub a (word_sub a b) = b:A word`] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[aligned_add_sub_cor; byte_aligned_def]; ALL_TAC] THEN
  MP_TAC(ISPEC `addr:A word` VAL_BOUND) THEN REWRITE_TAC[dimword_def] THEN
  ARITH_TAC);;

(* the facts state_rel keeps about a global (HOL4: gvs[state_rel_def] >>   *)
(* res_tac), and the preservation of state_rel by an assignment to a       *)
(* global (the Assign proof of HOL4, which its Call proof repeats)         *)

let PPASS2AUX_state_rel_global = prove
 (`pan_globalsProof_state_rel b ctxt (s:(A,FFI)pan_state) t /\
   FLOOKUP (pan_state_globals s) v = SOME value
   ==> ?addr. FLOOKUP (pan_globals_context_globals ctxt) v =
                SOME (shape_of value,addr) /\
              is_wf_shape ([]:(mlstring#struct_info)list) (shape_of value) /\
              pan_mem_load (shape_of value) (word_sub (pan_state_top_addr t) addr)
                (pan_state_memaddrs t) (pan_state_memory t) [] = SOME value /\
              DISJOINT (pan_state_memaddrs s)
                (addresses (word_sub (pan_state_top_addr t) addr)
                   (size_of_shape (shape_of value))) /\
              byte_aligned addr`,
  REWRITE_TAC[pan_globalsProof_state_rel_def] THEN MESON_TAC[]);;

let PPASS2AUX_state_rel_store_global = prove
 (`!b ctxt (s:(A,FFI)pan_state) t v w value addr m.
   pan_globalsProof_state_rel b ctxt s t /\
   FLOOKUP (pan_state_globals s) v = SOME w /\
   shape_of value = shape_of w /\
   FLOOKUP (pan_globals_context_globals ctxt) v = SOME (shape_of w,addr) /\
   mem_stores (word_sub (pan_state_top_addr t) addr) (flatten value)
     (pan_state_memaddrs t) (pan_state_memory t) = SOME m
   ==> pan_globalsProof_state_rel b ctxt
         (pan_state_globals_fupd (combin_K (pan_state_globals s |+ (v,value))) s)
         (pan_state_memory_fupd (combin_K m) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
     CONJ (ASSUME `pan_globalsProof_state_rel b ctxt (s:(A,FFI)pan_state) t`)) THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
   DISCH_THEN(X_CHOOSE_THEN `addr0:A word` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
   QPAT_X_ASSUM "pan_globalsProof_state_rel _ _ _ _"
     (STRIP_ASSUME_TAC o REWRITE_RULE[pan_globalsProof_state_rel_def]) THEN
   SUBGOAL_THEN `LENGTH (flatten (value:(A)pan_v)) * val(bytes_in_word:A word) <
                 dimword(:A)` ASSUME_TAC THENL
    [MATCH_MP_TAC PPASS2AUX_store_bound THEN
     MAP_EVERY EXISTS_TAC [`pan_state_top_addr (t:(A,FFI)pan_state)`; `addr0:A word`;
       `pan_state_memaddrs (t:(A,FFI)pan_state)`;
       `pan_state_memory (t:(A,FFI)pan_state)`; `m:A word->(A)word_lab`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `pan_mem_load (shape_of value)
                   (word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr0)
                   (pan_state_memaddrs t) m [] = SOME (value:(A)pan_v)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC (CONJUNCT1 mem_stores_mem_load_back) THEN
     EXISTS_TAC `pan_state_memory (t:(A,FFI)pan_state)` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (flatten (value:(A)pan_v)) = size_of_shape (shape_of (w:(A)pan_v))`
     ASSUME_TAC THENL
    [ASM_MESON_TAC[length_flatten_eq_size_of_shape]; ALL_TAC] THEN
   REWRITE_TAC[pan_globalsProof_state_rel_def] THEN
   ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
   REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
      [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
       REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
       EXISTS_TAC `addr0:A word` THEN ASM_REWRITE_TAC[];
       DISCH_TAC THEN
       FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
         `FLOOKUP (pan_state_globals (s:(A,FFI)pan_state)) v' = SOME (value':(A)pan_v)`))) THEN
       DISCH_THEN(X_CHOOSE_THEN `addr1:A word` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `addr1:A word` THEN ASM_REWRITE_TAC[] THEN
       FIRST_ASSUM(SUBST1_TAC o SYM) THEN
       MATCH_MP_TAC (CONJUNCT1 mem_stores_load_disjoint) THEN
       MAP_EVERY EXISTS_TAC [`word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr0`;
                             `flatten (value:(A)pan_v)`] THEN
       ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `disjoint_globals (pan_state_top_addr (t:(A,FFI)pan_state))
                      (pan_globals_context_globals ctxt) (pan_state_globals (s:(A,FFI)pan_state))` THEN
       REWRITE_TAC[disjoint_globals_def] THEN
       DISCH_THEN(MP_TAC o SPECL [`v':mlstring`; `v:mlstring`; `shape_of (value':(A)pan_v)`;
                                  `addr1:A word`; `shape_of (w:(A)pan_v)`; `addr0:A word`]) THEN
       ASM_REWRITE_TAC[IS_SOME_DEF] THEN MESON_TAC[]];
    X_GEN_TAC `a:A word` THEN DISCH_TAC THEN
     SUBGOAL_THEN `~((a:A word) IN addresses (word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr0)
                       (LENGTH (flatten (value:(A)pan_v))))` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `DISJOINT (pan_state_memaddrs (s:(A,FFI)pan_state))
         (addresses (word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr0)
                    (size_of_shape (shape_of (w:(A)pan_v))))` THEN
       UNDISCH_TAC `(a:A word) IN pan_state_memaddrs (s:(A,FFI)pan_state)` THEN SET_TAC[];
       ALL_TAC] THEN
     IMP_RES_TAC mem_stores_lookup THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `!x. IS_SOME (FLOOKUP (pan_state_globals (s:(A,FFI)pan_state) |+ (v,value:(A)pan_v)) x) <=>
                      IS_SOME (FLOOKUP (pan_state_globals s) x)` ASSUME_TAC THENL
      [GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THEN
       ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
       ASM_REWRITE_TAC[IS_SOME_DEF];
       ALL_TAC] THEN
     UNDISCH_TAC `disjoint_globals (pan_state_top_addr (t:(A,FFI)pan_state))
                    (pan_globals_context_globals ctxt) (pan_state_globals (s:(A,FFI)pan_state))` THEN
     ASM_REWRITE_TAC[disjoint_globals_def]]);;

let PPASS2AUX_cc_Assign = prove
 (PPASS2AUX_cc_case "panLang_Assign",
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::kvar_defs::all_case_eqs()) THEN
  DRULE_ALL pan_globalsProof_compile_exp_correct THEN STRIP_TAC THEN SIMP[] THENL
   [GVS[pan_globalsProof_state_rel_def; good_res_def];
    QCASES_ON "FLOOKUP (pan_state_globals s) v" THEN FS[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
      CONJ (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[good_res_def] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`shape_of (a':(A)pan_v)`;
                   `word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr`;
                   `pan_state_memaddrs (t:(A,FFI)pan_state)`;
                   `pan_state_memory (t:(A,FFI)pan_state)`;
                   `[]:(mlstring#struct_info)list`; `a':(A)pan_v`; `a:(A)pan_v`]
                  (CONJUNCT1 mem_load_mem_store)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:A word->(A)word_lab`) THEN
    SIMP[pan_evaluate_def; pan_eval_def; OPT_MMAP_def; OPTION_BIND_DEF;
         OPTION_MAP_DEF; word_op_def] THEN
    MATCH_MP_TAC PPASS2AUX_state_rel_store_global THEN
    MAP_EVERY EXISTS_TAC [`a':(A)pan_v`; `addr:A word`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4: proved after the While case; used here for Primitive *)

let OPT_MMAP_eval_correct = prove
 (`pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t /\
   OPT_MMAP (pan_eval s) argexps = SOME args
   ==> OPT_MMAP (pan_eval t) (MAP (pan_globals_compile_exp ctxt) argexps) =
       SOME args`,
  RW[OPT_MMAP_MAP_o] THEN IRULE EQ_TRANS THEN
  FIRST_ASSUM(IRULE_AT (Pos last)) THEN IRULE OPT_MMAP_CONG THEN RW[] THEN
  IMP_RES_TAC opt_mmap_mem_func THEN
  IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN GVS[]);;

let PPASS2AUX_cc_Primitive = prove
 (PPASS2AUX_cc_case "Primitive",
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::kvar_defs::all_case_eqs()) THEN
  DRULE_ALL OPT_MMAP_eval_correct THEN STRIP_TAC THEN
  SUBGOAL_THEN `pan_state_locals (s:(A,FFI)pan_state) = pan_state_locals (t:(A,FFI)pan_state)`
    ASSUME_TAC THENL [FS[pan_globalsProof_state_rel_def]; ALL_TAC] THEN
  GVS[] THEN GVS[pan_globalsProof_state_rel_def; good_res_def]);;

let state_rel_res_var = prove
 (`pan_globalsProof_state_rel l ctxt (s:(A,FFI)pan_state) t /\
   pan_globalsProof_state_rel T ctxt (s':(A,FFI)pan_state) t'
   ==> pan_globalsProof_state_rel l ctxt
         (pan_state_locals_fupd
            (combin_K (pan_res_var (pan_state_locals s) (v,FLOOKUP (pan_state_locals s') v'))) s)
         (pan_state_locals_fupd
            (combin_K (pan_res_var (pan_state_locals t) (v,FLOOKUP (pan_state_locals t') v'))) t)`,
  RW[pan_globalsProof_state_rel_def] THEN GVS[]);;

let PPASS2AUX_cc_Dec = prove
 (PPASS2AUX_cc_case "Dec",
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::all_case_eqs()) THEN
  DRULE_ALL pan_globalsProof_compile_exp_correct THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ctxt:(A)pan_globals_context`;
    `pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state) |+ (v,a:(A)pan_v))) t`]) THEN
  ANTS_TAC THENL [FS[pan_globalsProof_state_rel_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
  SIMP[] THEN IRULE state_rel_res_var THEN ASM_REWRITE_TAC[]);;
let mem_load_disjoint = prove
 (`(!vl (addr'':A word) (mem:A word->(A)word_lab) stcs v addr' addrs.
     pan_mem_load (shape_of vl) addr' addrs mem stcs = SOME vl /\
     ~(addr'' IN addresses addr' (size_of_shape (shape_of vl))) /\
     is_wf_shape ([]:(mlstring#struct_info)list) (shape_of vl)
     ==> pan_mem_load (shape_of vl) addr' addrs ((addr'' =+ v) mem) stcs = SOME vl) /\
   (!vls (addr'':A word) (mem:A word->(A)word_lab) stcs v addr' addrs.
     mem_loads (MAP shape_of vls) addr' addrs mem stcs = SOME vls /\
     ~(addr'' IN addresses addr' (SUM (MAP (size_of_shape o shape_of) vls))) /\
     ALL (is_wf_shape ([]:(mlstring#struct_info)list)) (MAP shape_of vls)
     ==> mem_loads (MAP shape_of vls) addr' addrs ((addr'' =+ v) mem) stcs = SOME vls)`,
  let mls_cons = el 2 (CONJUNCTS pan_mem_load_def) in
  PPASS2AUX_V_INDUCT_TAC THEN REPEAT CONJ_TAC THENL
   [(* Val *)
    GEN_TAC THEN QCASES_ON "a" THEN
    RW(shape_of_def::pan_mem_load_def::size_of_shape_def::PPASS2AUX_addresses_1::
       APPLY_UPDATE_THM::IN_SING::all_case_eqs());
    (* RStruct *)
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[shape_of_def; size_of_shape_def; is_wf_shape_def;
                                MAP_MAP_o]) THEN
    REWRITE_TAC[shape_of_def] THEN ONCE_REWRITE_TAC[pan_mem_load_def] THEN
    FS(pan_mem_load_def::all_case_eqs());
    (* NStruct *)
    SIMP[shape_of_def; is_wf_shape_def; ALOOKUP_DEF];
    (* [] *)
    SIMP[pan_mem_load_def];
    (* CONS *)
       REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL; SUM; o_THM; PPASS2AUX_addresses_add;
                                IN_UNION; DE_MORGAN_THM]) THEN
    FS(mls_cons::all_case_eqs()) THEN RVEQ_TAC THEN
    REWRITE_TAC[MAP; mls_cons] THEN
    SUBGOAL_THEN `size_of_sh_with_ctxt stcs (shape_of (a0:(A)pan_v)) = size_of_shape (shape_of a0)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[size_of_sh_with_ctxt_eq]; ALL_TAC] THEN
    RES_TAC THEN ASM_REWRITE_TAC[option_CASE]]);;

let state_rel_memory_update = prove
 (`pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t /\
   addr' IN pan_state_memaddrs s
   ==> pan_globalsProof_state_rel T ctxt
         (pan_state_memory_fupd (combin_K ((addr' =+ h) (pan_state_memory s))) s)
         (pan_state_memory_fupd (combin_K ((addr' =+ h) (pan_state_memory t))) t)`,
  REWRITE_TAC[pan_globalsProof_state_rel_def; pan_state_INFO.ri_accfupds; K_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
      `FLOOKUP (pan_state_globals (s:(A,FFI)pan_state)) v = SOME (value:(A)pan_v)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `addr:A word` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `addr:A word` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (CONJUNCT1 mem_load_disjoint) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (pan_state_memaddrs (s:(A,FFI)pan_state))
      (addresses (word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr)
                 (size_of_shape (shape_of (value:(A)pan_v))))` THEN
    UNDISCH_TAC `(addr':A word) IN pan_state_memaddrs (s:(A,FFI)pan_state)` THEN
    SET_TAC[];
    GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 Store proof: an induction on the stored words, with              *)
(* state_rel_memory_update at each word                                    *)

let PPASS2AUX_state_rel_mem_stores = prove
 (`!ws addr (s:(A,FFI)pan_state) t m.
     pan_globalsProof_state_rel T ctxt s t /\
     mem_stores addr ws (pan_state_memaddrs s) (pan_state_memory s) = SOME m
     ==> ?m'. mem_stores addr ws (pan_state_memaddrs t) (pan_state_memory t) = SOME m' /\
              pan_globalsProof_state_rel T ctxt (pan_state_memory_fupd (combin_K m) s)
                                                (pan_state_memory_fupd (combin_K m') t)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [RW[mem_stores_def] THEN
    SUBGOAL_THEN `!r:(A,FFI)pan_state. pan_state_memory_fupd (combin_K (pan_state_memory r)) r = r`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM];
    X_GEN_TAC `w:(A)word_lab` THEN X_GEN_TAC `ws:((A)word_lab)list` THEN DISCH_TAC THEN
    RW(mem_stores_def::pan_mem_store_def::all_case_eqs()) THEN
    SUBGOAL_THEN `(addr:A word) IN pan_state_memaddrs (t:(A,FFI)pan_state)` ASSUME_TAC THENL
     [FS[pan_globalsProof_state_rel_def; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DRULE_ALL state_rel_memory_update THEN DISCH_THEN(ASSUME_TAC o SPEC `w:(A)word_lab`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`word_add addr (bytes_in_word:A word)`;
       `pan_state_memory_fupd (combin_K ((addr =+ w) (pan_state_memory s))) (s:(A,FFI)pan_state)`;
       `pan_state_memory_fupd (combin_K ((addr =+ w) (pan_state_memory t))) (t:(A,FFI)pan_state)`;
       `m:A word->(A)word_lab`]) THEN
    ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; pan_state_INFO.ri_fupdfupds; K_THM;
                    K_o_THM]]);;
let PPASS2AUX_cc_Store = prove
 (PPASS2AUX_cc_case "panLang_Store",
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::all_case_eqs()) THEN
  IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN
  DRULE_ALL PPASS2AUX_state_rel_mem_stores THEN STRIP_TAC THEN SIMP[good_res_def]);;

let PPASS2AUX_cc_Store32 = prove
 (PPASS2AUX_cc_case "panLang_Store32",
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::all_case_eqs()) THEN
  IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN SIMP[] THEN
  QPAT_X_ASSUM "pan_mem_store_32 _ _ _ _ _ = _"
    (ASSUME_TAC o REWRITE_RULE[pan_mem_store_32_alt]) THEN
  GVS(good_res_def::all_case_eqs()) THEN
  DRULE_ALL state_rel_memory_update THEN DISCH_THEN(IRULE_AT (Pos last)) THEN
  GVS(pan_globalsProof_state_rel_def::pan_mem_store_32_alt::SUBSET::all_case_eqs()));;

let PPASS2AUX_cc_StoreByte = prove
 (PPASS2AUX_cc_case "StoreByte",
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::pan_mem_store_byte_def::good_res_def::
      all_case_eqs()) THEN
  IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN
  DRULE_ALL state_rel_memory_update THEN DISCH_THEN(IRULE_AT (Pos last)) THEN
  GVS(pan_globalsProof_state_rel_def::SUBSET::all_case_eqs()));;

let v_neq_v' = prove
 (`~(v = strcat v (implode "'"))`,
  DISCH_THEN(MP_TAC o AP_TERM `strlen`) THEN
  REWRITE_TAC[strlen_strcat; strlen_implode; LENGTH] THEN ARITH_TAC);;

let FLOOKUP_globals_val_state_rel = prove
 (`FLOOKUP (pan_state_globals s) nm = SOME (pan_Val v) /\
   pan_globalsProof_state_rel b ctxt (s:(A,FFI)pan_state) t
   ==> ?addr_diff.
         FLOOKUP (pan_globals_context_globals ctxt) nm =
           SOME (shape_of (pan_Val v),addr_diff) /\
         pan_mem_load (shape_of (pan_Val v))
           (word_sub (pan_state_top_addr t) addr_diff)
           (pan_state_memaddrs t) (pan_state_memory t) [] = SOME (pan_Val v) /\
         DISJOINT (pan_state_memaddrs s)
           (addresses (word_sub (pan_state_top_addr t) addr_diff)
              (size_of_shape (shape_of (pan_Val v)))) /\
         byte_aligned addr_diff`,
  REWRITE_TAC[pan_globalsProof_state_rel_def] THEN MESON_TAC[]);;

(* HOL4: proved before the ExtCall case; used here for ShMemLoad *)

let state_rel_change_ffi = prove
 (`pan_globalsProof_state_rel ls' ctxt (s:(A,FFI)pan_state) t
   ==> pan_globalsProof_state_rel ls' ctxt (pan_state_ffi_fupd (combin_K x) s)
                                           (pan_state_ffi_fupd (combin_K x) t)`,
  RW[pan_globalsProof_state_rel_def] THEN GVS[]);;

(* the two local variables of the compiled ShMemLoad are restored *)

let PPASS2AUX_res_var_twice = prove
 (`~(x = y)
   ==> pan_res_var (pan_res_var (l |+ (x,a) |+ (y,b)) (y,FLOOKUP l y))
                   (x,FLOOKUP l x) = l:(mlstring,(A)pan_v)fmap`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_pan_res_var_thm; FLOOKUP_UPDATE] THEN
  DISCH_TAC THEN X_GEN_TAC `z:mlstring` THEN
  ASM_CASES_TAC `z:mlstring = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z:mlstring = y` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let PPASS2AUX_cc_ShMemLoad = prove
 (PPASS2AUX_cc_case "ShMemLoad",
  REPEAT GEN_TAC THEN QCASES_ON "vk" THEN REPEAT STRIP_TAC THENL
   [(* Local *)
    GVS(pan_evaluate_def::pan_globals_compile_def::all_case_eqs()) THEN
       DRULE_ALL pan_globalsProof_compile_exp_correct THEN STRIP_TAC THEN
       GVS(pan_globalsProof_state_rel_def::pan_sh_mem_load_def::kvar_defs::SUBSET::
           pan_empty_locals_def::good_res_def::all_case_eqs());
    (* Global *)
    QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o REWRITE_RULE[pan_evaluate_def]) THEN
       GVS(all_case_eqs()) THEN
    STRIP_TAC THEN RVEQ_TAC THEN
       DRULE_ALL pan_globalsProof_compile_exp_correct THEN STRIP_TAC THEN
    DRULE_ALL FLOOKUP_globals_val_state_rel THEN STRIP_TAC THEN
    RENAME1 "pan_eval s ad = SOME (pan_Val (Word addr))" THEN
       RENAME1 "FLOOKUP (pan_state_globals s) v = SOME (pan_Val (Word w0))" THEN
       RULE_ASSUM_TAC(REWRITE_RULE[shape_of_val; size_of_shape_def; PPASS2AUX_addresses_1]) THEN
       SUBGOAL_THEN `pan_state_locals s = pan_state_locals (t:(A,FFI)pan_state) /\
                     pan_state_sh_memaddrs s = pan_state_sh_memaddrs t /\
                     pan_state_ffi s = pan_state_ffi t` STRIP_ASSUME_TAC THENL
        [FS[pan_globalsProof_state_rel_def]; ALL_TAC] THEN
       ASM_REWRITE_TAC[pan_globals_compile_def] THEN CAKE_REWRITE_TAC[] THEN
       SIMP[pan_evaluate_def; pan_eval_def; FLOOKUP_UPDATE; v_neq_v'; shape_of_val;
            pan_lookup_kvar_def] THEN
    QPAT_X_ASSUM "pan_sh_mem_load _ _ _ _ _ = _" (MP_TAC o REWRITE_RULE[pan_sh_mem_load_def]) THEN
       REWRITE_TAC[pan_sh_mem_load_def] THEN
       ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
       QCASES_ON "call_FFI (pan_state_ffi (t:(A,FFI)pan_state)) (SharedMem MappedRead) [word (nb_op op)] (word_to_bytes (addr:A word) F)" THEN
       ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THENL
     [(ASM_CASES_TAC `nb_op op = 0` THEN ASM_REWRITE_TAC[] THENL
          [ASM_CASES_TAC `(addr:A word) IN pan_state_sh_memaddrs (t:(A,FFI)pan_state)`;
           ASM_CASES_TAC `byte_align (addr:A word) IN pan_state_sh_memaddrs (t:(A,FFI)pan_state)`] THEN
         ASM_REWRITE_TAC[PAIR_EQ] THEN
         TRY(STRIP_TAC THEN UNDISCH_TAC `~(res = SOME (pan_Error:(A)pan_result))` THEN
             ASM_REWRITE_TAC[] THEN NO_TAC)) THEN
      (QPAT_X_ASSUM "pan_mem_load One _ _ _ _ = _" (MP_TAC o ONCE_REWRITE_RULE[pan_mem_load_def]) THEN
         SIMP(all_case_eqs()) THEN STRIP_TAC THEN
         STRIP_TAC THEN RVEQ_TAC THEN
         SIMP[kvar_defs; OPTION_MAP_DEF; word_op_def; FLOOKUP_UPDATE; flatten_def; mem_stores_def;
              pan_mem_store_def; v_neq_v'; good_res_def]) THEN
      (ASM_SIMP_TAC[PPASS2AUX_res_var_twice; GSYM v_neq_v'] THEN
         SUBGOAL_THEN `!m f. pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state)))
                         (pan_state_memory_fupd (combin_K m) (pan_state_ffi_fupd (combin_K f) t)) =
                       pan_state_memory_fupd (combin_K m) (pan_state_ffi_fupd (combin_K f) t)`
           (fun th -> REWRITE_TAC[th]) THENL
          [REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM];
           ALL_TAC] THEN
         MP_TAC(ISPECL [`T`; `ctxt:(A)pan_globals_context`;
                        `pan_state_ffi_fupd (combin_K a0) (s:(A,FFI)pan_state)`;
                        `pan_state_ffi_fupd (combin_K a0) (t:(A,FFI)pan_state)`; `v:mlstring`;
                        `pan_Val (Word (w0:A word))`;
                        `pan_Val (Word (word_of_bytes F (word 0) a1:A word))`;
                        `addr_diff:A word`;
                        `(word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr_diff =+
                          Word (word_of_bytes F (word 0) a1:A word)) (pan_state_memory t)`]
                       PPASS2AUX_state_rel_store_global) THEN
         SIMP[state_rel_change_ffi; pan_state_INFO.ri_accfupds; K_THM; shape_of_val;
                      flatten_def; mem_stores_def; pan_mem_store_def]);
      (ASM_CASES_TAC `nb_op op = 0` THEN ASM_REWRITE_TAC[] THENL
          [ASM_CASES_TAC `(addr:A word) IN pan_state_sh_memaddrs (t:(A,FFI)pan_state)`;
           ASM_CASES_TAC `byte_align (addr:A word) IN pan_state_sh_memaddrs (t:(A,FFI)pan_state)`] THEN
         ASM_REWRITE_TAC[PAIR_EQ] THEN
         TRY(STRIP_TAC THEN UNDISCH_TAC `~(res = SOME (pan_Error:(A)pan_result))` THEN
             ASM_REWRITE_TAC[] THEN NO_TAC)) THEN
      (STRIP_TAC THEN RVEQ_TAC THEN
         SIMP[kvar_defs; good_res_def; pan_empty_locals_def] THEN
         FS[pan_globalsProof_state_rel_def; pan_empty_locals_def])]]);;

let PPASS2AUX_cc_ShMemStore = prove
 (PPASS2AUX_cc_case "ShMemStore",
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::pan_globals_compile_def::pan_sh_mem_store_def::nb_op_def::
      good_res_def::all_case_eqs()) THEN
  IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN
  GVS[pan_globalsProof_state_rel_def]);;

let PPASS2AUX_cc_Return = prove
 (PPASS2AUX_cc_case "panLang_Return",
  RW(pan_evaluate_def::pan_globals_compile_def::all_case_eqs()) THEN
  IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN
  GVS[pan_globalsProof_state_rel_def; pan_empty_locals_def; good_res_def]);;

let PPASS2AUX_cc_Raise = prove
 (PPASS2AUX_cc_case "panLang_Raise",
  RW(pan_evaluate_def::pan_globals_compile_def::all_case_eqs()) THEN
  IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN
  GVS[pan_globalsProof_state_rel_def; pan_empty_locals_def; good_res_def]);;

let PPASS2AUX_cc_Seq = prove
 (PPASS2AUX_cc_case "panLang_Seq",
  RW[pan_evaluate_def; pan_globals_compile_def] THEN GVS(all_case_eqs()) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`ctxt:(A)pan_globals_context`; `t:(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[good_res_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ctxt:(A)pan_globals_context`; `t1:(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t2:(A,FFI)pan_state` THEN SIMP[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`ctxt:(A)pan_globals_context`; `t:(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t1:(A,FFI)pan_state` THEN SIMP[]]);;

let PPASS2AUX_cc_If = prove
 (PPASS2AUX_cc_case "panLang_If",
  RW[pan_evaluate_def; pan_globals_compile_def] THEN
   GVS(all_case_eqs()) THEN
   IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`ctxt:(A)pan_globals_context`; `t:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
   EXISTS_TAC `t':(A,FFI)pan_state` THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN SIMP[]);;

let PPASS2AUX_evaluate_clause pat =
  find (fun th -> can (term_match [] pat) (lhs (snd (strip_forall (concl th)))))
       (CONJUNCTS pan_evaluate_def);;
let PPASS2AUX_evaluate_While =
  PPASS2AUX_evaluate_clause `pan_evaluate (While e c, s:(A,FFI)pan_state)`;;
let state_rel_dec_clock = prove
 (`pan_globalsProof_state_rel ls ctxt (s:(A,FFI)pan_state) t
   ==> pan_globalsProof_state_rel ls ctxt (pan_dec_clock s) (pan_dec_clock t)`,
  RW[pan_globalsProof_state_rel_def; pan_dec_clock_def] THEN GVS[]);;

let PPASS2AUX_cc_While = prove
 (PPASS2AUX_cc_case "While",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihNone")
     (CONJUNCTS_THEN2 (LABEL_TAC "ihCont") (LABEL_TAC "ihBody"))) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `pan_state_clock (s:(A,FFI)pan_state) = pan_state_clock (t:(A,FFI)pan_state)`
     ASSUME_TAC THENL [FS[pan_globalsProof_state_rel_def]; ALL_TAC] THEN
   REWRITE_TAC[pan_globals_compile_def] THEN ONCE_REWRITE_TAC[PPASS2AUX_evaluate_While] THEN
   QPAT_X_ASSUM "pan_evaluate (While _ _,_) = _"
     (MP_TAC o ONCE_REWRITE_RULE[PPASS2AUX_evaluate_While]) THEN
   QCASES_ON "pan_eval s e" THEN ASM_REWRITE_TAC[option_CASE] THENL
    [SIMP[]; ALL_TAC] THEN
   IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN ASM_REWRITE_TAC[option_CASE] THEN
   NAMED_CASES_ON "a" ["wl"; "vs"; "nm flds"] THEN CAKE_REWRITE_TAC[] THEN SIMP[] THEN
   QCASES_ON "wl" THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
    [ALL_TAC;
     STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `t:(A,FFI)pan_state` THEN
     ASM_REWRITE_TAC[good_res_def]] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
    [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN
     FS[pan_globalsProof_state_rel_def; pan_empty_locals_def; good_res_def];
     ALL_TAC] THEN
   NAMED_CASES_ON "pan_evaluate (c,pan_dec_clock s)" ["res1 s1"] THEN
   CAKE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `res1 = SOME (pan_Error:(A)pan_result)` THENL
    [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   REMOVE_THEN "ihBody" (MP_TAC o SPEC `a':A word`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
                              `pan_dec_clock (t:(A,FFI)pan_state)`; `s1:(A,FFI)pan_state`]) THEN
   ASM_SIMP_TAC[state_rel_dec_clock] THEN
   DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   QCASES_ON "res1" THEN CAKE_REWRITE_TAC[] THENL
    [DISCH_TAC THEN
     REMOVE_THEN "ihNone" (MP_TAC o SPECL [`a':A word`; `s1:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
                                `t1:(A,FFI)pan_state`; `s':(A,FFI)pan_state`]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[good_res_def]) THEN
     ASM_REWRITE_TAC[pan_globals_compile_def];
     QCASES_ON "a''" THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
      [ASM_MESON_TAC[];
       STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `t1:(A,FFI)pan_state` THEN ASM_REWRITE_TAC[];
       STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `t1:(A,FFI)pan_state` THEN FS[good_res_def];
       DISCH_TAC THEN
       REMOVE_THEN "ihCont" (MP_TAC o SPECL [`a':A word`; `s1:(A,FFI)pan_state`]) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
                                  `t1:(A,FFI)pan_state`; `s':(A,FFI)pan_state`]) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[good_res_def]) THEN
       ASM_REWRITE_TAC[pan_globals_compile_def];
       STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `t1:(A,FFI)pan_state` THEN ASM_REWRITE_TAC[];
       STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `t1:(A,FFI)pan_state` THEN ASM_REWRITE_TAC[];
       STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `t1:(A,FFI)pan_state` THEN ASM_REWRITE_TAC[]]]);;

let state_rel_lookup_code = prove
 (`pan_globalsProof_state_rel ls ctxt (s:(A,FFI)pan_state) t /\
   pan_lookup_code (pan_state_code s) fname args = SOME (prog,newlocals)
   ==> pan_lookup_code (pan_state_code t) fname args =
       SOME (pan_globals_compile ctxt prog,newlocals)`,
  RW[] THEN GVS(pan_globalsProof_state_rel_def::pan_lookup_code_def::all_case_eqs()) THEN
  RES_TAC THEN FS[]);;

(* Simplifier doesn't trigger if flag is left symbolic *)

let state_rel_empty_locals = prove
 (`(pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t
    ==> pan_globalsProof_state_rel ls' ctxt (pan_empty_locals s) (pan_empty_locals t)) /\
   (pan_globalsProof_state_rel F ctxt s t
    ==> pan_globalsProof_state_rel ls' ctxt (pan_empty_locals s) (pan_empty_locals t))`,
  RW[] THEN GVS[pan_globalsProof_state_rel_def; pan_empty_locals_def]);;

let state_rel_change_locals = prove
 (`(pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t
    ==> pan_globalsProof_state_rel ls' ctxt (pan_state_locals_fupd (combin_K x) s)
                                            (pan_state_locals_fupd (combin_K x) t)) /\
   (pan_globalsProof_state_rel F ctxt s t
    ==> pan_globalsProof_state_rel ls' ctxt (pan_state_locals_fupd (combin_K x) s)
                                            (pan_state_locals_fupd (combin_K x) t))`,
  RW[] THEN GVS[pan_globalsProof_state_rel_def; pan_empty_locals_def]);;

let state_rel_set_var = prove
 (`pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t
   ==> pan_globalsProof_state_rel ls' ctxt (pan_set_var rt retv s) (pan_set_var rt retv t)`,
  RW[] THEN GVS[pan_globalsProof_state_rel_def; pan_empty_locals_def; pan_set_var_def]);;

let eval_shape_val_NONE = prove
 (`(!sh. pan_eval (t:(A,FFI)pan_state) (shape_val sh) = NONE <=> F) /\
   (!shs. OPT_MMAP (pan_eval (t:(A,FFI)pan_state)) (shape_vals shs) = NONE <=> F)`,
  MATCH_MP_TAC (cake_ind "shape_val") THEN
  RW[shape_val_def; pan_eval_def; OPT_MMAP_def; OPTION_BIND_DEF] THEN
  GVS(all_case_eqs()));;
let _ = cake_add_simps [eval_shape_val_NONE];;

let eval_shape_val_thm = prove
 (`(!sh v. pan_eval (t:(A,FFI)pan_state) (shape_val sh) = SOME v /\
           is_wf_shape ([]:(mlstring#struct_info)list) sh ==> sh = shape_of v) /\
   (!shs vs. OPT_MMAP (pan_eval (t:(A,FFI)pan_state)) (shape_vals shs) = SOME vs /\
             ALL (is_wf_shape ([]:(mlstring#struct_info)list)) shs
             ==> shs = MAP shape_of vs)`,
  MATCH_MP_TAC (cake_ind "shape_val") THEN
  RW[shape_val_def; pan_eval_def; shape_of_def; is_wf_shape_def; OPT_MMAP_def;
     ALOOKUP_DEF] THEN
  GVS(OPTION_BIND_DEF::shape_of_def::all_case_eqs()) THEN RES_TAC THEN FS[]);;

let fresh_name_correct = prove
 (`!name names. MEM (fresh_name name names) names ==> F`,
  MATCH_MP_TAC fresh_name_ind THEN RW[] THEN
  POP_ASSUM(MP_TAC o ONCE_REWRITE_RULE[fresh_name_def]) THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let fresh_name_correct' = prove
 (`!name names names'.
     MEM (fresh_name name names) names'
     ==> set_of_list names' SUBSET set_of_list names ==> F`,
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN MESON_TAC[fresh_name_correct]);;

let res_var_FEMPTY = prove
 (`pan_res_var FEMPTY (n,NONE) = FEMPTY:(mlstring,(A)pan_v)fmap`,
  RW[fmap_eq_flookup; FLOOKUP_pan_res_var_thm] THEN RW[FLOOKUP_EMPTY]);;
let _ = cake_add_simps [res_var_FEMPTY];;

let PPASS2AUX_evaluate_DecCall =
  PPASS2AUX_evaluate_clause
    `pan_evaluate (DecCall rt shape fname argexps prog1, s:(A,FFI)pan_state)`;;

let PPASS2AUX_evaluate_Call =
  PPASS2AUX_evaluate_clause
    `pan_evaluate (panLang_Call caltyp fname argexps, s:(A,FFI)pan_state)`;;

let PPASS2AUX_evaluate_Dec =
  PPASS2AUX_evaluate_clause `pan_evaluate (Dec v sh e prog, s:(A,FFI)pan_state)`;;

let PPASS2AUX_evaluate_Seq =
  PPASS2AUX_evaluate_clause `pan_evaluate (panLang_Seq c1 c2, s:(A,FFI)pan_state)`;;

let PPASS2AUX_evaluate_If =
  PPASS2AUX_evaluate_clause `pan_evaluate (panLang_If e c1 c2, s:(A,FFI)pan_state)`;;

let PPASS2AUX_evaluate_Assign =
  PPASS2AUX_evaluate_clause `pan_evaluate (panLang_Assign vk v src, s:(A,FFI)pan_state)`;;

(* the program constructor of a case of an evaluate induction, and the     *)
(* assembly of a theorem from its cases (special proofs by constructor     *)
(* name, the others by a uniform tactic)                                   *)

let PPASS2AUX_prog_case_name =
  let cons = map (fun (_,pat) -> fst(dest_const(fst(strip_comb pat))))
                 (case_info_of_tyname "panLang_prog").ci_pats in
  fun c ->
    let body = snd(strip_forall c) in
    let part = if is_imp body && is_forall (rand body) then rand body else body in
    let is_con t = is_const t && mem (fst(dest_const t)) cons in
    let tm = find_term (fun t ->
        is_comb t && is_const(rator t) && fst(dest_const(rator t)) = "pan_evaluate" &&
        is_pair(rand t) && is_con(fst(strip_comb(fst(dest_pair(rand t)))))) part in
    fst(dest_const(fst(strip_comb(fst(dest_pair(rand tm))))));;

let PPASS2AUX_assemble ind (special:(string*thm) list) (tac:tactic) =
  let prove_case c =
    try let th = assoc (PPASS2AUX_prog_case_name c) special in
        EQ_MP (ALPHA (concl th) c) th
    with Failure _ -> prove(c,tac) in
  MATCH_MP ind (end_itlist CONJ (map prove_case (conjuncts (lhand (concl ind)))));;

(* helpers of the fresh-variable lemmas: case splits on varkind variables, *)
(* the not-free assumptions split into parts                              *)

let PPASS2AUX_varkind_cases_tac : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> type_of v = `:varkind`) (freesl (w :: map (concl o snd) asl)) in
  MAP_EVERY (fun v -> DISJ_CASES_THEN SUBST_ALL_TAC (ISPEC v (cases "varkind"))) vs g;;

let PPASS2AUX_fresh_pre =
  REPEAT STRIP_TAC THEN PPASS2AUX_varkind_cases_tac THEN
  RULE_ASSUM_TAC(REWRITE_RULE[free_var_ids_def; MEM_APPEND; MEM; DE_MORGAN_THM; MEM_FILTER;
                              distinctness "varkind"]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

let PPASS2AUX_dec_clock_locals = prove
 (`pan_dec_clock (pan_state_locals_fupd (combin_K l) (s:(A,FFI)pan_state)) =
   pan_state_locals_fupd (combin_K l) (pan_dec_clock s) /\
   pan_state_locals (pan_dec_clock s) = pan_state_locals s /\
   pan_state_clock (pan_dec_clock s) = pan_state_clock s - 1`,
  REWRITE_TAC[pan_dec_clock_def] THEN SIMP[pan_state_component_equality]);;

let PPASS2AUX_call_fvi_tac =
  NAMED_CASES_ON "caltyp" ["";"ch"] THENL
   [REWRITE_TAC[free_var_ids_def; distinctness "option"];
    PAIR_CASES_ON `ch:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
    NAMED_CASES_ON "ch0" ["";"rt"] THEN NAMED_CASES_ON "ch1" ["";"h"] THEN
    TRY(PAIR_CASES_ON `rt:varkind#mlstring`) THEN
    TRY(PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog`) THEN
    PPASS2AUX_varkind_cases_tac THEN
    REWRITE_TAC[free_var_ids_def; MEM_APPEND; MEM; DE_MORGAN_THM; distinctness "option";
                injectivity "option"; PAIR_EQ; distinctness "varkind"] THEN
    MESON_TAC[]];;

let OPT_MMAP_eval_fresh_var = prove
 (`!s es n w.
     ~MEM n (FLAT (MAP var_exp es))
     ==> OPT_MMAP (pan_eval (pan_state_locals_fupd (combin_K (pan_state_locals s |+ (n,w)))
                              (s:(A,FFI)pan_state))) es =
         OPT_MMAP (pan_eval s) es`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[OPT_MMAP_def; MAP; FLAT; MEM_APPEND; DE_MORGAN_THM; eval_fresh_var]);;

let OPT_MMAP_eval_two_fresh_vars = prove
 (`!s es n1 w1 n2 w2.
     ~MEM n1 (FLAT (MAP var_exp es)) /\ ~MEM n2 (FLAT (MAP var_exp es))
     ==> OPT_MMAP (pan_eval (pan_state_locals_fupd
                     (combin_K (pan_state_locals s |+ (n1,w1) |+ (n2,w2))) (s:(A,FFI)pan_state))) es =
         OPT_MMAP (pan_eval s) es`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`pan_state_locals_fupd (combin_K (pan_state_locals s |+ (n1,w1))) (s:(A,FFI)pan_state)`;
                 `es:((A)panLang_exp)list`; `n2:mlstring`; `w2:(A)pan_v`]
                OPT_MMAP_eval_fresh_var) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[OPT_MMAP_eval_fresh_var]);;

let PPASS2AUX_evaluate_fresh_local_ind =
  let goal = `\(p:(A)panLang_prog,s:(A,FFI)pan_state).
      !res s'. ~MEM (z:mlstring) (free_var_ids p) /\ pan_evaluate (p,s) = (res,s')
               ==> ?locals.
                     pan_evaluate (p, pan_state_locals_fupd
                                        (combin_K (pan_state_locals s |+ (z,v:(A)pan_v))) s) =
                     (res, pan_state_locals_fupd (combin_K locals) s') /\
                     (good_res res /\ ~(res = SOME pan_Error)
                      ==> locals = pan_state_locals s' |+ (z,v))` in
  CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (ISPEC goal pan_evaluate_ind);;

let PPASS2AUX_efl_case name =
  let cases = conjuncts (lhand (concl PPASS2AUX_evaluate_fresh_local_ind)) in
  let prog_of c =
    let body = snd (strip_forall c) in
    let ab = if is_forall (rand body) then snd (strip_forall (rand body)) else body in
    let ev = lhand (rand (lhand ab)) in
    fst (dest_pair (rand ev)) in
  find (fun c -> let h = fst (strip_comb (prog_of c)) in
                 is_const h && fst (dest_const h) = name) cases;;

let PPASS2AUX_locals_wit_tac : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let c = find (fun c -> is_eq c && free_in v (rhs c) && not (free_in v (lhs c)))
               (conjuncts bod) in
  let st = lhs c in
  EXISTS_TAC (mk_icomb(`pan_state_locals:(A,FFI)pan_state->(mlstring,(A)pan_v)fmap`, st)) g;;



let PPASS2AUX_efl_simple_tac =
  PPASS2AUX_fresh_pre THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  ASM_SIMP_TAC[eval_fresh_var; OPT_MMAP_eval_fresh_var; pan_state_INFO.ri_accfupds; K_THM;
               kvar_defs; pan_sh_mem_load_def; pan_sh_mem_store_def; pan_empty_locals_def;
               pan_dec_clock_def; FLOOKUP_UPDATE] THEN
  REPEAT TOP_CASE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM] THEN
  TRY PPASS2AUX_locals_wit_tac THEN
  GVS[pan_state_component_equality; pan_state_INFO.ri_accfupds; good_res_def; FLOOKUP_UPDATE;
      FUPDATE_COMMUTES];;

let PPASS2AUX_efl_fin_tac =
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM] THEN
  TRY PPASS2AUX_locals_wit_tac THEN
  GVS[pan_state_component_equality; pan_state_INFO.ri_accfupds; good_res_def; FLOOKUP_UPDATE;
      FUPDATE_COMMUTES; kvar_defs];;

let PPASS2AUX_efl_Seq = prove
 (PPASS2AUX_efl_case "panLang_Seq",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN
  PPASS2AUX_fresh_pre THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  NAMED_CASES_ON "pan_evaluate (c1,s)" ["res1 s1"] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`res1:((A)pan_result)option`; `s1:(A,FFI)pan_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:(mlstring,(A)pan_v)fmap` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1:((A)pan_result)option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[good_res_def; distinctness "option"] THEN DISCH_THEN SUBST1_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,FFI)pan_state`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `l1:(mlstring,(A)pan_v)fmap` THEN ASM_MESON_TAC[]]);;

let PPASS2AUX_efl_If = prove
 (PPASS2AUX_efl_case "panLang_If",
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  PPASS2AUX_fresh_pre THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN ASM_SIMP_TAC[eval_fresh_var] THEN
  QCASES_ON "pan_eval s e" THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "a" ["wl"; "vs"; "nm flds"] THEN CAKE_REWRITE_TAC[] THENL
   [ALL_TAC; PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac] THEN
  NAMED_CASES_ON "wl" ["w"] THEN CAKE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `w:A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let PPASS2AUX_efl_Dec = prove
 (PPASS2AUX_efl_case "Dec",
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[free_var_ids_def; MEM_APPEND; DE_MORGAN_THM; MEM_FILTER]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  ASM_SIMP_TAC[eval_fresh_var; pan_state_INFO.ri_accfupds; K_THM] THEN
  QCASES_ON "pan_eval s e" THEN CAKE_REWRITE_TAC[] THENL [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_efl_fin_tac] THEN
  REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM;
              FLOOKUP_UPDATE] THEN
  ASM_CASES_TAC `v':mlstring = z` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FUPDATE_EQ] THEN
    NAMED_CASES_ON
      "pan_evaluate (prog,pan_state_locals_fupd (combin_K (pan_state_locals s |+ (z,a))) s)"
      ["res1 st"] THEN
    CAKE_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `pan_res_var (pan_state_locals (st:(A,FFI)pan_state)) (z,SOME (v:(A)pan_v))` THEN
    REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_pan_res_var_thm] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM z (free_var_ids (prog:(A)panLang_prog))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(z = v':mlstring)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`pan_state_locals (s:(A,FFI)pan_state)`; `z:mlstring`; `v:(A)pan_v`;
                 `v':mlstring`; `a:(A)pan_v`] FUPDATE_COMMUTES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K (pan_state_locals s |+ (v',a))) s)"
    ["res1 st"] THEN
  CAKE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a:(A)pan_v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `st:(A,FFI)pan_state`]) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:(mlstring,(A)pan_v)fmap` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  EXISTS_TAC `pan_res_var l1 (v',FLOOKUP (pan_state_locals (s:(A,FFI)pan_state)) v')` THEN
  REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `l1 = pan_state_locals (st:(A,FFI)pan_state) |+ (z,v)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_pan_res_var_thm] THEN
  ASM_MESON_TAC[]);;

let PPASS2AUX_efl_While = prove
 (PPASS2AUX_efl_case "While",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihNone")
     (CONJUNCTS_THEN2 (LABEL_TAC "ihCont") (LABEL_TAC "ihBody"))) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `~MEM z (var_exp (e:(A)panLang_exp)) /\ ~MEM z (free_var_ids (c:(A)panLang_prog))`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `~MEM z (free_var_ids (While e (c:(A)panLang_prog)))` THEN
     REWRITE_TAC[free_var_ids_def; MEM_APPEND; DE_MORGAN_THM];
     ALL_TAC] THEN
   ONCE_REWRITE_TAC[PPASS2AUX_evaluate_While] THEN
   QPAT_X_ASSUM "pan_evaluate (While _ _,_) = _"
     (MP_TAC o ONCE_REWRITE_RULE[PPASS2AUX_evaluate_While]) THEN
   ASM_SIMP_TAC[eval_fresh_var; pan_state_INFO.ri_accfupds; K_THM; PPASS2AUX_dec_clock_locals;
                pan_empty_locals_def] THEN
   QCASES_ON "pan_eval s e" THEN CAKE_REWRITE_TAC[] THENL [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   NAMED_CASES_ON "a" ["wl"; "vs"; "nm flds"] THEN CAKE_REWRITE_TAC[] THENL
    [ALL_TAC; PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac] THEN
   NAMED_CASES_ON "wl" ["w"] THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_efl_fin_tac] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "pan_evaluate (c,pan_dec_clock s)" ["res1 s1"] THEN CAKE_REWRITE_TAC[] THEN
   REMOVE_THEN "ihBody" (MP_TAC o SPEC `w:A word`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `s1:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[PPASS2AUX_dec_clock_locals] THEN
   DISCH_THEN(X_CHOOSE_THEN `l1:(mlstring,(A)pan_v)fmap` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
     REWRITE_TAC[good_res_def; distinctness "option"] THEN DISCH_THEN SUBST1_TAC THEN
     REMOVE_THEN "ihNone" (MP_TAC o SPECL [`w:A word`; `s1:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[] THEN MESON_TAC[];
     ALL_TAC] THEN
   NAMED_CASES_ON "r1" ["";"";"";"";"rv";"eid ev";"ffi_out"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac;
     FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
     REWRITE_TAC[good_res_def; distinctness "option"; injectivity "option";
                 distinctness "pan_result"] THEN DISCH_THEN SUBST1_TAC THEN
     REMOVE_THEN "ihCont" (MP_TAC o SPECL [`w:A word`; `s1:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[] THEN MESON_TAC[];
     PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac]);;

let PPASS2AUX_efl_Call = prove
 (PPASS2AUX_efl_case "panLang_Call",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihHdl")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `~MEM z (FLAT (MAP var_exp (argexps:((A)panLang_exp)list))) /\
                 (!vn hdl. caltyp = SOME (SOME (panLang_Local,vn:mlstring),
                                          hdl:(mlstring#mlstring#(A)panLang_prog)option)
                           ==> ~(z = vn)) /\
                 (!ret eid evar (p:(A)panLang_prog).
                    caltyp = SOME (ret:(varkind#mlstring)option,
                                   SOME (eid:mlstring,evar:mlstring,p))
                    ==> ~(z = evar) /\ ~MEM z (free_var_ids p))`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `~MEM z (free_var_ids (panLang_Call caltyp fname (argexps:((A)panLang_exp)list)))` THEN
     NAMED_CASES_ON "caltyp" ["";"ch"] THENL
      [REWRITE_TAC[free_var_ids_def; distinctness "option"];
       PAIR_CASES_ON `ch:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
       NAMED_CASES_ON "ch0" ["";"rt"] THEN NAMED_CASES_ON "ch1" ["";"h"] THEN
       TRY(PAIR_CASES_ON `rt:varkind#mlstring`) THEN
       TRY(PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog`) THEN
       PPASS2AUX_varkind_cases_tac THEN
       REWRITE_TAC[free_var_ids_def; MEM_APPEND; MEM; DE_MORGAN_THM; distinctness "option";
                   injectivity "option"; PAIR_EQ; distinctness "varkind"] THEN
       MESON_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Call] THEN
   QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o REWRITE_RULE[PPASS2AUX_evaluate_Call]) THEN
   ASM_SIMP_TAC[OPT_MMAP_eval_fresh_var; pan_state_INFO.ri_accfupds; K_THM;
                PPASS2AUX_dec_clock_locals; pan_state_INFO.ri_fupdfupds; K_o_THM;
                pan_empty_locals_def] THEN
   QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
  QCASES_ON "pan_lookup_code (pan_state_code s) fname a" THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   NAMED_CASES_ON "a'" ["prog newlocals rsh"] THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
     ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac;
     PPASS2AUX_efl_fin_tac;
     (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   NAMED_CASES_ON "caltyp" ["";"ch"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   PAIR_CASES_ON `ch:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
   CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "ch0" ["";"rt"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   PAIR_CASES_ON `rt:varkind#mlstring` THEN CAKE_REWRITE_TAC[] THEN
   PPASS2AUX_varkind_cases_tac THENL
    [SUBGOAL_THEN `~(z = rt1:mlstring)` ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPECL [`rt1:mlstring`;
                                     `ch1:(mlstring#mlstring#(A)panLang_prog)option`]) THEN
       REWRITE_TAC[];
       ALL_TAC];
     ALL_TAC] THEN
   ASM_SIMP_TAC[is_valid_value_simps; kvar_simps; pan_state_INFO.ri_accfupds; K_THM;
                FLOOKUP_UPDATE] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN PPASS2AUX_efl_fin_tac);
     (NAMED_CASES_ON "caltyp" ["";"ch"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   PAIR_CASES_ON `ch:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
   CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "ch1" ["";"h"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog` THEN CAKE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~(z = h1:mlstring) /\ ~MEM z (free_var_ids (h2:(A)panLang_prog))`
     STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPECL [`ch0:(varkind#mlstring)option`; `h0:mlstring`; `h1:mlstring`;
                                   `h2:(A)panLang_prog`]) THEN REWRITE_TAC[];
     ALL_TAC] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_efl_fin_tac] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `eid:mlstring = h0`)) THEN
   QCASES_ON "FLOOKUP (pan_state_eshapes s) eid" THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   ASM_SIMP_TAC[is_valid_value_simps; pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_efl_fin_tac] THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
   REMOVE_THEN "ihHdl" (MP_TAC o SPECL [`a:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
     `newlocals:(mlstring,(A)pan_v)fmap`; `ch0:(varkind#mlstring)option`; `eid:mlstring`;
     `h2:(A)panLang_prog`; `h1:mlstring`; `exn:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[is_valid_value_simps] THEN
   REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds;
               K_THM] THEN
   MP_TAC(ISPECL [`pan_state_locals (s:(A,FFI)pan_state)`; `z:mlstring`; `v:(A)pan_v`;
                  `h1:mlstring`; `exn:(A)pan_v`] FUPDATE_COMMUTES) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[]);
     PPASS2AUX_efl_fin_tac]);;

let PPASS2AUX_efl_DecCall = prove
 (PPASS2AUX_efl_case "DecCall",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihCont")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[free_var_ids_def; MEM_APPEND; MEM; DE_MORGAN_THM]) THEN
   REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
   REWRITE_TAC[PPASS2AUX_evaluate_DecCall] THEN
   QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o REWRITE_RULE[PPASS2AUX_evaluate_DecCall]) THEN
   ASM_SIMP_TAC[OPT_MMAP_eval_fresh_var; pan_state_INFO.ri_accfupds; K_THM;
                PPASS2AUX_dec_clock_locals; pan_state_INFO.ri_fupdfupds; K_o_THM;
                pan_empty_locals_def] THEN
   QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   QCASES_ON "pan_lookup_code (pan_state_code s) fname a" THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   NAMED_CASES_ON "a'" ["prog newlocals rsh"] THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
     ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; ALL_TAC] THEN
   NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THENL
    [PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac;
     PPASS2AUX_efl_fin_tac; ALL_TAC; PPASS2AUX_efl_fin_tac; PPASS2AUX_efl_fin_tac] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_efl_fin_tac] THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
   REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds;
               K_THM; FLOOKUP_UPDATE] THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`pan_state_locals (s:(A,FFI)pan_state)`; `z:mlstring`; `v:(A)pan_v`;
                  `rt:mlstring`; `retv:(A)pan_v`] FUPDATE_COMMUTES) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   NAMED_CASES_ON
     "pan_evaluate (prog1,pan_state_locals_fupd (combin_K (pan_state_locals s |+ (rt,retv))) st)"
     ["res2 st2"] THEN CAKE_REWRITE_TAC[] THEN
   REMOVE_THEN "ihCont" (MP_TAC o SPECL [`a:((A)pan_v)list`; `prog:(A)panLang_prog`;
     `newlocals:(mlstring,(A)pan_v)fmap`; `retv:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res2:((A)pan_result)option`; `st2:(A,FFI)pan_state`]) THEN
   REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds;
               K_THM] THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `l1:(mlstring,(A)pan_v)fmap` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
   EXISTS_TAC `pan_res_var l1 (rt,FLOOKUP (pan_state_locals (s:(A,FFI)pan_state)) rt)` THEN
   REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `l1 = pan_state_locals (st2:(A,FFI)pan_state) |+ (z,v)` SUBST1_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_pan_res_var_thm] THEN
   ASM_MESON_TAC[]);;

let evaluate_fresh_local = prove
 (`!z v p s res s'.
     ~MEM z (free_var_ids p) /\ pan_evaluate (p,s) = (res,s')
     ==> ?locals.
           pan_evaluate (p, pan_state_locals_fupd (combin_K (pan_state_locals s |+ (z,v)))
                              (s:(A,FFI)pan_state)) =
           (res, pan_state_locals_fupd (combin_K locals) s') /\
           (good_res res /\ ~(res = SOME pan_Error)
            ==> locals = pan_state_locals s' |+ (z,v))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(p:(A)panLang_prog,s:(A,FFI)pan_state)`
          (PPASS2AUX_assemble PPASS2AUX_evaluate_fresh_local_ind
             ["Dec",PPASS2AUX_efl_Dec; "panLang_Seq",PPASS2AUX_efl_Seq;
              "panLang_If",PPASS2AUX_efl_If; "While",PPASS2AUX_efl_While;
              "panLang_Call",PPASS2AUX_efl_Call; "DecCall",PPASS2AUX_efl_DecCall]
             PPASS2AUX_efl_simple_tac)) THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

let evaluate_two_fresh_locals = prove
 (`!z1 v1 z2 v2 p s res s'.
     ~MEM z1 (free_var_ids p) /\ ~MEM z2 (free_var_ids p) /\
     pan_evaluate (p,s) = (res,s')
     ==> ?locals.
           pan_evaluate (p, pan_state_locals_fupd
                              (combin_K (pan_state_locals s |+ (z1,v1) |+ (z2,v2)))
                              (s:(A,FFI)pan_state)) =
           (res, pan_state_locals_fupd (combin_K locals) s') /\
           (good_res res /\ ~(res = SOME pan_Error)
            ==> locals = pan_state_locals s' |+ (z1,v1) |+ (z2,v2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z1:mlstring`; `v1:(A)pan_v`; `p:(A)panLang_prog`; `s:(A,FFI)pan_state`;
                 `res:((A)pan_result)option`; `s':(A,FFI)pan_state`] evaluate_fresh_local) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:(mlstring,(A)pan_v)fmap` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`z2:mlstring`; `v2:(A)pan_v`; `p:(A)panLang_prog`;
                 `pan_state_locals_fupd (combin_K (pan_state_locals s |+ (z1,v1))) (s:(A,FFI)pan_state)`;
                 `res:((A)pan_result)option`;
                 `pan_state_locals_fupd (combin_K l1) (s':(A,FFI)pan_state)`] evaluate_fresh_local) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:(mlstring,(A)pan_v)fmap` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l2:(mlstring,(A)pan_v)fmap` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let PPASS2AUX_evaluate_unchanged_local_ind =
  let goal = `\(p:(A)panLang_prog,s:(A,FFI)pan_state).
      !res s'. ~MEM (z:mlstring) (free_var_ids p) /\ pan_evaluate (p,s) = (res,s') /\
               good_res res /\ ~(res = SOME pan_Error)
               ==> FLOOKUP (pan_state_locals s') z = FLOOKUP (pan_state_locals s) z` in
  CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (ISPEC goal pan_evaluate_ind);;

let PPASS2AUX_eul_case name =
  let cases = conjuncts (lhand (concl PPASS2AUX_evaluate_unchanged_local_ind)) in
  let prog_of c =
    let body = snd (strip_forall c) in
    let ab = if is_forall (rand body) then snd (strip_forall (rand body)) else body in
    let ev = lhand (lhand (rand (lhand ab))) in
    fst (dest_pair (rand ev)) in
  find (fun c -> let h = fst (strip_comb (prog_of c)) in
                 is_const h && fst (dest_const h) = name) cases;;

let PPASS2AUX_eul_fin_tac =
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  GVS[good_res_def; FLOOKUP_UPDATE; kvar_defs; pan_state_INFO.ri_accfupds; K_THM;
      pan_empty_locals_def; PPASS2AUX_dec_clock_locals; FLOOKUP_pan_res_var_thm];;

let PPASS2AUX_eul_simple_tac =
  PPASS2AUX_fresh_pre THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def; pan_sh_mem_load_def; pan_sh_mem_store_def] THEN
  REPEAT(CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN TOP_CASE_TAC) THEN
  PPASS2AUX_eul_fin_tac;;

let PPASS2AUX_eul_Seq = prove
 (PPASS2AUX_eul_case "panLang_Seq",
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN
  PPASS2AUX_fresh_pre THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  NAMED_CASES_ON "pan_evaluate (c1,s)" ["res1 s1"] THEN CAKE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`res1:((A)pan_result)option`; `s1:(A,FFI)pan_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `res1:((A)pan_result)option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[good_res_def; distinctness "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,FFI)pan_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

let PPASS2AUX_eul_If = prove
 (PPASS2AUX_eul_case "panLang_If",
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  PPASS2AUX_fresh_pre THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  QCASES_ON "pan_eval s e" THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "a" ["wl"; "vs"; "nm flds"] THEN CAKE_REWRITE_TAC[] THENL
   [ALL_TAC; PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac] THEN
  NAMED_CASES_ON "wl" ["w"] THEN CAKE_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `w:A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let PPASS2AUX_eul_Dec = prove
 (PPASS2AUX_eul_case "Dec",
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[free_var_ids_def; MEM_APPEND; DE_MORGAN_THM; MEM_FILTER]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  REWRITE_TAC[pan_evaluate_def] THEN
  QCASES_ON "pan_eval s e" THEN CAKE_REWRITE_TAC[] THENL [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_eul_fin_tac] THEN
  NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K (pan_state_locals s |+ (v,a))) s)"
    ["res1 st"] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_pan_res_var_thm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a:(A)pan_v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `st:(A,FFI)pan_state`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN ASM_MESON_TAC[]);;

let PPASS2AUX_eul_While = prove
 (PPASS2AUX_eul_case "While",
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihNone")
    (CONJUNCTS_THEN2 (LABEL_TAC "ihCont") (LABEL_TAC "ihBody"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM z (var_exp (e:(A)panLang_exp)) /\ ~MEM z (free_var_ids (c:(A)panLang_prog))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM z (free_var_ids (While e (c:(A)panLang_prog)))` THEN
    REWRITE_TAC[free_var_ids_def; MEM_APPEND; DE_MORGAN_THM];
    ALL_TAC] THEN
  QPAT_X_ASSUM "pan_evaluate (While _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[PPASS2AUX_evaluate_While]) THEN
  QCASES_ON "pan_eval s e" THEN CAKE_REWRITE_TAC[] THENL [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "a" ["wl"; "vs"; "nm flds"] THEN CAKE_REWRITE_TAC[] THENL
   [ALL_TAC; PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac] THEN
  NAMED_CASES_ON "wl" ["w"] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_eul_fin_tac] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "pan_evaluate (c,pan_dec_clock s)" ["res1 s1"] THEN CAKE_REWRITE_TAC[] THEN
  REMOVE_THEN "ihBody" (MP_TAC o SPEC `w:A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `s1:(A,FFI)pan_state`]) THEN
  ASM_REWRITE_TAC[PPASS2AUX_dec_clock_locals] THEN DISCH_TAC THEN
  NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    REWRITE_TAC[good_res_def; distinctness "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REMOVE_THEN "ihNone" (MP_TAC o SPECL [`w:A word`; `s1:(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  NAMED_CASES_ON "r1" ["";"";"";"";"rv";"eid ev";"ffi_out"] THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac;
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    REWRITE_TAC[good_res_def; distinctness "option"; injectivity "option";
                distinctness "pan_result"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REMOVE_THEN "ihCont" (MP_TAC o SPECL [`w:A word`; `s1:(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`]) THEN
    ASM_REWRITE_TAC[];
    PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac]);;

let PPASS2AUX_eul_Call = prove
 (PPASS2AUX_eul_case "panLang_Call",
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihHdl")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM z (FLAT (MAP var_exp (argexps:((A)panLang_exp)list))) /\
                (!vn hdl. caltyp = SOME (SOME (panLang_Local,vn:mlstring),
                                         hdl:(mlstring#mlstring#(A)panLang_prog)option)
                          ==> ~(z = vn)) /\
                (!ret eid evar (p:(A)panLang_prog).
                   caltyp = SOME (ret:(varkind#mlstring)option,
                                  SOME (eid:mlstring,evar:mlstring,p))
                   ==> ~(z = evar) /\ ~MEM z (free_var_ids p))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
      `~MEM z (free_var_ids (panLang_Call caltyp fname (argexps:((A)panLang_exp)list)))` THEN
    PPASS2AUX_call_fvi_tac;
    ALL_TAC] THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o REWRITE_RULE[PPASS2AUX_evaluate_Call]) THEN
  REWRITE_TAC[pan_empty_locals_def] THEN
  QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  QCASES_ON "pan_lookup_code (pan_state_code s) fname a" THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "a'" ["prog newlocals rsh"] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
    ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
  NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac;
    PPASS2AUX_eul_fin_tac;
    (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
     NAMED_CASES_ON "caltyp" ["";"ch"] THEN CAKE_REWRITE_TAC[] THENL
      [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
     PAIR_CASES_ON `ch:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
     CAKE_REWRITE_TAC[] THEN
     NAMED_CASES_ON "ch0" ["";"rt"] THEN CAKE_REWRITE_TAC[] THENL
      [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
     PAIR_CASES_ON `rt:varkind#mlstring` THEN CAKE_REWRITE_TAC[] THEN
     PPASS2AUX_varkind_cases_tac THENL
      [SUBGOAL_THEN `~(z = rt1:mlstring) /\ ~(rt1 = z)` STRIP_ASSUME_TAC THENL
        [FIRST_X_ASSUM(MP_TAC o SPECL [`rt1:mlstring`;
                                       `ch1:(mlstring#mlstring#(A)panLang_prog)option`]) THEN
         MESON_TAC[];
         ALL_TAC];
       ALL_TAC] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN PPASS2AUX_eul_fin_tac);
    (NAMED_CASES_ON "caltyp" ["";"ch"] THEN CAKE_REWRITE_TAC[] THENL
      [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
     PAIR_CASES_ON `ch:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
     CAKE_REWRITE_TAC[] THEN
     NAMED_CASES_ON "ch1" ["";"h"] THEN CAKE_REWRITE_TAC[] THENL
      [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
     PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog` THEN CAKE_REWRITE_TAC[] THEN
     SUBGOAL_THEN `~(z = h1:mlstring) /\ ~MEM z (free_var_ids (h2:(A)panLang_prog))`
       STRIP_ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o SPECL [`ch0:(varkind#mlstring)option`; `h0:mlstring`; `h1:mlstring`;
                                     `h2:(A)panLang_prog`]) THEN REWRITE_TAC[];
       ALL_TAC] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_eul_fin_tac] THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `eid:mlstring = h0`)) THEN
     QCASES_ON "FLOOKUP (pan_state_eshapes s) eid" THEN CAKE_REWRITE_TAC[] THENL
      [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_eul_fin_tac] THEN
     FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
     DISCH_TAC THEN
     REMOVE_THEN "ihHdl" (MP_TAC o SPECL [`a:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
       `newlocals:(mlstring,(A)pan_v)fmap`; `ch0:(varkind#mlstring)option`; `eid:mlstring`;
       `h2:(A)panLang_prog`; `h1:mlstring`; `exn:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE]);
    PPASS2AUX_eul_fin_tac]);;

let PPASS2AUX_eul_DecCall = prove
 (PPASS2AUX_eul_case "DecCall",
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihCont")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[free_var_ids_def; MEM_APPEND; MEM; DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o REWRITE_RULE[PPASS2AUX_evaluate_DecCall]) THEN
  REWRITE_TAC[pan_empty_locals_def] THEN
  QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  QCASES_ON "pan_lookup_code (pan_state_code s) fname a" THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "a'" ["prog newlocals rsh"] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
    ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
  NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; ALL_TAC] THEN
  NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THENL
   [PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac;
    PPASS2AUX_eul_fin_tac;
    (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ALL_TAC; PPASS2AUX_eul_fin_tac] THEN
     FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
     NAMED_CASES_ON
       "pan_evaluate (prog1,pan_set_var rt retv (pan_state_locals_fupd (combin_K (pan_state_locals s)) st))"
       ["res2 st2"] THEN CAKE_REWRITE_TAC[] THEN
     REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
     REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_pan_res_var_thm] THEN
     ASM_REWRITE_TAC[] THEN
     REMOVE_THEN "ihCont" (MP_TAC o SPECL [`a:((A)pan_v)list`; `prog:(A)panLang_prog`;
       `newlocals:(mlstring,(A)pan_v)fmap`; `retv:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`res2:((A)pan_result)option`; `st2:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE]);
    PPASS2AUX_eul_fin_tac; PPASS2AUX_eul_fin_tac]);;

let evaluate_unchanged_local = prove
 (`!z (v:B) p s res s'.
     ~MEM z (free_var_ids p) /\ pan_evaluate (p,s) = (res,s') /\
     good_res res /\ ~(res = SOME pan_Error)
     ==> FLOOKUP (pan_state_locals s') z = FLOOKUP (pan_state_locals (s:(A,FFI)pan_state)) z`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(p:(A)panLang_prog,s:(A,FFI)pan_state)`
          (PPASS2AUX_assemble PPASS2AUX_evaluate_unchanged_local_ind
             ["Dec",PPASS2AUX_eul_Dec; "panLang_Seq",PPASS2AUX_eul_Seq;
              "panLang_If",PPASS2AUX_eul_If; "While",PPASS2AUX_eul_While;
              "panLang_Call",PPASS2AUX_eul_Call; "DecCall",PPASS2AUX_eul_DecCall]
             PPASS2AUX_eul_simple_tac)) THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;



(* the results of the body that are not a return *)

let PPASS2AUX_err_tac = STRIP_TAC THEN ASM_MESON_TAC[];;

let PPASS2AUX_fin_tac = STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `pan_empty_locals (t1:(A,FFI)pan_state)` THEN REWRITE_TAC[good_res_def] THEN
  MATCH_MP_TAC (CONJUNCT2 state_rel_empty_locals) THEN ASM_REWRITE_TAC[];;

let PPASS2AUX_state_rel_locals_irrel = prove
 (`pan_globalsProof_state_rel F ctxt (s:(A,FFI)pan_state) t /\
   pan_state_locals_fupd (combin_K FEMPTY) t' = pan_state_locals_fupd (combin_K FEMPTY) t
   ==> pan_globalsProof_state_rel F ctxt s t'`,
  REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[pan_globalsProof_state_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let PPASS2AUX_cc_err_tac =
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `~(res = SOME (pan_Error:(A)pan_result))`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> concl th = `SOME (pan_Error:(A)pan_result) = res`)) THEN
  REWRITE_TAC[];;

let PPASS2AUX_cc_callee_tac =
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN REWRITE_TAC[good_res_def] THEN
    MATCH_MP_TAC (CONJUNCT1 state_rel_empty_locals) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
    ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1 = SOME (pan_Error:(A)pan_result)` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    PPASS2AUX_cc_err_tac;
    ALL_TAC] THEN
  REMOVE_THEN "ihBody" (MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`;
    `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
    `pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock (t:(A,FFI)pan_state))`;
    `st:(A,FFI)pan_state`]) THEN
  ASM_SIMP_TAC[state_rel_change_locals; state_rel_dec_clock] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac; ALL_TAC] THEN
  NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN RULE_ASSUM_TAC(REWRITE_RULE[good_res_def]);;

let PPASS2AUX_cc_exn_tac (x:term) =
  NAMED_CASES_ON "ch1" ["";"h"] THEN CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_fin_tac; ALL_TAC] THEN
  PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog` THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_fin_tac] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `eid:mlstring = h0`)) THEN
  QCASES_ON "FLOOKUP (pan_state_eshapes t) eid" THEN CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac; ALL_TAC] THEN
  SUBGOAL_THEN `pan_is_valid_value (t:(A,FFI)pan_state) panLang_Local h1 (exn:(A)pan_v) <=>
                pan_is_valid_value (s:(A,FFI)pan_state) panLang_Local h1 exn` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[is_valid_value_simps]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  DISCH_TAC THEN
  REMOVE_THEN "ihHdl" (MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
    `newlocals:(mlstring,(A)pan_v)fmap`; x; `eid:mlstring`;
    `h2:(A)panLang_prog`; `h1:mlstring`; `exn:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
    `pan_set_var h1 exn (pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state)))
                           (t1:(A,FFI)pan_state))`;
    `s':(A,FFI)pan_state`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC state_rel_set_var THEN MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]];;

let PPASS2AUX_cc_callee_part_tac =
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
    ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `res1 = SOME (pan_Error:(A)pan_result)` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    PPASS2AUX_cc_err_tac;
    ALL_TAC] THEN
  REMOVE_THEN "ihBody" (MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`;
    `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
    `pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock (t:(A,FFI)pan_state))`;
    `st:(A,FFI)pan_state`]) THEN
  ASM_SIMP_TAC[state_rel_change_locals; state_rel_dec_clock] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac; ALL_TAC] THEN
  NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN RULE_ASSUM_TAC(REWRITE_RULE[good_res_def]);;

let PPASS2AUX_fin6_tac =
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  CAKE_REWRITE_TAC[distinctness "option"] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1; good_res_def] THEN
  MATCH_MP_TAC (GEN_ALL PPASS2AUX_state_rel_locals_irrel) THEN
  EXISTS_TAC `pan_empty_locals (t1:(A,FFI)pan_state)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC (CONJUNCT2 state_rel_empty_locals) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[pan_empty_locals_def; pan_state_INFO.ri_fupdfupds; K_o_THM; K_THM]];;

let PPASS2AUX_cc_Call = prove
 (PPASS2AUX_cc_case "panLang_Call",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihHdl")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `pan_state_clock (s:(A,FFI)pan_state) = pan_state_clock (t:(A,FFI)pan_state) /\
                 pan_state_locals s = pan_state_locals t /\
                 pan_state_eshapes s = pan_state_eshapes t`
     STRIP_ASSUME_TAC THENL [FS[pan_globalsProof_state_rel_def]; ALL_TAC] THEN
   QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o REWRITE_RULE[PPASS2AUX_evaluate_Call]) THEN
   QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   RENAME1 "OPT_MMAP (pan_eval s) argexps = SOME args" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPT_MMAP_eval_correct o
     CONJ (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`)) THEN
   QCASES_ON "pan_lookup_code (pan_state_code s) fname args" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   RENAME1 "pan_lookup_code (pan_state_code s) fname args = SOME lk" THEN
   NAMED_CASES_ON "lk" ["prog newlocals rsh"] THEN CAKE_REWRITE_TAC[] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_lookup_code o
     CONJ (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`)) THEN
  NAMED_CASES_ON "caltyp" ["";"ch"] THENL
  [(REWRITE_TAC[pan_globals_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PPASS2AUX_evaluate_Call] THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN REWRITE_TAC[good_res_def] THEN
     MATCH_MP_TAC (CONJUNCT1 state_rel_empty_locals) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
     ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `res1 = SOME (pan_Error:(A)pan_result)` THENL
    [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REMOVE_THEN "ihBody" (MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`;
     `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
     `pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock (t:(A,FFI)pan_state))`;
     `st:(A,FFI)pan_state`]) THEN
   ASM_SIMP_TAC[state_rel_change_locals; state_rel_dec_clock] THEN
   DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  NAMED_CASES_ON "res1" ["";"r1"] THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac; ALL_TAC] THEN
   NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[PAIR_EQ] THEN RULE_ASSUM_TAC(REWRITE_RULE[good_res_def]) THENL
    [PPASS2AUX_cc_err_tac; PPASS2AUX_fin_tac; PPASS2AUX_cc_err_tac; PPASS2AUX_cc_err_tac;
     COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_fin_tac;
     PPASS2AUX_fin_tac; PPASS2AUX_fin_tac]);
   PAIR_CASES_ON `ch:(varkind#mlstring)option#(mlstring#mlstring#(A)panLang_prog)option` THEN
   NAMED_CASES_ON "ch0" ["";"rt"] THENL
   [(REWRITE_TAC[pan_globals_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PPASS2AUX_evaluate_Call] THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[] THEN PPASS2AUX_cc_callee_tac THENL
    [PPASS2AUX_cc_err_tac; PPASS2AUX_fin_tac; PPASS2AUX_cc_err_tac; PPASS2AUX_cc_err_tac;
     COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     EXISTS_TAC `pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state)))
                   (t1:(A,FFI)pan_state)` THEN
     REWRITE_TAC[good_res_def] THEN
     MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN ASM_REWRITE_TAC[];
     PPASS2AUX_cc_exn_tac `NONE:(varkind#mlstring)option`;
     PPASS2AUX_fin_tac]);
    PAIR_CASES_ON `rt:varkind#mlstring` THEN PPASS2AUX_varkind_cases_tac THENL
    [(REWRITE_TAC[pan_globals_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CAKE_REWRITE_TAC[distinctness "varkind"] THEN REWRITE_TAC[PPASS2AUX_evaluate_Call] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN PPASS2AUX_cc_callee_tac THENL
    [PPASS2AUX_cc_err_tac; PPASS2AUX_fin_tac; PPASS2AUX_cc_err_tac; PPASS2AUX_cc_err_tac;
     SUBGOAL_THEN `pan_is_valid_value (t:(A,FFI)pan_state) panLang_Local rt1 (retv:(A)pan_v) <=>
                   pan_is_valid_value (s:(A,FFI)pan_state) panLang_Local rt1 retv` SUBST1_TAC THENL
      [ASM_REWRITE_TAC[is_valid_value_simps]; ALL_TAC] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     EXISTS_TAC `pan_set_kvar panLang_Local rt1 retv
                   (pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state)))
                     (t1:(A,FFI)pan_state))` THEN
     REWRITE_TAC[good_res_def; kvar_simps] THEN
     MATCH_MP_TAC state_rel_set_var THEN
     MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN ASM_REWRITE_TAC[];
     PPASS2AUX_cc_exn_tac `SOME (panLang_Local,rt1:mlstring)`;
     PPASS2AUX_fin_tac]);
     QCASES_ON "FLOOKUP (pan_globals_context_globals ctxt) rt1" THENL
     [(REWRITE_TAC[pan_globals_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CAKE_REWRITE_TAC[distinctness "varkind"] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Call] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN PPASS2AUX_cc_callee_tac THENL
    [PPASS2AUX_cc_err_tac; PPASS2AUX_fin_tac; PPASS2AUX_cc_err_tac; PPASS2AUX_cc_err_tac;
     SUBGOAL_THEN `~pan_is_valid_value (s:(A,FFI)pan_state) panLang_Global rt1 (retv:(A)pan_v)`
       ASSUME_TAC THENL
      [REWRITE_TAC[is_valid_value_simps] THEN
       QCASES_ON "FLOOKUP (pan_state_globals s) rt1" THEN CAKE_REWRITE_TAC[] THEN
       FIRST_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
         CONJ (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`)) THEN
       ASM_REWRITE_TAC[distinctness "option"];
       ALL_TAC] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac;
     PPASS2AUX_cc_exn_tac `SOME (panLang_Global,rt1:mlstring)`;
     PPASS2AUX_fin_tac]);
      RENAME1 "FLOOKUP (pan_globals_context_globals ctxt) rt1 = SOME gl" THEN
   NAMED_CASES_ON "gl" ["sh addr"] THEN
   NAMED_CASES_ON "ch1" ["";"h"] THENL
      [(REWRITE_TAC[pan_globals_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CAKE_REWRITE_TAC[distinctness "varkind"] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_DecCall] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN PPASS2AUX_cc_callee_tac THENL
    [PPASS2AUX_cc_err_tac; PPASS2AUX_fin_tac; PPASS2AUX_cc_err_tac; PPASS2AUX_cc_err_tac;
     (COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
   SUBGOAL_THEN `?w. FLOOKUP (pan_state_globals (s:(A,FFI)pan_state)) rt1 = SOME w /\
                     shape_of (retv:(A)pan_v) = shape_of w` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `pan_is_valid_value (s:(A,FFI)pan_state) panLang_Global rt1 (retv:(A)pan_v)` THEN
     REWRITE_TAC[is_valid_value_simps] THEN
     QCASES_ON "FLOOKUP (pan_state_globals s) rt1" THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
     CONJ (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`)) THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     SUBGOAL_THEN `pan_state_globals (pan_state_locals_fupd (combin_K newlocals)
                   (pan_dec_clock (s:(A,FFI)pan_state))) = pan_state_globals s` ASSUME_TAC THENL
    [REWRITE_TAC[pan_dec_clock_def; pan_state_INFO.ri_accfupds]; ALL_TAC] THEN
   MP_TAC(ISPECL [`prog:(A)panLang_prog`;
                  `pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock (s:(A,FFI)pan_state))`;
                  `SOME (pan_Return retv):((A)pan_result)option`; `st:(A,FFI)pan_state`;
                  `rt1:mlstring`; `w:(A)pan_v`] evaluate_global_shape_invariant) THEN
   ASM_REWRITE_TAC[] THEN
DISCH_THEN(X_CHOOSE_THEN `w':(A)pan_v` STRIP_ASSUME_TAC) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
       CONJ (ASSUME `pan_globalsProof_state_rel F ctxt (st:(A,FFI)pan_state) t1`)) THEN
     ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
     DISCH_THEN(X_CHOOSE_THEN `addr2:A word` STRIP_ASSUME_TAC) THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `addr':A word = addr2`)) THEN
     MP_TAC(ISPECL [`shape_of (w:(A)pan_v)`;
                    `word_sub (pan_state_top_addr (t1:(A,FFI)pan_state)) addr'`;
                    `pan_state_memaddrs (t1:(A,FFI)pan_state)`;
                    `pan_state_memory (t1:(A,FFI)pan_state)`;
                    `[]:(mlstring#struct_info)list`; `w':(A)pan_v`; `retv:(A)pan_v`]
                   (CONJUNCT1 mem_load_mem_store)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:A word->(A)word_lab`) THEN
     SUBGOAL_THEN
    `pan_evaluate (panLang_Store (panLang_Op asm_Sub [TopAddr; panLang_Const addr'])
                    (panLang_Var panLang_Local (implode "")),
                  pan_set_var (implode "") (retv:(A)pan_v)
                    (pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state)))
                       (t1:(A,FFI)pan_state))) =
     (NONE, pan_state_memory_fupd (combin_K (m:A word->(A)word_lab))
              (pan_set_var (implode "") retv
                 (pan_state_locals_fupd (combin_K (pan_state_locals t)) t1)))` SUBST1_TAC THENL
    [SIMP[pan_evaluate_def; pan_eval_def; OPT_MMAP_def; OPTION_BIND_DEF; OPTION_MAP_DEF;
          word_op_def; pan_set_var_def; pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE];
     ALL_TAC] THEN
   CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
   EXISTS_TAC `pan_state_memory_fupd (combin_K (m:A word->(A)word_lab))
                 (pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state)))
                    (t1:(A,FFI)pan_state))` THEN
   REWRITE_TAC[good_res_def; PAIR_EQ] THEN CONJ_TAC THENL
    [REWRITE_TAC[pan_set_var_def; pan_state_component_equality; pan_state_INFO.ri_accfupds;
                 K_THM] THEN
     REWRITE_TAC[fmap_eq_flookup; FLOOKUP_pan_res_var_thm; FLOOKUP_UPDATE] THEN MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[kvar_simps; pan_set_global_def] THEN
   MATCH_MP_TAC PPASS2AUX_state_rel_store_global THEN
   MAP_EVERY EXISTS_TAC [`w':(A)pan_v`; `addr':A word`] THEN
   ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
   MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN ASM_REWRITE_TAC[]);
     PPASS2AUX_fin_tac; PPASS2AUX_fin_tac]);
       (PAIR_CASES_ON `h:mlstring#mlstring#(A)panLang_prog` THEN
   REWRITE_TAC[pan_globals_compile_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CAKE_REWRITE_TAC[distinctness "varkind"] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ABBREV_TAC `names = APPEND (CONS h1 (free_var_ids (pan_globals_compile ctxt (h2:(A)panLang_prog))))
                         (FLAT (MAP var_exp (MAP (pan_globals_compile_exp ctxt) (argexps:((A)panLang_exp)list))))` THEN
   ABBREV_TAC `vn' = fresh_name (implode "") names` THEN
   ABBREV_TAC `flag = fresh_name (implode "vn'") (CONS vn' names)` THEN
   SUBGOAL_THEN `~(vn' = h1:mlstring) /\ ~MEM vn' (free_var_ids (pan_globals_compile ctxt (h2:(A)panLang_prog))) /\
                 ~MEM vn' (FLAT (MAP var_exp (MAP (pan_globals_compile_exp ctxt) (argexps:((A)panLang_exp)list)))) /\
                 ~(flag = vn') /\ ~(flag = h1) /\
                 ~MEM flag (free_var_ids (pan_globals_compile ctxt h2)) /\
                 ~MEM flag (FLAT (MAP var_exp (MAP (pan_globals_compile_exp ctxt) argexps)))`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPECL [`implode ""`; `names:mlstring list`] fresh_name_correct) THEN
     MP_TAC(ISPECL [`implode "vn'"`; `CONS (vn':mlstring) names`] fresh_name_correct) THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `names:mlstring list`)) THEN
     REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `is_wf_shape ([]:(mlstring#struct_info)list) sh` ASSUME_TAC THENL
    [MP_TAC(MATCH_MP state_rel_globals_wf
       (CONJ (ASSUME `FLOOKUP (pan_globals_context_globals ctxt) rt1 = SOME (sh:shape,addr:A word)`)
             (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`))) THEN
     REWRITE_TAC[FST];
     ALL_TAC] THEN
   SUBGOAL_THEN `?shv. pan_eval (t:(A,FFI)pan_state) (shape_val sh) = SOME shv`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPEC `pan_eval (t:(A,FFI)pan_state) (shape_val sh)` (cases "option")) THEN
     REWRITE_TAC[eval_shape_val_NONE] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `sh = shape_of (shv:(A)pan_v)` ASSUME_TAC THENL
    [ASM_MESON_TAC[GEN_ALL eval_shape_val_thm]; ALL_TAC] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Dec] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[pan_eval_def; shape_of_def; pan_state_INFO.ri_accfupds; K_THM] THEN
   CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[shape_of_def; pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds;
               K_THM; FLOOKUP_UPDATE] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Seq] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Call] THEN
   ASM_SIMP_TAC[OPT_MMAP_eval_two_fresh_vars; pan_state_INFO.ri_accfupds; K_THM] THEN
   CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[PPASS2AUX_dec_clock_locals; pan_state_INFO.ri_fupdfupds; K_o_THM;
               is_valid_value_simps; pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
     CAKE_REWRITE_TAC[distinctness "option"] THEN
     REWRITE_TAC[PAIR_EQ; UNWIND_THM1; good_res_def] THEN
     MATCH_MP_TAC (GEN_ALL PPASS2AUX_state_rel_locals_irrel) THEN
     EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC (CONJUNCT1 state_rel_empty_locals) THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[pan_empty_locals_def; pan_state_INFO.ri_fupdfupds; K_o_THM; K_THM]];
     ALL_TAC] THEN
   PPASS2AUX_cc_callee_part_tac THENL
   [PPASS2AUX_cc_err_tac; PPASS2AUX_fin6_tac; PPASS2AUX_cc_err_tac; PPASS2AUX_cc_err_tac;
    (COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
   QCASES_ON "FLOOKUP (pan_state_globals s) rt1" THEN CAKE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN
   RENAME1 "FLOOKUP (pan_state_globals s) rt1 = SOME w" THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
     CONJ (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`)) THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
   DISCH_THEN(X_CHOOSE_THEN `addr0:A word` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `shape_of (retv:(A)pan_v) = shape_of (shv:(A)pan_v)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `pan_state_globals (pan_state_locals_fupd (combin_K newlocals)
                   (pan_dec_clock (s:(A,FFI)pan_state))) = pan_state_globals s` ASSUME_TAC THENL
    [REWRITE_TAC[pan_dec_clock_def; pan_state_INFO.ri_accfupds]; ALL_TAC] THEN
   MP_TAC(ISPECL [`prog:(A)panLang_prog`;
                  `pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock (s:(A,FFI)pan_state))`;
                  `SOME (pan_Return retv):((A)pan_result)option`; `st:(A,FFI)pan_state`;
                  `rt1:mlstring`; `w:(A)pan_v`] evaluate_global_shape_invariant) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `w':(A)pan_v` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
     CONJ (ASSUME `pan_globalsProof_state_rel F ctxt (st:(A,FFI)pan_state) t1`)) THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
   DISCH_THEN(X_CHOOSE_THEN `addr2:A word` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `addr0:A word = addr2`)) THEN
   MP_TAC(ISPECL [`shape_of (w:(A)pan_v)`;
                  `word_sub (pan_state_top_addr (t1:(A,FFI)pan_state)) addr0`;
                  `pan_state_memaddrs (t1:(A,FFI)pan_state)`;
                  `pan_state_memory (t1:(A,FFI)pan_state)`;
                  `[]:(mlstring#struct_info)list`; `w':(A)pan_v`; `retv:(A)pan_v`]
                 (CONJUNCT1 mem_load_mem_store)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:A word->(A)word_lab`) THEN
     CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_If; pan_eval_def; kvar_simps; pan_set_var_def;
               pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   SIMP[pan_evaluate_def; pan_eval_def; OPT_MMAP_def; OPTION_BIND_DEF; OPTION_MAP_DEF;
        word_op_def; pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[good_res_def] THEN
   SUBGOAL_THEN
     `pan_res_var (pan_res_var (pan_state_locals t |+ (vn',shv) |+
                                  (flag,pan_Val (Word (word 0))) |+ (vn',retv))
                     (flag,FLOOKUP (pan_state_locals t) flag))
                  (vn',FLOOKUP (pan_state_locals t) vn') =
      pan_state_locals (t:(A,FFI)pan_state)` SUBST1_TAC THENL
    [REWRITE_TAC[fmap_eq_flookup; FLOOKUP_pan_res_var_thm; FLOOKUP_UPDATE] THEN
     X_GEN_TAC `x:mlstring` THEN
     ASM_CASES_TAC `x:mlstring = vn'` THEN ASM_REWRITE_TAC[] THEN
     ASM_CASES_TAC `x:mlstring = flag` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
     `pan_state_locals_fupd (combin_K (pan_state_locals t)) (pan_state_memory_fupd (combin_K m) t1) =
      pan_state_memory_fupd (combin_K m)
        (pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state))) (t1:(A,FFI)pan_state))`
     SUBST1_TAC THENL
    [REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
   REWRITE_TAC[pan_set_global_def] THEN
   MATCH_MP_TAC PPASS2AUX_state_rel_store_global THEN
   MAP_EVERY EXISTS_TAC [`w':(A)pan_v`; `addr0:A word`] THEN
   ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
   MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN ASM_REWRITE_TAC[]);
    (COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_fin6_tac] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `eid:mlstring = h0`)) THEN
   QCASES_ON "FLOOKUP (pan_state_eshapes t) h0" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac; ALL_TAC] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN PPASS2AUX_cc_err_tac] THEN
     FIRST_X_ASSUM(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC o check (is_conj o concl)) THEN
   DISCH_TAC THEN
   REMOVE_THEN "ihHdl" (MP_TAC o SPECL [`args:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
     `newlocals:(mlstring,(A)pan_v)fmap`; `SOME (panLang_Global,rt1:mlstring)`; `h0:mlstring`;
     `h2:(A)panLang_prog`; `h1:mlstring`; `exn:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[is_valid_value_simps] THEN
   DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
     `pan_set_var h1 exn (pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state)))
                            (t1:(A,FFI)pan_state))`;
     `s':(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [MATCH_MP_TAC state_rel_set_var THEN MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `tX:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
     MP_TAC(ISPECL [`vn':mlstring`; `shv:(A)pan_v`; `flag:mlstring`;
                  `pan_Val (Word (word 0)):(A)pan_v`; `pan_globals_compile ctxt (h2:(A)panLang_prog)`;
                  `pan_set_var h1 exn (pan_state_locals_fupd
                     (combin_K (pan_state_locals (t:(A,FFI)pan_state))) (t1:(A,FFI)pan_state))`;
                  `res:((A)pan_result)option`; `tX:(A,FFI)pan_state`]
                 evaluate_two_fresh_locals) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `l2:(mlstring,(A)pan_v)fmap` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `pan_set_var h1 exn
        (pan_state_locals_fupd
           (combin_K (pan_state_locals (t:(A,FFI)pan_state) |+ (vn',shv) |+
               (flag,pan_Val (Word (word 0))))) (t1:(A,FFI)pan_state)) =
      pan_state_locals_fupd
        (combin_K (pan_state_locals (pan_set_var h1 exn
               (pan_state_locals_fupd (combin_K (pan_state_locals t)) t1)) |+ (vn',shv) |+
            (flag,pan_Val (Word (word 0)))))
        (pan_set_var h1 exn (pan_state_locals_fupd (combin_K (pan_state_locals t)) t1))`
     SUBST1_TAC THENL
    [REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_fupdfupds; K_o_THM;
                 pan_state_INFO.ri_accfupds; K_THM] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Seq] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     SUBGOAL_THEN `good_res (res:((A)pan_result)option)
                 ==> FLOOKUP (pan_state_locals (tX:(A,FFI)pan_state)) vn' =
                       FLOOKUP (pan_state_locals (t:(A,FFI)pan_state)) vn' /\
                     FLOOKUP (pan_state_locals tX) flag = FLOOKUP (pan_state_locals t) flag`
     ASSUME_TAC THENL
    [DISCH_TAC THEN CONJ_TAC THENL
      [MP_TAC(ISPECL [`vn':mlstring`; `T`; `pan_globals_compile ctxt (h2:(A)panLang_prog)`;
                      `pan_set_var h1 exn (pan_state_locals_fupd
                         (combin_K (pan_state_locals (t:(A,FFI)pan_state))) (t1:(A,FFI)pan_state))`;
                      `res:((A)pan_result)option`; `tX:(A,FFI)pan_state`]
                     evaluate_unchanged_local);
       MP_TAC(ISPECL [`flag:mlstring`; `T`; `pan_globals_compile ctxt (h2:(A)panLang_prog)`;
                      `pan_set_var h1 exn (pan_state_locals_fupd
                         (combin_K (pan_state_locals (t:(A,FFI)pan_state))) (t1:(A,FFI)pan_state))`;
                      `res:((A)pan_result)option`; `tX:(A,FFI)pan_state`]
                     evaluate_unchanged_local)] THEN
     ASM_REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
   ASM_CASES_TAC `res:((A)pan_result)option = NONE` THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[] THENL
     [(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `res:((A)pan_result)option = NONE`)) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[good_res_def; distinctness "option"]) THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `l2:(mlstring,(A)pan_v)fmap`)) THEN
       REWRITE_TAC[PPASS2AUX_evaluate_Assign; pan_eval_def; is_valid_value_simps; kvar_simps;
               pan_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
   CAKE_REWRITE_TAC[shape_of_def] THEN
   REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds;
               K_THM] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_If; pan_eval_def; kvar_simps; pan_state_INFO.ri_accfupds;
               K_THM; FLOOKUP_UPDATE] THEN CAKE_REWRITE_TAC[WORD_NE_10] THEN
   REWRITE_TAC[pan_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM] THEN
       REWRITE_TAC[UNWIND_THM1; good_res_def] THEN
   SUBGOAL_THEN
     `pan_res_var (pan_res_var (pan_state_locals tX |+ (vn',shv) |+
                                  (flag,pan_Val (Word (word 0))) |+
                                  (flag,pan_Val (Word (word 1))))
                     (flag,FLOOKUP (pan_state_locals t) flag))
                  (vn',FLOOKUP (pan_state_locals (t:(A,FFI)pan_state)) vn') =
      pan_state_locals (tX:(A,FFI)pan_state)` SUBST1_TAC THENL
    [REWRITE_TAC[fmap_eq_flookup; FLOOKUP_pan_res_var_thm; FLOOKUP_UPDATE] THEN
     X_GEN_TAC `x:mlstring` THEN
     ASM_CASES_TAC `x:mlstring = vn'` THEN ASM_REWRITE_TAC[] THEN
     ASM_CASES_TAC `x:mlstring = flag` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[record_fupdselfid "pan_state"] THEN ASM_REWRITE_TAC[]);
      (ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM;
               PAIR_EQ; UNWIND_THM1] THEN
   ASM_CASES_TAC `good_res (res:((A)pan_result)option)` THENL
    [FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_eq (rand (concl th)) &&
                                lhs (rand (concl th)) = `l2:(mlstring,(A)pan_v)fmap`
                             then MP_TAC th else failwith "not l2") THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     SUBGOAL_THEN
       `pan_res_var (pan_res_var (pan_state_locals tX |+ (vn',shv) |+
                                    (flag,pan_Val (Word (word 0))))
                       (flag,FLOOKUP (pan_state_locals t) flag))
                    (vn',FLOOKUP (pan_state_locals (t:(A,FFI)pan_state)) vn') =
        pan_state_locals (tX:(A,FFI)pan_state)` SUBST1_TAC THENL
      [REWRITE_TAC[fmap_eq_flookup; FLOOKUP_pan_res_var_thm; FLOOKUP_UPDATE] THEN
       X_GEN_TAC `x:mlstring` THEN
       ASM_CASES_TAC `x:mlstring = vn'` THEN ASM_REWRITE_TAC[] THEN
       ASM_CASES_TAC `x:mlstring = flag` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
       ALL_TAC] THEN
     REWRITE_TAC[record_fupdselfid "pan_state"] THEN
     UNDISCH_TAC `pan_globalsProof_state_rel (good_res (res:((A)pan_result)option)) ctxt s'
                    (tX:(A,FFI)pan_state)` THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC (GEN_ALL PPASS2AUX_state_rel_locals_irrel) THEN
     EXISTS_TAC `tX:(A,FFI)pan_state` THEN
     REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM] THEN
     UNDISCH_TAC `pan_globalsProof_state_rel (good_res (res:((A)pan_result)option)) ctxt s' (tX:(A,FFI)pan_state)` THEN
     ASM_REWRITE_TAC[]])]);
    PPASS2AUX_fin6_tac])]]]]]);;

let PPASS2AUX_cc_DecCall = prove
 (PPASS2AUX_cc_case "DecCall",
  REPEAT GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihCont")) THEN
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     SUBGOAL_THEN `pan_state_clock (s:(A,FFI)pan_state) = pan_state_clock (t:(A,FFI)pan_state) /\
                   pan_state_locals s = pan_state_locals t`
       STRIP_ASSUME_TAC THENL [FS[pan_globalsProof_state_rel_def]; ALL_TAC] THEN
     REWRITE_TAC[pan_globals_compile_def; PPASS2AUX_evaluate_DecCall] THEN
     QPAT_X_ASSUM "pan_evaluate _ = _" (MP_TAC o REWRITE_RULE[PPASS2AUX_evaluate_DecCall]) THEN
     QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
      [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
     IMP_RES_TAC OPT_MMAP_eval_correct THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     QCASES_ON "pan_lookup_code (pan_state_code s) fname a" THEN CAKE_REWRITE_TAC[] THENL
      [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
     NAMED_CASES_ON "a'" ["prog newlocals rsh"] THEN
     IMP_RES_TAC state_rel_lookup_code THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
      [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
       EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN REWRITE_TAC[good_res_def] THEN
       MATCH_MP_TAC (CONJUNCT1 state_rel_empty_locals) THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
     NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
       ["res1 st"] THEN
     CAKE_REWRITE_TAC[] THEN
     ASM_CASES_TAC `res1 = SOME (pan_Error:(A)pan_result)` THENL
      [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
       ASM_MESON_TAC[];
       ALL_TAC] THEN
     REMOVE_THEN "ihBody" (MP_TAC o SPECL [`a:((A)pan_v)list`; `rsh:shape`;
       `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`]) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
       `pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock (t:(A,FFI)pan_state))`;
       `st:(A,FFI)pan_state`]) THEN
     ASM_SIMP_TAC[state_rel_change_locals; state_rel_dec_clock] THEN
     DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  QCASES_ON "res1" THEN CAKE_REWRITE_TAC[] THENL
      [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
       ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN
     QCASES_ON "a''" THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[good_res_def]) THENL
   [PPASS2AUX_err_tac; PPASS2AUX_fin_tac; PPASS2AUX_err_tac; PPASS2AUX_err_tac;
    RENAME1 "pan_evaluate (prog,_) = (SOME (pan_Return retv),st)" THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        POP_ASSUM STRIP_ASSUME_TAC THEN
         NAMED_CASES_ON "pan_evaluate (prog1, pan_set_var rt retv (pan_state_locals_fupd (combin_K (pan_state_locals t)) st))"
           ["res2 st2"] THEN
         CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
         REMOVE_THEN "ihCont" (MP_TAC o SPECL [`a:((A)pan_v)list`; `prog:(A)panLang_prog`;
           `newlocals:(mlstring,(A)pan_v)fmap`; `retv:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `ctxt:(A)pan_globals_context`;
           `pan_set_var rt retv (pan_state_locals_fupd (combin_K (pan_state_locals (t:(A,FFI)pan_state))) (t1:(A,FFI)pan_state))`;
           `st2:(A,FFI)pan_state`]) THEN
         ASM_SIMP_TAC[state_rel_set_var; state_rel_change_locals] THEN
         DISCH_THEN(X_CHOOSE_THEN `t2:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
         ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
         REWRITE_TAC[PAIR_EQ; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
         MP_TAC(MATCH_MP (GEN_ALL state_rel_res_var)
           (CONJ (ASSUME `pan_globalsProof_state_rel (good_res (res:((A)pan_result)option)) ctxt st2 (t2:(A,FFI)pan_state)`)
                 (ASSUME `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t`))) THEN
         DISCH_THEN(MP_TAC o SPECL [`rt:mlstring`; `rt:mlstring`]) THEN
         ASM_REWRITE_TAC[] THEN SIMP[];
    PPASS2AUX_fin_tac; PPASS2AUX_fin_tac]);;

let state_rel_read_bytearray = prove
 (`!ls ctxt (s:(A,FFI)pan_state) t bytes sz ad.
     pan_globalsProof_state_rel ls ctxt s t /\
     read_bytearray sz ad
       (pan_mem_load_byte (pan_state_memory s) (pan_state_memaddrs s) (pan_state_be s)) =
       SOME bytes
     ==> read_bytearray sz ad
           (pan_mem_load_byte (pan_state_memory t) (pan_state_memaddrs t)
                              (pan_state_be t)) = SOME bytes`,
  REPLICATE_TAC 4 GEN_TAC THEN QINDUCT_ON "ad" THEN
  RW(read_bytearray_def::pan_mem_load_byte_def::all_case_eqs()) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN GVS[pan_globalsProof_state_rel_def; SUBSET]);;

let state_rel_mem_store_byte = prove
 (`pan_globalsProof_state_rel ls ctxt (s:(A,FFI)pan_state) t /\
   pan_mem_store_byte (pan_state_memory s) (pan_state_memaddrs s) (pan_state_be s) addr' b =
     SOME m'
   ==> ?m''. pan_mem_store_byte (pan_state_memory t) (pan_state_memaddrs t) (pan_state_be t)
               addr' b = SOME m'' /\
             pan_globalsProof_state_rel ls ctxt (pan_state_memory_fupd (combin_K m') s)
                                                (pan_state_memory_fupd (combin_K m'') t)`,
  REWRITE_TAC[pan_mem_store_byte_def; pan_globalsProof_state_rel_def] THEN
  STRIP_TAC THEN FS(all_case_eqs()) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `byte_align (addr':A word) IN pan_state_memaddrs (t:(A,FFI)pan_state) /\
                pan_state_memory t (byte_align addr') = Word a`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; UNWIND_THM1; pan_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
      `FLOOKUP (pan_state_globals (s:(A,FFI)pan_state)) v = SOME (value:(A)pan_v)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `addr:A word` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `addr:A word` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (CONJUNCT1 mem_load_disjoint) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (pan_state_memaddrs (s:(A,FFI)pan_state))
      (addresses (word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) addr)
                 (size_of_shape (shape_of (value:(A)pan_v))))` THEN
    UNDISCH_TAC `byte_align (addr':A word) IN pan_state_memaddrs (s:(A,FFI)pan_state)` THEN
    SET_TAC[];
    GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

let state_rel_write_bytearray = prove
 (`!(a:B) ls ctxt (s:(A,FFI)pan_state) t sz nbw bs.
     pan_globalsProof_state_rel ls ctxt s t /\
     read_bytearray sz (LENGTH nbw)
       (pan_mem_load_byte (pan_state_memory s) (pan_state_memaddrs s) (pan_state_be s)) =
       SOME bs
     ==> pan_globalsProof_state_rel ls ctxt
           (pan_state_memory_fupd
              (combin_K (pan_write_bytearray sz nbw (pan_state_memory s) (pan_state_memaddrs s)
                                      (pan_state_be s))) s)
           (pan_state_memory_fupd
              (combin_K (pan_write_bytearray sz nbw (pan_state_memory t) (pan_state_memaddrs t)
                                      (pan_state_be t))) t)`,
  QINDUCT_ON "nbw" THEN
   RW(pan_write_bytearray_def::read_bytearray_def::pan_mem_load_byte_def::LENGTH::
      all_case_eqs()) THENL
   [REWRITE_TAC[record_fupdselfid "pan_state"] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `?m'. pan_mem_store_byte
                    (pan_write_bytearray (word_add sz (word 1)) a1
                       (pan_state_memory (s:(A,FFI)pan_state)) (pan_state_memaddrs s)
                       (pan_state_be s))
                    (pan_state_memaddrs s) (pan_state_be s) sz a0 = SOME m'`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[pan_mem_store_byte_def] THEN
      QCASES_ON "pan_write_bytearray (word_add sz (word 1)) a1 (pan_state_memory s) (pan_state_memaddrs s) (pan_state_be s) (byte_align sz)" THEN
      CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ls:bool`; `ctxt:(A)pan_globals_context`;
      `s:(A,FFI)pan_state`; `t:(A,FFI)pan_state`; `word_add sz (word 1):A word`;
      `a:(byte)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL state_rel_mem_store_byte))) THEN
    REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; pan_state_INFO.ri_fupdfupds; K_o_THM] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE]]);;

let PPASS2AUX_cc_ExtCall = prove
 (PPASS2AUX_cc_case "panLang_ExtCall",
  RW(pan_globals_compile_def::pan_evaluate_def::all_case_eqs()) THEN
   IMP_RES_TAC pan_globalsProof_compile_exp_correct THEN SIMP[] THEN
   IMP_RES_TAC state_rel_read_bytearray THEN SIMP[] THEN
   (SUBGOAL_THEN `pan_state_ffi (s:(A,FFI)pan_state) = pan_state_ffi (t:(A,FFI)pan_state)`
      ASSUME_TAC THENL [FS[pan_globalsProof_state_rel_def]; ALL_TAC]) THEN
   GVS[state_rel_empty_locals; good_res_def] THEN
  IMP_RES_TAC read_bytearray_LENGTH THEN
   IMP_RES_TAC stack_removeProof_call_FFI_LENGTH THEN
   MP_TAC(ISPECL [`T`; `T`; `ctxt:(A)pan_globals_context`;
                  `pan_state_ffi_fupd (combin_K a0) (s:(A,FFI)pan_state)`;
                  `pan_state_ffi_fupd (combin_K a0) (t:(A,FFI)pan_state)`; `a'':A word`;
                  `a1:(byte)list`; `a':(byte)list`] state_rel_write_bytearray) THEN
   ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_SIMP_TAC[state_rel_change_ffi] THEN ASM_MESON_TAC[]);;

let pan_globalsProof_compile_correct = prove
 (`!p s res ctxt t s'.
     pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t /\
     pan_evaluate (p,s) = (res,s') /\ ~(res = SOME pan_Error)
     ==> ?t'. pan_evaluate (pan_globals_compile ctxt p,t) = (res,t') /\
              pan_globalsProof_state_rel (good_res res) ctxt s' t'`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(p:(A)panLang_prog,s:(A,FFI)pan_state)`
          (PPASS2AUX_assemble PPASS2AUX_compile_correct_ind
             ["panLang_Skip",PPASS2AUX_cc_Skip; "panLang_Break",PPASS2AUX_cc_Break;
              "panLang_Continue",PPASS2AUX_cc_Continue; "Annot",PPASS2AUX_cc_Annot;
              "panLang_Tick",PPASS2AUX_cc_Tick; "panLang_Assign",PPASS2AUX_cc_Assign;
              "Primitive",PPASS2AUX_cc_Primitive; "Dec",PPASS2AUX_cc_Dec;
              "panLang_Store",PPASS2AUX_cc_Store; "panLang_Store32",PPASS2AUX_cc_Store32;
              "StoreByte",PPASS2AUX_cc_StoreByte; "ShMemLoad",PPASS2AUX_cc_ShMemLoad;
              "ShMemStore",PPASS2AUX_cc_ShMemStore; "panLang_Return",PPASS2AUX_cc_Return;
              "panLang_Raise",PPASS2AUX_cc_Raise; "panLang_Seq",PPASS2AUX_cc_Seq;
              "panLang_If",PPASS2AUX_cc_If; "While",PPASS2AUX_cc_While;
              "panLang_Call",PPASS2AUX_cc_Call; "DecCall",PPASS2AUX_cc_DecCall;
              "panLang_ExtCall",PPASS2AUX_cc_ExtCall]
             NO_TAC)) THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

let fperm_code_def = cake_def
  `fperm_code f g (code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) =
     FUN_FMAP ((I ## (fperm f g ## I)) o THE o FLOOKUP code o fperm_name f g)
              (PREIMAGE (fperm_name f g) (FDOM code))`;;

let fperm_name_cancel = prove
 (`fperm_name f g (fperm_name f g name) = name:A`,
  RW[fperm_name_def] THEN REPEAT(POP_ASSUM MP_TAC) THEN RW[]);;
let _ = cake_add_simps [fperm_name_cancel];;

let fperm_name_cong = prove
 (`fperm_name f g x = fperm_name f g y <=> x = y:A`,
  REWRITE_TAC[fperm_name_def] THEN
  MAP_EVERY ASM_CASES_TAC [`f:A = x`; `g:A = x`; `f:A = y`; `g:A = y`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let _ = cake_add_simps [fperm_name_cong];;

let FLOOKUP_fperm_code = prove
 (`FLOOKUP (fperm_code f g code) (fperm_name f g name) =
   OPTION_MAP (I ## (fperm f g ## I))
     (FLOOKUP (code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) name)`,
  REWRITE_TAC[fperm_code_def] THEN
  SIMP_TAC[FLOOKUP_FUN_FMAP; FINITE_PREIMAGE; FDOM_FINITE; fperm_name_cong] THEN
  REWRITE_TAC[IN_PREIMAGE; fperm_name_cancel; o_THM] THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[THE_DEF; OPTION_MAP_DEF]);;

let FLOOKUP_fperm_code' = prove
 (`FLOOKUP (fperm_code f g code) name =
   OPTION_MAP (I ## (fperm f g ## I))
     (FLOOKUP (code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap)
              (fperm_name f g name))`,
  REWRITE_TAC[fperm_code_def] THEN
  SIMP_TAC[FLOOKUP_FUN_FMAP; FINITE_PREIMAGE; FDOM_FINITE; fperm_name_cong] THEN
  REWRITE_TAC[IN_PREIMAGE; o_THM] THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[THE_DEF; OPTION_MAP_DEF]);;

let fperm_code_FEMPTY = prove
 (`fperm_code f g FEMPTY =
   (FEMPTY:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap)`,
  RW[fmap_eq_flookup; FLOOKUP_fperm_code'; FLOOKUP_EMPTY; OPTION_MAP_DEF]);;

let fperm_decs_append = prove
 (`!f g xs ys:((A)decl)list.
     fperm_decs f g (APPEND xs ys) = APPEND (fperm_decs f g xs) (fperm_decs f g ys)`,
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; APPEND]);;

(* the code of a permuted program after one more function *)

let PPASS2AUX_fperm_code_FUPDATE = prove
 (`fperm_code f g
     ((code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) |+ (n,(p,b,r))) =
   fperm_code f g code |+ (fperm_name f g n,(p,fperm f g b,r))`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_fperm_code'; FLOOKUP_UPDATE] THEN
  X_GEN_TAC `x:mlstring` THEN
  REWRITE_TAC[MESON[fperm_name_cancel; fperm_name_cong]
    `(n:mlstring = fperm_name f g x) <=> (fperm_name f g n = x)`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

let fperm_code_FUPDATE_LIST_functions = prove
 (`!code:((A)decl)list.
     fperm_code f g (fm |++ functions code) =
     fperm_code f g fm |++ functions (fperm_decs f g code)`,
  SUBGOAL_THEN
    `!code:((A)decl)list fm.
       fperm_code f g (fm |++ functions code) =
       fperm_code f g fm |++ functions (fperm_decs f g code)`
    (fun th -> REWRITE_TAC[th]) THEN
  REC_IND_TAC (cake_ind "functions") THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[functions_def; fperm_decs_def; FUPDATE_LIST_THM;
                  PPASS2AUX_fperm_code_FUPDATE; fun_decl_INFO.ri_accfupds; K_THM]);;

let lookup_code_fperm_code = prove
 (`pan_lookup_code (fperm_code f g code) (fperm_name f g name) args =
   OPTION_MAP (fperm f g ## I)
     (pan_lookup_code
        (code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) name args)`,
  REWRITE_TAC[pan_lookup_code_def; FLOOKUP_fperm_code] THEN
  QCASES_ON "FLOOKUP code name" THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
  NAMED_CASES_ON "a" ["vs p r"] THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

(* HOL4 eval_upd_code_eta: eval_upd_code_eq with the expression abstracted *)

let eval_upd_code_eta = prove
 (`!t code. pan_eval (pan_state_code_fupd (combin_K code) (t:(A,FFI)pan_state)) = pan_eval t`,
  REWRITE_TAC[FUN_EQ_THM; eval_upd_code_eq]);;

let functions_fperm_decs = prove
 (`!x y code:((A)decl)list.
     functions (fperm_decs x y code) =
     MAP (\(a,b,c,d). (fperm_name x y a,b,fperm x y c,d)) (functions code)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`code:((A)decl)list`,`code:((A)decl)list`) THEN
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; fperm_decs_def; MAP; fun_decl_INFO.ri_accfupds; K_THM]);;

(* the name of a permuted function (HOL4: ELIM_UNCURRY) *)

let PPASS2AUX_FST_fperm4 = prove
 (`!(f:A->A) (h:B->B) (p:A#C#B#D). FST ((\(a,b,c,d). (f a,b,h c,d)) p) = f (FST p)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST]);;

let ALL_DISTINCT_fperm_decs = prove
 (`!x y code:((A)decl)list.
     ALL_DISTINCT (MAP FST (functions code))
     ==> ALL_DISTINCT (MAP FST (functions (fperm_decs x y code)))`,
  RW[functions_fperm_decs; MAP_MAP_o; o_DEF; PPASS2AUX_FST_fperm4] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`code:((A)decl)list`,`code:((A)decl)list`) THEN
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; MAP; ALL_DISTINCT; MEM_MAP]);;

let PPASS2AUX_evaluate_fperm_ind =
  let goal = `\(p:(A)panLang_prog,s:(A,FFI)pan_state).
      !res s'. pan_evaluate (p,s) = (res,s')
               ==> pan_evaluate (fperm f g p,
                                 pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s))) s) =
                   (res, pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s'))) s')` in
  CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (ISPEC goal pan_evaluate_ind);;
let PPASS2AUX_ef_case name =
  let cases = conjuncts (lhand (concl PPASS2AUX_evaluate_fperm_ind)) in
  let prog_of c =
    let body = snd (strip_forall c) in
    let ab = if is_forall (rand body) then snd (strip_forall (rand body)) else body in
    let ev = lhand (lhand ab) in
    fst (dest_pair (rand ev)) in
  find (fun c -> let h = fst (strip_comb (prog_of c)) in
                 is_const h && fst (dest_const h) = name) cases;;

let PPASS2AUX_ef_tac =
  REPEAT STRIP_TAC THEN
  GVS(pan_evaluate_def::fperm_def::eval_upd_code_eta::eval_upd_code_eq::kvar_defs::
      pan_sh_mem_load_def::pan_sh_mem_store_def::pan_empty_locals_def::pan_dec_clock_def::
      all_case_eqs());;

let PPASS2AUX_code_fupd_comm = prove
 (`(!c s:(A,FFI)pan_state.
      pan_dec_clock (pan_state_code_fupd (combin_K c) s) =
      pan_state_code_fupd (combin_K c) (pan_dec_clock s)) /\
   (!c s:(A,FFI)pan_state.
      pan_empty_locals (pan_state_code_fupd (combin_K c) s) =
      pan_state_code_fupd (combin_K c) (pan_empty_locals s)) /\
   (!s:(A,FFI)pan_state. pan_state_code (pan_dec_clock s) = pan_state_code s) /\
   (!s:(A,FFI)pan_state. pan_state_code (pan_empty_locals s) = pan_state_code s)`,
  REWRITE_TAC[pan_dec_clock_def; pan_empty_locals_def] THEN
  SIMP[pan_state_component_equality]);;

let PPASS2AUX_ef_If = prove
 (PPASS2AUX_ef_case "panLang_If",
  REPEAT STRIP_TAC THEN
   GVS(pan_evaluate_def::fperm_def::eval_upd_code_eta::eval_upd_code_eq::all_case_eqs()) THEN
  QPAT_X_ASSUM "pan_evaluate (fperm _ _ _,_) = _" MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let PPASS2AUX_ef_While = prove
 (PPASS2AUX_ef_case "While",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihNone")
     (CONJUNCTS_THEN2 (LABEL_TAC "ihCont") (LABEL_TAC "ihBody"))) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[fperm_def] THEN
   ONCE_REWRITE_TAC[PPASS2AUX_evaluate_While] THEN
   REWRITE_TAC[eval_upd_code_eq; pan_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[PPASS2AUX_code_fupd_comm] THEN
   QCASES_ON "pan_eval s e" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[PPASS2AUX_code_fupd_comm]; ALL_TAC] THEN
   NAMED_CASES_ON "a" ["wl"; "vs"; "nm flds"] THEN CAKE_REWRITE_TAC[] THENL
    [ALL_TAC;
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[PPASS2AUX_code_fupd_comm];
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[PPASS2AUX_code_fupd_comm]] THEN
   QCASES_ON "wl" THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[PPASS2AUX_code_fupd_comm]] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[PPASS2AUX_code_fupd_comm]; ALL_TAC] THEN
  NAMED_CASES_ON "pan_evaluate (c,pan_dec_clock s)" ["res1 s1"] THEN CAKE_REWRITE_TAC[] THEN
   REMOVE_THEN "ihBody" (MP_TAC o SPEC `a':A word`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `s1:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[PPASS2AUX_code_fupd_comm] THEN DISCH_THEN SUBST1_TAC THEN
   CAKE_REWRITE_TAC[] THEN
   QCASES_ON "res1" THEN CAKE_REWRITE_TAC[] THENL
    [DISCH_TAC THEN
     REMOVE_THEN "ihNone" (MP_TAC o SPECL [`a':A word`; `s1:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[fperm_def] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   QCASES_ON "a''" THEN CAKE_REWRITE_TAC[] THEN
   TRY(REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
       REWRITE_TAC[PPASS2AUX_code_fupd_comm] THEN NO_TAC) THEN
   DISCH_TAC THEN
   REMOVE_THEN "ihCont" (MP_TAC o SPECL [`a':A word`; `s1:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[fperm_def] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


let PPASS2AUX_ef_Call = prove
 (PPASS2AUX_ef_case "panLang_Call",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihHdl")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[fperm_def; PPASS2AUX_evaluate_Call] THEN
   REWRITE_TAC[eval_upd_code_eta; pan_state_INFO.ri_accfupds; K_THM] THEN
   QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[lookup_code_fperm_code] THEN
   QCASES_ON "pan_lookup_code (pan_state_code s) fname a" THEN
   REWRITE_TAC[OPTION_MAP_DEF] THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   NAMED_CASES_ON "a'" ["prog newlocals rsh"] THEN
   REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[PPASS2AUX_code_fupd_comm];
     ALL_TAC] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
     ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
   REMOVE_THEN "ihBody" (MP_TAC o SPECL [`a:((A)pan_v)list`; `rsh:shape`;
     `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `st:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; PPASS2AUX_code_fupd_comm] THEN
   REWRITE_TAC[pan_state_INFO.ri_fupdcanon] THEN DISCH_THEN SUBST1_TAC THEN
   CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "res1" [""; "r"] THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   TRY(STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[PPASS2AUX_code_fupd_comm] THEN NO_TAC) THENL
   [(* Return *)
    STRIP_TAC THEN
    GVS(kvar_defs::pan_empty_locals_def::pan_set_var_def::pan_set_global_def::
        all_case_eqs()) THEN
    MESON_TAC[cases "option"; PAIR];
    (* Exception *)
    NAMED_CASES_ON "caltyp" [""; "c"] THEN CAKE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      REWRITE_TAC[PPASS2AUX_code_fupd_comm];
      ALL_TAC] THEN
    NAMED_CASES_ON "c" ["tl hdl"] THEN CAKE_REWRITE_TAC[] THEN
    NAMED_CASES_ON "hdl" [""; "h"] THEN CAKE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      REWRITE_TAC[PPASS2AUX_code_fupd_comm];
      ALL_TAC] THEN
    NAMED_CASES_ON "h" ["eid' evar p"] THEN CAKE_REWRITE_TAC[] THEN
     REWRITE_TAC[is_valid_value_simps2] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
      [QCASES_ON "FLOOKUP (pan_state_eshapes s) eid'" THEN CAKE_REWRITE_TAC[] THENL
        [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
        [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]] THEN
       DISCH_TAC THEN
       REMOVE_THEN "ihHdl" (MP_TAC o SPECL [`a:((A)pan_v)list`; `rsh:shape`; `prog:(A)panLang_prog`;
         `newlocals:(mlstring,(A)pan_v)fmap`; `tl:((varkind#mlstring)option)`; `eid':mlstring`;
         `p:(A)panLang_prog`; `evar:mlstring`; `a1:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s':(A,FFI)pan_state`]) THEN
       ASM_REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_accfupds; pan_state_INFO.ri_fupdfupds;
                       pan_state_INFO.ri_fupdcanon; K_THM; K_o_THM];
       REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
       REWRITE_TAC[PPASS2AUX_code_fupd_comm]]]);;

let PPASS2AUX_ef_DecCall = prove
 (PPASS2AUX_ef_case "DecCall",
  REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihBody") (LABEL_TAC "ihCont")) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[fperm_def; PPASS2AUX_evaluate_DecCall] THEN
   REWRITE_TAC[eval_upd_code_eta; pan_state_INFO.ri_accfupds; K_THM] THEN
   QCASES_ON "OPT_MMAP (pan_eval s) argexps" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[lookup_code_fperm_code] THEN
   QCASES_ON "pan_lookup_code (pan_state_code s) fname a" THEN
   REWRITE_TAC[OPTION_MAP_DEF] THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   NAMED_CASES_ON "a'" ["prog newlocals rsh"] THEN
   REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CAKE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[PPASS2AUX_code_fupd_comm];
     ALL_TAC] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   NAMED_CASES_ON "pan_evaluate (prog,pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))"
     ["res1 st"] THEN CAKE_REWRITE_TAC[] THEN
   REMOVE_THEN "ihBody" (MP_TAC o SPECL [`a:((A)pan_v)list`; `rsh:shape`;
     `prog:(A)panLang_prog`; `newlocals:(mlstring,(A)pan_v)fmap`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res1:((A)pan_result)option`; `st:(A,FFI)pan_state`]) THEN
   ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; PPASS2AUX_code_fupd_comm] THEN
   REWRITE_TAC[pan_state_INFO.ri_fupdcanon] THEN DISCH_THEN SUBST1_TAC THEN
   CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "res1" [""; "r"] THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   TRY(STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[PPASS2AUX_code_fupd_comm] THEN NO_TAC) THEN
  RENAME1 "pan_evaluate (prog,_) = (SOME (pan_Return retv),st)" THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
    [POP_ASSUM STRIP_ASSUME_TAC THEN
     SUBGOAL_THEN `rsh:shape = shape` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     NAMED_CASES_ON "pan_evaluate (prog1, pan_set_var rt retv (pan_state_locals_fupd (combin_K (pan_state_locals s)) st))"
       ["res2 st2"] THEN CAKE_REWRITE_TAC[] THEN
     REMOVE_THEN "ihCont" (MP_TAC o SPECL [`a:((A)pan_v)list`; `prog:(A)panLang_prog`;
       `newlocals:(mlstring,(A)pan_v)fmap`; `retv:(A)pan_v`; `st:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`res2:((A)pan_result)option`; `st2:(A,FFI)pan_state`]) THEN
     ASM_REWRITE_TAC[pan_set_var_def; pan_state_INFO.ri_accfupds; pan_state_INFO.ri_fupdfupds;
                     pan_state_INFO.ri_fupdcanon; K_THM; K_o_THM] THEN
     DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[pan_state_INFO.ri_accfupds; pan_state_INFO.ri_fupdcanon; K_THM];
     REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]]);;


let evaluate_fperm = prove
 (`!f g p s res s'.
     pan_evaluate (p,s) = (res,s')
     ==> pan_evaluate (fperm f g p,
                       pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s)))
                         (s:(A,FFI)pan_state)) =
         (res, pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s'))) s')`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(p:(A)panLang_prog,s:(A,FFI)pan_state)`
          (PPASS2AUX_assemble PPASS2AUX_evaluate_fperm_ind
             ["panLang_If",PPASS2AUX_ef_If; "While",PPASS2AUX_ef_While;
              "panLang_Call",PPASS2AUX_ef_Call; "DecCall",PPASS2AUX_ef_DecCall]
             PPASS2AUX_ef_tac)) THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

let evaluate_fperm' = prove
 (`pan_evaluate (fperm f g p,
                 pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s)))
                   (pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))) =
   (\(x,s'). (x, pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s'))) s'))
     (pan_evaluate (p, pan_state_clock_fupd (combin_K k) s))`,
  NAMED_CASES_ON "pan_evaluate (p, pan_state_clock_fupd (combin_K k) s)" ["x y"] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_fperm) THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let PPASS2AUX_eval_locals_code = prove
 (`pan_eval (pan_state_locals_fupd (combin_K l)
               (pan_state_code_fupd (combin_K c) (s:(A,FFI)pan_state))) e =
   pan_eval (pan_state_locals_fupd (combin_K l) s) e`,
  SUBGOAL_THEN `pan_state_locals_fupd (combin_K l) (pan_state_code_fupd (combin_K c) (s:(A,FFI)pan_state)) =
                pan_state_code_fupd (combin_K c) (pan_state_locals_fupd (combin_K l) s)` SUBST1_TAC THENL
   [REWRITE_TAC[pan_state_INFO.ri_fupdcanon]; REWRITE_TAC[eval_upd_code_eq]]);;

let evaluate_decls_fperm = prove
 (`!s decs s' f g.
     evaluate_decls (s:(A,FFI)pan_state) decs = SOME s'
     ==> evaluate_decls (pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s))) s)
                        (fperm_decs f g decs) =
         SOME (pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s'))) s')`,
  REC_IND_TAC evaluate_decls_ind THEN
   RW(evaluate_decls_def::fperm_decs_def::all_case_eqs()) THENL
   [(* Decl *)
    REWRITE_TAC[PPASS2AUX_eval_locals_code] THEN EXISTS_TAC `a:(A)pan_v` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)pan_v`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* Function *)
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`s':(A,FFI)pan_state`; `f:mlstring`; `g:mlstring`]) THEN
    ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; pan_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
                    PPASS2AUX_fperm_code_FUPDATE]]);;

let PPASS2AUX_pair_eq = prove
 (`!p:A#B. p = (r,t) <=> FST p = r /\ SND p = t`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let semantics_fperm = prove
 (`pan_semantics (pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s)))
                    (s:(A,FFI)pan_state)) (fperm_name f g start) =
   pan_semantics s start`,
  SUBGOAL_THEN
    `!k. pan_evaluate (panLang_Call NONE (fperm_name f g start) [],
                       pan_state_clock_fupd (combin_K k)
                         (pan_state_code_fupd (combin_K (fperm_code f g (pan_state_code s)))
                            (s:(A,FFI)pan_state))) =
         (FST (pan_evaluate (panLang_Call NONE start [], pan_state_clock_fupd (combin_K k) s)),
          pan_state_code_fupd
            (combin_K (fperm_code f g (pan_state_code
                  (SND (pan_evaluate (panLang_Call NONE start [],
                                      pan_state_clock_fupd (combin_K k) s))))))
            (SND (pan_evaluate (panLang_Call NONE start [], pan_state_clock_fupd (combin_K k) s))))`
    ASSUME_TAC THENL
    [GEN_TAC THEN
     MP_TAC(INST [`panLang_Call NONE start []:(A)panLang_prog`,`p:(A)panLang_prog`]
                 evaluate_fperm') THEN
     REWRITE_TAC[fperm_def; pan_state_INFO.ri_fupdcanon] THEN CAKE_REWRITE_TAC[] THEN
     DISCH_THEN SUBST1_TAC THEN
     NAMED_CASES_ON "pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (combin_K k) s)" ["x y"] THEN
     CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND];
     ALL_TAC] THEN
  REWRITE_TAC[pan_semantics_def; LET_DEF; LET_END_DEF] THEN
   ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; FST; SND; PAIR_EQ] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [PPASS2AUX_pair_eq] THEN
   SIMP[]);;

let PPASS2AUX_fun_exn_commute = prove
 (`!s fi eid sh (ds:((A)decl)list).
     evaluate_decls (s:(A,FFI)pan_state) (CONS (Function fi) (CONS (ExnDecl eid sh) ds)) =
     evaluate_decls s (CONS (ExnDecl eid sh) (CONS (Function fi) ds))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_decls_def; pan_state_INFO.ri_accfupds; K_THM] THEN
  MAP_EVERY ASM_CASES_TAC
    [`ALL (is_wf_shape (pan_state_structs (s:(A,FFI)pan_state)) o SND)
           (fun_decl_params (fi:(A)fun_decl)) /\
      is_wf_shape (pan_state_structs s) (fun_decl_return fi)`;
     `FLOOKUP (pan_state_eshapes (s:(A,FFI)pan_state)) eid = NONE /\
      is_wf_shape (pan_state_structs s) sh`] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[pan_state_INFO.ri_fupdcanon]);;

let PPASS2AUX_decl_exn_commute = prove
 (`!s sh' v e eid sh (ds:((A)decl)list).
     evaluate_decls (s:(A,FFI)pan_state) (CONS (Decl sh' v e) (CONS (ExnDecl eid sh) ds)) =
     evaluate_decls s (CONS (ExnDecl eid sh) (CONS (Decl sh' v e) ds))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_decls_def; pan_state_INFO.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN
    `pan_eval (pan_state_locals_fupd (combin_K FEMPTY)
                 (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |+ (eid,sh)))
                    (s:(A,FFI)pan_state))) e =
     pan_eval (pan_state_locals_fupd (combin_K FEMPTY) s) e` SUBST1_TAC THENL
   [SUBGOAL_THEN
      `pan_state_locals_fupd (combin_K FEMPTY)
         (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |+ (eid,sh))) (s:(A,FFI)pan_state)) =
       pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |+ (eid,sh)))
         (pan_state_locals_fupd (combin_K FEMPTY) s)` SUBST1_TAC THENL
     [REWRITE_TAC[pan_state_component_equality; pan_state_INFO.ri_accfupds; K_THM];
      REWRITE_TAC[eval_upd_eshapes_eq]];
    ALL_TAC] THEN
  QCASES_ON "pan_eval (pan_state_locals_fupd (combin_K FEMPTY) (s:(A,FFI)pan_state)) e" THEN
  CAKE_REWRITE_TAC[COND_ID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[pan_state_INFO.ri_fupdcanon]);;

let PPASS2AUX_decls_cons_cong = prove
 (`!l1 l2 d s. (!s'. evaluate_decls (s':(A,FFI)pan_state) l1 = evaluate_decls s' l2)
               ==> evaluate_decls (s:(A,FFI)pan_state) (CONS d l1) =
                   evaluate_decls s (CONS d l2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  NAMED_CASES_ON "d" ["fi";"sh v e";"eid sh";"nm flds"] THEN
  ASM_REWRITE_TAC[evaluate_decls_def]);;

let PPASS2AUX_decl_past_exns = prove
 (`!l. ALL is_exn_decl l
       ==> !s rest. evaluate_decls (s:(A,FFI)pan_state) (CONS (Decl sh v e) (APPEND l rest)) =
                    evaluate_decls s (APPEND l (CONS (Decl sh v e) rest))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; APPEND] THEN
  NAMED_CASES_ON "h" ["fi";"sh' v' e'";"eid sh'";"nm flds"] THEN
  REWRITE_TAC[is_exn_decl_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PPASS2AUX_decl_exn_commute] THEN
  MATCH_MP_TAC PPASS2AUX_decls_cons_cong THEN ASM_REWRITE_TAC[]);;

let PPASS2AUX_fun_past = prove
 (`!l. ALL (\d. is_exn_decl d \/ is_decl d) l
       ==> !s rest. evaluate_decls (s:(A,FFI)pan_state) (CONS (Function fi) (APPEND l rest)) =
                    evaluate_decls s (APPEND l (CONS (Function fi) rest))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; APPEND] THEN
  NAMED_CASES_ON "h" ["fi'";"sh v e";"eid sh";"nm flds"] THEN
  REWRITE_TAC[is_exn_decl_def; is_decl_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PPASS2AUX_fun_exn_commute; evaluate_decl_commute] THEN
  MATCH_MP_TAC PPASS2AUX_decls_cons_cong THEN ASM_REWRITE_TAC[]);;

let evaluate_decls_one_fun_last = prove
 (CASE_TERM
  `!s. is_function y /\
       ALL (\d. match d with Decl _ _ _ -> T | ExnDecl _ _ -> T | _ -> F) xs
       ==> evaluate_decls (s:(A,FFI)pan_state) (APPEND xs [y]) = evaluate_decls s (CONS y xs)`,
  GEN_TAC THEN NAMED_CASES_ON "y" ["fi";"sh v e";"eid sh";"nm flds"] THEN
  REWRITE_TAC[is_function_def] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `xs:((A)decl)list` (GEN `l:((A)decl)list` (DISCH_ALL
    (SPECL [`s:(A,FFI)pan_state`; `[]:((A)decl)list`]
      (UNDISCH (SPEC `l:((A)decl)list` PPASS2AUX_fun_past)))))) THEN
  REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN(fun th -> CONV_TAC SYM_CONV THEN MATCH_MP_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false)) THEN
  MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN
  NAMED_CASES_ON "x" ["fi'";"sh v e";"eid sh";"nm flds"] THEN
  REWRITE_TAC[is_exn_decl_def; is_decl_def] THEN CAKE_REWRITE_TAC[]);;

let resort_decls_evaluate = prove
 (`!s decs. ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) decs
            ==> evaluate_decls (s:(A,FFI)pan_state) (resort_decls decs) =
                evaluate_decls s decs`,
  SUBGOAL_THEN
    `!decs. ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) decs
            ==> FILTER is_name decs = [] /\
                !s. evaluate_decls (s:(A,FFI)pan_state)
                      (APPEND (FILTER is_exn_decl decs)
                         (APPEND (FILTER is_decl decs) (FILTER is_function decs))) =
                    evaluate_decls s decs`
    (fun th -> REPEAT STRIP_TAC THEN
               FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th) THEN
               ASM_REWRITE_TAC[resort_decls_def; APPEND; GSYM APPEND_ASSOC]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; APPEND; ALL] THEN
  NAMED_CASES_ON "h" ["fi";"sh v e";"eid sh";"nm flds"] THEN
  REWRITE_TAC[is_function_def; is_decl_def; is_exn_decl_def; is_name_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND] THEN GEN_TAC THENL
   [MP_TAC(ISPEC `APPEND (FILTER is_exn_decl t) (FILTER is_decl (t:((A)decl)list))`
            PPASS2AUX_fun_past) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ALL_APPEND; ALL_FILTER] THEN
      CONJ_TAC THEN MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x:(A)decl. T` THEN
      REWRITE_TAC[ALL_T] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:(A,FFI)pan_state`; `FILTER is_function (t:((A)decl)list)`]) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PPASS2AUX_decls_cons_cong THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `FILTER is_exn_decl (t:((A)decl)list)` PPASS2AUX_decl_past_exns) THEN
    REWRITE_TAC[ALL_FILTER; ALL_T] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:(A,FFI)pan_state`;
      `APPEND (FILTER is_decl t) (FILTER is_function (t:((A)decl)list))`]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PPASS2AUX_decls_cons_cong THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PPASS2AUX_decls_cons_cong THEN ASM_REWRITE_TAC[]]);;

let resort_decls_evaluate_IMP = prove
 (`evaluate_decls (s:(A,FFI)pan_state) decs = SOME s' /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) decs
   ==> evaluate_decls s (resort_decls decs) = SOME s'`,
  MESON_TAC[resort_decls_evaluate]);;

let compile_decs_functions_thm = prove
 (CASE_TERM
  `!ctxt fdecs decls funs exns ctxt'.
     pan_globals_compile_decs (ctxt:(A)pan_globals_context) fdecs =
       (decls,funs,exns,ctxt') /\
     ALL is_function fdecs
     ==> decls = [] /\ exns = [] /\ ctxt' = ctxt /\
         funs = MAP (\x. match x with
                           Function fi ->
                             Function (fun_decl_body_fupd
                                         (combin_K (pan_globals_compile ctxt (fun_decl_body fi))) fi)
                         | _ -> ARB) fdecs`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW(pan_globals_compile_decs_def::is_function_def::MAP::ALL::all_case_eqs()) THEN
  GVS(is_function_def::all_case_eqs()));;

let compile_decs_decls_thm = prove
 (`!ctxt fdecs decls funs exns ctxt'.
     pan_globals_compile_decs (ctxt:(A)pan_globals_context) fdecs =
       (decls,funs,exns,ctxt') /\
     ALL (\d. ~is_function d) fdecs
     ==> funs = []`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW(pan_globals_compile_decs_def::is_function_def::is_exn_decl_def::ALL::
     all_case_eqs()) THEN
  GVS(is_function_def::all_case_eqs()));;

let compile_decs_EVERY_is_function = prove
 (`!ctxt decs decls funs exns ctxt'.
     pan_globals_compile_decs (ctxt:(A)pan_globals_context) decs =
       (decls,funs,exns,ctxt')
     ==> ALL is_function funs`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW(pan_globals_compile_decs_def::is_function_def::is_exn_decl_def::ALL::
     all_case_eqs()) THEN
  GVS(is_function_def::ALL::all_case_eqs()));;

let compile_decs_EVERY = prove
 (`!ctxt decs decls funs exns ctxt'.
     pan_globals_compile_decs (ctxt:(A)pan_globals_context) decs =
       (decls,funs,exns,ctxt') /\
     ALL (\d. !fi ctxt. d = Function fi
                        ==> P (Function (fun_decl_body_fupd
                                (combin_K (pan_globals_compile ctxt (fun_decl_body fi))) fi))) decs
     ==> ALL P funs`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW(pan_globals_compile_decs_def::is_function_def::ALL::all_case_eqs()) THEN
  GVS(is_function_def::ALL::injectivity "decl"::all_case_eqs()));;

(* a case split on each compile_decs of a list variable in the goal *)

let PPASS2AUX_split_cd_tac : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t ->
      is_comb t && is_var (rand t) &&
      (let h,args = strip_comb t in
       is_const h && fst(dest_const h) = "pan_globals_compile_decs" &&
       length args = 2)) w in
  PAIR_CASES_ON tm g;;

let compile_decls_append = prove
 (CASE_TERM
  `!decs' ctxt decs:((A)decl)list.
     pan_globals_compile_decs ctxt (APPEND decs decs') =
     let (decls,funs,exns,ctxt') = pan_globals_compile_decs ctxt decs in
     let (decls',funs',exns',ctxt'') = pan_globals_compile_decs ctxt' decs' in
     (APPEND decls decls',APPEND funs funs',APPEND exns exns',ctxt'')`,
  GEN_TAC THEN REC_IND_TAC pan_globals_compile_decs_ind THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[APPEND; pan_globals_compile_decs_def] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT(PPASS2AUX_split_cd_tac THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
  REWRITE_TAC[APPEND]);;

let compile_decls_append_IMP = prove
 (CASE_TERM
  `pan_globals_compile_decs ctxt (APPEND decs decs') = X
   ==> let (decls,funs,exns,ctxt') = pan_globals_compile_decs ctxt decs in
       let (decls',funs',exns',ctxt'') =
         pan_globals_compile_decs ctxt' (decs':((A)decl)list) in
       (APPEND decls decls',APPEND funs funs',APPEND exns exns',ctxt'') = X`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[compile_decls_append] THEN
  REPEAT(PPASS2AUX_split_cd_tac THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]));;

let fperm_decs_decls = prove
 (`!f g xs (ys:B). ALL ((~) o is_function) xs ==> fperm_decs f g xs = xs:((A)decl)list`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; is_function_def; ALL; o_THM]);;

let fperm_decs_FILTER_is_function = prove
 (`!f g decs:((A)decl)list.
     fperm_decs f g (FILTER is_function decs) = FILTER is_function (fperm_decs f g decs)`,
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; is_function_def; FILTER]);;

let functions_FILTER_exn_decl = prove
 (`!prog:((A)decl)list. functions (FILTER is_exn_decl prog) = []`,
  REC_IND_TAC (cake_ind "functions") THEN RW[functions_def; is_exn_decl_def; FILTER]);;

let functions_FILTER_is_name = prove
 (`!prog:((A)decl)list. functions (FILTER is_name prog) = []`,
  REC_IND_TAC (cake_ind "functions") THEN RW[functions_def; is_name_def; FILTER]);;

let resort_decls_preserve_functions = prove
 (`!code:((A)decl)list. functions (resort_decls code) = functions code`,
  REWRITE_TAC[resort_decls_def; functions_append; functions_FILTER'; functions_FILTER;
              functions_FILTER_exn_decl; functions_FILTER_is_name; APPEND]);;

let compile_decs_preserve_functions = prove
 (`!code ctxt decs funs exns ctxt'.
     pan_globals_compile_decs (ctxt:(A)pan_globals_context) code =
       (decs,funs,exns,ctxt')
     ==> MAP FST (functions funs) = MAP FST (functions code)`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW(pan_globals_compile_decs_def::functions_def::MAP::all_case_eqs()) THEN
  ASM_MESON_TAC[]);;

let new_main_name_correct = prove
 (`MEM (new_main_name (code:((A)decl)list)) (MAP FST (functions code)) ==> F`,
  REWRITE_TAC[new_main_name_def] THEN MESON_TAC[fresh_name_correct]);;

let mem_stores_addrs_IS_SOME = prove
 (`!addr' ws memaddrs (mem:A word->(A)word_lab).
     addresses addr' (LENGTH ws) SUBSET memaddrs
     ==> ?m. mem_stores addr' ws memaddrs mem = SOME m`,
  QINDUCT_ON "ws" THEN
  RW[addresses_def; mem_stores_def; pan_mem_store_def; LENGTH; INSERT_SUBSET] THEN
  ASM_MESON_TAC[]);;

(* the same statement as stack_removeProof's byte_aligned_bytes_in_word_MULT *)

let byte_aligned_bytes_in_word_mul = prove
 (`good_dimindex(:A) ==> byte_aligned (word_mul (bytes_in_word:A word) x)`,
  MESON_TAC[byte_aligned_bytes_in_word_MULT]);;

let eval_state_rel_is_wf_shape = prove
 (CASE_TERM
  `pan_eval s exp = SOME (v:(A)pan_v) /\
   pan_globalsProof_state_rel b ctxt (s:(A,FFI)pan_state) t /\
   FEVERY (\p. match p with (nm,v) -> is_wf_shape_v (pan_state_structs s) v)
          (pan_state_locals s)
   ==> is_wf_shape ([]:(mlstring#struct_info)list) (shape_of v)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `pan_state_structs (s:(A,FFI)pan_state) = []` ASSUME_TAC THENL
   [ASM_MESON_TAC[pan_globalsProof_state_rel_structs]; ALL_TAC] THEN
  MATCH_MP_TAC is_wf_shape_of_v THEN
  SUBGOAL_THEN `is_wf_shape_v (pan_state_structs (s:(A,FFI)pan_state)) (v:(A)pan_v)`
    MP_TAC THENL
   [MATCH_MP_TAC eval_is_wf_shape_v THEN EXISTS_TAC `exp:(A)panLang_exp` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[FEVERY_ALL_FLOOKUP] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CAKE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_state_rel_global o
      CONJ (ASSUME `pan_globalsProof_state_rel b ctxt (s:(A,FFI)pan_state) t`)) THEN
    MESON_TAC[is_wf_shape_v_nil];
    ASM_REWRITE_TAC[]]);;

let PPASS2AUX_split_top_tac : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t ->
      is_comb t &&
      (let h,args = strip_comb t in
       is_const h && fst(dest_const h) = "pan_globals_compile_decs" &&
       length args = 2)) w in
  PAIR_CASES_ON tm g;;

let PPASS2AUX_free_split = prove
 (`!(top:A word) g m r.
     addresses (word_sub (word_sub top (word_mul bytes_in_word (word (m + r)))) g) (m + r) =
     addresses (word_sub (word_sub top (word_mul bytes_in_word (word r)))
                         (word_add g (word_mul bytes_in_word (word m)))) r UNION
     addresses (word_sub top (word_add g (word_mul bytes_in_word (word m)))) m`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ADD_SYM] THEN
  REWRITE_TAC[PPASS2AUX_addresses_add] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE);;

let PPASS2AUX_free_disjoint = prove
 (`!(top:A word) g m r.
     good_dimindex(:A) /\ val(bytes_in_word:A word) * (r + m) < dimword(:A)
     ==> DISJOINT
           (addresses (word_sub (word_sub top (word_mul bytes_in_word (word r)))
                                (word_add g (word_mul bytes_in_word (word m)))) r)
           (addresses (word_sub top (word_add g (word_mul bytes_in_word (word m)))) m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DISJOINT_addresses_lemma THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

let PPASS2AUX_disjoint_globals_update = prove
 (`!(top:A word) cg (gl:(mlstring,B)fmap) v sh a value.
     disjoint_globals top cg gl /\
     (!v' sh' a'. ~(v' = v) /\ IS_SOME (FLOOKUP gl v') /\ FLOOKUP cg v' = SOME (sh',a')
                  ==> DISJOINT (addresses (word_sub top a') (size_of_shape sh'))
                               (addresses (word_sub top a) (size_of_shape sh)))
     ==> disjoint_globals top (cg |+ (v,(sh,a))) (gl |+ (v,value))`,
  REWRITE_TAC[disjoint_globals_def; FLOOKUP_UPDATE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`v1:mlstring`; `v2:mlstring`; `sh1:shape`; `a1:A word`;
                       `sh2:shape`; `a2:A word`] THEN
  ASM_CASES_TAC `v:mlstring = v1` THEN ASM_CASES_TAC `v:mlstring = v2` THEN
  ASM_REWRITE_TAC[IS_SOME_DEF; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[DISJOINT_SYM]);;

let PPASS2AUX_state_rel_new_global = prove
 (`pan_globalsProof_state_rel F ctxt (s:(A,FFI)pan_state) t /\
   is_wf_shape ([]:(mlstring#struct_info)list) (shape_of value) /\
   mem_stores (word_sub (pan_state_top_addr t) a) (flatten value) (pan_state_memaddrs t)
     (pan_state_memory t) = SOME mm /\
   byte_aligned a /\ pan_state_code s = FEMPTY /\
   DISJOINT (pan_state_memaddrs s)
     (addresses (word_sub (pan_state_top_addr t) a) (size_of_shape (shape_of value))) /\
   (!v' sh' a'. ~(v' = v) /\ IS_SOME (FLOOKUP (pan_state_globals s) v') /\
                FLOOKUP (pan_globals_context_globals ctxt) v' = SOME (sh',a')
                ==> DISJOINT (addresses (word_sub (pan_state_top_addr t) a') (size_of_shape sh'))
                      (addresses (word_sub (pan_state_top_addr t) a)
                                 (size_of_shape (shape_of value))))
   ==> pan_globalsProof_state_rel F
         (pan_globals_context_globals_fupd
            (combin_K (pan_globals_context_globals ctxt |+ (v,(shape_of value,a))))
            (pan_globals_context_globals_size_fupd (combin_K gs) ctxt))
         (pan_state_globals_fupd (combin_K (pan_state_globals s |+ (v,value))) s)
         (pan_state_memory_fupd (combin_K mm) t)`,
  STRIP_TAC THEN
   MP_TAC(ASSUME `pan_globalsProof_state_rel F ctxt (s:(A,FFI)pan_state) t`) THEN
   REWRITE_TAC[pan_globalsProof_state_rel_def] THEN STRIP_TAC THEN
   SUBGOAL_THEN `LENGTH (flatten (value:(A)pan_v)) = size_of_shape (shape_of value)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC length_flatten_eq_size_of_shape THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `LENGTH (flatten (value:(A)pan_v)) * val(bytes_in_word:A word) < dimword(:A)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC PPASS2AUX_store_bound THEN
     MAP_EVERY EXISTS_TAC [`pan_state_top_addr (t:(A,FFI)pan_state)`; `a:A word`;
       `pan_state_memaddrs (t:(A,FFI)pan_state)`; `pan_state_memory (t:(A,FFI)pan_state)`;
       `mm:A word->(A)word_lab`] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[pan_globalsProof_state_rel_def; pan_state_INFO.ri_accfupds;
               pan_globals_context_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
    [MAP_EVERY X_GEN_TAC [`v':mlstring`; `value':(A)pan_v`] THEN
     REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
      [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[injectivity "option"] THEN
       DISCH_THEN(SUBST_ALL_TAC o SYM) THEN EXISTS_TAC `a:A word` THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC (CONJUNCT1 mem_stores_mem_load_back) THEN
       EXISTS_TAC `pan_state_memory (t:(A,FFI)pan_state)` THEN ASM_REWRITE_TAC[];
       DISCH_TAC THEN
       FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
         `FLOOKUP (pan_state_globals (s:(A,FFI)pan_state)) v' = SOME (value':(A)pan_v)`))) THEN
       DISCH_THEN(X_CHOOSE_THEN `addr:A word` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `addr:A word` THEN ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
         can (find_term ((=) `pan_state_memory (t:(A,FFI)pan_state)`)) (lhs (concl th)))) THEN
       MATCH_MP_TAC (CONJUNCT1 mem_stores_load_disjoint) THEN
       MAP_EVERY EXISTS_TAC [`word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) a`;
                             `flatten (value:(A)pan_v)`] THEN
       ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       EXISTS_TAC `v':mlstring` THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[]];
     MATCH_MP_TAC (CONJUNCT2 (SPEC_ALL FEVERY_STRENGTHEN_THM)) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `addr:A word` THEN DISCH_TAC THEN
     MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `pan_state_memory (t:(A,FFI)pan_state) addr` THEN
     CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC mem_stores_lookup THEN
     MAP_EVERY EXISTS_TAC [`word_sub (pan_state_top_addr (t:(A,FFI)pan_state)) a`;
                           `flatten (value:(A)pan_v)`; `pan_state_memaddrs (t:(A,FFI)pan_state)`] THEN
     ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
     ASM_REWRITE_TAC[FLOOKUP_EMPTY; distinctness "option"];
     MATCH_MP_TAC PPASS2AUX_disjoint_globals_update THEN ASM_REWRITE_TAC[]]);;
let PPASS2AUX_DISJOINT_UNION_R = prove
 (`!s t u:A->bool. DISJOINT s (t UNION u) <=> DISJOINT s t /\ DISJOINT s u`,
  SET_TAC[]);;

let PPASS2AUX_globals_disj_asm =
  check (fun th -> is_forall (concl th) &&
                   can (find_term (fun t -> try fst(dest_const t) = "IS_SOME" with Failure _ -> false))
                       (concl th) &&
                   can (find_term (fun t -> try fst(dest_const t) = "DISJOINT" with Failure _ -> false))
                       (concl th));;

let PPASS2AUX_disj_memaddrs_asm =
  check (fun th -> try let c = concl th in
                       let f,args = strip_comb c in
                       fst(dest_const f) = "DISJOINT" &&
                       fst(dest_const(fst(strip_comb(hd args)))) = "pan_state_memaddrs"
                   with Failure _ -> false);;

let PPASS2AUX_subset_memaddrs_asm =
  check (fun th -> try let c = concl th in
                       let f,args = strip_comb c in
                       fst(dest_const f) = "SUBSET" &&
                       fst(dest_const(fst(strip_comb(el 1 args)))) = "pan_state_memaddrs"
                   with Failure _ -> false);;

let evaluate_decls_init_globals_lemma = prove
 (`!s decls s' decls' funs exns ctxt' ctxt t free_addrs.
    evaluate_decls (s:(A,FFI)pan_state) decls = SOME s' /\
    ALL is_decl decls /\
    pan_globals_compile_decs ctxt decls = (decls',funs,exns,ctxt') /\
    pan_globalsProof_state_rel F ctxt s t /\
    free_addrs =
      addresses (word_sub (word_sub (pan_state_top_addr t)
                   (word_mul bytes_in_word (word (SUM (MAP size_of_shape (dec_shapes decls))))))
                   (pan_globals_context_globals_size ctxt))
                (SUM (MAP size_of_shape (dec_shapes decls))) /\
    DISJOINT (pan_state_memaddrs s) free_addrs /\
    free_addrs SUBSET pan_state_memaddrs t /\
    byte_aligned (pan_globals_context_globals_size ctxt) /\
    pan_state_code s = FEMPTY /\
    (!v sh addr'. IS_SOME (FLOOKUP (pan_state_globals s) v) /\
                  FLOOKUP (pan_globals_context_globals ctxt) v = SOME (sh,addr')
                  ==> DISJOINT (addresses (word_sub (pan_state_top_addr t) addr')
                                          (size_of_shape sh)) free_addrs) /\
    val(bytes_in_word:A word) * SUM (MAP size_of_shape (dec_shapes decls)) < dimword(:A)
    ==> ?t'. pan_evaluate (nested_seq decls',t) = (NONE,t') /\
             pan_globalsProof_state_rel F ctxt' s' t' /\
             pan_state_clock t' = pan_state_clock t /\
             pan_state_ffi t' = pan_state_ffi t /\
             pan_state_locals t' = pan_state_locals t /\
             byte_aligned (pan_globals_context_globals_size ctxt')`,
  REC_IND_TAC evaluate_decls_ind THEN
   REWRITE_TAC[evaluate_decls_def; ALL; is_decl_def] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
   REWRITE_TAC[pan_globals_compile_decs_def; injectivity "option"; PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `t:(A,FFI)pan_state` THEN
   ASM_REWRITE_TAC[nested_seq_def; pan_evaluate_def];
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     lhs (concl th) = `free_addrs:A word->bool`)) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `SOME (s':(A,FFI)pan_state)`)) THEN
   QCASES_ON "pan_eval (pan_state_locals_fupd (combin_K FEMPTY) s) e" THEN
   CAKE_REWRITE_TAC[distinctness "option"] THEN
   RENAME1 "pan_eval (pan_state_locals_fupd (combin_K FEMPTY) s) e = SOME value" THEN
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "pan_globals_compile_decs"
                              with Failure _ -> false)) (lhs (concl th)))) THEN
   REWRITE_TAC[pan_globals_compile_decs_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   PPASS2AUX_split_top_tac THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `SUM (MAP size_of_shape (dec_shapes (CONS (Decl (shape_of value) v e) ds))) =
                 size_of_shape (shape_of (value:(A)pan_v)) +
                 SUM (MAP size_of_shape (dec_shapes (ds:((A)decl)list)))`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
    [REWRITE_TAC[dec_shapes_def; MAP; SUM]; ALL_TAC] THEN
   SUBGOAL_THEN `is_wf_shape ([]:(mlstring#struct_info)list) (shape_of (value:(A)pan_v))`
     ASSUME_TAC THENL
    [MP_TAC(INST [`pan_state_locals_fupd (combin_K FEMPTY) (s:(A,FFI)pan_state)`,`s:(A,FFI)pan_state`;
                  `e:(A)panLang_exp`,`exp:(A)panLang_exp`; `T`,`b:bool`;
                  `pan_state_locals_fupd (combin_K FEMPTY) (t:(A,FFI)pan_state)`,`t:(A,FFI)pan_state`;
                  `value:(A)pan_v`,`v:(A)pan_v`] eval_state_rel_is_wf_shape) THEN
     DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; FEVERY_FEMPTY] THEN
     MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `pan_eval (t:(A,FFI)pan_state) (pan_globals_compile_exp ctxt e) = SOME (value:(A)pan_v)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] eval_empty_locals_IMP) THEN
     MATCH_MP_TAC pan_globalsProof_compile_exp_correct THEN
     EXISTS_TAC `pan_state_locals_fupd (combin_K FEMPTY) (s:(A,FFI)pan_state)` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC (CONJUNCT2 state_rel_change_locals) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MP_TAC(ISPECL [`pan_state_top_addr (t:(A,FFI)pan_state)`;
                  `pan_globals_context_globals_size (ctxt:(A)pan_globals_context)`;
                  `size_of_shape (shape_of (value:(A)pan_v))`;
                  `SUM (MAP size_of_shape (dec_shapes (ds:((A)decl)list)))`]
                 PPASS2AUX_free_split) THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   SUBGOAL_THEN `LENGTH (flatten (value:(A)pan_v)) = size_of_shape (shape_of value)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC length_flatten_eq_size_of_shape THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `?mm. mem_stores (word_sub (pan_state_top_addr t)
                        (word_add (pan_globals_context_globals_size ctxt)
                           (word_mul bytes_in_word (word (size_of_shape (shape_of value))))))
             (flatten (value:(A)pan_v)) (pan_state_memaddrs (t:(A,FFI)pan_state))
             (pan_state_memory t) = SOME mm`
     STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC mem_stores_addrs_IS_SOME THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
     `pan_evaluate (panLang_Store (panLang_Op asm_Sub [TopAddr; panLang_Const
                      (word_add (pan_globals_context_globals_size ctxt)
                        (word_mul bytes_in_word (word (size_of_shape (shape_of (value:(A)pan_v))))))])
                    (pan_globals_compile_exp ctxt e), t) =
      (NONE, pan_state_memory_fupd (combin_K (mm:A word->(A)word_lab)) (t:(A,FFI)pan_state))` ASSUME_TAC THENL
    [SIMP[pan_evaluate_def; pan_eval_def; OPT_MMAP_def; OPTION_BIND_DEF; OPTION_MAP_DEF;
          word_op_def];
     ALL_TAC] THEN
   REWRITE_TAC[nested_seq_def; PPASS2AUX_evaluate_Seq] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `byte_aligned (word_add (pan_globals_context_globals_size ctxt)
                     (word_mul bytes_in_word (word (size_of_shape (shape_of (value:(A)pan_v)))))
                    :A word)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC byte_aligned_add THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC byte_aligned_bytes_in_word_mul THEN
     ASM_MESON_TAC[pan_globalsProof_state_rel_def];
     ALL_TAC] THEN
   REMOVE_THEN "ih" (MP_TAC o SPEC `value:(A)pan_v`) THEN REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL
     [`s':(A,FFI)pan_state`; `p0:((A)panLang_prog)list`; `funs:((A)decl)list`;
      `exns:((A)decl)list`; `ctxt':(A)pan_globals_context`;
      `pan_globals_context_globals_fupd
         (combin_K (pan_globals_context_globals ctxt |+
             (v,shape_of (value:(A)pan_v),
              word_add (pan_globals_context_globals_size ctxt)
                (word_mul bytes_in_word (word (size_of_shape (shape_of value)))))))
         (pan_globals_context_globals_size_fupd
            (combin_K (word_add (pan_globals_context_globals_size ctxt)
                  (word_mul bytes_in_word (word (size_of_shape (shape_of value))))))
            (ctxt:(A)pan_globals_context))`;
      `pan_state_memory_fupd (combin_K (mm:A word->(A)word_lab)) (t:(A,FFI)pan_state)`;
      `addresses (word_sub (word_sub (pan_state_top_addr (t:(A,FFI)pan_state))
          (word_mul bytes_in_word (word (SUM (MAP size_of_shape (dec_shapes (ds:((A)decl)list)))))))
          (word_add (pan_globals_context_globals_size ctxt)
             (word_mul bytes_in_word (word (size_of_shape (shape_of (value:(A)pan_v)))))))
          (SUM (MAP size_of_shape (dec_shapes ds)))`]) THEN
   REWRITE_TAC[pan_state_INFO.ri_accfupds; pan_globals_context_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
      [MP_TAC(ASSUME `pan_globalsProof_state_rel F ctxt (s:(A,FFI)pan_state) t`) THEN
       REWRITE_TAC[pan_globalsProof_state_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PPASS2AUX_state_rel_new_global THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
          [FIRST_ASSUM(MP_TAC o PPASS2AUX_disj_memaddrs_asm) THEN
           ONCE_REWRITE_TAC[DISJOINT_SYM] THEN REWRITE_TAC[DISJOINT_UNION] THEN SIMP_TAC[];
           MAP_EVERY X_GEN_TAC [`v':mlstring`; `sh':shape`; `a':A word`] THEN STRIP_TAC THEN
           FIRST_X_ASSUM(MP_TAC o SPECL [`v':mlstring`; `sh':shape`; `a':A word`] o
                         PPASS2AUX_globals_disj_asm) THEN
           ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
           REWRITE_TAC[DISJOINT_UNION] THEN SIMP_TAC[]];
        FIRST_ASSUM(MP_TAC o PPASS2AUX_disj_memaddrs_asm) THEN
         ONCE_REWRITE_TAC[DISJOINT_SYM] THEN REWRITE_TAC[DISJOINT_UNION] THEN SIMP_TAC[];
        FIRST_ASSUM(MP_TAC o PPASS2AUX_subset_memaddrs_asm) THEN
         REWRITE_TAC[UNION_SUBSET] THEN SIMP_TAC[];
        MAP_EVERY X_GEN_TAC [`v':mlstring`; `sh':shape`; `a':A word`] THEN
         REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THEN
         REWRITE_TAC[IS_SOME_DEF; injectivity "option"; PAIR_EQ] THENL
          [DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
           ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
           MP_TAC(ISPECL [`pan_state_top_addr (t:(A,FFI)pan_state)`;
                          `pan_globals_context_globals_size (ctxt:(A)pan_globals_context)`;
                          `size_of_shape (shape_of (value:(A)pan_v))`;
                          `SUM (MAP size_of_shape (dec_shapes (ds:((A)decl)list)))`]
                         PPASS2AUX_free_disjoint) THEN
           ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
           STRIP_TAC THEN
           FIRST_X_ASSUM(MP_TAC o SPECL [`v':mlstring`; `sh':shape`; `a':A word`] o
                         PPASS2AUX_globals_disj_asm) THEN
           ASM_REWRITE_TAC[PPASS2AUX_DISJOINT_UNION_R] THEN SIMP_TAC[]];
        MATCH_MP_TAC LET_TRANS THEN
         EXISTS_TAC `val(bytes_in_word:A word) * (size_of_shape (shape_of (value:(A)pan_v)) +
                       SUM (MAP size_of_shape (dec_shapes (ds:((A)decl)list))))` THEN
         ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `t':(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
       EXISTS_TAC `t':(A,FFI)pan_state` THEN
       ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM]]]);;

let dec_shapes_append = prove
 (`!xs ys:((A)decl)list.
     dec_shapes (APPEND xs ys) = APPEND (dec_shapes xs) (dec_shapes ys)`,
  REC_IND_TAC dec_shapes_ind THEN RW[dec_shapes_def; APPEND]);;

let dec_shapes_functions = prove
 (`!xs:((A)decl)list. ALL is_function xs ==> dec_shapes xs = []`,
  REC_IND_TAC dec_shapes_ind THEN RW[dec_shapes_def; is_function_def; ALL]);;

let dec_shapes_FILTER = prove
 (`(!xs:((A)decl)list. dec_shapes (FILTER ((~) o is_function) xs) = dec_shapes xs) /\
   (!xs:((A)decl)list. dec_shapes (FILTER is_name xs) = []) /\
   (!xs:((A)decl)list. dec_shapes (FILTER is_decl xs) = dec_shapes xs) /\
   (!xs:((A)decl)list. dec_shapes (FILTER is_exn_decl xs) = [])`,
  REPEAT CONJ_TAC THEN REC_IND_TAC dec_shapes_ind THEN
  RW[dec_shapes_def; is_function_def; is_decl_def; is_name_def; is_exn_decl_def;
     FILTER; o_THM]);;

let dec_shapes_fperm_decs = prove
 (`!xs:((A)decl)list. dec_shapes (fperm_decs f g xs) = dec_shapes xs`,
  REC_IND_TAC dec_shapes_ind THEN RW[dec_shapes_def; fperm_decs_def]);;

let dec_shapes_resort_decls_def = prove
 (`!xs:((A)decl)list. dec_shapes (resort_decls xs) = dec_shapes xs`,
  RW[resort_decls_def; dec_shapes_append; dec_shapes_FILTER] THEN
  SUBGOAL_THEN `dec_shapes (FILTER is_function (xs:((A)decl)list)) = []` SUBST1_TAC THENL
   [MATCH_MP_TAC dec_shapes_functions THEN REWRITE_TAC[ALL_FILTER; ALL_T]; ALL_TAC] THEN
  REWRITE_TAC[APPEND; APPEND_NIL]);;

let evaluate_decls_functions_wf = prove
 (`!s decs.
     evaluate_decls (s:(A,FFI)pan_state) decs = SOME s' /\
     MEM (Function fi) decs /\
     ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) decs
     ==> ALL (is_wf_shape (pan_state_structs s) o SND) (fun_decl_params fi) /\
         is_wf_shape (pan_state_structs s) (fun_decl_return fi)`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW(evaluate_decls_def::MEM::ALL::is_function_def::is_decl_def::is_exn_decl_def::
     is_name_def::injectivity "decl"::all_case_eqs()) THEN
  RES_TAC THEN FS[]);;

let MEM_functions = prove
 (`!decs:((A)decl)list.
     MEM t (functions decs)
     ==> ?fi. MEM (Function fi) decs /\
              t = (fun_decl_name fi,fun_decl_params fi,fun_decl_body fi,
                   fun_decl_return fi)`,
  REC_IND_TAC (cake_ind "functions") THEN RW[functions_def; MEM] THEN
  ASM_MESON_TAC[]);;

let evaluate_decls_only_functions_SOME = prove
 (`!s pan_code.
     ALL is_function pan_code /\
     ALL (\d. !fi. d = Function fi
                   ==> ALL (is_wf_shape (pan_state_structs s) o SND) (fun_decl_params fi) /\
                       is_wf_shape (pan_state_structs s) (fun_decl_return fi)) pan_code
     ==> evaluate_decls (s:(A,FFI)pan_state) pan_code =
         SOME (pan_state_code_fupd (combin_K (pan_state_code s |++ functions pan_code)) s)`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; is_function_def; functions_def; FUPDATE_LIST_THM; ALL;
     injectivity "decl"; record_fupdselfid "pan_state"]);;

let evaluate_decls_only_functions_and_exns_SOME = prove
 (`!s pan_code.
     ALL (\d. is_function d \/ is_exn_decl d) pan_code /\
     ALL (\d. !fi. d = Function fi
                   ==> ALL (is_wf_shape (pan_state_structs s) o SND) (fun_decl_params fi) /\
                       is_wf_shape (pan_state_structs s) (fun_decl_return fi)) pan_code /\
     ALL_DISTINCT (MAP FST (exceptions pan_code)) /\
     ALL (\(eid,sh). FLOOKUP (pan_state_eshapes s) eid = NONE) (exceptions pan_code) /\
     ALL (is_wf_shape (pan_state_structs s) o SND) (exceptions pan_code)
     ==> evaluate_decls (s:(A,FFI)pan_state) pan_code =
         SOME (pan_state_code_fupd (combin_K (pan_state_code s |++ functions pan_code))
                 (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions pan_code)) s))`,
  REC_IND_TAC evaluate_decls_ind THEN
  RW[evaluate_decls_def; is_function_def; functions_def; exceptions_def; is_exn_decl_def;
     FUPDATE_LIST_THM; ALL; injectivity "decl"; record_fupdselfid "pan_state"] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\(eid,sh). FLOOKUP (pan_state_eshapes (s:(A,FFI)pan_state)) eid = NONE)
                   (exceptions (ds:((A)decl)list))` THEN
  UNDISCH_TAC `~MEM (eid:mlstring) (MAP FST (exceptions (ds:((A)decl)list)))` THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; MEM_MAP; EXISTS_PAIR_THM; FLOOKUP_UPDATE] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN MESON_TAC[]);;

let EVERY_fperm_decs = prove
 (`!f g decs:((A)decl)list.
     ALL (\d. ~is_function d ==> P d) decs /\
     ALL (\d. !fi. d = Function fi
                   ==> P (Function (fun_decl_name_fupd (combin_K (fperm_name f g (fun_decl_name fi)))
                                     (fun_decl_body_fupd (combin_K (fperm f g (fun_decl_body fi)))
                                        fi)))) decs
     ==> ALL P (fperm_decs f g decs)`,
  REC_IND_TAC fperm_decs_ind THEN
  RW[fperm_decs_def; is_function_def; ALL; injectivity "decl"]);;

let compile_decs_exns_are_exns = prove
 (`!ctxt code decls funs exns ctxt'.
     pan_globals_compile_decs (ctxt:(A)pan_globals_context) code =
       (decls,funs,exns,ctxt')
     ==> exns = FILTER is_exn_decl code`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW(pan_globals_compile_decs_def::is_exn_decl_def::FILTER::all_case_eqs()) THEN
  ASM_MESON_TAC[]);;

let compile_top_shape_wf = prove
 (`evaluate_decls (s:(A,FFI)pan_state) code = SOME s' /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) code
   ==> ALL (\d. !fi. d = Function fi
                ==> ALL (is_wf_shape (pan_state_structs s) o SND) (fun_decl_params fi) /\
                    is_wf_shape (pan_state_structs s) (fun_decl_return fi))
           (pan_globals_compile_top code start)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `!fi. MEM (Function fi) (code:((A)decl)list)
                ==> ALL (is_wf_shape (pan_state_structs (s:(A,FFI)pan_state)) o SND)
                        (fun_decl_params fi) /\
                    is_wf_shape (pan_state_structs s) (fun_decl_return fi)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEN_ALL evaluate_decls_functions_wf]; ALL_TAC] THEN
  SUBGOAL_THEN `ALOOKUP (functions (code:((A)decl)list)) (start:mlstring) = NONE \/
                ?args body rshape.
                  ALOOKUP (functions code) start = SOME (args,body,rshape)`
    MP_TAC THENL [MESON_TAC[option_CASES; PAIR]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[pan_globals_compile_top_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PPASS2AUX_split_top_tac THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ALL_APPEND; ALL] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
    REWRITE_TAC[ALL_FILTER; GSYM ALL_MEM] THEN BETA_TAC THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `is_exn_decl (x:(A)decl)` THEN
    ASM_REWRITE_TAC[is_exn_decl_def];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `ALL (is_wf_shape (pan_state_structs (s:(A,FFI)pan_state)) o SND)
                      (args:(mlstring#shape)list) /\
                  is_wf_shape (pan_state_structs s) rshape` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP MEM_functions o MATCH_MP ALOOKUP_MEM) THEN
      REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(X_CHOOSE_THEN `fi:(A)fun_decl` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[injectivity "decl"] THEN GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN RW[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d. MEM d (resort_decls code) ==> MEM (d:(A)decl) code` ASSUME_TAC THENL
   [REWRITE_TAC[resort_decls_def; MEM_APPEND; MEM_FILTER] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] (GEN_ALL compile_decs_EVERY))) THEN
  IRULE EVERY_fperm_decs THEN
  ONCE_REWRITE_TAC[GSYM ALL_MEM] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  GVS[is_function_def; injectivity "decl"]);;

let compile_top_shape_wf_nil = prove
 (`evaluate_decls (s:(A,FFI)pan_state) code = SOME s' /\
   pan_state_structs s = [] /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) code
   ==> ALL (\d. !fi. d = Function fi
                ==> ALL (is_wf_shape ([]:(mlstring#struct_info)list) o SND)
                        (fun_decl_params fi) /\
                    is_wf_shape ([]:(mlstring#struct_info)list) (fun_decl_return fi))
           (pan_globals_compile_top code start)`,
  STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC compile_top_shape_wf THEN ASM_MESON_TAC[]);;

let exceptions_append = prove
 (`!ds ds':((A)decl)list.
     exceptions (APPEND ds ds') = APPEND (exceptions ds) (exceptions ds')`,
  REC_IND_TAC (cake_ind "exceptions") THEN RW[exceptions_def; APPEND]);;

let exceptions_FILTER_is_function = prove
 (`exceptions (FILTER is_function (decs:((A)decl)list)) = [] /\
   exceptions (FILTER ((~) o is_function) decs) = exceptions decs /\
   exceptions (FILTER is_exn_decl decs) = exceptions decs /\
   exceptions (FILTER is_name decs) = [] /\
   exceptions (FILTER is_decl decs) = []`,
  SPEC_TAC(`decs:((A)decl)list`,`decs:((A)decl)list`) THEN
  REWRITE_TAC[GSYM FORALL_AND_THM] THEN
  REC_IND_TAC (cake_ind "exceptions") THEN
  RW[exceptions_def; is_function_def; is_exn_decl_def; is_name_def; is_decl_def; FILTER;
     o_THM]);;

let not_is_function = prove
 (`(is_name x ==> ~is_function x) /\
   (is_decl x ==> ~is_function x) /\
   (is_exn_decl (x:(A)decl) ==> ~is_function x)`,
  QCASES_ON "x" THEN REWRITE_TAC[is_name_def; is_decl_def; is_exn_decl_def; is_function_def]);;

let pan_globalsProof_decl_distinct = prove
 (`(is_decl x /\ is_name x <=> F) /\
   (is_decl x /\ is_function x <=> F) /\
   (is_decl (x:(A)decl) /\ is_exn_decl x <=> F)`,
  QCASES_ON "x" THEN REWRITE_TAC[is_name_def; is_decl_def; is_exn_decl_def; is_function_def]);;

let PPASS2AUX_exceptions_fperm_decs = prove
 (`!f g decs:((A)decl)list. exceptions (fperm_decs f g decs) = exceptions decs`,
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; exceptions_def]);;

let PPASS2AUX_functions_compile_map = prove
 (CASE_TERM
  `!fs:((A)decl)list.
     ALL is_function fs
     ==> functions (MAP (\x. match x with
                               Function fi ->
                                 Function (fun_decl_body_fupd
                                   (combin_K (pan_globals_compile ctxt (fun_decl_body fi))) fi)
                             | _ -> ARB) fs) =
         MAP (\(x,y,z,t). (x,y,pan_globals_compile ctxt z,t)) (functions fs)`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; MAP; ALL; is_function_def; fun_decl_INFO.ri_accfupds; K_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let PPASS2AUX_compile_decs_funs_last = prove
 (`!xs ctxt decls exns ys funs ctxt'.
   ALL ((~) o is_function) xs /\ ALL is_function ys /\
   pan_globals_compile_decs ctxt (APPEND xs ys:((A)decl)list) = (decls,funs,exns,ctxt')
   ==> functions funs =
       MAP (\(x,y,z,t). (x,y,pan_globals_compile ctxt' z,t)) (functions ys)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP compile_decls_append_IMP) THEN
  PPASS2AUX_split_top_tac THEN CAKE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  PPASS2AUX_split_top_tac THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `p1:((A)decl)list = []` SUBST1_TAC THENL
   [MATCH_MP_TAC compile_decs_decls_thm THEN
    MAP_EVERY EXISTS_TAC [`ctxt:(A)pan_globals_context`; `xs:((A)decl)list`;
                          `p0:((A)panLang_prog)list`; `p2:((A)decl)list`;
                          `p3:(A)pan_globals_context`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ALL ((~) o is_function) (xs:((A)decl)list)` THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3:(A)pan_globals_context`; `ys:((A)decl)list`; `p0':((A)panLang_prog)list`;
                 `p1':((A)decl)list`; `p2':((A)decl)list`; `ctxt':(A)pan_globals_context`]
                compile_decs_functions_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `ctxt':(A)pan_globals_context`)) THEN
  MATCH_MP_TAC PPASS2AUX_functions_compile_map THEN ASM_REWRITE_TAC[]);;

let PPASS2AUX_fperm_nonfun = prove
 (`!P f g decs:((A)decl)list.
     (!x. P x ==> ~is_function x) ==> fperm_decs f g (FILTER P decs) = FILTER P decs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:mlstring`; `g:mlstring`; `FILTER P (decs:((A)decl)list)`; `T`]
                fperm_decs_decls) THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ALL_FILTER; o_THM] THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x:(A)decl. T` THEN ASM_REWRITE_TAC[ALL_T]);;

let evaluate_decls_compile_top = prove
 (`evaluate_decls (s:(A,FFI)pan_state) decs = SOME s' /\
   ALOOKUP (functions decs) start = SOME (args,body,rshape) /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) decs /\
   pan_globals_compile_decs
     (pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word (word (SUM (MAP size_of_shape (dec_shapes decs))))))
     (fperm_decs start (new_main_name decs) (resort_decls decs)) =
     (ndecls,nfuns,nexns,nctxt)
   ==> evaluate_decls s (pan_globals_compile_top decs start) =
       SOME (pan_state_code_fupd
               (combin_K (pan_state_code s |+
                     (start,args,
                      panLang_Seq (nested_seq ndecls)
                        (panLang_Call NONE (new_main_name decs)
                           (MAP (panLang_Var panLang_Local o FST) args)),
                      rshape) |++
                   MAP (\(x,y,z,t). (x,y,pan_globals_compile nctxt z,t))
                       (functions (fperm_decs start (new_main_name decs) decs))))
             (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions nexns)) s))`,
  STRIP_TAC THEN
   SUBGOAL_THEN
     `pan_globals_compile_top decs start =
      APPEND nexns
        (CONS (Function (fun_decl_REC start F F args
                 (panLang_Seq (nested_seq ndecls)
                    (panLang_Call NONE (new_main_name decs)
                       (MAP (panLang_Var panLang_Local o FST) args)))
                 rshape)) (nfuns:((A)decl)list))`
     ASSUME_TAC THENL
    [REWRITE_TAC[pan_globals_compile_top_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[dec_shapes_fperm_decs; dec_shapes_resort_decls_def] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV);
     ALL_TAC] THEN
   SUBGOAL_THEN `ALL is_exn_decl (nexns:((A)decl)list) /\
                 exceptions nexns = exceptions (decs:((A)decl)list)` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
     REWRITE_TAC[ALL_FILTER; ALL_T; exceptions_FILTER_is_function; PPASS2AUX_exceptions_fperm_decs;
                 resort_decls_def; exceptions_append; APPEND; APPEND_NIL];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `decs:((A)decl)list`; `s':(A,FFI)pan_state`]
                 evaluate_decls_exns_wf) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`s:(A,FFI)pan_state`; `nexns:((A)decl)list`; `T`] exns_wf_evaluate_decls) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[evaluate_decls_append] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL (is_wf_shape (pan_state_structs (s:(A,FFI)pan_state)) o SND)
                   (args:(mlstring#shape)list) /\
                 is_wf_shape (pan_state_structs s) rshape` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP MEM_functions o MATCH_MP ALOOKUP_MEM o
       check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ALOOKUP"
                        with Failure _ -> false)) THEN
     REWRITE_TAC[PAIR_EQ] THEN
     DISCH_THEN(X_CHOOSE_THEN `fi:(A)fun_decl` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`s:(A,FFI)pan_state`; `decs:((A)decl)list`] evaluate_decls_functions_wf) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[evaluate_decls_def; fun_decl_INFO.ri_accessors; pan_state_INFO.ri_accfupds;
               K_THM] THEN
   ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
     `functions (nfuns:((A)decl)list) =
      MAP (\(x,y,z,t). (x,y,pan_globals_compile nctxt z,t))
          (functions (fperm_decs start (new_main_name decs) (decs:((A)decl)list)))`
     ASSUME_TAC THENL
    [SUBGOAL_THEN
       `functions (fperm_decs start (new_main_name decs) (decs:((A)decl)list)) =
        functions (fperm_decs start (new_main_name decs) (FILTER is_function decs))`
       SUBST1_TAC THENL
      [REWRITE_TAC[fperm_decs_FILTER_is_function; functions_FILTER]; ALL_TAC] THEN
     MATCH_MP_TAC PPASS2AUX_compile_decs_funs_last THEN
     MAP_EVERY EXISTS_TAC
       [`APPEND (APPEND (FILTER is_name decs) (FILTER is_exn_decl decs))
                (FILTER is_decl (decs:((A)decl)list))`;
        `pan_globals_context_REC (FEMPTY:(mlstring,shape#A word)fmap) (word 0:A word)
           (word_mul (bytes_in_word:A word)
              (word (SUM (MAP size_of_shape (dec_shapes (decs:((A)decl)list))))))`;
        `ndecls:((A)panLang_prog)list`; `nexns:((A)decl)list`] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[ALL_APPEND; ALL_FILTER; o_THM] THEN REPEAT CONJ_TAC THEN
       MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x:(A)decl. T` THEN REWRITE_TAC[ALL_T] THEN
       MESON_TAC[not_is_function];
       REWRITE_TAC[fperm_decs_FILTER_is_function; ALL_FILTER] THEN
       MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x:(A)decl. T` THEN REWRITE_TAC[ALL_T];
       FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> try fst(dest_const t) = "pan_globals_compile_decs"
                                                           with Failure _ -> false)) (concl th)
                               then MP_TAC th else failwith "") THEN
       MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       REWRITE_TAC[resort_decls_def; fperm_decs_append; GSYM fperm_decs_FILTER_is_function] THEN
       SIMP_TAC[PPASS2AUX_fperm_nonfun; not_is_function]];
     ALL_TAC] THEN
  MP_TAC(ISPECL
     [`pan_state_code_fupd
         (combin_K (pan_state_code s |+
               (start,args,
                panLang_Seq (nested_seq ndecls)
                  (panLang_Call NONE (new_main_name decs)
                     (MAP (panLang_Var panLang_Local o FST) args)),
                rshape)))
         (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions (decs:((A)decl)list)))
            (s:(A,FFI)pan_state))`;
      `nfuns:((A)decl)list`] evaluate_decls_only_functions_SOME) THEN
   REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN ANTS_TAC THENL
    [CONJ_TAC THENL
      [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP compile_decs_EVERY_is_function);
       MP_TAC(INST [`decs:((A)decl)list`,`code:((A)decl)list`] compile_top_shape_wf) THEN
       ASM_REWRITE_TAC[ALL_APPEND; ALL] THEN SIMP_TAC[]];
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[injectivity "option"; pan_state_INFO.ri_fupdfupds; K_o_THM;
                 pan_state_INFO.ri_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[]]);;

let compile_top_only_functions_or_exns = prove
 (`ALL (\d. is_function d \/ is_exn_decl d)
       (pan_globals_compile_top (code:((A)decl)list) start)`,
  SUBGOAL_THEN `ALOOKUP (functions (code:((A)decl)list)) (start:mlstring) = NONE \/
                ?args body rshape.
                  ALOOKUP (functions code) start = SOME (args,body,rshape)`
    MP_TAC THENL
   [MP_TAC(ISPEC `ALOOKUP (functions (code:((A)decl)list)) (start:mlstring)`
             (cases "option")) THEN REWRITE_TAC[EXISTS_PAIR_THM];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[pan_globals_compile_top_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PPASS2AUX_split_top_tac THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ALL_APPEND; ALL; is_function_def] THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
    REWRITE_TAC[ALL_FILTER] THEN REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP compile_decs_EVERY_is_function) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]]);;

let evaluate_two = prove
 (`pan_evaluate (p,pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state)) = (res,st) /\
   pan_evaluate (p,pan_state_clock_fupd (combin_K k') t) = (res',st') /\
   ~(res = SOME pan_TimeOut) /\ ~(res' = SOME pan_TimeOut)
   ==> res = res' /\ pan_state_ffi st = pan_state_ffi st'`,
  STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `k <= k' \/ k' <= k:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `kk:num` SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THENL
   [MP_TAC(ISPECL [`p:(A)panLang_prog`; `pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state)`;
                   `res:((A)pan_result)option`; `st:(A,FFI)pan_state`; `kk:num`]
                  pan_evaluate_add_clock_eq);
    MP_TAC(ISPECL [`p:(A)panLang_prog`; `pan_state_clock_fupd (combin_K k') (t:(A,FFI)pan_state)`;
                   `res':((A)pan_result)option`; `st':(A,FFI)pan_state`; `kk:num`]
                  pan_evaluate_add_clock_eq)] THEN
  ASM_REWRITE_TAC[] THEN RW[] THEN GVS[]);;

let num_cases_lemma = prove
 (`(!) (P:num->bool) ==> P 0 /\ !x. P (SUC x)`,
  REWRITE_TAC[FORALL_DEF] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let LUB_IMAGE_SUC = prove
 (`(!x. LPREFIX ((f:num->(A)llist) x) (f (SUC x)))
   ==> build_lprefix_lub (IMAGE f (:num)) = build_lprefix_lub (IMAGE (f o SUC) (:num))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> LPREFIX ((f:num->(A)llist) m) (f n)` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
     [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LPREFIX_REFL];
      STRIP_TAC THENL [ASM_REWRITE_TAC[LPREFIX_REFL]; ASM_MESON_TAC[LPREFIX_TRANS]]];
    ALL_TAC] THEN
  MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN
  REWRITE_TAC[lprefix_chain_def; lprefix_rel_def; FORALL_IN_IMAGE_2; FORALL_IN_IMAGE;
              EXISTS_IN_IMAGE; IN_UNIV; o_THM] THEN
  ASM_MESON_TAC[LE_CASES; LPREFIX_REFL]);;

let PPASS2AUX_lookup_code_FLOOKUP = prove
 (`pan_lookup_code code f args = SOME (prog,nl,rsh)
   ==> ?vshapes. FLOOKUP (code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) f =
                 SOME (vshapes,prog,rsh)`,
  REWRITE_TAC[pan_lookup_code_def] THEN
  QCASES_ON "FLOOKUP (code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) f" THEN
  CAKE_REWRITE_TAC[distinctness "option"] THEN
  RENAME1 "FLOOKUP code f = SOME vpr" THEN PAIR_CASES_ON `vpr:(mlstring#shape)list#(A)panLang_prog#shape` THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN MESON_TAC[]);;

let PPASS2AUX_call_none_res = prove
 (`pan_evaluate (panLang_Call NONE f [], S:(A,FFI)pan_state) = (r,t)
   ==> ~(r = NONE) /\ ~(r = SOME pan_Break) /\ ~(r = SOME pan_Continue) /\
       (!retv. r = SOME (pan_Return retv)
               ==> ?vshapes prog. FLOOKUP (pan_state_code S) f =
                                   SOME (vshapes,prog,shape_of retv))`,
  REWRITE_TAC[PPASS2AUX_evaluate_Call; OPT_MMAP_def] THEN
  REPEAT(CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN TOP_CASE_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "pan_result";
              injectivity "pan_result"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PPASS2AUX_lookup_code_FLOOKUP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let PPASS2AUX_init_call_step = prove
 (`FLOOKUP (pan_state_code s) start =
     SOME ([],panLang_Seq body (panLang_Call NONE start' []),rshape) /\
   FLOOKUP (pan_state_code s) start' = SOME (args',body',rshape) /\
   pan_evaluate (body, pan_state_locals_fupd (combin_K FEMPTY)
                         (pan_state_clock_fupd (combin_K n) (s:(A,FFI)pan_state))) =
     (NONE, pan_state_clock_fupd (combin_K n) s')
   ==> FST (pan_evaluate (panLang_Call NONE start [], pan_state_clock_fupd (combin_K (SUC n)) s)) =
       FST (pan_evaluate (panLang_Call NONE start' [], pan_state_clock_fupd (combin_K n) s')) /\
       pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start [],
                                         pan_state_clock_fupd (combin_K (SUC n)) s))) =
       pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start' [],
                                         pan_state_clock_fupd (combin_K n) s')))`,
  STRIP_TAC THEN
   SUBGOAL_THEN `pan_state_code (s':(A,FFI)pan_state) = pan_state_code (s:(A,FFI)pan_state)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_invariants) THEN
     REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[];
     ALL_TAC] THEN
   NAMED_CASES_ON "pan_evaluate (panLang_Call NONE start' [], pan_state_clock_fupd (combin_K n) s')"
     ["r t"] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS2AUX_call_none_res) THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Call; OPT_MMAP_def] THEN
   CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[pan_lookup_code_def; pan_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[MAP; ALL_DISTINCT; ALL2; ZIP; FUPDATE_LIST_THM; NOT_SUC] THEN
   CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[pan_dec_clock_def; pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds;
               K_THM; SUC_SUB1] THEN
   REWRITE_TAC[PPASS2AUX_evaluate_Seq] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "r" ["";"r1"] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CAKE_REWRITE_TAC[] THEN
   NAMED_CASES_ON "r1" ["";"";"";"";"retv";"eid exn";"ffi_out"] THEN CAKE_REWRITE_TAC[] THEN
   GVS[pan_empty_locals_def; pan_state_INFO.ri_accfupds; K_THM; distinctness "option";
       injectivity "option"; injectivity "pan_result"]);;

let PPASS2AUX_exists_shift = prove
 (`!f g P. (!n. f (SUC n) = g n) /\ ~P ((f:num->B) 0)
           ==> ((?k. P (f k)) <=> (?k. P (g k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC `(P:B->bool) ((f:num->B) k)` THEN
    STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN ASM_MESON_TAC[];
    EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[]]);;

let PPASS2AUX_some_shift = prove
 (`!(E:num->((A)pan_result)option#(A,FFI)pan_state)
     (E':num->((A)pan_result)option#(A,FFI)pan_state) M res.
     (!n. FST (E (SUC n)) = FST (E' n) /\
          pan_state_ffi (SND (E (SUC n))) = pan_state_ffi (SND (E' n))) /\
     (!outcome. ~M (FST (E 0)) outcome)
     ==> ((?k t r outcome. E k = (r,t) /\ M r outcome /\
                           res = Terminate outcome (ffi_state_io_events (pan_state_ffi t))) <=>
          (?k t r outcome. E' k = (r,t) /\ M r outcome /\
                           res = Terminate outcome (ffi_state_io_events (pan_state_ffi t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC `(E:num->((A)pan_result)option#(A,FFI)pan_state) k = (r,t)` THEN
    STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THENL
     [DISCH_THEN(MP_TAC o AP_TERM `FST:((A)pan_result)option#(A,FFI)pan_state->((A)pan_result)option`) THEN
      REWRITE_TAC[FST] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `SND ((E':num->((A)pan_result)option#(A,FFI)pan_state) n)`;
                            `r:((A)pan_result)option`; `outcome:outcome`] THEN
      ASM_MESON_TAC[PAIR; FST; SND]];
    MAP_EVERY EXISTS_TAC [`SUC k`; `SND ((E:num->((A)pan_result)option#(A,FFI)pan_state) (SUC k))`;
                          `r:((A)pan_result)option`; `outcome:outcome`] THEN
    ASM_MESON_TAC[PAIR; FST; SND]]);;

let semantics_init_call = prove
 (`FLOOKUP (pan_state_code s) start =
     SOME ([],panLang_Seq body (panLang_Call NONE start' []),rshape) /\
   FLOOKUP (pan_state_code s) start' = SOME (args',body',rshape) /\
   (!k. pan_evaluate (body, pan_state_locals_fupd (combin_K FEMPTY)
                              (pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))) =
        (NONE, pan_state_clock_fupd (combin_K k) s')) /\
   ffi_state_io_events (pan_state_ffi s') = ffi_state_io_events (pan_state_ffi s)
   ==> pan_semantics s start = pan_semantics s' start'`,
  STRIP_TAC THEN
   SUBGOAL_THEN
     `!n. FST (pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (combin_K (SUC n)) (s:(A,FFI)pan_state))) =
          FST (pan_evaluate (panLang_Call NONE start' [], pan_state_clock_fupd (combin_K n) s')) /\
          pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start [],
                                            pan_state_clock_fupd (combin_K (SUC n)) s))) =
          pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start' [],
                                            pan_state_clock_fupd (combin_K n) s')))`
     ASSUME_TAC THENL
    [X_GEN_TAC `n:num` THEN MP_TAC PPASS2AUX_init_call_step THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
     `pan_evaluate (panLang_Call NONE start [], pan_state_clock_fupd (combin_K 0) (s:(A,FFI)pan_state)) =
      (SOME pan_TimeOut, pan_empty_locals (pan_state_clock_fupd (combin_K 0) s))`
     ASSUME_TAC THENL
    [REWRITE_TAC[PPASS2AUX_evaluate_Call; OPT_MMAP_def] THEN CAKE_REWRITE_TAC[] THEN
     REWRITE_TAC[pan_lookup_code_def; pan_state_INFO.ri_accfupds; K_THM] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     REWRITE_TAC[MAP; ALL_DISTINCT; ALL2; ZIP; FUPDATE_LIST_THM] THEN CAKE_REWRITE_TAC[];
     ALL_TAC] THEN
  REWRITE_TAC[pan_semantics_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(BETA_RULE(ISPECL
     [`\k. FST (pan_evaluate (panLang_Call NONE start [],
                              pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state)))`;
      `\k. FST (pan_evaluate (panLang_Call NONE start' [],
                              pan_state_clock_fupd (combin_K k) (s':(A,FFI)pan_state)))`;
      CASE_TERM `\x:((A)pan_result)option. match x with
                   SOME pan_TimeOut -> F
                 | SOME (pan_FinalFFI _) -> F
                 | SOME (pan_Return _) -> F
                 | _ -> T`] PPASS2AUX_exists_shift)) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(REWRITE_RULE[RIGHT_FORALL_IMP_THM] (BETA_RULE(ISPECL
     [`\k. pan_evaluate (panLang_Call NONE start [],
                         pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))`;
      `\k. pan_evaluate (panLang_Call NONE start' [],
                         pan_state_clock_fupd (combin_K k) (s':(A,FFI)pan_state))`;
      CASE_TERM `\(r:((A)pan_result)option) outcome.
                   match r with
                     SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                   | SOME (pan_Return _) -> outcome = Success
                   | _ -> F`] PPASS2AUX_some_shift))) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  SUBGOAL_THEN
     `build_lprefix_lub (IMAGE (\k. llist_fromList (ffi_state_io_events (pan_state_ffi
         (SND (pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))))))) (:num)) =
      build_lprefix_lub (IMAGE (\k. llist_fromList (ffi_state_io_events (pan_state_ffi
         (SND (pan_evaluate (panLang_Call NONE start' [],
                             pan_state_clock_fupd (combin_K k) (s':(A,FFI)pan_state))))))) (:num))`
     SUBST1_TAC THENL
    [MP_TAC(BETA_RULE(INST
       [`\k. llist_fromList (ffi_state_io_events (pan_state_ffi
           (SND (pan_evaluate (panLang_Call NONE start [],
                               pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))))))`,
        `f:num->(io_event)llist`]
       (INST_TYPE [`:io_event`,`:A`] LUB_IMAGE_SUC))) THEN
     ANTS_TAC THENL
      [X_GEN_TAC `x:num` THEN REWRITE_TAC[LPREFIX_fromList; from_toList] THEN
       CAKE_REWRITE_TAC[] THEN
       MP_TAC(ISPECL [`panLang_Call NONE start [] :(A)panLang_prog`;
                      `pan_state_clock_fupd (combin_K x) (s:(A,FFI)pan_state)`; `1`]
                     pan_evaluate_add_clock_io_events_mono) THEN
       REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM;
                   ADD1];
       DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   REWRITE_TAC[]);;

let semantics_init_call' = prove
 (`FLOOKUP (pan_state_code s) start =
     SOME ([],panLang_Seq body (panLang_Call NONE start' []),rshape) /\
   FLOOKUP (pan_state_code s) start' = SOME (args',body',rshape) /\
   pan_evaluate (body, pan_state_locals_fupd (combin_K FEMPTY) (s:(A,FFI)pan_state)) = (NONE,s') /\
   pan_state_clock s' = pan_state_clock s /\
   ffi_state_io_events (pan_state_ffi s') = ffi_state_io_events (pan_state_ffi s)
   ==> pan_semantics s start = pan_semantics s' start'`,
  STRIP_TAC THEN MP_TAC(ISPECL [] semantics_init_call) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `k:num` THEN
  MP_TAC(ISPECL [`body:(A)panLang_prog`;
                 `pan_state_locals_fupd (combin_K FEMPTY) (s:(A,FFI)pan_state)`;
                 `NONE:((A)pan_result)option`;
                 `pan_state_clock_fupd (combin_K 0) (s':(A,FFI)pan_state)`;
                 `pan_state_clock (s:(A,FFI)pan_state)`] evaluate_clock_sub) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_fupdfupds; K_o_THM; pan_state_INFO.ri_accfupds; K_THM;
                  ADD_CLAUSES; SUB_REFL; distinctness "option"] THEN
  SUBGOAL_THEN `pan_state_clock_fupd (combin_K (pan_state_clock (s:(A,FFI)pan_state)))
                  (s':(A,FFI)pan_state) = s'` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `pan_state_clock (s':(A,FFI)pan_state)`)) THEN
    REWRITE_TAC[record_fupdselfid "pan_state"];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`body:(A)panLang_prog`;
                 `pan_state_clock_fupd (combin_K 0) (pan_state_locals_fupd (combin_K FEMPTY) (s:(A,FFI)pan_state))`;
                 `NONE:((A)pan_result)option`;
                 `pan_state_clock_fupd (combin_K 0) (s':(A,FFI)pan_state)`; `k:num`]
                pan_evaluate_add_clock_eq) THEN
  ASM_REWRITE_TAC[distinctness "option"; pan_state_INFO.ri_fupdfupds; K_o_THM;
                  pan_state_INFO.ri_accfupds; K_THM; ADD_CLAUSES] THEN
  REWRITE_TAC[pan_state_INFO.ri_fupdcanon]);;

let compile_decs_FILTER_decs = prove
 (`!ctxt code decls funs exns ctxt'.
     pan_globals_compile_decs (ctxt:(A)pan_globals_context) code =
       (decls,funs,exns,ctxt')
     ==> pan_globals_compile_decs ctxt (FILTER is_decl code) = (decls,[],[],ctxt')`,
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  RW(pan_globals_compile_decs_def::is_function_def::is_decl_def::FILTER::
     all_case_eqs()) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let FILTER_decs_fperm_decs = prove
 (`!f g code:((A)decl)list.
     FILTER ((~) o is_function) (fperm_decs f g code) = FILTER ((~) o is_function) code`,
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; is_function_def; FILTER; o_THM]);;

let ALOOKUP_MAP3 = prove
 (`ALOOKUP (MAP (\(x,y,z). (x,y,(f:C->D) z)) (al:(A#B#C)list)) =
   OPTION_MAP (I ## f) o ALOOKUP al`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `k:A` THEN
  SPEC_TAC(`al:(A#B#C)list`,`al:(A#B#C)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_DEF; OPTION_MAP_DEF] THEN
  PAIR_CASES_ON `h:A#B#C` THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

let ALOOKUP_MAP4 = prove
 (`ALOOKUP (MAP (\(x,y,z,t). (x,y,(f:C->E) z,t)) (al:(A#B#C#D)list)) =
   OPTION_MAP (I ## (f ## I)) o ALOOKUP al`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `k:A` THEN
  SPEC_TAC(`al:(A#B#C#D)list`,`al:(A#B#C#D)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_DEF; OPTION_MAP_DEF] THEN
  PAIR_CASES_ON `h:A#B#C#D` THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

let PPASS2AUX_some_cong = prove
 (`!(E:num->((A)pan_result)option#(A,FFI)pan_state)
    (E':num->((A)pan_result)option#(A,FFI)pan_state) M res.
     (!n. FST (E n) = FST (E' n) /\
          pan_state_ffi (SND (E n)) = pan_state_ffi (SND (E' n)))
     ==> ((?k t r outcome. E k = (r,t) /\ M r outcome /\
                           res = Terminate outcome (ffi_state_io_events (pan_state_ffi t))) <=>
          (?k t r outcome. E' k = (r,t) /\ M r outcome /\
                           res = Terminate outcome (ffi_state_io_events (pan_state_ffi t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k:num`; `SND ((E':num->((A)pan_result)option#(A,FFI)pan_state) k)`;
                          `r:((A)pan_result)option`; `outcome:outcome`];
    MAP_EVERY EXISTS_TAC [`k:num`; `SND ((E:num->((A)pan_result)option#(A,FFI)pan_state) k)`;
                          `r:((A)pan_result)option`; `outcome:outcome`]] THEN
  ASM_MESON_TAC[PAIR; FST; SND]);;

let PPASS2AUX_call_none_locals = prove
 (`FST (pan_evaluate (panLang_Call NONE f [],
                      pan_state_locals_fupd (combin_K l) (S:(A,FFI)pan_state))) =
   FST (pan_evaluate (panLang_Call NONE f [], S)) /\
   pan_state_ffi (SND (pan_evaluate (panLang_Call NONE f [], pan_state_locals_fupd (combin_K l) S))) =
   pan_state_ffi (SND (pan_evaluate (panLang_Call NONE f [], S)))`,
  REWRITE_TAC[PPASS2AUX_evaluate_Call; OPT_MMAP_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM; PPASS2AUX_dec_clock_locals;
              pan_state_INFO.ri_fupdfupds; K_o_THM; pan_empty_locals_def] THEN
  REPEAT(CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN TOP_CASE_TAC) THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM]);;

let semantics_empty_locals = prove
 (`pan_semantics (t:(A,FFI)pan_state) start =
   pan_semantics (pan_state_locals_fupd (combin_K FEMPTY) t) start`,
  SUBGOAL_THEN
     `!k. FST (pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (combin_K k)
                               (pan_state_locals_fupd (combin_K FEMPTY) (t:(A,FFI)pan_state)))) =
          FST (pan_evaluate (panLang_Call NONE start [], pan_state_clock_fupd (combin_K k) t)) /\
          pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (combin_K k)
                               (pan_state_locals_fupd (combin_K FEMPTY) t)))) =
          pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start [],
                                            pan_state_clock_fupd (combin_K k) t)))`
     ASSUME_TAC THENL
    [GEN_TAC THEN REWRITE_TAC[pan_state_INFO.ri_fupdcanon] THEN
     REWRITE_TAC[PPASS2AUX_call_none_locals];
     ALL_TAC] THEN
   REWRITE_TAC[pan_semantics_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(REWRITE_RULE[RIGHT_FORALL_IMP_THM] (BETA_RULE(ISPECL
     [`\k. pan_evaluate (panLang_Call NONE start [],
                         pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state))`;
      `\k. pan_evaluate (panLang_Call NONE start [],
                         pan_state_clock_fupd (combin_K k)
                           (pan_state_locals_fupd (combin_K FEMPTY) (t:(A,FFI)pan_state)))`;
      CASE_TERM `\(r:((A)pan_result)option) outcome.
                   match r with
                     SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                   | SOME (pan_Return _) -> outcome = Success
                   | _ -> F`] PPASS2AUX_some_cong))) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let pan_globalsProof_state_rel_imp_semantics = prove
 (`pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t /\ ~(pan_semantics s start = Fail)
   ==> pan_semantics t start = pan_semantics s start`,
  STRIP_TAC THEN
   SUBGOAL_THEN
     `!k. ~(FST (pan_evaluate (panLang_Call NONE start [],
                               pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))) = SOME pan_Error)`
     ASSUME_TAC THENL
    [UNDISCH_TAC `~(pan_semantics (s:(A,FFI)pan_state) start = Fail)` THEN
     REWRITE_TAC[pan_semantics_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN
     DISCH_TAC THEN X_GEN_TAC `k:num` THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
     DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
     CAKE_REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN
     `!k. FST (pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state))) =
          FST (pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))) /\
          pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start [],
                                            pan_state_clock_fupd (combin_K k) t))) =
          pan_state_ffi (SND (pan_evaluate (panLang_Call NONE start [],
                                            pan_state_clock_fupd (combin_K k) s)))`
     ASSUME_TAC THENL
    [X_GEN_TAC `k:num` THEN
     MP_TAC(ISPECL [`panLang_Call NONE start [] :(A)panLang_prog`;
                    `pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state)`;
                    `FST (pan_evaluate (panLang_Call NONE start [],
                                        pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state)))`;
                    `ctxt:(A)pan_globals_context`;
                    `pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state)`;
                    `SND (pan_evaluate (panLang_Call NONE start [],
                                        pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state)))`]
                   pan_globalsProof_compile_correct) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
      [UNDISCH_TAC `pan_globalsProof_state_rel T ctxt (s:(A,FFI)pan_state) t` THEN
       REWRITE_TAC[pan_globalsProof_state_rel_def; pan_state_INFO.ri_accfupds; K_THM] THEN
       SIMP_TAC[];
       ALL_TAC] THEN
     REWRITE_TAC[pan_globals_compile_def; MAP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     CAKE_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `t':(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[pan_globalsProof_state_rel_def]) THEN
     SIMP_TAC[];
     ALL_TAC] THEN
  REWRITE_TAC[pan_semantics_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(REWRITE_RULE[RIGHT_FORALL_IMP_THM] (BETA_RULE(ISPECL
     [`\k. pan_evaluate (panLang_Call NONE start [],
                         pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state))`;
      `\k. pan_evaluate (panLang_Call NONE start [],
                         pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))`;
      CASE_TERM `\(r:((A)pan_result)option) outcome.
                   match r with
                     SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                   | SOME (pan_Return _) -> outcome = Success
                   | _ -> F`] PPASS2AUX_some_cong))) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let functions_filter_nil = prove
 (`!decls:((A)decl)list. functions (FILTER ((~) o is_function) decls) = []`,
  REC_IND_TAC (cake_ind "functions") THEN
  RW[functions_def; FILTER; is_function_def; o_THM]);;

let exceptions_compile_top = prove
 (`ALOOKUP (functions code) start = SOME x
   ==> exceptions (pan_globals_compile_top (code:((A)decl)list) start) = exceptions code`,
  PAIR_CASES_ON `x:(mlstring#shape)list#(A)panLang_prog#shape` THEN
  DISCH_TAC THEN REWRITE_TAC[pan_globals_compile_top_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PPASS2AUX_split_top_tac THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!l:((A)decl)list. ALL is_function l ==> exceptions l = []` ASSUME_TAC THENL
   [REC_IND_TAC (cake_ind "exceptions") THEN RW[exceptions_def; is_function_def; ALL];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_decs_EVERY_is_function) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
  ASM_SIMP_TAC[exceptions_append; exceptions_def; exceptions_FILTER_is_function;
               PPASS2AUX_exceptions_fperm_decs; resort_decls_def; APPEND; APPEND_NIL]);;

let map_pick_up_first = prove
 (`MAP FST (MAP (\(x,y,z,t). ((f1:A->E) x,(f2:B->F) y,(f3:C->G) z,(f4:D->H) t))
                (l:(A#B#C#D)list)) =
   MAP f1 (MAP FST l)`,
  SPEC_TAC(`l:(A#B#C#D)list`,`l:(A#B#C#D)list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; CONS_11] THEN
  PAIR_CASES_ON `h:A#B#C#D` THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST]);;

let tuple_4_o = prove
 (`(\(x,y,z,t). ((f1:A->E) x,(f2:B->F) y,(f3:C->G) z,(f4:D->H) t)) o
   (\(x,y,z,t). ((g1:I1->A) x,(g2:I2->B) y,(g3:I3->C) z,(g4:I4->D) t)) =
   (\(x,y,z,t). f1 (g1 x),f2 (g2 y),f3 (g3 z),f4 (g4 t))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* the declarations of functions and exceptions only read the structs and *)
(* the exception shapes of the state                                         *)

let PPASS2AUX_evaluate_decls_transfer = prove
 (`!s0 ds s0' s.
     ALL (\d. is_function d \/ is_exn_decl d) ds /\
     evaluate_decls (s0:(A,FFI)pan_state) ds = SOME s0' /\
     pan_state_structs s = pan_state_structs s0 /\
     pan_state_eshapes s = pan_state_eshapes s0
     ==> evaluate_decls (s:(A,FFI)pan_state) ds =
         SOME (pan_state_code_fupd (combin_K (pan_state_code s |++ functions ds))
                 (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions ds)) s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC evaluate_decls_only_functions_and_exns_SOME THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s0:(A,FFI)pan_state`; `ds:((A)decl)list`; `s0':(A,FFI)pan_state`]
                evaluate_decls_exns_wf) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `d:(A)decl` THEN DISCH_TAC THEN BETA_TAC THEN
    X_GEN_TAC `fi:(A)fun_decl` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC(INST [`s0':(A,FFI)pan_state`,`s':(A,FFI)pan_state`]
                      (SPECL [`s0:(A,FFI)pan_state`; `ds:((A)decl)list`]
                             evaluate_decls_functions_wf)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\d. is_function d \/ is_exn_decl d) (ds:((A)decl)list)` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `FLOOKUP (pan_state_eshapes (s0:(A,FFI)pan_state))`)) (concl th))) THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[]]);;

(* the semantics of declarations without struct names *)

let PPASS2AUX_semantics_decls_nonames = prove
 (CASE_TERM
  `ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) (code:((A)decl)list)
   ==> semantics_decls (s:(A,FFI)pan_state) start code =
       match evaluate_decls (pan_state_structs_fupd (combin_K []) s) code with
         NONE -> Fail
       | SOME s' -> pan_semantics s' start`,
  SIMP_TAC[semantics_decls_def; decs_stcnames_only_functions] THEN CAKE_REWRITE_TAC[]);;

let PPASS2AUX_ctsd_source = prove
 (`ALL_DISTINCT (MAP FST (functions (code:((A)decl)list))) /\
   pan_state_code (s:(A,FFI)pan_state) = FEMPTY /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) code /\
   ~(semantics_decls s start code = Fail)
   ==> ?s1 body rshape.
         evaluate_decls (pan_state_structs_fupd (combin_K []) s) code = SOME s1 /\
         semantics_decls s start code = pan_semantics s1 start /\
         ALOOKUP (functions code) start = SOME ([],body,rshape)`,
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP semantics_decls_has_main) THEN
  ASM_SIMP_TAC[FLOOKUP_FUPDATE_LIST; FLOOKUP_EMPTY; alookup_distinct_reverse] THEN
  QCASES_ON "ALOOKUP (functions (code:((A)decl)list)) start" THEN
  ASM_REWRITE_TAC[option_CASE; distinctness "option"] THEN
  DISCH_THEN(X_CHOOSE_THEN `body:(A)panLang_prog` (X_CHOOSE_TAC `rshape:shape`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_SIMP_TAC[PPASS2AUX_semantics_decls_nonames] THEN
  QCASES_ON "evaluate_decls (pan_state_structs_fupd (combin_K []) (s:(A,FFI)pan_state))
               (code:((A)decl)list)" THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`a':(A,FFI)pan_state`; `body:(A)panLang_prog`;
                                       `rshape:shape`] THEN
  ASM_REWRITE_TAC[]);;

(* the semantics of the compiled program as the semantics of a state *)

let PPASS2AUX_ctsd_target = prove
 (`evaluate_decls (pan_state_structs_fupd (combin_K []) (s:(A,FFI)pan_state)) code = SOME s1 /\
   ALOOKUP (functions code) start = SOME ([],body,rshape) /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) code /\
   pan_globals_compile_decs
     (pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word (word (SUM (MAP size_of_shape (dec_shapes code))))))
     (fperm_decs start (new_main_name code) (resort_decls code)) =
     (ndecls,nfuns,nexns,nctxt) /\
   pan_state_code s = FEMPTY /\ pan_state_code (t:(A,FFI)pan_state) = FEMPTY /\
   pan_state_eshapes t = pan_state_eshapes s
   ==> semantics_decls t start (pan_globals_compile_top code start) =
       pan_semantics
         (pan_state_code_fupd
            (combin_K (FEMPTY |+ (start,[],
                           panLang_Seq (nested_seq ndecls)
                             (panLang_Call NONE (new_main_name code) []),
                           rshape) |++
                MAP (\(x,y,z,t). (x,y,pan_globals_compile nctxt z,t))
                    (functions (fperm_decs start (new_main_name code) code))))
            (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions code))
               (pan_state_structs_fupd (combin_K []) t))) start`,
  STRIP_TAC THEN
  MP_TAC(INST [`pan_state_structs_fupd (combin_K []) (s:(A,FFI)pan_state)`,`s:(A,FFI)pan_state`;
               `code:((A)decl)list`,`decs:((A)decl)list`;
               `s1:(A,FFI)pan_state`,`s':(A,FFI)pan_state`;
               `[]:(mlstring#shape)list`,`args:(mlstring#shape)list`]
              evaluate_decls_compile_top) THEN
  ASM_REWRITE_TAC[MAP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ALL (\d. is_function d \/ is_exn_decl d)
                    (pan_globals_compile_top (code:((A)decl)list) start)` ASSUME_TAC THENL
   [REWRITE_TAC[compile_top_only_functions_or_exns]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_decls_only_funs_and_exn_decls o
              CONJ (ASSUME `ALL (\d. is_function d \/ is_exn_decl d)
                                (pan_globals_compile_top (code:((A)decl)list) start)`)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `pan_state_code:(A,FFI)pan_state->(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap`) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `evaluate_decls (pan_state_structs_fupd (combin_K []) (t:(A,FFI)pan_state))
       (pan_globals_compile_top (code:((A)decl)list) start) =
     SOME (pan_state_code_fupd
             (combin_K (pan_state_code (pan_state_structs_fupd (combin_K []) t) |++
                 functions (pan_globals_compile_top code start)))
             (pan_state_eshapes_fupd
                (combin_K (pan_state_eshapes (pan_state_structs_fupd (combin_K []) t) |++
                    exceptions (pan_globals_compile_top code start)))
                (pan_state_structs_fupd (combin_K []) t)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC PPASS2AUX_evaluate_decls_transfer THEN
    EXISTS_TAC `pan_state_structs_fupd (combin_K []) (s:(A,FFI)pan_state)` THEN
    REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d)
                    (pan_globals_compile_top (code:((A)decl)list) start)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\d. is_function d \/ is_exn_decl d)
                     (pan_globals_compile_top (code:((A)decl)list) start)` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PPASS2AUX_semantics_decls_nonames] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP exceptions_compile_top) THEN
  REWRITE_TAC[]);;

let PPASS2AUX_evaluate_decls_append_SOME = prove
 (`!s l1 l2 s''.
     evaluate_decls (s:(A,FFI)pan_state) (APPEND l1 l2) = SOME s'' <=>
     ?s'. evaluate_decls s l1 = SOME s' /\ evaluate_decls s' l2 = SOME s''`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_decls_append] THEN
  QCASES_ON "evaluate_decls (s:(A,FFI)pan_state) l1" THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let PPASS2AUX_ALL_FILTER_SELF = prove
 (`!P l:A list. ALL P (FILTER P l)`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[]);;

(* the source declarations in resorted order: exceptions, globals, functions *)

let PPASS2AUX_ctsd_source_split = prove
 (`evaluate_decls (s0:(A,FFI)pan_state) code = SOME s1 /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) (code:((A)decl)list)
   ==> ?s0d. evaluate_decls
               (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s0 |++ exceptions code)) s0)
               (FILTER is_decl code) = SOME s0d /\
             s1 = pan_state_code_fupd (combin_K (pan_state_code s0 |++ functions code)) s0d /\
             pan_state_code s0d = pan_state_code s0`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`s0:(A,FFI)pan_state`; `code:((A)decl)list`] resort_decls_evaluate) THEN
  ASM_REWRITE_TAC[resort_decls_def; PPASS2AUX_evaluate_decls_append_SOME] THEN
  DISCH_THEN(X_CHOOSE_THEN `sd:(A,FFI)pan_state` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `se:(A,FFI)pan_state` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `sn:(A,FFI)pan_state` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC)) THEN
  SUBGOAL_THEN `sn:(A,FFI)pan_state = s0` SUBST_ALL_TAC THENL
   [MP_TAC(SPECL [`s0:(A,FFI)pan_state`; `FILTER is_name (code:((A)decl)list)`]
                 evaluate_decls_names) THEN
    ASM_REWRITE_TAC[PPASS2AUX_ALL_FILTER_SELF; injectivity "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `se = pan_state_eshapes_fupd
                       (combin_K (pan_state_eshapes s0 |++ exceptions (code:((A)decl)list)))
                       (s0:(A,FFI)pan_state)` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`s0:(A,FFI)pan_state`; `FILTER is_exn_decl (code:((A)decl)list)`;
                   `se:(A,FFI)pan_state`] evaluate_decls_only_exn_decls) THEN
    ASM_REWRITE_TAC[PPASS2AUX_ALL_FILTER_SELF; exceptions_FILTER_is_function];
    ALL_TAC] THEN
  EXISTS_TAC `sd:(A,FFI)pan_state` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pan_state_code (sd:(A,FFI)pan_state) = pan_state_code (s0:(A,FFI)pan_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_decls_functions o
      check (fun th -> can (find_term ((=) `FILTER is_decl (code:((A)decl)list)`)) (concl th))) THEN
    REWRITE_TAC[functions_FILTER'; FUPDATE_LIST_THM; pan_state_INFO.ri_accfupds];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`sd:(A,FFI)pan_state`; `FILTER is_function (code:((A)decl)list)`;
                 `s1:(A,FFI)pan_state`] evaluate_decls_only_functions) THEN
  ASM_REWRITE_TAC[PPASS2AUX_ALL_FILTER_SELF; functions_FILTER]);;

let PPASS2AUX_top_not_in_addresses = prove
 (`good_dimindex(:A) /\ val(bytes_in_word:A word) * n < dimword(:A)
   ==> ~(word_add a (word_mul bytes_in_word (word n)) IN addresses (a:A word) n)`,
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS2AUX_good_dimindex_bytes) THEN
  REWRITE_TAC[IN_addresses; NOT_EXISTS_THM] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[WORD_EQ_ADD_LCANCEL] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  ASM_REWRITE_TAC[bytes_in_word_def; GSYM WORD_MUL; GSYM VAL_EQ; VAL_WORD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(bytes_in_word:A word) = dimindex(:A) DIV 8`]) THEN
  SUBGOAL_THEN `i * dimindex(:A) DIV 8 < n * dimindex(:A) DIV 8` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_MULT_RCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `i * dimindex(:A) DIV 8 < 2 EXP dimindex(:A) /\
                dimindex(:A) DIV 8 * n < 2 EXP dimindex(:A)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

(* the relation between the source state after the exception declarations *)
(* and the target state when the new main function starts                   *)

let PPASS2AUX_ctsd_init_rel = prove
 (`pan_state_globals (s:(A,FFI)pan_state) = FEMPTY /\ pan_state_code s = FEMPTY /\
   byte_aligned (pan_state_top_addr s) /\ good_dimindex(:A) /\
   (!addr'. addr' IN pan_state_memaddrs s ==> pan_state_memory s addr' = tmem addr') /\
   ~(word_add (pan_state_top_addr s) (word_mul bytes_in_word (word n)) IN
     pan_state_memaddrs s) /\
   val(bytes_in_word:A word) * n < dimword(:A)
   ==> pan_globalsProof_state_rel F
         (pan_globals_context_REC FEMPTY (word 0) (word_mul bytes_in_word (word n)))
         (pan_state_eshapes_fupd (combin_K E) (pan_state_structs_fupd (combin_K []) s))
         (pan_state_locals_fupd (combin_K FEMPTY)
           (pan_state_code_fupd (combin_K C1)
             (pan_state_eshapes_fupd (combin_K E)
               (pan_state_structs_fupd (combin_K [])
                 (pan_state_top_addr_fupd
                    (combin_K (word_add (pan_state_top_addr s) (word_mul bytes_in_word (word n))))
                   (pan_state_memaddrs_fupd
                      (combin_K (pan_state_memaddrs s UNION addresses (pan_state_top_addr s) n))
                     (pan_state_memory_fupd (combin_K tmem)
                       (pan_state_locals_fupd (combin_K tlocals) s))))))))`,
  STRIP_TAC THEN
  REWRITE_TAC[pan_globalsProof_state_rel_def; pan_state_INFO.ri_accfupds; K_THM;
              pan_globals_context_INFO.ri_accessors] THEN
  ASM_REWRITE_TAC[WORD_ADD_SUB; FLOOKUP_EMPTY; distinctness "option"; FEVERY_FEMPTY;
                  SUBSET_UNION; disjoint_globals_def; IS_SOME_DEF; IN_UNION] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PPASS2AUX_top_not_in_addresses THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC byte_aligned_add THEN ASM_SIMP_TAC[byte_aligned_bytes_in_word_mul]]);;

let PPASS2AUX_MAP_FST_MAP4 = prove
 (`!l:(B#C#D#G)list. MAP FST (MAP (\(x,y,z,t). (x,y,(f:D->E) z,t)) l) = MAP FST l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11] THEN
  PAIR_CASES_ON `h:B#C#D#G` THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST]);;

let PPASS2AUX_MAP_FST_functions_fperm = prove
 (`!f g code:((A)decl)list.
     MAP FST (functions (fperm_decs f g code)) =
     MAP (fperm_name f g) (MAP FST (functions code))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[functions_fperm_decs] THEN
  SPEC_TAC(`functions (code:((A)decl)list)`,
           `l:(mlstring#(mlstring#shape)list#(A)panLang_prog#shape)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11] THEN
  PAIR_CASES_ON `h:mlstring#(mlstring#shape)list#(A)panLang_prog#shape` THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST]);;

let PPASS2AUX_MEM_fperm_name = prove
 (`!f g k l. MEM k (MAP (fperm_name f g) l) <=> MEM (fperm_name f g k) (l:mlstring list)`,
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[fperm_name_cancel]);;

(* the code of the target state when the new main function starts *)

let PPASS2AUX_ctsd_code = prove
 (`ALL_DISTINCT (MAP FST (functions (code:((A)decl)list))) /\
   ALOOKUP (functions code) start = SOME ([],body,rshape) /\
   C1 = FEMPTY |+ (start,[],
                   panLang_Seq (nested_seq ndecls)
                     (panLang_Call NONE (new_main_name code) []),
                   rshape) |++
        MAP (\(x,y,z,t). (x,y,pan_globals_compile nctxt z,t))
            (functions (fperm_decs start (new_main_name code) code))
   ==> FLOOKUP C1 start =
         SOME ([],panLang_Seq (nested_seq ndecls)
                    (panLang_Call NONE (new_main_name code) []),rshape) /\
       FLOOKUP C1 (new_main_name code) =
         SOME ([],pan_globals_compile nctxt (fperm start (new_main_name code) body),
               rshape) /\
       (!fname vshapes prog rs.
          FLOOKUP (FEMPTY |++ functions (fperm_decs start (new_main_name code) code)) fname =
            SOME (vshapes,prog,rs)
          ==> FLOOKUP C1 fname = SOME (vshapes,pan_globals_compile nctxt prog,rs))`,
  STRIP_TAC THEN
  ABBREV_TAC `nm = new_main_name (code:((A)decl)list)` THEN
  ABBREV_TAC `L0 = functions (fperm_decs start nm (code:((A)decl)list))` THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (L0:(mlstring#(mlstring#shape)list#(A)panLang_prog#shape)list))`
    ASSUME_TAC THENL
   [EXPAND_TAC "L0" THEN MATCH_MP_TAC ALL_DISTINCT_fperm_decs THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!k. FLOOKUP (C1:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) k =
         option_CASE
           (OPTION_MAP (I ## (pan_globals_compile nctxt ## I)) (ALOOKUP L0 k))
           (FLOOKUP (FEMPTY |+ (start,[],
                                panLang_Seq (nested_seq ndecls) (panLang_Call NONE nm []),
                                rshape)) k) SOME`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_FUPDATE_LIST; MAP_REVERSE; ALOOKUP_MAP4; o_THM; ETA_AX] THEN
    ASM_SIMP_TAC[alookup_distinct_reverse];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `ALOOKUP (L0:(mlstring#(mlstring#shape)list#(A)panLang_prog#shape)list)
                    start = NONE` SUBST1_TAC THENL
     [EXPAND_TAC "L0" THEN
      REWRITE_TAC[ALOOKUP_NONE; PPASS2AUX_MAP_FST_functions_fperm; PPASS2AUX_MEM_fperm_name] THEN
      REWRITE_TAC[fperm_name_def] THEN ASM_MESON_TAC[new_main_name_correct];
      REWRITE_TAC[OPTION_MAP_DEF; option_CASE; FLOOKUP_UPDATE; FLOOKUP_EMPTY]];
    SUBGOAL_THEN `ALOOKUP (L0:(mlstring#(mlstring#shape)list#(A)panLang_prog#shape)list) nm =
                  SOME ([],fperm start nm body,rshape)` SUBST1_TAC THENL
     [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "L0" THEN REWRITE_TAC[functions_fperm_decs; MEM_MAP] THEN
      EXISTS_TAC `(start:mlstring,[]:(mlstring#shape)list,body:(A)panLang_prog,rshape:shape)` THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_SIMP_TAC[ALOOKUP_MEM; fperm_name_def];
      REWRITE_TAC[OPTION_MAP_DEF; option_CASE; PAIR_MAP_THM; I_THM]];
    REWRITE_TAC[FLOOKUP_FUPDATE_LIST; FLOOKUP_EMPTY; ETA_AX; option_case_ID] THEN
    ASM_SIMP_TAC[alookup_distinct_reverse] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_CASE; PAIR_MAP_THM; I_THM]]);;

let PPASS2AUX_FILTER_is_decl_FILTER = prove
 (`!code:((A)decl)list.
     FILTER is_decl (FILTER is_name code) = [] /\
     FILTER is_decl (FILTER is_exn_decl code) = [] /\
     FILTER is_decl (FILTER is_decl code) = FILTER is_decl code /\
     FILTER is_decl (FILTER is_function code) = []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER] THEN QCASES_ON "h" THEN
  ASM_REWRITE_TAC[is_name_def; is_decl_def; is_exn_decl_def; is_function_def; FILTER]);;

let PPASS2AUX_FILTER_is_decl_fperm = prove
 (`!f g xs:((A)decl)list. FILTER is_decl (fperm_decs f g xs) = FILTER is_decl xs`,
  REC_IND_TAC fperm_decs_ind THEN RW[fperm_decs_def; is_decl_def; FILTER]);;

let PPASS2AUX_FILTER_is_decl_resort = prove
 (`!f g code:((A)decl)list.
     FILTER is_decl (fperm_decs f g (resort_decls code)) = FILTER is_decl code`,
  REWRITE_TAC[PPASS2AUX_FILTER_is_decl_fperm; resort_decls_def; FILTER_APPEND;
              PPASS2AUX_FILTER_is_decl_FILTER; APPEND; APPEND_NIL]);;

(* the relation with all locals empty and the code of the permuted program *)

let PPASS2AUX_state_rel_code_locals = prove
 (`pan_globalsProof_state_rel F ctxt (s:(A,FFI)pan_state) t /\
   pan_state_locals t = FEMPTY /\
   (!fname vshapes prog rs.
      FLOOKUP c fname = SOME (vshapes,prog,rs)
      ==> FLOOKUP (pan_state_code t) fname =
            SOME (vshapes,pan_globals_compile ctxt prog,rs))
   ==> pan_globalsProof_state_rel T ctxt
         (pan_state_locals_fupd (combin_K FEMPTY) (pan_state_code_fupd (combin_K c) s)) t`,
  REWRITE_TAC[pan_globalsProof_state_rel_def; pan_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* the source semantics with the main function renamed and empty locals *)

let PPASS2AUX_ctsd_lhs = prove
 (`pan_semantics
     (pan_state_code_fupd (combin_K (FEMPTY |++ functions (code:((A)decl)list)))
        (s0d:(A,FFI)pan_state)) start =
   pan_semantics
     (pan_state_locals_fupd (combin_K FEMPTY)
        (pan_state_code_fupd
           (combin_K (FEMPTY |++ functions (fperm_decs start (new_main_name code) code))) s0d))
     (new_main_name code)`,
  GEN_REWRITE_TAC LAND_CONV
    [GSYM(INST [`start:mlstring`,`f:mlstring`; `new_main_name (code:((A)decl)list)`,`g:mlstring`]
               semantics_fperm)] THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; pan_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
              fperm_code_FUPDATE_LIST_functions; fperm_code_FEMPTY] THEN
  REWRITE_TAC[fperm_name_def] THEN
  GEN_REWRITE_TAC LAND_CONV [semantics_empty_locals] THEN REWRITE_TAC[]);;

(* the initialisation of the globals by the new main function *)

let PPASS2AUX_ctsd_init = prove
 (`evaluate_decls
     (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions code))
        (pan_state_structs_fupd (combin_K []) (s:(A,FFI)pan_state)))
     (FILTER is_decl code) = SOME s0d /\
   pan_globals_compile_decs
     (pan_globals_context_REC FEMPTY (word 0)
        (word_mul bytes_in_word (word (SUM (MAP size_of_shape (dec_shapes code))))))
     (fperm_decs start (new_main_name code) (resort_decls (code:((A)decl)list))) =
     (ndecls,nfuns,nexns,nctxt) /\
   pan_state_code s = FEMPTY /\ pan_state_globals s = FEMPTY /\
   byte_aligned (pan_state_top_addr s) /\ good_dimindex(:A) /\
   DISJOINT (pan_state_memaddrs s)
     (addresses (pan_state_top_addr s) (SUM (MAP size_of_shape (dec_shapes code)))) /\
   (!addr'. addr' IN pan_state_memaddrs s ==> pan_state_memory s addr' = tmem addr') /\
   ~(word_add (pan_state_top_addr s)
       (word_mul bytes_in_word (word (SUM (MAP size_of_shape (dec_shapes code))))) IN
     pan_state_memaddrs s) /\
   val(bytes_in_word:A word) * SUM (MAP size_of_shape (dec_shapes code)) < dimword(:A)
   ==> ?t'. pan_evaluate
              (nested_seq ndecls,
               pan_state_locals_fupd (combin_K FEMPTY)
                 (pan_state_code_fupd (combin_K C1)
                    (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions code))
                       (pan_state_structs_fupd (combin_K [])
                          (pan_state_top_addr_fupd
                             (combin_K (word_add (pan_state_top_addr s)
                                  (word_mul bytes_in_word
                                     (word (SUM (MAP size_of_shape (dec_shapes code)))))))
                             (pan_state_memaddrs_fupd
                                (combin_K (pan_state_memaddrs s UNION
                                    addresses (pan_state_top_addr s)
                                      (SUM (MAP size_of_shape (dec_shapes code)))))
                                (pan_state_memory_fupd (combin_K tmem)
                                   (pan_state_locals_fupd (combin_K tlocals) s)))))))) =
              (NONE,t') /\
            pan_globalsProof_state_rel F nctxt s0d t' /\
            pan_state_clock t' = pan_state_clock s /\
            pan_state_ffi t' = pan_state_ffi s /\
            pan_state_locals t' = FEMPTY /\
            pan_state_code t' = C1`,
  STRIP_TAC THEN
  MP_TAC(ISPECL
    [`pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++ exceptions (code:((A)decl)list)))
        (pan_state_structs_fupd (combin_K []) (s:(A,FFI)pan_state))`;
     `FILTER is_decl (code:((A)decl)list)`; `s0d:(A,FFI)pan_state`;
     `ndecls:((A)panLang_prog)list`; `[]:((A)decl)list`; `[]:((A)decl)list`;
     `nctxt:(A)pan_globals_context`;
     `pan_globals_context_REC (FEMPTY:(mlstring,shape#A word)fmap) (word 0:A word)
        (word_mul (bytes_in_word:A word)
           (word (SUM (MAP size_of_shape (dec_shapes (code:((A)decl)list))))))`;
     `pan_state_locals_fupd (combin_K FEMPTY)
        (pan_state_code_fupd (combin_K C1)
           (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |++
                                       exceptions (code:((A)decl)list)))
              (pan_state_structs_fupd (combin_K [])
                 (pan_state_top_addr_fupd
                    (combin_K (word_add (pan_state_top_addr s)
                         (word_mul bytes_in_word
                            (word (SUM (MAP size_of_shape (dec_shapes code)))))))
                    (pan_state_memaddrs_fupd
                       (combin_K (pan_state_memaddrs s UNION
                           addresses (pan_state_top_addr s)
                             (SUM (MAP size_of_shape (dec_shapes code)))))
                       (pan_state_memory_fupd (combin_K (tmem:A word->(A)word_lab))
                          (pan_state_locals_fupd
                             (combin_K (tlocals:(mlstring,(A)pan_v)fmap))
                             (s:(A,FFI)pan_state))))))))`;
     `addresses (pan_state_top_addr (s:(A,FFI)pan_state))
        (SUM (MAP size_of_shape (dec_shapes (code:((A)decl)list))))`]
    evaluate_decls_init_globals_lemma) THEN
  REWRITE_TAC[pan_state_INFO.ri_accfupds; pan_globals_context_INFO.ri_accessors; K_THM;
              dec_shapes_FILTER; WORD_ADD_SUB; WORD_SUB_RZERO; PPASS2AUX_ALL_FILTER_SELF;
              SUBSET_UNION; FLOOKUP_EMPTY; IS_SOME_DEF] THEN
  ASM_REWRITE_TAC[FLOOKUP_EMPTY; IS_SOME_DEF; distinctness "option"] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP compile_decs_FILTER_decs) THEN
      REWRITE_TAC[PPASS2AUX_FILTER_is_decl_resort; dec_shapes_fperm_decs;
                  dec_shapes_resort_decls_def];
      MATCH_MP_TAC PPASS2AUX_ctsd_init_rel THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[byte_aligned_def; aligned_0]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t':(A,FFI)pan_state` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_invariants) THEN
  SIMP_TAC[pan_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 compile_top_semantics_decls: t is HOL4's s with <| top_addr := ...;  *)
(* memaddrs := ...; memory := tmem; locals := tlocals |>                    *)

let pan_globalsProof_compile_top_semantics_decls = prove
 (`ALL_DISTINCT (MAP FST (functions (code:((A)decl)list))) /\
   t = pan_state_top_addr_fupd (combin_K (word_add (pan_state_top_addr s) (mgs:A word)))
         (pan_state_memaddrs_fupd (combin_K (pan_state_memaddrs s UNION free_addrs))
            (pan_state_memory_fupd (combin_K tmem)
               (pan_state_locals_fupd (combin_K tlocals) (s:(A,FFI)pan_state)))) /\
   pan_state_code s = FEMPTY /\
   pan_state_globals s = FEMPTY /\
   byte_aligned (pan_state_top_addr s) /\
   good_dimindex(:A) /\
   mgs = word_mul bytes_in_word (word (SUM (MAP size_of_shape (dec_shapes code)))) /\
   free_addrs = addresses (pan_state_top_addr s) (SUM (MAP size_of_shape (dec_shapes code))) /\
   DISJOINT (pan_state_memaddrs s) free_addrs /\
   (!addr'. addr' IN pan_state_memaddrs s ==> pan_state_memory s addr' = tmem addr') /\
   ~(word_add (pan_state_top_addr s) mgs IN pan_state_memaddrs s) /\
   val(bytes_in_word:A word) * SUM (MAP size_of_shape (dec_shapes code)) < dimword(:A) /\
   ALL (\d. is_function d \/ is_decl d \/ is_exn_decl d) code /\
   ~(semantics_decls s start code = Fail)
   ==> semantics_decls s start code =
       semantics_decls t start (pan_globals_compile_top code start)`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `mgs:A word`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `free_addrs:A word->bool`)) THEN
  MP_TAC PPASS2AUX_ctsd_source THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(A,FFI)pan_state` (X_CHOOSE_THEN `body:(A)panLang_prog`
    (X_CHOOSE_THEN `rshape:shape` STRIP_ASSUME_TAC))) THEN
  MP_TAC(INST [`pan_state_structs_fupd (combin_K []) (s:(A,FFI)pan_state)`,`s0:(A,FFI)pan_state`]
              PPASS2AUX_ctsd_source_split) THEN
  ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0d:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `?ndecls nfuns nexns nctxt.
       pan_globals_compile_decs
         (pan_globals_context_REC (FEMPTY:(mlstring,shape#A word)fmap) (word 0:A word)
            (word_mul (bytes_in_word:A word)
               (word (SUM (MAP size_of_shape (dec_shapes (code:((A)decl)list)))))))
         (fperm_decs start (new_main_name code) (resort_decls code)) =
       (ndecls:((A)panLang_prog)list,nfuns:((A)decl)list,nexns:((A)decl)list,
        nctxt:(A)pan_globals_context)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC PPASS2AUX_ctsd_target THEN ASM_REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN
   DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PPASS2AUX_ctsd_lhs] THEN
   SUBGOAL_THEN
     `~(pan_semantics
          (pan_state_locals_fupd (combin_K FEMPTY)
             (pan_state_code_fupd
                (combin_K (FEMPTY |++ functions (fperm_decs start (new_main_name code)
                                             (code:((A)decl)list))))
                (s0d:(A,FFI)pan_state)))
          (new_main_name code) = Fail)`
     ASSUME_TAC THENL
    [UNDISCH_TAC `~(semantics_decls (s:(A,FFI)pan_state) start (code:((A)decl)list) = Fail)` THEN
     ASM_REWRITE_TAC[PPASS2AUX_ctsd_lhs];
     ALL_TAC] THEN
   ABBREV_TAC
     `C1 = (FEMPTY:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap) |+
           (start,[],panLang_Seq (nested_seq ndecls)
                       (panLang_Call NONE (new_main_name (code:((A)decl)list)) []),rshape) |++
           MAP (\(x,y,z,t). (x,y,pan_globals_compile nctxt z,t))
               (functions (fperm_decs start (new_main_name code) code))` THEN
   MP_TAC PPASS2AUX_ctsd_code THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MP_TAC PPASS2AUX_ctsd_init THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `t':(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
   TRANS_TAC EQ_TRANS `pan_semantics (t':(A,FFI)pan_state) (new_main_name (code:((A)decl)list))` THEN
   CONJ_TAC THENL
    [CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC(INST [`nctxt:(A)pan_globals_context`,`ctxt:(A)pan_globals_context`]
                       pan_globalsProof_state_rel_imp_semantics) THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC PPASS2AUX_state_rel_code_locals THEN ASM_SIMP_TAC[];
     CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC(INST [`nested_seq (ndecls:((A)panLang_prog)list)`,`body:(A)panLang_prog`;
                        `pan_globals_compile nctxt
                           (fperm start (new_main_name (code:((A)decl)list))
                              (body:(A)panLang_prog))`,`body':(A)panLang_prog`;
                        `[]:(mlstring#shape)list`,`args':(mlstring#shape)list`]
                       semantics_init_call') THEN
     REWRITE_TAC[pan_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[]]);;

let compile_exp_localised = prove
 (`!ctxt e. localised_exp (pan_globals_compile_exp (ctxt:(A)pan_globals_context) e)`,
  REC_IND_TAC pan_globals_compile_exp_ind THEN
  RW[pan_globals_compile_exp_def; localised_exp_simps; ALL_MAP; GSYM ALL_MEM; o_THM] THEN
  REPEAT(TOP_CASE_TAC THEN RW[localised_exp_simps; ALL]));;

let localised_exp_shape_val = prove
 (`(!sh. localised_exp (shape_val sh:(A)panLang_exp)) /\
   (!shs. ALL localised_exp (shape_vals shs:((A)panLang_exp)list))`,
  MATCH_MP_TAC (cake_ind "shape_val") THEN
  RW[shape_val_def; localised_exp_simps; ALL]);;

let compile_localised = prove
 (`!ctxt body. localised_prog (pan_globals_compile (ctxt:(A)pan_globals_context) body)`,
  REC_IND_TAC pan_globals_compile_ind THEN
  RW[pan_globals_compile_def; localised_prog_def; compile_exp_localised; ALL_MAP;
     GSYM ALL_MEM; o_THM; localised_exp_simps] THEN
  REPEAT(TOP_CASE_TAC THEN
         RW[localised_prog_def; compile_exp_localised; localised_exp_simps; ALL_MAP;
            GSYM ALL_MEM; o_THM; ALL; localised_exp_shape_val]) THEN
  GVS(all_case_eqs()));;

let PPASS2AUX_compile_decs_split_tac =
  REC_IND_TAC pan_globals_compile_decs_ind THEN
  REWRITE_TAC[pan_globals_compile_decs_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT STRIP_TAC THEN REPEAT(PPASS2AUX_split_top_tac THEN CAKE_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND];;

let compile_decs_localised = prove
 (`!ctxt code.
     ALL (localised_prog o FST o SND o SND)
         (functions (FST (SND (pan_globals_compile_decs (ctxt:(A)pan_globals_context) code))))`,
  PPASS2AUX_compile_decs_split_tac THEN
  ASM_REWRITE_TAC[functions_def; ALL; o_THM; fun_decl_INFO.ri_accfupds; K_THM;
                  compile_localised]);;

let compile_decs_localised' = prove
 (`!ctxt code.
     ALL (localised_prog o FST o SND o SND)
         (functions (FST (SND (SND (pan_globals_compile_decs
                                     (ctxt:(A)pan_globals_context) code)))))`,
  PPASS2AUX_compile_decs_split_tac THEN
  ASM_REWRITE_TAC[functions_def; ALL; o_THM; fun_decl_INFO.ri_accfupds; K_THM;
                  compile_localised]);;

let compile_decs_localised_main = prove
 (`!ctxt code.
     ALL localised_prog (FST (pan_globals_compile_decs (ctxt:(A)pan_globals_context) code))`,
  PPASS2AUX_compile_decs_split_tac THEN
  ASM_REWRITE_TAC[ALL; localised_prog_def; localised_exp_simps; compile_exp_localised]);;

let nested_seqs_localised = prove
 (`!ps:((A)panLang_prog)list. localised_prog (nested_seq ps) <=> ALL localised_prog ps`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[nested_seq_def; localised_prog_def; ALL]);;

let compile_top_localised = prove
 (`!pan_code main.
     ALL (localised_prog o FST o SND o SND)
         (functions (pan_globals_compile_top (pan_code:((A)decl)list) main))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_globals_compile_top_def] THEN
   QCASES_ON "ALOOKUP (functions (pan_code:((A)decl)list)) (main:mlstring)" THEN
   CAKE_REWRITE_TAC[functions_def; ALL] THEN
   RENAME1 "ALOOKUP (functions pan_code) main = SOME x" THEN
   PAIR_CASES_ON `x:(mlstring#shape)list#(A)panLang_prog#shape` THEN CAKE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PPASS2AUX_split_top_tac THEN CAKE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MAP_EVERY (fun th -> MP_TAC(ISPECL
       [`pan_globals_context_REC (FEMPTY:(mlstring,shape#A word)fmap) (word 0:A word)
           (word_mul (bytes_in_word:A word)
              (word (SUM (MAP size_of_shape (dec_shapes
                 (fperm_decs main (new_main_name pan_code)
                    (resort_decls (pan_code:((A)decl)list))))))))`;
        `fperm_decs main (new_main_name pan_code) (resort_decls (pan_code:((A)decl)list))`] th))
     [compile_decs_localised; compile_decs_localised'; compile_decs_localised_main] THEN
   ASM_REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[functions_append; functions_def; ALL_APPEND; ALL; o_THM;
                   fun_decl_INFO.ri_accessors; localised_prog_def; nested_seqs_localised;
                   ALL_MAP; localised_exp_simps] THEN
   REWRITE_TAC[GSYM ALL_MEM; o_THM; localised_exp_simps] THEN CAKE_REWRITE_TAC[]);;

let ALL_DISTINCT_compile_top = prove
 (`!start code:((A)decl)list.
     ALL_DISTINCT (MAP FST (functions code))
     ==> ALL_DISTINCT (MAP FST (functions (pan_globals_compile_top code start)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pan_globals_compile_top_def] THEN
   QCASES_ON "ALOOKUP (functions (code:((A)decl)list)) (start:mlstring)" THEN
   CAKE_REWRITE_TAC[functions_def; MAP; ALL_DISTINCT] THEN
   RENAME1 "ALOOKUP (functions code) start = SOME x" THEN
   PAIR_CASES_ON `x:(mlstring#shape)list#(A)panLang_prog#shape` THEN CAKE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PPASS2AUX_split_top_tac THEN CAKE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_decs_exns_are_exns) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_decs_preserve_functions) THEN
   ASM_REWRITE_TAC[functions_append; functions_FILTER_exn_decl; functions_def; APPEND; MAP;
                   ALL_DISTINCT; fun_decl_INFO.ri_accessors] THEN
  CONJ_TAC THENL
    [SUBGOAL_THEN `MEM (start:mlstring) (MAP FST (functions (code:((A)decl)list)))` ASSUME_TAC THENL
      [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(start:mlstring,x0:(mlstring#shape)list,
                                              x1:(A)panLang_prog,x2:shape)` THEN
       REWRITE_TAC[FST] THEN MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     SUBGOAL_THEN `~MEM (new_main_name (code:((A)decl)list)) (MAP FST (functions code))`
       ASSUME_TAC THENL [MESON_TAC[new_main_name_correct]; ALL_TAC] THEN
     REWRITE_TAC[functions_fperm_decs; MAP_MAP_o; o_DEF; PPASS2AUX_FST_fperm4;
                 resort_decls_preserve_functions] THEN
     REWRITE_TAC[MEM_MAP; fperm_name_def; NOT_EXISTS_THM] THEN
     X_GEN_TAC `p:mlstring#(mlstring#shape)list#(A)panLang_prog#shape` THEN
     REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[MEM_MAP];
     MATCH_MP_TAC ALL_DISTINCT_fperm_decs THEN
     ASM_REWRITE_TAC[resort_decls_preserve_functions]]);;
