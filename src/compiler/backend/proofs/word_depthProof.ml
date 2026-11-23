(* ========================================================================= *)
(* word_depthProof: port of HOL4 compiler/backend/proofs/                    *)
(* word_depthProofScript.sml (CakeML v3479).                                 *)
(* Proves correctness of the max_depth applied to the call graph of a       *)
(* wordLang program as produced by the word_depth$call_graph function.      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang, wordSem and wordProps are those of their files  *)
(*   (wl_evaluate, wl_state_stack_max, ...): HOL4 s.f is wl_state_f s.      *)
(* - The call_tree constructors are those of word_depth.ml                 *)
(*   (word_depth_Leaf, Unknown, word_depth_Call, word_depth_Branch, ...).   *)
(* - HOL4's [local,simp] theorems of this script are ordinary theorems,    *)
(*   used explicitly.                                                       *)
(* - WDPAUX_ names are local helpers.                                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/semantics/backendProps.ml";;

type_invention_error := true;;

(* HOL4 line 13 *)
let option_le_X_MAX_X = prove
 (`!x m:num option. option_le x (OPTION_MAP2 MAX m x) /\ option_le x (OPTION_MAP2 MAX x m)`,
  REPEAT GEN_TAC THEN CASES_ON `x:num option` THEN CASES_ON `m:num option` THEN
  RW[option_le_def; OPTION_MAP2_THM] THEN ARITH_TAC);;

(* HOL4 line 20 *)
let OPTION_MAP2_MAX_IDEMPOT = prove
 (`!x:num option. OPTION_MAP2 MAX x x = x`,
  GEN_TAC THEN CASES_ON `x:num option` THEN RW[OPTION_MAP2_THM] THEN ARITH_TAC);;

(* HOL4 line 26 *)
let OPTION_MAP2_SOME_0 = prove
 (`!x:num option. OPTION_MAP2 (+) x (SOME 0) = x /\ OPTION_MAP2 MAX x (SOME 0) = x`,
  GEN_TAC THEN CASES_ON `x:num option` THEN RW[OPTION_MAP2_THM] THEN ARITH_TAC);;

(* HOL4 line 33 *)
let max_depth_mk_Branch = prove
 (`!s t1 t2. max_depth s (mk_Branch t1 t2) = max_depth s (word_depth_Branch t1 t2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_Branch_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[max_depth_def; OPTION_MAP2_MAX_IDEMPOT] THEN
  CASES_ON `max_depth s t1` THEN CASES_ON `max_depth s t2` THEN
  RW[OPTION_MAP2_THM] THEN ARITH_TAC);;

(* HOL4 line 41 *)
let MEM_max_depth_graphs = prove
 (`!ns name (y:num#(A)wl_prog) ss xs (funs:(num#(A)wl_prog)spt) code.
     MEM name ns /\ lookup name code = SOME y ==>
     option_le (max_depth_graphs ss [name] xs funs code)
               (max_depth_graphs ss ns xs funs code)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`name:num`; `a:num`; `body:(A)wl_prog`; `ss:num spt`; `xs:num list`;
    `funs:(num#(A)wl_prog)spt`; `code:(num#(A)wl_prog)spt`] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    ASM_REWRITE_TAC[max_depth_graphs_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[OPTION_MAP2_SOME_0; option_le_max; option_le_max_right; option_le_X_MAX_X;
                option_le_refl; option_le_SOME_0];
    FIRST_X_ASSUM(MP_TAC o SPECL [`name:num`; `a:num,(body:(A)wl_prog)`; `ss:num spt`;
      `xs:num list`; `funs:(num#(A)wl_prog)spt`; `code:(num#(A)wl_prog)spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [max_depth_graphs_def] THEN
    CASES_ON `lookup h (code:(num#(A)wl_prog)spt)` THEN CASE_REWRITE_TAC[option_le_def] THEN
    CASES_ON `a':num#(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[option_le_trans; option_le_X_MAX_X]]);;

let WDPAUX_MAX_MONO = prove
 (`!a1 a2 b1 b2:num option. option_le a1 a2 /\ option_le b1 b2 ==>
     option_le (OPTION_MAP2 MAX a1 b1) (OPTION_MAP2 MAX a2 b2)`,
  REPEAT GEN_TAC THEN MAP_EVERY (fun t -> CASES_ON t)
    [`a1:num option`; `a2:num option`; `b1:num option`; `b2:num option`] THEN
  RW[option_le_def; OPTION_MAP2_THM] THEN REWRITE_TAC[MAX] THEN ASM_ARITH_TAC);;

let WDPAUX_CG_MONO_TAC : tactic =
  REWRITE_TAC[call_graph_def; max_depth_mk_Branch; max_depth_def; option_le_refl] THEN
  REPEAT (MATCH_MP_TAC WDPAUX_MAX_MONO THEN CONJ_TAC) THEN
  TRY (MATCH_ACCEPT_TAC option_le_refl) THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

(* HOL4 line 61 *)
let option_le_max_depth_graph = prove
 (`!funs h ns1 t (x1:(A)wl_prog) ns2 ss.
     set_of_list ns2 SUBSET set_of_list ns1 /\ LENGTH ns2 <= LENGTH ns1 ==>
     option_le (max_depth ss (call_graph funs h ns1 t x1))
               (max_depth ss (call_graph funs h ns2 t x1))`,
  MATCH_MP_TAC call_graph_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN TRY WDPAUX_CG_MONO_TAC THEN
  REWRITE_TAC[call_graph_def] THEN
  CASES_ON `dest:num option` THEN CASE_REWRITE_TAC[max_depth_def; option_le_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[max_depth_def; option_le_SOME_0] THEN
  (fun (asl,w as g) ->
     let ret = find_term (fun t -> is_var t && fst(dest_var t) = "ret") w in
     let ty = hd(snd(dest_type(type_of ret))) in
     let tm = mk_neg(mk_conj(`MEM (a:num) ns2`,
                mk_eq(ret, mk_const("NONE",[ty,`:A`])))) in
     SUBGOAL_THEN tm (fun th -> REWRITE_TAC[th]) g) THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(rator(rator(concl th)))) = "SUBSET"
      with Failure _ -> false)) THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; PAIR_EQ]) THEN
  CASES_ON `lookup a (funs:(num#(A)wl_prog)spt)` THEN
  CASE_REWRITE_TAC[max_depth_def; option_le_def] THEN
  CASES_ON `a':num#(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     let ret = find_term (fun t -> is_var t && fst(dest_var t) = "ret") w in
     let ty = hd(snd(dest_type(type_of ret))) in
     ASM_CASES_TAC (mk_eq(ret, mk_const("NONE",[ty,`:A`]))) g) THENL
   [FIRST_ASSUM(fun th -> if is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "ret"
      then SUBST1_TAC th else NO_TAC) THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[max_depth_def; option_le_SOME_0] THEN
    SUBGOAL_THEN `LENGTH (ns2:num list) < total' /\
      set_of_list (CONS (a:num) ns2) SUBSET set_of_list (CONS a ns) /\
      LENGTH (CONS a ns2) <= LENGTH (CONS a ns)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH; set_of_list; LE_SUC] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(rator(rator(concl th)))) = "SUBSET"
        with Failure _ -> false)) THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `LENGTH (ns2:num list) <= LENGTH (ns:num list)`)) THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `LENGTH (ns:num list) < total'`)) THEN
      REWRITE_TAC[SUBSET; IN_INSERT] THEN MESON_TAC[LET_TRANS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[max_depth_mk_Branch; max_depth_def] THEN
    MATCH_MP_TAC WDPAUX_MAX_MONO THEN REWRITE_TAC[option_le_refl] THEN
    ASM_MESON_TAC[];
    (fun (asl,w as g) ->
       let ret = find_term (fun t -> is_var t && fst(dest_var t) = "ret") w in
       DISJ_CASES_THEN MP_TAC (ISPEC ret (cases "option")) g) THEN
    ASM_REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "ret"
      then SUBST1_TAC th else NO_TAC) THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    (fun (asl,w as g) ->
       let h = find_term (fun t -> is_var t && fst(dest_var t) = "handler") w in
       DISJ_CASES_THEN MP_TAC (ISPEC h (cases "option")) g) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "handler"
      then SUBST1_TAC th else NO_TAC) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[max_depth_mk_Branch; max_depth_def] THEN
    REPEAT (MATCH_MP_TAC WDPAUX_MAX_MONO THEN CONJ_TAC) THEN
    REWRITE_TAC[option_le_refl] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 103 *)
let option_le_max_depth_graphs = prove
 (`!ns ns1 ns2 ss (funs:(num#(A)wl_prog)spt) (funs2:(num#(A)wl_prog)spt).
     set_of_list ns2 SUBSET set_of_list ns1 /\ LENGTH ns2 <= LENGTH ns1 ==>
     option_le (max_depth_graphs ss ns ns1 funs funs2)
               (max_depth_graphs ss ns ns2 funs funs2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[max_depth_graphs_def; option_le_refl] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `lookup h (funs2:(num#(A)wl_prog)spt)` THEN CASE_REWRITE_TAC[option_le_def] THEN
  CASES_ON `a:num#(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC WDPAUX_MAX_MONO THEN REWRITE_TAC[option_le_refl] THEN
  MATCH_MP_TAC WDPAUX_MAX_MONO THEN CONJ_TAC THENL
   [MATCH_MP_TAC option_le_max_depth_graph THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 117 *)
let LENGTH_LESS_size = prove
 (`!name ns (funs:(A)spt) y.
     ~MEM name ns /\ set_of_list ns SUBSET domain funs /\ ALL_DISTINCT ns /\
     lookup name funs = SOME y ==>
     LENGTH ns < sptree_size funs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[size_domain] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP ALL_DISTINCT_CARD_LIST_TO_SET) THEN
  MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_domain; PSUBSET] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(name:num) IN domain (funs:(A)spt)` MP_TAC THENL
   [REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for max_depth_call_graph_lemma (WDPAUX_ names): facts about the   *)
(* stack fields under the wordLang constructs, and one tactic per case of   *)
(* the induction on evaluate                                                *)
(* ------------------------------------------------------------------------- *)

let WDPAUX_MAP2_NONE = prove
 (`!(f:A->B->C) x y. OPTION_MAP2 f x NONE = NONE /\ OPTION_MAP2 f NONE y = NONE`,
  REWRITE_TAC[OPTION_MAP2_DEF; IS_SOME_DEF]);;
let WDPAUX_sh_mem_set_var_const = prove
 (`sh_mem_set_var r v (s:(A,C,FFI)wl_state) = (x:((W)wl_result)option,s') ==>
   wl_state_stack_size s' = wl_state_stack_size s /\
   ((x = NONE \/ (?k. x = SOME (wordSem_Break k)) \/ (?k. x = SOME (wordSem_Continue k))) ==>
    wl_state_locals_size s' = wl_state_locals_size s)`,
  STRUCT_CASES_TAC (ISPEC `r:((FFI)ffi_result)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:(FFI)ffi_result` (cases "ffi_result"))) THEN
  REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[wl_set_var_def; wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM]);;

let WDPAUX_share_inst_const = prove
 (`share_inst op v c (s:(A,C,FFI)wl_state) = (res:((W)wl_result)option, s') ==>
   wl_state_stack_size s' = wl_state_stack_size s /\
   ((res = NONE \/ (?k. res = SOME (wordSem_Break k)) \/
     (?k. res = SOME (wordSem_Continue k))) ==>
    wl_state_locals_size s' = wl_state_locals_size s)`,
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[share_inst_def] THEN
  TRY (MATCH_ACCEPT_TAC WDPAUX_sh_mem_set_var_const) THEN
  EVERY_CASE_TAC THEN TRY (REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result"]) THEN
    TRY (FIRST_ASSUM CONTR_TAC) THEN SIMP[] THEN NO_TAC) THEN
  REWRITE_TAC[wl_sh_mem_store_def; wl_sh_mem_store_byte_def; wl_sh_mem_store16_def;
              wl_sh_mem_store32_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  SIMP[wl_flush_state_def]);;
let WDPAUX_NR_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  IL2AUX_FACTS_TAC [inst_const_full; mem_store_const; jump_exc_const; assign_const_full;
                    share_inst_const; wl_alloc_const; WDPAUX_share_inst_const] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result";
    injectivity "wl_result"; call_graph_def; max_depth_def; OPTION_MAP2_THM; WDPAUX_MAP2_NONE]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  ASM_REWRITE_TAC[call_graph_def; max_depth_def; wl_state_INFO.ri_accfupds; K_THM;
    wl_flush_state_def; wl_set_var_def; wl_set_vars_def; wl_set_store_def; wl_set_fp_var_def;
    wl_unset_var_def; wl_dec_clock_def; wl_state_INFO.ri_fupdfupds; K_o_THM;
    option_le_X_MAX_X; option_DISTINCT; option_INJ; distinctness "wl_result"; OPTION_MAP2_SOME_0;
    OPTION_MAP2_THM; WDPAUX_MAP2_NONE; option_le_def] THEN
  REWRITE_TAC[option_le_X_MAX_X] THEN
  TRY (ASM_MESON_TAC[]);;
let WDPAUX_push_env_NONE = prove
 (`!envs (s:(A,C,FFI)wl_state). ?l.
     wl_state_stack (wl_push_env envs NONE s) =
       CONS (StackFrame (wl_state_locals_size s) (toAList (FST envs)) l NONE) (wl_state_stack s) /\
     wl_state_locals_size (wl_push_env envs NONE s) = wl_state_locals_size s /\
     wl_state_stack_size (wl_push_env envs NONE s) = wl_state_stack_size s /\
     wl_state_stack_max (wl_push_env envs NONE s) =
       OPTION_MAP2 MAX (wl_state_stack_max s)
         (wl_stack_size (CONS (StackFrame (wl_state_locals_size s) (toAList (FST envs)) l NONE)
                              (wl_state_stack s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `env_to_list (SND (envs:((A)word_loc)spt#((A)word_loc)spt)) (wl_state_permute (s:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`l:(num#(A)word_loc)list`; `p:num->num->num`] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN EXISTS_TAC `l:(num#(A)word_loc)list` THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]);;

let WDPAUX_pop_env_locals_size = prove
 (`!(x:(A,C,FFI)wl_state) y n l0 l rest.
     wl_pop_env x = SOME y /\
     wl_state_stack x = CONS (StackFrame n l0 l NONE) rest ==>
     wl_state_locals_size y = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_pop_env (x:(A,C,FFI)wl_state) = SOME y` THEN
  ASM_REWRITE_TAC[wl_pop_env_def] THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]);;
let WDPAUX_key_eq_pop = prove
 (`!(x:(A,C,FFI)wl_state) y n l0 l rest.
     s_key_eq (CONS (StackFrame n l0 l NONE) rest) (wl_state_stack x) /\
     wl_pop_env x = SOME y ==>
     wl_state_locals_size y = n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `wl_state_stack (x:(A,C,FFI)wl_state)` (cases "list")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[s_key_eq_def] THEN
  MP_TAC(ISPEC `a0:(A)stack_frame` (cases "stack_frame")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[s_frame_key_eq_def2] THEN STRIP_TAC THEN
  MATCH_MP_TAC WDPAUX_pop_env_locals_size THEN
  MAP_EVERY EXISTS_TAC [`x:(A,C,FFI)wl_state`; `a1':(num#(A)word_loc)list`;
    `a2:(num#(A)word_loc)list`; `a1:((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `NONE = (a3:(num#num#num)option)`)) THEN
  REWRITE_TAC[]);;
let WDPAUX_alloc_case = prove
 (`!w names (s:(A,C,FFI)wl_state) res s1.
     wl_alloc w names s = (res, s1) /\ ~(res = SOME wl_Error) ==>
     option_le (wl_state_stack_max s1)
       (OPTION_MAP2 MAX (wl_state_stack_max s)
         (OPTION_MAP2 (+) (wl_state_locals_size s) (wl_stack_size (wl_state_stack s)))) /\
     wl_state_stack_size s1 = wl_state_stack_size s /\
     ((res = NONE \/ (?k. res = SOME (wordSem_Break k)) \/
       (?k. res = SOME (wordSem_Continue k))) ==>
      wl_state_locals_size s1 = wl_state_locals_size s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  IL2AUX_FACTS_TAC [gc_const; wl_pop_env_const; gc_s_key_eq] THEN
  (fun (asl,w as g) ->
     let pe = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "wl_push_env"
                                  with Failure _ -> false)
                (end_itlist (curry mk_conj) (map (concl o snd) asl)) in
     let envs = hd (snd (strip_comb pe)) and st = last (snd (strip_comb pe)) in
     X_CHOOSE_THEN `lf:(num#(A)word_loc)list` STRIP_ASSUME_TAC
       (SPECL [envs; st] WDPAUX_push_env_NONE) g) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM; stack_size_eq2;
    stack_size_frame_def; option_le_refl] THEN
  TRY (MATCH_MP_TAC WDPAUX_key_eq_pop THEN
       FIRST_ASSUM(fun th -> let c = concl th in
         if is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "wl_pop_env"
                        with Failure _ -> false)
         then EXISTS_TAC (rand (lhs c)) else NO_TAC) THEN
       MAP_EVERY EXISTS_TAC [`toAList (FST (a:((A)word_loc)spt#((A)word_loc)spt))`;
         `lf:(num#(A)word_loc)list`; `wl_state_stack (s:(A,C,FFI)wl_state)`] THEN
       CONJ_TAC THENL
        [FIRST_ASSUM(fun pf -> let c = concl pf in
           if is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "wl_state_stack" &&
                              (try fst(dest_const(fst(strip_comb(rand(lhs c))))) = "wl_push_env"
                               with Failure _ -> false)
                          with Failure _ -> false)
           then FIRST_ASSUM(fun th ->
             if (try fst(dest_const(fst(strip_comb(concl th)))) = "s_key_eq"
                 with Failure _ -> false)
             then ACCEPT_TAC (REWRITE_RULE[pf] th) else NO_TAC)
           else NO_TAC);
         FIRST_ASSUM ACCEPT_TAC]));;
let WDPAUX_ALLOC_BOUND = prove
 (`!x m l ss g:num option.
     option_le x (OPTION_MAP2 MAX m (OPTION_MAP2 (+) l ss)) ==>
     option_le x (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss (OPTION_MAP2 MAX g l)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (fun t -> CASES_ON t)
    [`x:num option`; `m:num option`; `l:num option`; `ss:num option`; `g:num option`] THEN
  RW[option_le_def; OPTION_MAP2_THM] THEN REWRITE_TAC[MAX] THEN ASM_ARITH_TAC);;

let WDPAUX_ALLOC_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  (fun (asl,w as g) ->
     let al = snd(find (fun (_,th) -> is_eq (concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_alloc" with Failure _ -> false)) asl) in
     let r = fst(dest_pair(rhs(concl al))) in
     let netm = mk_neg(mk_eq(r, `SOME (wl_Error:(A)wl_result)`)) in
     let ne = try snd(find (fun (_,th) -> aconv (concl th) netm) asl)
              with Failure _ -> EQT_ELIM (REWRITE_CONV[option_DISTINCT; option_INJ;
                                   distinctness "wl_result"] netm) in
     MP_TAC (MATCH_MP WDPAUX_alloc_case (CONJ al ne)) g) THEN
  ASM_REWRITE_TAC[call_graph_def; max_depth_def; OPTION_MAP2_SOME_0] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY (MATCH_MP_TAC WDPAUX_ALLOC_BOUND THEN FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (ASM_MESON_TAC[]);;
let WDPAUX_MT_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result";
    call_graph_def]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(fun ih -> if is_imp (concl ih) && not (IL2AUX_is_eval_eq (lhand (concl ih)))
    then MP_TAC ih else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     let ev = snd(find (fun (_,th) -> IL2AUX_is_eval_eq (concl th)) asl) in
     let (res1,s1') = dest_pair (rhs (concl ev)) in
     let ih = lhand w in
     let vs,_ = strip_forall ih in
     DISCH_THEN(MP_TAC o SPECL (res1 :: s1' :: tl (tl vs))) g) THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; call_graph_def] THEN
  REWRITE_TAC[option_DISTINCT; distinctness "wl_result"; option_INJ] THEN ASM_MESON_TAC[];;
let WDPAUX_SEQ_BOUND = prove
 (`!x0 x1 m ss g d1 d2:num option.
     option_le x0 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss (OPTION_MAP2 MAX g d1))) /\
     option_le x1 (OPTION_MAP2 MAX x0 (OPTION_MAP2 (+) ss (OPTION_MAP2 MAX g d2))) ==>
     option_le x1 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss
       (OPTION_MAP2 MAX g (OPTION_MAP2 MAX d1 d2))))`,
  REPEAT GEN_TAC THEN MAP_EVERY (fun t -> CASES_ON t)
    [`x0:num option`; `x1:num option`; `m:num option`; `ss:num option`; `g:num option`;
     `d1:num option`; `d2:num option`] THEN
  RW[option_le_def; OPTION_MAP2_THM] THEN REWRITE_TAC[MAX] THEN ASM_ARITH_TAC);;

let WDPAUX_BRANCH_BOUND = prove
 (`!x0 m ss g d1 d2:num option.
     option_le x0 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss (OPTION_MAP2 MAX g d1))) ==>
     option_le x0 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss
       (OPTION_MAP2 MAX g (OPTION_MAP2 MAX d1 d2)))) /\
     option_le x0 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss
       (OPTION_MAP2 MAX g (OPTION_MAP2 MAX d2 d1))))`,
  REPEAT GEN_TAC THEN MAP_EVERY (fun t -> CASES_ON t)
    [`x0:num option`; `m:num option`; `ss:num option`; `g:num option`;
     `d1:num option`; `d2:num option`] THEN
  RW[option_le_def; OPTION_MAP2_THM] THEN REWRITE_TAC[MAX] THEN ASM_ARITH_TAC);;
let WDPAUX_SEQ_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`c1:(A)wl_prog`; `c2:(A)wl_prog`; `s:(A,C,FFI)wl_state`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  MAP_EVERY X_GEN_TAC [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`;
    `funs:(num#(A)wl_prog)spt`; `n:num`; `ns:num list`; `funs2:(num#(A)wl_prog)spt`] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[call_graph_def; max_depth_mk_Branch; max_depth_def;
    OPTION_MAP2_NONE; DE_MORGAN_THM]) THEN
  REWRITE_TAC[call_graph_def; max_depth_mk_Branch; max_depth_def; OPTION_MAP2_NONE;
    DE_MORGAN_THM] THEN
  FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  MP_TAC(ISPEC `wl_evaluate (c1:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:((A)wl_result)option` (X_CHOOSE_THEN `s0:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r0:((A)wl_result)option = NONE` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(r0:((A)wl_result)option) = res`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(s0:(A,C,FFI)wl_state) = s1`)) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`;
      `funs:(num#(A)wl_prog)spt`; `n:num`; `ns:num list`; `funs2:(num#(A)wl_prog)spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[OPTION_MAP2_NONE; DE_MORGAN_THM] THEN
    MESON_TAC[WDPAUX_BRANCH_BOUND]] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `r0:((A)wl_result)option = NONE`)) THEN
  (fun (asl,w as g) ->
     let (_,bimp) = dest_conj w in
     ASM_CASES_TAC (lhand bimp) g) THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DE_MORGAN_THM] o check (fun th -> is_neg (concl th) &&
      is_conj (rand (concl th)))) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WDPAUX_MAP2_NONE; option_le_def]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    is_neg (lhand (concl th)))) THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`NONE:((A)wl_result)option`; `s0:(A,C,FFI)wl_state`;
      `funs:(num#(A)wl_prog)spt`; `n:num`; `ns:num list`; `funs2:(num#(A)wl_prog)spt`]) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC `s0:(A,C,FFI)wl_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`;
      `funs:(num#(A)wl_prog)spt`; `n:num`; `ns:num list`; `funs2:(num#(A)wl_prog)spt`]) THEN
  SUBGOAL_THEN `subspt (funs2:(num#(A)wl_prog)spt) (wl_state_code (s0:(A,C,FFI)wl_state)) /\
     wl_stack_size (wl_state_stack s0) = wl_stack_size (wl_state_stack (s:(A,C,FFI)wl_state))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC `wl_state_code (s:(A,C,FFI)wl_state)` THEN
      ASM_MESON_TAC[evaluate_code_only_grows];
      ASM_MESON_TAC[evaluate_NONE_stack_size_const]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WDPAUX_SEQ_BOUND THEN
  EXISTS_TAC `wl_state_stack_max (s0:(A,C,FFI)wl_state)` THEN ASM_MESON_TAC[];;
(* the conclusion of an induction hypothesis !vs. A1 /\ .. /\ An ==> C, the  *)
(* variables named funs n ns funs2 instantiated with the variables of the     *)
(* goal of these names, the others by matching the Ai with the assumptions   *)
(* (or with a side of an assumption equation), the Ai then proved by        *)
(* rewriting with the assumptions                                            *)
let WDPAUX_IH_TAC (ih0:thm) : tactic = fun (asl,w as g) ->
  let th = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] ih0 in
  let vs,bod = strip_forall (concl th) in
  let ant,_ = dest_imp bod in
  let gvs = freesl (w :: map (concl o snd) asl) in
  let theta0 = mapfilter (fun v ->
      let base = implode (filter (fun c -> c <> "'") (explode (fst(dest_var v)))) in
      if mem base ["funs";"n";"ns";"funs2"] then
        (find (fun u -> fst(dest_var u) = base && type_of u = type_of v) gvs, v)
      else failwith "") vs in
  let facts = map (concl o snd) asl in
  let cands = facts @ flat (map (fun f -> if is_eq f then [lhs f; rhs f] else []) facts) in
  let rec go theta cjs =
    match cjs with
      [] -> theta
    | c::rest ->
        let c' = vsubst theta c in
        let open_vs = filter (fun v -> mem v vs && not (exists (fun (_,x) -> x = v) theta))
                             (frees c') in
        if open_vs = [] then go theta rest else
        let lcs = subtract (frees c') open_vs in
        let tryc t =
          let (_,tmi,tyi) = term_match lcs c' t in
          if exists (fun (a,b) -> a <> b) tyi then failwith "" else
          tmi in
        let ext = try tryc (find (fun t -> can tryc t) cands) with Failure _ -> [] in
        go (ext @ theta) rest in
  let theta = go theta0 (conjuncts ant) in
  let th1 = SPECL (map (fun v -> try rev_assoc v theta with Failure _ -> v) vs) th in
  let a1 = lhand (concl th1) in
  let ath = EQT_ELIM (REWRITE_CONV (map snd asl @ IL2AUX_res_rws) a1) in
  MP_TAC (MP th1 ath) g;;
let WDPAUX_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  MAP_EVERY X_GEN_TAC [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`;
    `funs:(num#(A)wl_prog)spt`; `n:num`; `ns:num list`; `funs2:(num#(A)wl_prog)spt`] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[call_graph_def; max_depth_mk_Branch; max_depth_def;
    OPTION_MAP2_NONE; DE_MORGAN_THM]) THEN
  REWRITE_TAC[call_graph_def; max_depth_mk_Branch; max_depth_def; OPTION_MAP2_NONE;
    DE_MORGAN_THM] THEN
  FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  (fun (asl,w as g) ->
     let ev = snd(find (fun (_,th) -> IL2AUX_is_eval_eq (concl th)) asl) in
     let lab = if aconv (fst(dest_pair(rand(lhs(concl ev))))) `c1:(A)wl_prog`
               then "ih1" else "ih2" in
     REMOVE_THEN lab WDPAUX_IH_TAC g) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY (FIRST_X_ASSUM(MP_TAC o MATCH_MP WDPAUX_BRANCH_BOUND o check (fun th ->
         try fst(dest_const(fst(strip_comb(concl th)))) = "option_le" with Failure _ -> false)) THEN
       SIMP_TAC[]) THEN
  ASM_MESON_TAC[];;
let WDPAUX_stack_size_const = prove
 (`!c (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (c,s) = (res,s1) /\
     (res = NONE \/ (?k. res = SOME (wordSem_Break k)) \/ (?k. res = SOME (wordSem_Continue k))) ==>
     wl_stack_size (wl_state_stack s1) = wl_stack_size (wl_state_stack s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(A)wl_prog`; `s:(A,C,FFI)wl_state`] wl_evaluate_stack_swap) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[wl_s_key_eq_stack_size]);;
let WDPAUX_loop_err = prove
 (`!x:((W)wl_result)option.
     (wl_cont_loop x ==> ~(x = SOME wl_Error)) /\
     (~(wl_exit_loop x = SOME wl_Error) ==> ~(x = SOME wl_Error)) /\
     (wl_cont_loop x ==> (x = NONE \/ (?k. x = SOME (wordSem_Continue k)))) /\
     (wl_exit_loop x = NONE ==> x = NONE) /\
     (!k. wl_exit_loop x = SOME (wordSem_Break k) ==> ~(x = SOME wl_Error)) /\
     (!k. wl_exit_loop x = SOME (wordSem_Continue k) ==> ~(x = SOME wl_Error)) /\
     (!k. wl_exit_loop x = SOME (wordSem_Break k) ==> ?k'. x = SOME (wordSem_Break k')) /\
     (!k. wl_exit_loop x = SOME (wordSem_Continue k) ==> ?k'. x = SOME (wordSem_Continue k')) /\
     (~(wl_cont_loop x) /\ ~(x = SOME (wordSem_Break 0)) /\
      (wl_exit_loop x = NONE \/ (?k. wl_exit_loop x = SOME (wordSem_Break k)) \/
       (?k. wl_exit_loop x = SOME (wordSem_Continue k))) ==>
      (?k. x = SOME (wordSem_Break k)) \/ (?k. x = SOME (wordSem_Continue k)))`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:((W)wl_result)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:(W)wl_result` (cases "wl_result"))) THEN
  REWRITE_TAC[wl_cont_loop_def; wl_exit_loop_def; option_DISTINCT; option_INJ;
    distinctness "wl_result"; injectivity "wl_result"] THEN
  MESON_TAC[]);;

(* WDPAUX_IH_TAC with extra rewrites for the side conditions *)
let WDPAUX_IH_RW_TAC (rws:thm list) (ih0:thm) : tactic = fun (asl,w as g) ->
  let th = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] ih0 in
  let vs,bod = strip_forall (concl th) in
  let ant,_ = dest_imp bod in
  let gvs = freesl (w :: map (concl o snd) asl) in
  let theta0 = mapfilter (fun v ->
      let base = implode (filter (fun c -> c <> "'") (explode (fst(dest_var v)))) in
      if mem base ["funs";"n";"ns";"funs2"] then
        (find (fun u -> fst(dest_var u) = base && type_of u = type_of v) gvs, v)
      else failwith "") vs in
  let facts = map (concl o snd) asl in
  let cands = facts @ flat (map (fun f -> if is_eq f then [lhs f; rhs f] else []) facts) in
  let rec go theta cjs =
    match cjs with
      [] -> theta
    | c::rest ->
        let c' = vsubst theta c in
        let open_vs = filter (fun v -> mem v vs && not (exists (fun (_,x) -> x = v) theta))
                             (frees c') in
        if open_vs = [] then go theta rest else
        let lcs = subtract (frees c') open_vs in
        let tryc t =
          let (_,tmi,tyi) = term_match lcs c' t in
          if exists (fun (a,b) -> a <> b) tyi then failwith "" else
          tmi in
        let ext = try tryc (find (fun t -> can tryc t) cands) with Failure _ -> [] in
        go (ext @ theta) rest in
  let theta = go theta0 (conjuncts ant) in
  let th1 = SPECL (map (fun v -> try rev_assoc v theta with Failure _ -> v) vs) th in
  let a1 = lhand (concl th1) in
  let ath = EQT_ELIM (REWRITE_CONV (map snd asl @ IL2AUX_res_rws @ rws) a1) in
  MP_TAC (MP th1 ath) g;;
let WDPAUX_LOOP_BOUND = prove
 (`!x1 x0 m ss g d:num option.
     option_le x0 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss (OPTION_MAP2 MAX g d))) /\
     option_le x1 (OPTION_MAP2 MAX x0 (OPTION_MAP2 (+) ss (OPTION_MAP2 MAX g d))) ==>
     option_le x1 (OPTION_MAP2 MAX m (OPTION_MAP2 (+) ss (OPTION_MAP2 MAX g d)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (fun t -> CASES_ON t)
    [`x1:num option`; `x0:num option`; `m:num option`; `ss:num option`; `g:num option`;
     `d:num option`] THEN
  RW[option_le_def; OPTION_MAP2_THM] THEN REWRITE_TAC[MAX] THEN ASM_ARITH_TAC);;

let WDPAUX_LOOP_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  MAP_EVERY X_GEN_TAC [`res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`;
    `funs:(num#(A)wl_prog)spt`; `n:num`; `ns:num list`; `funs2:(num#(A)wl_prog)spt`] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[call_graph_def]) THEN REWRITE_TAC[call_graph_def] THEN
  (fun (asl,w as g) ->
     let (_,bimp) = dest_conj w in
     ASM_CASES_TAC (lhand bimp) g) THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DE_MORGAN_THM] o check (fun th -> is_neg (concl th) &&
      is_conj (rand (concl th)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[WDPAUX_MAP2_NONE; option_le_def]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    is_neg (lhand (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (IL2AUX_is_eval_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result"]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  IL2AUX_FACTS_TAC [cut_state_const] THEN
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_var (lhs c) && (try fst(dest_const(fst(strip_comb(rhs c)))) =
         "wl_state_locals_fupd" with Failure _ -> false)
    then SUBST_ALL_TAC th else NO_TAC) THEN
  (fun (asl,w as g) ->
     let ev = snd(find (fun (_,th) -> IL2AUX_is_eval_eq (concl th) &&
                  aconv (fst(dest_pair(rand(lhs(concl th))))) `c:(A)wl_prog`) asl) in
     let x = fst(dest_pair(rhs(concl ev))) in
     let lth = ISPEC x WDPAUX_loop_err in
     MAP_EVERY (fun th -> TRY (FIRST_ASSUM(fun a -> ASSUME_TAC (MATCH_MP th a))))
       (CONJUNCTS lth) g) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result";
    injectivity "wl_result"]) THEN
  REMOVE_THEN "ih2" (WDPAUX_IH_RW_TAC [wl_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; distinctness "wl_result";
    injectivity "wl_result"; UNWIND_THM1; UNWIND_THM2; EXISTS_REFL]) THEN
  REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     if exists (fun (_,th) -> IL2AUX_is_eval_eq (concl th) &&
          (try fst(dest_const(fst(strip_comb(fst(dest_pair(rand(lhs(concl th)))))))) = "wl_STOP"
           with Failure _ -> false)) asl
     then ALL_TAC g
     else (REMOVE_THEN "ih1" (K ALL_TAC) THEN ASM_MESON_TAC[]) g) THEN
  (* the recursive call *)
  (SUBGOAL_THEN `wl_state_locals_size (y:(A,C,FFI)wl_state) =
       lookup n (wl_state_stack_size (s:(A,C,FFI)wl_state)) /\
     wl_stack_size (wl_state_stack y) = wl_stack_size (wl_state_stack s) /\
     subspt (funs2:(num#(A)wl_prog)spt) (wl_state_code y)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`c:(A)wl_prog`; `wl_state_locals_fupd (K l) (s:(A,C,FFI)wl_state)`;
        `x:((A)wl_result)option`; `y:(A,C,FFI)wl_state`] WDPAUX_stack_size_const) THEN
      REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC (GEN_ALL subspt_trans) THEN
      EXISTS_TAC `wl_state_code (wl_state_locals_fupd (K l) (s:(A,C,FFI)wl_state))` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
                      ASM_MESON_TAC[evaluate_code_only_grows]]];
    ALL_TAC]) THEN
  REMOVE_THEN "ih1" (WDPAUX_IH_RW_TAC [wl_state_INFO.ri_accfupds; K_THM; wl_dec_clock_def;
    wl_STOP_def; call_graph_def]) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_dec_clock_def; wl_STOP_def;
    call_graph_def] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY (MATCH_MP_TAC WDPAUX_LOOP_BOUND THEN
       EXISTS_TAC `wl_state_stack_max (y:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The call case of max_depth_call_graph_lemma (HOL4: Resume                 *)
(* max_depth_call_graph_lemma[Call]): option arithmetic decided by case      *)
(* splits, facts about the stack around calls, the evaluation of a call     *)
(* by cases, and one tactic per kind of call                                *)
(* ------------------------------------------------------------------------- *)

let WDPAUX_MAX_RULES = prove
 (`(!a b c. a <= MAX b c <=> a <= b \/ a <= c) /\
   (!a b c. MAX a b <= c <=> a <= c /\ b <= c) /\
   (!x a b. x + MAX a b = MAX (x + a) (x + b)) /\
   (!x a b. MAX a b + x = MAX (a + x) (b + x))`,
  REWRITE_TAC[MAX] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* decide a goal H1 ==> .. ==> Hk ==> C of num option arithmetic, where the  *)
(* Hi and C are conjunctions of option_le a b, ~(a = NONE) and a = NONE, and *)
(* a b are built with OPTION_MAP2 MAX, OPTION_MAP2 (+), OPTION_MAP ((+) k),   *)
(* SOME and NONE from other num option terms (the atoms): the atoms are      *)
(* generalized and split, those of the conclusion (of b if it is option_le a *)
(* b) first, then the arithmetic is decided by ARITH_TAC                      *)
let WDPAUX_OPT_DECIDE_TAC : tactic = fun (asl,w as g) ->
  let nty = `:num option` in
  let rec atoms t acc =
    if type_of t = nty then
      (match t with
         Comb(Comb(Comb(Const("OPTION_MAP2",_),_),a),b) -> atoms b (atoms a acc)
       | Comb(Comb(Const("OPTION_MAP",_),_),a) -> atoms a acc
       | Comb(Const("SOME",_),_) -> acc
       | Const("NONE",_) -> acc
       | _ -> if mem t acc then acc else acc @ [t])
    else acc in
  let rec all_atoms t acc =
    match t with
      Comb(Comb(Const("option_le",_),a),b) -> atoms b (atoms a acc)
    | Comb(Comb(Const("=",_),a),b) when type_of a = nty -> atoms b (atoms a acc)
    | Comb(f,x) -> all_atoms x (all_atoms f acc)
    | _ -> acc in
  let rec concl_of t = if is_imp t then concl_of (rand t) else t in
  let c = concl_of w in
  let ca = match c with
             Comb(Comb(Const("option_le",_),_),b) -> atoms b []
           | _ -> all_atoms c [] in
  let aa = all_atoms w ca in
  let sz t = String.length (string_of_term t) in
  let bysize = sort (fun a b -> sz a > sz b) aa in
  let vs = map (fun t -> (t, genvar nty)) aa in
  let gen_tac = MAP_EVERY (fun t -> SPEC_TAC(t, assoc t vs)) bysize in
  let rws = [option_le_def; OPTION_MAP2_THM; OPTION_MAP_DEF; IMP_CLAUSES; option_DISTINCT] in
  (gen_tac THEN REPEAT GEN_TAC THEN
   MAP_EVERY (fun t -> let v = assoc t vs in
      STRUCT_CASES_TAC (ISPEC v (cases "option")) THEN REWRITE_TAC rws) aa THEN
   REWRITE_TAC[WDPAUX_MAX_RULES] THEN ARITH_TAC) g;;

let WDPAUX_pop_env_locals_size_gen = prove
 (`!(t:(A,C,FFI)wl_state) t1 m e0 e h rest.
     wl_pop_env t = SOME t1 /\ wl_state_stack t = CONS (StackFrame m e0 e h) rest
     ==> wl_state_locals_size t1 = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN
  STRUCT_CASES_TAC (ISPEC `h:(num#num#num)option` (cases "option")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `a:num#num#num` PAIR_SURJECTIVE)) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `y:num#num` PAIR_SURJECTIVE)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let WDPAUX_key_eq_pop_gen = prove
 (`!(x:(A,C,FFI)wl_state) y m l0 l h rest.
     s_key_eq (CONS (StackFrame m l0 l h) rest) (wl_state_stack x) /\
     wl_pop_env x = SOME y ==>
     wl_state_locals_size y = m`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `wl_state_stack (x:(A,C,FFI)wl_state)` (cases "list")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[s_key_eq_def] THEN
  MP_TAC(ISPEC `a0:(A)stack_frame` (cases "stack_frame")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[s_frame_key_eq_def2] THEN STRIP_TAC THEN
  MATCH_MP_TAC WDPAUX_pop_env_locals_size_gen THEN
  MAP_EVERY EXISTS_TAC [`x:(A,C,FFI)wl_state`; `a1':(num#(A)word_loc)list`;
    `a2:(num#(A)word_loc)list`; `a3:(num#num#num)option`; `a1:((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[]);;

let WDPAUX_push_env_ls = prove
 (`!envs handler (s:(A,C,FFI)wl_state).
     wl_state_locals_size (wl_push_env envs handler s) = wl_state_locals_size s`,
  GEN_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN SIMP[wl_state_INFO.ri_accfupds; K_THM]);;

let WDPAUX_push_env_ss = prove
 (`(!envs (s:(A,C,FFI)wl_state).
     wl_stack_size (wl_state_stack (wl_push_env envs NONE s)) =
     OPTION_MAP2 (+) (wl_state_locals_size s) (wl_stack_size (wl_state_stack s))) /\
   (!envs hn h hl1 hl2 (s:(A,C,FFI)wl_state).
     wl_stack_size (wl_state_stack (wl_push_env envs (SOME (hn,h,hl1,hl2)) s)) =
     OPTION_MAP2 (+) (OPTION_MAP ((+) 3) (wl_state_locals_size s))
       (wl_stack_size (wl_state_stack s)))`,
  REWRITE_TAC[IL2AUX_push_env_none_stack; IL2AUX_push_env_some_stack; stack_size_eq2;
    stack_size_frame_def]);;

let WDPAUX_call_result_facts = prove
 (`!args1 ss envs handler (s:(A,C,FFI)wl_state) prog w ws s2 s1.
     wl_evaluate (prog, wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock s))) =
       (SOME (wl_Result w ws), s2) /\
     wl_pop_env s2 = SOME s1 ==>
     wl_state_locals_size s1 = wl_state_locals_size s /\
     wl_stack_size (wl_state_stack s1) = wl_stack_size (wl_state_stack s) /\
     wl_state_stack_max s1 = wl_state_stack_max s2 /\
     wl_state_stack_size s1 = wl_state_stack_size s2 /\
     wl_state_code s1 = wl_state_code s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IL2AUX_evaluate_stack_swap) THEN
  REWRITE_TAC[IL2AUX_ss_thms] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`args1:((A)word_loc)list`; `ss:num option`;
    `envs:((A)word_loc)spt#((A)word_loc)spt`; `handler:(num#(A)wl_prog#num#num)option`;
    `s:(A,C,FFI)wl_state`; `prog:(A)wl_prog`; `SOME (wl_Result (w:(A)word_loc) ws)`;
    `s2:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`] IL2AUX_call_pop_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`;
      `handler:(num#(A)wl_prog#num#num)option`; `wl_dec_clock (s:(A,C,FFI)wl_state)`]
      IL2AUX_push_env_stack) THEN
    DISCH_THEN(X_CHOOSE_TAC `hh:(num#num#num)option`) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IL2AUX_ss_norm_def] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "IL2AUX_ss_norm" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[wl_call_env_const; wl_dec_clock_const] THEN STRIP_TAC THEN
    MATCH_MP_TAC WDPAUX_key_eq_pop_gen THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[wl_s_key_eq_stack_size]]);;

let WDPAUX_call_exc_facts = prove
 (`!args1 ss envs hn h hl1 hl2 (s:(A,C,FFI)wl_state) prog x y s2.
     wl_evaluate (prog, wl_call_env args1 ss
        (wl_push_env envs (SOME (hn,h,hl1,hl2)) (wl_dec_clock s))) =
       (SOME (wl_Exception x y), s2) ==>
     wl_state_locals_size s2 = wl_state_locals_size s /\
     wl_stack_size (wl_state_stack s2) = wl_stack_size (wl_state_stack s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IL2AUX_evaluate_stack_swap) THEN
  REWRITE_TAC[IL2AUX_ss_thms] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP IL2AUX_call_exc_facts) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IL2AUX_ss_exc_def] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "IL2AUX_ss_exc"
                       with Failure _ -> false)) THEN
    REWRITE_TAC[wl_call_env_const; IL2AUX_push_env_some_stack; wl_dec_clock_const] THEN
    REWRITE_TAC[RICHAUX_LASTN_CONS] THEN
    REWRITE_TAC[CONS_11; injectivity "stack_frame"] THEN MESON_TAC[];
    ASM_MESON_TAC[wl_s_key_eq_stack_size]]);;

let WDPAUX_call_eval_tail = prove
 (`!d args handler (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (wl_Call NONE (SOME d) args handler, s) = (res,s1) /\
     ~(res = SOME wl_Error) ==>
     ?xs args1 prog ss.
       wl_get_vars args s = SOME xs /\ ~bad_dest_args (SOME d) args /\
       wl_find_code (SOME d)
         (add_ret_loc (NONE:(num list#((1)spt#(1)spt)#(A)wl_prog#num#num)option) xs) (wl_state_code s)
         (wl_state_stack_size s) = SOME (args1,prog,ss) /\
       handler = NONE /\
       ((wl_state_clock s = 0 /\ res = SOME wl_TimeOut /\ s1 = wl_flush_state T s) \/
        (~(wl_state_clock s = 0) /\
         wl_evaluate (prog, wl_call_env args1 ss (wl_dec_clock s)) = (res,s1) /\
         ~wl_bad_fun_return res))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  IL2AUX_EXISTS_ASM_RW_TAC [] THEN ASM_MESON_TAC[]);;

let WDPAUX_call_eval_ret = prove
 (`!rn names ret_prog l1 l2 d args handler (s:(A,C,FFI)wl_state) res s1.
     wl_evaluate (wl_Call (SOME (rn,names,ret_prog,l1,l2)) (SOME d) args handler, s) =
       (res,s1) /\
     ~(res = SOME wl_Error) ==>
     ?xs args1 prog ss envs.
       wl_get_vars args s = SOME xs /\ ~bad_dest_args (SOME d) args /\
       wl_find_code (SOME d) (add_ret_loc (SOME (rn,names,ret_prog,l1,l2)) xs)
         (wl_state_code s) (wl_state_stack_size s) = SOME (args1,prog,ss) /\
       ~(domain (FST names) = {} \/ ~ALL_DISTINCT rn) /\
       cut_envs names (wl_state_locals s) = SOME envs /\
       ((wl_state_clock s = 0 /\ res = SOME wl_TimeOut /\
         s1 = wl_flush_state T (wl_state_stack_fupd (K [])
                (wl_state_stack_max_fupd
                  (K (wl_state_stack_max (wl_call_env args1 ss (wl_push_env envs handler s))))
                  s))) \/
        (~(wl_state_clock s = 0) /\
         ?r2 s2.
           wl_evaluate (prog, wl_call_env args1 ss (wl_push_env envs handler (wl_dec_clock s))) =
             (r2,s2) /\
           ((?ys s1'. r2 = SOME (wl_Result (wl_Loc l1 l2) ys) /\ LENGTH ys = LENGTH rn /\
                wl_pop_env s2 = SOME s1' /\
                domain (wl_state_locals s1') = domain (FST envs) UNION domain (SND envs) /\
                wl_evaluate (ret_prog, wl_set_vars rn ys s1') = (res,s1)) \/
            (?x y. r2 = SOME (wl_Exception x y) /\ handler = NONE /\ res = r2 /\ s1 = s2) \/
            (?x y hn h hl1 hl2. r2 = SOME (wl_Exception x y) /\ handler = SOME (hn,h,hl1,hl2) /\
                x = wl_Loc hl1 hl2 /\
                domain (wl_state_locals s2) = domain (FST envs) UNION domain (SND envs) /\
                wl_evaluate (h, wl_set_var hn y s2) = (res,s1)) \/
            ((r2 = SOME wl_TimeOut \/ r2 = SOME NotEnoughSpace \/
              (?e. r2 = SOME (wl_FinalFFI e))) /\ res = r2 /\ s1 = s2))))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; DE_MORGAN_THM]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  IL2AUX_EXISTS_ASM_RW_TAC [] THEN ASM_MESON_TAC[]);;

let WDPAUX_CALL_INTRO : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> match CONJUNCTS th with
      [a;b;c;d] -> LABEL_TAC "ihT" a THEN LABEL_TAC "ihR" b THEN LABEL_TAC "ihE" c THEN
                   LABEL_TAC "ihB" d
    | _ -> failwith "WDPAUX_CALL_INTRO") THEN
  REPEAT GEN_TAC THEN STRIP_TAC;;

let WDPAUX_ret_cases = prove
 (`!ret:(num list#((1)spt#(1)spt)#(A)wl_prog#num#num)option.
     ret = NONE \/ ?rn names ret_prog l1 l2. ret = SOME (rn,names,ret_prog,l1,l2)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let WDPAUX_find_code_SOME = prove
 (`!d (args:((A)word_loc)list) (code:(num#B)spt) (ssize:(C)spt) args1 prog ss.
     wl_find_code (SOME d) args code ssize = SOME (args1,prog,ss) ==>
     lookup d code = SOME (LENGTH args, prog) /\ args1 = args /\ ss = lookup d ssize`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_find_code_def] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [PAIR_EQ; option_INJ; option_DISTINCT]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let WDPAUX_option_le_NONE = prove
 (`!a g:num option. option_le a g /\ ~(g = NONE) ==> ~(a = NONE)`,
  REPEAT GEN_TAC THEN CASES_ON `a:num option` THEN CASES_ON `g:num option` THEN
  REWRITE_TAC[option_le_def; option_DISTINCT]);;

(* the goal: drop the cases where the bound is NONE *)
let WDPAUX_CALL_TRIV_TAC : tactic = fun (asl,w as g) ->
  let (_,c2) = dest_conj w in
  let (ng,nd) = dest_conj (lhand c2) in
  (ASM_CASES_TAC (rand ng) THENL
    [ASM_REWRITE_TAC[WDPAUX_MAP2_NONE; option_le_def]; ALL_TAC] THEN
   ASM_CASES_TAC (rand nd) THENL
    [ASM_REWRITE_TAC[WDPAUX_MAP2_NONE; option_le_def]; ALL_TAC] THEN
   ASM_REWRITE_TAC[]) g;;

let WDPAUX_is_D tm =
  is_neg tm && is_eq (rand tm) &&
  (try fst(dest_const(fst(strip_comb(lhs(rand tm))))) = "max_depth" with Failure _ -> false) &&
  rhs (rand tm) = `NONE:num option`;;

let WDPAUX_CG_RWS =
  [call_graph_def; LET_DEF; LET_END_DEF; max_depth_def; max_depth_mk_Branch; option_DISTINCT;
   COND_CLAUSES; OPTION_MAP2_SOME_0; WDPAUX_MAP2_NONE];;

(* unfold the call graph of the call in the assumption ~(D = NONE) and in   *)
(* the goal, with the case facts rws                                        *)
let WDPAUX_D_SIMP_TAC (rws:thm list) : tactic =
  RULE_ASSUM_TAC (fun th -> if WDPAUX_is_D (concl th)
                            then CASE_REWRITE_RULE (rws @ WDPAUX_CG_RWS) th else th) THEN
  CASE_REWRITE_TAC (rws @ WDPAUX_CG_RWS) THEN
  TRY (FIRST_X_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)));;

let WDPAUX_CALL_DEST_TAC : tactic =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)
    (ISPEC `dest:num option` (cases "option")) THENL
   [WDPAUX_D_SIMP_TAC [] THEN NO_TAC; ALL_TAC];;

let WDPAUX_RET_SPLIT_TAC : tactic =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `ret:(num list#((1)spt#(1)spt)#(A)wl_prog#num#num)option` WDPAUX_ret_cases);;

let WDPAUX_HANDLER_SPLIT_TAC : tactic =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `handler:(num#(A)wl_prog#num#num)option` IL2AUX_handler_cases);;

(* MP_TAC lem applied to the evaluation of the call and ~(res = SOME Error) *)
let WDPAUX_EVAL_MP_TAC (lem:thm) : tactic = fun (asl,w as g) ->
  let ev = snd(find (fun (_,th) -> IL2AUX_is_eval_eq (concl th) &&
     (try fst(dest_const(fst(strip_comb(fst(dest_pair(rand(lhs(concl th)))))))) = "wl_Call"
      with Failure _ -> false)) asl) in
  let r = fst(dest_pair(rhs(concl ev))) in
  let ne = snd(find (fun (_,th) -> let c = concl th in is_neg c && is_eq (rand c) &&
     lhs (rand c) = r &&
     (try fst(dest_const(rand(rhs(rand c)))) = "wl_Error" with Failure _ -> false)) asl) in
  MP_TAC (MATCH_MP lem (CONJ ev ne)) g;;

(* WDPAUX_IH_X_TAC, the variables funs n ns funs2 found by position: the     *)
(* induction hypothesis is !outer. A ==> !inner. B; the inner variables of   *)
(* these names are instantiated as given in insts, else by the variables of  *)
(* the goal of the same names and types                                     *)
let WDPAUX_IH_X_TAC (insts:(string*term) list) (rws:thm list) (ih0:thm) : tactic =
  fun (asl,w as g) ->
  let ovs,ob = strip_forall (concl ih0) in
  let _,ib = dest_imp ob in
  let ivs,_ = strip_forall ib in
  let th0 = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] ih0 in
  let gvs = freesl (w :: map (concl o snd) asl) in
  let vs0,_ = strip_forall (concl th0) in
  let vs1 = rev(itlist (fun v acc -> variant (acc @ gvs) v :: acc) (rev vs0) []) in
  let th = GENL vs1 (SPECL vs1 th0) in
  let vs,bod = strip_forall (concl th) in
  let k = length vs - length ivs in
  let inner = zip (snd (chop_list k vs)) ivs in
  let ant,_ = dest_imp bod in
  let theta0 = mapfilter (fun (v,v0) ->
      let b = fst(dest_var v0) in
      if mem b ["funs";"n";"ns";"funs2"] then
        (try let t = assoc b insts in
             if type_of t = type_of v then (t,v) else failwith ""
         with Failure _ ->
           (find (fun u -> fst(dest_var u) = b && type_of u = type_of v) gvs, v))
      else failwith "") inner in
  let facts = map (concl o snd) asl in
  let cands = facts @ flat (map (fun f -> if is_eq f then [lhs f; rhs f] else []) facts) in
  let rec go theta cjs =
    match cjs with
      [] -> theta
    | c::rest ->
        let c' = vsubst theta c in
        let open_vs = filter (fun v -> mem v vs && not (exists (fun (_,x) -> x = v) theta))
                             (frees c') in
        if open_vs = [] then go theta rest else
        let lcs = subtract (frees c') open_vs in
        let ok (_,tmi,tyi) =
          if exists (fun (a,b) -> a <> b) tyi then failwith "" else tmi in
        let tryc t = ok (term_match lcs c' t) in
        let ext =
          try tryc (find (fun t -> can tryc t) cands) with Failure _ ->
          try let (l,r) = dest_eq c' in
              if exists (fun v -> mem v open_vs) (frees l) then
                (if exists (fun v -> mem v open_vs) (frees r) then failwith "" else
                 ok (term_match (subtract (frees l) open_vs) l r))
              else ok (term_match (subtract (frees r) open_vs) r l)
          with Failure _ -> [] in
        go (ext @ theta) rest in
  let theta = go theta0 (conjuncts ant) in
  let th1 = SPECL (map (fun v -> try rev_assoc v theta with Failure _ -> v) vs) th in
  let a1 = lhand (concl th1) in
  let rth = REWRITE_CONV (map snd asl @ IL2AUX_res_rws @ rws) a1 in
  let ath = try EQT_ELIM rth
            with Failure _ ->
              (print_endline ("WDPAUX_IH_X_TAC residue: " ^ string_of_term (rhs(concl rth)));
               failwith "WDPAUX_IH_X_TAC") in
  MP_TAC (MP th1 ath) g;;

let WDPAUX_TIMEOUT_TAC : tactic =
  REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM; option_le_X_MAX_X] THEN
  REWRITE_TAC IL2AUX_res_rws THEN NO_TAC;;

let WDPAUX_is_fc th = try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_find_code"
                      with Failure _ -> false;;

let WDPAUX_FC_TAC : tactic =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WDPAUX_find_code_SOME o
              REWRITE_RULE[add_ret_loc_def] o check WDPAUX_is_fc) THEN
  RVEQ_TAC;;

let WDPAUX_CALL_ENV_RWS =
  [wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM];;

let WDPAUX_is_option_le th =
  try fst(dest_const(fst(strip_comb(concl th)))) = "option_le" with Failure _ -> false;;

(* the bound and the stack facts of the conclusion from the option_le and   *)
(* ~(x = NONE) assumptions and the implications ~(..) /\ ~(..) ==> P        *)
let WDPAUX_FINISH_TAC : tactic =
  let is_nn th = let c = concl th in is_neg c && is_eq (rand c) &&
                 rhs (rand c) = `NONE:num option` in
  let is_ih2 th = let c = concl th in is_imp c &&
     forall (fun t -> is_neg t && is_eq (rand t) && rhs (rand t) = `NONE:num option`)
            (conjuncts (lhand c)) in
  (* discharge the ~(.. = NONE) antecedents of the stack implications *)
  REPEAT (FIRST_X_ASSUM(fun th -> if is_ih2 th then
      (MP_TAC th THEN ANTS_TAC THENL
        [ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC (filter (fun t -> WDPAUX_is_option_le t || is_nn t) ths)) THEN
         WDPAUX_OPT_DECIDE_TAC; STRIP_TAC])
      else NO_TAC)) THEN
  CONJ_TAC THENL
   [ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC (filter WDPAUX_is_option_le ths)) THEN
    WDPAUX_OPT_DECIDE_TAC;
    ALL_TAC];;

(* WDPAUX_D_SIMP_TAC with the case facts of the assumptions: MEM, lookup   *)
(* equations and < comparisons, and their negations                       *)
let WDPAUX_D_ASM_SIMP_TAC : tactic =
  let hd_is names t =
    let t = if is_neg t then rand t else t in
    let t = if is_eq t then lhs t else t in
    (try mem (fst(dest_const(fst(strip_comb t)))) names with Failure _ -> false) in
  ASSUM_LIST(fun asl ->
    WDPAUX_D_SIMP_TAC (filter (fun th -> hd_is ["MEM"; "lookup"; "<"] (concl th)) asl));;

let WDPAUX_lookup_funs2_MEM = prove
 (`!d ns (funs2:(num#(A)wl_prog)spt) code y.
     MEM d ns /\ set_of_list ns SUBSET domain funs2 /\ subspt funs2 code /\
     lookup d code = SOME y ==> lookup d funs2 = SOME y`,
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST; domain_lookup; subspt_lookup] THEN
  MESON_TAC[option_INJ]);;

let WDPAUX_lookup_funs_sub = prove
 (`!d (funs:(num#(A)wl_prog)spt) funs2 code y.
     subspt funs funs2 /\ subspt funs2 code /\ lookup d funs = SOME y ==>
     lookup d funs2 = SOME y /\ lookup d code = SOME y /\ d IN domain funs2`,
  REWRITE_TAC[subspt_lookup; domain_lookup] THEN MESON_TAC[]);;

(* res is not NONE, Break or Continue after a tail call *)
let WDPAUX_BFR_TAC : tactic =
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_bad_fun_return_def]) THEN FIRST_ASSUM CONTR_TAC;;

let WDPAUX_TAIL_MEM_TAC : tactic =
  WDPAUX_D_SIMP_TAC [ASSUME `MEM (d:num) ns`] THEN
  SUBGOAL_THEN `lookup d (funs2:(num#(A)wl_prog)spt) =
                SOME (LENGTH (xs:((A)word_loc)list), prog:(A)wl_prog)` ASSUME_TAC THENL
   [MATCH_MP_TAC WDPAUX_lookup_funs2_MEM THEN
    MAP_EVERY EXISTS_TAC [`ns:num list`; `wl_state_code (s:(A,C,FFI)wl_state)`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "ihT" (WDPAUX_IH_X_TAC [("n",`d:num`)] WDPAUX_CALL_ENV_RWS) THEN
  REWRITE_TAC WDPAUX_CALL_ENV_RWS THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`ns:num list`; `d:num`; `(LENGTH (xs:((A)word_loc)list), prog:(A)wl_prog)`;
    `wl_state_stack_size (s:(A,C,FFI)wl_state)`; `ns:num list`; `funs:(num#(A)wl_prog)spt`;
    `funs2:(num#(A)wl_prog)spt`] MEM_max_depth_graphs) THEN
  ASM_REWRITE_TAC[max_depth_graphs_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  WDPAUX_FINISH_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; WDPAUX_BFR_TAC];;

let WDPAUX_lookup_cases = prove
 (`!d (funs:(num#(A)wl_prog)spt). lookup d funs = NONE \/ ?a body. lookup d funs = SOME (a,body)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `lookup d (funs:(num#(A)wl_prog)spt)` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[PAIR_SURJECTIVE]);;

let WDPAUX_is_lookup_SOME th =
  let c = concl th in is_eq c &&
  (try fst(dest_const(fst(strip_comb(lhs c)))) = "lookup" with Failure _ -> false) &&
  (try fst(dest_const(rator(rhs c))) = "SOME" with Failure _ -> false);;

(* after MP_TAC of an induction hypothesis instance: normalize it with rws,  *)
(* max_depth_graphs_def and the lookup facts, and strip it into the         *)
(* assumptions                                                              *)
let WDPAUX_IH_POST_TAC (rws:thm list) : tactic =
  DISCH_THEN(fun th -> ASSUM_LIST(fun asl ->
    let lks = filter WDPAUX_is_lookup_SOME asl in
    STRIP_ASSUME_TAC (CASE_REWRITE_RULE (rws @ [max_depth_graphs_def] @ lks) th)));;

let WDPAUX_LOOKUP_SPLIT_TAC : tactic =
  DISJ_CASES_THEN2 ASSUME_TAC (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
    (ISPECL [`d:num`; `funs:(num#(A)wl_prog)spt`] WDPAUX_lookup_cases) THENL
   [WDPAUX_D_ASM_SIMP_TAC THEN NO_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if WDPAUX_is_lookup_SOME th &&
      rand (lhs (concl th)) = `funs:(num#(A)wl_prog)spt`
    then STRIP_ASSUME_TAC (MATCH_MP WDPAUX_lookup_funs_sub
      (CONJ (ASSUME `subspt (funs:(num#(A)wl_prog)spt) funs2`)
        (CONJ (ASSUME `subspt (funs2:(num#(A)wl_prog)spt) (wl_state_code (s:(A,C,FFI)wl_state))`) th)))
    else NO_TAC);;

(* the code of the call: prog = body *)
let WDPAUX_PROG_BODY_TAC : tactic =
  SUBGOAL_THEN `(prog:(A)wl_prog) = body` SUBST_ALL_TAC THENL
   [ASSUM_LIST(fun asl ->
      let lks = filter (fun th -> WDPAUX_is_lookup_SOME th &&
         rand (lhs (concl th)) = `wl_state_code (s:(A,C,FFI)wl_state)`) asl in
      match lks with
        [l1;l2] -> MP_TAC (TRANS (SYM l1) l2) THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
                   MESON_TAC[]
      | _ -> failwith "WDPAUX_PROG_BODY_TAC"); ALL_TAC];;

let WDPAUX_TAIL_NMEM_TAC : tactic =
  WDPAUX_LOOKUP_SPLIT_TAC THEN WDPAUX_PROG_BODY_TAC THEN
  SUBGOAL_THEN `LENGTH (ns:num list) < sptree_size (funs2:(num#(A)wl_prog)spt)` ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_LESS_size THEN
    MAP_EVERY EXISTS_TAC [`d:num`; `(a:num, body:(A)wl_prog)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  WDPAUX_D_ASM_SIMP_TAC THEN
  REMOVE_THEN "ihT" (WDPAUX_IH_X_TAC [("n",`d:num`); ("ns",`CONS (d:num) ns`)]
    (WDPAUX_CALL_ENV_RWS @ [MEM; ALL_DISTINCT; set_of_list; INSERT_SUBSET])) THEN
  WDPAUX_IH_POST_TAC WDPAUX_CALL_ENV_RWS THEN
  MP_TAC (ISPECL [`ns:num list`; `CONS (d:num) ns`; `ns:num list`;
    `wl_state_stack_size (s:(A,C,FFI)wl_state)`; `funs:(num#(A)wl_prog)spt`;
    `funs2:(num#(A)wl_prog)spt`] option_le_max_depth_graphs) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[set_of_list; LENGTH] THEN CONJ_TAC THENL [SET_TAC[]; ARITH_TAC];
    DISCH_TAC] THEN
  WDPAUX_FINISH_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; WDPAUX_BFR_TAC];;

let WDPAUX_code_grows = prove
 (`!p (t:(A,C,FFI)wl_state) r t' (funs2:(num#(A)wl_prog)spt).
     wl_evaluate (p,t) = (r,t') /\ subspt funs2 (wl_state_code t) ==>
     subspt funs2 (wl_state_code t')`,
  MESON_TAC[evaluate_code_only_grows; subspt_trans]);;

(* discharge the ~(.. = NONE) antecedents of the stack implications of the  *)
(* induction hypotheses by option arithmetic                                 *)
let WDPAUX_DISCHARGE_TAC : tactic =
  let is_nn th = let c = concl th in is_neg c && is_eq (rand c) &&
                 rhs (rand c) = `NONE:num option` in
  let is_ih2 th = let c = concl th in is_imp c &&
     forall (fun t -> is_neg t && is_eq (rand t) && rhs (rand t) = `NONE:num option`)
            (conjuncts (lhand c)) in
  REPEAT (FIRST_X_ASSUM(fun th -> if is_ih2 th then
      (MP_TAC th THEN ANTS_TAC THENL
        [ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC
           (filter (fun t -> WDPAUX_is_option_le t || is_nn t) ths)) THEN
         WDPAUX_OPT_DECIDE_TAC; STRIP_TAC])
      else NO_TAC));;

let WDPAUX_BOUND_TAC : tactic =
  ASSUM_LIST(fun ths -> MAP_EVERY MP_TAC (filter WDPAUX_is_option_le ths)) THEN
  WDPAUX_OPT_DECIDE_TAC;;

let WDPAUX_LS_EQ = `wl_state_locals_size (s:(A,C,FFI)wl_state) = lookup n (wl_state_stack_size s)`;;

let WDPAUX_PUSH_RWS =
  WDPAUX_CALL_ENV_RWS @ [wl_push_env_const; push_env_stack_max_eq; WDPAUX_push_env_ss;
    WDPAUX_push_env_ls];;

(* the induction hypothesis of the callee body, its stack implication       *)
(* discharged, and the code of the state after the callee                   *)
let WDPAUX_CALLEE_TAC : tactic =
  ASSUME_TAC (MATCH_MP subspt_delete
    (ASSUME `subspt (funs:(num#(A)wl_prog)spt) funs2`)) THEN
  REMOVE_THEN "ihB" (WDPAUX_IH_X_TAC
    [("funs",`delete d (funs:(num#(A)wl_prog)spt)`); ("n",`d:num`); ("ns",`[d:num]`)]
    (WDPAUX_PUSH_RWS @ [MEM; ALL_DISTINCT; set_of_list; INSERT_SUBSET; EMPTY_SUBSET])) THEN
  WDPAUX_IH_POST_TAC (WDPAUX_PUSH_RWS @ [ASSUME WDPAUX_LS_EQ]) THEN
  WDPAUX_DISCHARGE_TAC THEN
  (fun (asl,w as g) ->
     let ev = snd(find (fun (_,th) -> IL2AUX_is_eval_eq (concl th) &&
       (try fst(dest_const(fst(strip_comb(snd(dest_pair(rand(lhs(concl th)))))))) = "wl_call_env"
        with Failure _ -> false)) asl) in
     let s2 = snd(dest_pair(rhs(concl ev))) in
     (SUBGOAL_THEN (mk_comb(`subspt (funs2:(num#(A)wl_prog)spt)`, mk_comb(`wl_state_code:(A,C,FFI)wl_state->(num#(A)wl_prog)spt`, s2)))
       ASSUME_TAC THENL
      [MATCH_MP_TAC WDPAUX_code_grows THEN
       MAP_EVERY EXISTS_TAC [fst(dest_pair(rand(lhs(concl ev)))); snd(dest_pair(rand(lhs(concl ev))));
                             fst(dest_pair(rhs(concl ev)))] THEN
       ASM_REWRITE_TAC WDPAUX_PUSH_RWS; ALL_TAC]) g);;

(* RULE_ASSUM_TAC on the assumptions that are not labelled ih...           *)
let WDPAUX_NONIH_RULE_TAC (rule:thm->thm) : tactic = fun (asl,w as g) ->
  let is_ih l = String.length l >= 2 && String.sub l 0 2 = "ih" in
  (POP_ASSUM_LIST(K ALL_TAC) THEN
   MAP_EVERY (fun (l,th) -> LABEL_TAC l (if is_ih l then th else rule th)) (rev asl)) g;;

let WDPAUX_is_field_eq th =
  let c = concl th in is_eq c &&
  (let t = lhs c in
   try let f = fst(dest_const(fst(strip_comb t))) in
       mem f ["wl_state_stack_max"; "wl_state_stack_size"; "wl_state_locals_size";
              "wl_state_code"; "wl_stack_size"] &&
       not (vfree_in t (rhs c))
   with Failure _ -> false);;

(* WDPAUX_IH_POST_TAC with the field equations of the assumptions          *)
let WDPAUX_IH_POST2_TAC (rws:thm list) : tactic =
  DISCH_THEN(fun th -> ASSUM_LIST(fun asl ->
    let lks = filter WDPAUX_is_lookup_SOME asl in
    let fes = filter WDPAUX_is_field_eq asl in
    STRIP_ASSUME_TAC (CASE_REWRITE_RULE (rws @ [max_depth_graphs_def] @ lks @ fes) th)));;

let WDPAUX_RET_TO_TAC : tactic =
  REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC (WDPAUX_PUSH_RWS @ IL2AUX_res_rws) THEN REWRITE_TAC[ASSUME WDPAUX_LS_EQ] THEN
  WDPAUX_D_ASM_SIMP_TAC THEN WDPAUX_BOUND_TAC;;

let WDPAUX_is_callee_ev th =
  IL2AUX_is_eval_eq (concl th) &&
  (try fst(dest_const(fst(strip_comb(snd(dest_pair(rand(lhs(concl th)))))))) = "wl_call_env"
   with Failure _ -> false);;

let WDPAUX_RET_RES_TAC : tactic =
  WDPAUX_CALLEE_TAC THEN
  FIRST_ASSUM(fun ev -> if WDPAUX_is_callee_ev ev then
     FIRST_ASSUM(fun pe -> if is_eq (concl pe) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl pe))))) = "wl_pop_env" with Failure _ -> false)
       then STRIP_ASSUME_TAC (MATCH_MP WDPAUX_call_result_facts (CONJ ev pe)) else NO_TAC)
     else NO_TAC) THEN
  REMOVE_THEN "ihR" (WDPAUX_IH_X_TAC [] [wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
  WDPAUX_IH_POST2_TAC [wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  WDPAUX_DISCHARGE_TAC THEN WDPAUX_D_ASM_SIMP_TAC THEN
  CONJ_TAC THENL [WDPAUX_BOUND_TAC; ASM_REWRITE_TAC[]];;

let WDPAUX_RET_EXC_TAC : tactic =
  WDPAUX_CALLEE_TAC THEN
  FIRST_ASSUM(fun ev -> if WDPAUX_is_callee_ev ev then
     STRIP_ASSUME_TAC (MATCH_MP WDPAUX_call_exc_facts ev) else NO_TAC) THEN
  REMOVE_THEN "ihE" (WDPAUX_IH_X_TAC [] [wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
  WDPAUX_IH_POST2_TAC [wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  WDPAUX_DISCHARGE_TAC THEN WDPAUX_D_ASM_SIMP_TAC THEN
  CONJ_TAC THENL [WDPAUX_BOUND_TAC; ASM_REWRITE_TAC[]];;

let WDPAUX_RET_STOP_TAC : tactic =
  WDPAUX_CALLEE_TAC THEN WDPAUX_D_ASM_SIMP_TAC THEN
  CONJ_TAC THENL [WDPAUX_BOUND_TAC; ASM_REWRITE_TAC IL2AUX_res_rws];;

let WDPAUX_RET_DISPATCH_TAC : tactic = fun (asl,w as g) ->
  let has p = exists (fun (_,th) -> p (concl th)) asl in
  let is_head name t = try fst(dest_const(fst(strip_comb t))) = name with Failure _ -> false in
  if has (fun c -> c = `wl_state_clock (s:(A,C,FFI)wl_state) = 0`) then WDPAUX_RET_TO_TAC g
  else if has (fun c -> is_eq c && is_head "wl_pop_env" (lhs c)) then WDPAUX_RET_RES_TAC g
  else if has (fun c -> IL2AUX_is_eval_eq c &&
                        is_head "wl_set_var" (snd(dest_pair(rand(lhs c))))) then WDPAUX_RET_EXC_TAC g
  else WDPAUX_RET_STOP_TAC g;;

let WDPAUX_SPLIT_PAIR_EQS_TAC : tactic =
  WDPAUX_NONIH_RULE_TAC (REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RVEQ_TAC;;

let WDPAUX_CALL_TAIL_TAC : tactic =
  WDPAUX_EVAL_MP_TAC WDPAUX_call_eval_tail THEN STRIP_TAC THEN RVEQ_TAC THENL
   [WDPAUX_TIMEOUT_TAC;
    WDPAUX_FC_TAC THEN ASM_CASES_TAC `MEM (d:num) ns` THENL
     [WDPAUX_TAIL_MEM_TAC; WDPAUX_TAIL_NMEM_TAC]];;

let WDPAUX_CALL_RET_TAC : tactic =
  REMOVE_THEN "ihT" (K ALL_TAC) THEN
  WDPAUX_LOOKUP_SPLIT_TAC THEN
  WDPAUX_HANDLER_SPLIT_TAC THEN
  WDPAUX_D_ASM_SIMP_TAC THEN
  WDPAUX_EVAL_MP_TAC WDPAUX_call_eval_ret THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  WDPAUX_NONIH_RULE_TAC (REWRITE_RULE IL2AUX_res_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  WDPAUX_SPLIT_PAIR_EQS_TAC THEN
  WDPAUX_FC_TAC THEN WDPAUX_PROG_BODY_TAC THEN
  WDPAUX_RET_DISPATCH_TAC;;

let WDPAUX_CALL_TAC : tactic =
  WDPAUX_CALL_INTRO THEN WDPAUX_CALL_TRIV_TAC THEN WDPAUX_CALL_DEST_TAC THEN
  WDPAUX_RET_SPLIT_TAC THENL [WDPAUX_CALL_TAIL_TAC; WDPAUX_CALL_RET_TAC];;

(* HOL4 line 147 *)
let max_depth_call_graph_lemma = prove
 (`!prog (s:(A,C,FFI)wl_state) res s1 funs n ns funs2.
     wl_evaluate (prog,s) = (res,s1) /\
     subspt funs funs2 /\ subspt funs2 (wl_state_code s) /\
     wl_state_locals_size s = lookup n (wl_state_stack_size s) /\ ~(res = SOME wl_Error) /\
     MEM n ns /\ ALL_DISTINCT ns /\ set_of_list ns SUBSET domain funs2 ==>
     option_le (wl_state_stack_max s1)
       (OPTION_MAP2 MAX (wl_state_stack_max s)
         (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s))
           (OPTION_MAP2 MAX
             (max_depth_graphs (wl_state_stack_size s) ns ns funs funs2)
             (max_depth (wl_state_stack_size s)
                (call_graph funs n ns (sptree_size funs2) prog))))) /\
     (~(max_depth_graphs (wl_state_stack_size s) ns ns funs funs2 = NONE) /\
      ~(max_depth (wl_state_stack_size s) (call_graph funs n ns (sptree_size funs2) prog) = NONE) ==>
      wl_state_stack_size s1 = wl_state_stack_size s /\
      ((res = NONE \/ (?k. res = SOME (wordSem_Break k)) \/
        (?k. res = SOME (wordSem_Continue k))) ==>
       wl_state_locals_size s1 = wl_state_locals_size s))`,
  IL2AUX_EVAL_IND_TAC wl_evaluate_ind THEN REPEAT CONJ_TAC THENL
   [WDPAUX_NR_TAC;
    WDPAUX_ALLOC_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_MT_TAC;
    WDPAUX_SEQ_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_IF_TAC;
    WDPAUX_LOOP_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_NR_TAC;
    WDPAUX_CALL_TAC]);;

(* HOL4 line 790 *)
let max_depth_call_graph = prove
 (`!prog (s:(A,C,FFI)wl_state) res s1 funs n a.
     wl_evaluate (prog,s) = (res,s1) /\ subspt funs (wl_state_code s) /\
     lookup n funs = SOME (a,prog) /\
     wl_state_locals_size s = lookup n (wl_state_stack_size s) /\ ~(res = SOME wl_Error) ==>
     option_le (wl_state_stack_max s1)
       (OPTION_MAP2 MAX (wl_state_stack_max s)
         (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s))
           (max_depth (wl_state_stack_size s) (full_call_graph n funs))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`prog:(A)wl_prog`; `s:(A,C,FFI)wl_state`; `res:((A)wl_result)option`;
    `s1:(A,C,FFI)wl_state`; `funs:(num#(A)wl_prog)spt`; `n:num`; `[n:num]`;
    `funs:(num#(A)wl_prog)spt`] max_depth_call_graph_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[subspt_refl; MEM; ALL_DISTINCT; set_of_list; INSERT_SUBSET;
                    EMPTY_SUBSET; domain_lookup] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[full_call_graph_def; max_depth_graphs_def] THEN
  CASE_REWRITE_TAC[max_depth_def] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN WDPAUX_OPT_DECIDE_TAC);;

(* the stack_max bound of a call with the return program Skip and no      *)
(* handler, from max_depth_call_graph for the callee body                  *)
let WDPAUX_CALL_SOME_TAC : tactic = fun (asl,w as g) ->
  if exists (fun (_,th) -> concl th = `wl_state_clock (s:(A,C,FFI)wl_state) = 0`) asl then
    (REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM] THEN
     REWRITE_TAC WDPAUX_PUSH_RWS THEN ASM_REWRITE_TAC[full_call_graph_def] THEN
     CASE_REWRITE_TAC[max_depth_def] THEN WDPAUX_OPT_DECIDE_TAC) g
  else
    (TRY (FIRST_X_ASSUM(fun th -> if IL2AUX_is_eval_eq (concl th) &&
            fst(dest_pair(rand(lhs(concl th)))) = `wl_Skip:(A)wl_prog`
          then MP_TAC (ONCE_REWRITE_RULE[wl_evaluate_def] th) else NO_TAC) THEN
          REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC) THEN
     IL2AUX_FACTS_TAC [wl_pop_env_const] THEN
     REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(fun ev -> if WDPAUX_is_callee_ev ev then
        let (p,t) = dest_pair(rand(lhs(concl ev))) and (r,t') = dest_pair(rhs(concl ev)) in
        MP_TAC (ISPECL [p; t; r; t'; `funs:(num#(A)wl_prog)spt`; `dest:num`; `a:num`]
                 max_depth_call_graph)
       else NO_TAC) THEN
     ASM_REWRITE_TAC (WDPAUX_PUSH_RWS @ IL2AUX_res_rws @ [full_call_graph_def]) THEN
     CASE_REWRITE_TAC[max_depth_def] THEN WDPAUX_OPT_DECIDE_TAC) g;;

(* HOL4 line 808 *)
let max_depth_Call_SOME = prove
 (`!n1 n2 n3 n4 dest args (s:(A,C,FFI)wl_state) res s1 funs.
     wl_evaluate (wl_Call (SOME (n1,n2,wl_Skip,n3,n4)) (SOME dest) args NONE,s) = (res,s1) /\
     ~(res = SOME wl_Error) /\ subspt funs (wl_state_code s) ==>
     option_le (wl_state_stack_max s1)
       (OPTION_MAP2 MAX (wl_state_stack_max s)
         (OPTION_MAP2 (+) (wl_state_locals_size s)
           (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s))
             (max_depth (wl_state_stack_size s) (full_call_graph dest funs)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_THEN2 ASSUME_TAC (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
    (ISPECL [`dest:num`; `funs:(num#(A)wl_prog)spt`] WDPAUX_lookup_cases) THEN
  ASM_REWRITE_TAC[full_call_graph_def] THEN CASE_REWRITE_TAC[max_depth_def] THEN
  REWRITE_TAC[WDPAUX_MAP2_NONE; option_le_def] THEN
  WDPAUX_EVAL_MP_TAC WDPAUX_call_eval_ret THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE IL2AUX_res_rws) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WDPAUX_find_code_SOME o
              REWRITE_RULE[add_ret_loc_def] o check WDPAUX_is_fc) THEN
  RVEQ_TAC THEN
  (SUBGOAL_THEN `(prog:(A)wl_prog) = body` SUBST_ALL_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[subspt_lookup]) THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`dest:num`; `(a:num,body:(A)wl_prog)`] o
       check (is_forall o concl)) THEN
     ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
     ALL_TAC]) THEN
  WDPAUX_CALL_SOME_TAC);;

(* HOL4 line 857 *)
let max_depth_Call_NONE = prove
 (`!dest args (s:(A,C,FFI)wl_state) res s1 funs.
     wl_evaluate (wl_Call NONE (SOME dest) args NONE,s) = (res,s1) /\
     ~(res = SOME wl_Error) /\ subspt funs (wl_state_code s) ==>
     option_le (wl_state_stack_max s1)
       (OPTION_MAP2 MAX (wl_state_stack_max s)
         (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s))
           (max_depth (wl_state_stack_size s) (full_call_graph dest funs))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_THEN2 ASSUME_TAC (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
    (ISPECL [`dest:num`; `funs:(num#(A)wl_prog)spt`] WDPAUX_lookup_cases) THEN
  ASM_REWRITE_TAC[full_call_graph_def] THEN CASE_REWRITE_TAC[max_depth_def] THEN
  REWRITE_TAC[WDPAUX_MAP2_NONE; option_le_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WDPAUX_call_eval_tail o
    CONJ (ASSUME `wl_evaluate (wl_Call NONE (SOME dest) args NONE,s) =
                  (res:((A)wl_result)option,s1:(A,C,FFI)wl_state)`)) THEN
  (STRIP_TAC THEN RVEQ_TAC THENL
    [REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM; option_le_X_MAX_X];
     ALL_TAC]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WDPAUX_find_code_SOME o
              REWRITE_RULE[add_ret_loc_def] o check WDPAUX_is_fc) THEN
  RVEQ_TAC THEN
  (SUBGOAL_THEN `(prog:(A)wl_prog) = body` SUBST_ALL_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[subspt_lookup]) THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`dest:num`; `(a:num,body:(A)wl_prog)`] o
       check (is_forall o concl)) THEN
     ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
     ALL_TAC]) THEN
  MP_TAC (ISPECL [`body:(A)wl_prog`;
    `wl_call_env xs (lookup dest (wl_state_stack_size s)) (wl_dec_clock (s:(A,C,FFI)wl_state))`;
    `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`; `funs:(num#(A)wl_prog)spt`;
    `dest:num`; `a:num`] max_depth_call_graph) THEN
  ASM_REWRITE_TAC WDPAUX_CALL_ENV_RWS THEN
  ASM_REWRITE_TAC[full_call_graph_def] THEN CASE_REWRITE_TAC[max_depth_def] THEN
  WDPAUX_OPT_DECIDE_TAC);;
