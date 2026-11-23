(* ========================================================================= *)
(* data_to_word_bignumProof: port of HOL4                                    *)
(* compiler/backend/proofs/data_to_word_bignumProofScript.sml (CakeML v3479).*)
(* Part of the correctness proof for data_to_word: the bignum arithmetic    *)
(* stubs (AnyArith, LongDiv, Replicate) and the calls of the Arith stubs.   *)
(*                                                                           *)
(* Rendering notes:                                                          *)
(* - HOL4 temp_bring_to_front_overload cut_env wordSem: unqualified cut_env  *)
(*   is wordSem's (wl_cut_env) here.                                         *)
(* - HOL4 b2n is HOL Light's bitval; multiword$Add ... are multiword_Add ... *)
(*   (hol4/multiword.ml); HOL4 FAIL x s is FAIL x s (hol4/basic.ml).         *)
(* - eq_eval is the LIST_CONJ of definitions as in HOL4.                     *)
(* - wordSem is a qualified ancestor in HOL4: its constants are the wl_      *)
(*   ones; HOL4 Type state (wordSem state) is (A,C,FFI)wl_state.             *)
(* BIGPAUX_ names are local helpers of this file.                           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/sptree.ml";;
needs "hol4/int_bitwise.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/multiword.ml";;
needs "hol4/mc_multiword.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/word_depthProof.ml";;
(* HOL4 ancestors not needed here: semanticsProps, alignment (in            *)
(* hol4/words4.ml); word_depthProof is needed by the proof of               *)
(* eval_Call_Arith only (max_depth_Call_NONE).                               *)

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Helpers (BIGPAUX_ names).                                                 *)
(* ------------------------------------------------------------------------- *)

(* case split on every num option valued subterm satisfying pr (with free   *)
(* variables only) of the goal and the assumptions                         *)
let BIGPAUX_OPTION_CASES_TAC (pr:term->bool) : tactic = fun (asl,w as g) ->
  let all = list_mk_conj (w :: map (concl o snd) asl) in
  let fv = frees all in
  let tms = setify (find_terms (fun t -> pr t && type_of t = `:num option` &&
                                         subset (frees t) fv) all) in
  MAP_EVERY (fun t ->
    DISJ_CASES_THEN2 (X_CHOOSE_THEN (genvar `:num`) SUBST_ALL_TAC) SUBST_ALL_TAC
      (ISPEC t option_CASES)) tms g;;

(* symbolic evaluation of wordLang code: the clauses of wl_evaluate except  *)
(* Call (and Loop), with the definitions of the semantic helpers           *)
let BIGPAUX_EV_THMS =
  [WBIGPAUX_ev_Skip; WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; WBIGPAUX_ev_Set;
   WBIGPAUX_ev_Get; WBIGPAUX_ev_Store; WBIGPAUX_ev_If; WBIGPAUX_ev_Return;
   WBIGPAUX_ev_Inst; wl_word_exp_def; wl_get_var_def;
   wl_get_vars_def; wl_get_var_imm_def; WBIGPAUX_word_cmp_Word; the_words_def;
   word_op_def; wl_set_var_def; wl_set_store_def; wl_get_store_def;
   wl_mem_store_def; wl_mem_load_def; lookup_insert; wl_call_env_def;
   wl_dec_clock_def; wl_flush_state_def; MAP; ITLIST; OPTION_MAP_DEF;
   WORD_ADD_0; asm_word_cmp_def; WORD_AND_REFL; GE];;

(* fromList2 [x0; ...; xk] as an insert chain *)
let BIGPAUX_FROMLIST2_CONV tm =
  match tm with
    Comb(Const("fromList2",_),l) when is_list l ->
      (REWR_CONV fromList2_def THENC REWRITE_CONV[FOLDL] THENC
       TOP_DEPTH_CONV GEN_BETA_CONV THENC REWRITE_CONV[SND] THENC
       NUM_REDUCE_CONV) tm
  | _ -> failwith "BIGPAUX_FROMLIST2_CONV";;

let BIGPAUX_FROMLIST2_TAC = CONV_TAC(TOP_DEPTH_CONV BIGPAUX_FROMLIST2_CONV);;

(* HOL4 qmatch_goalsub_abbrev_tac: abbreviate as v the part of the first   *)
(* subterm of the goal matching pat that v matches                          *)
let BIGPAUX_MATCH_ABBREV_TAC (pat:term) (v:term) : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let (_,tmi,_) = term_match [] pat t in
  let x = rev_assoc v tmi in
  ABBREV_TAC (mk_eq(v,x)) g;;

(* HOL4 simp with the simple facts among the assumptions only (no          *)
(* quantified, implicational or existential ones, no abbreviations x = v   *)
(* and none mentioning a constant of excl): the kit's SIMP uses every      *)
(* assumption                                                               *)
let BIGPAUX_ASM_SIMP_TAC (excl:string list) (thl:thm list) : tactic = fun (asl,w as g) ->
  let ok th =
    let c = concl th in
    not (is_forall c) && not (is_imp c) && not (is_exists c) &&
    not (is_eq c && is_var (rhs c) && not (is_var (lhs c))) &&
    not (exists (fun nm -> can (find_term (fun t -> is_const t && fst (dest_const t) = nm)) c)
           excl) in
  let ths = filter ok (map snd asl) in
  CONV_TAC (CAKE_SIMP_CONV (thl @ ths)) g;;

(* plain rewriting evaluation (no contextual rewriting, so a conditional   *)
(* whose test is not decided keeps both branches unevaluated only as far  *)
(* as the clauses go): the clauses and helpers, record accessors, and the *)
(* simple facts among the assumptions                                       *)
let BIGPAUX_RW_THMS =
  [WBIGPAUX_ev_Skip; WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; WBIGPAUX_ev_Set;
   WBIGPAUX_ev_Get; WBIGPAUX_ev_Store; WBIGPAUX_ev_If; WBIGPAUX_ev_Return;
   WBIGPAUX_ev_Inst; wl_word_exp_def; wl_get_var_def; wl_get_vars_def;
   wl_get_var_imm_def; WBIGPAUX_word_cmp_Word; asm_word_cmp_def; the_words_def;
   word_op_def; word_sh_def; wl_set_var_def; wl_set_store_def; wl_get_store_def;
   wl_mem_store_def; wl_mem_load_def; lookup_insert; wl_call_env_def;
   wl_dec_clock_def; wl_flush_state_def; MAP; ITLIST; OPTION_MAP_DEF;
   WORD_ADD_0; WORD_OR_0; WORD_XOR_0; WORD_AND_REFL; GE; ARITH_EQ;
   wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; option_INJ; option_DISTINCT;
   WBIGPAUX_ev_Call; bad_dest_args_def; add_ret_loc_def; wl_find_code_def; LENGTH;
   wl_bad_fun_return_def; wl_inst_def; LET_DEF; LET_END_DEF];;

let BIGPAUX_RW_TAC (excl:string list) (thl:thm list) : tactic = fun (asl,w as g) ->
  let ok th =
    let c = concl th in
    not (is_forall c) && not (is_imp c) && not (is_exists c) &&
    not (is_eq c && is_var (rhs c) && not (is_var (lhs c))) &&
    not (exists (fun nm -> can (find_term (fun t -> is_const t && fst (dest_const t) = nm)) c)
           excl) in
  let ths = filter ok (map snd asl) in
  CASE_REWRITE_TAC (thl @ ths) g;;

let BIGPAUX_EVAL_TAC (excl:string list) : tactic =
  REPEAT (CHANGED_TAC (BIGPAUX_RW_TAC excl BIGPAUX_RW_THMS THEN
    CONV_TAC (TOP_DEPTH_CONV BIGPAUX_FROMLIST2_CONV) THEN CONV_TAC NUM_REDUCE_CONV));;

(* one more instruction of a list_Seq *)
let BIGPAUX_SEQ_STEP_TAC (excl:string list) : tactic =
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN BIGPAUX_EVAL_TAC excl;;

(* the same with extra theorems *)
let BIGPAUX_EVAL_THMS_TAC (excl:string list) (thl:thm list) : tactic =
  REPEAT (CHANGED_TAC (BIGPAUX_RW_TAC excl (thl @ BIGPAUX_RW_THMS) THEN
    CONV_TAC (TOP_DEPTH_CONV BIGPAUX_FROMLIST2_CONV) THEN CONV_TAC NUM_REDUCE_CONV));;

(* HOL4 lines 29-30: val state_rel_def = data_to_word_gcProof state_rel_def *)
(* and val code_rel_def = data_to_word_gcProof code_rel_def (ML bindings)    *)

(* HOL4 line 38 (HOL4: LIST_CONJ of definitions) *)
let eq_eval = end_itlist CONJ
  [wl_evaluate_def; wl_get_var_def; lookup_insert; wl_get_var_imm_def;
   asm_word_cmp_def; wl_word_exp_def; wl_set_var_def; wl_call_env_def;
   fromList2_def; wl_mem_load_def; bad_dest_args_def; wl_get_vars_def;
   wl_find_code_def; add_ret_loc_def; list_insert_def; wl_dec_clock_def;
   the_words_def; word_op_def];;

(* HOL4 line 48 *)
let word_list_IMP_store_list = prove
 (`!xs (a:A word) frame m dm.
     (misc_word_list a xs STAR frame) (fun2set (m,dm)) ==>
     data_to_word_memoryProof_store_list a xs m dm = SOME m`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def; misc_word_list_def] THEN
  REPEAT STRIP_TAC THEN MP4AUX_SEP_R_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((a:A word) =+ (h:A word_loc)) m = m` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `set_sep_one (a:A word,h:A word_loc) STAR frame` THEN
  MP4AUX_SEP_AC_TAC);;

(* HOL4 line 61 *)
let word_exp_set_var_ShiftVar_lemma = prove
 (CASE_TERM
  `!(t:(A,C,FFI)wl_state) sow v n.
     wl_word_exp t (ShiftVar sow v n) =
     match lookup v (wl_state_locals t) with
       SOME (wl_Word w) ->
         OPTION_MAP wl_Word
           (match sow with
              Lsl -> SOME (word_shl w n)
            | Lsr -> SOME (word_ushr w n)
            | Asr -> SOME (word_ishr w n)
            | Ror -> SOME (word_ror w n))
     | _ -> FAIL (wl_word_exp t (ShiftVar sow v n)) "lookup failed"`,
  REPEAT GEN_TAC THEN
  CASES_ON `lookup v (wl_state_locals (t:(A,C,FFI)wl_state))` THEN
  CASE_REWRITE_TAC[FAIL_DEF] THEN
  CASES_ON `a:A word_loc` THEN CASE_REWRITE_TAC[FAIL_DEF] THEN
  SUBGOAL_THEN `!m. m < dimindex(:A) ==> val(word m:A word) = m` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_MESON_TAC[LT_TRANS; dimindex_lt_dimword; dimword_def]; ALL_TAC] THEN
  CASES_ON `sow:shift` THEN CASE_REWRITE_TAC[ShiftVar_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[wl_word_exp_def; wl_get_var_def; OPTION_MAP_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(d <= n:num) ==> n < d`; ARITH_RULE `~(d = 0) ==> d - 1 < d`;
     DIMINDEX_NONZERO; word_sh_def; WORD_SHL_ZERO; WORD_USHR_ZERO; WORD_ISHR_ZERO;
     WORD_ROR_ZERO; GE; ARITH_RULE `~(d <= n:num) ==> ~(d <= n)`; MOD_LT_EQ;
     ARITH_RULE `~(d = 0) ==> ~(d <= d - 1)`; ARITH_RULE `x < d ==> ~(d <= x:num)`] THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[option_INJ] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_SHL_TRIVIAL; GSYM WORD_ROR_MOD; word_asr_dimindex] THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[WORD_USHR_EQ_0] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP dimindex(:A)` THEN
    ASM_REWRITE_TAC[VAL_BOUND; LE_EXP] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT; WORD_ROR_ZERO]]);;

(* HOL4 line 95 *)
let i2mw_small_int_IMP_0 = prove
 (`!v. (!v1. ~(i2mw v = (F,[v1:A word]))) /\ (!v1. ~(i2mw v = (T,[v1:A word]))) /\
       small_int (:A) v /\ good_dimindex (:A) ==> v = &0`,
  GEN_TAC THEN REWRITE_TAC[i2mw_def; small_int_def; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_CASES_TAC `v:int = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(num_of_int (abs (v:int))) = abs v` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN REWRITE_TAC[INT_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(num_of_int (abs (v:int)) = 0) /\ num_of_int (abs v) < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP (ARITH_RULE `0 < n ==> n DIV 8 < n`)
                    (INST_TYPE [`:A`,`:N`] ZERO_LT_dimword)) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`~(v:int = &0)`; `--(&(dimword(:A) DIV 8)) <= v:int`;
                           `v:int < &(dimword(:A) DIV 8)`] THEN
    INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n2mw (num_of_int (abs (v:int))) =
                [word (num_of_int (abs v) MOD dimword(:A)):A word]` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[n2mw_def] THEN ASM_SIMP_TAC[DIV_LT] THEN
    ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(v:int) < &0` THEN ASM_MESON_TAC[]);;

(* HOL4 line 110 *)
let state_rel_Number_small_int = prove
 (`!c r1 r2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) x locs i.
     data_to_word_gcProof_state_rel c r1 r2 s t (SOME [x]) locs /\ small_int (:A) i ==>
     data_to_word_gcProof_state_rel c r1 r2 s t
       (SOME [(data_Number i,wl_Word (Smallnum i:A word))]) locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC memory_rel_rearrange) THEN
  REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 120 *)
let heap_lookup_Unused_Bignum = prove
 (`!a k (hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
              heap_element)list) j.
     heap_lookup a (CONS (Unused k) hb) = SOME (Bignum j) <=>
     k + 1 <= a /\ heap_lookup (a - (k + 1)) hb = SOME (Bignum j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_lookup_def; el_length_def] THEN
  REWRITE_TAC[data_to_word_memoryProof_Bignum_def] THEN
  CASES_ON `i2mw (j:int):bool#(A word)list` THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a = 0` THEN
  ASM_REWRITE_TAC[option_INJ; option_DISTINCT; ARITH_RULE `~(k + 1 <= 0)`] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a < k + 1` THEN
  ASM_SIMP_TAC[option_DISTINCT; ARITH_RULE `a < k + 1 ==> ~(k + 1 <= a)`;
               ARITH_RULE `~(a < k + 1) ==> k + 1 <= a`]);;

(* HOL4 line 130 *)
let push_env_insert_0 = prove
 (`!(x:A word_loc) (t:(A,C,FFI)wl_state).
     wl_push_env (insert 0 x LN,LN) NONE t =
     wl_state_stack_fupd
       (K (CONS (StackFrame (wl_state_locals_size t) [(0,x)] [] NONE) (wl_state_stack t)))
       (wl_state_stack_max_fupd
          (K (OPTION_MAP2 MAX (wl_state_stack_max t)
                (wl_stack_size (CONS (StackFrame (wl_state_locals_size t) [(0,x)] [] NONE)
                                     (wl_state_stack t)))))
          (wl_state_permute_fupd (K (\n. wl_state_permute t (n + 1))) t))`,
  REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF; WBIGPAUX_toAList_insert_0_LN;
              WBIGPAUX_env_to_list_LN; FST; SND] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 144 *)
let mc_header_i2mw_eq_0w = prove
 (`!i. 2 * LENGTH (SND (i2mw i):(A word)list) + 1 < dimword (:A) ==>
       (mc_header (i2mw i:bool#(A word)list) = word 0:A word <=> i = &0)`,
  GEN_TAC THEN REWRITE_TAC[i2mw_def; mc_header_def; SND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!b n. 2 * n + 1 < dimword(:A) ==>
     (word_add (word (n * 2)) (if b then word 1 else word 0):A word = word 0 <=>
      n = 0 /\ ~b)` (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD; ADD_CLAUSES; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `2 * n + 1 < d ==> n * 2 + 1 < d /\ n * 2 < d`] THEN
    ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_EQ_NIL; n2mw_NIL] THEN
  SUBGOAL_THEN `num_of_int (abs i) = 0 <=> i = &0` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    INT_ARITH_TAC; ALL_TAC] THEN
  INT_ARITH_TAC);;

(* HOL4 line 156 *)
let MustTerminate_limit_eq = prove
 (`good_dimindex (:A) ==>
   ?k. MustTerminate_limit (:A) =
       10 * dimword (:A) * dimword (:A) + 10 * dimword (:A) + 100 + k`,
  DISCH_TAC THEN REWRITE_TAC[MustTerminate_limit_def] THEN
  SUBGOAL_THEN `10 * dimword (:A) * dimword (:A) + 10 * dimword (:A) + 100 <=
                dimword(:A) EXP dimword(:A)` MP_TAC THENL
   [TRANS_TAC LE_TRANS `dimword(:A) EXP 3` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def]) THEN
      ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN
      MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN
      MP_TAC(INST_TYPE [`:A`,`:N`] ZERO_LT_dimword) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def]) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    REWRITE_TAC[ADD_ASSOC; GSYM LE_EXISTS] THEN ARITH_TAC]);;

(* HOL4 line 178 *)
let SND_i2mw_NIL = prove
 (`!i. SND (i2mw i:bool#(A word)list) = [] <=> i = &0`,
  GEN_TAC THEN REWRITE_TAC[i2mw_def; SND; n2mw_NIL] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  INT_ARITH_TAC);;

(* HOL4 line 187 *)
let word_cmp_Test_1 = prove
 (`!w:A word. asm_word_cmp asm_Test w (word 1) <=> ~(bit 0 w)`,
  REWRITE_TAC[asm_word_cmp_def; WORD_AND_1_BITVAL; GSYM VAL_EQ_0; VAL_WORD_BITVAL] THEN
  REWRITE_TAC[BITVAL_EQ_0]);;

(* HOL4 line 193 *)
let word_bit_if_1_0 = prove
 (`!b. bit 0 (if b then word 1 else word 0:A word) <=> b`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

(* HOL4 line 199 *)
let get_iop_def = cake_def
  `get_iop (n:num) =
     if n = 0 then multiword_Add else
     if n = 1 then multiword_Sub else
     if n = 4 then multiword_Mul else
     if n = 5 then multiword_Div else
                   multiword_Mod`;;

(* HOL4 line 208 *)
let data_to_word_bignumProof_int_op_def = cake_def
  `data_to_word_bignumProof_int_op op_index (i:int) j =
     if op_index = 0 then SOME (i + j) else
     if op_index = 1 then SOME (i - j) else
     if op_index = 4 then SOME (i * j) else
     if op_index = 5 /\ ~(j = &0) then SOME (int_div i j) else
     if op_index = 6 /\ ~(j = &0) then SOME (integer_int_mod i j) else NONE`;;

(* HOL4 line 217 *)
let get_sign_word_lemma = prove
 (`!x:A word.
     good_dimindex (:A) ==>
     word_and (word 1) (word_ushr x 4) = if bit 4 x then word 1 else word 0:A word`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_USHR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_1; BIT_WORD_0] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

(* HOL4 line 225 (local) *)
let if_eq_b2w = prove
 (`!b. (if b then word 1 else word 0) = b2w b:A word`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[multiword_b2w_def; bitval]);;

(* HOL4 line 232 *)
let option_le_max_dest = prove
 (`!a b. option_le a b ==> OPTION_MAP2 MAX a b = b`,
  REPEAT GEN_TAC THEN CASES_ON `a:num option` THEN CASES_ON `b:num option` THEN
  REWRITE_TAC[option_le_def; OPTION_MAP2_THM; option_INJ] THEN ARITH_TAC);;

(* HOL4 line 240 *)
let option_map_max_comm = prove
 (`!a b. OPTION_MAP2 MAX a b = OPTION_MAP2 MAX b a`,
  REPEAT GEN_TAC THEN CASES_ON `a:num option` THEN CASES_ON `b:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_INJ] THEN ARITH_TAC);;

(* HOL4 line 248 (local) *)
let b2n_not = prove
 (`!c. (if c then 0 else 1) = bitval (~c)`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[bitval]);;

let BIGPAUX_LD1_FACTS = prove
 (`!k. good_dimindex(:A) /\ SUC k < dimword(:A) ==>
       ~(word (SUC k):A word = word 0) /\ word_sub (word (SUC k)) (word 1) = word k:A word /\
       val (word 1:A word) = 1 /\
       val (word (dimindex(:A) - 1):A word) = dimindex(:A) - 1 /\
       ~(dimindex(:A) - 1 = 0) /\ ~(dimindex(:A) <= dimindex(:A) - 1) /\
       ~(dimindex(:A) <= 1)`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT; NOT_SUC]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
    check ((=) `good_dimindex(:A)` o concl)) THEN
  ASM_REWRITE_TAC[VAL_WORD; dimword_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGPAUX_WORD_XOR_NEG1 = prove
 (`!x:A word. word_xor x (word_neg (word 1)) = word_not x`,
  REWRITE_TAC[WORD_NEG_1; WBIGPAUX_WORD_XOR_NOT0]);;

let BIGPAUX_ADD_CARRY_EQ = prove
 (`!(x:A word) y c.
     word_add_carry x y (if c then word 1 else word 0) =
     (word_add (word_add x y) (b2w c),
      if dimword(:A) <= val x + val y + bitval c then word 1 else word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_add_carry_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `~(word 1:A word = word 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1; VAL_WORD_0] THEN ARITH_TAC; ALL_TAC] THEN
  CASES_ON `c:bool` THEN ASM_REWRITE_TAC[multiword_b2w_def; bitval; PAIR_EQ] THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL; ADD_CLAUSES; ADD_ASSOC] THEN
  TRY(CONV_TAC WORD_RULE));;

let BIGPAUX_ADD_CARRY_1 = prove
 (`!(x:A word) y.
     word_add_carry x y (word 1) =
     (word_add (word_add x y) (word 1),
      if dimword(:A) <= val x + val y + 1 then word 1 else word 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`x:A word`; `y:A word`; `T`] BIGPAUX_ADD_CARRY_EQ) THEN
  REWRITE_TAC[multiword_b2w_def; bitval]);;

let BIGPAUX_LD1_EVAL =
  BIGPAUX_EVAL_TAC ["single_div_loop"; "mw_sub"] THEN
  REWRITE_TAC[BIGPAUX_WORD_XOR_NEG1; BIGPAUX_ADD_CARRY_1; BIGPAUX_ADD_CARRY_EQ] THEN
  BIGPAUX_EVAL_TAC ["single_div_loop"; "mw_sub"];;

let BIGPAUX_LD1_SEQ = ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN BIGPAUX_LD1_EVAL;;

let bigp_is_sdl_eq tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "single_div_loop" with Failure _ -> false);;

(* the recursive call: the induction hypothesis ih at the callee state, with *)
(* the arguments of the single_div_loop assumption                          *)

let BIGPAUX_LD1_CALL_GEN_TAC (fin:tactic) (ih:thm) : tactic = fun (asl,w as g) ->
  let th = snd (find (fun (_,th) -> bigp_is_sdl_eq (concl th)) asl) in
  let tup = rand (lhs (concl th)) in
  let _,r1 = dest_pair tup in
  let ns,r2 = dest_pair r1 in
  let m',is' = dest_pair r2 in
  let args = dest_list ns @ [m'] @ dest_list is' in
  (BIGPAUX_MATCH_ABBREV_TAC
     `wl_evaluate (LongDiv1_code (c:data_to_word_config), t3:(A,C,FFI)wl_state)`
     `t3:(A,C,FFI)wl_state` THEN
   MP_TAC(SPECL (args @ [`t3:(A,C,FFI)wl_state`; `r1:num`; `r2:num`; `m1:A word`;
                         `is1:(A word)list`; `c:data_to_word_config`]) ih) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "t3" THEN BIGPAUX_LD1_EVAL THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN BIGPAUX_LD1_EVAL THEN
   MAP_EVERY EXISTS_TAC [`j1:A word`; `j2:A word`; mk_var("max",`:num option`)] THEN
   fin) g;;

let BIGPAUX_LD1_CALL_TAC = BIGPAUX_LD1_CALL_GEN_TAC
  (ASM_REWRITE_TAC[] THEN EXPAND_TAC "t3" THEN
   REWRITE_TAC[wl_state_component_equality] THEN SIMP[OPTION_MAP2_MAX_CANCEL] THEN
   ARITH_TAC);;

let bigp_has_sdl tm =
  can (find_term (fun t -> is_const t && fst(dest_const t) = "single_div_loop")) tm;;

let BIGPAUX_B2W_T = prove
 (`b2w T = word 1:A word`,
  REWRITE_TAC[multiword_b2w_def; BITVAL_CLAUSES]);;

let BIGPAUX_IF_NONE_SOME = prove
 (`!b (x:bool). (if b then NONE else SOME x) = SOME T <=> ~b /\ x`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ]);;

let BIGPAUX_LD1_SDL_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (bigp_has_sdl o concl)) THEN
  ASM_REWRITE_TAC[mw_sub_def; single_sub_def; single_add_def; BIGPAUX_B2W_T;
                  BITVAL_CLAUSES; BIGPAUX_IF_NONE_SOME; WORD_LOWER_REFL] THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC;;

let BIGPAUX_LD1_STEP_GEN_TAC (calltac:thm->tactic) (ih:thm) : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP BIGPAUX_LD1_FACTS o
    CONJ (ASSUME `good_dimindex(:A)`) o
    check ((=) `SUC k < dimword(:A)` o concl)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(wl_state_clock (t2:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `single_div_loop (word (SUC k),[n1;n2],m,[i1;i2]) =
               (m1:A word,is1:(A word)list)` THEN
  ONCE_REWRITE_TAC[single_div_loop_def] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; mw_shift_def] THEN
  ONCE_REWRITE_TAC[mw_cmp_def] THEN REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST] THEN
  ONCE_REWRITE_TAC[mw_cmp_def] THEN REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST] THEN
  ONCE_REWRITE_TAC[mw_cmp_def] THEN REWRITE_TAC[NOT_CONS_NIL; LAST; BUTLAST] THEN
  ABBREV_TAC `n2' = word_ushr (n2:A word) 1` THEN
  ABBREV_TAC `n1' = word_or (word_ushr (n1:A word) 1) (word_shl n2 (dimindex (:A) - 1))` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[LongDiv1_code_def] THEN
  BIGPAUX_ASM_SIMP_TAC ["single_div_loop"; "mw_sub"] [ShiftVar_def; LET_DEF; LET_END_DEF; GE] THEN
  BIGPAUX_LD1_EVAL THEN
  BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN
  ASM_CASES_TAC `word_ult (i2:A word) n2'` THENL
   [SUBGOAL_THEN `~(i2:A word = n2')` ASSUME_TAC THENL
     [ASM_MESON_TAC[WORD_LOWER_NOT_EQ]; ALL_TAC] THEN
    BIGPAUX_LD1_SDL_TAC THEN BIGPAUX_LD1_SEQ THEN calltac ih;
    ALL_TAC] THEN
  BIGPAUX_LD1_SEQ THEN
  ASM_CASES_TAC `i2:A word = n2'` THENL
   [ASM_CASES_TAC `word_ult (i1:A word) n1'` THENL
     [SUBGOAL_THEN `~(i1:A word = n1')` ASSUME_TAC THENL
       [ASM_MESON_TAC[WORD_LOWER_NOT_EQ]; ALL_TAC] THEN
      BIGPAUX_LD1_SDL_TAC THEN BIGPAUX_LD1_SEQ THEN calltac ih;
      BIGPAUX_LD1_SDL_TAC THEN
      BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN
      BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN
      calltac ih];
    BIGPAUX_LD1_SDL_TAC THEN
    BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN
    BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN BIGPAUX_LD1_SEQ THEN
    calltac ih];;

let BIGPAUX_LD1_STEP_TAC = BIGPAUX_LD1_STEP_GEN_TAC BIGPAUX_LD1_CALL_TAC;;

let BIGPAUX_LD1_CALL2_TAC = BIGPAUX_LD1_CALL_GEN_TAC
  (ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [EXPAND_TAC "t3" THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
     ARITH_TAC;
     STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
       mp4_is_app "option_le" (lhand (lhand (concl th))))) THEN
     EXPAND_TAC "t3" THEN SIMP[option_le_max_right; option_le_refl] THEN
     DISCH_THEN SUBST1_TAC THEN
     ONCE_REWRITE_TAC[option_map_max_comm] THEN MATCH_MP_TAC option_le_max_dest THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let BIGPAUX_LD1_STEP2_TAC = BIGPAUX_LD1_STEP_GEN_TAC BIGPAUX_LD1_CALL2_TAC;;

(* HOL4 line 254 *)
let LongDiv1_thm' = prove
 (`!k n1 n2 m i1 i2 (t2:(A,C,FFI)wl_state) r1 r2 m1 is1 (c:data_to_word_config).
     single_div_loop (word k,[n1;n2],m,[i1;i2]) = (m1,is1) /\
     lookup LongDiv1_location (wl_state_code t2) = SOME (7,LongDiv1_code c) /\
     lookup 0 (wl_state_locals t2) = SOME (wl_Loc r1 r2) /\
     lookup 2 (wl_state_locals t2) = SOME (wl_Word (word k)) /\
     lookup 4 (wl_state_locals t2) = SOME (wl_Word n2) /\
     lookup 6 (wl_state_locals t2) = SOME (wl_Word n1) /\
     lookup 8 (wl_state_locals t2) = SOME (wl_Word m) /\
     lookup 10 (wl_state_locals t2) = SOME (wl_Word i1) /\
     lookup 12 (wl_state_locals t2) = SOME (wl_Word i2) /\
     k < dimword (:A) /\ k < wl_state_clock t2 /\ good_dimindex (:A) /\
     ~data_to_word_config_has_longdiv c ==>
     ?j1 j2 max.
       is1 = [j1;j2] /\
       wl_evaluate (LongDiv1_code c,t2) =
         (SOME (wl_Result (wl_Loc r1 r2) [wl_Word m1]),
          wl_state_clock_fupd (K (wl_state_clock t2 - k))
            (wl_state_locals_fupd (K LN)
               (wl_state_locals_size_fupd (K (SOME 0))
                  (wl_state_stack_max_fupd (K max)
                     (wl_state_store_fupd
                        (K (wl_state_store t2 |+ (Temp (word 28),wl_Word (HD is1))))
                        t2))))) /\
       (max = wl_state_stack_max t2 \/
        max = OPTION_MAP2 MAX (wl_state_stack_max t2)
                (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t2))
                   (lookup LongDiv1_location (wl_state_stack_size t2))))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `single_div_loop (word 0,[n1;n2],m,[i1;i2]) =
                 (m1:A word,is1:(A word)list)` THEN
    ONCE_REWRITE_TAC[single_div_loop_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[LongDiv1_code_def] THEN SIMP BIGPAUX_EV_THMS THEN
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN MESON_TAC[];
    POP_ASSUM(fun ih -> REPEAT GEN_TAC THEN STRIP_TAC THEN BIGPAUX_LD1_STEP_TAC ih)]);;

(* HOL4 line 365 *)
let LongDiv1_thm = prove
 (`!k n1 n2 m i1 i2 (t2:(A,C,FFI)wl_state) r1 r2 m1 is1 (c:data_to_word_config).
     single_div_loop (word k,[n1;n2],m,[i1;i2]) = (m1,is1) /\
     lookup LongDiv1_location (wl_state_code t2) = SOME (7,LongDiv1_code c) /\
     lookup 0 (wl_state_locals t2) = SOME (wl_Loc r1 r2) /\
     lookup 2 (wl_state_locals t2) = SOME (wl_Word (word k)) /\
     lookup 4 (wl_state_locals t2) = SOME (wl_Word n2) /\
     lookup 6 (wl_state_locals t2) = SOME (wl_Word n1) /\
     lookup 8 (wl_state_locals t2) = SOME (wl_Word m) /\
     lookup 10 (wl_state_locals t2) = SOME (wl_Word i1) /\
     lookup 12 (wl_state_locals t2) = SOME (wl_Word i2) /\
     k < dimword (:A) /\ k < wl_state_clock t2 /\ good_dimindex (:A) /\
     ~data_to_word_config_has_longdiv c ==>
     ?j1 j2 max.
       is1 = [j1;j2] /\
       wl_evaluate (LongDiv1_code c,t2) =
         (SOME (wl_Result (wl_Loc r1 r2) [wl_Word m1]),
          wl_state_clock_fupd (K (wl_state_clock t2 - k))
            (wl_state_locals_fupd (K LN)
               (wl_state_locals_size_fupd (K (SOME 0))
                  (wl_state_stack_max_fupd (K max)
                     (wl_state_store_fupd
                        (K (wl_state_store t2 |+ (Temp (word 28),wl_Word (HD is1))))
                        t2))))) /\
       (option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t2))
                     (wl_state_locals_size t2)) (wl_state_stack_max t2) /\
        wl_state_locals_size t2 = lookup LongDiv1_location (wl_state_stack_size t2) ==>
        max = wl_state_stack_max t2)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `single_div_loop (word 0,[n1;n2],m,[i1;i2]) =
                 (m1:A word,is1:(A word)list)` THEN
    ONCE_REWRITE_TAC[single_div_loop_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[LongDiv1_code_def] THEN SIMP BIGPAUX_EV_THMS THEN
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN MESON_TAC[];
    POP_ASSUM(fun ih -> REPEAT GEN_TAC THEN STRIP_TAC THEN BIGPAUX_LD1_STEP2_TAC ih)]);;

(* HOL4 line 480 (local, simp) *)
let data_to_word_bignumProof_lt_dimindex_MOD_dimword = prove
 (`!n. n < dimindex (:A) ==> n MOD dimword (:A) = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
  ASM_MESON_TAC[LT_TRANS; INST_TYPE [`:A`,`:N`] dimindex_lt_dimword]);;

let _ = cake_add_simps [data_to_word_bignumProof_lt_dimindex_MOD_dimword];;

(* HOL4 line 488 *)
let get_real_addr_lemma = prove
 (`!c v (t:(A,C,FFI)wl_state) ptr_w x.
     shift_length c < dimindex (:A) /\
     good_dimindex (:A) /\
     wl_get_var v t = SOME (wl_Word ptr_w) /\
     get_real_addr c (wl_state_store t) ptr_w = SOME x ==>
     wl_word_exp t (real_addr c v) = SOME (wl_Word (x:A word))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. m < dimindex(:A) ==> val(word m:A word) = m` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_MESON_TAC[LT_TRANS; dimindex_lt_dimword; dimword_def]; ALL_TAC] THEN
  SUBGOAL_THEN `backend_common_word_shift (:A) < dimindex(:A)` ASSUME_TAC THENL
   [REWRITE_TAC[backend_common_word_shift_def] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) ptr_w =
               SOME (x:A word)` THEN
  REWRITE_TAC[get_real_addr_def; real_addr_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) CurrHeap` THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `a:A word_loc` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASM_REWRITE_TAC[wl_word_exp_def; wl_get_store_def; wl_get_var_def; the_words_def; MAP] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[word_op_def; word_sh_def] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[OPTION_MAP_DEF; GE; ARITH_RULE `l < d ==> l - k < d:num`;
               ARITH_RULE `l < d ==> ~(d <= l - k:num)`;
               ARITH_RULE `l < d ==> ~(d <= l:num)`] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[OPTION_MAP_DEF; GE; ARITH_RULE `l < d ==> l - k < d:num`;
               ARITH_RULE `l < d ==> ~(d <= l - k:num)`;
               ARITH_RULE `l < d ==> ~(d <= l:num)`] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ITLIST; WORD_ADD_0; option_INJ] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;

(* HOL4 line 504 *)
let memory_rel_lookup = prove
 (`!c be ts refs s st (m:A word->A word_loc) dm l1 l2 xs n x w.
     memory_rel c be ts refs s st m dm
       (APPEND (join_env l1 (toAList (sptree_inter l2 (adjust_set l1)))) xs) /\
     lookup n l1 = SOME x /\ lookup (adjust_var n) l2 = SOME w ==>
     memory_rel c be ts refs s st m dm
       (CONS (x,w) (APPEND (join_env l1 (toAList (sptree_inter l2 (adjust_set l1)))) xs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                                heap_element)list`;
                        `limit:num`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE[APPEND]
    (INST [`[]:(data_v#A word_loc)list`,`ys:(data_v#A word_loc)list`]
      (SPEC_ALL word_ml_inv_lookup))) THEN
  ASM_REWRITE_TAC[]);;

let BIGPAUX_state_rel_memory_rel_var = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs src x.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var src (data_state_locals s) = SOME x ==>
     ?w vars. lookup (adjust_var src) (wl_state_locals t) = SOME w /\
       memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
         (data_state_space s) (wl_state_store t) (wl_state_memory t)
         (wl_state_mdomain t) (CONS (x,w) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`src:num`; `x:data_v`] o MATCH_MP state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[wl_get_var_def] THEN DISCH_THEN(X_CHOOSE_TAC `w:A word_loc`) THEN
  EXISTS_TAC `w:A word_loc` THEN ASM_REWRITE_TAC[] THEN
  MP4_X_ASM "data_to_word_gcProof_state_rel"
    (MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm]) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def]) THEN
  DRULE_ALL memory_rel_lookup THEN MESON_TAC[]);;

let BIGPAUX_LENGTH_n2mw_LE_1 = prove
 (`!n. n < dimword(:A) ==> LENGTH (n2mw n:(A word)list) <= 1`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[n2mw_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[DIV_LT] THEN ONCE_REWRITE_TAC[n2mw_def] THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let BIGPAUX_small_int_LENGTH = prove
 (`!i. small_int (:A) i ==> LENGTH (SND (i2mw i):(A word)list) <= 1`,
  GEN_TAC THEN REWRITE_TAC[small_int_def; i2mw_def; SND] THEN STRIP_TAC THEN
  MATCH_MP_TAC BIGPAUX_LENGTH_n2mw_LE_1 THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  MP_TAC(MATCH_MP (ARITH_RULE `0 < n ==> n DIV 8 < n`)
                  (INST_TYPE [`:A`,`:N`] ZERO_LT_dimword)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  MAP_EVERY UNDISCH_TAC [`--(&(dimword(:A) DIV 8)) <= i:int`;
                         `i:int < &(dimword(:A) DIV 8)`] THEN
  INT_ARITH_TAC);;

(* HOL4 line 516 *)
let evaluate_AddNumSize = prove
 (`!src c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs i w.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var src (data_state_locals s) = SOME (data_Number i) ==>
     wl_evaluate (AddNumSize c src,wl_set_var 1 (wl_Word w) t) =
       (NONE,wl_set_var 1 (wl_Word (word_add w
          (word (4 * LENGTH ((SND (i2mw i):(A word)list)))))) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `src:num`; `data_Number i`]
    BIGPAUX_state_rel_memory_rel_var) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A word_loc` (X_CHOOSE_THEN `vars:(data_v#A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `good_dimindex(:A) /\ shift_length c < dimindex(:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
    `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `i:int`; `v:A word_loc`; `vars:(data_v#A word_loc)list`] memory_rel_any_Number_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w4:A word` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  REWRITE_TAC[AddNumSize_def] THEN
  ASM_CASES_TAC `w4:A word = word 0` THENL
   [MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
      `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
      `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
      `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
      `i:int`; `w4:A word`; `vars:(data_v#A word_loc)list`; `&0:int`]
      memory_rel_Number_const_test) THEN
    ASM_SIMP_TAC[small_int_0; data_to_word_Smallnum_def; INT_LT_REFL] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[i2mw_def; INT_ABS_NUM; NUM_OF_INT_OF_NUM] THEN
    ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[LENGTH; MULT_CLAUSES; WORD_ADD_0] THEN
    BIGPAUX_EVAL_THMS_TAC [] [adjust_var_NEQ_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bit 0 (w4:A word) <=> ~(word_and w4 (word 1) = word 0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`0`; `w4:A word`] word_index_test) THEN
    REWRITE_TAC[EXP; DIMINDEX_GT_0]; ALL_TAC] THEN
  ASM_CASES_TAC `word_and (w4:A word) (word 1) = word 0` THENL
   [SUBGOAL_THEN `small_int (:A) i` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
      `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
      `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
      `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
      `i:int`; `w4:A word`; `vars:(data_v#A word_loc)list`; `i:int`]
      memory_rel_Number_const_test) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH (SND (i2mw i):(A word)list) = 1` SUBST1_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `n <= 1 /\ ~(n = 0) ==> n = 1`) THEN
      ASM_SIMP_TAC[BIGPAUX_small_int_LENGTH] THEN
      REWRITE_TAC[LENGTH_EQ_NIL; SND_i2mw_NIL] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(w4:A word = word 0)` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        mp4_is_app "Smallnum" (lhs (concl th)))) THEN
      ASM_REWRITE_TAC[data_to_word_Smallnum_def; INT_LT_REFL] THEN
      CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[NUM_OF_INT_OF_NUM];
      ALL_TAC] THEN
    BIGPAUX_EVAL_THMS_TAC [] [adjust_var_NEQ_1; insert_shadow] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; wl_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~small_int (:A) i` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
    `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `i:int`; `wl_Word w4:A word_loc`; `vars:(data_v#A word_loc)list`]
    memory_rel_Number_bignum_IMP_ALT) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `w4:A word = w'` o concl)) THEN
  SUBGOAL_THEN `~(data_to_word_config_len_size c = 0) /\
                data_to_word_config_len_size c + 7 < dimindex(:A)` STRIP_ASSUME_TAC THENL
   [MP4_ASM "memory_rel" (MP_TAC o REWRITE_RULE[memory_rel_def; heap_in_memory_store_def]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_word_exp (wl_state_locals_fupd (K (insert 1 (wl_Word w)
                   (wl_state_locals (t:(A,C,FFI)wl_state)))) t)
                  (real_addr c (adjust_var src)) = SOME (wl_Word a)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w4:A word` THEN
    ASM_SIMP_TAC[wl_get_var_def; lookup_insert; adjust_var_NEQ_1;
                 wl_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word 2:A word) = 2 /\ ~(dimindex(:A) <= 2) /\
     val (word (dimindex(:A) - data_to_word_config_len_size c):A word) =
       dimindex(:A) - data_to_word_config_len_size c /\
     ~(dimindex(:A) <= dimindex(:A) - data_to_word_config_len_size c)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN TRY (MATCH_MP_TAC MOD_LT) THEN MP5AUX_ARITH_TAC; ALL_TAC] THEN
  BIGPAUX_EVAL_THMS_TAC [] [adjust_var_NEQ_1; insert_shadow] THEN
  REWRITE_TAC[GSYM decode_length_def] THEN ASM_REWRITE_TAC[WORD_SHL_WORD; i2mw_def; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let BIGPAUX_small_ival = prove
 (`!i. small_int (:A) i /\ good_dimindex(:A) ==> ival (Smallnum i:A word) = &4 * i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w] THEN
  ASM_SIMP_TAC[small_int_w2i_i2w]);;

let BIGPAUX_small_lt_0 = prove
 (`!i. small_int (:A) i /\ good_dimindex(:A) ==>
       (word_ilt (Smallnum i:A word) (word 0) <=> i < &0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_ILT; BIGPAUX_small_ival; IVAL_WORD_0] THEN
  INT_ARITH_TAC);;

let BIGPAUX_small_n_lt = prove
 (`!n. small_int (:A) (&n) \/ small_int (:A) (--(&n)) ==> 4 * n < dimword(:A)`,
  GEN_TAC THEN REWRITE_TAC[small_int_def] THEN
  MP_TAC(SPEC `dimword(:A)` (ARITH_RULE `!d. 8 * (d DIV 8) <= d`)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL] THEN
  INT_ARITH_TAC);;

let BIGPAUX_small_pos = prove
 (`!n. small_int (:A) (&n) ==> word_ushr (Smallnum (&n):A word) 2 = word n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BIGPAUX_small_n_lt o (fun th -> DISJ1 th
    `small_int (:A) (--(&n))`)) THEN DISCH_TAC THEN
  REWRITE_TAC[data_to_word_Smallnum_def; INT_LT; INT_OF_NUM_LT; LT] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; GSYM dimword_def] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `4 * n < d ==> n < d`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let BIGPAUX_small_neg = prove
 (`!n. small_int (:A) (--(&n)) /\ good_dimindex(:A) ==>
       word_sub (word 0) (word_ishr (Smallnum (--(&n)):A word) 2) = word n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BIGPAUX_small_n_lt o DISJ2 `small_int (:A) (&n)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `word_ishr (Smallnum (--(&n)):A word) 2 = iword (--(&n))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_ISHR] THEN
    ASM_SIMP_TAC[BIGPAUX_small_ival] THEN
    SUBGOAL_THEN `ival (iword (--(&n)):A word) = --(&n)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_IWORD THEN
      SUBGOAL_THEN `n <= 2 EXP (dimindex(:A) - 1)` MP_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
          check ((=) `good_dimindex(:A)` o concl)) THEN
        UNDISCH_TAC `4 * n < dimword(:A)` THEN
        ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_POW] THEN
        MP_TAC(SPEC `dimindex(:A) - 1` INT_LT_POW2) THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    MATCH_MP_TAC INT_DIV_UNIQ THEN EXISTS_TAC `&0:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB_LZERO; IWORD_INT_NEG; WORD_NEG_NEG; GSYM WORD_IWORD]);;

let BIGPAUX_i2mw_small = prove
 (`!i. small_int (:A) i /\ ~(i = &0) ==>
       i2mw i = ((i < &0),[word (num_of_int (abs i))]:(A word)list)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[i2mw_def; PAIR_EQ] THEN
  SUBGOAL_THEN `&(num_of_int (abs i)) = abs i` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN REWRITE_TAC[INT_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(num_of_int (abs i) = 0) /\ num_of_int (abs i) < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP (ARITH_RULE `0 < n ==> n DIV 8 < n`)
                    (INST_TYPE [`:A`,`:N`] ZERO_LT_dimword)) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `small_int (:A) i` THEN REWRITE_TAC[small_int_def] THEN
    UNDISCH_TAC `~(i:int = &0)` THEN INT_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN ASM_SIMP_TAC[DIV_LT; MOD_LT] THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[]);;

let BIGPAUX_FUPDATE_REV3 = prove
 (`!(f:(A,B)fmap) k1 k2 k3 a b c.
     ~(k1 = k2) /\ ~(k1 = k3) /\ ~(k2 = k3) ==>
     f |+ (k1,a) |+ (k2,b) |+ (k3,c) = f |+ (k3,c) |+ (k2,b) |+ (k1,a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`k1:A = x`; `k2:A = x`; `k3:A = x`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let BIGPAUX_FUPDATE_PERM3 = prove
 (`!(f:(A,B)fmap) k1 k2 k3 a b c.
     ~(k1 = k2) /\ ~(k1 = k3) /\ ~(k2 = k3) ==>
     f |+ (k2,b) |+ (k1,a) |+ (k3,c) = f |+ (k3,c) |+ (k2,b) |+ (k1,a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`k1:A = x`; `k2:A = x`; `k3:A = x`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
(* small numerals as shift amounts, for any good word size *)

let BIGPAUX_SHIFT_FACTS = prove
 (`good_dimindex(:A) ==>
   val (word 1:A word) = 1 /\ val (word 2:A word) = 2 /\ val (word 4:A word) = 4 /\
   ~(dimindex(:A) <= 1) /\ ~(dimindex(:A) <= 2) /\ ~(dimindex(:A) <= 4)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD; dimword_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGPAUX_LEN_SHIFT_FACTS = prove
 (`!c. good_dimindex(:A) /\ ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size c + 7 < dimindex(:A) ==>
       val (word (dimindex(:A) - data_to_word_config_len_size c):A word) =
         dimindex(:A) - data_to_word_config_len_size c /\
       ~(dimindex(:A) <= dimindex(:A) - data_to_word_config_len_size c)`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN ARITH_TAC);;

let BIGPAUX_AND_NOT0 = prove
 (`!x:A word. word_and x (word_not (word 0)) = x`,
  CONV_TAC WORD_BITWISE_RULE);;

(* HOL4 line 579 *)
let AnyHeader_thm = prove
 (`!t1 t2 t3 r c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs i a.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var r (data_state_locals s) = SOME (data_Number i) /\
     ALL_DISTINCT [t1;t2;t3] ==>
     ?a2 a3 temp.
       wl_evaluate (AnyHeader c (adjust_var r) a t1 t2 t3,t) =
         (NONE,(wl_set_store (Temp t1) (wl_Word (mc_header (i2mw i)))
                (wl_set_store (Temp t2) (wl_Word a2)
                (wl_set_store (Temp t3) (wl_Word a3) (wl_set_var 7 temp t))))) /\
       (i = &0 ==>
          small_int (:A) (&0) /\ i2mw i = (F,[]:(A word)list) /\
          a2 = word 0 /\ a3 = word 0) /\
       (small_int (:A) i /\ ~(i = &0) ==>
          i2mw i = ((i < &0),[a3]) /\
          FLOOKUP (wl_state_store t) (if a then OtherHeap else NextFree) =
            SOME (wl_Word a2)) /\
       (~small_int (:A) i ==>
          ?w x. wl_get_var (adjust_var r) t = SOME (wl_Word w) /\
                get_real_addr c (wl_state_store t) w = SOME x /\
                a2 = word_add x bytes_in_word)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `r:num`; `data_Number i`]
    BIGPAUX_state_rel_memory_rel_var) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A word_loc` (X_CHOOSE_THEN `vars:(data_v#A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `good_dimindex(:A) /\ shift_length c < dimindex(:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
    `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `i:int`; `v:A word_loc`; `vars:(data_v#A word_loc)list`] memory_rel_any_Number_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w4:A word` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM] o
    check (fun th -> mp4_is_app "ALL_DISTINCT" (concl th))) THEN
  SUBGOAL_THEN `?other a2'. FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) OtherHeap =
                  SOME (wl_Word other) /\
                FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word a2') /\
                ~(data_to_word_config_len_size c = 0) /\
                data_to_word_config_len_size c + 7 < dimindex(:A)` STRIP_ASSUME_TAC THENL
   [MP4_ASM "memory_rel" (MP_TAC o REWRITE_RULE[memory_rel_def; heap_in_memory_store_def]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "option"; injectivity "word_loc"] THEN
    MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BIGPAUX_SHIFT_FACTS o
    check ((=) `good_dimindex(:A)` o concl)) THEN
  MP_TAC(SPEC `c:data_to_word_config` BIGPAUX_LEN_SHIFT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[AnyHeader_def] THEN
  ASM_CASES_TAC `i:int = &0` THENL
   [(FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `w4:A word = word 0` SUBST_ALL_TAC THENL
     [MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
        `THE (data_state_tstamps (s:(C,FFI)data_state))`;
        `data_state_refs (s:(C,FFI)data_state)`; `data_state_space (s:(C,FFI)data_state)`;
        `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
        `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `&0:int`; `wl_Word w4:A word_loc`;
        `vars:(data_v#A word_loc)list`] memory_rel_Number_IMP) THEN
      ASM_SIMP_TAC[small_int_0; injectivity "word_loc"; data_to_word_Smallnum_def;
                   INT_LT_REFL] THEN
      CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[NUM_OF_INT_OF_NUM];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`word 0:A word`; `word 0:A word`; `wl_Word (word 0):A word_loc`] THEN
    ASM_SIMP_TAC[small_int_0] THEN
    REWRITE_TAC[i2mw_def; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_LT_REFL] THEN
    ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[mc_header_def; LENGTH; MULT_CLAUSES] THEN
    BIGPAUX_EVAL_THMS_TAC [] [data_to_word_list_Seq_def; adjust_var_NEQ] THEN
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
    MATCH_MP_TAC BIGPAUX_FUPDATE_REV3 THEN ASM_REWRITE_TAC[injectivity "store_name"]);
    ASM_CASES_TAC `small_int (:A) i` THENL
     [(SUBGOAL_THEN `w4 = Smallnum i:A word` SUBST_ALL_TAC THENL
     [MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
        `THE (data_state_tstamps (s:(C,FFI)data_state))`;
        `data_state_refs (s:(C,FFI)data_state)`; `data_state_space (s:(C,FFI)data_state)`;
        `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
        `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `i:int`; `wl_Word w4:A word_loc`;
        `vars:(data_v#A word_loc)list`] memory_rel_Number_IMP) THEN
      ASM_SIMP_TAC[injectivity "word_loc"]; ALL_TAC] THEN
    SUBGOAL_THEN `~(Smallnum i:A word = word 0) /\
                  word_and (Smallnum i:A word) (word 1) = word 0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[GSYM IVAL_EQ_0] THEN ASM_SIMP_TAC[BIGPAUX_small_ival] THEN
        UNDISCH_TAC `~(i:int = &0)` THEN INT_ARITH_TAC;
        ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
        REWRITE_TAC[data_to_word_memoryProof_Smallnum_bits]];
      ALL_TAC]) THEN
      ASM_CASES_TAC `i:int < &0` THENL
       [(SUBGOAL_THEN `?n. i:int = --(&n)` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `num_of_int (--i)` THEN
    SUBGOAL_THEN `&(num_of_int (--i)) = --i:int` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_ilt (Smallnum (--(&n)):A word) (word 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BIGPAUX_small_lt_0]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`if a then other else a2':A word`; `word n:A word`;
                        `wl_Word (word 0):A word_loc`] THEN
  ASM_SIMP_TAC[BIGPAUX_i2mw_small; INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM] THEN
  CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[mc_header_def; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  BOOL_CASES_TAC `a:bool` THEN
  BIGPAUX_EVAL_THMS_TAC [] [data_to_word_list_Seq_def; adjust_var_NEQ;
    distinctness "store_name"] THEN
  (ASM_SIMP_TAC[BIGPAUX_small_neg] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
  MATCH_MP_TAC BIGPAUX_FUPDATE_REV3 THEN ASM_REWRITE_TAC[injectivity "store_name"]));
        (SUBGOAL_THEN `?n. i:int = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~word_ilt (Smallnum (&n):A word) (word 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BIGPAUX_small_lt_0]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`if a then other else a2':A word`; `word n:A word`;
                        `wl_Word (word 0):A word_loc`] THEN
  ASM_SIMP_TAC[BIGPAUX_i2mw_small; INT_ABS_NUM; NUM_OF_INT_OF_NUM] THEN
  CONJ_TAC THENL [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[mc_header_def; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  BOOL_CASES_TAC `a:bool` THEN
  BIGPAUX_EVAL_THMS_TAC [] [data_to_word_list_Seq_def; adjust_var_NEQ;
    distinctness "store_name"] THEN
  ASM_SIMP_TAC[BIGPAUX_small_pos] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
  MATCH_MP_TAC BIGPAUX_FUPDATE_REV3 THEN ASM_REWRITE_TAC[injectivity "store_name"])];
      (SUBGOAL_THEN `bit 0 (w4:A word) /\ ~(word_and w4 (word 1) = word 0) /\ ~(w4 = word 0)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`0`; `w4:A word`] word_index_test) THEN
    REWRITE_TAC[EXP; DIMINDEX_GT_0] THEN ASM_MESON_TAC[BIT_WORD_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
    `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `i:int`; `wl_Word w4:A word_loc`; `vars:(data_v#A word_loc)list`]
    memory_rel_Number_bignum_IMP_ALT) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `w4:A word` && is_var (rhs (concl th)))) THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var r)) =
                SOME (wl_Word a')` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w4:A word` THEN
    ASM_REWRITE_TAC[wl_get_var_def]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`word_add a' bytes_in_word:A word`; `word 0:A word`;
                        `wl_Word a':A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; MAP_EVERY EXISTS_TAC [`w4:A word`; `a':A word`] THEN
                  ASM_REWRITE_TAC[wl_get_var_def]] THEN
  BIGPAUX_EVAL_THMS_TAC [] [data_to_word_list_Seq_def; adjust_var_NEQ;
    distinctness "store_name"; BIGPAUX_AND_NOT0] THEN
  REWRITE_TAC[GSYM decode_length_def] THEN ASM_REWRITE_TAC[WORD_SHL_WORD] THEN
  ASM_SIMP_TAC[get_sign_word_lemma] THEN
  REWRITE_TAC[i2mw_def; mc_header_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `2 * n = n * 2`] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
  MATCH_MP_TAC BIGPAUX_FUPDATE_PERM3 THEN ASM_REWRITE_TAC[injectivity "store_name"])]]);;

(* HOL4 line 733 *)
let state_rel_set_store_Temp = prove
 (`!c l1 l2 (s:(C,FFI)data_state) tmp w (t:(A,C,FFI)wl_state) vs locs.
     data_to_word_gcProof_state_rel c l1 l2 s (wl_set_store (Temp tmp) w t) vs locs =
     data_to_word_gcProof_state_rel c l1 l2 s t vs locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; wl_set_store_def] THEN
  SIMP[code_oracle_rel_def; FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT;
       FAPPLY_FUPDATE_THM; memory_rel_Temp]);;

(* HOL4 line 744 *)
let state_rel_IMP_num_size_limit = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs k i.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var k (data_state_locals s) = SOME (data_Number i) ==>
     LENGTH (SND (i2mw i):(A word)list) < dimword (:A) DIV 16`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`k:num`; `data_Number i`] o
              MATCH_MP state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex(:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  ASM_CASES_TAC `small_int (:A) i` THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[BIGPAUX_small_int_LENGTH] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP4_X_ASM "data_to_word_gcProof_state_rel"
    (MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm]) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def; wl_get_var_def]) THEN
  DRULE_ALL memory_rel_lookup THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_Number_bignum_IMP_ALT THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[i2mw_def; SND] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE `a < b ==> b <= c ==> a < c`) o
    check (fun th -> can (find_term ((=) `dimindex(:A) - 4`)) (concl th))) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
    check ((=) `good_dimindex(:A)` o concl)) THEN
  ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 768 *)
let word_list_store_list = prove
 (`!xs (a:A word) frame m dm.
     (misc_word_list a xs STAR frame) (fun2set (m,dm)) ==>
     ?m2. (data_to_word_memoryProof_store_list a
             (REPLICATE (LENGTH xs) (wl_Word (word 0))) m dm = SOME m2) /\
          (misc_word_list a (REPLICATE (LENGTH xs) (wl_Word (word 0))) STAR frame)
            (fun2set (m2,dm))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def; REPLICATE; LENGTH;
              misc_word_list_def] THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `m:A word->A word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MP4AUX_SEP_R_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(misc_word_list (word_add a bytes_in_word) t STAR
     (set_sep_one (a:A word,wl_Word (word 0):A word_loc) STAR frame))
       (fun2set ((a =+ wl_Word (word 0)) m,dm))` MP_TAC THENL
   [MP4AUX_SEP_W_TAC THEN MP4AUX_SEP_AC_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun ih -> DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP ih)) THEN
  EXISTS_TAC `m2:A word->A word_loc` THEN ASM_REWRITE_TAC[] THEN
  MP4AUX_SEP_AC_TAC);;

(* HOL4 line 780 *)
let MustTerminate_limit_SUB_2 = prove
 (`good_dimindex (:A) ==> dimword (:A) <= MustTerminate_limit (:A) - 2`,
  DISCH_TAC THEN REWRITE_TAC[MustTerminate_limit_def] THEN
  MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN ARITH_TAC);;

(* HOL4 line 790 (dataSem cut_env: wordSem's, brought to the front by the   *)
(* header, does not type-check with a num_set)                               *)
let cut_env_fromList_sing = prove
 (`!l1 l2. data_cut_env (fromList [one])
             (insert 0 (wl_Loc l1 l2) (LN:(A word_loc)spt)) =
           SOME (insert 0 (wl_Loc l1 l2) LN)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fromList_def; FOLDL] THEN
  CASE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[insert_def] THEN REWRITE_TAC[] THEN
  REWRITE_TAC[data_cut_env_def; domain_def; sptree_inter_def; mk_wf_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REFL; mk_wf_def]);;

(* HOL4 line 797 *)
let single_div_pre_IMP_single_div_full = prove
 (`!x1 x2 (y:A word).
     single_div_pre x1 x2 y ==> single_div x1 x2 y = single_div_full x1 x2 y`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC single_div_full_thm THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[single_div_pre_def; mw2n_def; VAL_WORD_0] THEN
  REWRITE_TAC[GSYM VAL_EQ_0] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ] THEN ARITH_TAC);;

(* HOL4 line 807 *)
let IMP_LESS_MustTerminate_limit = prove
 (`!i. i < dimword (:A) ==> i < MustTerminate_limit (:A) - 1`,
  GEN_TAC THEN REWRITE_TAC[MustTerminate_limit_def] THEN ARITH_TAC);;

let _ = cake_add_simps [IMP_LESS_MustTerminate_limit];;

(* HOL4 line 814 (the unused bound variable w is left out) *)
let evaluate_LongDiv_code' = prove
 (`!(t:(A,C,FFI)wl_state) l1 l2 c x1 x2 y d1 m1.
     single_div_pre x1 x2 y /\
     single_div x1 x2 y = (d1,m1:A word) /\
     lookup LongDiv1_location (wl_state_code t) = SOME (7,LongDiv1_code c) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word x1) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word x2) /\
     lookup 6 (wl_state_locals t) = SOME (wl_Word y) /\
     dimword (:A) < wl_state_clock t /\ good_dimindex (:A) ==>
     ?ck max.
       wl_evaluate (LongDiv_code c,t) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word d1]),
          wl_state_clock_fupd (K ck)
            (wl_state_locals_fupd (K LN)
               (wl_state_locals_size_fupd (K (SOME 0))
                  (wl_state_store_fupd
                     (K (wl_state_store t |+ (Temp (word 28),wl_Word m1)))
                     (wl_state_stack_max_fupd (K max) t))))) /\
       (max = wl_state_stack_max t \/
        max = OPTION_MAP2 MAX (wl_state_stack_max t)
                (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                   (lookup LongDiv1_location (wl_state_stack_size t))))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `data_to_word_config_has_longdiv (c:data_to_word_config)` THEN
  ASM_REWRITE_TAC[LongDiv_code_def] THENL
   [UNDISCH_TAC `single_div_pre x1 x2 (y:A word)` THEN
    UNDISCH_TAC `single_div x1 x2 y = (d1,m1:A word)` THEN
    REWRITE_TAC[single_div_pre_def; single_div_def; PAIR_EQ; GSYM VAL_EQ_0] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN STRIP_TAC THEN
    REWRITE_TAC[data_to_word_list_Seq_def] THEN BIGPAUX_EVAL_TAC [] THEN
    MAP_EVERY EXISTS_TAC [`wl_state_clock (t:(A,C,FFI)wl_state)`;
                          `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dimindex (:A) + 5 < dimword (:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `single_div_full x1 x2 (y:A word) = (d1,m1)` MP_TAC THENL
   [ASM_MESON_TAC[single_div_pre_IMP_single_div_full]; ALL_TAC] THEN
  REWRITE_TAC[single_div_full_def] THEN
  MP_TAC(ISPEC `single_div_loop (word (dimindex(:A)),[word 0;y],word 0,[x2;x1:A word])`
    PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`mm:A word`; `iss:(A word)list`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  BIGPAUX_EVAL_TAC [] THEN
  BIGPAUX_MATCH_ABBREV_TAC
     `wl_evaluate (LongDiv1_code (c:data_to_word_config), t2:(A,C,FFI)wl_state)`
     `t2:(A,C,FFI)wl_state` THEN
  MP_TAC(SPECL [`dimindex(:A)`; `word 0:A word`; `y:A word`; `word 0:A word`; `x2:A word`;
     `x1:A word`; `t2:(A,C,FFI)wl_state`; `l1:num`; `l2:num`; `mm:A word`;
     `iss:(A word)list`; `c:data_to_word_config`] LongDiv1_thm') THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t2" THEN BIGPAUX_EVAL_TAC [] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN BIGPAUX_EVAL_TAC [] THEN
  EXISTS_TAC `wl_state_clock (t2:(A,C,FFI)wl_state) - dimindex(:A)` THEN
  EXISTS_TAC (mk_var("max",`:num option`)) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "t2" THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[OPTION_MAP2_MAX_CANCEL]);;

(* HOL4 line 865 (the unused bound variable w is left out) *)
let evaluate_LongDiv_code = prove
 (`!(t:(A,C,FFI)wl_state) l1 l2 c x1 x2 y d1 m1.
     single_div_pre x1 x2 y /\
     single_div x1 x2 y = (d1,m1:A word) /\
     lookup LongDiv1_location (wl_state_code t) = SOME (7,LongDiv1_code c) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word x1) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word x2) /\
     lookup 6 (wl_state_locals t) = SOME (wl_Word y) /\
     dimword (:A) < wl_state_clock t /\ good_dimindex (:A) ==>
     ?ck max.
       wl_evaluate (LongDiv_code c,t) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word d1]),
          wl_state_clock_fupd (K ck)
            (wl_state_locals_fupd (K LN)
               (wl_state_locals_size_fupd (K (SOME 0))
                  (wl_state_store_fupd
                     (K (wl_state_store t |+ (Temp (word 28),wl_Word m1)))
                     (wl_state_stack_max_fupd (K max) t))))) /\
       (option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                     (wl_state_locals_size t)) (wl_state_stack_max t) /\
        wl_state_locals_size t = lookup LongDiv1_location (wl_state_stack_size t) ==>
        max = wl_state_stack_max t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `data_to_word_config_has_longdiv (c:data_to_word_config)` THEN
  ASM_REWRITE_TAC[LongDiv_code_def] THENL
   [UNDISCH_TAC `single_div_pre x1 x2 (y:A word)` THEN
    UNDISCH_TAC `single_div x1 x2 y = (d1,m1:A word)` THEN
    REWRITE_TAC[single_div_pre_def; single_div_def; PAIR_EQ; GSYM VAL_EQ_0] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN STRIP_TAC THEN
    REWRITE_TAC[data_to_word_list_Seq_def] THEN BIGPAUX_EVAL_TAC [] THEN
    MAP_EVERY EXISTS_TAC [`wl_state_clock (t:(A,C,FFI)wl_state)`;
                          `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dimindex (:A) + 5 < dimword (:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `single_div_full x1 x2 (y:A word) = (d1,m1)` MP_TAC THENL
   [ASM_MESON_TAC[single_div_pre_IMP_single_div_full]; ALL_TAC] THEN
  REWRITE_TAC[single_div_full_def] THEN
  MP_TAC(ISPEC `single_div_loop (word (dimindex(:A)),[word 0;y],word 0,[x2;x1:A word])`
    PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`mm:A word`; `iss:(A word)list`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  BIGPAUX_EVAL_TAC [] THEN
  BIGPAUX_MATCH_ABBREV_TAC
     `wl_evaluate (LongDiv1_code (c:data_to_word_config), t2:(A,C,FFI)wl_state)`
     `t2:(A,C,FFI)wl_state` THEN
  MP_TAC(SPECL [`dimindex(:A)`; `word 0:A word`; `y:A word`; `word 0:A word`; `x2:A word`;
     `x1:A word`; `t2:(A,C,FFI)wl_state`; `l1:num`; `l2:num`; `mm:A word`;
     `iss:(A word)list`; `c:data_to_word_config`] LongDiv1_thm) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t2" THEN BIGPAUX_EVAL_TAC [] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN BIGPAUX_EVAL_TAC [] THEN
  EXISTS_TAC `wl_state_clock (t2:(A,C,FFI)wl_state) - dimindex(:A)` THEN
  EXISTS_TAC (mk_var("max",`:num option`)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "t2" THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      mp4_is_app "option_le" (lhand (lhand (concl th))))) THEN
    EXPAND_TAC "t2" THEN SIMP[option_le_max_right; option_le_refl] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[option_map_max_comm] THEN MATCH_MP_TAC option_le_max_dest THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 917 *)
let div_code_assum_thm = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     div_code_assum (:FFI) (:C) (wl_state_code t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[div_code_assum_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lookup LongDiv_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                  SOME (4,LongDiv_code c) /\
                lookup LongDiv1_location (wl_state_code t) = SOME (7,LongDiv1_code c) /\
                good_dimindex(:A)` STRIP_ASSUME_TAC THENL
   [MP4_X_ASM "data_to_word_gcProof_state_rel"
      (MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm]) THEN
    REWRITE_TAC[data_to_word_gcProof_code_rel_def; data_to_word_stubs_def; ALL_APPEND; ALL] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DivCode_def; GSYM check_LongDiv_location] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `cut_envs (LS one,LN) (insert i2 (wl_Word w3) (insert i3 (wl_Word w4)
       (insert i4 (wl_Word w5) (wl_state_locals (t1:(A,C,FFI)wl_state))))) =
       SOME (insert 0 ret_val LN,LN)` ASSUME_TAC THENL
   [MATCH_MP_TAC WBIGPAUX_cut_envs_ret THEN ASM_SIMP_TAC[lookup_insert;
      ARITH_RULE `0 < i ==> ~(0 = i)`]; ALL_TAC] THEN
  SUBGOAL_THEN `~(i3:num = i2) /\ ~(i4:num = i2) /\ ~(i4:num = i3) /\ ~(i1:num = i0) /\
                ~(i0 = 0) /\ ~(i1 = 0)` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM]) THEN MP5AUX_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM] o
    check (fun th -> mp4_is_app "ALL_DISTINCT" (concl th))) THEN
  REWRITE_TAC[WBIGPAUX_ev_MustTerminate] THEN ASM_REWRITE_TAC[] THEN
  BIGPAUX_EVAL_THMS_TAC [] [domain_def; NOT_INSERT_EMPTY; ALL_DISTINCT; MEM;
    MustTerminate_limit_NOT_0; push_env_insert_0; GSYM CONJ_ASSOC] THEN
  MP_TAC(ISPEC `single_div w3 w4 (w5:A word)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d1:A word`; `m1:A word`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  BIGPAUX_MATCH_ABBREV_TAC
     `wl_evaluate (LongDiv_code (c:data_to_word_config), t2:(A,C,FFI)wl_state)`
     `t2:(A,C,FFI)wl_state` THEN
  MP_TAC(SPECL [`t2:(A,C,FFI)wl_state`; `n:num`; `l:num`; `c:data_to_word_config`;
     `w3:A word`; `w4:A word`; `w5:A word`; `d1:A word`; `m1:A word`]
     evaluate_LongDiv_code') THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t2" THEN BIGPAUX_EVAL_TAC [] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MustTerminate_limit_def] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t2" THEN
  BIGPAUX_EVAL_THMS_TAC [] [wl_pop_env_def; wl_set_vars_def; alist_insert_def;
    fromAList_def; union_LN; domain_insert; domain_def; insert_shadow; UNION_EMPTY] THEN
  REWRITE_TAC[o_THM; wl_set_var_def; wl_set_store_def; wl_state_component_equality] THEN
  SIMP[] THEN
  REWRITE_TAC[MATCH_MP insert_swap (ARITH_RULE `0 < i1 ==> ~(0 = i1)` |> C MP (ASSUME `0 < i1`))] THEN
  REWRITE_TAC[MATCH_MP insert_swap (ARITH_RULE `0 < i0 ==> ~(0 = i0)` |> C MP (ASSUME `0 < i0`))]);;

(* HOL4 line 955 (the code_rel of word_bignumProof) *)
let IMP_bignum_code_rel = prove
 (`!xx1 xx2 xx3 xx4 xx5 c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     word_bignum_compile Bignum_location 2 1 (Bignum_location + 1,[])
       mc_iop_code = (xx1,xx2,xx3,xx4,xx5) /\
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     word_bignumProof_code_rel (xx4,xx5) (wl_state_code t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL (\(n,x). lookup n (wl_state_code (t:(A,C,FFI)wl_state)) = SOME x)
                  (generated_bignum_stubs Bignum_location:(num#num#(A)wl_prog)list)`
    MP_TAC THENL
   [MP4_X_ASM "data_to_word_gcProof_state_rel"
      (MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm]) THEN
    REWRITE_TAC[data_to_word_gcProof_code_rel_def; data_to_word_stubs_def; ALL_APPEND] THEN
    MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[generated_bignum_stubs_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALL; ALL_MAP; GSYM ALL_MEM; o_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[word_bignumProof_code_rel_def; SND] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `prog:(A)mini,(n:num),(p2:(A)wl_prog)`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Bignum_location`; `2`; `1`; `Bignum_location + 1`;
                 `mc_iop_code:(A)mini`; `xx1:(A)wl_prog`; `xx2:num`; `xx3:num`;
                 `(xx4:num),(xx5:((A)mini#num#(A)wl_prog)list)`] compile_NIL_IMP) THEN
  ASM_REWRITE_TAC[SND] THEN
  DISCH_THEN(MP_TAC o SPECL [`prog:(A)mini`; `n:num`; `p2:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 971 *)
let TWO_LESS_MustTerminate_limit = prove
 (`2 < MustTerminate_limit (:A) /\ ~(MustTerminate_limit (:A) <= 1)`,
  REWRITE_TAC[MustTerminate_limit_def] THEN
  MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN ARITH_TAC);;

let _ = cake_add_simps [TWO_LESS_MustTerminate_limit];;

(* HOL4 line 980 *)
let data_to_word_bignumProof_Arith_location_def = cake_def
  `Arith_location index =
     if index = 0 then Add_location else
     if index = 1 then Sub_location else
     if index = 4 then Mul_location else
     if index = 5 then Div_location else
     if index = 6 then Mod_location else ARB`;;

(* HOL4 line 989 *)
let push_env_code = prove
 (`!y (t:(A,C,FFI)wl_state).
     wl_state_code (wl_push_env y NONE t) = wl_state_code t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `env_to_list (SND (y:(A word_loc)spt#(A word_loc)spt))
                        (wl_state_permute (t:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 995 *)
let data_to_word_bignumProof_Arith_code_def = cake_def
  `Arith_code index =
     wl_Seq (wl_Assign 6 (wl_Const (word (4 * index))))
       (wl_Call NONE (SOME AnyArith_location) [0; 2; 4; 6] NONE):(A)wl_prog`;;

(* HOL4 line 1001 *)
let lookup_Arith_location = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs index i1 i2 r.
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\
     data_to_word_bignumProof_int_op index i1 i2 = SOME r ==>
     lookup (Arith_location index) (wl_state_code t) = SOME (3,Arith_code index)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP lookup_RefByte_location) THEN
  UNDISCH_TAC `data_to_word_bignumProof_int_op index i1 i2 = SOME (r:int)` THEN
  REWRITE_TAC[data_to_word_bignumProof_int_op_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[data_to_word_bignumProof_Arith_location_def;
                  data_to_word_bignumProof_Arith_code_def; ARITH_EQ] THEN
  REWRITE_TAC[data_to_word_Add_code_def; data_to_word_Sub_code_def;
              data_to_word_Mul_code_def; data_to_word_Div_code_def;
              data_to_word_Mod_code_def] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1010 *)
let data_to_word_bignumProof_Replicate_code_thm = prove
 (`!n a (r:(A,C,FFI)wl_state) m1 a1 a2 a3 a4 a5 v l1 l2 ret_val.
     lookup Replicate_location (wl_state_code r) = SOME (5,Replicate_code) /\
     data_to_word_memoryProof_store_list (word_add a bytes_in_word) (REPLICATE n v)
       (wl_state_memory r) (wl_state_mdomain r) = SOME m1 /\
     wl_get_var a1 r = SOME (wl_Loc l1 l2) /\
     wl_get_var a2 r = SOME (wl_Word a) /\
     wl_get_var a3 r = SOME v /\
     wl_get_var a4 r = SOME (wl_Word (word (4 * n))) /\
     wl_get_var a5 r = SOME ret_val /\
     4 * n < dimword (:A) /\
     n < wl_state_clock r ==>
     ?m.
       wl_evaluate (wl_Call NONE (SOME Replicate_location) [a1;a2;a3;a4;a5] NONE,r) =
         (SOME (wl_Result (wl_Loc l1 l2) [ret_val]),
          wl_state_memory_fupd (K m1)
            (wl_state_clock_fupd (K ((wl_state_clock r - n) - 1))
               (wl_state_locals_fupd (K LN)
                  (wl_state_locals_size_fupd (K (SOME 0))
                     (wl_state_stack_max_fupd (K m) r))))) /\
       option_le m
         (OPTION_MAP2 MAX (wl_state_stack_max r)
            (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack r))
               (lookup Replicate_location (wl_state_stack_size r))))`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WBIGPAUX_ev_Call] THEN ASM_REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_Replicate_code_def] THEN
  (SUBGOAL_THEN `~(wl_state_clock (r:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC]) THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[wl_call_env_def; wl_dec_clock_def] THEN
    BIGPAUX_FROMLIST2_TAC THEN SIMP (data_to_word_list_Seq_def :: BIGPAUX_EV_THMS) THEN
    UNDISCH_TAC `data_to_word_memoryProof_store_list (word_add a bytes_in_word)
      (REPLICATE 0 (v:A word_loc)) (wl_state_memory (r:(A,C,FFI)wl_state))
      (wl_state_mdomain r) = SOME m1` THEN
    REWRITE_TAC[REPLICATE; data_to_word_memoryProof_store_list_def; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `OPTION_MAP2 MAX (wl_state_stack_max (r:(A,C,FFI)wl_state))
        (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack r))
        (lookup Replicate_location (wl_state_stack_size r)))` THEN
    REWRITE_TAC[option_le_refl; wl_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(4 + 4 * n) MOD dimword(:A) = 4 + 4 * n` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `data_to_word_memoryProof_store_list (word_add a bytes_in_word)
      (REPLICATE (SUC n) (v:A word_loc)) (wl_state_memory (r:(A,C,FFI)wl_state))
      (wl_state_mdomain r) = SOME m1` THEN
  REWRITE_TAC[REPLICATE; data_to_word_memoryProof_store_list_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def] THEN
  BIGPAUX_FROMLIST2_TAC THEN SIMP (data_to_word_list_Seq_def :: BIGPAUX_EV_THMS) THEN
  BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (wl_Call NONE (SOME Replicate_location) [0; 2; 4; 6; 8] NONE,
                  t3:(A,C,FFI)wl_state)` `t3:(A,C,FFI)wl_state` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add a bytes_in_word:A word`; `t3:(A,C,FFI)wl_state`;
     `m1:A word->A word_loc`; `0`; `2`; `4`; `6`; `8`; `v:A word_loc`; `l1:num`;
     `l2:num`; `ret_val:A word_loc`] o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t3" THEN SIMP[wl_get_var_def; lookup_insert] THEN
    REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
  EXISTS_TAC `m:num option` THEN EXPAND_TAC "t3" THEN
  SIMP[wl_state_component_equality; OPTION_MAP2_MAX_CANCEL] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "option_le" (concl th))) THEN
  EXPAND_TAC "t3" THEN SIMP[OPTION_MAP2_MAX_CANCEL]);;

let BIGPAUX_fromList_one = prove
 (`fromList [one] = LS one`,
  REWRITE_TAC[fromList_def; FOLDL] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[insert_def] THEN REWRITE_TAC[]);;

(* HOL4 line 1057 (the unused bound variables a1 a5 var are left out) *)
let data_to_word_bignumProof_Replicate_code_alt_thm = prove
 (`!n a (r:(A,C,FFI)wl_state) m1 a2 a3 a4 v ret_val l1 l2.
     lookup Replicate_location (wl_state_code r) = SOME (5,Replicate_code) /\
     data_to_word_memoryProof_store_list (word_add a bytes_in_word) (REPLICATE n v)
       (wl_state_memory r) (wl_state_mdomain r) = SOME m1 /\
     wl_get_var a2 r = SOME (wl_Word a) /\
     wl_get_var a3 r = SOME v /\
     wl_get_var a4 r = SOME (wl_Word (word (4 * n))) /\
     wl_get_var 0 r = SOME ret_val /\
     4 * n < dimword (:A) /\
     n < wl_state_clock r ==>
     ?max.
       wl_evaluate (wl_Call (SOME ([0],(fromList [one],LN),wl_Skip,l1,l2))
                      (SOME Replicate_location) [a2;a3;a4;0] NONE,r) =
       (NONE,
        wl_state_memory_fupd (K m1)
          (wl_state_clock_fupd (K ((wl_state_clock r - n) - 1))
             (wl_state_locals_fupd (K (insert 0 ret_val LN))
                (wl_state_stack_max_fupd (K max)
                   (wl_state_permute_fupd (K (\n. wl_state_permute r (n + 1))) r)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(wl_state_clock (r:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WBIGPAUX_ev_Call] THEN ASM_REWRITE_TAC[wl_get_vars_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[BIGPAUX_fromList_one; domain_def; NOT_INSERT_EMPTY; ALL_DISTINCT; MEM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WBIGPAUX_cut_envs_ret
    (check ((=) `lookup 0 (wl_state_locals (r:(A,C,FFI)wl_state)) =
                                  SOME (ret_val:(A)word_loc)` o concl) th)]) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_Replicate_code_def] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)
    (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[push_env_insert_0; wl_call_env_def; wl_dec_clock_def] THEN
  BIGPAUX_FROMLIST2_TAC THENL
   [SIMP (data_to_word_list_Seq_def :: BIGPAUX_EV_THMS) THEN
    SIMP[wl_pop_env_def; wl_set_vars_def; alist_insert_def; fromAList_def; union_LN;
         domain_insert; domain_def; insert_shadow] THEN
    UNDISCH_TAC `data_to_word_memoryProof_store_list (word_add a bytes_in_word)
        (REPLICATE 0 (v:A word_loc)) (wl_state_memory (r:(A,C,FFI)wl_state))
        (wl_state_mdomain r) = SOME m1` THEN
    REWRITE_TAC[REPLICATE; data_to_word_memoryProof_store_list_def; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(4 + 4 * k) MOD dimword(:A) = 4 + 4 * k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `data_to_word_memoryProof_store_list (word_add a bytes_in_word)
      (REPLICATE (SUC k) (v:A word_loc)) (wl_state_memory (r:(A,C,FFI)wl_state))
      (wl_state_mdomain r) = SOME m1` THEN
  REWRITE_TAC[REPLICATE; data_to_word_memoryProof_store_list_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  SIMP (data_to_word_list_Seq_def :: BIGPAUX_EV_THMS) THEN
  BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (wl_Call NONE (SOME Replicate_location) [0; 2; 4; 6; 8] NONE,
                  t3:(A,C,FFI)wl_state)` `t3:(A,C,FFI)wl_state` THEN
  MP_TAC(SPECL [`k:num`; `word_add a bytes_in_word:A word`; `t3:(A,C,FFI)wl_state`;
     `m1:A word->A word_loc`; `0`; `2`; `4`; `6`; `8`; `v:A word_loc`; `l1:num`;
     `l2:num`; `ret_val:A word_loc`] data_to_word_bignumProof_Replicate_code_thm) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t3" THEN SIMP[wl_get_var_def; lookup_insert] THEN
    REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
  EXPAND_TAC "t3" THEN
  SIMP[wl_pop_env_def; wl_set_vars_def; alist_insert_def; fromAList_def; union_LN;
       domain_insert; domain_def; insert_shadow] THEN
  EXISTS_TAC `m:num option` THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
  ARITH_TAC);;

(* HOL4 line 1132 *)
let bignum_digits_LENGTH_n2mw = prove
 (`good_dimindex (:A) ==>
   !n. bignum_digits (dimindex (:A) = 64) n = LENGTH ((n2mw n):(A word)list)`,
  DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP (if dimindex(:A) = 64 then 64 else 32) = dimword(:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def]) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC (INST_TYPE [`:A`,`:N`] n2mw_ind) THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[n2mw_def; bignum_digits_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

(* HOL4 line 1145: val s = s:('c,'ffi)dataSem$state *)

(* ------------------------------------------------------------------------- *)
(* Helpers for AnyArith_thm (BIGPAUX_ names)                                 *)
(* ------------------------------------------------------------------------- *)

let BIGPAUX_cut_env_3 = prove
 (`!(env:A spt) x0 x1 x2.
     lookup 0 env = SOME x0 /\ lookup 1 env = SOME x1 /\ lookup 2 env = SOME x2 ==>
     data_cut_env (fromList [one;one;one]) env = SOME (fromList [x0;x1;x2])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_cut_env_def; domain_fromList; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `pred_set_count 3 SUBSET domain (env:A spt)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SUBSET; IN_COUNT; domain_lookup] THEN X_GEN_TAC `n:num` THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (ARITH_RULE
      `n < 3 ==> n = 0 \/ n = 1 \/ n = 2`)) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[option_INJ] THEN
  MP_TAC(ISPECL [`mk_wf (sptree_inter (env:A spt) (fromList [one;one;one]))`;
                 `fromList [x0;x1;x2:A]`] spt_eq_thm) THEN
  REWRITE_TAC[wf_mk_wf; wf_fromList] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_fromList; IN_COUNT; LENGTH;
              lookup_fromList] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (ARITH_RULE
      `n < 3 ==> n = 0 \/ n = 1 \/ n = 2`)) THEN
  ASM_REWRITE_TAC[EL; HD; TL; num_CONV `2`; num_CONV `1`]);;

(* opening existential heap parts in a separation assertion *)
let BIGPAUX_word_list_exists_STAR = prove
 (`!(a:A word) n (R:((A word#B)->bool)->bool) s.
     (word_list_exists a n STAR R) s <=>
     ?xs. LENGTH xs = n /\ (misc_word_list a xs STAR R) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_list_exists_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  SUBGOAL_THEN `!(p:((A word#B)->bool)->bool) q r. (p STAR q) STAR r = q STAR (p STAR r)`
    (fun th -> REWRITE_TAC[th; cond_STAR]) THEN
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

let BIGPAUX_heap_expand_STAR = prove
 (`!limit (other:A word) c R s.
     ~(limit = 0) /\ (word_heap other (heap_expand limit) c STAR R) s ==>
     ?w. (set_sep_one (other,w) STAR
          (word_heap (word_add other bytes_in_word) (heap_expand (limit - 1)) c STAR R)) s`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC
   `(word_heap (other:A word) (heap_expand limit) c STAR R) (s:(A word#A word_loc)->bool)` THEN
  ASM_SIMP_TAC[word_heap_non_empty_limit; SEP_CLAUSES; SEP_EXISTS_THM; STAR_ASSOC]);;

(* the heap around its free space, opened up: a word for one payload, the   *)
(* output array, the rest of the free space, and the first word of the     *)
(* other heap                                                               *)
let BIGPAUX_word_list_exists_3 = prove
 (`!(a:A word) n k.
     word_list_exists a ((n + k) + 1):((A word#B)->bool)->bool =
     word_list_exists a 1 STAR
     word_list_exists (word_add a (word_mul bytes_in_word (word 1))) n STAR
     word_list_exists (word_add a (word_mul bytes_in_word (word (1 + n)))) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `(n + k) + 1 = (1 + n) + k`] THEN
  GEN_REWRITE_TAC LAND_CONV [data_to_word_memoryProof_word_list_exists_ADD] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [data_to_word_memoryProof_word_list_exists_ADD] THEN
  REWRITE_TAC[STAR_ASSOC]);;

let BIGPAUX_heap_decomp = prove
 (`!(curr:A word) ha n k hb other limit c m dm.
     (word_heap curr (APPEND ha (CONS (Unused (n + k)) hb)) c STAR
      word_heap other (heap_expand limit) c) (fun2set (m,dm)) /\ ~(limit = 0) ==>
     ?x1 xs wo.
       LENGTH xs = n /\
       (set_sep_one (word_add curr (word_mul bytes_in_word (word (heap_length ha))),x1) STAR
        misc_word_list (word_add (word_add curr (word_mul bytes_in_word
          (word (heap_length ha)))) (word_mul bytes_in_word (word 1))) xs STAR
        set_sep_one (other,wo) STAR
        word_heap curr ha c STAR
        word_list_exists (word_add (word_add curr (word_mul bytes_in_word
          (word (heap_length ha)))) (word_mul bytes_in_word (word (1 + n)))) k STAR
        word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
          (word_mul bytes_in_word (word ((n + k) + 1)))) hb c STAR
        word_heap (word_add other bytes_in_word) (heap_expand (limit - 1)) c)
       (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def; el_length_def] THEN
  REWRITE_TAC[BIGPAUX_word_list_exists_3] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BIGPAUX_heap_expand_STAR o CONJ (ASSUME `~(limit = 0)`) o
    MP4AUX_STAR_FOCUS (fun l -> mp4_is_app "word_heap" l &&
       can (find_term (fun t -> is_comb t && is_const (rator t) &&
                                fst (dest_const (rator t)) = "heap_expand")) l)) THEN
  DISCH_THEN(X_CHOOSE_THEN `wo:A word_loc` (fun th ->
    MP_TAC(MP4AUX_STAR_FOCUS (fun l -> mp4_is_app "word_list_exists" l &&
       rand l = `1`) th))) THEN
  REWRITE_TAC[BIGPAUX_word_list_exists_STAR; LENGTH_EQ_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1s:(A word_loc)list` (fun th ->
    MP_TAC (CONJUNCT2 th) THEN
    X_CHOOSE_THEN `x1:A word_loc` SUBST1_TAC (CONJUNCT1 th))) THEN
  REWRITE_TAC[misc_word_list_def; SEP_CLAUSES] THEN
  DISCH_THEN(fun th -> MP_TAC(MP4AUX_STAR_FOCUS (fun l -> mp4_is_app "word_list_exists" l &&
       rand l = `n:num`) th)) THEN
  REWRITE_TAC[BIGPAUX_word_list_exists_STAR] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x1:A word_loc`; `xs:(A word_loc)list`; `wo:A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN MP4AUX_SEP_AC_TAC);;

let BIGPAUX_MUL_1 = prove
 (`!x:A word. word_mul x (word 1) = x`,
  REWRITE_TAC[WORD_MULT_CLAUSES]);;

(* the assumptions of the goal whose conclusions are the given terms *)
let BIGPAUX_ASMS (tms:term list) ((asl,w):goal) : thm list =
  map (fun t -> try snd (find (fun (_,th) -> aconv (concl th) t) asl)
                with Failure _ -> failwith ("BIGPAUX_ASMS: " ^ string_of_term t)) tms;;

let BIGPAUX_ASM_REWRITE_TAC (tms:term list) (thl:thm list) : tactic = fun g ->
  REWRITE_TAC (BIGPAUX_ASMS tms g @ thl) g;;

(* rewrite with the assumptions whose conclusions satisfy p *)
let BIGPAUX_ASM_PRED_REWRITE_TAC (p:term->bool) (thl:thm list) : tactic = fun (asl,w as g) ->
  REWRITE_TAC (map snd (filter (fun (_,th) -> p (concl th)) asl) @ thl) g;;

(* delete the assumptions with the given conclusions *)
let BIGPAUX_DEL_ASMS (tms:term list) : tactic =
  MAP_EVERY (fun t -> FIRST_X_ASSUM(K ALL_TAC o check (fun th -> aconv (concl th) t))) tms;;

(* goal ?rest. P = L STAR rest, with the STAR leaves of L among those of P *)
let BIGPAUX_STAR_EXISTS_EQ_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let p,q = dest_eq bod in
  let l = rand(rator q) in
  let lleaves = mp4_star_leaves l in
  let pleaves = mp4_star_leaves p in
  let rest = itlist (fun x acc -> mp4_remove_first (fun y -> aconv x y) acc)
               lleaves pleaves in
  let r = mp4_list_mk_star rest in
  (EXISTS_TAC r THEN ACCEPT_TAC (MP4AUX_STAR_AC_EQ p (mp4_mk_star l r))) g;;

let BIGPAUX_word_heap_Bignum = prove
 (`!heap ptr i (curr:A word) c.
     heap_lookup ptr heap = SOME (Bignum i) ==>
     ?rest. word_heap curr heap c =
            misc_word_list
              (word_add (word_add curr (word_mul bytes_in_word (word ptr))) bytes_in_word)
              (MAP wl_Word (SND (i2mw i:bool#(A word)list))) STAR rest`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN
    `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; data_to_word_memoryProof_Bignum_def] THEN
  MP_TAC(ISPEC `i2mw i:bool#(A word)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:bool` (X_CHOOSE_THEN `pl:(A word)list` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[word_el_def; word_payload_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[misc_word_list_def; SND] THEN
  BIGPAUX_STAR_EXISTS_EQ_TAC);;

let BIGPAUX_AA_SIZES = prove
 (`!il jl. good_dimindex(:A) /\ il < dimword (:A) DIV 16 /\ jl < dimword (:A) DIV 16 ==>
     3 < dimindex(:A) /\ il + jl < il + jl + 1 /\ il + jl + 1 < dimword (:A) DIV 2 /\
     2 * il + 1 < dimword (:A) /\ 2 * jl + 1 < dimword (:A) /\
     4 * (il + jl + 1) < dimword (:A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[dimword_def] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[dimword_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let BIGPAUX_USHR_4 = prove
 (`!k. 4 * k < dimword(:A) ==> word_ushr (word (4 * k):A word) 2 = word k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `k < dimword(:A)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ARITH_RULE `4 * k = k * 4`; DIV_MULT; ARITH_EQ]);;

let BIGPAUX_USHR_4_SMALL = prove
 (`!k. good_dimindex(:A) /\ k < 7 ==> word_ushr (word (4 * k):A word) 2 = word k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BIGPAUX_USHR_4 THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def]) THEN
  ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let BIGPAUX_int_op_iop = prove
 (`!op_index i j v. data_to_word_bignumProof_int_op op_index i j = SOME v ==>
     ~(get_iop op_index = multiword_Lt) /\ ~(get_iop op_index = Eq) /\
     ~(get_iop op_index = multiword_Dec) /\
     (get_iop op_index = multiword_Div \/ get_iop op_index = multiword_Mod ==> ~(j = &0)) /\
     multiword_int_op (get_iop op_index) i j = v /\
     op_index < 7 /\
     (good_dimindex(:A) ==>
      word_ushr (word (4 * op_index)) 2 = int_op_rep (get_iop op_index):A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_bignumProof_int_op_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[get_iop_def] THEN
  ASM_SIMP_TAC[BIGPAUX_USHR_4_SMALL; ARITH] THEN
  REWRITE_TAC[int_op_def; int_op_rep_def; distinctness "mw_op"]);;

let BIGPAUX_div_max_bound = prove
 (`!(xs:(A word)list) (ys:(A word)list) il jl.
     good_dimindex(:A) /\ LENGTH xs = il /\ LENGTH ys = jl /\
     il < dimword (:A) DIV 16 /\ jl < dimword (:A) DIV 16 ==>
     mc_div_max xs ys (REPLICATE (il + jl + 1) (word 0:A word)) +
     2 * LENGTH (REPLICATE (il + jl + 1) (word 0:A word)) + 2 <=
     (((MustTerminate_limit (:A) - 2) - (il + jl + 1)) - 1) - 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mc_div_max_def; LENGTH_REPLICATE] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `k:num` o MATCH_MP MustTerminate_limit_eq) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `il < dimword(:A) /\ jl < dimword(:A) /\ dimindex(:A) < dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[dimindex_lt_dimword] THEN
    MP_TAC(SPECL [`dimword(:A)`; `16`] DIV_LE) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `il * jl <= dimword(:A) * dimword(:A) /\ il * dimword(:A) <= dimword(:A) * dimword(:A)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ASM_ARITH_TAC);;

let BIGPAUX_word_ml_inv_Bignum = prove
 (`!heap be a sp sp1 gens limit ts c refs i (w:A word) vars.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (CONS (data_Number i,wl_Word w) vars) /\
     ~small_int (:A) i ==>
     ?ptr. heap_lookup ptr heap = SOME (Bignum i) /\
           w = get_addr c ptr (wl_Word (word 0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def; MAP] THEN
  REWRITE_TAC[LIST_REL_CONS2; LIST_REL_CONS1] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "hs")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONJ_ASSOC]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC o check (fun th ->
    is_conj (concl th) && is_eq (lhand (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "v_inv" (concl th))) THEN
  ASM_REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    mp4_is_app "Pointer" (rhs (concl th)))) THEN
  EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    mp4_is_app "word_addr" (lhs (concl th)))) THEN
  REWRITE_TAC[word_addr_def; injectivity "word_loc"] THEN MESON_TAC[]);;

let BIGPAUX_SEP_EXISTS_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let ps,s = dest_comb bod in
  let p = rand(rator ps) in
  let pleaves = mp4_star_leaves p in
  let th = snd(find (fun (_,th) -> let c = concl th in
              is_comb c && aconv (rand c) s &&
              (let qleaves = mp4_star_leaves (rator c) in
               forall (fun l -> exists (aconv l) qleaves) pleaves)) asl) in
  let th' = MP4AUX_STAR_FOCUS_LIST (map (fun l -> aconv l) pleaves) th in
  let rest = rand(rator(concl th')) in
  (EXISTS_TAC rest THEN ACCEPT_TAC th') g;;

let BIGPAUX_Bignum_NOT_Unused = prove
 (`!i N. ~(Unused N = (Bignum i:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)heap_element))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_memoryProof_Bignum_def] THEN
  MP_TAC(ISPEC `i2mw i:bool#(A word)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:bool` (X_CHOOSE_THEN `pl:(A word)list` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REWRITE_TAC[distinctness "heap_element"]);;

let BIGPAUX_bignum_payload = prove
 (`!c heap ptr i (curr:A word) ha hb N frame m dm.
     heap = APPEND ha (CONS (Unused N) hb) /\
     heap_lookup ptr heap = SOME (Bignum i) /\
     (word_heap curr ha c STAR
      word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
                          (word_mul bytes_in_word (word (N + 1)))) hb c STAR frame)
       (fun2set (m,dm)) ==>
     ?rest. (misc_word_list
               (word_add (word_add curr (word_mul bytes_in_word (word ptr))) bytes_in_word)
               (MAP wl_Word (SND (i2mw i:bool#(A word)list))) STAR frame STAR rest)
            (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)))) THEN
  ASM_CASES_TAC `ptr < heap_length
    (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THENL
   [FIRST_X_ASSUM(fun lt -> FIRST_X_ASSUM(MP_TAC o
      REWRITE_RULE[MATCH_MP heap_lookup_APPEND2 lt] o check (fun th ->
      mp4_is_app "heap_lookup" (lhand (concl th))))) THEN
    DISCH_THEN(X_CHOOSE_TAC `rest0:(A word#(A)word_loc->bool)->bool` o
      SPECL [`curr:A word`; `c:data_to_word_config`] o MATCH_MP BIGPAUX_word_heap_Bignum) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "fun2set" (rand (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN BIGPAUX_SEP_EXISTS_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "heap_lookup" (lhand (concl th)))) THEN
  ASM_SIMP_TAC[heap_lookup_APPEND1; GSYM NOT_LT] THEN
  REWRITE_TAC[heap_lookup_def; el_length_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; BIGPAUX_Bignum_NOT_Unused] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(X_CHOOSE_TAC `rest0:(A word#(A)word_loc->bool)->bool` o
    SPECL [`word_add (word_add curr (word_mul bytes_in_word (word (heap_length
      (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
      (word_mul bytes_in_word (word (N + 1))):A word`; `c:data_to_word_config`] o
    MATCH_MP BIGPAUX_word_heap_Bignum) THEN
  SUBGOAL_THEN `word_add (word_add (word_add (word_add curr (word_mul bytes_in_word
      (word (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
      (word_mul bytes_in_word (word (N + 1))))
      (word_mul bytes_in_word (word ((ptr - heap_length ha) - (N + 1))))) bytes_in_word =
    word_add (word_add curr (word_mul bytes_in_word (word ptr))) (bytes_in_word:A word)`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `ptr = heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) + (N + 1) + ((ptr - heap_length ha) - (N + 1))`
      (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "fun2set" (rand (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN BIGPAUX_SEP_EXISTS_TAC);;

let BIGPAUX_bignum_arg_payload = prove
 (`!c heap be a sp sp1 gens limit ts refs (s0:(C,FFI)data_state) (t:(A,C,FFI)wl_state)
    envs n i w x st curr ha hb N frame m dm.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env (data_state_locals s0)
          (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s0)))))
          envs) /\
     data_get_var n (data_state_locals s0) = SOME (data_Number i) /\
     wl_get_var (adjust_var n) t = SOME (wl_Word w) /\
     ~small_int (:A) i /\ good_dimindex(:A) /\
     heap = APPEND ha (CONS (Unused N) hb) /\
     heap_length heap <= dimword (:A) DIV 2 EXP shift_length c /\
     FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
     get_real_addr c st w = SOME x /\
     (word_heap curr ha c STAR
      word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
                          (word_mul bytes_in_word (word (N + 1)))) hb c STAR frame)
       (fun2set (m,dm)) ==>
     ?rest. (misc_word_list (word_add x bytes_in_word)
               (MAP wl_Word (SND (i2mw i:bool#(A word)list))) STAR frame STAR rest)
            (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP word_ml_inv_get_var_IMP o
    CONJ (ASSUME `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env (data_state_locals (s0:(C,FFI)data_state))
          (toAList (sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
             (adjust_set (data_state_locals s0)))))
          envs)`) o
    CONJ (ASSUME `data_get_var n (data_state_locals (s0:(C,FFI)data_state)) =
                  SOME (data_Number i)`) o
    check (fun th -> mp4_is_app "wl_get_var" (lhand (concl th)))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BIGPAUX_word_ml_inv_Bignum o C CONJ
    (ASSUME `~small_int (:A) i`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x = word_add curr (word_mul bytes_in_word (word ptr)):A word` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `c:data_to_word_config`; `ptr:num`; `Bignum i:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`;
      `st:(store_name,(A)word_loc)fmap`; `curr:A word`; `wl_Word (word 0):A word_loc`]
      get_real_addr_get_addr) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "w")) THEN
    ASM_REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_MUL_SYM; ALL_TAC] THEN
  MATCH_MP_TAC BIGPAUX_bignum_payload THEN
  MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `N:num`] THEN
  ASM_REWRITE_TAC[]);;

(* MP_TAC the conclusion of the assumption ante ==> concl, ante proved by *)
(* rewriting with the assumptions whose conclusions are parts             *)
let BIGPAUX_MP_ASM_TAC (ante:term) (parts:term list) : tactic = fun (asl,w as g) ->
  let th = try snd(find (fun (_,th) -> is_imp (concl th) && aconv (lhand (concl th)) ante) asl)
           with Failure _ -> failwith ("BIGPAUX_MP_ASM_TAC: " ^ string_of_term ante) in
  let pths = BIGPAUX_ASMS parts g in
  let ath = EQT_ELIM (REWRITE_CONV pths ante) in
  MP_TAC (MP th ath) g;;

(* the bignum case of an In array of array_rel: hv the integer, n its data  *)
(* variable, gv the theorem wl_get_var (adjust_var n) s9 = SOME (wl_Word w), *)
(* st the store of get_real_addr, cth FLOOKUP st CurrHeap = SOME curr, gra   *)
(* get_real_addr c st w = SOME x                                             *)
let BIGPAUX_ARR_BIG_TAC (hv:term) (n:term) (gv:thm) (cth:thm) (gra:thm) : tactic =
  fun (asl,w as g) ->
  let find_asm p = snd(find (fun (_,th) -> p (concl th)) asl) in
  let wml = REWRITE_RULE[GSYM APPEND_ASSOC]
    (find_asm (fun c -> mp4_is_app "word_ml_inv" c)) in
  let gv0 = find_asm (fun c -> is_eq c && mp4_is_app "data_get_var" (lhs c) &&
                        rand(rator(lhs c)) = n &&
                        free_in `s0:(C,FFI)data_state` c) in
  let nsmall = ASSUME (mk_neg (mk_comb (`small_int (:A)`, hv))) in
  let gd = find_asm ((=) `good_dimindex(:A)`) in
  let heapeq = find_asm (fun c -> is_eq c && is_var (lhs c) && fst(dest_var(lhs c)) = "heap") in
  let hlen = find_asm (fun c -> mp4_is_app "<=" c && mp4_is_app "heap_length" (lhand c) &&
                         is_var (rand (lhand c))) in
  let mth = find_asm (fun c -> mp4_is_app "fun2set" (rand c) &&
                         free_in `m2:A word->A word_loc` (rand c) &&
                         free_in `s9:(A,C,FFI)wl_state` (rand c)) in
  let isheap v l = mp4_is_app "word_heap" l && rand(rator l) = v in
  let ha = `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` in
  let hb = `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` in
  let fth = MP4AUX_STAR_FOCUS_LIST [isheap ha; isheap hb] mth in
  let ante = end_itlist CONJ [wml; gv0; gv; nsmall; gd; heapeq; hlen; cth; gra; fth] in
  (MP_TAC (MATCH_MP BIGPAUX_bignum_arg_payload ante) THEN
   DISCH_THEN(X_CHOOSE_TAC `rest0:(A word#(A)word_loc->bool)->bool`) THEN
   BIGPAUX_SEP_EXISTS_TAC) g;;

(* goal p s: the first leaf of p satisfying pr put in front *)
let BIGPAUX_GOAL_FOCUS_TAC (pr:term->bool) : tactic = fun (asl,w as g) ->
  let p,s = dest_comb w in
  let leaves = mp4_star_leaves p in
  let l = find pr leaves in
  let rest = mp4_remove_first (fun x -> x == l) leaves in
  let q = mp4_mk_star l (mp4_list_mk_star rest) in
  CONV_TAC (RATOR_CONV (K (MP4AUX_STAR_AC_EQ p q))) g;;

let BIGPAUX_heap_recomp = prove
 (`!(curr:A word) ha n k hb other limit c x1 xs wo m dm.
     LENGTH xs = n /\ ~(limit = 0) /\
     (set_sep_one (word_add curr (word_mul bytes_in_word (word (heap_length ha))),x1) STAR
      misc_word_list (word_add (word_add curr (word_mul bytes_in_word
        (word (heap_length ha)))) bytes_in_word) xs STAR
      set_sep_one (other,wo) STAR
      word_heap curr ha c STAR
      word_list_exists (word_add (word_add curr (word_mul bytes_in_word
        (word (heap_length ha)))) (word_mul bytes_in_word (word (1 + n)))) k STAR
      word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
        (word_mul bytes_in_word (word ((n + k) + 1)))) hb c STAR
      word_heap (word_add other bytes_in_word) (heap_expand (limit - 1)) c)
     (fun2set (m,dm)) ==>
     (word_heap curr (APPEND ha (CONS (Unused (n + k)) hb)) c STAR
      word_heap other (heap_expand limit) c) (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def; el_length_def] THEN
  REWRITE_TAC[BIGPAUX_word_list_exists_3; BIGPAUX_MUL_1] THEN
  ASM_SIMP_TAC[word_heap_non_empty_limit; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  EXISTS_TAC `wo:A word_loc` THEN
  BIGPAUX_GOAL_FOCUS_TAC (fun l -> mp4_is_app "word_list_exists" l && rand l = `1`) THEN
  REWRITE_TAC[BIGPAUX_word_list_exists_STAR] THEN
  EXISTS_TAC `[x1:A word_loc]` THEN REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  REWRITE_TAC[misc_word_list_def; SEP_CLAUSES] THEN
  BIGPAUX_GOAL_FOCUS_TAC (fun l -> mp4_is_app "word_list_exists" l && rand l = `n:num`) THEN
  REWRITE_TAC[BIGPAUX_word_list_exists_STAR] THEN
  EXISTS_TAC `xs:(A word_loc)list` THEN ASM_REWRITE_TAC[] THEN
  MP4AUX_SEP_AC_TAC);;

(* keep only the assumptions whose conclusions satisfy p *)
let BIGPAUX_KEEP_TAC (p:term->bool) : tactic = fun (asl,w) ->
  null_meta,[(filter (fun (_,th) -> p (concl th)) asl,w)],
  (fun i ths -> match ths with [th] -> th | _ -> failwith "BIGPAUX_KEEP_TAC");;

let BIGPAUX_mc_header_23 = prove
 (`!(x:bool#(A word)list). good_dimindex(:A) /\ 2 * LENGTH (SND x) + 1 < dimword (:A) ==>
     (mc_header x = word 2 <=> ?v1. x = (F,[v1])) /\
     (mc_header x = word 3 <=> ?v1. x = (T,[v1]))`,
  REWRITE_TAC[FORALL_PAIR_THM; SND; mc_header_def] THEN
  MAP_EVERY X_GEN_TAC [`sg:bool`; `xs:(A word)list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. n < dimword(:A) ==>
      (word_add (word (LENGTH (xs:(A word)list) * 2)) (if sg then word 1 else word 0) =
       (word n:A word) <=>
       LENGTH xs * 2 + (if sg then 1 else 0) = n)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `word_add (word (LENGTH (xs:(A word)list) * 2)) (if sg then word 1 else word 0) =
                  word (LENGTH xs * 2 + (if sg then 1 else 0)):A word` SUBST1_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[WORD_ADD; ADD_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword_def] THEN
    SUBGOAL_THEN `LENGTH (xs:(A word)list) * 2 + (if sg then 1 else 0) < dimword(:A)`
      ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 < dimword(:A) /\ 3 < dimword(:A)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[PAIR_EQ] THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM LENGTH_EQ_1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPEC `LENGTH (xs:(A word)list)` (ARITH_RULE `!n. n = 0 \/ n = 1 \/ 2 <= n`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let BIGPAUX_FLOOKUP_EQ_FDOM = prove
 (`!(f:(A,B)fmap) g x. FLOOKUP f x = FLOOKUP g x ==>
     (x IN FDOM f <=> x IN FDOM g) /\ (x IN FDOM f ==> FAPPLY f x = FAPPLY g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; option_DISTINCT]);;

let BIGPAUX_store_nonTemp = prove
 (`!(st:(store_name,A word_loc)fmap) st'.
     (!n. (!r. ~(n = Temp r)) ==> FLOOKUP st' n = FLOOKUP st n) ==>
     FLOOKUP st' CurrHeap = FLOOKUP st CurrHeap /\
     FLOOKUP st' OtherHeap = FLOOKUP st OtherHeap /\
     FLOOKUP st' NextFree = FLOOKUP st NextFree /\
     FLOOKUP st' TriggerGC = FLOOKUP st TriggerGC /\
     FLOOKUP st' EndOfHeap = FLOOKUP st EndOfHeap /\
     FLOOKUP st' HeapLength = FLOOKUP st HeapLength /\
     FLOOKUP st' Globals = FLOOKUP st Globals /\
     FLOOKUP st' GlobReal = FLOOKUP st GlobReal /\
     FLOOKUP st' GenStart = FLOOKUP st GenStart /\
     FLOOKUP st' CodeBuffer = FLOOKUP st CodeBuffer /\
     FLOOKUP st' CodeBufferEnd = FLOOKUP st CodeBufferEnd /\
     FLOOKUP st' BitmapBuffer = FLOOKUP st BitmapBuffer /\
     FLOOKUP st' BitmapBufferEnd = FLOOKUP st BitmapBufferEnd /\
     (Globals IN FDOM st' <=> Globals IN FDOM st) /\
     (Globals IN FDOM st ==> FAPPLY st' Globals = FAPPLY st Globals)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `FLOOKUP (st':(store_name,A word_loc)fmap) Globals = FLOOKUP st Globals`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[distinctness "store_name"]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BIGPAUX_FLOOKUP_EQ_FDOM) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_MESON_TAC[distinctness "store_name"]);;

let BIGPAUX_heap_in_memory_store_change = prove
 (`!heap a sp sp1 gens c (st:(store_name,A word_loc)fmap) st' m dm m' dm' limit curr other.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     (!n. (!r. ~(n = Temp r)) ==> FLOOKUP st' n = FLOOKUP st n) /\
     FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
     FLOOKUP st OtherHeap = SOME (wl_Word other) /\
     (word_heap curr heap c STAR word_heap other (heap_expand limit) c) (fun2set (m',dm')) ==>
     heap_in_memory_store heap a sp sp1 gens c st' m' dm' limit`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o MATCH_MP BIGPAUX_store_nonTemp) STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[heap_in_memory_store_def] THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `curr' = curr:A word /\ other' = other:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[option_INJ; injectivity "word_loc"]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN
  ASM_REWRITE_TAC[]);;

let BIGPAUX_stack_max_le = prove
 (`!(st:((A)stack_frame)list) lsz e sm0 big (smax:num option).
     option_le (OPTION_MAP2 MAX (OPTION_MAP2 MAX sm0
                  (wl_stack_size (CONS (StackFrame lsz e [] NONE) st)))
                (OPTION_MAP2 (+) (wl_stack_size (CONS (StackFrame lsz e [] NONE) st)) big))
               smax ==>
     option_le (OPTION_MAP2 (+) (wl_stack_size st) (SOME 0)) smax`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_stack_size_def; ITLIST; o_THM; stack_size_frame_def] THEN
  SPEC_TAC(`ITLIST (OPTION_MAP2 (+) o stack_size_frame) (st:((A)stack_frame)list) (SOME 1)`,
           `x:num option`) THEN
  GEN_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option")))
    [`x:num option`; `lsz:num option`; `sm0:num option`; `big:num option`; `smax:num option`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

(* goal R a1 .. an, th |- R b1 .. bn: the differing arguments are proved equal *)
(* by tac (as a conjunction), then th closes the goal                       *)
let BIGPAUX_ARGS_MATCH_TAC (tac:tactic) (th:thm) : tactic = fun (asl,w as g) ->
  let (_,args) = strip_comb w in
  let (_,args') = strip_comb (concl th) in
  let eqs = filter (fun e -> not (aconv (lhs e) (rhs e))) (map2 (curry mk_eq) args args') in
  if eqs = [] then ACCEPT_TAC th g else
  (SUBGOAL_THEN (list_mk_conj eqs) (fun eth -> REWRITE_TAC[eth] THEN ACCEPT_TAC th) THEN
   REPEAT CONJ_TAC THEN tac) g;;

let BIGPAUX_one_digit = prove
 (`!v (d:A word) sg. i2mw v = (sg,[d]) ==>
     (sg <=> v < &0) /\ &(val d) = abs v /\ ~(v = &0) /\ d = word (val d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[i2mw_def; PAIR_EQ; WORD_VAL] THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL; CONS_11; n2mw_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(num_of_int (abs v)) = abs v` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN REWRITE_TAC[INT_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `num_of_int (abs v) < dimword(:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      mp4_is_app "DIV" (lhs (concl th)))) THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] ZERO_LT_dimword) THEN
    SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < n ==> ~(n = 0)`]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    mp4_is_app "word" (lhs (concl th)))) THEN
  ASM_SIMP_TAC[VAL_WORD; GSYM dimword_def; MOD_LT] THEN
  UNDISCH_TAC `~(num_of_int (abs v) = 0)` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let BIGPAUX_DIMWORD_DIV8 = prove
 (`good_dimindex(:A) ==> 2 EXP (dimindex(:A) - 3) = dimword(:A) DIV 8`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGPAUX_digit_pos = prove
 (`!v (d:A word). good_dimindex(:A) /\ i2mw v = (F,[d]) ==>
     (word_ushr d (dimindex(:A) - 3) = word 0 <=> small_int (:A) v) /\
     (small_int (:A) v ==> word_shl d 2 = Smallnum v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o MATCH_MP BIGPAUX_one_digit) THEN
  SUBGOAL_THEN `&0 < (v:int)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(v:int = &0)` THEN UNDISCH_TAC `~(v:int < &0)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:int) = &(val (d:A word))` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&(val (d:A word)) = abs (v:int)` THEN UNDISCH_TAC `&0 < (v:int)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BIGPAUX_DIMWORD_DIV8) THEN
  SUBGOAL_THEN `~(dimword(:A) DIV 8 = 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `small_int (:A) (&(val (d:A word))) <=> val d < dimword(:A) DIV 8`
    SUBST1_TAC THENL
   [REWRITE_TAC[small_int_def; INT_OF_NUM_LT] THEN
    REWRITE_TAC[INT_ARITH `--(&n:int) <= &m`]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_0] THEN ASM_SIMP_TAC[DIV_EQ_0];
    DISCH_TAC THEN
    REWRITE_TAC[data_to_word_Smallnum_def; INT_LT; INT_OF_NUM_LT; LT; INT_OF_NUM_MUL;
                NUM_OF_INT_OF_NUM] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
    REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC]);;

let BIGPAUX_digit_neg = prove
 (`!v (d:A word). good_dimindex(:A) /\ i2mw v = (T,[d]) ==>
     (word_ushr (word_sub d (word 1)) (dimindex(:A) - 3) = word 0 <=> small_int (:A) v) /\
     (small_int (:A) v ==> word_sub (word 0) (word_shl d 2) = Smallnum v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o MATCH_MP BIGPAUX_one_digit) THEN
  SUBGOAL_THEN `(v:int) = --(&(val (d:A word))) /\ 1 <= val d` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `&(val (d:A word)) = abs (v:int)` THEN UNDISCH_TAC `(v:int) < &0` THEN
    INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "v")) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BIGPAUX_DIMWORD_DIV8) THEN
  SUBGOAL_THEN `~(dimword(:A) DIV 8 = 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `small_int (:A) (--(&(val (d:A word)))) <=> val d <= dimword(:A) DIV 8`
    SUBST1_TAC THENL
   [REWRITE_TAC[small_int_def; INT_LE_NEG2; INT_OF_NUM_LE] THEN
    MATCH_MP_TAC(TAUT `b ==> (a /\ b <=> a)`) THEN
    UNDISCH_TAC `~(dimword(:A) DIV 8 = 0)` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub d (word 1) = word (val (d:A word) - 1):A word` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB; WORD_VAL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_0] THEN
    REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
    MP_TAC(ISPEC `d:A word` VAL_BOUND) THEN REWRITE_TAC[GSYM dimword_def] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < d ==> x - 1 < d`; DIV_EQ_0] THEN
    UNDISCH_TAC `1 <= val (d:A word)` THEN ARITH_TAC;
    DISCH_TAC THEN
    REWRITE_TAC[data_to_word_Smallnum_def] THEN
    SUBGOAL_THEN `--(&(val (d:A word))):int < &0` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `1 <= val (d:A word)` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_SUB_LZERO; INT_NEG_NEG; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
    REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC]);;

let BIGPAUX_SHIFT3_FACTS = prove
 (`good_dimindex(:A) ==>
     val (word (dimindex(:A) - 3):A word) = dimindex(:A) - 3 /\
     ~(dimindex(:A) - 3 = 0) /\ ~(dimindex(:A) <= dimindex(:A) - 3)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD; dimword_def] THEN CONV_TAC NUM_REDUCE_CONV);;

(* the end of AnyArith_thm for a result rv: the witnesses q r new_c taken  *)
(* from the evaluation, the state relation from the zero-result claim      *)
(* (the assumption about t2) transformed by thf                            *)
let BIGPAUX_RESULT_FINISH_TAC (rv:term) (thf:thm->thm) : tactic =
  W(fun (asl,w) -> let (_,bod) = strip_exists w in
     let (eqs,_) = dest_conj bod in
     let (e1,e2) = dest_conj eqs in
     MAP_EVERY EXISTS_TAC [lhs e1; lhs e2; `wl_state_clock (t2:(A,C,FFI)wl_state)`]) THEN
  REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"] THEN
  EXISTS_TAC rv THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if mp4_is_app "data_to_word_gcProof_state_rel" (concl th) &&
      free_in `t2:(A,C,FFI)wl_state` (concl th)
    then BIGPAUX_ARGS_MATCH_TAC
      (TRY (EXPAND_TAC "t7") THEN TRY (EXPAND_TAC "t6") THEN TRY (EXPAND_TAC "t5") THEN
       REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds;
         wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM])
      (thf (MATCH_MP state_rel_with_clock_0 th)) else NO_TAC);;

let BIGPAUX_WORD_3_NE_2 = prove
 (`good_dimindex(:A) ==> ~(word 3 = word 2:A word)`,
  REWRITE_TAC[good_dimindex_def; GSYM VAL_EQ; VAL_WORD; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGPAUX_mc_header_bits = prove
 (`!(x:bool#(A word)list). 2 * LENGTH (SND x) + 1 < dimword(:A) ==>
     word_ushr (mc_header x) 1 = word (LENGTH (SND x)) /\
     word_and (mc_header x) (word 1) = b2w (FST x)`,
  REWRITE_TAC[FORALL_PAIR_THM; SND; FST; mc_header_def] THEN
  MAP_EVERY X_GEN_TAC [`sg:bool`; `xs:(A word)list`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `word_add (word (LENGTH (xs:(A word)list) * 2)) (if sg then word 1 else word 0) =
                word (LENGTH xs * 2 + (if sg then 1 else 0)):A word` SUBST1_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[WORD_ADD; ADD_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (xs:(A word)list) * 2 + (if sg then 1 else 0) < dimword(:A)`
    ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `2 * n + 1 < d ==> n < d`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1` THEN ARITH_TAC;
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC];
    REWRITE_TAC[WORD_AND_1; BIT_WORD] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] DIMINDEX_GE_1) THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> 1 <= n`; EXP; DIV_1] THEN
    BOOL_CASES_TAC `sg:bool` THEN
    REWRITE_TAC[b2w_def; ADD_CLAUSES; ODD_ADD; ODD_MULT; ARITH]]);;

let BIGPAUX_WORD_OR_SWAP = prove
 (`!(x:A word) y z. word_or x (word_or y z) = word_or y (word_or x z)`,
  CONV_TAC WORD_BITWISE_RULE);;

let BIGPAUX_HEADER_BITS = prove
 (`!(a:A word) s. word_or (word 15) (word_or a (word_shl (b2w s) 4)) =
     word_or a (word_or (word_shl (word_or (word_shl (b2w s) 2) (word 3)) 2) (word 3))`,
  GEN_TAC THEN GEN_TAC THEN CONV_TAC(LAND_CONV(REWR_CONV BIGPAUX_WORD_OR_SWAP)) THEN
  AP_TERM_TAC THEN
  BOOL_CASES_TAC `s:bool` THEN
  REWRITE_TAC[b2w_def; WORD_SHL_OR; WORD_SHL_COMPOSE; WORD_SHL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MP4AUX_WORD_BITS_TAC 5);;

let BIGPAUX_encode_bignum_header = prove
 (`!c s len. good_dimindex(:A) /\ data_to_word_config_len_size c + 7 < dimindex(:A) /\
     len < 2 EXP data_to_word_config_len_size c ==>
     encode_header c (val (word_or (word_shl (b2w s) 2) (word 3):A word)) len =
     SOME (make_header c (word_or (word_shl (b2w s) 2) (word 3)) len:A word)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[encode_header_def; WORD_VAL] THEN
  SUBGOAL_THEN `val (word_or (word_shl (b2w s) 2) (word 3):A word) <= 7` ASSUME_TAC THENL
   [BOOL_CASES_TAC `s:bool` THEN REWRITE_TAC[b2w_def; WORD_SHL_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THENL
     [SUBGOAL_THEN `word_or (word 4) (word 3):A word = word 7` SUBST1_TAC THENL
       [MP4AUX_WORD_BITS_TAC 3; ALL_TAC];
      SUBGOAL_THEN `word_or (word 0) (word 3):A word = word 3` SUBST1_TAC THENL
       [REWRITE_TAC[WORD_OR_0]; ALL_TAC]] THEN
    REWRITE_TAC[VAL_WORD] THEN
    MATCH_MP_TAC(ARITH_RULE `x <= n ==> x MOD m <= n`) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 <= dimindex(:A) - data_to_word_config_len_size c /\
                data_to_word_config_len_size c <= dimindex(:A) - 4` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP 6 <= 2 EXP ((dimindex(:A) - data_to_word_config_len_size c) - 2) /\
                2 EXP data_to_word_config_len_size c <= 2 EXP (dimindex(:A) - 4)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 < dimword(:A) DIV 16` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN ASM_ARITH_TAC);;

let BIGPAUX_store_list_header = prove
 (`!(a:A word) x hd ws frame m dm.
     (set_sep_one (a,x) STAR misc_word_list (word_add a bytes_in_word) ws STAR frame)
       (fun2set (m,dm)) ==>
     data_to_word_memoryProof_store_list a (CONS (wl_Word hd) ws) m dm =
       SOME ((a =+ wl_Word hd) m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_to_word_memoryProof_store_list_def] THEN
  MP4AUX_SEP_R_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC word_list_IMP_store_list THEN
  EXISTS_TAC `set_sep_one (a:A word,wl_Word hd:A word_loc) STAR frame` THEN
  FIRST_X_ASSUM(fun th -> if mp4_is_fun2set_asm (concl th) then
    MP_TAC (MP4AUX_SEP_WRITE `a:A word` `wl_Word hd:A word_loc` th) else NO_TAC) THEN
  DISCH_TAC THEN MP4AUX_SEP_AC_TAC);;

let BIGPAUX_I2MW_REWRITE_TAC (hv:term) : tactic =
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) =
     mk_comb(`i2mw:int->bool#(A word)list`, hv) then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[SND; MAP; misc_word_list_def; SEP_CLAUSES];;

let BIGPAUX_T2_STORE_TAC : tactic =
  let st = `wl_state_store (t2:(A,C,FFI)wl_state)` in
  BIGPAUX_ASM_PRED_REWRITE_TAC (fun c -> (is_eq c || is_iff c) &&
    can (find_term ((=) st)) (lhs c) && not (can (find_term ((=) st)) (rhs c))) [];;

let BIGPAUX_SMALL_I2MW_TAC : tactic =
  SUBGOAL_THEN `i2mw v = ((v < &0),[d1]):bool#(A word)list` ASSUME_TAC THENL
   [SUBGOAL_THEN `i2mw v = ((v < &0),[word (num_of_int (abs v))]:(A word)list)` ASSUME_TAC THENL
     [MATCH_MP_TAC BIGPAUX_i2mw_small THEN
      BIGPAUX_ASM_REWRITE_TAC [`small_int (:A) v`; `~(v:int = &0)`] []; ALL_TAC] THEN
    FIRST_ASSUM(let qtm = `SND (i2mw v:bool#(A word)list) = CONS d1 ds` in fun th -> if concl th = qtm then
      MP_TAC th else NO_TAC) THEN
    BIGPAUX_ASM_REWRITE_TAC [`i2mw v = ((v < &0),[word (num_of_int (abs v))]:(A word)list)`]
      [SND; CONS_11] THEN MESON_TAC[]; ALL_TAC];;

let BIGPAUX_SV_STEP_TAC = ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN
  BIGPAUX_EVAL_THMS_TAC [] [wl_mem_store_def; BIGPAUX_AND_NOT0] THEN
  TRY (CHANGED_TAC (ONCE_REWRITE_TAC[word_exp_set_var_ShiftVar_lemma]) THEN
       BIGPAUX_EVAL_THMS_TAC [] [wl_mem_store_def; BIGPAUX_AND_NOT0]);;

let BIGPAUX_mc_iop_inst (asl,w) =
  let mth = snd(find (fun (_,th) -> let c = concl th in
      mp4_is_app "fun2set" (rand c) &&
      free_in `m2:A word->A word_loc` (rand c)) asl) in
  let frame = rand (rator (concl mth)) in
  ISPECL [`i:int`; `j:int`; `2`; frame;
     `REPLICATE (LENGTH (xs:(A word_loc)list)) (word 0:A word)`; `t3:(A,C,FFI)wl_state`;
     `wl_Loc AnyArith_location 3:A word_loc`; `Bignum_location`;
     `wl_state_clock (t3:(A,C,FFI)wl_state)`; `get_iop op_index`; `p1:(A)wl_prog`;
     `ll:num`; `ii:num`; `(nn:num),(cs:((A)mini#num#(A)wl_prog)list)`] evaluate_mc_iop;;

(* an equation goal l = r from a chain of equational assumptions (each used in *)
(* either direction), by breadth first search; ASM_MESON_TAC[] took up to 6 s  *)
(* on such goals here                                                          *)
let BIGPAUX_EQ_CHAIN_TAC : tactic = fun (asl,w as gl) ->
  let l,r = dest_eq w in
  let eqs = mapfilter (fun (_,th) -> if is_eq (concl th) then th else failwith "") asl in
  let rec bfs frontier visited =
    match filter (fun (t,_) -> aconv t r) frontier with
      (_,th)::_ -> th
    | [] ->
      if frontier = [] then failwith "BIGPAUX_EQ_CHAIN_TAC" else
      let next = flat (map (fun (t,th) ->
          mapfilter (fun e -> let a,b = dest_eq (concl e) in
             if aconv a t && not (exists (aconv b) visited) then (b, TRANS th e)
             else if aconv b t && not (exists (aconv a) visited) then (a, TRANS th (SYM e))
             else failwith "") eqs) frontier) in
      let next = itlist (fun (t,th) acc -> if exists (fun (u,_) -> aconv t u) acc then acc
                                           else (t,th)::acc) next [] in
      bfs next (map fst next @ visited) in
  ACCEPT_TAC (bfs [l, REFL l] [l]) gl;;

(* the goal by rewriting with the negated equations among the assumptions,   *)
(* in both orientations (conditionals on n = Temp r under !r. ~(n = Temp r))  *)
let BIGPAUX_NEQ_REWRITE_TAC : tactic = fun (asl,w as gl) ->
  let neqs = filter (fun th -> let c = snd (strip_forall (concl th)) in
                       is_neg c && is_eq (rand c)) (map snd asl) in
  let syms = map (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)) neqs in
  (REWRITE_TAC (neqs @ syms) THEN NO_TAC) gl;;

let BIGPAUX_FAST_MESON_TAC : tactic =
  FIRST [BIGPAUX_EQ_CHAIN_TAC; BIGPAUX_NEQ_REWRITE_TAC; ASM_MESON_TAC[]];;

(* HOL4 line 1154 *)
let AnyArith_thm = prove
 (CASE_TERM
  `!op_index i j v (t:(A,C,FFI)wl_state) (s:(C,FFI)data_state) r2 r1 locs l2 l1 c.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars [0;1;2] (data_state_locals s) =
       SOME [data_Number i; data_Number j; data_Number (&op_index)] /\
     wl_state_clock t = MustTerminate_limit (:A) - 2 /\ ~(wl_state_termdep t = 0) /\
     lookup 6 (wl_state_locals t) = SOME (wl_Word (word (4 * op_index))) /\
     data_to_word_bignumProof_int_op op_index i j = SOME v ==>
     ?q r new_c.
       wl_evaluate (AnyArith_code c,t) = (q,r) /\
       if q = SOME NotEnoughSpace then
         wl_state_ffi r = wl_state_ffi t /\
         (~(data_to_word_config_gc_kind c = data_to_word_None) /\
          no_thunks_in_refs (data_state_refs s) ==>
          let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i in
          let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) j in
            il + jl <= 2 EXP data_to_word_config_len_size c ==>
            limits_heap_limit (data_state_limits s) <
            il + jl + size_of_heap (cut_locals (fromList [one; one; one]) s))
       else
         ?rv. q = SOME (wl_Result (wl_Loc l1 l2) [rv]) /\
              data_to_word_gcProof_state_rel c r1 r2
                (data_state_locals_fupd (K LN)
                   (data_state_locals_size_fupd (K (SOME 0))
                      (data_state_clock_fupd (K new_c)
                         (data_state_space_fupd (K 0)
                            (data_state_stack_max_fupd (K NONE) s))))) r
                (SOME [(data_Number v,rv)]) locs`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[get_vars_SOME_IFF_data] o
    check (fun th -> mp4_is_app "data_get_vars" (lhs (concl th)))) THEN
  SUBGOAL_THEN `good_dimindex(:A) /\ shift_length c < dimindex(:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  ABBREV_TAC `il = LENGTH (SND (i2mw i):(A word)list)` THEN
  ABBREV_TAC `jl = LENGTH (SND (i2mw j):(A word)list)` THEN
  MP_TAC(SPECL [`0`; `c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `i:int`; `word 4:A word`]
    evaluate_AddNumSize) THEN
  ASM_REWRITE_TAC[wl_set_var_def] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`1`; `c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `j:int`;
    `word_add (word 4) (word (4 * il)):A word`] evaluate_AddNumSize) THEN
  ASM_REWRITE_TAC[wl_set_var_def] THEN DISCH_TAC THEN
  ABBREV_TAC `w1 = word_add (word_add (word 4) (word (4 * il))) (word (4 * jl)):A word` THEN
  REWRITE_TAC[AnyArith_code_def] THEN
  BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC [] THEN
  BIGPAUX_SEQ_STEP_TAC []) THEN
  (BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (data_to_word_list_Seq (CONS (AllocVar c lim nms) rest), t4:(A,C,FFI)wl_state)`
    `t4:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `t4 = wl_set_store (Temp (word 29)) (wl_Word w1)
     (wl_state_locals_fupd (K (insert 1 (wl_Word w1) (wl_state_locals t))) (t:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL
   [EXPAND_TAC "t4" THEN REWRITE_TAC[wl_set_store_def] THEN CONV_TAC(CAKE_SIMP_CONV []);
    ALL_TAC] THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) t4 NONE locs /\
                wl_get_var 1 (t4:(A,C,FFI)wl_state) = SOME (wl_Word w1) /\
                FLOOKUP (wl_state_store t4) (Temp (word 29)) = SOME (wl_Word w1)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(let qtm = `t4 = wl_set_store (Temp (word 29)) (wl_Word w1)
       (wl_state_locals_fupd (K (insert 1 (wl_Word w1) (wl_state_locals t)))
         (t:(A,C,FFI)wl_state))` in fun th -> if concl th = qtm then SUBST1_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[state_rel_set_store_Temp; state_rel_insert_1] THEN
    REWRITE_TAC[wl_set_store_def; wl_get_var_def] THEN
    CONV_TAC(CAKE_SIMP_CONV [lookup_insert; FLOOKUP_UPDATE]);
    ALL_TAC] THEN
  SUBGOAL_THEN `data_cut_env (fromList [one;one;one]) (data_state_locals (s:(C,FFI)data_state)) =
     SOME (fromList [data_Number i; data_Number j; data_Number (&op_index)])` ASSUME_TAC THENL
   [MATCH_MP_TAC BIGPAUX_cut_env_3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP data_to_word_config_len_size c < dimword (:A) DIV 8` ASSUME_TAC THENL
   [MP4_ASM "data_to_word_gcProof_state_rel"
      (MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm; memory_rel_def;
                             heap_in_memory_store_def]) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check ((=) `good_dimindex(:A)` o concl)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `data_to_word_config_len_size c + 7 < dimindex(:A)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    TRANS_TAC LTE_TRANS `2 EXP (dimindex(:A) - 7)` THEN
    ASM_REWRITE_TAC[LT_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `il < dimword(:A) DIV 16 /\ jl < dimword(:A) DIV 16` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MAP_EVERY EXPAND_TAC ["il"; "jl"] THEN MATCH_MP_TAC state_rel_IMP_num_size_limit THEN
    MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] THEN BIGPAUX_FAST_MESON_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (w1:A word) DIV 4 = il + jl + 1` ASSUME_TAC THENL
   [EXPAND_TAC "w1" THEN REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; GSYM dimword_def; GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN `(4 + 4 * il + 4 * jl) MOD dimword(:A) = 4 + 4 * il + 4 * jl` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      MP_TAC(SPEC `dimword(:A)` (ARITH_RULE `!d. 16 * (d DIV 16) <= d`)) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `4 + 4 * il + 4 * jl = 4 * (il + jl + 1)`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(ISPEC `wl_evaluate (AllocVar c (2 EXP data_to_word_config_len_size c)
                  (fromList [one;one;one]), t4:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q5:((A)wl_result)option`; `r5:(A,C,FFI)wl_state`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t4:(A,C,FFI)wl_state`; `locs:(num#num)list`; `fromList [one;one;one]`;
    `fromList [data_Number i; data_Number j; data_Number (&op_index)]`; `w1:A word`;
    `2 EXP data_to_word_config_len_size c`; `q5:((A)wl_result)option`;
    `r5:(A,C,FFI)wl_state`] AllocVar_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `bignum_size (limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state))) i
                  = il + 1 /\
                bignum_size (limits_arch_64_bit (data_state_limits s)) j = jl + 1`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state)) <=>
                  dimindex(:A) = 64` SUBST1_TAC THENL
     [MP4_ASM "data_to_word_gcProof_state_rel"
        (MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm; limits_inv_def]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[bignum_size_def] THEN
    FIRST_ASSUM(let qtm = `good_dimindex(:A)` in fun th -> if concl th = qtm
      then REWRITE_TAC[MATCH_MP bignum_digits_LENGTH_n2mw th] else NO_TAC) THEN
    MAP_EVERY EXPAND_TAC ["il"; "jl"] THEN REWRITE_TAC[i2mw_def; SND] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `q5 = SOME (NotEnoughSpace:(A)wl_result)` THENL
   [ASM_REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      lhand (concl th) = `q5 = SOME (NotEnoughSpace:(A)wl_result)`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`q5:((A)wl_result)option`; `r5:(A,C,FFI)wl_state`; `0`] THEN
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      can (find_term ((=) `limits_heap_limit`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    lhand (concl th) = `~(q5 = SOME (NotEnoughSpace:(A)wl_result))`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `q5 = NONE:((A)wl_result)option` o concl)) THEN
  REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(il + jl + 1) + 1 = il + jl + 2`]) THEN
  ABBREV_TAC `s0 = data_state_locals_fupd
    (K (fromList [data_Number i; data_Number j; data_Number (&op_index)]))
    (data_state_space_fupd (K (il + jl + 2)) (s:(C,FFI)data_state))` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "data_to_word_gcProof_state_rel" (concl th)
    && free_in `r5:(A,C,FFI)wl_state` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `data_get_var 0 (data_state_locals (s0:(C,FFI)data_state)) = SOME (data_Number i) /\
                data_get_var 1 (data_state_locals s0) = SOME (data_Number j) /\
                data_get_var 2 (data_state_locals s0) = SOME (data_Number (&op_index))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN REWRITE_TAC[data_get_var_def] THEN
    CONV_TAC(CAKE_SIMP_CONV [lookup_fromList; LENGTH]) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD; TL; num_CONV `2`; num_CONV `1`]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(SPECL [`word 0:5 word`; `word 31:5 word`; `word 12:5 word`; `0`;
    `c:data_to_word_config`; `l1:num`; `l2:num`; `s0:(C,FFI)data_state`;
    `r5:(A,C,FFI)wl_state`; `locs:(num#num)list`; `i:int`; `F`] AnyHeader_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_DISTINCT; MEM] THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (ABBREV_TAC `s8 = wl_set_store (Temp (word 0)) (wl_Word (mc_header (i2mw i)))
       (wl_set_store (Temp (word 31)) (wl_Word a2)
       (wl_set_store (Temp (word 12)) (wl_Word a3)
       (wl_set_var 7 temp (r5:(A,C,FFI)wl_state))))` THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 (s0:(C,FFI)data_state) (s8:(A,C,FFI)wl_state) NONE locs`
    ASSUME_TAC THENL
   [EXPAND_TAC "s8" THEN
    ASM_REWRITE_TAC[state_rel_set_store_Temp; wl_set_var_def; state_rel_insert_7];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(SPECL [`word 1:5 word`; `word 30:5 word`; `word 11:5 word`; `1`;
    `c:data_to_word_config`; `l1:num`; `l2:num`; `s0:(C,FFI)data_state`;
    `s8:(A,C,FFI)wl_state`; `locs:(num#num)list`; `j:int`; `T`] AnyHeader_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_DISTINCT; MEM] THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `b2:A word` (X_CHOOSE_THEN `b3:A word`
    (X_CHOOSE_THEN `temp2:A word_loc` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ABBREV_TAC `s9 = wl_set_store (Temp (word 1)) (wl_Word (mc_header (i2mw j)))
       (wl_set_store (Temp (word 30)) (wl_Word b2)
       (wl_set_store (Temp (word 11)) (wl_Word b3)
       (wl_set_var 7 temp2 (s8:(A,C,FFI)wl_state))))` THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 (s0:(C,FFI)data_state) (s9:(A,C,FFI)wl_state) NONE locs`
    ASSUME_TAC THENL
   [EXPAND_TAC "s9" THEN
    ASM_REWRITE_TAC[state_rel_set_store_Temp; wl_set_var_def; state_rel_insert_7];
    ALL_TAC]) THEN
  (MP4_ASM "data_to_word_gcProof_state_rel"
    (fun th -> if free_in `s9:(A,C,FFI)wl_state` (concl th) then
       MP_TAC(REWRITE_RULE[data_to_word_gcProof_state_rel_thm; memory_rel_def;
                           heap_in_memory_store_def] th) else NO_TAC) THEN
  CASE_REWRITE_TAC[APPEND] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `unused_space_inv a (sp + sp1)
     (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) /\
     heap_ok heap limit` STRIP_ASSUME_TAC THENL
   [MP4_ASM "word_ml_inv" (MP_TAC o REWRITE_RULE[word_ml_inv_def; abs_ml_inv_def]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[unused_space_inv_def] o
    check (fun th -> mp4_is_app "unused_space_inv" (concl th))) THEN
  SUBGOAL_THEN `data_state_space (s0:(C,FFI)data_state) = il + jl + 2` ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN CONV_TAC(CAKE_SIMP_CONV []); ALL_TAC] THEN
  SUBGOAL_THEN `?k. sp + sp1 = (il + jl + 2) + k` (X_CHOOSE_TAC `k:num`) THENL
   [EXISTS_TAC `(sp + sp1) - (il + jl + 2)` THEN
    UNDISCH_TAC `data_state_space (s0:(C,FFI)data_state) <= sp` THEN
    FIRST_ASSUM(let qtm = `data_state_space (s0:(C,FFI)data_state) = il + jl + 2` in fun th -> if concl th = qtm
      then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    mp4_is_app "heap_lookup" (lhs (rand (concl th))))) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~((il + jl + 2) + k = 0)`;
                  ARITH_RULE `((il + jl + 2) + k) - 1 = (il + jl + 1) + k`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
    heap_element)list` (X_CHOOSE_THEN `hb:((A word_loc,data_to_word_memoryProof_tag#
    (A word_loc)list)heap_element)list` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN `~(limit = 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[heap_ok_def] o
      check (fun th -> mp4_is_app "heap_ok" (concl th))) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) =
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_def; MAP; SUM; el_length_def] THEN
    ARITH_TAC; ALL_TAC] THEN
  MP4_X_ASM "STAR" (fun th -> if can (find_term (fun t -> is_comb t && is_const (rator t) &&
      fst (dest_const (rator t)) = "heap_expand")) (concl th) then MP_TAC th else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) =
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
      then REWRITE_TAC[th] else NO_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`curr:A word`; `ha:((A word_loc,data_to_word_memoryProof_tag#
      (A word_loc)list)heap_element)list`; `il + jl + 1`; `k:num`; `hb:((A word_loc,
      data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`; `other:A word`;
      `limit:num`; `c:data_to_word_config`; `wl_state_memory (s9:(A,C,FFI)wl_state)`;
      `wl_state_mdomain (s9:(A,C,FFI)wl_state)`] BIGPAUX_heap_decomp) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:A word_loc` (X_CHOOSE_THEN `xs:(A word_loc)list`
    (X_CHOOSE_THEN `wo:A word_loc` STRIP_ASSUME_TAC)))) THEN
  (SUBGOAL_THEN `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) (Temp (word 11)) =
     SOME (wl_Word b3) /\
   FLOOKUP (wl_state_store s9) (Temp (word 12)) = SOME (wl_Word a3) /\
   FLOOKUP (wl_state_store s9) (Temp (word 29)) = SOME (wl_Word w1) /\
   FLOOKUP (wl_state_store s9) (Temp (word 31)) = SOME (wl_Word a2) /\
   FLOOKUP (wl_state_store s9) (Temp (word 30)) = SOME (wl_Word b2) /\
   FLOOKUP (wl_state_store s9) (Temp (word 0)) = SOME (wl_Word (mc_header (i2mw i))) /\
   FLOOKUP (wl_state_store s9) (Temp (word 1)) = SOME (wl_Word (mc_header (i2mw j))) /\
   wl_state_code s9 = wl_state_code (r5:(A,C,FFI)wl_state) /\
   wl_state_clock s9 = wl_state_clock r5`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s9" THEN EXPAND_TAC "s8" THEN
    REWRITE_TAC[wl_set_store_def; wl_set_var_def] THEN
    CONV_TAC(CAKE_SIMP_CONV [FLOOKUP_UPDATE; injectivity "store_name"]) THEN
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `op_index < 7` ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_bignumProof_int_op op_index i j = SOME (v:int)` THEN
    REWRITE_TAC[data_to_word_bignumProof_int_op_def] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup 6 (wl_state_locals (s9:(A,C,FFI)wl_state)) =
                SOME (wl_Word (word (4 * op_index)))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s0:(C,FFI)data_state`;
      `s9:(A,C,FFI)wl_state`; `locs:(num#num)list`; `2`; `data_Number (&op_index)`]
      BIGPAUX_state_rel_memory_rel_var) THEN
    ASM_REWRITE_TAC[adjust_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `w6:A word_loc` (X_CHOOSE_THEN `vars6:(data_v#A word_loc)list`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `small_int (:A) (&op_index)` ASSUME_TAC THENL
     [REWRITE_TAC[small_int_def] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
        check ((=) `good_dimindex(:A)` o concl)) THEN
      ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[INT_OF_NUM_LT] THEN (CONJ_TAC THENL
       [MATCH_MP_TAC(INT_ARITH `&0 <= x /\ &0 <= y ==> --x <= y:int`) THEN
        REWRITE_TAC[INT_POS];
        UNDISCH_TAC `op_index < 7` THEN ARITH_TAC]); ALL_TAC] THEN
    MP_TAC(SPECL [`c:data_to_word_config`; `wl_state_be (s9:(A,C,FFI)wl_state)`;
      `THE (data_state_tstamps (s0:(C,FFI)data_state))`; `data_state_refs (s0:(C,FFI)data_state)`;
      `data_state_space (s0:(C,FFI)data_state)`; `wl_state_store (s9:(A,C,FFI)wl_state)`;
      `wl_state_memory (s9:(A,C,FFI)wl_state)`; `wl_state_mdomain (s9:(A,C,FFI)wl_state)`;
      `&op_index:int`; `w6:A word_loc`; `vars6:(data_v#A word_loc)list`] memory_rel_Number_IMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[data_to_word_Smallnum_def; INT_LT; INT_OF_NUM_LT; LT] THEN
    REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM];
    ALL_TAC]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BIGPAUX_SHIFT_FACTS o
    check ((=) `good_dimindex(:A)` o concl)) THEN
  MP4AUX_SEP_R_TAC THEN
  BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC [] THEN
  BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC [] THEN
  BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC [] THEN BIGPAUX_SEQ_STEP_TAC []) THEN
  (BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (data_to_word_list_Seq (CONS (wl_Call (SOME ([0],nms,wl_Skip,ll1,ll2))
       dst args NONE) rest), t9:(A,C,FFI)wl_state)` `t9:(A,C,FFI)wl_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BIGPAUX_MUL_1]) THEN
  SUBGOAL_THEN `(misc_word_list (word_add (word_add curr (word_mul bytes_in_word
                   (word (heap_length ha)))) bytes_in_word) xs STAR
     (set_sep_one (word_add curr (word_mul bytes_in_word (word (heap_length ha))),wl_Word a3) STAR
      set_sep_one (other,wl_Word b3) STAR
      word_heap curr ha c STAR
      word_list_exists (word_add (word_add curr (word_mul bytes_in_word
        (word (heap_length ha)))) (word_mul bytes_in_word (word (1 + (il + jl + 1))))) k STAR
      word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
        (word_mul bytes_in_word (word (((il + jl + 1) + k) + 1)))) hb c STAR
      word_heap (word_add other bytes_in_word) (heap_expand (limit - 1)) c))
     (fun2set (wl_state_memory (t9:(A,C,FFI)wl_state),wl_state_mdomain t9))` ASSUME_TAC THENL
   [EXPAND_TAC "t9" THEN CONV_TAC(CAKE_SIMP_CONV []) THEN
    MP4AUX_SEP_W_TAC THEN MP4AUX_SEP_W_TAC THEN MP4AUX_SEP_AC_TAC; ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o MATCH_MP word_list_store_list o check (fun th ->
    can (find_term ((=) `t9:(A,C,FFI)wl_state`)) (concl th) &&
    mp4_is_app "fun2set" (rand (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `m2:A word->A word_loc` STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN `lookup Replicate_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                  SOME (5,Replicate_code)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP lookup_RefByte_location o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                    (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    SIMP_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `lookup Replicate_location (wl_state_code (s9:(A,C,FFI)wl_state)) =
                  SOME (5,Replicate_code)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP lookup_RefByte_location o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s0:(C,FFI)data_state)
                    (s9:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_clock (s9:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 2`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `data_state_clock (s0:(C,FFI)data_state) = data_state_clock (s:(C,FFI)data_state)`
      ASSUME_TAC THENL
     [EXPAND_TAC "s0" THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
      REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                    (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
      REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s0:(C,FFI)data_state)
                    (s9:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check ((=) `data_state_clock (s0:(C,FFI)data_state) = data_state_clock (s:(C,FFI)data_state)` o concl)) THEN
    FIRST_ASSUM(SUBST1_TAC o check ((=) `wl_state_clock (t:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 2` o concl)) THEN
    MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_state_code (t9:(A,C,FFI)wl_state) = wl_state_code (s9:(A,C,FFI)wl_state) /\
              wl_state_clock t9 = wl_state_clock s9 /\
              wl_state_termdep t9 = wl_state_termdep s9 /\
              wl_state_mdomain t9 = wl_state_mdomain s9 /\
              wl_state_be t9 = wl_state_be s9 /\
              wl_get_var 2 t9 = SOME (wl_Word (word_add curr (word_mul bytes_in_word
                                       (word (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))) /\
              wl_get_var 3 t9 = SOME (wl_Word (word 0)) /\
              wl_get_var 1 t9 = SOME (wl_Word w1) /\
              wl_get_var 0 t9 = SOME (wl_Loc l1 l2)` STRIP_ASSUME_TAC THENL
 [EXPAND_TAC "t9" THEN
  REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  BIGPAUX_ASM_REWRITE_TAC [`lookup 0 (wl_state_locals (s9:(A,C,FFI)wl_state)) =
                             SOME (wl_Loc l1 l2)`] []; ALL_TAC] THEN
  SUBGOAL_THEN `w1 = word (4 * LENGTH (xs:(A word_loc)list)):A word` ASSUME_TAC THENL
   [BIGPAUX_ASM_REWRITE_TAC [`LENGTH (xs:(A word_loc)list) = il + jl + 1`] [] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check ((=) `word_add (word_add (word 4) (word (4 * il))) (word (4 * jl)) = w1:A word` o concl)) THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
  (MP_TAC(SPECL [`LENGTH (xs:(A word_loc)list)`;
   `word_add curr (word_mul bytes_in_word (word (heap_length
      (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))):A word`;
   `t9:(A,C,FFI)wl_state`; `m2:A word->A word_loc`; `2`; `3`; `1`;
   `wl_Word (word 0):A word_loc`; `wl_Loc l1 l2:A word_loc`; `AnyArith_location`; `2`]
   data_to_word_bignumProof_Replicate_code_alt_thm) THEN
 ANTS_TAC THENL
  [BIGPAUX_ASM_PRED_REWRITE_TAC (fun c -> is_eq c &&
     (mp4_is_app "data_to_word_memoryProof_store_list" (lhand c) ||
      mp4_is_app "wl_get_var" (lhand c) &&
        free_in `t9:(A,C,FFI)wl_state` (lhand c))) [] THEN
   BIGPAUX_ASM_REWRITE_TAC
     [`wl_state_code (t9:(A,C,FFI)wl_state) = wl_state_code (s9:(A,C,FFI)wl_state)`;
      `wl_state_clock (t9:(A,C,FFI)wl_state) = wl_state_clock (s9:(A,C,FFI)wl_state)`;
      `wl_state_clock (s9:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 2`;
      `lookup Replicate_location (wl_state_code (s9:(A,C,FFI)wl_state)) =
         SOME (5,Replicate_code)`] [] THEN
   FIRST_ASSUM(let qtm = `w1 = word (4 * LENGTH (xs:(A word_loc)list)):A word` in fun th -> if concl th = qtm
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
   BIGPAUX_ASM_REWRITE_TAC [`LENGTH (xs:(A word_loc)list) = il + jl + 1`] [] THEN
   MP_TAC(SPECL [`dimword(:A)`; `16`] DIV_MUL_LE) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP MustTerminate_limit_SUB_2 o check ((=) `good_dimindex(:A)` o concl)) THEN
   BIGPAUX_ASM_REWRITE_TAC [`il < dimword (:A) DIV 16`; `jl < dimword (:A) DIV 16`] [] THEN
   MP_TAC(SPECL [`il:num`; `dimword (:A) DIV 16`] (ARITH_RULE `!a b. a < b ==> a + 1 <= b`)) THEN
   MP_TAC(SPECL [`jl:num`; `dimword (:A) DIV 16`] (ARITH_RULE `!a b. a < b ==> a + 1 <= b`)) THEN
   BIGPAUX_ASM_REWRITE_TAC [`il < dimword (:A) DIV 16`; `jl < dimword (:A) DIV 16`] [] THEN
   ARITH_TAC;
   ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_TAC (mk_var("max",`:num option`))) THEN
  SUBGOAL_THEN `FLOOKUP (wl_state_store (t9:(A,C,FFI)wl_state)) (Temp (word 29)) =
     SOME (wl_Word (word_add curr (word_mul bytes_in_word (word (heap_length
      (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))))`
    ASSUME_TAC THENL
   [EXPAND_TAC "t9" THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    CONV_TAC(CAKE_SIMP_CONV [FLOOKUP_UPDATE; injectivity "store_name"]) THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  BIGPAUX_ASM_PRED_REWRITE_TAC (fun c -> is_eq c && mp4_is_app "wl_evaluate" (lhand c) &&
     free_in `t9:(A,C,FFI)wl_state` (lhand c)) [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]) THEN
  (CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN BIGPAUX_SEQ_STEP_TAC []) THEN
  (BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (data_to_word_list_Seq (CONS (wl_Call (SOME ([1],nms,wl_Skip,ll1,ll2))
       dst args NONE) rest), t10:(A,C,FFI)wl_state)` `t10:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `?p1 ll ii nn cs. word_bignum_compile Bignum_location 2 1
      (Bignum_location + 1,[]) (mc_iop_code:(A)mini) = (p1,ll,ii,nn,cs)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXISTS_PAIR_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lookup Bignum_location (wl_state_code (s9:(A,C,FFI)wl_state)) =
      SOME (1,wl_Seq p1 (wl_Return 0 [0]))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s0:(C,FFI)data_state)
                    (s9:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_code_rel_def; data_to_word_stubs_def; ALL_APPEND] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[generated_bignum_stubs_def; LET_DEF; LET_END_DEF] THEN
    BIGPAUX_ASM_REWRITE_TAC [`word_bignum_compile Bignum_location 2 1
      (Bignum_location + 1,[]) (mc_iop_code:(A)mini) = (p1,ll,ii,nn,cs)`] [] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_state_clock (t10:(A,C,FFI)wl_state) =
     (data_state_clock (s0:(C,FFI)data_state) - (il + jl + 1)) - 1 /\
   wl_state_locals t10 = insert 0 (wl_Loc l1 l2) LN /\
   wl_state_store t10 = wl_state_store (t9:(A,C,FFI)wl_state) |+ (Temp (word 29),
     wl_Word (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
      (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
      bytes_in_word)) /\
   wl_state_memory t10 = m2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t10" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_code (t10:(A,C,FFI)wl_state) = wl_state_code (s9:(A,C,FFI)wl_state) /\
   wl_state_mdomain t10 = wl_state_mdomain s9 /\
   wl_state_termdep t10 = wl_state_termdep s9 /\
   wl_state_be t10 = wl_state_be s9 /\
   wl_state_stack t10 = wl_state_stack s9 /\
   wl_state_stack_size t10 = wl_state_stack_size s9 /\
   wl_state_locals_size t10 = wl_state_locals_size s9 /\
   wl_state_gc_fun t10 = wl_state_gc_fun s9 /\
   wl_state_handler t10 = wl_state_handler s9 /\
   wl_state_ffi t10 = wl_state_ffi s9 /\
   wl_state_compile t10 = wl_state_compile s9 /\
   wl_state_compile_oracle t10 = wl_state_compile_oracle s9 /\
   wl_state_code_buffer t10 = wl_state_code_buffer s9 /\
   wl_state_data_buffer t10 = wl_state_data_buffer s9 /\
   wl_state_stack_limit t10 = wl_state_stack_limit s9` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t10" THEN EXPAND_TAC "t9" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
  (ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN
  BIGPAUX_EVAL_THMS_TAC [] [BIGPAUX_fromList_one; domain_def; NOT_INSERT_EMPTY; ALL_DISTINCT; MEM;
     wl_get_vars_def]) THEN
  (SUBGOAL_THEN `lookup Bignum_location (wl_state_code (t:(A,C,FFI)wl_state)) =
      SOME (1,wl_Seq p1 (wl_Return 0 [0]))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                    (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
    REWRITE_TAC[data_to_word_gcProof_code_rel_def; data_to_word_stubs_def; ALL_APPEND] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[generated_bignum_stubs_def; LET_DEF; LET_END_DEF] THEN
    BIGPAUX_ASM_REWRITE_TAC [`word_bignum_compile Bignum_location 2 1
      (Bignum_location + 1,[]) (mc_iop_code:(A)mini) = (p1,ll,ii,nn,cs)`] [] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[ALL] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((data_state_clock (s0:(C,FFI)data_state) - (il + jl + 1)) - 1 = 0) /\
                ~(((data_state_clock s0 - (il + jl + 1)) - 1) - 1 = 0)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `data_state_clock (s0:(C,FFI)data_state) = MustTerminate_limit (:A) - 2`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check ((=) `wl_state_clock (s9:(A,C,FFI)wl_state) = data_state_clock (s0:(C,FFI)data_state)` o concl)) THEN
      BIGPAUX_ASM_REWRITE_TAC [`wl_state_clock (s9:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 2`] [];
      ALL_TAC] THEN
    MP_TAC(SPECL [`dimword(:A)`; `16`] DIV_MUL_LE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MustTerminate_limit_SUB_2 o check ((=) `good_dimindex(:A)` o concl)) THEN
    MP_TAC(SPECL [`il:num`; `dimword (:A) DIV 16`] (ARITH_RULE `!a b. a < b ==> a + 1 <= b`)) THEN
    MP_TAC(SPECL [`jl:num`; `dimword (:A) DIV 16`] (ARITH_RULE `!a b. a < b ==> a + 1 <= b`)) THEN
    BIGPAUX_ASM_REWRITE_TAC [`il < dimword (:A) DIV 16`; `jl < dimword (:A) DIV 16`] [] THEN
    ARITH_TAC; ALL_TAC]) THEN
  (ABBREV_TAC `bigbody = wl_Seq p1 (wl_Return 0 [0]):(A)wl_prog` THEN
  REWRITE_TAC[MATCH_MP WBIGPAUX_cut_envs_ret
     (ISPECL [`0`; `wl_Loc l1 l2:A word_loc`; `LN:(A word_loc)spt`] lookup_insert1)] THEN
  BIGPAUX_EVAL_THMS_TAC [] [BIGPAUX_fromList_one; domain_def; NOT_INSERT_EMPTY; ALL_DISTINCT; MEM;
     wl_get_vars_def; push_env_insert_0]) THEN
  (BIGPAUX_MATCH_ABBREV_TAC `wl_evaluate (bigbody, t3:(A,C,FFI)wl_state)`
    `t3:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `wl_state_termdep (s9:(A,C,FFI)wl_state) = wl_state_termdep (t:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [(fun g -> MAP_EVERY (fun th -> MP_TAC(CONJUNCT2(MATCH_MP wl_evaluate_clock th)))
      (BIGPAUX_ASMS [`wl_evaluate (AnyHeader c 4 T (word 1) (word 30) (word 11),
                        s8:(A,C,FFI)wl_state) = NONE,(s9:(A,C,FFI)wl_state)`;
         `wl_evaluate (AnyHeader c 2 F (word 0) (word 31) (word 12),
                        r5:(A,C,FFI)wl_state) = NONE,(s8:(A,C,FFI)wl_state)`;
         `wl_evaluate (AllocVar c (2 EXP data_to_word_config_len_size c)
             (fromList [one; one; one]), t4:(A,C,FFI)wl_state) = NONE,(r5:(A,C,FFI)wl_state)`]
       g) g) THEN
    BIGPAUX_ASM_REWRITE_TAC [`t4 = wl_set_store (Temp (word 29)) (wl_Word w1)
     (wl_state_locals_fupd (K (insert 1 (wl_Word w1) (wl_state_locals t))) (t:(A,C,FFI)wl_state))`]
      [wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `wl_state_code (t3:(A,C,FFI)wl_state) = wl_state_code (t:(A,C,FFI)wl_state) /\
     wl_state_termdep t3 = wl_state_termdep t /\
     wl_state_clock t3 = ((data_state_clock (s0:(C,FFI)data_state) - (il + jl + 1)) - 1) - 1 /\
     wl_get_var 0 t3 = SOME (wl_Loc AnyArith_location 3) /\
     wl_state_store t3 = wl_state_store (t9:(A,C,FFI)wl_state) |+ (Temp (word 29),
       wl_Word (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
        bytes_in_word)) /\
     wl_state_memory t3 = m2 /\
     wl_state_mdomain t3 = wl_state_mdomain (s9:(A,C,FFI)wl_state) /\
     wl_state_be t3 = wl_state_be s9 /\
     wl_state_stack t3 = CONS (StackFrame (data_state_locals_size s0) [0,wl_Loc l1 l2] [] NONE)
                           (wl_state_stack s9)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t3" THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def; lookup_insert] THEN
    BIGPAUX_ASM_REWRITE_TAC [
      `wl_state_code (t10:(A,C,FFI)wl_state) = wl_state_code (s9:(A,C,FFI)wl_state)`;
      `wl_state_code (s9:(A,C,FFI)wl_state) = wl_state_code (r5:(A,C,FFI)wl_state)`;
      `wl_state_code (r5:(A,C,FFI)wl_state) = wl_state_code (wl_set_store (Temp (word 29)) (wl_Word w1)
        (wl_state_locals_fupd (K (insert 1 (wl_Word w1) (wl_state_locals t))) (t:(A,C,FFI)wl_state)))`;
      `wl_state_termdep (t10:(A,C,FFI)wl_state) = wl_state_termdep (s9:(A,C,FFI)wl_state)`;
      `wl_state_termdep (s9:(A,C,FFI)wl_state) = wl_state_termdep (t:(A,C,FFI)wl_state)`;
      `wl_state_store (t10:(A,C,FFI)wl_state) = wl_state_store (t9:(A,C,FFI)wl_state) |+ (Temp (word 29),
       wl_Word (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
        bytes_in_word))`;
      `wl_state_memory (t10:(A,C,FFI)wl_state) = m2`;
      `wl_state_mdomain (t10:(A,C,FFI)wl_state) = wl_state_mdomain (s9:(A,C,FFI)wl_state)`;
      `wl_state_be (t10:(A,C,FFI)wl_state) = wl_state_be (s9:(A,C,FFI)wl_state)`;
      `wl_state_stack (t10:(A,C,FFI)wl_state) = wl_state_stack (s9:(A,C,FFI)wl_state)`]
      [wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM]; ALL_TAC]) THEN
  (SUBGOAL_THEN `data_state_clock (s0:(C,FFI)data_state) = MustTerminate_limit (:A) - 2`
    ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check ((=) `wl_state_clock (s9:(A,C,FFI)wl_state) = data_state_clock (s0:(C,FFI)data_state)` o concl)) THEN
    BIGPAUX_ASM_REWRITE_TAC [`wl_state_clock (s9:(A,C,FFI)wl_state) = MustTerminate_limit (:A) - 2`] [];
    ALL_TAC] THEN
  (fun g -> MP_TAC(MATCH_MP (SPECL [`il:num`; `jl:num`] BIGPAUX_AA_SIZES)
     (end_itlist CONJ (BIGPAUX_ASMS [`good_dimindex(:A)`; `il < dimword (:A) DIV 16`;
        `jl < dimword (:A) DIV 16`] g))) g) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(mc_header (i2mw i:bool#(A word)list) = word 0 <=> SND (i2mw i:bool#(A word)list) = []) /\
     (mc_header (i2mw j:bool#(A word)list) = word 0 <=> SND (i2mw j:bool#(A word)list) = [])`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SND_i2mw_NIL] THEN CONJ_TAC THEN MATCH_MP_TAC mc_header_i2mw_eq_0w THEN
    BIGPAUX_ASM_REWRITE_TAC [`LENGTH (SND (i2mw i:bool#(A word)list)) = il`;
      `LENGTH (SND (i2mw j:bool#(A word)list)) = jl`;
      `2 * il + 1 < dimword (:A)`; `2 * jl + 1 < dimword (:A)`] [];
    ALL_TAC]) THEN
  ((fun g -> MP_TAC(MATCH_MP BIGPAUX_int_op_iop (hd (BIGPAUX_ASMS
     [`data_to_word_bignumProof_int_op op_index i j = SOME (v:int)`] g))) g) THEN
  (fun g -> REWRITE_TAC (BIGPAUX_ASMS [`good_dimindex(:A)`] g) g) THEN STRIP_TAC THEN
  SUBGOAL_THEN `mc_div_max (SND (i2mw i:bool#(A word)list)) (SND (i2mw j:bool#(A word)list))
       (REPLICATE (LENGTH (xs:(A word_loc)list)) (word 0:A word)) +
     2 * LENGTH (REPLICATE (LENGTH (xs:(A word_loc)list)) (word 0:A word)) + 2 <=
     wl_state_clock (t3:(A,C,FFI)wl_state)` ASSUME_TAC THENL
   [BIGPAUX_ASM_REWRITE_TAC [`LENGTH (xs:(A word_loc)list) = il + jl + 1`;
      `wl_state_clock (t3:(A,C,FFI)wl_state) =
         ((data_state_clock (s0:(C,FFI)data_state) - (il + jl + 1)) - 1) - 1`;
      `data_state_clock (s0:(C,FFI)data_state) = MustTerminate_limit (:A) - 2`] [] THEN
    MATCH_MP_TAC BIGPAUX_div_max_bound THEN
    BIGPAUX_ASM_REWRITE_TAC [`good_dimindex(:A)`; `il < dimword (:A) DIV 16`;
      `jl < dimword (:A) DIV 16`; `LENGTH (SND (i2mw i:bool#(A word)list)) = il`;
      `LENGTH (SND (i2mw j:bool#(A word)list)) = jl`] []; ALL_TAC]) THEN
  (fun g ->
  let th = BIGPAUX_mc_iop_inst g in
  let srel = el 1 (conjuncts (lhand (concl th))) in
  (SUBGOAL_THEN srel ASSUME_TAC THENL
   [ALL_TAC;
    MP_TAC th THEN ANTS_TAC THENL
     [BIGPAUX_ASM_PRED_REWRITE_TAC (fun c ->
        is_imp c && is_disj (lhand c) && mp4_is_app "get_iop" (lhand (lhand c)) ||
        is_eq c && mp4_is_app "LENGTH" (lhand c) ||
        not (is_imp c) &&
        (mp4_is_app "word_bignumProof_state_rel" c ||
         mp4_is_app "good_dimindex" c ||
         is_eq c && (mp4_is_app "word_bignum_compile" (lhand c) ||
                     mp4_is_app "wl_get_var" (lhand c) &&
                       free_in `t3:(A,C,FFI)wl_state` c) ||
         is_iff c ||
         is_neg c && is_eq (rand c) && mp4_is_app "get_iop" (lhand (rand c)) ||
         mp4_is_app "<" c || mp4_is_app "<=" c)) [LENGTH_REPLICATE] THEN
      FIRST_ASSUM(fun th -> if is_imp (concl th) &&
         is_disj (lhand (concl th)) then ACCEPT_TAC th else NO_TAC);
      ALL_TAC]]) g) THENL
  [(REWRITE_TAC[word_bignumProof_state_rel_def; word_bignumProof_state_INFO.ri_accessors] THEN
  BIGPAUX_ASM_REWRITE_TAC [
    `wl_state_code (t3:(A,C,FFI)wl_state) = wl_state_code (t:(A,C,FFI)wl_state)`;
    `wl_state_termdep (t3:(A,C,FFI)wl_state) = wl_state_termdep (t:(A,C,FFI)wl_state)`;
    `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)`] []) THEN
   ((fun g -> match BIGPAUX_ASMS [`word_bignum_compile Bignum_location 2 1
      (Bignum_location + 1,[]) (mc_iop_code:(A)mini) = (p1,ll,ii,nn,cs)`;
      `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                    (t:(A,C,FFI)wl_state) NONE locs`] g with
     [ce; sr] -> REWRITE_TAC[MATCH_MP IMP_bignum_code_rel (CONJ ce sr);
                             MATCH_MP div_code_assum_thm sr] g
   | _ -> failwith "asms") THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_numeral (lhs (concl th)))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    BIGPAUX_ASM_REWRITE_TAC [`wl_state_store (t3:(A,C,FFI)wl_state) =
      wl_state_store (t9:(A,C,FFI)wl_state) |+ (Temp (word 29),
       wl_Word (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
        bytes_in_word))`] [FLOOKUP_UPDATE; injectivity "store_name"] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    EXPAND_TAC "t9" THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; injectivity "store_name"] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    BIGPAUX_ASM_REWRITE_TAC [
      `word_ushr (word (4 * op_index)) 2 = int_op_rep (get_iop op_index):A word`;
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) (Temp (word 1)) =
         SOME (wl_Word (mc_header (i2mw j:bool#(A word)list)))`;
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) (Temp (word 0)) =
         SOME (wl_Word (mc_header (i2mw i:bool#(A word)list)))`] []]) THEN
   (REWRITE_TAC[array_rel_def; TempIn1_def; TempIn2_def; TempOut_def] THEN
  BIGPAUX_ASM_REWRITE_TAC [`wl_state_store (t3:(A,C,FFI)wl_state) =
      wl_state_store (t9:(A,C,FFI)wl_state) |+ (Temp (word 29),
       wl_Word (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
        bytes_in_word))`;
     `wl_state_memory (t3:(A,C,FFI)wl_state) = m2`;
     `wl_state_mdomain (t3:(A,C,FFI)wl_state) = wl_state_mdomain (s9:(A,C,FFI)wl_state)`]
    [FLOOKUP_UPDATE; injectivity "store_name"] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
  EXPAND_TAC "t9" THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; injectivity "store_name"] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
  BIGPAUX_ASM_REWRITE_TAC [
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) (Temp (word 31)) = SOME (wl_Word a2)`;
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) (Temp (word 30)) = SOME (wl_Word b2)`]
    [option_INJ; injectivity "word_loc"; APPLY_UPDATE_THM; distinctness "address"; K_THM;
     map_replicate] THEN
  REWRITE_TAC[UNWIND_THM1; LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM]) THEN
   (FIRST_ASSUM(let qtm = `wl_state_mdomain (t9:(A,C,FFI)wl_state) = wl_state_mdomain (s9:(A,C,FFI)wl_state)` in fun eqth -> if concl eqth = qtm
    then FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[eqth] o check (fun th -> let c = concl th in
      mp4_is_app "fun2set" (rand c) && free_in `m2:A word->A word_loc` (rand c)))
    else NO_TAC) THEN
  SUBGOAL_THEN `wl_get_var 2 (s9:(A,C,FFI)wl_state) = wl_get_var 2 (r5:(A,C,FFI)wl_state) /\
     wl_get_var 4 s9 = wl_get_var 4 (s8:(A,C,FFI)wl_state) /\
     FLOOKUP (wl_state_store r5) CurrHeap = FLOOKUP (wl_state_store s9) CurrHeap /\
     FLOOKUP (wl_state_store s8) CurrHeap = FLOOKUP (wl_state_store s9) CurrHeap /\
     FLOOKUP (wl_state_store r5) NextFree = FLOOKUP (wl_state_store s9) NextFree /\
     FLOOKUP (wl_state_store s8) OtherHeap = FLOOKUP (wl_state_store s9) OtherHeap`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s9" THEN EXPAND_TAC "s8" THEN
    REWRITE_TAC[wl_set_store_def; wl_set_var_def; wl_get_var_def; wl_state_INFO.ri_accfupds;
      K_THM; FLOOKUP_UPDATE; lookup_insert; distinctness "store_name"] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC]) THEN
   (REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [CONJ_TAC; FIRST_ASSUM ACCEPT_TAC]) THENL
   [(ASM_CASES_TAC `(i:int) = &0` THENL
   [BIGPAUX_MP_ASM_TAC `(i:int) = &0` [`(i:int) = &0`] THEN STRIP_TAC THEN
    BIGPAUX_I2MW_REWRITE_TAC `i:int` THEN BIGPAUX_SEP_EXISTS_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `small_int (:A) i` THENL
   [BIGPAUX_MP_ASM_TAC `small_int (:A) i /\ ~(i = &0)`
      [`small_int (:A) i`; `~((i:int) = &0)`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a2 = word_add curr (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))):A word`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check ((=) `FLOOKUP (wl_state_store (r5:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word a2)` o concl)) THEN
      BIGPAUX_ASM_REWRITE_TAC [
        `FLOOKUP (wl_state_store (r5:(A,C,FFI)wl_state)) NextFree =
         FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) NextFree`;
        `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) NextFree =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a))))`;
        `a = heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`]
        [option_INJ; injectivity "word_loc"] THEN
      MESON_TAC[]; ALL_TAC] THEN
    BIGPAUX_I2MW_REWRITE_TAC `i:int` THEN BIGPAUX_SEP_EXISTS_TAC;
    ALL_TAC] THEN
  BIGPAUX_MP_ASM_TAC `~small_int (:A) i` [`~small_int (:A) i`] THEN
  DISCH_THEN(X_CHOOSE_THEN `wi:A word` (X_CHOOSE_THEN `xi:A word` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check ((=) `a2 = word_add xi bytes_in_word:A word` o concl)) THEN
  (fun g -> match BIGPAUX_ASMS [
       `wl_get_var 2 (r5:(A,C,FFI)wl_state) = SOME (wl_Word wi)`;
       `wl_get_var 2 (s9:(A,C,FFI)wl_state) = wl_get_var 2 (r5:(A,C,FFI)wl_state)`;
       `FLOOKUP (wl_state_store (r5:(A,C,FFI)wl_state)) CurrHeap =
        FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap`;
       `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr)`;
       `get_real_addr c (wl_state_store (r5:(A,C,FFI)wl_state)) wi = SOME xi`] g with
     [gr5; geq; ceq; cs9; gra] ->
       let gv = EQT_ELIM (REWRITE_CONV [adjust_var_def; ARITH; geq; gr5]
                  `wl_get_var (adjust_var 0) (s9:(A,C,FFI)wl_state) = SOME (wl_Word wi)`) in
       let cth = EQT_ELIM (REWRITE_CONV [ceq; cs9]
                  `FLOOKUP (wl_state_store (r5:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr)`) in
       BIGPAUX_ARR_BIG_TAC `i:int` `0` gv cth gra g
   | _ -> failwith "asms"));
    (ASM_CASES_TAC `(j:int) = &0` THENL
   [BIGPAUX_MP_ASM_TAC `(j:int) = &0` [`(j:int) = &0`] THEN STRIP_TAC THEN
    BIGPAUX_I2MW_REWRITE_TAC `j:int` THEN BIGPAUX_SEP_EXISTS_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `small_int (:A) j` THENL
   [BIGPAUX_MP_ASM_TAC `small_int (:A) j /\ ~(j = &0)`
      [`small_int (:A) j`; `~((j:int) = &0)`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `b2 = other:A word` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check ((=) `FLOOKUP (wl_state_store (s8:(A,C,FFI)wl_state)) OtherHeap = SOME (wl_Word b2)` o concl)) THEN
      BIGPAUX_ASM_REWRITE_TAC [
        `FLOOKUP (wl_state_store (s8:(A,C,FFI)wl_state)) OtherHeap =
         FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) OtherHeap`;
        `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) OtherHeap = SOME (wl_Word other)`]
        [option_INJ; injectivity "word_loc"] THEN
      MESON_TAC[]; ALL_TAC] THEN
    BIGPAUX_I2MW_REWRITE_TAC `j:int` THEN BIGPAUX_SEP_EXISTS_TAC;
    ALL_TAC] THEN
  BIGPAUX_MP_ASM_TAC `~small_int (:A) j` [`~small_int (:A) j`] THEN
  DISCH_THEN(X_CHOOSE_THEN `wj:A word` (X_CHOOSE_THEN `xj:A word` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check ((=) `b2 = word_add xj bytes_in_word:A word` o concl)) THEN
  (fun g -> match BIGPAUX_ASMS [
       `wl_get_var 4 (s8:(A,C,FFI)wl_state) = SOME (wl_Word wj)`;
       `wl_get_var 4 (s9:(A,C,FFI)wl_state) = wl_get_var 4 (s8:(A,C,FFI)wl_state)`;
       `FLOOKUP (wl_state_store (s8:(A,C,FFI)wl_state)) CurrHeap =
        FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap`;
       `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr)`;
       `get_real_addr c (wl_state_store (s8:(A,C,FFI)wl_state)) wj = SOME xj`] g with
     [gr5; geq; ceq; cs9; gra] ->
       let gv = EQT_ELIM (REWRITE_CONV [adjust_var_def; ARITH; geq; gr5]
                  `wl_get_var (adjust_var 1) (s9:(A,C,FFI)wl_state) = SOME (wl_Word wj)`) in
       let cth = EQT_ELIM (REWRITE_CONV [ceq; cs9]
                  `FLOOKUP (wl_state_store (s8:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr)`) in
       BIGPAUX_ARR_BIG_TAC `j:int` `1` gv cth gra g
   | _ -> failwith "asms"))];
   ALL_TAC] THEN
  (DISCH_THEN(X_CHOOSE_THEN `zs1:(A word)list` (X_CHOOSE_THEN `lc2:num`
    (X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && mp4_is_app "wl_evaluate" (lhs (concl th)) &&
      free_in `t2:(A,C,FFI)wl_state` (concl th) then
      FIRST_ASSUM(let qtm = `wl_Seq p1 (wl_Return 0 [0]) = bigbody:(A)wl_prog` in fun ab -> if concl ab = qtm
        then ASSUME_TAC (REWRITE_RULE[ab] th) else NO_TAC) else NO_TAC) THEN
  BIGPAUX_ASM_PRED_REWRITE_TAC (fun c -> is_eq c && mp4_is_app "wl_evaluate" (lhs c) &&
      free_in `t2:(A,C,FFI)wl_state` c) [] THEN
  BIGPAUX_EVAL_THMS_TAC [] [wl_pop_env_def; wl_set_vars_def; alist_insert_def; fromAList_def;
     union_LN; domain_insert; domain_def; insert_shadow; wl_flush_state_def; wl_get_vars_def]) THEN
  (BIGPAUX_EVAL_THMS_TAC [] [UNION_EMPTY] THEN
  BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (data_to_word_list_Seq (CONS (wl_Get 1 (Temp (word 10))) rest),
                  t5:(A,C,FFI)wl_state)` `t5:(A,C,FFI)wl_state`) THEN
  (FIRST_ASSUM(let qtm = `multiword_int_op (get_iop op_index) i j = v` in fun th -> if concl th = qtm
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  SUBGOAL_THEN `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) (Temp (word 10)) =
       SOME (wl_Word (mc_header (i2mw v:bool#(A word)list))) /\
     (!n. (!r. ~(n = Temp r)) ==>
          FLOOKUP (wl_state_store t2) n = FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) n) /\
     (misc_word_list (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
        bytes_in_word) (MAP wl_Word (APPEND (SND (i2mw v:bool#(A word)list)) zs1)) STAR
      (set_sep_one (word_add curr (word_mul bytes_in_word (word (heap_length ha))),wl_Word a3) STAR
      set_sep_one (other,wl_Word b3) STAR
      word_heap curr ha c STAR
      word_list_exists (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
        (word_mul bytes_in_word (word (1 + il + jl + 1)))) k STAR
      word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
        (word_mul bytes_in_word (word (((il + jl + 1) + k) + 1)))) hb c STAR
      word_heap (word_add other bytes_in_word) (heap_expand (limit - 1)) c))
       (fun2set (wl_state_memory t2,wl_state_mdomain t2)) /\
     wl_state_code t2 = wl_state_code (t:(A,C,FFI)wl_state) /\
     wl_state_be t2 = wl_state_be s9 /\
     wl_state_ffi t2 = wl_state_ffi s9 /\
     wl_state_handler t2 = wl_state_handler s9 /\
     wl_state_gc_fun t2 = wl_state_gc_fun s9 /\
     wl_state_compile t2 = wl_state_compile s9 /\
     wl_state_compile_oracle t2 = wl_state_compile_oracle s9 /\
     wl_state_code_buffer t2 = wl_state_code_buffer s9 /\
     wl_state_data_buffer t2 = wl_state_data_buffer s9 /\
     wl_state_stack_limit t2 = wl_state_stack_limit s9 /\
     wl_state_stack_size t2 = wl_state_stack_size s9` STRIP_ASSUME_TAC THENL
   [BIGPAUX_KEEP_TAC (fun c ->
      (mp4_is_app "word_bignumProof_state_rel" c && free_in `t2:(A,C,FFI)wl_state` c) ||
      is_eq c && (rand c = `t3:(A,C,FFI)wl_state` || rand c = `t9:(A,C,FFI)wl_state` ||
        (is_comb (lhs c) && (rand (lhs c) = `t3:(A,C,FFI)wl_state` ||
                             rand (lhs c) = `t10:(A,C,FFI)wl_state`)))) THEN
    SUBGOAL_THEN `wl_state_be (t3:(A,C,FFI)wl_state) = wl_state_be (s9:(A,C,FFI)wl_state) /\
       wl_state_ffi t3 = wl_state_ffi s9 /\
       wl_state_handler t3 = wl_state_handler s9 /\
       wl_state_gc_fun t3 = wl_state_gc_fun s9 /\
       wl_state_compile t3 = wl_state_compile s9 /\
       wl_state_compile_oracle t3 = wl_state_compile_oracle s9 /\
       wl_state_code_buffer t3 = wl_state_code_buffer s9 /\
       wl_state_data_buffer t3 = wl_state_data_buffer s9 /\
       wl_state_stack_limit t3 = wl_state_stack_limit s9 /\
       wl_state_stack_size t3 = wl_state_stack_size s9` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t3" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> mp4_is_app "word_bignumProof_state_rel" (concl th))) THEN
    REWRITE_TAC[word_bignumProof_state_rel_def; WBIGPAUX_delete_vars_simp;
      WBIGPAUX_reg_write_simp; WBIGPAUX_array_write_simp; clock_write_def;
      word_bignumProof_state_INFO.ri_accfupds;
      word_bignumProof_state_INFO.ri_accessors; K_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `!n. (!r. ~(n = Temp r)) ==>
          FLOOKUP (wl_state_store (t3:(A,C,FFI)wl_state)) n =
          FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) n` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      BIGPAUX_ASM_REWRITE_TAC [`wl_state_store (t3:(A,C,FFI)wl_state) =
        wl_state_store (t9:(A,C,FFI)wl_state) |+ (Temp (word 29),
         wl_Word (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
          (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
          bytes_in_word))`] [FLOOKUP_UPDATE] THEN
      EXPAND_TAC "t9" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
      BIGPAUX_FAST_MESON_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`10`; `mc_header (i2mw v:bool#(A word)list):A word`] o
        check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `25`)) (concl th))) THEN
      REWRITE_TAC[DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE; MEM; ARITH_EQ] THEN SIMP_TAC[];
      BIGPAUX_FAST_MESON_TAC;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "array_rel" (concl th))) THEN
      FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) =
        `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) TempOut`
        then REWRITE_TAC[th] else NO_TAC) THEN
      REWRITE_TAC[array_rel_def; TempOut_def] THEN
      BIGPAUX_ASM_REWRITE_TAC [`wl_state_store (t3:(A,C,FFI)wl_state) =
        wl_state_store (t9:(A,C,FFI)wl_state) |+ (Temp (word 29),
         wl_Word (word_add (word_add curr (word_mul bytes_in_word (word (heap_length
          (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
          bytes_in_word))`] [FLOOKUP_UPDATE; option_INJ; injectivity "word_loc";
          APPLY_UPDATE_THM; distinctness "address"; K_THM] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
        is_var (rhs (concl th)) && mp4_is_app "word_add" (lhs (concl th)))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC;
      BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC; BIGPAUX_FAST_MESON_TAC;
      BIGPAUX_FAST_MESON_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `LENGTH (APPEND (SND (i2mw v:bool#(A word)list)) zs1) = il + jl + 1`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) =
       `LENGTH (APPEND (SND (i2mw v:bool#(A word)list)) zs1)` then REWRITE_TAC[th] else NO_TAC) THEN
    BIGPAUX_ASM_REWRITE_TAC [`LENGTH (xs:(A word_loc)list) = il + jl + 1`] [LENGTH_REPLICATE];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * LENGTH (SND (i2mw v:bool#(A word)list)) + 1 < dimword (:A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `LENGTH (APPEND (SND (i2mw v:bool#(A word)list)) zs1) = il + jl + 1` o concl)) THEN
    FIRST_ASSUM(MP_TAC o check ((=) `il + jl + 1 < dimword (:A) DIV 2` o concl)) THEN
    MP_TAC(SPECL [`dimword(:A)`; `2`] DIV_MUL_LE) THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(mc_header (i2mw v:bool#(A word)list) = word 0 <=> v = &0) /\
     (mc_header (i2mw v:bool#(A word)list) = word 2 <=>
        ?v1. i2mw v = (F,[v1]:(A word)list)) /\
     (mc_header (i2mw v:bool#(A word)list) = word 3 <=>
        ?v1. i2mw v = (T,[v1]:(A word)list))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC mc_header_i2mw_eq_0w THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC BIGPAUX_mc_header_23 THEN
      BIGPAUX_ASM_REWRITE_TAC [`good_dimindex(:A)`;
        `2 * LENGTH (SND (i2mw v:bool#(A word)list)) + 1 < dimword (:A)`] []];
    ALL_TAC] THEN
  SUBGOAL_THEN `option_le (wl_state_stack_max (t3:(A,C,FFI)wl_state))
                          (wl_state_stack_max (t2:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`bigbody:(A)wl_prog`; `t3:(A,C,FFI)wl_state`;
      `SOME (wl_Result (wl_Loc AnyArith_location 3) [wl_Loc AnyArith_location 3]):((A)wl_result)option`;
      `wl_flush_state F (t2:(A,C,FFI)wl_state)`] evaluate_stack_max_le) THEN
    REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    BIGPAUX_ASM_PRED_REWRITE_TAC (fun c -> is_eq c && mp4_is_app "wl_evaluate" (lhs c) &&
      free_in `t2:(A,C,FFI)wl_state` c) [] THEN
    REWRITE_TAC[WBIGPAUX_ev_Return; wl_get_vars_def] THEN
    BIGPAUX_ASM_REWRITE_TAC [`wl_get_var 0 (t2:(A,C,FFI)wl_state) = SOME (wl_Loc AnyArith_location 3)`] [] THEN
    CASE_REWRITE_TAC[wl_flush_state_def]; ALL_TAC]) THEN
  (SUBGOAL_THEN `data_state_ffi (s0:(C,FFI)data_state) = data_state_ffi (s:(C,FFI)data_state) /\
     data_state_handler s0 = data_state_handler s /\
     data_state_code s0 = data_state_code s /\
     data_state_compile s0 = data_state_compile s /\
     data_state_compile_oracle s0 = data_state_compile_oracle s /\
     data_state_tstamps s0 = data_state_tstamps s /\
     data_state_stack s0 = data_state_stack s /\
     data_state_stack_frame_sizes s0 = data_state_stack_frame_sizes s /\
     data_state_limits s0 = data_state_limits s /\
     data_state_refs s0 = data_state_refs s /\
     data_state_global s0 = data_state_global s /\
     data_state_locals_size s0 = data_state_locals_size s /\
     data_state_stack_max s0 = data_state_stack_max s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN REWRITE_TAC[data_state_INFO.ri_accfupds]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) &&
      can (find_term ((=) `wl_state_store (t2:(A,C,FFI)wl_state)`)) (concl th)
    then STRIP_ASSUME_TAC (MATCH_MP BIGPAUX_store_nonTemp th) else NO_TAC) THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c r1 r2
     (data_state_locals_fupd (K LN) (data_state_locals_size_fupd (K (SOME 0))
       (data_state_clock_fupd (K (wl_state_clock (t2:(A,C,FFI)wl_state)))
       (data_state_space_fupd (K (il + jl + 2))
       (data_state_stack_max_fupd (K NONE) (s:(C,FFI)data_state))))))
     (wl_state_locals_fupd (K LN) (wl_state_locals_size_fupd (K (SOME 0))
       (wl_state_stack_fupd (K (wl_state_stack (s9:(A,C,FFI)wl_state))) t2)))
     (SOME [(data_Number (&0), wl_Word (word 0))]) locs` ASSUME_TAC THENL
   [REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
      wl_state_INFO.ri_accfupds; K_THM; option_DISTINCT; lookup_def; IS_SOME_DEF] THEN
    BIGPAUX_ASM_PRED_REWRITE_TAC (fun c -> is_eq c && is_comb (lhs c) &&
      (rand (lhs c) = `t2:(A,C,FFI)wl_state` ||
       is_comb (rand (lhs c)) && rand (rand (lhs c)) = `t2:(A,C,FFI)wl_state`)) [] THEN
    (fun (asl,w as g) -> REWRITE_TAC (map (GSYM o snd) (filter (fun (_,th) -> let c = concl th in
       is_eq c && is_comb (lhs c) && rand (lhs c) = `s0:(C,FFI)data_state` &&
       is_comb (rhs c) && rand (rhs c) = `s:(C,FFI)data_state`) asl)) g) THEN
    BIGPAUX_ASM_REWRITE_TAC [`wl_state_code (t3:(A,C,FFI)wl_state) = wl_state_code (t:(A,C,FFI)wl_state)`]
      [option_le_def; ALL] THEN
    BIGPAUX_T2_STORE_TAC THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
     [BIGPAUX_ASM_REWRITE_TAC [`data_state_code (s0:(C,FFI)data_state) = data_state_code (s:(C,FFI)data_state)`] [] THEN
      FIRST_ASSUM(MP_TAC o check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN SIMP_TAC[];
      FIRST_ASSUM(MP_TAC o check (fun th -> mp4_is_app "code_oracle_rel" (concl th) &&
        free_in `s9:(A,C,FFI)wl_state` (concl th))) THEN
      REWRITE_TAC[code_oracle_rel_def] THEN BIGPAUX_T2_STORE_TAC THEN SIMP_TAC[];
      MATCH_MP_TAC BIGPAUX_stack_max_le THEN
      MAP_EVERY EXISTS_TAC [`data_state_locals_size (s0:(C,FFI)data_state)`;
        `[0,wl_Loc l1 l2:A word_loc]`; `wl_state_stack_max (t10:(A,C,FFI)wl_state)`;
        `lookup Bignum_location (data_state_stack_frame_sizes (s0:(C,FFI)data_state))`] THEN
      MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t3:(A,C,FFI)wl_state)` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "t3" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; option_le_refl];
        FIRST_ASSUM ACCEPT_TAC];
      CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[inter_LN; join_env_def; toAList_def; foldi_def; FILTER; MAP; APPEND;
                  APPEND_NIL] THEN
      BIGPAUX_MP_ASM_TAC `Globals IN FDOM (wl_state_store (s9:(A,C,FFI)wl_state))`
        [`Globals IN FDOM (wl_state_store (s9:(A,C,FFI)wl_state))`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `wl_Word (word 0:A word) = wl_Word (Smallnum (&0))` SUBST1_TAC THENL
       [REWRITE_TAC[data_to_word_Smallnum_def; INT_LT_REFL; INT_MUL_RZERO; NUM_OF_INT_OF_NUM];
        ALL_TAC] THEN
      MATCH_MP_TAC IMP_memory_rel_Number THEN
      BIGPAUX_ASM_REWRITE_TAC [`good_dimindex(:A)`] [] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC small_int_0 THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[memory_rel_def] THEN
      MAP_EVERY EXISTS_TAC
        [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
         `limit:num`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC BIGPAUX_heap_in_memory_store_change THEN
        MAP_EVERY EXISTS_TAC [`wl_state_store (s9:(A,C,FFI)wl_state)`;
          `wl_state_memory (s9:(A,C,FFI)wl_state)`; `wl_state_mdomain (s9:(A,C,FFI)wl_state)`;
          `curr:A word`; `other:A word`] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[heap_in_memory_store_def] THEN
          REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
          MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN
          REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
          BIGPAUX_ASM_REWRITE_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list =
             APPEND ha (CONS (Unused ((il + jl + 1) + k)) hb)`] [] THEN
          FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          BIGPAUX_ASM_REWRITE_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list =
             APPEND ha (CONS (Unused ((il + jl + 1) + k)) hb)`] [] THEN
          MATCH_MP_TAC BIGPAUX_heap_recomp THEN
          MAP_EVERY EXISTS_TAC [`wl_Word a3:A word_loc`;
            `MAP wl_Word (APPEND (SND (i2mw v:bool#(A word)list)) zs1):(A word_loc)list`;
            `wl_Word b3:A word_loc`] THEN
          BIGPAUX_ASM_REWRITE_TAC [`~(limit = 0)`;
            `LENGTH (APPEND (SND (i2mw v:bool#(A word)list)) zs1) = il + jl + 1`] [LENGTH_MAP] THEN
          MP4AUX_SEP_AC_TAC];
        FIRST_ASSUM(fun th -> if mp4_is_app "word_ml_inv" (concl th) then MP_TAC th else NO_TAC) THEN
        MATCH_MP_TAC word_ml_inv_rearrange THEN
        REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        BIGPAUX_ASM_REWRITE_TAC [`data_state_space (s0:(C,FFI)data_state) = il + jl + 2`;
          `data_state_space (s0:(C,FFI)data_state) <= sp`] [] THEN
        FIRST_ASSUM(let qtm = `data_state_space (s0:(C,FFI)data_state) <= sp` in fun th -> if concl th = qtm
          then MP_TAC th else NO_TAC) THEN
        BIGPAUX_ASM_REWRITE_TAC [`data_state_space (s0:(C,FFI)data_state) = il + jl + 2`] []]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `FLOOKUP (wl_state_store (t5:(A,C,FFI)wl_state)) (Temp (word 10)) =
       SOME (wl_Word (mc_header (i2mw v:bool#(A word)list))) /\
     wl_state_locals t5 = insert 1 (wl_Loc AnyArith_location 3) (insert 0 (wl_Loc l1 l2) LN)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t5" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    BIGPAUX_ASM_REWRITE_TAC [`FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) (Temp (word 10)) =
       SOME (wl_Word (mc_header (i2mw v:bool#(A word)list)))`] []; ALL_TAC] THEN
  BIGPAUX_SEQ_STEP_TAC [] THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN BIGPAUX_EVAL_TAC []) THEN
  (ASM_CASES_TAC `v:int = &0` THENL
   [REWRITE_TAC[EQT_INTRO (ASSUME `v:int = &0`)] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
    SUBGOAL_THEN `mc_header (i2mw v:bool#(A word)list) = word 0` ASSUME_TAC THENL
     [BIGPAUX_ASM_REWRITE_TAC [`mc_header (i2mw v:bool#(A word)list) = word 0 <=> v = &0`;
        `v:int = &0`] []; ALL_TAC] THEN
    W(fun (asl,w) -> let (_,bod) = strip_exists w in
       let (eqs,_) = dest_conj bod in
       let (e1,e2) = dest_conj eqs in
       MAP_EVERY EXISTS_TAC [lhs e1; lhs e2; `wl_state_clock (t2:(A,C,FFI)wl_state)`]) THEN
    REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"] THEN
    EXISTS_TAC `wl_Word (mc_header (i2mw v:bool#(A word)list)):A word_loc` THEN
    REWRITE_TAC[] THEN
    BIGPAUX_ASM_REWRITE_TAC [`mc_header (i2mw v:bool#(A word)list) = word 0`; `v:int = &0`] [] THEN
    FIRST_ASSUM(fun th -> if mp4_is_app "data_to_word_gcProof_state_rel" (concl th) &&
        free_in `t2:(A,C,FFI)wl_state` (concl th)
      then BIGPAUX_ARGS_MATCH_TAC
        (TRY (EXPAND_TAC "t5") THEN
         REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds;
           wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM])
        (MATCH_MP state_rel_with_clock_0 th) else NO_TAC);
    ALL_TAC]) THEN
  (REWRITE_TAC[EQF_INTRO (ASSUME `~(v:int = &0)`)] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN
  BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (data_to_word_list_Seq (CONS (wl_Assign 3 ee) rest), t6:(A,C,FFI)wl_state)`
    `t6:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `?d1 ds. SND (i2mw v:bool#(A word)list) = CONS d1 ds` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `SND (i2mw v:bool#(A word)list)` list_CASES) THEN
    REWRITE_TAC[SND_i2mw_NIL; ASSUME `~(v:int = &0)`] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (wl_state_store (t6:(A,C,FFI)wl_state)) NextFree =
       SOME (wl_Word (word_add curr (word_mul bytes_in_word (word (heap_length
        (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))) /\
     FLOOKUP (wl_state_store t6) CurrHeap = SOME (wl_Word curr) /\
     wl_state_memory t6 = wl_state_memory (t2:(A,C,FFI)wl_state) /\
     wl_state_mdomain t6 = wl_state_mdomain t2 /\
     wl_state_store t6 = wl_state_store t2 /\
     wl_state_locals t6 = insert 1 (wl_Word (mc_header (i2mw v:bool#(A word)list)))
       (insert 1 (wl_Loc AnyArith_location 3) (insert 0 (wl_Loc l1 l2) LN))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t6" THEN EXPAND_TAC "t5" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    BIGPAUX_ASM_REWRITE_TAC [
      `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) NextFree =
       FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) NextFree`;
      `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) CurrHeap =
       FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap`;
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) NextFree =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a))))`;
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr)`;
      `a = heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`] [];
    ALL_TAC]) THEN
  (FIRST_ASSUM(fun th -> if mp4_is_fun2set_asm (concl th) &&
      free_in `zs1:(A word)list` (concl th) &&
      free_in `t2:(A,C,FFI)wl_state` (concl th) then
      FIRST_ASSUM(let qtm = `SND (i2mw v:bool#(A word)list) = CONS d1 ds` in fun eq -> if concl eq = qtm then
        let th' = REWRITE_RULE[eq; APPEND; MAP; misc_word_list_def] th in
        ASSUME_TAC th' THEN
        MAP_EVERY ASSUME_TAC (flat (map CONJUNCTS (MP4AUX_SEP_READS th')))
      else NO_TAC) else NO_TAC) THEN
  BIGPAUX_SEQ_STEP_TAC []) THEN
  (BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (data_to_word_list_Seq (CONS ifs rest), t7:(A,C,FFI)wl_state)`
    `t7:(A,C,FFI)wl_state`) THEN
  ((fun g -> MP_TAC(MATCH_MP BIGPAUX_SHIFT3_FACTS
     (hd (BIGPAUX_ASMS [`good_dimindex(:A)`] g))) g) THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_locals (t7:(A,C,FFI)wl_state) =
       insert 3 (wl_Word d1) (insert 1 (wl_Word (mc_header (i2mw v:bool#(A word)list)))
         (insert 1 (wl_Loc AnyArith_location 3) (insert 0 (wl_Loc l1 l2) LN))) /\
     wl_state_store t7 = wl_state_store (t2:(A,C,FFI)wl_state) /\
     wl_state_memory t7 = wl_state_memory t2 /\
     wl_state_mdomain t7 = wl_state_mdomain t2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t7" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    BIGPAUX_ASM_REWRITE_TAC [
      `wl_state_store (t6:(A,C,FFI)wl_state) = wl_state_store (t2:(A,C,FFI)wl_state)`;
      `wl_state_memory (t6:(A,C,FFI)wl_state) = wl_state_memory (t2:(A,C,FFI)wl_state)`;
      `wl_state_mdomain (t6:(A,C,FFI)wl_state) = wl_state_mdomain (t2:(A,C,FFI)wl_state)`;
      `wl_state_locals (t6:(A,C,FFI)wl_state) =
       insert 1 (wl_Word (mc_header (i2mw v:bool#(A word)list)))
       (insert 1 (wl_Loc AnyArith_location 3) (insert 0 (wl_Loc l1 l2) LN))`] [];
    ALL_TAC]) THEN
  (ASM_CASES_TAC `small_int (:A) v` THENL
   [ASM_CASES_TAC `(v:int) < &0` THENL
     [(fun g -> ASSUME_TAC(MATCH_MP BIGPAUX_WORD_3_NE_2
         (hd (BIGPAUX_ASMS [`good_dimindex(:A)`] g))) g) THEN
      SUBGOAL_THEN `~(mc_header (i2mw v:bool#(A word)list) = word 2) /\
          mc_header (i2mw v:bool#(A word)list) = word 3 /\
          word_ushr (word_sub d1 (word 1)) (dimindex(:A) - 3) = word 0 /\
          word_sub (word 0) (word_shl d1 2) = Smallnum v:A word`
        STRIP_ASSUME_TAC THENL
       [BIGPAUX_SMALL_I2MW_TAC THEN
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ASSUME `(v:int) < &0`] o check ((=) `i2mw v = ((v < &0),[d1]):bool#(A word)list` o concl)) THEN DISCH_TAC THEN
        (fun g -> MP_TAC(MATCH_MP BIGPAUX_digit_neg (CONJ (hd (BIGPAUX_ASMS [`good_dimindex(:A)`] g))
           (hd (BIGPAUX_ASMS [`i2mw v = (T,[d1]):bool#(A word)list`] g)))) g) THEN
        BIGPAUX_ASM_REWRITE_TAC [`small_int (:A) v`;
          `mc_header (i2mw v:bool#(A word)list) = word 2 <=> ?v1. i2mw v = (F,[v1]:(A word)list)`;
          `mc_header (i2mw v:bool#(A word)list) = word 3 <=> ?v1. i2mw v = (T,[v1]:(A word)list)`;
          `i2mw v = (T,[d1]):bool#(A word)list`] [PAIR_EQ] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN
      BIGPAUX_EVAL_THMS_TAC [] [word_sh_def] THEN
      (fun g -> BIGPAUX_RESULT_FINISH_TAC `wl_Word (Smallnum v):A word_loc`
        (fun th -> MATCH_MP state_rel_Number_small_int
           (CONJ th (hd (BIGPAUX_ASMS [`small_int (:A) v`] g)))) g);
      SUBGOAL_THEN `mc_header (i2mw v:bool#(A word)list) = word 2 /\
          word_ushr d1 (dimindex(:A) - 3) = word 0 /\ word_shl d1 2 = Smallnum v:A word`
        STRIP_ASSUME_TAC THENL
       [BIGPAUX_SMALL_I2MW_TAC THEN
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ASSUME `~((v:int) < &0)`] o check ((=) `i2mw v = ((v < &0),[d1]):bool#(A word)list` o concl)) THEN DISCH_TAC THEN
        (fun g -> MP_TAC(MATCH_MP BIGPAUX_digit_pos (CONJ (hd (BIGPAUX_ASMS [`good_dimindex(:A)`] g))
           (hd (BIGPAUX_ASMS [`i2mw v = (F,[d1]):bool#(A word)list`] g)))) g) THEN
        BIGPAUX_ASM_REWRITE_TAC [`small_int (:A) v`;
          `mc_header (i2mw v:bool#(A word)list) = word 2 <=> ?v1. i2mw v = (F,[v1]:(A word)list)`] [] THEN
        STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        EXISTS_TAC `d1:A word` THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN
      BIGPAUX_EVAL_THMS_TAC [] [word_sh_def] THEN
      (fun g -> BIGPAUX_RESULT_FINISH_TAC `wl_Word (Smallnum v):A word_loc`
        (fun th -> MATCH_MP state_rel_Number_small_int
           (CONJ th (hd (BIGPAUX_ASMS [`small_int (:A) v`] g)))) g)]; ALL_TAC]) THEN
  ((fun (asl,w as g) ->
    let seqtm = find_term (fun t -> mp4_is_app "data_to_word_list_Seq" t) w in
    let ifs = hd (dest_list (rand seqtm)) in
    let stmt = subst [ifs, `ifs_var:(A)wl_prog`]
      `?w5. wl_evaluate (ifs_var, t7:(A,C,FFI)wl_state) = (NONE, wl_set_var 5 w5 t7)` in
    (SUBGOAL_THEN stmt STRIP_ASSUME_TAC THENL
      [(fun g -> ASSUME_TAC(MATCH_MP BIGPAUX_WORD_3_NE_2
         (hd (BIGPAUX_ASMS [`good_dimindex(:A)`] g))) g) THEN
       ASM_CASES_TAC `?v1. i2mw v = (F,[v1]):bool#(A word)list` THENL
        [SUBGOAL_THEN `mc_header (i2mw v:bool#(A word)list) = word 2 /\
            ~(word_ushr (d1:A word) (dimindex(:A) - 3) = word 0)` STRIP_ASSUME_TAC THENL
          [FIRST_X_ASSUM(X_CHOOSE_TAC `e1:A word` o check (fun th -> is_exists (concl th) &&
             free_in `F` (concl th))) THEN
           SUBGOAL_THEN `i2mw v = (F,[d1]):bool#(A word)list` ASSUME_TAC THENL
            [FIRST_ASSUM(let qtm = `SND (i2mw v:bool#(A word)list) = CONS d1 ds` in fun th -> if concl th = qtm
               then MP_TAC th else NO_TAC) THEN
             BIGPAUX_ASM_REWRITE_TAC [`i2mw v = (F,[e1]):bool#(A word)list`] [SND; CONS_11] THEN
             MESON_TAC[]; ALL_TAC] THEN
           (fun g -> MP_TAC(MATCH_MP BIGPAUX_digit_pos (CONJ (hd (BIGPAUX_ASMS [`good_dimindex(:A)`] g))
              (hd (BIGPAUX_ASMS [`i2mw v = (F,[d1]):bool#(A word)list`] g)))) g) THEN
           BIGPAUX_ASM_REWRITE_TAC [`~small_int (:A) v`;
             `mc_header (i2mw v:bool#(A word)list) = word 2 <=> ?v1. i2mw v = (F,[v1]:(A word)list)`] [] THEN
           STRIP_TAC THEN CONJ_TAC THENL
            [EXISTS_TAC `d1:A word` THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
           ALL_TAC] THEN
         BIGPAUX_EVAL_THMS_TAC [] [word_sh_def] THEN MESON_TAC[];
         SUBGOAL_THEN `~(mc_header (i2mw v:bool#(A word)list) = word 2)` ASSUME_TAC THENL
          [BIGPAUX_ASM_REWRITE_TAC [
             `mc_header (i2mw v:bool#(A word)list) = word 2 <=> ?v1. i2mw v = (F,[v1]:(A word)list)`;
             `~(?v1. i2mw v = (F,[v1]):bool#(A word)list)`] [];
           ALL_TAC] THEN
         ASM_CASES_TAC `?v1. i2mw v = (T,[v1]):bool#(A word)list` THENL
          [SUBGOAL_THEN `mc_header (i2mw v:bool#(A word)list) = word 3 /\
              ~(word_ushr (word_sub (d1:A word) (word 1)) (dimindex(:A) - 3) = word 0)`
              STRIP_ASSUME_TAC THENL
            [FIRST_X_ASSUM(X_CHOOSE_TAC `e1:A word` o check (fun th -> is_exists (concl th) &&
               free_in `T` (concl th))) THEN
             SUBGOAL_THEN `i2mw v = (T,[d1]):bool#(A word)list` ASSUME_TAC THENL
              [FIRST_ASSUM(let qtm = `SND (i2mw v:bool#(A word)list) = CONS d1 ds` in fun th -> if concl th = qtm
                 then MP_TAC th else NO_TAC) THEN
               BIGPAUX_ASM_REWRITE_TAC [`i2mw v = (T,[e1]):bool#(A word)list`] [SND; CONS_11] THEN
               MESON_TAC[]; ALL_TAC] THEN
             (fun g -> MP_TAC(MATCH_MP BIGPAUX_digit_neg (CONJ (hd (BIGPAUX_ASMS [`good_dimindex(:A)`] g))
                (hd (BIGPAUX_ASMS [`i2mw v = (T,[d1]):bool#(A word)list`] g)))) g) THEN
             BIGPAUX_ASM_REWRITE_TAC [`~small_int (:A) v`;
               `mc_header (i2mw v:bool#(A word)list) = word 3 <=> ?v1. i2mw v = (T,[v1]:(A word)list)`] [] THEN
             STRIP_TAC THEN CONJ_TAC THENL
              [EXISTS_TAC `d1:A word` THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
             ALL_TAC] THEN
           BIGPAUX_EVAL_THMS_TAC [] [word_sh_def] THEN MESON_TAC[];
           SUBGOAL_THEN `~(mc_header (i2mw v:bool#(A word)list) = word 3)` ASSUME_TAC THENL
            [BIGPAUX_ASM_REWRITE_TAC [
               `mc_header (i2mw v:bool#(A word)list) = word 3 <=> ?v1. i2mw v = (T,[v1]:(A word)list)`;
               `~(?v1. i2mw v = (T,[v1]):bool#(A word)list)`] [];
             ALL_TAC] THEN
           BIGPAUX_EVAL_THMS_TAC [] [word_sh_def] THEN MESON_TAC[]]];
       ALL_TAC]) g)) THEN
  (ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  BIGPAUX_ASM_PRED_REWRITE_TAC (fun c -> is_eq c && mp4_is_app "wl_evaluate" (lhs c) &&
      free_in `t7:(A,C,FFI)wl_state` c) [] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  BIGPAUX_MATCH_ABBREV_TAC
    `wl_evaluate (data_to_word_list_Seq rest, t8:(A,C,FFI)wl_state)` `t8:(A,C,FFI)wl_state` THEN
  SUBGOAL_THEN `wl_state_locals (t8:(A,C,FFI)wl_state) =
       insert 5 w5 (insert 3 (wl_Word d1) (insert 1 (wl_Word (mc_header (i2mw v:bool#(A word)list)))
         (insert 1 (wl_Loc AnyArith_location 3) (insert 0 (wl_Loc l1 l2) LN)))) /\
     wl_state_store t8 = wl_state_store (t2:(A,C,FFI)wl_state) /\
     wl_state_memory t8 = wl_state_memory t2 /\
     wl_state_mdomain t8 = wl_state_mdomain t2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t8" THEN REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    BIGPAUX_ASM_REWRITE_TAC [
      `wl_state_store (t7:(A,C,FFI)wl_state) = wl_state_store (t2:(A,C,FFI)wl_state)`;
      `wl_state_memory (t7:(A,C,FFI)wl_state) = wl_state_memory (t2:(A,C,FFI)wl_state)`;
      `wl_state_mdomain (t7:(A,C,FFI)wl_state) = wl_state_mdomain (t2:(A,C,FFI)wl_state)`;
      `wl_state_locals (t7:(A,C,FFI)wl_state) =
       insert 3 (wl_Word d1) (insert 1 (wl_Word (mc_header (i2mw v:bool#(A word)list)))
         (insert 1 (wl_Loc AnyArith_location 3) (insert 0 (wl_Loc l1 l2) LN)))`] [];
    ALL_TAC]) THEN
  (BIGPAUX_SV_STEP_TAC THEN BIGPAUX_SV_STEP_TAC THEN BIGPAUX_SV_STEP_TAC THEN
  BIGPAUX_SV_STEP_TAC THEN BIGPAUX_SV_STEP_TAC THEN BIGPAUX_SV_STEP_TAC THEN
  BIGPAUX_SV_STEP_TAC THEN BIGPAUX_SV_STEP_TAC THEN
  ONCE_REWRITE_TAC[data_to_word_list_Seq_def] THEN
  BIGPAUX_EVAL_THMS_TAC [] [wl_mem_store_def; BIGPAUX_AND_NOT0]) THEN
  (SUBGOAL_THEN `word_ushr (mc_header (i2mw v:bool#(A word)list)) 1 =
       word (LENGTH (SND (i2mw v:bool#(A word)list))) /\
     word_and (mc_header (i2mw v:bool#(A word)list)) (word 1) = b2w (v < &0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `i2mw v:bool#(A word)list` BIGPAUX_mc_header_bits) THEN
    BIGPAUX_ASM_REWRITE_TAC [`2 * LENGTH (SND (i2mw v:bool#(A word)list)) + 1 < dimword (:A)`] [] THEN
    REWRITE_TAC[i2mw_def; FST]; ALL_TAC] THEN
  BIGPAUX_ASM_REWRITE_TAC [`word_ushr (mc_header (i2mw v:bool#(A word)list)) 1 =
       word (LENGTH (SND (i2mw v:bool#(A word)list)))`;
     `word_and (mc_header (i2mw v:bool#(A word)list)) (word 1) = b2w (v < &0)`] [] THEN
  W(fun (asl,w) -> let (_,bod) = strip_exists w in
     let (eqs,_) = dest_conj bod in
     let (e1,e2) = dest_conj eqs in
     MAP_EVERY EXISTS_TAC [lhs e1; lhs e2; `wl_state_clock (t2:(A,C,FFI)wl_state)`]) THEN
  REWRITE_TAC[option_INJ; distinctness "wl_result"; injectivity "wl_result"] THEN
  EXISTS_TAC `wl_Word (word_or (word_shl (word_sub (word_add curr (word_mul bytes_in_word
     (word (heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
     curr) (shift_length c - backend_common_word_shift (:A))) (word 1)):A word_loc` THEN
  REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `word_or (word 15) (word_or (word_shl (word (LENGTH (SND (i2mw v:bool#(A word)list))))
       (dimindex(:A) - data_to_word_config_len_size c)) (word_shl (b2w (v < &0)) 4)) =
     make_header c (word_or (word_shl (b2w (v < &0)) 2) (word 3))
       (LENGTH (SND (i2mw v:bool#(A word)list))):A word` SUBST1_TAC THENL
   [REWRITE_TAC[make_header_def; LET_DEF; LET_END_DEF; BIGPAUX_HEADER_BITS]; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add (curr:A word) (word_mul bytes_in_word (word (heap_length
       (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))))
     (word_add bytes_in_word (word_shl (word (LENGTH (SND (i2mw v:bool#(A word)list))))
       (backend_common_word_shift (:A)))) =
     word_add (word_add curr (word_mul bytes_in_word (word (heap_length ha))))
       (word_mul bytes_in_word (word (LENGTH (SND (i2mw v:bool#(A word)list)) + 1)))`
    SUBST1_TAC THENL
   [SIMP_TAC[shift_lsl; ASSUME `good_dimindex(:A)`] THEN REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `Bignum v = DataElement [] (LENGTH (SND (i2mw v:bool#(A word)list)))
       (NumTag (v < &0), MAP wl_Word (SND (i2mw v:bool#(A word)list)))` ASSUME_TAC THENL
   [REWRITE_TAC[data_to_word_memoryProof_Bignum_def; i2mw_def] THEN
    CASE_REWRITE_TAC[LET_DEF; LET_END_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (SND (i2mw v:bool#(A word)list)) < il + jl + 2 /\
     LENGTH (SND (i2mw v:bool#(A word)list)) < 2 EXP data_to_word_config_len_size c`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check ((=) `LENGTH (APPEND (SND (i2mw v:bool#(A word)list)) zs1) = il + jl + 1` o concl)) THEN
    FIRST_ASSUM(MP_TAC o check ((=) `il + jl + 1 < 2 EXP data_to_word_config_len_size c` o concl)) THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  (fun g -> ASSUME_TAC (MATCH_MP (SPECL [`c:data_to_word_config`; `(v:int) < &0`;
     `LENGTH (SND (i2mw v:bool#(A word)list))`] BIGPAUX_encode_bignum_header)
     (end_itlist CONJ (BIGPAUX_ASMS [`good_dimindex(:A)`;
        `data_to_word_config_len_size c + 7 < dimindex (:A)`;
        `LENGTH (SND (i2mw v:bool#(A word)list)) < 2 EXP data_to_word_config_len_size c`] g))) g) THEN
  FIRST_ASSUM(fun c0 -> if mp4_is_app "data_to_word_gcProof_state_rel" (concl c0) &&
      free_in `t2:(A,C,FFI)wl_state` (concl c0) then
     let th = REWRITE_RULE[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
       wl_state_INFO.ri_accfupds; K_THM] c0 in
     MP_TAC (find (fun t -> mp4_is_app "memory_rel" (concl t)) (CONJUNCTS th)) else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[inter_LN; join_env_def; toAList_def; foldi_def; FILTER; MAP; APPEND; APPEND_NIL] THEN
  DISCH_TAC THEN
  (fun g -> match BIGPAUX_ASMS [`good_dimindex(:A)`; `~small_int (:A) v`;
       `Bignum v = DataElement [] (LENGTH (SND (i2mw v:bool#(A word)list)))
       (NumTag (v < &0), MAP wl_Word (SND (i2mw v:bool#(A word)list)))`;
       `LENGTH (SND (i2mw v:bool#(A word)list)) < il + jl + 2`] g with
     [gd; ns; be; ll] ->
       FIRST_X_ASSUM(fun mr -> if mp4_is_app "memory_rel" (concl mr) then
         FIRST_ASSUM(fun enc -> if mp4_is_app "encode_header" (lhs (concl enc)) then
           MP_TAC (MATCH_MP IMP_memory_rel_bignum_alt (end_itlist CONJ [mr; gd; ns; be; ll; enc]))
         else NO_TAC) else NO_TAC) g
   | _ -> failwith "asms") THEN
  DISCH_THEN(X_CHOOSE_THEN `nxt:A word` (X_CHOOSE_THEN `cur2:A word`
    (X_CHOOSE_THEN `mm1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `nxt = word_add curr (word_mul bytes_in_word (word (heap_length
       (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))) /\
     cur2 = curr:A word` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check ((=) `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word nxt)` o concl));
      FIRST_X_ASSUM(MP_TAC o check ((=) `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word cur2)` o concl))] THEN
    BIGPAUX_ASM_REWRITE_TAC [
      `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) NextFree =
       FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) NextFree`;
      `FLOOKUP (wl_state_store (t2:(A,C,FFI)wl_state)) CurrHeap =
       FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap`;
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) NextFree =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a))))`;
      `FLOOKUP (wl_state_store (s9:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr)`;
      `a = heap_length (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`]
      [option_INJ; injectivity "word_loc"] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mm1 = (word_add curr (word_mul bytes_in_word (word (heap_length
       (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)))) =+
       wl_Word (make_header c (word_or (word_shl (b2w (v < &0)) 2) (word 3))
         (LENGTH (SND (i2mw v:bool#(A word)list)))))
       (wl_state_memory (t2:(A,C,FFI)wl_state))` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      mp4_is_app "data_to_word_memoryProof_store_list" (lhs (concl th)))) THEN
    REWRITE_TAC[MAP] THEN
    FIRST_ASSUM(fun th -> if mp4_is_fun2set_asm (concl th) &&
        free_in `zs1:(A word)list` (concl th) && free_in `t2:(A,C,FFI)wl_state` (concl th) &&
        can (find_term ((=) `SND (i2mw v:bool#(A word)list)`)) (concl th) then
      let th1 = REWRITE_RULE[MAP_APPEND; data_to_word_memoryProof_word_list_APPEND] th in
      let isone l = mp4_is_one l && fst(dest_pair(rand l)) =
         `word_add (curr:A word) (word_mul bytes_in_word (word (heap_length
           (ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))))` in
      let iswl l = mp4_is_app "misc_word_list" l &&
         rand l = `MAP wl_Word (SND (i2mw v:bool#(A word)list))` in
      let th2 = MP4AUX_STAR_FOCUS_LIST [isone; iswl] th1 in
      REWRITE_TAC[MATCH_MP BIGPAUX_store_list_header th2]
    else NO_TAC) THEN
    REWRITE_TAC[option_INJ] THEN MESON_TAC[]; ALL_TAC] THEN
  BIGPAUX_KEEP_TAC (fun c ->
      (mp4_is_app "data_to_word_gcProof_state_rel" c && free_in `t2:(A,C,FFI)wl_state` c) ||
      (mp4_is_app "memory_rel" c && can (find_term ((=) `NextFree`)) c) ||
      is_eq c && (rand c = `t8:(A,C,FFI)wl_state` || rand c = `t7:(A,C,FFI)wl_state` ||
                  rand c = `t6:(A,C,FFI)wl_state` || rand c = `t5:(A,C,FFI)wl_state`)) THEN
  EXPAND_TAC "t8" THEN EXPAND_TAC "t7" THEN EXPAND_TAC "t6" THEN EXPAND_TAC "t5" THEN
  REWRITE_TAC[wl_set_var_def; data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
    wl_state_INFO.ri_accfupds; K_THM; option_DISTINCT; lookup_def; IS_SOME_DEF] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm;
    data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM; option_DISTINCT;
    lookup_def; IS_SOME_DEF] o check (fun th -> mp4_is_app "data_to_word_gcProof_state_rel" (concl th))) THEN
  REWRITE_TAC[code_oracle_rel_NextFree; ALL; FDOM_FUPDATE; IN_INSERT; FLOOKUP_UPDATE;
    FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[inter_LN; join_env_def; toAList_def; foldi_def; FILTER; MAP; APPEND; APPEND_NIL] THEN
  FIRST_ASSUM(fun th -> if mp4_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `NextFree`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "make_ptr" with Failure _ -> false)) (concl th)
    then MP_TAC (MATCH_MP memory_rel_zero_space th) else NO_TAC) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM; MEM_APPEND; make_ptr_def] THEN MESON_TAC[]));;

(* HOL4 line 2130 *)
let MAP_FST_EQ_IMP_IS_SOME_ALOOKUP = prove
 (`!(xs:(A#B)list) (ys:(A#C)list) n.
     MAP FST xs = MAP FST ys ==> IS_SOME (ALOOKUP xs n) = IS_SOME (ALOOKUP ys n)`,
  LIST_INDUCT_TAC THEN TRY DISCH_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:(A#C)list` list_CASES) THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; ALOOKUP_DEF; IS_SOME_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2139 *)
let domain_adjust_sets = prove
 (`!kept_names:A spt. ~(domain (FST (adjust_sets kept_names)) = {})`,
  REWRITE_TAC[adjust_sets_def; FST; domain_def; NOT_INSERT_EMPTY]);;

(* HOL4 line 2145 *)
let env_to_list_domain_eq = prove
 (`!(y2:(A word_loc)spt) (t:(A,C,FFI)wl_state) l' permute (ms:(num#B)list).
     env_to_list y2 (wl_state_permute t) = (l',permute) /\
     MAP FST l' = MAP FST ms ==>
     domain (fromAList ms) = domain y2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP env_to_list_lookup_equiv) THEN
  DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; domain_fromAList; IN_SET_OF_LIST] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
     can (find_term ((=) `ms:(num#B)list`)) (concl th))) THEN
  REWRITE_TAC[GSYM IS_SOME_ALOOKUP_EQ; domain_lookup] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN CASES_ON `lookup n (y2:(A word_loc)spt)` THEN
  REWRITE_TAC[IS_SOME_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 2159 *)
let size_of_LE_append = prove
 (`!vs ys lims refs seen.
     FST (size_of lims ys refs seen) <= FST (size_of lims (APPEND vs ys) refs seen)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LE_REFL] THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ys:(data_v)list`; `lims:limits`;
     `refs:((data_v)bvl_ref)spt`; `seen:(1)spt`]) THEN
  ONCE_REWRITE_TAC[size_of_cons] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST] THEN ARITH_TAC);;

(* HOL4 line 2173 *)
let size_of_heap_LE_args = prove
 (`!vs (s:(C,FFI)data_state). size_of_heap s <= size_of_heap_args vs s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[size_of_heap_def; size_of_heap_args_def] THEN
  MP_TAC(SPECL [`vs:(data_v)list`; `stack_to_vs (s:(C,FFI)data_state)`;
                `data_state_limits (s:(C,FFI)data_state)`;
                `data_state_refs (s:(C,FFI)data_state)`; `LN:(1)spt`]
         size_of_LE_append) THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for eval_Call_Arith_max_stack_NONE and eval_Call_Arith (BIGPAUX_  *)
(* names): the evaluation of the call of an Arith stub down to the AnyArith  *)
(* body, the state relations on the way, the return and its locals           *)
(* ------------------------------------------------------------------------- *)

let BIGPAUX_t2_facts = prove
 (`!(t:(A,C,FFI)wl_state) y1 y2 n l x1 x2 ss.
     let t2 = wl_call_env [wl_Loc n l; x1; x2] ss
            (wl_push_env (y1,y2) NONE (wl_dec_clock
               (wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                 (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) t)))) in
     wl_state_locals t2 = fromList2 [wl_Loc n l; x1; x2] /\
     wl_state_code t2 = wl_state_code t /\
     wl_state_stack_size t2 = wl_state_stack_size t /\
     wl_state_clock t2 = MustTerminate_limit (:A) - 1`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM; wl_push_env_const;
    wl_dec_clock_def]);;

(* the evaluation of an Assign, by the definitions *)
let BIGPAUX_ASSIGN_CONV tm =
  if (try fst(dest_const(rator tm)) = "wl_evaluate" with Failure _ -> false) &&
     (try fst(dest_const(fst(strip_comb(fst(dest_pair(rand tm)))))) = "wl_Assign"
      with Failure _ -> false)
  then (REWRITE_CONV[wl_evaluate_def; wl_word_exp_def; wl_set_var_def] THENC
        CASE_REWRITE_CONV[]) tm
  else failwith "BIGPAUX_ASSIGN_CONV";;

let BIGPAUX_Arith_code_eval = prove
 (CASE_TERM
  `!c index (t2:(A,C,FFI)wl_state) a b d.
     wl_state_locals t2 = fromList2 [a; b; d] /\
     lookup AnyArith_location (wl_state_code t2) = SOME (4,AnyArith_code c) /\
     ~(wl_state_clock t2 = 0) ==>
     wl_evaluate (Arith_code index, t2) =
     (match wl_evaluate (AnyArith_code c,
        wl_call_env [a; b; d; wl_Word (word (4 * index))]
          (lookup AnyArith_location (wl_state_stack_size t2))
          (wl_dec_clock (wl_set_var 6 (wl_Word (word (4 * index))) t2))) with
       (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[data_to_word_bignumProof_Arith_code_def] THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGPAUX_ASSIGN_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  REWRITE_TAC[wl_get_vars_def; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
  ASM_REWRITE_TAC[lookup_fromList2; lookup_fromList] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CASE_REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[LENGTH; wl_set_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

let BIGPAUX_MustTerminate_limit_GE2 = prove
 (`~(MustTerminate_limit (:A) = 0) /\ ~(MustTerminate_limit (:A) - 1 = 0)`,
  REWRITE_TAC[MustTerminate_limit_DEF] THEN
  MP_TAC(INST_TYPE [`:A`,`:N`] ZERO_LT_dimword) THEN ARITH_TAC);;

let BIGPAUX_arith_call_eval = prove
 (`!c index (t:(A,C,FFI)wl_state) a1 a2 x1 x2 (names:(1)spt) n l y1 y2 t2 t4 r4 s4.
     ~(wl_state_termdep t = 0) /\
     wl_get_vars [adjust_var a1; adjust_var a2] t = SOME [x1; x2] /\
     lookup (Arith_location index) (wl_state_code t) = SOME (3,Arith_code index) /\
     lookup AnyArith_location (wl_state_code t) = SOME (4,AnyArith_code c) /\
     cut_envs (adjust_sets names) (wl_state_locals t) = SOME (y1,y2) /\
     t2 = wl_call_env [wl_Loc n l; x1; x2] (lookup (Arith_location index) (wl_state_stack_size t))
            (wl_push_env (y1,y2) NONE (wl_dec_clock
               (wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                 (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) t)))) /\
     t4 = wl_call_env [wl_Loc n l; x1; x2; wl_Word (word (4 * index))]
            (lookup AnyArith_location (wl_state_stack_size t))
            (wl_dec_clock (wl_set_var 6 (wl_Word (word (4 * index))) t2)) /\
     wl_evaluate (AnyArith_code c, t4) = (r4, s4) ==>
     (r4 = SOME NotEnoughSpace ==>
      wl_evaluate (MustTerminate (wl_Call (SOME ([1],adjust_sets names,wl_Skip,n,l))
         (SOME (Arith_location index)) [adjust_var a1; adjust_var a2] NONE), t) =
      (SOME NotEnoughSpace, wl_state_clock_fupd (K (wl_state_clock t))
         (wl_state_termdep_fupd (K (wl_state_termdep t)) s4))) /\
     (!rv s5. r4 = SOME (wl_Result (wl_Loc n l) [rv]) /\ wl_pop_env s4 = SOME s5 /\
        domain (wl_state_locals s5) = domain y1 UNION domain y2 ==>
      wl_evaluate (MustTerminate (wl_Call (SOME ([1],adjust_sets names,wl_Skip,n,l))
         (SOME (Arith_location index)) [adjust_var a1; adjust_var a2] NONE), t) =
      (NONE, wl_state_clock_fupd (K (wl_state_clock t))
         (wl_state_termdep_fupd (K (wl_state_termdep t)) (wl_set_vars [1] [rv] s5))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_vars_2_IMP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `t4:(A,C,FFI)wl_state`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `t2:(A,C,FFI)wl_state`)) THEN
  MP_TAC(ISPECL [`t:(A,C,FFI)wl_state`; `y1:(A word_loc)spt`; `y2:(A word_loc)spt`; `n:num`;
    `l:num`; `x1:A word_loc`; `x2:A word_loc`;
    `lookup (Arith_location index) (wl_state_stack_size (t:(A,C,FFI)wl_state))`]
    BIGPAUX_t2_facts) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `index:num`; `t2:(A,C,FFI)wl_state`;
    `wl_Loc n l:A word_loc`; `x1:A word_loc`; `x2:A word_loc`] BIGPAUX_Arith_code_eval) THEN
  ASM_REWRITE_TAC[BIGPAUX_MustTerminate_limit_GE2] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL [DISCH_TAC; REPEAT GEN_TAC THEN STRIP_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `r4:((A)wl_result)option`)) THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC[wl_get_vars_def; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[LENGTH; domain_adjust_sets; ALL_DISTINCT; MEM; BIGPAUX_MustTerminate_limit_GE2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[wl_bad_fun_return_def; BIGPAUX_MustTerminate_limit_GE2] THEN
  CASE_REWRITE_TAC[option_DISTINCT; distinctness "wl_result"] THEN
  ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [wl_evaluate_def] THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT]);;

(* the state of the AnyArith body after the call of Arith_code: the state of *)
(* a single call_env and push_env with another stack_max                     *)
let BIGPAUX_t4_eq = prove
 (`!(t1:(A,C,FFI)wl_state) y n l x1 x2 (w:A word) ss1 ss2.
     wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
       (wl_dec_clock (wl_set_var 6 (wl_Word w)
         (wl_call_env [wl_Loc n l; x1; x2] ss1
           (wl_push_env y NONE (wl_dec_clock
             (wl_state_clock_fupd (K (MustTerminate_limit (:A))) t1)))))) =
     wl_state_stack_max_fupd
       (K (wl_state_stack_max (wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
         (wl_dec_clock (wl_set_var 6 (wl_Word w)
           (wl_call_env [wl_Loc n l; x1; x2] ss1
             (wl_push_env y NONE (wl_dec_clock
               (wl_state_clock_fupd (K (MustTerminate_limit (:A))) t1)))))))))
       (wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
         (wl_push_env y NONE (wl_dec_clock
           (wl_state_clock_fupd (K (MustTerminate_limit (:A) - 1)) t1))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
    K_o_THM; K_THM] THEN
  REWRITE_TAC[wl_push_env_with_const] THEN
  REWRITE_TAC[wl_state_component_equality; wl_call_env_def; wl_dec_clock_def; wl_set_var_def;
    wl_state_INFO.ri_accfupds; K_THM]);;

(* state_rel with the stack_max of the word state changed (bounded below)  *)
(* and the one of the data state NONE                                       *)
let BIGPAUX_state_rel_stack_max_NONE = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs m.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs /\
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t)) m ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_stack_max_fupd (K NONE) s)
       (wl_state_stack_max_fupd (K m) t) v locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
    wl_state_INFO.ri_accfupds; K_THM; option_le_def] THEN MESON_TAC[]);;

let BIGPAUX_state_rel_termdep = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs k.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     data_to_word_gcProof_state_rel c l1 l2 s (wl_state_termdep_fupd (K k) t) v locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; wl_state_INFO.ri_accfupds; K_THM]);;

let BIGPAUX_LENGTH_EQ_2 = prove
 (`!l:A list. LENGTH l = 2 ==> ?x1 x2. l = [x1;x2]`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 2)`; ARITH_RULE `SUC n = 2 <=> n = 1`] THEN
  STRUCT_CASES_TAC (ISPEC `t:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 1)`; ARITH_RULE `SUC n = 1 <=> n = 0`; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let BIGPAUX_int_op_index = prove
 (`!index i1 i2 r. data_to_word_bignumProof_int_op index i1 i2 = SOME r ==> index < 7`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_bignumProof_int_op_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN ARITH_TAC);;

let BIGPAUX_index_lt_dimword = prove
 (`!index. good_dimindex (:A) /\ index < 7 ==> index < dimword (:A) DIV 16`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let BIGPAUX_t4_stack_bound = prove
 (`!(t1:(A,C,FFI)wl_state) y n l x1 x2 (w:A word) ss1 ss2.
     option_le
       (OPTION_MAP2 (+)
         (wl_stack_size (wl_state_stack (wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
            (wl_push_env y NONE (wl_dec_clock
              (wl_state_clock_fupd (K (MustTerminate_limit (:A) - 1)) t1))))))
         (wl_state_locals_size (wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
            (wl_push_env y NONE (wl_dec_clock
              (wl_state_clock_fupd (K (MustTerminate_limit (:A) - 1)) t1))))))
       (wl_state_stack_max (wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
         (wl_dec_clock (wl_set_var 6 (wl_Word w)
           (wl_call_env [wl_Loc n l; x1; x2] ss1
             (wl_push_env y NONE (wl_dec_clock
               (wl_state_clock_fupd (K (MustTerminate_limit (:A))) t1))))))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_set_var_def; wl_state_INFO.ri_accfupds;
    K_THM; IL2AUX_push_env_none_stack] THEN
  REWRITE_TAC[option_le_X_MAX_X]);;

let BIGPAUX_toList_fromList_3 = prove
 (`!x y z:A. toList (fromList [x;y;z]) = [z;x;y]`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV (REWRITE_CONV[toList_def; fromList_def; FOLDL] THENC CASE_REWRITE_CONV[] THENC
    NUM_REDUCE_CONV THENC REPEATC (CHANGED_CONV (ONCE_REWRITE_CONV[insert_def] THENC
      NUM_REDUCE_CONV THENC CASE_REWRITE_CONV[])) THENC
    REWRITE_CONV[toListA_def] THENC CASE_REWRITE_CONV[])) THEN
  REFL_TAC);;

let BIGPAUX_size_of_Number_cons = prove
 (`!lims i xs refs (seen:num_set).
     FST (size_of lims (CONS (data_Number i) xs) refs seen) =
     FST (size_of lims xs refs seen) +
     (if small_num (limits_arch_64_bit lims) i then 0
      else bignum_size (limits_arch_64_bit lims) i)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[size_of_cons] THEN
  MP_TAC(ISPEC `size_of lims xs refs (seen:num_set)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `rs:((data_v)bvl_ref)spt#num_set`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `rs:((data_v)bvl_ref)spt#num_set` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `refs1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `seen1:num_set`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[size_of_def; FST]);;

let BIGPAUX_small_index = prove
 (`!b index. index < 7 ==> small_num b (&index)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[small_num_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE; INT_OF_NUM_LT;
    INT_LE_NEG2; INT_NEG_LE0; INT_POS; INT_LE_TRANS] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[INT_ARITH `&0 <= &n:int ==> --(&k) <= &n`; INT_POS] THEN ASM_ARITH_TAC);;

let BIGPAUX_size_of_heap_FST = prove
 (`!s:(C,FFI)data_state.
     size_of_heap s = FST (size_of (data_state_limits s) (stack_to_vs s) (data_state_refs s) LN)`,
  GEN_TAC THEN REWRITE_TAC[size_of_heap_def] THEN
  MP_TAC(ISPEC `size_of (data_state_limits (s:(C,FFI)data_state)) (stack_to_vs s)
                  (data_state_refs s) LN` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `rs:((data_v)bvl_ref)spt#num_set` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `rs:((data_v)bvl_ref)spt#num_set` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `refs1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `seen1:num_set`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[FST]);;

let BIGPAUX_NES_heap = prove
 (`!(s:(C,FFI)data_state) env i1 i2 index ss k.
     index < 7 ==>
     size_of_heap (cut_locals (fromList [one;one;one])
       (data_state_stack_max_fupd (K NONE)
         (data_call_env [data_Number i1; data_Number i2; data_Number (&index)] ss
           (data_push_env env F (data_dec_clock (data_state_clock_fupd (K k) s)))))) <=
     bignum_size (limits_arch_64_bit (data_state_limits s)) i1 +
     bignum_size (limits_arch_64_bit (data_state_limits s)) i2 +
     size_of_heap (data_state_locals_fupd (K env) s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cut_locals_def] THEN
  REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
    data_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC(ISPECL [`fromList [data_Number i1; data_Number i2; data_Number (&index)]`;
    `data_Number i1`; `data_Number i2`; `data_Number (&index)`] BIGPAUX_cut_env_3) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[lookup_fromList; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[BIGPAUX_size_of_heap_FST; stack_to_vs_def; data_state_INFO.ri_accfupds; K_THM;
    BIGPAUX_toList_fromList_3; MAP; FLAT; extract_stack_def; APPEND] THEN
  REWRITE_TAC[BIGPAUX_size_of_Number_cons; GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[BIGPAUX_small_index] THEN
  REPEAT COND_CASES_TAC THEN ARITH_TAC);;

(* the locals after the return from the AnyArith call                       *)
let BIGPAUX_pop_locals = prove
 (`!c (t0:(A,C,FFI)wl_state) y1 y2 n l x1 x2 (w:A word) ss1 ss2 v vs s4 s5.
     wl_evaluate (AnyArith_code c,
       wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
         (wl_dec_clock (wl_set_var 6 (wl_Word w)
           (wl_call_env [wl_Loc n l; x1; x2] ss1
             (wl_push_env (y1,y2) NONE (wl_dec_clock t0)))))) =
       (SOME (wl_Result v vs), s4) /\
     wl_pop_env s4 = SOME s5 ==>
     ?e. domain (fromAList e) = domain y2 /\
         wl_state_locals s5 = sptree_union (fromAList e) (fromAList (toAList y1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP IL2AUX_evaluate_stack_swap o check (IL2AUX_is_eval_eq o concl)) THEN
  REWRITE_TAC[IL2AUX_ss_thms; IL2AUX_ss_norm_def] THEN
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_set_var_def; wl_state_INFO.ri_accfupds;
    K_THM; IL2AUX_push_env_none_stack] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (t0:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:(num#(A word_loc))list` (X_CHOOSE_THEN `perm:num->num->num`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `wl_state_stack (s4:(A,C,FFI)wl_state)` (cases "list")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `f:(A)stack_frame`
    (X_CHOOSE_THEN `rest:((A)stack_frame)list` ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[s_key_eq_def] THEN
  MP_TAC(ISPEC `f:(A)stack_frame` (cases "stack_frame")) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `e0:(num#(A word_loc))list`
    (X_CHOOSE_THEN `e:(num#(A word_loc))list` (X_CHOOSE_THEN `h:(num#num#num)option`
    SUBST_ALL_TAC)))) THEN
  REWRITE_TAC[s_frame_key_eq_def2] THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_pop_env (s4:(A,C,FFI)wl_state) = SOME s5` THEN
  ASM_REWRITE_TAC[wl_pop_env_def] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `NONE = (h:(num#num#num)option)` o concl)) THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  EXISTS_TAC `e:(num#(A word_loc))list` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `toAList (y1:(A word_loc)spt)`)) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC env_to_list_domain_eq THEN
  MAP_EVERY EXISTS_TAC [`t0:(A,C,FFI)wl_state`; `l0:(num#(A word_loc))list`; `perm:num->num->num`] THEN
  ASM_REWRITE_TAC[]);;

let BIGPAUX_domain_pop = prove
 (`!c (t0:(A,C,FFI)wl_state) y1 y2 n l x1 x2 (w:A word) ss1 ss2 v vs s4 s5.
     wl_evaluate (AnyArith_code c,
       wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
         (wl_dec_clock (wl_set_var 6 (wl_Word w)
           (wl_call_env [wl_Loc n l; x1; x2] ss1
             (wl_push_env (y1,y2) NONE (wl_dec_clock t0)))))) =
       (SOME (wl_Result v vs), s4) /\
     wl_pop_env s4 = SOME s5 ==>
     domain (wl_state_locals s5) = domain y1 UNION domain y2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BIGPAUX_pop_locals) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(num#(A word_loc))list` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[domain_union; domain_fromAList_toAList] THEN
  REWRITE_TAC[UNION_COMM]);;

(* the return location of the caller after the return from the AnyArith call *)
let BIGPAUX_lookup0_pop = prove
 (`!c (t0:(A,C,FFI)wl_state) y1 y2 n l x1 x2 (w:A word) ss1 ss2 v vs s4 s5
    (names:(1)spt) L w0.
     wl_evaluate (AnyArith_code c,
       wl_call_env [wl_Loc n l; x1; x2; wl_Word w] ss2
         (wl_dec_clock (wl_set_var 6 (wl_Word w)
           (wl_call_env [wl_Loc n l; x1; x2] ss1
             (wl_push_env (y1,y2) NONE (wl_dec_clock t0)))))) =
       (SOME (wl_Result v vs), s4) /\
     wl_pop_env s4 = SOME s5 /\
     cut_envs (adjust_sets names) L = SOME (y1,y2) /\ lookup 0 L = SOME w0 ==>
     lookup 0 (wl_state_locals s5) = SOME w0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `t0:(A,C,FFI)wl_state`; `y1:(A word_loc)spt`;
    `y2:(A word_loc)spt`; `n:num`; `l:num`; `x1:A word_loc`; `x2:A word_loc`; `w:A word`;
    `ss1:num option`; `ss2:num option`; `v:A word_loc`; `vs:(A word_loc)list`;
    `s4:(A,C,FFI)wl_state`; `s5:(A,C,FFI)wl_state`] BIGPAUX_pop_locals) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(num#(A word_loc))list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `cut_envs (adjust_sets (names:(1)spt)) (L:(A word_loc)spt) = SOME (y1,y2)` THEN
  ASM_REWRITE_TAC[cut_envs_def; cut_names_def; adjust_sets_def] THEN
  REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[lookup_union; lookup_fromAList_toAList; lookup_inter_alt] THEN
  SUBGOAL_THEN `lookup 0 (fromAList (e:(num#(A word_loc))list)) = NONE` SUBST1_TAC THENL
   [REWRITE_TAC[lookup_NONE_domain] THEN ASM_REWRITE_TAC[domain_inter; IN_INTER] THEN
    REWRITE_TAC[adjust_set_def; domain_fromAList; MAP_MAP_o; IN_SET_OF_LIST; MEM_MAP; o_DEF] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; adjust_var_def] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[domain_def; IN_INSERT] THEN CASE_REWRITE_TAC[]);;

let BIGPAUX_memory_rel_insert = prove
 (`!c be ts refs st (m:A word -> A word_loc) dm d l (w:A word_loc) x dest g xs.
     memory_rel c be ts refs 0 st m dm
       (APPEND (APPEND (APPEND [(x,w)] (join_env d (toAList (sptree_inter l (adjust_set d))))) [g]) xs) ==>
     memory_rel c be ts refs 0 st m dm
       (APPEND (APPEND (APPEND []
          (join_env (insert dest x d)
            (toAList (sptree_inter (insert (adjust_var dest) w (insert 1 w l))
                            (adjust_set (insert dest x d)))))) [g]) xs)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[inter_insert_ODD_adjust_set; ARITH_RULE `ODD 1`] THEN
  REWRITE_TAC[memory_rel_def; GSYM APPEND_ASSOC; APPEND] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MESON_TAC[REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] word_ml_inv_insert]);;

let BIGPAUX_final_state_rel = prove
 (CASE_TERM
  `!c l1 l2 (D6:(C,FFI)data_state) (s5:(A,C,FFI)wl_state) r rv locs (x:(C,FFI)data_state)
    dest kc kt.
     data_to_word_gcProof_state_rel c l1 l2 D6 s5 (SOME [(data_Number r, rv)]) locs /\
     lookup 0 (wl_state_locals s5) = SOME (wl_Loc l1 l2) /\
     data_state_ffi x = data_state_ffi D6 /\ data_state_handler x = data_state_handler D6 /\
     data_state_code x = data_state_code D6 /\ data_state_compile x = data_state_compile D6 /\
     data_state_compile_oracle x = data_state_compile_oracle D6 /\
     data_state_tstamps x = data_state_tstamps D6 /\
     data_state_locals x = data_state_locals D6 /\ data_state_stack x = data_state_stack D6 /\
     data_state_stack_frame_sizes x = data_state_stack_frame_sizes D6 /\
     data_state_locals_size x = data_state_locals_size D6 /\
     data_state_limits x = data_state_limits D6 /\ data_state_refs x = data_state_refs D6 /\
     data_state_global x = data_state_global D6 /\ data_state_space D6 = 0 /\
     kc = data_state_clock x ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K (insert dest (data_Number r) (data_state_locals x)))
          (data_state_space_fupd (K 0) (data_state_stack_max_fupd (K NONE) x)))
       (wl_set_vars [adjust_var dest] [rv]
          (wl_state_clock_fupd (K kc) (wl_state_termdep_fupd (K kt) (wl_set_vars [1] [rv] s5))))
       NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN
  REWRITE_TAC[wl_set_vars_def; alist_insert_def; wl_state_INFO.ri_accfupds;
    data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[option_le_def; option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lookup_insert; adjust_var_def; ARITH_RULE `~(0 = 2 * n + 2) /\ ~(0 = 1)`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[lookup_insert] THEN
    ASM_CASES_TAC `k:num = dest` THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
    REWRITE_TAC[adjust_var_def; ARITH_RULE `(2 * k + 2 = 2 * d + 2 <=> k = d) /\ ~(2 * k + 2 = 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
    REWRITE_TAC[adjust_var_def];
    MATCH_MP_TAC BIGPAUX_memory_rel_insert THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "memory_rel" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

let BIGPAUX_Move_eval = prove
 (`!dest (rv:A word_loc) (s:(A,C,FFI)wl_state).
     lookup 1 (wl_state_locals s) = SOME rv ==>
     wl_evaluate (wl_Move 2 [(adjust_var dest,1)], s) =
     (NONE, wl_set_vars [adjust_var dest] [rv] s)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; wl_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* terms used in the proof of eval_Call_Arith_max_stack_NONE *)
let bigpaux_ecan_sr0 = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
  (t:(A,C,FFI)wl_state) NONE locs`;;
let bigpaux_ecan_s4 = `data_state_stack_max_fupd (K NONE)
        (data_call_env [data_Number i1; data_Number i2; data_Number (&index)]
          (lookup AnyArith_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
          (data_push_env env F (data_dec_clock
             (data_state_clock_fupd (K (MustTerminate_limit (:A) - 1)) (s:(C,FFI)data_state)))))`;;
let BIGPAUX_S4_FIELDS_TAC : tactic =
  REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
    data_state_INFO.ri_accfupds; K_THM];;
let bigpaux_ecan_t0 = `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
             (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state))`;;
let bigpaux_ecan_popargs = [`c:data_to_word_config`; bigpaux_ecan_t0; `y1:(A word_loc)spt`;
    `y2:(A word_loc)spt`;
    `n:num`; `l:num`; `x1:A word_loc`; `x2:A word_loc`; `word (4 * index):A word`;
    `lookup (Arith_location index) (wl_state_stack_size (t:(A,C,FFI)wl_state))`;
    `lookup AnyArith_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`;
    `wl_Loc n l:A word_loc`; `[rv:A word_loc]`; `s4:(A,C,FFI)wl_state`; `t5:(A,C,FFI)wl_state`];;
let bigpaux_ecan_x5 = `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state)))
    (wl_state_termdep_fupd (K (wl_state_termdep t))
      (wl_set_vars [1] [rv:A word_loc] (t5:(A,C,FFI)wl_state)))`;;

(* the proof of eval_Call_Arith_max_stack_NONE, with bound_tac proving the *)
(* stack_max bound of BIGPAUX_eval_Call_Arith_lemma in both cases of the   *)
(* result of the AnyArith call when strong                                  *)
let BIGPAUX_ECAN_STEPS_TAC (bound_tac:tactic) (strong:bool) : tactic =
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP evaluate_GiveUp) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `names:(1)spt` SUBST_ALL_TAC)
    (ISPEC `names_opt:((1)spt)option` (cases "option")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_cut_IMP o CONJ
    (ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp4_is_app "data_cut_state_opt" (lhs (concl th)))) THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC(IL2AUX_clock_case_eqs @ [option_INJ; option_DISTINCT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `env:(data_v)spt` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[data_to_word_get_names_def]) THEN
  (FIRST_ASSUM(MP_TAC o SPECL [`[a1;a2]:num list`; `[data_Number i1; data_Number i2]`] o
    MATCH_MP state_rel_get_vars_IMP o check (fun th -> concl th = bigpaux_ecan_sr0)) THEN
  ASM_REWRITE_TAC[MAP; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o MATCH_MP BIGPAUX_LENGTH_EQ_2 o SYM))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:A word_loc` (X_CHOOSE_THEN `x2:A word_loc` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:(1)spt`; `env:(data_v)spt`]
    cut_env_IMP_cut_env) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (MP_TAC o MATCH_MP cut_env_IMP_cut_envs)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP lookup_Arith_location o CONJ (ASSUME bigpaux_ecan_sr0) o
    check (fun th -> mp4_is_app "data_to_word_bignumProof_int_op" (lhs (concl th)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP lookup_RefByte_location o check (fun th -> concl th = bigpaux_ecan_sr0)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BIGPAUX_int_op_index o
    check (fun th -> mp4_is_app "data_to_word_bignumProof_int_op" (lhs (concl th)))) THEN
  SUBGOAL_THEN `good_dimindex (:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  SUBGOAL_THEN `index < dimword (:A) DIV 16` ASSUME_TAC THENL
   [MATCH_MP_TAC BIGPAUX_index_lt_dimword THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP get_vars_2_IMP o
    check (fun th -> mp4_is_app "wl_get_vars" (lhs (concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ABBREV_TAC `t2 = wl_call_env [wl_Loc n l; x1; x2]
     (lookup (Arith_location index) (wl_state_stack_size (t:(A,C,FFI)wl_state)))
     (wl_push_env (y1,y2) NONE (wl_dec_clock (wl_state_clock_fupd (K (MustTerminate_limit (:A)))
        (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) t))))` THEN
  ABBREV_TAC `t4 = wl_call_env [wl_Loc n l; x1:A word_loc; x2; wl_Word (word (4 * index))]
     (lookup AnyArith_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
     (wl_dec_clock (wl_set_var 6 (wl_Word (word (4 * index))) (t2:(A,C,FFI)wl_state)))` THEN
  MP_TAC(ISPEC `wl_evaluate (AnyArith_code c, t4:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r4:((A)wl_result)option` (X_CHOOSE_TAC `s4:(A,C,FFI)wl_state`)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `index:num`; `t:(A,C,FFI)wl_state`; `a1:num`; `a2:num`;
    `x1:A word_loc`; `x2:A word_loc`; `names:(1)spt`; `n:num`; `l:num`; `y1:(A word_loc)spt`;
    `y2:(A word_loc)spt`; `t2:(A,C,FFI)wl_state`; `t4:(A,C,FFI)wl_state`;
    `r4:((A)wl_result)option`; `s4:(A,C,FFI)wl_state`] BIGPAUX_arith_call_eval) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `1 < wl_state_termdep (t:(A,C,FFI)wl_state)` THEN ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "evNES") (LABEL_TAC "evRES"))]) THEN
  (SUBGOAL_THEN
   `data_to_word_gcProof_state_rel c n l
      (data_state_stack_max_fupd (K NONE)
        (data_call_env [data_Number i1; data_Number i2; data_Number (&index)]
          (lookup AnyArith_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
          (data_push_env env F (data_dec_clock
             (data_state_clock_fupd (K (MustTerminate_limit (:A) - 1)) (s:(C,FFI)data_state))))))
      (t4:(A,C,FFI)wl_state) NONE (CONS (l1,l2) locs)`
   ASSUME_TAC THENL
   [MP_TAC(SPEC `MustTerminate_limit (:A) - 1` (MATCH_MP data_to_word_gcProof_state_rel_with_clock
      (SPEC `wl_state_termdep (t:(A,C,FFI)wl_state) - 1` (MATCH_MP BIGPAUX_state_rel_termdep
        (ASSUME bigpaux_ecan_sr0))))) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`NONE:(num#(A)wl_prog#num#num)option`; `c:data_to_word_config`; `l1:num`; `l2:num`;
      `data_state_clock_fupd (K (MustTerminate_limit (:A) - 1)) (s:(C,FFI)data_state)`;
      `wl_state_clock_fupd (K (MustTerminate_limit (:A) - 1))
         (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) (t:(A,C,FFI)wl_state))`;
      `locs:(num#num)list`; `[a1;a2]:num list`; `[data_Number i1; data_Number i2]`;
      `[x1;x2]:(A word_loc)list`; `names:(1)spt`; `env:(data_v)spt`;
      `(y1,y2):(A word_loc)spt#(A word_loc)spt`; `n:num`; `l:num`;
      `lookup AnyArith_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`]
      state_rel_call_env_push_env) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; MAP; wl_get_vars_def; wl_get_var_def;
        wl_state_INFO.ri_accfupds] THEN CASE_REWRITE_TAC[];
      REWRITE_TAC[IS_SOME_DEF] THEN DISCH_TAC] THEN
    FIRST_X_ASSUM(fun th -> if mp4_is_app "data_to_word_gcProof_state_rel" (concl th) &&
        can (find_term (mp4_is_app "data_call_env")) (concl th) then
        MP_TAC(SPEC `index:num` (MATCH_MP (REWRITE_RULE[IMP_CONJ] state_rel_IMP_Number_arg) th))
      else NO_TAC) THEN
    ASM_REWRITE_TAC[LENGTH; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    SUBGOAL_THEN `t4 = wl_state_stack_max_fupd (K (wl_state_stack_max t4))
        (wl_call_env [wl_Loc n l; x1; x2; wl_Word (word (4 * index))]
          (lookup AnyArith_location (wl_state_stack_size (t:(A,C,FFI)wl_state)))
          (wl_push_env (y1,y2) NONE (wl_dec_clock
            (wl_state_clock_fupd (K (MustTerminate_limit (:A) - 1))
              (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) t)))))`
      SUBST1_TAC THENL
     [EXPAND_TAC "t4" THEN EXPAND_TAC "t2" THEN MATCH_ACCEPT_TAC BIGPAUX_t4_eq; ALL_TAC] THEN
    MATCH_MP_TAC BIGPAUX_state_rel_stack_max_NONE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "t4" THEN EXPAND_TAC "t2" THEN MATCH_ACCEPT_TAC BIGPAUX_t4_stack_bound;
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`index:num`; `i1:int`; `i2:int`; `r:int`; `t4:(A,C,FFI)wl_state`; bigpaux_ecan_s4;
    `l2:num`; `l1:num`; `CONS (l1,l2) (locs:(num#num)list)`; `l:num`; `n:num`;
    `c:data_to_word_config`] AnyArith_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[data_get_vars_def; data_get_var_def; lookup_fromList; LENGTH; EL; HD; TL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CASE_REWRITE_TAC[] THEN
    EXPAND_TAC "t4" THEN EXPAND_TAC "t2" THEN
    REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_set_var_def; wl_state_INFO.ri_accfupds;
      K_THM; wl_push_env_const; lookup_fromList2; lookup_fromList; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    UNDISCH_TAC `1 < wl_state_termdep (t:(A,C,FFI)wl_state)` THEN
    MP_TAC BIGPAUX_MustTerminate_limit_GE2 THEN ARITH_TAC;
    ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `q4:((A)wl_result)option` (X_CHOOSE_THEN `r4s:(A,C,FFI)wl_state`
    (X_CHOOSE_THEN `new_c:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN `(r4:((A)wl_result)option,s4:(A,C,FFI)wl_state) = (q4,r4s)` MP_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq (concl th) &&
       rhs (concl th) = `(r4:((A)wl_result)option,s4:(A,C,FFI)wl_state)`
     then REWRITE_TAC[SYM th] else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM))] THEN
  ASM_CASES_TAC `r4 = SOME (NotEnoughSpace:(A)wl_result)` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC; DISCH_THEN(X_CHOOSE_THEN `rv:A word_loc` STRIP_ASSUME_TAC)]) THENL
  [bound_tac THEN (REMOVE_THEN "evNES" (MP_TAC o C MP (ASSUME `r4 = SOME (NotEnoughSpace:(A)wl_result)`)) THEN
  DISCH_TAC THEN
  EXISTS_TAC `SOME (NotEnoughSpace:(A)wl_result)` THEN
  EXISTS_TAC `wl_state_clock_fupd (K (wl_state_clock (t:(A,C,FFI)wl_state)))
    (wl_state_termdep_fupd (K (wl_state_termdep t)) (s4:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[option_DISTINCT; wl_state_INFO.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `wl_state_ffi (t4:(A,C,FFI)wl_state) = wl_state_ffi (t:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL
   [EXPAND_TAC "t4" THEN EXPAND_TAC "t2" THEN
    REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_set_var_def; wl_state_INFO.ri_accfupds;
      K_THM; wl_push_env_const]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "no_thunks_in_refs")) (concl th))) THEN
  SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`data_state_limits:(C,FFI)data_state->limits`, bigpaux_ecan_s4),
                               `data_state_limits (s:(C,FFI)data_state)`),
                        mk_eq(mk_comb(`data_state_refs:(C,FFI)data_state->((data_v)bvl_ref)spt`, bigpaux_ecan_s4),
                               `data_state_refs (s:(C,FFI)data_state)`)))
    (fun th -> REWRITE_TAC[th]) THENL [BIGPAUX_S4_FIELDS_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun ih -> STRIP_TAC THEN MP_TAC (MP ih (ASSUME (lhand (concl ih))))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `env:(data_v)spt`; `i1:int`; `i2:int`; `index:num`;
    `lookup AnyArith_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`;
    `MustTerminate_limit (:A) - 1`] BIGPAUX_NES_heap) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);
   bound_tac THEN (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `x:(C,FFI)data_state`)) THEN
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if mp4_is_app "data_to_word_gcProof_state_rel" c &&
       can (find_term ((=) `SOME [(data_Number r, rv:A word_loc)]`)) c then
      let d5 = el 3 (snd (strip_comb c)) in
      let d6 = vsubst [d5, `dd5:(C,FFI)data_state`]
        `data_state_locals_fupd (K (env:(data_v)spt))
           (data_state_stack_fupd (K (data_state_stack (s:(C,FFI)data_state)))
             (data_state_locals_size_fupd (K (data_state_locals_size s)) (dd5:(C,FFI)data_state)))` in
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; d5; `s4:(A,C,FFI)wl_state`;
        `SOME [(data_Number r, rv:A word_loc)]`; `CONS (l1,l2) (locs:(num#num)list)`; d6]
        state_rel_pop_env_IMP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[data_pop_env_def] THEN BIGPAUX_S4_FIELDS_TAC THEN
        CASE_REWRITE_TAC[];
        ALL_TAC]
    else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t5:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num`
    (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    (let c = lhand (concl th) in is_eq c && (lhs c = `l1:num` || lhs c = `l2:num`))))) THEN
  RVEQ_TAC) THEN
   (FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    free_in `l8:num` (concl th) && not (mp4_is_app "data_to_word_gcProof_state_rel" (concl th)))) THEN
  RVEQ_TAC) THEN
   (MP_TAC(ISPECL bigpaux_ecan_popargs BIGPAUX_domain_pop) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l8 l9)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> let c = concl th in
      if mp4_is_app "data_to_word_gcProof_state_rel" c &&
         el 3 (snd (strip_comb c)) = `s:(C,FFI)data_state` &&
         el 4 (snd (strip_comb c)) = `t:(A,C,FFI)wl_state` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL (bigpaux_ecan_popargs @ [`names:(1)spt`; `wl_state_locals (t:(A,C,FFI)wl_state)`;
    `wl_Loc l8 l9:A word_loc`]) BIGPAUX_lookup0_pop) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REMOVE_THEN "evRES" (MP_TAC o SPECL [`rv:A word_loc`; `t5:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
   (if strong then
   (EXISTS_TAC `NONE:((A)wl_result)option` THEN
  EXISTS_TAC (vsubst [bigpaux_ecan_x5, `xx5:(A,C,FFI)wl_state`]
    `wl_set_vars [adjust_var dest] [rv:A word_loc] (xx5:(A,C,FFI)wl_state)`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[data_to_word_list_Seq_def; option_DISTINCT] THEN
  MP_TAC(ISPECL [`dest:num`; `rv:A word_loc`; bigpaux_ecan_x5] BIGPAUX_Move_eval) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_set_vars_def; alist_insert_def; wl_state_INFO.ri_accfupds; K_THM;
      lookup_insert]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [(  SUBGOAL_THEN `wl_state_clock (t:(A,C,FFI)wl_state) = data_state_clock (s:(C,FFI)data_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> let c = concl th in
      if mp4_is_app "data_to_word_gcProof_state_rel" c &&
         el 3 (snd (strip_comb c)) = `s:(C,FFI)data_state` &&
         el 4 (snd (strip_comb c)) = `t:(A,C,FFI)wl_state` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC BIGPAUX_final_state_rel THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if mp4_is_app "data_to_word_gcProof_state_rel" c &&
       el 4 (snd (strip_comb c)) = `t5:(A,C,FFI)wl_state` then
      EXISTS_TAC (el 3 (snd (strip_comb c))) THEN ASM_REWRITE_TAC[]
    else NO_TAC) THEN
  BIGPAUX_S4_FIELDS_TAC THEN ASM_REWRITE_TAC[]);
   REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const o check (fun th ->
     is_eq (concl th) && mp4_is_app "wl_pop_env" (lhs (concl th)) &&
     rand (lhs (concl th)) = `s4:(A,C,FFI)wl_state`)) THEN
   ASM_REWRITE_TAC[]])
    else
   (EXISTS_TAC `NONE:((A)wl_result)option` THEN
  EXISTS_TAC (vsubst [bigpaux_ecan_x5, `xx5:(A,C,FFI)wl_state`]
    `wl_set_vars [adjust_var dest] [rv:A word_loc] (xx5:(A,C,FFI)wl_state)`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[data_to_word_list_Seq_def; option_DISTINCT] THEN
  MP_TAC(ISPECL [`dest:num`; `rv:A word_loc`; bigpaux_ecan_x5] BIGPAUX_Move_eval) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_set_vars_def; alist_insert_def; wl_state_INFO.ri_accfupds; K_THM;
      lookup_insert]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `wl_state_clock (t:(A,C,FFI)wl_state) = data_state_clock (s:(C,FFI)data_state)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> let c = concl th in
      if mp4_is_app "data_to_word_gcProof_state_rel" c &&
         el 3 (snd (strip_comb c)) = `s:(C,FFI)data_state` &&
         el 4 (snd (strip_comb c)) = `t:(A,C,FFI)wl_state` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC BIGPAUX_final_state_rel THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if mp4_is_app "data_to_word_gcProof_state_rel" c &&
       el 4 (snd (strip_comb c)) = `t5:(A,C,FFI)wl_state` then
      EXISTS_TAC (el 3 (snd (strip_comb c))) THEN ASM_REWRITE_TAC[]
    else NO_TAC) THEN
  BIGPAUX_S4_FIELDS_TAC THEN ASM_REWRITE_TAC[]))];;

(* HOL4 line 2181 *)
let eval_Call_Arith_max_stack_NONE = prove
 (CASE_TERM
  `!index r c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names_opt a1 a2
    i1 i2 x dest n l.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     ~(names_opt = NONE) /\ 1 < wl_state_termdep t /\
     data_get_vars [a1; a2] (data_state_locals s) = SOME [data_Number i1; data_Number i2] /\
     data_cut_state_opt names_opt s = SOME x /\
     data_to_word_bignumProof_int_op index i1 i2 = SOME r ==>
     ?q r'.
       (\(res,s1).
          if res = NONE then
            wl_evaluate (data_to_word_list_Seq [wl_Move 2 [(adjust_var dest,1)]],s1)
          else (res,s1))
         (wl_evaluate
           (MustTerminate
             (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names_opt),wl_Skip,n,l))
               (SOME (Arith_location index))
               [adjust_var a1; adjust_var a2] NONE),t)) = (q,r') /\
       (q = SOME NotEnoughSpace ==>
        wl_state_ffi r' = data_state_ffi s /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) /\
         no_thunks_in_refs (data_state_refs s) ==>
         let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
           il + jl <= 2 EXP data_to_word_config_len_size c ==>
           limits_heap_limit (data_state_limits s) < 2 * il + 2 * jl + size_of_heap x)) /\
       (~(q = SOME NotEnoughSpace) ==>
        data_to_word_gcProof_state_rel c l1 l2
          (data_state_locals_fupd (K (insert dest (data_Number r) (data_state_locals x)))
             (data_state_space_fupd (K 0) (data_state_stack_max_fupd (K NONE) x)))
          r' NONE locs /\ q = NONE)`,
  BIGPAUX_ECAN_STEPS_TAC ALL_TAC false);;

(* HOL4 line 2421 *)
let EVERY_IMP_ALOOKUP = prove
 (`!(xs:(A#B)list) P. ALL P xs ==> !x y. ALOOKUP xs x = SOME y ==> P (x,y)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; ALOOKUP_DEF; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ] THEN
  ASM_MESON_TAC[PAIR]);;

(* HOL4 line 2429 *)
let structure_le_IMP_option_le = prove
 (`!l x y. structure_le x y ==> option_le (max_depth l x) (max_depth l y)`,
  GEN_TAC THEN MATCH_MP_TAC call_tree_INDUCT THEN REPEAT STRIP_TAC THEN
  CASES_ON `y:call_tree` THEN FS[structure_le_def; max_depth_def; option_le_def] THEN
  RES_TAC THEN REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN
  BIGPAUX_OPTION_CASES_TAC (fun t -> match strip_comb t with
     (c,_) -> is_const c && mem (fst(dest_const c)) ["max_depth";"lookup"]) THEN
  ASM_REWRITE_TAC[OPTION_MAP2_THM; OPTION_MAP_DEF; option_le_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_le_def]) THEN ASM_ARITH_TAC);;

(* HOL4 line 2450 (HOL4: SIMP_CONV std_ss [evaluate_def,word_exp_def,       *)
(* set_var_def] on wordSem evaluate (Assign n (Const w), s))                *)
let evaluate_Assign_Const = prove
 (`!n (w:A word) (s:(A,C,FFI)wl_state).
     wl_evaluate (wl_Assign n (wl_Const w),s) =
     (NONE,wl_state_locals_fupd (K (insert n (wl_Word w) (wl_state_locals s))) s)`,
  REWRITE_TAC[wl_evaluate_def; wl_word_exp_def; wl_set_var_def] THEN
  CASE_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for eval_Call_Arith (BIGPAUX_ names): the stack_max after the    *)
(* call, from max_depth_Call_NONE of word_depthProof                        *)
(* ------------------------------------------------------------------------- *)

let BIGPAUX_AnyArith_tail_eval = prove
 (CASE_TERM
  `!c (t2:(A,C,FFI)wl_state) a b d (w:A word).
     wl_state_locals t2 = fromList2 [a; b; d] /\
     lookup AnyArith_location (wl_state_code t2) = SOME (4,AnyArith_code c) /\
     ~(wl_state_clock t2 = 0) ==>
     wl_evaluate (wl_Call NONE (SOME AnyArith_location) [0; 2; 4; 6] NONE,
                  wl_set_var 6 (wl_Word w) t2) =
     (match wl_evaluate (AnyArith_code c,
        wl_call_env [a; b; d; wl_Word w]
          (lookup AnyArith_location (wl_state_stack_size t2))
          (wl_dec_clock (wl_set_var 6 (wl_Word w) t2))) with
       (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  REWRITE_TAC[wl_get_vars_def; wl_get_var_def; wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM;
    lookup_insert] THEN
  ASM_REWRITE_TAC[lookup_fromList2; lookup_fromList] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CASE_REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* the stack fields of the state of the AnyArith tail call *)
let BIGPAUX_t2_stack_facts = prove
 (`!(t:(A,C,FFI)wl_state) y1 y2 n l x1 x2 ss (w:A word).
     let t2' = wl_set_var 6 (wl_Word w) (wl_call_env [wl_Loc n l; x1; x2] ss
            (wl_push_env (y1,y2) NONE (wl_dec_clock
               (wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                 (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) t))))) in
     wl_state_stack_max t2' =
       OPTION_MAP2 MAX (OPTION_MAP2 MAX (wl_state_stack_max t)
         (OPTION_MAP2 (+) (wl_state_locals_size t) (wl_stack_size (wl_state_stack t))))
         (OPTION_MAP2 (+) (OPTION_MAP2 (+) (wl_state_locals_size t) (wl_stack_size (wl_state_stack t))) ss) /\
     wl_stack_size (wl_state_stack t2') =
       OPTION_MAP2 (+) (wl_state_locals_size t) (wl_stack_size (wl_state_stack t)) /\
     wl_state_stack_size t2' = wl_state_stack_size t /\
     wl_state_code t2' = wl_state_code t`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[wl_set_var_def; wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
    push_env_stack_max_eq; IL2AUX_push_env_none_stack; wl_push_env_const; stack_size_eq2;
    stack_size_frame_def; wl_dec_clock_def]);;

(* the code of the stubs is in the code of the word state *)
let BIGPAUX_code_rel_subspt = prove
 (`!c (scode:(num#data_prog)spt) (tcode:(num#(A)wl_prog)spt).
     data_to_word_gcProof_code_rel c scode tcode ==>
     subspt (fromAList (data_to_word_stubs (:A) c)) tcode`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_code_rel_def] THEN STRIP_TAC THEN
  REWRITE_TAC[subspt_lookup; lookup_fromAList] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP EVERY_IMP_ALOOKUP o check (fun th -> mp4_is_app "ALL" (concl th))) THEN
  REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* the stack_max of the data state can be raised to a bound of the word one *)
let BIGPAUX_state_rel_stack_max_some = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs ls m.
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K ls) (data_state_space_fupd (K 0)
          (data_state_stack_max_fupd (K NONE) x))) t v locs /\
     option_le (wl_state_stack_max t) m ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K ls) (data_state_space_fupd (K 0)
          (data_state_stack_max_fupd (K m) x))) t v locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let bigpaux_eca_max0 = `OPTION_MAP2 MAX (data_state_stack_max (s:(C,FFI)data_state))
            (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)))
               (OPTION_MAP2 (+) (wl_state_locals_size t)
                  (OPTION_MAP2 MAX (lookup (Arith_location index) (wl_state_stack_size t))
                     (max_depth (wl_state_stack_size t) AnyArith_call_tree))))`;;

(* the stack_max after the AnyArith call, from max_depth_Call_NONE *)
let BIGPAUX_ECA_BOUND_TAC : tactic =
  SUBGOAL_THEN (mk_comb(mk_comb(`option_le`, `wl_state_stack_max (s4:(A,C,FFI)wl_state)`),
                        bigpaux_eca_max0)) ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(A,C,FFI)wl_state`; `y1:(A word_loc)spt`; `y2:(A word_loc)spt`; `n:num`; `l:num`;
      `x1:A word_loc`; `x2:A word_loc`;
      `lookup (Arith_location index) (wl_state_stack_size (t:(A,C,FFI)wl_state))`]
      BIGPAUX_t2_facts) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `t2:(A,C,FFI)wl_state`; `wl_Loc n l:A word_loc`;
      `x1:A word_loc`; `x2:A word_loc`; `word (4 * index):A word`] BIGPAUX_AnyArith_tail_eval) THEN
    ASM_REWRITE_TAC[BIGPAUX_MustTerminate_limit_GE2] THEN
    CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`AnyArith_location`; `[0;2;4;6]:num list`;
      `wl_set_var 6 (wl_Word (word (4 * index))) (t2:(A,C,FFI)wl_state)`;
      `r4:((A)wl_result)option`; `s4:(A,C,FFI)wl_state`;
      `fromAList (data_to_word_stubs (:A) c)`] max_depth_Call_NONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[option_DISTINCT; option_INJ; distinctness "wl_result"; wl_set_var_def;
        wl_state_INFO.ri_accfupds] THEN
      MATCH_MP_TAC BIGPAUX_code_rel_subspt THEN
      EXISTS_TAC `data_state_code (s:(C,FFI)data_state)` THEN
      FIRST_ASSUM(fun th -> let cc = concl th in
        if mp4_is_app "data_to_word_gcProof_state_rel" cc &&
           el 3 (snd (strip_comb cc)) = `s:(C,FFI)data_state` &&
           el 4 (snd (strip_comb cc)) = `t:(A,C,FFI)wl_state` then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(A,C,FFI)wl_state`; `y1:(A word_loc)spt`; `y2:(A word_loc)spt`; `n:num`; `l:num`;
      `x1:A word_loc`; `x2:A word_loc`;
      `lookup (Arith_location index) (wl_state_stack_size (t:(A,C,FFI)wl_state))`;
      `word (4 * index):A word`] BIGPAUX_t2_stack_facts) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`wl_state_stack_size (t:(A,C,FFI)wl_state)`;
      `full_call_graph AnyArith_location (fromAList (data_to_word_stubs (:A) c))`;
      `AnyArith_call_tree`] structure_le_IMP_option_le) THEN
    REWRITE_TAC[AnyArith_call_tree_thm] THEN
    FIRST_ASSUM(fun th -> let cc = concl th in
      if mp4_is_app "data_to_word_gcProof_state_rel" cc &&
         el 3 (snd (strip_comb cc)) = `s:(C,FFI)data_state` &&
         el 4 (snd (strip_comb cc)) = `t:(A,C,FFI)wl_state` then
        MP_TAC (find (fun cj -> let cc = concl cj in
                   mp4_is_app "option_le" cc &&
                   lhand cc = `wl_state_stack_max (t:(A,C,FFI)wl_state)`)
                 (CONJUNCTS (REWRITE_RULE[data_to_word_gcProof_state_rel_thm] th)))
      else NO_TAC) THEN
    WDPAUX_OPT_DECIDE_TAC;
    ALL_TAC];;

(* eval_Call_Arith_max_stack_NONE with the stack_max bound of the result *)
(* state, for eval_Call_Arith                                              *)
let BIGPAUX_eval_Call_Arith_lemma = prove
 (CASE_TERM
  `!index r c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names_opt a1 a2
    i1 i2 x dest n l.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     ~(names_opt = NONE) /\ 1 < wl_state_termdep t /\
     data_get_vars [a1; a2] (data_state_locals s) = SOME [data_Number i1; data_Number i2] /\
     data_cut_state_opt names_opt s = SOME x /\
     data_to_word_bignumProof_int_op index i1 i2 = SOME r ==>
     ?q r'.
       (\(res,s1).
          if res = NONE then
            wl_evaluate (data_to_word_list_Seq [wl_Move 2 [(adjust_var dest,1)]],s1)
          else (res,s1))
         (wl_evaluate
           (MustTerminate
             (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names_opt),wl_Skip,n,l))
               (SOME (Arith_location index))
               [adjust_var a1; adjust_var a2] NONE),t)) = (q,r') /\
       (q = SOME NotEnoughSpace ==>
        wl_state_ffi r' = data_state_ffi s /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) /\
         no_thunks_in_refs (data_state_refs s) ==>
         let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
           il + jl <= 2 EXP data_to_word_config_len_size c ==>
           limits_heap_limit (data_state_limits s) < 2 * il + 2 * jl + size_of_heap x)) /\
       (~(q = SOME NotEnoughSpace) ==>
        data_to_word_gcProof_state_rel c l1 l2
          (data_state_locals_fupd (K (insert dest (data_Number r) (data_state_locals x)))
             (data_state_space_fupd (K 0) (data_state_stack_max_fupd (K NONE) x)))
          r' NONE locs /\ q = NONE) /\
       option_le (wl_state_stack_max r')
         (OPTION_MAP2 MAX (data_state_stack_max s)
            (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
               (OPTION_MAP2 (+) (wl_state_locals_size t)
                  (OPTION_MAP2 MAX (lookup (Arith_location index) (wl_state_stack_size t))
                     (max_depth (wl_state_stack_size t) AnyArith_call_tree)))))`,
  BIGPAUX_ECAN_STEPS_TAC BIGPAUX_ECA_BOUND_TAC true);;

(* HOL4 line 2455 *)
let eval_Call_Arith = prove
 (CASE_TERM
  `!index r c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names_opt a1 a2
    i1 i2 x dest n l.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     ~(names_opt = NONE) /\ 1 < wl_state_termdep t /\
     data_get_vars [a1; a2] (data_state_locals s) = SOME [data_Number i1; data_Number i2] /\
     data_cut_state_opt names_opt s = SOME x /\
     data_to_word_bignumProof_int_op index i1 i2 = SOME r ==>
     ?q r'.
       (\(res,s1).
          if res = NONE then
            wl_evaluate (data_to_word_list_Seq [wl_Move 2 [(adjust_var dest,1)]],s1)
          else (res,s1))
         (wl_evaluate
           (MustTerminate
             (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names names_opt),wl_Skip,n,l))
               (SOME (Arith_location index))
               [adjust_var a1; adjust_var a2] NONE),t)) = (q,r') /\
       let max = OPTION_MAP2 MAX (data_state_stack_max s)
                   (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                      (OPTION_MAP2 (+) (wl_state_locals_size t)
                         (OPTION_MAP2 MAX
                            (lookup (Arith_location index) (wl_state_stack_size t))
                            (max_depth (wl_state_stack_size t) AnyArith_call_tree)))) in
       option_le (wl_state_stack_max r') max /\
       (q = SOME NotEnoughSpace ==>
        wl_state_ffi r' = data_state_ffi s /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) /\
         no_thunks_in_refs (data_state_refs s) ==>
         let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
           il + jl <= 2 EXP data_to_word_config_len_size c ==>
           limits_heap_limit (data_state_limits s) <
             2 * il + 2 * jl + size_of_heap_args [data_Number i1; data_Number i2] x)) /\
       (~(q = SOME NotEnoughSpace) ==>
        data_to_word_gcProof_state_rel c l1 l2
          (data_state_locals_fupd (K (insert dest (data_Number r) (data_state_locals x)))
             (data_state_space_fupd (K 0) (data_state_stack_max_fupd (K max) x)))
          r' NONE locs /\ q = NONE)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`dest:num`; `n:num`; `l:num`] o MATCH_MP BIGPAUX_eval_Call_Arith_lemma) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `r':(A,C,FFI)wl_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`q:((A)wl_result)option`; `r':(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `q = SOME (NotEnoughSpace:(A)wl_result)`) o
      check (fun th -> is_imp (concl th) &&
        lhand (concl th) = `q = SOME (NotEnoughSpace:(A)wl_result)`)) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun ih -> DISCH_THEN(fun g1 -> DISCH_THEN(fun g2 ->
      MP_TAC (MP (MP ih g1) g2)))) THEN
    MP_TAC(ISPECL [`[data_Number i1; data_Number i2]`; `x:(C,FFI)data_state`]
      size_of_heap_LE_args) THEN
    ARITH_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `~(q = SOME (NotEnoughSpace:(A)wl_result))`) o
      check (fun th -> is_imp (concl th) &&
        lhand (concl th) = `~(q = SOME (NotEnoughSpace:(A)wl_result))`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BIGPAUX_state_rel_stack_max_some THEN ASM_REWRITE_TAC[]]);;
