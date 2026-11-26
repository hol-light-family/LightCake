(* ========================================================================= *)
(* data_to_word_assignProof_p2: part 2 of 6 (HOL4 lines 2890-5410) of the    *)
(* port of HOL4 compiler/backend/proofs/data_to_word_assignProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p6 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_assignProof.ml needs the last.                *)
(* ASP2AUX_ names are local helpers of this part; the separation-logic       *)
(* tactics MP4AUX_SEP_R_TAC, MP4AUX_SEP_WRITES, MP4AUX_STAR_AC_RULE and      *)
(* MP4AUX_SEP_AC_TAC are those of data_to_word_memoryProof_p4.               *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_assignProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 2890-5410 ===== *)

(* HOL4 line 2890 *)
let LENGTH_EQ_5 = prove
 (`!xs:A list.
     (LENGTH xs = 5 <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5]) /\
     (5 = LENGTH xs <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5])`,
  GEN_TAC THEN
  SUBGOAL_THEN `(5 = LENGTH (xs:A list)) <=> (LENGTH xs = 5)` SUBST1_TAC THENL
   [MESON_TAC[]; REWRITE_TAC[]] THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helpers of this part (asp2_ functions, ASP2AUX_ theorems and tactics).    *)
(* ------------------------------------------------------------------------- *)

(* is tm an application of the constant name? *)
let asp2_head_is name tm =
  try let f,_ = strip_comb tm in is_const f && fst(dest_const f) = name
  with Failure _ -> false;;

(* HOL4 line 2898 *)
let memory_rel_get_num = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars n a.
     memory_rel c be ts refs sp st m dm vars /\
     n < dimword (:A) DIV 8 /\ good_dimindex (:A) /\
     MEM (data_Number (&n),a:A word_loc) vars ==>
     ?w. a = wl_Word w /\ word_ushr w 2 = word n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `memory_rel c be ts refs sp st (m:A word->A word_loc) dm
                  [data_Number (&n),(a:A word_loc)]` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (asp2_head_is "memory_rel" o concl)) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN ASM_REWRITE_TAC[MEM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `small_int (:A) (&n)` ASSUME_TAC THENL
   [REWRITE_TAC[small_int_def; INT_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[INT_ARITH `--(&x) <= (&y:int)`];
    ALL_TAC] THEN
  DRULE_ALL memory_rel_Number_IMP THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `Smallnum (&n):A word` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_Smallnum_def; INT_ARITH `~(&n:int < &0)`;
              INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `4 * n < dimword (:A) /\ n < dimword (:A)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `8 * (n + 1) <= dimword (:A)` MP_TAC THENL
     [SIMP_TAC[GSYM LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* HOL4 line 2918 *)
let IN_domain_adjust_set_inter = prove
 (`!x (s1:A spt) (s2:B spt).
     x IN domain (adjust_set (sptree_inter s1 s2)) <=>
     x IN domain (adjust_set s1) /\ x IN domain (adjust_set s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_lookup] THEN
  REWRITE_TAC[lookup_adjust_set] THEN
  REWRITE_TAC[domain_inter; IN_INTER] THEN
  MAP_EVERY ASM_CASES_TAC [`ODD x \/ x = 0`; `(x - 2) DIV 2 IN domain (s1:A spt)`;
                           `(x - 2) DIV 2 IN domain (s2:B spt)`] THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 2928 *)
let get_var_to_word_exp = prove
 (`!r (s:(A,C,FFI)wl_state) w.
     wl_get_var r s = SOME (wl_Word w) ==>
     wl_word_exp s (wl_Op asm_Add [wl_Var r; wl_Const (word 0)]) =
       SOME (wl_Word (word_add w (word 0))) /\
     wl_word_exp s (wl_Op asm_Add [wl_Var r; wl_Const (word 1)]) =
       SOME (wl_Word (word_add w (word 1))) /\
     wl_word_exp s (wl_Op asm_Add [wl_Var r; wl_Const (word 2)]) =
       SOME (wl_Word (word_add w (word 2))) /\
     wl_word_exp s (wl_Op asm_Add [wl_Var r; wl_Const (word 3)]) =
       SOME (wl_Word (word_add w (word 3)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[wl_word_exp_def; MAP; the_words_def] THEN
  CAKE_REWRITE_TAC[word_op_def; ITLIST; OPTION_MAP_DEF] THEN
  REWRITE_TAC[WORD_ADD_0]);;

(* HOL4 line 2938 (local) *)
let word_exp_set = prove
 (CASE_TERM
  `!(s:(A,C,FFI)wl_state) n c.
     (wl_word_exp s (wl_Op asm_Add [wl_Var n; wl_Const c]) =
      match wl_get_var n s with
        SOME (wl_Word w) -> SOME (wl_Word (word_add w c))
      | _ -> NONE) /\
     (wl_word_exp s (wl_Op asm_Sub [wl_Var n; wl_Const c]) =
      match wl_get_var n s with
        SOME (wl_Word w) -> SOME (wl_Word (word_sub w c))
      | _ -> NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def; MAP] THEN
  CASES_ON `wl_get_var n (s:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[the_words_def] THEN
  TRY(CASES_ON `a:A word_loc`) THEN
  CAKE_REWRITE_TAC[the_words_def; word_op_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0]);;

(* HOL4 line 2953 (local) *)
let good_dimindex_w2w_byte = prove
 (`!w:byte. good_dimindex (:A) ==> word_zx (word_zx w:A word) = w`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC WORD_ZX_ZX THEN ASM_REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* HOL4 line 2962 (local) *)
let set_var_consts = prove
 (`!r (v:A word_loc) (s:(A,C,FFI)wl_state).
     wl_state_memory (wl_set_var r v s) = wl_state_memory s /\
     wl_state_mdomain (wl_set_var r v s) = wl_state_mdomain s /\
     wl_state_be (wl_set_var r v s) = wl_state_be s /\
     wl_state_code (wl_set_var r v s) = wl_state_code s`,
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds]);;

(* HOL4 line 2971 (local) *)
let get_var_consts = prove
 (`!r (s:(A,C,FFI)wl_state) m.
     wl_get_var r (wl_state_memory_fupd (combin_K m) s) = wl_get_var r s`,
  REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds]);;

(* ------------------------------------------------------------------------- *)
(* Symbolic evaluation of wordLang code (the work of HOL4's eq_eval and      *)
(* simp in the proofs below): rewriting to a fixpoint with the case          *)
(* equations of all datatypes, the assumptions and the given theorems.       *)
(* ------------------------------------------------------------------------- *)

let ASP2AUX_CRW_TAC thl : tactic = fun (asl,w as g) ->
  CAKE_REWRITE_TAC (map snd asl @ thl) g;;

let asp2_eval_rws =
  [wl_evaluate_def; wl_word_exp_def; wl_get_var_def; wl_set_var_def;
   wl_get_var_imm_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
   K_o_THM; K_THM; lookup_insert; ARITH_EQ; wl_word_cmp_def; insert_shadow];;

let asp2_eval_rws2 =
  [data_to_word_list_Seq_def; wl_inst_def; the_words_def; word_op_def; MAP; ITLIST;
   WORD_ADD_0; OPTION_MAP_DEF; wl_get_vars_def; wl_flush_state_def];;

let asp2_call_rws =
  [bad_dest_args_def; wl_find_code_def; add_ret_loc_def; wl_call_env_def;
   wl_dec_clock_def; LENGTH; ARITH_SUC; option_DISTINCT; NOT_CONS_NIL];;

(* lookup k (fromList2 [x0; ...; xn]) for a numeral k *)
let ASP2AUX_LOOKUP_FROMLIST2_CONV : conv = fun tm ->
  match tm with
    Comb(Comb(Const("lookup",_),k),Comb(Const("fromList2",_),l))
      when is_numeral k && is_list l ->
      (REWR_CONV lookup_fromList2 THENC NUM_REDUCE_CONV THENC
       REWRITE_CONV[lookup_fromList; LENGTH] THENC NUM_REDUCE_CONV THENC
       REWRITE_CONV[] THENC TRY_CONV(ONCE_DEPTH_CONV EL_CONV)) tm
  | _ -> failwith "ASP2AUX_LOOKUP_FROMLIST2_CONV";;

(* the state st of the first wl_evaluate (code,st) in tm *)
let asp2_eval_arg code tm =
  let t = find_term (fun t ->
      try let f,a = dest_comb t in
          (match f with Const("wl_evaluate",_) -> fst(dest_pair a) = code
                      | _ -> false)
      with Failure _ -> false) tm in
  snd(dest_pair(rand t));;

(* the goal is  (!... s .... P s ==> ...) ==> concl: specialise the        *)
(* antecedent with the list mk st, where st is the state of the            *)
(* wl_evaluate (code,_) of concl                                            *)
let ASP2AUX_SPEC_EVAL_TAC code (mk:term->term list) : tactic = fun (asl,w as g) ->
  let ant,con = dest_imp w in
  let st = asp2_eval_arg code con in
  DISCH_THEN(MP_TAC o ISPECL (mk st)) g;;

let rec asp2_drule_n asl n th =
  if n = 0 then th else
  let mp = MATCH_MP_CURRIED th in
  tryfind (fun a -> asp2_drule_n asl (n-1) (mp a)) asl;;

(* MP_TAC th with its first n (curried) antecedents discharged by matching *)
(* assumptions                                                              *)
let ASP2AUX_DRULE_N n th : tactic = fun (asl,w as g) ->
  MP_TAC (asp2_drule_n (map snd asl) n (IMP_CURRY_RULE (GEN_ALL th))) g;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of the byte copying loops.                                     *)
(* ------------------------------------------------------------------------- *)

let ASP2AUX_ULT_4_DIV = prove
 (`!n:A word. word_ult n (word 4) ==> val n DIV 4 = 0`,
  GEN_TAC THEN REWRITE_TAC[WORD_ULT; VAL_WORD] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIV_LT THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `4 MOD 2 EXP dimindex (:A)` THEN
  ASM_REWRITE_TAC[MOD_LE]);;

let ASP2AUX_VAL_WORD_SMALL = prove
 (`!k. good_dimindex (:A) /\ k < 2 EXP 32 ==> val (word k:A word) = k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let ASP2AUX_VAL_SUB_4 = prove
 (`!n:A word. good_dimindex (:A) /\ ~word_ult n (word 4) ==>
     4 <= val n /\ val (word_sub n (word 4)) = val n - 4 /\
     val n DIV 4 = (val n - 4) DIV 4 + 1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word 4:A word) = 4` ASSUME_TAC THENL
   [MATCH_MP_TAC ASP2AUX_VAL_WORD_SMALL THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  UNDISCH_TAC `~word_ult (n:A word) (word 4)` THEN
  ASM_REWRITE_TAC[WORD_ULT; NOT_LT] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  SUBGOAL_THEN `val (n:A word) = 1 * 4 + (val n - 4)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;

(* the recursion of word_copy_fwd and word_copy_bwd decreases val n by 4;   *)
(* the kit's word_copy_fwd_ind and word_copy_bwd_ind name two different    *)
(* context variables alike (their induction hypothesis needs the bytes at  *)
(* a and a + 3 to be equal), so the proofs below induct on val n instead   *)
let ASP2AUX_COPY_IND = prove
 (`!P:bool->A word->A word->A word->(A word->A word_loc)->(A word->bool)->bool.
       (!be (n:A word) a b (m:A word->A word_loc) dm.
          (~(dimword (:A) <= 4) /\ ~word_ult n (word 4) ==>
           !a' b' m'. P be (word_sub n (word 4)) a' b' m' dm) ==>
          P be n a b m dm) ==>
       !be n a b m dm. P be n a b m dm`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k be (n:A word) (a:A word) (b:A word) (m:A word->A word_loc) dm.
                  val n = k ==>
                  (P:bool->A word->A word->A word->(A word->A word_loc)->(A word->bool)->bool)
                    be n a b m dm`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  EXISTS_TAC `val (word_sub n (word 4):A word)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `~word_ult (n:A word) (word 4)` THEN
  UNDISCH_TAC `~(dimword (:A) <= 4)` THEN
  REWRITE_TAC[WORD_ULT; NOT_LE; NOT_LT; dimword_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word 4:A word) = 4` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word 4:A word) = 4`]) THEN
  ASM_ARITH_TAC);;

let ASP2AUX_WORD_ADD_NEG = prove
 (`!x y:A word. word_add x (word_neg y) = word_sub x y`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

(* HOL4 line 2977 *)
let CopyByteAdd_thm = prove
 (`!be n a1 a2 m dm ret_val l1 l2 (s:(A,C,FFI)wl_state) m1.
     word_copy_fwd be n a1 a2 m dm = SOME m1 /\
     wl_state_memory s = m /\ wl_state_mdomain s = dm /\
     wl_state_be s = be /\
     good_dimindex(:A) /\
     lookup ByteCopyAdd_location (wl_state_code s) = SOME (5,ByteCopyAdd_code) /\
     val n DIV 4 <= wl_state_clock s /\
     wl_get_var 0 s = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 s = SOME (wl_Word n) /\
     wl_get_var 4 s = SOME (wl_Word (a1:A word)) /\
     wl_get_var 6 s = SOME (wl_Word a2) /\
     wl_get_var 8 s = SOME ret_val ==>
     wl_evaluate (ByteCopyAdd_code,s) =
       (SOME (wl_Result (wl_Loc l1 l2) [ret_val]),
        wl_state_clock_fupd (combin_K (wl_state_clock s - val n DIV 4))
          (wl_state_memory_fupd (combin_K m1)
             (wl_state_locals_fupd (combin_K LN)
                (wl_state_locals_size_fupd (combin_K (SOME 0))
                   (wl_state_stack_max_fupd
                      (combin_K (if word_ult n (word 4) then wl_state_stack_max s
                          else OPTION_MAP2 MAX (wl_state_stack_max s)
                                 (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s))
                                    (lookup ByteCopyAdd_location (wl_state_stack_size s)))))
                      s)))))`,
  MATCH_MP_TAC ASP2AUX_COPY_IND THEN
  MAP_EVERY X_GEN_TAC [`be:bool`; `n:A word`; `a1:A word`; `a2:A word`;
                       `m:A word->A word_loc`; `dm:A word->bool`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`ret_val:A word_loc`; `l1:num`; `l2:num`;
                       `s:(A,C,FFI)wl_state`; `m1:A word->A word_loc`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(dimword (:A) <= 4)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_TAC `word_copy_fwd be n a1 a2 (m:A word->A word_loc) dm = SOME m1` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [word_copy_fwd_def] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV) [ByteCopyAdd_code_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `!w:byte. word_zx (word_zx w:A word) = w` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_dimindex_w2w_byte]; ALL_TAC] THEN
  ASM_CASES_TAC `word_ult (n:A word) (word 4)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `word_ult (n:A word) (word 2)` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `n:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
        REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                    VAL_WORD_0; DIV_0; SUB_0] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[OPTION_BIND_EQUALS_OPTION] THEN STRIP_TAC THEN
        ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
        REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
        ASM_SIMP_TAC[ASP2AUX_ULT_4_DIV; SUB_0]];
      ASM_CASES_TAC `n:A word = word 2` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[OPTION_BIND_EQUALS_OPTION; option_INJ] THEN STRIP_TAC THEN
      ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
      REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_SIMP_TAC[ASP2AUX_ULT_4_DIV; SUB_0]];
    REWRITE_TAC[OPTION_BIND_EQUALS_OPTION] THEN STRIP_TAC THEN
    MP_TAC(SPEC `n:A word` ASP2AUX_VAL_SUB_4) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(wl_state_clock (s:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
     [MP5AUX_ARITH_TAC; ALL_TAC] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
    REMOVE_THEN "IH" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASP2AUX_SPEC_EVAL_TAC `ByteCopyAdd_code:(A)wl_prog`
      (fun st -> [`word_add a1 (word 4):A word`; `word_add a2 (word 4):A word`;
                  mk_comb(`wl_state_memory:(A,C,FFI)wl_state->A word->A word_loc`,st);
                  `ret_val:A word_loc`; `l1:num`; `l2:num`; st;
                  `m1:A word->A word_loc`]) THEN
    REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ [wl_bad_fun_return_def; PAIR_EQ]) THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                OPTION_MAP2_MAX_CANCEL; COND_ID] THEN
    ARITH_TAC]);;

(* HOL4 line 3090 *)
let CopyByteSub_thm = prove
 (`!be n a1 a2 m dm ret_val l1 l2 (s:(A,C,FFI)wl_state) m1.
     word_copy_bwd be n a1 a2 m dm = SOME m1 /\
     wl_state_memory s = m /\ wl_state_mdomain s = dm /\
     wl_state_be s = be /\
     good_dimindex(:A) /\
     lookup ByteCopySub_location (wl_state_code s) = SOME (5,ByteCopySub_code) /\
     val n DIV 4 <= wl_state_clock s /\
     wl_get_var 0 s = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 s = SOME (wl_Word n) /\
     wl_get_var 4 s = SOME (wl_Word (a1:A word)) /\
     wl_get_var 6 s = SOME (wl_Word a2) /\
     wl_get_var 8 s = SOME ret_val ==>
     wl_evaluate (ByteCopySub_code,s) =
       (SOME (wl_Result (wl_Loc l1 l2) [ret_val]),
        wl_state_clock_fupd (combin_K (wl_state_clock s - val n DIV 4))
          (wl_state_memory_fupd (combin_K m1)
             (wl_state_locals_fupd (combin_K LN)
                (wl_state_locals_size_fupd (combin_K (SOME 0))
                   (wl_state_stack_max_fupd
                      (combin_K (if word_ult n (word 4) then wl_state_stack_max s
                          else OPTION_MAP2 MAX (wl_state_stack_max s)
                                 (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s))
                                    (lookup ByteCopySub_location (wl_state_stack_size s)))))
                      s)))))`,
  MATCH_MP_TAC ASP2AUX_COPY_IND THEN
  MAP_EVERY X_GEN_TAC [`be:bool`; `n:A word`; `a1:A word`; `a2:A word`;
                       `m:A word->A word_loc`; `dm:A word->bool`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`ret_val:A word_loc`; `l1:num`; `l2:num`;
                       `s:(A,C,FFI)wl_state`; `m1:A word->A word_loc`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(dimword (:A) <= 4)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_TAC `word_copy_bwd be n a1 a2 (m:A word->A word_loc) dm = SOME m1` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [word_copy_bwd_def] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV) [ByteCopySub_code_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `!w:byte. word_zx (word_zx w:A word) = w` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_dimindex_w2w_byte]; ALL_TAC] THEN
  ASM_CASES_TAC `word_ult (n:A word) (word 4)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `word_ult (n:A word) (word 2)` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `n:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ [ASP2AUX_WORD_ADD_NEG]) THEN
        REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                    VAL_WORD_0; DIV_0; SUB_0] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[OPTION_BIND_EQUALS_OPTION] THEN STRIP_TAC THEN
        ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ [ASP2AUX_WORD_ADD_NEG]) THEN
        REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
        ASM_SIMP_TAC[ASP2AUX_ULT_4_DIV; SUB_0]];
      ASM_CASES_TAC `n:A word = word 2` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[OPTION_BIND_EQUALS_OPTION; option_INJ] THEN STRIP_TAC THEN
      ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ [ASP2AUX_WORD_ADD_NEG]) THEN
      REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_SIMP_TAC[ASP2AUX_ULT_4_DIV; SUB_0]];
    REWRITE_TAC[OPTION_BIND_EQUALS_OPTION] THEN STRIP_TAC THEN
    MP_TAC(SPEC `n:A word` ASP2AUX_VAL_SUB_4) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(wl_state_clock (s:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
     [MP5AUX_ARITH_TAC; ALL_TAC] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ [ASP2AUX_WORD_ADD_NEG] @ asp2_call_rws) THEN
    REMOVE_THEN "IH" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASP2AUX_SPEC_EVAL_TAC `ByteCopySub_code:(A)wl_prog`
      (fun st -> [`word_sub a1 (word 4):A word`; `word_sub a2 (word 4):A word`;
                  mk_comb(`wl_state_memory:(A,C,FFI)wl_state->A word->A word_loc`,st);
                  `ret_val:A word_loc`; `l1:num`; `l2:num`; st;
                  `m1:A word->A word_loc`]) THEN
    REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ [ASP2AUX_WORD_ADD_NEG] @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ [wl_bad_fun_return_def; PAIR_EQ]) THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                OPTION_MAP2_MAX_CANCEL; COND_ID] THEN
    ARITH_TAC]);;

(* HOL4 line 3203 *)
let push_env_store = prove
 (`!x y (s:(A,C,FFI)wl_state).
     wl_state_store (wl_push_env x y s) = wl_state_store s /\
     wl_state_memory (wl_push_env x y s) = wl_state_memory s /\
     wl_state_mdomain (wl_push_env x y s) = wl_state_mdomain s /\
     wl_state_code (wl_push_env x y s) = wl_state_code s /\
     wl_state_be (wl_push_env x y s) = wl_state_be s`,
  GEN_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT STRIP_TAC THEN PAIRARG_TAC THEN SIMP[]);;

(* HOL4 line 3217 (local) *)
let not_less_zero_int_eq = prove
 (`!i:int. ~(i < &0) <=> ?n. i = &n`,
  GEN_TAC THEN REWRITE_TAC[INT_NOT_LT] THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `num_of_int i` THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT];
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the assign theorems below.                                      *)
(* ------------------------------------------------------------------------- *)

(* rewrite conversion with the case net, the assumptions and thl *)
let asp2_crw_conv asl thl = CAKE_REWRITE_CONV (map snd asl @ thl);;

(* the first subterm wl_word_exp st (real_addr c v) of the goal: add its   *)
(* value SOME (wl_Word x) (get_var_get_real_addr_lemma) as an assumption;    *)
(* wl_get_var v st is computed by rewriting with thl and the assumptions,   *)
(* x comes from an assumption get_real_addr c _ ptr = SOME x                 *)
let ASP2AUX_REAL_ADDR_TAC thl : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t ->
      try let f,args = strip_comb t in
          fst(dest_const f) = "wl_word_exp" && length args = 2 &&
          asp2_head_is "real_addr" (el 1 args)
      with Failure _ -> false) w in
  let st = rand(rator tm) and e = rand tm in
  let c = rand(rator e) and v = rand e in
  let gv = list_mk_icomb "wl_get_var" [v; st] in
  let th1 = asp2_crw_conv asl thl gv in
  let ptr = rand(rand(rhs(concl th1))) in
  let x = rand(rhs(snd(find (fun (_,th) ->
            try let l = lhs(concl th) in
                asp2_head_is "get_real_addr" l && rand l = ptr && rand(rator(rator l)) = c
            with Failure _ -> false) asl) |> concl)) in
  (MP_TAC (ISPECL [c; v; st; ptr; x] get_var_get_real_addr_lemma) THEN
   ANTS_TAC THENL [ASP2AUX_CRW_TAC thl; DISCH_TAC]) g;;

(* symbolic evaluation: rewriting, with the real_addr expressions resolved *)
let ASP2AUX_EVAL_TAC thl : tactic =
  ASP2AUX_CRW_TAC thl THEN
  REPEAT(ASP2AUX_REAL_ADDR_TAC thl THEN ASP2AUX_CRW_TAC thl);;

(* decide a goal about option_le / OPTION_MAP2 (+) MAX over num option atoms: *)
(* case split every maximal atom of type num option (not SOME/NONE/          *)
(* OPTION_MAP2/OPTION_MAP), then arithmetic                                   *)
let ASP2AUX_OPTION_ARITH_TAC : tactic = fun (asl,w as g) ->
  let is_atom t =
    type_of t = `:num option` &&
    (let f,_ = strip_comb t in
     not (is_const f && mem (fst(dest_const f)) ["OPTION_MAP2";"SOME";"NONE";"OPTION_MAP"])) in
  let rec atoms t acc =
    if is_atom t then insert t acc
    else if is_comb t then atoms (rator t) (atoms (rand t) acc)
    else if is_abs t then atoms (body t) acc
    else acc in
  let tms = atoms w [] in
  (MAP_EVERY (fun t ->
     DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (genvar `:num`) SUBST1_TAC)
       (ISPEC t option_nchotomy)) tms THEN
   REWRITE_TAC[OPTION_MAP2_THM; option_le_def; OPTION_MAP_DEF] THEN
   ARITH_TAC) g;;

(* from an assumption  ~(a = b) ==> a = b  get  a = b *)
let ASP2AUX_EQ_FROM_NEG_IMP_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    let a,b = dest_imp(concl th) in
    if is_neg a && aconv (dest_neg a) b then
      ASSUME_TAC (MP (INST [b,`p:bool`] (TAUT `(~p ==> p) ==> p`)) th)
    else failwith "ASP2AUX_EQ_FROM_NEG_IMP_TAC");;

let ASP2AUX_code_rel_stub = prove
 (`!c (s_code:(num#data_prog)spt) (t_code:(num#(A)wl_prog)spt) n x.
     data_to_word_gcProof_code_rel c s_code t_code /\
     MEM (n,x) (data_to_word_stubs (:A) c) ==> lookup n t_code = SOME x`,
  REWRITE_TAC[data_to_word_gcProof_code_rel_def; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(n:num,x:num#(A)wl_prog)`) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* lookup loc (wl_state_code t) = SOME (k,code) for a stub, from the code_rel *)
(* assumption                                                               *)
let ASP2AUX_STUB_TAC tm : tactic =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MATCH_MP_TAC ASP2AUX_code_rel_stub THEN
    FIRST_ASSUM(fun th -> if asp2_head_is "data_to_word_gcProof_code_rel" (concl th)
                          then MAP_EVERY EXISTS_TAC [rand(rator(rator(concl th)));
                                                     rand(rator(concl th))] THEN
                               ASM_REWRITE_TAC[]
                          else failwith "") THEN
    REWRITE_TAC[data_to_word_stubs_def; MEM; MEM_APPEND];
    ALL_TAC];;

let ASP2AUX_cut_envs_ins k =
  REWRITE_RULE[ARITH] (ISPEC (mk_small_numeral k)
    data_to_word_gcProof_cut_envs_adjust_sets_insert_ODD);;

(* MP_TAC (mk st) where st is the state of the first wl_evaluate (code,st)  *)
(* of the goal                                                               *)
let ASP2AUX_EVAL_LEMMA_TAC code (mk:term->thm) : tactic = fun (asl,w as g) ->
  MP_TAC (mk (asp2_eval_arg code w)) g;;

let ASP2AUX_val_lt_MustTerminate_limit = prove
 (`!w:A word. val w < MustTerminate_limit (:A) - 1`,
  GEN_TAC THEN MP_TAC(ISPEC `w:A word` VAL_BOUND) THEN
  REWRITE_TAC[MustTerminate_limit_DEF; GSYM dimword_def] THEN ARITH_TAC);;

(* the goal  ?q r. (x,y) = (q,r) /\ P q r  (or  ?q r. (x = q /\ y = r) /\ ...): *)
(* instantiate q and r with x, y                                            *)
let ASP2AUX_EXISTS_PAIR_TAC : tactic = fun (asl,w as g) ->
  let q,b1 = dest_exists w in
  let r,b2 = dest_exists b1 in
  let e = fst(dest_conj b2) in
  let x,y = if is_conj e then lhs(fst(dest_conj e)),lhs(snd(dest_conj e))
            else dest_pair(lhs e) in
  (EXISTS_TAC x THEN EXISTS_TAC y THEN REWRITE_TAC[]) g;;

let ASP2AUX_do_stack_lim_safe = prove
 (`!op vs (x:(C,FFI)data_state).
     data_state_refs (do_stack op vs (do_lim_safe x op vs)) = data_state_refs x /\
     data_state_locals (do_stack op vs (do_lim_safe x op vs)) = data_state_locals x /\
     data_state_stack (do_stack op vs (do_lim_safe x op vs)) = data_state_stack x /\
     data_state_tstamps (do_stack op vs (do_lim_safe x op vs)) = data_state_tstamps x /\
     data_state_space (do_stack op vs (do_lim_safe x op vs)) = data_state_space x /\
     data_state_global (do_stack op vs (do_lim_safe x op vs)) = data_state_global x /\
     data_state_limits (do_stack op vs (do_lim_safe x op vs)) = data_state_limits x /\
     data_state_locals_size (do_stack op vs (do_lim_safe x op vs)) =
       data_state_locals_size x /\
     data_state_stack_frame_sizes (do_stack op vs (do_lim_safe x op vs)) =
       data_state_stack_frame_sizes x /\
     data_state_ffi (do_stack op vs (do_lim_safe x op vs)) = data_state_ffi x /\
     data_state_clock (do_stack op vs (do_lim_safe x op vs)) = data_state_clock x /\
     data_state_handler (do_stack op vs (do_lim_safe x op vs)) = data_state_handler x /\
     data_state_code (do_stack op vs (do_lim_safe x op vs)) = data_state_code x /\
     data_state_compile (do_stack op vs (do_lim_safe x op vs)) = data_state_compile x /\
     data_state_compile_oracle (do_stack op vs (do_lim_safe x op vs)) =
       data_state_compile_oracle x /\
     data_state_stack_max (do_stack op vs (do_lim_safe x op vs)) =
       OPTION_MAP2 MAX (data_state_stack_max x)
         (OPTION_MAP2 (+)
            (stack_consumed (data_state_stack_frame_sizes x) (data_state_limits x) op vs)
            (OPTION_MAP2 (+) (size_of_stack (data_state_stack x))
               (data_state_locals_size x)))`,
  REWRITE_TAC[do_stack_def; do_lim_safe; data_state_INFO.ri_accfupds; K_THM;
              LET_DEF; LET_END_DEF]);;

let ASP2AUX_memory_rel_IMP = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     shift_length c < dimindex (:A) /\
     backend_common_word_shift (:A) <= shift_length c /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex (:A)`,
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN MESON_TAC[]);;

let ASP2AUX_v_to_list_Block = prove
 (`!v l. data_v_to_list v = SOME l ==> ?ts tag vs. v = data_Block ts tag vs`,
  GEN_TAC THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[data_v_to_list_def; option_DISTINCT] THEN MESON_TAC[]);;

let ASP2AUX_get_real_offset_1 = prove
 (`good_dimindex (:A) ==>
   get_real_offset (Smallnum (&1):A word) = SOME (word_mul (word 2) bytes_in_word)`,
  REWRITE_TAC[good_dimindex_def; get_real_offset_def; data_to_word_Smallnum_def;
              bytes_in_word_def] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_SHL; VAL_WORD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* from assumptions  e = SOME a  and  e = SOME b  derive  a = b  (for every *)
(* such pair), then eliminate variables                                     *)
let ASP2AUX_SOME_UNIQ_TAC : tactic = fun (asl,w as g) ->
  let is_some_eq th =
    let c = concl th in
    is_eq c && (try fst(dest_const(rator(rhs c))) = "SOME" with Failure _ -> false) in
  let ths = map snd (filter (fun (_,th) -> is_some_eq th) asl) in
  let rec pairs l = match l with
      [] -> []
    | h::t -> map (fun x -> (h,x)) t @ pairs t in
  let news = mapfilter (fun (th1,th2) ->
      if aconv (lhs(concl th1)) (lhs(concl th2)) &&
         not (aconv (rhs(concl th1)) (rhs(concl th2)))
      then REWRITE_RULE[option_INJ] (TRANS (SYM th1) th2)
      else failwith "") (pairs ths) in
  (MAP_EVERY ASSUME_TAC news THEN RVEQ_TAC) g;;

(* a goal  wl_get_vars [v1;..;vn] t = SOME [w1;..;wn] ==> P : the lookups of *)
(* the vi as assumptions                                                     *)
let ASP2AUX_GET_VARS_TAC : tactic =
  REWRITE_TAC[wl_get_vars_def; wl_get_var_def] THEN
  REWRITE_TAC(all_case_eqs()) THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(CHANGED_TAC
    (RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; option_INJ]) THEN
     REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
     RVEQ_TAC));;

let ASP2AUX_ShiftVar_2 = prove
 (CASE_TERM
  `good_dimindex (:A) ==>
   (!(t:(A,C,FFI)wl_state) v.
      wl_word_exp t (ShiftVar Lsr v 2) =
      match lookup v (wl_state_locals t) with
        SOME (wl_Word w) -> SOME (wl_Word (word_ushr w 2))
      | _ -> NONE) /\
   (!(t:(A,C,FFI)wl_state) v.
      wl_word_exp t (ShiftVar Lsl v 2) =
      match lookup v (wl_state_locals t) with
        SOME (wl_Word w) -> SOME (wl_Word (word_shl w 2))
      | _ -> NONE)`,
  REWRITE_TAC[good_dimindex_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(dimindex (:A) <= 2) /\ val (word 2:A word) = 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_EQ_EQ] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[ShiftVar_def] THEN CAKE_REWRITE_TAC[ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_word_exp_def; wl_get_var_def] THEN
  CASES_ON `lookup v (wl_state_locals (t:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:A word_loc`) THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[word_sh_def; GE; ARITH_EQ; OPTION_MAP_DEF] THEN
  CAKE_REWRITE_TAC[OPTION_MAP_DEF]);;

let ASP2AUX_IS_SOME_insert_mono = prove
 (`!k a (l:(A word_loc)spt) n. IS_SOME (lookup n l) ==> IS_SOME (lookup n (insert k a l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN
  REWRITE_TAC[IS_SOME_DEF]);;

let ASP2AUX_inter_ins k =
  REWRITE_RULE[ARITH] (ISPEC (mk_small_numeral k) inter_insert_ODD_adjust_set);;

let ASP2AUX_do_word_app_WordFromWord = prove
 (`!b vals res.
     data_do_word_app (WordFromWord b) vals = SOME res ==>
     (b /\ ?w. vals = [data_Word64 w] /\ res = data_Number (&(val (word_zx w:byte)))) \/
     (~b /\ ?w:byte. vals = [data_Number (&(val w))] /\ res = data_Word64 (word_zx w))`,
  REPEAT GEN_TAC THEN CASES_ON `vals:data_v list` THEN
  CAKE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  CASES_ON `a0:data_v` THEN CAKE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  CASES_ON `a1:data_v list` THEN CAKE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; some_DEF] THEN
    COND_CASES_TAC THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `@x:byte. (a:int) = &(val x)` THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM(ACCEPT_TAC o SELECT_RULE o
      check (is_exists o concl));
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `a:int64` THEN REWRITE_TAC[]]);;

let ASP2AUX_do_app_WordFromWord = prove
 (`!b vals (x:(C,FFI)data_state) v s2.
     data_do_app (WordOp (WordFromWord b)) vals x = Rval (v,s2) ==>
     (b /\ ?w. vals = [data_Word64 w] /\ v = data_Number (&(val (word_zx w:byte))) /\
               s2 = do_stack (WordOp (WordFromWord b)) vals
                      (do_lim_safe x (WordOp (WordFromWord b)) vals)) \/
     (~b /\ ?w:byte. vals = [data_Number (&(val w))] /\ v = data_Word64 (word_zx w) /\
               3 <= data_state_space x /\
               s2 = do_stack (WordOp (WordFromWord b)) vals
                      (do_lim_safe (data_state_space_fupd (combin_K (data_state_space x - 3)) x)
                         (WordOp (WordFromWord b)) vals))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_do_app_def; do_space_def; MEM] THEN
  CAKE_REWRITE_TAC[op_space_reset_def; op_space_req_def; consume_space_def] THEN
  CONV_TAC NUM_REDUCE_CONV THENL
   [ALL_TAC;
    COND_CASES_TAC THEN CAKE_REWRITE_TAC[distinctness "result"] THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_LT])] THEN
  ONCE_REWRITE_TAC[data_do_app_aux_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC(all_case_eqs()) THEN CAKE_REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(X_CHOOSE_THEN `res:data_v` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP2AUX_do_word_app_WordFromWord) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST [EXISTS_TAC `w:int64`; EXISTS_TAC `w:byte`] THEN ASM_REWRITE_TAC[]);;

let ASP2AUX_byte_of_w64 = prove
 (`!k (w:int64). 7 <= k /\ 8 <= dimindex (:A) ==>
     word_shl (word_and (word_extract k 0 w:A word) (word 255)) 2 =
     Smallnum (&(val (word_zx w:byte)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[data_to_word_Smallnum_def; INT_OF_NUM_LT; LT; INT_OF_NUM_MUL;
              NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[ARITH_RULE `255 = 2 EXP 8 - 1`; WORD_AND_MASK_WORD; WORD_SHL_WORD] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[word_extract_DEF; VAL_WORD_ZX_GEN; VAL_WORD_BITS; BITS_THM2;
              CONJUNCT1 EXP; DIV_1; MOD_MOD_EXP_MIN; DIMINDEX_8] THEN
  SUBGOAL_THEN `MIN (MIN (SUC k) (dimindex (:A))) 8 = 8` SUBST1_TAC THENL
   [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]);;

let ASP2AUX_Smallnum_byte_ushr = prove
 (`!w:byte. good_dimindex (:A) ==>
     word_ushr (Smallnum (&(val w)):A word) 2 = word (val w)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[data_to_word_Smallnum_def; INT_OF_NUM_LT; LT; INT_OF_NUM_MUL;
              NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD] THEN
  MP_TAC(ISPEC `w:byte` w2n_lt_256) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o REWRITE_RULE[good_dimindex_def]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  (SUBGOAL_THEN `4 * val (w:byte) < 4294967296 /\ val w < 4294967296 /\
                 4 * val (w:byte) < 18446744073709551616 /\ val w < 18446744073709551616`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let ASP2AUX_word_zx_byte_word = prove
 (`!w:byte. good_dimindex (:A) ==> (word_zx (word (val w):A word):int64) = word_zx w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  MP_TAC(ISPEC `w:byte` w2n_lt_256) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o REWRITE_RULE[good_dimindex_def]) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  (SUBGOAL_THEN `val (w:byte) < 4294967296 /\ val w < 18446744073709551616`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[MOD_LT]);;

let ASP2AUX_extract_zx_byte = prove
 (`!w:byte. dimindex (:A) = 32 ==>
     word_extract 31 0 (word_zx w:int64) = (word (val w):A word) /\
     word_extract 63 32 (word_zx w:int64) = (word 0:A word)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; word_extract_DEF; VAL_WORD_ZX_GEN; VAL_WORD_BITS; BITS_THM2;
              VAL_WORD; DIMINDEX_64] THEN
  MP_TAC(ISPEC `w:byte` w2n_lt_256) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  (SUBGOAL_THEN `val (w:byte) < 4294967296 /\ val w < 18446744073709551616`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[MOD_LT; DIV_LT; MOD_0; DIV_1]);;

(* the IS_SOME part of state_rel after a set_var (no cut) *)
let ASP2AUX_IS_SOME_set_var = prove
 (`!(s_locals:data_v spt) (t_locals:(A word_loc)spt) (l:(A word_loc)spt) dest v w.
     (!n. IS_SOME (lookup n s_locals) ==> IS_SOME (lookup (adjust_var n) t_locals)) /\
     (!k. IS_SOME (lookup k t_locals) ==> IS_SOME (lookup k l)) ==>
     !n. IS_SOME (lookup n (insert dest v s_locals)) ==>
         IS_SOME (lookup (adjust_var n) (insert (adjust_var dest) w l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[lookup_insert; adjust_var_11] THEN COND_CASES_TAC THEN
  REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[]);;

(* encode_header c 3 len fails (len < 4) only for len_size 0 or 1 *)
let ASP2AUX_encode_header_NONE = prove
 (`!c len. encode_header c 3 len = (NONE:(A word)option) /\
       data_to_word_config_len_size c + 7 < dimindex (:A) /\ good_dimindex (:A) /\
       len < 4 ==>
       ~(1 < data_to_word_config_len_size c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `32 <= dimindex (:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ABBREV_TAC `k = data_to_word_config_len_size c` THEN
  SUBGOAL_THEN `3 < 2 EXP ((dimindex (:A) - k) - 2) /\ 3 < dimword (:A) DIV 16 /\
                len < 2 EXP (dimindex (:A) - 4)` (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 2` THEN
      CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC TWOEXP_MONO2 THEN ASM_ARITH_TAC];
      SUBGOAL_THEN `2 EXP 6 <= dimword (:A)` MP_TAC THENL
       [REWRITE_TAC[dimword_def] THEN MATCH_MP_TAC TWOEXP_MONO2 THEN ASM_ARITH_TAC;
        ARITH_TAC];
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 2` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC TWOEXP_MONO2 THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `2 <= k` THENL
   [SUBGOAL_THEN `2 EXP 2 <= 2 EXP k` MP_TAC THENL
     [MATCH_MP_TAC TWOEXP_MONO2 THEN ASM_REWRITE_TAC[]; ASM_ARITH_TAC];
    ASM_ARITH_TAC]);;

(* state_rel after WriteWord64 / WriteWord64_on_32 (from their lemmas)     *)
let ASP2AUX_state_rel_WriteWord64 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v nf m' locals' sp
    (s2:(C,FFI)data_state).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     data_state_global s2 = data_state_global s /\
     data_state_tstamps s2 = data_state_tstamps s /\
     data_state_refs s2 = data_state_refs s /\
     data_state_space s2 <= sp /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s) sp
       (wl_state_store t |+ (NextFree,nf)) m' (wl_state_mdomain t)
       (APPEND (join_env_locals (insert dest v (data_state_locals s)) locals')
          (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))) /\
     (!n. IS_SOME (lookup n (data_state_locals s)) ==>
          IS_SOME (lookup (adjust_var n) locals')) /\
     IS_SOME (lookup (adjust_var dest) locals') /\
     lookup 0 locals' = lookup 0 (wl_state_locals t) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_state_store_fupd (combin_K (wl_state_store t |+ (NextFree,nf)))
         (wl_state_memory_fupd (combin_K m') (wl_state_locals_fupd (combin_K locals') t))) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds;
              K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[lookup_insert; FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT;
                  FAPPLY_FUPDATE_THM; distinctness "store_name"; code_oracle_rel_NextFree;
                  ALL] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ALL (\n. n IN FDOM (wl_state_store (t:(A,C,FFI)wl_state))) [Globals]` THEN
    REWRITE_TAC[ALL];
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    MP5AUX_HEAD_MESON_TAC[option_le_trans];
    MATCH_MP_TAC memory_rel_less_space THEN EXISTS_TAC `sp:num` THEN ASM_REWRITE_TAC[] THEN
    CAKE_REWRITE_TAC[APPEND] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
      free_in `m':A word->A word_loc` (concl th))) THEN
    REWRITE_TAC[join_env_locals_def]]);;

(* args = [a1] and ws = [w1] (one argument) *)
let ASP2AUX_ONE_ARG_TAC : tactic =
  SUBGOAL_THEN `?a1. args = [a1:num]` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (args:num list) = 1` MP_TAC THENL
     [ASM_MESON_TAC[data_to_word_gcProof_get_vars_IMP_LENGTH; LENGTH; ONE];
      REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL; ONE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w1. ws = [w1:A word_loc]` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (ws:(A word_loc)list) = 1` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        rand(concl th) = `LENGTH (ws:(A word_loc)list)`)) THEN
      REWRITE_TAC[LENGTH; ONE];
      REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL; ONE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ZIP; APPEND; MAP]);;

(* assign_WordFromWord F: the GiveUp case (encode_header fails, which only *)
(* happens when the op is not lim_safe)                                     *)
let ASP2AUX_WFW_GIVEUP_TAC len : tactic =
  FIRST_ASSUM(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC o
    MATCH_MP evaluate_GiveUp2) THEN
  MAP_EVERY EXISTS_TAC [`SOME NotEnoughSpace:((A)wl_result)option`;
                        `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[ASP2AUX_do_stack_lim_safe; data_state_INFO.ri_accfupds; K_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[option_le_max_right] THEN DISJ1_TAC THEN
    MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; len] ASP2AUX_encode_header_NONE) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    UNDISCH_TAC `limits_inv (data_state_limits (s:(C,FFI)data_state))
      (FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength)
      (wl_state_stack_limit t) (data_to_word_config_len_size c)
      (data_to_word_config_has_fp_ops c) (data_to_word_config_has_fp_tern c)` THEN
    REWRITE_TAC[limits_inv_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[]];;

(* HOL4 line 3223 *)
let assign_WordFromWord = prove
 (assign_thm_stmt `(?b. op = WordOp (WordFromWord b))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` SUBST_ALL_TAC) THEN
  BOOL_CASES_TAC `b:bool` THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "clos_op"]) THEN
  VAR_EQ_TAC THEN
  UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `data_get_vars args (data_state_locals (s:(C,FFI)data_state)) = SOME vals`) o
    MATCH_MP state_rel_get_vars_IMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2
      (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
  CAKE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  DRULE_ALL memory_rel_get_vars_IMP THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_memory_rel_IMP o
    check (asp2_head_is "memory_rel" o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP2AUX_do_app_WordFromWord) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASP2AUX_ONE_ARG_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Word64_IMP o
      (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
      check (fun th -> asp2_head_is "memory_rel" (concl th) &&
        can (find_term ((=) `data_Word64 w`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `xa:A word`
      (X_CHOOSE_THEN `hw:A word` STRIP_ASSUME_TAC))) THEN
    RVEQ_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      try asp2_head_is "wl_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
    ASP2AUX_GET_VARS_TAC THEN
    FIRST_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_ShiftVar_2) THEN
    FIRST_ASSUM(MP_TAC o check ((=) `good_dimindex (:A)` o concl)) THEN
    REWRITE_TAC[good_dimindex_def] THEN
    DISCH_THEN(DISJ_CASES_THEN (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    REWRITE_TAC[data_to_word_assign_def] THEN
    CAKE_REWRITE_TAC[data_to_word_arg1_def; assign_WordFromWord_def; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @
      [adjust_var_NEQ; adjust_var_11; wl_mem_load_def; WORD_AND_NOT0]) THEN
    ASM_SIMP_TAC[ASP2AUX_byte_of_w64; ARITH] THEN
    ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
    REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM;
                ASP2AUX_do_stack_lim_safe; wl_state_INFO.ri_accfupds] THEN
    CAKE_REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[] THEN
    (REPEAT CONJ_TAC THENL
     [REWRITE_TAC[lookup_insert; adjust_var_NEQ; ARITH_EQ] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ASP2AUX_IS_SOME_set_var THEN
      EXISTS_TAC `wl_state_locals (t:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN DISCH_TAC THEN
      REPEAT(MATCH_MP_TAC ASP2AUX_IS_SOME_insert_mono) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[option_le_max_right] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ASP2AUX_inter_ins 1; GSYM APPEND_ASSOC] THEN
      MATCH_MP_TAC memory_rel_insert THEN REWRITE_TAC[APPEND] THEN
      MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_SIMP_TAC[small_int_w2n]]);
    FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_IMP o
      (fun th -> CONJ (ASSUME `good_dimindex (:A)`)
                   (CONJ (UNDISCH (ISPEC `w:byte` small_int_w2n)) th)) o
      check (fun th -> asp2_head_is "memory_rel" (concl th) &&
        can (find_term ((=) `data_Number (&(val (w:byte)))`)) (concl th))) THEN
    DISCH_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      try asp2_head_is "wl_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
    ASP2AUX_GET_VARS_TAC THEN
    REWRITE_TAC[data_to_word_assign_def] THEN
    CAKE_REWRITE_TAC[data_to_word_arg1_def; assign_WordFromWord_def; LET_DEF; LET_END_DEF] THEN
    FIRST_ASSUM(MP_TAC o check ((=) `good_dimindex (:A)` o concl)) THEN
    REWRITE_TAC[good_dimindex_def] THEN
    DISCH_THEN(DISJ_CASES_THEN (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])) THEN
    CONV_TAC NUM_REDUCE_CONV THENL
     [DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `header:A word` ASSUME_TAC)
        (ISPEC `encode_header c 3 2:(A word)option` option_nchotomy) THEN
      ASP2AUX_CRW_TAC [] THENL
       [ASP2AUX_WFW_GIVEUP_TAC `2`;
        SUBGOAL_THEN `val (word 2:A word) = 2` ASSUME_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[dimword_def] THEN
          CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @
          [adjust_var_NEQ; adjust_var_11; word_sh_def; GE; ARITH_LE]) THEN
        ASP2AUX_EVAL_LEMMA_TAC `WriteWord64_on_32 c header dest 5 3:(A)wl_prog` (fun st ->
          ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
                  `THE (data_state_tstamps (s:(C,FFI)data_state))`;
                  `data_state_refs (s:(C,FFI)data_state)`;
                  `data_state_space (s:(C,FFI)data_state)`;
                  st; `data_state_locals (s:(C,FFI)data_state)`;
                  `CONS (the_global (data_state_global (s:(C,FFI)data_state)),
                         FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)
                     (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))`;
                  `5`; `3`; `word_zx (w:byte):int64`; `header:A word`; `dest:num`]
                 evaluate_WriteWord64_on_32) THEN
        ANTS_TAC THENL
         [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
          ASM_SIMP_TAC[ASP2AUX_Smallnum_byte_ushr; ASP2AUX_extract_zx_byte;
                       join_env_locals_insert_odd; ARITH; join_env_locals_def;
                       adjust_var_NEQ] THEN
          UNDISCH_TAC `3 <= data_state_space (s:(C,FFI)data_state)` THEN ARITH_TAC;
          DISCH_THEN(X_CHOOSE_THEN `nf:A word_loc` (X_CHOOSE_THEN `m1:A word->A word_loc`
            (X_CHOOSE_THEN `locals1:(A word_loc)spt` STRIP_ASSUME_TAC)))] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH_EQ]) THEN
        ASM_REWRITE_TAC[] THEN
        ASP2AUX_CRW_TAC asp2_eval_rws THEN
        ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
        MATCH_MP_TAC ASP2AUX_state_rel_WriteWord64 THEN
        MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`;
                              `data_state_space (s:(C,FFI)data_state) - 3`] THEN
        ASM_REWRITE_TAC[ASP2AUX_do_stack_lim_safe; data_state_INFO.ri_accfupds; K_THM;
                        LE_REFL; option_le_max_right; option_le_refl]];
      DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `header:A word` ASSUME_TAC)
        (ISPEC `encode_header c 3 1:(A word)option` option_nchotomy) THEN
      ASP2AUX_CRW_TAC [] THENL
       [ASP2AUX_WFW_GIVEUP_TAC `1`;
        SUBGOAL_THEN `val (word 2:A word) = 2` ASSUME_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[dimword_def] THEN
          CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @
          [adjust_var_NEQ; adjust_var_11; word_sh_def; GE; ARITH_LE]) THEN
        ASP2AUX_EVAL_LEMMA_TAC `WriteWord64 c header dest 3:(A)wl_prog` (fun st ->
          ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
                  `THE (data_state_tstamps (s:(C,FFI)data_state))`;
                  `data_state_refs (s:(C,FFI)data_state)`;
                  `data_state_space (s:(C,FFI)data_state)`;
                  st; `data_state_locals (s:(C,FFI)data_state)`;
                  `CONS (the_global (data_state_global (s:(C,FFI)data_state)),
                         FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)
                     (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))`;
                  `3`; `word (val (w:byte)):A word`; `header:A word`; `dest:num`]
                 evaluate_WriteWord64) THEN
        ANTS_TAC THENL
         [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
          ASM_SIMP_TAC[ASP2AUX_Smallnum_byte_ushr; join_env_locals_insert_odd; ARITH;
                       join_env_locals_def; adjust_var_NEQ] THEN
          UNDISCH_TAC `3 <= data_state_space (s:(C,FFI)data_state)` THEN ARITH_TAC;
          DISCH_THEN(X_CHOOSE_THEN `nf:A word_loc` (X_CHOOSE_THEN `m1:A word->A word_loc`
            (X_CHOOSE_THEN `locals1:(A word_loc)spt` STRIP_ASSUME_TAC)))] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH_EQ;
          MP (SPEC `w:byte` ASP2AUX_word_zx_byte_word) (ASSUME `good_dimindex (:A)`)]) THEN
        ASM_REWRITE_TAC[] THEN
        ASP2AUX_CRW_TAC asp2_eval_rws THEN
        ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
        MATCH_MP_TAC ASP2AUX_state_rel_WriteWord64 THEN
        MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`;
                              `data_state_space (s:(C,FFI)data_state) - 2`] THEN
        ASM_REWRITE_TAC[ASP2AUX_do_stack_lim_safe; data_state_INFO.ri_accfupds; K_THM;
                        ARITH_RULE `!x. x - 3 <= x - 2`; option_le_max_right;
                        option_le_refl]]]]);;

(* HOL4 line 3371 *)
let IS_SOME_lookup = prove
 (`!n l:A spt. IS_SOME (lookup n l) <=> n IN domain l`,
  REWRITE_TAC[domain_lookup; IS_SOME_EXISTS]);;

(* HOL4 line 3377 *)
let IN_adjust_var_lemma = prove
 (`!kept_names (s_locals:A spt) x (t_locals:B spt) y1 y2 n.
     data_cut_env kept_names s_locals = SOME x /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     n IN domain x ==>
     adjust_var n IN domain y2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_env_def; cut_envs_def; adjust_sets_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN
  CAKE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_mk_wf; domain_inter; IN_INTER; SUBSET]) THEN
  REWRITE_TAC[domain_inter; IN_INTER] THEN
  ASM_MESON_TAC[adjust_var_IN_adjust_set]);;

(* HOL4 line 3393 *)
let cut_env_envs_lookup_lookup = prove
 (`!kept_names (s_locals:A spt) x (t_locals:B spt) y1 y2 k.
     data_cut_env kept_names s_locals = SOME x /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     k IN domain (adjust_set x) ==>
     ?v. lookup k t_locals = SOME v /\ lookup k y2 = SOME v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_env_def; cut_envs_def; adjust_sets_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN
  CAKE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; mk_wf_inter; IN_domain_adjust_set_inter]) THEN
  ASM_REWRITE_TAC[lookup_inter_alt] THEN
  ASM_MESON_TAC[domain_lookup]);;

(* HOL4 line 3410 *)
let env_to_list_domain = prove
 (`!(y2:(A word_loc)spt) p l permute.
     env_to_list y2 p = (l,permute) ==> domain (fromAList l) = domain y2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  REWRITE_TAC[EXTENSION; domain_lookup; lookup_fromAList] THEN
  SIMP_TAC[]);;

(* HOL4 line 3419 *)
let cut_envs_lookup_0 = prove
 (`!(names:B spt) (t_locals:(A word_loc)spt) y1 y2 p q r' l1 l2.
     cut_envs (adjust_sets names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,r') /\
     lookup 0 t_locals = SOME (wl_Loc l1 l2) ==>
     ALOOKUP q 0 = NONE /\ lookup 0 y1 = SOME (wl_Loc l1 l2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cut_envs_def; adjust_sets_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN
  CAKE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  ASM_SIMP_TAC[lookup_inter_alt; NOT_0_domain; domain_def; IN_SING]);;

(* HOL4 line 3433 *)
let cut_envs_domain_IN = prove
 (`!kept_names (t_locals:B spt) y1 y2 (s_locals:A spt) x n.
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     data_cut_env kept_names s_locals = SOME x /\
     n IN domain x ==>
     adjust_var n IN domain y2`,
  MESON_TAC[IN_adjust_var_lemma]);;

(* HOL4 line 3447 *)
let inter_union_distrib = prove
 (`!(x:A spt) y (z:B spt). sptree_inter (sptree_union x y) z = sptree_union (sptree_inter x z) (sptree_inter y z)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[spt_eq_thm; wf_inter; wf_union] THEN
  REWRITE_TAC[lookup_inter_alt; lookup_union] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CASES_ON `lookup n (x:A spt)` THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 3456 *)
let cut_envs_inter = prove
 (`!kept_names (t_locals:B spt) y1 y2 (s_locals:A spt) x.
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     data_cut_env kept_names s_locals = SOME x ==>
     sptree_inter (fromAList (toAList y1)) (adjust_set x) = LN`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_env_def; cut_envs_def; adjust_sets_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN
  CAKE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SIMP_TAC[spt_eq_thm; wf_inter; sptree_wf_def] THEN
  REWRITE_TAC[lookup_inter_alt; lookup_fromAList; ALOOKUP_toAList; lookup_def] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[domain_def; IN_SING] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[NOT_0_domain; COND_ID]);;

(* the variables kept by a cut (env_to_list of the cut-set part of the word *)
(* locals, as restored by pop_env) give no new join_env entries             *)
let ASP2AUX_join_env_cut_MEM = prove
 (`!kept_names (s_locals:data_v spt) xl (t_locals:(A word_loc)spt) y1 y2 p q perm x.
     data_cut_env kept_names s_locals = SOME xl /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,perm) /\
     MEM x (join_env xl (toAList (sptree_inter (sptree_union (fromAList q) (fromAList (toAList y1)))
                                    (adjust_set xl)))) ==>
     MEM x (join_env s_locals (toAList (sptree_inter t_locals (adjust_set s_locals))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_env_def; cut_envs_def; adjust_sets_def; cut_names_def] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP env_to_list_lookup_equiv) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; mk_wf_inter]) THEN
  FIRST_X_ASSUM(MP_TAC o check (asp2_head_is "MEM" o concl)) THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM; MEM_toAList] THEN
  REWRITE_TAC[mk_wf_inter] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:A word_loc` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `v:A word_loc`] THEN
  UNDISCH_TAC `lookup k (sptree_inter (sptree_union (fromAList (q:(num#A word_loc)list))
      (fromAList (toAList (sptree_inter t_locals (LS one)))))
      (adjust_set (sptree_inter (s_locals:data_v spt) (kept_names:num_set)))) = SOME (v:A word_loc)` THEN
  REWRITE_TAC[lookup_inter_alt; IN_domain_adjust_set_inter] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `?w. lookup k (t_locals:(A word_loc)spt) = SOME w` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_union; lookup_fromAList] THEN
  ASM_REWRITE_TAC[lookup_inter_alt] THEN CAKE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k - 2) DIV 2 IN domain (kept_names:num_set)` ASSUME_TAC THENL
   [UNDISCH_TAC `k IN domain (adjust_set (kept_names:num_set))` THEN
    REWRITE_TAC[domain_lookup; lookup_adjust_set] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    ASM_REWRITE_TAC[domain_lookup];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let ASP2AUX_cut_state_opt_cut_env = prove
 (`!names (s:(C,FFI)data_state) x.
     data_cut_state_opt (SOME names) s = SOME x ==>
     data_cut_env names (data_state_locals s) = SOME (data_state_locals x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  CAKE_REWRITE_TAC[] THEN
  CASES_ON `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* the locals restored after a call that cut with adjust_sets kept_names  *)
let ASP2AUX_cut_ret_lookup_0 = prove
 (`!(kept_names:num_set) (t_locals:(A word_loc)spt) y1 y2 p q perm l1 l2 dest ret.
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,perm) /\
     lookup 0 t_locals = SOME (wl_Loc l1 l2) ==>
     lookup 0 (insert (adjust_var dest) ret
                 (sptree_union (fromAList q) (fromAList (toAList y1)))) =
     SOME (wl_Loc l1 l2)`,
  REPEAT STRIP_TAC THEN DRULE_ALL cut_envs_lookup_0 THEN
  ASM_REWRITE_TAC[lookup_insert; adjust_var_NEQ; lookup_union; lookup_fromAList;
                  ALOOKUP_toAList] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let ASP2AUX_cut_ret_IS_SOME = prove
 (`!(kept_names:num_set) (s_locals:data_v spt) xl (t_locals:(A word_loc)spt) y1 y2 p q
    perm dest v ret.
     data_cut_env kept_names s_locals = SOME xl /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,perm) ==>
     !n. IS_SOME (lookup n (insert dest v xl)) ==>
         IS_SOME (lookup (adjust_var n) (insert (adjust_var dest) ret
                   (sptree_union (fromAList q) (fromAList (toAList y1)))))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n:num = dest` THEN ASM_REWRITE_TAC[lookup_insert; IS_SOME_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lookup_insert]) THEN
  UNDISCH_TAC `IS_SOME (if n = dest then SOME (v:data_v) else lookup n xl)` THEN
  ASM_REWRITE_TAC[adjust_var_11; IS_SOME_lookup] THEN DISCH_TAC THEN
  REWRITE_TAC[domain_union; IN_UNION] THEN DISJ1_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP env_to_list_domain) THEN
  MATCH_MP_TAC (INST_TYPE [`:data_v`,`:A`; `:A word_loc`,`:B`] IN_adjust_var_lemma) THEN
  MAP_EVERY EXISTS_TAC [`kept_names:num_set`; `s_locals:data_v spt`; `xl:data_v spt`;
                        `t_locals:(A word_loc)spt`; `y1:(A word_loc)spt`] THEN
  ASM_REWRITE_TAC[]);;

let ASP2AUX_memory_rel_cut_ret = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm v ret ys xs (kept_names:num_set)
    s_locals xl (t_locals:(A word_loc)spt) y1 y2 p q perm dest.
     data_cut_env kept_names s_locals = SOME xl /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,perm) /\
     memory_rel c be ts refs sp st m dm (CONS (v,ret) ys) /\
     (!x. MEM x (join_env s_locals (toAList (sptree_inter t_locals (adjust_set s_locals)))) ==>
          MEM x ys) /\
     (!x. MEM x xs ==> MEM x ys) ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (join_env (insert dest v xl)
          (toAList (sptree_inter (insert (adjust_var dest) ret
                             (sptree_union (fromAList q) (fromAList (toAList y1))))
                          (adjust_set (insert dest v xl))))) xs)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC memory_rel_insert THEN
  FIRST_X_ASSUM(MP_TAC o check (asp2_head_is "memory_rel" o concl)) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN
  FIRST [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
           can (find_term (asp2_head_is "join_env")) (concl th))) THEN
         MATCH_MP_TAC ASP2AUX_join_env_cut_MEM THEN
         MAP_EVERY EXISTS_TAC [`kept_names:num_set`; `xl:data_v spt`;
           `y1:(A word_loc)spt`; `y2:(A word_loc)spt`; `p:num->num->num`;
           `q:(num#A word_loc)list`; `perm:num->num->num`] THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* for the memory_rel assumption th (vars = CONS x1 (CONS x2 ... rest)),    *)
(* add memory_rel ... (CONS xi1 (CONS xi2 ... rest)) for the indices is     *)
(* (0-based) of the CONS prefix                                              *)
let asp2_strip_cons tm =
  let rec go t acc =
    try let h,t' = dest_cons t in go t' (h::acc) with Failure _ -> (rev acc, t) in
  go tm [];;

let ASP2AUX_MEMREL_PICK_TAC (pred:term->bool) (is:int list) : tactic = fun (asl,w as g) ->
  let th = snd(find (fun (_,th) -> asp2_head_is "memory_rel" (concl th) &&
                                   pred (concl th)) asl) in
  let vars = rand(concl th) in
  let xs,rest = asp2_strip_cons vars in
  let nl = itlist (fun i acc -> mk_cons (el i xs) acc) is rest in
  let goal' = mk_comb(rator(concl th), nl) in
  let th' = prove(mk_imp(concl th, goal'),
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]) in
  ASSUME_TAC (MP th' th) g;;

(* for a memory_rel assumption containing (data_Number (&n),a) in its list: *)
(* the fact ?w. a = wl_Word w /\ word_ushr w 2 = word n (memory_rel_get_num) *)
(* as the antecedent of the goal (n < dimword DIV 8 must be an assumption)  *)
let ASP2AUX_GET_NUM_TAC (ntm:term) (atm:term) : tactic = fun (asl,w as g) ->
  let pr = mk_pair(mk_comb(`data_Number`, mk_comb(`(&):num->int`, ntm)), atm) in
  let th = snd(find (fun (_,th) -> asp2_head_is "memory_rel" (concl th) &&
                                   can (find_term ((=) pr)) (concl th)) asl) in
  (MP_TAC (SPECL [ntm; atm] (MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_get_num) th)) THEN
   ASM_REWRITE_TAC[MEM; PAIR_EQ]) g;;

let ASP2AUX_DIV8_lt_dimword = prove
 (`!k. k < dimword (:A) DIV 8 ==> k < dimword (:A) /\ k DIV 4 < dimword (:A)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `dimword (:A) DIV 8 <= dimword (:A) /\ k DIV 4 <= k` MP_TAC THENL
   [REWRITE_TAC[DIV_LE]; ASM_ARITH_TAC]);;

(* the goal  ?ck ms. (x,S1) = (y,S2) /\ ...  (or with the pair equation     *)
(* split): instantiate ck and ms with the clock and the stack_max of S1      *)
let ASP2AUX_EXISTS_CLOCK_MAX_TAC : tactic = fun (asl,w as g) ->
  let ck,b1 = dest_exists w in
  let ms,b2 = dest_exists b1 in
  let e = fst(dest_conj b2) in
  let s1 = if is_conj e then lhs(snd(dest_conj e))
           else if is_pair(lhs e) then snd(dest_pair(lhs e)) else lhs e in
  (EXISTS_TAC (list_mk_icomb "wl_state_clock" [s1]) THEN
   EXISTS_TAC (list_mk_icomb "wl_state_stack_max" [s1])) g;;

let ASP2AUX_do_app_CopyByte = prove
 (`!vals (x:(C,FFI)data_state) v s2.
     data_do_app (MemOp (CopyByte F)) vals x = Rval (v,s2) <=>
     ?src_b src srcoff le dst_b dst dstoff fl1 ws fl ds ds1.
       vals = [data_RefPtr src_b src; data_Number srcoff; data_Number le;
               data_RefPtr dst_b dst; data_Number dstoff] /\
       lookup src (data_state_refs x) = SOME (bvl_ByteArray fl1 ws) /\
       lookup dst (data_state_refs x) = SOME (bvl_ByteArray fl ds) /\
       copy_array (ws,srcoff) le (SOME (ds,dstoff)) = SOME ds1 /\ v = data_Unit /\
       s2 = data_state_refs_fupd
              (combin_K (insert dst (bvl_ByteArray fl ds1) (data_state_refs x)))
              (do_stack (MemOp (CopyByte F)) vals
                 (do_lim_safe x (MemOp (CopyByte F)) vals))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; MEM] THEN
  CAKE_REWRITE_TAC[op_space_reset_def; op_space_req_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [data_do_app_aux_def] THEN
  CAKE_REWRITE_TAC[ASP2AUX_do_stack_lim_safe] THEN
  EQ_TAC THENL
   [REWRITE_TAC(all_case_eqs()) THEN CAKE_REWRITE_TAC[] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[CONS_11; injectivity "data_v"] THEN
    SIMP[];
    STRIP_TAC THEN RVEQ_TAC THEN ASP2AUX_CRW_TAC[ASP2AUX_do_stack_lim_safe]]);;

let ASP2AUX_copy_array_bounds = prove
 (`!(xs:A list) srcoff le ys dstoff zs.
     copy_array (xs,srcoff) le (SOME (ys,dstoff)) = SOME zs ==>
     ?xp yp n. srcoff = &xp /\ dstoff = &yp /\ le = &n /\
               xp + n <= LENGTH xs /\ yp + n <= LENGTH ys`,
  REPEAT GEN_TAC THEN REWRITE_TAC[copy_array_def; I_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; not_less_zero_int_eq]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (is_exists o concl)) ORELSE
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[not_less_zero_int_eq]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o check (is_exists o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_ADD; INT_ABS_NUM; NUM_OF_INT_OF_NUM; NOT_LT]) THEN
  REWRITE_TAC[INT_OF_NUM_EQ; UNWIND_THM1] THEN ASM_MESON_TAC[]);;

let ASP2AUX_ByteArray_LENGTH = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl p v vars fl vals.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl p,v:A word_loc) vars) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\ good_dimindex (:A) ==>
     LENGTH vals < dimword (:A) DIV 8`,
  REPEAT STRIP_TAC THEN
  DRULE_ALL memory_rel_ByteArray_IMP THEN STRIP_TAC THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let ASP2AUX_bwd_addr = prove
 (`!a b x n:A word.
     word_sub (word_add (word_add (word_add a b) x) n) (word 1) =
     word_add (word_add a (word_add b x)) (word_sub n (word 1))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let ASP2AUX_ByteCopy_code_thm = prove
 (`!c (t0:(A,C,FFI)wl_state) l1 l2 wsrc sw lw wdst ow asrc adst xp yp len m1.
     lookup ByteCopyAdd_location (wl_state_code t0) = SOME (5,ByteCopyAdd_code) /\
     lookup ByteCopySub_location (wl_state_code t0) = SOME (5,ByteCopySub_code) /\
     lookup 0 (wl_state_locals t0) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals t0) = SOME (wl_Word wsrc) /\
     lookup 4 (wl_state_locals t0) = SOME (wl_Word sw) /\
     lookup 6 (wl_state_locals t0) = SOME (wl_Word lw) /\
     lookup 8 (wl_state_locals t0) = SOME (wl_Word wdst) /\
     lookup 10 (wl_state_locals t0) = SOME (wl_Word ow) /\
     word_ushr sw 2 = word xp /\ word_ushr lw 2 = word len /\ word_ushr ow 2 = word yp /\
     xp < dimword (:A) /\ yp < dimword (:A) /\ len < dimword (:A) /\
     get_real_addr c (wl_state_store t0) wsrc = SOME asrc /\
     get_real_addr c (wl_state_store t0) wdst = SOME adst /\
     word_copy_array (wl_state_be t0) (word len) (word_add asrc bytes_in_word) (word xp)
       (word_add adst bytes_in_word) (word yp) (wl_state_memory t0)
       (wl_state_mdomain t0) = SOME m1 /\
     len DIV 4 < wl_state_clock t0 /\
     good_dimindex (:A) /\ shift_length c < dimindex (:A) ==>
     ?ck ms.
       wl_evaluate (ByteCopy_code c,t0) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word (word 2)]),
          wl_state_clock_fupd (combin_K ck) (wl_state_memory_fupd (combin_K m1)
            (wl_state_locals_fupd (combin_K LN) (wl_state_locals_size_fupd (combin_K (SOME 0))
              (wl_state_stack_max_fupd (combin_K ms) t0))))) /\
       option_le (wl_state_stack_max t0) ms /\
       option_le ms (OPTION_MAP2 MAX (wl_state_stack_max t0)
         (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t0))
            (OPTION_MAP2 MAX (lookup ByteCopyAdd_location (wl_state_stack_size t0))
                             (lookup ByteCopySub_location (wl_state_stack_size t0)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word xp:A word) = xp /\ val (word yp:A word) = yp /\
                val (word len:A word) = len` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_EQ_EQ; GSYM dimword_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `word_copy_array (wl_state_be (t0:(A,C,FFI)wl_state)) (word len)
       (word_add asrc bytes_in_word) (word xp)
       (word_add adst bytes_in_word) (word yp) (wl_state_memory t0)
       (wl_state_mdomain t0) = SOME m1` THEN
  REWRITE_TAC[word_copy_array_def; WORD_ULE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV ByteCopy_code_def)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_ShiftVar_2) THEN
  ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
    [data_to_word_Unit_def; WORD_ULT; WORD_ADD_0]) THEN
  SUBGOAL_THEN `~(wl_state_clock (t0:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE] THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN DISCH_TAC THEN
    ASP2AUX_EVAL_LEMMA_TAC `ByteCopyAdd_code:(A)wl_prog` (fun st ->
      ISPECL [`wl_state_be (t0:(A,C,FFI)wl_state)`; `word len:A word`;
              `word_add asrc (word_add bytes_in_word (word xp)):A word`;
              `word_add adst (word_add bytes_in_word (word yp)):A word`;
              `wl_state_memory (t0:(A,C,FFI)wl_state)`;
              `wl_state_mdomain (t0:(A,C,FFI)wl_state)`;
              `wl_Word (word 2):A word_loc`; `l1:num`; `l2:num`; st;
              `m1:A word->A word_loc`] CopyByteAdd_thm) THEN
    ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ [wl_bad_fun_return_def; PAIR_EQ]) THEN
    ASP2AUX_EXISTS_CLOCK_MAX_TAC THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[OPTION_MAP2_MAX_CANCEL; COND_ID] THEN ASP2AUX_OPTION_ARITH_TAC;
    REWRITE_TAC[ASP2AUX_bwd_addr] THEN DISCH_TAC THEN
    ASP2AUX_EVAL_LEMMA_TAC `ByteCopySub_code:(A)wl_prog` (fun st ->
      ISPECL [`wl_state_be (t0:(A,C,FFI)wl_state)`; `word len:A word`;
              `word_add (word_add asrc (word_add bytes_in_word (word xp)))
                 (word_sub (word len) (word 1)):A word`;
              `word_add (word_add adst (word_add bytes_in_word (word yp)))
                 (word_sub (word len) (word 1)):A word`;
              `wl_state_memory (t0:(A,C,FFI)wl_state)`;
              `wl_state_mdomain (t0:(A,C,FFI)wl_state)`;
              `wl_Word (word 2):A word_loc`; `l1:num`; `l2:num`; st;
              `m1:A word->A word_loc`] CopyByteSub_thm) THEN
    ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ [wl_bad_fun_return_def; PAIR_EQ]) THEN
    ASP2AUX_EXISTS_CLOCK_MAX_TAC THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[OPTION_MAP2_MAX_CANCEL; COND_ID] THEN ASP2AUX_OPTION_ARITH_TAC]);;

(* HOL4 line 3469 *)
let assign_CopyByte = prove
 (assign_thm_stmt `(?new_flag. op = MemOp (CopyByte new_flag) /\ ~new_flag)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `new_flag:bool` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `new_flag = F` SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?kept_names. names_opt = SOME (kept_names:num_set)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(op_requires_names (MemOp (CopyByte F)) <=>
                   names_opt = (NONE:num_set option))` THEN
    REWRITE_TAC[op_requires_names_def] THEN MESON_TAC[option_nchotomy];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `vals:data_v list`;
    `kept_names:num_set`; `x:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (MemOp (CopyByte F)) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP2AUX_do_app_CopyByte; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`src_b:bool`; `src:num`; `srcoff:int`; `le:int`; `dst_b:bool`;
    `dst:num`; `dstoff:int`; `fl1:bool`; `xs:byte list`; `fl:bool`; `ys:byte list`;
    `ys1:byte list`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  SUBGOAL_THEN `?e1 e2 e3 e4 e5. args = [e1:num; e2; e3; e4; e5]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_5] THEN ASM_REWRITE_TAC[LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `?w1 w2 w3 w4 w5. ws = [w1:A word_loc; w2; w3; w4; w5]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_5] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `LENGTH (ws:(A word_loc)list)`)) THEN
    ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM; MAP]) THEN
  FIRST_ASSUM(MP_TAC o check ((=) `wl_get_vars [adjust_var e1; adjust_var e2; adjust_var e3; adjust_var e4;
                  adjust_var e5] (t:(A,C,FFI)wl_state) = SOME [w1; w2; w3; w4; w5]` o concl)) THEN
  ASP2AUX_GET_VARS_TAC THEN
  SUBGOAL_THEN `wl_get_vars (MAP adjust_var [e1; e2; e3; e4; e5]) (t:(A,C,FFI)wl_state) =
                SOME [w1; w2; w3; w4; w5]` ASSUME_TAC THENL [ASM_REWRITE_TAC[MAP]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2
      (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
  CAKE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  DRULE_ALL memory_rel_get_vars_IMP THEN
  REWRITE_TAC[ZIP; APPEND; MAP] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `xp:num` (X_CHOOSE_THEN `yp:num` (X_CHOOSE_THEN `len:num`
    STRIP_ASSUME_TAC)) o MATCH_MP ASP2AUX_copy_array_bounds) THEN RVEQ_TAC THEN
  ASP2AUX_DRULE_N 3 ASP2AUX_ByteArray_LENGTH THEN DISCH_TAC THEN
  ASP2AUX_MEMREL_PICK_TAC (fun t -> can (find_term ((=) `data_Number (&yp)`)) t) [3; 0] THEN
  ASP2AUX_DRULE_N 3 ASP2AUX_ByteArray_LENGTH THEN DISCH_TAC THEN
  SUBGOAL_THEN `xp < dimword (:A) DIV 8 /\ yp < dimword (:A) DIV 8 /\
                len < dimword (:A) DIV 8` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`xp + len <= LENGTH (xs:byte list)`;
      `yp + len <= LENGTH (ys:byte list)`; `LENGTH (xs:byte list) < dimword (:A) DIV 8`;
      `LENGTH (ys:byte list) < dimword (:A) DIV 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASP2AUX_GET_NUM_TAC `xp:num` `w2:A word_loc` THEN
  DISCH_THEN(X_CHOOSE_THEN `sw:A word` STRIP_ASSUME_TAC) THEN
  ASP2AUX_GET_NUM_TAC `len:num` `w3:A word_loc` THEN
  DISCH_THEN(X_CHOOSE_THEN `lw:A word` STRIP_ASSUME_TAC) THEN
  ASP2AUX_GET_NUM_TAC `yp:num` `w5:A word_loc` THEN
  DISCH_THEN(X_CHOOSE_THEN `ow:A word` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN
   `?wsrc wdst asrc adst m1.
      w1 = wl_Word wsrc /\ w4 = wl_Word wdst /\
      get_real_addr c (wl_state_store t) wsrc = SOME asrc /\
      get_real_addr c (wl_state_store t) wdst = SOME adst /\
      word_copy_array (wl_state_be t) (word len) (word_add asrc bytes_in_word) (word xp)
        (word_add adst bytes_in_word) (word yp) (wl_state_memory t)
        (wl_state_mdomain (t:(A,C,FFI)wl_state)) = SOME m1 /\
      memory_rel c (wl_state_be t) (THE (data_state_tstamps s))
        (insert dst (bvl_ByteArray fl ys1) (data_state_refs (s:(C,FFI)data_state)))
        (data_state_space s) (wl_state_store t) m1 (wl_state_mdomain t)
        (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
           (CONS (the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)
              (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))`
   STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `src:num = dst` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASP2AUX_SOME_UNIQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[injectivity "bvl_ref"]) THEN
      REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
      RVEQ_TAC THEN
      ASP2AUX_DRULE_N 4 word_copy_array_alias_thm THEN
      DISCH_THEN(X_CHOOSE_THEN `wd:A word` (X_CHOOSE_THEN `ad:A word`
        (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
      RVEQ_TAC THEN
      ASP2AUX_MEMREL_PICK_TAC (fun t -> can (find_term ((=) `data_Number (&yp)`)) t &&
        can (find_term ((=) `wl_state_memory (t:(A,C,FFI)wl_state)`)) t) [0; 3] THEN
      ASP2AUX_DRULE_N 3 memory_rel_ByteArray_IMP THEN
      DISCH_THEN(X_CHOOSE_THEN `ws:A word` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
      ASP2AUX_DRULE_N 3 memory_rel_RefPtr_EQ_IMP THEN DISCH_TAC THEN RVEQ_TAC THEN
      MAP_EVERY EXISTS_TAC [`wd:A word`; `wd:A word`; `ad:A word`; `ad:A word`;
                            `m1:A word->A word_loc`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
        can (find_term ((=) `m1:A word->A word_loc`)) (concl th))) THEN
      DISCH_THEN(ACCEPT_TAC o MATCH_MP memory_rel_tl o MATCH_MP memory_rel_tl);
      ASP2AUX_MEMREL_PICK_TAC (fun t -> can (find_term ((=) `data_Number (&yp)`)) t &&
        can (find_term ((=) `wl_state_memory (t:(A,C,FFI)wl_state)`)) t) [0; 3] THEN
      ASP2AUX_DRULE_N 6 word_copy_array_thm THEN
      DISCH_THEN(X_CHOOSE_THEN `ws:A word` (X_CHOOSE_THEN `wd:A word`
        (X_CHOOSE_THEN `as:A word` (X_CHOOSE_THEN `ad:A word`
        (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))))) THEN
      RVEQ_TAC THEN
      MAP_EVERY EXISTS_TAC [`ws:A word`; `wd:A word`; `as:A word`; `ad:A word`;
                            `m1:A word->A word_loc`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
        can (find_term ((=) `m1:A word->A word_loc`)) (concl th))) THEN
      DISCH_THEN(ACCEPT_TAC o MATCH_MP memory_rel_tl o MATCH_MP memory_rel_tl)];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  ASP2AUX_STUB_TAC `lookup ByteCopy_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                    SOME (6,ByteCopy_code c)` THEN
  ASP2AUX_STUB_TAC `lookup ByteCopyAdd_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                    SOME (5,ByteCopyAdd_code)` THEN
  ASP2AUX_STUB_TAC `lookup ByteCopySub_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                    SOME (5,ByteCopySub_code)` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(num#A word_loc)list` (X_CHOOSE_THEN `perm:num->num->num`
    ASSUME_TAC)) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN
  CAKE_REWRITE_TAC[assign_CopyByte_def; data_to_word_get_names_def] THEN
  ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
    [domain_adjust_sets; ALL_DISTINCT; MEM; adjust_var_NEQ; adjust_var_11;
     MustTerminate_limit_NOT_0; wl_push_env_def; LET_DEF; LET_END_DEF]) THEN
  ASP2AUX_EVAL_LEMMA_TAC `ByteCopy_code c:(A)wl_prog` (fun st ->
    ISPECL [`c:data_to_word_config`; st; `n:num`; `l:num`; `wsrc:A word`; `sw:A word`;
            `lw:A word`; `wdst:A word`; `ow:A word`; `asrc:A word`; `adst:A word`;
            `xp:num`; `yp:num`; `len:num`; `m1:A word->A word_loc`]
           ASP2AUX_ByteCopy_code_thm) THEN
  ANTS_TAC THENL
   [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [push_env_store; wl_push_env_clock]) THEN
    CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
    ASM_SIMP_TAC[ASP2AUX_DIV8_lt_dimword; IMP_LESS_MustTerminate_limit];
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `ms:num option`
      STRIP_ASSUME_TAC))] THEN
  ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [push_env_store; wl_push_env_clock; wl_push_env_def; wl_pop_env_def;
       wl_set_vars_def; alist_insert_def; LET_DEF; LET_END_DEF; LENGTH;
       wl_bad_fun_return_def]) THEN
  SUBGOAL_THEN `domain (sptree_union (fromAList (q:(num#A word_loc)list))
                  (fromAList (toAList (y1:(A word_loc)spt)))) =
                domain y1 UNION domain (y2:(A word_loc)spt)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[domain_union; domain_fromAList_toAList] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP env_to_list_domain) THEN SET_TAC[];
    ALL_TAC] THEN
  ASP2AUX_CRW_TAC [option_DISTINCT; injectivity "wl_result"] THEN
  ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM;
              ASP2AUX_do_stack_lim_safe; wl_state_INFO.ri_accfupds] THEN
  CAKE_REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM] o
    MATCH_MP ASP2AUX_cut_state_opt_cut_env) THEN
  REPEAT CONJ_TAC THENL
   [ASP2AUX_DRULE_N 3 ASP2AUX_cut_ret_lookup_0 THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ASP2AUX_DRULE_N 3 ASP2AUX_cut_ret_IS_SOME THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ALL_TAC;
    ALL_TAC;
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Unit o
      (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
      check (fun th -> asp2_head_is "memory_rel" (concl th) &&
             can (find_term ((=) `m1:A word->A word_loc`)) (concl th))) THEN
    DISCH_TAC THEN
    ASP2AUX_DRULE_N 4 ASP2AUX_memory_rel_cut_ret THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_rel_IMP_size_of_stack) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "option_le" (concl th) &&
    free_in `ms:num option` (concl th)))) THEN
  UNDISCH_TAC `option_le (wl_state_stack_max (t:(A,C,FFI)wl_state))
                 (data_state_stack_max (s:(C,FFI)data_state))` THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; stack_size_eq; stack_consumed_def] THEN
  ASP2AUX_OPTION_ARITH_TAC);;

let ASP2AUX_word_zx_byte_11 = prove
 (`!b1 b2:byte. good_dimindex (:A) ==>
     ((word_zx b1:A word) = word_zx b2 <=> b1 = b2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word_zx:A word->byte`) THEN
  ASM_SIMP_TAC[good_dimindex_w2w_byte]);;

let ASP2AUX_OPTION_CASES_TAC tm v : tactic =
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN v ASSUME_TAC) (ISPEC tm option_nchotomy);;

(* HOL4 line 4094 *)
let evaluate_StringCmpLoop = prove
 (`!a1 a2 r1 r2 len be ck dm m l1 l2 (t1:(A,C,FFI)wl_state) x1 x2.
     word_str_cmp_loop a1 a2 r1 r2 len dm m be ck = SOME (x1,x2) /\
     wl_state_memory t1 = m /\ wl_state_mdomain t1 = dm /\ be = wl_state_be t1 /\
     ck < wl_state_clock t1 /\ good_dimindex (:A) /\
     lookup StringCmpLoop_location (wl_state_code t1) = SOME (6,StringCmpLoop_code) /\
     wl_get_var 0 t1 = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 t1 = SOME (wl_Word a1) /\
     wl_get_var 4 t1 = SOME (wl_Word a2) /\
     wl_get_var 6 t1 = SOME (wl_Word len) /\
     wl_get_var 8 t1 = SOME (wl_Word r1) /\
     wl_get_var 10 t1 = SOME (wl_Word r2) ==>
     ?ck max_stack.
       wl_evaluate (StringCmpLoop_code,t1) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word x1; wl_Word x2]),
          wl_state_clock_fupd (combin_K ck) (wl_state_stack_max_fupd (combin_K max_stack)
            (wl_state_locals_fupd (combin_K LN) (wl_state_locals_size_fupd (combin_K (SOME 0)) t1)))) /\
       (~(max_stack = wl_state_stack_max t1) ==>
        max_stack = OPTION_MAP2 MAX (wl_state_stack_max t1)
                      (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1))
                         (lookup StringCmpLoop_location (wl_state_stack_size t1))))`,
  SUBGOAL_THEN
   `!ck a1 a2 r1 r2 len be dm m l1 l2 (t1:(A,C,FFI)wl_state) x1 x2.
     word_str_cmp_loop a1 a2 r1 r2 len dm m be ck = SOME (x1,x2) /\
     wl_state_memory t1 = m /\ wl_state_mdomain t1 = dm /\ be = wl_state_be t1 /\
     ck < wl_state_clock t1 /\ good_dimindex (:A) /\
     lookup StringCmpLoop_location (wl_state_code t1) = SOME (6,StringCmpLoop_code) /\
     wl_get_var 0 t1 = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 t1 = SOME (wl_Word a1) /\
     wl_get_var 4 t1 = SOME (wl_Word a2) /\
     wl_get_var 6 t1 = SOME (wl_Word len) /\
     wl_get_var 8 t1 = SOME (wl_Word r1) /\
     wl_get_var 10 t1 = SOME (wl_Word r2) ==>
     ?ck max_stack.
       wl_evaluate (StringCmpLoop_code,t1) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word x1; wl_Word x2]),
          wl_state_clock_fupd (combin_K ck) (wl_state_stack_max_fupd (combin_K max_stack)
            (wl_state_locals_fupd (combin_K LN) (wl_state_locals_size_fupd (combin_K (SOME 0)) t1)))) /\
       (~(max_stack = wl_state_stack_max t1) ==>
        max_stack = OPTION_MAP2 MAX (wl_state_stack_max t1)
                      (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1))
                         (lookup StringCmpLoop_location (wl_state_stack_size t1))))`
   (fun th -> MAP_EVERY X_GEN_TAC [`a1:A word`; `a2:A word`; `r1:A word`; `r2:A word`;
       `len:A word`; `be:bool`; `ck:num`; `dm:A word->bool`; `m:A word->A word_loc`;
       `l1:num`; `l2:num`; `t1:(A,C,FFI)wl_state`; `x1:A word`; `x2:A word`] THEN
     MATCH_ACCEPT_TAC (SPECL [`ck:num`; `a1:A word`; `a2:A word`; `r1:A word`; `r2:A word`;
       `len:A word`; `be:bool`; `dm:A word->bool`; `m:A word->A word_loc`;
       `l1:num`; `l2:num`; `t1:(A,C,FFI)wl_state`; `x1:A word`; `x2:A word`] th)) THEN
  INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[word_str_cmp_loop_def] THEN REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) then LABEL_TAC "IH" th
                          else failwith "IH") THEN
  ONCE_REWRITE_TAC[word_str_cmp_loop_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
  MAP_EVERY X_GEN_TAC [`a1:A word`; `a2:A word`; `r1:A word`; `r2:A word`;
    `len:A word`; `be:bool`; `dm:A word->bool`; `m:A word->A word_loc`;
    `l1:num`; `l2:num`; `t1:(A,C,FFI)wl_state`; `x1:A word`; `x2:A word`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV StringCmpLoop_code_def)) THEN
  SUBGOAL_THEN `!w:byte. word_zx (word_zx w:A word) = w` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_dimindex_w2w_byte]; ALL_TAC] THEN
  UNDISCH_TAC `be = wl_state_be (t1:(A,C,FFI)wl_state)` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `!b1 b2:byte. (word_zx b1:A word = word_zx b2) <=> b1 = b2` ASSUME_TAC THENL
   [ASM_MESON_TAC[ASP2AUX_word_zx_byte_11]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
    MAP_EVERY EXISTS_TAC [`wl_state_clock (t1:(A,C,FFI)wl_state)`;
                          `wl_state_stack_max (t1:(A,C,FFI)wl_state)`] THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASP2AUX_OPTION_CASES_TAC `mem_load_byte_aux m dm be (a1:A word)` `b1:byte` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  ASP2AUX_OPTION_CASES_TAC `mem_load_byte_aux m dm be (a2:A word)` `b2:byte` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `b1:byte = b2` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~(wl_state_clock (t1:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`word_add a1 (word 1):A word`;
      `word_add a2 (word 1):A word`; `r1:A word`; `r2:A word`;
      `word_sub len (word 1):A word`; `be:bool`; `dm:A word->bool`;
      `m:A word->A word_loc`; `l1:num`; `l2:num`]) THEN
    ASP2AUX_SPEC_EVAL_TAC `StringCmpLoop_code:(A)wl_prog`
      (fun st -> [st; `x1:A word`; `x2:A word`]) THEN
    ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `ms:num option`
      STRIP_ASSUME_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM;
                                OPTION_MAP2_MAX_CANCEL]) THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ [wl_bad_fun_return_def; PAIR_EQ]) THEN
    MAP_EVERY EXISTS_TAC [`ck':num`; `ms:num option`] THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
    MAP_EVERY EXISTS_TAC [`wl_state_clock (t1:(A,C,FFI)wl_state)`;
                          `wl_state_stack_max (t1:(A,C,FFI)wl_state)`] THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]]);;

(* HOL4 line 4153 *)
let evaluate_AssignCmp = prove
 (CASE_TERM
  `!dest cmp v1 v2 (s:(A,C,FFI)wl_state).
     wl_evaluate (AssignCmp dest cmp v1 v2,s) =
     match (wl_get_var v1 s,wl_get_var v2 s) with
       (SOME (wl_Word x1),SOME (wl_Word x2)) ->
         (NONE,wl_set_var dest
                 (if num_cmp cmp (val x1) (val x2) then wl_Word (word 18)
                  else wl_Word (word 2)) s)
     | _ -> wl_evaluate (AssignCmp dest cmp v1 v2,s)`,
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  CASES_ON `cmp:opb` THEN
  ASM_REWRITE_TAC[AssignCmp_def; SetBool_def; wl_evaluate_def; wl_get_var_imm_def] THEN
  CAKE_REWRITE_TAC[wl_word_cmp_def; wl_word_exp_def; num_cmp_def; WORD_ULT; GT; GE; NOT_LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_cmp_def; GT; GE]) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4166 (local) *)
let evaluate_StringCmpMin = prove
 (CASE_TERM
  `!p (t1:(A,C,FFI)wl_state) l.
     wl_evaluate
       (wl_Seq (wl_Assign 9 (wl_Var 5))
          (wl_Seq (wl_If Lower 7 (Reg 5) (wl_Assign 9 (wl_Var 7)) wl_Skip) p),
        wl_state_locals_fupd (combin_K l) t1) =
     match (lookup 5 l,lookup 7 l) with
       (SOME (wl_Word w1),SOME (wl_Word w2)) ->
         wl_evaluate (p,wl_state_locals_fupd
           (combin_K (insert 9 (wl_Word (word (MIN (val w1) (val w2)))) l)) t1)
     | _ ->
         wl_evaluate
           (wl_Seq (wl_Assign 9 (wl_Var 5))
              (wl_Seq (wl_If Lower 7 (Reg 5) (wl_Assign 9 (wl_Var 7)) wl_Skip) p),
            wl_state_locals_fupd (combin_K l) t1)`,
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  ASP2AUX_CRW_TAC asp2_eval_rws THEN
  REWRITE_TAC[WORD_ULT; MIN] THEN
  COND_CASES_TAC THEN ASP2AUX_CRW_TAC (asp2_eval_rws @ [WORD_VAL]) THEN
  ASM_SIMP_TAC[GSYM NOT_LT; WORD_VAL]);;

let ASP2AUX_do_app_StringCmp = prove
 (`!b cmp vals (x:(C,FFI)data_state) v s2.
     data_do_app (MemOp (StringCmp b cmp)) vals x = Rval (v,s2) <=>
     ?b1 p1 b2 p2 f1 ws1 f2 ws2.
       vals = [data_RefPtr b1 p1; data_RefPtr b2 p2] /\
       lookup p1 (data_state_refs x) = SOME (bvl_ByteArray f1 ws1) /\
       lookup p2 (data_state_refs x) = SOME (bvl_ByteArray f2 ws2) /\
       v = data_Boolv (str_cmp b cmp (implode (MAP (CHR o val) ws1))
                                     (implode (MAP (CHR o val) ws2))) /\
       s2 = do_stack (MemOp (StringCmp b cmp)) vals
              (do_lim_safe x (MemOp (StringCmp b cmp)) vals)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; MEM] THEN
  CAKE_REWRITE_TAC[op_space_reset_def; op_space_req_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [data_do_app_aux_def] THEN
  CAKE_REWRITE_TAC[ASP2AUX_do_stack_lim_safe; LET_DEF; LET_END_DEF] THEN
  EQ_TAC THENL
   [REWRITE_TAC(all_case_eqs()) THEN CAKE_REWRITE_TAC[] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[CONS_11; injectivity "data_v"] THEN
    SIMP[];
    STRIP_TAC THEN RVEQ_TAC THEN ASP2AUX_CRW_TAC[ASP2AUX_do_stack_lim_safe; LET_DEF;
      LET_END_DEF]]);;

(* the join_env entries of a cut environment (without a call) *)
let ASP2AUX_join_env_cut_MEM_nocall = prove
 (`!kept_names (s_locals:data_v spt) xl (t_locals:(A word_loc)spt) x.
     data_cut_env kept_names s_locals = SOME xl /\
     MEM x (join_env xl (toAList (sptree_inter t_locals (adjust_set xl)))) ==>
     MEM x (join_env s_locals (toAList (sptree_inter t_locals (adjust_set s_locals))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; mk_wf_inter]) THEN
  FIRST_X_ASSUM(MP_TAC o check (asp2_head_is "MEM" o concl)) THEN
  REWRITE_TAC[join_env_def; MEM_MAP; MEM_FILTER; EXISTS_PAIR_THM; MEM_toAList;
              mk_wf_inter] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `v:A word_loc` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `v:A word_loc`] THEN
  UNDISCH_TAC `lookup k (sptree_inter (t_locals:(A word_loc)spt)
      (adjust_set (sptree_inter (s_locals:data_v spt) (kept_names:num_set)))) = SOME (v:A word_loc)` THEN
  REWRITE_TAC[lookup_inter_alt; IN_domain_adjust_set_inter] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k - 2) DIV 2 IN domain (kept_names:num_set)` ASSUME_TAC THENL
   [UNDISCH_TAC `k IN domain (adjust_set (kept_names:num_set))` THEN
    REWRITE_TAC[domain_lookup; lookup_adjust_set] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    ASM_REWRITE_TAC[domain_lookup];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_inter_alt]);;

let ASP2AUX_word_MIN = prove
 (`!x y:A word. word (MIN (val x) (val y)) = if word_ult y x then y else x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ULT; MIN] THEN
  ASM_CASES_TAC `val (y:A word) < val (x:A word)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(val (x:A word) <= val (y:A word))` (fun th -> REWRITE_TAC[th; WORD_VAL])
    THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `val (x:A word) <= val (y:A word)` (fun th -> REWRITE_TAC[th; WORD_VAL])
    THEN ASM_ARITH_TAC]);;

let ASP2AUX_dimword_lt_MustTerminate = prove
 (`dimword (:A) < MustTerminate_limit (:A) - 1`,
  REWRITE_TAC[MustTerminate_limit_DEF] THEN
  SUBGOAL_THEN `2 <= dimword (:A)` MP_TAC THENL
   [REWRITE_TAC[dimword_def] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 1` THEN
    REWRITE_TAC[LE_EXP; DIMINDEX_GE_1] THEN ARITH_TAC;
    ARITH_TAC]);;

let ASP2AUX_evaluate_AssignCmp_Word = prove
 (`!dest cmp v1 v2 (s:(A,C,FFI)wl_state) x1 x2.
     wl_get_var v1 s = SOME (wl_Word x1) /\ wl_get_var v2 s = SOME (wl_Word x2) ==>
     wl_evaluate (AssignCmp dest cmp v1 v2,s) =
     (NONE,wl_set_var dest
             (if num_cmp cmp (val x1) (val x2) then wl_Word (word 18)
              else wl_Word (word 2)) s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[evaluate_AssignCmp] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* the first wl_evaluate (AssignCmp dest cmp v1 v2,st) of the goal gets its *)
(* value as an assumption; the variables are computed by rewriting         *)
let ASP2AUX_ASSIGNCMP_TAC thl : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t ->
      try let f,a = dest_comb t in
          fst(dest_const f) = "wl_evaluate" &&
          asp2_head_is "AssignCmp" (fst(dest_pair a))
      with Failure _ -> false) w in
  let p,st = dest_pair(rand tm) in
  let _,args = strip_comb p in
  let v1 = el 2 args and v2 = el 3 args in
  let th1 = asp2_crw_conv asl thl (list_mk_icomb "wl_get_var" [v1; st]) in
  let th2 = asp2_crw_conv asl thl (list_mk_icomb "wl_get_var" [v2; st]) in
  let x1 = rand(rand(rhs(concl th1))) and x2 = rand(rand(rhs(concl th2))) in
  let th = MP (ISPECL [el 0 args; el 1 args; v1; v2; st; x1; x2]
                 ASP2AUX_evaluate_AssignCmp_Word) (CONJ th1 th2) in
  ASSUME_TAC th g;;

let ASP2AUX_cut_ret_lookup_0_union = prove
 (`!(kept_names:num_set) (t_locals:(A word_loc)spt) y1 y2 p q perm l1 l2.
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,perm) /\
     lookup 0 t_locals = SOME (wl_Loc l1 l2) ==>
     lookup 0 (sptree_union (fromAList q) (fromAList (toAList y1))) = SOME (wl_Loc l1 l2)`,
  REPEAT STRIP_TAC THEN DRULE_ALL cut_envs_lookup_0 THEN
  ASM_REWRITE_TAC[lookup_union; lookup_fromAList; ALOOKUP_toAList] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let ASP2AUX_cut_ret_IS_SOME_57 = prove
 (`!(kept_names:num_set) (s_locals:data_v spt) xl (t_locals:(A word_loc)spt) y1 y2 p q
    perm dest v ret r5 r7.
     data_cut_env kept_names s_locals = SOME xl /\
     cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) /\
     env_to_list y2 p = (q,perm) ==>
     !n. IS_SOME (lookup n (insert dest v xl)) ==>
         IS_SOME (lookup (adjust_var n) (insert (adjust_var dest) ret
                   (insert 5 r5 (insert 7 r7
                     (sptree_union (fromAList q) (fromAList (toAList y1)))))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`dest:num`; `v:data_v`; `ret:A word_loc`] o
    MATCH_MP ASP2AUX_cut_ret_IS_SOME) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(q ==> r) ==> (p ==> q) ==> (p ==> r)`) THEN
  REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN
  REWRITE_TAC[adjust_var_NEQ]);;

(* no call: the IS_SOME part of state_rel after a cut and inserts *)
let ASP2AUX_nocall_IS_SOME = prove
 (`!(kept_names:num_set) (s_locals:data_v spt) xl (t_locals:(A word_loc)spt)
    (l:(A word_loc)spt) dest v (w:A word_loc).
     (!n. IS_SOME (lookup n s_locals) ==> IS_SOME (lookup (adjust_var n) t_locals)) /\
     data_cut_env kept_names s_locals = SOME xl /\
     (!k. IS_SOME (lookup k t_locals) ==> IS_SOME (lookup k l)) ==>
     !n. IS_SOME (lookup n (insert dest v xl)) ==>
         IS_SOME (lookup (adjust_var n) (insert (adjust_var dest) w l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN GEN_TAC THEN
  REWRITE_TAC[lookup_insert; adjust_var_11] THEN COND_CASES_TAC THEN
  REWRITE_TAC[IS_SOME_DEF; mk_wf_inter; lookup_inter_alt] THEN
  COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[]);;

(* evaluate_StringCmpLoop with the return location and the state first and *)
(* the loop equation as a separate antecedent                              *)
let ASP2AUX_StringCmpLoop_cur = prove
 (`!l1 l2 (t1:(A,C,FFI)wl_state) a1 a2 r1 r2 len be ck dm m x1 x2.
     word_str_cmp_loop a1 a2 r1 r2 len dm m be ck = SOME (x1,x2) ==>
     wl_state_memory t1 = m /\ wl_state_mdomain t1 = dm /\ be = wl_state_be t1 /\
     ck < wl_state_clock t1 /\ good_dimindex (:A) /\
     lookup StringCmpLoop_location (wl_state_code t1) = SOME (6,StringCmpLoop_code) /\
     wl_get_var 0 t1 = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 t1 = SOME (wl_Word a1) /\
     wl_get_var 4 t1 = SOME (wl_Word a2) /\
     wl_get_var 6 t1 = SOME (wl_Word len) /\
     wl_get_var 8 t1 = SOME (wl_Word r1) /\
     wl_get_var 10 t1 = SOME (wl_Word r2) ==>
     ?ck max_stack.
       wl_evaluate (StringCmpLoop_code,t1) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word x1; wl_Word x2]),
          wl_state_clock_fupd (combin_K ck) (wl_state_stack_max_fupd (combin_K max_stack)
            (wl_state_locals_fupd (combin_K LN) (wl_state_locals_size_fupd (combin_K (SOME 0)) t1)))) /\
       (~(max_stack = wl_state_stack_max t1) ==>
        max_stack = OPTION_MAP2 MAX (wl_state_stack_max t1)
                      (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1))
                         (lookup StringCmpLoop_location (wl_state_stack_size t1))))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC evaluate_StringCmpLoop THEN
  MAP_EVERY EXISTS_TAC [`a1:A word`; `a2:A word`; `r1:A word`; `r2:A word`;
    `len:A word`; `be:bool`; `ck:num`; `dm:A word->bool`; `m:A word->A word_loc`] THEN
  ASM_REWRITE_TAC[]);;

(* MP_TAC the instance of ASP2AUX_StringCmpLoop_cur for the call of the goal *)
(* and the word_str_cmp_loop assumption                                     *)
let ASP2AUX_STRCMP_LEMMA_TAC : tactic = fun (asl,w as g) ->
  let st = asp2_eval_arg `StringCmpLoop_code:(A)wl_prog` w in
  let th = snd(find (fun (_,th) ->
      try asp2_head_is "word_str_cmp_loop" (lhs(concl th)) with Failure _ -> false) asl) in
  MP_TAC (MATCH_MP (ISPECL [`n:num`; `l:num`; st] ASP2AUX_StringCmpLoop_cur) th) g;;

let ASP2AUX_memory_rel_Boolv_COND = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars b.
     memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Boolv b,if b then wl_Word (word 18) else wl_Word (word 2:A word)) vars)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC memory_rel_Boolv THEN ASM_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

(* assign_StringCmp: from the call of StringCmpLoop (the variables have been *)
(* assigned) to the end                                                     *)
let ASP2AUX_STRCMP_CALL_TAC : tactic =
  ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
    [ASP2AUX_cut_envs_ins 1; ASP2AUX_cut_envs_ins 3; ASP2AUX_cut_envs_ins 5;
     ASP2AUX_cut_envs_ins 7; ASP2AUX_cut_envs_ins 9; ASP2AUX_cut_envs_ins 11;
     ASP2AUX_cut_envs_ins 13;
     domain_adjust_sets; ALL_DISTINCT; MEM; adjust_var_NEQ; adjust_var_11;
     MustTerminate_limit_NOT_0; wl_push_env_def; LET_DEF; LET_END_DEF]) THEN
  ASP2AUX_STRCMP_LEMMA_TAC THEN
  ANTS_TAC THENL
   [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [push_env_store; wl_push_env_clock; ASP2AUX_dimword_lt_MustTerminate]) THEN
    CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `ms:num option`
      STRIP_ASSUME_TAC))] THEN
  ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [push_env_store; wl_push_env_clock; wl_push_env_def; wl_pop_env_def;
       wl_set_vars_def; alist_insert_def; LET_DEF; LET_END_DEF; LENGTH;
       wl_bad_fun_return_def]) THEN
  SUBGOAL_THEN `domain (sptree_union (fromAList (q:(num#A word_loc)list))
                  (fromAList (toAList (y1:(A word_loc)spt)))) =
                domain y1 UNION domain (y2:(A word_loc)spt)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[domain_union; domain_fromAList_toAList] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP env_to_list_domain) THEN SET_TAC[];
    ALL_TAC] THEN
  ASP2AUX_CRW_TAC [option_DISTINCT; injectivity "wl_result"] THEN
  ASP2AUX_ASSIGNCMP_TAC asp2_eval_rws THEN
  ASP2AUX_CRW_TAC asp2_eval_rws THEN
  ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM;
              ASP2AUX_do_stack_lim_safe; wl_state_INFO.ri_accfupds] THEN
  CAKE_REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lookup_insert; adjust_var_NEQ; ARITH_EQ] THEN
    ASP2AUX_DRULE_N 3 ASP2AUX_cut_ret_lookup_0_union THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ASP2AUX_DRULE_N 3 ASP2AUX_cut_ret_IS_SOME_57 THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ALL_TAC;
    ALL_TAC;
    REWRITE_TAC[ASP2AUX_inter_ins 5; ASP2AUX_inter_ins 7; GSYM APPEND_ASSOC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `num_cmp cmp (val (r1:A word)) (val (r2:A word))` o
      MATCH_MP ASP2AUX_memory_rel_Boolv_COND o
      (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
      check (fun th -> asp2_head_is "memory_rel" (concl th) &&
        asp2_head_is "APPEND" (rand (concl th)))) THEN
    DISCH_TAC THEN
    ASP2AUX_DRULE_N 4 ASP2AUX_memory_rel_cut_ret THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]] THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM; OPTION_MAP2_MAX_CANCEL] o
    REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM;
      ASSUME `wl_state_stack_size (t:(A,C,FFI)wl_state) =
              data_state_stack_frame_sizes (s:(C,FFI)data_state)`] o
    check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
  ASP2AUX_EQ_FROM_NEG_IMP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_rel_IMP_size_of_stack) THEN
  ASM_REWRITE_TAC[stack_size_eq; stack_consumed_def] THEN
  UNDISCH_TAC `option_le (wl_state_stack_max (t:(A,C,FFI)wl_state))
                 (data_state_stack_max (s:(C,FFI)data_state))` THEN
  ASP2AUX_OPTION_ARITH_TAC;;

(* HOL4 line 4187 *)
let assign_StringCmp = prove
 (assign_thm_stmt `(?b cmp. op = MemOp (StringCmp b cmp))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `cmp:opb` SUBST_ALL_TAC)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?kept_names. names_opt = SOME (kept_names:num_set)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(op_requires_names (MemOp (StringCmp b cmp)) <=>
                   names_opt = (NONE:num_set option))` THEN
    REWRITE_TAC[op_requires_names_def] THEN MESON_TAC[option_nchotomy];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `vals:data_v list`;
    `kept_names:num_set`; `x:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (MemOp (StringCmp b cmp)) vals (x:(C,FFI)data_state) =
               Rval (v,s2)` THEN
  REWRITE_TAC[ASP2AUX_do_app_StringCmp; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:bool`; `p1:num`; `b2:bool`; `p2:num`; `f1:bool`;
    `bs1:byte list`; `f2:bool`; `bs2:byte list`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  SUBGOAL_THEN `?a1 a2. args = [a1:num; a2]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LBIGAUX_LENGTH_2] THEN ASM_REWRITE_TAC[LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `?w1 w2. ws = [w1:A word_loc; w2]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LBIGAUX_LENGTH_2] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `LENGTH (ws:(A word_loc)list)`)) THEN
    ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM; MAP]) THEN
  FIRST_ASSUM(MP_TAC o check ((=) `wl_get_vars [adjust_var a1; adjust_var a2] (t:(A,C,FFI)wl_state) = SOME [w1; w2]` o concl)) THEN
  ASP2AUX_GET_VARS_TAC THEN
  SUBGOAL_THEN `wl_get_vars (MAP adjust_var [a1; a2]) (t:(A,C,FFI)wl_state) = SOME [w1; w2]`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[MAP]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2
      (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
  CAKE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  DRULE_ALL memory_rel_get_vars_IMP THEN
  REWRITE_TAC[ZIP; APPEND; MAP] THEN DISCH_TAC THEN
  ASP2AUX_DRULE_N 4 memory_rel_str_cmp THEN
  DISCH_THEN(MP_TAC o SPECL [`b:bool`; `cmp:opb`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `wa1:A word` (X_CHOOSE_THEN `ra1:A word`
    (X_CHOOSE_THEN `wa2:A word` (X_CHOOSE_THEN `ra2:A word`
    (X_CHOOSE_THEN `r1:A word` (X_CHOOSE_THEN `r2:A word` STRIP_ASSUME_TAC)))))) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_memory_rel_IMP) THEN
  UNDISCH_TAC `word_str_cmp b ra1 ra2 (wl_state_mdomain (t:(A,C,FFI)wl_state))
                 (wl_state_memory t) (wl_state_be t) c = SOME (r1:A word,r2)` THEN
  REWRITE_TAC[word_str_cmp_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[isWord_exists]) THEN
  ASM_REWRITE_TAC[theWord_def] THEN
  ABBREV_TAC `sh_len = (dimindex (:A) - data_to_word_config_len_size c) -
                       backend_common_word_shift (:A)` THEN
  SUBGOAL_THEN `~(dimindex (:A) <= sh_len) /\ val (word sh_len:A word) = sh_len`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sh_len < dimindex (:A)` ASSUME_TAC THENL
     [EXPAND_TAC "sh_len" THEN
      UNDISCH_TAC `~(data_to_word_config_len_size c = 0)` THEN
      UNDISCH_TAC `data_to_word_config_len_size c + 7 < dimindex (:A)` THEN
      ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[NOT_LE] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `dimindex (:A)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL];
    ALL_TAC] THEN
  ASP2AUX_STUB_TAC `lookup StringCmpLoop_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                    SOME (6,StringCmpLoop_code)` THEN
  REWRITE_TAC[data_to_word_assign_def] THEN
  CAKE_REWRITE_TAC[data_to_word_arg2_def; assign_StringCmp_def;
                   data_to_word_get_names_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @
    [adjust_var_NEQ; adjust_var_11; wl_mem_load_def; word_sh_def; GE]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(num#A word_loc)list` (X_CHOOSE_THEN `perm:num->num->num`
    ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM] o
    MATCH_MP ASP2AUX_cut_state_opt_cut_env) THEN
  REWRITE_TAC[ASP2AUX_word_MIN] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `word_ushr (w:A word) sh_len = word_ushr w' sh_len` THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN ASP2AUX_STRCMP_CALL_TAC;
      REWRITE_TAC[option_INJ; PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @
        [adjust_var_NEQ; adjust_var_11]) THEN
      ASP2AUX_ASSIGNCMP_TAC asp2_eval_rws THEN
      ASP2AUX_CRW_TAC asp2_eval_rws THEN
      ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
      REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM;
                  ASP2AUX_do_stack_lim_safe; wl_state_INFO.ri_accfupds] THEN
      CAKE_REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[lookup_insert; adjust_var_NEQ; ARITH_EQ] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC ASP2AUX_nocall_IS_SOME THEN
        MAP_EVERY EXISTS_TAC [`kept_names:num_set`; `data_state_locals (s:(C,FFI)data_state)`;
                              `wl_state_locals (t:(A,C,FFI)wl_state)`] THEN
        ASM_REWRITE_TAC[] THEN
        GEN_TAC THEN DISCH_TAC THEN
        REPEAT(MATCH_MP_TAC ASP2AUX_IS_SOME_insert_mono) THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[option_le_max_right] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[ASP2AUX_inter_ins 7; ASP2AUX_inter_ins 5; ASP2AUX_inter_ins 3;
                    ASP2AUX_inter_ins 1; GSYM APPEND_ASSOC] THEN
        MATCH_MP_TAC memory_rel_insert THEN REWRITE_TAC[APPEND] THEN
        MATCH_MP_TAC ASP2AUX_memory_rel_Boolv_COND THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
          asp2_head_is "APPEND" (rand (concl th)))) THEN
        MATCH_MP_TAC memory_rel_rearrange THEN
        REWRITE_TAC[MEM_APPEND; MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISJ1_TAC THEN MATCH_MP_TAC ASP2AUX_join_env_cut_MEM_nocall THEN
        MAP_EVERY EXISTS_TAC [`kept_names:num_set`;
          `mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (kept_names:num_set))`] THEN
        ASM_REWRITE_TAC[]]];
    ASM_CASES_TAC `word_ult (word_ushr (w':A word) sh_len) (word_ushr w sh_len)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASP2AUX_STRCMP_CALL_TAC]);;

let ASP2AUX_VAL_SUB_K = prove
 (`!k n:A word. good_dimindex (:A) /\ k < 2 EXP 32 /\ ~word_ult n (word k) ==>
     k <= val n /\ val (word_sub n (word k)) = val n - k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word k:A word) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC ASP2AUX_VAL_WORD_SMALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~word_ult (n:A word) (word k)` THEN
  ASM_REWRITE_TAC[WORD_ULT; NOT_LT] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES]);;

(* HOL4 line 4565 *)
let evaluate_XorLoop = prove
 (`!a1 a2 l dm m l1 l2 (t1:(A,C,FFI)wl_state) m1.
     word_xor_bytes a1 a2 l dm m = SOME m1 /\ wl_state_memory t1 = m /\
     wl_state_mdomain t1 = dm /\
     val l < wl_state_clock t1 /\ good_dimindex (:A) /\
     lookup XorLoop_location (wl_state_code t1) = SOME (4,XorLoop_code) /\
     wl_get_var 0 t1 = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 t1 = SOME (wl_Word a2) /\
     wl_get_var 4 t1 = SOME (wl_Word a1) /\
     wl_get_var 6 t1 = SOME (wl_Word l) ==>
     ?ck max_stack.
       wl_evaluate (XorLoop_code,t1) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word (word 2)]),
          wl_state_memory_fupd (combin_K m1) (wl_state_clock_fupd (combin_K ck)
            (wl_state_stack_max_fupd (combin_K max_stack)
               (wl_state_locals_fupd (combin_K LN) (wl_state_locals_size_fupd (combin_K (SOME 0)) t1))))) /\
       (~(max_stack = wl_state_stack_max t1) ==>
        max_stack = OPTION_MAP2 MAX (wl_state_stack_max t1)
                      (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1))
                         (lookup XorLoop_location (wl_state_stack_size t1))))`,
  MATCH_MP_TAC word_xor_bytes_ind THEN
  MAP_EVERY X_GEN_TAC [`a1:A word`; `a2:A word`; `len:A word`; `dm:A word->bool`;
                       `m:A word->A word_loc`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`l1:num`; `l2:num`; `t1:(A,C,FFI)wl_state`;
                       `m1:A word->A word_loc`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [word_xor_bytes_def] THEN
  REWRITE_TAC[read_word_def] THEN CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV XorLoop_code_def)) THEN
  ASM_CASES_TAC `word_ult (len:A word) (word 2)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `len:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
      MAP_EVERY EXISTS_TAC [`wl_state_clock (t1:(A,C,FFI)wl_state)`;
                            `wl_state_stack_max (t1:(A,C,FFI)wl_state)`] THEN
      REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[isWord_exists]) THEN
      REPEAT(FIRST_X_ASSUM(CAKE_STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
      ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ [wl_mem_store_def; WORD_XOR_0;
        theWord_def; wl_mem_load_def]) THEN
      MAP_EVERY EXISTS_TAC [`wl_state_clock (t1:(A,C,FFI)wl_state)`;
                            `wl_state_stack_max (t1:(A,C,FFI)wl_state)`] THEN
      REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]];
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[isWord_exists]) THEN
    ASM_REWRITE_TAC[theWord_def] THEN DISCH_TAC THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`T`; `T`; `T`; `T`; `w'':A word`; `w''':A word`;
                                      `w:A word`; `w':A word`]) THEN
    ASM_REWRITE_TAC[read_word_def; theWord_def; isWord_def] THEN
    MP_TAC(SPECL [`2`; `len:A word`] ASP2AUX_VAL_SUB_K) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; STRIP_TAC] THEN
    SUBGOAL_THEN `~(wl_state_clock (t1:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [wl_mem_store_def; WORD_XOR_0; wl_mem_load_def]) THEN
    ASP2AUX_SPEC_EVAL_TAC `XorLoop_code:(A)wl_prog`
      (fun st -> [`l1:num`; `l2:num`; st; `m1:A word->A word_loc`]) THEN
    ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `ms:num option`
      STRIP_ASSUME_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM;
                                OPTION_MAP2_MAX_CANCEL]) THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ [wl_bad_fun_return_def; PAIR_EQ]) THEN
    MAP_EVERY EXISTS_TAC [`ck':num`; `ms:num option`] THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_MESON_TAC[]]);;

let ASP2AUX_do_app_XorByte = prove
 (`!vals (x:(C,FFI)data_state) v s2.
     data_do_app (MemOp XorByte) vals x = Rval (v,s2) <=>
     ?b1 dst b2 src f1 ws f ds ds1.
       vals = [data_RefPtr b1 dst; data_RefPtr b2 src] /\
       lookup src (data_state_refs x) = SOME (bvl_ByteArray f1 ws) /\
       lookup dst (data_state_refs x) = SOME (bvl_ByteArray f ds) /\
       xor_bytes ws ds = SOME ds1 /\ v = data_Unit /\
       s2 = data_state_refs_fupd
              (combin_K (insert dst (bvl_ByteArray f ds1) (data_state_refs x)))
              (do_stack (MemOp XorByte) vals (do_lim_safe x (MemOp XorByte) vals))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; MEM] THEN
  CAKE_REWRITE_TAC[op_space_reset_def; op_space_req_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [data_do_app_aux_def] THEN
  CAKE_REWRITE_TAC[ASP2AUX_do_stack_lim_safe] THEN
  EQ_TAC THENL
   [REWRITE_TAC(all_case_eqs()) THEN CAKE_REWRITE_TAC[] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[CONS_11; injectivity "data_v"] THEN
    SIMP[];
    STRIP_TAC THEN RVEQ_TAC THEN ASP2AUX_CRW_TAC[ASP2AUX_do_stack_lim_safe]]);;

(* HOL4 line 4632 *)
let assign_XorByte = prove
 (assign_thm_stmt `op = MemOp XorByte`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?kept_names. names_opt = SOME (kept_names:num_set)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(op_requires_names (MemOp XorByte) <=> names_opt = (NONE:num_set option))` THEN
    REWRITE_TAC[op_requires_names_def] THEN MESON_TAC[option_nchotomy];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`; `vals:data_v list`;
    `kept_names:num_set`; `x:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (MemOp XorByte) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP2AUX_do_app_XorByte; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`dst_b:bool`; `dst:num`; `src_b:bool`; `src:num`; `fl1:bool`;
    `bs1:byte list`; `fl2:bool`; `bs2:byte list`; `bs3:byte list`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  SUBGOAL_THEN `?a1 a2. args = [a1:num; a2]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LBIGAUX_LENGTH_2] THEN ASM_REWRITE_TAC[LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `?w1 w2. ws = [w1:A word_loc; w2]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LBIGAUX_LENGTH_2] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `LENGTH (ws:(A word_loc)list)`)) THEN
    ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM; MAP]) THEN
  FIRST_ASSUM(MP_TAC o check ((=) `wl_get_vars [adjust_var a1; adjust_var a2] (t:(A,C,FFI)wl_state) = SOME [w1; w2]` o concl)) THEN
  REWRITE_TAC[wl_get_vars_def; wl_get_var_def] THEN
  REWRITE_TAC(all_case_eqs()) THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; option_INJ]) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; option_INJ]) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `wl_get_vars (MAP adjust_var [a1; a2]) (t:(A,C,FFI)wl_state) = SOME [w1; w2]`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[MAP]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check ((=) `data_to_word_gcProof_state_rel c l1 l2
      (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
  CAKE_REWRITE_TAC[APPEND] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  DRULE_ALL memory_rel_get_vars_IMP THEN
  REWRITE_TAC[ZIP; APPEND; MAP] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_swap) THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_xor_bytes THEN
  DISCH_THEN(X_CHOOSE_THEN `wsrc:A word` (X_CHOOSE_THEN `asrc:A word`
    (X_CHOOSE_THEN `wdst:A word` (X_CHOOSE_THEN `adst:A word`
    (X_CHOOSE_THEN `hdr:A word` (X_CHOOSE_THEN `m1:A word->A word_loc`
    STRIP_ASSUME_TAC)))))) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_memory_rel_IMP) THEN
  ASP2AUX_STUB_TAC `lookup XorLoop_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                    SOME (4,XorLoop_code)` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex (:A) - data_to_word_config_len_size c < dimindex (:A)`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(num#A word_loc)list` (X_CHOOSE_THEN `perm:num->num->num`
    ASSUME_TAC)) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN
  CAKE_REWRITE_TAC[data_to_word_arg2_def; assign_XorByte_def;
                   data_to_word_get_names_def] THEN
  ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
    [ASP2AUX_cut_envs_ins 1; ASP2AUX_cut_envs_ins 3; ASP2AUX_cut_envs_ins 5;
     domain_adjust_sets; ALL_DISTINCT; MEM; wl_mem_load_def; adjust_var_NEQ;
     adjust_var_11;
     MustTerminate_limit_NOT_0; GSYM decode_length_def;
     wl_push_env_def; LET_DEF; LET_END_DEF;
     REWRITE_RULE[ASSUME `dimindex (:A) - data_to_word_config_len_size c < dimindex (:A)`]
       (ISPEC `dimindex (:A) - data_to_word_config_len_size c` word_exp_SmallLsr)]) THEN
  ASP2AUX_EVAL_LEMMA_TAC `XorLoop_code:(A)wl_prog` (fun st ->
    ISPECL [`word_add asrc bytes_in_word:A word`; `word_add adst bytes_in_word:A word`;
            `decode_length c (hdr:A word)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
            `wl_state_memory (t:(A,C,FFI)wl_state)`; `n:num`; `l:num`; st;
            `m1:A word->A word_loc`] evaluate_XorLoop) THEN
  ANTS_TAC THENL
   [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [push_env_store; wl_push_env_clock; ASP2AUX_val_lt_MustTerminate_limit]) THEN
    CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `ms:num option`
      STRIP_ASSUME_TAC))] THEN
  ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [push_env_store; wl_push_env_clock; wl_push_env_def; wl_pop_env_def;
       wl_set_vars_def; alist_insert_def; LET_DEF; LET_END_DEF; LENGTH;
       wl_bad_fun_return_def]) THEN
  SUBGOAL_THEN `domain (sptree_union (fromAList (q:(num#A word_loc)list))
                  (fromAList (toAList (y1:(A word_loc)spt)))) =
                domain y1 UNION domain (y2:(A word_loc)spt)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[domain_union; domain_fromAList_toAList] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP env_to_list_domain) THEN SET_TAC[];
    ALL_TAC] THEN
  ASP2AUX_CRW_TAC [option_DISTINCT; injectivity "wl_result"] THEN
  ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM;
              ASP2AUX_do_stack_lim_safe; wl_state_INFO.ri_accfupds] THEN
  CAKE_REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM] o
    MATCH_MP ASP2AUX_cut_state_opt_cut_env) THEN
  REPEAT CONJ_TAC THENL
   [ASP2AUX_DRULE_N 3 ASP2AUX_cut_ret_lookup_0 THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ASP2AUX_DRULE_N 3 ASP2AUX_cut_ret_IS_SOME THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ALL_TAC;
    ALL_TAC;
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Unit o
      (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
      check (fun th -> asp2_head_is "memory_rel" (concl th) &&
             can (find_term ((=) `m1:A word->A word_loc`)) (concl th))) THEN
    DISCH_TAC THEN
    ASP2AUX_DRULE_N 4 ASP2AUX_memory_rel_cut_ret THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]] THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM; OPTION_MAP2_MAX_CANCEL] o
    REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM;
      ASSUME `wl_state_stack_size (t:(A,C,FFI)wl_state) =
              data_state_stack_frame_sizes (s:(C,FFI)data_state)`] o
    check (fun th -> is_imp (concl th) && is_neg (lhand (concl th)))) THEN
  ASP2AUX_EQ_FROM_NEG_IMP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_rel_IMP_size_of_stack) THEN
  ASM_REWRITE_TAC[stack_size_eq; stack_consumed_def] THEN
  UNDISCH_TAC `option_le (wl_state_stack_max (t:(A,C,FFI)wl_state))
                 (data_state_stack_max (s:(C,FFI)data_state))` THEN
  ASP2AUX_OPTION_ARITH_TAC);;

let ASP2AUX_get_real_offset_0 = prove
 (`get_real_offset (Smallnum (&0):A word) = SOME bytes_in_word`,
  REWRITE_TAC[get_real_offset_def; data_to_word_Smallnum_def] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; WORD_SHL_0; WORD_ADD_0; COND_ID]);;

let ASP2AUX_memory_rel_write1 = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars f n w.
     memory_rel c be ts refs sp st m dm vars /\
     FLOOKUP st NextFree = SOME (wl_Word f) /\ n < sp ==>
     word_add f (word_mul bytes_in_word (word n)) IN dm /\
     memory_rel c be ts refs sp st
       ((word_add f (word_mul bytes_in_word (word n)) =+ w) m) dm vars`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A word_loc` o MATCH_MP memory_rel_write) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':A word` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `n:num`))) THEN
  SUBGOAL_THEN `f':A word = f` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP (st:(store_name,A word_loc)fmap) NextFree = SOME (wl_Word f')` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF]);;

let ASP2AUX_memory_rel_write3 = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars f k nf w1 w2 w3.
     memory_rel c be ts refs sp st m dm vars /\
     FLOOKUP st NextFree = SOME (wl_Word f) /\
     nf = word_add f (word_mul bytes_in_word (word k)) /\ k + 3 <= sp ==>
     nf IN dm /\ word_add nf bytes_in_word IN dm /\
     word_add nf (word_mul (word 2) bytes_in_word) IN dm /\
     memory_rel c be ts refs sp st
       ((word_add nf (word_mul (word 2) bytes_in_word) =+ w3)
          ((word_add nf bytes_in_word =+ w2) ((nf =+ w1) m))) dm vars`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_add nf bytes_in_word =
                  word_add f (word_mul bytes_in_word (word (k + 1))):A word /\
                word_add nf (word_mul (word 2) bytes_in_word) =
                  word_add f (word_mul bytes_in_word (word (k + 2)))`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`;
    `refs:(data_v bvl_ref)spt`; `sp:num`; `st:(store_name,A word_loc)fmap`]
    ASP2AUX_memory_rel_write1) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m:A word->A word_loc`; `dm:A word->bool`;
    `vars:(data_v#A word_loc)list`; `f:A word`; `k:num`; `w1:A word_loc`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(word_add f (word_mul bytes_in_word (word k)) =+ w1)
    (m:A word->A word_loc)`; `dm:A word->bool`;
    `vars:(data_v#A word_loc)list`; `f:A word`; `k + 1`; `w2:A word_loc`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(word_add f (word_mul bytes_in_word (word (k + 1))) =+ w2)
    ((word_add f (word_mul bytes_in_word (word k)) =+ w1) (m:A word->A word_loc))`;
    `dm:A word->bool`; `vars:(data_v#A word_loc)list`; `f:A word`; `k + 2`;
    `w3:A word_loc`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[]);;

let ASP2AUX_addr_23 = prove
 (`!a b:A word. word_add (word_add a b) b = word_add a (word_mul (word 2) b) /\
                word_add (word_add (word_add a b) b) b = word_add a (word_mul (word 3) b)`,
  CONV_TAC WORD_RULE);;

let ASP2AUX_word_list_exists_open3 = prove
 (`!(nf:A word) n (frame:((A word#A word_loc)->bool)->bool) s.
     (word_list_exists nf (3 * SUC n) STAR frame) s ==>
     ?x1 x2 x3.
       (set_sep_one (nf,x1) STAR (set_sep_one (word_add nf bytes_in_word,x2) STAR
        (set_sep_one (word_add nf (word_mul (word 2) bytes_in_word),x3) STAR
         (word_list_exists (word_add nf (word_mul (word 3) bytes_in_word)) (3 * n) STAR
          frame)))) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `3 * SUC n = SUC (SUC (SUC (3 * n)))`;
              data_to_word_memoryProof_word_list_exists_thm] THEN
  REWRITE_TAC[SEP_CLAUSES; SEP_EXISTS_THM; GSYM STAR_ASSOC; ASP2AUX_addr_23]);;

let ASP2AUX_sep_write3 = prove
 (`!a1 a2 a3 (x1:A word_loc) x2 x3 y1 y2 y3 (p:((A word#A word_loc)->bool)->bool)
    (m:A word->A word_loc) dm.
     (set_sep_one (a1,x1) STAR (set_sep_one (a2,x2) STAR (set_sep_one (a3,x3) STAR p)))
       (fun2set (m,dm)) ==>
     (set_sep_one (a1,y1) STAR (set_sep_one (a2,y2) STAR (set_sep_one (a3,y3) STAR p)))
       (fun2set ((a3 =+ y3) ((a2 =+ y2) ((a1 =+ y1) m)),dm))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let th0 = th in
    let th1 = MP4AUX_SEP_WRITES
      `(a3 =+ (y3:A word_loc)) ((a2 =+ y2) ((a1 =+ y1) (m:A word->A word_loc)))` th0 in
    ACCEPT_TAC (MP4AUX_STAR_AC_RULE
      `set_sep_one ((a1:A word),(y1:A word_loc)) STAR (set_sep_one (a2,y2) STAR
         (set_sep_one (a3,y3) STAR (p:((A word#A word_loc)->bool)->bool)))` th1)));;

(* eliminate the variable v with an assumption  v = t  or  t = v *)
let ASP2AUX_ELIM_TAC (v:term) : tactic =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq (concl th) in
    if aconv r v && not (aconv l v) then SUBST_ALL_TAC (SYM th)
    else if aconv l v && not (aconv r v) then SUBST_ALL_TAC th
    else failwith "ASP2AUX_ELIM_TAC");;

(* the two fields of a cons cell: their addresses and values *)
let ASP2AUX_Block_MEM_01 = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm ts' tag h ys ww vars a.
     memory_rel c be ts refs sp st m dm (CONS (data_Block ts' tag [h; ys],wl_Word ww) vars) /\
     good_dimindex (:A) /\ get_real_addr c st ww = SOME a ==>
     word_add a bytes_in_word IN dm /\
     word_add a (word_mul (word 2) bytes_in_word) IN dm /\
     memory_rel c be ts refs sp st m dm
       (CONS (ys,m (word_add a (word_mul (word 2) bytes_in_word)))
         (CONS (h,m (word_add a bytes_in_word)) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `ts':num`; `tag:num`; `[h; ys]:data_v list`; `wl_Word ww:A word_loc`;
    `vars:(data_v#A word_loc)list`; `0`] memory_rel_Block_MEM) THEN
  ASM_REWRITE_TAC[LENGTH; ARITH; ASP2AUX_get_real_offset_0; option_INJ;
                  injectivity "word_loc"] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:A word` (X_CHOOSE_THEN `a0:A word`
    (X_CHOOSE_THEN `y0:A word` STRIP_ASSUME_TAC))) THEN
  ASP2AUX_ELIM_TAC `y0:A word` THEN ASP2AUX_ELIM_TAC `w0:A word` THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `get_real_addr c st (ww:A word) = SOME (a0:A word)` o concl)) THEN
  ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_swap o check (fun th ->
    asp2_head_is "memory_rel" (concl th) && can (find_term ((=) `h:data_v`)) (concl th))) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `ts':num`; `tag:num`; `[h; ys]:data_v list`; `wl_Word ww:A word_loc`;
    `CONS (h:data_v,(m:A word->A word_loc) (word_add a bytes_in_word))
       (vars:(data_v#A word_loc)list)`; `1`]
    memory_rel_Block_MEM) THEN
  ASM_REWRITE_TAC[LENGTH; ARITH; MP ASP2AUX_get_real_offset_1 (ASSUME `good_dimindex (:A)`);
                  option_INJ; injectivity "word_loc"] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `a1:A word`
    (X_CHOOSE_THEN `y1:A word` STRIP_ASSUME_TAC))) THEN
  ASP2AUX_ELIM_TAC `y1:A word` THEN ASP2AUX_ELIM_TAC `w1:A word` THEN
  FIRST_X_ASSUM(MP_TAC o check ((=) `get_real_addr c st (ww:A word) = SOME (a1:A word)` o concl)) THEN
  ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
    can (find_term ((=) `ys:data_v`)) (concl th) &&
    can (find_term ((=) `(m:A word->A word_loc) (word_add a (word_mul (word 2) bytes_in_word))`)) (concl th))) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let ASP2AUX_append_not_lower = prove
 (`!sp k. good_dimindex (:A) /\ sp * (dimindex (:A) DIV 8) < dimword (:A) /\
          k + 3 <= sp ==>
     ~word_ult (word_mul bytes_in_word (word (sp - k)):A word)
               (word_mul (word 3) bytes_in_word)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes_in_word_def; WORD_ULT; GSYM WORD_MUL; VAL_WORD; GSYM dimword_def] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
    REWRITE_TAC[th]) o REWRITE_RULE[good_dimindex_def]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THENL
   [SUBGOAL_THEN `4 * (sp - k) < dimword (:A) /\ 12 < dimword (:A)` STRIP_ASSUME_TAC;
    SUBGOAL_THEN `8 * (sp - k) < dimword (:A) /\ 24 < dimword (:A)` STRIP_ASSUME_TAC] THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

let ASP2AUX_append_sub = prove
 (`!sp k. k + 3 <= sp ==>
     word_sub (word_mul bytes_in_word (word (sp - k))) (word_mul (word 3) bytes_in_word) =
     word_mul bytes_in_word (word (sp - (k + 3))):A word`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sp - k = (sp - (k + 3)) + 3` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let ASP2AUX_append_nf = prove
 (`!nf f k. nf = word_add f (word_mul bytes_in_word (word k)) ==>
     word_add nf (word_mul (word 3) bytes_in_word) =
     word_add f (word_mul bytes_in_word (word (k + 3))):A word`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let ASP2AUX_append_final_nf = prove
 (`!nf n. word_add (word_add nf (word_mul (word 3) bytes_in_word))
            (word_mul bytes_in_word (word (3 * n))) =
          word_add nf (word_mul bytes_in_word (word (3 * SUC n))):A word`,
  REWRITE_TAC[ARITH_RULE `3 * SUC n = 3 * n + 3`; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let ASP2AUX_append_ptr = prove
 (`!(ptr:A word) n. word_add ptr (word (3 * 2 EXP n)) = word_add ptr (word_shl (word 3) n)`,
  REWRITE_TAC[WORD_SHL_WORD; MULT_SYM]);;

let ASP2AUX_memory_rel_write3_mr = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars f k nf w1 w2 w3.
     memory_rel c be ts refs sp st m dm vars /\
     FLOOKUP st NextFree = SOME (wl_Word f) /\
     nf = word_add f (word_mul bytes_in_word (word k)) /\ k + 3 <= sp ==>
     memory_rel c be ts refs sp st
       ((word_add nf (word_mul (word 2) bytes_in_word) =+ w3)
          ((word_add nf bytes_in_word =+ w2) ((nf =+ w1) m))) dm vars`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ACCEPT_TAC(last(CONJUNCTS(SPEC_ALL(MATCH_MP ASP2AUX_memory_rel_write3 th))))));;

(* HOL4 line 4827 (local; HOL4 Abbrev (x = e) is the plain equation; the  *)
(* unused bound variable l is left out)                                     *)
let evaluate_AppendMainLoop_code = prove
 (`!xs ww (t:(A,C,FFI)wl_state) vars ptr hdr k frame r1 r2 next_free ts v c
    (s:(C,FFI)data_state) sp tmp0 tmp2 f.
     memory_rel c (wl_state_be t) ts (data_state_refs s) sp (wl_state_store t)
       (wl_state_memory t) (wl_state_mdomain t) (CONS (v,wl_Word ww) vars) /\
     ~(xs = []) /\
     data_v_to_list v = SOME xs /\
     lookup 10 (wl_state_locals t) = SOME (wl_Word ptr) /\
     lookup 8 (wl_state_locals t) = SOME (wl_Word (word_mul bytes_in_word (word (sp - k)))) /\
     lookup 6 (wl_state_locals t) = SOME (wl_Word hdr) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word ww) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word next_free) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc r1 r2) /\
     k + 3 * LENGTH xs <= sp /\ good_dimindex (:A) /\
     sp * (dimindex (:A) DIV 8) < dimword (:A) /\
     FLOOKUP (wl_state_store t) (Temp (word 0)) = SOME tmp0 /\
     FLOOKUP (wl_state_store t) (Temp (word 2)) = SOME tmp2 /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word f) /\
     (next_free = word_add f (word_mul bytes_in_word (word k))) /\
     lookup AppendMainLoop_location (wl_state_code t) = SOME (6,AppendMainLoop_code c) /\
     lookup AppendMainLoop_location (wl_state_stack_size t) = wl_state_locals_size t /\
     (word_list_exists next_free (3 * LENGTH xs) STAR frame)
       (fun2set (wl_state_memory t,wl_state_mdomain t)) /\
     LENGTH xs <= wl_state_clock t ==>
     ?m1 ws smx.
       wl_evaluate (AppendMainLoop_code c,t) =
         (SOME (wl_Result (wl_Loc r1 r2) [tmp2]),
          wl_state_locals_fupd (combin_K LN) (wl_state_locals_size_fupd (combin_K (SOME 0))
            (wl_state_store_fupd
               (combin_K (wl_state_store t |+ (NextFree,wl_Word (word_add next_free
                     (word_mul bytes_in_word (word (3 * LENGTH xs)))))))
               (wl_state_memory_fupd (combin_K m1) (wl_state_stack_max_fupd (combin_K smx)
                  (wl_state_clock_fupd (combin_K (wl_state_clock t - (LENGTH xs - 1))) t)))))) /\
       LENGTH ws = LENGTH xs /\
       option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                        (OPTION_MAP2 (+)
                           (OPTION_MAP2 MAX
                              (lookup AppendMainLoop_location (wl_state_stack_size t))
                              (lookup AppendLenLoop_location (wl_state_stack_size t)))
                           (wl_stack_size (wl_state_stack t)))) /\
       (misc_word_list next_free (append_writes c ptr hdr ws tmp0) STAR frame)
         (fun2set (m1,wl_state_mdomain t)) /\
       memory_rel c (wl_state_be t) ts (data_state_refs s) sp (wl_state_store t) m1
         (wl_state_mdomain t) (APPEND (ZIP xs ws) vars)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `h:data_v` THEN X_GEN_TAC `tl:data_v list` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`ww:A word`; `t:(A,C,FFI)wl_state`; `vars:(data_v#A word_loc)list`;
    `ptr:A word`; `hdr:A word`; `k:num`; `frame:((A word#A word_loc)->bool)->bool`;
    `r1:num`; `r2:num`; `next_free:A word`; `ts:num`; `v:data_v`; `c:data_to_word_config`;
    `s:(C,FFI)data_state`; `sp:num`; `tmp0:A word_loc`; `tmp2:A word_loc`; `f:A word`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check ((=) `next_free = word_add f (word_mul bytes_in_word (word k)):A word` o concl)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ts1:num` (X_CHOOSE_THEN `ys:data_v`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) o MATCH_MP v_to_list_SOME_CONS_IMP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_memory_rel_IMP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
    (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
    check (fun th -> asp2_head_is "memory_rel" (concl th))) THEN
  REWRITE_TAC[injectivity "word_loc"; NOT_CONS_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:A word` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC)))) THEN
  ASP2AUX_ELIM_TAC `w0:A word` THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts:num`;
    `data_state_refs (s:(C,FFI)data_state)`; `sp:num`;
    `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `ts1:num`; `cons_tag`; `h:data_v`;
    `ys:data_v`; `ww:A word`; `vars:(data_v#A word_loc)list`; `a:A word`]
    ASP2AUX_Block_MEM_01) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ts2:num` (X_CHOOSE_THEN `tag2:num` (X_CHOOSE_THEN `vs2:data_v list`
    SUBST_ALL_TAC)) o MATCH_MP ASP2AUX_v_to_list_Block) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
    (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
    check (fun th -> asp2_head_is "memory_rel" (concl th) &&
      can (find_term ((=) `vs2:data_v list`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP2AUX_word_list_exists_open3 o
    REWRITE_RULE[LENGTH] o check (fun th -> can (find_term (fun t -> try
      fst(dest_const(fst(strip_comb t))) = "word_list_exists" with Failure _ -> false))
      (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:A word_loc` (X_CHOOSE_THEN `x2:A word_loc`
    (X_CHOOSE_THEN `x3:A word_loc` ASSUME_TAC))) THEN
  MP4AUX_SEP_R_TAC THEN
  MP_TAC(ISPECL [`sp:num`; `k:num`] (INST_TYPE [`:A`,`:A`] ASP2AUX_append_not_lower)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k + 3 * LENGTH (CONS (h:data_v) tl) <= sp` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (CONS (h:data_v) tl) <= wl_state_clock (t:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (BINDER_CONV o BINDER_CONV o BINDER_CONV o LAND_CONV o LAND_CONV o
    RAND_CONV o LAND_CONV) [AppendMainLoop_code_def] THEN
  ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
    [wl_mem_load_def; wl_mem_store_def; data_to_word_gcProof_word_and_one_eq_0_iff]) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `h2:data_v` (X_CHOOSE_THEN `tl2:data_v list`
    SUBST_ALL_TAC)) (ISPEC `tl:data_v list` list_CASES) THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[v_to_list_EQ_SOME_NIL] o check ((=) `data_v_to_list (data_Block ts2 tag2 vs2) = SOME []` o concl)) THEN
    REWRITE_TAC[injectivity "data_v"] THEN
    DISCH_THEN(X_CHOOSE_THEN `ts3:num` STRIP_ASSUME_TAC) THEN
    ASP2AUX_ELIM_TAC `vs2:data_v list` THEN ASP2AUX_ELIM_TAC `tag2:num` THEN
    ASP2AUX_ELIM_TAC `ts2:num` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o check (is_cond o concl)) THEN
    ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [wl_mem_load_def; wl_mem_store_def; wl_set_store_def; wl_get_store_def]) THEN
    MAP_EVERY EXISTS_TAC
     [`(word_add next_free (word_mul (word 2) bytes_in_word) =+ (tmp0:A word_loc))
        ((word_add next_free bytes_in_word =+
          wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word))
         ((next_free =+ wl_Word hdr) (wl_state_memory t)))`;
      `[wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)]`;
      `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUB_0; WORD_MUL_SYM];
      REWRITE_TAC[LENGTH; ONE];
      REWRITE_TAC[option_le_max_right; option_le_refl];
      REWRITE_TAC[append_writes_def; misc_word_list_def; ASP2AUX_addr_23; SEP_CLAUSES] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`wl_Word hdr:A word_loc`;
        `wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)`;
        `tmp0:A word_loc`] o MATCH_MP ASP2AUX_sep_write3 o check (fun th ->
          can (find_term ((=) `x1:A word_loc`)) (concl th))) THEN
      REWRITE_TAC[LENGTH; MULT_CLAUSES; data_to_word_memoryProof_word_list_exists_thm;
                  SEP_CLAUSES] THEN
      DISCH_TAC THEN MP4AUX_SEP_AC_TAC;
      REWRITE_TAC[ZIP; APPEND] THEN MATCH_MP_TAC ASP2AUX_memory_rel_write3_mr THEN
      MAP_EVERY EXISTS_TAC [`f:A word`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th ->
          asp2_head_is "memory_rel" (concl th) &&
          can (find_term ((=) `data_Block ts3 0 []`)) (concl th))) THEN
        REWRITE_TAC[];
        UNDISCH_TAC `k + 3 * LENGTH [h:data_v] <= sp` THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC]];
    FIRST_ASSUM(X_CHOOSE_THEN `ts3:num` (X_CHOOSE_THEN `ys2:data_v`
      (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) o MATCH_MP v_to_list_SOME_CONS_IMP o
      check ((=) `data_v_to_list (data_Block ts2 tag2 vs2) = SOME (CONS h2 tl2)` o concl)) THEN
    REWRITE_TAC[injectivity "data_v"] THEN STRIP_TAC THEN
    ASP2AUX_ELIM_TAC `vs2:data_v list` THEN ASP2AUX_ELIM_TAC `tag2:num` THEN
    ASP2AUX_ELIM_TAC `ts2:num` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[NOT_CONS_NIL] o check (is_cond o concl)) THEN
    ASP2AUX_CRW_TAC [] THEN
    REMOVE_THEN "IH" (fun th -> ASP2AUX_EVAL_LEMMA_TAC `AppendMainLoop_code c:(A)wl_prog`
      (fun st -> ISPECL [`w2:A word`; st;
         `CONS (h:data_v,wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word))
            (vars:(data_v#A word_loc)list)`;
         `word_add (ptr:A word) (word (3 * 2 EXP shift_length c))`; `hdr:A word`; `k + 3`;
         `set_sep_one (next_free:A word,wl_Word hdr) STAR
          (set_sep_one (word_add next_free bytes_in_word,
             wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)) STAR
           (set_sep_one (word_add next_free (word_mul (word 2) bytes_in_word),
              wl_Word (word_add (ptr:A word) (word (3 * 2 EXP shift_length c)))) STAR
            (frame:((A word#A word_loc)->bool)->bool)))`;
         `r1:num`; `r2:num`; `word_add next_free (word_mul (word 3) bytes_in_word):A word`;
         `ts:num`; `data_Block ts3 cons_tag [h2; ys2]`; `c:data_to_word_config`;
         `s:(C,FFI)data_state`; `sp:num`; `tmp0:A word_loc`; `tmp2:A word_loc`; `f:A word`]
        th)) THEN
    ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
      SUBGOAL_THEN `k + 3 <= sp /\ (k + 3) + 3 * SUC (LENGTH (tl2:data_v list)) <= sp /\
                    SUC (LENGTH tl2) <= wl_state_clock (t:(A,C,FFI)wl_state) - 1`
        STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `k + 3 * LENGTH (CONS (h:data_v) (CONS h2 tl2)) <= sp` THEN
        UNDISCH_TAC `LENGTH (CONS (h:data_v) (CONS h2 tl2)) <=
                     wl_state_clock (t:(A,C,FFI)wl_state)` THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC ASP2AUX_memory_rel_write3_mr THEN
        MAP_EVERY EXISTS_TAC [`f:A word`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
          can (find_term ((=) `ys2:data_v`)) (concl th) &&
          can (find_term ((=) `h:data_v`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ASP2AUX_append_sub THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC ASP2AUX_append_nf THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(MP_TAC o SPECL [`wl_Word hdr:A word_loc`;
          `wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)`;
          `wl_Word (word_add (ptr:A word) (word (3 * 2 EXP shift_length c)))`] o
          MATCH_MP ASP2AUX_sep_write3 o check (fun th ->
            can (find_term ((=) `x1:A word_loc`)) (concl th))) THEN
        REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN MP4AUX_SEP_AC_TAC];
      DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` (X_CHOOSE_THEN `ws:(A word_loc)list`
        (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC)))] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [wl_bad_fun_return_def]) THEN
    MAP_EVERY EXISTS_TAC [`m1:A word->A word_loc`;
      `CONS (wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)) ws`;
      `smx:num option`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[PAIR_EQ; wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                  LENGTH; ASP2AUX_append_final_nf] THEN ARITH_TAC;
      ASM_REWRITE_TAC[LENGTH];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "option_le" (concl th) &&
        free_in `smx:num option` (concl th))) THEN
      ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN
      ASP2AUX_OPTION_ARITH_TAC;
      SUBGOAL_THEN `~(ws:(A word_loc)list = [])` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> try lhs(concl th) =
          `LENGTH (ws:(A word_loc)list)` with Failure _ -> false)) THEN
        ASM_CASES_TAC `ws:(A word_loc)list = []` THEN ASM_REWRITE_TAC[LENGTH] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[append_writes_def; misc_word_list_def; ASP2AUX_addr_23;
                      LET_DEF; LET_END_DEF] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ASP2AUX_append_ptr; wl_state_INFO.ri_accfupds;
        K_THM] o check (fun th ->
        can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "append_writes"
                                 with Failure _ -> false)) (concl th))) THEN
      DISCH_TAC THEN MP4AUX_SEP_AC_TAC;
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM] o
        check (fun th -> asp2_head_is "memory_rel" (concl th) &&
          free_in `m1:A word->A word_loc` (concl th))) THEN
      MATCH_MP_TAC memory_rel_rearrange THEN
      REWRITE_TAC[ZIP; APPEND; MEM; MEM_APPEND] THEN MESON_TAC[]]]);;

(* HOL4 line 5041 *)
let data_to_word_assignProof_STOP_def = cake_def
  `data_to_word_assignProof_STOP (x:A) = x`;;

let ASP2AUX_append_lower = prove
 (`!sp k. good_dimindex (:A) /\ sp * (dimindex (:A) DIV 8) < dimword (:A) /\
          k <= sp /\ sp - k < 3 ==>
     word_ult (word_mul bytes_in_word (word (sp - k)):A word)
              (word_mul (word 3) bytes_in_word)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bytes_in_word_def; WORD_ULT; GSYM WORD_MUL; VAL_WORD; GSYM dimword_def] THEN
  SUBGOAL_THEN `64 <= dimword (:A)` ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 6` THEN
    CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC TWOEXP_MONO2] THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
    REWRITE_TAC[th]) o REWRITE_RULE[good_dimindex_def]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THENL
   [SUBGOAL_THEN `4 * (sp - k) < dimword (:A) /\ 12 < dimword (:A)` STRIP_ASSUME_TAC;
    SUBGOAL_THEN `8 * (sp - k) < dimword (:A) /\ 24 < dimword (:A)` STRIP_ASSUME_TAC] THEN
  TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;

let ASP2AUX_word_list_exists_open3n = prove
 (`!(nf:A word) n (frame:((A word#A word_loc)->bool)->bool) s.
     (word_list_exists nf (SUC (SUC (SUC n))) STAR frame) s ==>
     ?x1 x2 x3.
       (set_sep_one (nf,x1) STAR (set_sep_one (word_add nf bytes_in_word,x2) STAR
        (set_sep_one (word_add nf (word_mul (word 2) bytes_in_word),x3) STAR
         (word_list_exists (word_add nf (word_mul (word 3) bytes_in_word)) n STAR
          frame)))) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_word_list_exists_thm] THEN
  REWRITE_TAC[SEP_CLAUSES; SEP_EXISTS_THM; GSYM STAR_ASSOC; ASP2AUX_addr_23]);;

(* a tail call result followed by more code: the code is not run *)
let ASP2AUX_bad_fun_seq = prove
 (CASE_TERM
  `!(e:((A)wl_result)option#(A,C,FFI)wl_state)
    (f:(A,C,FFI)wl_state->((A)wl_result)option#(A,C,FFI)wl_state).
     (match (match e with
               (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) with
        (res,s1) -> if res = NONE then f s1 else (res,s1)) =
     (match e with
        (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~wl_bad_fun_return (p1:((A)wl_result)option)` THEN
  ASM_REWRITE_TAC[wl_bad_fun_return_def]);;

let ASP2AUX_DIV3_SUC = prove
 (`!sp k. k + 3 <= sp ==> (sp - k) DIV 3 = SUC ((sp - (k + 3)) DIV 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sp - k = (sp - (k + 3)) + 3` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ARITH_TAC]);;

(* HOL4 line 5045 (local; the theorem of line 5278 rebinds the name; HOL4  *)
(* Abbrev (x = e) is the plain equation; the unused bound variable l is     *)
(* left out)                                                                *)
let evaluate_AppendMainLoop_code_alt = prove
 (CASE_TERM
  `!xs ww (t:(A,C,FFI)wl_state) vars ptr hdr k frame r1 r2 next_free ts v c
    (s:(C,FFI)data_state) sp tmp0 tmp2 f.
     memory_rel c (wl_state_be t) ts (data_state_refs s) sp (wl_state_store t)
       (wl_state_memory t) (wl_state_mdomain t) (CONS (v,wl_Word ww) vars) /\
     ~(xs = []) /\
     data_v_to_list v = SOME xs /\
     lookup 10 (wl_state_locals t) = SOME (wl_Word ptr) /\
     lookup 8 (wl_state_locals t) = SOME (wl_Word (word_mul bytes_in_word (word (sp - k)))) /\
     lookup 6 (wl_state_locals t) = SOME (wl_Word hdr) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word ww) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word next_free) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc r1 r2) /\
     sp < k + 3 * LENGTH xs /\ good_dimindex (:A) /\ k <= sp /\
     sp * (dimindex (:A) DIV 8) < dimword (:A) /\
     FLOOKUP (wl_state_store t) (Temp (word 0)) = SOME tmp0 /\
     FLOOKUP (wl_state_store t) (Temp (word 2)) = SOME tmp2 /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word f) /\
     (next_free = word_add f (word_mul bytes_in_word (word k))) /\
     lookup AppendMainLoop_location (wl_state_code t) = SOME (6,AppendMainLoop_code c) /\
     lookup AppendLenLoop_location (wl_state_code t) = SOME (3,AppendLenLoop_code c) /\
     (word_list_exists next_free (sp - k) STAR frame)
       (fun2set (wl_state_memory t,wl_state_mdomain t)) /\
     LENGTH xs <= wl_state_clock t ==>
     ?m1 ww2 smx.
       wl_evaluate (AppendMainLoop_code c,t) =
         (match data_to_word_assignProof_STOP wl_evaluate
                  (AppendLenLoop_code c,
                   wl_state_locals_fupd (combin_K (fromList2 [wl_Loc r1 r2; wl_Word ww2;
                                                       wl_Word (word 0)]))
                     (wl_state_locals_size_fupd
                        (combin_K (lookup AppendLenLoop_location (wl_state_stack_size t)))
                        (wl_state_memory_fupd (combin_K m1) (wl_state_stack_max_fupd (combin_K smx)
                           (wl_state_clock_fupd
                              (combin_K (wl_state_clock t - ((sp - k) DIV 3 + 1))) t))))) with
            (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) /\
       option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                    (lookup AppendLenLoop_location (wl_state_stack_size t))) smx /\
       option_le smx
         (OPTION_MAP2 MAX (wl_state_stack_max t)
            (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
               (OPTION_MAP2 MAX
                  (lookup AppendLenLoop_location (wl_state_stack_size t))
                  (lookup AppendMainLoop_location (wl_state_stack_size t))))) /\
       memory_rel c (wl_state_be t) ts (data_state_refs s) sp (wl_state_store t) m1
         (wl_state_mdomain t)
         (CONS (THE (block_drop ((sp - k) DIV 3) v),wl_Word ww2) vars)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `h:data_v` THEN X_GEN_TAC `tl:data_v list` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`ww:A word`; `t:(A,C,FFI)wl_state`; `vars:(data_v#A word_loc)list`;
    `ptr:A word`; `hdr:A word`; `k:num`; `frame:((A word#A word_loc)->bool)->bool`;
    `r1:num`; `r2:num`; `next_free:A word`; `ts:num`; `v:data_v`; `c:data_to_word_config`;
    `s:(C,FFI)data_state`; `sp:num`; `tmp0:A word_loc`; `tmp2:A word_loc`; `f:A word`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check ((=) `next_free = word_add f (word_mul bytes_in_word (word k)):A word` o concl)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ts1:num` (X_CHOOSE_THEN `ys:data_v`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) o MATCH_MP v_to_list_SOME_CONS_IMP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_memory_rel_IMP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
    (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
    check (fun th -> asp2_head_is "memory_rel" (concl th))) THEN
  REWRITE_TAC[injectivity "word_loc"; NOT_CONS_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:A word` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC)))) THEN
  ASP2AUX_ELIM_TAC `w0:A word` THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`; `ts:num`;
    `data_state_refs (s:(C,FFI)data_state)`; `sp:num`;
    `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `ts1:num`; `cons_tag`; `h:data_v`;
    `ys:data_v`; `ww:A word`; `vars:(data_v#A word_loc)list`; `a:A word`]
    ASP2AUX_Block_MEM_01) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ts2:num` (X_CHOOSE_THEN `tag2:num` (X_CHOOSE_THEN `vs2:data_v list`
    SUBST_ALL_TAC)) o MATCH_MP ASP2AUX_v_to_list_Block) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
    (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
    check (fun th -> asp2_head_is "memory_rel" (concl th) &&
      can (find_term ((=) `vs2:data_v list`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (CONS (h:data_v) tl) <= wl_state_clock (t:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (BINDER_CONV o BINDER_CONV o BINDER_CONV o LAND_CONV o LAND_CONV o
    RAND_CONV o LAND_CONV) [AppendMainLoop_code_def] THEN
  ASM_CASES_TAC `k + 3 <= sp` THENL
   [MP_TAC(ISPECL [`sp:num`; `k:num`] (INST_TYPE [`:A`,`:A`] ASP2AUX_append_not_lower)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP2AUX_word_list_exists_open3n o
      REWRITE_RULE[MATCH_MP (ARITH_RULE `k + 3 <= sp ==> sp - k = SUC (SUC (SUC (sp - (k + 3))))`)
        (ASSUME `k + 3 <= sp`)] o
      check (fun th -> can (find_term (fun t -> try
        fst(dest_const(fst(strip_comb t))) = "word_list_exists" with Failure _ -> false))
        (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:A word_loc` (X_CHOOSE_THEN `x2:A word_loc`
      (X_CHOOSE_THEN `x3:A word_loc` ASSUME_TAC))) THEN
    MP4AUX_SEP_R_TAC THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `h2:data_v` (X_CHOOSE_THEN `tl2:data_v list`
      SUBST_ALL_TAC)) (ISPEC `tl:data_v list` list_CASES) THENL
     [UNDISCH_TAC `sp < k + 3 * LENGTH [h:data_v]` THEN
      UNDISCH_TAC `k + 3 <= sp` THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `ts3:num` (X_CHOOSE_THEN `ys2:data_v`
      (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) o MATCH_MP v_to_list_SOME_CONS_IMP o
      check ((=) `data_v_to_list (data_Block ts2 tag2 vs2) = SOME (CONS h2 tl2)` o concl)) THEN
    REWRITE_TAC[injectivity "data_v"] THEN STRIP_TAC THEN
    ASP2AUX_ELIM_TAC `vs2:data_v list` THEN ASP2AUX_ELIM_TAC `tag2:num` THEN
    ASP2AUX_ELIM_TAC `ts2:num` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[NOT_CONS_NIL] o check (is_cond o concl)) THEN
    ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [wl_mem_load_def; wl_mem_store_def; data_to_word_gcProof_word_and_one_eq_0_iff;
       ASP2AUX_bad_fun_seq]) THEN
    REMOVE_THEN "IH" (fun th -> ASP2AUX_EVAL_LEMMA_TAC `AppendMainLoop_code c:(A)wl_prog`
      (fun st -> ISPECL [`w2:A word`; st;
         `CONS (h:data_v,wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word))
            (vars:(data_v#A word_loc)list)`;
         `word_add (ptr:A word) (word (3 * 2 EXP shift_length c))`; `hdr:A word`; `k + 3`;
         `set_sep_one (next_free:A word,wl_Word hdr) STAR
          (set_sep_one (word_add next_free bytes_in_word,
             wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)) STAR
           (set_sep_one (word_add next_free (word_mul (word 2) bytes_in_word),
              wl_Word (word_add (ptr:A word) (word (3 * 2 EXP shift_length c)))) STAR
            (frame:((A word#A word_loc)->bool)->bool)))`;
         `r1:num`; `r2:num`; `word_add next_free (word_mul (word 3) bytes_in_word):A word`;
         `ts:num`; `data_Block ts3 cons_tag [h2; ys2]`; `c:data_to_word_config`;
         `s:(C,FFI)data_state`; `sp:num`; `tmp0:A word_loc`; `tmp2:A word_loc`; `f:A word`]
        th)) THEN
    ANTS_TAC THENL
     [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws) THEN
      CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
      ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
      SUBGOAL_THEN `sp < (k + 3) + 3 * SUC (LENGTH (tl2:data_v list)) /\
                    SUC (LENGTH tl2) <= wl_state_clock (t:(A,C,FFI)wl_state) - 1`
        STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `sp < k + 3 * LENGTH (CONS (h:data_v) (CONS h2 tl2))` THEN
        UNDISCH_TAC `LENGTH (CONS (h:data_v) (CONS h2 tl2)) <=
                     wl_state_clock (t:(A,C,FFI)wl_state)` THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC ASP2AUX_memory_rel_write3_mr THEN
        MAP_EVERY EXISTS_TAC [`f:A word`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
          can (find_term ((=) `ys2:data_v`)) (concl th) &&
          can (find_term ((=) `h:data_v`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ASP2AUX_append_sub THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC ASP2AUX_append_nf THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(MP_TAC o SPECL [`wl_Word hdr:A word_loc`;
          `wl_state_memory (t:(A,C,FFI)wl_state) (word_add a bytes_in_word)`;
          `wl_Word (word_add (ptr:A word) (word (3 * 2 EXP shift_length c)))`] o
          MATCH_MP ASP2AUX_sep_write3 o check (fun th ->
            can (find_term ((=) `x1:A word_loc`)) (concl th))) THEN
        DISCH_TAC THEN MP4AUX_SEP_AC_TAC];
      DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` (X_CHOOSE_THEN `ww2:A word`
        (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC)))] THEN
    ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [ASP1AUX_bad_fun_filter]) THEN
    MAP_EVERY EXISTS_TAC [`m1:A word->A word_loc`; `ww2:A word`; `smx:num option`] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP2AUX_DIV3_SUC) THEN
    REPEAT CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "option_le" (concl th) &&
        free_in `smx:num option` (concl th)))) THEN
      ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN ASP2AUX_OPTION_ARITH_TAC;
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "option_le" (concl th) &&
        free_in `smx:num option` (concl th)))) THEN
      ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2) THEN ASP2AUX_OPTION_ARITH_TAC;
      ASM_REWRITE_TAC[block_drop_def] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM] o
        check (fun th -> asp2_head_is "memory_rel" (concl th) &&
          free_in `m1:A word->A word_loc` (concl th))) THEN
      MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM] THEN MESON_TAC[]];
    MP_TAC(ISPECL [`sp:num`; `k:num`] (INST_TYPE [`:A`,`:A`] ASP2AUX_append_lower)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(k + 3 <= sp)` THEN ARITH_TAC; DISCH_TAC] THEN
    ASP2AUX_EVAL_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [wl_mem_load_def; ASP2AUX_bad_fun_seq]) THEN
    SUBGOAL_THEN `(sp - k) DIV 3 = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN UNDISCH_TAC `~(k + 3 <= sp)` THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`wl_state_memory (t:(A,C,FFI)wl_state)`; `ww:A word`;
      `OPTION_MAP2 MAX (wl_state_stack_max (t:(A,C,FFI)wl_state))
         (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
            (lookup AppendLenLoop_location (wl_state_stack_size t)))`] THEN
    REWRITE_TAC[block_drop_def; THE_DEF; ADD_CLAUSES] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[data_to_word_assignProof_STOP_def] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM];
      REWRITE_TAC[option_le_max_right; option_le_refl];
      ASP2AUX_OPTION_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 5278 (val evaluate_AppendMainLoop_code_alt: the theorem above   *)
(* with k = 0, SIMP_RULE std_ss [] |> GEN_ALL; rebinds the name)            *)
let evaluate_AppendMainLoop_code_alt = prove
 (CASE_TERM
  `!xs ww (t:(A,C,FFI)wl_state) vars ptr hdr frame r1 r2 next_free ts v c
    (s:(C,FFI)data_state) sp tmp0 tmp2 f.
     memory_rel c (wl_state_be t) ts (data_state_refs s) sp (wl_state_store t)
       (wl_state_memory t) (wl_state_mdomain t) (CONS (v,wl_Word ww) vars) /\
     ~(xs = []) /\
     data_v_to_list v = SOME xs /\
     lookup 10 (wl_state_locals t) = SOME (wl_Word ptr) /\
     lookup 8 (wl_state_locals t) = SOME (wl_Word (word_mul bytes_in_word (word sp))) /\
     lookup 6 (wl_state_locals t) = SOME (wl_Word hdr) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word ww) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word next_free) /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc r1 r2) /\
     sp < 3 * LENGTH xs /\ good_dimindex (:A) /\
     sp * (dimindex (:A) DIV 8) < dimword (:A) /\
     FLOOKUP (wl_state_store t) (Temp (word 0)) = SOME tmp0 /\
     FLOOKUP (wl_state_store t) (Temp (word 2)) = SOME tmp2 /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word f) /\
     (next_free = f) /\
     lookup AppendMainLoop_location (wl_state_code t) = SOME (6,AppendMainLoop_code c) /\
     lookup AppendLenLoop_location (wl_state_code t) = SOME (3,AppendLenLoop_code c) /\
     (word_list_exists next_free sp STAR frame)
       (fun2set (wl_state_memory t,wl_state_mdomain t)) /\
     LENGTH xs <= wl_state_clock t ==>
     ?m1 ww2 smx.
       wl_evaluate (AppendMainLoop_code c,t) =
         (match data_to_word_assignProof_STOP wl_evaluate
                  (AppendLenLoop_code c,
                   wl_state_locals_fupd (combin_K (fromList2 [wl_Loc r1 r2; wl_Word ww2;
                                                       wl_Word (word 0)]))
                     (wl_state_locals_size_fupd
                        (combin_K (lookup AppendLenLoop_location (wl_state_stack_size t)))
                        (wl_state_memory_fupd (combin_K m1) (wl_state_stack_max_fupd (combin_K smx)
                           (wl_state_clock_fupd
                              (combin_K (wl_state_clock t - (sp DIV 3 + 1))) t))))) with
            (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) /\
       option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                    (lookup AppendLenLoop_location (wl_state_stack_size t))) smx /\
       option_le smx
         (OPTION_MAP2 MAX (wl_state_stack_max t)
            (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
               (OPTION_MAP2 MAX
                  (lookup AppendLenLoop_location (wl_state_stack_size t))
                  (lookup AppendMainLoop_location (wl_state_stack_size t))))) /\
       memory_rel c (wl_state_be t) ts (data_state_refs s) sp (wl_state_store t) m1
         (wl_state_mdomain t)
         (CONS (THE (block_drop (sp DIV 3) v),wl_Word ww2) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASP2AUX_ELIM_TAC `next_free:A word` THEN
  MP_TAC(SPECL [`xs:data_v list`; `ww:A word`; `t:(A,C,FFI)wl_state`;
    `vars:(data_v#A word_loc)list`; `ptr:A word`; `hdr:A word`; `0`;
    `frame:((A word#A word_loc)->bool)->bool`; `r1:num`; `r2:num`; `f:A word`;
    `ts:num`; `v:data_v`; `c:data_to_word_config`; `s:(C,FFI)data_state`; `sp:num`;
    `tmp0:A word_loc`; `tmp2:A word_loc`; `f:A word`] evaluate_AppendMainLoop_code_alt) THEN
  ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; LE_0; WORD_MUL_0; WORD_ADD_0]);;

(* HOL4 line 5283 (local; the theorem of line 5370 rebinds the name) *)
let evaluate_AppendLenLoop_code = prove
 (CASE_TERM
  `!k (t:(A,C,FFI)wl_state) c xs l1 l2 (w:A word) vars ts v refs sp.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (v,wl_Word w) vars) /\
     data_v_to_list v = SOME xs /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word w) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word (word (12 * k))) /\
     lookup AppendLenLoop_location (wl_state_code t) = SOME (3,AppendLenLoop_code c) /\
     wl_state_locals_size t = lookup AppendLenLoop_location (wl_state_stack_size t) /\
     good_dimindex (:A) /\
     LENGTH xs <= wl_state_clock t ==>
     ?locals smx.
       (match wl_evaluate (AppendLenLoop_code c,t) with
          (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) =
       (match wl_evaluate (AppendLenLoop_code c,
                wl_state_locals_fupd (combin_K locals)
                  (wl_state_clock_fupd (combin_K (wl_state_clock t - LENGTH xs))
                     (wl_state_stack_max_fupd (combin_K smx) t))) with
          (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) /\
       lookup 0 locals = SOME (wl_Loc l1 l2) /\
       lookup 2 locals = SOME (wl_Word (word 2)) /\
       lookup 4 locals = SOME (wl_Word (word (12 * (k + LENGTH xs)))) /\
       option_le (wl_state_stack_max t) smx /\
       option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                       (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                          (lookup AppendLenLoop_location (wl_state_stack_size t))))`,
  SUBGOAL_THEN (CASE_TERM
   `!xs k (t:(A,C,FFI)wl_state) c l1 l2 (w:A word) vars ts v refs sp.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (v,wl_Word w) vars) /\
     data_v_to_list v = SOME xs /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word w) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word (word (12 * k))) /\
     lookup AppendLenLoop_location (wl_state_code t) = SOME (3,AppendLenLoop_code c) /\
     wl_state_locals_size t = lookup AppendLenLoop_location (wl_state_stack_size t) /\
     good_dimindex (:A) /\
     LENGTH xs <= wl_state_clock t ==>
     ?locals smx.
       (match wl_evaluate (AppendLenLoop_code c,t) with
          (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) =
       (match wl_evaluate (AppendLenLoop_code c,
                wl_state_locals_fupd (combin_K locals)
                  (wl_state_clock_fupd (combin_K (wl_state_clock t - LENGTH xs))
                     (wl_state_stack_max_fupd (combin_K smx) t))) with
          (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) /\
       lookup 0 locals = SOME (wl_Loc l1 l2) /\
       lookup 2 locals = SOME (wl_Word (word 2)) /\
       lookup 4 locals = SOME (wl_Word (word (12 * (k + LENGTH xs)))) /\
       option_le (wl_state_stack_max t) smx /\
       option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                       (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                          (lookup AppendLenLoop_location (wl_state_stack_size t))))`)
   (fun th -> MAP_EVERY X_GEN_TAC [`k:num`; `t:(A,C,FFI)wl_state`;
       `c:data_to_word_config`; `xs:data_v list`; `l1:num`; `l2:num`; `w:A word`;
       `vars:(data_v#A word_loc)list`; `ts:num`; `v:data_v`;
       `refs:(data_v bvl_ref)spt`; `sp:num`] THEN
     MATCH_ACCEPT_TAC (SPECL [`xs:data_v list`; `k:num`; `t:(A,C,FFI)wl_state`;
       `c:data_to_word_config`; `l1:num`; `l2:num`; `w:A word`;
       `vars:(data_v#A word_loc)list`; `ts:num`; `v:data_v`;
       `refs:(data_v bvl_ref)spt`; `sp:num`] th)) THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`wl_state_locals (t:(A,C,FFI)wl_state)`;
                          `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
    SUBGOAL_THEN
     `wl_state_locals_fupd (combin_K (wl_state_locals t))
        (wl_state_clock_fupd (combin_K (wl_state_clock t - LENGTH ([]:data_v list)))
           (wl_state_stack_max_fupd (combin_K (wl_state_stack_max t)) t)) =
      (t:(A,C,FFI)wl_state)` SUBST1_TAC THENL
     [REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                  LENGTH; SUB_0];
      ALL_TAC] THEN
    REWRITE_TAC[option_le_refl; option_le_max_right; LENGTH; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `data_v_to_list v = SOME []` THEN
    REWRITE_TAC[v_to_list_EQ_SOME_NIL] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    DRULE_ALL memory_rel_Block_IMP THEN
    REWRITE_TAC[injectivity "word_loc"] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[WORD_MUL_0; WORD_ADD_0];
    ALL_TAC] THEN
  X_GEN_TAC `x:data_v` THEN X_GEN_TAC `xs:data_v list` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:(A,C,FFI)wl_state`;
     `c:data_to_word_config`; `l1:num`; `l2:num`; `w:A word`;
     `vars:(data_v#A word_loc)list`; `ts:num`; `v:data_v`;
     `refs:(data_v bvl_ref)spt`; `sp:num`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP v_to_list_SOME_CONS_IMP) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP2AUX_memory_rel_IMP) THEN
  DRULE_ALL memory_rel_Block_IMP THEN
  REWRITE_TAC[injectivity "word_loc"; NOT_CONS_NIL] THEN STRIP_TAC THEN RVEQ_TAC THEN
  DRULE memory_rel_Block_MEM THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
  ASM_SIMP_TAC[LENGTH; ARITH; ASP2AUX_get_real_offset_1; injectivity "word_loc";
               option_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASP2AUX_SOME_UNIQ_TAC THEN
  SUBGOAL_THEN `?xx. wl_state_memory (t:(A,C,FFI)wl_state)
                  (word_add a (word_mul (word 2) bytes_in_word)) = wl_Word xx`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP ASP2AUX_v_to_list_Block o
     check (fun th -> rand(concl th) = `SOME (xs:data_v list)`)) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
      can (find_term ((=) `ys:data_v`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DRULE_ALL memory_rel_Block_IMP THEN MESON_TAC[];
    ALL_TAC] THEN
  DRULE_ALL (REWRITE_RULE[wl_get_var_def] get_var_get_real_addr_lemma) THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o BINDER_CONV o LAND_CONV o LAND_CONV o LAND_CONV o
    RAND_CONV o LAND_CONV) [AppendLenLoop_code_def] THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (CONS (x:data_v) xs) <= wl_state_clock (t:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
    [data_to_word_gcProof_word_and_one_eq_0_iff; wl_mem_load_def]) THEN
  REWRITE_TAC[ASP1AUX_bad_fun_filter] THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `k + 1`) THEN
  ASP2AUX_SPEC_EVAL_TAC `AppendLenLoop_code c:(A)wl_prog`
    (fun st -> [st; `c:data_to_word_config`; `l1:num`; `l2:num`; `xx:A word`;
                `vars:(data_v#A word_loc)list`; `ts:num`; `ys:data_v`;
                `refs:(data_v bvl_ref)spt`; `sp:num`]) THEN
  ANTS_TAC THENL
   [ASP2AUX_CRW_TAC (asp2_eval_rws @ asp2_eval_rws2 @ asp2_call_rws @
      [LEFT_ADD_DISTRIB; MULT_CLAUSES; WORD_ADD]) THEN
    CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> asp2_head_is "memory_rel" (concl th) &&
         can (find_term ((=) `ys:data_v`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC memory_rel_rearrange THEN
      REWRITE_TAC[MEM] THEN MESON_TAC[];
      UNDISCH_TAC `LENGTH (CONS (x:data_v) xs) <= wl_state_clock (t:(A,C,FFI)wl_state)` THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `locals':(A word_loc)spt` (X_CHOOSE_THEN `smx':num option`
    STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM; OPTION_MAP2_MAX_CANCEL]) THEN
  MAP_EVERY EXISTS_TAC [`locals':(A word_loc)spt`; `smx':num option`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `(k + 1) + n = k + SUC n`];
    ASM_MESON_TAC[option_le_trans; option_le_max_right; option_le_refl]]);;

(* HOL4 line 5370 (val evaluate_AppendLenLoop_code: the theorem above with  *)
(* k = 0, SIMP_RULE std_ss [] |> Q.GEN refs; rebinds the name)            *)
let evaluate_AppendLenLoop_code = prove
 (CASE_TERM
  `!refs (t:(A,C,FFI)wl_state) c xs l1 l2 (w:A word) vars ts v sp.
     memory_rel c (wl_state_be t) ts refs sp (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) (CONS (v,wl_Word w) vars) /\
     data_v_to_list v = SOME xs /\
     lookup 0 (wl_state_locals t) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals t) = SOME (wl_Word w) /\
     lookup 4 (wl_state_locals t) = SOME (wl_Word (word 0)) /\
     lookup AppendLenLoop_location (wl_state_code t) = SOME (3,AppendLenLoop_code c) /\
     wl_state_locals_size t = lookup AppendLenLoop_location (wl_state_stack_size t) /\
     good_dimindex (:A) /\
     LENGTH xs <= wl_state_clock t ==>
     ?locals smx.
       (match wl_evaluate (AppendLenLoop_code c,t) with
          (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) =
       (match wl_evaluate (AppendLenLoop_code c,
                wl_state_locals_fupd (combin_K locals)
                  (wl_state_clock_fupd (combin_K (wl_state_clock t - LENGTH xs))
                     (wl_state_stack_max_fupd (combin_K smx) t))) with
          (res,s) -> if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) /\
       lookup 0 locals = SOME (wl_Loc l1 l2) /\
       lookup 2 locals = SOME (wl_Word (word 2)) /\
       lookup 4 locals = SOME (wl_Word (word (12 * LENGTH xs))) /\
       option_le (wl_state_stack_max t) smx /\
       option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                       (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                          (lookup AppendLenLoop_location (wl_state_stack_size t))))`,
  MAP_EVERY X_GEN_TAC [`refs:(data_v bvl_ref)spt`; `t:(A,C,FFI)wl_state`;
    `c:data_to_word_config`; `xs:data_v list`; `l1:num`; `l2:num`; `w:A word`;
    `vars:(data_v#A word_loc)list`; `ts:num`; `v:data_v`; `sp:num`] THEN
  MP_TAC(SPECL [`0`; `t:(A,C,FFI)wl_state`; `c:data_to_word_config`; `xs:data_v list`;
    `l1:num`; `l2:num`; `w:A word`; `vars:(data_v#A word_loc)list`; `ts:num`;
    `v:data_v`; `refs:(data_v bvl_ref)spt`; `sp:num`] evaluate_AppendLenLoop_code) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* HOL4 line 5373 *)
let v_to_list_block_drop = prove
 (`!k v l.
     data_v_to_list v = SOME l /\ k < LENGTH l ==>
     data_v_to_list (THE (block_drop k v)) = SOME (DROP k l)`,
  INDUCT_TAC THENL [SIMP_TAC[block_drop_def; DROP; THE_DEF]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:data_v list` list_CASES) THEN
  REWRITE_TAC[LENGTH; LT_SUC; ARITH_RULE `~(SUC k < 0)`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP v_to_list_SOME_CONS_IMP) THEN
  ASM_REWRITE_TAC[block_drop_def; DROP] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5384 *)
let OPTION_MAP2_NONE_THM = prove
 (`!(f:A->B->C) x y.
     (OPTION_MAP2 f NONE x = NONE) /\ (OPTION_MAP2 f y NONE = NONE)`,
  REPEAT GEN_TAC THEN CASES_ON `x:B option` THEN CASES_ON `y:A option` THEN
  REWRITE_TAC[OPTION_MAP2_THM]);;

(* HOL4 line 5392 (local) *)
let opt_map_plus_zero_id = prove
 (`!n. OPTION_MAP2 (+) (SOME 0) n = (n:num option)`,
  GEN_TAC THEN CASES_ON `n:num option` THEN REWRITE_TAC[OPTION_MAP2_THM; ADD_CLAUSES]);;

(* HOL4 line 5399 *)
let option_le_flip_neg = prove
 (`!a b. ~option_le a b ==> option_le b a`,
  REPEAT GEN_TAC THEN CASES_ON `a:num option` THEN CASES_ON `b:num option` THEN
  REWRITE_TAC[option_le_def] THEN ARITH_TAC);;

(* HOL4 line 5405 *)
let cut_state_refs_same = prove
 (`!n (s:(C,FFI)data_state) x.
     data_cut_state n s = SOME x ==> data_state_refs s = data_state_refs x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_def] THEN
  CASES_ON `data_cut_env n (data_state_locals (s:(C,FFI)data_state))` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;
