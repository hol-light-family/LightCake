(* ========================================================================= *)
(* crep_arithProof: port of HOL4 pancake/proofs/crep_arithProofScript.sml    *)
(* (CakeML v3479).  Correctness proof for crep_arith pass.                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's Ancestors crepSem crepProps crep_arith: no crepProps theorem is  *)
(*   used, so crepProps is not loaded (pan_commonProps and libext are, for   *)
(*   opt_mmap_mem_func and word_log2).                                       *)
(* - The [local] HOL4 Overloads are written out:                             *)
(*   mapc f s = crep_state_code_fupd (K (FMAP_MAP2 f (crep_state_code s))) s *)
(*   and mapcs = mapc (\(s,n,p). (n,simp_prog p)).                           *)
(* - w2n is val, n2w is word, word_lsl is word_shl, * on words is word_mul, *)
(*   ## is PAIR_MAP (vocab.ml).                                              *)
(* - Local helpers that are not HOL4 theorems are PCREPAUX_.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/libext.ml";;
needs "pancake/semantics/crepSem.ml";;
needs "pancake/crep_arith.ml";;
needs "pancake/semantics/pan_commonProps.ml";;

prioritize_num();;
type_invention_error := true;;
(* dest_2exp n w = SOME m: w is 2 EXP (m - n), below the word size *)

let PCREPAUX_dest_2exp_val = prove
 (`!i (w:A word) n. dest_2exp i w = SOME n ==>
     i <= n /\ n - i < dimindex(:A) /\ val w = 2 EXP (n - i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w:A word = word 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[dest_2exp_def]) THEN
    REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP dest_2exp_lemma) THEN
  SUBGOAL_THEN `val(w:A word) = (2 EXP (n - i)) MOD (2 EXP dimindex(:A))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_1; MULT_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n - i < dimindex(:A)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[LT_EXP] THEN ARITH_TAC;
    UNDISCH_TAC `~(w:A word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `2 EXP (n - i) = 2 EXP dimindex(:A) * 2 EXP ((n - i) - dimindex(:A))`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MOD_MULT; EXP_EQ_0; ARITH_EQ]]);;

let dest_2exp_bound = prove
 (`!n (w:A word) m. dest_2exp n w = SOME m ==> m <= n + val (word_log2 w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PCREPAUX_dest_2exp_val) THEN
  ASM_REWRITE_TAC[word_log2_def; VAL_WORD] THEN
  SUBGOAL_THEN `LOG2 (2 EXP (m - n)) = m - n` SUBST1_TAC THENL
   [MATCH_MP_TAC LOG2_UNIQUE THEN REWRITE_TAC[LE_REFL; LT_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(m - n) MOD 2 EXP dimindex(:A) = m - n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `dimindex(:A)` THEN ASM_REWRITE_TAC[LT_POW2_REFL];
    ASM_ARITH_TAC]);;

let dest_2exp_bound' = prove
 (`!(n:B) (w:A word) m. dest_2exp 0 w = SOME m ==> m < dimindex(:A)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PCREPAUX_dest_2exp_val) THEN
  REWRITE_TAC[SUB_0] THEN MESON_TAC[]);;

let dest_const_thm = prove
 (`dest_const exp = SOME v ==> exp = crep_Const (v:A word)`,
  QCASES_ON "exp" THEN FS[dest_const_def]);;

let eval_mul_const = prove
 (`crep_eval (s:(A,FFI)crep_state) exp = SOME (Word w) ==>
   crep_eval s (mul_const exp c) = SOME (Word (word_mul w c))`,
  DISCH_TAC THEN REWRITE_TAC[mul_const_def] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[crep_eval_def; WORD_MUL_0]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  QCASES_ON "dest_2exp 0 (c:A word)" THEN SIMP[] THENL
   [SIMP[crep_eval_def; OPT_MMAP_DEF; OPTION_BIND_DEF; OPTION_MAP_DEF; crep_op_def; MAP;
         ALL];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP dest_2exp_thm) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ISPEC `0` dest_2exp_bound')) THEN
  SUBGOAL_THEN `~(a = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(c:A word = word 1)` THEN
    ASM_REWRITE_TAC[WORD_SHL_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word a:A word) = a` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `dimindex(:A)` THEN
    ASM_REWRITE_TAC[LT_POW2_REFL];
    ALL_TAC] THEN
  SIMP[crep_eval_def; OPTION_MAP_DEF; word_sh_def; GE; NOT_LE] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[NOT_LE]; REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC WORD_RULE]);;

(* HOL4: [local] *)

let OPT_MMAP_EQ_SOME_MONO = prove
 (`OPT_MMAP (f:A->B option) xs = SOME y ==>
   (!x z. MEM x xs ==> f x = SOME z ==> g x = SOME z) ==>
   OPT_MMAP g xs = SOME y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `OPT_MMAP (g:A->B option) xs = OPT_MMAP f xs`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC OPT_MMAP_CONG THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC opt_mmap_mem_func THEN ASM_MESON_TAC[]);;

(* the code of the state does not matter to crep_eval *)

let PCREPAUX_eval_code_upd = prove
 (`!(s:(A,FFI)crep_state) e g.
     crep_eval (crep_state_code_fupd g s) e = crep_eval s e`,
  MATCH_MP_TAC crep_eval_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[crep_eval_def] THEN SIMP[crep_mem_load_def] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let PCREPAUX_opt_mmap_simp_exp = prove
 (`!(s:(A,FFI)crep_state) es ws.
     OPT_MMAP (crep_eval s) es = SOME ws /\
     (!y. MEM y es ==> !v. crep_eval s y = SOME v ==> crep_eval s (simp_exp y) = SOME v)
     ==> OPT_MMAP (crep_eval s) (MAP simp_exp es) = SOME ws`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPT_MMAP_MAP_o] THEN
  FIRST_ASSUM(fun th -> MATCH_MP_TAC (GEN_ALL (MATCH_MP OPT_MMAP_EQ_SOME_MONO th))) THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

(* a Crepop that evaluates multiplies two words *)

let PCREPAUX_eval_crepop = prove
 (`!(s:(A,FFI)crep_state) op es v.
     crep_eval s (Crepop op es) = SOME v ==>
     ?e1 e2 w1 w2. op = crep_Mul /\ es = [e1; e2] /\
                   crep_eval s e1 = SOME (Word w1) /\ crep_eval s e2 = SOME (Word w2) /\
                   v = Word (word_mul w1 w2)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[crep_eval_def] THEN QCASES_ON "op" THEN
  DISCH_TAC THEN GVS(all_case_eqs()) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[opt_mmap_eq_some]) THEN
  NAMED_CASES_ON "a" ["";"x1 t1"] THEN FS[MAP; crep_op_def] THEN
  NAMED_CASES_ON "t1" ["";"x2 t2"] THEN FS[MAP; crep_op_def] THEN
  NAMED_CASES_ON "t2" ["";"x3 t3"] THEN FS[MAP; crep_op_def] THEN
  GVS[MAP_EQ_CONS; MAP_EQ_NIL] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[EQ_SYM_EQ]) THEN GVS[MAP_EQ_CONS; MAP_EQ_NIL] THEN
  QCASES_ON "x1:(A)word_lab" THEN QCASES_ON "x2:(A)word_lab" THEN SIMP[] THEN
  QEXISTS_TAC "a'" THEN ASM_REWRITE_TAC[]);;

(* simp_exp of a multiplication of two expressions whose simplified forms *)
(* evaluate to words                                                       *)

let PCREPAUX_simp_crepop = prove
 (`!(s:(A,FFI)crep_state) e1 e2 w1 w2.
     crep_eval s (simp_exp e1) = SOME (Word w1) /\
     crep_eval s (simp_exp e2) = SOME (Word w2) ==>
     crep_eval s (simp_exp (Crepop crep_Mul [e1; e2])) =
     SOME (Word (word_mul w1 w2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simp_exp_def; MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN
  QCASES_ON "dest_const (simp_exp (e1:(A)crep_exp))" THEN
  QCASES_ON "dest_const (simp_exp (e2:(A)crep_exp))" THEN SIMP[] THENL
   [ONCE_REWRITE_TAC[crep_eval_def] THEN ASM_REWRITE_TAC[OPT_MMAP_DEF; OPTION_BIND_DEF] THEN
    SIMP[OPTION_MAP_DEF; crep_op_def; MAP; ALL];
    IMP_RES_TAC dest_const_thm THEN RFS[crep_eval_def] THEN RVEQ_TAC THEN
    IMP_RES_TAC eval_mul_const THEN ASM_REWRITE_TAC[];
    IMP_RES_TAC dest_const_thm THEN RFS[crep_eval_def] THEN RVEQ_TAC THEN
    IMP_RES_TAC eval_mul_const THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_MUL_SYM];
    IMP_RES_TAC dest_const_thm THEN RFS[crep_eval_def] THEN RVEQ_TAC THEN
    REWRITE_TAC[crep_eval_def]]);;

(* simp_exp preserves successful evaluation (by induction; HOL4 proves the *)
(* form simp_exp_correct1 directly)                                        *)

let PCREPAUX_simp_exp_some = prove
 (`!(s:(A,FFI)crep_state) exp v.
     crep_eval s exp = SOME v ==> crep_eval s (simp_exp exp) = SOME v`,
  let gen_tac =
    REPEAT STRIP_TAC THEN
    QPAT_X_ASSUM "crep_eval _ _ = SOME _" (MP_TAC o ONCE_REWRITE_RULE[crep_eval_def]) THEN
    DISCH_TAC THEN GVS(all_case_eqs()) THEN RES_TAC THEN
    IMP_RES_TAC PCREPAUX_opt_mmap_simp_exp THEN REWRITE_TAC[simp_exp_def] THEN
    ONCE_REWRITE_TAC[crep_eval_def] THEN SIMP[]
  and crepop_tac =
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PCREPAUX_eval_crepop) THEN RVEQ_TAC THEN
    MATCH_MP_TAC PCREPAUX_simp_crepop THEN ASM_MESON_TAC[MEM] in
  MATCH_MP_TAC crep_eval_ind THEN REPEAT CONJ_TAC THENL
   [gen_tac; gen_tac; gen_tac; gen_tac; gen_tac; gen_tac; gen_tac; crepop_tac;
    gen_tac; gen_tac; gen_tac; gen_tac]);;

(* HOL4: [local]; mapc f s = crep_state_code_fupd (K (FMAP_MAP2 f            *)
(* (crep_state_code s))) s                                                  *)

let simp_exp_correct1 = prove
 (`!(s:(A,FFI)crep_state) exp (v:B).
     ~(crep_eval s exp = NONE) ==>
     crep_eval (crep_state_code_fupd (K (FMAP_MAP2 f (crep_state_code s))) s)
       (simp_exp exp) =
     crep_eval s exp`,
  REWRITE_TAC[PCREPAUX_eval_code_upd] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A,FFI)crep_state`; `exp:(A)crep_exp`] PCREPAUX_simp_exp_some) THEN
  QCASES_ON "crep_eval s exp" THEN ASM_MESON_TAC[]);;

let simp_exp_correct = prove
 (`crep_eval (s:(A,FFI)crep_state) exp = SOME v ==>
   crep_eval (crep_state_code_fupd (K (FMAP_MAP2 f (crep_state_code s))) s)
     (simp_exp exp) = SOME v`,
  RW[simp_exp_correct1; option_DISTINCT]);;

let PCREPAUX_eval_code_upd_fun = prove
 (`!(s:(A,FFI)crep_state) g. crep_eval (crep_state_code_fupd g s) = crep_eval s`,
  REWRITE_TAC[FUN_EQ_THM; PCREPAUX_eval_code_upd]);;

let opt_mmap_simp_exp_correct = prove
 (`OPT_MMAP (crep_eval (s:(A,FFI)crep_state)) es = SOME vs ==>
   OPT_MMAP (crep_eval (crep_state_code_fupd (K (FMAP_MAP2 f (crep_state_code s))) s))
     (MAP simp_exp es) = SOME vs`,
  REWRITE_TAC[PCREPAUX_eval_code_upd_fun] THEN STRIP_TAC THEN
  MATCH_MP_TAC PCREPAUX_opt_mmap_simp_exp THEN ASM_REWRITE_TAC[PCREPAUX_simp_exp_some]);;

(* HOL4: [local] *)

let lookup_code = prove
 (`crep_lookup_code (FMAP_MAP2 (\(s,n,p). (n,simp_prog p))
                       (c:(K,(N)list#(A)crep_prog)fmap)) fname (args:(V)list) (len:L) =
   OPTION_MAP (simp_prog ## I) (crep_lookup_code c fname args len)`,
  REWRITE_TAC[crep_lookup_code_def; FLOOKUP_FMAP_MAP2] THEN
  QCASES_ON "FLOOKUP (c:(K,(N)list#(A)crep_prog)fmap) fname" THEN SIMP[OPTION_MAP_DEF] THEN
  PAIR_CASES_ON `a:(N)list#(A)crep_prog` THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

(* HOL4: [local] *)

let sh_mem_op_code = prove
 (`crep_sh_mem_op op p addr
     (crep_state_code_fupd (K (FMAP_MAP2 f (crep_state_code s))) (s:(A,FFI)crep_state)) =
   ((I:((B)crep_result)option->((B)crep_result)option) ##
    (\s. crep_state_code_fupd (K (FMAP_MAP2 f (crep_state_code s))) s))
     (crep_sh_mem_op op p addr s)`,
  QCASES_ON "op" THEN
  SIMP[crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
  EVERY_CASE_TAC THEN SIMP[crep_set_var_def; crep_empty_locals_def; PAIR_MAP_THM; I_THM]);;

(* HOL4: [local] ind_thm = evaluate_ind |> Q.SPEC `UNCURRY Q` |>              *)
(* REWRITE_RULE [UNCURRY_DEF] |> Q.GEN `Q`                                   *)

let ind_thm =
  GEN `Q:(A)crep_prog->(A,FFI)crep_state->bool`
    (REWRITE_RULE[UNCURRY_DEF]
       (ISPEC `UNCURRY (Q:(A)crep_prog->(A,FFI)crep_state->bool)` crep_evaluate_ind));;

(* HOL4 mapcs s = s with code := FMAP_MAP2 (\(s,n,p). (n,simp_prog p))      *)
(* s.code.  One tactic for the cases of the induction: the evaluation is     *)
(* unfolded once and split, the induction hypotheses instantiated at the     *)
(* facts found (FULL_RES_TAC), the simplified program evaluated one step;    *)
(* for crep_Call the call type is split first.                              *)

let simp_prog_correct = prove
 (`!p (s:(A,FFI)crep_state) r s'.
     crep_evaluate (p,s) = (r,s') ==>
     ~(r = SOME crep_Error) ==>
     crep_evaluate
       (simp_prog p,
        crep_state_code_fupd
          (K (FMAP_MAP2 (\(s,n,p). (n,simp_prog p)) (crep_state_code s))) s) =
     (r,crep_state_code_fupd
          (K (FMAP_MAP2 (\(s,n,p). (n,simp_prog p)) (crep_state_code s'))) s')`,
  let step_tac =
    QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
    DISCH_TAC THEN GVS(all_case_eqs()) THEN FULL_RES_TAC THEN
    IMP_RES_TAC simp_exp_correct THEN IMP_RES_TAC opt_mmap_simp_exp_correct THEN
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[crep_dec_clock_def; crep_empty_locals_def;
                                  crep_set_var_def; crep_set_globals_def; simp_prog_def]) THEN
    REWRITE_TAC[simp_prog_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN
    SIMP[lookup_code; sh_mem_op_code; PCREPAUX_eval_code_upd; PCREPAUX_eval_code_upd_fun;
         crep_dec_clock_def; crep_empty_locals_def; crep_set_var_def; crep_set_globals_def;
         OPTION_MAP_DEF; PAIR_MAP_THM; I_THM] THEN
    TRY(COND_CASES_TAC THEN RFS[]) in
  let call_tac =
    REPEAT STRIP_TAC THEN NAMED_CASES_ON "caltyp" ["";"ct"] THEN
    TRY(PAIR_CASES_ON `ct:(num)list#((A word#(A)crep_prog)option)`) THEN
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN step_tac in
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THENL
   (map (fun i -> if i = 17 then call_tac else REPEAT STRIP_TAC THEN step_tac) (0--18)));;
