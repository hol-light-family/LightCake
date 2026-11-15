(* ========================================================================= *)
(* word_instProof: port of HOL4 compiler/backend/proofs/                     *)
(* word_instProofScript.sml (CakeML v3479).                                  *)
(* Correctness proof for word_inst.                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang, wordSem, wordProps and word_inst are those of    *)
(*   their files (wl_evaluate, wl_word_exp, wl_state_locals, ...): HOL4 s.f  *)
(*   is wl_state_f s, s with f := v is wl_state_f_fupd (K v) s.              *)
(* - HOL4's Type result = wordSem$result (a parsing abbreviation) is not    *)
(*   needed: the result type is (A)wl_result.  is_const is                   *)
(*   word_inst_is_const; HOL4 exp_size ARB is wl_exp_size (\x. 0).           *)
(* - The proofs of inst_select_exp_thm and inst_select_thm go by cases: one *)
(*   lemma per expression or program constructor (WPROOF2AUX_ise_...,       *)
(*   WPROOF2AUX_is_...), with the statement as a term function              *)
(*   (WPROOF2AUX_ise, WPROOF2AUX_is) and small evaluation lemmas for the     *)
(*   instructions that inst_select emits (WPROOF2AUX_eval_...); the ShareInst *)
(*   case uses wordProps' IL2AUX_share_inst_lr.                              *)
(* - WPROOF2AUX_ names are local helpers.                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/encoders/asm/asm.ml";;

type_invention_error := true;;

(* the case equations that the proofs below split (HOL4 AllCaseEqs(), for   *)
(* the types that occur here)                                                *)

let WPROOF2AUX_ceqs =
  [COND_CASE_EQ; option_case_eq; case_eq "word_loc"; pair_case_eq; list_case_eq];;

(* TODO: Move, but some of these are specific instantiations *)

let PERM_SWAP_SIMP = prove
 (`PERM (APPEND (a:A list) (CONS b c)) (CONS b (APPEND a c))`,
  MATCH_MP_TAC APPEND_PERM_SYM THEN REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[PERM_CONS_IFF; PERM_APPEND]);;

let EL_FILTER = prove
 (`!ls x. x < LENGTH (FILTER P ls) ==> P (EL x (FILTER P (ls:A list)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH; LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC]);;

let PERM_SWAP = prove
 (`PERM (APPEND (APPEND (a:A list) b) c) (APPEND b (APPEND a c))`,
  REWRITE_TAC[APPEND_ASSOC] THEN REWRITE_TAC[PERM_APPEND_IFF; PERM_APPEND]);;

(* Instruction selection and assorted optimisation correctness              *)
(* 0) pull_exp correctness -- this does pull_ops and optimize_consts         *)
(* 1) pull_exp syntax                                                         *)
(* 2) flatten_exp correctness -- makes stuff into binary branching trees     *)
(* 3) flatten_exp syntax -- prove the above property (binary_branch_exp)     *)
(* 4) inst_select_exp and inst_select correctness                            *)
(* 5) inst_select syntax -- flat_exp_conventions and full_inst_ok_less        *)
(* 6) three_to_two_reg correctness                                            *)
(* 7) three_to_two_reg syntax -- two_reg_insts and some preservation ones    *)

(* pull_exp correctness *)

let WPROOF2AUX_convert_sub_add = prove
 (`!x w. wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op asm_Add [wl_Const (word_neg w); x]) =
         wl_word_exp s (wl_Op asm_Sub [x; wl_Const w])`,
  REPEAT GEN_TAC THEN SIMP[wl_word_exp_def; MAP; the_words_def] THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) x` THEN SIMP[] THEN
  CASES_ON `a:(A)word_loc` THEN SIMP[word_op_def; ITLIST] THEN
  CONV_TAC WORD_RULE);;

let convert_sub_ok = prove
 (`!ls. wl_word_exp (s:(A,C,FFI)wl_state) (convert_sub ls) =
        wl_word_exp s (wl_Op asm_Sub ls)`,
  GEN_TAC THEN REWRITE_TAC[convert_sub_pmatch] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[WPROOF2AUX_convert_sub_add]) THEN
  SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def]);;

(* the four commutative operations commute on the left *)

let WPROOF2AUX_word_lcomm = prove
 (`!x y z:A word.
     word_add x (word_add y z) = word_add y (word_add x z) /\
     word_and x (word_and y z) = word_and y (word_and x z) /\
     word_or x (word_or y z) = word_or y (word_or x z) /\
     word_xor x (word_xor y z) = word_xor y (word_xor x z)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE; CONV_TAC WORD_BITWISE_RULE;
    CONV_TAC WORD_BITWISE_RULE]);;

(* In general, any permutation works *)

let word_exp_op_permute_lem = prove
 (`~(op = asm_Sub) ==>
   !ls ls'. PERM ls ls' ==>
     wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op ls) = wl_word_exp s (wl_Op op ls')`,
  DISCH_TAC THEN MATCH_MP_TAC PERM_STRONG_IND THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[];
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN SIMP[wl_word_exp_def; MAP; the_words_def] THEN
    EVERY_CASE_TAC THEN CASES_ON `op:binop` THEN FS[word_op_def; ITLIST];
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN SIMP[wl_word_exp_def; MAP; the_words_def] THEN
    EVERY_CASE_TAC THEN CASES_ON `op:binop` THEN
    FS[word_op_def; ITLIST; WPROOF2AUX_word_lcomm];
    MESON_TAC[]]);;

(* Remove tail recursion to make proof easier... *)

let pull_ops_simp_def = cake_def
  `(pull_ops_simp (op:binop) [] = []:((A)wl_exp)list) /\
   (pull_ops_simp op (CONS x xs) =
      match x with
        wl_Op op' ls ->
          if op = op' then APPEND ls (pull_ops_simp op xs)
          else CONS x (pull_ops_simp op xs)
      | _ -> CONS x (pull_ops_simp op xs))`;;

let WPROOF2AUX_perm_cons = prove
 (`!f p (e:A) x. (!x. PERM (f x) (APPEND p x))
                 ==> PERM (f (CONS e x)) (CONS e (APPEND p x))`,
  MESON_TAC[PERM_TRANS; PERM_SWAP_SIMP]);;

let pull_ops_simp_pull_ops_perm = prove
 (`!ls x. PERM (pull_ops op ls x) (APPEND (pull_ops_simp op ls) (x:((A)wl_exp)list))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[pull_ops_def; pull_ops_simp_def; APPEND; PERM_REFL] THEN
  GEN_TAC THEN CASES_ON `h:(A)wl_exp` THEN CASE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[APPEND] THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    MATCH_MP_TAC PERM_TRANS THEN
    EXISTS_TAC `APPEND (pull_ops_simp op t) (APPEND a1 (x:((A)wl_exp)list))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[APPEND_ASSOC] THEN
    MATCH_ACCEPT_TAC (REWRITE_RULE[APPEND_ASSOC] PERM_SWAP);
    ALL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP WPROOF2AUX_perm_cons));;

let pull_ops_simp_pull_ops_word_exp = prove
 (`~(op = asm_Sub) ==>
   wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op (pull_ops op ls [])) =
   wl_word_exp s (wl_Op op (pull_ops_simp op ls))`,
  DISCH_THEN(MP_TAC o MATCH_MP word_exp_op_permute_lem) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`ls:((A)wl_exp)list`; `[]:((A)wl_exp)list`]
         pull_ops_simp_pull_ops_perm) THEN
  REWRITE_TAC[APPEND_NIL]);;

(* TODO: Maybe move to props, if these are needed elsewhere *)

let word_exp_op_mono = prove
 (`~(op = asm_Sub) ==>
   wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op ls) = wl_word_exp s (wl_Op op ls') ==>
   wl_word_exp s (wl_Op op (CONS x ls)) = wl_word_exp s (wl_Op op (CONS x ls'))`,
  DISCH_TAC THEN SIMP[wl_word_exp_def; MAP; the_words_def] THEN
  EVERY_CASE_TAC THEN CASES_ON `op:binop` THEN FS[word_op_def; ITLIST]);;

let the_words_append = prove
 (CASE_TERM
  `!ls ls'. the_words (APPEND ls ls') =
     match the_words ls with
       NONE -> NONE
     | SOME w -> (match the_words ls' with
                    NONE -> NONE
                  | SOME v -> SOME (APPEND w (v:((A)word)list)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; the_words_def] THEN GEN_TAC THENL
   [CASES_ON `the_words (ls':(((A)word_loc)option)list)` THEN SIMP[APPEND];
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    EVERY_CASE_TAC THEN FS[APPEND]]);;

(* ITLIST of a monoid operation *)

let WPROOF2AUX_itlist_monoid = prove
 (`!(f:A->A->A) e l z. (!x. f e x = x) /\ (!x y z. f x (f y z) = f (f x y) z)
     ==> ITLIST f l z = f (ITLIST f l e) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`z:A`,`z:A`) THEN
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ITLIST];
    REWRITE_TAC[ITLIST] THEN GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    ASM_REWRITE_TAC[]]);;

let WPROOF2AUX_itlist_word_ops = prove
 (`!l z:A word.
     ITLIST word_add l z = word_add (ITLIST word_add l (word 0)) z /\
     ITLIST word_and l z = word_and (ITLIST word_and l (word_not (word 0))) z /\
     ITLIST word_or l z = word_or (ITLIST word_or l (word 0)) z /\
     ITLIST word_xor l z = word_xor (ITLIST word_xor l (word 0)) z`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC WPROOF2AUX_itlist_monoid THEN
  REWRITE_TAC[WORD_ADD_0; WORD_AND_NOT0; WORD_OR_0; WORD_XOR_0; WORD_ADD_ASSOC;
              WORD_AND_ASSOC; WORD_OR_ASSOC; WORD_XOR_ASSOC]);;

let word_exp_op_op = prove
 (`~(op = asm_Sub) ==>
   !ls ls'.
     wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op ls) = wl_word_exp s (wl_Op op ls') ==>
     wl_word_exp s (wl_Op op (APPEND l ls)) =
     wl_word_exp s (wl_Op op (CONS (wl_Op op l) ls'))`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  SIMP[wl_word_exp_def; MAP; MAP_APPEND; the_words_def; the_words_append] THEN
  EVERY_CASE_TAC THEN CASES_ON `op:binop` THEN FS[word_op_def; ITLIST; ITLIST_APPEND] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [WPROOF2AUX_itlist_word_ops] THEN REFL_TAC);;

let pull_ops_ok = prove
 (`~(op = asm_Sub) ==>
   !ls. wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op (pull_ops op ls [])) =
        wl_word_exp s (wl_Op op ls)`,
  DISCH_TAC THEN ASM_SIMP_TAC[pull_ops_simp_pull_ops_word_exp] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[pull_ops_simp_def] THEN
  CASES_ON `h:(A)wl_exp` THEN CASE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN
  FIRST [MATCH_MP_TAC (UNDISCH word_exp_op_mono) THEN ASM_REWRITE_TAC[];
         FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
         MATCH_MP_TAC (UNDISCH word_exp_op_op) THEN ASM_REWRITE_TAC[]]);;

(* Done with pull_ops, next is optimize_consts *)

let word_exp_swap_head = prove
 (`!B. ~(op = asm_Sub) ==>
       wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op A) = SOME (wl_Word w) ==>
       wl_word_exp s (wl_Op op (APPEND B A)) =
       wl_word_exp s (wl_Op op (CONS (wl_Const w) B))`,
  GEN_TAC THEN DISCH_TAC THEN
  SIMP[wl_word_exp_def; MAP; MAP_APPEND; the_words_def; the_words_append] THEN
  EVERY_CASE_TAC THEN CASES_ON `op:binop` THEN FS[word_op_def; ITLIST; ITLIST_APPEND] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC LAND_CONV [WPROOF2AUX_itlist_word_ops] THEN
  REWRITE_TAC[WORD_ADD_SYM; WORD_AND_SYM; WORD_OR_SYM; WORD_XOR_SYM]);;

let EVERY_is_const_word_exp = prove
 (`!ls. ALL word_inst_is_const ls ==>
        ALL IS_SOME (MAP (\a. wl_word_exp (s:(A,C,FFI)wl_state) a) ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  CASES_ON `h:(A)wl_exp` THEN
  REWRITE_TAC[word_inst_is_const_def; wl_word_exp_def; IS_SOME_DEF] THEN
  ASM_MESON_TAC[]);;

let all_consts_simp = prove
 (`~(op = asm_Sub) ==>
   !ls. ALL word_inst_is_const ls ==>
        wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op ls) =
        SOME (wl_Word (THE (word_op op (MAP rm_const ls))))`,
  DISCH_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THENL
   [SIMP[wl_word_exp_def; MAP; the_words_def] THEN
    CASES_ON `op:binop` THEN FS[word_op_def; ITLIST; THE_DEF];
    ALL_TAC] THEN
  CASES_ON `h:(A)wl_exp` THEN REWRITE_TAC[word_inst_is_const_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `ALL word_inst_is_const (t:((A)wl_exp)list)`)) THEN
  SIMP[wl_word_exp_def; MAP; the_words_def; rm_const_def] THEN
  EVERY_CASE_TAC THEN CASES_ON `op:binop` THEN FS[word_op_def; ITLIST; THE_DEF]);;

let word_exp_reduce_const = prove
 (`wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op (CONS (wl_Const w) rest)) = SOME x ==>
   wl_word_exp s (reduce_const op w rest) = SOME x`,
  REWRITE_TAC[reduce_const_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REPEAT TOP_CASE_TAC THEN
    SIMP[wl_word_exp_def; MAP; the_words_def] THEN
    EVERY_CASE_TAC THEN FS[word_op_def; ITLIST] THEN
    REWRITE_TAC[WORD_ADD_0; WORD_OR_0; WORD_XOR_0];
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SIMP[wl_word_exp_def; MAP; the_words_def] THEN
    EVERY_CASE_TAC THEN FS[word_op_def; ITLIST] THEN
    REWRITE_TAC[WORD_AND_0]]);;

let optimize_consts_ok = prove
 (`~(op = asm_Sub) /\ wl_word_exp (s:(A,C,FFI)wl_state) (wl_Op op ls) = SOME x ==>
   wl_word_exp s (optimize_consts op ls) = SOME x`,
  STRIP_TAC THEN REWRITE_TAC[optimize_consts_def] THEN PAIRARG_TAC THEN
  SUBGOAL_THEN `PERM ls (APPEND const_ls nconst_ls:((A)wl_exp)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC misc_PERM_PARTITION THEN
    EXISTS_TAC `word_inst_is_const:(A)wl_exp->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL word_inst_is_const (const_ls:((A)wl_exp)list)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN
    MP_TAC(ISPECL [`word_inst_is_const:(A)wl_exp->bool`; `ls:((A)wl_exp)list`;
                   `const_ls:((A)wl_exp)list`; `nconst_ls:((A)wl_exp)list`;
                   `[]:((A)wl_exp)list`; `[]:((A)wl_exp)list`] PARTs_HAVE_PROP) THEN
    ASM_REWRITE_TAC[GSYM PARTITION_DEF; MEM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP word_exp_op_permute_lem) THEN
  CASES_ON `const_ls:((A)wl_exp)list` THEN CASE_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(MP_TAC o MATCH_MP th)) THEN
    ASM_REWRITE_TAC[APPEND] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN MATCH_MP_TAC word_exp_reduce_const THEN
  MP_TAC(SPEC `CONS (a0:(A)wl_exp) a1` (UNDISCH all_consts_simp)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (UNDISCH (SPEC `nconst_ls:((A)wl_exp)list` word_exp_swap_head))) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `wl_word_exp (s:(A,C,FFI)wl_state)
                  (wl_Op op (APPEND nconst_ls (CONS a0 a1))) =
                wl_word_exp s (wl_Op op ls)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC PERM_TRANS THEN
    EXISTS_TAC `APPEND (CONS a0 a1) nconst_ls:((A)wl_exp)list` THEN
    ASM_REWRITE_TAC[PERM_APPEND];
    ASM_REWRITE_TAC[]]);;

(* word_exp of an Op whose arguments are mapped by a value-preserving f *)

let WPROOF2AUX_the_words_map = prove
 (`!ls ws (s:(A,C,FFI)wl_state).
     (!e. MEM e ls ==> !x. wl_word_exp s e = SOME x ==> wl_word_exp s (f e) = SOME x) /\
     the_words (MAP (wl_word_exp s) ls) = SOME ws
     ==> the_words (MAP (wl_word_exp s) (MAP f ls)) = SOME ws`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; the_words_def] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM;
              FORALL_UNWIND_THM2] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) h` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `a:(A)word_loc` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `the_words (MAP (wl_word_exp (s:(A,C,FFI)wl_state)) t)` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wl_word_exp (s:(A,C,FFI)wl_state) ((f:(A)wl_exp->(A)wl_exp) h) =
                SOME (wl_Word a')`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `the_words (MAP (wl_word_exp (s:(A,C,FFI)wl_state))
                  (MAP (f:(A)wl_exp->(A)wl_exp) t)) = SOME a''`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_word_exp_Op_map = prove
 (`!ls op x (s:(A,C,FFI)wl_state).
     (!e. MEM e ls ==> !x. wl_word_exp s e = SOME x ==> wl_word_exp s (f e) = SOME x) /\
     wl_word_exp s (wl_Op op ls) = SOME x
     ==> wl_word_exp s (wl_Op op (MAP f ls)) = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def] THEN
  CASES_ON `the_words (MAP (wl_word_exp (s:(A,C,FFI)wl_state)) ls)` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `the_words (MAP (wl_word_exp (s:(A,C,FFI)wl_state))
                  (MAP (f:(A)wl_exp->(A)wl_exp) ls)) = SOME a`
    SUBST1_TAC THENL
   [MATCH_MP_TAC WPROOF2AUX_the_words_map THEN ASM_REWRITE_TAC[];
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

(* tactics for the expression proofs: substitute the induction hypotheses  *)
(* (word_exp s e = SOME x ==> word_exp s (f e) = SOME x) at the facts       *)
(* word_exp s e = SOME v of the assumptions                                 *)

let WPROOF2AUX_IH_SUBST_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun ih -> FIRST_ASSUM (fun eq ->
    SUBST1_TAC (MATCH_MP ih eq))));;

let WPROOF2AUX_EXP_IH_TAC : tactic =
  DISCH_THEN(STRIP_ASSUME_TAC o CAKE_SIMP_RULE WPROOF2AUX_ceqs) THEN RVEQ_TAC THEN
  WPROOF2AUX_IH_SUBST_TAC THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN SIMP[];;

let WPROOF2AUX_long_tac : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC optimize_consts_ok THEN SIMP_TAC[pull_ops_ok; distinctness "binop"] THEN
  MATCH_MP_TAC WPROOF2AUX_word_exp_Op_map THEN ASM_MESON_TAC[];;

let WPROOF2AUX_single_tac : tactic =
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP[wl_word_exp_def; MAP; the_words_def] THEN EVERY_CASE_TAC THEN
  FS[word_op_def; ITLIST; WORD_ADD_0; WORD_AND_NOT0; WORD_OR_0; WORD_XOR_0];;

let pull_exp_ok = prove
 (`!exp (s:(A,C,FFI)wl_state) x.
     wl_word_exp s exp = SOME x ==> wl_word_exp s (pull_exp exp) = SOME x`,
  MATCH_MP_TAC pull_exp_ind THEN REWRITE_TAC[pull_exp_def; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THENL
   [(* Sub *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[convert_sub_ok] THEN
    MATCH_MP_TAC WPROOF2AUX_word_exp_Op_map THEN ASM_MESON_TAC[];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    WPROOF2AUX_single_tac; WPROOF2AUX_single_tac; WPROOF2AUX_single_tac;
    WPROOF2AUX_single_tac;
    WPROOF2AUX_long_tac; WPROOF2AUX_long_tac; WPROOF2AUX_long_tac; WPROOF2AUX_long_tac;
    (* Load *)
    GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def] THEN
    WPROOF2AUX_EXP_IH_TAC;
    (* Shift *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def] THEN
    WPROOF2AUX_EXP_IH_TAC]);;

(* pull_exp syntax *)

let convert_sub_every_var_exp = prove
 (`!ls. (!x. MEM x ls ==> every_var_exp P x) ==>
        every_var_exp P (convert_sub ls:(A)wl_exp)`,
  GEN_TAC THEN REWRITE_TAC[ALL_MEM; ETA_AX] THEN REWRITE_TAC[convert_sub_pmatch] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
  REWRITE_TAC[every_var_exp_def; ALL; ETA_AX] THEN SIMP_TAC[]);;

let optimize_consts_every_var_exp = prove
 (`!ls. (!x. MEM x ls ==> every_var_exp P x) ==>
        every_var_exp P (optimize_consts op ls:(A)wl_exp)`,
  GEN_TAC THEN REWRITE_TAC[optimize_consts_def] THEN PAIRARG_TAC THEN
  SUBGOAL_THEN `PERM ls (APPEND const_ls nconst_ls:((A)wl_exp)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC misc_PERM_PARTITION THEN
    EXISTS_TAC `word_inst_is_const:(A)wl_exp->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERM_MEM_EQ) THEN
  ASM_REWRITE_TAC[MEM_APPEND] THEN DISCH_TAC THEN
  REWRITE_TAC[reduce_const_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  ASM_SIMP_TAC[every_var_exp_def; GSYM ALL_MEM; ALL; MEM]);;

(* HOL4: a val (pull_ops_every_var_exp), stated after REWRITE_RULE[EVERY_MEM] *)

let pull_ops_every_var_exp = prove
 (`!ls acc. (!x. MEM x acc ==> every_var_exp P x) /\
            (!x. MEM x ls ==> every_var_exp P x)
            ==> !x. MEM x (pull_ops op ls acc) ==> every_var_exp P (x:(A)wl_exp)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[pull_ops_def; MEM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `h:(A)wl_exp` THEN CASE_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM; MEM_APPEND] THEN
  ASM_MESON_TAC[every_var_exp_def; ALL_MEM]);;

let pull_exp_every_var_exp = prove
 (`!exp. every_var_exp P exp ==> every_var_exp P (pull_exp exp:(A)wl_exp)`,
  MATCH_MP_TAC pull_exp_ind THEN
  REWRITE_TAC[op_consts_def; pull_exp_def; every_var_exp_def; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC convert_sub_every_var_exp THEN
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MEM] THEN MESON_TAC[];
    REWRITE_TAC[MEM] THEN MESON_TAC[];
    REWRITE_TAC[MEM] THEN MESON_TAC[];
    REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC optimize_consts_every_var_exp THEN
  MATCH_MP_TAC pull_ops_every_var_exp THEN
  (CONJ_TAC THENL [REWRITE_TAC[MEM]; REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]]));;

(* flatten_exp correctness *)

let WPROOF2AUX_word_exp_op_cons = prove
 (`!op x xs (s:(A,C,FFI)wl_state) v.
     wl_word_exp s (wl_Op op (CONS x xs)) = SOME v ==> ~(op = asm_Sub)
     ==> ?a w. wl_word_exp s x = SOME (wl_Word a) /\
               wl_word_exp s (wl_Op op xs) = SOME (wl_Word w) /\
               !e1 e2. wl_word_exp s e1 = SOME (wl_Word w) /\
                       wl_word_exp s e2 = SOME (wl_Word a)
                       ==> wl_word_exp s (wl_Op op [e1; e2]) = SOME v`,
  REPEAT GEN_TAC THEN SIMP[wl_word_exp_def; MAP; the_words_def] THEN
  EVERY_CASE_TAC THEN CASES_ON `op:binop` THEN FS[word_op_def; ITLIST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SIMP[ITLIST; WORD_ADD_0; WORD_AND_NOT0; WORD_OR_0; WORD_XOR_0] THEN
  REWRITE_TAC[WORD_ADD_SYM; WORD_AND_SYM; WORD_OR_SYM; WORD_XOR_SYM]);;

let WPROOF2AUX_flatten_long_tac : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_word_exp_op_cons) THEN
  REWRITE_TAC[distinctness "binop"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];;

let flatten_exp_ok = prove
 (`!exp (s:(A,C,FFI)wl_state) x.
     wl_word_exp s exp = SOME x ==> wl_word_exp s (flatten_exp exp) = SOME x`,
  MATCH_MP_TAC flatten_exp_ind THEN REWRITE_TAC[flatten_exp_def] THEN
  REPEAT CONJ_TAC THENL
   [(* Sub *)
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WPROOF2AUX_word_exp_Op_map THEN ASM_MESON_TAC[];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    SIMP[wl_word_exp_def; MAP; the_words_def; word_op_def; ITLIST; op_consts_def];
    WPROOF2AUX_single_tac; WPROOF2AUX_single_tac; WPROOF2AUX_single_tac;
    WPROOF2AUX_single_tac;
    WPROOF2AUX_flatten_long_tac; WPROOF2AUX_flatten_long_tac;
    WPROOF2AUX_flatten_long_tac; WPROOF2AUX_flatten_long_tac;
    (* Load *)
    GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def] THEN
    WPROOF2AUX_EXP_IH_TAC;
    (* Shift *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[wl_word_exp_def] THEN
    WPROOF2AUX_EXP_IH_TAC]);;

(* All ops are 2 args. Technically, we should probably check that Sub has 2  *)
(* args. However, the semantics already checks that and it will get removed  *)
(* later.  HOL4 exp_size ARB is wl_exp_size (\x. 0).                         *)

let binary_branch_exp_def = sem1aux_def_wf `measure (wl_exp_size (\x:A. 0))` TERM_TAC
  `(binary_branch_exp (wl_Op asm_Sub exps) <=> ALL binary_branch_exp exps) /\
   (binary_branch_exp (wl_Op op xs) <=> LENGTH xs = 2 /\ ALL binary_branch_exp xs) /\
   (binary_branch_exp (wl_Load exp) <=> binary_branch_exp exp) /\
   (binary_branch_exp (wl_Shift shift exp nexp) <=>
      binary_branch_exp exp /\ binary_branch_exp nexp) /\
   (binary_branch_exp (exp:(A)wl_exp) <=> T)`;;

let binary_branch_exp_ind = cake_ind "binary_branch_exp";;

(* flatten_exp syntax *)

let flatten_exp_binary_branch_exp = prove
 (`!exp:(A)wl_exp. binary_branch_exp (flatten_exp exp)`,
  MATCH_MP_TAC flatten_exp_ind THEN
  REWRITE_TAC[op_consts_def; flatten_exp_def; binary_branch_exp_def; GSYM ALL_MEM;
              ALL_MAP; o_DEF; LENGTH; ALL] THEN
  REWRITE_TAC[ALL_MEM; ETA_AX] THEN SIMP_TAC[ARITH]);;

let flatten_exp_every_var_exp = prove
 (`!exp:(A)wl_exp. every_var_exp P exp ==> every_var_exp P (flatten_exp exp)`,
  MATCH_MP_TAC flatten_exp_ind THEN
  REWRITE_TAC[op_consts_def; flatten_exp_def; every_var_exp_def; ALL_MAP; o_DEF; ALL] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

(* inst_select correctness.  Main difficulty: Dealing with multiple choice  *)
(* of optimizations, depending on whether we are allowed to use them w.r.t.  *)
(* to the asm configuration                                                   *)

(* steps of the evaluation of the selected instructions, on a state whose   *)
(* locals are replaced                                                        *)

let WPROOF2AUX_fix_clock_locals = prove
 (`!l1 l2 (s:(A,C,FFI)wl_state) (res:((A)wl_result)option).
     wl_fix_clock (wl_state_locals_fupd (K l1) s) (res, wl_state_locals_fupd (K l2) s) =
     (res, wl_state_locals_fupd (K l2) s)`,
  REWRITE_TAC[wl_fix_clock_def; LT_REFL] THEN SIMP[] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let WPROOF2AUX_eval_Seq_locals = prove
 (`!c1 c2 l1 l2 (s:(A,C,FFI)wl_state).
     wl_evaluate (c1, wl_state_locals_fupd (K l1) s) =
       (NONE, wl_state_locals_fupd (K l2) s)
     ==> wl_evaluate (wl_Seq c1 c2, wl_state_locals_fupd (K l1) s) =
         wl_evaluate (c2, wl_state_locals_fupd (K l2) s)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[WPROOF2AUX_fix_clock_locals] THEN CASE_REWRITE_TAC[]);;

let WPROOF2AUX_eval_Const = prove
 (`!r w l (s:(A,C,FFI)wl_state).
     wl_evaluate (wl_Inst (asm_Const r w), wl_state_locals_fupd (K l) s) =
     (NONE, wl_state_locals_fupd (K (insert r (wl_Word w) l)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def; wl_assign_def; wl_word_exp_def; wl_set_var_def] THEN
  CASE_REWRITE_TAC[] THEN SIMP[]);;

let WPROOF2AUX_eval_Move1 = prove
 (`!tar v x l (s:(A,C,FFI)wl_state).
     lookup v l = SOME x
     ==> wl_evaluate (wl_Move 0 [tar,v], wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert tar x l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; wl_get_var_def; wl_set_vars_def] THEN
  SIMP[alist_insert_def]);;

let WPROOF2AUX_eval_Get = prove
 (`!tar n x l (s:(A,C,FFI)wl_state).
     wl_get_store n s = SOME x
     ==> wl_evaluate (wl_Get tar n, wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert tar x l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wl_get_store_def]) THEN
  REWRITE_TAC[wl_get_store_def; wl_set_var_def] THEN SIMP[]);;

let WPROOF2AUX_eval_Load = prove
 (`!tar a w v x l (s:(A,C,FFI)wl_state).
     lookup a l = SOME (wl_Word v) /\ wl_mem_load (word_add v w) s = SOME x
     ==> wl_evaluate (wl_Inst (Mem asm_Load tar (Addr a w)),
                      wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert tar x l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_exp_def; MAP; the_words_def; wl_get_var_def] THEN SIMP[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_op_def; ITLIST; WORD_ADD_0] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wl_mem_load_def]) THEN
  REWRITE_TAC[wl_mem_load_def; wl_set_var_def] THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[]);;

let WPROOF2AUX_eval_Binop_Imm = prove
 (`!op r1 r2 w v1 v l (s:(A,C,FFI)wl_state).
     lookup r2 l = SOME (wl_Word v1) /\ word_op op [v1; w] = SOME v
     ==> wl_evaluate (wl_Inst (asm_Arith (Binop op r1 r2 (Imm w))),
                      wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert r1 (wl_Word v) l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; MAP; the_words_def; wl_get_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[wl_set_var_def] THEN SIMP[]);;

let WPROOF2AUX_eval_Binop_Reg = prove
 (`!op r1 r2 r3 v1 v2 v l (s:(A,C,FFI)wl_state).
     lookup r2 l = SOME (wl_Word v1) /\ lookup r3 l = SOME (wl_Word v2) /\
     word_op op [v1; v2] = SOME v
     ==> wl_evaluate (wl_Inst (asm_Arith (Binop op r1 r2 (Reg r3))),
                      wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert r1 (wl_Word v) l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; MAP; the_words_def; wl_get_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[wl_set_var_def] THEN SIMP[]);;

let WPROOF2AUX_eval_Shift_Imm = prove
 (`!sh r1 r2 w v1 v l (s:(A,C,FFI)wl_state).
     lookup r2 l = SOME (wl_Word v1) /\ word_sh sh v1 (val w) = SOME v
     ==> wl_evaluate (wl_Inst (asm_Arith (asm_Shift sh r1 r2 (Imm w))),
                      wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert r1 (wl_Word v) l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; MAP; the_words_def; wl_get_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[wl_set_var_def] THEN SIMP[]);;

let WPROOF2AUX_eval_Shift_Reg = prove
 (`!sh r1 r2 r3 v1 v2 v l (s:(A,C,FFI)wl_state).
     lookup r2 l = SOME (wl_Word v1) /\ lookup r3 l = SOME (wl_Word v2) /\
     word_sh sh v1 (val v2) = SOME v
     ==> wl_evaluate (wl_Inst (asm_Arith (asm_Shift sh r1 r2 (Reg r3))),
                      wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert r1 (wl_Word v) l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; MAP; the_words_def; wl_get_var_def] THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[wl_set_var_def] THEN SIMP[]);;

let WPROOF2AUX_eval_OpCurrHeap = prove
 (`!op dst src v1 v2 v l (s:(A,C,FFI)wl_state).
     lookup src l = SOME (wl_Word v1) /\ wl_get_store CurrHeap s = SOME (wl_Word v2) /\
     word_op op [v1; v2] = SOME v
     ==> wl_evaluate (wl_OpCurrHeap op dst src, wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K (insert dst (wl_Word v) l)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_word_exp_def; MAP; the_words_def; wl_get_var_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `CurrHeap`)) (concl th))) THEN
  REWRITE_TAC[wl_get_store_def] THEN SIMP[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  REWRITE_TAC[wl_set_var_def] THEN SIMP[]);;

(* the statement of inst_select_exp_thm for one expression e (with the      *)
(* quantifiers that the induction needs inside), and its cases                *)

let WPROOF2AUX_ISE = `\e:(A)wl_exp.
  !(c:(A)asm_config) tar temp (s:(A,C,FFI)wl_state) w loc.
    binary_branch_exp e /\ every_var_exp (\x. x < temp) e /\
    locals_rel temp (wl_state_locals s) loc /\ wl_word_exp s e = SOME w
    ==> ?loc'. wl_evaluate (inst_select_exp c tar temp e, wl_state_locals_fupd (K loc) s) =
               (NONE:((A)wl_result)option, wl_state_locals_fupd (K loc') s) /\
               !x. if x = tar then lookup x loc' = SOME w
                   else if x < temp then lookup x loc' = lookup x (wl_state_locals s)
                   else T`;;

let WPROOF2AUX_ise tm = rhs(concl(BETA_CONV(mk_comb(WPROOF2AUX_ISE, tm))));;

let WPROOF2AUX_ise_Const = prove
 (WPROOF2AUX_ise `wl_Const (v:A word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_exp_def; wl_word_exp_def] THEN
  STRIP_TAC THEN EXISTS_TAC `insert tar (wl_Word (v:A word)) loc` THEN
  REWRITE_TAC[WPROOF2AUX_eval_Const; lookup_insert] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[locals_rel_def]);;

let WPROOF2AUX_ise_Var = prove
 (WPROOF2AUX_ise `wl_Var n:(A)wl_exp`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[inst_select_exp_def; wl_word_exp_def; every_var_exp_def; wl_get_var_def] THEN
  STRIP_TAC THEN EXISTS_TAC `insert tar (w:(A)word_loc) loc` THEN
  SUBGOAL_THEN `lookup n loc = SOME (w:(A)word_loc)` ASSUME_TAC THENL
   [ASM_MESON_TAC[locals_rel_def]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Move1 th]) THEN
  REWRITE_TAC[lookup_insert] THEN
  GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[locals_rel_def]);;

let WPROOF2AUX_ise_Lookup = prove
 (WPROOF2AUX_ise `Lookup n:(A)wl_exp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_exp_def; wl_word_exp_def] THEN
  STRIP_TAC THEN EXISTS_TAC `insert tar (w:(A)word_loc) loc` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Get th]) THEN
  REWRITE_TAC[lookup_insert] THEN
  GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[locals_rel_def]);;

let WPROOF2AUX_lookup_insert_fin = prove
 (`!(l:((A)word_loc)spt) sl tar (w:(A)word_loc) temp.
     (!x. x < temp ==> lookup x l = lookup x sl)
     ==> !x. if x = tar then lookup x (insert tar w l) = SOME w
             else if x < temp then lookup x (insert tar w l) = lookup x sl
             else T`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
  ASM_CASES_TAC `x:num = tar` THEN ASM_SIMP_TAC[COND_ID]);;

let WPROOF2AUX_word_exp_add_const = prove
 (`!(s:(A,C,FFI)wl_state) e1 w1 a.
     wl_word_exp s (wl_Op asm_Add [e1; wl_Const w1]) = SOME (wl_Word a) <=>
     ?b. wl_word_exp s e1 = SOME (wl_Word b) /\ a = word_add b w1`,
  REPEAT GEN_TAC THEN SIMP[wl_word_exp_def; MAP; the_words_def] THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) e1` THEN SIMP[] THEN
  CASES_ON `a':(A)word_loc` THEN SIMP[word_op_def; ITLIST; WORD_ADD_0] THEN
  MESON_TAC[]);;

let WPROOF2AUX_ise_post = prove
 (`!(l:((A)word_loc)spt) t v temp sl.
     (!x. if x = t then lookup x l = SOME v
          else if x < temp then lookup x l = lookup x sl else T) <=>
     lookup t l = SOME v /\ (!x. x < temp /\ ~(x = t) ==> lookup x l = lookup x sl)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN REWRITE_TAC[];
      X_GEN_TAC `x:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x:num = t` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

let WPROOF2AUX_word_exp_Load = el 3 (CONJUNCTS wl_word_exp_def);;

(* split the facts of a hypothesis that is a conjunction of case equations *)

let WPROOF2AUX_CASE_HYPS_TAC : tactic =
  DISCH_THEN(fun th -> MAP_EVERY (STRIP_ASSUME_TAC o CAKE_SIMP_RULE WPROOF2AUX_ceqs)
                                 (CONJUNCTS th)) THEN
  RVEQ_TAC;;

let WPROOF2AUX_ise_Load = prove
 (let e = `e:(A)wl_exp` and e' = `e':(A)wl_exp` and w' = `w':A word` in
  mk_imp(mk_conj(WPROOF2AUX_ise e,
                 list_mk_forall([e'; w'],
                   mk_imp(`e = wl_Op asm_Add [e':(A)wl_exp; wl_Const w']`,
                          WPROOF2AUX_ise e'))),
         WPROOF2AUX_ise `wl_Load e:(A)wl_exp`),
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[binary_branch_exp_def; every_var_exp_def; WPROOF2AUX_word_exp_Load] THEN
  WPROOF2AUX_CASE_HYPS_TAC THEN
  ASM_CASES_TAC `?e' w'. e = wl_Op asm_Add [e':(A)wl_exp; wl_Const w'] /\
                         asm_offset_ok 0 (asm_config_addr_offset (c:(A)asm_config)) w'`
  THENL
   [(* Load (Op Add [e1; Const w1]) with a valid offset *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `e1:(A)wl_exp` (X_CHOOSE_THEN `w1:A word`
                    STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e1:(A)wl_exp`; `w1:A word`]) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[binary_branch_exp_def; every_var_exp_def; ALL;
                                WPROOF2AUX_word_exp_add_const]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:A word` STRIP_ASSUME_TAC o
                  check (is_exists o concl)) THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A)asm_config`; `temp:num`; `temp:num`;
                               `s:(A,C,FFI)wl_state`; `wl_Word (b:A word)`;
                               `loc:((A)word_loc)spt`]) THEN
    ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `insert tar (w:(A)word_loc) l1` THEN
    REWRITE_TAC[inst_select_exp_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    RVEQ_TAC THEN
    SUBGOAL_THEN `wl_evaluate (wl_Inst (Mem asm_Load tar (Addr temp w1)),
                    wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                  (NONE, wl_state_locals_fupd (K (insert tar w l1)) s)` SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_Load THEN EXISTS_TAC `b:A word` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[LT_REFL];
    (* the other loads: the address is computed into temp *)
    SUBGOAL_THEN `inst_select_exp (c:(A)asm_config) tar temp (wl_Load e) =
                  wl_Seq (inst_select_exp c temp temp e)
                         (wl_Inst (Mem asm_Load tar (Addr temp (word 0))))` SUBST1_TAC THENL
     [REWRITE_TAC[inst_select_exp_def] THEN REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (is_neg o concl)) THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall (concl th) &&
      fst(dest_var(fst(dest_forall(concl th)))) = "e'")) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A)asm_config`; `temp:num`; `temp:num`;
                                  `s:(A,C,FFI)wl_state`; `wl_Word (a':A word)`;
                                  `loc:((A)word_loc)spt`]) THEN
    ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `insert tar (w:(A)word_loc) l1` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    SUBGOAL_THEN `wl_evaluate (wl_Inst (Mem asm_Load tar (Addr temp (word 0))),
                    wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                  (NONE, wl_state_locals_fupd (K (insert tar w l1)) s)` SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_Load THEN EXISTS_TAC `a':A word` THEN
      ASM_REWRITE_TAC[WORD_ADD_0];
      ALL_TAC] THEN
    REWRITE_TAC[WPROOF2AUX_ise_post; lookup_insert] THEN ASM_MESON_TAC[LT_REFL]]);;

let WPROOF2AUX_word_exp_op2 = prove
 (`!(s:(A,C,FFI)wl_state) op e1 e2 w.
     wl_word_exp s (wl_Op op [e1; e2]) = SOME w <=>
     ?a b v. wl_word_exp s e1 = SOME (wl_Word a) /\ wl_word_exp s e2 = SOME (wl_Word b) /\
             word_op op [a; b] = SOME v /\ w = wl_Word v`,
  REPEAT GEN_TAC THEN SIMP[wl_word_exp_def; MAP; the_words_def] THEN
  SIMP WPROOF2AUX_ceqs THEN MESON_TAC[]);;

let WPROOF2AUX_word_op_comm = prove
 (`!op (a:A word) b. ~(op = asm_Sub) ==> word_op op [a; b] = word_op op [b; a]`,
  GEN_TAC THEN CASES_ON `op:binop` THEN
  SIMP[word_op_def; ITLIST; WORD_ADD_0; WORD_AND_NOT0; WORD_OR_0; WORD_XOR_0] THEN
  REWRITE_TAC[WORD_ADD_SYM; WORD_AND_SYM; WORD_OR_SYM; WORD_XOR_SYM]);;

let WPROOF2AUX_is_Lookup_CurrHeap = prove
 (`!e:(A)wl_exp. is_Lookup_CurrHeap e <=> e = Lookup CurrHeap`,
  GEN_TAC THEN REWRITE_TAC[is_Lookup_CurrHeap_pmatch] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]));;

let WPROOF2AUX_is_app_of name th =
  try fst(dest_const(fst(strip_comb(lhs(concl th))))) = name with Failure _ -> false;;

(* the induction hypothesis for the subexpression e at (tar,temp) = (t,t) *)

let WPROOF2AUX_ISE_IH_TAC (e:term) (t:term) (s:term) (w:term) (l:term) (l1:term) : tactic =
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A)asm_config`; t; t; s; w; l] o
                check (fun th -> is_forall (concl th) &&
                  can (find_term ((=) e)) (concl th))) THEN
  ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
  DISCH_THEN(X_CHOOSE_THEN l1 STRIP_ASSUME_TAC);;

(* e2 is not a constant: evaluate e2 into temp + 1 *)

let WPROOF2AUX_ise_Op_gen = prove
 (mk_imp(mk_conj(WPROOF2AUX_ise `e2:(A)wl_exp`,
   `binary_branch_exp (e2:(A)wl_exp) /\ every_var_exp (\x. x < temp) e2 /\
    wl_word_exp (s:(A,C,FFI)wl_state) e2 = SOME (wl_Word b) /\
    wl_evaluate (inst_select_exp (c:(A)asm_config) temp temp e1,
                 wl_state_locals_fupd (K loc) s) =
      (NONE, wl_state_locals_fupd (K l1) s) /\
    lookup temp l1 = SOME (wl_Word a) /\
    (!x. x < temp /\ ~(x = temp) ==> lookup x l1 = lookup x (wl_state_locals s)) /\
    word_op op [a; b] = SOME v`),
  `?loc'. wl_evaluate (wl_Seq (inst_select_exp (c:(A)asm_config) temp temp e1)
                         (wl_Seq (inst_select_exp c (temp + 1) (temp + 1) e2)
                            (wl_Inst (asm_Arith (Binop op tar temp (Reg (temp + 1)))))),
                       wl_state_locals_fupd (K loc) (s:(A,C,FFI)wl_state)) =
          (NONE:((A)wl_result)option, wl_state_locals_fupd (K loc') s) /\
          lookup tar loc' = SOME (wl_Word (v:A word)) /\
          (!x. x < temp /\ ~(x = tar) ==> lookup x loc' = lookup x (wl_state_locals s))`),
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
  SUBGOAL_THEN `locals_rel temp (wl_state_locals (s:(A,C,FFI)wl_state)) l1` ASSUME_TAC THENL
   [REWRITE_TAC[locals_rel_def] THEN ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_word_exp (wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) e2 =
                SOME (wl_Word b)` ASSUME_TAC THENL
   [MATCH_MP_TAC locals_rel_word_exp THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `every_var_exp (\x. x < temp + 1) (e2:(A)wl_exp)` ASSUME_TAC THENL
   [MATCH_MP_TAC every_var_exp_mono THEN EXISTS_TAC `\x. x < temp` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A)asm_config`; `temp + 1`; `temp + 1`;
                                `wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)`;
                                `wl_Word (b:A word)`; `l1:((A)word_loc)spt`] o
                check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN SIMP[] THEN
  REWRITE_TAC[locals_rel_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `insert tar (wl_Word (v:A word)) l2` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
  SUBGOAL_THEN `wl_evaluate (wl_Inst (asm_Arith (Binop op tar temp (Reg (temp + 1)))),
                  wl_state_locals_fupd (K l2) (s:(A,C,FFI)wl_state)) =
                (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v) l2)) s)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC WPROOF2AUX_eval_Binop_Reg THEN
    MAP_EVERY EXISTS_TAC [`a:A word`; `b:A word`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `temp < temp + 1 /\ ~(temp = temp + 1)`];
    ALL_TAC] THEN
  REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[LT_REFL; ARITH_RULE `x < temp ==> x < temp + 1 /\ ~(x = temp + 1)`]);;

let WPROOF2AUX_ise_Op = prove
 (mk_imp(mk_conj(WPROOF2AUX_ise `e1:(A)wl_exp`, WPROOF2AUX_ise `e2:(A)wl_exp`),
         WPROOF2AUX_ise `wl_Op op [e1; e2]:(A)wl_exp`),
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[WPROOF2AUX_word_exp_op2] THEN
  SUBGOAL_THEN `binary_branch_exp (wl_Op op [e1;e2]:(A)wl_exp) <=>
                binary_branch_exp e1 /\ binary_branch_exp e2` SUBST1_TAC THENL
   [CASES_ON `op:binop` THEN REWRITE_TAC[binary_branch_exp_def; ALL; LENGTH; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[every_var_exp_def; ALL] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[inst_select_exp_def; LET_DEF; LET_END_DEF; WPROOF2AUX_ise_post] THEN
  ASM_CASES_TAC `is_Lookup_CurrHeap (e2:(A)wl_exp)` THEN ASM_REWRITE_TAC[] THENL
   [(* e2 is the current heap *)
    WPROOF2AUX_ISE_IH_TAC `e1:(A)wl_exp` `temp:num` `s:(A,C,FFI)wl_state`
      `wl_Word (a:A word)` `loc:((A)word_loc)spt` `l1:((A)word_loc)spt` THEN
    EXISTS_TAC `insert tar (wl_Word (v:A word)) l1` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WPROOF2AUX_is_Lookup_CurrHeap]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[el 2 (CONJUNCTS wl_word_exp_def)]) THEN
    SUBGOAL_THEN `wl_evaluate (wl_OpCurrHeap op tar temp,
                    wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                  (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v) l1)) s)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_OpCurrHeap THEN
      MAP_EVERY EXISTS_TAC [`a:A word`; `b:A word`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `is_Lookup_CurrHeap (e1:(A)wl_exp) /\ ~(op = asm_Sub)` THEN
  ASM_REWRITE_TAC[] THENL
   [(* e1 is the current heap (and the operation commutes) *)
    WPROOF2AUX_ISE_IH_TAC `e2:(A)wl_exp` `temp:num` `s:(A,C,FFI)wl_state`
      `wl_Word (b:A word)` `loc:((A)word_loc)spt` `l1:((A)word_loc)spt` THEN
    EXISTS_TAC `insert tar (wl_Word (v:A word)) l1` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WPROOF2AUX_is_Lookup_CurrHeap]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[el 2 (CONJUNCTS wl_word_exp_def)]) THEN
    SUBGOAL_THEN `wl_evaluate (wl_OpCurrHeap op tar temp,
                    wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                  (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v) l1)) s)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_OpCurrHeap THEN
      MAP_EVERY EXISTS_TAC [`b:A word`; `a:A word`] THEN
      ASM_SIMP_TAC[GSYM WPROOF2AUX_word_op_comm];
      ALL_TAC] THEN
    REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  WPROOF2AUX_ISE_IH_TAC `e1:(A)wl_exp` `temp:num` `s:(A,C,FFI)wl_state`
    `wl_Word (a:A word)` `loc:((A)word_loc)spt` `l1:((A)word_loc)spt` THEN
  CASES_ON `e2:(A)wl_exp` THEN CASE_REWRITE_TAC[] THENL
   [(* e2 is a constant b *)
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[el 0 (CONJUNCTS wl_word_exp_def)]) THEN RVEQ_TAC THEN
    COND_CASES_TAC THENL
     [EXISTS_TAC `insert tar (wl_Word (v:A word)) l1` THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
      SUBGOAL_THEN `wl_evaluate (wl_Inst (asm_Arith (Binop op tar temp (Imm b))),
                      wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                    (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v) l1)) s)`
        SUBST1_TAC THENL
       [MATCH_MP_TAC WPROOF2AUX_eval_Binop_Imm THEN EXISTS_TAC `a:A word` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[LT_REFL];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [EXISTS_TAC `insert tar (wl_Word (v:A word)) l1` THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
      SUBGOAL_THEN `wl_evaluate (wl_Inst (asm_Arith (Binop asm_Sub tar temp
                                               (Imm (word_neg b)))),
                      wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                    (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v) l1)) s)`
        SUBST1_TAC THENL
       [MATCH_MP_TAC WPROOF2AUX_eval_Binop_Imm THEN EXISTS_TAC `a:A word` THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "word_op")) THEN
        SIMP[word_op_def; ITLIST; WORD_ADD_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[LT_REFL];
      ALL_TAC] THEN
    EXISTS_TAC `insert tar (wl_Word (v:A word)) (insert (temp + 1) (wl_Word b) l1)` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    SUBGOAL_THEN `wl_evaluate (wl_Seq (wl_Inst (asm_Const (temp + 1) b))
                     (wl_Inst (asm_Arith (Binop op tar temp (Reg (temp + 1))))),
                    wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                  (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v)
                            (insert (temp + 1) (wl_Word b) l1))) s)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `wl_evaluate (wl_Inst (asm_Arith (Binop op tar temp (Reg (temp + 1)))),
                    wl_state_locals_fupd (K (insert (temp + 1) (wl_Word b) l1))
                      (s:(A,C,FFI)wl_state))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC WPROOF2AUX_eval_Seq_locals THEN REWRITE_TAC[WPROOF2AUX_eval_Const];
        MATCH_MP_TAC WPROOF2AUX_eval_Binop_Reg THEN
        MAP_EVERY EXISTS_TAC [`a:A word`; `b:A word`] THEN
        ASM_REWRITE_TAC[lookup_insert; ARITH_RULE `~(temp = temp + 1)`]];
      ALL_TAC] THEN
    REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[LT_REFL; ARITH_RULE `x < temp ==> ~(x = temp + 1)`];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC WPROOF2AUX_ise_Op_gen THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_word_exp_shift = prove
 (`!(s:(A,C,FFI)wl_state) sh e1 e2 w.
     wl_word_exp s (wl_Shift sh e1 e2) = SOME w <=>
     ?a b v. wl_word_exp s e1 = SOME (wl_Word a) /\ wl_word_exp s e2 = SOME (wl_Word b) /\
             word_sh sh a (val b) = SOME v /\ w = wl_Word v`,
  REPEAT GEN_TAC THEN SIMP[wl_word_exp_def] THEN
  SIMP WPROOF2AUX_ceqs THEN MESON_TAC[]);;

let WPROOF2AUX_word_sh_0 = prove
 (`!sh (w:A word). word_sh sh w 0 = SOME w`,
  GEN_TAC THEN CASES_ON `sh:shift` THEN
  SIMP[word_sh_def; WORD_SHL_ZERO; WORD_USHR_ZERO; WORD_ISHR_ZERO; WORD_ROR_ZERO]);;

(* the shift amount is not a constant: evaluate it into temp + 1 *)

let WPROOF2AUX_ise_Shift_gen = prove
 (mk_imp(mk_conj(WPROOF2AUX_ise `e2:(A)wl_exp`,
   `binary_branch_exp (e2:(A)wl_exp) /\ every_var_exp (\x. x < temp) e2 /\
    wl_word_exp (s:(A,C,FFI)wl_state) e2 = SOME (wl_Word b) /\
    wl_evaluate (inst_select_exp (c:(A)asm_config) temp temp e1,
                 wl_state_locals_fupd (K loc) s) =
      (NONE, wl_state_locals_fupd (K l1) s) /\
    lookup temp l1 = SOME (wl_Word a) /\
    (!x. x < temp /\ ~(x = temp) ==> lookup x l1 = lookup x (wl_state_locals s)) /\
    word_sh sh a (val b) = SOME v`),
  `?loc'. wl_evaluate (wl_Seq (inst_select_exp (c:(A)asm_config) temp temp e1)
                         (wl_Seq (inst_select_exp c (temp + 1) (temp + 1) e2)
                            (wl_Inst (asm_Arith (asm_Shift sh tar temp (Reg (temp + 1)))))),
                       wl_state_locals_fupd (K loc) (s:(A,C,FFI)wl_state)) =
          (NONE:((A)wl_result)option, wl_state_locals_fupd (K loc') s) /\
          lookup tar loc' = SOME (wl_Word (v:A word)) /\
          (!x. x < temp /\ ~(x = tar) ==> lookup x loc' = lookup x (wl_state_locals s))`),
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
  SUBGOAL_THEN `locals_rel temp (wl_state_locals (s:(A,C,FFI)wl_state)) l1` ASSUME_TAC THENL
   [REWRITE_TAC[locals_rel_def] THEN ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_word_exp (wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) e2 =
                SOME (wl_Word b)` ASSUME_TAC THENL
   [MATCH_MP_TAC locals_rel_word_exp THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `every_var_exp (\x. x < temp + 1) (e2:(A)wl_exp)` ASSUME_TAC THENL
   [MATCH_MP_TAC every_var_exp_mono THEN EXISTS_TAC `\x. x < temp` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A)asm_config`; `temp + 1`; `temp + 1`;
                                `wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)`;
                                `wl_Word (b:A word)`; `l1:((A)word_loc)spt`] o
                check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN SIMP[] THEN
  REWRITE_TAC[locals_rel_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `insert tar (wl_Word (v:A word)) l2` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
  SUBGOAL_THEN `wl_evaluate (wl_Inst (asm_Arith (asm_Shift sh tar temp (Reg (temp + 1)))),
                  wl_state_locals_fupd (K l2) (s:(A,C,FFI)wl_state)) =
                (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v) l2)) s)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC WPROOF2AUX_eval_Shift_Reg THEN
    MAP_EVERY EXISTS_TAC [`a:A word`; `b:A word`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `temp < temp + 1 /\ ~(temp = temp + 1)`];
    ALL_TAC] THEN
  REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[LT_REFL; ARITH_RULE `x < temp ==> x < temp + 1 /\ ~(x = temp + 1)`]);;

let WPROOF2AUX_ise_Shift = prove
 (mk_imp(mk_conj(WPROOF2AUX_ise `e1:(A)wl_exp`, WPROOF2AUX_ise `e2:(A)wl_exp`),
         WPROOF2AUX_ise `wl_Shift sh e1 e2:(A)wl_exp`),
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[WPROOF2AUX_word_exp_shift] THEN
  REWRITE_TAC[binary_branch_exp_def; every_var_exp_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[inst_select_exp_def; LET_DEF; LET_END_DEF; WPROOF2AUX_ise_post] THEN
  WPROOF2AUX_ISE_IH_TAC `e1:(A)wl_exp` `temp:num` `s:(A,C,FFI)wl_state`
    `wl_Word (a:A word)` `loc:((A)word_loc)spt` `l1:((A)word_loc)spt` THEN
  CASES_ON `e2:(A)wl_exp` THEN CASE_REWRITE_TAC[] THENL
   [(* a constant shift amount b *)
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[el 0 (CONJUNCTS wl_word_exp_def)]) THEN RVEQ_TAC THEN
    COND_CASES_TAC THENL
     [COND_CASES_TAC THENL
       [EXISTS_TAC `insert tar (wl_Word (v:A word)) l1` THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
        FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "word_sh")) THEN
        ASM_REWRITE_TAC[WPROOF2AUX_word_sh_0; option_INJ] THEN
        DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Move1 th]) THEN
        REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[LT_REFL];
        EXISTS_TAC `insert tar (wl_Word (v:A word)) l1` THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
        SUBGOAL_THEN `wl_evaluate (wl_Inst (asm_Arith (asm_Shift sh tar temp
                                     (Imm (word (val (b:A word)))))),
                        wl_state_locals_fupd (K l1) (s:(A,C,FFI)wl_state)) =
                      (NONE, wl_state_locals_fupd (K (insert tar (wl_Word v) l1)) s)`
          SUBST1_TAC THENL
         [MATCH_MP_TAC WPROOF2AUX_eval_Shift_Imm THEN EXISTS_TAC `a:A word` THEN
          ASM_REWRITE_TAC[WORD_VAL];
          ALL_TAC] THEN
        REWRITE_TAC[lookup_insert] THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[LT_REFL]];
      FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "word_sh")) THEN
      REWRITE_TAC[word_sh_def] THEN
      MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN
      REWRITE_TAC[GE] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `~(val (b:A word) = 0) /\ dimindex(:A) <= val b` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
      ASM_REWRITE_TAC[option_DISTINCT]];
    MATCH_MP_TAC WPROOF2AUX_ise_Shift_gen THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WPROOF2AUX_ise_Shift_gen THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WPROOF2AUX_ise_Shift_gen THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WPROOF2AUX_ise_Shift_gen THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WPROOF2AUX_ise_Shift_gen THEN ASM_REWRITE_TAC[]]);;

let WPROOF2AUX_the_words_length = prove
 (`!ls (ws:(A word)list). the_words ls = SOME ws ==> LENGTH ws = LENGTH ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[the_words_def] THEN
  SIMP[LENGTH] THEN GEN_TAC THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

let WPROOF2AUX_word_op_Sub_length = prove
 (`!ws (x:A word). word_op asm_Sub ws = SOME x ==> LENGTH ws = 2`,
  GEN_TAC THEN REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (TOP_CASE_TAC THEN SIMP[option_DISTINCT; LENGTH]) THEN ARITH_TAC);;

let WPROOF2AUX_ise_Op_other = prove
 (mk_imp(`~(LENGTH (l:((A)wl_exp)list) = 2)`, WPROOF2AUX_ise `wl_Op op l:(A)wl_exp`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `op = asm_Sub` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_word_exp")) THEN
    REWRITE_TAC[wl_word_exp_def] THEN
    CASES_ON `the_words (MAP (wl_word_exp (s:(A,C,FFI)wl_state)) (l:((A)wl_exp)list))` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_the_words_length) THEN
    REWRITE_TAC[LENGTH_MAP] THEN
    CASES_ON `word_op asm_Sub (a:(A word)list)` THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_word_op_Sub_length) THEN
    MP_TAC(ASSUME `~(LENGTH (l:((A)wl_exp)list) = 2)`) THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(rator(concl th))) = "binary_branch_exp" with Failure _ -> false)) THEN
    CASES_ON `op:binop` THEN FS[binary_branch_exp_def]]);;

let WPROOF2AUX_exp_size = type_size_def "wl_exp";;

let WPROOF2AUX_ise_all = prove
 (mk_forall(`exp:(A)wl_exp`, WPROOF2AUX_ise `exp:(A)wl_exp`),
  MP_TAC(ISPEC `wl_exp_size (\x:A. 0)` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `exp:(A)wl_exp` THEN DISCH_TAC THEN
  CASES_ON `exp:(A)wl_exp` THENL
   [MATCH_ACCEPT_TAC WPROOF2AUX_ise_Const;
    MATCH_ACCEPT_TAC WPROOF2AUX_ise_Var;
    MATCH_ACCEPT_TAC WPROOF2AUX_ise_Lookup;
    MATCH_MP_TAC WPROOF2AUX_ise_Load THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[WPROOF2AUX_exp_size] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[WPROOF2AUX_exp_size] THEN ARITH_TAC];
    ASM_CASES_TAC `LENGTH (a1:((A)wl_exp)list) = 2` THENL
     [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[LENGTH_EQ_CONS; LENGTH_EQ_NIL;
                      ARITH_RULE `2 = SUC 1 /\ 1 = SUC 0`] o
                    check (fun th -> concl th = `LENGTH (a1:((A)wl_exp)list) = 2`)) THEN
      RVEQ_TAC THEN
      MATCH_MP_TAC WPROOF2AUX_ise_Op THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[WPROOF2AUX_exp_size] THEN ARITH_TAC;
      MATCH_MP_TAC WPROOF2AUX_ise_Op_other THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC WPROOF2AUX_ise_Shift THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[WPROOF2AUX_exp_size] THEN ARITH_TAC]);;

let inst_select_exp_thm = prove
 (`!c tar temp exp (s:(A,C,FFI)wl_state) w loc.
     binary_branch_exp exp /\
     every_var_exp (\x. x < temp) exp /\
     locals_rel temp (wl_state_locals s) loc /\
     wl_word_exp s exp = SOME w
     ==> ?loc'.
           wl_evaluate (inst_select_exp c tar temp exp, wl_state_locals_fupd (K loc) s) =
           (NONE:((A)wl_result)option, wl_state_locals_fupd (K loc') s) /\
           !x. if x = tar then lookup x loc' = SOME w
               else if x < temp then lookup x loc' = lookup x (wl_state_locals s)
               else T`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`exp:(A)wl_exp`; `c:(A)asm_config`; `tar:num`; `temp:num`;
                `s:(A,C,FFI)wl_state`; `w:(A)word_loc`; `loc:((A)word_loc)spt`]
               WPROOF2AUX_ise_all) THEN
  REWRITE_TAC[]);;

let locals_rm = prove
 (`!D:(A,C,FFI)wl_state. wl_state_locals_fupd (K (wl_state_locals D)) D = D`,
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

(* the statement of inst_select_thm for one program, and its cases *)

let WPROOF2AUX_IS = CASE_TERM
 `\c temp prog. !(st:(A,C,FFI)wl_state) res rst loc.
     wl_evaluate (prog,st) = (res,rst) /\ wl_every_var (\x. x < temp) prog /\
     ~(res = SOME wl_Error) /\ locals_rel temp (wl_state_locals st) loc
     ==> ?loc'. wl_evaluate (inst_select (c:(A)asm_config) temp prog,
                             wl_state_locals_fupd (K loc) st) =
                (res, wl_state_locals_fupd (K loc') rst) /\
                (match res with
                   NONE -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Break _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Continue _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME _ -> wl_state_locals rst = loc')`;;

let WPROOF2AUX_is c t p =
  rhs(concl(DEPTH_CONV BETA_CONV (list_mk_comb(WPROOF2AUX_IS, [c; t; p]))));;

let WPROOF2AUX_flat_facts = prove
 (`!exp (st:(A,C,FFI)wl_state) w temp.
     wl_word_exp st exp = SOME w /\ every_var_exp (\x. x < temp) exp
     ==> wl_word_exp st (flatten_exp (pull_exp exp)) = SOME w /\
         binary_branch_exp (flatten_exp (pull_exp exp)) /\
         every_var_exp (\x. x < temp) (flatten_exp (pull_exp exp))`,
  MESON_TAC[pull_exp_ok; flatten_exp_ok; flatten_exp_binary_branch_exp;
            pull_exp_every_var_exp; flatten_exp_every_var_exp]);;

let WPROOF2AUX_ERR_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC);;

let WPROOF2AUX_EVAL_HYP_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wl_evaluate_def] o
                check (WPROOF2AUX_is_app_of "wl_evaluate"));;

let WPROOF2AUX_EVAL_SPLIT_TAC : tactic =
  WPROOF2AUX_EVAL_HYP_TAC THEN REWRITE_TAC(PAIR_EQ :: WPROOF2AUX_ceqs) THEN
  STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC;;

(* the program of the goal ?loc'. wl_evaluate (p,s) = .. /\ .. equals dflt *)

let WPROOF2AUX_PROG_EQ_TAC (dflt:term) : tactic = fun (asl,w as g) ->
  let _,bod = dest_exists w in
  let c1 = fst(dest_conj bod) in
  let x = fst(dest_pair(rand(lhs c1))) in
  (SUBGOAL_THEN (mk_eq(x,dflt)) SUBST1_TAC THENL
    [REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[]) THEN ASM_MESON_TAC[]; ALL_TAC]) g;;

let WPROOF2AUX_is_Assign = prove
 (WPROOF2AUX_is `c:(A)asm_config` `temp:num` `wl_Assign v exp:(A)wl_prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; o_THM; wl_every_var_def] THEN
  REWRITE_TAC[wl_evaluate_def] THEN
  CASES_ON `wl_word_exp (st:(A,C,FFI)wl_state) exp` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC THEN
  MP_TAC(SPECL [`exp:(A)wl_exp`; `st:(A,C,FFI)wl_state`; `a:(A)word_loc`; `temp:num`]
               WPROOF2AUX_flat_facts) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(A)asm_config`; `v:num`; `temp:num`;
                `flatten_exp (pull_exp exp):(A)wl_exp`;
                `st:(A,C,FFI)wl_state`; `a:(A)word_loc`; `loc:((A)word_loc)spt`]
               inst_select_exp_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l1:((A)word_loc)spt` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_set_var_def] THEN SIMP[] THEN
  REWRITE_TAC[locals_rel_def; lookup_insert] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
  ASM_CASES_TAC `x:num = v` THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let WPROOF2AUX_is_Set = prove
 (WPROOF2AUX_is `c:(A)asm_config` `temp:num` `wl_Set store exp:(A)wl_prog`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[inst_select_def; o_THM; wl_every_var_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN WPROOF2AUX_EVAL_HYP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
  CASES_ON `wl_word_exp (st:(A,C,FFI)wl_state) exp` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC THEN
  MP_TAC(SPECL [`exp:(A)wl_exp`; `st:(A,C,FFI)wl_state`; `a:(A)word_loc`; `temp:num`]
               WPROOF2AUX_flat_facts) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(A)asm_config`; `temp:num`; `temp:num`;
                `flatten_exp (pull_exp exp):(A)wl_exp`;
                `st:(A,C,FFI)wl_state`; `a:(A)word_loc`; `loc:((A)word_loc)spt`]
               inst_select_exp_thm) THEN
  ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l1:((A)word_loc)spt` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
  REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_exp_def; wl_get_var_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_set_store_def] THEN SIMP[] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[] THEN
  REWRITE_TAC[locals_rel_def] THEN ASM_MESON_TAC[LT_REFL]);;

let WPROOF2AUX_mem_store_locals = prove
 (`!a w l (s:(A,C,FFI)wl_state).
     wl_mem_store a w (wl_state_locals_fupd (K l) s) =
     OPTION_MAP (wl_state_locals_fupd (K l)) (wl_mem_store a w s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_mem_store_def] THEN SIMP[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN SIMP[] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let WPROOF2AUX_mem_store_locals_eq = prove
 (`!a w (s:(A,C,FFI)wl_state) s1.
     wl_mem_store a w s = SOME s1 ==> wl_state_locals s1 = wl_state_locals s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_mem_store_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let WPROOF2AUX_eval_Store = prove
 (`!var a off x w s1 l (s:(A,C,FFI)wl_state).
     lookup a l = SOME (wl_Word x) /\ lookup var l = SOME w /\
     wl_mem_store (word_add x off) w s = SOME s1
     ==> wl_evaluate (wl_Inst (Mem asm_Store var (Addr a off)),
                      wl_state_locals_fupd (K l) s) =
         (NONE, wl_state_locals_fupd (K l) s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_exp_def; MAP; the_words_def; wl_get_var_def] THEN SIMP[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_op_def; ITLIST; WORD_ADD_0] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  ASM_REWRITE_TAC[WPROOF2AUX_mem_store_locals; OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[]);;

let WPROOF2AUX_is_Store = prove
 (WPROOF2AUX_is `c:(A)asm_config` `temp:num` `wl_Store exp var:(A)wl_prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; o_THM; wl_every_var_def] THEN
  STRIP_TAC THEN WPROOF2AUX_EVAL_SPLIT_TAC THEN
  MP_TAC(SPECL [`exp:(A)wl_exp`; `st:(A,C,FFI)wl_state`; `wl_Word (a':A word)`; `temp:num`]
               WPROOF2AUX_flat_facts) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SPEC_TAC(`flatten_exp (pull_exp exp):(A)wl_exp`,`E:(A)wl_exp`) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WPROOF2AUX_mem_store_locals_eq) THEN
  SUBGOAL_THEN `lookup var (wl_state_locals (st:(A,C,FFI)wl_state)) = SOME a''` ASSUME_TAC THENL
   [ASM_MESON_TAC[wl_get_var_def]; ALL_TAC] THEN
  ASM_CASES_TAC `?e' w'. E = wl_Op asm_Add [e':(A)wl_exp; wl_Const w'] /\
                         asm_offset_ok 0 (asm_config_addr_offset (c:(A)asm_config)) w'`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e1:(A)wl_exp` (X_CHOOSE_THEN `w1:A word`
                    STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[binary_branch_exp_def; every_var_exp_def; ALL;
                                WPROOF2AUX_word_exp_add_const]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:A word` STRIP_ASSUME_TAC o
                  check (is_exists o concl)) THEN
    RVEQ_TAC THEN
    MP_TAC(SPECL [`c:(A)asm_config`; `temp:num`; `temp:num`; `e1:(A)wl_exp`;
                  `st:(A,C,FFI)wl_state`; `wl_Word (b:A word)`; `loc:((A)word_loc)spt`]
                 inst_select_exp_thm) THEN
    ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l1:((A)word_loc)spt` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    SUBGOAL_THEN `wl_evaluate (wl_Inst (Mem asm_Store var (Addr temp w1)),
                    wl_state_locals_fupd (K l1) (st:(A,C,FFI)wl_state)) =
                  (NONE, wl_state_locals_fupd (K l1) rst)` SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_Store THEN
      MAP_EVERY EXISTS_TAC [`b:A word`; `a'':(A)word_loc`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[LT_REFL];
      ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[locals_rel_def] THEN ASM_MESON_TAC[LT_REFL];
    WPROOF2AUX_PROG_EQ_TAC `wl_Seq (inst_select_exp (c:(A)asm_config) temp temp E)
                              (wl_Inst (Mem asm_Store var (Addr temp (word 0))))` THEN
    MP_TAC(SPECL [`c:(A)asm_config`; `temp:num`; `temp:num`; `E:(A)wl_exp`;
                  `st:(A,C,FFI)wl_state`; `wl_Word (a':A word)`; `loc:((A)word_loc)spt`]
                 inst_select_exp_thm) THEN
    ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l1:((A)word_loc)spt` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    SUBGOAL_THEN `wl_evaluate (wl_Inst (Mem asm_Store var (Addr temp (word 0))),
                    wl_state_locals_fupd (K l1) (st:(A,C,FFI)wl_state)) =
                  (NONE, wl_state_locals_fupd (K l1) rst)` SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_Store THEN
      MAP_EVERY EXISTS_TAC [`a':A word`; `a'':(A)word_loc`] THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_MESON_TAC[LT_REFL];
      ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[locals_rel_def] THEN ASM_MESON_TAC[LT_REFL]]);;

let WPROOF2AUX_is_Seq = prove
 (mk_imp(mk_conj(WPROOF2AUX_is `c:(A)asm_config` `temp:num` `p1:(A)wl_prog`,
                 WPROOF2AUX_is `c:(A)asm_config` `temp:num` `p2:(A)wl_prog`),
         WPROOF2AUX_is `c:(A)asm_config` `temp:num` `wl_Seq p1 p2:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; wl_every_var_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  CASES_ON `wl_evaluate (p1:(A)wl_prog, st:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
    SIMP[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`st:(A,C,FFI)wl_state`; `x:((A)wl_result)option`;
                                     `y:(A,C,FFI)wl_state`; `loc:((A)word_loc)spt`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:((A)wl_result)option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`y:(A,C,FFI)wl_state`; `res:((A)wl_result)option`;
                                       `rst:(A,C,FFI)wl_state`; `l1:((A)word_loc)spt`]) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `l1:((A)word_loc)spt` THEN ASM_REWRITE_TAC[]]);;

let WPROOF2AUX_is_MustTerminate = prove
 (mk_imp(WPROOF2AUX_is `c:(A)asm_config` `temp:num` `p1:(A)wl_prog`,
         WPROOF2AUX_is `c:(A)asm_config` `temp:num` `MustTerminate p1:(A)wl_prog`),
  DISCH_THEN(LABEL_TAC "ih1") THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; wl_every_var_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
  PAIRARG_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL
    [`wl_state_clock_fupd (K (MustTerminate_limit (:A)))
        (wl_state_termdep_fupd (K (wl_state_termdep st - 1)) (st:(A,C,FFI)wl_state))`;
     `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`; `loc:((A)word_loc)spt`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l1:((A)word_loc)spt` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN SIMP[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let WPROOF2AUX_lr_rws = prove
 (`!temp (st:(A,C,FFI)wl_state) loc. locals_rel temp (wl_state_locals st) loc
     ==> (!r. r < temp ==> wl_get_var r (wl_state_locals_fupd (K loc) st) = wl_get_var r st) /\
         (!l. ALL (\x. x < temp) l
              ==> wl_get_vars l (wl_state_locals_fupd (K loc) st) = wl_get_vars l st) /\
         (!r. every_var_imm (\x. x < temp) r
              ==> wl_get_var_imm r (wl_state_locals_fupd (K loc) st) = wl_get_var_imm r st) /\
         (!e. every_var_exp (\x. x < temp) e
              ==> wl_word_exp (wl_state_locals_fupd (K loc) st) e = wl_word_exp st e)`,
  MESON_TAC[locals_rel_get_var_simp; locals_rel_get_vars_simp; locals_rel_get_var_imm_simp;
            locals_rel_word_exp_simp]);;

let WPROOF2AUX_LR_SIMP_TAC (thl:thm list) : tactic =
  FIRST_ASSUM(fun lr -> ASM_SIMP_TAC(MATCH_MP WPROOF2AUX_lr_rws lr :: thl));;

let WPROOF2AUX_is_If = prove
 (mk_imp(mk_conj(WPROOF2AUX_is `c:(A)asm_config` `temp:num` `c1:(A)wl_prog`,
                 WPROOF2AUX_is `c:(A)asm_config` `temp:num` `c2:(A)wl_prog`),
         WPROOF2AUX_is `c:(A)asm_config` `temp:num` `wl_If cmp r1 ri c1 c2:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; wl_every_var_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  WPROOF2AUX_LR_SIMP_TAC[] THEN
  CASES_ON `wl_get_var r1 (st:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
  CASES_ON `wl_get_var_imm ri (st:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
  CASES_ON `wl_word_cmp cmp (a:(A)word_loc) a'` THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let WPROOF2AUX_eval_ShareInst = prove
 (`!op v e ad (st:(A,C,FFI)wl_state).
     wl_word_exp st e = SOME (wl_Word ad)
     ==> wl_evaluate (ShareInst op v e, st) = share_inst op v ad st`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let WPROOF2AUX_is_ShareInst = prove
 (WPROOF2AUX_is `c:(A)asm_config` `temp:num` `ShareInst op var exp:(A)wl_prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; o_THM; wl_every_var_def] THEN
  STRIP_TAC THEN WPROOF2AUX_EVAL_SPLIT_TAC THEN
  MP_TAC(SPECL [`exp:(A)wl_exp`; `st:(A,C,FFI)wl_state`; `wl_Word (a':A word)`; `temp:num`]
               WPROOF2AUX_flat_facts) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SPEC_TAC(`flatten_exp (pull_exp exp):(A)wl_exp`,`E:(A)wl_exp`) THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `?e' w'. E = wl_Op asm_Add [e':(A)wl_exp; wl_Const w'] /\
      (((op = asm_Load \/ op = asm_Store) /\
        asm_offset_ok 0 (asm_config_addr_offset (c:(A)asm_config)) w') \/
       ((op = asm_Load32 \/ op = asm_Store32) /\
        asm_offset_ok 0 (asm_config_addr_offset c) w') \/
       ((op = Load16 \/ op = Store16) /\
        asm_offset_ok 0 (asm_config_hw_offset c) w') \/
       ((op = Load8 \/ op = Store8) /\
        asm_offset_ok 0 (asm_config_byte_offset c) w'))`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e1:(A)wl_exp` (X_CHOOSE_THEN `w1:A word`
                    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[binary_branch_exp_def; every_var_exp_def; ALL;
                                WPROOF2AUX_word_exp_add_const]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:A word` STRIP_ASSUME_TAC o
                  check (is_exists o concl)) THEN
    RVEQ_TAC THEN
    MP_TAC(SPECL [`c:(A)asm_config`; `temp:num`; `temp:num`; `e1:(A)wl_exp`;
                  `st:(A,C,FFI)wl_state`; `wl_Word (b:A word)`; `loc:((A)word_loc)spt`]
                 inst_select_exp_thm) THEN
    ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    SUBGOAL_THEN `wl_evaluate (ShareInst op var (wl_Op asm_Add [wl_Var temp; wl_Const w1]),
                    wl_state_locals_fupd (K l1) (st:(A,C,FFI)wl_state)) =
                  share_inst op var (word_add b w1) (wl_state_locals_fupd (K l1) st)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_ShareInst THEN
      REWRITE_TAC[WPROOF2AUX_word_exp_add_const] THEN EXISTS_TAC `b:A word` THEN
      REWRITE_TAC[wl_word_exp_def; wl_get_var_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC IL2AUX_share_inst_lr THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[locals_rel_def] THEN ASM_MESON_TAC[LT_REFL];
    WPROOF2AUX_PROG_EQ_TAC `wl_Seq (inst_select_exp (c:(A)asm_config) temp temp E)
                               (ShareInst op var (wl_Var temp))` THEN
    MP_TAC(SPECL [`c:(A)asm_config`; `temp:num`; `temp:num`; `E:(A)wl_exp`;
                  `st:(A,C,FFI)wl_state`; `wl_Word (a':A word)`; `loc:((A)word_loc)spt`]
                 inst_select_exp_thm) THEN
    ASM_REWRITE_TAC[WPROOF2AUX_ise_post] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_locals th]) THEN
    SUBGOAL_THEN `wl_evaluate (ShareInst op var (wl_Var temp),
                    wl_state_locals_fupd (K l1) (st:(A,C,FFI)wl_state)) =
                  share_inst op var a' (wl_state_locals_fupd (K l1) st)` SUBST1_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_eval_ShareInst THEN
      REWRITE_TAC[wl_word_exp_def; wl_get_var_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC IL2AUX_share_inst_lr THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[locals_rel_def] THEN ASM_MESON_TAC[LT_REFL]]);;

let WPROOF2AUX_locals_fupd_fupd = prove
 (`!(a:((A)word_loc)spt) b (s:(A,C,FFI)wl_state).
     wl_state_locals_fupd (K a) (wl_state_locals_fupd (K b) s) = wl_state_locals_fupd (K a) s`,
  SIMP[]);;

let inst_select_Loop_helper = prove
 (CASE_TERM
  `!(s:(A,C,FFI)wl_state) names prog exit_names res rst (c:(A)asm_config) temp loc.
     (!(st:(A,C,FFI)wl_state) res rst loc.
        wl_evaluate (prog, st) = (res, rst) /\ ~(res = SOME wl_Error) /\
        locals_rel temp (wl_state_locals st) loc
        ==> ?loc'. wl_evaluate (inst_select c temp prog, wl_state_locals_fupd (K loc) st) =
                   (res, wl_state_locals_fupd (K loc') rst) /\
                   (match res with
                      NONE -> locals_rel temp (wl_state_locals rst) loc'
                    | SOME (wordSem_Break _) -> locals_rel temp (wl_state_locals rst) loc'
                    | SOME (wordSem_Continue _) -> locals_rel temp (wl_state_locals rst) loc'
                    | SOME _ -> wl_state_locals rst = loc')) /\
     wl_evaluate (wl_Loop names prog exit_names, s) = (res, rst) /\
     ~(res = SOME wl_Error) /\
     wl_every_var (\x. x < temp) prog /\
     every_name (\x. x < temp) (names, LN) /\
     every_name (\x. x < temp) (exit_names, LN) /\
     locals_rel temp (wl_state_locals s) loc
     ==> ?loc'. wl_evaluate (wl_Loop names (inst_select c temp prog) exit_names,
                             wl_state_locals_fupd (K loc) s) =
                (res, wl_state_locals_fupd (K loc') rst) /\
                (match res with
                   NONE -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Break _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME (wordSem_Continue _) -> locals_rel temp (wl_state_locals rst) loc'
                 | SOME _ -> wl_state_locals rst = loc')`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC(MESON[]
   `(!n (s:(A,C,FFI)wl_state). wl_state_clock s = n ==> P s) ==> !s. P s`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:(A,C,FFI)wl_state` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[wl_cut_state_def; wl_STOP_def] THEN
  SIMP[] THEN
  CASES_ON `wl_cut_env (names,LN) (wl_state_locals (s:(A,C,FFI)wl_state))` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wl_cut_env (names,LN) (loc:((A)word_loc)spt) = SOME a` SUBST1_TAC THENL
   [MATCH_MP_TAC (GEN_ALL locals_rel_cut_env) THEN
    MAP_EVERY EXISTS_TAC [`temp:num`; `wl_state_locals (s:(A,C,FFI)wl_state)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN SIMP[] THEN
  CASES_ON `wl_evaluate (prog:(A)wl_prog, wl_state_locals_fupd (K a) (s:(A,C,FFI)wl_state))` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
    SIMP[PAIR_EQ] THEN REPEAT COND_CASES_TAC THEN SIMP[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`wl_state_locals_fupd (K a) (s:(A,C,FFI)wl_state)`;
                              `x:((A)wl_result)option`; `y:(A,C,FFI)wl_state`;
                              `a:((A)word_loc)spt`] o
              check (fun th -> is_forall (concl th) &&
                       can (find_term ((=) `inst_select (c:(A)asm_config) temp prog`))
                           (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[locals_rel_def]; ALL_TAC] THEN
  SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WPROOF2AUX_locals_fupd_fupd]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [(* the loop continues *)
    SIMP[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      EXISTS_TAC `wl_state_locals (wl_flush_state T (y:(A,C,FFI)wl_state))` THEN
      REWRITE_TAC[locals_rm] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[wl_flush_state_def] THEN SIMP[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_clock (wl_dec_clock (y:(A,C,FFI)wl_state))` o
                  check (fun th -> is_forall (concl th) &&
                           is_imp (snd(dest_forall(concl th))) &&
                           is_binary "<" (fst(dest_imp(snd(dest_forall(concl th))))))) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o
                    check (fun th -> concl th = `wl_evaluate (prog:(A)wl_prog,
                             wl_state_locals_fupd (K a) (s:(A,C,FFI)wl_state)) = x,y`)) THEN
      REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `wl_dec_clock (y:(A,C,FFI)wl_state)`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`names:(1)spt`; `prog:(A)wl_prog`; `exit_names:(1)spt`;
      `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`; `c:(A)asm_config`; `temp:num`;
      `l1:((A)word_loc)spt`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
         (try fst(dest_const(rator(concl th))) = "wl_cont_loop" with Failure _ -> false))) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
         can (find_term ((=) `l1:((A)word_loc)spt`)) (concl th) &&
         not (is_eq (concl th) && WPROOF2AUX_is_app_of "wl_evaluate" th))) THEN
      CASES_ON `x:((A)wl_result)option` THEN CASE_REWRITE_TAC[] THEN
      TRY (CASES_ON `a':(A)wl_result` THEN CASE_REWRITE_TAC[]) THEN
      SIMP[] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l2:((A)word_loc)spt` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `l2:((A)word_loc)spt`)) (concl th) &&
      WPROOF2AUX_is_app_of "wl_evaluate" th)) THEN
    REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[];
    (* the loop exits *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
      SIMP[] THEN
      CASES_ON `wl_cut_env (exit_names,LN) (wl_state_locals (y:(A,C,FFI)wl_state))` THEN
      CASE_REWRITE_TAC[PAIR_EQ] THENL
       [STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `wl_cut_env (exit_names,LN) (l1:((A)word_loc)spt) = SOME a'`
        SUBST1_TAC THENL
       [MATCH_MP_TAC (GEN_ALL locals_rel_cut_env) THEN
        MAP_EVERY EXISTS_TAC [`temp:num`; `wl_state_locals (y:(A,C,FFI)wl_state)`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      EXISTS_TAC `a':((A)word_loc)spt` THEN SIMP[locals_rel_def];
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      EXISTS_TAC `l1:((A)word_loc)spt` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term ((=) `l1:((A)word_loc)spt`)) (concl th) &&
        not (is_eq (concl th)))) THEN
      CASES_ON `x:((A)wl_result)option` THEN CASE_REWRITE_TAC[] THEN
      TRY (CASES_ON `a':(A)wl_result` THEN CASE_REWRITE_TAC[]) THEN
      SIMP[wl_exit_loop_def]]]);;
let WPROOF2AUX_toAList_LN = prove
 (`toAList (LN:A spt) = []`,
  REWRITE_TAC[toAList_def; SPTAUX_foldi_thm]);;

let WPROOF2AUX_is_Loop = prove
 (mk_imp(WPROOF2AUX_is `c:(A)asm_config` `temp:num` `body:(A)wl_prog`,
         WPROOF2AUX_is `c:(A)asm_config` `temp:num` `wl_Loop names body exit_names:(A)wl_prog`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; wl_every_var_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC inst_select_Loop_helper THEN
  ASM_REWRITE_TAC[every_name_def; WPROOF2AUX_toAList_LN; MAP; ALL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: a [local] copy of wordProps' locals_rel_cut_envs *)

let locals_rel_cut_envs_local = prove
 (`locals_rel temp loc loc' /\ every_name (\x. x < temp) names /\
   cut_envs names loc = SOME (x:((A)word_loc)spt#((A)word_loc)spt)
   ==> cut_envs names loc' = SOME x`,
  ACCEPT_TAC locals_rel_cut_envs);;

(* the call machinery does not read the locals of the caller (they are     *)
(* saved by cut_envs before the call)                                        *)

let WPROOF2AUX_push_env_locals = prove
 (`!envs h l (s:(A,C,FFI)wl_state).
     wl_push_env envs h (wl_state_locals_fupd (K l) s) =
     wl_state_locals_fupd (K l) (wl_push_env envs h s)`,
  REPEAT GEN_TAC THEN CASES_ON `h:(num#(A)wl_prog#num#num)option` THENL
   [REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN SIMP[] THEN
    PAIRARG_TAC THEN SIMP[] THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[];
    STRUCT_CASES_TAC (ISPEC `a:num#(A)wl_prog#num#num` PAIR_SURJECTIVE) THEN
    STRUCT_CASES_TAC (ISPEC `y:(A)wl_prog#num#num` PAIR_SURJECTIVE) THEN
    STRUCT_CASES_TAC (ISPEC `y':num#num` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN SIMP[] THEN
    PAIRARG_TAC THEN SIMP[] THEN REWRITE_TAC[wl_state_component_equality] THEN SIMP[]]);;

let WPROOF2AUX_call_env_locals = prove
 (`!args ss l (s:(A,C,FFI)wl_state).
     wl_call_env args ss (wl_state_locals_fupd (K l) s) = wl_call_env args ss s`,
  REWRITE_TAC[wl_call_env_def] THEN SIMP[] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;

let WPROOF2AUX_dec_clock_locals = prove
 (`!l (s:(A,C,FFI)wl_state).
     wl_dec_clock (wl_state_locals_fupd (K l) s) =
     wl_state_locals_fupd (K l) (wl_dec_clock s)`,
  REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN
  REWRITE_TAC[wl_state_component_equality] THEN SIMP[]);;



let WPROOF2AUX_push_env_handler = prove
 (CASE_TERM
  `!envs handler (g:(A)wl_prog->(A)wl_prog) (s:(A,C,FFI)wl_state).
     wl_push_env envs (match handler with
                         NONE -> NONE
                       | SOME (n,h,l1,l2) -> SOME (n,g h,l1,l2)) s =
     wl_push_env envs handler s`,
  REPEAT GEN_TAC THEN CASES_ON `handler:(num#(A)wl_prog#num#num)option` THEN
  CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `a:num#(A)wl_prog#num#num` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC (ISPEC `y:(A)wl_prog#num#num` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC (ISPEC `y':num#num` PAIR_SURJECTIVE) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_push_env_def]);;

let WPROOF2AUX_push_env_inst = prove
 (`!envs n (c:(A)asm_config) temp h l1 l2 (s:(A,C,FFI)wl_state).
     wl_push_env envs (SOME (n,inst_select c temp h,l1,l2)) s =
     wl_push_env envs (SOME (n,h,l1,l2)) s`,
  REWRITE_TAC[wl_push_env_def]);;

let WPROOF2AUX_handler_cases = prove
 (`!(handler:(num#(A)wl_prog#num#num)option).
     handler = NONE \/ ?hn h hl1 hl2. handler = SOME (hn,h,hl1,hl2)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `handler:(num#(A)wl_prog#num#num)option`
                                        (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let WPROOF2AUX_ret_cases = prove
 (`!(ret:(num list#cutsets#(A)wl_prog#num#num)option).
     ret = NONE \/ ?n names rh l1 l2. ret = SOME (n,names,rh,l1,l2)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option`
                                        (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  SPEC_TAC(`a:num list#cutsets#(A)wl_prog#num#num`,`a:num list#cutsets#(A)wl_prog#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* split the outermost case or conditional of the antecedent of the goal;   *)
(* the cut_envs of the related locals follows the original one              *)

let WPROOF2AUX_ANT_CASE_TAC : tactic = fun (asl,w as g) ->
  let a = fst(dest_imp w) in
  let tm = find_term (fun t -> is_case_app t || is_cond t) a in
  (if is_cond tm then
     let c = fst(dest_cond tm) in
     ASM_CASES_TAC c THEN ASM_REWRITE_TAC[]
   else
     let _,x,_ = dest_case_app tm in
     CASES_ON x THEN CASE_REWRITE_TAC[] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; FORALL_UNWIND_THM1]) THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) g;;

(* the leaves: an error, the same final state, or the induction hypothesis *)
(* for the program of the return handler or the exception handler          *)

let WPROOF2AUX_locals_rel_refl = prove
 (`!temp (l:((A)word_loc)spt). locals_rel temp l l`,
  REWRITE_TAC[locals_rel_def]);;

let WPROOF2AUX_CALL_IH_TAC : tactic = fun (asl,w as g) ->
  let ant = fst(dest_imp w) in
  let p,s = dest_pair(rand(lhs ant)) in
  let ih_ok th =
    let c = concl th in
    is_forall c &&
    (let v,b = dest_forall c in
     type_of v = `:(A,C,FFI)wl_state` &&
     can (find_term ((=) (mk_comb(mk_comb(
       `inst_select:(A)asm_config->num->(A)wl_prog->(A)wl_prog`,
       `c:(A)asm_config`), `temp:num`)))) b &&
     can (find_term ((=) p)) b) in
  (DISCH_TAC THEN
   FIRST_ASSUM(fun ih -> if not (ih_ok ih) then failwith "" else
     MP_TAC(SPECL [s; `res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`;
                   mk_icomb(`wl_state_locals:(A,C,FFI)wl_state->((A)word_loc)spt`, s)] ih)) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[WPROOF2AUX_locals_rel_refl];
     REWRITE_TAC[locals_rm]]) g;;

let WPROOF2AUX_SAME_WIT_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
                       rand(rator t) =
                         mk_icomb(`K:((A)word_loc)spt->((A)word_loc)spt->((A)word_loc)spt`, v) &&
                       (try fst(dest_const(rator(rator t))) = "wl_state_locals_fupd"
                        with Failure _ -> false)) bod in
  let s = rand t in
  EXISTS_TAC (mk_icomb(`wl_state_locals:(A,C,FFI)wl_state->((A)word_loc)spt`, s)) g;;

let WPROOF2AUX_CALL_LEAF_TAC : tactic =
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  FIRST
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC THEN NO_TAC;
    WPROOF2AUX_CALL_IH_TAC THEN NO_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    WPROOF2AUX_SAME_WIT_TAC THEN
    REWRITE_TAC[locals_rm] THEN CASE_REWRITE_TAC[] THEN NO_TAC];;

let WPROOF2AUX_is_Call = prove
 (let P = WPROOF2AUX_is `c:(A)asm_config` `temp:num` in
  let ihr = list_mk_forall([`n:num list`; `names:cutsets`; `l1:num`; `l2:num`;
                            `ret_handler:(A)wl_prog`],
              mk_imp(`ret = SOME (n:num list,names:cutsets,ret_handler:(A)wl_prog,
                                  l1:num,l2:num)`,
                     P `ret_handler:(A)wl_prog`))
  and ihh = list_mk_forall([`n:num`; `l1:num`; `l2:num`; `h:(A)wl_prog`],
              mk_imp(`handler = SOME (n:num,h:(A)wl_prog,l1:num,l2:num)`, P `h:(A)wl_prog`)) in
  mk_imp(mk_conj(ihr,ihh), P `wl_Call ret dest args handler:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def; LET_DEF; LET_END_DEF] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n:num list` (X_CHOOSE_THEN `names:cutsets`
      (X_CHOOSE_THEN `rh:(A)wl_prog` (X_CHOOSE_THEN `l1:num`
        (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)))))
    (SPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option` WPROOF2AUX_ret_cases) THEN
  CASE_REWRITE_TAC[] THENL
   [(* a tail call: the handler is NONE, and the program is unchanged *)
    STRIP_TAC THEN
    ASM_CASES_TAC `handler:(num#(A)wl_prog#num#num)option = NONE` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN
      MATCH_MP_TAC locals_rel_evaluate_thm THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th))))
                                                = "wl_every_var" with Failure _ -> false)) THEN
      REWRITE_TAC[wl_every_var_def] THEN CASE_REWRITE_TAC[] THEN SIMP[];
      FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ]) THEN
      STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[wl_every_var_def] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ihr" (MP_TAC o SPECL [`n:num list`; `names:cutsets`; `l1:num`; `l2:num`;
                                     `rh:(A)wl_prog`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ihr") THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hn:num` (X_CHOOSE_THEN `h:(A)wl_prog`
      (X_CHOOSE_THEN `hl1:num` (X_CHOOSE_THEN `hl2:num` SUBST_ALL_TAC))))
    (SPEC `handler:(num#(A)wl_prog#num#num)option` WPROOF2AUX_handler_cases) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    REMOVE_THEN "ihh" (MP_TAC o SPECL [`hn:num`; `hl1:num`; `hl2:num`; `h:(A)wl_prog`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ihh")] THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV) [wl_evaluate_def] THEN
  REWRITE_TAC[add_ret_loc_def] THEN CASE_REWRITE_TAC[] THEN
  WPROOF2AUX_LR_SIMP_TAC[] THEN
  REWRITE_TAC[WPROOF2AUX_push_env_handler; WPROOF2AUX_push_env_inst;
              WPROOF2AUX_dec_clock_locals;
              WPROOF2AUX_push_env_locals; WPROOF2AUX_call_env_locals] THEN
  SIMP[] THEN
  (SUBGOAL_THEN `!envs. cut_envs names (wl_state_locals (st:(A,C,FFI)wl_state)) = SOME envs
                        ==> cut_envs names (loc:((A)word_loc)spt) = SOME envs`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL locals_rel_cut_envs) THEN
     MAP_EVERY EXISTS_TAC [`temp:num`; `wl_state_locals (st:(A,C,FFI)wl_state)`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  REPEAT WPROOF2AUX_ANT_CASE_TAC THEN WPROOF2AUX_CALL_LEAF_TAC);;

(* the programs that inst_select leaves unchanged *)

let WPROOF2AUX_IS_ID_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[inst_select_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC locals_rel_evaluate_thm THEN ASM_REWRITE_TAC[];;

(* Main semantics theorem for inst selection: the inst-selected program     *)
(* gives same result but with possibly more locals used                     *)

let inst_select_thm = prove
 (CASE_TERM
  `!(c:(A)asm_config) temp prog (st:(A,C,FFI)wl_state) res rst loc.
     wl_evaluate (prog,st) = (res,rst) /\
     wl_every_var (\x. x < temp) prog /\
     ~(res = SOME wl_Error) /\
     locals_rel temp (wl_state_locals st) loc
     ==> ?loc'.
           wl_evaluate (inst_select c temp prog, wl_state_locals_fupd (K loc) st) =
           (res, wl_state_locals_fupd (K loc') rst) /\
           (match res with
              NONE -> locals_rel temp (wl_state_locals rst) loc'
            | SOME (wordSem_Break _) -> locals_rel temp (wl_state_locals rst) loc'
            | SOME (wordSem_Continue _) -> locals_rel temp (wl_state_locals rst) loc'
            | SOME _ -> wl_state_locals rst = loc')`,
  MATCH_MP_TAC inst_select_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_Assign;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_Set;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_Store;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_Seq;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_MustTerminate;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_ShareInst;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_If;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_Call;
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC WPROOF2AUX_is_Loop;
    WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC;
    WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC;
    WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC;
    WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC; WPROOF2AUX_IS_ID_TAC;
    WPROOF2AUX_IS_ID_TAC]);;
let WPROOF2AUX_eval_clause name =
  find (fun th ->
          try let l = lhs(snd(strip_forall(concl th))) in
              let p = fst(dest_pair(rand l)) in
              fst(dest_const(fst(strip_comb p))) = name
          with Failure _ -> false)
       (CONJUNCTS wl_evaluate_def);;
let WPROOF2AUX_eval_Seq_def = WPROOF2AUX_eval_clause "wl_Seq";;
let WPROOF2AUX_eval_Move_def = WPROOF2AUX_eval_clause "wl_Move";;
let WPROOF2AUX_eval_Inst_def = WPROOF2AUX_eval_clause "wl_Inst";;

let WPROOF2AUX_eval_Seq_gen = prove
 (`!c1 c2 (s:(A,C,FFI)wl_state) s1.
     wl_evaluate (c1, s) = (NONE, s1)
     ==> wl_evaluate (wl_Seq c1 c2, s) = wl_evaluate (c2, s1)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let WPROOF2AUX_eval_Move1_gen = prove
 (`!tar v x (s:(A,C,FFI)wl_state).
     lookup v (wl_state_locals s) = SOME x
     ==> wl_evaluate (wl_Move 0 [tar,v], s) =
         (NONE, wl_state_locals_fupd (K (insert tar x (wl_state_locals s))) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tar:num`; `v:num`; `x:(A)word_loc`; `wl_state_locals (s:(A,C,FFI)wl_state)`;
                `s:(A,C,FFI)wl_state`] WPROOF2AUX_eval_Move1) THEN
  ASM_REWRITE_TAC[locals_rm]);;



(* the instructions with a target register: Move then a two-register *)
(* instruction                                                            *)

let WPROOF2AUX_TT_INST_TAC : tactic =
  REWRITE_TAC[three_to_two_reg_def; every_inst_def; distinct_tar_reg_def] THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
   CAKE_SIMP_RULE (PAIR_EQ :: CONS_11 :: wl_get_vars_def :: wl_get_var_def :: WPROOF2AUX_ceqs) o
   REWRITE_RULE[WPROOF2AUX_eval_Inst_def; wl_inst_def; wl_assign_def; LET_DEF; LET_END_DEF] o
   check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC THEN
  REWRITE_TAC[WPROOF2AUX_eval_Seq_def; WPROOF2AUX_eval_Move_def; MAP; ALL_DISTINCT; MEM;
              wl_get_vars_def; wl_get_var_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WPROOF2AUX_eval_Inst_def; wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; wl_get_vars_def; wl_get_var_def; wl_set_vars_def;
              alist_insert_def] THEN
  SIMP[lookup_insert] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_set_var_def] THEN SIMP[insert_shadow];;


let WPROOF2AUX_INST_HYP_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o
    CAKE_SIMP_RULE (PAIR_EQ :: WPROOF2AUX_word_exp_op2 :: WPROOF2AUX_word_exp_shift ::
                    WPROOF2AUX_ceqs) o
    REWRITE_RULE[WPROOF2AUX_eval_Inst_def; wl_inst_def; wl_assign_def] o
    check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC;;


let WPROOF2AUX_TT_ARITH_TAC (step_reg:thm) (step_imm:thm) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[three_to_two_reg_def; every_inst_def; distinct_tar_reg_def] THEN
  STRIP_TAC THEN WPROOF2AUX_INST_HYP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_word_exp_def; wl_get_var_def]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_gen
                                      (MATCH_MP (SPEC `r1:num` WPROOF2AUX_eval_Move1_gen) th)]) THEN
  CASES_ON `ri:(A)reg_imm` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_word_exp_def; wl_get_var_def; option_INJ;
                              injectivity "word_loc"]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(NONE:((A)wl_result)option,
               wl_state_locals_fupd (K (insert r1 (wl_Word v)
                 (insert r1 (wl_Word a') (wl_state_locals s)))) (s:(A,C,FFI)wl_state))` THEN
  (CONJ_TAC THENL
    [FIRST [MATCH_MP_TAC step_reg THEN MAP_EVERY EXISTS_TAC [`a':A word`; `b:A word`] THEN
            ASM_REWRITE_TAC[lookup_insert] THEN ASM_MESON_TAC[];
            RVEQ_TAC THEN MATCH_MP_TAC step_imm THEN EXISTS_TAC `a':A word` THEN
            ASM_REWRITE_TAC[lookup_insert]];
     REWRITE_TAC[wl_set_var_def; insert_shadow] THEN SIMP[]]);;

let WPROOF2AUX_tt_Binop = prove
 (`!bop r1 r2 ri (s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg (wl_Inst (asm_Arith (Binop bop r1 r2 ri)):(A)wl_prog) /\
     wl_evaluate (wl_Inst (asm_Arith (Binop bop r1 r2 ri)), s) = (res,s') /\
     ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg (wl_Inst (asm_Arith (Binop bop r1 r2 ri))), s) =
         (res,s')`,
  WPROOF2AUX_TT_ARITH_TAC WPROOF2AUX_eval_Binop_Reg WPROOF2AUX_eval_Binop_Imm);;

let WPROOF2AUX_tt_Shift = prove
 (`!l r1 r2 ri (s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg (wl_Inst (asm_Arith (asm_Shift l r1 r2 ri)):(A)wl_prog) /\
     wl_evaluate (wl_Inst (asm_Arith (asm_Shift l r1 r2 ri)), s) = (res,s') /\
     ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg (wl_Inst (asm_Arith (asm_Shift l r1 r2 ri))), s) =
         (res,s')`,
  WPROOF2AUX_TT_ARITH_TAC WPROOF2AUX_eval_Shift_Reg WPROOF2AUX_eval_Shift_Imm);;

let WPROOF2AUX_tt_AddCarry = prove
 (`!r1 r2 r3 r4 (s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg (wl_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)):(A)wl_prog) /\
     wl_evaluate (wl_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)), s) = (res,s') /\
     ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg (wl_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4))), s) =
         (res,s')`,
  REPEAT GEN_TAC THEN WPROOF2AUX_TT_INST_TAC);;

let WPROOF2AUX_tt_AddOverflow = prove
 (`!r1 r2 r3 r4 (s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg (wl_Inst (asm_Arith (AddOverflow r1 r2 r3 r4)):(A)wl_prog) /\
     wl_evaluate (wl_Inst (asm_Arith (AddOverflow r1 r2 r3 r4)), s) = (res,s') /\
     ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg (wl_Inst (asm_Arith (AddOverflow r1 r2 r3 r4))), s) =
         (res,s')`,
  REPEAT GEN_TAC THEN WPROOF2AUX_TT_INST_TAC);;

let WPROOF2AUX_tt_SubOverflow = prove
 (`!r1 r2 r3 r4 (s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg (wl_Inst (asm_Arith (SubOverflow r1 r2 r3 r4)):(A)wl_prog) /\
     wl_evaluate (wl_Inst (asm_Arith (SubOverflow r1 r2 r3 r4)), s) = (res,s') /\
     ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg (wl_Inst (asm_Arith (SubOverflow r1 r2 r3 r4))), s) =
         (res,s')`,
  REPEAT GEN_TAC THEN WPROOF2AUX_TT_INST_TAC);;

let WPROOF2AUX_eval_OpCurrHeap_def = WPROOF2AUX_eval_clause "wl_OpCurrHeap";;

let WPROOF2AUX_tt_OpCurrHeap = prove
 (`!bop r1 r2 (s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg (wl_OpCurrHeap bop r1 r2:(A)wl_prog) /\
     wl_evaluate (wl_OpCurrHeap bop r1 r2, s) = (res,s') /\
     ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg (wl_OpCurrHeap bop r1 r2), s) = (res,s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[three_to_two_reg_def; every_inst_def; distinct_tar_reg_def] THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    CAKE_SIMP_RULE (PAIR_EQ :: WPROOF2AUX_word_exp_op2 :: WPROOF2AUX_ceqs) o
    REWRITE_RULE[WPROOF2AUX_eval_OpCurrHeap_def] o
    check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_word_exp_def; wl_get_var_def]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_eval_Seq_gen
                                      (MATCH_MP (SPEC `r1:num` WPROOF2AUX_eval_Move1_gen) th)]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(NONE:((A)wl_result)option,
               wl_state_locals_fupd (K (insert r1 (wl_Word v)
                 (insert r1 (wl_Word a') (wl_state_locals s)))) (s:(A,C,FFI)wl_state))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WPROOF2AUX_eval_OpCurrHeap THEN
    MAP_EVERY EXISTS_TAC [`a':A word`; `b:A word`] THEN
    ASM_REWRITE_TAC[lookup_insert];
    REWRITE_TAC[wl_set_var_def; insert_shadow] THEN SIMP[]]);;


(* three_to_two_reg semantics *)

let three_to_two_reg_Loop = prove
 (`!(s:(A,C,FFI)wl_state) names prog exit_names res s'.
     (!(v:(A,C,FFI)wl_state) res s'.
        wl_evaluate (prog, v) = (res, s') /\ ~(res = SOME wl_Error)
        ==> wl_evaluate (three_to_two_reg prog, v) = (res, s')) /\
     wl_evaluate (wl_Loop names prog exit_names, s) = (res, s') /\ ~(res = SOME wl_Error)
     ==> wl_evaluate (wl_Loop names (three_to_two_reg prog) exit_names, s) = (res, s')`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC(MESON[]
   `(!n (s:(A,C,FFI)wl_state). wl_state_clock s = n ==> P s) ==> !s. P s`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:(A,C,FFI)wl_state` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[wl_STOP_def] THEN
  CASES_ON `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  CASES_ON `wl_evaluate (prog:(A)wl_prog, a:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
    SIMP[PAIR_EQ] THEN REPEAT COND_CASES_TAC THEN SIMP[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (three_to_two_reg prog, a:(A,C,FFI)wl_state) = (x,y)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_clock (wl_dec_clock (y:(A,C,FFI)wl_state))` o
                check (fun th -> is_forall (concl th) &&
                         is_imp (snd(dest_forall(concl th))) &&
                         is_binary "<" (fst(dest_imp(snd(dest_forall(concl th))))))) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o
                  check (fun th -> concl th = `wl_evaluate (prog:(A)wl_prog,
                                    a:(A,C,FFI)wl_state) = x,y`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> try rator(lhs(concl th)) =
                    `wl_cut_state (names,LN):(A,C,FFI)wl_state->((A,C,FFI)wl_state)option`
                    with Failure _ -> false)) THEN
    REWRITE_TAC[wl_cut_state_def] THEN
    CASES_ON `wl_cut_env (names,LN) (wl_state_locals (s:(A,C,FFI)wl_state))` THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `wl_dec_clock (y:(A,C,FFI)wl_state)`) THEN REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


let WPROOF2AUX_TT = `\prog:(A)wl_prog. !(s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg prog /\ wl_evaluate (prog,s) = (res,s') /\
     ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg prog, s) = (res,s')`;;

let WPROOF2AUX_tt p = rhs(concl(BETA_CONV(mk_comb(WPROOF2AUX_TT, p))));;

let WPROOF2AUX_tt_Seq = prove
 (mk_imp(mk_conj(WPROOF2AUX_tt `p1:(A)wl_prog`, WPROOF2AUX_tt `p2:(A)wl_prog`),
         WPROOF2AUX_tt `wl_Seq p1 p2:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[three_to_two_reg_def; every_inst_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  REWRITE_TAC[WPROOF2AUX_eval_Seq_def] THEN
  CASES_ON `wl_evaluate (p1:(A)wl_prog, s:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
    SIMP[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (three_to_two_reg p1, s:(A,C,FFI)wl_state) = (x,y)`
    SUBST1_TAC THENL [REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_eval_MustTerminate_def = WPROOF2AUX_eval_clause "MustTerminate";;

let WPROOF2AUX_tt_MustTerminate = prove
 (mk_imp(WPROOF2AUX_tt `p1:(A)wl_prog`, WPROOF2AUX_tt `MustTerminate p1:(A)wl_prog`),
  DISCH_THEN(LABEL_TAC "ih1") THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[three_to_two_reg_def; every_inst_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  REWRITE_TAC[WPROOF2AUX_eval_MustTerminate_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  PAIRARG_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `wl_evaluate (three_to_two_reg p1,
                  wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                    (wl_state_termdep_fupd (K (wl_state_termdep s - 1))
                       (s:(A,C,FFI)wl_state))) = (res',s1)`
    SUBST1_TAC THENL
   [REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond(lhs(concl th)))) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_eval_If_def = WPROOF2AUX_eval_clause "wl_If";;

let WPROOF2AUX_tt_If = prove
 (mk_imp(mk_conj(WPROOF2AUX_tt `c1:(A)wl_prog`, WPROOF2AUX_tt `c2:(A)wl_prog`),
         WPROOF2AUX_tt `wl_If cmp r1 ri c1 c2:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[three_to_two_reg_def; every_inst_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  REWRITE_TAC[WPROOF2AUX_eval_If_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN DISCH_TAC THENL
   [REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let WPROOF2AUX_tt_Loop = prove
 (mk_imp(WPROOF2AUX_tt `body:(A)wl_prog`,
         WPROOF2AUX_tt `wl_Loop names body exit_names:(A)wl_prog`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[three_to_two_reg_def; every_inst_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC three_to_two_reg_Loop THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


let WPROOF2AUX_push_env_tt = prove
 (`!envs n h l1 l2 (s:(A,C,FFI)wl_state).
     wl_push_env envs (SOME (n,three_to_two_reg h,l1,l2)) s =
     wl_push_env envs (SOME (n,h,l1,l2)) s`,
  REWRITE_TAC[wl_push_env_def]);;

let WPROOF2AUX_eval_Call_def = WPROOF2AUX_eval_clause "wl_Call";;

let WPROOF2AUX_TT_LEAF_TAC : tactic =
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  FIRST
   [REWRITE_TAC[] THEN NO_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN WPROOF2AUX_ERR_TAC THEN NO_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC];;

let WPROOF2AUX_tt_Call = prove
 (let P = WPROOF2AUX_tt in
  let ihr = list_mk_forall([`n:num list`; `names:cutsets`; `l1:num`; `l2:num`;
                            `ret_handler:(A)wl_prog`],
              mk_imp(`ret = SOME (n:num list,names:cutsets,ret_handler:(A)wl_prog,
                                  l1:num,l2:num)`,
                     P `ret_handler:(A)wl_prog`))
  and ihh = list_mk_forall([`n:num`; `l1:num`; `l2:num`; `h:(A)wl_prog`],
              mk_imp(`handler = SOME (n:num,h:(A)wl_prog,l1:num,l2:num)`, P `h:(A)wl_prog`)) in
  mk_imp(mk_conj(ihr,ihh), P `wl_Call ret dest args handler:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[three_to_two_reg_def; LET_DEF; LET_END_DEF] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n:num list` (X_CHOOSE_THEN `names:cutsets`
      (X_CHOOSE_THEN `rh:(A)wl_prog` (X_CHOOSE_THEN `l1:num`
        (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)))))
    (SPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option` WPROOF2AUX_ret_cases) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hn:num` (X_CHOOSE_THEN `h:(A)wl_prog`
      (X_CHOOSE_THEN `hl1:num` (X_CHOOSE_THEN `hl2:num` SUBST_ALL_TAC))))
    (SPEC `handler:(num#(A)wl_prog#num#num)option` WPROOF2AUX_handler_cases) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[every_inst_def] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REMOVE_THEN "ihr" (MP_TAC o SPECL [`n:num list`; `names:cutsets`; `l1:num`; `l2:num`;
                                     `rh:(A)wl_prog`]) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "ihh" (MP_TAC o SPECL [`hn:num`; `hl1:num`; `hl2:num`; `h:(A)wl_prog`]) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (WPROOF2AUX_is_app_of "wl_evaluate")) THEN
  REWRITE_TAC[WPROOF2AUX_eval_Call_def] THEN
  REWRITE_TAC[add_ret_loc_def; WPROOF2AUX_push_env_tt] THEN CASE_REWRITE_TAC[] THEN
  REPEAT WPROOF2AUX_ANT_CASE_TAC THEN WPROOF2AUX_TT_LEAF_TAC);;


(* Semantics preservation *)

let three_to_two_reg_correct = prove
 (`!prog (s:(A,C,FFI)wl_state) res s'.
     every_inst distinct_tar_reg prog /\
     wl_evaluate (prog,s) = (res,s') /\ ~(res = SOME wl_Error)
     ==> wl_evaluate (three_to_two_reg prog,s) = (res,s')`,
  MATCH_MP_TAC three_to_two_reg_ind THEN REPEAT CONJ_TAC THEN
  FIRST (map (fun th -> REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC th)
           [WPROOF2AUX_tt_Binop; WPROOF2AUX_tt_Shift; WPROOF2AUX_tt_AddCarry;
            WPROOF2AUX_tt_AddOverflow; WPROOF2AUX_tt_SubOverflow; WPROOF2AUX_tt_OpCurrHeap;
            WPROOF2AUX_tt_Seq; WPROOF2AUX_tt_MustTerminate; WPROOF2AUX_tt_If;
            WPROOF2AUX_tt_Call; WPROOF2AUX_tt_Loop] @
         [REWRITE_TAC[three_to_two_reg_def] THEN MESON_TAC[]]));;

let evaluate_three_to_two_reg_prog = prove
 (`wl_evaluate (prog,s:(A,C,FFI)wl_state) = (res,s') /\ ~(res = SOME wl_Error) /\
   every_inst distinct_tar_reg prog
   ==> wl_evaluate (three_to_two_reg_prog t prog,s) = (res,s')`,
  REWRITE_TAC[three_to_two_reg_prog_def] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[three_to_two_reg_correct]);;
