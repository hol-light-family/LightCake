(* ========================================================================= *)
(* word_simpProof: port of HOL4 compiler/backend/proofs/                     *)
(* word_simpProofScript.sml (CakeML v3479).                                  *)
(* Correctness proof for word_simp.                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The names of wordLang, wordSem and wordProps are those of their files  *)
(*   (wl_evaluate, wl_get_var, wl_state_locals, ...): HOL4 s.f is           *)
(*   wl_state_f s, s with f := v is wl_state_f_fupd (K v) s.                 *)
(* - HOL4's type abbreviation gc_fun_type is written out.                   *)
(* - WSIMPPAUX_ names are local helpers.                                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/word_simp.ml";;
needs "hol4/alist.ml";;

type_invention_error := true;;

(* verification of Seq_assoc *)

let evaluate_SmartSeq = prove
 (`wl_evaluate (SmartSeq p1 p2,s:(A,C,FFI)wl_state) =
   wl_evaluate (wl_Seq p1 p2,s)`,
  RW[SmartSeq_def; wl_evaluate_def]);;

(* HOL4: evaluate_Seq_Skip *)

let word_simpProof_evaluate_Seq_Skip = prove
 (`!p1 (s:(A,C,FFI)wl_state).
     wl_evaluate (wl_Seq p1 wl_Skip,s) = wl_evaluate (p1,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN PAIRARG_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: evaluate_Skip_Seq *)

let word_simpProof_evaluate_Skip_Seq = prove
 (`wl_evaluate (wl_Seq wl_Skip p,s:(A,C,FFI)wl_state) = wl_evaluate (p,s)`,
  SIMP[wl_evaluate_def]);;

let evaluate_Loop_body_cong = prove
 (`!(s:(A,C,FFI)wl_state) names c c' exit_names.
     (!(v:(A,C,FFI)wl_state). wl_evaluate (c',v) = wl_evaluate (c,v)) ==>
     wl_evaluate (wl_Loop names c' exit_names,s) =
     wl_evaluate (wl_Loop names c exit_names,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n (s:(A,C,FFI)wl_state). wl_state_clock s = n ==>
      wl_evaluate (wl_Loop names c' exit_names,s) =
      wl_evaluate (wl_Loop names c exit_names,s)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s0:(A,C,FFI)wl_state` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[wl_STOP_def] THEN
  CASES_ON `wl_cut_state (names,LN) (s0:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN
  SUBGOAL_THEN `wl_state_clock (a:(A,C,FFI)wl_state) = wl_state_clock (s0:(A,C,FFI)wl_state)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `wl_cut_state (names,LN) (s0:(A,C,FFI)wl_state) = SOME a` THEN
    REWRITE_TAC[wl_cut_state_def] THEN CASE_TAC THEN SIMP[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_evaluate_clock) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_clock (wl_dec_clock (s1:(A,C,FFI)wl_state))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_ARITH_TAC;
    DISCH_THEN MATCH_MP_TAC THEN REFL_TAC]);;

let evaluate_Loop_body_cong_gc = prove
 (`!(s:(A,C,FFI)wl_state) names c c' exit_names.
     (!(v:(A,C,FFI)wl_state). R (wl_state_gc_fun v) ==>
        wl_evaluate (c',v) = wl_evaluate (c,v)) ==>
     R (wl_state_gc_fun s) ==>
     wl_evaluate (wl_Loop names c' exit_names,s) =
     wl_evaluate (wl_Loop names c exit_names,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n (s:(A,C,FFI)wl_state). wl_state_clock s = n ==> R (wl_state_gc_fun s) ==>
      wl_evaluate (wl_Loop names c' exit_names,s) =
      wl_evaluate (wl_Loop names c exit_names,s)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s0:(A,C,FFI)wl_state` THEN REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[wl_STOP_def] THEN
  CASES_ON `wl_cut_state (names,LN) (s0:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wl_state_clock (a:(A,C,FFI)wl_state) = wl_state_clock (s0:(A,C,FFI)wl_state) /\
                wl_state_gc_fun a = wl_state_gc_fun s0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wl_cut_state (names,LN) (s0:(A,C,FFI)wl_state) = SOME a` THEN
    REWRITE_TAC[wl_cut_state_def] THEN CASE_TAC THEN SIMP[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (c',a) = wl_evaluate (c,a:(A,C,FFI)wl_state)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_evaluate_clock) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_evaluate_consts) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_clock (wl_dec_clock (s1:(A,C,FFI)wl_state))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `wl_dec_clock (s1:(A,C,FFI)wl_state)`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_MESON_TAC[]]);;

let evaluate_Seq_assoc_lemma = prove
 (`!p1 p2 (s:(A,C,FFI)wl_state).
     wl_evaluate (Seq_assoc p1 p2,s) = wl_evaluate (wl_Seq p1 p2,s)`,
  MATCH_MP_TAC word_simp_Seq_assoc_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[word_simp_Seq_assoc_def; evaluate_SmartSeq;
              word_simpProof_evaluate_Seq_Skip] THENL
   [(* Seq *)
    STRIP_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[wl_evaluate_def] THEN
    CASES_ON `wl_evaluate (p1,s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    (* If *)
    STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[word_simpProof_evaluate_Skip_Seq];
    (* MustTerminate *)
    DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[word_simpProof_evaluate_Skip_Seq];
    (* Call *)
    MAP_EVERY (fun t -> SPEC_TAC(t,t))
      [`handler:(num#(A)wl_prog#num#num)option`;
       `ret_prog:(num list#cutsets#(A)wl_prog#num#num)option`] THEN
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_INJ; PAIR_EQ;
                option_DISTINCT] THEN
    CASE_REWRITE_TAC[] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[wl_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[wl_push_env_def; add_ret_loc_def] THEN
    ASM_REWRITE_TAC[word_simpProof_evaluate_Skip_Seq];
    (* Loop *)
    DISCH_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    SUBGOAL_THEN
     `!s. wl_evaluate (wl_Loop names (Seq_assoc wl_Skip body) exit_names,
                       s:(A,C,FFI)wl_state) =
          wl_evaluate (wl_Loop names body exit_names,s)`
     (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN MATCH_MP_TAC evaluate_Loop_body_cong THEN
    ASM_REWRITE_TAC[word_simpProof_evaluate_Skip_Seq]]);;

(* HOL4: evaluate_Seq_assoc *)

let word_simpProof_evaluate_Seq_assoc = prove
 (`!p (s:(A,C,FFI)wl_state). wl_evaluate (Seq_assoc wl_Skip p,s) = wl_evaluate (p,s)`,
  REWRITE_TAC[evaluate_Seq_assoc_lemma; word_simpProof_evaluate_Skip_Seq]);;

let dest_If_Eq_Imm_thm = prove
 (`dest_If_Eq_Imm x2 = SOME (n,w,p1,p2) <=>
   x2 = wl_If asm_Equal n (Imm w) (p1:(A)wl_prog) p2`,
  CASES_ON `x2:(A)wl_prog` THEN FS[dest_If_Eq_Imm_def; dest_If_def] THEN
  EVERY_CASE_TAC THEN FS[]);;

(* HOL4: dest_If_thm *)

let word_simpProof_dest_If_thm = prove
 (`dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = wl_If g1 g2 g3 g4 (g5:(A)wl_prog)`,
  CASES_ON `x2:(A)wl_prog` THEN FS[dest_If_def]);;

let dest_Seq_IMP = prove
 (`word_simp_dest_Seq p1 = (x1,x2) ==>
   wl_evaluate (p1,s:(A,C,FFI)wl_state) = wl_evaluate (wl_Seq x1 x2,s)`,
  CASES_ON `p1:(A)wl_prog` THEN FS[SmartSeq_def; word_simp_dest_Seq_def] THEN
  RW[] THEN FS[word_simpProof_evaluate_Skip_Seq]);;

let dest_Seq_Assign_Const_IMP = prove
 (`dest_Seq_Assign_Const v p = SOME (q,w) ==>
   wl_evaluate (p,s:(A,C,FFI)wl_state) =
   wl_evaluate (wl_Seq q (wl_Assign v (wl_Const w)),s)`,
  REWRITE_TAC[dest_Seq_Assign_Const_def] THEN PAIRARG_TAC THEN
  CASES_ON `p2:(A)wl_prog` THEN FS[] THEN TOP_CASE_TAC THEN FS[] THEN
  RW[] THEN IMP_RES_TAC dest_Seq_IMP THEN FS[]);;

(* verification of const_fp *)

(* gc *)

let is_gc_word_const_def = cake_def
  `(is_gc_word_const (wl_Loc _ _:(A)word_loc) <=> T) /\
   (is_gc_word_const (wl_Word (w:A word)) <=> is_gc_const w)`;;

(* HOL4's type abbreviation gc_fun_type written out *)

let gc_fun_const_ok_def = cake_def
  `gc_fun_const_ok (f:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                      (store_name,(A)word_loc)fmap->
                      (((A)word_loc)list#(A word->(A)word_loc)#
                       (store_name,(A)word_loc)fmap)option) <=>
     !x y. f x = SOME y ==>
           ALL2 (\a b. is_gc_word_const a ==> b = a) (FST x) (FST y)`;;

let sf_gc_consts_def = cake_def
  `sf_gc_consts (StackFrame _ l0 sv h:(A)stack_frame) (StackFrame _ l0' sw h') <=>
     ALL2 (\(ak,av) (bk,bv). ak = bk /\ (is_gc_word_const av ==> bv = av)) sv sw /\
     l0 = l0' /\ h = h'`;;

let sf_gc_consts_refl = prove
 (`!x:(A)stack_frame. sf_gc_consts x x`,
  GEN_TAC THEN CASES_ON `x:(A)stack_frame` THEN RW[sf_gc_consts_def] THEN
  MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[FORALL_PAIR_THM]);;

(* HOL4's EVERY2_trans in the form that irule uses *)

let WSIMPPAUX_EVERY2_trans = prove
 (`!R x y z. (!x y z. R x y /\ R y z ==> R x z) /\
             ALL2 (R:A->A->bool) x y /\ ALL2 R y z ==> ALL2 R x z`,
  MESON_TAC[EVERY2_trans]);;

let sf_gc_consts_trans = prove
 (`!a b c:(A)stack_frame.
     sf_gc_consts a b /\ sf_gc_consts b c ==> sf_gc_consts a c`,
  REPEAT GEN_TAC THEN CASES_ON `a:(A)stack_frame` THEN
  CASES_ON `b:(A)stack_frame` THEN CASES_ON `c:(A)stack_frame` THEN
  REWRITE_TAC[sf_gc_consts_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WSIMPPAUX_EVERY2_trans THEN
  EXISTS_TAC `a2':(num#(A)word_loc)list` THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
  MESON_TAC[]);;

(* Assign *)

let strip_const_thm = prove
 (`!xs (x:(A word)list) (s:(A,C,FFI)wl_state).
     strip_const xs = SOME x ==>
     MAP (\a. wl_word_exp s a) xs = MAP (SOME o wl_Word) x`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:(A)wl_exp`) THEN
  FS[strip_const_def; wl_word_exp_def] THEN
  REPEAT GEN_TAC THEN CASE_TAC THEN FS[MAP; o_THM] THEN RW[MAP; o_THM]);;

let the_words_thm = prove
 (`!x. the_words (MAP (SOME o wl_Word) x) = SOME (x:(A word)list)`,
  LIST_INDUCT_TAC THEN SIMP[the_words_def; MAP; o_THM]);;

let const_fp_exp_word_exp = prove
 (`!e cs (s:(A,C,FFI)wl_state).
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) ==>
     wl_word_exp s (const_fp_exp e cs) = wl_word_exp s e`,
  MATCH_MP_TAC const_fp_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[const_fp_exp_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THENL
   [(* Var *)
    DISCH_TAC THEN CASE_TAC THEN SIMP[wl_word_exp_def] THEN ASM_MESON_TAC[];
    (* Op *)
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `MAP (wl_word_exp s) (MAP (\a. const_fp_exp a cs) args) =
                  MAP (wl_word_exp (s:(A,C,FFI)wl_state)) args` ASSUME_TAC THENL
     [REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!ws. MAP (wl_word_exp (s:(A,C,FFI)wl_state)) (MAP wl_Const ws) =
                       MAP (SOME o wl_Word) ws` ASSUME_TAC THENL
     [REWRITE_TAC[MAP_MAP_o; MAP_EQ_f; o_THM; wl_word_exp_def]; ALL_TAC] THEN
    CASE_TAC THEN ASM_REWRITE_TAC[wl_word_exp_def] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:(A,C,FFI)wl_state` o MATCH_MP strip_const_thm) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[the_words_thm] THEN CASE_TAC THEN
    SIMP[wl_word_exp_def; the_words_thm];
    (* Shift *)
    STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `wl_word_exp s (wl_Shift sh e e1) =
                  wl_word_exp (s:(A,C,FFI)wl_state)
                    (wl_Shift sh (const_fp_exp e cs) (const_fp_exp e1 cs))`
    SUBST1_TAC THENL
     [REWRITE_TAC[wl_word_exp_def] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`const_fp_exp e1 cs:(A)wl_exp`,`ce1:(A)wl_exp`) THEN
    SPEC_TAC(`const_fp_exp e cs:(A)wl_exp`,`ce:(A)wl_exp`) THEN
    REPEAT GEN_TAC THEN REPEAT (CASE_TAC THEN SIMP[wl_word_exp_def])]);;

(* HOL4 proves this by induction; it follows from const_fp_exp_word_exp *)

let const_fp_exp_word_exp_const = prove
 (`!e cs (s:(A,C,FFI)wl_state) c.
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) /\
     const_fp_exp e cs = wl_Const c ==>
     wl_word_exp s e = SOME (wl_Word c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:(A)wl_exp`; `cs:(A word)spt`; `s:(A,C,FFI)wl_state`]
               const_fp_exp_word_exp) THEN
  ASM_REWRITE_TAC[wl_word_exp_def] THEN MESON_TAC[]);;

(* Move *)

let set_vars_move_NONE = prove
 (`!(moves:(num#num)list) (x:((A)word_loc)list) (s:(A,C,FFI)wl_state) s' v.
     wl_set_vars (MAP FST moves) x s = s' /\ ALOOKUP moves v = NONE ==>
     wl_get_var v s' = wl_get_var v s`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  FS[wl_set_vars_def; wl_get_var_def; alist_insert_def; MAP] THEN RW[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ALOOKUP_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP[]);;

let set_vars_move_SOME = prove
 (`!(moves:(num#num)list) (x:((A)word_loc)list) v w (s:(A,C,FFI)wl_state) s'.
     wl_set_vars (MAP FST moves) x s = s' /\
     wl_get_vars (MAP SND moves) s = SOME x /\
     ALOOKUP moves v = SOME w ==>
     wl_get_var v s' = wl_get_var w s`,
  LIST_INDUCT_TAC THEN RW[] THEN CASES_ON `h:num#num` THEN
  FS[wl_get_var_def; wl_get_vars_def; wl_set_vars_def; MAP; ALOOKUP_DEF] THEN
  EVERY_CASE_TAC THEN FS[] THEN RW[alist_insert_def; lookup_insert]);;

let get_var_move_thm = prove
 (CASE_TERM
  `!(s:(A,C,FFI)wl_state) s' (moves:(num#num)list) x v.
     wl_get_vars (MAP SND moves) s = SOME x /\
     wl_set_vars (MAP FST moves) x s = s' ==>
     wl_get_var v s' = match ALOOKUP moves v with
                         SOME w -> wl_get_var w s
                       | NONE -> wl_get_var v s`,
  RW[] THEN CASE_TAC THEN ASM_MESON_TAC[set_vars_move_SOME; set_vars_move_NONE]);;

let lookup_const_fp_move_cs_NONE = prove
 (`!(moves:(num#num)list) v (cs:A spt) cs'.
     ALOOKUP moves v = NONE /\ lookup v cs = lookup v cs' ==>
     lookup v (const_fp_move_cs moves cs cs') = lookup v cs'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[const_fp_move_cs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALOOKUP_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!ncs:A spt. lookup v ncs = lookup v (cs':A spt) ==>
                 lookup v (const_fp_move_cs t cs ncs) = lookup v cs'`
  MATCH_MP_TAC THENL
   [ASM_MESON_TAC[];
    CASE_TAC THEN REWRITE_TAC[lookup_insert; lookup_delete] THEN ASM_MESON_TAC[]]);;

let lookup_const_fp_move_cs_SOME_part = prove
 (`!(moves:(num#num)list) q (cs:A spt) cs' x.
     ~MEM q (MAP FST moves) /\ lookup q cs' = x ==>
     lookup q (const_fp_move_cs moves cs cs') = x`,
  LIST_INDUCT_TAC THEN RW[const_fp_move_cs_def; MAP; MEM] THEN CASE_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[lookup_delete; lookup_insert] THEN
  ASM_MESON_TAC[]);;

(* HOL4: TODO: In need of cleanup *)

let lookup_const_fp_move_cs_SOME = prove
 (`!(moves:(num#num)list) v w (cs:A spt) cs'.
     ALOOKUP moves v = SOME w /\
     ALL_DISTINCT (MAP FST moves) /\
     lookup v cs = lookup v cs' ==>
     lookup v (const_fp_move_cs moves cs cs') = lookup w cs`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ALOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `r:num`] THEN
  REWRITE_TAC[const_fp_move_cs_def; MAP; ALL_DISTINCT; FST; SND; ALOOKUP_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `q:num = v` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC lookup_const_fp_move_cs_SOME_part THEN
    ASM_REWRITE_TAC[] THEN CASE_TAC THEN REWRITE_TAC[lookup_delete; lookup_insert] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CASE_TAC THEN REWRITE_TAC[lookup_delete; lookup_insert] THEN ASM_MESON_TAC[]]);;

let lookup_const_fp_move_cs = prove
 (CASE_TERM
  `!v (moves:(num#num)list) (cs:A spt).
     ALL_DISTINCT (MAP FST moves) ==>
     lookup v (const_fp_move_cs moves cs cs) =
     match ALOOKUP moves v with SOME w -> lookup w cs | NONE -> lookup v cs`,
  RW[] THEN CASE_TAC THEN
  ASM_MESON_TAC[lookup_const_fp_move_cs_SOME; lookup_const_fp_move_cs_NONE]);;

(* If *)

let get_var_imm_cs_imp_get_var_imm = prove
 (`!x (y:A word) (s:(A,C,FFI)wl_state) cs.
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) /\
     get_var_imm_cs x cs = SOME y ==>
     wl_get_var_imm x s = SOME (wl_Word y)`,
  RW[] THEN CASES_ON `x:(A)reg_imm` THEN
  FS[get_var_imm_cs_def; wl_get_var_imm_def] THEN ASM_MESON_TAC[]);;

(* Helpful lemmas about locals *)

(* HOL4: get_var_set_var_thm (TODO move) *)

let word_simpProof_get_var_set_var_thm = prove
 (`!k1 k2 v (s:(A,C,FFI)wl_state).
     wl_get_var k1 (wl_set_var k2 v s) =
     if k1 = k2 then SOME v else wl_get_var k1 s`,
  RW[wl_get_var_def; wl_set_var_def; lookup_insert]);;

let get_var_mem_store_thm = prove
 (`!v addr (x:(A)word_loc) (s:(A,C,FFI)wl_state).
     wl_mem_store addr x s = SOME s' ==> wl_get_var v s' = wl_get_var v s`,
  RW[wl_mem_store_def] THEN RW[wl_get_var_def]);;

let cs_delete_if_set = prove
 (`!x v1 v2 (s:(A,C,FFI)wl_state) cs w.
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) /\
     lookup v2 (delete v1 cs) = SOME w ==>
     wl_get_var v2 (wl_set_var v1 x s) = SOME (wl_Word w)`,
  RW[word_simpProof_get_var_set_var_thm] THEN FS[lookup_delete]);;

let cs_delete_if_set_x2 = prove
 (`!x1 x2 v1 v2 v3 (s:(A,C,FFI)wl_state) cs w.
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) /\
     lookup v3 (delete v2 (delete v1 cs)) = SOME w ==>
     wl_get_var v3 (wl_set_var v2 x2 (wl_set_var v1 x1 s)) = SOME (wl_Word w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC cs_delete_if_set THEN
  EXISTS_TAC `delete v1 (cs:(A word)spt)` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[cs_delete_if_set]);;

(* Lookup thms *)

let lookup_inter_eq_some = prove
 (`!m1 m2 k (x:A). lookup k (inter_eq m1 m2) = SOME x ==>
                   lookup k m1 = SOME x /\ lookup k m2 = SOME x`,
  RW[lookup_inter_eq] THEN EVERY_CASE_TAC THEN FS[]);;

let lookup_filter_v_SOME = prove
 (`!t k (v:A) f. lookup k (filter_v f t) = SOME v ==> f v`,
  REWRITE_TAC[lookup_filter_v] THEN REPEAT GEN_TAC THEN TOP_CASE_TAC THEN RW[] THEN
  RW[]);;

let lookup_filter_v_SOME_imp = prove
 (`!t k (v:A) f. lookup k (filter_v f t) = SOME v ==> lookup k t = SOME v`,
  REWRITE_TAC[lookup_filter_v] THEN REPEAT GEN_TAC THEN TOP_CASE_TAC THEN RW[]);;

(* LIST_REL/EVERY2 thms *)

let LIST_REL_prefix = prove
 (`!R l1 l2 l1' l2'.
     ALL2 (R:A->B->bool) (APPEND l1 l2) (APPEND l1' l2') /\
     LENGTH l1 = LENGTH l1' ==>
     ALL2 R l1 l1'`,
  MESON_TAC[LIST_REL_APPEND_IMP]);;

let LIST_REL_append_left = prove
 (`!l0 l1 l2 (R:A->B->bool).
     ALL2 R (APPEND l0 l1) l2 ==>
     ALL2 R l0 (TAKE (LENGTH l0) l2) /\ ALL2 R l1 (DROP (LENGTH l0) l2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_TAC LIST_REL_LENGTH THEN
  MATCH_MP_TAC LIST_REL_APPEND_IMP THEN ASM_REWRITE_TAC[TAKE_DROP] THEN
  SUBGOAL_THEN `LENGTH (l0:A list) <= LENGTH (l2:B list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (APPEND (l0:A list) l1) = LENGTH (l2:B list)` THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
    ASM_SIMP_TAC[LENGTH_TAKE]]);;

(* Stack thms *)

let push_env_set_store_stack = prove
 (`!x1 x2 x3 x4 (s:(A,C,FFI)wl_state).
     wl_state_stack (wl_push_env x1 x2 (wl_set_store x3 x4 s)) =
     wl_state_stack (wl_push_env x1 x2 s)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[wl_push_env_def; wl_set_store_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  PAIRARG_TAC THEN SIMP[]);;

(* HOL4 [local], TODO delete *)

let pop_env_stack_gc = prove
 (`!s:(A,C,FFI)wl_state.
     wl_pop_env s = SOME s' ==> wl_state_gc_fun s' = wl_state_gc_fun s`,
  RW[wl_pop_env_def] THEN EVERY_CASE_TAC THEN FS[] THEN RW[]);;

(* move the assumption (if b then x else y) = z into the goal *)

let WSIMPPAUX_COND_ASM_TAC : tactic =
  FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_eq c && is_cond(lhs c) then MP_TAC th else failwith "WSIMPPAUX_COND_ASM_TAC");;

let ALOOKUP_LIST_REL_sf_gc_consts = prove
 (`!(l1:(B#(A)word_loc)list) l2 k v.
     ALL2 (\(ak,av) (bk,bv). ak = bk /\ (is_gc_word_const av ==> bv = av)) l1 l2 /\
     is_gc_word_const v /\
     ALOOKUP l1 k = SOME v ==>
     ALOOKUP l2 k = SOME v`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALOOKUP_DEF; option_DISTINCT] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`h':B#(A)word_loc`; `h:B#(A)word_loc`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[]);;

let ALOOKUP_LIST_REL_sf_gc_consts_NONE = prove
 (`!(l1:(B#(A)word_loc)list) l2 k (v:(A)word_loc).
     ALL2 (\(ak,av) (bk,bv). ak = bk /\ (is_gc_word_const av ==> bv = av)) l1 l2 /\
     ALOOKUP l1 k = NONE ==>
     ALOOKUP l2 k = NONE`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALOOKUP_DEF; option_DISTINCT] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`h':B#(A)word_loc`; `h:B#(A)word_loc`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let ALL_DISTINCT_PERM_FST = prove
 (`!l:(A#B)list. ALL_DISTINCT (MAP FST l) /\ PERM l (f l) ==>
                 ALL_DISTINCT (MAP FST (f l))`,
  RW[] THEN
  SUBGOAL_THEN `PERM (MAP FST (l:(A#B)list)) (MAP FST ((f:(A#B)list->(A#B)list) l))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[PERM_MAP]; ALL_TAC] THEN
  ASM_MESON_TAC[ALL_DISTINCT_PERM]);;

let ALOOKUP_LIST_REL_value_rel = prove
 (`!f (l':(B#A)list) l k v.
     ALL2 (\(ak,av) (bk,bv). ak = bk /\ (f av ==> bv = av)) l' l /\
     ALOOKUP l' k = SOME v /\ f v ==>
     ALOOKUP l k = SOME v`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALOOKUP_DEF; option_DISTINCT] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`h':B#A`; `h:B#A`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN WSIMPPAUX_COND_ASM_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 alistTheory.ALOOKUP_ALL_DISTINCT_PERM_same (not in hol4/alist.ml) *)

let WSIMPPAUX_ALOOKUP_ALL_DISTINCT_PERM_same = prove
 (`!(l1:(A#B)list) l2.
     ALL_DISTINCT (MAP FST l1) /\ PERM (MAP FST l1) (MAP FST l2) /\
     set_of_list l1 = set_of_list l2 ==> ALOOKUP l1 = ALOOKUP l2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  SUBGOAL_THEN `!p:A#B. MEM p l1 <=> MEM p l2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (l2:(A#B)list))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALL_DISTINCT_PERM]; ALL_TAC] THEN
  CASES_ON `ALOOKUP (l2:(A#B)list) x` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ALOOKUP_FAILS]) THEN
    ASM_REWRITE_TAC[ALOOKUP_FAILS] THEN ASM_MESON_TAC[];
    IMP_RES_TAC ALOOKUP_MEM THEN ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM]]);;

let ALOOKUP_ALL_DISTINCT_FST_PERM = prove
 (`!l1 l2:(A#B)list. ALL_DISTINCT (MAP FST l1) /\ PERM l1 l2 ==>
                     ALOOKUP l1 = ALOOKUP l2`,
  RW[] THEN MATCH_MP_TAC WSIMPPAUX_ALOOKUP_ALL_DISTINCT_PERM_same THEN
  ASM_SIMP_TAC[PERM_MAP] THEN ASM_MESON_TAC[PERM_LIST_TO_SET]);;

let ALOOKUP_ALL_DISTINCT_FST_PERM_SOME = prove
 (`!(l1:(A#B)list) f k v.
     ALL_DISTINCT (MAP FST l1) /\
     PERM l1 (f l1) /\
     ALOOKUP l1 k = SOME v ==>
     ALOOKUP (f l1) k = SOME v`,
  MESON_TAC[ALOOKUP_ALL_DISTINCT_FST_PERM]);;

let pop_env_gc_fun = prove
 (`!(s:(A,C,FFI)wl_state) s'.
     wl_pop_env s = SOME s' ==> wl_state_gc_fun s' = wl_state_gc_fun s`,
  RW[wl_pop_env_def] THEN EVERY_CASE_TAC THEN FS[] THEN RW[]);;

let pop_env_gc_fun_const_ok = prove
 (`!(s:(A,C,FFI)wl_state) s'.
     wl_pop_env s = SOME s' /\ gc_fun_const_ok (wl_state_gc_fun s) ==>
     gc_fun_const_ok (wl_state_gc_fun s')`,
  MESON_TAC[pop_env_gc_fun]);;

(* (HOL4 has a commented-out call_env_push_env_dec_clock here) *)

let evaluate_gc_fun_const_ok = prove
 (`!p (s:(A,C,FFI)wl_state) res s'.
     wl_evaluate (p,s) = (res,s') /\ gc_fun_const_ok (wl_state_gc_fun s) ==>
     gc_fun_const_ok (wl_state_gc_fun s')`,
  MESON_TAC[wl_evaluate_consts]);;

let get_above_handler_def = cake_def
  `get_above_handler (s:(A,C,FFI)wl_state) =
     match EL (LENGTH (wl_state_stack s) - (wl_state_handler s + 1))
              (wl_state_stack s) with
       StackFrame _ _ _ (SOME (h,_,_)) -> h`;;

(* the stack frame relation on the values of a frame (part of the proof of *)
(* HOL4's enc_stack_dec_stack_is_gc_word_const)                            *)

let WSIMPPAUX_ALL2_ZIP_MAP_FST = prove
 (`!(l:(num#(A)word_loc)list) t.
     LENGTH t = LENGTH l /\
     ALL2 (\a b. is_gc_word_const a ==> b = a) (MAP SND l) t ==>
     ALL2 (\(ak,av) (bk,bv). ak = bk /\ (is_gc_word_const av ==> bv = av))
          l (ZIP (MAP FST l) t)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP; ALL2] THEN
  SPEC_TAC(`h:num#(A)word_loc`,`h:num#(A)word_loc`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN ASM_MESON_TAC[]);;

(* HOL4's dec_stack_def clause for a frame with a general value list (the  *)
(* TFL completion splits it on the value list)                              *)

let enc_stack_dec_stack_is_gc_word_const = prove
 (`!(s:((A)stack_frame)list) s' s'l.
     ALL2 (\a b. is_gc_word_const a ==> b = a) (wl_enc_stack s) s'l /\
     wl_dec_stack s'l s = SOME s' ==>
     ALL2 sf_gc_consts s s'`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[wl_enc_stack_def; ALL2_DEF] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FS[wl_dec_stack_def];
    ALL_TAC] THEN
  SPEC_TAC(`h:(A)stack_frame`,`h:(A)stack_frame`) THEN
  MATCH_MP_TAC stack_frame_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`n:num option`; `l0:(num#(A)word_loc)list`;
                       `l:(num#(A)word_loc)list`; `hd:(num#num#num)option`] THEN
  REWRITE_TAC[wl_enc_stack_def; IL2AUX_dec_stack_cons] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN CASE_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LIST_REL_append_left) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  REWRITE_TAC[ALL2; sf_gc_consts_def] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WSIMPPAUX_ALL2_ZIP_MAP_FST THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let gc_fun_sf_gc_consts = prove
 (`!(s:((A)stack_frame)list) s'l s' gc_fun memory memory' mdomain store store'.
     gc_fun_const_ok gc_fun /\
     gc_fun (wl_enc_stack s,memory,mdomain,store) = SOME (s'l,memory',store') /\
     wl_dec_stack s'l s = SOME s' ==>
     ALL2 sf_gc_consts s s'`,
  RW[] THEN RULE_ASSUM_TAC(REWRITE_RULE[gc_fun_const_ok_def]) THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[FST] THEN ASM_MESON_TAC[enc_stack_dec_stack_is_gc_word_const]);;

let gc_sf_gc_consts = prove
 (`!(s:(A,C,FFI)wl_state) s'.
     gc_fun_const_ok (wl_state_gc_fun s) /\ wl_gc s = SOME s' ==>
     ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s')`,
  RW[wl_gc_def] THEN EVERY_CASE_TAC THEN FS[] THEN
  IMP_RES_TAC gc_fun_sf_gc_consts THEN RW[] THEN SIMP[]);;

let gc_handler = prove
 (`!(s:(A,C,FFI)wl_state) s'.
     wl_gc s = SOME s' ==> wl_state_handler s' = wl_state_handler s`,
  RW[wl_gc_def] THEN EVERY_CASE_TAC THEN RW[] THEN SIMP[]);;

(* a frame related to a given frame by sf_gc_consts *)

let WSIMPPAUX_sf_gc_consts_left = prove
 (`!n l0 sv h (y:(A)stack_frame).
     sf_gc_consts (StackFrame n l0 sv h) y <=>
     ?n' sw. y = StackFrame n' l0 sw h /\
             ALL2 (\(ak,av) (bk,bv). ak = bk /\ (is_gc_word_const av ==> bv = av))
                  sv sw`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)stack_frame` THEN
  SIMP[sf_gc_consts_def] THEN MESON_TAC[]);;

let sf_gc_consts_get_above_handler = prove
 (`!(s:(A,C,FFI)wl_state) (s':(A,C1,FFI1)wl_state).
     ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
     wl_state_handler s' = wl_state_handler s /\
     wl_state_handler s < LENGTH (wl_state_stack s) ==>
     get_above_handler s' = get_above_handler s`,
  RW[get_above_handler_def] THEN IMP_RES_TAC EVERY2_LENGTH THEN
  SUBGOAL_THEN
   `sf_gc_consts
      (EL (LENGTH (wl_state_stack (s':(A,C1,FFI1)wl_state)) -
           (wl_state_handler (s:(A,C,FFI)wl_state) + 1)) (wl_state_stack s))
      (EL (LENGTH (wl_state_stack s') - (wl_state_handler s + 1))
          (wl_state_stack s'))`
  MP_TAC THENL
   [FS[LIST_REL_EL_EQN] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`EL (LENGTH (wl_state_stack (s':(A,C1,FFI1)wl_state)) -
                (wl_state_handler (s:(A,C,FFI)wl_state) + 1)) (wl_state_stack s')`,
           `y:(A)stack_frame`) THEN
  SPEC_TAC(`EL (LENGTH (wl_state_stack (s':(A,C1,FFI1)wl_state)) -
                (wl_state_handler (s:(A,C,FFI)wl_state) + 1)) (wl_state_stack s)`,
           `x:(A)stack_frame`) THEN
  REPEAT STRIP_TAC THEN CASES_ON `x:(A)stack_frame` THEN
  CASES_ON `y:(A)stack_frame` THEN FS[sf_gc_consts_def]);;

let LIST_REL_call_Result = prove
 (`!(s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) (s'':(A,C1,FFI1)wl_state) s'''
    env (handler:(num#(A)wl_prog#num#num)option).
     ALL2 sf_gc_consts (wl_state_stack (wl_push_env env handler s))
                       (wl_state_stack s'') /\
     wl_pop_env s'' = SOME s''' /\
     wl_state_handler s'' = wl_state_handler (wl_push_env env handler s) ==>
     ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s''') /\
     wl_state_handler s''' = wl_state_handler s`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`handler:(num#(A)wl_prog#num#num)option`,
           `handler:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT GEN_TAC THEN PAIRARG_TAC THEN SIMP[] THEN
  REWRITE_TAC[wl_pop_env_def] THEN
  CASES_ON `wl_state_stack (s'':(A,C1,FFI1)wl_state)` THEN
  ASM_REWRITE_TAC[ALL2; WSIMPPAUX_sf_gc_consts_left] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN FS[] THEN RVEQ_TAC THEN SIMP[]);;

let get_above_handler_call_env_push_env_dec_clock = prove
 (`!(s:(A,C,FFI)wl_state) s' (s'':(B,D,E)wl_state) args lsz env x0 x1 x2 x3.
     s' = wl_call_env args lsz
            (wl_push_env env (SOME (x0,x1,x2,x3)) (wl_dec_clock s)) /\
     wl_state_handler s'' = get_above_handler s' ==>
     wl_state_handler s'' = wl_state_handler s`,
  RW[wl_call_env_def; wl_push_env_def; wl_dec_clock_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
  FS[get_above_handler_def; LENGTH; ARITH_RULE `SUC n - (n + 1) = 0`; EL; HD]);;

let call_env_push_env_dec_clock_handler_length = prove
 (`!(s:(A,C,FFI)wl_state) s' args lsz env x0 x1 x2 x3.
     s' = wl_call_env args lsz
            (wl_push_env env (SOME (x0,x1,x2,x3)) (wl_dec_clock s)) ==>
     wl_state_handler s' < LENGTH (wl_state_stack s')`,
  RW[wl_call_env_def; wl_push_env_def; wl_dec_clock_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
  SIMP[LENGTH] THEN ARITH_TAC);;

let EVERY2_trans_LASTN_sf_gc_consts = prove
 (`!(l:((A)stack_frame)list) l' l'' n (R:B).
     n <= LENGTH l /\ ALL2 sf_gc_consts l l' /\
     ALL2 sf_gc_consts (LASTN n l') l'' ==>
     ALL2 sf_gc_consts (LASTN n l) l''`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WSIMPPAUX_EVERY2_trans THEN
  EXISTS_TAC `LASTN n (l':((A)stack_frame)list)` THEN
  ASM_SIMP_TAC[list_rel_lastn] THEN MESON_TAC[sf_gc_consts_trans]);;

let LIST_REL_push_env = prove
 (`!R (s:(A,C,FFI)wl_state) (s':(B,D,E)wl_state) env h.
     ALL2 R (wl_state_stack (wl_push_env env h s)) (wl_state_stack s') ==>
     ALL2 R (wl_state_stack s) (TL (wl_state_stack s'))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT GEN_TAC THEN PAIRARG_TAC THEN
  SIMP[] THEN CASES_ON `wl_state_stack (s':(B,D,E)wl_state)` THEN
  ASM_REWRITE_TAC[ALL2; TL] THEN MESON_TAC[CONS_11; NOT_CONS_NIL]);;

(* HOL4: TODO move *)

let LASTN_LENGTH_CONS = prove
 (`!l (h:A). LASTN (LENGTH l) (CONS h l) = l`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `CONS (h:A) l = APPEND [h] l` SUBST1_TAC THENL
   [REWRITE_TAC[APPEND]; REWRITE_TAC[LASTN_LENGTH_APPEND]]);;

let LASTN_TL_res = prove
 (`!(l:A list) n h t. n < LENGTH l /\ LASTN (n + 1) l = CONS h t ==> t = LASTN n l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LASTN (n + 1) l = DROP (LENGTH l - (n + 1)) (l:A list) /\
                LASTN n l = DROP (LENGTH l - n) (l:A list)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LASTN_DROP THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (l:A list) - (n + 1) < LENGTH l` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DROP_EL_CONS) THEN
  SUBGOAL_THEN `LENGTH (l:A list) - (n + 1) + 1 = LENGTH l - n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LASTN (n + 1) l = CONS (h:A) t` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[CONS_11]);;

let HD_LASTN = prove
 (`!(l:A list) n. 0 < n /\ n <= LENGTH l ==> HD (LASTN n l) = EL (LENGTH l - n) l`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LASTN_DROP] THEN
  MP_TAC(ISPECL [`0`; `LENGTH (l:A list) - n`; `l:A list`] EL_DROP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; EL] THEN DISCH_THEN ACCEPT_TAC);;

(* the GCed cutset of a pushed frame, looked up (from the proof of HOL4's *)
(* push_env_pop_env_locals_thm)                                           *)

let WSIMPPAUX_ALOOKUP_env_to_list = prove
 (`!(e:((A)word_loc)spt) bij k. ALOOKUP (FST (env_to_list e bij)) k = lookup k e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST] THEN
  SUBGOAL_THEN
   `PERM (toAList (e:((A)word_loc)spt))
         (list_rearrange (bij 0) (sort key_val_compare (toAList e)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PERM_TRANS THEN
    EXISTS_TAC `sort key_val_compare (toAList (e:((A)word_loc)spt))` THEN
    REWRITE_TAC[sort_PERM] THEN MATCH_MP_TAC PERM_list_rearrange THEN
    MP_TAC(ISPECL [`key_val_compare:num#(A)word_loc->num#(A)word_loc->bool`;
                   `toAList (e:((A)word_loc)spt)`] sort_PERM) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP ALL_DISTINCT_PERM th)]) THEN
    MATCH_MP_TAC(ISPEC `FST:num#(A)word_loc->num` ALL_DISTINCT_MAP) THEN
    REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`toAList (e:((A)word_loc)spt)`;
                 `list_rearrange (bij 0)
                    (sort key_val_compare (toAList (e:((A)word_loc)spt)))`]
                ALOOKUP_ALL_DISTINCT_FST_PERM) THEN
  ASM_REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ALOOKUP_toAList]);;

let push_env_pop_env_locals_thm = prove
 (`!(s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state) (s'':(A,C,FFI)wl_state) s''' env names
    (handler:(num#(A)wl_prog#num#num)option).
     cut_envs names (wl_state_locals s) = SOME env /\
     wl_push_env env handler s = s' /\
     ALL2 sf_gc_consts (wl_state_stack s') (wl_state_stack s'') /\
     wl_pop_env s'' = SOME s''' ==>
     (!v w. wl_get_var v s = SOME w /\ is_gc_word_const w /\
            ~(lookup v (all_names names) = NONE) ==>
            wl_get_var v s''' = SOME w)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:(A,C,FFI)wl_state`; `s':(A,C,FFI)wl_state`;
    `s'':(A,C,FFI)wl_state`; `s''':(A,C,FFI)wl_state`; `e1:((A)word_loc)spt`;
    `e2:((A)word_loc)spt`; `n0:num_set`; `n1:num_set`;
    `handler:(num#(A)wl_prog#num#num)option`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  (* the frame that is pushed *)
  SUBGOAL_THEN
   `?h'. wl_state_stack (wl_push_env (e1,e2) handler (s:(A,C,FFI)wl_state)) =
         CONS (StackFrame (wl_state_locals_size s) (toAList e1)
                 (FST (env_to_list e2 (wl_state_permute s))) h')
              (wl_state_stack s)`
  STRIP_ASSUME_TAC THENL
   [SPEC_TAC(`handler:(num#(A)wl_prog#num#num)option`,
             `handler:(num#(A)wl_prog#num#num)option`) THEN
    REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT GEN_TAC THEN PAIRARG_TAC THEN
    SIMP[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; WSIMPPAUX_sf_gc_consts_left]) THEN
  FIRST_X_ASSUM(fun th -> if is_exists(concl th) then CAKE_STRIP_ASSUME_TAC th
                          else failwith "") THEN RVEQ_TAC THEN
  REWRITE_TAC[wl_get_var_def] THEN
  (* the locals after the pop *)
  SUBGOAL_THEN `wl_state_locals (s''':(A,C,FFI)wl_state) =
                union (fromAList sw) (fromAList (toAList (e1:((A)word_loc)spt)))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `wl_pop_env (s'':(A,C,FFI)wl_state) = SOME s'''` THEN
    ASM_REWRITE_TAC[wl_pop_env_def] THEN CASE_REWRITE_TAC[] THEN
    REPEAT (TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[];
    ALL_TAC] THEN
  (* the cutsets *)
  UNDISCH_TAC `cut_envs (n0,n1) (wl_state_locals (s:(A,C,FFI)wl_state)) = SOME (e1,e2)` THEN
  REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  REPEAT (COND_CASES_TAC THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[all_names_def; lookup_union; lookup_fromAList; ALOOKUP_toAList] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `lookup v (n1:num_set) = NONE` THENL
   [SUBGOAL_THEN `ALOOKUP (sw:(num#(A)word_loc)list) v = NONE` SUBST1_TAC THENL
     [MATCH_MP_TAC ALOOKUP_LIST_REL_sf_gc_consts_NONE THEN
      EXISTS_TAC `FST (env_to_list (inter (wl_state_locals (s:(A,C,FFI)wl_state))
                                          (n1:num_set)) (wl_state_permute s))` THEN
      ASM_REWRITE_TAC[WSIMPPAUX_ALOOKUP_env_to_list; lookup_inter_EQ];
      ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[lookup_inter_EQ] THEN ASM_REWRITE_TAC[] THEN
    CASES_ON `lookup v (n0:num_set)` THEN FS[];
    SUBGOAL_THEN `ALOOKUP (sw:(num#(A)word_loc)list) v = SOME w` SUBST1_TAC THENL
     [MATCH_MP_TAC ALOOKUP_LIST_REL_sf_gc_consts THEN
      EXISTS_TAC `FST (env_to_list (inter (wl_state_locals (s:(A,C,FFI)wl_state))
                                          (n1:num_set)) (wl_state_permute s))` THEN
      ASM_REWRITE_TAC[WSIMPPAUX_ALOOKUP_env_to_list; lookup_inter_EQ];
      CASE_REWRITE_TAC[]]]);;

(* The conclusion of evaluate_sf_gc_consts as a function of the result and *)
(* the states, and its properties (local helpers for that proof)          *)

let WSIMPPAUX_sfc = CASE_TERM
 `\(res:((A)wl_result)option) (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state).
    match res with
      NONE ->
        ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
        wl_state_handler s' = wl_state_handler s
    | SOME (wl_Result _ _) ->
        ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
        wl_state_handler s' = wl_state_handler s
    | SOME (wl_Exception _ _) ->
        wl_state_handler s < LENGTH (wl_state_stack s) ==>
        ALL2 sf_gc_consts (LASTN (wl_state_handler s) (wl_state_stack s))
                          (wl_state_stack s') /\
        wl_state_handler s' = get_above_handler s
    | SOME (wordSem_Break _) ->
        ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
        wl_state_handler s' = wl_state_handler s
    | SOME (wordSem_Continue _) ->
        ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
        wl_state_handler s' = wl_state_handler s
    | _ -> T`;;

let WSIMPPAUX_SFC_TERM res s s' =
  rand(concl(DEPTH_CONV BETA_CONV (list_mk_comb(WSIMPPAUX_sfc,[res;s;s']))));;

let WSIMPPAUX_SFC_trans = prove
 (mk_imp(`ALL2 sf_gc_consts (wl_state_stack (s:(A,C,FFI)wl_state))
                            (wl_state_stack (s1:(A,C,FFI)wl_state)) /\
          wl_state_handler s1 = wl_state_handler s`,
         mk_imp(WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s1:(A,C,FFI)wl_state`
                                   `s':(A,C,FFI)wl_state`,
                WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                                   `s':(A,C,FFI)wl_state`)),
  STRIP_TAC THEN
  SUBGOAL_THEN `!l:((A)stack_frame)list. ALL2 sf_gc_consts (wl_state_stack (s1:(A,C,FFI)wl_state)) l
                  ==> ALL2 sf_gc_consts (wl_state_stack (s:(A,C,FFI)wl_state)) l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WSIMPPAUX_EVERY2_trans THEN
    EXISTS_TAC `wl_state_stack (s1:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[sf_gc_consts_trans];
    ALL_TAC] THEN
  CASES_ON `res:((A)wl_result)option` THEN CASE_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `a:(A)wl_result` THEN CASE_REWRITE_TAC[] THEN
  TRY (ASM_MESON_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (wl_state_stack (s:(A,C,FFI)wl_state)) =
                LENGTH (wl_state_stack (s1:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC EVERY2_trans_LASTN_sf_gc_consts THEN
    EXISTS_TAC `wl_state_stack (s1:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_IMP_LE; ARITH_RULE `0 <= 0`];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC sf_gc_consts_get_above_handler THEN
    ASM_REWRITE_TAC[]]);;

let WSIMPPAUX_SFC_eq = prove
 (mk_imp(`wl_state_stack (s1:(A,C,FFI)wl_state) = wl_state_stack (s:(A,C,FFI)wl_state) /\
          wl_state_handler s1 = wl_state_handler s /\
          wl_state_stack (s2:(A,C,FFI)wl_state) = wl_state_stack (s2':(A,C,FFI)wl_state) /\
          wl_state_handler s2 = wl_state_handler s2'`,
         mk_eq(WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s1:(A,C,FFI)wl_state`
                                  `s2:(A,C,FFI)wl_state`,
               WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                                  `s2':(A,C,FFI)wl_state`)),
  STRIP_TAC THEN ASM_REWRITE_TAC[get_above_handler_def]);;

(* induction on the pair (p,s) of a goal !p s. Q p s with wl_evaluate_ind *)

let WSIMPPAUX_EVAL_IND_TAC : tactic = fun (asl,w as g) ->
  let p,b = dest_forall w in
  let s,body = dest_forall b in
  let x = mk_var("x", mk_type("prod",[type_of p; type_of s])) in
  let body' = subst [mk_icomb(mk_const("FST",[]),x), p;
                     mk_icomb(mk_const("SND",[]),x), s] body in
  (SUBGOAL_THEN (mk_forall(x, body')) MP_TAC THENL
    [MATCH_MP_TAC wl_evaluate_ind THEN REWRITE_TAC[FST; SND];
     REWRITE_TAC[FORALL_PAIR_THM; FST; SND]]) g;;

let WSIMPPAUX_SFC_trans_alt = REWRITE_RULE[IMP_IMP] (GEN_ALL WSIMPPAUX_SFC_trans);;

let WSIMPPAUX_ALL2_sf_refl = prove
 (`!l:((A)stack_frame)list. ALL2 sf_gc_consts l l`,
  GEN_TAC THEN MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[sf_gc_consts_refl]);;

(* tactics for the clauses of evaluate: a clause (case ... ) = (res,s') ==> *)
(* conclusion is split along its cases (in the antecedent only); an error  *)
(* result closes by computation, a normal one by simplification            *)

let WSIMPPAUX_easy_rws =
  [wl_set_var_def; wl_set_vars_def; wl_unset_var_def; wl_set_store_def;
   wl_dec_clock_def; wl_flush_state_def; wl_mem_store_def; wl_call_env_def;
   WSIMPPAUX_ALL2_sf_refl];;

let WSIMPPAUX_KILL_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN NO_TAC;;

let WSIMPPAUX_FINISH_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
  SIMP WSIMPPAUX_easy_rws THEN NO_TAC;;

let WSIMPPAUX_share_rws =
  [share_inst_def; wl_sh_mem_store_def; wl_sh_mem_store_byte_def;
   wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_sh_mem_load_def;
   wl_sh_mem_load_byte_def; wl_sh_mem_load16_def; wl_sh_mem_load32_def;
   sh_mem_set_var_def];;

(* split on the result of an FFI call in sh_mem_set_var (SOME x) v s *)

let WSIMPPAUX_SHMEM_CASE_TAC : tactic = fun (asl,w as g) ->
  let is_shm t =
    let h,args = strip_comb t in
    is_const h && fst(dest_const h) = "sh_mem_set_var" && length args = 3 &&
    (let a = hd args in is_comb a && is_const(rator a) &&
                        fst(dest_const(rator a)) = "SOME" &&
                        not (is_comb (rand a) && is_const(fst(strip_comb(rand a))) &&
                             mem (fst(dest_const(fst(strip_comb(rand a)))))
                                 ["FFI_final"; "FFI_return"])) in
  let t = find_term is_shm w in
  CASES_ON (rand(hd(snd(strip_comb t)))) g;;

(* split the first case or conditional of the antecedent of the goal *)

let WSIMPPAUX_ANT_CASE_TAC : tactic = fun (asl,w as g) ->
  let ant = fst(dest_imp w) in
  let x = first_case_scrutinee w (lhs ant) in
  if type_of x = bool_ty then (ASM_CASES_TAC x THEN ASM_REWRITE_TAC[]) g
  else (CASES_ON x THEN CASE_TIDY_TAC) g;;

let WSIMPPAUX_LOOP_TAC rws =
  REPEAT (WSIMPPAUX_KILL_TAC ORELSE WSIMPPAUX_FINISH_TAC ORELSE
          CHANGED_TAC (REWRITE_TAC rws) ORELSE WSIMPPAUX_SHMEM_CASE_TAC ORELSE
          WSIMPPAUX_ANT_CASE_TAC);;

let WSIMPPAUX_CLAUSE_TAC rws : tactic =
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  WSIMPPAUX_LOOP_TAC rws;;

(* use an induction hypothesis whose conclusion matches the goal *)

let WSIMPPAUX_IH_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th) THEN
    ASM_MESON_TAC[]);;

let WSIMPPAUX_push_env_consts = prove
 (`!env h (s:(A,C,FFI)wl_state).
     wl_state_gc_fun (wl_push_env env h s) = wl_state_gc_fun s /\
     (h = NONE ==> wl_state_handler (wl_push_env env h s) = wl_state_handler s)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN PAIRARG_TAC THEN
  SIMP[option_DISTINCT]);;

(* the Alloc clause *)

let WSIMPPAUX_alloc_stack = prove
 (`!(s:(A,C,FFI)wl_state) envs w s1 s2.
     gc_fun_const_ok (wl_state_gc_fun s) /\
     wl_gc (wl_push_env envs NONE (wl_set_store AllocSize (wl_Word w) s)) = SOME s1 /\
     wl_pop_env s1 = SOME s2 ==>
     ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s2) /\
     wl_state_handler s2 = wl_state_handler s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wl_set_store AllocSize (wl_Word w) (s:(A,C,FFI)wl_state)`;
                 `wl_set_store AllocSize (wl_Word w) (s:(A,C,FFI)wl_state)`;
                 `s1:(A,C,FFI)wl_state`; `s2:(A,C,FFI)wl_state`;
                 `envs:((A)word_loc)spt#((A)word_loc)spt`;
                 `NONE:(num#(A)wl_prog#num#num)option`] LIST_REL_call_Result) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC gc_sf_gc_consts THEN
      ASM_REWRITE_TAC[WSIMPPAUX_push_env_consts; wl_set_store_def] THEN SIMP[];
      IMP_RES_TAC gc_handler THEN ASM_REWRITE_TAC[]];
    SIMP[wl_set_store_def]]);;

(* the Raise clause *)

let WSIMPPAUX_jump_exc = prove
 (`!(s:(A,C,FFI)wl_state) s1 l1 l2.
     wl_jump_exc s = SOME (s1,l1,l2) ==>
     wl_state_handler s < LENGTH (wl_state_stack s) /\
     wl_state_stack s1 = LASTN (wl_state_handler s) (wl_state_stack s) /\
     wl_state_handler s1 = get_above_handler s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_jump_exc_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `LASTN (wl_state_handler s + 1) (wl_state_stack (s:(A,C,FFI)wl_state))` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT]) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LASTN_TL_res THEN ASM_MESON_TAC[];
    REWRITE_TAC[get_above_handler_def] THEN
    MP_TAC(ISPECL [`wl_state_stack (s:(A,C,FFI)wl_state)`;
                   `wl_state_handler (s:(A,C,FFI)wl_state) + 1`] HD_LASTN) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[HD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CASE_REWRITE_TAC[]]);;

(* the Loop clause *)

let WSIMPPAUX_SFC_exit_loop = prove
 (mk_imp(WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                            `s1:(A,C,FFI)wl_state`,
         WSIMPPAUX_SFC_TERM `wl_exit_loop (res:((A)wl_result)option)` `s:(A,C,FFI)wl_state`
                            `s1:(A,C,FFI)wl_state`),
  CASES_ON `res:((A)wl_result)option` THEN REWRITE_TAC[wl_exit_loop_def] THEN
  CASE_REWRITE_TAC[] THEN CASES_ON `a:(A)wl_result` THEN
  REWRITE_TAC[wl_exit_loop_def] THEN CASE_REWRITE_TAC[]);;

let WSIMPPAUX_SFC_unlabelled = prove
 (mk_imp(`(res:((A)wl_result)option) = NONE \/ (?n. res = SOME (wordSem_Break n)) \/
          (?n. res = SOME (wordSem_Continue n))`,
         mk_imp(WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                                   `s1:(A,C,FFI)wl_state`,
                `ALL2 sf_gc_consts (wl_state_stack (s:(A,C,FFI)wl_state))
                                   (wl_state_stack (s1:(A,C,FFI)wl_state)) /\
                 wl_state_handler s1 = wl_state_handler s`)),
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let WSIMPPAUX_SFC_unlabelled_alt = REWRITE_RULE[IMP_IMP] (GEN_ALL WSIMPPAUX_SFC_unlabelled);;

(* stack, handler and gc_fun under the state updates of a call *)

let WSIMPPAUX_call_state_consts = prove
 (`!args1 ss n ys v y (s:(A,C,FFI)wl_state).
     wl_state_stack (wl_call_env args1 ss s) = wl_state_stack s /\
     wl_state_handler (wl_call_env args1 ss s) = wl_state_handler s /\
     wl_state_gc_fun (wl_call_env args1 ss s) = wl_state_gc_fun s /\
     wl_state_stack (wl_dec_clock s) = wl_state_stack s /\
     wl_state_handler (wl_dec_clock s) = wl_state_handler s /\
     wl_state_gc_fun (wl_dec_clock s) = wl_state_gc_fun s /\
     wl_state_stack (wl_set_vars n ys s) = wl_state_stack s /\
     wl_state_handler (wl_set_vars n ys s) = wl_state_handler s /\
     wl_state_gc_fun (wl_set_vars n ys s) = wl_state_gc_fun s /\
     wl_state_stack (wl_set_var v y s) = wl_state_stack s /\
     wl_state_handler (wl_set_var v y s) = wl_state_handler s /\
     wl_state_gc_fun (wl_set_var v y s) = wl_state_gc_fun s`,
  SIMP[wl_call_env_def; wl_dec_clock_def; wl_set_vars_def; wl_set_var_def]);;

let WSIMPPAUX_SFC_eq_imp = prove
 (mk_imp(`wl_state_stack (s1:(A,C,FFI)wl_state) = wl_state_stack (s:(A,C,FFI)wl_state) /\
          wl_state_handler s1 = wl_state_handler s`,
         mk_imp(WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s1:(A,C,FFI)wl_state`
                                   `s2:(A,C,FFI)wl_state`,
                WSIMPPAUX_SFC_TERM `res:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                                   `s2:(A,C,FFI)wl_state`)),
  STRIP_TAC THEN ASM_REWRITE_TAC[get_above_handler_def]);;

(* the induction hypothesis of evaluate_sf_gc_consts for (p,st), as a term *)

let WSIMPPAUX_IH_TERM p st =
  let pp = `pp:(A)wl_prog` and st0 = `st0:(A,C,FFI)wl_state`
  and s' = `s':(A,C,FFI)wl_state` and res = `res:((A)wl_result)option` in
  let body = mk_imp(mk_conj(`wl_evaluate (pp:(A)wl_prog,st0:(A,C,FFI)wl_state) = (res,s')`,
                            `gc_fun_const_ok (wl_state_gc_fun (st0:(A,C,FFI)wl_state))`),
                    WSIMPPAUX_SFC_TERM res st0 s') in
  vsubst [p,pp; st,st0] (list_mk_forall([s';res],body));;

let WSIMPPAUX_list_mk_imp (hs,c) = itlist (curry mk_imp) hs c;;

let WSIMPPAUX_SFC_eq_imp_alt = REWRITE_RULE[IMP_IMP] (GEN_ALL WSIMPPAUX_SFC_eq_imp);;

(* the four leaves of the Call case *)

let WSIMPPAUX_call_tail = prove
 (WSIMPPAUX_list_mk_imp
   ([WSIMPPAUX_IH_TERM `prog:(A)wl_prog`
       `wl_call_env args1 ss (wl_dec_clock (s:(A,C,FFI)wl_state))`;
     `wl_evaluate (prog:(A)wl_prog, wl_call_env args1 ss (wl_dec_clock s)) =
      (r,s2:(A,C,FFI)wl_state)`;
     `gc_fun_const_ok (wl_state_gc_fun (s:(A,C,FFI)wl_state))`],
    WSIMPPAUX_SFC_TERM `r:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                       `s2:(A,C,FFI)wl_state`),
  REPEAT DISCH_TAC THEN MATCH_MP_TAC WSIMPPAUX_SFC_eq_imp_alt THEN
  EXISTS_TAC `wl_call_env args1 ss (wl_dec_clock (s:(A,C,FFI)wl_state))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WSIMPPAUX_call_state_consts];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts]]);;

let WSIMPPAUX_sc_tm =
  `wl_call_env args1 ss (wl_push_env (envs:((A)word_loc)spt#((A)word_loc)spt)
     (handler:(num#(A)wl_prog#num#num)option) (wl_dec_clock (s:(A,C,FFI)wl_state)))`;;

let WSIMPPAUX_call_result = prove
 (WSIMPPAUX_list_mk_imp
   ([WSIMPPAUX_IH_TERM `prog:(A)wl_prog` WSIMPPAUX_sc_tm;
     WSIMPPAUX_IH_TERM `ret_handler:(A)wl_prog`
       `wl_set_vars n (ys:((A)word_loc)list) (s1:(A,C,FFI)wl_state)`;
     mk_eq(mk_comb(`wl_evaluate:(A)wl_prog#(A,C,FFI)wl_state->((A)wl_result)option#(A,C,FFI)wl_state`,
                   mk_pair(`prog:(A)wl_prog`,WSIMPPAUX_sc_tm)),
           `(SOME (wl_Result (x:(A)word_loc) ys),s2:(A,C,FFI)wl_state)`);
     `wl_pop_env (s2:(A,C,FFI)wl_state) = SOME s1`;
     `wl_evaluate (ret_handler:(A)wl_prog, wl_set_vars n ys (s1:(A,C,FFI)wl_state)) =
      (r,s3)`;
     `gc_fun_const_ok (wl_state_gc_fun (s:(A,C,FFI)wl_state))`],
    WSIMPPAUX_SFC_TERM `r:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                       `s3:(A,C,FFI)wl_state`),
  DISCH_THEN(LABEL_TAC "ih1") THEN DISCH_THEN(LABEL_TAC "ih2") THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   (WSIMPPAUX_SFC_TERM `SOME (wl_Result (x:(A)word_loc) ys)` WSIMPPAUX_sc_tm
                       `s2:(A,C,FFI)wl_state`) MP_TAC THENL
   [USE_THEN "ih1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[WSIMPPAUX_call_state_consts] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wl_dec_clock (s:(A,C,FFI)wl_state)`; `s:(A,C,FFI)wl_state`;
                 `s2:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`;
                 `envs:((A)word_loc)spt#((A)word_loc)spt`;
                 `handler:(num#(A)wl_prog#num#num)option`] LIST_REL_call_Result) THEN
  ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_gc_fun (s1:(A,C,FFI)wl_state) = wl_state_gc_fun (s:(A,C,FFI)wl_state)`
  ASSUME_TAC THENL
   [IMP_RES_TAC pop_env_gc_fun THEN IMP_RES_TAC wl_evaluate_consts THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) =
                                 `wl_state_gc_fun (s2:(A,C,FFI)wl_state)`
                            then SUBST1_TAC(SYM th) else failwith "") THEN
    REWRITE_TAC[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts];
    ALL_TAC] THEN
  MATCH_MP_TAC WSIMPPAUX_SFC_trans_alt THEN
  EXISTS_TAC `wl_set_vars n ys (s1:(A,C,FFI)wl_state)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts];
    USE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts]]);;

let WSIMPPAUX_push_env_stack = prove
 (`!env h (s:(A,C,FFI)wl_state).
     (?f. wl_state_stack (wl_push_env env h s) = CONS f (wl_state_stack s)) /\
     (!x. h = SOME x ==>
          wl_state_handler (wl_push_env env h s) = LENGTH (wl_state_stack s))`,
  GEN_TAC THEN REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN PAIRARG_TAC THEN
  SIMP[option_DISTINCT] THEN MESON_TAC[]);;

let WSIMPPAUX_get_above_handler_cons = prove
 (`!(s1:(A,C,FFI)wl_state) (s:(A,C,FFI)wl_state) f.
     wl_state_stack s1 = CONS f (wl_state_stack s) /\
     wl_state_handler s1 = wl_state_handler s /\
     wl_state_handler s < LENGTH (wl_state_stack s) ==>
     get_above_handler s1 = get_above_handler s`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[get_above_handler_def; LENGTH] THEN
  SUBGOAL_THEN `SUC (LENGTH (wl_state_stack (s:(A,C,FFI)wl_state))) -
                (wl_state_handler s + 1) =
                SUC (LENGTH (wl_state_stack s) - (wl_state_handler s + 1))`
  SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]);;

let WSIMPPAUX_sc_none_tm =
  vsubst [`NONE:(num#(A)wl_prog#num#num)option`,`handler:(num#(A)wl_prog#num#num)option`]
    WSIMPPAUX_sc_tm;;

let WSIMPPAUX_call_exc_none = prove
 (WSIMPPAUX_list_mk_imp
   ([WSIMPPAUX_IH_TERM `prog:(A)wl_prog` WSIMPPAUX_sc_none_tm;
     mk_eq(mk_comb(`wl_evaluate:(A)wl_prog#(A,C,FFI)wl_state->((A)wl_result)option#(A,C,FFI)wl_state`,
                   mk_pair(`prog:(A)wl_prog`,WSIMPPAUX_sc_none_tm)),
           `(SOME (wl_Exception (x:(A)word_loc) y),s2:(A,C,FFI)wl_state)`);
     `gc_fun_const_ok (wl_state_gc_fun (s:(A,C,FFI)wl_state))`],
    WSIMPPAUX_SFC_TERM `SOME (wl_Exception (x:(A)word_loc) y)` `s:(A,C,FFI)wl_state`
                       `s2:(A,C,FFI)wl_state`),
  DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   (WSIMPPAUX_SFC_TERM `SOME (wl_Exception (x:(A)word_loc) y)` WSIMPPAUX_sc_none_tm
                       `s2:(A,C,FFI)wl_state`) MP_TAC THENL
   [USE_THEN "ih1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`;
                 `NONE:(num#(A)wl_prog#num#num)option`;
                 `wl_dec_clock (s:(A,C,FFI)wl_state)`] WSIMPPAUX_push_env_stack) THEN
  REWRITE_TAC[option_DISTINCT; WSIMPPAUX_call_state_consts] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_handler (wl_push_env (envs:((A)word_loc)spt#((A)word_loc)spt)
                  NONE (wl_dec_clock (s:(A,C,FFI)wl_state))) = wl_state_handler s`
  ASSUME_TAC THENL
   [MESON_TAC[WSIMPPAUX_push_env_consts; WSIMPPAUX_call_state_consts]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sfc") THEN DISCH_TAC THEN
  REMOVE_THEN "sfc" MP_TAC THEN
  ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts; LENGTH] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `ALL2 sf_gc_consts
       (LASTN (wl_state_handler (s:(A,C,FFI)wl_state)) (CONS f (wl_state_stack s)))
       (wl_state_stack (s2:(A,C,FFI)wl_state))` THEN
    ASM_SIMP_TAC[LASTN_CONS; LT_IMP_LE];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WSIMPPAUX_get_above_handler_cons THEN
    EXISTS_TAC `f:(A)stack_frame` THEN
    ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts]]);;

let WSIMPPAUX_sc_some_tm =
  vsubst [`SOME (n':num,h:(A)wl_prog,l1':num,l2':num)`,
          `handler:(num#(A)wl_prog#num#num)option`] WSIMPPAUX_sc_tm;;

let WSIMPPAUX_call_exc_some = prove
 (WSIMPPAUX_list_mk_imp
   ([WSIMPPAUX_IH_TERM `prog:(A)wl_prog` WSIMPPAUX_sc_some_tm;
     WSIMPPAUX_IH_TERM `h:(A)wl_prog` `wl_set_var n' y (s2:(A,C,FFI)wl_state)`;
     mk_eq(mk_comb(`wl_evaluate:(A)wl_prog#(A,C,FFI)wl_state->((A)wl_result)option#(A,C,FFI)wl_state`,
                   mk_pair(`prog:(A)wl_prog`,WSIMPPAUX_sc_some_tm)),
           `(SOME (wl_Exception (x:(A)word_loc) y),s2:(A,C,FFI)wl_state)`);
     `wl_evaluate (h:(A)wl_prog, wl_set_var n' y (s2:(A,C,FFI)wl_state)) = (r,s3)`;
     `gc_fun_const_ok (wl_state_gc_fun (s:(A,C,FFI)wl_state))`],
    WSIMPPAUX_SFC_TERM `r:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                       `s3:(A,C,FFI)wl_state`),
  DISCH_THEN(LABEL_TAC "ih1") THEN DISCH_THEN(LABEL_TAC "ih2") THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   (WSIMPPAUX_SFC_TERM `SOME (wl_Exception (x:(A)word_loc) y)` WSIMPPAUX_sc_some_tm
                       `s2:(A,C,FFI)wl_state`) MP_TAC THENL
   [USE_THEN "ih1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)wl_state`; WSIMPPAUX_sc_some_tm; `args1:((A)word_loc)list`;
                 `ss:num option`; `envs:((A)word_loc)spt#((A)word_loc)spt`;
                 `n':num`; `h:(A)wl_prog`; `l1':num`; `l2':num`]
                call_env_push_env_dec_clock_handler_length) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_handler (s2:(A,C,FFI)wl_state) = wl_state_handler (s:(A,C,FFI)wl_state)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC get_above_handler_call_env_push_env_dec_clock THEN
    MAP_EVERY EXISTS_TAC [WSIMPPAUX_sc_some_tm; `args1:((A)word_loc)list`; `ss:num option`;
      `envs:((A)word_loc)spt#((A)word_loc)spt`; `n':num`; `h:(A)wl_prog`; `l1':num`;
      `l2':num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL2 sf_gc_consts (wl_state_stack (s:(A,C,FFI)wl_state))
                                  (wl_state_stack (s2:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`envs:((A)word_loc)spt#((A)word_loc)spt`;
                   `SOME (n':num,h:(A)wl_prog,l1':num,l2':num)`;
                   `wl_dec_clock (s:(A,C,FFI)wl_state)`] WSIMPPAUX_push_env_stack) THEN
    REWRITE_TAC[option_INJ; WSIMPPAUX_call_state_consts] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `(n':num,h:(A)wl_prog,l1':num,l2':num)`) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `ALL2 sf_gc_consts
       (LASTN (wl_state_handler (wl_call_env args1 ss
          (wl_push_env (envs:((A)word_loc)spt#((A)word_loc)spt)
             (SOME (n':num,h:(A)wl_prog,l1':num,l2':num))
             (wl_dec_clock (s:(A,C,FFI)wl_state)))))
          (wl_state_stack (wl_call_env args1 ss
          (wl_push_env envs (SOME (n',h,l1',l2')) (wl_dec_clock s)))))
       (wl_state_stack (s2:(A,C,FFI)wl_state))` THEN
    ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts; LASTN_LENGTH_CONS];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_state_gc_fun (s2:(A,C,FFI)wl_state) = wl_state_gc_fun (s:(A,C,FFI)wl_state)`
  ASSUME_TAC THENL
   [IMP_RES_TAC wl_evaluate_consts THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) =
                                 `wl_state_gc_fun (s2:(A,C,FFI)wl_state)`
                            then SUBST1_TAC(SYM th) else failwith "") THEN
    REWRITE_TAC[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts];
    ALL_TAC] THEN
  MATCH_MP_TAC WSIMPPAUX_SFC_trans_alt THEN
  EXISTS_TAC `wl_set_var n' y (s2:(A,C,FFI)wl_state)` THEN CONJ_TAC THENL
   [REWRITE_TAC[WSIMPPAUX_call_state_consts] THEN ASM_MESON_TAC[];
    USE_THEN "ih2" MATCH_MP_TAC THEN REWRITE_TAC[WSIMPPAUX_call_state_consts] THEN
    ASM_MESON_TAC[]]);;

(* a leaf of the Call case: the lemma's antecedents number ks (evaluations) *)
(* are matched against assumptions, the others are assumptions or follow  *)
(* from the induction hypotheses (labelled iht ihr ihh ihc)               *)

let WSIMPPAUX_REORDER ks th =
  let rec ants t = if is_imp t then let a,b = dest_imp t in a :: ants b else [] in
  let hs = ants (concl th) in
  let es = map (fun k -> el k hs) ks in
  let others = filter (fun h -> not (mem h es)) hs in
  let conj_th = ASSUME (list_mk_conj others) in
  let lookup h = if mem h es then ASSUME h
                 else find (fun c -> concl c = h) (CONJUNCTS conj_th) in
  let res = rev_itlist (fun h acc -> MP acc (lookup h)) hs th in
  GEN_ALL (itlist DISCH es (DISCH (list_mk_conj others) res));;

let WSIMPPAUX_LEAF_TAC ks lemma : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let th0 = WSIMPPAUX_REORDER ks lemma in
  let th = rev_itlist (fun _ th -> tryfind (fun a -> MATCH_MP th a) asms) ks th0 in
  (MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN
   FIRST [FIRST_ASSUM ACCEPT_TAC;
          FIRST (map (fun l -> USE_THEN l (fun th -> MATCH_MP_TAC th THEN ASM_MESON_TAC[]))
                     ["iht";"ihr";"ihh";"ihc"])]) g;;

let evaluate_sf_gc_consts = prove
 (CASE_TERM
  `!p (s:(A,C,FFI)wl_state) s' res.
     wl_evaluate (p,s) = (res,s') /\ gc_fun_const_ok (wl_state_gc_fun s) ==>
     match res with
       NONE ->
         ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
         wl_state_handler s' = wl_state_handler s
     | SOME (wl_Result _ _) ->
         ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
         wl_state_handler s' = wl_state_handler s
     | SOME (wl_Exception _ _) ->
         wl_state_handler s < LENGTH (wl_state_stack s) ==>
         ALL2 sf_gc_consts (LASTN (wl_state_handler s) (wl_state_stack s))
                           (wl_state_stack s') /\
         wl_state_handler s' = get_above_handler s
     | SOME (wordSem_Break _) ->
         ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
         wl_state_handler s' = wl_state_handler s
     | SOME (wordSem_Continue _) ->
         ALL2 sf_gc_consts (wl_state_stack s) (wl_state_stack s') /\
         wl_state_handler s' = wl_state_handler s
     | _ -> T`,
  WSIMPPAUX_EVAL_IND_TAC THEN REPEAT CONJ_TAC THENL
   [(* Skip *) WSIMPPAUX_CLAUSE_TAC [];
    (* Alloc *)
    WSIMPPAUX_CLAUSE_TAC [wl_alloc_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC WSIMPPAUX_alloc_stack THEN ASM_MESON_TAC[];
    (* StoreConsts *) WSIMPPAUX_CLAUSE_TAC [];
    (* Move *) WSIMPPAUX_CLAUSE_TAC [];
    (* Inst *)
    WSIMPPAUX_CLAUSE_TAC [] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP inst_const_full) THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[WSIMPPAUX_ALL2_sf_refl];
    (* Assign *) WSIMPPAUX_CLAUSE_TAC [];
    (* Get *) WSIMPPAUX_CLAUSE_TAC [];
    (* Set *) WSIMPPAUX_CLAUSE_TAC [];
    (* OpCurrHeap *) WSIMPPAUX_CLAUSE_TAC [];
    (* Store *)
    WSIMPPAUX_CLAUSE_TAC [] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
    FS[wl_mem_store_def; COND_CASE_EQ] THEN RVEQ_TAC THEN SIMP WSIMPPAUX_easy_rws;
    (* Tick *) WSIMPPAUX_CLAUSE_TAC [];
    (* MustTerminate *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    COND_CASES_TAC THENL [WSIMPPAUX_KILL_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN PAIRARG_TAC THEN
    COND_CASES_TAC THENL [WSIMPPAUX_KILL_TAC; ALL_TAC] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP
      (ASSUME `~(wl_state_termdep (s:(A,C,FFI)wl_state) = 0)`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`s1:(A,C,FFI)wl_state`; `res:((A)wl_result)option`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [SIMP[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN MATCH_MP_TAC WSIMPPAUX_SFC_eq THEN
    SIMP[];
    (* Seq *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    MP_TAC(ISPEC `wl_evaluate (c1, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
      (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC WSIMPPAUX_SFC_trans_alt THEN
      EXISTS_TAC `s1:(A,C,FFI)wl_state` THEN CONJ_TAC THENL
       [REMOVE_THEN "ih1" (MP_TAC o SPECL [`s1:(A,C,FFI)wl_state`;
                                           `r1:((A)wl_result)option`]) THEN
        ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
        REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,C,FFI)wl_state`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC evaluate_gc_fun_const_ok THEN ASM_MESON_TAC[]];
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* Return *) WSIMPPAUX_CLAUSE_TAC [];
    (* Raise *)
    WSIMPPAUX_CLAUSE_TAC [] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WSIMPPAUX_jump_exc) THEN
    ASM_REWRITE_TAC[WSIMPPAUX_ALL2_sf_refl];
    (* Break *) WSIMPPAUX_CLAUSE_TAC [];
    (* Continue *) WSIMPPAUX_CLAUSE_TAC [];
    (* If *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    WSIMPPAUX_CLAUSE_TAC [] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN WSIMPPAUX_IH_TAC;
    (* Loop *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihc")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    CASES_ON `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THENL
     [WSIMPPAUX_KILL_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_stack (a:(A,C,FFI)wl_state) = wl_state_stack (s:(A,C,FFI)wl_state) /\
                  wl_state_handler a = wl_state_handler s /\
                  wl_state_gc_fun a = wl_state_gc_fun s` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_state_const) THEN
      ASM_REWRITE_TAC[] THEN SIMP[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `wl_evaluate (c, a:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
      (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN (WSIMPPAUX_SFC_TERM `r1:((A)wl_result)option` `s:(A,C,FFI)wl_state`
                                     `s1:(A,C,FFI)wl_state`) ASSUME_TAC THENL
     [REMOVE_THEN "ihc" (MP_TAC o SPEC `a:(A,C,FFI)wl_state`) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`s1:(A,C,FFI)wl_state`; `r1:((A)wl_result)option`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN MATCH_MP_TAC WSIMPPAUX_SFC_eq THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_gc_fun (s1:(A,C,FFI)wl_state) = wl_state_gc_fun (s:(A,C,FFI)wl_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[wl_evaluate_consts]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [COND_CASES_TAC THENL [WSIMPPAUX_KILL_TAC; ALL_TAC] THEN
      REWRITE_TAC[wl_STOP_def] THEN DISCH_TAC THEN
      MATCH_MP_TAC WSIMPPAUX_SFC_trans_alt THEN
      EXISTS_TAC `wl_dec_clock (s1:(A,C,FFI)wl_state)` THEN CONJ_TAC THENL
       [REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN
        MATCH_MP_TAC WSIMPPAUX_SFC_unlabelled_alt THEN
        EXISTS_TAC `r1:((A)wl_result)option` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `wl_cont_loop (r1:((A)wl_result)option)` THEN
        CASES_ON `r1:((A)wl_result)option` THEN SIMP[] THEN
        CASES_ON `a':(A)wl_result` THEN SIMP[] THEN MESON_TAC[];
        REMOVE_THEN "ihl" (MP_TAC o SPECL [`a:(A,C,FFI)wl_state`; `r1:((A)wl_result)option`;
                                           `s1:(A,C,FFI)wl_state`]) THEN
        ASM_REWRITE_TAC[wl_STOP_def] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[wl_dec_clock_def] THEN SIMP[]];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [RVEQ_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
      CASES_ON `wl_cut_state (exit_names,LN) (s1:(A,C,FFI)wl_state)` THEN
      CASE_REWRITE_TAC[] THENL [WSIMPPAUX_KILL_TAC; ALL_TAC] THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_state_const) THEN
      ASM_REWRITE_TAC[] THEN SIMP_NOASM[] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      MATCH_MP_TAC WSIMPPAUX_SFC_exit_loop THEN ASM_REWRITE_TAC[]];
    (* LocValue *) WSIMPPAUX_CLAUSE_TAC [];
    (* Install *) WSIMPPAUX_CLAUSE_TAC [];
    (* CodeBufferWrite *) WSIMPPAUX_CLAUSE_TAC [];
    (* DataBufferWrite *) WSIMPPAUX_CLAUSE_TAC [];
    (* FFI *) WSIMPPAUX_CLAUSE_TAC [];
    (* ShareInst *)
    REPEAT GEN_TAC THEN CASES_ON `op:memop` THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    WSIMPPAUX_LOOP_TAC WSIMPPAUX_share_rws;
    (* Call *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> let ths = CONJUNCTS th in
      LABEL_TAC "iht" (el 0 ths) THEN LABEL_TAC "ihr" (el 1 ths) THEN
      LABEL_TAC "ihh" (el 2 ths) THEN LABEL_TAC "ihc" (el 3 ths)) THEN
    WSIMPPAUX_CLAUSE_TAC [] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      WSIMPPAUX_LEAF_TAC [1] WSIMPPAUX_call_tail;
      DISCH_TAC THEN WSIMPPAUX_LEAF_TAC [2;4] WSIMPPAUX_call_result;
      STRIP_TAC THEN RVEQ_TAC THEN WSIMPPAUX_LEAF_TAC [1] WSIMPPAUX_call_exc_none;
      DISCH_TAC THEN WSIMPPAUX_LEAF_TAC [2;3] WSIMPPAUX_call_exc_some]]);;

let evaluate_drop_consts_1 = prove
 (`!vs (rest:B) (s:(A,C,FFI)wl_state).
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) ==>
     wl_evaluate (drop_consts cs vs,s) = (NONE,s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[drop_consts_def] THENL
   [REWRITE_TAC[wl_evaluate_def]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN CASE_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[evaluate_SmartSeq; wl_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_exp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_set_var_def; PAIR_EQ] THEN
  SUBGOAL_THEN `insert h (wl_Word a) (wl_state_locals (s:(A,C,FFI)wl_state)) =
                wl_state_locals s` SUBST1_TAC THENL
   [MATCH_MP_TAC insert_unchanged THEN ASM_MESON_TAC[wl_get_var_def];
    REWRITE_TAC[wl_state_component_equality] THEN SIMP[]]);;

let evaluate_drop_consts = prove
 (`(!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) ==>
   wl_evaluate (SmartSeq (drop_consts cs vs) p,s:(A,C,FFI)wl_state) =
   wl_evaluate (p,s)`,
  DISCH_TAC THEN REWRITE_TAC[evaluate_SmartSeq] THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  MP_TAC(ISPECL [`vs:num list`; `ARB:bool`; `s:(A,C,FFI)wl_state`]
         evaluate_drop_consts_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [evaluate_drop_consts];;

(* HOL4: lookup_FOLDR_delete [local] *)

let word_simpProof_lookup_FOLDR_delete = prove
 (`!l (m:A spt) v w.
     lookup v (ITLIST delete l m) = SOME w ==> lookup v m = SOME w /\ ~MEM v l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MEM] THEN
  REWRITE_TAC[lookup_delete] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let get_var_set_vars_ignore = prove
 (`!xs l (m:(A,C,FFI)wl_state).
     ~MEM v xs ==> wl_get_var v (wl_set_vars xs l m) = wl_get_var v m`,
  SIMP[wl_set_vars_def; wl_get_var_def] THEN
  SUBGOAL_THEN `!xs (l:((A)word_loc)list) t.
                  ~MEM v xs ==> lookup v (alist_insert xs l t) = lookup v t`
  (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_insert_def; MEM; DE_MORGAN_THM] THEN
  GEN_TAC THEN CASES_ON `l:((A)word_loc)list` THEN
  REWRITE_TAC[alist_insert_def; lookup_insert] THEN ASM_MESON_TAC[]);;

(* evaluate_const_fp_loop: tactics and helpers *)

(* the constants known after a state update *)

let WSIMPPAUX_CSI_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FS[wl_get_var_def; wl_set_var_def; wl_unset_var_def; wl_set_vars_def; wl_set_store_def;
     wl_dec_clock_def; wl_flush_state_def; wl_mem_store_def;
     lookup_insert; lookup_delete; COND_CASE_EQ] THEN
  RVEQ_TAC THEN FS[] THEN ASM_MESON_TAC[];;

(* split an evaluation (case ...) = (NONE,s') in the antecedent of the goal  *)
(* (rewriting with rws on the way); the errors close, the remaining cases go *)
(* to WSIMPPAUX_CSI_TAC                                                      *)

let WSIMPPAUX_CFL_EVAL_TAC rws : tactic =
  REPEAT ((REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN NO_TAC) ORELSE
          CHANGED_TAC (REWRITE_TAC rws) ORELSE
          WSIMPPAUX_SHMEM_CASE_TAC ORELSE WSIMPPAUX_ANT_CASE_TAC ORELSE
          CHANGED_TAC (CONV_TAC(TOP_DEPTH_CONV let_CONV)) ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN WSIMPPAUX_CSI_TAC;;

let WSIMPPAUX_CFL_INTRO_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[const_fp_loop_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV);;

let WSIMPPAUX_EVAL_ASM_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "wl_evaluate"
                              with _ -> false)) (lhs(concl th))));;

(* a clause where const_fp_loop keeps the program *)

let WSIMPPAUX_CFL_SIMPLE_TAC rws : tactic =
  WSIMPPAUX_CFL_INTRO_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN RVEQ_TAC THEN WSIMPPAUX_EVAL_ASM_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN WSIMPPAUX_CFL_EVAL_TAC rws;;

(* a clause where const_fp_loop folds the constants of an expression *)

let WSIMPPAUX_CFL_EXP_TAC rws : tactic =
  WSIMPPAUX_CFL_INTRO_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_pair(rhs(concl th))
     then (SUBST1_TAC(SYM th) THEN ASSUME_TAC th) else failwith "") THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_SIMP_TAC[const_fp_exp_word_exp]; ALL_TAC] THEN
  DISCH_TAC THEN RVEQ_TAC THEN WSIMPPAUX_EVAL_ASM_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN WSIMPPAUX_CFL_EVAL_TAC rws;;

(* the constants after a cut of the locals (FFI, Install) and after an Alloc *)

let WSIMPPAUX_cut_env_lookup = prove
 (`!names (l:(A)spt) env v x.
     wl_cut_env names l = SOME env /\ lookup v l = SOME x /\
     ~(lookup v (all_names names) = NONE) ==> lookup v env = SOME x`,
  REWRITE_TAC[FORALL_PAIR_THM; all_names_def; wl_cut_env_def; cut_envs_def;
              cut_names_def] THEN
  REPEAT GEN_TAC THEN REPEAT (COND_CASES_TAC THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[lookup_union; lookup_inter] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup v (p1:num_set)` THEN CASES_ON `lookup v (p2:num_set)` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[]);;

let WSIMPPAUX_alloc_locals = prove
 (`!(s:(A,C,FFI)wl_state) envs names w s1 s2 v c.
     gc_fun_const_ok (wl_state_gc_fun s) /\
     cut_envs names (wl_state_locals s) = SOME envs /\
     wl_gc (wl_push_env envs NONE (wl_set_store AllocSize (wl_Word w) s)) = SOME s1 /\
     wl_pop_env s1 = SOME s2 /\
     wl_get_var v s = SOME (wl_Word c) /\ is_gc_const c /\
     ~(lookup v (all_names names) = NONE)
     ==> wl_get_var v s2 = SOME (wl_Word c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`wl_set_store AllocSize (wl_Word w) (s:(A,C,FFI)wl_state)`;
                 `wl_push_env envs NONE
                    (wl_set_store AllocSize (wl_Word w) (s:(A,C,FFI)wl_state))`;
                 `s1:(A,C,FFI)wl_state`; `s2:(A,C,FFI)wl_state`;
                 `envs:((A)word_loc)spt#((A)word_loc)spt`; `names:cutsets`;
                 `NONE:(num#(A)wl_prog#num#num)option`] push_env_pop_env_locals_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP[wl_set_store_def] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC gc_sf_gc_consts THEN
      ASM_REWRITE_TAC[WSIMPPAUX_push_env_consts; wl_set_store_def] THEN SIMP[]];
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[is_gc_word_const_def] THEN
    UNDISCH_TAC `wl_get_var v (s:(A,C,FFI)wl_state) = SOME (wl_Word c)` THEN
    SIMP[wl_get_var_def; wl_set_store_def]]);;

(* the two kinds of branches of the If clause *)

let WSIMPPAUX_IF_OTHER_TAC : tactic =
  MP_TAC(ISPEC `const_fp_loop p1 (cs:(A word)spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)wl_prog` (X_CHOOSE_THEN `c1:(A word)spt` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `const_fp_loop p2 (cs:(A word)spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)wl_prog` (X_CHOOSE_THEN `c2:(A word)spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  UNDISCH_TAC `wl_evaluate (wl_If cmp lhs rhs p1 p2,s:(A,C,FFI)wl_state) = (res,s')` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REPEAT ((REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
           REWRITE_TAC[option_DISTINCT] THEN NO_TAC) ORELSE WSIMPPAUX_ANT_CASE_TAC) THEN
  DISCH_TAC THEN ASM_MESON_TAC[lookup_inter_eq_some];;

let WSIMPPAUX_IF_BOTH_TAC : tactic =
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  SUBGOAL_THEN `wl_get_var lhs (s:(A,C,FFI)wl_state) = SOME (wl_Word (a:A word))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_var_imm rhs (s:(A,C,FFI)wl_state) = SOME (wl_Word (a':A word))`
  ASSUME_TAC THENL [ASM_MESON_TAC[get_var_imm_cs_imp_get_var_imm]; ALL_TAC] THEN
  UNDISCH_TAC `wl_evaluate (wl_If cmp lhs rhs p1 p2,s:(A,C,FFI)wl_state) = (res,s')` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_cmp_Word_Word] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN REPEAT DISCH_TAC THENL
   [REMOVE_THEN "ie" MP_TAC; REMOVE_THEN "if" MP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`p':(A)wl_prog`; `cs':(A word)spt`; `s:(A,C,FFI)wl_state`;
                             `res:((A)wl_result)option`; `s':(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[];;

(* case split on the variables of the given types in the goal *)

let WSIMPPAUX_SPLIT_VARS_TAC tys : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> match type_of v with Tyapp(n,_) -> mem n tys | _ -> false)
                  (frees w) in
  match vs with [] -> failwith "WSIMPPAUX_SPLIT_VARS_TAC" | v::_ -> CASES_ON v g;;

(* the Inst case of evaluate_const_fp_loop: the constants that survive *)
(* const_fp_inst_cs are those of the registers the instruction keeps   *)

let WSIMPPAUX_inst_cs = prove
 (`!i (s:(A,C,FFI)wl_state) s' cs v w.
     wl_inst i s = SOME s' ==> lookup v (const_fp_inst_cs i cs) = SOME w ==>
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) ==>
     wl_get_var v s' = SOME (wl_Word w)`,
  REPEAT GEN_TAC THEN
  REPEAT (WSIMPPAUX_SPLIT_VARS_TAC ["inst";"asm_arith";"memop";"addr";"fp"]) THEN
  REWRITE_TAC[const_fp_inst_cs_def] THEN REWRITE_TAC[wl_inst_def] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[wl_assign_def] THEN
  REPEAT (CHANGED_TAC (REWRITE_TAC[option_DISTINCT]) ORELSE WSIMPPAUX_ANT_CASE_TAC ORELSE
          CHANGED_TAC (CONV_TAC(TOP_DEPTH_CONV let_CONV)) ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT STRIP_TAC THEN
  FS[wl_get_var_def; wl_set_var_def; wl_set_fp_var_def; wl_mem_store_def;
     lookup_insert; lookup_delete; COND_CASE_EQ] THEN
  RVEQ_TAC THEN FS[] THEN ASM_MESON_TAC[]);;

(* the Call clause *)

let WSIMPPAUX_DROP_TAC : tactic =
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP evaluate_drop_consts th]);;

let WSIMPPAUX_call_NONE_res = prove
 (`!dest args handler (s:(A,C,FFI)wl_state) res s'.
     wl_evaluate (wl_Call NONE dest args handler,s) = (res,s') ==> ~(res = NONE)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REPEAT ((REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
           REWRITE_TAC[option_DISTINCT] THEN NO_TAC) ORELSE WSIMPPAUX_ANT_CASE_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN DISCH_TAC THEN RVEQ_TAC THEN
  FS[wl_bad_fun_return_def]);;

let WSIMPPAUX_cfl_call_cs = prove
 (`!(s:(A,C,FFI)wl_state) envs names args1 ss prog x ys s2 s1 n cs v w.
     cut_envs names (wl_state_locals s) = SOME envs /\
     wl_evaluate (prog,wl_call_env args1 ss
                         (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
                            (wl_dec_clock s))) =
       (SOME (wl_Result x ys),s2) /\
     wl_pop_env s2 = SOME s1 /\
     gc_fun_const_ok (wl_state_gc_fun s) /\
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) /\
     lookup v (ITLIST delete n (filter_v is_gc_const (inter cs (all_names names)))) =
       SOME w
     ==> wl_get_var v (wl_set_vars n ys s1) = SOME (wl_Word w)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP word_simpProof_lookup_FOLDR_delete) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP lookup_filter_v_SOME) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP lookup_filter_v_SOME_imp) THEN
  REWRITE_TAC[lookup_inter_EQ] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[get_var_set_vars_ignore] THEN
  MP_TAC(ISPECL [`wl_dec_clock (s:(A,C,FFI)wl_state)`;
                 `wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
                    (wl_dec_clock (s:(A,C,FFI)wl_state))`;
                 `s2:(A,C,FFI)wl_state`; `s1:(A,C,FFI)wl_state`;
                 `envs:((A)word_loc)spt#((A)word_loc)spt`; `names:cutsets`;
                 `NONE:(num#(A)wl_prog#num#num)option`] push_env_pop_env_locals_thm) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP[wl_dec_clock_def] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`prog:(A)wl_prog`;
                     `wl_call_env args1 ss (wl_push_env envs
                        (NONE:(num#(A)wl_prog#num#num)option)
                        (wl_dec_clock (s:(A,C,FFI)wl_state)))`;
                     `s2:(A,C,FFI)wl_state`;
                     `SOME (wl_Result (x:(A)word_loc) ys)`] evaluate_sf_gc_consts) THEN
      ASM_REWRITE_TAC[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts] THEN
      CASE_REWRITE_TAC[] THEN SIMP_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[is_gc_word_const_def] THEN
    REWRITE_TAC[wl_get_var_def; wl_dec_clock_def] THEN SIMP[] THEN
    ASM_MESON_TAC[wl_get_var_def]]);;

(* the induction hypothesis of evaluate_const_fp_loop for (p,cs), as a term *)

let WSIMPPAUX_cfl_goal =
 `!p cs p' cs' (s:(A,C,FFI)wl_state) res s'.
     wl_evaluate (p,s) = (res,s') /\
     const_fp_loop p cs = (p',cs') /\
     gc_fun_const_ok (wl_state_gc_fun s) /\
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) ==>
     wl_evaluate (p',s) = (res,s') /\
     (res = NONE ==>
      (!v w. lookup v cs' = SOME w ==> wl_get_var v s' = SOME (wl_Word w)))`;;

let WSIMPPAUX_CFL_P p cs =
  let vs,body = strip_forall WSIMPPAUX_cfl_goal in
  let p0 = el 0 vs and cs0 = el 1 vs in
  list_mk_forall(tl(tl vs), vsubst [p,p0; cs,cs0] body);;

let WSIMPPAUX_cs1_tm =
  `ITLIST delete n (filter_v is_gc_const (inter (cs:(A word)spt) (all_names (names:cutsets))))`;;

let WSIMPPAUX_cfl_call_leaf = prove
 (WSIMPPAUX_list_mk_imp
   ([`wl_evaluate (prog,wl_call_env args1 ss
         (wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
            (wl_dec_clock (s:(A,C,FFI)wl_state)))) =
      (SOME (wl_Result (x:(A)word_loc) ys),s2)`;
     `wl_evaluate (rh:(A)wl_prog,wl_set_vars n ys (s1:(A,C,FFI)wl_state)) = (r,s3)`;
     WSIMPPAUX_CFL_P `rh:(A)wl_prog` WSIMPPAUX_cs1_tm;
     `cut_envs names (wl_state_locals (s:(A,C,FFI)wl_state)) = SOME envs`;
     `wl_pop_env (s2:(A,C,FFI)wl_state) = SOME s1`;
     mk_eq(mk_comb(`const_fp_loop (rh:(A)wl_prog)`,WSIMPPAUX_cs1_tm),
           `(rh':(A)wl_prog,c2:(A word)spt)`);
     `gc_fun_const_ok (wl_state_gc_fun (s:(A,C,FFI)wl_state))`;
     `!v w. lookup v cs = SOME w ==> wl_get_var v (s:(A,C,FFI)wl_state) = SOME (wl_Word w)`],
    `wl_evaluate (rh',wl_set_vars n ys (s1:(A,C,FFI)wl_state)) = (r,s3) /\
     (r = NONE ==> (!v w. lookup v c2 = SOME w ==>
                          wl_get_var v s3 = SOME (wl_Word w)))`),
  DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT DISCH_TAC THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[WSIMPPAUX_call_state_consts] THEN
    IMP_RES_TAC pop_env_gc_fun THEN IMP_RES_TAC wl_evaluate_consts THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) =
                                 `wl_state_gc_fun (s2:(A,C,FFI)wl_state)`
                            then SUBST1_TAC(SYM th) else failwith "") THEN
    REWRITE_TAC[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WSIMPPAUX_cfl_call_cs THEN
    MAP_EVERY EXISTS_TAC [`s:(A,C,FFI)wl_state`; `envs:((A)word_loc)spt#((A)word_loc)spt`;
      `names:cutsets`; `args1:((A)word_loc)list`; `ss:num option`; `prog:(A)wl_prog`;
      `x:(A)word_loc`; `s2:(A,C,FFI)wl_state`; `cs:(A word)spt`] THEN
    ASM_REWRITE_TAC[]]);;
let WSIMPPAUX_cfl_cases = [
  (* 1 Move *)
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[const_fp_loop_def] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN RVEQ_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Move pri (moves:(num#num)list),s:(A,C,FFI)wl_state) =
               (NONE,s')` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  CASES_ON `wl_get_vars (MAP SND (moves:(num#num)list)) (s:(A,C,FFI)wl_state)` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`v:num`; `moves:(num#num)list`; `cs:(A word)spt`]
                lookup_const_fp_move_cs) THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)wl_state`; `s':(A,C,FFI)wl_state`; `moves:(num#num)list`;
                 `a:((A)word_loc)list`; `v:num`] get_var_move_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  CASE_TAC THEN ASM_MESON_TAC[];
  (* 2 Inst *)
  WSIMPPAUX_CFL_INTRO_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN RVEQ_TAC THEN WSIMPPAUX_EVAL_ASM_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CASES_ON `wl_inst i (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WSIMPPAUX_inst_cs) THEN ASM_MESON_TAC[];
  (* 3 Assign *)
  WSIMPPAUX_CFL_INTRO_TAC THEN
  SUBGOAL_THEN `wl_evaluate (wl_Assign v (const_fp_exp e cs),s:(A,C,FFI)wl_state) =
                (res,s')` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_pair(rhs(concl th)))) THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_SIMP_TAC[const_fp_exp_word_exp];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. const_fp_exp e cs = wl_Const c ==>
                    wl_word_exp (s:(A,C,FFI)wl_state) e = SOME (wl_Word c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC const_fp_exp_word_exp_const THEN
    EXISTS_TAC `cs:(A word)spt` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `const_fp_exp e (cs:(A word)spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN RVEQ_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Assign v e,s:(A,C,FFI)wl_state) = (NONE,s')` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  CASES_ON `wl_word_exp (s:(A,C,FFI)wl_state) e` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN STRIP_TAC THEN RVEQ_TAC THEN
  WSIMPPAUX_CSI_TAC;
  (* 4 Get *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 5 OpCurrHeap *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 6 MustTerminate *)
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  WSIMPPAUX_CFL_INTRO_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `wl_evaluate (MustTerminate p,s:(A,C,FFI)wl_state) = (res,s')` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `wl_evaluate (p,wl_state_clock_fupd (K (MustTerminate_limit (:A)))
                  (wl_state_termdep_fupd (K (wl_state_termdep s - 1))
                     (s:(A,C,FFI)wl_state)))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
    (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`p'':(A)wl_prog`; `cs':(A word)spt`;
    `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
       (wl_state_termdep_fupd (K (wl_state_termdep s - 1)) (s:(A,C,FFI)wl_state))`;
    `r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN SIMP[wl_get_var_def]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN REWRITE_TAC[] THEN
  SIMP[wl_get_var_def];
  (* 7 Seq *)
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih1")) THEN
  WSIMPPAUX_CFL_INTRO_TAC THEN
  MP_TAC(ISPEC `const_fp_loop p1 (cs:(A word)spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)wl_prog` (X_CHOOSE_THEN `c1:(A word)spt` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `const_fp_loop p2 (c1:(A word)spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)wl_prog` (X_CHOOSE_THEN `c2:(A word)spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPEC `wl_evaluate (p1, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
    (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`q1:(A)wl_prog`; `c1:(A word)spt`;
    `s:(A,C,FFI)wl_state`; `r1:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Seq p1 p2,s:(A,C,FFI)wl_state) = (res,s')` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`q1:(A)wl_prog`; `c1:(A word)spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`q2:(A)wl_prog`; `c2:(A word)spt`; `t1:(A,C,FFI)wl_state`;
                               `res:((A)wl_result)option`; `s':(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC evaluate_gc_fun_const_ok THEN ASM_MESON_TAC[];
                      ASM_MESON_TAC[]];
      SIMP_TAC[]];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]];
  (* 8 If *)
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    MAP_EVERY (fun (l,t) -> LABEL_TAC l t) (zip ["ia";"ib";"ic";"id";"ie";"if"] ths)) THEN
  WSIMPPAUX_CFL_INTRO_TAC THEN
  CASES_ON `lookup lhs (cs:(A word)spt)` THEN
  CASES_ON `get_var_imm_cs rhs (cs:(A word)spt)` THEN CASE_REWRITE_TAC[] THENL
   [WSIMPPAUX_IF_OTHER_TAC; WSIMPPAUX_IF_OTHER_TAC; WSIMPPAUX_IF_OTHER_TAC;
    WSIMPPAUX_IF_BOTH_TAC];
  (* 9 Call *)
  MATCH_MP_TAC option_INDUCT THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `n:num list` THEN
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `names:cutsets` THEN
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `rh:(A)wl_prog` THEN
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `l1:num` THEN
    X_GEN_TAC `l2:num`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN WSIMPPAUX_CFL_INTRO_TAC THEN
  CASE_REWRITE_TAC[] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN WSIMPPAUX_DROP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WSIMPPAUX_call_NONE_res) THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN WSIMPPAUX_DROP_TAC THEN
    ASM_REWRITE_TAC[lookup_rwts; option_DISTINCT]] THEN
  RVEQ_TAC THEN
  MP_TAC(ISPEC (mk_comb(`const_fp_loop (rh:(A)wl_prog)`,WSIMPPAUX_cs1_tm)) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `rh':(A)wl_prog` (X_CHOOSE_THEN `c2:(A word)spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  WSIMPPAUX_DROP_TAC THEN
  USE_THEN "ih" (MP_TAC o SPECL [`n:num list`; `names:cutsets`; `l1:num`; `l2:num`;
                                 `rh:(A)wl_prog`; WSIMPPAUX_cs1_tm]) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Call (SOME (n,names,rh,l1,l2)) dest args NONE,
                            s:(A,C,FFI)wl_state) = (res,s')` THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[add_ret_loc_def] THEN
  REPEAT ((REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
           REWRITE_TAC[option_DISTINCT] THEN NO_TAC) ORELSE WSIMPPAUX_ANT_CASE_TAC) THEN
  DISCH_TAC THEN WSIMPPAUX_LEAF_TAC [0;1;5] WSIMPPAUX_cfl_call_leaf;
  (* 10 FFI *)
  WSIMPPAUX_CFL_INTRO_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[evaluate_drop_consts] THEN
  DISCH_TAC THEN RVEQ_TAC THEN WSIMPPAUX_EVAL_ASM_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REPEAT ((REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN NO_TAC) ORELSE
          WSIMPPAUX_ANT_CASE_TAC ORELSE
          CHANGED_TAC (CONV_TAC(TOP_DEPTH_CONV let_CONV))) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_inter_EQ] THEN STRIP_TAC THEN
  SIMP[wl_get_var_def] THEN MATCH_MP_TAC WSIMPPAUX_cut_env_lookup THEN
  EXISTS_TAC `names:cutsets` THEN EXISTS_TAC `wl_state_locals (s:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[wl_get_var_def];
  (* 11 LocValue *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 12 Alloc *)
  WSIMPPAUX_CFL_INTRO_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[evaluate_drop_consts] THEN
  DISCH_TAC THEN RVEQ_TAC THEN WSIMPPAUX_EVAL_ASM_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN REWRITE_TAC[wl_alloc_def] THEN
  REPEAT ((REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN NO_TAC) ORELSE
          WSIMPPAUX_ANT_CASE_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  IMP_RES_TAC lookup_filter_v_SOME THEN IMP_RES_TAC lookup_filter_v_SOME_imp THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lookup_inter_EQ]) THEN
  MATCH_MP_TAC WSIMPPAUX_alloc_locals THEN ASM_MESON_TAC[];
  (* 13 StoreConsts *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 14 Install *)
  WSIMPPAUX_CFL_INTRO_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[evaluate_drop_consts] THEN
  DISCH_TAC THEN RVEQ_TAC THEN WSIMPPAUX_EVAL_ASM_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REPEAT ((REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN NO_TAC) ORELSE
          WSIMPPAUX_ANT_CASE_TAC ORELSE
          CHANGED_TAC (CONV_TAC(TOP_DEPTH_CONV let_CONV)) ORELSE PAIRARG_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_delete] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  IMP_RES_TAC lookup_filter_v_SOME_imp THEN RULE_ASSUM_TAC(REWRITE_RULE[lookup_inter_EQ]) THEN
  SIMP[wl_get_var_def; lookup_insert] THEN
  MATCH_MP_TAC WSIMPPAUX_cut_env_lookup THEN
  EXISTS_TAC `names:cutsets` THEN EXISTS_TAC `wl_state_locals (s:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[wl_get_var_def];
  (* 15 Store *) WSIMPPAUX_CFL_EXP_TAC [];
  (* 16-23 ShareInst *)
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  WSIMPPAUX_CFL_EXP_TAC WSIMPPAUX_share_rws;
  (* 24 Loop *)
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  WSIMPPAUX_CFL_INTRO_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[lookup_rwts; option_DISTINCT] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_pair(rhs(concl th))
     then SUBST1_TAC(SYM th) else failwith "") THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)wl_state`; `names:num_set`; `body:(A)wl_prog`;
                 `FST (const_fp_loop body (LN:(A word)spt))`; `exit_names:num_set`]
         (INST [`gc_fun_const_ok:(((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                      (store_name,(A)word_loc)fmap->
                      (((A)word_loc)list#(A word->(A)word_loc)#
                       (store_name,(A)word_loc)fmap)option)->bool`,
                `R:(((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                      (store_name,(A)word_loc)fmap->
                      (((A)word_loc)list#(A word->(A)word_loc)#
                       (store_name,(A)word_loc)fmap)option)->bool`]
               evaluate_Loop_body_cong_gc)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  X_GEN_TAC `v:(A,C,FFI)wl_state` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `wl_evaluate (body, v:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
    (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`FST (const_fp_loop body (LN:(A word)spt))`;
    `SND (const_fp_loop body (LN:(A word)spt))`; `v:(A,C,FFI)wl_state`;
    `r1:((A)wl_result)option`; `t1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[lookup_rwts; option_DISTINCT] THEN SIMP_TAC[];
  (* 25 Skip *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 26 Set *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 27 Raise *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 28 Return *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 29 Break *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 30 Continue *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 31 Tick *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 32 CodeBufferWrite *) WSIMPPAUX_CFL_SIMPLE_TAC [];
  (* 33 DataBufferWrite *) WSIMPPAUX_CFL_SIMPLE_TAC []];;

let evaluate_const_fp_loop = prove
 (`!p cs p' cs' (s:(A,C,FFI)wl_state) res s'.
     wl_evaluate (p,s) = (res,s') /\
     const_fp_loop p cs = (p',cs') /\
     gc_fun_const_ok (wl_state_gc_fun s) /\
     (!v w. lookup v cs = SOME w ==> wl_get_var v s = SOME (wl_Word w)) ==>
     wl_evaluate (p',s) = (res,s') /\
     (res = NONE ==>
      (!v w. lookup v cs' = SOME w ==> wl_get_var v s' = SOME (wl_Word w)))`,
  MATCH_MP_TAC const_fp_loop_ind THEN REPEAT CONJ_TAC THENL WSIMPPAUX_cfl_cases);;

let evaluate_const_fp = prove
 (`!p (s:(A,C,FFI)wl_state). gc_fun_const_ok (wl_state_gc_fun s) ==>
     wl_evaluate (const_fp p,s) = wl_evaluate (p,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[const_fp_def] THEN
  MP_TAC(ISPEC `const_fp_loop p (LN:(A word)spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)wl_prog` (X_CHOOSE_THEN `c:(A word)spt` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `wl_evaluate (p,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option`
    (X_CHOOSE_THEN `t:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `LN:(A word)spt`; `q:(A)wl_prog`; `c:(A word)spt`;
                 `s:(A,C,FFI)wl_state`; `r:((A)wl_result)option`; `t:(A,C,FFI)wl_state`]
                evaluate_const_fp_loop) THEN
  ASM_REWRITE_TAC[FST; lookup_rwts; option_DISTINCT] THEN SIMP_TAC[]);;

(* the duplicate-if pass *)

let WSIMPPAUX_evaluate_If_Seq = prove
 (`!cmp lhs rhs br1 br2 interm p2 (s:(A,C,FFI)wl_state).
     wl_evaluate (wl_If cmp lhs rhs (wl_Seq (wl_Seq br1 interm) p2)
                                    (wl_Seq (wl_Seq br2 interm) p2),s) =
     wl_evaluate (wl_Seq (wl_Seq (wl_If cmp lhs rhs br1 br2) interm) p2,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN
  CASES_ON `wl_get_var lhs (s:(A,C,FFI)wl_state)` THEN
  CASES_ON `wl_get_var_imm rhs (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  TRY (CASES_ON `wl_word_cmp cmp a (a':(A)word_loc)` THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[option_DISTINCT] THEN TRY (COND_CASES_TAC THEN REWRITE_TAC[]) THEN
       NO_TAC));;

(* HOL4 [local] *)

let evaluate_try_if_hoist2 = prove
 (`!N p1 interm dummy p2 (s:(A,C,FFI)wl_state).
     try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
     gc_fun_const_ok (wl_state_gc_fun s) ==>
     wl_evaluate (p3,s) = wl_evaluate (wl_Seq (wl_Seq p1 interm) p2,s)`,
  MATCH_MP_TAC try_if_hoist2_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[try_if_hoist2_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `p1:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THENL
   [(* Seq *)
    CASES_ON `dest_If (a1:(A)wl_prog)` THEN CASE_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)wl_prog`; `a1:(A)wl_prog`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:(A,C,FFI)wl_state`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC[GSYM word_simpProof_evaluate_Seq_assoc] THEN
      REWRITE_TAC[word_simp_Seq_assoc_def];
      ALL_TAC] THEN
    REPEAT (TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REPEAT (COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_If" with _ -> false)) THEN
    REWRITE_TAC[word_simpProof_dest_If_thm] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `!X. wl_evaluate (wl_Seq (wl_Seq (wl_Seq a0 X) interm) p2,s:(A,C,FFI)wl_state) =
          wl_evaluate (wl_Seq a0 (wl_Seq (wl_Seq X interm) p2),s)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM word_simpProof_evaluate_Seq_assoc] THEN
      REWRITE_TAC[word_simp_Seq_assoc_def]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    MP_TAC(ISPEC `wl_evaluate (a0, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
      (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `gc_fun_const_ok (wl_state_gc_fun (t1:(A,C,FFI)wl_state))` ASSUME_TAC THENL
     [MATCH_MP_TAC evaluate_gc_fun_const_ok THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[evaluate_const_fp; WSIMPPAUX_evaluate_If_Seq];
    (* If *)
    REPEAT (COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[evaluate_const_fp; WSIMPPAUX_evaluate_If_Seq]]);;
(* HOL4 [local] *)

let evaluate_try_if_hoist1 = prove
 (`try_if_hoist1 p1 p2 = SOME p3 ==> gc_fun_const_ok (wl_state_gc_fun s) ==>
   wl_evaluate (p3,s:(A,C,FFI)wl_state) = wl_evaluate (wl_Seq p1 p2,s)`,
  REWRITE_TAC[try_if_hoist1_def] THEN
  REPEAT (TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THEN REWRITE_TAC[option_DISTINCT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_try_if_hoist2) THEN
  DISCH_THEN(MP_TAC o SPEC `s:(A,C,FFI)wl_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[GSYM word_simpProof_evaluate_Seq_assoc] THEN
  REWRITE_TAC[word_simp_Seq_assoc_def]);;

let WSIMPPAUX_Loop_cong_gc =
  REWRITE_RULE[IMP_IMP]
   (INST [`gc_fun_const_ok:(((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                (store_name,(A)word_loc)fmap->
                (((A)word_loc)list#(A word->(A)word_loc)#
                 (store_name,(A)word_loc)fmap)option)->bool`,
          `R:(((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                (store_name,(A)word_loc)fmap->
                (((A)word_loc)list#(A word->(A)word_loc)#
                 (store_name,(A)word_loc)fmap)option)->bool`]
         evaluate_Loop_body_cong_gc);;

(* push_env does not look at the handler program *)

let WSIMPPAUX_push_env_handler = prove
 (`!env w (h:(A)wl_prog) l1 l2 (s:(A,C,FFI)wl_state).
     wl_push_env env (SOME (w,h,l1,l2)) s = wl_push_env env (SOME (w,wl_Skip,l1,l2)) s`,
  REWRITE_TAC[wl_push_env_def]);;

let WSIMPPAUX_evaluate_gc = prove
 (`!p (s1:(A,C,FFI)wl_state) vs s2.
     wl_evaluate (p,s1) = (vs,s2) ==> wl_state_gc_fun s1 = wl_state_gc_fun s2`,
  MESON_TAC[wl_evaluate_consts]);;

(* prove gc_fun_const_ok of a state reached by a call from the equations  *)
(* between the gc_fun fields of the states                                *)

let WSIMPPAUX_GC_SUBST_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th -> let c = concl th in
    if is_eq c && is_comb (lhs c) && is_const (rator (lhs c)) &&
       fst(dest_const(rator(lhs c))) = "wl_state_gc_fun" && not (lhs c = rhs c)
    then SUBST_ALL_TAC th else failwith "")) THEN
  ASM_REWRITE_TAC[];;

let WSIMPPAUX_SDI_GC_TAC : tactic =
  REWRITE_TAC[WSIMPPAUX_call_state_consts] THEN
  IMP_RES_TAC pop_env_gc_fun THEN IMP_RES_TAC WSIMPPAUX_evaluate_gc THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[WSIMPPAUX_call_state_consts; WSIMPPAUX_push_env_consts]) THEN
  WSIMPPAUX_GC_SUBST_TAC;;

(* a leaf wl_evaluate (simp_duplicate_if q,st) = (rr,tt) of the Call case *)

let WSIMPPAUX_SDI_LEAF_TAC : tactic = fun (asl,w as g) ->
  let st = snd(dest_pair(rand(lhs w))) in
  (SUBGOAL_THEN (mk_comb(`gc_fun_const_ok:(((A)word_loc)list#(A word->(A)word_loc)#
                     (A word->bool)#(store_name,(A)word_loc)fmap->
                     (((A)word_loc)list#(A word->(A)word_loc)#
                      (store_name,(A)word_loc)fmap)option)->bool`,
                  mk_comb(`wl_state_gc_fun:(A,C,FFI)wl_state->(((A)word_loc)list#
                     (A word->(A)word_loc)#(A word->bool)#(store_name,(A)word_loc)fmap->
                     (((A)word_loc)list#(A word->(A)word_loc)#
                      (store_name,(A)word_loc)fmap)option)`, st)))
     ASSUME_TAC THENL [WSIMPPAUX_SDI_GC_TAC; ASM_SIMP_TAC[]]) g;;

let WSIMPPAUX_SDI_CALL_TAC : tactic = fun (asl,w as g) ->
  let r = rhs w in
  (MP_TAC(ISPEC r PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `rr:((A)wl_result)option`
     (X_CHOOSE_THEN `tt:(A,C,FFI)wl_state` (fun th -> SUBST1_TAC th THEN MP_TAC th))) THEN
   ONCE_REWRITE_TAC[wl_evaluate_def] THEN
   ONCE_REWRITE_TAC[WSIMPPAUX_push_env_handler] THEN REWRITE_TAC[add_ret_loc_def] THEN
   REPEAT (DISCH_THEN ACCEPT_TAC ORELSE WSIMPPAUX_ANT_CASE_TAC) THEN
   DISCH_TAC THEN WSIMPPAUX_SDI_LEAF_TAC) g;;

let evaluate_simp_duplicate_if = prove
 (`!p (s:(A,C,FFI)wl_state). gc_fun_const_ok (wl_state_gc_fun s) ==>
     wl_evaluate (simp_duplicate_if p,s) = wl_evaluate (p,s)`,
  MATCH_MP_TAC simp_duplicate_if_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[simp_duplicate_if_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THENL
   [(* MustTerminate *)
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[];
    (* Call *)
    REPEAT (WSIMPPAUX_SPLIT_VARS_TAC ["option"]) THEN CASE_REWRITE_TAC[] THEN
    REPEAT (WSIMPPAUX_SPLIT_VARS_TAC ["prod"]) THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN WSIMPPAUX_SDI_CALL_TAC;
    (* Seq *)
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `wl_evaluate (wl_Seq (simp_duplicate_if a0) (simp_duplicate_if a1),
                               s:(A,C,FFI)wl_state) = wl_evaluate (wl_Seq a0 a1,s)`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPEC `wl_evaluate (a0, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
        (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `simp_duplicate_if (a1:(A)wl_prog)`)) (concl th) &&
        not (is_imp(concl th)))) THEN
      MATCH_MP_TAC evaluate_gc_fun_const_ok THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CASES_ON `try_if_hoist1 (simp_duplicate_if a0) (simp_duplicate_if (a1:(A)wl_prog))` THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[word_simpProof_evaluate_Seq_assoc] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_try_if_hoist1) THEN ASM_SIMP_TAC[];
    (* If *)
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[];
    (* Loop *)
    MATCH_MP_TAC WSIMPPAUX_Loop_cong_gc THEN ASM_REWRITE_TAC[]]);;

(* a program whose push_out_if_aux flag is set does not terminate normally *)

let WSIMPPAUX_NOT_NONE_TAC : tactic =
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REPEAT ((REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
           REWRITE_TAC[option_DISTINCT] THEN NO_TAC) ORELSE WSIMPPAUX_ANT_CASE_TAC);;

(* HOL4 [local] *)

let push_out_if_aux_T = prove
 (`!c2 c2' res (s:(A,C,FFI)wl_state) s'.
     push_out_if_aux c2 = (c2',T) ==> wl_evaluate (c2,s) = (res,s') ==> ~(res = NONE)`,
  MATCH_MP_TAC push_out_if_aux_ind THEN GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[push_out_if_aux_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT GEN_TAC THEN
  TRY (REPEAT (TOP_CASE_TAC THEN CASE_REWRITE_TAC[]) THEN REWRITE_TAC[PAIR_EQ] THEN
       NO_TAC) THENL
   [(* MustTerminate *)
    MP_TAC(ISPEC `push_out_if_aux (a:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(A)wl_prog` (X_CHOOSE_THEN `b:bool` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN WSIMPPAUX_NOT_NONE_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A)wl_prog`]) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    (* Call *)
    CASES_ON `a0:(num list#cutsets#(A)wl_prog#num#num)option` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MESON_TAC[WSIMPPAUX_call_NONE_res];
    (* Seq *)
    MP_TAC(ISPEC `push_out_if_aux (a0:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:(A)wl_prog` (X_CHOOSE_THEN `b1:bool` MP_TAC)) THEN
    BOOL_CASES_TAC `b1:bool` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `wl_evaluate (a0,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:((A)wl_result)option`
      (X_CHOOSE_THEN `t1:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]];
      MP_TAC(ISPEC `push_out_if_aux (a1:(A)wl_prog)` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `c2:(A)wl_prog` (X_CHOOSE_THEN `b2:bool` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
      STRIP_TAC THEN RVEQ_TAC THEN COND_CASES_TAC THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]]];
    (* If *)
    MP_TAC(ISPEC `push_out_if_aux (a3:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:(A)wl_prog` (X_CHOOSE_THEN `b1:bool` MP_TAC)) THEN
    BOOL_CASES_TAC `b1:bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `push_out_if_aux (a4:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c2:(A)wl_prog` (X_CHOOSE_THEN `b2:bool` MP_TAC)) THEN
    BOOL_CASES_TAC `b2:bool` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REPEAT ((REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
             REWRITE_TAC[option_DISTINCT] THEN NO_TAC) ORELSE WSIMPPAUX_ANT_CASE_TAC) THEN
    ASM_MESON_TAC[];
    (* Raise *) DISCH_TAC THEN WSIMPPAUX_NOT_NONE_TAC;
    (* Return *) DISCH_TAC THEN WSIMPPAUX_NOT_NONE_TAC]);;

(* the program computed by push_out_if_aux evaluates as the original one   *)
(* (the induction in the proof of HOL4's evaluate_simp_push_out_if)        *)

let WSIMPPAUX_POI_IH_TAC : tactic =
  REPEAT (FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun eq ->
    ASSUME_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) eq)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]);;

let WSIMPPAUX_POI_TF_TAC p : tactic =
  MP_TAC(ISPEC (mk_comb(`wl_evaluate:(A)wl_prog#(A,C,FFI)wl_state->
                           ((A)wl_result)option#(A,C,FFI)wl_state`,
                        mk_pair(p,`s:(A,C,FFI)wl_state`))) PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:((A)wl_result)option`
    (X_CHOOSE_THEN `t3:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r3:((A)wl_result)option = NONE)` ASSUME_TAC THENL
   [ASM_MESON_TAC[push_out_if_aux_T]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT (CASE_TAC THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let WSIMPPAUX_push_out_if_aux_eval = prove
 (`!p (c:(A)wl_prog) b. push_out_if_aux p = (c,b) ==>
     !s:(A,C,FFI)wl_state. wl_evaluate (c,s) = wl_evaluate (p,s)`,
  MATCH_MP_TAC push_out_if_aux_ind THEN GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[push_out_if_aux_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT GEN_TAC THEN
  TRY (STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THENL
   [(* MustTerminate *)
    MP_TAC(ISPEC `push_out_if_aux (a:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:(A)wl_prog` (X_CHOOSE_THEN `b1:bool` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    WSIMPPAUX_POI_IH_TAC THEN ASM_REWRITE_TAC[];
    (* Call *)
    CASES_ON `a0:(num list#cutsets#(A)wl_prog#num#num)option` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[];
    (* Seq *)
    MP_TAC(ISPEC `push_out_if_aux (a0:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:(A)wl_prog` (X_CHOOSE_THEN `b1:bool` MP_TAC)) THEN
    BOOL_CASES_TAC `b1:bool` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN GEN_TAC THEN
      ONCE_REWRITE_TAC[wl_evaluate_def] THEN WSIMPPAUX_POI_IH_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `push_out_if_aux (a1:(A)wl_prog)` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `c2:(A)wl_prog` (X_CHOOSE_THEN `b2:bool` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
      STRIP_TAC THEN RVEQ_TAC THEN GEN_TAC THEN
      ONCE_REWRITE_TAC[wl_evaluate_def] THEN WSIMPPAUX_POI_IH_TAC THEN ASM_REWRITE_TAC[]];
    (* If *)
    MP_TAC(ISPEC `push_out_if_aux (a3:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:(A)wl_prog` (X_CHOOSE_THEN `b1:bool` MP_TAC)) THEN
    BOOL_CASES_TAC `b1:bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `push_out_if_aux (a4:(A)wl_prog)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:(A)wl_prog` (X_CHOOSE_THEN `b2:bool` MP_TAC)) THEN
    BOOL_CASES_TAC `b2:bool` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN GEN_TAC THEN WSIMPPAUX_POI_IH_TAC THEN
    REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THENL
     [WSIMPPAUX_POI_TF_TAC `a3:(A)wl_prog`; WSIMPPAUX_POI_TF_TAC `a4:(A)wl_prog`];
    (* Loop *)
    STRIP_TAC THEN RVEQ_TAC THEN GEN_TAC THEN MATCH_MP_TAC evaluate_Loop_body_cong THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`FST (push_out_if_aux (a1:(A)wl_prog))`;
                                  `SND (push_out_if_aux (a1:(A)wl_prog))`]) THEN
    REWRITE_TAC[] THEN SIMP_TAC[]]);;

let evaluate_simp_push_out_if = prove
 (`!p (s:(A,C,FFI)wl_state).
     wl_evaluate (push_out_if p,s) = wl_evaluate (p,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[push_out_if_def] THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `FST (push_out_if_aux (p:(A)wl_prog))`;
                 `SND (push_out_if_aux (p:(A)wl_prog))`] WSIMPPAUX_push_out_if_aux_eval) THEN
  REWRITE_TAC[] THEN SIMP_TAC[]);;

(* putting it all together *)

(* HOL4: compile_exp_thm *)

let word_simpProof_compile_exp_thm = prove
 (`wl_evaluate (prog,s:(A,C,FFI)wl_state) = (res,s2) /\ ~(res = SOME wl_Error) /\
   gc_fun_const_ok (wl_state_gc_fun s) ==>
   wl_evaluate (word_simp_compile_exp prog,s) = (res,s2)`,
  STRIP_TAC THEN REWRITE_TAC[word_simp_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[evaluate_simp_push_out_if; evaluate_simp_duplicate_if; evaluate_const_fp;
               word_simpProof_evaluate_Seq_assoc]);;
