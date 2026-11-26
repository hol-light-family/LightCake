(* ========================================================================= *)
(* pan_simpProof: port of HOL4 pancake/proofs/pan_simpProofScript.sml        *)
(* (CakeML v3479).  Correctness proof for pan_simp.                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says (pan_simpProof_compile_correct,             *)
(*   pan_simpProof_state_rel, ...); PPASS1AUX_ names are local helpers.      *)
(* - HOL4 paired lambdas are written with match; r with f := v is            *)
(*   RECTYPE_f_fupd (K v) r.                                                 *)
(* - compile_eval_correct is proved from eval_upd_code_eq of panProps.       *)
(* - state_rel_imp_evaluate_decls: the HOL4 binder start (it does not occur  *)
(*   in the statement) is dropped.                                           *)
(* - state_rel_imp_semantics: state_rel keeps the clocks and the ffi states  *)
(*   equal, so compile_correct gives equal runs at every clock and the two   *)
(*   semantics agree by PPASS1AUX_pan_semantics_cong (HOL4 goes through     *)
(*   evaluate_add_clock_eq and the io-event prefixes).                       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/semantics/panSem.ml";;
needs "pancake/pan_simp.ml";;
needs "pancake/semantics/panProps.ml";;

type_invention_error := true;;

let exp_ids_ret_to_tail_eq = prove
 (`!p:(A)panLang_prog. exp_ids (ret_to_tail p) = exp_ids p`,
  MATCH_MP_TAC ret_to_tail_ind THEN RW[] THEN FS[ret_to_tail_def; exp_ids_def] THENL
   [(* the induction hypotheses right to left, then the cases of seq_call_ret *)
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[seq_call_ret_def] THEN REPEAT TOP_CASE_TAC THEN
    FS[exp_ids_def];
    REPEAT TOP_CASE_TAC THEN FS[exp_ids_def]]);;

let exp_ids_seq_assoc_eq = prove
 (`!p q:(A)panLang_prog. exp_ids (seq_assoc p q) = APPEND (exp_ids p) (exp_ids q)`,
  MATCH_MP_TAC seq_assoc_ind THEN RW[] THEN
  FS[seq_assoc_def; exp_ids_def] THEN
  REPEAT TOP_CASE_TAC THEN FS[seq_assoc_def; exp_ids_def]);;

let exp_ids_compile_eq = prove
 (`!p:(A)panLang_prog. exp_ids (pan_simp_compile p) = exp_ids p`,
  RW[] THEN FS[pan_simp_compile_def] THEN
  FS[exp_ids_ret_to_tail_eq; exp_ids_seq_assoc_eq; exp_ids_def]);;

let map_snd_f_eq = prove
 (CASE_TERM
  `!(p:(A#B#C)list) (f:C->D) (g:D->E).
     MAP (g o SND o SND o (\x. match x with (name,params,body) -> (name,params,f body))) p =
     MAP (g o f) (MAP (SND o SND) p)`,
  LIST_INDUCT_TAC THEN RW[] THEN
  PAIR_CASES_ON `h:A#B#C` THEN FS[o_THM; MAP]);;

let size_of_eids_compile_eq = prove
 (`!pan_code:((A)decl)list.
     size_of_eids (pan_simp_compile_prog pan_code) = size_of_eids pan_code`,
  LIST_INDUCT_TAC THENL
   [RW[pan_simp_compile_prog_def; size_of_eids_def]; ALL_TAC] THEN
  CASES_ON `h:(A)decl` THEN
  GVS[pan_simp_compile_prog_def; size_of_eids_def; is_exn_decl_def]);;

let pan_simpProof_evaluate_SmartSeq = prove
 (`pan_evaluate (pan_simp_SmartSeq p q,s:(A,FFI)pan_state) =
   pan_evaluate (panLang_Seq p q,s)`,
  RW[pan_simp_SmartSeq_def; pan_evaluate_def]);;

let evaluate_seq_skip = prove
 (`!p (s:(A,FFI)pan_state). pan_evaluate (panLang_Seq p panLang_Skip,s) = pan_evaluate (p,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pan_evaluate_def] THEN
  PAIR_CASES_ON `pan_evaluate (p:(A)panLang_prog,s:(A,FFI)pan_state)` THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let evaluate_skip_seq = prove
 (`pan_evaluate (panLang_Seq panLang_Skip p,s:(A,FFI)pan_state) = pan_evaluate (p,s)`,
  FS[pan_evaluate_def]);;

let evaluate_while_body_same = prove
 (`(!s:(A,FFI)pan_state. pan_evaluate (body,s) = pan_evaluate (body',s)) ==>
   !s:(A,FFI)pan_state. pan_evaluate (While e body,s) = pan_evaluate (While e body',s)`,
  (DISCH_TAC THEN
  SUBGOAL_THEN `!n (s:(A,FFI)pan_state). pan_state_clock s = n ==>
                  pan_evaluate (While e body,s) = pan_evaluate (While e body',s)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:(A,FFI)pan_state` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[])) THEN
  (FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP pan_evaluate_clock th)) THEN
   FS[pan_dec_clock_def] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `pan_state_clock (y:(A,FFI)pan_state)`) THEN
   ANTS_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(MATCH_MP_TAC o SPEC `y:(A,FFI)pan_state`) THEN REWRITE_TAC[]]));;

let evaluate_while_no_error_imp = prove
 (`pan_eval s e = SOME (pan_Val (Word w)) /\ ~(w = word 0) /\
   ~(pan_state_clock s = 0) /\
   ~(FST (pan_evaluate (While e c,s:(A,FFI)pan_state)) = SOME pan_Error) ==>
   ~(FST (pan_evaluate (c,pan_dec_clock s)) = SOME pan_Error)`,
  STRIP_TAC THEN
  UNDISCH_TAC `~(FST (pan_evaluate (While e c,s:(A,FFI)pan_state)) = SOME pan_Error)` THEN
  ONCE_REWRITE_TAC[pan_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  PAIR_CASES_ON `pan_evaluate (c:(A)panLang_prog,pan_dec_clock (s:(A,FFI)pan_state))` THEN
  CAKE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN FS[]);;

(* evaluate_seq_assoc: two helpers for HOL4's case analysis of the clauses *)

let PPASS1AUX_evaluate_seq_cong = prove
 (`(!s:(A,FFI)pan_state. pan_evaluate (q',s) = pan_evaluate (q,s)) ==>
   pan_evaluate (panLang_Seq p q',s:(A,FFI)pan_state) = pan_evaluate (panLang_Seq p q,s)`,
  DISCH_TAC THEN REWRITE_TAC[pan_evaluate_def] THEN ASM_REWRITE_TAC[]);;

let PPASS1AUX_evaluate_seq_seq = prove
 (`pan_evaluate (panLang_Seq (panLang_Seq p q) r,s:(A,FFI)pan_state) =
   pan_evaluate (panLang_Seq p (panLang_Seq q r),s)`,
  REWRITE_TAC[pan_evaluate_def] THEN
  PAIR_CASES_ON `pan_evaluate (p:(A)panLang_prog,s:(A,FFI)pan_state)` THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let evaluate_seq_assoc = prove
 (`!p q (s:(A,FFI)pan_state).
     pan_evaluate (seq_assoc p q,s) = pan_evaluate (panLang_Seq p q,s)`,
  MATCH_MP_TAC seq_assoc_ind THEN
  REWRITE_TAC[seq_assoc_def; pan_simpProof_evaluate_SmartSeq; evaluate_seq_skip] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THENL
   [(* Dec *)
    GEN_TAC THEN MATCH_MP_TAC PPASS1AUX_evaluate_seq_cong THEN GEN_TAC THEN
    REWRITE_TAC[pan_evaluate_def] THEN ASM_REWRITE_TAC[evaluate_skip_seq];
    (* Seq *)
    GEN_TAC THEN ASM_REWRITE_TAC[GSYM PPASS1AUX_evaluate_seq_seq] THEN
    ONCE_REWRITE_TAC[pan_evaluate_def] THEN ASM_REWRITE_TAC[];
    (* If *)
    GEN_TAC THEN MATCH_MP_TAC PPASS1AUX_evaluate_seq_cong THEN GEN_TAC THEN
    REWRITE_TAC[pan_evaluate_def] THEN ASM_REWRITE_TAC[evaluate_skip_seq] THEN
    REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[evaluate_skip_seq]);
    (* While *)
    GEN_TAC THEN MATCH_MP_TAC PPASS1AUX_evaluate_seq_cong THEN
    MATCH_MP_TAC evaluate_while_body_same THEN ASM_REWRITE_TAC[evaluate_skip_seq];
    (* Call (SOME (rv,exp)) *)
    GEN_TAC THEN MATCH_MP_TAC PPASS1AUX_evaluate_seq_cong THEN GEN_TAC THEN
    QCASES_ON "exp:(mlstring#mlstring#(A)panLang_prog)option" THEN
    CAKE_REWRITE_TAC[] THEN
    PAIR_CASES_ON `a:mlstring#mlstring#(A)panLang_prog` THEN CAKE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a0:mlstring`; `a1:mlstring`; `a2:(A)panLang_prog`]) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[pan_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[evaluate_skip_seq];
    (* DecCall *)
    GEN_TAC THEN MATCH_MP_TAC PPASS1AUX_evaluate_seq_cong THEN GEN_TAC THEN
    REWRITE_TAC[pan_evaluate_def] THEN ASM_REWRITE_TAC[evaluate_skip_seq];
    (* Annot *)
    REWRITE_TAC[pan_evaluate_def] THEN
    PAIR_CASES_ON `pan_evaluate (p:(A)panLang_prog,s:(A,FFI)pan_state)` THEN
    CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

(* evaluate_seq_call_ret_eq: the one case where seq_call_ret changes the     *)
(* program (HOL4: fs [evaluate_def] >> every_case_tac >> ...)                *)

let PPASS1AUX_evaluate_tail_call = prove
 (`~(FST (pan_evaluate
          (panLang_Seq (panLang_Call (SOME (SOME (panLang_Local,rv),NONE)) trgt args)
                       (panLang_Return (panLang_Var panLang_Local rv)),
           s:(A,FFI)pan_state)) = SOME pan_Error) ==>
   pan_evaluate (panLang_Call NONE trgt args,s) =
   pan_evaluate (panLang_Seq (panLang_Call (SOME (SOME (panLang_Local,rv),NONE)) trgt args)
                             (panLang_Return (panLang_Var panLang_Local rv)),s)`,
  REWRITE_TAC[pan_evaluate_def; LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN FS[] THEN
  FS[pan_empty_locals_def; kvar_defs] THEN FS[pan_eval_def; FLOOKUP_UPDATE]);;

let evaluate_seq_call_ret_eq = prove
 (`!p (s:(A,FFI)pan_state). ~(FST (pan_evaluate (p,s)) = SOME pan_Error) ==>
       pan_evaluate (seq_call_ret p,s) = pan_evaluate (p,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[seq_call_ret_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[] THEN
  RVEQ_TAC THEN MATCH_ACCEPT_TAC PPASS1AUX_evaluate_tail_call);;

let evaluate_seq_no_error_fst = prove
 (`~(FST (pan_evaluate (panLang_Seq p p',s:(A,FFI)pan_state)) = SOME pan_Error) ==>
   ~(FST (pan_evaluate (p,s)) = SOME pan_Error)`,
  REWRITE_TAC[pan_evaluate_def] THEN
  PAIR_CASES_ON `pan_evaluate (p:(A)panLang_prog,s:(A,FFI)pan_state)` THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let eval_seq_assoc_eq_evaluate = prove
 (`pan_evaluate (seq_assoc panLang_Skip p,s:(A,FFI)pan_state) = (res,t) ==>
   pan_evaluate (p,s) = (res,t)`,
  REWRITE_TAC[evaluate_seq_assoc; evaluate_skip_seq]);;

let eval_seq_assoc_not_error = prove
 (`~(FST (pan_evaluate (p,s:(A,FFI)pan_state)) = SOME pan_Error) ==>
   ~(FST (pan_evaluate (seq_assoc panLang_Skip p,s)) = SOME pan_Error)`,
  REWRITE_TAC[evaluate_seq_assoc; evaluate_skip_seq]);;

let ret_to_tail_correct = prove
 (`!p (s:(A,FFI)pan_state).
     ~(FST (pan_evaluate (p,s)) = SOME pan_Error) ==>
     pan_evaluate (ret_to_tail p,s) = pan_evaluate (p,s)`,
  REC_IND_TAC pan_evaluate_ind THEN REPEAT CONJ_TAC THEN
   TRY(RW[ret_to_tail_def] THEN NO_TAC) THENL
   [(* Dec *)
    RW[ret_to_tail_def] THEN FS[pan_evaluate_def] THEN TOP_CASE_TAC THEN FS[] THEN RW[] THEN
   REPEAT(PAIRARG_TAC THEN FS[] THEN RVEQ_TAC);
    (* Seq *)
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[ret_to_tail_def] THEN
   SUBGOAL_THEN `pan_evaluate (panLang_Seq (ret_to_tail c1) (ret_to_tail c2),s) =
                 pan_evaluate (panLang_Seq c1 c2,s:(A,FFI)pan_state)` ASSUME_TAC THENL
    [IMP_RES_TAC evaluate_seq_no_error_fst THEN
     UNDISCH_TAC `~(FST (pan_evaluate (panLang_Seq c1 c2,s:(A,FFI)pan_state)) = SOME pan_Error)` THEN
     REWRITE_TAC[pan_evaluate_def] THEN RFS[] THEN
     PAIR_CASES_ON `pan_evaluate (c1:(A)panLang_prog,s:(A,FFI)pan_state)` THEN
     CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     RVEQ_TAC THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `pan_evaluate (panLang_Seq (ret_to_tail c1) (ret_to_tail c2),s:(A,FFI)pan_state)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC evaluate_seq_call_ret_eq THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    (* If *)
    RW[ret_to_tail_def] THEN FS[pan_evaluate_def] THEN EVERY_CASE_TAC THEN RFS[];
    (* While *)
    (REPEAT GEN_TAC THEN REWRITE_TAC[ret_to_tail_def] THEN STRIP_TAC THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[pan_evaluate_def] THEN
   TOP_CASE_TAC THEN ASM_REWRITE_TAC[] THEN TOP_CASE_TAC THEN ASM_REWRITE_TAC[] THEN
   TOP_CASE_TAC THEN ASM_REWRITE_TAC[] THEN TOP_CASE_TAC THEN ASM_REWRITE_TAC[] THEN
   TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
    (SUBGOAL_THEN `~(FST (pan_evaluate (c,pan_dec_clock (s:(A,FFI)pan_state))) = SOME (pan_Error:(A)pan_result))`
     ASSUME_TAC THENL
    [MP_TAC(INST [`a'':A word`,`w:A word`] evaluate_while_no_error_imp) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   RFS[] THEN
   PAIR_CASES_ON `pan_evaluate (c:(A)panLang_prog,pan_dec_clock (s:(A,FFI)pan_state))` THEN
   CAKE_REWRITE_TAC[] THEN REPEAT(TOP_CASE_TAC THEN CAKE_REWRITE_TAC[])) THEN
    (SUBGOAL_THEN `~(FST (pan_evaluate (While e c,p1:(A,FFI)pan_state)) =
                   SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
    [UNDISCH_TAC `~(FST (pan_evaluate (While e c,s:(A,FFI)pan_state)) = SOME pan_Error)` THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [pan_evaluate_def] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
     RFS[]]);
    (* Call *)
    RW[] THEN FS[ret_to_tail_def; pan_evaluate_def] THEN EVERY_CASE_TAC THEN
   FS[pan_evaluate_def; ret_to_tail_def];
    (* DecCall *)
    (RW[] THEN FS[ret_to_tail_def; pan_evaluate_def] THEN EVERY_CASE_TAC THEN
   FS[pan_evaluate_def; ret_to_tail_def] THEN
   REPEAT(PAIRARG_TAC THEN GVS[])) THEN
    (SUBGOAL_THEN `x''':((A)pan_result)option = x'''' /\ y''':(A,FFI)pan_state = y''''`
     (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[GSYM PAIR_EQ] THEN ASM_MESON_TAC[FST])]);;

let compile_correct_same_state = prove
 (`~(FST (pan_evaluate (p,s:(A,FFI)pan_state)) = SOME pan_Error) ==>
   pan_evaluate (pan_simp_compile p,s) = pan_evaluate (p,s)`,
  REWRITE_TAC[pan_simp_compile_def; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP eval_seq_assoc_not_error) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP ret_to_tail_correct) THEN
  REWRITE_TAC[evaluate_seq_assoc; evaluate_skip_seq]);;

let evaluate_seq_simp = prove
 (`pan_evaluate (p,s:(A,FFI)pan_state) = (res,t) /\ ~(res = SOME pan_Error) ==>
   pan_evaluate (pan_simp_compile p,s) = (res,t)`,
  STRIP_TAC THEN ASM_SIMP_TAC[compile_correct_same_state; FST]);;

let pan_simpProof_state_rel_def = cake_def
 `pan_simpProof_state_rel (s:(A,FFI)pan_state) t c <=>
    t = pan_state_code_fupd (combin_K c) s /\
    (!f. FLOOKUP (pan_state_code s) f = NONE ==> FLOOKUP c f = NONE) /\
    (!f vshs prog rshape.
       FLOOKUP (pan_state_code s) f = SOME (vshs,prog,rshape) ==>
       FLOOKUP c f = SOME (vshs,pan_simp_compile prog,rshape))`;;

let pan_simpProof_state_rel_intro = prove
 (`!(s:(A,FFI)pan_state) t c. pan_simpProof_state_rel s t c ==>
     t = pan_state_code_fupd (combin_K c) s /\
     (!f vshs prog rshape.
        FLOOKUP (pan_state_code s) f = SOME (vshs,prog,rshape) ==>
        FLOOKUP c f = SOME (vshs,pan_simp_compile prog,rshape))`,
  RW[pan_simpProof_state_rel_def]);;

let state_rel_upd_inv = prove
 (`pan_simpProof_state_rel (s:(A,FFI)pan_state) t code ==>
   ?s_code. s = pan_state_code_fupd (combin_K s_code) t`,
  RW[pan_simpProof_state_rel_def] THEN EXISTS_TAC `pan_state_code (s:(A,FFI)pan_state)` THEN
  SIMP[pan_state_component_equality]);;

let pan_simpProof_opt_mmap_eq_some_helper = prove
 (`!xs zs. OPT_MMAP (f:A->B option) xs = SOME zs /\
           (!x. MEM x xs ==> !y. f x = SOME y ==> g x = SOME y) ==>
           OPT_MMAP g xs = SOME zs`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def] THEN FS[OPTION_BIND_EQUALS_OPTION] THEN
  ASM_MESON_TAC[]);;

(* HOL4 proves this by induction on eval; panProps' eval_upd_code_eq (eval *)
(* ignores the code field) gives it at once                                  *)
let compile_eval_correct = prove
 (`!s e v (t:(A,FFI)pan_state).
     pan_eval s e = SOME v /\ pan_simpProof_state_rel s t (pan_state_code t) ==>
     pan_eval t e = SOME v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[pan_simpProof_state_rel_def]) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[eval_upd_code_eq]);;

let OPT_MMAP_NONE = prove
 (`OPT_MMAP (f:A->B option) xs = NONE ==> ?x. MEM x xs /\ f x = NONE`,
  QINDUCT_ON "xs" THEN RW[OPT_MMAP_def] THEN ASM_MESON_TAC[]);;

let OPT_MMAP_NONE' = prove
 (`MEM (x:A) xs /\ (f:A->B option) x = NONE ==> OPT_MMAP f xs = NONE`,
  QINDUCT_ON "xs" THEN RW[OPT_MMAP_def] THEN MESON_TAC[cases "option"]);;

let OPT_MMAP_eval_some_eq = prove
 (`OPT_MMAP (\a. pan_eval s a) es = SOME vs /\
   pan_simpProof_state_rel s t (pan_state_code (t:(A,FFI)pan_state)) ==>
   OPT_MMAP (\a. pan_eval t a) es = SOME vs`,
  STRIP_TAC THEN MATCH_MP_TAC(GEN_ALL pan_simpProof_opt_mmap_eq_some_helper) THEN
  EXISTS_TAC `\a. pan_eval (s:(A,FFI)pan_state) a` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[compile_eval_correct]);;

(* compile_correct: helpers for the cases of the induction *)

(* state_rel is kept by dec_clock and empty_locals (HOL4: fs [dec_clock_def, *)
(* state_rel_def, state_component_equality] in the cases of compile_correct) *)

let PPASS1AUX_state_rel_dec_clock = prove
 (`pan_simpProof_state_rel s t (pan_state_code (t:(A,FFI)pan_state)) ==>
   pan_simpProof_state_rel (pan_dec_clock s) (pan_dec_clock t)
     (pan_state_code (pan_dec_clock t))`,
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN
    `c:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap` SUBST_ALL_TAC o
    MATCH_MP state_rel_upd_inv) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[pan_simpProof_state_rel_def; pan_dec_clock_def] THEN
  SIMP[pan_state_component_equality]);;

let PPASS1AUX_state_rel_empty_locals = prove
 (`pan_simpProof_state_rel s t (pan_state_code (t:(A,FFI)pan_state)) ==>
   pan_simpProof_state_rel (pan_empty_locals s) (pan_empty_locals t)
     (pan_state_code (pan_empty_locals t))`,
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN
    `c:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap` SUBST_ALL_TAC o
    MATCH_MP state_rel_upd_inv) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[pan_simpProof_state_rel_def; pan_empty_locals_def] THEN
  SIMP[pan_state_component_equality]);;

let PPASS1AUX_state_rel_locals = prove
 (`pan_simpProof_state_rel s (t:(A,FFI)pan_state) c ==>
   pan_simpProof_state_rel (pan_state_locals_fupd f s) (pan_state_locals_fupd f t) c`,
  REWRITE_TAC[pan_simpProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FS[pan_state_component_equality]);;

let PPASS1AUX_state_rel_lookup_code = prove
 (`pan_simpProof_state_rel s t (pan_state_code (t:(A,FFI)pan_state)) /\
   pan_lookup_code (pan_state_code s) fname args = SOME (prog,nl,rsh) ==>
   pan_lookup_code (pan_state_code t) fname args = SOME (pan_simp_compile prog,nl,rsh)`,
  REWRITE_TAC[pan_lookup_code_def; pan_simpProof_state_rel_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  QCASES_ON "FLOOKUP (pan_state_code (s:(A,FFI)pan_state)) fname" THEN
  CAKE_REWRITE_TAC[option_DISTINCT] THEN
  PAIR_CASES_ON `a:(mlstring#shape)list#(A)panLang_prog#shape` THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  MESON_TAC[]);;

let PPASS1AUX_state_rel_fields = prove
 (`pan_simpProof_state_rel s t c ==>
   pan_state_locals t = pan_state_locals (s:(A,FFI)pan_state) /\
   pan_state_globals t = pan_state_globals s /\
   pan_state_structs t = pan_state_structs s /\
   pan_state_eshapes t = pan_state_eshapes s /\
   pan_state_clock t = pan_state_clock s`,
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN
    `s_code:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap` SUBST_ALL_TAC o
    MATCH_MP state_rel_upd_inv) THEN
  SIMP[]);;

let PPASS1AUX_state_rel_globals = prove
 (`pan_simpProof_state_rel s (t:(A,FFI)pan_state) c ==>
   pan_simpProof_state_rel (pan_state_globals_fupd f s) (pan_state_globals_fupd f t) c`,
  REWRITE_TAC[pan_simpProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FS[pan_state_component_equality]);;


let PPASS1AUX_eval_upd_code_eq_fun = prove
 (`!(t:(A,FFI)pan_state) c. pan_eval (pan_state_code_fupd (combin_K c) t) = pan_eval t`,
  REWRITE_TAC[FUN_EQ_THM; eval_upd_code_eq]);;
let PPASS1AUX_LOCAL_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN
    `sc:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap` SUBST_ALL_TAC o
    MATCH_MP state_rel_upd_inv) THEN
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  REWRITE_TAC[pan_evaluate_def; eval_upd_code_eq; PPASS1AUX_eval_upd_code_eq_fun;
              LET_DEF; LET_END_DEF; pan_sh_mem_load_def; pan_sh_mem_store_def;
              kvar_defs] THEN
  SIMP[] THEN REWRITE_TAC[eval_upd_code_eq; PPASS1AUX_eval_upd_code_eq_fun] THEN
  REPEAT(TOP_CASE_TAC THEN CAKE_REWRITE_TAC[]) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FS[pan_simpProof_state_rel_def; pan_empty_locals_def] THEN
  FS[pan_state_component_equality];;

(* HOL4's compile_Others_tac *)
let PPASS1AUX_OTHERS_TAC : tactic =
  RW[] THEN FS[pan_evaluate_def] THEN RVEQ_TAC THEN FS[kvar_defs] THEN
  EVERY_CASE_TAC THEN GVS[] THEN IMP_RES_TAC compile_eval_correct THEN
  GVS[pan_simpProof_state_rel_def; pan_state_component_equality;
      pan_empty_locals_def; pan_dec_clock_def];;

let PPASS1AUX_CALL_CLOSE_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST [SIMP[] THEN
         REWRITE_TAC[pan_set_kvar_def] THEN TRY(TOP_CASE_TAC) THEN
         REWRITE_TAC[pan_set_var_def; pan_set_global_def] THEN
         (fun (asl,w as g) -> MAP_EVERY (fun (_,th) ->
            try STRIP_ASSUME_TAC (MATCH_MP PPASS1AUX_state_rel_fields th)
            with Failure _ -> ALL_TAC) asl g) THEN
         FS[PPASS1AUX_state_rel_empty_locals; PPASS1AUX_state_rel_locals;
            PPASS1AUX_state_rel_globals] THEN NO_TAC;
         ASM_MESON_TAC[]];;

let PPASS1AUX_CALL_HANDLER_TAC : tactic =
  DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_X_ASSUM(IRULE o REWRITE_RULE[option_INJ; PAIR_EQ] o
                check (fun th -> is_forall(concl th) &&
                                 can (find_term (fun t -> is_const t && fst(dest_const t) = "pan_Exception")) (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`a'2:shape`; `a'0:(A)panLang_prog`; `a'1:(mlstring,(A)pan_v)fmap`;
                        `x:(varkind#mlstring)option`; `x':mlstring`; `x'':mlstring`;
                        `a1:(A)pan_v`; `p1:(A,FFI)pan_state`] THEN
  ASM_REWRITE_TAC[pan_is_valid_value_def; pan_lookup_kvar_def] THEN
  REWRITE_TAC[pan_set_var_def] THEN FS[PPASS1AUX_state_rel_locals];;

let PPASS1AUX_DECCALL_CONT_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a'0:(A)panLang_prog`; `a'1:(mlstring,(A)pan_v)fmap`;
                                `a''':(A)pan_v`; `p1:(A,FFI)pan_state`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:((A)pan_result)option`; `y:(A,FFI)pan_state`;
    `pan_set_var rt a''' (pan_state_locals_fupd (combin_K (pan_state_locals (s:(A,FFI)pan_state)))
                            (t1:(A,FFI)pan_state))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[pan_set_var_def] THEN
    FS[PPASS1AUX_state_rel_locals];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
  GVS[] THEN
  (fun (asl,w as g) -> MAP_EVERY (fun (_,th) ->
     try STRIP_ASSUME_TAC (MATCH_MP PPASS1AUX_state_rel_fields th)
     with Failure _ -> ALL_TAC) asl g) THEN
  ASM_REWRITE_TAC[] THEN FS[PPASS1AUX_state_rel_locals];;

let pan_simpProof_compile_correct = prove
 (`!prog (s:(A,FFI)pan_state) res s1 t.
     pan_evaluate (prog,s) = (res,s1) /\ ~(res = SOME pan_Error) /\
     pan_simpProof_state_rel s t (pan_state_code t) ==>
     ?t1. pan_evaluate (seq_assoc panLang_Skip prog,t) = (res,t1) /\
          pan_simpProof_state_rel s1 t1 (pan_state_code t1)`,
  REC_IND_TAC pan_evaluate_ind THEN REWRITE_TAC[evaluate_seq_assoc; evaluate_skip_seq] THEN
  REPEAT CONJ_TAC THENL
   [(* Skip *)
    PPASS1AUX_OTHERS_TAC;
    (* Dec *)
    (RW[] THEN FS[pan_evaluate_def] THEN
   QCASES_ON "pan_eval (s:(A,FFI)pan_state) e" THEN FS[] THEN RVEQ_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP compile_eval_correct o CONJ
     (ASSUME `pan_eval (s:(A,FFI)pan_state) e = SOME a`)) THEN DISCH_TAC THEN
   GVS[COND_CASE_EQ] THEN REPEAT(PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN FS[])) THEN
    (FIRST_X_ASSUM(MP_TAC o
     SPEC `pan_state_locals_fupd (combin_K (pan_state_locals t |+ (v,a:(A)pan_v)))
             (t:(A,FFI)pan_state)` o check (is_forall o concl)) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN FS[pan_simpProof_state_rel_def; pan_state_component_equality];
     ALL_TAC] THEN
   STRIP_TAC THEN FS[] THEN RVEQ_TAC THEN RFS[pan_simpProof_state_rel_def] THEN
   FS[pan_state_component_equality]);
    (* Assign *)
    PPASS1AUX_OTHERS_TAC;
    (* Primitive *)
    PPASS1AUX_LOCAL_TAC;
    (* Store *)
    PPASS1AUX_OTHERS_TAC;
    (* Store32 *)
    PPASS1AUX_OTHERS_TAC;
    (* StoreByte *)
    PPASS1AUX_OTHERS_TAC;
    (* ShMemLoad *)
    PPASS1AUX_LOCAL_TAC;
    (* ShMemStore *)
    PPASS1AUX_LOCAL_TAC;
    (* Seq *)
    (RW[] THEN FS[pan_evaluate_def] THEN
     REPEAT(PAIRARG_TAC THEN FS[] THEN RVEQ_TAC THEN FS[])) THEN
    (FIRST_X_ASSUM(MP_TAC o SPEC `t:(A,FFI)pan_state` o check (is_forall o concl)) THEN
     ASM_CASES_TAC `res'':((A)pan_result)option = NONE` THEN
     FS[option_DISTINCT] THEN STRIP_TAC THEN GVS[] THEN ASM_MESON_TAC[]);
    (* If *)
    RW[] THEN FS[pan_evaluate_def] THEN
    QCASES_ON "pan_eval (s:(A,FFI)pan_state) e" THEN FS[] THEN RVEQ_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP compile_eval_correct o CONJ
      (ASSUME `pan_eval (s:(A,FFI)pan_state) e = SOME a`)) THEN DISCH_TAC THEN
    FS[] THEN TOP_CASE_TAC THEN FS[] THEN TOP_CASE_TAC THEN FS[];
    (* Break *)
    PPASS1AUX_OTHERS_TAC;
    (* Continue *)
    PPASS1AUX_OTHERS_TAC;
    (* While *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `pan_evaluate (While e c,s:(A,FFI)pan_state) = (res,s1)` THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   QCASES_ON "pan_eval (s:(A,FFI)pan_state) e" THEN CAKE_REWRITE_TAC[] THENL
    [ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP compile_eval_correct o CONJ
     (ASSUME `pan_eval (s:(A,FFI)pan_state) e = SOME a`)) THEN DISCH_TAC THEN
   SUBGOAL_THEN `pan_state_clock (t:(A,FFI)pan_state) = pan_state_clock (s:(A,FFI)pan_state)` ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[pan_simpProof_state_rel_def] o
       check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "pan_simpProof_state_rel"
                        with Failure _ -> false)) THEN
     DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
     SIMP[];
     ALL_TAC] THEN
   GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
    (QCASES_ON "a:(A)pan_v" THEN CAKE_REWRITE_TAC[] THEN
   TRY(REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
   QCASES_ON "a':(A)word_lab" THEN CAKE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `a'':A word = word 0` THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
    [STRIP_TAC THEN EXISTS_TAC `t:(A,FFI)pan_state` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `pan_state_clock (s:(A,FFI)pan_state) = 0` THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
    [STRIP_TAC THEN EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN
     ASM_MESON_TAC[PPASS1AUX_state_rel_empty_locals];
     ALL_TAC]) THEN
    (PAIR_CASES_ON `pan_evaluate (c:(A)panLang_prog,pan_dec_clock (s:(A,FFI)pan_state))` THEN
   CAKE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `p0 = SOME (pan_Error:(A)pan_result)` THENL
    [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `a'':A word`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`p0:((A)pan_result)option`; `p1:(A,FFI)pan_state`;
                               `pan_dec_clock (t:(A,FFI)pan_state)`]) THEN
   ASM_SIMP_TAC[PPASS1AUX_state_rel_dec_clock] THEN
   DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
    (QCASES_ON "p0:((A)pan_result)option" THEN CAKE_REWRITE_TAC[] THEN
   TRY(TOP_CASE_TAC THEN CAKE_REWRITE_TAC[]) THEN
   REWRITE_TAC[PAIR_EQ] THEN
   FIRST
    [DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
       MP_TAC(SPECL [`a'':A word`; `p1:(A,FFI)pan_state`] th) THEN
       ASM_REWRITE_TAC[PAIR_EQ] THEN
       DISCH_THEN(MP_TAC o SPECL [`res:((A)pan_result)option`; `s1:(A,FFI)pan_state`;
                                  `t1:(A,FFI)pan_state`]) THEN
       ASM_REWRITE_TAC[] THEN NO_TAC);
     DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     EXISTS_TAC `t1:(A,FFI)pan_state` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
     ASM_MESON_TAC[]]);
    (* Return *)
    PPASS1AUX_OTHERS_TAC;
    (* Raise *)
    PPASS1AUX_OTHERS_TAC;
    (* Tick *)
    PPASS1AUX_OTHERS_TAC;
    (* Annot *)
    PPASS1AUX_OTHERS_TAC;
    (* Call *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `pan_evaluate (panLang_Call caltyp fname argexps,s:(A,FFI)pan_state) = (res,s1)` THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   QCASES_ON "OPT_MMAP (pan_eval (s:(A,FFI)pan_state)) argexps" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
    (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS1AUX_state_rel_fields) THEN
   MP_TAC(INST [`argexps:((A)panLang_exp)list`,`es:((A)panLang_exp)list`;
                `a:((A)pan_v)list`,`vs:((A)pan_v)list`]
            (REWRITE_RULE[ETA_AX] OPT_MMAP_eval_some_eq)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
   QCASES_ON "pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname a" THEN
   CAKE_REWRITE_TAC[] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   PAIR_CASES_ON `a':(A)panLang_prog#((mlstring,(A)pan_v)fmap)#shape` THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP PPASS1AUX_state_rel_lookup_code o
     C CONJ (ASSUME `pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname a =
                     SOME (a'0,a'1,a'2)`)) THEN
   DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `pan_state_clock (s:(A,FFI)pan_state) = 0` THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN
     ASM_MESON_TAC[PPASS1AUX_state_rel_empty_locals];
     ALL_TAC] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF]) THEN
    (REWRITE_TAC[pan_is_valid_value_def; pan_lookup_kvar_def] THEN ASM_REWRITE_TAC[] THEN
   PAIR_CASES_ON `pan_evaluate (a'0:(A)panLang_prog,
                    pan_state_locals_fupd (combin_K a'1) (pan_dec_clock (s:(A,FFI)pan_state)))` THEN
   CAKE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `p0 = NONE \/ p0 = SOME (pan_Error:(A)pan_result) \/
                  p0 = SOME pan_Break \/ p0 = SOME pan_Continue` THENL
    [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
     CAKE_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a:((A)pan_v)list`; `a'2:shape`; `a'0:(A)panLang_prog`;
                                 `a'1:(mlstring,(A)pan_v)fmap`] o
                 check (fun th -> is_forall(concl th) &&
                                  length(fst(strip_forall(concl th))) = 4)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`p0:((A)pan_result)option`; `p1:(A,FFI)pan_state`;
     `pan_state_locals_fupd (combin_K a'1) (pan_dec_clock (t:(A,FFI)pan_state))`]) THEN
   FS[PPASS1AUX_state_rel_locals; PPASS1AUX_state_rel_dec_clock] THEN
   DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_seq_simp o C CONJ
     (ASSUME `~(p0 = SOME (pan_Error:(A)pan_result))`)) THEN
   DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[]) THEN
    (REPEAT(TOP_CASE_TAC THEN CAKE_REWRITE_TAC[]) THEN REWRITE_TAC[PAIR_EQ]) THEN
    FIRST [PPASS1AUX_CALL_HANDLER_TAC; PPASS1AUX_CALL_CLOSE_TAC];
    (* DecCall *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `pan_evaluate (DecCall rt shape fname argexps prog1,s:(A,FFI)pan_state) = (res,s1)` THEN
   GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV) [pan_evaluate_def] THEN
   QCASES_ON "OPT_MMAP (pan_eval (s:(A,FFI)pan_state)) argexps" THEN CAKE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
    (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS1AUX_state_rel_fields) THEN
   MP_TAC(INST [`argexps:((A)panLang_exp)list`,`es:((A)panLang_exp)list`;
                `a:((A)pan_v)list`,`vs:((A)pan_v)list`]
            (REWRITE_RULE[ETA_AX] OPT_MMAP_eval_some_eq)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
   QCASES_ON "pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname a" THEN
   CAKE_REWRITE_TAC[] THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   PAIR_CASES_ON `a':(A)panLang_prog#((mlstring,(A)pan_v)fmap)#shape` THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP PPASS1AUX_state_rel_lookup_code o
     C CONJ (ASSUME `pan_lookup_code (pan_state_code (s:(A,FFI)pan_state)) fname a =
                     SOME (a'0,a'1,a'2)`)) THEN
   DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `pan_state_clock (s:(A,FFI)pan_state) = 0` THEN ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
     EXISTS_TAC `pan_empty_locals (t:(A,FFI)pan_state)` THEN
     ASM_MESON_TAC[PPASS1AUX_state_rel_empty_locals];
     ALL_TAC] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF]) THEN
    (REWRITE_TAC[pan_is_valid_value_def; pan_lookup_kvar_def] THEN ASM_REWRITE_TAC[] THEN
   PAIR_CASES_ON `pan_evaluate (a'0:(A)panLang_prog,
                    pan_state_locals_fupd (combin_K a'1) (pan_dec_clock (s:(A,FFI)pan_state)))` THEN
   CAKE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `p0 = NONE \/ p0 = SOME (pan_Error:(A)pan_result) \/
                  p0 = SOME pan_Break \/ p0 = SOME pan_Continue` THENL
    [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
     CAKE_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a:((A)pan_v)list`; `a'2:shape`; `a'0:(A)panLang_prog`;
                                 `a'1:(mlstring,(A)pan_v)fmap`] o
                 check (fun th -> is_forall(concl th) &&
                                  length(fst(strip_forall(concl th))) = 4)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`p0:((A)pan_result)option`; `p1:(A,FFI)pan_state`;
     `pan_state_locals_fupd (combin_K a'1) (pan_dec_clock (t:(A,FFI)pan_state))`]) THEN
   FS[PPASS1AUX_state_rel_locals; PPASS1AUX_state_rel_dec_clock] THEN
   DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_seq_simp o C CONJ
     (ASSUME `~(p0 = SOME (pan_Error:(A)pan_result))`)) THEN
   DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[]) THEN
    (REPEAT(TOP_CASE_TAC THEN CAKE_REWRITE_TAC[]) THEN REWRITE_TAC[PAIR_EQ]) THEN
    FIRST [PPASS1AUX_CALL_CLOSE_TAC; PPASS1AUX_DECCALL_CONT_TAC THEN NO_TAC];
    (* ExtCall *)
    PPASS1AUX_LOCAL_TAC]);;

let functions_compile_prog = prove
 (CASE_TERM
  `functions (pan_simp_compile_prog (prog:((A)decl)list)) =
   MAP (\q. match q with (x,y,z,t) -> (x,y,pan_simp_compile z,t)) (functions prog)`,
  SPEC_TAC(`prog:((A)decl)list`,`prog:((A)decl)list`) THEN
  MATCH_MP_TAC (cake_ind "functions") THEN RW[] THEN
  GVS[pan_simp_compile_prog_def; functions_def]);;

let pan_simpProof_first_compile_prog_all_distinct = prove
 (`ALL_DISTINCT (MAP FST (functions (prog:((A)decl)list))) ==>
   ALL_DISTINCT (MAP FST (functions (pan_simp_compile_prog prog)))`,
  REWRITE_TAC[functions_compile_prog; MAP_MAP_o] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN SIMP[]);;

let pan_simpProof_el_compile_prog_el_prog_eq = prove
 (`!(prog:((A)decl)list) n start pprog p rshape.
     EL n (functions (pan_simp_compile_prog prog)) = (start,[],pprog,rshape) /\
     ALL_DISTINCT (MAP FST (functions prog)) /\ n < LENGTH (functions prog) /\
     ALOOKUP (functions prog) start = SOME ([],p,rshape) ==>
     EL n (functions prog) = (start,[],p,rshape)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[functions_compile_prog] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALOOKUP (functions (prog:((A)decl)list)) (FST (EL n (functions prog))) =
    SOME (SND (EL n (functions prog)))` MP_TAC THENL
   [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[PAIR] THEN
    ASM_MESON_TAC[MEM_EL];
    ALL_TAC] THEN
  RFS[EL_MAP] THEN
  PAIR_CASES_ON `EL n (functions (prog:((A)decl)list))` THEN GVS[]);;

let pan_simpProof_compile_prog_distinct_params = prove
 (CASE_TERM
  `!prog:((A)decl)list.
     ALL (\q. match q with (name,params,body) -> ALL_DISTINCT params) (functions prog) ==>
     ALL (\q. match q with (name,params,body) -> ALL_DISTINCT params)
         (functions (pan_simp_compile_prog prog))`,
  REWRITE_TAC[functions_compile_prog; ALL_MAP] THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN SIMP[]);;

(* the two semantics agree when the runs of the program of pan_semantics   *)
(* agree, clock by clock, in their results and their ffi states            *)

let PPASS1AUX_pan_semantics_cong = prove
 (`!(s:(A,FFI)pan_state) (t:(A,FFI)pan_state) start.
     (!k. FST (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (combin_K k) t)) =
          FST (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (combin_K k) s))) /\
     (!k. pan_state_ffi
            (SND (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (combin_K k) t))) =
          pan_state_ffi
            (SND (pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (combin_K k) s))))
     ==> pan_semantics t start = pan_semantics s start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pan_semantics_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    (CASE_TERM
     `!res. (?k t' r outcome.
               pan_evaluate (panLang_Call NONE (start:mlstring) [],
                             pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state)) =
                 (r,t') /\
               (match r with
                  SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                | SOME (pan_Return _) -> outcome = Success
                | _ -> F) /\
               res = Terminate outcome (ffi_state_io_events (pan_state_ffi t'))) <=>
            (?k t' r outcome.
               pan_evaluate (panLang_Call NONE start [],
                             pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state)) =
                 (r,t') /\
               (match r with
                  SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                | SOME (pan_Return _) -> outcome = Success
                | _ -> F) /\
               res = Terminate outcome
                       (ffi_state_io_events (pan_state_ffi (t':(A,FFI)pan_state))))`)
    (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[PAIR_FST_SND_EQ; FST; SND] THEN
  EQ_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:num`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    try let l,r = dest_eq(concl th) in is_var r && not (is_var l) && rator l = `SND:((A)pan_result)option#(A,FFI)pan_state->(A,FFI)pan_state` with Failure _ -> false))) THEN
  ASM_MESON_TAC[]);;

let PPASS1AUX_state_rel_clock = prove
 (`pan_simpProof_state_rel s t (pan_state_code (t:(A,FFI)pan_state)) ==>
   pan_simpProof_state_rel (pan_state_clock_fupd (combin_K k) s) (pan_state_clock_fupd (combin_K k) t)
     (pan_state_code (pan_state_clock_fupd (combin_K k) t))`,
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN
    `c:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap` SUBST_ALL_TAC o
    MATCH_MP state_rel_upd_inv) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[pan_simpProof_state_rel_def] THEN
  SIMP[pan_state_component_equality]);;

(* HOL4 goes through the clocks with evaluate_add_clock_eq and the io      *)
(* prefixes; here state_rel keeps the clocks and the ffi states equal, so  *)
(* the runs agree clock by clock (PPASS1AUX_pan_semantics_cong)            *)

let pan_simpProof_state_rel_imp_semantics = prove
 (`!(s:(A,FFI)pan_state) t pan_code start.
     pan_simpProof_state_rel s t (pan_state_code t) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     pan_state_code s = alist_to_fmap (functions pan_code) /\
     pan_state_code t = alist_to_fmap (functions (pan_simp_compile_prog pan_code)) /\
     ~(pan_semantics s start = Fail) ==>
     pan_semantics t start = pan_semantics s start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `!k. ?r s1 t1.
       pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (combin_K k) s) = (r,s1) /\
       pan_evaluate (panLang_Call NONE start [],pan_state_clock_fupd (combin_K k) t) = (r,t1) /\
       pan_state_ffi t1 = pan_state_ffi (s1:(A,FFI)pan_state)`
    MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPEC `pan_evaluate (panLang_Call NONE start [],
                                pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state))`
           PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:((A)pan_result)option`; `s1:(A,FFI)pan_state`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~(r = SOME (pan_Error:(A)pan_result))` ASSUME_TAC THENL
     [UNDISCH_TAC `~(pan_semantics (s:(A,FFI)pan_state) start = Fail)` THEN
      REWRITE_TAC[pan_semantics_def; LET_DEF; LET_END_DEF] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[FST] THEN CAKE_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`panLang_Call NONE start []:(A)panLang_prog`;
                   `pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state)`;
                   `r:((A)pan_result)option`; `s1:(A,FFI)pan_state`;
                   `pan_state_clock_fupd (combin_K k) (t:(A,FFI)pan_state)`]
           pan_simpProof_compile_correct) THEN
    ASM_SIMP_TAC[PPASS1AUX_state_rel_clock] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`r:((A)pan_result)option`; `s1:(A,FFI)pan_state`;
                          `t1:(A,FFI)pan_state`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC eval_seq_assoc_eq_evaluate THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP state_rel_upd_inv) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC PPASS1AUX_pan_semantics_cong THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]);;

(* HOL4 also quantifies an unused variable start *)
let state_rel_imp_evaluate_decls = prove
 (`!s (pan_code:((A)decl)list) (t:(A,FFI)pan_state) s'.
     pan_simpProof_state_rel s t (pan_state_code t) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     evaluate_decls s pan_code = SOME s' ==>
     ?t'. evaluate_decls t (pan_simp_compile_prog pan_code) = SOME t' /\
          pan_simpProof_state_rel s' t' (pan_state_code t')`,
  REC_IND_TAC evaluate_decls_ind THEN
   RW[pan_simp_compile_prog_def; functions_def; evaluate_decls_def] THEN
   GVS(all_case_eqs()) THENL
   [(* Decl *)
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS1AUX_state_rel_fields) THEN
   SUBGOAL_THEN `pan_eval (pan_state_locals_fupd (combin_K FEMPTY) (t:(A,FFI)pan_state)) e =
                 SOME (a:(A)pan_v)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC compile_eval_correct THEN
     EXISTS_TAC `pan_state_locals_fupd (combin_K FEMPTY) (s:(A,FFI)pan_state)` THEN
     ASM_REWRITE_TAC[] THEN FS[PPASS1AUX_state_rel_locals];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `pan_state_globals_fupd (combin_K (pan_state_globals t |+ (v,a:(A)pan_v)))
                                  (t:(A,FFI)pan_state)` o check (is_forall o concl)) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FS[PPASS1AUX_state_rel_globals]; ALL_TAC] THEN
   STRIP_TAC THEN EXISTS_TAC `t':(A,FFI)pan_state` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `a:(A)pan_v` THEN REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_eq o concl) o
     check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "evaluate_decls"
                      with Failure _ -> false)) THEN
   ASM_REWRITE_TAC[];
    (* Function *)
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS1AUX_state_rel_fields) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC
     `pan_state_code_fupd (combin_K (pan_state_code t |+
        (fun_decl_name fi,fun_decl_params fi,pan_simp_compile (fun_decl_body fi),
         fun_decl_return fi))) (t:(A,FFI)pan_state)` o check (is_forall o concl)) THEN
   ANTS_TAC THENL
    [FIRST_ASSUM(X_CHOOSE_THEN
       `sc:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap` SUBST_ALL_TAC o
       MATCH_MP state_rel_upd_inv) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[pan_simpProof_state_rel_def]) THEN
     REWRITE_TAC[pan_simpProof_state_rel_def] THEN FS[FLOOKUP_UPDATE] THEN RW[] THEN FS[];
     ALL_TAC] THEN
   STRIP_TAC THEN EXISTS_TAC `t':(A,FFI)pan_state` THEN ASM_REWRITE_TAC[];
    (* ExnDecl *)
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PPASS1AUX_state_rel_fields) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC
     `pan_state_eshapes_fupd (combin_K (pan_state_eshapes t |+ (eid,sh)))
        (t:(A,FFI)pan_state)` o check (is_forall o concl)) THEN
   ANTS_TAC THENL
    [FIRST_ASSUM(X_CHOOSE_THEN
       `sc:(mlstring,(mlstring#shape)list#(A)panLang_prog#shape)fmap` SUBST_ALL_TAC o
       MATCH_MP state_rel_upd_inv) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[pan_simpProof_state_rel_def]) THEN
     REWRITE_TAC[pan_simpProof_state_rel_def] THEN FS[] THEN
     FS[pan_state_component_equality];
     ALL_TAC] THEN
   STRIP_TAC THEN EXISTS_TAC `t':(A,FFI)pan_state` THEN ASM_REWRITE_TAC[]]);;

let decs_stcnames_compile_prog = prove
 (`!ctxt (pan_code:((A)decl)list).
     decs_stcnames ctxt (pan_simp_compile_prog pan_code) = decs_stcnames ctxt pan_code`,
  REC_IND_TAC decs_stcnames_ind THEN REWRITE_TAC[pan_simp_compile_prog_def; MAP] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[decs_stcnames_def; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_MESON_TAC[]);;

(* uses evaluate_decls_functions of panProps *)

let pan_simpProof_state_rel_imp_semantics_decls = prove
 (`!(s:(A,FFI)pan_state) t pan_code start.
     pan_simpProof_state_rel s t (pan_state_code t) /\
     ALL_DISTINCT (MAP FST (functions pan_code)) /\
     pan_state_code s = FEMPTY /\ pan_state_code t = FEMPTY /\
     ~(semantics_decls s start pan_code = Fail) ==>
     semantics_decls s start pan_code =
     semantics_decls t start (pan_simp_compile_prog pan_code)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(semantics_decls (s:(A,FFI)pan_state) start pan_code = Fail)` THEN
  REWRITE_TAC[semantics_decls_def; decs_stcnames_compile_prog] THEN
  QCASES_ON "decs_stcnames [] (pan_code:((A)decl)list)" THEN CAKE_REWRITE_TAC[] THEN
  RENAME1 "decs_stcnames [] pan_code = SOME st_ctxt" THEN
  QCASES_ON "evaluate_decls (pan_state_structs_fupd (combin_K st_ctxt) (s:(A,FFI)pan_state)) pan_code" THEN
  CAKE_REWRITE_TAC[] THEN
  RENAME1 "evaluate_decls (pan_state_structs_fupd (combin_K st_ctxt) s) pan_code = SOME s1" THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`pan_state_structs_fupd (combin_K st_ctxt) (s:(A,FFI)pan_state)`;
                 `pan_code:((A)decl)list`;
                 `pan_state_structs_fupd (combin_K st_ctxt) (t:(A,FFI)pan_state)`;
                 `s1:(A,FFI)pan_state`] state_rel_imp_evaluate_decls) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
      "pan_simpProof_state_rel" with Failure _ -> false)) THEN
    SIMP[pan_simpProof_state_rel_def] THEN RW[] THEN SIMP[pan_state_component_equality];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)pan_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC pan_simpProof_state_rel_imp_semantics THEN
  EXISTS_TAC `pan_code:((A)decl)list` THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_decls_functions)) THEN
  SIMP[] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FMAPAUX_FEMPTY_FUPDATE_LIST; pan_simpProof_first_compile_prog_all_distinct]);;
