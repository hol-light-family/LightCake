(* ========================================================================= *)
(* compute_evalProof: port of HOL4 candle/prover/compute/                     *)
(* compute_evalProofScript.sml (CakeML v3479).  Proofs about the interpreter *)
(* function for the Candle compute primitive.                                 *)
(*                                                                            *)
(* Notes on the rendering:                                                    *)
(* - The overloads of compute_syntax are read by its parser extension (see    *)
(*   the header of compute_syntax.ml).  This file adds HOL4's thyof (of a     *)
(*   context, holSyntax) to the table: thyof ctxt is ((alist_to_fmap (FLAT    *)
(*   (MAP types_of_upd ctxt)), alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),*)
(*   set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd *)
(*   upd)) ctxt))), as holKernelProof.ml writes it out.                       *)
(* - term_ok (sigof thy) is hol_term_ok (FST thy); TERM and STATE are         *)
(*   holKernelProof_TERM and holKernelProof_STATE; s.the_context is           *)
(*   hol_refs_the_context s.  The free variables of the HOL4 statements are   *)
(*   universally quantified.                                                  *)
(* - Local helpers that are not HOL4 theorems are CMPEVPAUX_.                *)
(* ========================================================================= *)

needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/prover/compute/compute_syntaxProof.ml";;
needs "candle/prover/compute/compute_eval.ml";;

prioritize_num();;
type_invention_error := true;;

compute_overloads_on ();;

compute_add_overload "thyof" ["ctxt"]
  "((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
     alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
    set_of_list (FLAT (MAP (\\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                           ctxt)))";;

let do_fst_thm = prove
 (`!p (s:A) (res:(compute_exp,B)exc) s'.
     compute_do_fst p s = (res,s') ==>
       s = s' /\
       ?q. res = M_success q /\ cexp_consts q SUBSET cexp_consts p`,
  GEN_TAC THEN CASES_ON `p:compute_exp` THEN
  REWRITE_TAC[compute_do_fst_def; st_ex_return_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; UNWIND_THM1; cexp_consts_def; EMPTY_SUBSET;
              SUBSET_UNION]);;

let do_snd_thm = prove
 (`!p (s:A) (res:(compute_exp,B)exc) s'.
     compute_do_snd p s = (res,s') ==>
       s = s' /\
       ?q. res = M_success q /\ cexp_consts q SUBSET cexp_consts p`,
  GEN_TAC THEN CASES_ON `p:compute_exp` THEN
  REWRITE_TAC[compute_do_snd_def; st_ex_return_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; UNWIND_THM1; cexp_consts_def; EMPTY_SUBSET;
              SUBSET_UNION]);;

let do_ispair_thm = prove
 (`!p (s:A) (res:(compute_exp,B)exc) s'.
     compute_do_ispair p s = (res,s') ==>
       s = s' /\
       ?q. res = M_success q /\ cexp_consts q SUBSET cexp_consts p`,
  GEN_TAC THEN CASES_ON `p:compute_exp` THEN
  REWRITE_TAC[compute_do_ispair_def; st_ex_return_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; UNWIND_THM1; cexp_consts_def; EMPTY_SUBSET;
              SUBSET_UNION]);;

let term_ok_FOLDL_Comb = prove
 (`!tms tm sig.
     hol_term_ok sig (FOLDL hol_Comb tm tms) ==>
       hol_term_ok sig tm /\
       ALL (hol_term_ok sig) tms`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; ALL] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  SIMP_TAC[hol_term_ok_def]);;

(* an argument of uop2term, bop2term replaced by a term of the same type *)
let CMPEVPAUX_uop2term_replace = prove
 (`!sig uop t t'.
     hol_term_ok sig (uop2term uop t) /\ hol_term_ok sig t' /\ typeof t' = typeof t
     ==> hol_term_ok sig (uop2term uop t')`,
  GEN_TAC THEN MATCH_MP_TAC uop_INDUCT THEN REWRITE_TAC[uop2term_def] THEN
  REWRITE_TAC[CMPSYNPAUX_term_ok_Comb_alt] THEN MESON_TAC[]);;

let CMPEVPAUX_bop2term_replace = prove
 (`!sig bop t1 t2 t1' t2'.
     hol_term_ok sig (bop2term bop t1 t2) /\
     hol_term_ok sig t1' /\ typeof t1' = typeof t1 /\
     hol_term_ok sig t2' /\ typeof t2' = typeof t2
     ==> hol_term_ok sig (bop2term bop t1' t2')`,
  GEN_TAC THEN MATCH_MP_TAC compute_binop_INDUCT THEN REWRITE_TAC[bop2term_def] THEN
  REWRITE_TAC[CMPSYNPAUX_term_ok_Comb_alt; typeof_def] THEN MESON_TAC[]);;

let CMPEVPAUX_uop2term_arg = prove
 (`!sig uop t. hol_term_ok sig (uop2term uop t) ==> hol_term_ok sig t`,
  GEN_TAC THEN MATCH_MP_TAC uop_INDUCT THEN REWRITE_TAC[uop2term_def] THEN
  SIMP_TAC[hol_term_ok_def]);;

let CMPEVPAUX_bop2term_args = prove
 (`!sig bop t1 t2. hol_term_ok sig (bop2term bop t1 t2) ==>
                   hol_term_ok sig t1 /\ hol_term_ok sig t2`,
  GEN_TAC THEN MATCH_MP_TAC compute_binop_INDUCT THEN REWRITE_TAC[bop2term_def] THEN
  SIMP_TAC[hol_term_ok_def]);;

let CMPEVPAUX_ALL_MAP_FILTER = prove
 (`!(P:B->bool) (f:A->B) Q l. ALL P (MAP f l) ==> ALL P (MAP f (FILTER Q l))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; MAP; ALL] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MAP; ALL]);;

let subst_term_ok = prove
 (`!ctxt env cv.
     hol_term_ok ctxt (cexp2term cv) /\
     ALL (hol_term_ok ctxt o cexp2term) (MAP SND env) ==>
       hol_term_ok ctxt (cexp2term (compute_subst env cv))`,
  GEN_TAC THEN MATCH_MP_TAC compute_subst_ind THEN
  REWRITE_TAC[compute_subst_def; cexp2term_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL
   [(* Var *)
    TOP_CASE_TAC THEN ASM_REWRITE_TAC[cexp2term_def] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (hol_term_ok ctxt o cexp2term)
                     (MAP SND (env:(mlstring#compute_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; o_THM] THEN MESON_TAC[SND];
    (* (Num is solved by the stripping) Pair *)
    RULE_ASSUM_TAC(REWRITE_RULE[CMPSYNPAUX_term_ok_Comb_alt; typeof_def;
                                cexp2term_typeof; codomain_def]) THEN
    REWRITE_TAC[CMPSYNPAUX_term_ok_Comb_alt; typeof_def; cexp2term_typeof;
                codomain_def] THEN
    ASM_SIMP_TAC[];
    (* Uop *)
    MATCH_MP_TAC CMPEVPAUX_uop2term_replace THEN
    EXISTS_TAC `cexp2term p` THEN ASM_REWRITE_TAC[cexp2term_typeof] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMPEVPAUX_uop2term_arg];
    (* Binop *)
    MATCH_MP_TAC CMPEVPAUX_bop2term_replace THEN
    MAP_EVERY EXISTS_TAC [`cexp2term p`; `cexp2term q`] THEN
    ASM_REWRITE_TAC[cexp2term_typeof] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPEVPAUX_bop2term_args) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* App *)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP term_ok_FOLDL_Comb) THEN
    MATCH_MP_TAC CMPSYNPAUX_FOLDL_term_ok THEN
    ASM_REWRITE_TAC[LENGTH_MAP; has_type_rules; cexp2term_has_type; MEM_MAP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
                  check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (hol_term_ok ctxt) (MAP cexp2term cs)` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[];
    (* If *)
    RULE_ASSUM_TAC(REWRITE_RULE[CMPSYNPAUX_term_ok_Comb_alt; typeof_def;
                                cexp2term_typeof; codomain_def]) THEN
    REWRITE_TAC[CMPSYNPAUX_term_ok_Comb_alt; typeof_def; cexp2term_typeof;
                codomain_def] THEN
    ASM_SIMP_TAC[];
    (* Let *)
    RULE_ASSUM_TAC(REWRITE_RULE[CMPSYNPAUX_term_ok_Comb_alt; CMPSYNPAUX_term_ok_Abs_Var;
                                typeof_def; cexp2term_typeof; codomain_def]) THEN
    REWRITE_TAC[CMPSYNPAUX_term_ok_Comb_alt; CMPSYNPAUX_term_ok_Abs_Var;
                typeof_def; cexp2term_typeof; codomain_def] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CMPEVPAUX_ALL_MAP_FILTER]]);;

let do_arith_value = prove
 (`!opn x y (s:A) z s'.
     compute_do_arith opn x y s = (M_success z:(compute_exp,B)exc,s') ==>
       cexp_value z`,
  MATCH_MP_TAC compute_do_arith_ind THEN
  GVS[compute_do_arith_def; st_ex_return_def; cexp_value_def]);;

let do_reln_value = prove
 (`!opn x y (s:A) z s'.
     compute_do_reln opn x y s = (M_success z:(compute_exp,B)exc,s') ==>
       cexp_value z`,
  MATCH_MP_TAC compute_do_reln_ind THEN
  GVS[compute_do_reln_def; st_ex_return_def; cexp_value_def]);;

let do_eq_value = prove
 (`!(x:compute_exp) y (s:A) z s'.
     compute_do_eq x y s = (M_success z:(compute_exp,B)exc,s') ==>
       cexp_value z`,
  GVS[compute_do_eq_def; st_ex_return_def; cexp_value_def]);;

let do_binop_value = prove
 (`!bop x y z (s:A) s'.
     compute_do_binop bop x y s = (M_success z:(compute_exp,B)exc,s') ==>
       cexp_value z`,
  MATCH_MP_TAC compute_binop_INDUCT THEN REWRITE_TAC[compute_do_binop_def] THEN
  MESON_TAC[do_arith_value; do_reln_value; do_eq_value]);;

(* the monad: st_ex_ignore_bind as ml_monadBase_st_ex_bind_success *)
let CMPEVPAUX_st_ex_ignore_bind_success = prove
 (`!(f:A->(B,C)exc#A) (g:A->(D,C)exc#A) st st' v.
     st_ex_ignore_bind f g st = (M_success v,st') <=>
     ?v' st''. f st = (M_success v',st'') /\ g st'' = (M_success v,st')`,
  RW[st_ex_ignore_bind_def] THEN EVERY_CASE_TAC THEN RW[]);;

let CMPEVPAUX_do_uop_value = prove
 (`!uop x (s:A) v s'.
     cexp_value x /\ compute_do_uop uop x s = (M_success v:(compute_exp,B)exc,s')
     ==> cexp_value v`,
  MATCH_MP_TAC uop_INDUCT THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  CASES_ON `x:compute_exp` THEN
  GVS[compute_do_uop_def; compute_do_fst_def; compute_do_snd_def;
      compute_do_ispair_def; st_ex_return_def; cexp_value_def]);;

let CMPEVPAUX_pair_CASE_FST_SND = prove
 (`!(p:A#B) (f:A->B->C). pair_CASE p f = f (FST p) (SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

(* the monadic steps of compute_eval as equations *)
let CMPEVPAUX_MONAD_RULE =
  REWRITE_RULE[ml_monadBase_st_ex_bind_success; ml_monadBase_st_ex_return_success;
               CMPEVPAUX_st_ex_ignore_bind_success; holKernel_raise_Failure_def;
               compute_option_def; compute_check_def; PAIR_EQ;
               injectivity "exc"; distinctness "exc"];;

let compute_eval_value = prove
 (`(!ck ceqs cv (s:hol_refs) x s'.
     compute_eval ck ceqs cv s = (M_success x,s') ==> cexp_value x) /\
   (!ck ceqs cvs (s:hol_refs) xs s'.
     compute_eval_list ck ceqs cvs s = (M_success xs,s') ==> ALL cexp_value xs)`,
  MATCH_MP_TAC compute_eval_ind THEN ONCE_REWRITE_TAC[compute_eval_def] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC CMPEVPAUX_MONAD_RULE THEN
  GVS[cexp_value_def; ALL; distinctness "exc"] THENL
   [(* Pair *)
    ASM_MESON_TAC[];
    (* Uop *)
    ASM_MESON_TAC[CMPEVPAUX_do_uop_value];
    (* Binop *)
    ASM_MESON_TAC[do_binop_value];
    (* App *)
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ; distinctness "exc"] THEN
    REWRITE_TAC[ml_monadBase_st_ex_bind_success] THEN TOP_CASE_TAC THEN
    GVS[ml_monadBase_st_ex_return_success; holKernel_raise_Failure_def;
        distinctness "exc"; CMPEVPAUX_pair_CASE_FST_SND;
        CMPEVPAUX_st_ex_ignore_bind_success; COND_RATOR;
        ml_monadBase_st_ex_bind_success] THEN
    ASM_MESON_TAC[];
    (* If *)
    POP_ASSUM MP_TAC THEN TOP_CASE_TAC THEN
    REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ; distinctness "exc"] THEN
    TRY COND_CASES_TAC THEN ASM_MESON_TAC[];
    (* Let *)
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ; distinctness "exc";
                ml_monadBase_st_ex_bind_success] THEN
    ASM_MESON_TAC[];
    (* CONS *)
    ASM_MESON_TAC[]]);;

let dest_binary_thm = prove
 (`!ctxt s tm tm' res s'.
     holKernelProof_STATE ctxt s /\
     holKernelProof_TERM ctxt tm /\
     holKernelProof_TERM ctxt tm' ==>
     compute_dest_binary tm' tm s = (res,s') ==>
       s' = s /\
       !l r. res = M_success (l,r) ==>
             holKernelProof_TERM ctxt l /\ holKernelProof_TERM ctxt r /\
             tm = hol_Comb (hol_Comb tm' l) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compute_dest_binary_def] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ;
              distinctness "exc"; injectivity "exc"] THEN
  REPEAT STRIP_TAC THEN GVS[distinctness "exc"; injectivity "exc"; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_TERM_def; hol_term_ok_def]) THEN
  ASM_REWRITE_TAC[holKernelProof_TERM_def]);;

let dest_numeral_thm = prove
 (`!ctxt s tm res s'.
     holKernelProof_STATE ctxt s /\
     holKernelProof_TERM ctxt tm ==>
     compute_dest_numeral tm s = (res,s') ==>
       s' = s /\
       !n. res = M_success n ==>
           (numeral_thy_ok (thyof ctxt) ==> typeof tm = Num) /\
           ?tm'. tm = _NUMERAL tm' /\ compute_dest_num tm' = SOME n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compute_dest_numeral_def] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ;
              distinctness "exc"; injectivity "exc"] THEN
  REPEAT STRIP_TAC THEN GVS[distinctness "exc"; injectivity "exc"; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
  ASM_REWRITE_TAC[typeof_def; codomain_def; injectivity "hol_term"] THEN
  ASM_MESON_TAC[]);;

let num2bit_thm = prove
 (`!ctxt x. numeral_thy_ok (thyof ctxt) ==> holKernelProof_TERM ctxt (num2bit x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP num2bit_term_ok) THEN
  REWRITE_TAC[holKernelProof_TERM_def; FST]);;

let CMPEVPAUX_DIV_MOD_2 = prove
 (`!a. (2 * a) MOD 2 = 0 /\ (2 * a) DIV 2 = a /\
       (2 * a + 1) MOD 2 = 1 /\ (2 * a + 1) DIV 2 = a`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `a:num` THEN ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `a:num` THEN ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1` THEN ARITH_TAC]);;

(* the induction hypothesis of dest_num (with its case context, made true *)
(* by the one-point rules) applied to the assumption dest_num r = SOME n   *)
let CMPEVPAUX_IH_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"; GSYM CONJ_ASSOC; IMP_CONJ;
                              RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1]) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP ih));;

let dest_num_num2bit = prove
 (`!thy. numeral_thy_ok thy ==>
     !x y. compute_dest_num x = SOME y ==>
           (thy,[]) |- num2bit y === x`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC compute_dest_num_ind THEN
  X_GEN_TAC `x:hol_term` THEN DISCH_TAC THEN X_GEN_TAC `y:num` THEN
  ONCE_REWRITE_TAC[compute_dest_num_def] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THENL
   [(* _0 *)
    ONCE_REWRITE_TAC[num2bit_def] THEN ASM_REWRITE_TAC[] THEN
    CMPSYNPAUX_EQN_TAC proves_REFL;
    (* BIT0 *)
    CMPEVPAUX_IH_TAC THEN
    ONCE_REWRITE_TAC[num2bit_def] THEN
    REWRITE_TAC[ARITH_RULE `2 * a = 0 <=> a = 0`; CMPEVPAUX_DIV_MOD_2] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
      ONCE_REWRITE_TAC[num2bit_def] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `_BIT0 _0` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[compute_BIT0_0];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN
        ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC];
      MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN CMPSYNPAUX_WT_TAC];
    (* BIT1 *)
    CMPEVPAUX_IH_TAC THEN
    ONCE_REWRITE_TAC[num2bit_def] THEN
    REWRITE_TAC[ARITH_RULE `~(2 * a + 1 = 0)`; CMPEVPAUX_DIV_MOD_2; ARITH_EQ] THEN
    MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CMPSYNPAUX_WT_TAC]);;

let num2bit_dest_numeral = prove
 (`!x s y s'.
     compute_dest_numeral (_NUMERAL x) s = (M_success y,s') /\
     numeral_thy_ok (thyof (hol_refs_the_context s)) ==>
       s = s' /\ (thyof (hol_refs_the_context s),[]) |- num2bit y === x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compute_dest_numeral_def] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def; PAIR_EQ;
              distinctness "exc"; injectivity "exc"] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP dest_num_num2bit) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let cexp2term_dest_numeral_opt = prove
 (`!x y thy.
     compute_dest_numeral_opt x = SOME y /\
     compute_thy_ok thy ==>
       (thy,[]) |- cexp2term (compute_Num y) === _CEXP_NUM x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compute_dest_numeral_opt_def] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `numeral_thy_ok thy` ASSUME_TAC THENL
   [ASM_SIMP_TAC[compute_thy_ok_numeral_thy_ok]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP (MATCH_MP dest_num_num2bit th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_eq_ok o
              check (is_comb o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num2bit_typeof]) THEN
  REWRITE_TAC[cexp2term_def] THEN
  MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
    CMPSYNPAUX_WT_TAC]);;

(* congruence for iterated applications *)
let CMPEVPAUX_MK_COMB = prove
 (`!thy l1 l2 r1 r2.
     (thy,[]) |- l1 === r1 /\ (thy,[]) |- l2 === r2 /\ welltyped (hol_Comb l1 l2)
     ==> (thy,[]) |- hol_Comb l1 l2 === hol_Comb r1 r2`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`[]:hol_term list`; `[]:hol_term list`; `l1:hol_term`; `l2:hol_term`;
                  `r1:hol_term`; `r2:hol_term`; `thy:thy`] proves_MK_COMB) THEN
  ASM_REWRITE_TAC[term_union_idem]);;

let CMPEVPAUX_welltyped_FOLDL = prove
 (`!l f. welltyped (FOLDL hol_Comb f l) ==> welltyped f`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL] THEN ASM_MESON_TAC[WELLTYPED_CLAUSES]);;

let CMPEVPAUX_FOLDL_cong = prove
 (`!l1 l2 f g thy.
     (thy,[]) |- f === g /\ welltyped (FOLDL hol_Comb f l1) /\
     ALL2 (\a b. (thy,[]) |- a === b) l1 l2
     ==> (thy,[]) |- FOLDL hol_Comb f l1 === FOLDL hol_Comb g l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; FOLDL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPEVPAUX_MK_COMB THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CMPEVPAUX_welltyped_FOLDL]);;

(* the lists of length 0, 1, 2, 3 and at least 4 *)
let CMPEVPAUX_LIST_CASES4 = prove
 (`!l:A list. l = [] \/ (?a. l = [a]) \/ (?a b. l = [a; b]) \/ (?a b c. l = [a; b; c]) \/
              ?a b c d e. l = CONS a (CONS b (CONS c (CONS d e)))`,
  GEN_TAC THEN
  MP_TAC (ISPEC `l:A list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  MP_TAC (ISPEC `t:A list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  TRY (MESON_TAC[]) THEN
  MP_TAC (ISPEC `t':A list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  TRY (MESON_TAC[]) THEN
  MP_TAC (ISPEC `t'':A list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let CMPEVPAUX_mapOption_I = prove
 (`!(l:(A option)list) cs. compute_mapOption I l = SOME cs ==> l = MAP SOME cs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[compute_mapOption_def; I_THM] THENL
   [MESON_TAC[injectivity "option"; MAP]; ALL_TAC] THEN
  GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[distinctness "option"]) THEN
  REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MAP; CONS_11] THEN ASM_MESON_TAC[]);;
let CMPEVPAUX_SHAPE_LEAF_TAC : tactic = fun (asl,w as g) ->
  let expr = lhs (fst (dest_imp w)) in
  let c,args = strip_comb expr in
  let cname = fst (dest_const c) in
  let mos = mapfilter (fun (_,th) -> MATCH_MP CMPEVPAUX_mapOption_I th) asl in
  if cname = "compute_Let" then
    (RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN ASM_MESON_TAC[]) g
  else if cname = "compute_Num" then
    (DISCH_THEN(SUBST_ALL_TAC o SYM) THEN (DISJ1_TAC ORELSE ALL_TAC) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"; HD]) THEN
     REWRITE_TAC[injectivity "compute_exp"] THEN ASM_MESON_TAC[]) g
  else
  let wit = if cname = "compute_App" then el 1 args
            else mk_list (filter (fun a -> type_of a = `:compute_exp`) args, `:compute_exp`) in
  let lens = mapfilter (fun (_,th) -> GSYM (MATCH_MP mapOption_LENGTH th)) asl in
  (DISCH_THEN(SUBST_ALL_TAC o SYM) THEN (DISJ2_TAC ORELSE ALL_TAC) THEN EXISTS_TAC wit THEN
   RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"]) THEN
   REWRITE_TAC (map GSYM mos @ lens) THEN
   ASM_REWRITE_TAC([MAP; LENGTH; LENGTH_MAP; app_type; cexp2term_def; bop2term_def;
                    uop2term_def; FOLDL; injectivity "hol_term"] @ lens)) g;;

(* the results of compute_dest_cexp at a constant other than LET: a       *)
(* number, or an application of the constant to the decoded arguments     *)
let CMPEVPAUX_dest_cexp_shape = prove
 (`!tm n ty xs cv.
     list_dest_comb [] tm = CONS (hol_Const n ty) xs /\
     ~(hol_Const n ty = _LET_TM) /\
     compute_dest_cexp tm = SOME cv
     ==> (hol_Const n ty = _CEXP_NUM_TM /\
          ?x m. xs = [x] /\ compute_dest_numeral_opt x = SOME m /\ cv = compute_Num m) \/
         (?cvs. MAP compute_dest_cexp xs = MAP SOME cvs /\
                ty = app_type (LENGTH xs) /\
                cexp2term cv = FOLDL hol_Comb (hol_Const n ty) (MAP cexp2term cvs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[compute_dest_cexp_def] o
                check (fun th -> can (find_term ((=) `compute_dest_cexp tm`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC (ISPEC `xs:hol_term list` CMPEVPAUX_LIST_CASES4) THEN
  ASM_REWRITE_TAC[MAP] THEN CAKE_REWRITE_TAC[] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  CMPEVPAUX_SHAPE_LEAF_TAC);;

let CMPEVPAUX_FOLDL_typeof = prove
 (`!l f. typeof f = app_type (LENGTH l) ==> typeof (FOLDL hol_Comb f l) = Cexp`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[FOLDL; LENGTH; app_type; typeof_def; codomain_def]);;

let CMPEVPAUX_ALL2_MAP_SOME = prove
 (`!xs cvs (f:A->(B)option) (g:B->C) R.
     MAP f xs = MAP SOME cvs /\
     (!x c. MEM x xs /\ f x = SOME c ==> R (g c) x)
     ==> ALL2 R (MAP g cvs) xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL2; NOT_CONS_NIL; CONS_11; MEM] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `f:A->(B)option` THEN
    ASM_MESON_TAC[]]);;

let dest_cexp_thm = prove
 (`!thy. compute_thy_ok thy ==>
     !tm cv.
       compute_dest_cexp tm = SOME cv ==>
       hol_term_ok (FST thy) tm ==>
         (thy,[]) |- cexp2term cv === tm /\
         typeof tm = Cexp`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC compute_dest_cexp_ind THEN
  X_GEN_TAC `tm:hol_term` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `cv:compute_exp` THEN
  MP_TAC (SPECL [`[]:hol_term list`; `tm:hol_term`] list_dest_comb_not_nil) THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `h:hol_term` (X_CHOOSE_THEN `t:hol_term list` ASSUME_TAC))
    (ISPEC `list_dest_comb [] tm` list_CASES) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL] THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_dest_comb_folds_back) THEN
  REWRITE_TAC[APPEND_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:hol_term list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `compute_dest_cexp (FOLDL hol_Comb h xs) = SOME cv` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[compute_dest_cexp_def] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if concl th = `list_dest_comb [] tm = CONS h xs` then th
    else REWRITE_RULE[ASSUME `list_dest_comb [] tm = CONS h xs`; CONS_11] th) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `tm:hol_term`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP term_ok_FOLDL_Comb o
    check (fun th -> try fst (dest_const (fst (strip_comb (concl th)))) = "hol_term_ok"
                     with Failure _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `SOME (cv:compute_exp)` &&
     not (fst (strip_comb (lhs (concl th))) = `compute_dest_cexp`))) THEN
  NAMED_CASES_ON "h" ["n ty"; "n ty"; "hf hx"; "hv hb"] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THENL
   [(* a variable: xs = [] and ty = Cexp *)
    STRUCT_CASES_TAC (ISPEC `xs:hol_term list` list_CASES) THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[cexp2term_def; FOLDL; typeof_def] THEN
    MATCH_MP_TAC proves_REFL THEN ASM_SIMP_TAC[compute_thy_ok_theory_ok];
    (* a constant *)
    DISCH_TAC THEN ASM_CASES_TAC `hol_Const n ty = _LET_TM` THENL
     [(* LET: xs = [Abs (Var s Cexp) y; x] *)
      FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `hol_Const n ty = _LET_TM`)) THEN
      REWRITE_TAC[injectivity "hol_term"] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
         rhs (concl th) = `SOME (cv:compute_exp)` &&
         not (fst (strip_comb (lhs (concl th))) = `compute_dest_cexp`))) THEN
      REWRITE_TAC[] THEN
      REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[distinctness "option"]) THEN
      REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"; CONS_11; GSYM CONJ_ASSOC;
                                  IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1;
                                  FORALL_UNWIND_THM2; ALL; CMPSYNPAUX_term_ok_Abs_Var]) THEN
      REPEAT (FIRST_X_ASSUM (fun ih -> FIRST_ASSUM (fun th ->
                let r = MATCH_MP ih th in
                if is_forall (concl r) || is_imp (concl r) then ASSUME_TAC r
                else failwith ""))) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
      REPEAT (FIRST_X_ASSUM (fun th ->
        STRIP_ASSUME_TAC (MP th (ASSUME (fst (dest_imp (concl th))))))) THEN
      REWRITE_TAC[cexp2term_def; FOLDL; typeof_def; codomain_def] THEN
      MATCH_MP_TAC CMPEVPAUX_MK_COMB THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CMPEVPAUX_MK_COMB THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC proves_REFL THEN ASM_SIMP_TAC[compute_thy_ok_theory_ok];
          MATCH_MP_TAC proves_ABS THEN ASM_REWRITE_TAC[EX];
          CMPSYNPAUX_WT_TAC];
        ASM_REWRITE_TAC[];
        CMPSYNPAUX_WT_TAC];
      (* not LET *)
      MP_TAC (SPECL [`FOLDL hol_Comb (hol_Const n ty) xs`; `n:mlstring`; `ty:hol_type`;
                       `xs:hol_term list`; `cv:compute_exp`] CMPEVPAUX_dest_cexp_shape) THEN
        ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[injectivity "hol_term"; CONS_11; GSYM CONJ_ASSOC;
                                    IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1;
                                    FORALL_UNWIND_THM2]) THEN
        FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP ih)) THEN
        STRIP_TAC THENL
         [(* a number *)
          REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
          ASM_REWRITE_TAC[FOLDL; typeof_def; codomain_def] THEN
          MATCH_MP_TAC cexp2term_dest_numeral_opt THEN ASM_REWRITE_TAC[];
          (* an application of the constant *)
          FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
            try lhs (concl th) = `ty:hol_type` with Failure _ -> false)) THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [MATCH_MP_TAC CMPEVPAUX_FOLDL_cong THEN REPEAT CONJ_TAC THENL
             [MATCH_MP_TAC proves_REFL THEN ASM_SIMP_TAC[compute_thy_ok_theory_ok];
              REWRITE_TAC[welltyped_def] THEN EXISTS_TAC `(Cexp)` THEN
              MATCH_MP_TAC CMPSYNPAUX_FOLDL_has_type THEN
              REWRITE_TAC[has_type_rules; cexp2term_has_type] THEN
              FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(compute_exp option)list->num` o
                check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
                  fst (strip_comb (lhs (concl th))) =
                  `MAP:(hol_term->(compute_exp)option)->hol_term list->(compute_exp option)list`))
              THEN
              REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
              REWRITE_TAC[has_type_rules];
              MATCH_MP_TAC CMPEVPAUX_ALL2_MAP_SOME THEN
              EXISTS_TAC `compute_dest_cexp` THEN ASM_REWRITE_TAC[] THEN
              REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
              FIRST_X_ASSUM(MP_TAC o SPEC `x:hol_term` o check (is_forall o concl)) THEN
              ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:compute_exp`) THEN
              ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
               [UNDISCH_TAC `ALL (hol_term_ok (FST (thy:thy))) xs` THEN
                REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
                SIMP_TAC[]]];
            MATCH_MP_TAC CMPEVPAUX_FOLDL_typeof THEN ASM_REWRITE_TAC[typeof_def]]]]]);;

let ALOOKUP_MAP_3 = prove
 (`!(f:A->C) (g:B->D) xs n.
     (!x y. f x = f y ==> x = y) ==>
       ALOOKUP (MAP (\(k,v). (f k,g v)) xs) (f n) =
       ALOOKUP (MAP (\(k,v). (k,g v)) xs) n`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_THM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALOOKUP_THM; FST; SND] THEN
  SUBGOAL_THEN `(f:A->C) p1 = f n <=> p1 = n` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let cexp_value_closed = prove
 (`!v. cexp_value v ==> cexp_vars v = {}`,
  MATCH_MP_TAC cexp_value_ind THEN
  SIMP_TAC[cexp_value_def; cexp_vars_def; UNION_EMPTY]);;

let CMPEVPAUX_MAP_FST_FILTER = prove
 (`!s (env:(mlstring#B)list).
     set_of_list (MAP FST (FILTER (\(n,x). ~(n = s)) env)) =
     set_of_list (MAP FST env) DIFF {s}`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP; set_of_list; EMPTY_DIFF] THEN
  SPEC_TAC(`h:mlstring#B`,`h:mlstring#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; set_of_list] THEN
  ASM SET_TAC[]);;

let CMPEVPAUX_UNIONS_MAP_DIFF = prove
 (`!(f:A->B->bool) s l.
     UNIONS (set_of_list (MAP (\y. f y DIFF s) l)) =
     UNIONS (set_of_list (MAP f l)) DIFF s`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0; EMPTY_DIFF] THEN
  SET_TAC[]);;

let closed_subst = prove
 (`!env v.
     ALL cexp_value (MAP SND env) ==>
       cexp_vars (compute_subst env v) = cexp_vars v DIFF set_of_list (MAP FST env)`,
  MATCH_MP_TAC compute_subst_ind THEN
  REWRITE_TAC[compute_subst_def; cexp_vars_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMPEVPAUX_ALL_MAP_FILTER] THENL
   [(* Var *)
    TOP_CASE_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ALOOKUP_NONE]) THEN
      REWRITE_TAC[cexp_vars_def; GSYM IN_SET_OF_LIST] THEN SET_TAC[];
      FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
      SUBGOAL_THEN `cexp_vars a = {}` SUBST1_TAC THENL
       [MATCH_MP_TAC cexp_value_closed THEN
        UNDISCH_TAC `ALL cexp_value (MAP SND (env:(mlstring#compute_exp)list))` THEN
        REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[SND];
        ALL_TAC] THEN
      SUBGOAL_THEN `(n:mlstring) IN set_of_list (MAP FST (env:(mlstring#compute_exp)list))`
        MP_TAC THENL
       [REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP] THEN ASM_MESON_TAC[FST]; SET_TAC[]]];
    (* (Num is solved by the simplification) Pair *)
    SET_TAC[];
    (* Uop *)
    SET_TAC[];
    (* Binop *)
    SET_TAC[];
    (* App *)
    SUBGOAL_THEN `MAP cexp_vars (MAP (compute_subst env) cs) =
                  MAP (\y. cexp_vars y DIFF set_of_list (MAP FST env)) cs`
      SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
      REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[CMPEVPAUX_UNIONS_MAP_DIFF]];
    (* If *)
    SET_TAC[];
    (* Let *)
    REWRITE_TAC[CMPEVPAUX_MAP_FST_FILTER] THEN SET_TAC[]]);;

let closed_subst' = prove
 (`!env v.
     ALL cexp_value (MAP SND env) /\
     cexp_vars v SUBSET set_of_list (MAP FST env) ==>
       cexp_vars (compute_subst env v) = {}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[closed_subst] THEN ASM SET_TAC[]);;


let VSUBST_FOLDL_Comb_push = prove
 (`!tms ilist t.
     FOLDL hol_Comb (VSUBST ilist t) (MAP (VSUBST ilist) tms) =
     VSUBST ilist (FOLDL hol_Comb t tms)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; MAP] THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 VSUBST_def)))]);;

let VSUBST_bop2term = prove
 (`!ilist bop x y.
     VSUBST ilist (bop2term bop x y) = bop2term bop (VSUBST ilist x) (VSUBST ilist y)`,
  GEN_TAC THEN MATCH_MP_TAC compute_binop_INDUCT THEN
  REWRITE_TAC[bop2term_def; VSUBST_def]);;
let _ = cake_add_simps [VSUBST_bop2term];;

let VSUBST_uop2term = prove
 (`!ilist uop x.
     VSUBST ilist (uop2term uop x) = uop2term uop (VSUBST ilist x)`,
  GEN_TAC THEN MATCH_MP_TAC uop_INDUCT THEN
  REWRITE_TAC[uop2term_def; VSUBST_def]);;
let _ = cake_add_simps [VSUBST_uop2term];;

let VFREE_IN_FOLDL = prove
 (`!ts v t.
     VFREE_IN v (FOLDL hol_Comb t ts) <=> EX (VFREE_IN v) ts \/ VFREE_IN v t`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; EX; VFREE_IN_def] THEN
  CONV_TAC TAUT);;

let CMPEVPAUX_num2bit_closed = prove
 (`!n x ty. ~VFREE_IN (hol_Var x ty) (num2bit n)`,
  MATCH_MP_TAC num2bit_ind THEN GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[num2bit_def] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VFREE_IN_def; distinctness "hol_term"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VFREE_IN_def; distinctness "hol_term"]);;

let VFREE_IN_cexp_vars = prove
 (`!v. cexp_vars v = {n | VFREE_IN (hol_Var n Cexp) (cexp2term v)}`,
  MATCH_MP_TAC cexp2term_ind THEN
  REWRITE_TAC[cexp2term_def; cexp_vars_def] THEN REPEAT CONJ_TAC THENL
   [(* Num *)
    REWRITE_TAC[VFREE_IN_def; distinctness "hol_term"; CMPEVPAUX_num2bit_closed;
                EMPTY_GSPEC];
    (* Pair *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; VFREE_IN_def;
                distinctness "hol_term"] THEN MESON_TAC[];
    (* Uop *)
    REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    STRUCT_CASES_TAC(SPEC `uop:uop` (cases "uop")) THEN
    REWRITE_TAC[uop2term_def; VFREE_IN_def; distinctness "hol_term"];
    (* Binop *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    STRUCT_CASES_TAC(SPEC `bop:compute_binop` (cases "compute_binop")) THEN
    REWRITE_TAC[bop2term_def; EXTENSION; IN_UNION; IN_ELIM_THM; VFREE_IN_def;
                distinctness "hol_term"] THEN MESON_TAC[];
    (* If *)
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; VFREE_IN_def;
                distinctness "hol_term"] THEN MESON_TAC[];
    (* Let *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_SING; IN_ELIM_THM; VFREE_IN_def;
                distinctness "hol_term"; injectivity "hol_term"] THEN MESON_TAC[];
    (* Var *)
    REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM; VFREE_IN_def;
                injectivity "hol_term"] THEN MESON_TAC[];
    (* App *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `MAP cexp_vars cs =
                  MAP (\y. {n | VFREE_IN (hol_Var n Cexp) (cexp2term y)}) cs`
      SUBST1_TAC THENL
     [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SET_OF_LIST_MAP; UNIONS_IMAGE; EXTENSION; IN_ELIM_THM;
                IN_SET_OF_LIST; VFREE_IN_FOLDL; VFREE_IN_def;
                distinctness "hol_term"; EX_MAP; GSYM EX_MEM; o_THM] THEN
    MESON_TAC[]]);;

let CMPEVPAUX_subst_Var = prove
 (`!env n.
     cexp2term (compute_subst env (compute_Var n)) =
     REV_ASSOCD (hol_Var n Cexp)
       (MAP (\(s,v). (cexp2term v, hol_Var s Cexp)) env) (hol_Var n Cexp)`,
  REWRITE_TAC[compute_subst_def] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; REV_ASSOCD; ALOOKUP_THM] THENL
   [CAKE_REWRITE_TAC[] THEN REWRITE_TAC[cexp2term_def]; ALL_TAC] THEN
  SPEC_TAC(`h:mlstring#compute_exp`,`h:mlstring#compute_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALOOKUP_THM; REV_ASSOCD; MAP; injectivity "hol_term"] THEN
  ASM_CASES_TAC `(p1:mlstring) = n` THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[]);;

let CMPEVPAUX_FILTER_ilist = prove
 (`!s env.
     FILTER (\(s',s0). ~(s0 = hol_Var s Cexp))
       (MAP (\(s,v). (cexp2term v, hol_Var s Cexp)) env) =
     MAP (\(s,v). (cexp2term v, hol_Var s Cexp)) (FILTER (\(n,x). ~(n = s)) env)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FILTER] THEN
  SPEC_TAC(`h:mlstring#compute_exp`,`h:mlstring#compute_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; FILTER; injectivity "hol_term"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let CMPEVPAUX_EX_closed = prove
 (`!l s tm.
     ALL (\v. cexp_vars v = {}) (MAP SND l) ==>
     ~EX (\(s',s0). VFREE_IN (hol_Var s Cexp) s' /\ VFREE_IN s0 tm)
         (MAP (\(s,v). (cexp2term v, hol_Var s Cexp)) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; EX; ALL] THEN
  SPEC_TAC(`h:mlstring#compute_exp`,`h:mlstring#compute_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; EX; ALL] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `cexp_vars p2 = {}` THEN
  REWRITE_TAC[VFREE_IN_cexp_vars; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let subst_VSUBST = prove
 (`!env x.
     ALL (\v. cexp_vars v = {}) (MAP SND env) ==>
       cexp2term (compute_subst env x) =
       VSUBST (MAP (\(s,v). (cexp2term v, hol_Var s Cexp)) env) (cexp2term x)`,
  MATCH_MP_TAC compute_subst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [(* Var *)
    DISCH_TAC THEN REWRITE_TAC[CMPEVPAUX_subst_Var; cexp2term_def; VSUBST_def];
    (* Num *)
    DISCH_TAC THEN
    REWRITE_TAC[compute_subst_def; cexp2term_def; VSUBST_def; num2bit_VSUBST];
    (* Pair *)
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[compute_subst_def; cexp2term_def; VSUBST_def];
    (* Uop *)
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[compute_subst_def; cexp2term_def; VSUBST_uop2term];
    (* Binop *)
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[compute_subst_def; cexp2term_def; VSUBST_bop2term];
    (* App *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[compute_subst_def; cexp2term_def; LENGTH_MAP] THEN
    REWRITE_TAC[GSYM VSUBST_FOLDL_Comb_push; VSUBST_def] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_SIMP_TAC[];
    (* If *)
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[compute_subst_def; cexp2term_def; VSUBST_def];
    (* Let *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `ALL (\v. cexp_vars v = {})
           (MAP SND (FILTER (\(n,x). ~(n = s)) (env:(mlstring#compute_exp)list)))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC CMPEVPAUX_ALL_MAP_FILTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[compute_subst_def; cexp2term_def; VSUBST_def; LET_DEF; LET_END_DEF;
                 CMPEVPAUX_FILTER_ilist; CMPEVPAUX_EX_closed]]);;

let MAP_subst_MAP_Var = prove
 (`!(xs:mlstring list) (ys:compute_exp list).
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ==>
       MAP (compute_subst (ZIP xs ys)) (MAP compute_Var xs) = ys`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; MAP] THEN MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  X_GEN_TAC `ys:compute_exp list` THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:compute_exp` (X_CHOOSE_THEN `ys':compute_exp list` SUBST1_TAC))
    (ISPEC `ys:compute_exp list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ALL_DISTINCT; SUC_INJ; MAP; ZIP] THEN
  STRIP_TAC THEN REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
   [REWRITE_TAC[compute_subst_def; ALOOKUP_THM] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `MAP (compute_subst (ZIP t ys')) (MAP compute_Var t)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    X_GEN_TAC `z:mlstring` THEN DISCH_TAC THEN
    REWRITE_TAC[compute_subst_def; ALOOKUP_THM] THEN
    SUBGOAL_THEN `~(h:mlstring = z)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let SAFEDIV_0 = prove
 (`!n. 0 SAFEDIV n = 0`,
  GEN_TAC THEN REWRITE_TAC[SAFEDIV_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[DIV_0]);;
let _ = cake_add_simps [SAFEDIV_0];;

let NUMERAL_ONE = prove
 (`!thy. numeral_thy_ok thy ==>
     (thy,[]) |- _NUMERAL (_SUC _0) === _SUC (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_TRANS_TAC NUMERAL_eqn THEN
  MATCH_MP_TAC MK_COMB_simple THEN EXISTS_TAC `(Num)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC proves_REFL THEN ASM_SIMP_TAC[numeral_thy_ok_theory_ok] THEN
    CMPSYNPAUX_WT_TAC;
    MATCH_MP_TAC sym_equation THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn;
    CMPSYNPAUX_WT_TAC;
    CMPSYNPAUX_WT_TAC;
    CMPSYNPAUX_WT_TAC]);;

(* the arguments of bop2term replaced along proved equations *)
let CMPEVPAUX_bop2term_cong = prove
 (`!thy bop p q x y z.
     (thy,[]) |- p === x /\ (thy,[]) |- q === y /\
     (thy,[]) |- bop2term bop x y === z ==>
     (thy,[]) |- bop2term bop p q === z`,
  GEN_TAC THEN MATCH_MP_TAC compute_binop_INDUCT THEN REWRITE_TAC[bop2term_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `x:hol_term` THEN
  ASM_SIMP_TAC[sym_equation] THEN
  MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `y:hol_term` THEN
  ASM_SIMP_TAC[sym_equation]);;

let CMPEVPAUX_num2bit_0 = prove
 (`num2bit 0 = _0`,
  ONCE_REWRITE_TAC[num2bit_def] THEN REWRITE_TAC[]);;

let CMPEVPAUX_NUMERAL_num2bit = prove
 (`!thy n. numeral_thy_ok thy ==> (thy,[]) |- _NUMERAL (num2bit n) === num2term n`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_TRANS_TAC NUMERAL_eqn THEN
  ASM_MESON_TAC[num2bit_num2term]);;

let CMPEVPAUX_num2term_NUMERAL =
  GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL CMPEVPAUX_NUMERAL_num2bit))));;

(* the numeral 1 *)
let CMPEVPAUX_SUC_NUMERAL_0 = prove
 (`!thy. numeral_thy_ok thy ==>
     (thy,[]) |- _SUC (_NUMERAL _0) === _NUMERAL (num2bit (SUC 0))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `_NUMERAL (_SUC _0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[NUMERAL_ONE];
    MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC sym_equation THEN
      MP_TAC (SPEC `thy:thy` num2bit_num2term) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC 0`) THEN REWRITE_TAC[num2term_def];
      CMPSYNPAUX_WT_TAC;
      CMPSYNPAUX_WT_TAC]]);;

(* the value of a test: _COND b 1 0 *)
let CMPEVPAUX_COND_bool2term = prove
 (`!thy b. numeral_thy_ok thy ==>
     (thy,[]) |- _COND (bool2term b) (_SUC (_NUMERAL _0)) (_NUMERAL _0) ===
                 _NUMERAL (num2bit (if b then SUC 0 else 0))`,
  REPEAT STRIP_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[bool2term_def] THENL
   [CMPSYNPAUX_TRANS_TAC (CMPSYNPAUX_cj 1 COND_eqn) THEN
    ASM_SIMP_TAC[CMPEVPAUX_SUC_NUMERAL_0];
    REWRITE_TAC[CMPEVPAUX_num2bit_0] THEN CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 2 COND_eqn)]);;

let CMPEVPAUX_CEXP_NUM_COND = prove
 (`!thy c b. compute_thy_ok thy /\ (thy,[]) |- c === bool2term b ==>
     (thy,[]) |- _CEXP_NUM (_COND c (_SUC (_NUMERAL _0)) (_NUMERAL _0)) ===
                 _CEXP_NUM (_NUMERAL (num2bit (if b then SUC 0 else 0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) c /\ welltyped c /\ typeof c = (Bool)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_eq_ok) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[term_ok_welltyped]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[bool2term_def; typeof_def];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `bool2term b` THEN CONJ_TAC THENL
     [MATCH_MP_TAC sym_equation THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMPEVPAUX_COND_bool2term THEN
      ASM_SIMP_TAC[compute_thy_ok_numeral_thy_ok]];
    CMPSYNPAUX_WT_TAC;
    CMPSYNPAUX_WT_TAC]);;

let CMPEVPAUX_term_ok_Pair = prove
 (`!sig a b. hol_term_ok sig (cexp2term (compute_Pair a b)) ==>
             hol_term_ok sig (cexp2term a) /\ hol_term_ok sig (cexp2term b)`,
  REWRITE_TAC[cexp2term_def; CMPSYNPAUX_term_ok_Comb_alt] THEN SIMP_TAC[]);;

let CMPEVPAUX_SAFE_0 = prove
 (`(!m. m SAFEDIV 0 = 0) /\ (!m. m SAFEMOD 0 = m) /\ (!n. 0 SAFEMOD n = 0)`,
  REWRITE_TAC[SAFEDIV_def; SAFEMOD_def; MOD_0; COND_ID]);;

(* HOL4's irule_at Any th on the first conjunct, side conditions by simp *)
let CMPEVPAUX_IRULE_TAC (th:thm) : tactic =
  IRULE_AT (Pos hd) th THEN CMPSYNPAUX_SIDE_TAC;;

(* the cases Num, Pair of a value variable, substituted *)
let CMPEVPAUX_VALUE_CASES_TAC (v:term) : tactic =
  UNDISCH_TAC (mk_comb(`cexp_value`,v)) THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_cexp_value_cases) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC;;

(* the four cases Num/Num, Num/Pair, Pair/Num, Pair/Pair of x and y *)
let CMPEVPAUX_VALUES_TAC (def:thm) : tactic =
  CMPEVPAUX_VALUE_CASES_TAC `x:compute_exp` THEN
  CMPEVPAUX_VALUE_CASES_TAC `y:compute_exp` THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP CMPEVPAUX_term_ok_Pair)) THEN
  REWRITE_TAC[def; st_ex_return_def; PAIR_EQ; injectivity "exc"; UNWIND_THM1;
              cexp2term_def; ADD_CLAUSES; SUB_0; MULT_CLAUSES; SAFEDIV_0;
              CMPEVPAUX_SAFE_0; CMPEVPAUX_num2bit_0];;

let CMPEVPAUX_ARITH_NN_TAC (eqn1:thm) (opth:thm) : tactic =
  CMPSYNPAUX_TRANS_TAC eqn1 THEN
  MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC replaceL1 THEN CMPEVPAUX_IRULE_TAC CMPEVPAUX_num2term_NUMERAL THEN
    MATCH_MP_TAC replaceL2 THEN CMPEVPAUX_IRULE_TAC CMPEVPAUX_num2term_NUMERAL THEN
    MATCH_MP_TAC trans_equation_simple THEN CMPEVPAUX_IRULE_TAC opth THEN
    CMPSYNPAUX_EQN_TAC CMPEVPAUX_num2term_NUMERAL;
    CMPSYNPAUX_WT_TAC;
    CMPSYNPAUX_WT_TAC];;

let CMPEVPAUX_ARITH_TAC (eqn1:thm) (opth:thm) (eqn2:thm) (eqn3:thm) (eqn4:thm) : tactic =
  CMPEVPAUX_VALUES_TAC compute_do_arith_def THENL
   [CMPEVPAUX_ARITH_NN_TAC eqn1 opth;
    CMPSYNPAUX_EQN_TAC eqn2;
    CMPSYNPAUX_EQN_TAC eqn3;
    CMPSYNPAUX_EQN_TAC eqn4];;

let CMPEVPAUX_LESS_NN_TAC : tactic =
  CMPSYNPAUX_TRANS_TAC CEXP_LESS_eqn1 THEN
  MATCH_MP_TAC CMPEVPAUX_CEXP_NUM_COND THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC replaceL1 THEN CMPEVPAUX_IRULE_TAC CMPEVPAUX_num2term_NUMERAL THEN
  MATCH_MP_TAC replaceL2 THEN CMPEVPAUX_IRULE_TAC CMPEVPAUX_num2term_NUMERAL THEN
  CMPSYNPAUX_EQN_TAC LESS_bool2term_num2term;;

(* do_binop on values: the equation for the values themselves *)
let CMPEVPAUX_do_binop_values = prove
 (`!thy bop x y (s:A).
     compute_thy_ok thy /\ cexp_value x /\ cexp_value y /\
     hol_term_ok (FST thy) (cexp2term x) /\ hol_term_ok (FST thy) (cexp2term y) ==>
     ?cv. compute_do_binop bop x y s = (M_success cv:(compute_exp,B)exc,s) /\
          (thy,[]) |- bop2term bop (cexp2term x) (cexp2term y) === cexp2term cv`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRUCT_CASES_TAC (SPEC `bop:compute_binop` (cases "compute_binop")) THEN
  REWRITE_TAC[compute_do_binop_def; bop2term_def] THENL
   [CMPEVPAUX_ARITH_TAC CEXP_ADD_eqn1 ADD_num2term CEXP_ADD_eqn2 CEXP_ADD_eqn3 CEXP_ADD_eqn4;
    CMPEVPAUX_ARITH_TAC CEXP_SUB_eqn1 SUB_num2term CEXP_SUB_eqn2 CEXP_SUB_eqn3 CEXP_SUB_eqn4;
    CMPEVPAUX_ARITH_TAC CEXP_MUL_eqn1 MUL_num2term CEXP_MUL_eqn2 CEXP_MUL_eqn3 CEXP_MUL_eqn4;
    CMPEVPAUX_ARITH_TAC CEXP_DIV_eqn1 DIV_num2term CEXP_DIV_eqn2 CEXP_DIV_eqn3 CEXP_DIV_eqn4;
    CMPEVPAUX_ARITH_TAC CEXP_MOD_eqn1 MOD_num2term CEXP_MOD_eqn2 CEXP_MOD_eqn3 CEXP_MOD_eqn4;
    (* Less *)
    CMPEVPAUX_VALUES_TAC compute_do_reln_def THENL
     [CMPEVPAUX_LESS_NN_TAC;
      CMPSYNPAUX_EQN_TAC CEXP_LESS_eqn2;
      CMPSYNPAUX_EQN_TAC CEXP_LESS_eqn3;
      CMPSYNPAUX_EQN_TAC CEXP_LESS_eqn4];
    (* Eq *)
    REWRITE_TAC[compute_do_eq_def; st_ex_return_def; PAIR_EQ; injectivity "exc";
                UNWIND_THM1; cexp2term_def] THEN
    CMPSYNPAUX_TRANS_TAC CEXP_EQ_eqn1 THEN
    MATCH_MP_TAC CMPEVPAUX_CEXP_NUM_COND THEN ASM_SIMP_TAC[EQ_bool2term_cexpterm]]);;

let do_binop_thm = prove
 (`!thy p q x y bop (s:A) (res:(compute_exp,B)exc) (s':A).
     compute_thy_ok thy ==>
       hol_term_ok (FST thy) (cexp2term p) /\
       hol_term_ok (FST thy) (cexp2term q) /\
       (thy,[]) |- cexp2term p === cexp2term x /\ cexp_value x /\
       (thy,[]) |- cexp2term q === cexp2term y /\ cexp_value y /\
       compute_do_binop bop x y s = (res,s') ==>
         s' = s /\
         ?cv. res = M_success cv /\
              (thy,[]) |- bop2term bop (cexp2term p) (cexp2term q) === cexp2term cv`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`thy:thy`; `bop:compute_binop`; `x:compute_exp`; `y:compute_exp`;
                  `s:A`] CMPEVPAUX_do_binop_values) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CMPSYNPAUX_proves_eq_ok]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cv:compute_exp` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `compute_do_binop bop x y (s:A) = (res:(compute_exp,B)exc,s')` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; UNWIND_THM1] THEN
  MATCH_MP_TAC CMPEVPAUX_bop2term_cong THEN
  MAP_EVERY EXISTS_TAC [`cexp2term x`; `cexp2term y`] THEN ASM_REWRITE_TAC[]);;

(* the argument of uop2term replaced along a proved equation *)
let CMPEVPAUX_uop2term_cong = prove
 (`!thy uop p x z.
     (thy,[]) |- p === x /\ (thy,[]) |- uop2term uop x === z ==>
     (thy,[]) |- uop2term uop p === z`,
  GEN_TAC THEN MATCH_MP_TAC uop_INDUCT THEN REWRITE_TAC[uop2term_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `x:hol_term` THEN
  ASM_SIMP_TAC[sym_equation]);;

(* do_uop on values: the equation for the value itself *)
let CMPEVPAUX_do_uop_values = prove
 (`!thy uop x (s:A).
     compute_thy_ok thy /\ cexp_value x /\ hol_term_ok (FST thy) (cexp2term x) ==>
     ?cv. compute_do_uop uop x s = (M_success cv:(compute_exp,B)exc,s) /\
          (thy,[]) |- uop2term uop (cexp2term x) === cexp2term cv`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRUCT_CASES_TAC (SPEC `uop:uop` (cases "uop")) THEN
  REWRITE_TAC[compute_do_uop_def; uop2term_def] THEN
  CMPEVPAUX_VALUE_CASES_TAC `x:compute_exp` THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP CMPEVPAUX_term_ok_Pair)) THEN
  REWRITE_TAC[compute_do_fst_def; compute_do_snd_def; compute_do_ispair_def;
              st_ex_return_def; PAIR_EQ; injectivity "exc"; UNWIND_THM1;
              cexp2term_def; CMPEVPAUX_num2bit_0] THENL
   [CMPSYNPAUX_EQN_TAC CEXP_FST_eqn2;
    CMPSYNPAUX_EQN_TAC CEXP_FST_eqn1;
    CMPSYNPAUX_EQN_TAC CEXP_SND_eqn2;
    CMPSYNPAUX_EQN_TAC CEXP_SND_eqn1;
    CMPSYNPAUX_EQN_TAC CEXP_ISPAIR_eqn2;
    REWRITE_TAC[ONE] THEN CMPSYNPAUX_TRANS_TAC CEXP_ISPAIR_eqn1 THEN
    MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPEVPAUX_SUC_NUMERAL_0 THEN
      ASM_SIMP_TAC[compute_thy_ok_numeral_thy_ok];
      CMPSYNPAUX_WT_TAC;
      CMPSYNPAUX_WT_TAC]]);;

let do_uop_thm = prove
 (`!thy p x uop (s:A) (res:(compute_exp,B)exc) (s':A).
     compute_thy_ok thy ==>
       hol_term_ok (FST thy) (cexp2term p) /\
       (thy,[]) |- cexp2term p === cexp2term x /\ cexp_value x /\
       compute_do_uop uop x s = (res,s') ==>
         s' = s /\
         ?cv. res = M_success cv /\
              (thy,[]) |- uop2term uop (cexp2term p) === cexp2term cv`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`thy:thy`; `uop:uop`; `x:compute_exp`; `s:A`]
                 CMPEVPAUX_do_uop_values) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CMPSYNPAUX_proves_eq_ok]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cv:compute_exp` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `compute_do_uop uop x (s:A) = (res:(compute_exp,B)exc,s')` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[injectivity "exc"; UNWIND_THM1] THEN
  MATCH_MP_TAC CMPEVPAUX_uop2term_cong THEN
  EXISTS_TAC `cexp2term x` THEN ASM_REWRITE_TAC[]);;

(* HOL4's statements; the facts were needed earlier, for subst_term_ok *)
let term_ok_bop2term = prove
 (`!sig bop tm1 tm2.
     hol_term_ok sig (bop2term bop tm1 tm2) ==>
       hol_term_ok sig tm1 /\ hol_term_ok sig tm2`,
  MATCH_ACCEPT_TAC CMPEVPAUX_bop2term_args);;

let term_ok_uop2term = prove
 (`!sig uop tm. hol_term_ok sig (uop2term uop tm) ==> hol_term_ok sig tm`,
  MATCH_ACCEPT_TAC CMPEVPAUX_uop2term_arg);;

let compute_eval_list_map = prove
 (`!ck ceqs cvs (s:hol_refs).
     compute_eval_list ck ceqs cvs s = compute_map (compute_eval ck ceqs) cvs s`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[compute_map_def; compute_eval_def] THEN
  ASM_REWRITE_TAC[st_ex_bind_def; FUN_EQ_THM]);;

let compute_thy_ok_is_std_sig = prove
 (`!thy. compute_thy_ok thy ==> is_std_sig (FST thy)`,
  MESON_TAC[compute_thy_ok_theory_ok; theory_ok_sig]);;

(* HOL4: Termination wf_rel_tac measure (compute_exp_size o SND) *)
let cexp_consts_ok_def = cake_def
  `(cexp_consts_ok (eqs:(mlstring#(A)list#B)list) (compute_Var s) <=> T) /\
   (cexp_consts_ok eqs (compute_Num n) <=> T) /\
   (cexp_consts_ok eqs (compute_Pair p q) <=>
      cexp_consts_ok eqs p /\ cexp_consts_ok eqs q) /\
   (cexp_consts_ok eqs (compute_If p q r) <=>
      cexp_consts_ok eqs p /\ cexp_consts_ok eqs q /\ cexp_consts_ok eqs r) /\
   (cexp_consts_ok eqs (compute_Uop uop p) <=> cexp_consts_ok eqs p) /\
   (cexp_consts_ok eqs (compute_Binop bop p q) <=>
      cexp_consts_ok eqs p /\ cexp_consts_ok eqs q) /\
   (cexp_consts_ok eqs (compute_Let s p q) <=>
      cexp_consts_ok eqs p /\ cexp_consts_ok eqs q) /\
   (cexp_consts_ok eqs (compute_App f cs) <=>
      MEM (f,LENGTH cs) (MAP (\(f,n,x). (f,LENGTH n)) eqs) /\
      ALL (cexp_consts_ok eqs) cs)`;;

let cexp_consts_ok_ind = cake_ind "cexp_consts_ok";;

let cexp_consts_ok_value = prove
 (`!(eqs:(mlstring#(A)list#B)list) cv. cexp_value cv ==> cexp_consts_ok eqs cv`,
  MATCH_MP_TAC cexp_consts_ok_ind THEN
  REWRITE_TAC[cexp_value_def; cexp_consts_ok_def] THEN MESON_TAC[]);;

let cexp_consts_ok_subst = prove
 (`!(eqs:(mlstring#(A)list#B)list) xs x.
     cexp_consts_ok eqs x /\ ALL (cexp_consts_ok eqs) (MAP SND xs) ==>
       cexp_consts_ok eqs (compute_subst xs x)`,
  GEN_TAC THEN MATCH_MP_TAC compute_subst_ind THEN
  REWRITE_TAC[compute_subst_def; cexp_consts_ok_def] THEN REPEAT CONJ_TAC THENL
   [(* Var *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN TOP_CASE_TAC THEN
    REWRITE_TAC[cexp_consts_ok_def] THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (cexp_consts_ok (eqs:(mlstring#(A)list#B)list))
                     (MAP SND (env:(mlstring#compute_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[SND];
    (* (Num and Uop are solved by the rewriting) Pair *)
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    (* Binop *)
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    (* App *)
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP; ALL_MAP] THEN
    UNDISCH_TAC `ALL (cexp_consts_ok (eqs:(mlstring#(A)list#B)list)) cs` THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_SIMP_TAC[];
    (* If *)
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    (* Let *)
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CMPEVPAUX_ALL_MAP_FILTER]]);;

(* HOL4's N.B.: a derivation of general beta conversion is hidden in here *)
let LET_VSUBST = prove
 (`!thy p q r s.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) q /\ hol_term_ok (FST thy) p /\ hol_term_ok (FST thy) r /\
     (thy,[]) |- p === r /\ p has_type Cexp /\ q has_type Cexp ==>
       (thy,[]) |- _LET (hol_Abs (hol_Var s Cexp) q) p ===
                   VSUBST [(r,hol_Var s Cexp)] q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r has_type (Cexp)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_eq_ok) THEN
    REWRITE_TAC[CMPSYNPAUX_has_type] THEN
    ASM_MESON_TAC[term_ok_welltyped; WELLTYPED_LEMMA];
    ALL_TAC] THEN
  SUBGOAL_THEN `type_ok (FST (FST (thy:thy))) (Cexp)` ASSUME_TAC THENL
   [SUBGOAL_THEN `typeof q = (Cexp)` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[WELLTYPED_LEMMA]; ALL_TAC] THEN
    MATCH_MP_TAC term_ok_type_ok THEN ASM_SIMP_TAC[compute_thy_ok_is_std_sig];
    ALL_TAC] THEN
  CMPSYNPAUX_TRANS_TAC LET_eqn THEN
  MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `r:hol_term` THEN CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC (ISPECL [`thy:thy`;
                  `hol_Comb (hol_Abs (hol_Var s Cexp) q) (hol_Var s Cexp) === q`;
                  `[r:hol_term,(s:mlstring),(Cexp)]`] CMPSYNPAUX_proves_INST) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC proves_BETA THEN ASM_SIMP_TAC[compute_thy_ok_theory_ok];
    ALL_TAC] THEN
  REWRITE_TAC[MAP; equation_def; VSUBST_def; REV_ASSOCD; FILTER; LET_DEF;
              LET_END_DEF; EX; VSUBST_NIL; typeof_def]);;

(* hol_term_ok of cexp2term of a compound expression: its parts *)
let CMPEVPAUX_term_ok_parts = prove
 (`(!sig p q r. hol_term_ok sig (cexp2term (compute_If p q r)) ==>
      hol_term_ok sig (cexp2term p) /\ hol_term_ok sig (cexp2term q) /\
      hol_term_ok sig (cexp2term r)) /\
   (!sig s p q. hol_term_ok sig (cexp2term (compute_Let s p q)) ==>
      hol_term_ok sig (cexp2term p) /\ hol_term_ok sig (cexp2term q)) /\
   (!sig f cs. hol_term_ok sig (cexp2term (compute_App f cs)) ==>
      ALL (hol_term_ok sig) (MAP cexp2term cs))`,
  REWRITE_TAC[cexp2term_def; CMPSYNPAUX_term_ok_Comb_alt; CMPSYNPAUX_term_ok_Abs_Var] THEN
  SIMP_TAC[] THEN MESON_TAC[term_ok_FOLDL_Comb]);;

(* the congruence for a binary application *)
let CMPEVPAUX_MK_COMB2 = prove
 (`!thy f a b x y.
     (thy,[]) |- a === x /\ (thy,[]) |- b === y /\
     hol_term_ok (FST thy) (hol_Comb (hol_Comb f x) y) ==>
     (thy,[]) |- hol_Comb (hol_Comb f a) b === hol_Comb (hol_Comb f x) y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `x:hol_term` THEN
  ASM_SIMP_TAC[sym_equation] THEN
  MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `y:hol_term` THEN
  ASM_SIMP_TAC[sym_equation] THEN
  MATCH_MP_TAC proves_REFL THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CMPSYNPAUX_proves_eq_ok]);;

(* the If step: the test evaluated to 0 or to a pair *)
let CMPEVPAUX_If_else = prove
 (`!thy p q r x cv'.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) (cexp2term (compute_If p q r)) /\
     (thy,[]) |- cexp2term p === cexp2term x /\
     (x = compute_Num 0 \/ ?a b. x = compute_Pair a b) /\
     (thy,[]) |- cexp2term r === cexp2term cv'
     ==> (thy,[]) |- cexp2term (compute_If p q r) === cexp2term cv'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 CMPEVPAUX_term_ok_parts)) THEN
  MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `cexp2term r` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[cexp2term_def] THEN
  MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `cexp2term x` THEN
  ASM_SIMP_TAC[sym_equation] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_eq_ok o
    check (fun th -> rand (rator (rand (concl th))) = `cexp2term p`)) THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP CMPEVPAUX_term_ok_Pair)) THEN
  REWRITE_TAC[cexp2term_def; CMPEVPAUX_num2bit_0] THENL
   [CMPSYNPAUX_EQN_TAC CEXP_IF_eqn3; CMPSYNPAUX_EQN_TAC CEXP_IF_eqn2]);;

(* the If step: the test evaluated to a positive number *)
let CMPEVPAUX_If_then = prove
 (`!thy p q r n cv'.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) (cexp2term (compute_If p q r)) /\
     (thy,[]) |- cexp2term p === cexp2term (compute_Num (SUC n)) /\
     (thy,[]) |- cexp2term q === cexp2term cv'
     ==> (thy,[]) |- cexp2term (compute_If p q r) === cexp2term cv'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 CMPEVPAUX_term_ok_parts)) THEN
  MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `cexp2term q` THEN
  ASM_REWRITE_TAC[cexp2term_def] THEN
  MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `_CEXP_NUM (_SUC (num2term n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC trans_equation_simple THEN
    EXISTS_TAC `cexp2term (compute_Num (SUC n))` THEN ASM_SIMP_TAC[sym_equation] THEN
    REWRITE_TAC[cexp2term_def] THEN MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC (SPECL [`thy:thy`; `SUC n`] CMPEVPAUX_num2term_NUMERAL) THEN
      ASM_SIMP_TAC[compute_thy_ok_numeral_thy_ok; num2term_def];
      CMPSYNPAUX_WT_TAC;
      CMPSYNPAUX_WT_TAC];
    CMPSYNPAUX_EQN_TAC CEXP_IF_eqn1]);;

(* the Let step *)
let CMPEVPAUX_Let_eqn = prove
 (`!thy s p q a cv'.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) (cexp2term (compute_Let s p q)) /\
     (thy,[]) |- cexp2term p === cexp2term a /\ cexp_value a /\
     (thy,[]) |- cexp2term (compute_subst [s,a] q) === cexp2term cv'
     ==> (thy,[]) |- cexp2term (compute_Let s p q) === cexp2term cv'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 (CONJUNCT2 CMPEVPAUX_term_ok_parts))) THEN
  REWRITE_TAC[cexp2term_def] THEN
  MATCH_MP_TAC trans_equation_simple THEN
  EXISTS_TAC `VSUBST [(cexp2term a, hol_Var s Cexp)] (cexp2term q)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LET_VSUBST THEN ASM_REWRITE_TAC[cexp2term_has_type] THEN
    ASM_MESON_TAC[CMPSYNPAUX_proves_eq_ok];
    MP_TAC (ISPECL [`[s:mlstring,a:compute_exp]`; `q:compute_exp`] subst_VSUBST) THEN
    REWRITE_TAC[MAP; ALL] THEN ASM_SIMP_TAC[cexp_value_closed] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

let CMPEVPAUX_ALL2_RIGHT = prove
 (`!(R:A->B->bool) Q l1 l2. ALL2 R l1 l2 /\ (!x y. R x y ==> Q y) ==> ALL Q l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALL] THEN ASM_MESON_TAC[]);;

(* the App step: the arguments evaluated to bs, then the instance of the *)
(* defining equation evaluated to cv'                                     *)
let CMPEVPAUX_App_eqn = prove
 (`!thy f cs bs args exp r cv'.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) (cexp2term (compute_App f cs)) /\
     ALL2 (\cv cv'. (thy,[]) |- cexp2term cv === cexp2term cv') cs bs /\
     ALL cexp_value bs /\
     ALL_DISTINCT args /\ LENGTH args = LENGTH bs /\
     (thy,[]) |- cexp2term (compute_App f (MAP compute_Var args)) === r /\
     compute_dest_cexp r = SOME exp /\
     (thy,[]) |- cexp2term (compute_subst (ZIP args bs) exp) === cexp2term cv'
     ==> (thy,[]) |- cexp2term (compute_App f cs) === cexp2term cv'`,
  REPEAT STRIP_TAC THEN
  (* the defining equation, as an equation of expressions *)
  SUBGOAL_THEN
    `(thy,[]) |- cexp2term (compute_App f (MAP compute_Var args)) === cexp2term exp`
    ASSUME_TAC THENL
   [MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `r:hol_term` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC sym_equation THEN
    MP_TAC (SPEC `thy:thy` dest_cexp_thm) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:hol_term`; `exp:compute_exp`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[CMPSYNPAUX_proves_eq_ok]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the values bs *)
  SUBGOAL_THEN `ALL (\b. hol_term_ok (FST (thy:thy)) (cexp2term b)) bs` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`\cv cv'. (thy,[]) |- cexp2term cv === cexp2term cv'`;
                          `\b. hol_term_ok (FST (thy:thy)) (cexp2term b)`;
                          `cs:compute_exp list`; `bs:compute_exp list`]
                         CMPEVPAUX_ALL2_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CMPSYNPAUX_proves_eq_ok];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\v. cexp_vars v = {}) (MAP SND (ZIP (args:mlstring list) (bs:compute_exp list)))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[MAP_SND_ZIP] THEN UNDISCH_TAC `ALL cexp_value bs` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[cexp_value_closed];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!s s'. MEM (s',s) (MAP (\(s,v). (cexp2term v, hol_Var s Cexp))
                            (ZIP (args:mlstring list) (bs:compute_exp list))) ==>
            ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok (FST (thy:thy)) s'`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:mlstring`; `b:compute_exp`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:mlstring`; `(Cexp)`] THEN
    ASM_REWRITE_TAC[cexp2term_has_type] THEN
    UNDISCH_TAC `ALL (\b. hol_term_ok (FST (thy:thy)) (cexp2term b)) bs` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `MEM (b:compute_exp) (MAP SND (ZIP (args:mlstring list) (bs:compute_exp list)))`
      MP_TAC THENL
     [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(x:mlstring,b:compute_exp)` THEN
      ASM_REWRITE_TAC[SND];
      ASM_SIMP_TAC[MAP_SND_ZIP]];
    ALL_TAC] THEN
  (* the instance of the defining equation *)
  SUBGOAL_THEN
    `(thy,[]) |- VSUBST (MAP (\(s,v). (cexp2term v, hol_Var s Cexp))
                             (ZIP (args:mlstring list) (bs:compute_exp list)))
                   (cexp2term (compute_App f (MAP compute_Var args)) === cexp2term exp)`
    MP_TAC THENL
   [MP_TAC (ISPECL [`cexp2term (compute_App f (MAP compute_Var args)) === cexp2term exp`;
                    `[]:hol_term list`;
                    `MAP (\(s,v). (cexp2term v, hol_Var s Cexp))
                         (ZIP (args:mlstring list) (bs:compute_exp list))`;
                    `thy:thy`] proves_INST) THEN
    REWRITE_TAC[term_image_nil] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `typeof (VSUBST (MAP (\(s,v). (cexp2term v, hol_Var s Cexp))
                         (ZIP (args:mlstring list) (bs:compute_exp list)))
                    (cexp2term (compute_App f (MAP compute_Var args)))) =
     typeof (cexp2term (compute_App f (MAP compute_Var args)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[cexp2term_typeof] THEN MATCH_MP_TAC WELLTYPED_LEMMA THEN
    MATCH_MP_TAC VSUBST_HAS_TYPE THEN REWRITE_TAC[cexp2term_has_type] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[equation_def; VSUBST_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM equation_def] THEN
  MP_TAC (ISPECL [`ZIP (args:mlstring list) (bs:compute_exp list)`;
                  `compute_App f (MAP compute_Var args)`] subst_VSUBST) THEN
  MP_TAC (ISPECL [`ZIP (args:mlstring list) (bs:compute_exp list)`; `exp:compute_exp`] subst_VSUBST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[compute_subst_def] THEN ASM_SIMP_TAC[MAP_subst_MAP_Var] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `cexp2term (compute_App f bs)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC trans_equation_simple THEN
    EXISTS_TAC `cexp2term (compute_subst (ZIP args bs) exp)` THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[equation_def; cexp2term_typeof]] THEN
  (* the arguments cs replaced by their values bs *)
  SUBGOAL_THEN `LENGTH (bs:compute_exp list) = LENGTH (cs:compute_exp list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_EL_EQN]; ALL_TAC] THEN
  REWRITE_TAC[cexp2term_def] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPEVPAUX_FOLDL_cong THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC proves_REFL THEN ASM_SIMP_TAC[compute_thy_ok_theory_ok] THEN
    UNDISCH_TAC `hol_term_ok (FST (thy:thy)) (cexp2term (compute_App f cs))` THEN
    REWRITE_TAC[cexp2term_def] THEN MESON_TAC[term_ok_FOLDL_Comb];
    UNDISCH_TAC `hol_term_ok (FST (thy:thy)) (cexp2term (compute_App f cs))` THEN
    REWRITE_TAC[cexp2term_def] THEN MESON_TAC[term_ok_welltyped];
    REWRITE_TAC[ALL2_MAP2] THEN ASM_REWRITE_TAC[]]);;

let CMPEVPAUX_proves_rhs_ok = prove
 (`!thy x y. (thy,[]) |- x === y ==> hol_term_ok (FST thy) y`,
  MESON_TAC[CMPSYNPAUX_proves_eq_ok]);;

let CMPEVPAUX_proves_lhs_ok = prove
 (`!thy x y. (thy,[]) |- x === y ==> hol_term_ok (FST thy) x`,
  MESON_TAC[CMPSYNPAUX_proves_eq_ok]);;

(* the case set-up: the IHs with the eqs condition discharged *)
let CMPEVPAUX_EV_PREP_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  POP_ASSUM (fun eqs -> RULE_ASSUM_TAC (REWRITE_RULE [eqs]) THEN ASSUME_TAC eqs) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* the monadic plumbing *)
let CMPEVPAUX_EV_SIMP_TAC : tactic =
  CAKE_REWRITE_TAC[st_ex_return_def; st_ex_bind_def; st_ex_ignore_bind_def;
                   PAIR_EQ; injectivity "exc";
                   distinctness "exc"; UNWIND_THM1; holKernel_raise_Failure_def];;

(* cases on an evaluation compute_eval ck ceqs e st (st free) of the goal *)
(* by its induction hypothesis !s. C ==> ...; side proves C.  In the     *)
(* success case the equation, the value and hol_term_ok of the result    *)
(* are kept                                                               *)
let CMPEVPAUX_EVAL_CASES_TAC (side:tactic) : tactic = fun (asl,w as g) ->
  let is_ev t = try let f,args = strip_comb t in
                    let n = fst (dest_const f) in
                    (n = "compute_eval" || n = "compute_eval_list") && length args = 4
                with Failure _ -> false in
  let evs = filter (fun t -> free_in t w) (find_terms is_ev w) in
  let cands = List.concat (map (fun ev ->
      let st = rand ev in
      mapfilter (fun (_,th) ->
        let th' = SPEC st th in
        let c = concl th' in
        if is_imp c && free_in ev (rand c) then th' else failwith "no") asl) evs) in
  if cands = [] then failwith "CMPEVPAUX_EVAL_CASES_TAC" else
  (MP_TAC (hd cands) THEN ANTS_TAC THENL [side; ALL_TAC] THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
     (CHOOSE_THEN (CONJUNCTS_THEN2
        (fun eq -> SUBST1_TAC eq THEN ASSUME_TAC eq THEN
           TRY (fun g -> ASSUME_TAC (MATCH_MP (CONJUNCT1 compute_eval_value) eq) g) THEN
           TRY (fun g -> ASSUME_TAC (MATCH_MP (CONJUNCT2 compute_eval_value) eq) g))
        (fun pr -> ASSUME_TAC pr THEN
           TRY (fun g -> ASSUME_TAC (MATCH_MP CMPEVPAUX_proves_rhs_ok pr) g)))))) g;;

(* do_uop, do_binop of values in the goal by their value lemmas *)
let CMPEVPAUX_DO_TAC (lemma:thm) (cname:string) (n:int) : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try let f,args = strip_comb t in
                                  fst (dest_const f) = cname && length args = n &&
                                  free_in t w
                              with Failure _ -> false) w in
  let args = snd (strip_comb t) in
  let lemma' = INST_TYPE [`:hol_exn`,`:B`] lemma in
  (MP_TAC (ISPECL (`thy:thy` :: args) lemma') THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `cv:compute_exp` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))]) g;;

(* the eqs condition ALL (\(f,vs,cv). ...) ceqs among the assumptions *)
let CMPEVPAUX_EQS_ALL_TAC (ttac:thm_tactic) : tactic =
  FIRST_ASSUM(ttac o check (fun th ->
    let c = concl th in
    try let f,args = strip_comb c in
        fst (dest_const f) = "ALL" && length args = 2 &&
        is_var (el 1 args) && fst (dest_var (el 1 args)) = "ceqs"
    with Failure _ -> false));;

(* compute_eval_thm in the form: the result is the timeout or a value  *)
(* proved equal; the eqs condition outside the quantifier over states   *)
let CMPEVPAUX_eval_thm = prove
 (`!thy. compute_thy_ok thy ==>
     (!ck ceqs cv.
        ALL_DISTINCT (MAP FST (ceqs:(mlstring#mlstring list#compute_exp)list)) /\
        ALL (\(f,vs,cv). ALL_DISTINCT vs /\ cexp_consts_ok ceqs cv /\
              ?r. (thy,[]) |- cexp2term (compute_App f (MAP compute_Var vs)) === r /\
                  compute_dest_cexp r = SOME cv /\
                  cexp_vars cv SUBSET set_of_list vs) ceqs ==>
        !s:hol_refs.
          hol_term_ok (FST thy) (cexp2term cv) /\ cexp_vars cv = {} /\
          cexp_consts_ok ceqs cv ==>
          compute_eval ck ceqs cv s =
            (M_failure (holKernel_Failure (implode "timeout")),s) \/
          ?cv'. compute_eval ck ceqs cv s = (M_success cv',s) /\
                (thy,[]) |- cexp2term cv === cexp2term cv') /\
     (!ck ceqs cvs.
        ALL_DISTINCT (MAP FST (ceqs:(mlstring#mlstring list#compute_exp)list)) /\
        ALL (\(f,vs,cv). ALL_DISTINCT vs /\ cexp_consts_ok ceqs cv /\
              ?r. (thy,[]) |- cexp2term (compute_App f (MAP compute_Var vs)) === r /\
                  compute_dest_cexp r = SOME cv /\
                  cexp_vars cv SUBSET set_of_list vs) ceqs ==>
        !s:hol_refs.
          ALL (hol_term_ok (FST thy)) (MAP cexp2term cvs) /\
          ALL (\cv. cexp_vars cv = {}) cvs /\ ALL (cexp_consts_ok ceqs) cvs ==>
          compute_eval_list ck ceqs cvs s =
            (M_failure (holKernel_Failure (implode "timeout")),s) \/
          ?cvs'. compute_eval_list ck ceqs cvs s = (M_success cvs',s) /\
                 ALL2 (\cv cv'. (thy,[]) |- cexp2term cv === cexp2term cv') cvs cvs')`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC compute_eval_ind THEN
  REPEAT CONJ_TAC THENL
   [(* Var *)
    CMPEVPAUX_EV_PREP_TAC THEN REWRITE_TAC[cexp_vars_def; NOT_INSERT_EMPTY];
    (* Num *)
    CMPEVPAUX_EV_PREP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN CMPEVPAUX_EV_SIMP_TAC THEN
    MATCH_MP_TAC proves_REFL THEN ASM_SIMP_TAC[compute_thy_ok_theory_ok];
    (* Pair *)
    CMPEVPAUX_EV_PREP_TAC THEN
    GEN_TAC THEN REWRITE_TAC[cexp_vars_def; cexp_consts_ok_def; EMPTY_UNION] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPEVPAUX_term_ok_Pair) THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN REWRITE_TAC[st_ex_bind_def] THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    REWRITE_TAC[cexp2term_def] THEN MATCH_MP_TAC CMPEVPAUX_MK_COMB2 THEN
    ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
    (* Uop *)
    CMPEVPAUX_EV_PREP_TAC THEN
    GEN_TAC THEN REWRITE_TAC[cexp_vars_def; cexp_consts_ok_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (cexp2term p)` ASSUME_TAC THENL
     [UNDISCH_TAC `hol_term_ok (FST (thy:thy)) (cexp2term (compute_Uop uop p))` THEN
      REWRITE_TAC[cexp2term_def] THEN MESON_TAC[term_ok_uop2term]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN REWRITE_TAC[st_ex_bind_def] THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    CMPEVPAUX_DO_TAC CMPEVPAUX_do_uop_values "compute_do_uop" 3 THEN
    CMPEVPAUX_EV_SIMP_TAC THEN
    REWRITE_TAC[cexp2term_def] THEN MATCH_MP_TAC CMPEVPAUX_uop2term_cong THEN
    EXISTS_TAC `cexp2term cv'` THEN ASM_REWRITE_TAC[];
    (* Binop *)
    CMPEVPAUX_EV_PREP_TAC THEN
    GEN_TAC THEN REWRITE_TAC[cexp_vars_def; cexp_consts_ok_def; EMPTY_UNION] THEN STRIP_TAC THEN
    SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (cexp2term p) /\
                  hol_term_ok (FST (thy:thy)) (cexp2term q)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `hol_term_ok (FST (thy:thy)) (cexp2term (compute_Binop bop p q))` THEN
      REWRITE_TAC[cexp2term_def] THEN MESON_TAC[term_ok_bop2term]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN REWRITE_TAC[st_ex_bind_def] THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    CMPEVPAUX_DO_TAC CMPEVPAUX_do_binop_values "compute_do_binop" 4 THEN
    CMPEVPAUX_EV_SIMP_TAC THEN
    REWRITE_TAC[cexp2term_def] THEN MATCH_MP_TAC CMPEVPAUX_bop2term_cong THEN
    MAP_EVERY EXISTS_TAC [`cexp2term cv'`; `cexp2term cv''`] THEN ASM_REWRITE_TAC[];
    (* App *)
    CMPEVPAUX_EV_PREP_TAC THEN
    GEN_TAC THEN REWRITE_TAC[cexp_consts_ok_def] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN
    ASM_CASES_TAC `ck = 0` THEN ASM_REWRITE_TAC[] THENL
     [CMPEVPAUX_EV_SIMP_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun ckth -> RULE_ASSUM_TAC (REWRITE_RULE[ckth]) THEN ASSUME_TAC ckth) THEN
    SUBGOAL_THEN `?args exp. ALOOKUP (ceqs:(mlstring#mlstring list#compute_exp)list) f = SOME (args,exp) /\
                             LENGTH (args:mlstring list) = LENGTH (cs:compute_exp list)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `MEM (f,LENGTH (cs:compute_exp list)) (MAP (\(f,n,x). (f,LENGTH n))
                     (ceqs:(mlstring#mlstring list#compute_exp)list))` THEN
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN STRIP_TAC THEN
      ASM_MESON_TAC[MEM_ALOOKUP];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[compute_option_def; compute_check_def] THEN CMPEVPAUX_EV_SIMP_TAC THEN
    ASM_REWRITE_TAC[] THEN CMPEVPAUX_EV_SIMP_TAC THEN
    CMPEVPAUX_EVAL_CASES_TAC
     (ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 CMPEVPAUX_term_ok_parts)) THEN
        EXISTS_TAC `f:mlstring` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `cexp_vars (compute_App f cs) = {}` THEN
        REWRITE_TAC[cexp_vars_def; EMPTY_UNIONS; IN_SET_OF_LIST; MEM_MAP; GSYM ALL_MEM] THEN
        MESON_TAC[]]) THEN
    CMPEVPAUX_EV_SIMP_TAC THEN
    SUBGOAL_THEN `ALL_DISTINCT (args:mlstring list) /\
                  cexp_consts_ok (ceqs:(mlstring#mlstring list#compute_exp)list) exp /\
                  ?r. (thy,[]) |- cexp2term (compute_App f (MAP compute_Var args)) === r /\
                      compute_dest_cexp r = SOME exp /\ cexp_vars exp SUBSET set_of_list args`
      STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM o check (fun th ->
        is_eq (concl th) &&
        (try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "ALOOKUP"
         with Failure _ -> false))) THEN
      CMPEVPAUX_EQS_ALL_TAC (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN
      DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(thy,[]) |- cexp2term exp === r` ASSUME_TAC THENL
     [MP_TAC (SPEC `thy:thy` dest_cexp_thm) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`r:hol_term`; `exp:compute_exp`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MATCH_MP_TAC CMPEVPAUX_proves_rhs_ok THEN
        EXISTS_TAC `cexp2term (compute_App f (MAP compute_Var args))` THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (cs:compute_exp list) = LENGTH (cvs':compute_exp list)` ASSUME_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[LIST_REL_EL_EQN] o check (fun th ->
        try fst (dest_const (fst (strip_comb (concl th)))) = "ALL2" with Failure _ -> false));
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (args:mlstring list) = LENGTH (cvs':compute_exp list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `MAP FST (ZIP (args:mlstring list) (cvs':compute_exp list)) = args /\
                  MAP SND (ZIP (args:mlstring list) (cvs':compute_exp list)) = cvs'`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC MAP_FST_ZIP; MATCH_MP_TAC MAP_SND_ZIP] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o
      SPECL [`args:mlstring list`; `cvs':compute_exp list`; `exp:compute_exp`] o
      check (fun th -> try fst (dest_var (fst (dest_forall (concl th)))) = "args"
                       with Failure _ -> false)) THEN
    CMPEVPAUX_EVAL_CASES_TAC
     (REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC subst_term_ok THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CMPEVPAUX_proves_lhs_ok THEN EXISTS_TAC `r:hol_term` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC (ISPECL [`\cv cv'. (thy,[]) |- cexp2term cv === cexp2term cv'`;
                                `hol_term_ok (FST (thy:thy)) o cexp2term`;
                                `cs:compute_exp list`; `cvs':compute_exp list`]
                               CMPEVPAUX_ALL2_RIGHT) THEN
          ASM_REWRITE_TAC[o_THM] THEN MESON_TAC[CMPEVPAUX_proves_rhs_ok]];
        MATCH_MP_TAC closed_subst' THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC cexp_consts_ok_subst THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `ALL cexp_value (cvs':compute_exp list)` THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN
        MESON_TAC[ISPEC `ceqs:(mlstring#mlstring list#compute_exp)list`
                        cexp_consts_ok_value]]) THEN
    CMPEVPAUX_EV_SIMP_TAC THEN
    MATCH_MP_TAC CMPEVPAUX_App_eqn THEN
    MAP_EVERY EXISTS_TAC [`cvs':compute_exp list`; `args:mlstring list`; `exp:compute_exp`;
                          `r:hol_term`] THEN
    ASM_REWRITE_TAC[];
    (* If *)
    CMPEVPAUX_EV_PREP_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o (fun th -> MP th (SPEC `0` NOT_SUC)) o SPEC `SUC 0` o
      check (fun th -> try type_of (fst (dest_forall (concl th))) = `:num`
                       with Failure _ -> false)) THEN
    GEN_TAC THEN REWRITE_TAC[cexp_vars_def; cexp_consts_ok_def; EMPTY_UNION] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 CMPEVPAUX_term_ok_parts)) THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN REWRITE_TAC[st_ex_bind_def] THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    CMPEVPAUX_VALUE_CASES_TAC `cv':compute_exp` THEN CMPEVPAUX_EV_SIMP_TAC THENL
     [DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)
        (SPEC `m:num` num_CASES) THEN
      REWRITE_TAC[COND_RATOR; NOT_SUC] THEN
      CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THENL
       [MATCH_MP_TAC CMPEVPAUX_If_else THEN EXISTS_TAC `compute_Num 0` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CMPEVPAUX_If_then THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
      CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
      MATCH_MP_TAC CMPEVPAUX_If_else THEN EXISTS_TAC `compute_Pair a b` THEN
      ASM_REWRITE_TAC[distinctness "compute_exp"; injectivity "compute_exp"] THEN
      MESON_TAC[]];
    (* Let *)
    CMPEVPAUX_EV_PREP_TAC THEN
    GEN_TAC THEN REWRITE_TAC[cexp_vars_def; cexp_consts_ok_def; EMPTY_UNION] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      MATCH_MP (CONJUNCT1 (CONJUNCT2 CMPEVPAUX_term_ok_parts))) THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN
    ASM_CASES_TAC `ck = 0` THEN ASM_REWRITE_TAC[] THENL [CMPEVPAUX_EV_SIMP_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun ckth -> RULE_ASSUM_TAC (REWRITE_RULE[ckth]) THEN ASSUME_TAC ckth) THEN
    REWRITE_TAC[st_ex_bind_def] THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o SPEC `cv':compute_exp` o
      check (fun th -> try type_of (fst (dest_forall (concl th))) = `:compute_exp`
                       with Failure _ -> false)) THEN
    CMPEVPAUX_EVAL_CASES_TAC
     (REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC subst_term_ok THEN ASM_REWRITE_TAC[MAP; ALL; SND; o_THM];
        MATCH_MP_TAC closed_subst' THEN ASM_REWRITE_TAC[MAP; ALL; SND; FST; set_of_list] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC cexp_consts_ok_subst THEN ASM_REWRITE_TAC[MAP; ALL; SND] THEN
        MATCH_MP_TAC cexp_consts_ok_value THEN ASM_REWRITE_TAC[]]) THEN
    CMPEVPAUX_EV_SIMP_TAC THEN
    MATCH_MP_TAC CMPEVPAUX_Let_eqn THEN EXISTS_TAC `cv':compute_exp` THEN
    ASM_REWRITE_TAC[];
    (* Nil *)
    CMPEVPAUX_EV_PREP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN CMPEVPAUX_EV_SIMP_TAC THEN REWRITE_TAC[ALL2];
    (* Cons *)
    CMPEVPAUX_EV_PREP_TAC THEN
    GEN_TAC THEN REWRITE_TAC[MAP; ALL] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[compute_eval_def] THEN REWRITE_TAC[st_ex_bind_def] THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    CMPEVPAUX_EVAL_CASES_TAC (ASM_REWRITE_TAC[]) THEN CMPEVPAUX_EV_SIMP_TAC THEN
    ASM_REWRITE_TAC[ALL2]]);;

(* HOL4 quantifies an unused variable tm in both conjuncts; it is left out *)
let compute_eval_thm = prove
 (`!thy. compute_thy_ok thy ==>
     (!ck eqs cv (s:hol_refs) res s'.
        compute_eval ck eqs cv s = (res,s') /\
        hol_term_ok (FST thy) (cexp2term cv) /\
        cexp_vars cv = {} /\
        cexp_consts_ok eqs cv /\
        ALL_DISTINCT (MAP FST eqs) /\
        ALL (\(f,vs,cv).
              ALL_DISTINCT vs /\
              cexp_consts_ok eqs cv /\
              ?r. (thy,[]) |- cexp2term (compute_App f (MAP compute_Var vs)) === r /\
                  compute_dest_cexp r = SOME cv /\
                  cexp_vars cv SUBSET set_of_list vs) eqs ==>
          s' = s /\
          (!err. res = M_failure err ==> err = holKernel_Failure (implode "timeout")) /\
          !cv'. res = M_success cv' ==> (thy,[]) |- cexp2term cv === cexp2term cv') /\
     (!ck eqs cvs (s:hol_refs) res s'.
        compute_eval_list ck eqs cvs s = (res,s') /\
        ALL (hol_term_ok (FST thy)) (MAP cexp2term cvs) /\
        ALL (\cv. cexp_vars cv = {}) cvs /\
        ALL (cexp_consts_ok eqs) cvs /\
        ALL_DISTINCT (MAP FST eqs) /\
        ALL (\(f,vs,cv).
              ALL_DISTINCT vs /\
              cexp_consts_ok eqs cv /\
              ?r. (thy,[]) |- cexp2term (compute_App f (MAP compute_Var vs)) === r /\
                  compute_dest_cexp r = SOME cv /\
                  cexp_vars cv SUBSET set_of_list vs) eqs ==>
          s' = s /\
          (!err. res = M_failure err ==> err = holKernel_Failure (implode "timeout")) /\
          !cvs'. res = M_success cvs' ==>
            ALL2 (\cv cv'. (thy,[]) |- cexp2term cv === cexp2term cv') cvs cvs')`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CMPEVPAUX_eval_thm) THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o
      SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`; `cv:compute_exp`] o
      check (can (SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`;
                         `cv:compute_exp`])));
    FIRST_X_ASSUM(MP_TAC o
      SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`;
             `cvs:compute_exp list`] o
      check (can (SPECL [`ck:num`; `eqs:(mlstring#mlstring list#compute_exp)list`;
                         `cvs:compute_exp list`])))] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:hol_refs`) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN ASM_MESON_TAC[]);;

compute_overloads_off ();;
