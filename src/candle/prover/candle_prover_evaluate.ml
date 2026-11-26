(* ========================================================================= *)
(* candle_prover_evaluate: port of HOL4 candle/prover/                       *)
(* candle_prover_evaluateScript.sml (CakeML v3479).  Proving that Candle     *)
(* prover maintains its invariants (i.e. v_ok).                              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 proves evaluate_v_ok by match_mp_tac with an instance of           *)
(*   full_evaluate_ind and one suspended goal per case (Resume ...); here    *)
(*   the instance is can2daux_ind_thm and each case is a lemma               *)
(*   CAN2DAUX_evaluate_v_ok_NAME of its antecedent (App in three parts:      *)
(*   App_Eval, App_Opapp, App_Op, as HOL4 splits it).                        *)
(* - HOL4 LLOOKUP s n is oEL n s; HOL4 STATE is holKernelProof_STATE.        *)
(* - The App cases are proved with the kit's kit_distinct_names (the case    *)
(*   splits name new variables apart; restored afterwards).                  *)
(* - Local helpers that are not HOL4 theorems are CAN2DAUX_ (OCaml values    *)
(*   can2daux_); perms.ml's PERMSAUX_getOpClass is used for getOpClass.      *)
(* ========================================================================= *)

needs "candle/prover/candle_kernel_funs.ml";;
needs "candle/prover/ast_extras.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "candle/prover/perms.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "hol4/sptree.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local helpers (not HOL4 theorems): CAN2DAUX_ theorems and tactics,        *)
(* can2daux_ OCaml values.                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4 temp_send_to_back_overload of compute_syntax's If, App, Var, Let:   *)
(* the port's compute constructors have the prefix compute_ (nothing to do)  *)

(* HOL4: (!x. P x ==> Q x) for the environment invariant, by env_ok_def and  *)
(* SF SFY_ss in each case                                                    *)
let CAN2DAUX_env_ok_mono = prove
 (`(!v. candle_v_ok ctxt v ==> candle_v_ok ctxt' v) /\ candle_env_ok ctxt env ==>
   candle_env_ok ctxt' env`,
  REWRITE_TAC[candle_env_ok_def] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* pmatch_v_ok                                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4 LLOOKUP s loc is oEL loc s *)
let pmatch_v_ok = prove
 (`(!envC s p v ws env.
      pmatch envC s p v ws = Match env /\
      candle_v_ok ctxt v /\
      (!n len tag m.
         nsLookup envC n = SOME (len,TypeStamp tag m) /\
         m IN kernel_types ==>
           id_to_n n IN kernel_ctors) /\
      (!loc r. ~(loc IN kernel_locs) /\ oEL loc s = SOME r ==> candle_ref_ok ctxt r) /\
      ALL (candle_v_ok ctxt) (MAP SND ws) ==>
        ALL (candle_v_ok ctxt) (MAP SND env)) /\
   (!envC s ps vs ws env.
      pmatch_list envC s ps vs ws = Match env /\
      ALL (candle_v_ok ctxt) vs /\
      (!n len tag m.
         nsLookup envC n = SOME (len,TypeStamp tag m) /\
         m IN kernel_types ==>
           id_to_n n IN kernel_ctors) /\
      (!loc r. ~(loc IN kernel_locs) /\ oEL loc s = SOME r ==> candle_ref_ok ctxt r) /\
      ALL (candle_v_ok ctxt) (MAP SND ws) ==>
        ALL (candle_v_ok ctxt) (MAP SND env))`,
  MATCH_MP_TAC pmatch_ind THEN RW[] THEN
  GVS[pmatch_def; COND_CASE_EQ; option_case_eq; pair_case_eq; case_eq "match_result";
      case_eq "store_v"] THEN
  REPEAT STRIP_TAC THEN TRY (ASM_MESON_TAC[]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY (ASM_MESON_TAC[v_ok_Conv_alt; v_ok_Conv_NONE]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_v_ok_def; store_lookup_def; GSYM oEL_THM]) THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`lnum:num`; `Refv (a:v)`]) THEN
  ASM_REWRITE_TAC[candle_ref_ok_def]);;

(* pmatch_v_ok for a whole pattern against the invariants of the state and  *)
(* the environment (HOL4 does this in each case with drule pmatch_v_ok)     *)
let CAN2DAUX_pmatch_env_ok = prove
 (`pmatch (sem_env_c env) (state_refs s) p v [] = Match env1 /\
   candle_state_ok ctxt (s:(FFI)state) /\ candle_env_ok ctxt env /\
   candle_v_ok ctxt v ==>
   ALL (candle_v_ok ctxt) (MAP SND env1)`,
  REWRITE_TAC[candle_state_ok_def; candle_env_ok_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT1 pmatch_v_ok) THEN
  MAP_EVERY QEXISTS_TAC ["sem_env_c env"; "state_refs s"; "p"; "v"; "[]:(varN#v)list"] THEN
  ASM_REWRITE_TAC[MAP; ALL] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The environment invariant under the environment updates of evaluate      *)
(* ------------------------------------------------------------------------- *)

let CAN2DAUX_env_ok_nsOptBind = prove
 (`candle_env_ok ctxt env /\ candle_v_ok ctxt v ==>
   candle_env_ok ctxt (sem_env_v_fupd (combin_K (nsOptBind xo v (sem_env_v env))) env)`,
  REWRITE_TAC[candle_env_ok_def] THEN STRIP_TAC THEN SIMP[] THEN
  QCASES_ON "xo" THEN REWRITE_TAC[nsOptBind_def; option_CASE] THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN GEN_TAC THEN QCASES_ON "n" THEN
  REWRITE_TAC[nsLookup_nsBind_compute] THEN RW[] THEN ASM_MESON_TAC[]);;

let CAN2DAUX_env_ok_build_rec_env = prove
 (`candle_env_ok ctxt env /\ candle_env_ok ctxt cle /\
   ALL safe_exp (MAP (SND o SND) funs) ==>
   candle_env_ok ctxt
     (sem_env_v_fupd (combin_K (build_rec_env funs cle (sem_env_v env))) env)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `!f. candle_v_ok ctxt (Recclosure cle funs f)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC candle_v_ok_Recclosure THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `candle_env_ok ctxt env` THEN
  REWRITE_TAC[candle_env_ok_def] THEN STRIP_TAC THEN SIMP[] THEN
  REWRITE_TAC[build_rec_env_merge; nsLookup_nsAppend_some; nsLookup_alist_to_ns_some] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PROD] THEN STRIP_TAC THEN GVS[];
    ASM_MESON_TAC[]]);;

let CAN2DAUX_env_ok_nsAppend_alist = prove
 (`candle_env_ok ctxt env /\ ALL (candle_v_ok ctxt) (MAP SND l) ==>
   candle_env_ok ctxt
     (sem_env_v_fupd (combin_K (nsAppend (alist_to_ns l) (sem_env_v env))) env)`,
  REWRITE_TAC[candle_env_ok_def] THEN STRIP_TAC THEN SIMP[] THEN
  REWRITE_TAC[nsLookup_nsAppend_some; nsLookup_alist_to_ns_some] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    UNDISCH_TAC `ALL (candle_v_ok ctxt) (MAP SND (l:(varN#v)list))` THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_DEF] THEN
    MESON_TAC[SND];
    ASM_MESON_TAC[]]);;

let CAN2DAUX_env_ok_alist_to_ns = prove
 (`ALL (candle_v_ok ctxt) (MAP SND l) ==>
   candle_env_ok ctxt (sem_env_REC (alist_to_ns l) nsEmpty)`,
  REWRITE_TAC[candle_env_ok_def] THEN SIMP[nsLookup_nsEmpty; option_DISTINCT] THEN
  REWRITE_TAC[nsLookup_alist_to_ns_some] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  UNDISCH_TAC `ALL (candle_v_ok ctxt) (MAP SND (l:(varN#v)list))` THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_DEF] THEN MESON_TAC[SND]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_v_ok: the invariants are preserved by evaluate, evaluate_match   *)
(* and evaluate_decs.  HOL4 states the theorem as the conclusion of          *)
(* full_evaluate_ind for the three predicates below and proves it by         *)
(* match_mp_tac with that instance, one suspended goal per case (Nil, Cons,  *)
(* ..., decs_Dlocal); here each case is a lemma CAN2DAUX_evaluate_v_ok_NAME  *)
(* of the instance's antecedent.                                             *)
(* ------------------------------------------------------------------------- *)

let can2daux_evaluate_P = CASE_TERM
 `\(s:(FFI)state) (env:v sem_env) (xs:exp list).
    !(res:(v list,v)result) (s':(FFI)state) (ctxt:update list).
      evaluate s env xs = (s',res) /\
      candle_state_ok ctxt s /\
      candle_env_ok ctxt env /\
      ALL safe_exp xs ==>
        ?ctxt'.
          (!v. candle_v_ok ctxt v ==> candle_v_ok ctxt' v) /\
          (match res with
             Rval vs -> candle_state_ok ctxt' s' /\ ALL (candle_v_ok ctxt') vs
           | Rerr (Rraise v) -> candle_state_ok ctxt' s' /\ candle_v_ok ctxt' v
           | _ -> ALL ok_event (ffi_state_io_events (state_ffi s')))`;;

let can2daux_evaluate_match_P = CASE_TERM
 `\(s:(FFI)state) (env:v sem_env) (v:v) (ps:(pat#exp)list) (errv:v).
    !(res:(v list,v)result) (s':(FFI)state) (ctxt:update list).
      evaluate_match s env v ps errv = (s',res) /\
      candle_state_ok ctxt s /\
      candle_env_ok ctxt env /\
      candle_v_ok ctxt v /\
      candle_v_ok ctxt errv /\
      ALL safe_exp (MAP SND ps) ==>
        ?ctxt'.
          (!v. candle_v_ok ctxt v ==> candle_v_ok ctxt' v) /\
          (match res with
             Rval vs -> candle_state_ok ctxt' s' /\ ALL (candle_v_ok ctxt') vs
           | Rerr (Rraise v) -> candle_state_ok ctxt' s' /\ candle_v_ok ctxt' v
           | _ -> ALL ok_event (ffi_state_io_events (state_ffi s')))`;;

let can2daux_evaluate_decs_P = CASE_TERM
 `\(s:(FFI)state) (env:v sem_env) (ds:dec list).
    !(res:(v sem_env,v)result) (s':(FFI)state) (ctxt:update list).
      evaluate_decs s env ds = (s',res) /\
      candle_state_ok ctxt s /\
      candle_env_ok ctxt env /\
      ALL safe_dec ds ==>
        ?ctxt'.
          (!v. candle_v_ok ctxt v ==> candle_v_ok ctxt' v) /\
          (match res with
             Rval env1 -> candle_state_ok ctxt' s' /\
                          candle_env_ok ctxt' (extend_dec_env env1 env)
           | Rerr (Rraise v) -> candle_state_ok ctxt' s' /\ candle_v_ok ctxt' v
           | _ -> ALL ok_event (ffi_state_io_events (state_ffi s')))`;;

let can2daux_ind_thm =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [can2daux_evaluate_P; can2daux_evaluate_match_P; can2daux_evaluate_decs_P]
       full_evaluate_ind);;

(* the k-th case of the induction (0 Nil, 1 Cons, 2 Lit, 3 Raise, 4 Handle,  *)
(* 5 Con, 6 Var, 7 Fun, 8 App, 9 Log, 10 If, 11 Mat, 12 Let, 13 Letrec,      *)
(* 14 Tannot, 15 Lannot, 16 pmatch_Nil, 17 pmatch_Cons, 18 decs_Nil,         *)
(* 19 decs_Cons, 20 decs_Dlet, 21 decs_Dletrec, 22 decs_Dtype,               *)
(* 23 decs_Dtabbrev, 24 decs_Denv, 25 decs_Dexn, 26 decs_Dmod,               *)
(* 27 decs_Dlocal)                                                           *)
let can2daux_case k = el k (conjuncts (lhand (concl can2daux_ind_thm)));;

(* HOL4 first_x_assum (drule_all_then (qx_choose_then name strip_assume_tac)) *)
(* on an induction hypothesis                                                *)
let CAN2DAUX_IH_TAC (name:string) : tactic =
  FIRST_X_ASSUM (fun th -> DRULE_ALL th) THEN
  DISCH_THEN (X_CHOOSE_THEN (mk_var(name,`:update list`)) STRIP_ASSUME_TAC);;

(* the second induction hypothesis after the first one gave ctxt1 *)
let CAN2DAUX_CHAIN_TAC : tactic =
  QBY "candle_env_ok ctxt1 env" (ASM_MESON_TAC[CAN2DAUX_env_ok_mono]) THEN
  CAN2DAUX_IH_TAC "ctxt2" THEN QEXISTS_TAC "ctxt2" THEN ASM_MESON_TAC[];;

let CAN2DAUX_evaluate_v_ok_Nil = prove
 (can2daux_case 0,
  RW[evaluate_def] THEN QEXISTS_TAC "ctxt" THEN ASM_REWRITE_TAC[ALL]);;

let CAN2DAUX_evaluate_v_ok_Cons = prove
 (can2daux_case 1,
  RW[evaluate_def] THEN GVS[case_eq "result"; pair_case_eq] THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[] THEN
  CAN2DAUX_IH_TAC "ctxt1" THEN CAN2DAUX_CHAIN_TAC);;

let CAN2DAUX_evaluate_v_ok_Lit = prove
 (can2daux_case 2,
  RW[evaluate_def] THEN QEXISTS_TAC "ctxt" THEN ASM_REWRITE_TAC[ALL; candle_v_ok_Lit]);;

let CAN2DAUX_evaluate_v_ok_Raise = prove
 (can2daux_case 3,
  RW[evaluate_def] THEN GVS[case_eq "result"; pair_case_eq] THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[ALL] THEN
  ASM_MESON_TAC[]);;

(* HOL4 [local,simp]; HOL4's gs uses it to close the goals                   *)
(* ?ctxt'. (!v. v_ok ctxt v ==> v_ok ctxt' v) /\ .., the port gives the      *)
(* witness (it is not added to the simpset, which files loading this one     *)
(* would see)                                                                *)
let candle_EXISTS_IMP = prove
 (`?b:A. !x:B. (P:A->B->bool) a x ==> P b x`,
  QEXISTS_TAC "a" THEN REWRITE_TAC[]);;

let CAN2DAUX_evaluate_v_ok_Handle = prove
 (can2daux_case 4,
  RW[evaluate_def] THEN GVS(all_case_eqs() @ [ALL_MAP]) THEN
  CAN2DAUX_IH_TAC "ctxt1" THENL
   [CAN2DAUX_CHAIN_TAC;
    QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[candle_state_ok_def]]);;

let CAN2DAUX_evaluate_v_ok_Con = prove
 (can2daux_case 5,
  RW[evaluate_def] THEN GVS(all_case_eqs() @ [ALL_MAP]) THENL
   [CAN2DAUX_IH_TAC "ctxt1" THEN
    QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[candle_state_ok_def];
    CAN2DAUX_IH_TAC "ctxt1" THEN QEXISTS_TAC "ctxt1" THEN ASM_REWRITE_TAC[] THEN
    QPAT_X_ASSUM "build_conv _ _ _ = SOME _" MP_TAC THEN
    REWRITE_TAC[build_conv_def] THEN QCASES_ON "cn" THEN
    RW[option_case_eq; pair_case_eq] THEN
    MATCH_MP_TAC candle_v_ok_Conv THEN
    ASM_REWRITE_TAC[EVERY_REVERSE; option_DISTINCT; option_INJ] THEN
    REPEAT STRIP_TAC THEN GVS[] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_env_ok_def]) THEN ASM_MESON_TAC[];
    QEXISTS_TAC "ctxt" THEN ASM_MESON_TAC[candle_state_ok_def]]);;

let CAN2DAUX_evaluate_v_ok_Var = prove
 (can2daux_case 6,
  RW[evaluate_def] THEN GVS[option_case_eq] THEN QEXISTS_TAC "ctxt" THEN
  ASM_REWRITE_TAC[ALL] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_env_ok_def; candle_state_ok_def]) THEN
  ASM_MESON_TAC[]);;

let CAN2DAUX_evaluate_v_ok_Fun = prove
 (can2daux_case 7,
  RW[evaluate_def] THEN QEXISTS_TAC "ctxt" THEN ASM_REWRITE_TAC[ALL] THEN
  MATCH_MP_TAC candle_v_ok_Closure THEN ASM_REWRITE_TAC[]);;

let CAN2DAUX_evaluate_v_ok_Log = prove
 (can2daux_case 9,
  RW[evaluate_def] THEN GVS(all_case_eqs() @ [do_log_def]) THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[] THEN
  CAN2DAUX_IH_TAC "ctxt1" THENL
   [QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[candle_state_ok_def];
    CAN2DAUX_CHAIN_TAC; CAN2DAUX_CHAIN_TAC]);;

let CAN2DAUX_evaluate_v_ok_If = prove
 (can2daux_case 10,
  RW[evaluate_def] THEN GVS(all_case_eqs() @ [do_if_def]) THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[] THEN
  CAN2DAUX_IH_TAC "ctxt1" THENL
   [QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[candle_state_ok_def];
    CAN2DAUX_CHAIN_TAC; CAN2DAUX_CHAIN_TAC]);;

let CAN2DAUX_evaluate_v_ok_Mat = prove
 (can2daux_case 11,
  RW[evaluate_def] THEN GVS(all_case_eqs()) THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[] THEN
  CAN2DAUX_IH_TAC "ctxt1" THENL
   [CAN2DAUX_CHAIN_TAC;
    QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[candle_state_ok_def]]);;

let CAN2DAUX_evaluate_v_ok_Let = prove
 (can2daux_case 12,
  RW[evaluate_def] THEN GVS(all_case_eqs()) THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing) THEN GVS[] THEN
  CAN2DAUX_IH_TAC "ctxt1" THEN
  QBY "candle_env_ok ctxt1 env" (ASM_MESON_TAC[CAN2DAUX_env_ok_mono]) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `ctxt1:update list`) THEN
  ASM_SIMP_TAC[CAN2DAUX_env_ok_nsOptBind] THEN
  DISCH_THEN (X_CHOOSE_THEN `ctxt2:update list` STRIP_ASSUME_TAC) THEN
  QEXISTS_TAC "ctxt2" THEN ASM_MESON_TAC[]);;

let CAN2DAUX_evaluate_v_ok_Letrec = prove
 (can2daux_case 13,
  RW[evaluate_def] THEN GVS(all_case_eqs()) THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `ctxt:update list`) THEN
    ASM_SIMP_TAC[CAN2DAUX_env_ok_build_rec_env];
    QEXISTS_TAC "ctxt" THEN ASM_MESON_TAC[candle_state_ok_def]]);;

let CAN2DAUX_evaluate_v_ok_Tannot = prove
 (can2daux_case 14,
  RW[evaluate_def]);;

let CAN2DAUX_evaluate_v_ok_Lannot = prove
 (can2daux_case 15,
  RW[evaluate_def]);;

let CAN2DAUX_evaluate_v_ok_pmatch_Nil = prove
 (can2daux_case 16,
  RW[evaluate_def] THEN QEXISTS_TAC "ctxt" THEN ASM_REWRITE_TAC[]);;

let CAN2DAUX_evaluate_v_ok_pmatch_Cons = prove
 (can2daux_case 17,
  RW[evaluate_def] THEN GVS(all_case_eqs()) THENL
   [QEXISTS_TAC "ctxt" THEN ASM_MESON_TAC[candle_state_ok_def];
    DRULE_ALL CAN2DAUX_pmatch_env_ok THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `ctxt:update list`) THEN
    ASM_SIMP_TAC[CAN2DAUX_env_ok_nsAppend_alist];
    QEXISTS_TAC "ctxt" THEN ASM_MESON_TAC[candle_state_ok_def]]);;

let CAN2DAUX_evaluate_v_ok_decs_Nil = prove
 (can2daux_case 18,
  RW[evaluate_decs_def] THEN QEXISTS_TAC "ctxt" THEN
  ASM_SIMP_TAC[env_ok_extend_dec_env; env_ok_nsEmpty]);;

let CAN2DAUX_evaluate_v_ok_decs_Cons = prove
 (can2daux_case 19,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  CAN2DAUX_IH_TAC "ctxt1" THEN CAN2DAUX_IH_TAC "ctxt2" THEN
  MATCH_GOALSUB_RENAME_TAC "combine_dec_result _ r" THEN QCASES_ON "r" THEN
  FS[combine_dec_result_def; extend_dec_env_def] THEN
  QEXISTS_TAC "ctxt2" THEN ASM_MESON_TAC[]);;

let CAN2DAUX_evaluate_v_ok_decs_Dlet = prove
 (can2daux_case 20,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  TRY (FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP evaluate_sing)) THEN GVS[] THENL
   [CAN2DAUX_IH_TAC "ctxt1" THEN QEXISTS_TAC "ctxt1" THEN ASM_REWRITE_TAC[];
    CAN2DAUX_IH_TAC "ctxt1" THEN QEXISTS_TAC "ctxt1" THEN
    ASM_MESON_TAC[candle_state_ok_def];
    CAN2DAUX_IH_TAC "ctxt1" THEN QEXISTS_TAC "ctxt1" THEN ASM_REWRITE_TAC[] THEN
    QBY "candle_env_ok ctxt1 env" (ASM_MESON_TAC[CAN2DAUX_env_ok_mono]) THEN
    DRULE_ALL CAN2DAUX_pmatch_env_ok THEN DISCH_TAC THEN
    MATCH_MP_TAC env_ok_extend_dec_env THEN ASM_SIMP_TAC[CAN2DAUX_env_ok_alist_to_ns];
    QEXISTS_TAC "ctxt" THEN ASM_MESON_TAC[candle_state_ok_def]]);;

(* HOL4 proves this inside decs_Dtype (m <= k) and candle_basis_evaluate's  *)
(* decs_Dtype (m <= k /\ k < m + LENGTH tds), by build_tdefs_ind            *)
let CAN2DAUX_build_tdefs_stamp = prove
 (`!m tds n l t k.
     nsLookup (build_tdefs m tds) n = SOME (l,TypeStamp t k) ==>
     m <= k /\ k < m + LENGTH tds`,
  MATCH_MP_TAC build_tdefs_ind THEN
  SIMP[build_tdefs_def; nsLookup_nsAppend_some; nsLookup_alist_to_ns_some; LENGTH] THEN
  REPEAT STRIP_TAC THEN
  FIRST
   [FIRST_X_ASSUM (MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    REWRITE_TAC[MEM_REVERSE; build_constrs_def; MEM_MAP; EXISTS_PROD] THEN
    STRIP_TAC THEN GVS[] THEN ARITH_TAC;
    RES_TAC THEN ASM_ARITH_TAC]);;

let CAN2DAUX_env_ok_build_rec_env_nsEmpty = prove
 (`candle_env_ok ctxt cle /\ ALL safe_exp (MAP (SND o SND) funs) ==>
   candle_env_ok ctxt (sem_env_REC (build_rec_env funs cle nsEmpty) nsEmpty)`,
  STRIP_TAC THEN
  MP_TAC (INST [`sem_env_REC nsEmpty nsEmpty:v sem_env`,`env:v sem_env`]
            CAN2DAUX_env_ok_build_rec_env) THEN
  ASM_REWRITE_TAC[env_ok_nsEmpty; sem_env_INFO.ri_accessors; sem_env_INFO.ri_fupds;
                  K_THM]);;

let CAN2DAUX_env_ok_nsSing = prove
 (`candle_v_ok ctxt x ==> candle_env_ok ctxt (sem_env_REC (nsSing n x) nsEmpty)`,
  REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
              option_DISTINCT] THEN
  DISCH_TAC THEN GEN_TAC THEN QCASES_ON "n'" THEN
  REWRITE_TAC[nsSing_def; nsLookup_def; ALOOKUP_DEF; option_DISTINCT] THEN
  RW[] THEN ASM_MESON_TAC[]);;

let CAN2DAUX_env_ok_extend_dec_env_IMP = prove
 (`candle_env_ok ctxt (extend_dec_env env1 env2) ==> candle_env_ok ctxt env1`,
  REWRITE_TAC[candle_env_ok_def; extend_dec_env_def; sem_env_INFO.ri_accessors;
              nsLookup_nsAppend_some] THEN MESON_TAC[]);;

let CAN2DAUX_env_ok_nsLift = prove
 (`candle_env_ok ctxt env1 ==>
   candle_env_ok ctxt
     (sem_env_REC (nsLift mn (sem_env_v env1)) (nsLift mn (sem_env_c env1)))`,
  REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accessors] THEN STRIP_TAC THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[nsLookup_nsLift] THEN
  TOP_CASE_TAC THEN RW[option_DISTINCT; id_to_n_def] THEN ASM_MESON_TAC[]);;

let CAN2DAUX_state_ok_eval_state = prove
 (`candle_state_ok ctxt (s:(FFI)state) /\ candle_eval_state_ok es ==>
   candle_state_ok ctxt (state_eval_state_fupd (combin_K es) s)`,
  REWRITE_TAC[candle_state_ok_def; state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

(* HOL4: gvs [declare_env_def, CaseEqs ["option", "eval_state", "prod"]] \\ *)
(* fs [eval_state_ok_def, SF SFY_ss], in decs_Denv (and App_Eval)           *)
let CAN2DAUX_declare_env_ok = prove
 (`declare_env es env = SOME (x,es') /\ candle_eval_state_ok es /\
   candle_env_ok ctxt env ==>
   candle_eval_state_ok es' /\ candle_v_ok ctxt x`,
  QCASES_ON "es" THEN REWRITE_TAC[declare_env_def; option_CASE; option_DISTINCT] THEN
  MATCH_GOALSUB_RENAME_TAC "eval_state_CASE e" THEN QCASES_ON "e" THEN
  REWRITE_TAC[candle_eval_state_ok_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[pair_case_eq] THEN
  ASM_REWRITE_TAC[candle_eval_state_ok_def; candle_v_ok_def;
                  eval_decs_state_INFO.ri_accfupds]);;

let CAN2DAUX_evaluate_v_ok_decs_Dletrec = prove
 (can2daux_case 21,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  QEXISTS_TAC "ctxt" THEN
  ASM_SIMP_TAC[env_ok_extend_dec_env; CAN2DAUX_env_ok_build_rec_env_nsEmpty] THEN
  ASM_MESON_TAC[candle_state_ok_def]);;

let CAN2DAUX_evaluate_v_ok_decs_Dtype = prove
 (can2daux_case 22,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN QEXISTS_TAC "ctxt" THENL
   [ALL_TAC; ASM_MESON_TAC[candle_state_ok_def]] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `candle_state_ok ctxt (st:(FFI)state)` THEN
    REWRITE_TAC[candle_state_ok_def; state_INFO.ri_accfupds; K_THM] THEN
    MESON_TAC[ARITH_RULE `n < a ==> n < a + b:num`];
    MATCH_MP_TAC env_ok_extend_dec_env THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
                option_DISTINCT] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP CAN2DAUX_build_tdefs_stamp) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_state_ok_def]) THEN
    ASM_MESON_TAC[NOT_LESS]]);;

let CAN2DAUX_evaluate_v_ok_decs_Dtabbrev = prove
 (can2daux_case 23,
  RW[evaluate_decs_def] THEN QEXISTS_TAC "ctxt" THEN
  ASM_SIMP_TAC[env_ok_extend_dec_env; env_ok_nsEmpty]);;

let CAN2DAUX_evaluate_v_ok_decs_Denv = prove
 (can2daux_case 24,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THENL
   [QEXISTS_TAC "ctxt" THEN ASM_MESON_TAC[candle_state_ok_def];
    QEXISTS_TAC "ctxt" THEN REWRITE_TAC[] THEN
    QBY "candle_eval_state_ok (state_eval_state st)"
      (ASM_MESON_TAC[candle_state_ok_def]) THEN
    DRULE_ALL CAN2DAUX_declare_env_ok THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CAN2DAUX_state_ok_eval_state; env_ok_extend_dec_env;
                 CAN2DAUX_env_ok_nsSing]]);;

let CAN2DAUX_evaluate_v_ok_decs_Dexn = prove
 (can2daux_case 25,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  QEXISTS_TAC "ctxt" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `candle_state_ok ctxt (st:(FFI)state)` THEN
    REWRITE_TAC[candle_state_ok_def; state_INFO.ri_accfupds; K_THM];
    MATCH_MP_TAC env_ok_extend_dec_env THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
                option_DISTINCT] THEN
    GEN_TAC THEN QCASES_ON "id" THEN
    REWRITE_TAC[nsSing_def; nsLookup_def; ALOOKUP_DEF; option_DISTINCT] THEN
    RW[option_INJ; PAIR_EQ; distinctness "stamp"]]);;

let CAN2DAUX_evaluate_v_ok_decs_Dmod = prove
 (can2daux_case 26,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  CAN2DAUX_IH_TAC "ctxt1" THEN QEXISTS_TAC "ctxt1" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC env_ok_extend_dec_env THEN
  ASM_MESON_TAC[CAN2DAUX_env_ok_nsLift; CAN2DAUX_env_ok_extend_dec_env_IMP;
                CAN2DAUX_env_ok_mono]);;

let CAN2DAUX_evaluate_v_ok_decs_Dlocal = prove
 (can2daux_case 27,
  RW[evaluate_decs_def] THEN GVS(all_case_eqs()) THEN
  CAN2DAUX_IH_TAC "ctxt1" THEN CAN2DAUX_IH_TAC "ctxt2" THEN
  QEXISTS_TAC "ctxt2" THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  QCASES_ON "res" THEN FS[] THEN
  MATCH_MP_TAC env_ok_extend_dec_env THEN
  ASM_MESON_TAC[CAN2DAUX_env_ok_extend_dec_env_IMP; CAN2DAUX_env_ok_mono]);;

(* ------------------------------------------------------------------------- *)
(* Primitive operations: v_ok_v_to_list, do_app_ok, state_ok_dest_thunk,     *)
(* state_ok_update_thunk                                                     *)
(* ------------------------------------------------------------------------- *)

let v_ok_v_to_list = prove
 (`!v vs. v_to_list v = SOME vs /\ candle_v_ok ctxt v ==> ALL (candle_v_ok ctxt) vs`,
  MATCH_MP_TAC v_to_list_ind THEN RW[v_to_list_def] THEN
  GVS[option_case_eq; COND_CASE_EQ] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP v_ok_Conv_alt) THEN REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[]);;

(* the clauses of v_ok_def for Vectorv, Litv, Loc and Env *)
let can2daux_v_ok_basic = map (fun i -> el i (CONJUNCTS candle_v_ok_def)) [3;4;5;6];;

let CAN2DAUX_v_ok_Boolv = prove
 (`candle_v_ok ctxt (Boolv b)`,
  MESON_TAC[BOOL_v_ok; ml_BOOL_def]);;

let CAN2DAUX_v_ok_list_to_v = prove
 (`!xs. ALL (candle_v_ok ctxt) xs ==> candle_v_ok ctxt (list_to_v xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_to_v_def; ALL; list_type_num_def] THENL
   [MATCH_MP_TAC candle_v_ok_Conv THEN
    REWRITE_TAC[ALL; option_INJ; injectivity "stamp"; kernel_types_def; IN_INSERT;
                NOT_IN_EMPTY] THEN ARITH_TAC;
    ASM_SIMP_TAC[v_ok_Cons]]);;

let CAN2DAUX_do_arith_ok = prove
 (`(do_arith a ty vs = SOME (INL e) ==> candle_v_ok ctxt e) /\
   (do_arith a ty vs = SOME (INR v) ==> candle_v_ok ctxt v)`,
  STRUCT_CASES_TAC (SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_arith_def] THEN CONJ_TAC THEN
  REPEAT (FIRST [TOP_CASE_TAC; DISCH_TAC]) THEN
  GVS[candle_v_ok_Lit; CAN2DAUX_v_ok_Boolv; v_ok_div_exn_v] THEN
  RW[candle_v_ok_Lit; CAN2DAUX_v_ok_Boolv; v_ok_div_exn_v]);;

let CAN2DAUX_do_conversion_ok = prove
 (`(do_conversion v ty1 ty2 = SOME (INL e) ==> candle_v_ok ctxt e) /\
   (do_conversion v ty1 ty2 = SOME (INR w) ==> candle_v_ok ctxt w)`,
  STRUCT_CASES_TAC (SPEC `ty1:prim_type` prim_type_cases) THEN
  STRUCT_CASES_TAC (SPEC `ty2:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_conversion_def; LET_DEF; LET_END_DEF] THEN
  RW[candle_v_ok_Lit; v_ok_chr_exn_v] THEN GVS[candle_v_ok_Lit; v_ok_chr_exn_v]);;

(* the store invariants under store_assign and store_alloc *)
let CAN2DAUX_refs_ok_LUPDATE = prove
 (`(!loc r. ~(loc IN kernel_locs) /\ oEL loc refs = SOME r ==> candle_ref_ok ctxt r) /\
   candle_ref_ok ctxt x ==>
   !loc r. ~(loc IN kernel_locs) /\ oEL loc (LUPDATE x n refs) = SOME r ==>
           candle_ref_ok ctxt r`,
  REWRITE_TAC[oEL_LUPDATE] THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  RW[option_INJ; option_DISTINCT] THEN ASM_MESON_TAC[]);;

let CAN2DAUX_refs_ok_APPEND = prove
 (`(!loc r. ~(loc IN kernel_locs) /\ oEL loc refs = SOME r ==> candle_ref_ok ctxt r) /\
   candle_ref_ok ctxt x ==>
   !loc r. ~(loc IN kernel_locs) /\ oEL loc (APPEND refs [x]) = SOME r ==>
           candle_ref_ok ctxt r`,
  REWRITE_TAC[oEL_EQ_EL; LENGTH_APPEND; LENGTH; EL_APPEND_EQN] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[];
    SUBGOAL_THEN `loc - LENGTH (refs:(v store_v)list) = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EL; HD] THEN ASM_MESON_TAC[]]]);;

let CAN2DAUX_refs_EL = prove
 (`EL n refs = x /\ n < LENGTH refs /\ ~(n IN kernel_locs) /\
   (!loc r. ~(loc IN kernel_locs) /\ oEL loc refs = SOME r ==> candle_ref_ok ctxt r) ==>
   candle_ref_ok ctxt x`,
  MESON_TAC[oEL_EQ_EL]);;

let CAN2DAUX_kernel_loc_ok_APPEND = prove
 (`candle_kernel_loc_ok st loc refs ==> candle_kernel_loc_ok st loc (APPEND refs xs)`,
  DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP kernel_loc_ok_LENGTH) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[candle_kernel_loc_ok_def; oEL_EQ_EL; LENGTH_APPEND; EL_APPEND_EQN] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `v:v` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let CAN2DAUX_kernel_locs_APPEND = prove
 (`(!loc. loc IN kernel_locs ==> candle_kernel_loc_ok st loc refs) ==>
   !loc. loc IN kernel_locs ==> candle_kernel_loc_ok st loc (APPEND refs xs)`,
  MESON_TAC[CAN2DAUX_kernel_loc_ok_APPEND]);;

let CAN2DAUX_kernel_locs_LUPDATE = prove
 (`(!loc. loc IN kernel_locs ==> candle_kernel_loc_ok st loc refs) /\
   ~(n IN kernel_locs) ==>
   !loc. loc IN kernel_locs ==> candle_kernel_loc_ok st loc (LUPDATE x n refs)`,
  MESON_TAC[kernel_loc_ok_LUPDATE1]);;

let CAN2DAUX_kernel_locs_LENGTH = prove
 (`(!loc. loc IN kernel_locs ==> candle_kernel_loc_ok st loc refs) ==>
   ~(LENGTH refs IN kernel_locs)`,
  MESON_TAC[kernel_loc_ok_LENGTH; LT_REFL]);;

(* candle_ref_ok ctxt x for every assumption EL n refs = x with n a          *)
(* location of the store other than the kernel's                             *)
let CAN2DAUX_REFS_EL_TAC : tactic = fun (asl,w as g) ->
  let th0 = IMP_CURRY_RULE (GEN_ALL CAN2DAUX_refs_EL) in
  let ths = mapfilter (fun (_,a) -> drule_all_with (map snd asl) (MATCH_MP th0 a)) asl in
  MAP_EVERY (ASSUME_TAC o REWRITE_RULE[candle_ref_ok_def]) ths g;;

let can2daux_has c w = can (find_term (fun t -> is_const t && fst(dest_const t) = c)) w;;

(* one conjunct of the conclusion of do_app_ok, after the case split; the    *)
(* tactic is chosen by the shape of the goal                                 *)
let CAN2DAUX_DO_APP_FIN_TAC : tactic = fun (asl,w as g) ->
  (if can2daux_has "candle_kernel_loc_ok" w then
     FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
            MATCH_MP_TAC CAN2DAUX_kernel_locs_APPEND THEN FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC CAN2DAUX_kernel_locs_LUPDATE THEN ASM_REWRITE_TAC[] THEN NO_TAC]
   else if can2daux_has "candle_ref_ok" w then
     FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
            MATCH_MP_TAC CAN2DAUX_refs_ok_APPEND THEN
            ASM_SIMP_TAC[candle_ref_ok_def; EVERY_REPLICATE; ALL] THEN NO_TAC;
            MATCH_MP_TAC CAN2DAUX_refs_ok_LUPDATE THEN
            ASM_SIMP_TAC[candle_ref_ok_def; IMP_EVERY_LUPDATE] THEN NO_TAC]
   else if can2daux_has "kernel_locs" w then
     ASM_MESON_TAC[CAN2DAUX_kernel_locs_LENGTH]
   else if can2daux_has "ok_event" w then
     FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
            ASM_REWRITE_TAC[ok_event_def; injectivity "ffiname"] THEN NO_TAC]
   else
     RULE_ASSUM_TAC (REWRITE_RULE[GE; NOT_LE]) THEN
     FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
            ASM_SIMP_TAC[CAN2DAUX_v_ok_list_to_v; ALL_APPEND] THEN NO_TAC;
            MATCH_MP_TAC CAN2DAUX_v_ok_list_to_v THEN REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
            MESON_TAC[candle_v_ok_Lit];
            ASM_MESON_TAC[EVERY_EL]]) g;;

(* HOL4 do_app_ok, case by case on op (61 cases of do_app_cases); in every   *)
(* case the kernel state st is unchanged (st1 = st, as HOL4's                *)
(* first_assum (irule_at Any))                                               *)
let candle_do_app_ok = prove
 (CASE_TERM
  `do_app (refs,ffi:(FFI)ffi_state) op vs = SOME ((refs1,ffi1),res) /\
   ~(op = Opapp) /\
   ~(op = Eval) /\
   ALL (candle_v_ok ctxt) vs /\
   (!loc r. ~(loc IN kernel_locs) /\ oEL loc refs = SOME r ==> candle_ref_ok ctxt r) /\
   ALL ok_event (ffi_state_io_events ffi) /\
   ~(op = FFI kernel_ffi) /\
   holKernelProof_STATE ctxt st /\
   (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok st loc refs) ==>
     ?st1.
       holKernelProof_STATE ctxt st1 /\
       (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok st1 loc refs1) /\
       (!loc r. ~(loc IN kernel_locs) /\ oEL loc refs1 = SOME r ==> candle_ref_ok ctxt r) /\
       ALL ok_event (ffi_state_io_events ffi1) /\
       (match list_result res with
          Rval vs -> ALL (candle_v_ok ctxt) vs
        | Rerr (Rraise v) -> candle_v_ok ctxt v
        | _ -> T)`,
  STRIP_TAC THEN QPAT_X_ASSUM "do_app _ _ _ = _" (MP_TAC o REWRITE_RULE[do_app_cases]) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN
  EXISTS_TAC `st:hol_refs` THEN RVEQ_TAC THEN
  GVS([PAIR_EQ; ALL; candle_ref_ok_def; store_assign_def; store_alloc_def; store_lookup_def;
       sum_case_eq; option_case_eq; pair_case_eq; list_case_eq; COND_CASE_EQ; case_eq "v";
       call_FFI_def; case_eq "ffi_result"; case_eq "oracle_result"; thunk_op_def;
       case_eq "thunk_op";
       CAN2DAUX_v_ok_Boolv; v_ok_Conv_NONE; nat_to_v_def] @ can2daux_v_ok_basic) THEN
  IMP_RES_TAC CAN2DAUX_do_arith_ok THEN IMP_RES_TAC CAN2DAUX_do_conversion_ok THEN
  IMP_RES_TAC v_ok_v_to_list THEN CAN2DAUX_REFS_EL_TAC THEN
  REPEAT CONJ_TAC THEN CAN2DAUX_DO_APP_FIN_TAC);;

let state_ok_dest_thunk = prove
 (`candle_state_ok ctxt (s:(FFI)state) /\ ALL (candle_v_ok ctxt) vs /\
   dest_thunk (REVERSE vs) (state_refs s) = IsThunk m v ==> candle_v_ok ctxt v`,
  REWRITE_TAC[candle_state_ok_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ONELINE dest_thunk_def] THEN
  GVS(all_case_eqs() @ [store_lookup_def]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM (MP_TAC o AP_TERM `ALL (candle_v_ok ctxt)`) THEN
  ASM_REWRITE_TAC[EVERY_REVERSE; ALL] THEN REWRITE_TAC can2daux_v_ok_basic THEN
  DISCH_TAC THEN DRULE_ALL CAN2DAUX_refs_EL THEN REWRITE_TAC[candle_ref_ok_def]);;

let state_ok_update_thunk = prove
 (`candle_state_ok ctxt (s:(FFI)state) /\ ALL (candle_v_ok ctxt) vs /\
   ALL (candle_v_ok ctxt) vs2 /\
   update_thunk (REVERSE vs) (state_refs s) vs2 = SOME refs ==>
   candle_state_ok ctxt (state_refs_fupd (combin_K refs) s)`,
  REWRITE_TAC[candle_state_ok_def; state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ONELINE update_thunk_def] THEN
  GVS(all_case_eqs() @ [store_assign_def]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM (MP_TAC o AP_TERM `ALL (candle_v_ok ctxt)`) THEN
  ASM_REWRITE_TAC[EVERY_REVERSE; ALL] THEN REWRITE_TAC can2daux_v_ok_basic THEN
  DISCH_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[ALL]) THEN
  QEXISTS_TAC "state" THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CAN2DAUX_kernel_locs_LUPDATE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CAN2DAUX_refs_ok_LUPDATE THEN ASM_REWRITE_TAC[candle_ref_ok_def]]);;

(* ------------------------------------------------------------------------- *)
(* The App cases (HOL4 App_Eval, App_Opapp, App_Op)                          *)
(* ------------------------------------------------------------------------- *)

(* the App case of the induction with an extra hypothesis on op *)
let can2daux_app_case cond =
  let vs,body = strip_forall (can2daux_case 8) in
  list_mk_forall(vs, mk_imp(cond, body));;

let CAN2DAUX_state_ok_ok_event = prove
 (`candle_state_ok ctxt (s:(FFI)state) ==> ALL ok_event (ffi_state_io_events (state_ffi s))`,
  SIMP[candle_state_ok_def]);;

let CAN2DAUX_state_ok_eval_state_ok = prove
 (`candle_state_ok ctxt (s:(FFI)state) ==> candle_eval_state_ok (state_eval_state s)`,
  SIMP[candle_state_ok_def]);;

(* candle_eval_state_ok (state_eval_state s) for every assumption            *)
(* candle_state_ok ctxt s                                                    *)
let CAN2DAUX_EVAL_STATE_OK_TAC : tactic = fun (asl,w as g) ->
  let ths = mapfilter (fun (_,th) -> MATCH_MP CAN2DAUX_state_ok_eval_state_ok th) asl in
  MAP_EVERY ASSUME_TAC ths g;;

(* candle_state_ok ctxt (dec_clock s) for every assumption candle_state_ok   *)
(* ctxt s                                                                    *)
let CAN2DAUX_DEC_CLOCK_TAC : tactic = fun (asl,w as g) ->
  let ths = mapfilter (fun (_,th) ->
      if can (term_match [] `candle_state_ok c (s:(FFI)state)`) (concl th)
      then ONCE_REWRITE_RULE[GSYM state_ok_dec_clock] th else failwith "") asl in
  MAP_EVERY ASSUME_TAC ths g;;

let CAN2DAUX_eval_state_ok_reset = prove
 (`candle_eval_state_ok es ==> candle_eval_state_ok (reset_env_generation prior es)`,
  REWRITE_TAC[reset_env_generation_def] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[candle_eval_state_ok_def; eval_decs_state_INFO.ri_accfupds]);;

let CAN2DAUX_decode_decs_add_decs_generation = prove
 (`eval_decs_state_decode_decs (add_decs_generation s) = eval_decs_state_decode_decs s`,
  REWRITE_TAC[add_decs_generation_def] THEN
  PAIR_CASES_ON `eval_decs_state_env_id_counter s` THEN
  ASM_REWRITE_TAC[pair_CASE; eval_decs_state_INFO.ri_accfupds]);;

(* HOL4 App_Eval: gvs [do_eval_def, AllCaseEqs(), eval_state_ok_def, ..]    *)
let CAN2DAUX_do_eval_ok = prove
 (`do_eval (REVERSE vs) es = SOME (env1,decs,es1) /\ candle_eval_state_ok es /\
   ALL (candle_v_ok ctxt) vs ==>
   candle_env_ok ctxt env1 /\ ALL safe_dec decs /\ candle_eval_state_ok es1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL (candle_v_ok ctxt) (REVERSE vs)` MP_TAC THENL
   [ASM_REWRITE_TAC[EVERY_REVERSE]; ALL_TAC] THEN
  UNDISCH_TAC `do_eval (REVERSE vs) es = SOME (env1,decs,es1)` THEN
  UNDISCH_TAC `candle_eval_state_ok es` THEN
  SPEC_TAC(`REVERSE vs:v list`,`ws:v list`) THEN GEN_TAC THEN
  REWRITE_TAC[do_eval_def] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[candle_eval_state_ok_def; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE (ALL :: can2daux_v_ok_basic)) THEN
  ASM_REWRITE_TAC[candle_eval_state_ok_def; CAN2DAUX_decode_decs_add_decs_generation;
                  eval_decs_state_INFO.ri_accfupds] THEN
  ASM_MESON_TAC[]);;

(* the case splits of the App cases name new variables apart (the kit's     *)
(* default can give a v and a state the same name)                           *)
let can2daux_distinct_names = !kit_distinct_names;;
kit_distinct_names := true;;

let CAN2DAUX_evaluate_v_ok_App_Eval = prove
 (can2daux_app_case `op = Eval`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[PERMSAUX_getOpClass; distinctness "op"] THEN
  RW[evaluate_def; PERMSAUX_getOpClass] THEN
  GVS(all_case_eqs() @ [do_eval_res_def]) THEN
  CAN2DAUX_IH_TAC "ctxt1" THEN
  TRY (QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event] THEN NO_TAC) THEN
  CAN2DAUX_EVAL_STATE_OK_TAC THEN
  DRULE_ALL CAN2DAUX_do_eval_ok THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `ctxt1:update list`) THEN
  ASM_SIMP_TAC[state_ok_dec_clock; CAN2DAUX_state_ok_eval_state] THEN
  DISCH_THEN (X_CHOOSE_THEN `ctxt2:update list` STRIP_ASSUME_TAC) THEN
  QEXISTS_TAC "ctxt2" THEN CAN2DAUX_EVAL_STATE_OK_TAC THEN
  TRY (DRULE_ALL CAN2DAUX_declare_env_ok THEN STRIP_TAC) THEN
  ASM_SIMP_TAC[CAN2DAUX_state_ok_eval_state; CAN2DAUX_eval_state_ok_reset] THEN
  ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event]);;

let CAN2DAUX_env_ok_nsBind = prove
 (`candle_env_ok ctxt (sem_env_v_fupd (combin_K e) env) /\ candle_v_ok ctxt v ==>
   candle_env_ok ctxt (sem_env_v_fupd (combin_K (nsBind n v e)) env)`,
  REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN QCASES_ON "n'" THEN
  REWRITE_TAC[nsLookup_nsBind_compute] THEN RW[] THEN ASM_MESON_TAC[]);;

let CAN2DAUX_env_ok_self = prove
 (`candle_env_ok ctxt (sem_env_v_fupd (combin_K (sem_env_v env)) env) <=> candle_env_ok ctxt env`,
  REWRITE_TAC[candle_env_ok_def; sem_env_INFO.ri_accfupds; K_THM]);;

(* HOL4 App_Opapp (and the Force case): the closure of an application of a  *)
(* value that is not a kernel value                                          *)
let CAN2DAUX_do_opapp_ok = prove
 (`do_opapp [f; v] = SOME (env1,e) /\ candle_v_ok ctxt f /\ ~candle_kernel_vals ctxt f /\
   candle_v_ok ctxt v ==> candle_env_ok ctxt env1 /\ safe_exp e`,
  REWRITE_TAC[do_opapp_cases; CONS_11; NOT_CONS_NIL] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_v_ok_def]) THEN GVS[] THENL
   [MATCH_MP_TAC CAN2DAUX_env_ok_nsBind THEN ASM_REWRITE_TAC[CAN2DAUX_env_ok_self];
    CONJ_TAC THENL
     [MATCH_MP_TAC CAN2DAUX_env_ok_nsBind THEN ASM_SIMP_TAC[CAN2DAUX_env_ok_build_rec_env];
      FIRST_X_ASSUM (MP_TAC o MATCH_MP ALOOKUP_MEM o REWRITE_RULE[find_recfun_ALOOKUP]) THEN
      UNDISCH_TAC `ALL safe_exp (MAP (SND o SND) (funs:(varN#varN#exp)list))` THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; o_DEF; EXISTS_PROD] THEN
      MESON_TAC[FST; SND]]]);;

let CAN2DAUX_do_opapp_SOME = prove
 (`do_opapp vs = SOME x ==> ?f v. vs = [f; v]`,
  MP_TAC (ISPEC `x:v sem_env#exp` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[do_opapp_cases] THEN MESON_TAC[]);;

let CAN2DAUX_ALL_REVERSE_2 = prove
 (`REVERSE vs = [f; w] ==> !P. ALL P vs <=> P f /\ P (w:A)`,
  DISCH_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[GSYM EVERY_REVERSE] THEN
  ASM_REWRITE_TAC[ALL]);;

let CAN2DAUX_evaluate_v_ok_App_Opapp = prove
 (can2daux_app_case `op = Opapp`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[PERMSAUX_getOpClass] THEN
  RW[evaluate_def; PERMSAUX_getOpClass] THEN
  GVS(all_case_eqs()) THEN
  CAN2DAUX_IH_TAC "ctxt1" THEN
  TRY (QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event] THEN NO_TAC) THEN
  CAN2DAUX_DEC_CLOCK_TAC THEN
  FIRST_ASSUM (X_CHOOSE_THEN `f:v` (X_CHOOSE_THEN `w:v`
    (fun th -> RULE_ASSUM_TAC (REWRITE_RULE[th]) THEN ASSUME_TAC th)) o
    MATCH_MP CAN2DAUX_do_opapp_SOME) THEN
  QBY "candle_v_ok ctxt1 f /\\ candle_v_ok ctxt1 w" (ASM_MESON_TAC[CAN2DAUX_ALL_REVERSE_2]) THEN
  ASM_CASES_TAC `candle_kernel_vals ctxt1 f` THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP kernel_vals_ok) THEN
    DISCH_THEN (fun th -> DRULE_ALL th) THEN STRIP_TAC THENL
     [QEXISTS_TAC "ctxt1" THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds] THEN
      ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event];
      QEXISTS_TAC "ctxt'" THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      QCASES_ON "res" THEN CAKE_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[];
        TOP_CASE_TAC THEN ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event]]];
    DRULE_ALL CAN2DAUX_do_opapp_ok THEN STRIP_TAC THEN
    CAN2DAUX_IH_TAC "ctxt2" THEN QEXISTS_TAC "ctxt2" THEN ASM_MESON_TAC[]]);;

let CAN2DAUX_v_ok_unit = prove
 (`candle_v_ok ctxt (Conv NONE [])`,
  REWRITE_TAC[v_ok_Conv_NONE; ALL]);;

let CAN2DAUX_ALL_v_ok_mono = prove
 (`(!v. candle_v_ok c1 v ==> candle_v_ok c2 v) /\ ALL (candle_v_ok c1) l ==>
   ALL (candle_v_ok c2) l`,
  MESON_TAC[MONO_ALL]);;

(* case split on whether the thunk value f of an assumption dest_thunk .. = *)
(* IsThunk NotEvaluated f is a kernel value of ctxt1                         *)
let CAN2DAUX_THUNK_KERNEL_CASES_TAC : tactic = fun (asl,w as g) ->
  let th = snd (find (fun (_,th) ->
      can (term_match [] `dest_thunk (vs:v list) (refs:(v store_v)list) =
                          IsThunk NotEvaluated (f:v)`) (concl th)) asl) in
  let f = rand (rhs (concl th)) in
  ASM_CASES_TAC (mk_comb(`candle_kernel_vals ctxt1`,f)) g;;

(* the end of a Force case, the new context chosen *)
let CAN2DAUX_FORCE_FIN_TAC : tactic =
  TRY (DRULE_ALL CAN2DAUX_ALL_v_ok_mono THEN DISCH_TAC) THEN
  TRY (DRULE_ALL state_ok_update_thunk THEN DISCH_TAC) THEN
  REPEAT TOP_CASE_TAC THEN
  ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event];;

(* a Force case after kernel_vals_ok: its abort result (no ctxt') or its    *)
(* new context ctxt'                                                         *)
let CAN2DAUX_KERNEL_FIN_TAC : tactic = fun (asl,w as g) ->
  if exists (fun (_,th) -> mem "ctxt'" (map (fst o dest_var) (frees (concl th)))) asl
  then (QEXISTS_TAC "ctxt'" THEN CONJ_TAC THENL
          [ASM_MESON_TAC[]; CAN2DAUX_FORCE_FIN_TAC]) g
  else (QEXISTS_TAC "ctxt1" THEN REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds] THEN
        ASM_REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds] THEN
        ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event]) g;;

(* do_app_ok for the state invariant *)
let CAN2DAUX_state_ok_do_app = prove
 (CASE_TERM
  `candle_state_ok ctxt (s:(FFI)state) /\
   do_app (state_refs s,state_ffi s) op vs = SOME ((refs1,ffi1),res) /\
   ~(op = Opapp) /\ ~(op = Eval) /\ ~(op = FFI kernel_ffi) /\
   ALL (candle_v_ok ctxt) vs ==>
   candle_state_ok ctxt (state_refs_fupd (combin_K refs1) (state_ffi_fupd (combin_K ffi1) s)) /\
   ALL ok_event (ffi_state_io_events ffi1) /\
   (match list_result res with
      Rval vs -> ALL (candle_v_ok ctxt) vs
    | Rerr (Rraise v) -> candle_v_ok ctxt v
    | _ -> T)`,
  REWRITE_TAC[candle_state_ok_def; state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  MP_TAC (INST [`state_refs (s:(FFI)state)`,`refs:(v store_v)list`;
                `state_ffi (s:(FFI)state)`,`ffi:(FFI)ffi_state`;
                `state:hol_refs`,`st:hol_refs`] candle_do_app_ok) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QEXISTS_TAC "st1" THEN ASM_REWRITE_TAC[]);;

let CAN2DAUX_state_ok_do_app_rev =
  REWRITE_RULE[EVERY_REVERSE]
    (INST [`REVERSE (vs:v list)`,`vs:v list`] CAN2DAUX_state_ok_do_app);;

let CAN2DAUX_evaluate_v_ok_App_Op = prove
 (can2daux_app_case `~(op = Eval) /\ ~(op = Opapp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `op = ThunkOp ForceThunk` THENL
   [(* HOL4: Force *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[PERMSAUX_getOpClass; distinctness "op"] THEN
    RW[evaluate_def; PERMSAUX_getOpClass] THEN GVS(all_case_eqs()) THEN
    CAN2DAUX_IH_TAC "ctxt1" THEN
    TRY (QEXISTS_TAC "ctxt1" THEN ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event] THEN NO_TAC) THEN
    TRY (QEXISTS_TAC "ctxt1" THEN ASM_REWRITE_TAC[] THEN
         DRULE_ALL state_ok_dest_thunk THEN REWRITE_TAC[] THEN NO_TAC) THEN
    DRULE_ALL state_ok_dest_thunk THEN DISCH_TAC THEN
    ASSUME_TAC (SPEC `ctxt1:update list` (GEN `ctxt:update list` CAN2DAUX_v_ok_unit)) THEN
    CAN2DAUX_DEC_CLOCK_TAC THEN
    (CAN2DAUX_THUNK_KERNEL_CASES_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP kernel_vals_ok) THEN
      DISCH_THEN (fun th -> DRULE_ALL th) THEN STRIP_TAC THEN GVS[] THEN
      CAN2DAUX_KERNEL_FIN_TAC;
      DRULE_ALL CAN2DAUX_do_opapp_ok THEN STRIP_TAC THEN
      CAN2DAUX_IH_TAC "ctxt2" THEN QEXISTS_TAC "ctxt2" THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; CAN2DAUX_FORCE_FIN_TAC]]);
    (* HOL4: Simple *)
    SUBGOAL_THEN `getOpClass op = Simple` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PERMSAUX_getOpClass]; ALL_TAC] THEN
    REWRITE_TAC[PERMSAUX_getOpClass] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    QPAT_X_ASSUM "evaluate _ _ [App _ _] = _" (MP_TAC o ONCE_REWRITE_RULE[evaluate_def]) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    QPAT_X_ASSUM "getOpClass op = Simple" (K ALL_TAC) THEN DISCH_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[ALL; safe_exp_simps]) THEN
    GVS[pair_case_eq; case_eq "result"; option_case_eq] THEN
    CAN2DAUX_IH_TAC "ctxt1" THEN QEXISTS_TAC "ctxt1" THEN ASM_REWRITE_TAC[] THEN
    TRY (ASM_MESON_TAC[CAN2DAUX_state_ok_ok_event] THEN NO_TAC) THEN
    DRULE_ALL CAN2DAUX_state_ok_do_app_rev THEN STRIP_TAC THEN
    REPEAT TOP_CASE_TAC THEN ASM_REWRITE_TAC[]]);;

kit_distinct_names := can2daux_distinct_names;;

let CAN2DAUX_evaluate_v_ok_App = prove
 (can2daux_case 8,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `op = Eval` THENL
   [MATCH_MP_TAC (SPEC_ALL CAN2DAUX_evaluate_v_ok_App_Eval) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `op = Opapp` THENL
   [MATCH_MP_TAC (SPEC_ALL CAN2DAUX_evaluate_v_ok_App_Opapp) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC (SPEC_ALL CAN2DAUX_evaluate_v_ok_App_Op) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_v_ok (HOL4: Finalise evaluate_v_ok)                              *)
(* ------------------------------------------------------------------------- *)

let evaluate_v_ok = prove
 (rand (concl can2daux_ind_thm),
  MATCH_MP_TAC can2daux_ind_thm THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
   [CAN2DAUX_evaluate_v_ok_Nil; CAN2DAUX_evaluate_v_ok_Cons; CAN2DAUX_evaluate_v_ok_Lit;
    CAN2DAUX_evaluate_v_ok_Raise; CAN2DAUX_evaluate_v_ok_Handle; CAN2DAUX_evaluate_v_ok_Con;
    CAN2DAUX_evaluate_v_ok_Var; CAN2DAUX_evaluate_v_ok_Fun; CAN2DAUX_evaluate_v_ok_App;
    CAN2DAUX_evaluate_v_ok_Log; CAN2DAUX_evaluate_v_ok_If; CAN2DAUX_evaluate_v_ok_Mat;
    CAN2DAUX_evaluate_v_ok_Let; CAN2DAUX_evaluate_v_ok_Letrec;
    CAN2DAUX_evaluate_v_ok_Tannot; CAN2DAUX_evaluate_v_ok_Lannot;
    CAN2DAUX_evaluate_v_ok_pmatch_Nil; CAN2DAUX_evaluate_v_ok_pmatch_Cons;
    CAN2DAUX_evaluate_v_ok_decs_Nil; CAN2DAUX_evaluate_v_ok_decs_Cons;
    CAN2DAUX_evaluate_v_ok_decs_Dlet; CAN2DAUX_evaluate_v_ok_decs_Dletrec;
    CAN2DAUX_evaluate_v_ok_decs_Dtype; CAN2DAUX_evaluate_v_ok_decs_Dtabbrev;
    CAN2DAUX_evaluate_v_ok_decs_Denv; CAN2DAUX_evaluate_v_ok_decs_Dexn;
    CAN2DAUX_evaluate_v_ok_decs_Dmod; CAN2DAUX_evaluate_v_ok_decs_Dlocal]));;
