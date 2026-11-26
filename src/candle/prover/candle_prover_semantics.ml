(* ========================================================================= *)
(* candle_prover_semantics: port of HOL4 candle/prover/                     *)
(* candle_prover_semanticsScript.sml (CakeML v3479).  Top-level soundness    *)
(* theorem for the Candle theorem prover.                                    *)
(*                                                                           *)
(* The headline semantics_thm is HOL4's statement, bound as the OCaml term   *)
(* candle_prover_semantics_statement in candle_prover_statement.ml (with the *)
(* notions it uses and the files that define them); the end of this file    *)
(* checks, failing loudly otherwise, that the theorem has no hypotheses and *)
(* that its conclusion is alpha-equivalent to that term.                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's translation_extends "candle_kernelProg" is not needed: nothing   *)
(*   here translates, and the program, its environments and states are the *)
(*   constants and theorems of candle_kernelProg.ml and basisProg.ml.        *)
(* - HOL4's Overloads basis_env and basis_state are the environment and the *)
(*   state function of basis_Decls_thm (basisProg_env_9 and basisProg_st_0  *)
(*   at present; OCaml terms can3aux_basis_env, can3aux_basis_state): the   *)
(*   statements are written with variables of these names, replaced by      *)
(*   can3aux_basis.  HOL4's basis is basisProg_basis.                        *)
(* - HOL4's EVAL of simple_dec, safe_dec and prog_syntax_ok over the basis  *)
(*   program (about 609,000 term nodes) is call-by-value evaluation with    *)
(*   HOL Light's Compute and two compsets made here (can3aux_dec_cs,         *)
(*   can3aux_cons_cs); for safe_dec, safe_exp is first restated in a form   *)
(*   that evaluation decides (CAN3AUX_safe_exp_eval).  The other EVALs are  *)
(*   rewriting with the definitions of the states and of the NAME_refs      *)
(*   constants.                                                              *)
(* - HOL4 LLOOKUP l n is oEL n l; HOL4's s with clock := k is               *)
(*   state_clock_fupd (K k) s; HOL4's names eval_state_ok, env_ok, v_ok,     *)
(*   state_ok, kernel_loc_ok, ref_ok, simple_dec, STATE and CONTEXT are      *)
(*   candle_eval_state_ok, candle_env_ok, candle_v_ok, candle_state_ok,      *)
(*   candle_kernel_loc_ok, candle_ref_ok, candle_simple_dec,                 *)
(*   holKernelProof_STATE and holKernelProof_CONTEXT; init_state and         *)
(*   init_env are ml_init_state and ml_init_env.                             *)
(* - prove_env_ok is HOL4's OCaml conversion, with the same cache, provers  *)
(*   and base cases (a hash table instead of HOL4's Net).                    *)
(* - semantics_thm: HOL4 shows in each of the two cases (Terminate, Diverge) *)
(*   that the run of candle_code ends in the state of candle_prog_thm (up to *)
(*   the clock) or times out without events, and then applies              *)
(*   evaluate_v_ok to prog; here that argument is one lemma for any clock   *)
(*   (CAN3AUX_semantics_events) used by both cases.                          *)
(* - Decision D8 (not in HOL4): at the end, prog_syntax_ok_candle_code       *)
(*   proves the hypothesis prog_syntax_ok candle_code of semantics_thm by    *)
(*   evaluation, and semantics_thm_strong is semantics_thm without it (its  *)
(*   statement is in candle_prover_statement.ml too).                        *)
(* - Local helpers that are not HOL4 theorems are CAN3AUX_ (OCaml values     *)
(*   can3aux_).                                                              *)
(* ========================================================================= *)

needs "candle/prover/candle_prover_statement.ml";;
needs "misc/misc.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/evaluate.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/candle_basis_evaluate.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "semantics/semantics.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "hol4/sptree.ml";;
needs "candle/prover/perms.ml";;
needs "candle/prover/candle_kernel_funs.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_evaluate.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "basis/basisProg.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_progLib.ml";;
needs "hol4/llist.ml";;
needs "hol4/lprefix_lub.ml";;

type_invention_error := true;;

let LPREFIX_LNTH = prove
 (`!n (xs:A llist) l ll.
     LPREFIX xs l /\ LNTH n xs = NONE /\ LTAKE n l = SOME ll ==>
     LPREFIX xs (llist_fromList ll)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN LLIST_CASE_TAC `xs:A llist` THEN
  REWRITE_TAC[LPREFIX_LNIL; LNTH_THM; option_DISTINCT; LPREFIX_LCONS] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)))) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[LTAKE_THM; OPTION_MAP_EQ_SOME]) THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `l1:A list` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[llist_fromList_def; LCONS_11] THEN
  EXISTS_TAC `llist_fromList (l1:A list)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* - The basis program:                                                      *)
(*   basis, basis_env, basis_state                                           *)
(* - The candle program (includes the former):                               *)
(*   candle_code, candle_init_env, candle_init_state                         *)
(* ------------------------------------------------------------------------- *)

(* HOL4 Overload basis_env = (basis_Decls_thm |> concl |> rator |> rand) *)
let can3aux_basis_env = rand (rator (concl basis_Decls_thm));;

(* HOL4 Overload basis_state = (basis_Decls_thm |> concl |> rand |> rator) *)
let can3aux_basis_state = rator (rand (concl basis_Decls_thm));;

let can3aux_basis tm =
  subst [can3aux_basis_env,`basis_env:v sem_env`;
         can3aux_basis_state,`basis_state:(FFI)ffi_state->(FFI)state`] tm;;

(* the definitions NAME_refs = [] of the reference constants in a term      *)
(* (candle_kernel_vals' can2aaux_refs_def)                                   *)
let can3aux_refs_defs tm =
  map can2aaux_refs_def
    (setify (find_terms (fun t -> is_const t && type_of t = `:(v store_v)list` &&
                                  fst (dest_const t) <> "NIL") tm));;

let can3aux_basis_state_def =
  ml_prog_fetch (fst (dest_const can3aux_basis_state) ^ "_def");;

(* ------------------------------------------------------------------------- *)
(* Show that the basis program satisfies post_state_ok, simple_dec and       *)
(* safe_dec. Use this to show basis_env is env_ok.                           *)
(* ------------------------------------------------------------------------- *)

let post_state_ok_basis_state = prove
 (can3aux_basis `post_state_ok ((basis_state:(FFI)ffi_state->(FFI)state) ffi)`,
  REWRITE_TAC[post_state_ok_def; kernel_types_def; IN_INSERT; NOT_IN_EMPTY; kernel_locs] THEN
  REWRITE_TAC[can3aux_basis_state_def; state_INFO.ri_accessors] THEN
  REWRITE_TAC(can3aux_refs_defs (concl can3aux_basis_state_def)) THEN
  REWRITE_TAC[APPEND; LENGTH] THEN ARITH_TAC);;

(* safe_exp in a form that call-by-value evaluation decides: the            *)
(* constructor test as a case on the option, the FFI test as a case on the  *)
(* operator                                                                  *)
let CAN3AUX_safe_exp_eval = prove
 (CASE_TERM
  `safe_exp =
     every_exp (\x. match x with
                      Con opt xs -> (match opt with
                                       NONE -> T
                                     | SOME id -> ~(id_to_n id IN kernel_ctors))
                    | App op xs -> (match op with
                                      FFI s -> ~(s = kernel_ffi)
                                    | _ -> T)
                    | _ -> T)`,
  REWRITE_TAC[safe_exp_def] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `x:exp` THEN QCASES_ON "x" THEN CAKE_REWRITE_TAC[] THENL
   [QCASES_ON "a0" THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    QCASES_ON "a0" THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "op"; injectivity "op"]]);;

(* HOL4 EVAL of simple_dec and safe_dec *)
let can3aux_dec_cs =
  let cs = Compute.bool_compset () in
  Compute.add_conv (`(=):A->A->bool`,2,ml_prog_lit_eq_conv) cs;
  Compute.add_thms
    [candle_simple_dec_def; candle_simple_exp_def; candle_simple_pat_def;
     safe_dec_def; CAN3AUX_safe_exp_eval; every_dec_def; every_exp_def;
     case_def "dec"; case_def "exp"; case_def "op"; case_def "pat"; case_def "option";
     case_def "list"; case_def "prod"; case_def "id";
     ALL; MAP; o_THM; FST; SND; id_to_n_def; kernel_ctors_def; kernel_ffi_def;
     IN_UNION; IN_INSERT; EQF_INTRO (SPEC_ALL NOT_IN_EMPTY)] cs;
  cs;;

(* HOL4 once_rewrite_tac [basis_def] and EVAL: the definition of the program *)
(* is used by congruence only (no rewriting of the program term)             *)
let basis_decs_ok =
  let ev tm = EQT_ELIM (CONV_RULE (RAND_CONV (Compute.CBV_CONV can3aux_dec_cs))
                          (AP_TERM tm basisProg_basis_def)) in
  CONJ (ev `ALL candle_simple_dec`) (ev `ALL safe_dec`);;

(* HOL4 EVAL of prog_syntax_ok.  The constructor lookups (ALOOKUP on the    *)
(* literal constructor environment) are done in one pass each, with a cache  *)
(* of the theorems, and the mlstring comparisons are cached too: the same    *)
(* few dozen lookups recur thousands of times in the kernel's code.          *)
let can3aux_mlstring_eq_cache = (Hashtbl.create 1000 : (string * string, thm) Hashtbl.t);;

let CAN3AUX_MLSTRING_EQ_CONV tm =
  let a,b = dest_eq tm in
  let key = (ml_prog_dest_mlstring a, ml_prog_dest_mlstring b) in
  try Hashtbl.find can3aux_mlstring_eq_cache key with Not_found ->
  let th = ML_PROG_MLSTRING_EQ_CONV tm in
  Hashtbl.add can3aux_mlstring_eq_cache key th; th;;

let can3aux_alookup_nil = CONJUNCT1 ALOOKUP_THM;;
let can3aux_alookup_cons = CONJUNCT2 ALOOKUP_THM;;
let can3aux_T_tm = `T`;;
let can3aux_cond_t = prove (`!a b:A. (if T then a else b) = a`, REWRITE_TAC[]);;
let can3aux_cond_f = prove (`!a b:A. (if F then a else b) = b`, REWRITE_TAC[]);;

(* ALOOKUP l q for a literal list l with literal mlstring keys and a literal *)
(* key q (HOL4 ALOOKUP_def, step by step)                                    *)
let rec CAN3AUX_ALOOKUP_CONV tm =
  let l = rand (rator tm) in
  if is_const l then REWR_CONV can3aux_alookup_nil tm else
  let th1 = REWR_CONV can3aux_alookup_cons tm in
  let c = rand (concl th1) in
  let gab,b = dest_comb c in
  let ga,a = dest_comb gab in
  let cnd,g = dest_comb ga in
  let eqth = CAN3AUX_MLSTRING_EQ_CONV g in
  let th2 = AP_THM (AP_THM (AP_TERM cnd eqth) a) b in
  if rand (concl eqth) = can3aux_T_tm then
    TRANS th1 (TRANS th2 (ISPECL [a;b] can3aux_cond_t))
  else
    let th3 = TRANS th1 (TRANS th2 (ISPECL [a;b] can3aux_cond_f)) in
    TRANS th3 (CAN3AUX_ALOOKUP_CONV b);;

let can3aux_alookup_cache = (Hashtbl.create 1000 : (term,thm) Hashtbl.t);;

let CAN3AUX_ALOOKUP_CACHED_CONV tm =
  try Hashtbl.find can3aux_alookup_cache tm with Not_found ->
  let th = CAN3AUX_ALOOKUP_CONV tm in
  Hashtbl.add can3aux_alookup_cache tm th; th;;

let can3aux_cons_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`(=):A->A->bool`,2,ml_prog_lit_eq_conv) cs;
  Compute.add_conv (`ALOOKUP:(A#B)list->A->B option`,2,CAN3AUX_ALOOKUP_CACHED_CONV) cs;
  Compute.add_thms
    [prog_syntax_ok_def; check_cons_dec_list_def; one_con_check_def; do_con_check_def;
     every_exp_def; build_tdefs_def; build_constrs_def; alist_to_ns_def; nsAppend_def;
     nsLift_def; nsSing_def; nsEmpty_def; nsLookup_def; REVERSE; APPEND; MAP;
     LENGTH; ALL; IS_SOME_DEF; sem_env_INFO.ri_accessors; ml_init_env_def;
     case_def "dec"; case_def "exp"; case_def "option"; case_def "list"; case_def "prod";
     case_def "id"; case_def "namespace"; injectivity "option"; PAIR_EQ] cs;
  cs;;

(* the constructor environment of the basis program *)
let CAN3AUX_check_cons_basis =
  CONV_RULE (RAND_CONV (Compute.CBV_CONV can3aux_cons_cs))
    (AP_TERM `check_cons_dec_list (sem_env_c ml_init_env)` basisProg_basis_def);;

(* HOL4 proves it inside env_ok_basis_env by EVAL_TAC *)
let CAN3AUX_prog_syntax_ok_basis = prove
 (`prog_syntax_ok basisProg_basis`,
  REWRITE_TAC[prog_syntax_ok_def; CAN3AUX_check_cons_basis; IS_SOME_DEF]);;

(* the constructors of ml_init_env have no kernel type stamp *)
let CAN3AUX_init_env_not_kernel_types = prove
 (`!id len tag tn.
     nsLookup (sem_env_c ml_init_env) id = SOME (len,TypeStamp tag tn) ==>
     ~(tn IN kernel_types)`,
  REWRITE_TAC[ml_init_env_def; sem_env_INFO.ri_accessors] THEN
  SIMP[nsLookup_Bind_v_some] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[kernel_types_def; IN_INSERT; NOT_IN_EMPTY] THEN
  GVS[ALOOKUP_def; COND_CASE_EQ; option_INJ; PAIR_EQ; injectivity "stamp";
      distinctness "stamp"; option_DISTINCT] THEN
  ARITH_TAC);;

(* an environment that extends to an ok environment is ok *)
let CAN3AUX_env_ok_extend_dec_env_left = prove
 (`candle_env_ok ctxt (extend_dec_env env1 env2) ==> candle_env_ok ctxt env1`,
  REWRITE_TAC[candle_env_ok_def; extend_dec_env_def; sem_env_INFO.ri_accessors;
              nsLookup_nsAppend_some] THEN
  MESON_TAC[]);;

let env_ok_basis_env = prove
 (can3aux_basis `candle_env_ok (ctxt:update list) basis_env`,
  MP_TAC (MATCH_MP (MATCH_MP Decls_IMP_Prog basis_Decls_thm)
                   CAN3AUX_prog_syntax_ok_basis) THEN
  REWRITE_TAC[ml_Prog_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `ctxt:update list` o MATCH_MP
    (REWRITE_RULE[GSYM AND_IMP_INTRO] evaluate_basis_v_ok_decs)) THEN
  REWRITE_TAC[post_state_ok_with_clock; post_state_ok_basis_state; basis_decs_ok;
              env_ok_init_env; CAN3AUX_init_env_not_kernel_types] THEN
  CAKE_REWRITE_TAC[] THEN MESON_TAC[CAN3AUX_env_ok_extend_dec_env_left]);;

(* ------------------------------------------------------------------------- *)
(* Show that the candle_init_state is state_ok.                              *)
(* ------------------------------------------------------------------------- *)

(* TODO Move this to standard/ml_kernel; a copy of this is used by the       *)
(*      OpenTheory reader.                                                   *)

let init_refs_def = cake_def
  `init_refs = hol_refs_REC init_type_constants init_term_constants init_axioms
                            init_context`;;

let STATE_init_refs = prove
 (`holKernelProof_STATE init_context init_refs`,
  SIMP[holKernelProof_STATE_def; holKernelProof_CONTEXT_def; init_type_constants_def;
       init_axioms_def; init_term_constants_def; init_context_def; init_refs_def;
       init_ctxt_def; extends_def; RTC_REFL]);;

let candle_init_state_stamp = prove
 (`n IN kernel_types ==> n < state_next_type_stamp (candle_init_state (ffi:(FFI)ffi_state))`,
  REWRITE_TAC[kernel_types_def; IN_INSERT; NOT_IN_EMPTY; candle_init_state_def;
              state_INFO.ri_accessors] THEN ARITH_TAC);;

(* the locations of the kernel's references (HOL4 evaluates them) *)
let CAN3AUX_kernel_refs =
  CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[LENGTH; APPEND; refs_defs]
     (REWRITE_RULE (can3aux_refs_defs (concl the_context_def))
       (end_itlist CONJ [the_type_constants_def; the_term_constants_def; the_axioms_def;
                         the_context_def])));;

(* HOL4 [local,simp] *)
let kernel_refs_distinct = prove
 (`~(the_type_constants = the_term_constants) /\
   ~(the_type_constants = the_axioms) /\
   ~(the_type_constants = the_context) /\
   ~(the_term_constants = the_axioms) /\
   ~(the_term_constants = the_context) /\
   ~(the_axioms = the_context)`,
  REWRITE_TAC[CAN3AUX_kernel_refs; injectivity "v"] THEN ARITH_TAC);;
let _ = cake_add_simps [kernel_refs_distinct];;

(* the references of candle_init_state as an explicit list (HOL4 evaluates *)
(* them with candle_init_state_def and EL_APPEND_EQN)                       *)
let CAN3AUX_candle_init_state_refs =
  let tm = `state_refs (candle_init_state (ffi:(FFI)ffi_state))` in
  (REWRITE_CONV[candle_init_state_def; state_INFO.ri_accessors] THENC
   REWRITE_CONV (can3aux_refs_defs (concl candle_init_state_def)) THENC
   REWRITE_CONV[APPEND]) tm;;

(* HOL4 [local] *)
let LLOOKUPs = prove
 (`(Loc T loc = the_type_constants ==>
      oEL loc (state_refs (candle_init_state (ffi:(FFI)ffi_state))) =
      SOME (Refv init_type_constants_v)) /\
   (Loc T loc = the_term_constants ==>
      oEL loc (state_refs (candle_init_state ffi)) =
      SOME (Refv init_term_constants_v)) /\
   (Loc T loc = the_axioms ==>
      oEL loc (state_refs (candle_init_state ffi)) =
      SOME (Refv init_axioms_v)) /\
   (Loc T loc = the_context ==>
      oEL loc (state_refs (candle_init_state ffi)) =
      SOME (Refv init_context_v))`,
  REWRITE_TAC[CAN3AUX_kernel_refs; injectivity "v"] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CAN3AUX_candle_init_state_refs; oEL_EQ_EL] THEN
  CONV_TAC (ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_init_state_refs = prove
 (`loc IN kernel_locs ==>
   candle_kernel_loc_ok init_refs loc (state_refs (candle_init_state (ffi:(FFI)ffi_state)))`,
  REWRITE_TAC[kernel_locs; candle_kernel_loc_ok_def; CAN3AUX_kernel_refs;
              injectivity "v"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CAN3AUX_candle_init_state_refs; oEL_EQ_EL] THEN
  CONV_TAC (ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[LENGTH; injectivity "store_v"] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[init_refs_def; hol_refs_INFO.ri_accessors; init_type_constants_v_thm;
              init_term_constants_v_thm; init_axioms_v_thm; init_context_v_thm]);;

let candle_init_state_eval = prove
 (`candle_eval_state_ok (state_eval_state (candle_init_state (ffi:(FFI)ffi_state)))`,
  REWRITE_TAC[candle_init_state_def; state_INFO.ri_accessors; candle_eval_state_ok_def]);;
let _ = cake_add_simps [candle_init_state_eval];;

let candle_init_state_ffi = prove
 (`state_ffi (candle_init_state (ffi:(FFI)ffi_state)) = ffi`,
  REWRITE_TAC[candle_init_state_def; state_INFO.ri_accessors]);;
let _ = cake_add_simps [candle_init_state_ffi];;

let candle_init_state_state_ok = prove
 (`ffi_state_io_events (ffi:(FFI)ffi_state) = [] ==>
   candle_state_ok init_context (candle_init_state ffi)`,
  STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_state_ok_def; candle_init_state_stamp; candle_init_state_ffi;
                  candle_init_state_eval; ALL] THEN
  EXISTS_TAC `init_refs` THEN REWRITE_TAC[STATE_init_refs; candle_init_state_refs] THEN
  REWRITE_TAC[kernel_locs; CAN3AUX_candle_init_state_refs; oEL_EQ_EL] THEN
  CONV_TAC (ONCE_DEPTH_CONV LENGTH_CONV) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `loc = 0 \/ loc = 1` MP_TAC THENL
   [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)) &&
                                                  fst (dest_var (lhs (concl th))) = "r")) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC (ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[candle_ref_ok_def]);;

(* ------------------------------------------------------------------------- *)
(* First prove that all kernel values are v_ok (this follows from the        *)
(* definition of v_ok but it's nice to have in one theorem.)                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 prove_v_ok: v_ok for a kernel function, by the rules v_ok_KernelVals, *)
(* v_ok_Inferred and inferred_KernelFuns                                      *)
let can3aux_v_ok_kernel_fun =
  let th = prove
   (`!ctxt (f:v). f IN kernel_funs ==> candle_v_ok ctxt f`,
    MESON_TAC[candle_v_ok_KernelVals; candle_v_ok_Inferred; candle_inferred_KernelFuns]) in
  fun v -> MP (SPECL [`ctxt:update list`; v] th)
              (EQT_ELIM (REWRITE_CONV[kernel_funs_def; IN_INSERT]
                           (mk_comb (mk_comb (`(IN):v->(v->bool)->bool`, v), `kernel_funs`))));;

(* HOL4 [local] *)
let v_ok_kernel_funs =
  let vs = striplist (fun t -> let f,x = dest_comb t in rand f, x)
             (rhs (concl kernel_funs_def)) in
  let vs = filter (fun t -> not (is_const t && fst (dest_const t) = "EMPTY")) vs in
  end_itlist CONJ (map can3aux_v_ok_kernel_fun vs);;

(* ------------------------------------------------------------------------- *)
(* Now prove that candle_init_env is env_ok.                                 *)
(* ------------------------------------------------------------------------- *)

(* Prove env_ok and cache intermediate results (HOL4 prove_env_ok): an       *)
(* environment built by ml_progLib (abbreviation constants, merge_env,        *)
(* write_mod, write, write_cons) is env_ok init_context by recursion on its  *)
(* term; the basis environment (env_ok_basis_env), empty_env and the empty   *)
(* environment are the base cases, and the values written are the kernel     *)
(* functions (v_ok_kernel_funs).                                             *)

let can3aux_env_ok_tm = `candle_env_ok init_context`;;

let can3aux_inst_context = INST [`init_context`,`ctxt:update list`];;

let can3aux_dest_env_ok tm =
  match tm with
    Comb(Comb(Const("candle_env_ok",_),Const("init_context",_)),env) -> env
  | _ -> failwith "dest_env_ok: not an env_ok";;

let can3aux_mk_env_ok tm = mk_comb (can3aux_env_ok_tm, tm);;

(* Cache of previously proven theorems *)
let can3aux_env_ok_cache = (Hashtbl.create 1000 : (term,thm) Hashtbl.t);;

let can3aux_insert_term th =
  let th = can3aux_inst_context th in
  Hashtbl.replace can3aux_env_ok_cache (can3aux_dest_env_ok (concl th)) th;;

(* HOL4 reset_cache () *)
let can3aux_reset_cache () =
  Hashtbl.reset can3aux_env_ok_cache;
  List.iter can3aux_insert_term [env_ok_basis_env; env_ok_empty_env; env_ok_nsEmpty];;

let () = can3aux_reset_cache ();;

(* HOL4 get_cache () *)
let can3aux_get_cache () =
  Hashtbl.fold (fun _ th acc -> th :: acc) can3aux_env_ok_cache [];;

(* 'Prove' v_ok for kernel values by looking them up in the kernel funs     *)
(* theorem from above.                                                       *)
let can3aux_v_ok_thms = map can3aux_inst_context (CONJUNCTS v_ok_kernel_funs);;

let can3aux_prove_v_ok tm =
  let goal = mk_comb (`candle_v_ok init_context`, tm) in
  try find (fun th -> aconv (concl th) goal) can3aux_v_ok_thms
  with Failure _ -> failwith "prove_env_ok: a value that is not a kernel function";;

let can3aux_write_th =
  can3aux_inst_context (REWRITE_RULE[GSYM AND_IMP_INTRO] env_ok_write);;
let can3aux_merge_env_th =
  can3aux_inst_context (REWRITE_RULE[GSYM AND_IMP_INTRO] env_ok_merge_env);;
let can3aux_write_mod_th =
  can3aux_inst_context (REWRITE_RULE[GSYM AND_IMP_INTRO] env_ok_write_mod);;
let can3aux_write_cons_th =
  can3aux_inst_context (REWRITE_RULE[GSYM AND_IMP_INTRO] env_ok_write_cons);;
let can3aux_write_exn_th = can3aux_inst_context env_ok_write_Exn;;

(* t IN kernel_types ==> nm IN kernel_ctors, for literals t and nm (HOL4    *)
(* SIMP_CONV list_ss [kernel_types_def, kernel_ctors_def])                   *)
let can3aux_ctor_conv =
  REWRITE_CONV[kernel_types_def; kernel_ctors_def; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THENC
  DEPTH_CONV (NUM_EQ_CONV ORELSEC ML_PROG_MLSTRING_EQ_CONV) THENC REWRITE_CONV[];;

(* the provers of HOL4, by the head of the environment term *)
let rec can3aux_prove_bare tm =
  (* bare environment: an abbreviation constant, unfolded *)
  let name,ty = dest_const tm in
  if ty <> `:v sem_env` then failwith "not an env" else
  let defn = ml_prog_fetch (name ^ "_def") in
  let th = AP_TERM can3aux_env_ok_tm defn in
  EQ_MP (SYM th) (can3aux_env_ok_conv (rand (concl th)))
and can3aux_prove_merge_env e1 e2 =
  (* merge_env e1 e2 *)
  MATCH_MP (MATCH_MP can3aux_merge_env_th (can3aux_env_ok_conv (can3aux_mk_env_ok e1)))
    (can3aux_env_ok_conv (can3aux_mk_env_ok e2))
and can3aux_prove_write_mod mn e1 e2 =
  (* write_mod mn env1 env2 *)
  INST [mn,`mn:mlstring`]
    (MATCH_MP (MATCH_MP can3aux_write_mod_th (can3aux_env_ok_conv (can3aux_mk_env_ok e1)))
       (can3aux_env_ok_conv (can3aux_mk_env_ok e2)))
and can3aux_prove_write n v env =
  (* write nm v env *)
  INST [n,`nm:mlstring`]
    (MATCH_MP (MATCH_MP can3aux_write_th (can3aux_env_ok_conv (can3aux_mk_env_ok env)))
       (can3aux_prove_v_ok v))
and can3aux_prove_write_cons n s env =
  (* write_cons n (m,TypeStamp nm t) env *)
  let m,st = dest_pair s in
  let t = rand st and nm = rand (rator st) in
  let th1 = can3aux_env_ok_conv (can3aux_mk_env_ok env) in
  let goal = mk_imp (mk_comb (mk_comb (`(IN):num->(num->bool)->bool`, t), `kernel_types`),
                     mk_comb (mk_comb (`(IN):mlstring->(mlstring->bool)->bool`, nm),
                              `kernel_ctors`)) in
  let th2 = can3aux_ctor_conv goal in
  let th3 = INST [m,`n:num`; nm,`s:mlstring`; t,`t:num`; n,`nm:mlstring`]
              (MATCH_MP can3aux_write_cons_th th1) in
  MATCH_MP th3 (EQT_ELIM th2)
and can3aux_prove_write_exn n s env =
  (* write_cons n (k,ExnStamp m) env *)
  let k,st = dest_pair s in
  let m = rand st in
  INST [k,`n:num`; m,`m:num`; n,`nm:mlstring`]
    (MATCH_MP can3aux_write_exn_th (can3aux_env_ok_conv (can3aux_mk_env_ok env)))
and can3aux_env_ok_conv tm =
  let env = can3aux_dest_env_ok tm in
  try Hashtbl.find can3aux_env_ok_cache env with Not_found ->
  let f,xs = strip_comb env in
  let th =
    match f,xs with
      Const(_,_),[] -> can3aux_prove_bare env
    | Const("merge_env",_),[e1;e2] -> can3aux_prove_merge_env e1 e2
    | Const("ml_write_mod",_),[mn;e1;e2] -> can3aux_prove_write_mod mn e1 e2
    | Const("ml_write",_),[n;v;e] -> can3aux_prove_write n v e
    | Const("ml_write_cons",_),[n;s;e] ->
        (match strip_comb (snd (dest_pair s)) with
           Const("TypeStamp",_),[_;_] -> can3aux_prove_write_cons n s e
         | Const("ExnStamp",_),[_] -> can3aux_prove_write_exn n s e
         | _ -> failwith "prove_env_ok: write_cons")
    | _ -> failwith ("prove_env_ok: cannot prove " ^ string_of_term tm) in
  if aconv (concl th) tm then (Hashtbl.replace can3aux_env_ok_cache env th; th)
  else failwith "prove_env_ok: wrong theorem";;

(* HOL4 prove_env_ok = EQT_INTRO o env_ok_conv *)
let prove_env_ok = EQT_INTRO o can3aux_env_ok_conv;;

let env_ok_candle_init_env = prove
 (`candle_env_ok init_context candle_init_env`,
  CONV_TAC prove_env_ok);;

(* ------------------------------------------------------------------------- *)
(* Top-level semantics theorem.                                              *)
(* ------------------------------------------------------------------------- *)

(* TODO Print context updates on FFI                                         *)
(*    -- Magnus: actually, we might want to print the entire context         *)
(*               for each theorem to make soundness statement simple         *)
(*   TODO: Use 'ffi                                                          *)

(* TODO why do these both exist? *)

(* HOL4 [local,simp] (the proofs below do not use it) *)
let init_context_init_ctxt = prove
 (`init_ctxt = init_context`,
  REWRITE_TAC[init_ctxt_def; init_context_def]);;

(* the evaluation of candle_code from the initial state with eval state es *)
(* (HOL4: candle_prog_thm, Decls_set_eval_state, Decls_IMP_Prog, Prog_def)  *)
let CAN3AUX_candle_Prog = prove
 (`prog_syntax_ok candle_code ==>
   ?ck1 ck2.
     evaluate_decs (state_clock_fupd (combin_K ck1)
                      (state_eval_state_fupd (combin_K es) (ml_init_state (ffi:(FFI)ffi_state))))
                   ml_init_env candle_code =
     (state_clock_fupd (combin_K ck2) (state_eval_state_fupd (combin_K es) (candle_init_state ffi)),
      Rval candle_init_env)`,
  DISCH_TAC THEN
  SUBGOAL_THEN `state_eval_state (ml_init_state (ffi:(FFI)ffi_state)) = NONE` ASSUME_TAC THENL
   [REWRITE_TAC[ml_init_state_def; state_INFO.ri_accessors]; ALL_TAC] THEN
  MP_TAC (SPEC `es:(eval_state)option`
    (MATCH_MP ml_Decls_set_eval_state (CONJ candle_prog_thm
       (ASSUME `state_eval_state (ml_init_state (ffi:(FFI)ffi_state)) = NONE`)))) THEN
  DISCH_THEN (MP_TAC o MATCH_MP Decls_IMP_Prog) THEN ASM_REWRITE_TAC[ml_Prog_def] THEN
  MESON_TAC[]);;

(* two states that differ at most in their clocks *)
let CAN3AUX_clock_fupd_eq = prove
 (`state_clock_fupd (combin_K a) (s1:(FFI)state) = state_clock_fupd (combin_K b) s2 ==>
   s1 = state_clock_fupd (combin_K (state_clock s1)) s2`,
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* evaluate_decs_clock_determ when the second run returns a value *)
let CAN3AUX_clock_determ_Rval = prove
 (`evaluate_decs (state_clock_fupd (combin_K k1) (s:(FFI)state)) env p = (s1,r1) /\
   evaluate_decs (state_clock_fupd (combin_K k2) s) env p = (s2,Rval x) ==>
   r1 = Rval x \/ (r1 = Rerr (Rabort Rtimeout_error) /\ k1 < k2)`,
  DISCH_THEN (MP_TAC o MATCH_MP evaluate_decs_clock_determ) THEN
  QCASES_ON "r1" THEN CAKE_REWRITE_TAC[] THENL
   [MESON_TAC[];
    QCASES_ON "a" THEN CAKE_REWRITE_TAC[] THEN
    QCASES_ON "a'" THEN CAKE_REWRITE_TAC[]]);;

(* a run of candle_code that returns gives candle_init_env, in the state of *)
(* candle_prog_thm up to the clock (HOL4: evaluate_decs_add_to_clock twice)  *)
let CAN3AUX_candle_code_Rval = prove
 (`prog_syntax_ok candle_code /\
   evaluate_decs (state_clock_fupd (combin_K k)
                    (state_eval_state_fupd (combin_K es) (ml_init_state (ffi:(FFI)ffi_state))))
                 ml_init_env candle_code = (s1,Rval env1) ==>
   env1 = candle_init_env /\
   s1 = state_clock_fupd (combin_K (state_clock s1))
          (state_eval_state_fupd (combin_K es) (candle_init_state ffi))`,
  STRIP_TAC THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_TAC `ck2:num`) o
                 MATCH_MP CAN3AUX_candle_Prog) THEN
  MP_TAC (ISPECL
    [`state_clock_fupd (combin_K k)
        (state_eval_state_fupd (combin_K es) (ml_init_state (ffi:(FFI)ffi_state)))`;
     `ml_init_env`; `candle_code`; `s1:(FFI)state`; `Rval env1:(v sem_env,v)result`;
     `ck1:num`] evaluate_decs_add_to_clock) THEN
  MP_TAC (ISPECL
    [`state_clock_fupd (combin_K ck1)
        (state_eval_state_fupd (combin_K es) (ml_init_state (ffi:(FFI)ffi_state)))`;
     `ml_init_env`; `candle_code`;
     `state_clock_fupd (combin_K ck2)
        (state_eval_state_fupd (combin_K es) (candle_init_state (ffi:(FFI)ffi_state)))`;
     `Rval candle_init_env:(v sem_env,v)result`; `k:num`] evaluate_decs_add_to_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"; state_INFO.ri_accfupds; state_INFO.ri_fupdfupds;
                  K_o_THM; K_THM] THEN
  SUBGOAL_THEN `k + ck1 = ck1 + k` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP CAN3AUX_clock_fupd_eq) THEN
  REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM]);;

(* a run of candle_code that fails (it times out) has no events (HOL4:      *)
(* evaluate_decs_clock_determ and evaluate_decs_ffi_mono_clock)              *)
let CAN3AUX_candle_code_Rerr = prove
 (`prog_syntax_ok candle_code /\ ffi_state_io_events (ffi:(FFI)ffi_state) = [] /\
   evaluate_decs (state_clock_fupd (combin_K k)
                    (state_eval_state_fupd (combin_K es) (ml_init_state ffi)))
                 ml_init_env candle_code = (s1,Rerr e) ==>
   ffi_state_io_events (state_ffi s1) = []`,
  STRIP_TAC THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `ck1:num` (X_CHOOSE_TAC `ck2:num`) o
                 MATCH_MP CAN3AUX_candle_Prog) THEN
  FIRST_X_ASSUM (fun a1 -> FIRST_X_ASSUM (fun a2 ->
    MP_TAC (MATCH_MP CAN3AUX_clock_determ_Rval (CONJ a1 a2)) THEN
    ASSUME_TAC a1 THEN ASSUME_TAC a2)) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"] THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`k:num`; `ck1:num`;
                  `state_eval_state_fupd (combin_K es) (ml_init_state (ffi:(FFI)ffi_state))`;
                  `ml_init_env`; `candle_code`] evaluate_decs_ffi_mono_clock) THEN
  ASM_SIMP_TAC[LT_IMP_LE; FST; io_events_mono_def; state_INFO.ri_accfupds;
               candle_init_state_ffi; isPREFIX_NILR]);;

(* the events of a safe program run after candle_code are ok (HOL4:        *)
(* el 3 (CONJUNCTS evaluate_v_ok))                                           *)
let CAN3AUX_prog_events = prove
 (`!(s1:(FFI)state) prog s2 r.
   candle_state_ok init_context s1 /\ ALL safe_dec prog /\
   evaluate_decs s1 (extend_dec_env candle_init_env ml_init_env) prog = (s2,r) ==>
   ALL ok_event (ffi_state_io_events (state_ffi s2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`s1:(FFI)state`; `extend_dec_env candle_init_env ml_init_env`;
                 `prog:dec list`; `r:(v sem_env,v)result`; `s2:(FFI)state`;
                 `init_context`]
            (el 2 (CONJUNCTS evaluate_v_ok))) THEN
  ASM_SIMP_TAC[env_ok_extend_dec_env; env_ok_candle_init_env; env_ok_init_env] THEN
  DISCH_THEN (X_CHOOSE_THEN `ctxt1:update list` (MP_TAC o CONJUNCT2)) THEN
  QCASES_ON "r" THEN CAKE_REWRITE_TAC[] THENL
   [SIMP_TAC[candle_state_ok_def];
    QCASES_ON "a" THEN CAKE_REWRITE_TAC[] THEN SIMP_TAC[candle_state_ok_def]]);;

(* the state of candle_prog_thm with another clock and eval state es *)
let CAN3AUX_state_ok_with = prove
 (`candle_state_ok ctxt (s:(FFI)state) /\ candle_eval_state_ok es ==>
   candle_state_ok ctxt (state_clock_fupd (combin_K c) (state_eval_state_fupd (combin_K es) s))`,
  REWRITE_TAC[candle_state_ok_def; state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

(* every event of a run of candle_code followed by a safe program is ok,   *)
(* for any clock (HOL4 argues this in each case of semantics_thm)            *)
let CAN3AUX_semantics_events = prove
 (`!(ffi:(FFI)ffi_state) es prog k s2 r.
   candle_eval_state_ok es /\ prog_syntax_ok candle_code /\ ALL safe_dec prog /\
   ffi_state_io_events ffi = [] /\
   evaluate_decs (state_clock_fupd (combin_K k)
                    (state_eval_state_fupd (combin_K es) (ml_init_state ffi)))
                 ml_init_env (APPEND candle_code prog) = (s2,r) ==>
   ALL ok_event (ffi_state_io_events (state_ffi s2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[evaluate_decs_append] THEN
  GVS[case_eq "prod"; case_eq "result"] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP CAN3AUX_candle_code_Rval o
                 CONJ (ASSUME `prog_syntax_ok candle_code`)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC (SPECL [`x:(FFI)state`; `prog:dec list`; `s2:(FFI)state`;
                         `y':(v sem_env,v)result`] CAN3AUX_prog_events) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM SUBST1_TAC THEN
    MATCH_MP_TAC CAN3AUX_state_ok_with THEN
    ASM_SIMP_TAC[candle_init_state_state_ok];
    FIRST_ASSUM (MP_TAC o MATCH_MP CAN3AUX_candle_code_Rerr o
                 CONJ (ASSUME `prog_syntax_ok candle_code`) o
                 CONJ (ASSUME `ffi_state_io_events (ffi:(FFI)ffi_state) = []`)) THEN
    SIMP_TAC[ALL]]);;

(* the same for evaluate_prog_with_clock *)
let CAN3AUX_prog_with_clock_events = prove
 (`candle_eval_state_ok es /\ prog_syntax_ok candle_code /\ ALL safe_dec prog /\
   ffi_state_io_events (ffi:(FFI)ffi_state) = [] ==>
   ALL ok_event
     (ffi_state_io_events
        (FST (evaluate_prog_with_clock (state_eval_state_fupd (combin_K es) (ml_init_state ffi))
                ml_init_env k (APPEND candle_code prog))))`,
  STRIP_TAC THEN REWRITE_TAC[evaluate_prog_with_clock_def] THEN
  MP_TAC (ISPEC `evaluate_decs (state_clock_fupd (combin_K k)
                    (state_eval_state_fupd (combin_K es) (ml_init_state (ffi:(FFI)ffi_state))))
                 ml_init_env (APPEND candle_code prog)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_TAC `r:(v sem_env,v)result`)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[FST] THEN
  MATCH_MP_TAC (SPECL [`ffi:(FFI)ffi_state`; `es:(eval_state)option`; `prog:dec list`;
                       `k:num`; `s2:(FFI)state`; `r:(v sem_env,v)result`]
                 CAN3AUX_semantics_events) THEN
  ASM_REWRITE_TAC[]);;

(* an element of the least upper bound of a chain is an element of a member *)
(* of the chain (HOL4 proves it inside semantics_thm)                        *)
let CAN3AUX_lprefix_lub_LNTH = prove
 (`!ls (ub:A llist) n e.
     lprefix_lub ls ub /\ LNTH n ub = SOME e ==> ?l. l IN ls /\ LNTH n l = SOME e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?p:A llist. p IN ls /\ ~(LNTH n p = NONE)` THENL
   [FIRST_X_ASSUM (X_CHOOSE_THEN `p:A llist` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `p:A llist` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(LNTH n (p:A llist) = NONE)` THEN
    MP_TAC (ISPEC `LNTH n (p:A llist)` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    SUBGOAL_THEN `LPREFIX (p:A llist) ub` MP_TAC THENL
     [ASM_MESON_TAC[lprefix_lub_def]; ALL_TAC] THEN
    REWRITE_TAC[LPREFIX_NTH] THEN DISCH_THEN (MP_TAC o SPECL [`n:num`; `a:A`]) THEN
    ASM_MESON_TAC[option_INJ];
    SUBGOAL_THEN `lprefix_chain_nth n (ls:(A llist)->bool) = NONE` MP_TAC THENL
     [MATCH_MP_TAC not_exists_lprefix_chain_nth THEN
      ASM_MESON_TAC[lprefix_lub_is_chain];
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP lprefix_lub_is_chain) THEN
    DISCH_THEN (fun th -> FIRST_ASSUM (MP_TAC o SPEC `n:num` o
                  REWRITE_RULE[MATCH_MP lprefix_lub_nth th])) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[option_DISTINCT]]);;

let semantics_thm = prove
 (candle_prover_semantics_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. ALL ok_event
          (ffi_state_io_events
             (FST (evaluate_prog_with_clock
                     (state_eval_state_fupd (combin_K es) (ml_init_state (ffi:(FFI)ffi_state)))
                     ml_init_env k (APPEND candle_code prog))))`
   ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CAN3AUX_prog_with_clock_events THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[semantics_prog_def] o
                 check (fun th -> try fst (dest_const (fst (strip_comb (concl th)))) =
                                      "semantics_prog" with Failure _ -> false)) THENL
   [(* Terminate *)
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[FST];
    (* Diverge: every event of the least upper bound is an event of a run *)
    DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN
    REWRITE_TAC[every_LNTH] THEN MAP_EVERY X_GEN_TAC [`n:num`; `e:io_event`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (fun lnth -> FIRST_X_ASSUM (fun lub ->
      MP_TAC (MATCH_MP CAN3AUX_lprefix_lub_LNTH (CONJ lub lnth)))) THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN (X_CHOOSE_THEN `l:io_event llist` (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `k:num`) MP_TAC)) THEN
    FIRST_X_ASSUM (SUBST1_TAC o check (is_var o lhs o concl)) THEN
    REWRITE_TAC[LNTH_fromList] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[GSYM ALL_EL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let events_of_def = cake_def
  `(events_of (Terminate _ io_list) = set_of_list io_list) /\
   (events_of (Diverge io_llist) = LSET io_llist) /\
   (events_of Fail = (:io_event))`;;

let events_of_semantics = prove
 (`semantics_prog (ml_init_state ffi) ml_init_env (APPEND candle_code prog) res /\
   prog_syntax_ok candle_code /\
   ALL safe_dec prog /\ ffi_state_io_events (ffi:(FFI)ffi_state) = [] /\ ~(res = Fail) ==>
   !e. e IN events_of res ==> ok_event e`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ml_init_state (ffi:(FFI)ffi_state) =
                state_eval_state_fupd (combin_K NONE) (ml_init_state ffi)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[ml_init_state_def; state_INFO.ri_fupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `candle_eval_state_ok NONE` ASSUME_TAC THENL
   [REWRITE_TAC[candle_eval_state_ok_def]; ALL_TAC] THEN
  MP_TAC (SPECL [`ffi:(FFI)ffi_state`; `NONE:(eval_state)option`; `prog:dec list`;
                 `res:behaviour`] semantics_thm) THEN
  ASM_REWRITE_TAC[] THEN
  QCASES_ON "res" THEN REWRITE_TAC[events_of_def; distinctness "behaviour";
                                    injectivity "behaviour"] THEN
  REWRITE_TAC[every_LNTH; GSYM ALL_MEM; IN_SET_OF_LIST; LSET_def; IN] THEN
  ASM_MESON_TAC[]);;

let events_of_semantics_with_eval_state = prove
 (`semantics_prog (state_eval_state_fupd (combin_K ev) (ml_init_state ffi)) ml_init_env
     (APPEND candle_code prog) res /\ candle_eval_state_ok ev /\
   prog_syntax_ok candle_code /\
   ALL safe_dec prog /\ ffi_state_io_events (ffi:(FFI)ffi_state) = [] /\ ~(res = Fail) ==>
   !e. e IN events_of res ==> ok_event e`,
  STRIP_TAC THEN
  MP_TAC (SPECL [`ffi:(FFI)ffi_state`; `ev:(eval_state)option`; `prog:dec list`;
                 `res:behaviour`] semantics_thm) THEN
  ASM_REWRITE_TAC[] THEN
  QCASES_ON "res" THEN REWRITE_TAC[events_of_def; distinctness "behaviour";
                                    injectivity "behaviour"] THEN
  REWRITE_TAC[every_LNTH; GSYM ALL_MEM; IN_SET_OF_LIST; LSET_def; IN] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Decision D8 (not in HOL4): the hypothesis prog_syntax_ok candle_code of    *)
(* semantics_thm holds, by evaluation, and semantics_thm without it          *)
(* ------------------------------------------------------------------------- *)

(* the cons check of an appended program: candle_code begins with the       *)
(* basis program, whose constructor environment is CAN3AUX_check_cons_basis *)
let CAN3AUX_check_cons_APPEND = prove
 (`!l1 env l2 e1.
     check_cons_dec_list env l1 = SOME e1 ==>
     (IS_SOME (check_cons_dec_list env (APPEND l1 l2)) <=>
      IS_SOME (check_cons_dec_list (nsAppend e1 env) l2))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; check_cons_dec_list_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[nsAppend_nsEmpty];
    MP_TAC (ISPEC `check_cons_dec env h` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC (ISPEC `check_cons_dec_list (nsAppend a env) t` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`nsAppend a env:(mlstring,mlstring,num#stamp)namespace`;
                                   `l2:dec list`; `a':(mlstring,mlstring,num#stamp)namespace`]) THEN
    ASM_REWRITE_TAC[GSYM nsAppend_assoc] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (ISPEC `check_cons_dec_list (nsAppend a env) (APPEND t l2)` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[IS_SOME_DEF]]);;

(* prog_syntax_ok candle_code: the basis part by CAN3AUX_check_cons_basis,  *)
(* the kernel's declarations by evaluation (the theorem that splits the      *)
(* program is local: it would print the kernel's code)                       *)
let prog_syntax_ok_candle_code =
  let ds = dest_list (rhs (concl candle_code_def)) in
  let bs = dest_list (rhs (concl basisProg_basis_def)) in
  let pre,post = chop_list (length bs) ds in
  if not (forall2 (fun a b -> a = b) pre bs)
  then failwith "candle_code does not begin with the basis program" else
  let ks = mk_list (post, `:dec`) in
  let nil_th,cons_th = CONJ_PAIR APPEND in
  let rec append_conv tm =
    (REWR_CONV nil_th ORELSEC (REWR_CONV cons_th THENC RAND_CONV append_conv)) tm in
  let split =
    let th = AP_THM (AP_TERM `APPEND:dec list->dec list->dec list` basisProg_basis_def) ks in
    TRANS candle_code_def (SYM (TRANS th (append_conv (rand (concl th))))) in
  let app = SPEC ks (MATCH_MP (SPEC `basisProg_basis` CAN3AUX_check_cons_APPEND)
                              CAN3AUX_check_cons_basis) in
  let ev = Compute.CBV_CONV can3aux_cons_cs (rand (concl app)) in
  let th1 = REWR_CONV prog_syntax_ok_def `prog_syntax_ok candle_code` in
  let th2 = AP_TERM `IS_SOME:((mlstring,mlstring,num#stamp)namespace)option->bool`
              (AP_TERM `check_cons_dec_list (sem_env_c ml_init_env)` split) in
  EQT_ELIM (TRANS th1 (TRANS th2 (TRANS app ev)));;

let semantics_thm_strong = prove
 (candle_prover_semantics_strong_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (SPEC_ALL semantics_thm) THEN
  ASM_REWRITE_TAC[prog_syntax_ok_candle_code]);;

(* ------------------------------------------------------------------------- *)
(* The headline checks: semantics_thm and semantics_thm_strong are the       *)
(* statements of candle_prover_statement.ml                                  *)
(* ------------------------------------------------------------------------- *)

let () =
  if hyp semantics_thm = [] &&
     aconv (concl semantics_thm) candle_prover_semantics_statement
  then () else failwith "semantics_thm is not the headline statement";;

let () =
  if hyp semantics_thm_strong = [] &&
     aconv (concl semantics_thm_strong) candle_prover_semantics_strong_statement
  then () else failwith "semantics_thm_strong is not the statement of D8";;
