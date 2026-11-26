(* ========================================================================= *)
(* candle_kernel_vals: port of HOL4 candle/prover/candle_kernel_valsScript.sml *)
(* (CakeML v3479).  Theorems about values from the Candle kernel program.    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Decision D5 (user, 2026-11-24): the bodies of about 31 kernel and       *)
(*   compute closures differ from HOL4's code (nested one-level Mats instead *)
(*   of one Mat with nested patterns); their prefixes (closure, tuple and    *)
(*   Sequent Mats, runtime checks) are HOL4's.  The lemmas here look at the  *)
(*   prefixes only and keep HOL4's statements.  The 59 NAME_v_head lemmas    *)
(*   are proved by CAN2AAUX_HEAD_TAC, HOL4's prove_head_tac: the closure     *)
(*   is unfolded and its checks are consumed by the evaluate_X_check         *)
(*   lemmas, whose lookups are computed by conversion.                       *)
(* - HOL4's Overloads type_stamp_n, term_stamp_n and thm_stamp_n are the     *)
(*   type stamps of TYPE_TYPE_def, TERM_TYPE_def and THM_TYPE_def (21, 22,   *)
(*   23 here; OCaml terms type_stamp_n_tm, ...); the statements are written  *)
(*   with variables of these names, replaced by can2aaux_stamps.  HOL4's     *)
(*   local Overloads type_ctors_set, term_ctors_set and thm_ctors_set are    *)
(*   written out and checked against the invariants.                         *)
(* - HOL4's ^safe_error_goal is written out in each statement; HOL4's s with *)
(*   clock := k is state_clock_fupd (K k) s, () is one, INT is ml_INT, TYPE, *)
(*   TERM and THM are holKernelProof_TYPE, _TERM and _THM, inferred is       *)
(*   candle_inferred; abs_v is the interface entry for abs_1_v.              *)
(* - HOL4 proves the five check_X_head lemmas by complete induction on       *)
(*   v_size v each; here CAN2AAUX_LIST_CHECK_GEN does the induction once,    *)
(*   for any list check function, and each lemma gives its element check.    *)
(* - HOL4's EVAL_TAC on closures is rewriting with the closure definitions   *)
(*   and the distinctness of the value constructors.                         *)
(* ========================================================================= *)

needs "translator/ml_translator.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "semantics/evaluate.ml";;
needs "candle/prover/perms.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local helpers (not HOL4 theorems): CAN2AAUX_ theorems, can2aaux_ OCaml     *)
(* values.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* a theorem made by the translator or by ml_progLib, by its HOL4 name *)
let can2aaux_fetch n = try tr_fetch n with Failure _ -> ml_prog_fetch n;;

(* HOL4's Overloads type_stamp_n, term_stamp_n and thm_stamp_n are the type *)
(* stamp numerals of the kernel's types in TYPE_TYPE_def, TERM_TYPE_def and *)
(* THM_TYPE_def; the statements below are written with variables of these   *)
(* names, which can2aaux_stamps replaces by the numerals (HOL4 expands the  *)
(* Overloads when parsing)                                                   *)
let can2aaux_is_typestamp t =
  is_comb t && is_comb (rator t) && is_const (rator (rator t)) &&
  fst (dest_const (rator (rator t))) = "TypeStamp";;

let can2aaux_typestamp_num th = rand (find_term can2aaux_is_typestamp (concl th));;

let type_stamp_n_tm = can2aaux_typestamp_num TYPE_TYPE_def;;
let term_stamp_n_tm = can2aaux_typestamp_num TERM_TYPE_def;;
let thm_stamp_n_tm = can2aaux_typestamp_num THM_TYPE_def;;

let can2aaux_stamps tm =
  subst [type_stamp_n_tm,`type_stamp_n:num`; term_stamp_n_tm,`term_stamp_n:num`;
         thm_stamp_n_tm,`thm_stamp_n:num`] tm;;

(* the constructor names of a type invariant (HOL4 get_constructors) *)
let can2aaux_constructors th =
  setify (map (rand o rator) (find_terms can2aaux_is_typestamp (concl th)));;

(* ------------------------------------------------------------------------- *)
(* 'inferred' relation                                                       *)
(* ------------------------------------------------------------------------- *)

(* this list attempts to match the functions given in:                       *)
(* https://github.com/jrh13/hol-light/blob/master/fusion.ml                   *)
(* (HOL4's abs_v is its Overload of abs_1_v, an interface entry here)        *)
let kernel_funs_def = cake_def
  `kernel_funs =
     {types_v,
      get_type_arity_v,
      call_new_type_v,
      mk_type_v,
      mk_vartype_v,
      dest_type_v,
      dest_vartype_v,
      is_type_v,
      is_vartype_v,
      call_tyvars_v,
      call_type_subst_v,

      constants_v,
      get_const_type_v,
      new_constant_v,
      call_type_of_v,
      is_var_v,
      is_const_v,
      is_abs_v,
      is_comb_v,
      mk_var_v,
      mk_const_v,
      mk_abs_v,
      mk_comb_v,
      dest_var_v,
      dest_const_v,
      dest_comb_v,
      dest_abs_v,
      call_frees_v,
      freesl_v,
      call_freesin_v,
      call_vfree_in_v,
      call_type_vars_in_term_v,
      call_variant_v,
      vsubst_v,
      inst_v,
      rand_v,
      rator_v,
      dest_eq_v,

      dest_thm_v,
      hyp_v,
      concl_v,
      refl_v,
      trans_v,
      mk_comb_1_v,
      abs_v,
      beta_v,
      assume_v,
      eq_mp_v,
      deduct_antisym_rule_v,
      inst_type_v,
      inst_1_v,
      axioms_v,
      new_axiom_v,
      new_basic_definition_v,
      new_basic_type_definition_v,
      new_specification_v,

      Kernel_print_thm_v,

      compute_add_v,
      compute_v}`;;

(* HOL4: the definitions of the closures of kernel_funs (found by name), *)
(* with constants_v_def and abs_v_def first                                *)
let kernel_funs_v_def =
  let cs = filter (fun t -> is_const t && not (mem (fst (dest_const t)) ["INSERT"; "EMPTY"]))
             (striplist (fun t -> let f,x = dest_comb t in rand f, x)
                (rhs (concl kernel_funs_def))) in
  let def c = let n = fst (dest_const c) in
              if n = "Kernel_print_thm_v" then candle_Kernel_print_thm_v_def
              else can2aaux_fetch (n ^ "_def") in
  end_itlist CONJ (constants_v_def :: ml_hol_kernel_funsProg_abs_v_def :: map def cs);;

(* HOL4: abs_v_def[compute] = abs_v_def *)
let candle_abs_v_def = ml_hol_kernel_funsProg_abs_v_def;;

let kernel_locs_def = cake_def
  `kernel_locs =
     {l | Loc T l IN {the_type_constants,
                      the_term_constants,
                      the_axioms,
                      the_context}}`;;

let IN_kernel_locs = prove
 (`n IN kernel_locs <=>
   Loc T n = the_type_constants \/
   Loc T n = the_term_constants \/
   Loc T n = the_axioms \/
   Loc T n = the_context`,
  REWRITE_TAC[kernel_locs_def; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY]);;

(* HOL4 context_refs_defs: the definitions NAME_refs_def of the constants    *)
(* NAME_refs under LENGTH in the_context_def, as the translator stores them *)
let can2aaux_refs_def c = can2aaux_fetch (fst (dest_const c) ^ "_def");;

let can2aaux_context_refs_defs =
  map (can2aaux_refs_def o rand)
    (find_terms (fun t -> is_comb t && is_const (rator t) &&
                          fst (dest_const (rator t)) = "LENGTH")
       (concl the_context_def));;

let refs_defs = end_itlist CONJ (cv_t_refs_def :: cv_f_refs_def :: can2aaux_context_refs_defs);;

let kernel_locs =
  CONV_RULE NUM_REDUCE_CONV
    (REWRITE_RULE [the_type_constants_def; the_term_constants_def; the_axioms_def;
                   the_context_def; refs_defs; LENGTH; injectivity "v"]
       IN_kernel_locs);;

let kernel_perms_def = cake_def
  `kernel_perms = IMAGE RefMention kernel_locs UNION {RefUpdate}`;;

(* HOL4's local Overloads type_ctors_set, term_ctors_set and thm_ctors_set: *)
(* the constructor names in TYPE_TYPE_def, TERM_TYPE_def and THM_TYPE_def   *)
(* (get_constructors); written out here and checked against the invariants *)
let can2aaux_type_ctors_set = `{implode "Tyvar", implode "Tyapp"}`;;
let can2aaux_term_ctors_set =
  `{implode "Var", implode "Const", implode "Comb", implode "Abs"}`;;
let can2aaux_thm_ctors_set = `{implode "Sequent"}`;;

let () =
  let same th s = set_eq (can2aaux_constructors th)
                    (striplist (fun t -> let f,x = dest_comb t in rand f, x) s
                     |> filter (fun t -> not (is_const t && fst (dest_const t) = "EMPTY"))) in
  if same TYPE_TYPE_def can2aaux_type_ctors_set &&
     same TERM_TYPE_def can2aaux_term_ctors_set &&
     same THM_TYPE_def can2aaux_thm_ctors_set then ()
  else failwith "candle_kernel_vals: constructor sets differ from the type invariants";;

let kernel_ctors_def = cake_def
  `kernel_ctors =
     ({implode "Tyvar", implode "Tyapp"} UNION
      {implode "Var", implode "Const", implode "Comb", implode "Abs"}) UNION
     {implode "Sequent"}`;;

let kernel_types_def = cake_def (can2aaux_stamps
  `kernel_types = {type_stamp_n, term_stamp_n, thm_stamp_n}:num->bool`);;

let candle_inferred_rules,candle_inferred_ind,candle_inferred_cases,
    candle_inferred_strongind = cake_inductive
  `(!ctxt f.
      f IN kernel_funs ==>
        candle_inferred (ctxt:update list) f) /\
   (!ctxt ty v.
      holKernelProof_TYPE ctxt ty /\
      TYPE_TYPE ty v ==>
        candle_inferred ctxt v) /\
   (!ctxt tm v.
      holKernelProof_TERM ctxt tm /\
      TERM_TYPE tm v ==>
        candle_inferred ctxt v) /\
   (!ctxt th v.
      holKernelProof_THM ctxt th /\
      THM_TYPE th v ==>
        candle_inferred ctxt v)`;;

let candle_inferred_KernelFuns = el 0 (CONJUNCTS candle_inferred_rules);;
let candle_inferred_TYPE = el 1 (CONJUNCTS candle_inferred_rules);;
let candle_inferred_TERM = el 2 (CONJUNCTS candle_inferred_rules);;
let candle_inferred_THM = el 3 (CONJUNCTS candle_inferred_rules);;

let kernel_ffi_def = cake_def
  `kernel_ffi = implode "kernel_ffi"`;;

let thm2bytes_def = cake_def
  `thm2bytes ctxt th =
     MAP (word:num->byte) (MAP ORD (explode (thm_to_string ctxt th)))`;;

(* the bytes written on the kernel channel can be read back: the context the *)
(* theorem was proved in is recoverable from the event alone                 *)

let bytes2str_def = cake_def
  `bytes2str (out:byte list) = implode (MAP (CHR o val) out)`;;

let bytes2str_thm2bytes = prove
 (`bytes2str (thm2bytes ctxt th) = thm_to_string ctxt th`,
  REWRITE_TAC[bytes2str_def; thm2bytes_def; MAP_MAP_o; o_DEF] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; ARITH_RULE `2 EXP 8 = 256`] THEN
  SIMP_TAC[MOD_LT; ORD_BOUND; CHR_ORD; MAP_ID; implode_explode]);;

let ok_event_def = cake_def
  `ok_event (IO_event n out y) <=>
     (n = ExtCall kernel_ffi ==>
      ?ctxt th. holKernelProof_THM ctxt th /\
                thm2bytes ctxt th = out /\
                ctxt extends init_ctxt)`;;

(* ------------------------------------------------------------------------- *)
(* Versions of TERM, THM that only match the outermost structure             *)
(* ------------------------------------------------------------------------- *)

let TYPE_TYPE_HEAD_def = cake_def (can2aaux_stamps
  `TYPE_TYPE_HEAD v <=>
     ?s vs. v = Conv (SOME (TypeStamp s type_stamp_n)) vs /\
            s IN {implode "Tyvar", implode "Tyapp"}`);;

let TERM_TYPE_HEAD_def = cake_def (can2aaux_stamps
  `TERM_TYPE_HEAD v <=>
     ?s vs. v = Conv (SOME (TypeStamp s term_stamp_n)) vs /\
            s IN {implode "Var", implode "Const", implode "Comb", implode "Abs"}`);;

(* HOL4 defines THM_TYPE_HEAD with s IN thm_ctors_set and rebinds          *)
(* THM_TYPE_HEAD_def to SIMP_RULE list_ss [] of it; here the first one is   *)
(* CAN2AAUX_THM_TYPE_HEAD_def0 and THM_TYPE_HEAD_def has the membership in   *)
(* the one-element set simplified                                            *)
let CAN2AAUX_THM_TYPE_HEAD_def0 = cake_def (can2aaux_stamps
  `THM_TYPE_HEAD v <=>
     ?s vs. v = Conv (SOME (TypeStamp s thm_stamp_n)) vs /\
            s IN {implode "Sequent"}`);;

let THM_TYPE_HEAD_def = prove
 (can2aaux_stamps
  `!v. THM_TYPE_HEAD v <=>
       ?vs. v = Conv (SOME (TypeStamp (implode "Sequent") thm_stamp_n)) vs`,
  REWRITE_TAC[CAN2AAUX_THM_TYPE_HEAD_def0; IN_SING] THEN MESON_TAC[]);;

let LIST_TYPE_HEAD_def = cake_def
  `LIST_TYPE_HEAD h v <=> ?l:1 list. LIST_TYPE (combin_K h) l v`;;

let PAIR_TYPE_HEAD_def = cake_def
  `PAIR_TYPE_HEAD h1 h2 v <=> PAIR_TYPE (combin_K h1) (combin_K h2) (one,one) v`;;

let STRING_TYPE_HEAD_def = cake_def
  `STRING_TYPE_HEAD v <=> ?s. STRING_TYPE s v`;;

let INT_HEAD_def = cake_def
  `INT_HEAD v <=> ?n. ml_INT n v`;;

(* ------------------------------------------------------------------------- *)
(* THM, TERM, TYPE lemmas                                                    *)
(* ------------------------------------------------------------------------- *)

(* no closure of kernel_funs is a constructor value (HOL4's EVAL_TAC) *)
let CAN2AAUX_Conv_NOT_IN_kernel_funs = prove
 (`!opt vs. ~(Conv opt vs IN kernel_funs)`,
  REWRITE_TAC[kernel_funs_def; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[kernel_funs_v_def; distinctness "v"]);;

let kernel_funs_inferred = prove
 (`(!ty. v IN kernel_funs ==> ~TYPE_TYPE ty v) /\
   (!tm. v IN kernel_funs ==> ~TERM_TYPE tm v) /\
   (!th. v IN kernel_funs ==> ~THM_TYPE th v)`,
  REPEAT CONJ_TAC THEN GEN_TAC THENL
   [CASES_ON `ty:hol_type`; CASES_ON `tm:hol_term`; CASES_ON `th:thm`] THEN
  REWRITE_TAC[TYPE_TYPE_def; TERM_TYPE_def; THM_TYPE_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_MESON_TAC[CAN2AAUX_Conv_NOT_IN_kernel_funs]);;
let _ = cake_add_simps [kernel_funs_inferred];;

let TYPE_from_TYPE_TYPE = prove
 (`candle_inferred ctxt v /\ TYPE_TYPE ty v ==> holKernelProof_TYPE ctxt ty`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[kernel_funs_inferred];
    MP_TAC EqualityType_TYPE_TYPE THEN REWRITE_TAC[EqualityType_def] THEN
    ASM_MESON_TAC[];
    CASES_ON `tm:hol_term` THEN CASES_ON `ty:hol_type` THEN
    GVS[TERM_TYPE_def; TYPE_TYPE_def];
    CASES_ON `th:thm` THEN CASES_ON `ty:hol_type` THEN
    GVS[THM_TYPE_def; TYPE_TYPE_def]]);;

let TERM_from_TERM_TYPE = prove
 (`candle_inferred ctxt v /\ TERM_TYPE tm v ==> holKernelProof_TERM ctxt tm`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[kernel_funs_inferred];
    CASES_ON `ty:hol_type` THEN CASES_ON `tm:hol_term` THEN
    GVS[TYPE_TYPE_def; TERM_TYPE_def];
    MP_TAC EqualityType_TERM_TYPE THEN REWRITE_TAC[EqualityType_def] THEN
    ASM_MESON_TAC[];
    CASES_ON `th:thm` THEN CASES_ON `tm:hol_term` THEN
    GVS[THM_TYPE_def; TERM_TYPE_def]]);;

let THM_from_THM_TYPE = prove
 (`candle_inferred ctxt v /\ THM_TYPE th v ==> holKernelProof_THM ctxt th`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[kernel_funs_inferred];
    CASES_ON `ty:hol_type` THEN CASES_ON `th:thm` THEN
    GVS[TYPE_TYPE_def; THM_TYPE_def];
    CASES_ON `tm:hol_term` THEN CASES_ON `th:thm` THEN
    GVS[TERM_TYPE_def; THM_TYPE_def];
    MP_TAC EqualityType_THM_TYPE THEN REWRITE_TAC[EqualityType_def] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Theorems applying kernel functions to any arguments (incl. wrong type)    *)
(* ------------------------------------------------------------------------- *)

(* HOL4's safe_error_goal, antiquoted into the statements below as          *)
(* ^safe_error_goal, is written out:                                         *)
(*   ?k. s' = state_clock_fupd (K k) s /\ (res = Rerr (Rabort Rtype_error)    *)
(*       \/ res = Rerr (Rraise bind_exn_v) \/ res = Rerr (Rabort              *)
(*       Rtimeout_error))                                                    *)
(* (HOL4's s with clock := k is state_clock_fupd (K k) s)                    *)

let do_opapp_clos = prove
 (`do_opapp [Closure env v e; argv] = SOME (env1,e1) <=>
   sem_env_v_fupd (combin_K (nsBind v argv (sem_env_v env))) env = env1 /\ e = e1`,
  SIMP[do_opapp_def; option_INJ; PAIR_EQ]);;

let do_partial_app_clos = prove
 (`do_partial_app (Closure env v (Fun n e)) argv = SOME g <=>
   Closure (sem_env_v_fupd (combin_K (nsBind v argv (sem_env_v env))) env) n e = g`,
  SIMP[do_partial_app_def; option_INJ]);;

(* the clock updates of states (as semanticsProps' clock_lemmas, which this   *)
(* file does not load)                                                       *)
let CAN2AAUX_clock_lemmas = prove
 (`state_clock (state_clock_fupd (combin_K c) (x:(FFI)state)) = c /\
   state_clock_fupd (combin_K d) (state_clock_fupd (combin_K c) x) = state_clock_fupd (combin_K d) x /\
   state_clock_fupd (combin_K (state_clock x)) x = x`,
  REWRITE_TAC[(record_info "state").ri_accfupds; (record_info "state").ri_fupdfupds; K_THM;
              with_same_clock] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

(* HOL4 [local] *)
let same_clock_exists = prove
 (`((?k. s = state_clock_fupd (combin_K k) (s:(FFI)state)) <=> T) /\
   ((?k. state_clock_fupd (combin_K k') s = state_clock_fupd (combin_K k) s) <=> T)`,
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `state_clock (s:(FFI)state)` THEN REWRITE_TAC[CAN2AAUX_clock_lemmas];
    EXISTS_TAC `k':num` THEN REWRITE_TAC[]]);;

let CAN2AAUX_LENGTH_SYM = prove
 (`!l:v list. (1 = LENGTH l <=> LENGTH l = 1) /\ (2 = LENGTH l <=> LENGTH l = 2)`,
  MESON_TAC[]);;

(* the evaluation of a Mat on the value w of a variable, w split into its    *)
(* constructor cases; head_def proves the HEAD conclusion                    *)
let CAN2AAUX_MAT_CHECK_TAC head_defs =
  STRIP_TAC THEN QPAT_X_ASSUM "evaluate _ _ _ = _" MP_TAC THEN
  SIMP[evaluate_def; same_ctor_def; pmatch_def; do_con_check_def; nsOptBind_def;
       build_conv_def] THEN
  RW(same_clock_exists :: all_case_eqs()) THEN
  CASES_ON `w:v` THEN GVS[pmatch_def] THEN
  RENAME1 "Conv oo ll" THEN CASES_ON `oo:stamp option` THEN
  GVS(CAN2AAUX_LENGTH_SYM :: LENGTH_EQ_NUM_compute :: pmatch_def :: all_case_eqs()) THEN
  GVS([same_ctor_def; IN_INSERT; NOT_IN_EMPTY] @ head_defs);;

let evaluate_unit_check = prove
 (`evaluate s (sem_env_v_fupd (combin_K (nsBind v w env1)) env)
      [Mat (Var (Short v)) [(Pcon NONE [],ee)]] = (s',res) ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/ UNIT_TYPE one w`,
  SIMP[evaluate_def; same_ctor_def; pmatch_def; do_con_check_def] THEN
  RW(same_clock_exists :: all_case_eqs()) THEN
  CASES_ON `w:v` THEN GVS[pmatch_def] THEN
  RENAME1 "Conv oo ll" THEN CASES_ON `oo:stamp option` THEN
  GVS(UNIT_TYPE_def :: pmatch_def :: all_case_eqs()));;

let evaluate_str_check = prove
 (`evaluate s env [Let NONE (App Strlen [Var (Short v)]) ee] = (s',res) /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/ STRING_TYPE_HEAD w /\ evaluate s env [ee] = (s',res)`,
  STRIP_TAC THEN QPAT_X_ASSUM "evaluate _ _ _ = _" MP_TAC THEN
  SIMP[evaluate_def; nsOptBind_def] THEN SIMP[do_app_def] THEN
  CASES_ON `w:v` THEN SIMP[] THEN TRY (RENAME1 "Litv ll" THEN CASES_ON `ll:lit`) THEN
  SIMP[RECORD_SELFID_ss; list_result_def] THEN RW(same_clock_exists :: all_case_eqs()) THEN
  GVS[STRING_TYPE_HEAD_def; STRING_TYPE_def]);;

let evaluate_ty_check = prove
 (can2aaux_stamps
  `evaluate s env
      [Let NONE
         (Mat (Var (Short v))
            [(Pcon (SOME (Short (implode "Tyvar"))) [Pvar a1], Con NONE []);
             (Pcon (SOME (Short (implode "Tyapp"))) [Pvar a3; Pvar a4], Con NONE [])])
         ee] = (s',res) /\
    nsLookup (sem_env_c env) (Short (implode "Tyvar")) =
      SOME (1,TypeStamp (implode "Tyvar") type_stamp_n) /\
    nsLookup (sem_env_c env) (Short (implode "Tyapp")) =
      SOME (2,TypeStamp (implode "Tyapp") type_stamp_n) /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/ TYPE_TYPE_HEAD w /\ evaluate s env [ee] = (s',res)`,
  CAN2AAUX_MAT_CHECK_TAC [TYPE_TYPE_HEAD_def]);;

let evaluate_tm_check = prove
 (can2aaux_stamps
  `evaluate s env
      [Let NONE
         (Mat (Var (Short v))
            [(Pcon (SOME (Short (implode "Var")))   [Pvar a1; Pvar a2], Con NONE []);
             (Pcon (SOME (Short (implode "Const"))) [Pvar a3; Pvar a4], Con NONE []);
             (Pcon (SOME (Short (implode "Comb")))  [Pvar a5; Pvar a6], Con NONE []);
             (Pcon (SOME (Short (implode "Abs")))   [Pvar a7; Pvar a8], Con NONE [])])
         ee] = (s',res) /\
    nsLookup (sem_env_c env) (Short (implode "Var")) =
      SOME (2,TypeStamp (implode "Var") term_stamp_n) /\
    nsLookup (sem_env_c env) (Short (implode "Const")) =
      SOME (2,TypeStamp (implode "Const") term_stamp_n) /\
    nsLookup (sem_env_c env) (Short (implode "Comb")) =
      SOME (2,TypeStamp (implode "Comb") term_stamp_n) /\
    nsLookup (sem_env_c env) (Short (implode "Abs")) =
      SOME (2,TypeStamp (implode "Abs") term_stamp_n) /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/ TERM_TYPE_HEAD w /\ evaluate s env [ee] = (s',res)`,
  CAN2AAUX_MAT_CHECK_TAC [TERM_TYPE_HEAD_def]);;

let evaluate_thm_check = prove
 (can2aaux_stamps
  `evaluate s env
      [Let NONE
         (Mat (Var (Short v))
            [(Pcon (SOME (Short (implode "Sequent"))) [Pvar a1; Pvar a2], Con NONE [])])
         ee] = (s',res) /\
    nsLookup (sem_env_c env) (Short (implode "Sequent")) =
      SOME (2,TypeStamp (implode "Sequent") thm_stamp_n) /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/ THM_TYPE_HEAD w /\ evaluate s env [ee] = (s',res)`,
  CAN2AAUX_MAT_CHECK_TAC [THM_TYPE_HEAD_def]);;

let evaluate_mat_pair = prove
 (`evaluate s env
      [Mat (Var (Short v)) [(Pcon NONE [Pvar a1; Pvar a2], ee)]] = (s',res) /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/
    ?v1 v2.
      w = Conv NONE [v1; v2] /\
      evaluate s (sem_env_v_fupd (combin_K (nsBind a2 v2 (nsBind a1 v1 (sem_env_v env)))) env)
        [ee] = (s',res)`,
  CAN2AAUX_MAT_CHECK_TAC []);;

let evaluate_mat_thm = prove
 (can2aaux_stamps
  `evaluate s env
      [Mat (Var (Short v))
         [(Pcon (SOME (Short (implode "Sequent"))) [Pvar a1; Pvar a2], ee)]] = (s',res) /\
    nsLookup (sem_env_c env) (Short (implode "Sequent")) =
      SOME (2,TypeStamp (implode "Sequent") thm_stamp_n) /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/
    ?v1 v2.
      THM_TYPE_HEAD w /\
      evaluate s (sem_env_v_fupd (combin_K (nsBind a2 v2 (nsBind a1 v1 (sem_env_v env)))) env)
        [ee] = (s',res)`,
  CAN2AAUX_MAT_CHECK_TAC [THM_TYPE_HEAD_def] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The runtime checks of lists: check_ty, check_tm, check_thm, check_tm_tm,  *)
(* check_ty_ty.  HOL4 proves each by complete induction on v_size v and      *)
(* stepwise evaluation; here the induction is done once, in                  *)
(* CAN2AAUX_LIST_CHECK_GEN, for any one-function recursive closure that      *)
(* matches a list with [] and :: and checks the head before the recursive    *)
(* call on the tail; each check function only supplies its element check.   *)
(* ------------------------------------------------------------------------- *)

(* lookups in the environments of the kernel closures: record accessors,    *)
(* nsBind chains with mlstring keys, then ml_progLib's tables                *)
let can2aaux_lookup_conv =
  REWRITE_CONV [(record_info "sem_env").ri_accfupds; K_THM; nsLookup_nsBind_compute] THENC
  DEPTH_CONV ML_PROG_MLSTRING_EQ_CONV THENC REWRITE_CONV [] THENC
  TRY_CONV (DEPTH_CONV nsLookup_conv) THENC REWRITE_CONV [];;

let can2aaux_is_eval_eq t =
  is_eq t && (let f,args = strip_comb (lhs t) in
              is_const f && fst (dest_const f) = "evaluate" && length args = 3);;

(* apply a check lemma |- A1 /\ .. /\ An ==> C to the evaluate fact ev: A1 by *)
(* matching, each later Ai = (l = r) by evaluating l and matching r with the  *)
(* result (which instantiates the value variables of the lemma)              *)
let can2aaux_apply_check lemma ev =
  let l0 = SPEC_ALL lemma in
  (* the lemma's variables renamed apart from the goal's *)
  let l1 = INST (map (fun v -> genvar (type_of v), v) (frees (concl l0))) l0 in
  let ants = conjuncts (lhand (concl l1)) in
  let i1 = term_match [] (hd ants) (concl ev) in
  let l2 = INSTANTIATE i1 l1 in
  let rec discharge th acc = function
      [] -> MP th (end_itlist CONJ (rev acc))
    | a :: rest ->
        let eq = can2aaux_lookup_conv (lhs a) in
        let i = term_match [] (rhs a) (rhs (concl eq)) in
        let th' = INSTANTIATE i th in
        let a' = instantiate i a in
        let ath = EQ_MP (ALPHA (concl eq) a') eq in
        discharge th' (ath :: acc) (map (instantiate i) rest) in
  discharge l2 [ev] (tl (conjuncts (lhand (concl l2))));;

(* the conclusion SAFE \/ X of a check lemma: the SAFE case proves the       *)
(* goal's first disjunct; otherwise X is stripped and the next check is      *)
(* applied to the remaining evaluation, until no check applies               *)
let CAN2AAUX_SAFE_TAC th =
  DISJ1_TAC THEN MP_TAC th THEN REWRITE_TAC[CAN2AAUX_clock_lemmas] THEN MESON_TAC[];;

let rec CAN2AAUX_CHECK_LOOP_TAC lemmas (finish:tactic) : tactic = fun (asl,w as g) ->
  let evs = filter (fun (_,th) -> can2aaux_is_eval_eq (concl th)) asl in
  match evs with
    [] -> finish g
  | (_,ev)::_ ->
     (match (try Some (tryfind (fun l -> can2aaux_apply_check l ev) lemmas)
             with Failure _ -> None) with
        None -> finish g
      | Some th ->
          (UNDISCH_THEN (concl ev) (K ALL_TAC) THEN
           DISJ_CASES_THEN2 CAN2AAUX_SAFE_TAC
             (fun th' -> CAKE_STRIP_ASSUME_TAC th' THEN
                         CAN2AAUX_CHECK_LOOP_TAC lemmas finish) th) g);;

(* substitute the values split by evaluate_mat_pair *)
let CAN2AAUX_SUBST_CONV_TAC =
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
    let c = concl th in is_eq c && is_var (lhs c) &&
    (try fst (dest_const (fst (strip_comb (rhs c)))) = "Conv" with Failure _ -> false))));;

let CAN2AAUX_HEAD_DEFS = [PAIR_TYPE_HEAD_def; PAIR_TYPE_def; K_THM; injectivity "v"; CONS_11];;

let CAN2AAUX_do_opapp_Recclosure1 = prove
 (`do_opapp [Recclosure ENV [(f,p,b)] f; v] =
   SOME (sem_env_v_fupd (combin_K (nsBind p v (nsBind f (Recclosure ENV [(f,p,b)] f) (sem_env_v ENV))))
           ENV, b)`,
  SIMP[do_opapp_def] THEN ONCE_REWRITE_TAC[find_recfun_def] THEN
  SIMP[build_rec_env_def; ITLIST]);;

let CAN2AAUX_EXISTS_EVAL = prove
 (`!X Y (st:(FFI)state) (P:(FFI)state->(v list,v)result->bool).
     (!s' res. evaluate st X [Y] = (s',res) ==> P s' res) ==>
     ?env e s' res. (X = env /\ Y = e) /\ evaluate st env [e] = (s',res) /\ P s' res`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`X:v sem_env`; `Y:exp`; `FST (evaluate (st:(FFI)state) X [Y])`;
                        `SND (evaluate (st:(FFI)state) X [Y])`] THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[PAIR]);;

(* the application of a variable to a variable *)
let CAN2AAUX_evaluate_Opapp_vars = prove
 (CASE_TERM `evaluate (s:(FFI)state) env [App Opapp [Var (Short f); Var (Short x)]] =
     match nsLookup (sem_env_v env) (Short x) with
       NONE -> (s, Rerr (Rabort Rtype_error))
     | SOME xv ->
        (match nsLookup (sem_env_v env) (Short f) with
           NONE -> (s, Rerr (Rabort Rtype_error))
         | SOME fv ->
            (match do_opapp [fv; xv] with
               NONE -> (s, Rerr (Rabort Rtype_error))
             | SOME (env',e) -> if state_clock s = 0 then (s, Rerr (Rabort Rtimeout_error))
                                else evaluate (dec_clock s) env' [e]))`,
  SIMP[evaluate_def; getOpClass_def] THEN
  QCASES_ON "nsLookup (sem_env_v env) (Short x)" THEN SIMP[] THEN
  QCASES_ON "nsLookup (sem_env_v env) (Short f)" THEN SIMP[REVERSE; APPEND; HD]);;

let CAN2AAUX_v_size_cons2 = prove
 (`v_size y < v_size (Conv c [x; y])`,
  REWRITE_TAC[type_size_def "v"] THEN ARITH_TAC);;

let CAN2AAUX_LIST_TYPE_HEAD_CONS = prove
 (`A h /\ LIST_TYPE_HEAD A t ==>
   LIST_TYPE_HEAD A (Conv (SOME (TypeStamp (implode "::") 1)) [h; t])`,
  REWRITE_TAC[LIST_TYPE_HEAD_def] THEN STRIP_TAC THEN
  EXISTS_TAC `CONS one l` THEN ASM_REWRITE_TAC[LIST_TYPE_def; K_THM] THEN ASM_MESON_TAC[]);;

let CAN2AAUX_LIST_TYPE_HEAD_NIL = prove
 (`LIST_TYPE_HEAD A (Conv (SOME (TypeStamp (implode "[]") 1)) [])`,
  REWRITE_TAC[LIST_TYPE_HEAD_def] THEN EXISTS_TAC `[]:1 list` THEN
  REWRITE_TAC[LIST_TYPE_def]);;

let CAN2AAUX_IGN = [IGNASM "!s env x y s' res. _"];;

let CAN2AAUX_LIST_CHECK_GEN = prove
 (`!ENV fnm pnm hnm tnm CHK (A:v->bool).
     ~(hnm = tnm) /\ ~(fnm = hnm) /\ ~(fnm = tnm) /\ ~(fnm = pnm) /\
     nsLookup (sem_env_c ENV) (Short (implode "[]")) = SOME (0,TypeStamp (implode "[]") 1) /\
     nsLookup (sem_env_c ENV) (Short (implode "::")) = SOME (2,TypeStamp (implode "::") 1) /\
     (!s v x y s' res.
        evaluate s
          (sem_env_v_fupd (combin_K (nsBind tnm y (nsBind hnm x (nsBind pnm v
             (nsBind fnm (Recclosure ENV
                  [(fnm,pnm,Mat (Var (Short pnm))
                     [(Pcon (SOME (Short (implode "[]"))) [], Con NONE []);
                      (Pcon (SOME (Short (implode "::"))) [Pvar hnm; Pvar tnm], CHK)])] fnm)
               (sem_env_v ENV)))))) ENV) [CHK] = (s',res) ==>
        (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
             (res = Rerr (Rabort Rtype_error) \/
              res = Rerr (Rraise bind_exn_v) \/
              res = Rerr (Rabort Rtimeout_error))) \/
        A x /\
        ?k env'. evaluate (state_clock_fupd (combin_K k) s) env'
                   [App Opapp [Var (Short fnm); Var (Short tnm)]] = (s',res) /\
                 nsLookup (sem_env_v env') (Short fnm) =
                   SOME (Recclosure ENV
                     [(fnm,pnm,Mat (Var (Short pnm))
                        [(Pcon (SOME (Short (implode "[]"))) [], Con NONE []);
                         (Pcon (SOME (Short (implode "::"))) [Pvar hnm; Pvar tnm], CHK)])] fnm) /\
                 nsLookup (sem_env_v env') (Short tnm) = SOME y) ==>
     !v s.
       ?env e s' res.
         do_opapp [Recclosure ENV
                     [(fnm,pnm,Mat (Var (Short pnm))
                        [(Pcon (SOME (Short (implode "[]"))) [], Con NONE []);
                         (Pcon (SOME (Short (implode "::"))) [Pvar hnm; Pvar tnm], CHK)])] fnm;
                   v] = SOME (env,e) /\
         evaluate (dec_clock s) env [e] = (s',res) /\
         ((?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
               (res = Rerr (Rabort Rtype_error) \/
                res = Rerr (Rraise bind_exn_v) \/
                res = Rerr (Rabort Rtimeout_error))) \/
          ?k z. s' = state_clock_fupd (combin_K k) s /\ res = Rval [z] /\ LIST_TYPE_HEAD A v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `v_size v` THEN GEN_TAC THEN
  REWRITE_TAC[CAN2AAUX_do_opapp_Recclosure1; option_INJ; PAIR_EQ] THEN
  MATCH_MP_TAC CAN2AAUX_EXISTS_EVAL THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  QPAT_X_ASSUM "evaluate _ _ _ = _" MP_TAC THEN
  SIMP(CAN2AAUX_IGN @ [evaluate_def; pmatch_def; same_ctor_def; nsOptBind_def;
       nsLookup_nsBind_compute; do_con_check_def; build_conv_def]) THEN
  RW(CAN2AAUX_IGN @ same_clock_exists :: dec_clock_def :: all_case_eqs()) THEN
  CASES_ON `v:v` THEN GVS(CAN2AAUX_IGN @ [pmatch_def]) THEN
  RENAME1 "Conv oo ll" THEN CASES_ON `oo:stamp option` THEN
  GVS(CAN2AAUX_IGN @ CAN2AAUX_LENGTH_SYM :: LENGTH_EQ_NUM_compute :: pmatch_def :: same_ctor_def ::
      all_case_eqs()) THENL
   [ALL_TAC;
    MESON_TAC[CAN2AAUX_LIST_TYPE_HEAD_NIL]] THEN
  FIRST_X_ASSUM (fun th -> DRULE th) THEN
  DISCH_THEN (DISJ_CASES_THEN2
    (fun th -> DISJ1_TAC THEN MP_TAC th THEN REWRITE_TAC[CAN2AAUX_clock_lemmas] THEN MESON_TAC[])
    STRIP_ASSUME_TAC) THEN
  QPAT_X_ASSUM "evaluate _ _ [App _ _] = _" MP_TAC THEN
  ASM_REWRITE_TAC[CAN2AAUX_evaluate_Opapp_vars] THEN
  SIMP(CAN2AAUX_IGN @ [CAN2AAUX_do_opapp_Recclosure1; CAN2AAUX_clock_lemmas]) THEN
  COND_CASES_TAC THENL [RW[same_clock_exists]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `h':v` o
    check (fun th -> is_forall (concl th) &&
                     fst (dest_var (fst (dest_forall (concl th)))) = "v'")) THEN
  REWRITE_TAC[CAN2AAUX_v_size_cons2] THEN
  DISCH_THEN (MP_TAC o SPEC `state_clock_fupd (combin_K k) (s:(FFI)state)`) THEN
  REWRITE_TAC[CAN2AAUX_do_opapp_Recclosure1; option_INJ; PAIR_EQ] THEN
  STRIP_TAC THEN GVS(CAN2AAUX_IGN @ [CAN2AAUX_clock_lemmas; same_clock_exists]) THEN
  EXISTS_TAC `k':num` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CAN2AAUX_LIST_TYPE_HEAD_CONS THEN ASM_REWRITE_TAC[]);;

(* the element check of a list check function: A x, then the recursive call *)
let CAN2AAUX_ELEM_FINISH_TAC : tactic = fun (asl,w as g) ->
  let ev = snd (find (fun (_,th) -> can2aaux_is_eval_eq (concl th)) asl) in
  let st, env = match strip_comb (lhs (concl ev)) with
      _,[st; env; _] -> st, env | _ -> failwith "CAN2AAUX_ELEM_FINISH_TAC" in
  (DISJ2_TAC THEN CONJ_TAC THENL
    [CAN2AAUX_SUBST_CONV_TAC THEN SIMP CAN2AAUX_HEAD_DEFS THEN ASM_MESON_TAC[];
     EXISTS_TAC (mk_comb (`state_clock:(FFI)state->num`, st)) THEN EXISTS_TAC env THEN
     REWRITE_TAC[CAN2AAUX_clock_lemmas] THEN ASM_REWRITE_TAC[] THEN CONV_TAC can2aaux_lookup_conv]) g;;

let CAN2AAUX_LIST_CHECK_TAC v_def lemmas =
  REWRITE_TAC[v_def] THEN MATCH_MP_TAC CAN2AAUX_LIST_CHECK_GEN THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC can2aaux_lookup_conv THEN NO_TAC) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CAN2AAUX_CHECK_LOOP_TAC lemmas CAN2AAUX_ELEM_FINISH_TAC;;

let check_tm_head = prove
 (`!v s.
      ?env e s' res.
        do_opapp [check_tm_v; v] = SOME (env,e) /\
        evaluate (dec_clock s) env [e] = (s',res) /\
        ((?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
              (res = Rerr (Rabort Rtype_error) \/
               res = Rerr (Rraise bind_exn_v) \/
               res = Rerr (Rabort Rtimeout_error))) \/
         ?k z. s' = state_clock_fupd (combin_K k) s /\ res = Rval [z] /\
               LIST_TYPE_HEAD TERM_TYPE_HEAD v)`,
  CAN2AAUX_LIST_CHECK_TAC check_tm_v_def [evaluate_tm_check]);;

let check_ty_head = prove
 (`!v s.
      ?env e s' res.
        do_opapp [check_ty_v; v] = SOME (env,e) /\
        evaluate (dec_clock s) env [e] = (s',res) /\
        ((?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
              (res = Rerr (Rabort Rtype_error) \/
               res = Rerr (Rraise bind_exn_v) \/
               res = Rerr (Rabort Rtimeout_error))) \/
         ?k z. s' = state_clock_fupd (combin_K k) s /\ res = Rval [z] /\
               LIST_TYPE_HEAD TYPE_TYPE_HEAD v)`,
  CAN2AAUX_LIST_CHECK_TAC check_ty_v_def [evaluate_ty_check]);;

let check_thm_head = prove
 (`!v s.
      ?env e s' res.
        do_opapp [check_thm_v; v] = SOME (env,e) /\
        evaluate (dec_clock s) env [e] = (s',res) /\
        ((?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
              (res = Rerr (Rabort Rtype_error) \/
               res = Rerr (Rraise bind_exn_v) \/
               res = Rerr (Rabort Rtimeout_error))) \/
         ?k z. s' = state_clock_fupd (combin_K k) s /\ res = Rval [z] /\
               LIST_TYPE_HEAD THM_TYPE_HEAD v)`,
  CAN2AAUX_LIST_CHECK_TAC check_thm_v_def [evaluate_thm_check]);;

let check_tm_tm_head = prove
 (`!v s.
      ?env e s' res.
        do_opapp [check_tm_tm_v; v] = SOME (env,e) /\
        evaluate (dec_clock s) env [e] = (s',res) /\
        ((?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
              (res = Rerr (Rabort Rtype_error) \/
               res = Rerr (Rraise bind_exn_v) \/
               res = Rerr (Rabort Rtimeout_error))) \/
         ?k z. s' = state_clock_fupd (combin_K k) s /\ res = Rval [z] /\
               LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v)`,
  CAN2AAUX_LIST_CHECK_TAC check_tm_tm_v_def [evaluate_mat_pair; evaluate_tm_check]);;

let check_ty_ty_head = prove
 (`!v s.
      ?env e s' res.
        do_opapp [check_ty_ty_v; v] = SOME (env,e) /\
        evaluate (dec_clock s) env [e] = (s',res) /\
        ((?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
              (res = Rerr (Rabort Rtype_error) \/
               res = Rerr (Rraise bind_exn_v) \/
               res = Rerr (Rabort Rtimeout_error))) \/
         ?k z. s' = state_clock_fupd (combin_K k) s /\ res = Rval [z] /\
               LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v)`,
  CAN2AAUX_LIST_CHECK_TAC check_ty_ty_v_def [evaluate_mat_pair; evaluate_ty_check]);;

(* the call of a list check on the value w of a variable *)
let CAN2AAUX_LIST_EVAL_TAC head_th =
  STRIP_TAC THEN
  MP_TAC (ISPECL [`w:v`; `s:(FFI)state`] head_th) THEN STRIP_TAC THEN
  QPAT_X_ASSUM "evaluate _ _ [Let _ _ _] = _" MP_TAC THEN
  SIMP[evaluate_def; CAN2AAUX_evaluate_Opapp_vars; nsOptBind_def; RECORD_SELFID_ss] THEN
  COND_CASES_TAC THEN SIMP[] THEN RW[same_clock_exists] THEN ASM_MESON_TAC[];;

let evaluate_ty_list_check = prove
 (`evaluate s env
      [Let NONE (App Opapp [Var (Short (implode "check_ty")); Var (Short v)]) ee] = (s',res) /\
    nsLookup (sem_env_v env) (Short (implode "check_ty")) = SOME check_ty_v /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/
    LIST_TYPE_HEAD TYPE_TYPE_HEAD w /\
    ?k. evaluate (state_clock_fupd (combin_K k) s) env [ee] = (s',res)`,
  CAN2AAUX_LIST_EVAL_TAC check_ty_head);;

let evaluate_thm_list_check = prove
 (`evaluate s env
      [Let NONE (App Opapp [Var (Short (implode "check_thm")); Var (Short v)]) ee] = (s',res) /\
    nsLookup (sem_env_v env) (Short (implode "check_thm")) = SOME check_thm_v /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/
    LIST_TYPE_HEAD THM_TYPE_HEAD w /\
    ?k. evaluate (state_clock_fupd (combin_K k) s) env [ee] = (s',res)`,
  CAN2AAUX_LIST_EVAL_TAC check_thm_head);;

let evaluate_ty_ty_list_check = prove
 (`evaluate s env
      [Let NONE (App Opapp [Var (Short (implode "check_ty_ty")); Var (Short v)]) ee] =
      (s',res) /\
    nsLookup (sem_env_v env) (Short (implode "check_ty_ty")) = SOME check_ty_ty_v /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) w /\
    ?k. evaluate (state_clock_fupd (combin_K k) s) env [ee] = (s',res)`,
  CAN2AAUX_LIST_EVAL_TAC check_ty_ty_head);;

let evaluate_tm_list_check = prove
 (`evaluate s env
      [Let NONE (App Opapp [Var (Short (implode "check_tm")); Var (Short v)]) ee] = (s',res) /\
    nsLookup (sem_env_v env) (Short (implode "check_tm")) = SOME check_tm_v /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/
    LIST_TYPE_HEAD TERM_TYPE_HEAD w /\
    ?k. evaluate (state_clock_fupd (combin_K k) s) env [ee] = (s',res)`,
  CAN2AAUX_LIST_EVAL_TAC check_tm_head);;

let evaluate_tm_tm_list_check = prove
 (`evaluate s env
      [Let NONE (App Opapp [Var (Short (implode "check_tm_tm")); Var (Short v)]) ee] =
      (s',res) /\
    nsLookup (sem_env_v env) (Short (implode "check_tm_tm")) = SOME check_tm_tm_v /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) w /\
    ?k. evaluate (state_clock_fupd (combin_K k) s) env [ee] = (s',res)`,
  CAN2AAUX_LIST_EVAL_TAC check_tm_tm_head);;

(* ------------------------------------------------------------------------- *)
(* The heads of the kernel functions: HOL4's prove_head_tac.  The closure is  *)
(* unfolded, the checks at the start of its code are consumed one by one by   *)
(* the evaluate_X_check lemmas (their lookups are computed), and the rest of   *)
(* the body is never inspected.  The bodies differ from HOL4's code (D5), the *)
(* prefixes are HOL4's.                                                       *)
(* ------------------------------------------------------------------------- *)

(* the integer argument test of call_new_type (HOL4 evaluates it by          *)
(* simplification in the proof of call_new_type_v_head)                       *)
let CAN2AAUX_evaluate_int_check = prove
 (`evaluate s env
      [If (App (Test (Compare Leq) IntT) [Lit (IntLit i); Var (Short v)]) e1 e2] = (s',res) /\
    nsLookup (sem_env_v env) (Short v) = SOME w ==>
    (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
         (res = Rerr (Rabort Rtype_error) \/
          res = Rerr (Rraise bind_exn_v) \/
          res = Rerr (Rabort Rtimeout_error))) \/ INT_HEAD w`,
  STRIP_TAC THEN QPAT_X_ASSUM "evaluate _ _ _ = _" MP_TAC THEN
  SIMP[evaluate_def; REVERSE; APPEND; HD] THEN SIMP[do_app_def] THEN
  ASM_CASES_TAC `INT_HEAD w` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[INT_HEAD_def; ml_INT_def; NOT_EXISTS_THM]) THEN
  CASES_ON `w:v` THEN SIMP[do_test_def; dest_Litv_def] THEN
  TRY (RENAME1 "Litv ll" THEN CASES_ON `ll:lit` THEN SIMP[do_test_def; dest_Litv_def]) THEN
  RW[same_clock_exists] THEN ASM_MESON_TAC[]);;

let can2aaux_head_lemmas =
  [evaluate_ty_check; evaluate_ty_list_check; evaluate_ty_ty_list_check;
   evaluate_tm_check; evaluate_tm_list_check; evaluate_tm_tm_list_check;
   evaluate_thm_check; evaluate_thm_list_check; evaluate_str_check;
   evaluate_mat_thm; evaluate_mat_pair; evaluate_unit_check; CAN2AAUX_evaluate_int_check];;

(* the closure (HOL4 rewrite_tac [kernel_funs_v_def]), do_partial_app and   *)
(* do_opapp; the evaluate fact of the body is left as an assumption          *)
let CAN2AAUX_HEAD_START_TAC v_def =
  let subst_vars =
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq (concl th) && is_var (rhs (concl th))))) in
  REWRITE_TAC[v_def] THEN REWRITE_TAC[do_partial_app_clos; do_opapp_clos] THEN
  STRIP_TAC THEN subst_vars THEN
  RULE_ASSUM_TAC (REWRITE_RULE[do_opapp_clos]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  subst_vars;;

(* the HEAD conclusion from the HEAD facts of the checks *)
let CAN2AAUX_HEAD_FINISH_TAC =
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (can2aaux_is_eval_eq o concl))) THEN
  DISJ2_TAC THEN CAN2AAUX_SUBST_CONV_TAC THEN SIMP CAN2AAUX_HEAD_DEFS THEN
  ASM_MESON_TAC[STRING_TYPE_HEAD_def];;

let CAN2AAUX_HEAD_TAC v_def =
  CAN2AAUX_HEAD_START_TAC v_def THEN
  CAN2AAUX_CHECK_LOOP_TAC can2aaux_head_lemmas CAN2AAUX_HEAD_FINISH_TAC;;

let types_v_head = prove
 (`do_opapp [types_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      UNIT_TYPE one v`,
  CAN2AAUX_HEAD_TAC types_v_def);;

let constants_v_head = prove
 (`do_opapp [constants_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      UNIT_TYPE one v`,
  CAN2AAUX_HEAD_TAC constants_v_def);;

let axioms_v_head = prove
 (`do_opapp [axioms_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      UNIT_TYPE one v`,
  CAN2AAUX_HEAD_TAC axioms_v_def);;

let mk_vartype_v_head = prove
 (`do_opapp [mk_vartype_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      ?x. STRING_TYPE x v`,
  CAN2AAUX_HEAD_TAC mk_vartype_v_def);;

let call_new_type_v_head = prove
 (`do_opapp [call_new_type_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD STRING_TYPE_HEAD INT_HEAD v`,
  CAN2AAUX_HEAD_TAC call_new_type_v_def);;

let is_type_v_head = prove
 (`do_opapp [is_type_v; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TYPE_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC is_type_v_def);;

let concl_v_head = prove
 (`do_opapp [concl_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC concl_v_def);;

let trans_v_head = prove
 (`do_partial_app trans_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v /\ THM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC trans_v_def);;

let beta_v_head = prove
 (`do_opapp [beta_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC beta_v_def);;

let call_variant_v_head = prove
 (`do_partial_app call_variant_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      LIST_TYPE_HEAD TERM_TYPE_HEAD v /\
      TERM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC call_variant_v_def);;

let vsubst_v_head = prove
 (`do_partial_app vsubst_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v /\
      TERM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC vsubst_v_def);;

let dest_type_v_head = prove
 (`do_opapp [dest_type_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TYPE_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_type_v_def);;

let is_vartype_v_head = prove
 (`do_opapp [is_vartype_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TYPE_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC is_vartype_v_def);;

let is_var_v_head = prove
 (`do_opapp [is_var_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC is_var_v_def);;

let is_const_v_head = prove
 (`do_opapp [is_const_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC is_const_v_def);;

let is_abs_v_head = prove
 (`do_opapp [is_abs_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC is_abs_v_def);;

let is_comb_v_head = prove
 (`do_opapp [is_comb_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC is_comb_v_def);;

let rand_v_head = prove
 (`do_opapp [rand_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC rand_v_def);;

let rator_v_head = prove
 (`do_opapp [rator_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC rator_v_def);;

let dest_var_v_head = prove
 (`do_opapp [dest_var_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_var_v_def);;

let dest_const_v_head = prove
 (`do_opapp [dest_const_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_const_v_def);;

let dest_comb_v_head = prove
 (`do_opapp [dest_comb_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_comb_v_def);;

let dest_abs_v_head = prove
 (`do_opapp [dest_abs_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_abs_v_def);;

let dest_vartype_v_head = prove
 (`do_opapp [dest_vartype_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TYPE_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_vartype_v_def);;

let dest_eq_v_head = prove
 (`do_opapp [dest_eq_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_eq_v_def);;

let call_tyvars_v_head = prove
 (`do_opapp [call_tyvars_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TYPE_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC call_tyvars_v_def);;

let call_type_vars_in_term_v_head = prove
 (`do_opapp [call_type_vars_in_term_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC call_type_vars_in_term_v_def);;

let new_basic_definition_v_head = prove
 (`do_opapp [new_basic_definition_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC new_basic_definition_v_def);;

let new_specification_v_head = prove
 (`do_opapp [new_specification_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC new_specification_v_def);;

let get_const_type_v_head = prove
 (`do_opapp [get_const_type_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      STRING_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC get_const_type_v_def);;

let new_constant_v_head = prove
 (`do_opapp [new_constant_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD STRING_TYPE_HEAD TYPE_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC new_constant_v_def);;

let mk_var_v_head = prove
 (`do_opapp [mk_var_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD STRING_TYPE_HEAD TYPE_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC mk_var_v_def);;

let mk_comb_v_head = prove
 (`do_opapp [mk_comb_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC mk_comb_v_def);;

let get_type_arity_v_head = prove
 (`do_opapp [get_type_arity_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      STRING_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC get_type_arity_v_def);;

let mk_type_v_head = prove
 (`do_opapp [mk_type_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD STRING_TYPE_HEAD (LIST_TYPE_HEAD TYPE_TYPE_HEAD) v`,
  CAN2AAUX_HEAD_TAC mk_type_v_def);;

let refl_v_head = prove
 (`do_opapp [refl_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC refl_v_def);;

let mk_const_v_head = prove
 (`do_opapp [mk_const_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD STRING_TYPE_HEAD
        (LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD)) v`,
  CAN2AAUX_HEAD_TAC mk_const_v_def);;

let freesl_v_head = prove
 (`do_opapp [freesl_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      LIST_TYPE_HEAD TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC freesl_v_def);;

let assume_v_head = prove
 (`do_opapp [assume_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC assume_v_def);;

let hyp_v_head = prove
 (`do_opapp [hyp_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC hyp_v_def);;

let dest_thm_v_head = prove
 (`do_opapp [dest_thm_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC dest_thm_v_def);;

let mk_comb_1_v_head = prove
 (`do_opapp [mk_comb_1_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD THM_TYPE_HEAD THM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC mk_comb_1_v_def);;

let new_basic_type_definition_v_head = prove
 (`do_opapp [new_basic_type_definition_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      (PAIR_TYPE_HEAD STRING_TYPE_HEAD
         (PAIR_TYPE_HEAD STRING_TYPE_HEAD
            (PAIR_TYPE_HEAD STRING_TYPE_HEAD THM_TYPE_HEAD))) v`,
  CAN2AAUX_HEAD_TAC new_basic_type_definition_v_def);;

let call_type_subst_v_head = prove
 (`do_partial_app call_type_subst_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v /\
      TYPE_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC call_type_subst_v_def);;

let inst_v_head = prove
 (`do_partial_app inst_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v /\
      TERM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC inst_v_def);;

let abs_v_head = prove
 (`do_partial_app abs_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD w /\
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC ml_hol_kernel_funsProg_abs_v_def);;

let eq_mp_v_head = prove
 (`do_partial_app eq_mp_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v /\
      THM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC eq_mp_v_def);;

let deduct_antisym_rule_v_head = prove
 (`do_partial_app deduct_antisym_rule_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v /\
      THM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC deduct_antisym_rule_v_def);;

let inst_type_v_head = prove
 (`do_partial_app inst_type_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD w /\
      LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v`,
  CAN2AAUX_HEAD_TAC inst_type_v_def);;

let inst_1_v_head = prove
 (`do_partial_app inst_1_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD w /\
      LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v`,
  CAN2AAUX_HEAD_TAC inst_1_v_def);;

let new_axiom_v_head = prove
 (`do_opapp [new_axiom_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC new_axiom_v_def);;

let call_type_of_v_head = prove
 (`do_opapp [call_type_of_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC call_type_of_v_def);;

let call_vfree_in_v_head = prove
 (`do_partial_app call_vfree_in_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v /\
      TERM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC call_vfree_in_v_def);;

let call_freesin_v_head = prove
 (`do_partial_app call_freesin_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      LIST_TYPE_HEAD TERM_TYPE_HEAD v /\
      TERM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC call_freesin_v_def);;

let mk_abs_v_head = prove
 (`do_opapp [mk_abs_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC mk_abs_v_def);;

let call_frees_v_head = prove
 (`do_opapp [call_frees_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      TERM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC call_frees_v_def);;

let candle_Kernel_print_thm_v_head = prove
 (`do_opapp [Kernel_print_thm_v; v] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      THM_TYPE_HEAD v`,
  CAN2AAUX_HEAD_TAC candle_Kernel_print_thm_v_def);;

let compute_add_v_head = prove
 (`do_partial_app compute_add_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      LIST_TYPE_HEAD THM_TYPE_HEAD v /\
      TERM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC compute_add_v_def);;

let compute_v_head = prove
 (`do_partial_app compute_v v = SOME g /\
    do_opapp [g; w] = SOME (env,exp) /\
    evaluate s env [exp] = (s',res) ==>
      (?k. s' = state_clock_fupd (combin_K k) (s:(FFI)state) /\
           (res = Rerr (Rabort Rtype_error) \/
            res = Rerr (Rraise bind_exn_v) \/
            res = Rerr (Rabort Rtimeout_error))) \/
      PAIR_TYPE_HEAD (LIST_TYPE_HEAD THM_TYPE_HEAD)
                     (LIST_TYPE_HEAD THM_TYPE_HEAD) v /\
      TERM_TYPE_HEAD w`,
  CAN2AAUX_HEAD_TAC compute_v_def);;

(* ------------------------------------------------------------------------- *)
(* Misc. simps                                                               *)
(* ------------------------------------------------------------------------- *)

let Conv_NOT_IN_kernel_funs = prove
 (`~(Conv opt vs IN kernel_funs)`,
  REWRITE_TAC[CAN2AAUX_Conv_NOT_IN_kernel_funs]);;
let _ = cake_add_simps [Conv_NOT_IN_kernel_funs];;

let list_not_TERM_TYPE = prove
 (`~TERM_TYPE tm (Conv (SOME (TypeStamp nm list_type_num)) vs)`,
  CASES_ON `tm:hol_term` THEN RW[TERM_TYPE_def] THEN GVS[list_type_num_def]);;
let _ = cake_add_simps [list_not_TERM_TYPE];;

let list_not_THM_TYPE = prove
 (`~THM_TYPE th (Conv (SOME (TypeStamp nm list_type_num)) vs)`,
  CASES_ON `th:thm` THEN RW[THM_TYPE_def] THEN GVS[list_type_num_def]);;
let _ = cake_add_simps [list_not_THM_TYPE];;

let list_type_NOTIN_kernel_types = prove
 (`~(list_type_num IN kernel_types)`,
  RW[list_type_num_def; kernel_types_def; IN_INSERT; NOT_IN_EMPTY]);;
let _ = cake_add_simps [list_type_NOTIN_kernel_types];;

let bool_type_NOTIN_kernel_types = prove
 (`~(bool_type_num IN kernel_types)`,
  RW[bool_type_num_def; kernel_types_def; IN_INSERT; NOT_IN_EMPTY]);;
let _ = cake_add_simps [bool_type_NOTIN_kernel_types];;

let TYPE_TYPE_Vectorv = prove
 (`~TYPE_TYPE ty (Vectorv vs)`,
  CASES_ON `ty:hol_type` THEN RW[TYPE_TYPE_def]);;
let _ = cake_add_simps [TYPE_TYPE_Vectorv];;

let TERM_TYPE_Vectorv = prove
 (`~TERM_TYPE tm (Vectorv vs)`,
  CASES_ON `tm:hol_term` THEN RW[TERM_TYPE_def]);;
let _ = cake_add_simps [TERM_TYPE_Vectorv];;

let THM_TYPE_Vectorv = prove
 (`~THM_TYPE th (Vectorv vs)`,
  CASES_ON `th:thm` THEN RW[THM_TYPE_def]);;
let _ = cake_add_simps [THM_TYPE_Vectorv];;

(* a value of kernel_funs is a closure: v = NAME_v is decided by unfolding  *)
(* the closure definitions (HOL4 once_rewrite_tac [kernel_funs_v_def])       *)
let CAN2AAUX_KFUNS_TAC =
  REWRITE_TAC[kernel_funs_def; IN_INSERT; NOT_IN_EMPTY] THEN
  ONCE_REWRITE_TAC[kernel_funs_v_def] THEN REWRITE_TAC[distinctness "v"];;

let inferred_Vectorv = prove
 (`~candle_inferred ctxt (Vectorv vs)`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  REWRITE_TAC[TYPE_TYPE_Vectorv; TERM_TYPE_Vectorv; THM_TYPE_Vectorv] THEN
  CAN2AAUX_KFUNS_TAC);;
let _ = cake_add_simps [inferred_Vectorv];;

let inferred_Conv = prove
 (`candle_inferred ctxt (Conv (SOME stamp) vs) ==>
   ?tag m. stamp = TypeStamp tag m /\ m IN kernel_types`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  RW[Conv_NOT_IN_kernel_funs; kernel_types_def; IN_INSERT; NOT_IN_EMPTY] THENL
   [CASES_ON `ty:hol_type` THEN GVS[TYPE_TYPE_def];
    CASES_ON `tm:hol_term` THEN GVS[TERM_TYPE_def];
    CASES_ON `th:thm` THEN GVS[THM_TYPE_def]] THEN
  MESON_TAC[]);;

let inferred_Conv_NONE = prove
 (`~candle_inferred ctxt (Conv NONE vs)`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  RW[Conv_NOT_IN_kernel_funs] THENL
   [CASES_ON `ty:hol_type` THEN GVS[TYPE_TYPE_def];
    CASES_ON `tm:hol_term` THEN GVS[TERM_TYPE_def];
    CASES_ON `th:thm` THEN GVS[THM_TYPE_def]]);;
let _ = cake_add_simps [inferred_Conv_NONE];;

let inferred_Loc = prove
 (`~candle_inferred ctxt (Loc b loc)`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [CAN2AAUX_KFUNS_TAC;
    GEN_TAC THEN CASES_ON `ty:hol_type` THEN RW[TYPE_TYPE_def];
    GEN_TAC THEN CASES_ON `tm:hol_term` THEN RW[TERM_TYPE_def];
    GEN_TAC THEN CASES_ON `th:thm` THEN RW[THM_TYPE_def]]);;
let _ = cake_add_simps [inferred_Loc];;

let inferred_Env = prove
 (`~candle_inferred ctxt1 (Env env id)`,
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [CAN2AAUX_KFUNS_TAC;
    GEN_TAC THEN CASES_ON `ty:hol_type` THEN RW[TYPE_TYPE_def];
    GEN_TAC THEN CASES_ON `tm:hol_term` THEN RW[TERM_TYPE_def];
    GEN_TAC THEN CASES_ON `th:thm` THEN RW[THM_TYPE_def]]);;
let _ = cake_add_simps [inferred_Env];;
