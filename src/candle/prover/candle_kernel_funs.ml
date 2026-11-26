(* ========================================================================= *)
(* candle_kernel_funs: port of HOL4 candle/prover/candle_kernel_funsScript.sml *)
(* (CakeML v3479).  Prove that kernel functions maintain Candle prover's     *)
(* invariants.                                                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Local helpers that are not HOL4 theorems are CKFAUX_ (OCaml values     *)
(*   ckfaux_).                                                               *)
(* - HOL4's Arrow1, Arrow2 and GC_T are candle_Arrow1, candle_Arrow2 and     *)
(*   candle_GC_T (names.tsv); the other theorems keep HOL4's names.          *)
(* - Arrow1 and Arrow2 are proved from the AppReturns of the certificate     *)
(*   and the permission lemmas of perms (HOL4 uses Eval_Arrow in an          *)
(*   environment with the two values written).                              *)
(* - MEM_st2heap is proved from cfStore's lemma on store2heap_aux.           *)
(* - v_ok_APPEND and ref_ok_APPEND keep HOL4's unused quantifiers !x s.,     *)
(*   typed as update list and hol_refs.                                      *)
(* - EqualityType_11: HOL4's bound variable abs is a here (abs is a          *)
(*   constant of HOL Light).                                                 *)
(* - inferred_ok (a 1250-line proof in HOL4) is split into one lemma         *)
(*   CKFAUX_inferred_NAME per kernel function, in HOL4's case order: the    *)
(*   one-argument functions from Arrow1 or ArrowM1 and the head lemmas, the  *)
(*   two-argument closures through their partial applications                *)
(*   (CKFAUX_inferred_partial); kernel_vals_ok likewise has one lemma        *)
(*   CKFAUX_kv_NAME per two-argument function.                               *)
(* - Clash failures, which HOL4 removes with its [simp] not_clash lemmas,    *)
(*   are excluded by holKernelProof's not_clash lemmas and five local ones.  *)
(* - print_thm (D5 code shape): the closure body is evaluated Let by Let,    *)
(*   one lemma per step; the context is read from the kernel's reference at  *)
(*   location 5 through kernel_loc_ok (HOL4: get_the_context_thm and         *)
(*   EvalM); the event of the FFI call is ok by kernel_ffi_def.              *)
(* ========================================================================= *)

needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/ast_extras.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "candle/prover/perms.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "hol4/sptree.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/prover/candle_kernel_perms.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/compute/computeProof.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "characteristic/cfLetAuto.ml";;
needs "hol4/set_sep.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Applying certificates of pure functions (ml_translator's Arrow)          *)
(* ------------------------------------------------------------------------- *)

(* HOL4 Arrow1.  HOL4's proof goes through Eval_Arrow in an environment with *)
(* the two values written; here the AppReturns of the certificate is used   *)
(* directly, and the permission lemma of perms (evaluate_perms_ok_exp with  *)
(* no permissions) gives the unchanged parts of the state.                  *)
let candle_Arrow1 = prove
 (`(A --> B) (f:A->B) fv /\
   do_opapp [fv; av] = SOME (env,exp) /\
   evaluate (s:(FFI)state) env [exp] = (s',res) /\
   A a av /\
   perms_ok {} av /\
   perms_ok {} fv ==>
   state_ffi s = state_ffi s' /\
   (res = Rerr (Rabort Rtimeout_error) \/
    res = Rerr (Rabort Rtype_error) \/
    state_refs s = state_refs s' /\
    state_eval_state s = state_eval_state s' /\
    state_next_type_stamp s = state_next_type_stamp s' /\
    ?rv. res = Rval [rv] /\ B (f a) rv)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `exp:exp`; `s':(FFI)state`;
                 `res:(v list,v)result`; `{}:permission->bool`] evaluate_perms_ok_exp) THEN
  MP_TAC(ISPECL [`{}:permission->bool`; `fv:v`; `av:v`; `env:v sem_env`; `exp:exp`]
    perms_ok_do_opapp) THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; perms_ok_state_def] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A` o REWRITE_RULE[ml_Arrow_def]) THEN
  REWRITE_TAC[ml_AppReturns_def] THEN
  DISCH_THEN(MP_TAC o SPEC `av:v`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `state_refs (s:(FFI)state)`) THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_ALL_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP evaluate_empty_state_IMP) ASSUME_TAC) THEN
  REWRITE_TAC[eval_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] evaluate_set_init_clock)) THEN
  REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(MP_TAC o SPEC `state_clock (s:(FFI)state)`) THEN
  REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[with_same_clock; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rhs o concl))) THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ2_TAC THEN
  UNDISCH_TAC `LENGTH (state_refs (st1:(FFI)state)) = LENGTH (state_refs (s:(FFI)state))` THEN
  ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM;
    LENGTH_APPEND; ARITH_RULE `a + b = a <=> b = 0`; LENGTH_EQ_NIL] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL; injectivity "result"; CONS_11] THEN
  ASM_MESON_TAC[]);;

(* the result of a partial application has the permissions of its parts *)
let CKFAUX_perms_ok_do_partial_app = prove
 (`!ps fv av gv.
     perms_ok ps fv /\ perms_ok ps av /\ do_partial_app fv av = SOME gv ==>
     perms_ok ps gv`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_partial_app_def] THEN
  REPEAT(CASE_TAC THEN REWRITE_TAC[distinctness "option"]) THEN
  REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[perms_ok_def; perms_ok_exp_thm; freevars_def]) THEN
  ASM_REWRITE_TAC[perms_ok_def] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[perms_ok_env_def; IN_DIFF; IN_SING] THEN
  SIMP[] THEN DISCH_TAC THEN RENAME1 "nsBind n0 _ _" THEN
  MAP_EVERY X_GEN_TAC [`x:(mlstring,mlstring)id`; `w:v`] THEN
  ASM_CASES_TAC `(x:(mlstring,mlstring)id) = Short (n0:mlstring)` THEN
  ASM_SIMP_TAC[nsLookup_nsBind; injectivity "option"] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 Arrow2.  The partial application evaluates to the closure gv at once *)
(* (a Fun), so the inner certificate (B --> C) (f a) holds of gv and Arrow1 *)
(* applies.                                                                  *)
let candle_Arrow2 = prove
 (`(A --> B --> C) (f:A->B->C) fv /\
   do_partial_app fv av = SOME gv /\
   do_opapp [gv; bv] = SOME (env,exp) /\
   evaluate (s:(FFI)state) env [exp] = (s',res) /\
   A a av /\ B b bv /\
   perms_ok {} av /\
   perms_ok {} bv /\
   perms_ok {} fv ==>
   state_ffi s = state_ffi s' /\
   (res = Rerr (Rabort Rtimeout_error) \/
    res = Rerr (Rabort Rtype_error) \/
    state_refs s = state_refs s' /\
    state_eval_state s = state_eval_state s' /\
    state_next_type_stamp s = state_next_type_stamp s' /\
    ?rv. res = Rval [rv] /\ C (f a b) rv)`,
  STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL candle_Arrow1) THEN
  MAP_EVERY EXISTS_TAC [`env:v sem_env`; `exp:exp`; `B:B->v->bool`; `bv:v`; `gv:v`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CKFAUX_perms_ok_do_partial_app]] THEN
  UNDISCH_TAC `do_partial_app fv av = SOME gv` THEN
  REWRITE_TAC[do_partial_app_def] THEN
  REPEAT(CASE_TAC THEN REWRITE_TAC[distinctness "option"]) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM o REWRITE_RULE[injectivity "option"]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A` o BETA_RULE o
    GEN_REWRITE_RULE (RATOR_CONV o RATOR_CONV) [ml_Arrow_def]) THEN
  REWRITE_TAC[ml_AppReturns_def] THEN DISCH_THEN(MP_TAC o SPEC `av:v`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `[]:(v store_v)list`) THEN
  SIMP[do_opapp_cases; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[eval_rel_def; evaluate_def; PAIR_EQ; injectivity "result"; CONS_11] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The store invariant of the kernel (HOL_STORE)                             *)
(* ------------------------------------------------------------------------- *)

(* HOL4 GC_T [local] *)
let candle_GC_T = prove
 (`!s. cf_GC s <=> T`,
  REWRITE_TAC[SAT_GC]);;

(* HOL4: the proof uses cfApp's store2heap_MAPi; here cfStore's            *)
(* characterisation of the members of store2heap_aux                         *)
let MEM_st2heap = prove
 (`cf_Mem l x IN st2heap p (s:(FFI)state) <=>
   l < LENGTH (state_refs s) /\ x = EL l (state_refs s)`,
  PAIR_CASES_ON `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)` THEN
  REWRITE_TAC[st2heap_def; ffi2heap_def; IN_UNION; store2heap_def;
    CF1AUX_store2heap_aux_IN; LE_0; ADD_CLAUSES; SUB_0] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM; IN_SING; distinctness "heap_part"] THEN
  MESON_TAC[distinctness "heap_part"]);;

(* the locations of the kernel's references (the_type_constants = Loc T n, *)
(* ..., with the numerals computed as in candle_kernel_vals' kernel_locs)  *)
let ckfaux_loc_conv =
  REWRITE_CONV[the_type_constants_def; the_term_constants_def; the_axioms_def;
               the_context_def; refs_defs; LENGTH] THENC NUM_REDUCE_CONV;;

let CKFAUX_kernel_loc_nums =
  end_itlist CONJ (map ckfaux_loc_conv
    [`the_type_constants`; `the_term_constants`; `the_axioms`; `the_context`]);;

(* a reference assertion at a known location, as a membership *)
let CKFAUX_REF_REL_STAR = prove
 (`!(A:A->v->bool) l x P h.
     (REF_REL A (Loc T l) x STAR P) h <=>
     ?v. A x v /\ cf_Mem l (Refv v) IN h /\ P (h DELETE cf_Mem l (Refv v))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REF_REL_def; cf_REF_def; cf_cell_def; SEP_CLAUSES; SEP_EXISTS_THM] THEN
  REWRITE_TAC[AC LSORTAUX_STAR_AC
    `((set_sep_cond c1 STAR set_sep_one m) STAR set_sep_cond c2) STAR (P:(heap_part->bool)->bool) =
     set_sep_cond c1 STAR (set_sep_cond c2 STAR (set_sep_one m STAR P))`] THEN
  REWRITE_TAC[cond_STAR; one_STAR; injectivity "v"] THEN MESON_TAC[]);;

(* !loc. loc IN kernel_locs ==> P loc as one conjunct per location *)
let ckfaux_locs_rules =
  [kernel_locs; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM;
   FORALL_UNWIND_THM2];;

(* HOL_STORE refs STAR P as memberships of the four kernel references *)
let ckfaux_store_rules =
  [HOL_STORE_def; GSYM STAR_ASSOC; CKFAUX_kernel_loc_nums; CKFAUX_REF_REL_STAR;
   one_STAR; candle_GC_T; IN_DELETE; MEM_st2heap; injectivity "heap_part"];;

let HOL_STORE_not_kernel_locs = prove
 (`(!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs loc (state_refs s)) /\
   l < LENGTH (state_refs s) /\ ~(l IN kernel_locs) ==>
   (HOL_STORE refs STAR set_sep_one (cf_Mem l (EL l (state_refs s))) STAR cf_GC)
     (st2heap p (s:(FFI)state))`,
  REWRITE_TAC[candle_kernel_loc_ok_def; CKFAUX_kernel_loc_nums; injectivity "v";
    DE_MORGAN_THM] THEN
  REWRITE_TAC ckfaux_locs_rules THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC ckfaux_store_rules THEN
  REWRITE_TAC[oEL_EQ_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let REFS_PRED_HOL_STORE = prove
 (`(!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs loc (state_refs s)) ==>
   REFS_PRED (HOL_STORE,p) refs (s:(FFI)state)`,
  REWRITE_TAC[REFS_PRED_def; candle_kernel_loc_ok_def; CKFAUX_kernel_loc_nums;
    injectivity "v"] THEN
  REWRITE_TAC ckfaux_locs_rules THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC ckfaux_store_rules THEN
  REWRITE_TAC[oEL_EQ_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let HOL_STORE_kernel_loc_ok = prove
 (`(HOL_STORE r STAR frame) (st2heap p (s:(FFI)state)) /\ loc IN kernel_locs ==>
   candle_kernel_loc_ok r loc (state_refs s)`,
  REWRITE_TAC ckfaux_store_rules THEN REWRITE_TAC[kernel_locs] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[candle_kernel_loc_ok_def; CKFAUX_kernel_loc_nums; injectivity "v";
    oEL_EQ_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]);;

(* HOL4 IMP_perms_ok_lemma [local] *)
let IMP_perms_ok_lemma = prove
 (`(LIST_TYPE (PAIR_TYPE STRING_TYPE ml_NUM) x1 v ==> perms_ok ps v) /\
   (LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE) x2 v ==> perms_ok ps v) /\
   (LIST_TYPE THM_TYPE x3 v ==> perms_ok ps v) /\
   (LIST_TYPE UPDATE_TYPE x4 v ==> perms_ok ps v)`,
  RW[] THEN DRULE_AT (Pos last) LIST_TYPE_perms_ok THEN DISCH_THEN IRULE THEN RW[] THEN
  TRY (DRULE_AT (Pos last) PAIR_TYPE_perms_ok THEN DISCH_THEN IRULE THEN RW[]) THEN
  ASM_MESON_TAC[STRING_TYPE_perms_ok; NUM_perms_ok; TYPE_TYPE_perms_ok;
                THM_TYPE_perms_ok; UPDATE_TYPE_perms_ok]);;

(* ------------------------------------------------------------------------- *)
(* Applying certificates of monadic functions (ml_monad_translator's ArrowP) *)
(* ------------------------------------------------------------------------- *)

let CKFAUX_kernel_perms_not = prove
 (`~(DoFFI IN kernel_perms) /\ ~(RefAlloc IN kernel_perms) /\ ~(W8Alloc IN kernel_perms) /\
   (RefMention n IN kernel_perms <=> n IN kernel_locs)`,
  REWRITE_TAC[kernel_perms_def; IN_UNION; IN_IMAGE; IN_SING; distinctness "permission";
    injectivity "permission"; UNWIND_THM1]);;

(* the kernel's references have the kernel's permissions (HOL4: the impl_tac *)
(* of evaluate_kernel_perms in ArrowM1)                                      *)
let CKFAUX_perms_ok_state_kernel = prove
 (`(!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs loc (state_refs s)) ==>
   perms_ok_state kernel_perms (s:(FFI)state)`,
  REWRITE_TAC[perms_ok_state_def; kernel_perms_def; IN_UNION; IN_IMAGE; IN_SING;
    injectivity "permission"; distinctness "permission"] THEN
  REWRITE_TAC[UNWIND_THM1] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[candle_kernel_loc_ok_def] THEN
  REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[perms_ok_ref_def] THEN
  UNDISCH_TAC `(n:num) IN kernel_locs` THEN REWRITE_TAC[IN_kernel_locs] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_MESON_TAC[IMP_perms_ok_lemma]);;

(* MONAD as a disjunction of the two outcomes *)
let CKFAUX_MONAD_THM = prove
 (`!(a:A->v->bool) (b:B->v->bool) (x:R->(A,B)exc#R) st1 st2 res.
     MONAD a b x st1 (st2,res) <=>
     (?y v. x st1 = (M_success y,st2) /\ res = Rval [v] /\ a y v) \/
     (?e v. x st1 = (M_failure e,st2) /\ res = Rerr (Rraise v) /\ b e v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MONAD_def] THEN
  PAIR_CASES_ON `(x:R->(A,B)exc#R) st1` THEN
  REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc";
    injectivity "result"; distinctness "result"; injectivity "error_result";
    distinctness "error_result"; CONS_11; NOT_CONS_NIL]) THEN
  MESON_TAC[]);;

(* a membership in the heap from a separating conjunction *)
let CKFAUX_STAR_one_IN = prove
 (`!P Q R m (h:heap_part->bool).
     ((P STAR (set_sep_one m STAR Q)) STAR R) h ==> m IN h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[AC LSORTAUX_STAR_AC
    `((P STAR (set_sep_one m STAR Q)) STAR R) =
     set_sep_one (m:heap_part) STAR (P STAR Q STAR R)`] THEN
  SIMP_TAC[one_STAR]);;

(* HOL4 ArrowM1.  As in HOL4: the certificate run with no junk, the clock   *)
(* set back to the one of s, the frame rule of REFS_PRED_FRAME for the       *)
(* kernel's references (frame GC) and for each other reference (frame the   *)
(* reference itself); the permissions give the unchanged length, ffi and    *)
(* eval state (here from perms' evaluate_perms_ok_exp).                      *)
let ArrowM1 = prove
 (`ArrowP F (HOL_STORE,(p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (PURE A) (MONAD B D) (f:A->hol_refs->(B,C)exc#hol_refs) fv /\
   do_opapp [fv; av] = SOME (env,exp) /\
   evaluate (s:(FFI)state) env [exp] = (s',res) /\
   A a av /\ holKernelProof_STATE ctxt refs /\
   (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs loc (state_refs s)) /\
   (!loc r. ~(loc IN kernel_locs) /\ oEL loc (state_refs s) = SOME r ==>
            candle_ref_ok ctxt r) /\
   perms_ok kernel_perms av /\
   perms_ok kernel_perms fv ==>
   state_ffi s = state_ffi s' /\
   (res = Rerr (Rabort Rtimeout_error) \/
    res = Rerr (Rabort Rtype_error) \/
    state_next_type_stamp s = state_next_type_stamp s' /\
    state_eval_state s = state_eval_state s' /\
    ?r refs2.
      f a refs = (r,refs2) /\
      (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs2 loc (state_refs s')) /\
      (!loc r. ~(loc IN kernel_locs) /\ oEL loc (state_refs s') = SOME r ==>
               candle_ref_ok ctxt r) /\
      (!x. r = M_success x ==> ?rv. res = Rval [rv] /\ B x rv) /\
      (!x. r = M_failure x ==> ?rv. res = Rerr (Rraise rv) /\ D x rv))`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `exp:exp`; `s':(FFI)state`;
                 `res:(v list,v)result`; `kernel_perms`] evaluate_perms_ok_exp) THEN
  MP_TAC(ISPECL [`kernel_perms`; `fv:v`; `av:v`; `env:v sem_env`; `exp:exp`]
    perms_ok_do_opapp) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[CKFAUX_kernel_perms_not] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CKFAUX_perms_ok_state_kernel th]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the certificate, for the argument av and no junk *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `refs:hol_refs`; `s:(FFI)state`; `refs:hol_refs`;
    `Rval [av]:(v list,v)result`] o REWRITE_RULE[ArrowP_def]) THEN
  ASM_SIMP_TAC[PURE_def; REFS_PRED_HOL_STORE; injectivity "result"; CONS_11; UNWIND_THM1] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:v`; `env':v sem_env`; `exp':exp`] THEN
  STRIP_TAC THEN UNDISCH_THEN `av:v = v` (SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `do_opapp [fv; av] = SOME (env':v sem_env,exp':exp)` THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `[]:(v store_v)list`) THEN
  REWRITE_TAC[APPEND_NIL; with_same_refs] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(res3 = Rerr (Rabort Rtimeout_error):(v list,v)result)` ASSUME_TAC THENL
   [UNDISCH_TAC `MONAD B D ((f:A->hol_refs->(B,C)exc#hol_refs) a) refs (st3,res3)` THEN
    REWRITE_TAC[CKFAUX_MONAD_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result"];
    ALL_TAC] THEN
  (* the run from the clock of s *)
  MP_TAC(SPEC `state_clock (s:(FFI)state)` (MATCH_MP evaluate_set_init_clock
    (CONJ (ASSUME `evaluate (state_clock_fupd (combin_K ck) (s:(FFI)state)) env [exp] = s3,res3`)
          (ASSUME `~(res3 = Rerr (Rabort Rtimeout_error):(v list,v)result)`)))) THEN
  REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[with_same_clock; PAIR_EQ] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
     mem (fst(dest_var(lhs(concl th)))) ["s'"; "res"; "res1"; "st1"]))) THEN
  DISJ2_TAC THEN DISJ2_TAC THEN
  REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM] THEN
  UNDISCH_TAC `REFS_PRED_FRAME F (HOL_STORE,(p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
                 (refs,s) (st3,s3)` THEN
  REWRITE_TAC[REFS_PRED_FRAME_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(HOL_STORE refs STAR cf_GC)
                  (st2heap (p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list))
                    (s:(FFI)state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[REFS_PRED_HOL_STORE; REFS_PRED_def]; ALL_TAC] THEN
  (* the kernel's references, with the frame GC *)
  SUBGOAL_THEN `!loc. loc IN kernel_locs ==>
                      candle_kernel_loc_ok st3 loc (state_refs (s3:(FFI)state))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL HOL_STORE_kernel_loc_ok) THEN
    MAP_EVERY EXISTS_TAC
      [`cf_GC STAR cf_GC`; `p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STAR_ASSOC] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* each other reference, with itself as the frame *)
  SUBGOAL_THEN `!loc r. ~(loc IN kernel_locs) /\ oEL loc (state_refs (s3:(FFI)state)) = SOME r ==>
                candle_ref_ok ctxt r` ASSUME_TAC THENL
   [REWRITE_TAC[oEL_EQ_EL] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `loc < LENGTH (state_refs (s:(FFI)state))` ASSUME_TAC THENL
     [UNDISCH_TAC `LENGTH (state_refs (state_clock_fupd (combin_K ck') (s3:(FFI)state))) =
                   LENGTH (state_refs (s:(FFI)state))` THEN
      REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(INST [`loc:num`,`l:num`] HOL_STORE_not_kernel_locs) THEN
    ASM_REWRITE_TAC[GSYM STAR_ASSOC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (is_forall o concl))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CKFAUX_STAR_one_IN) THEN
    REWRITE_TAC[MEM_st2heap] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t ->
      try fst(dest_const t) = "candle_ref_ok" with _ -> false)) (concl th))) THEN
    EXISTS_TAC `loc:num` THEN ASM_REWRITE_TAC[oEL_EQ_EL];
    ALL_TAC] THEN
  (* the result *)
  EXISTS_TAC `FST ((f:A->hol_refs->(B,C)exc#hol_refs) a refs)` THEN
  EXISTS_TAC `st3:hol_refs` THEN
  UNDISCH_TAC `MONAD B D ((f:A->hol_refs->(B,C)exc#hol_refs) a) refs (st3,res3)` THEN
  REWRITE_TAC[CKFAUX_MONAD_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "exc"; injectivity "exc"] THEN
  REWRITE_TAC[injectivity "result"; injectivity "error_result"; CONS_11] THEN
  ASM_MESON_TAC[]);;

(* a partial application is a closure made by do_opapp on a Fun *)
let CKFAUX_do_partial_app_opapp = prove
 (`!f v g. do_partial_app f v = SOME g ==>
           ?env x e. do_opapp [f; v] = SOME (env,Fun x e) /\ g = Closure env x e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_partial_app_def] THEN
  REPEAT(CASE_TAC THEN REWRITE_TAC[distinctness "option"]) THEN
  REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP[do_opapp_cases; CONS_11; injectivity "v"; distinctness "v"; PAIR_EQ] THEN
  MESON_TAC[]);;

let CKFAUX_evaluate_Fun = prove
 (`!(st:(FFI)state) env x e. evaluate st env [Fun x e] = (st,Rval [Closure env x e])`,
  REWRITE_TAC[evaluate_def]);;

(* HOL4 ArrowM2.  HOL4 applies ArrowM1 to the closure gv after showing     *)
(* the inner certificate from a run of the outer one; the same here (the   *)
(* run with no junk evaluates the Fun to gv at once).                      *)
let ArrowM2 = prove
 (`ArrowP F (HOL_STORE,(p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
     (PURE A1) (ArrowM F (HOL_STORE,p) (PURE A2) (MONAD B D))
     (f:A->X->hol_refs->(B,C)exc#hol_refs) fv /\
   do_partial_app fv a1v = SOME gv /\
   do_opapp [gv; a2v] = SOME (env,exp) /\
   evaluate (s:(FFI)state) env [exp] = (s',res) /\
   A1 a1 a1v /\ A2 a2 a2v /\ holKernelProof_STATE ctxt refs /\
   (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs loc (state_refs s)) /\
   (!loc r. ~(loc IN kernel_locs) /\ oEL loc (state_refs s) = SOME r ==>
            candle_ref_ok ctxt r) /\
   perms_ok kernel_perms a1v /\
   perms_ok kernel_perms a2v /\
   perms_ok kernel_perms fv ==>
   state_ffi s = state_ffi s' /\
   (res = Rerr (Rabort Rtimeout_error) \/
    res = Rerr (Rabort Rtype_error) \/
    state_next_type_stamp s = state_next_type_stamp s' /\
    state_eval_state s = state_eval_state s' /\
    ?r refs2.
      f a1 a2 refs = (r,refs2) /\
      (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs2 loc (state_refs s')) /\
      (!loc r. ~(loc IN kernel_locs) /\ oEL loc (state_refs s') = SOME r ==>
               candle_ref_ok ctxt r) /\
      (!x. r = M_success x ==> ?rv. res = Rval [rv] /\ B x rv) /\
      (!x. r = M_failure x ==> ?rv. res = Rerr (Rraise rv) /\ D x rv))`,
  STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL ArrowM1) THEN
  MAP_EVERY EXISTS_TAC [`p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)`;
    `env:v sem_env`; `exp:exp`; `A2:X->v->bool`; `a2v:v`; `gv:v`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CKFAUX_perms_ok_do_partial_app]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a1:A`; `refs:hol_refs`; `s:(FFI)state`; `refs:hol_refs`;
    `Rval [a1v]:(v list,v)result`] o REWRITE_RULE[ArrowP_def] o
    check (can (find_term (fun t -> try fst(dest_const t) = "ArrowM" with _ -> false)) o concl)) THEN
  ASM_SIMP_TAC[PURE_def; REFS_PRED_HOL_STORE; injectivity "result"; CONS_11; UNWIND_THM1] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:v`; `env1:v sem_env`; `exp1:exp`] THEN
  STRIP_TAC THEN UNDISCH_THEN `a1v:v = v` (SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `[]:(v store_v)list`) THEN
  REWRITE_TAC[APPEND_NIL; with_same_refs; ArrowM_def; PURE_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CKFAUX_do_partial_app_opapp o
    check (can (find_term (fun t -> try fst(dest_const t) = "do_partial_app" with _ -> false)) o
           concl)) THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v':v = gv` (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
  UNDISCH_TAC `evaluate (state_clock_fupd (combin_K ck) (s:(FFI)state)) env1 [exp1] = s3,res3` THEN
  ASM_REWRITE_TAC[CKFAUX_evaluate_Fun; PAIR_EQ; injectivity "result"; CONS_11] THEN
  MESON_TAC[]);;

let state_ok_with_clock = prove
 (`candle_state_ok ctxt (state_clock_fupd (combin_K k) (s:(FFI)state)) <=> candle_state_ok ctxt s`,
  SIMP[candle_state_ok_def]);;
let _ = cake_add_simps [state_ok_with_clock];;

(* HOL4's variable abs is an interface name here: a *)
let EqualityType_11 = prove
 (`!(a:A->v->bool) x v v'. EqualityType a /\ a x v /\ a x v' ==> v = v'`,
  REWRITE_TAC[EqualityType_def] THEN MESON_TAC[]);;

(* HOL4: the four EqualityType facts proved inside IMP_EVERY_v_ok *)
let CKFAUX_EqualityType_kernel_refs = prove
 (`EqualityType (LIST_TYPE (PAIR_TYPE STRING_TYPE ml_NUM)) /\
   EqualityType (LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE)) /\
   EqualityType (LIST_TYPE THM_TYPE) /\
   EqualityType (LIST_TYPE UPDATE_TYPE)`,
  REPEAT CONJ_TAC THEN MATCH_MP_TAC EqualityType_LIST_TYPE THEN
  REWRITE_TAC[EqualityType_THM_TYPE; EqualityType_UPDATE_TYPE] THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] EqualityType_PAIR_TYPE) THEN
  REWRITE_TAC[EqualityType_NUM_BOOL; EqualityType_TYPE_TYPE]);;

let IMP_EVERY_v_ok = prove
 (`(!loc. if loc IN kernel_locs then candle_kernel_loc_ok refs loc (state_refs (s':(FFI)state))
          else oEL loc (state_refs s') = oEL loc (state_refs (s:(FFI)state))) /\
   (!loc. loc IN kernel_locs ==> candle_kernel_loc_ok refs loc (state_refs s)) /\
   ALL (candle_ref_ok ctxt) (state_refs s) /\ holKernelProof_STATE ctxt refs ==>
   ALL (candle_ref_ok ctxt) (state_refs s')`,
  REWRITE_TAC[EVERY_EL] THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_cond o snd o strip_forall o concl)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [(* a kernel reference: the same value in both stores (EqualityType) *)
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `candle_kernel_loc_ok refs n (state_refs (s':(FFI)state))` THEN
    REWRITE_TAC[candle_kernel_loc_ok_def; CKFAUX_kernel_loc_nums; injectivity "v"; oEL_EQ_EL] THEN
    UNDISCH_TAC `n IN kernel_locs` THEN REWRITE_TAC[kernel_locs] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    W(fun (_,w) -> FIRST_X_ASSUM(MP_TAC o SPEC (rand(rator(rand w))) o
                     check (is_forall o concl))) THEN
    REWRITE_TAC[kernel_locs; candle_kernel_loc_ok_def; CKFAUX_kernel_loc_nums; injectivity "v";
      oEL_EQ_EL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    (SUBGOAL_THEN `v:v = v'` SUBST_ALL_TAC THENL
      [FIRST_ASSUM(fun th -> let a = rator(rator(concl th)) in
         MATCH_MP_TAC (ISPEC a EqualityType_11) THEN EXISTS_TAC (rand(rator(concl th)))) THEN
       ASM_REWRITE_TAC[CKFAUX_EqualityType_kernel_refs];
       ALL_TAC]) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(rator(lhs(concl th)))) = "Refv" with _ -> false)))) THEN
    ASM_MESON_TAC[];
    (* another reference: unchanged *)
    SUBGOAL_THEN `oEL n (state_refs (s':(FFI)state)) = SOME (EL n (state_refs s'))`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[oEL_EQ_EL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
    ASM_MESON_TAC[]]);;

let HOL_EXN_TYPE_Fail_v_ok = prove
 (`HOL_EXN_TYPE (holKernel_Failure m) v ==> candle_v_ok ctxt v`,
  REWRITE_TAC[HOL_EXN_TYPE_def; STRING_TYPE_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC candle_v_ok_Conv THEN
  REWRITE_TAC[ALL; injectivity "option"; distinctness "stamp"; candle_v_ok_Lit]);;

let inferred_APPEND = prove
 (`!c v. candle_inferred c v ==>
     !x s. holKernelProof_STATE (APPEND x c) s /\
           (!th. holKernelProof_THM c th ==> holKernelProof_THM (APPEND x c) th) ==>
           candle_inferred (APPEND x c) v`,
  MATCH_MP_TAC candle_inferred_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  ASM_MESON_TAC[TYPE_APPEND_EXTEND; TERM_APPEND_EXTEND]);;

(* HOL4's statement has the vacuous quantifiers !x s. before !x s. in its  *)
(* second and third conjuncts; they are kept (with types)                  *)
let v_ok_APPEND = prove
 (`(!c v. candle_kernel_vals c v ==>
     !x s. holKernelProof_STATE (APPEND x c) s /\
           (!th. holKernelProof_THM c th ==> holKernelProof_THM (APPEND x c) th) ==>
           candle_kernel_vals (APPEND x c) v) /\
   (!c v. candle_v_ok c v ==> !(x:update list) (s:hol_refs).
     !x s. holKernelProof_STATE (APPEND x c) s /\
           (!th. holKernelProof_THM c th ==> holKernelProof_THM (APPEND x c) th) ==>
           candle_v_ok (APPEND x c) v) /\
   (!c e. candle_env_ok c e ==> !(x:update list) (s:hol_refs).
     !x s. holKernelProof_STATE (APPEND x c) s /\
           (!th. holKernelProof_THM c th ==> holKernelProof_THM (APPEND x c) th) ==>
           candle_env_ok (APPEND x c) e)`,
  MATCH_MP_TAC candle_v_ok_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[candle_v_ok_cases] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[inferred_APPEND]);;
let ref_ok_APPEND = prove
 (`!c v. candle_ref_ok c v ==> !(x:update list) (s:hol_refs).
     !x s. holKernelProof_STATE (APPEND x c) s /\
           (!th. holKernelProof_THM c th ==> holKernelProof_THM (APPEND x c) th) ==>
           candle_ref_ok (APPEND x c) v`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `v:(v)store_v` (cases "store_v")) THEN
  REWRITE_TAC[candle_ref_ok_def; GSYM ALL_MEM] THEN MESON_TAC[v_ok_APPEND]);;

(* ------------------------------------------------------------------------- *)
(* inferred_ok, one lemma per kernel function (HOL4's cases), from common   *)
(* drivers: the safe errors of the argument checks (the head lemmas), and   *)
(* the certificates of the functions translated by translate (Arrow1) and   *)
(* by m_translate (ArrowM1)                                                  *)
(* ------------------------------------------------------------------------- *)

(* the conclusion of inferred_ok and kernel_vals_ok, for a state s, the     *)
(* final state s' and the result res                                         *)
let ckfaux_concl =
  `(?abort. state_ffi s' = state_ffi (s:(FFI)state) /\ res = Rerr (Rabort abort)) \/
   ?ctxt'. candle_state_ok ctxt' (s':(FFI)state) /\
     (!v. candle_v_ok ctxt v ==> candle_v_ok ctxt' v) /\
     (!v. candle_kernel_vals ctxt v ==> candle_kernel_vals ctxt' v) /\
     (!vs. res = Rval vs ==> ALL (candle_v_ok ctxt') vs) /\
     (!v. res = Rerr (Rraise v) ==> candle_v_ok ctxt' v)`;;

(* the errors that the argument checks of the kernel functions raise *)
let CKFAUX_safe_error = prove
 (mk_imp(`candle_state_ok ctxt (s:(FFI)state) /\
          (?k. s' = state_clock_fupd (combin_K k) s /\
               (res = Rerr (Rabort Rtype_error) \/
                res = Rerr (Rraise bind_exn_v) \/
                res = Rerr (Rabort Rtimeout_error):(v list,v)result))`, ckfaux_concl),
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN SIMP[] THEN MESON_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `ctxt:update list` THEN
    ASM_SIMP_TAC[state_ok_with_clock; distinctness "result"; injectivity "result";
                 injectivity "error_result"] THEN
    MESON_TAC[v_ok_bind_exn_v];
    DISJ1_TAC THEN SIMP[] THEN MESON_TAC[]]);;

let CKFAUX_state_ok_same = prove
 (`candle_state_ok ctxt (s:(FFI)state) /\ state_refs s' = state_refs s /\
   state_ffi s' = state_ffi s /\ state_eval_state s' = state_eval_state s /\
   state_next_type_stamp s' = state_next_type_stamp s ==> candle_state_ok ctxt (s':(FFI)state)`,
  STRIP_TAC THEN ASM_REWRITE_TAC[candle_state_ok_def] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[candle_state_ok_def] o
    check (can (find_term ((=) `candle_state_ok:update list->(FFI)state->bool`)) o concl)) THEN
  REWRITE_TAC[]);;

(* a kernel function translated by translate (a certificate (A --> B) f fv) *)
let CKFAUX_pure1_ok = prove
 (mk_imp(`(A --> B) (f:A->B) fv /\ do_opapp [fv; v] = SOME (env,exp) /\
          evaluate (s:(FFI)state) env [exp] = (s',res) /\ A a v /\
          perms_ok {} v /\ perms_ok {} fv /\ candle_state_ok ctxt s /\
          (!rv. B (f a) rv ==> candle_v_ok ctxt rv)`, ckfaux_concl),
  STRIP_TAC THEN MP_TAC(INST [`v:v`,`av:v`] candle_Arrow1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "result"; injectivity "result";
    injectivity "error_result"; distinctness "error_result"] THENL
   [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `ctxt:update list` THEN SIMP[ALL] THEN
  ASM_MESON_TAC[CKFAUX_state_ok_same]);;
(* the side condition of the monadic drivers: what the kernel function f    *)
(* does with the kernel's state (a new context ctxt' that preserves every   *)
(* invariant of ctxt, and invariant results)                                *)
let ckfaux_monad_side =
  `!refs r refs2. holKernelProof_STATE ctxt refs /\
     (f:A->hol_refs->(B,hol_exn)exc#hol_refs) a refs = (r,refs2) ==>
     ?ctxt'. holKernelProof_STATE ctxt' refs2 /\
       (!v. candle_v_ok ctxt v ==> candle_v_ok ctxt' v) /\
       (!v. candle_kernel_vals ctxt v ==> candle_kernel_vals ctxt' v) /\
       (!r. candle_ref_ok ctxt r ==> candle_ref_ok ctxt' r) /\
       (!x rv. r = M_success x /\ (B:B->v->bool) x rv ==> candle_v_ok ctxt' rv) /\
       (!e rv. r = M_failure e /\ HOL_EXN_TYPE e rv ==> candle_v_ok ctxt' rv)`;;

(* a kernel function translated by m_translate, one argument (ArrowM1) *)
let CKFAUX_monad1_ok = prove
 (mk_imp(list_mk_conj
   [`ArrowP F (HOL_STORE,(p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
       (PURE A) (MONAD B HOL_EXN_TYPE) (f:A->hol_refs->(B,hol_exn)exc#hol_refs) fv`;
    `do_opapp [fv; v] = SOME (env,exp)`;
    `evaluate (s:(FFI)state) env [exp] = (s',res)`; `(A:A->v->bool) a v`;
    `perms_ok kernel_perms v`; `perms_ok kernel_perms fv`; `candle_state_ok ctxt (s:(FFI)state)`;
    ckfaux_monad_side], ckfaux_concl),
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[candle_state_ok_def] o
    check (can (find_term ((=) `candle_state_ok:update list->(FFI)state->bool`)) o concl)) THEN
  MP_TAC(INST [`v:v`,`av:v`; `HOL_EXN_TYPE`,`D:hol_exn->v->bool`; `state:hol_refs`,`refs:hol_refs`]
    (INST_TYPE [`:hol_exn`,`:C`] ArrowM1)) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "result"; injectivity "result";
    injectivity "error_result"; distinctness "error_result"] THENL
   [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`state:hol_refs`; `r:(B,hol_exn)exc`; `refs2:hol_refs`] o
    check (is_forall o concl) o
    check (can (find_term (fun t -> try fst(dest_const t) = "holKernelProof_STATE"
                                    with _ -> false)) o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ctxt':update list` STRIP_ASSUME_TAC) THEN
  DISJ2_TAC THEN EXISTS_TAC `ctxt':update list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[candle_state_ok_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[candle_state_ok_def]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `y:B` SUBST_ALL_TAC) (X_CHOOSE_THEN `y:hol_exn` SUBST_ALL_TAC)
    (ISPEC `r:(B,hol_exn)exc` (cases "exc")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"; distinctness "exc"; UNWIND_THM1;
    FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `rv:v` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; injectivity "error_result";
    distinctness "error_result"] THEN
  SIMP[ALL] THEN ASM_MESON_TAC[]);;

(* the failures of a kernel function that raises no Clash are invariant *)
let CKFAUX_failure_ok = prove
 (`!(r:(A,hol_exn)exc) ctxt. (!t. ~(r = M_failure (holKernel_Clash t))) ==>
     !e rv. r = M_failure e /\ HOL_EXN_TYPE e rv ==> candle_v_ok ctxt rv`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:hol_exn` THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `m:mlstring` SUBST_ALL_TAC)
                   (X_CHOOSE_THEN `t:hol_term` SUBST_ALL_TAC) (ISPEC `e:hol_exn` (cases "hol_exn")) THEN
  ASM_MESON_TAC[HOL_EXN_TYPE_Fail_v_ok]);;

(* a driver applied to a certificate, with the HOL argument a instantiated *)
let ckfaux_drive drv cert a =
  let th = MATCH_MP (CONV_RULE (REWR_CONV (TAUT `(p /\ q ==> r) <=> (p ==> q ==> r)`)) drv)
             cert in
  let av = find (fun v -> fst(dest_var v) = "a") (frees (concl th)) in
  INST [a,av] th;;

(* the statement of inferred_ok for the closure fv of a kernel function *)
let ckfaux_inferred_goal fv =
  vsubst [fv,`f:v`]
    (mk_imp(`candle_state_ok ctxt (s:(FFI)state) /\ candle_v_ok ctxt v /\
             do_opapp [f; v] = SOME (env,exp) /\ evaluate s env [exp] = (s',res)`,
            ckfaux_concl));;

(* the first step of each case: the head lemma gives a safe error or the    *)
(* shape of the argument                                                     *)
let ckfaux_head_tac head =
  STRIP_TAC THEN DRULE_ALL head THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> MATCH_MP_TAC CKFAUX_safe_error THEN ASM_REWRITE_TAC[th]) ASSUME_TAC);;

(* the kernel's state of a state_ok state *)
let ckfaux_state_tac =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[candle_state_ok_def] o
    check (can (find_term ((=) `candle_state_ok:update list->(FFI)state->bool`)) o concl));;

(* the shape tests of the head lemmas give typed values (HOL4: the          *)
(* v_ok_*_HEAD lemmas, composed by hand at each use)                         *)
let CKFAUX_STRING_TYPE_HEAD = prove
 (`!v. candle_v_ok ctxt v /\ STRING_TYPE_HEAD v ==> ?s. STRING_TYPE s v`,
  REWRITE_TAC[STRING_TYPE_HEAD_def] THEN MESON_TAC[]);;

let CKFAUX_INT_HEAD = prove
 (`!v. candle_v_ok ctxt v /\ INT_HEAD v ==> ?n. ml_INT n v`,
  REWRITE_TAC[INT_HEAD_def] THEN MESON_TAC[]);;

(* |- !v. candle_v_ok ctxt v /\ h v ==> ?a. inv a v, for a head predicate h *)
let rec ckfaux_head_thm h =
  let inv_of th = let _,b = dest_forall (concl th) in
                  let _,e = dest_exists (rand b) in rator(rator e) in
  match h with
    Const("TYPE_TYPE_HEAD",_) -> GEN `v:v` v_ok_TYPE_TYPE_HEAD
  | Const("TERM_TYPE_HEAD",_) -> GEN `v:v` v_ok_TERM_TYPE_HEAD
  | Const("THM_TYPE_HEAD",_) -> GEN `v:v` v_ok_THM_TYPE_HEAD
  | Const("STRING_TYPE_HEAD",_) -> CKFAUX_STRING_TYPE_HEAD
  | Const("INT_HEAD",_) -> CKFAUX_INT_HEAD
  | Comb(Const("LIST_TYPE_HEAD",_),h1) ->
      let th1 = ckfaux_head_thm h1 in
      let inv1 = inv_of th1 in
      let ty1 = hd(snd(dest_type(type_of inv1))) in
      let th = INST [h1,`A_HEAD:v->bool`; inv1,mk_var("A",type_of inv1)]
                 (INST_TYPE [ty1,`:A`] v_ok_LIST_TYPE_HEAD) in
      let gl = mk_forall(`v:v`, mk_imp(mk_conj(`candle_v_ok ctxt v`, mk_comb(h,`v:v`)),
                 rand(concl th))) in
      prove(gl, GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[th1])
  | Comb(Comb(Const("PAIR_TYPE_HEAD",_),h1),h2) ->
      let th1 = ckfaux_head_thm h1 and th2 = ckfaux_head_thm h2 in
      let inv1 = inv_of th1 and inv2 = inv_of th2 in
      let ty1 = hd(snd(dest_type(type_of inv1))) and ty2 = hd(snd(dest_type(type_of inv2))) in
      let th = INST [h1,`A_HEAD:v->bool`; h2,`B_HEAD:v->bool`;
                     inv1,mk_var("A",type_of inv1); inv2,mk_var("B",type_of inv2)]
                 (INST_TYPE [ty1,`:A`; ty2,`:B`] v_ok_PAIR_TYPE_HEAD) in
      let gl = mk_forall(`v:v`, mk_imp(mk_conj(`candle_v_ok ctxt v`, mk_comb(h,`v:v`)),
                 rand(concl th))) in
      prove(gl, GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[th1; th2])
  | _ -> failwith "ckfaux_head_thm";;

(* |- !x v. inv x v ==> perms_ok ps v, for a type invariant inv *)
let rec ckfaux_perms_thm inv =
  match inv with
    Const("TYPE_TYPE",_) -> TYPE_TYPE_perms_ok
  | Const("TERM_TYPE",_) -> TERM_TYPE_perms_ok
  | Const("THM_TYPE",_) -> THM_TYPE_perms_ok
  | Const("STRING_TYPE",_) -> STRING_TYPE_perms_ok
  | Const("ml_INT",_) -> INT_perms_ok
  | Const("ml_NUM",_) -> NUM_perms_ok
  | Const("UNIT_TYPE",_) -> UNIT_TYPE_perms_ok
  | Const("UPDATE_TYPE",_) -> UPDATE_TYPE_perms_ok
  | Comb(Const("LIST_TYPE",_),a) ->
      let th1 = ckfaux_perms_thm a in
      let ty1 = hd(snd(dest_type(type_of a))) in
      let th = INST [a,mk_var("A",type_of a)] (INST_TYPE [ty1,`:A`] LIST_TYPE_perms_ok) in
      let x = mk_var("x",mk_type("list",[ty1])) in
      let gl = list_mk_forall([x;`v:v`], mk_imp(list_mk_comb(inv,[x;`v:v`]), `perms_ok ps v`)) in
      prove(gl, REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN TRY (EXISTS_TAC x) THEN
                ASM_MESON_TAC[th1])
  | Comb(Comb(Const("PAIR_TYPE",_),a),b) ->
      let th1 = ckfaux_perms_thm a and th2 = ckfaux_perms_thm b in
      let ty1 = hd(snd(dest_type(type_of a))) and ty2 = hd(snd(dest_type(type_of b))) in
      let th = INST [a,mk_var("A",type_of a); b,mk_var("B",type_of b)]
                 (INST_TYPE [ty1,`:A`; ty2,`:B`] PAIR_TYPE_perms_ok) in
      let x = mk_var("x",mk_type("prod",[ty1;ty2])) in
      let gl = list_mk_forall([x;`v:v`], mk_imp(list_mk_comb(inv,[x;`v:v`]), `perms_ok ps v`)) in
      prove(gl, REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN TRY (EXISTS_TAC x) THEN
                ASM_MESON_TAC[th1; th2])
  | _ -> failwith "ckfaux_perms_thm";;

let CKFAUX_UNIT_TYPE_v_ok = prove
 (`UNIT_TYPE x v ==> candle_v_ok ctxt v`,
  REWRITE_TAC[UNIT_TYPE_def] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[v_ok_Conv_NONE; ALL]);;

(* the beta normal form of a term *)
let ckfaux_bnorm t = rhs(concl(TOP_DEPTH_CONV BETA_CONV t));;

(* (P, |- !x rv. inv x rv /\ P x ==> candle_v_ok ctxt rv) for a type        *)
(* invariant inv; P is the validity of the HOL value (TYPE, TERM, THM of   *)
(* ctxt, componentwise); the statement is in beta normal form              *)
let rec ckfaux_vok inv =
  let ty = hd(snd(dest_type(type_of inv))) in
  let x = mk_var("x",ty) in
  let mk p th0 =
    let gl = list_mk_forall([x;`rv:v`],
               mk_imp(mk_conj(list_mk_comb(inv,[x;`rv:v`]), ckfaux_bnorm (mk_comb(p,x))),
                      `candle_v_ok ctxt rv`)) in
    p, prove(gl, REPEAT GEN_TAC THEN th0) in
  match inv with
    Const("TYPE_TYPE",_) -> mk `holKernelProof_TYPE ctxt` (MESON_TAC[TYPE_IMP_v_ok])
  | Const("TERM_TYPE",_) -> mk `holKernelProof_TERM ctxt` (MESON_TAC[TERM_IMP_v_ok])
  | Const("THM_TYPE",_) -> mk `holKernelProof_THM ctxt` (MESON_TAC[THM_IMP_v_ok])
  | Const("STRING_TYPE",_) -> mk `\x:mlstring. T` (MESON_TAC[STRING_TYPE_v_ok])
  | Const("ml_NUM",_) -> mk `\x:num. T` (MESON_TAC[NUM_v_ok])
  | Const("ml_BOOL",_) -> mk `\x:bool. T` (MESON_TAC[BOOL_v_ok])
  | Const("UNIT_TYPE",_) -> mk `\x:1. T` (MESON_TAC[CKFAUX_UNIT_TYPE_v_ok])
  | Comb(Const("LIST_TYPE",_),a) ->
      let p1,th1 = ckfaux_vok a in
      let ty1 = hd(snd(dest_type(type_of a))) in
      let lth = ISPEC a LIST_TYPE_v_ok in
      mk (mk_comb(mk_const("ALL",[ty1,`:A`]),p1))
        (STRIP_TAC THEN MATCH_MP_TAC lth THEN EXISTS_TAC x THEN ASM_REWRITE_TAC[] THEN
         FIRST_X_ASSUM(MP_TAC o check (fun th ->
           try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with _ -> false)) THEN
         MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN REPEAT STRIP_TAC THEN
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
         RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN ASM_MESON_TAC[th1])
  | Comb(Comb(Const("PAIR_TYPE",_),a),b) ->
      let p1,th1 = ckfaux_vok a and p2,th2 = ckfaux_vok b in
      let ty1 = hd(snd(dest_type(type_of a))) and ty2 = hd(snd(dest_type(type_of b))) in
      let pv = mk_var("p",mk_type("prod",[ty1;ty2])) in
      let p = mk_abs(pv, mk_conj(mk_comb(p1, mk_comb(mk_const("FST",[ty1,`:A`;ty2,`:B`]),pv)),
                                 mk_comb(p2, mk_comb(mk_const("SND",[ty1,`:A`;ty2,`:B`]),pv)))) in
      let pth = INST [a,mk_var("A",type_of a); b,mk_var("B",type_of b)]
                  (INST_TYPE [ty1,`:A`; ty2,`:B`] PAIR_TYPE_v_ok) in
      mk p (STRIP_TAC THEN MATCH_MP_TAC (INST [x,mk_var("p",type_of x)] pth) THEN
            ASM_REWRITE_TAC[] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
            CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[th1; th2])
  | _ -> failwith "ckfaux_vok";;

(* (P, |- !x v. inv x v /\ candle_v_ok ctxt v ==> P x): the validity of the *)
(* HOL value of a v_ok value (HOL4 v_ok_TYPE, v_ok_LIST, v_ok_PAIR, ...)     *)
let rec ckfaux_valid inv =
  let ty = hd(snd(dest_type(type_of inv))) in
  let x = mk_var("x",ty) in
  let mk p tac =
    let gl = list_mk_forall([x;`v:v`],
               mk_imp(mk_conj(list_mk_comb(inv,[x;`v:v`]), `candle_v_ok ctxt v`),
                      ckfaux_bnorm (mk_comb(p,x)))) in
    p, prove(gl, REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN tac) in
  let abs_ctxt p = mk_abs(`c:update list`, vsubst [`c:update list`,`ctxt:update list`] p) in
  match inv with
    Const("TYPE_TYPE",_) -> mk `holKernelProof_TYPE ctxt` (MESON_TAC[v_ok_TYPE])
  | Const("TERM_TYPE",_) -> mk `holKernelProof_TERM ctxt` (MESON_TAC[v_ok_TERM])
  | Const("THM_TYPE",_) -> mk `holKernelProof_THM ctxt` (MESON_TAC[v_ok_THM])
  | Const(_,_) -> mk (mk_abs(x,`T`)) (REWRITE_TAC[])
  | Comb(Const("LIST_TYPE",_),a) ->
      let p1,th1 = ckfaux_valid a in
      let ty1 = hd(snd(dest_type(type_of a))) in
      let lth = BETA_RULE (INST [abs_ctxt p1,mk_var("A",mk_fun_ty `:update list` (type_of p1));
                                 a,mk_var("A_TYPE",type_of a)]
                   (INST_TYPE [ty1,`:A`] v_ok_LIST)) in
      mk (mk_comb(mk_const("ALL",[ty1,`:A`]),p1)) (MESON_TAC[MP lth th1])
  | Comb(Comb(Const("PAIR_TYPE",_),a),b) ->
      let p1,th1 = ckfaux_valid a and p2,th2 = ckfaux_valid b in
      let ty1 = hd(snd(dest_type(type_of a))) and ty2 = hd(snd(dest_type(type_of b))) in
      let pv = mk_var("p",mk_type("prod",[ty1;ty2])) in
      let fst_tm = mk_const("FST",[ty1,`:A`;ty2,`:B`])
      and snd_tm = mk_const("SND",[ty1,`:A`;ty2,`:B`]) in
      let p = mk_abs(pv, mk_conj(mk_comb(p1, mk_comb(fst_tm,pv)), mk_comb(p2, mk_comb(snd_tm,pv)))) in
      let pth = BETA_RULE (INST [abs_ctxt p1,mk_var("A",mk_fun_ty `:update list` (type_of p1));
                                 abs_ctxt p2,mk_var("B",mk_fun_ty `:update list` (type_of p2));
                                 a,mk_var("A_TYPE",type_of a); b,mk_var("B_TYPE",type_of b)]
                   (INST_TYPE [ty1,`:A`; ty2,`:B`] v_ok_PAIR)) in
      mk p (STRIP_TAC THEN MATCH_MP_TAC (CONV_RULE(TOP_DEPTH_CONV BETA_CONV) pth) THEN
            ASM_REWRITE_TAC[th1; th2])
  | _ -> failwith "ckfaux_valid";;

(* the newest assumption h v (a head of the argument v) as a typed value a; *)
(* the validity of a (ckfaux_valid) is assumed too                          *)
let ckfaux_typed_tac (a:term) (asl,w as g) =
  let hv = concl(snd(hd asl)) in
  let valid_tac (asl,w as g) =
    let iv = concl(snd(hd asl)) in
    let _,vth = ckfaux_valid (rator(rator iv)) in
    let th = SPECL [a; rand iv] vth in
    (SUBGOAL_THEN (rand(concl th)) (STRIP_ASSUME_TAC o REWRITE_RULE[]) THENL
      [MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]; ALL_TAC]) g in
  if is_exists hv then (FIRST_X_ASSUM(X_CHOOSE_TAC a) THEN valid_tac) g
  else if rator hv = `UNIT_TYPE one` then ALL_TAC g else
  let th = ckfaux_head_thm (rator hv) in
  (MP_TAC (SPEC (rand hv) th) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC a) THEN
   valid_tac) g;;

(* perms_ok ps v from an assumption inv a v *)
let ckfaux_arg_perms_tac =
  FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC
    (MATCH_MP (SPEC_ALL (ckfaux_perms_thm (rator(rator(concl th))))) th));;

(* !rv. inv y rv ==> candle_v_ok ctxt rv, reduced to the validity of y *)
let ckfaux_res_tac (asl,w as g) =
  let rv,body = dest_forall w in
  let ant = lhand body in
  let inv = rator(rator ant) and y = rand(rator ant) in
  let _,th = ckfaux_vok inv in
  (X_GEN_TAC rv THEN DISCH_TAC THEN MATCH_MP_TAC th THEN EXISTS_TAC y THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ALL_T]) g;;

(* a pure one-argument kernel function (certificate by translate) *)
let ckfaux_pure1_case head cert a perms_th res_tac =
  ckfaux_head_tac head THEN ckfaux_typed_tac a THEN
  MP_TAC(ckfaux_drive CKFAUX_pure1_ok cert a) THEN
  ASM_REWRITE_TAC[perms_th] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ckfaux_arg_perms_tac; ckfaux_res_tac THEN res_tac];;

(* the side condition of a monadic kernel function that does not change    *)
(* the kernel's state                                                        *)
let CKFAUX_monad_side_same = prove
 (mk_imp(`(!refs r refs2. holKernelProof_STATE ctxt refs /\
             (f:A->hol_refs->(B,hol_exn)exc#hol_refs) a refs = (r,refs2) ==>
             refs2 = refs /\ (!x. r = M_success x ==> P x) /\
             (!t. ~(r = M_failure (holKernel_Clash t)))) /\
          (!x rv. (B:B->v->bool) x rv /\ P x ==> candle_v_ok ctxt rv)`, ckfaux_monad_side),
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`refs:hol_refs`; `r:(B,hol_exn)exc`; `refs2:hol_refs`] o check (is_forall o concl) o
    check (can (find_term (fun t -> try fst(dest_const t) = "holKernelProof_STATE"
                                    with _ -> false)) o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `ctxt:update list` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC CKFAUX_failure_ok THEN ASM_REWRITE_TAC[]]);;

(* the monadic one-argument kernel functions that do not change the state;  *)
(* spec_tac proves the side condition with the validity predicate of the   *)
(* result type                                                               *)
let ckfaux_monad1_case head cert a perms_th spec_tac =
  let args = snd(strip_comb(concl cert)) in
  let b = rand(rator(el 3 args)) in
  let p,vth = ckfaux_vok b in
  ckfaux_head_tac head THEN ckfaux_typed_tac a THEN
  MP_TAC(ckfaux_drive CKFAUX_monad1_ok cert a) THEN
  ASM_REWRITE_TAC[perms_th] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ckfaux_arg_perms_tac;
    MATCH_MP_TAC (GEN_ALL CKFAUX_monad_side_same) THEN EXISTS_TAC p THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [spec_tac; MATCH_ACCEPT_TAC vth]];;
let CKFAUX_inferred_concl = prove
 (ckfaux_inferred_goal `concl_v`,
  ckfaux_pure1_case concl_v_head concl_v_thm `th:thm` perms_ok_concl_v
   (ckfaux_state_tac THEN MATCH_MP_TAC concl_thm THEN ASM_MESON_TAC[]));;

let CKFAUX_inferred_is_type = prove
 (ckfaux_inferred_goal `is_type_v`,
  ckfaux_pure1_case is_type_v_head is_type_v_thm `ty:hol_type` perms_ok_is_type_v ALL_TAC);;

let CKFAUX_inferred_is_vartype = prove
 (ckfaux_inferred_goal `is_vartype_v`,
  ckfaux_pure1_case is_vartype_v_head is_vartype_v_thm `ty:hol_type` perms_ok_is_vartype_v
   ALL_TAC);;

let CKFAUX_inferred_call_tyvars = prove
 (ckfaux_inferred_goal `call_tyvars_v`,
  ckfaux_pure1_case call_tyvars_v_head call_tyvars_v_thm `ty:hol_type` perms_ok_call_tyvars_v
   ALL_TAC);;

let CKFAUX_inferred_is_var = prove
 (ckfaux_inferred_goal `is_var_v`,
  ckfaux_pure1_case is_var_v_head is_var_v_thm `tm:hol_term` perms_ok_is_var_v ALL_TAC);;

let CKFAUX_inferred_is_const = prove
 (ckfaux_inferred_goal `is_const_v`,
  ckfaux_pure1_case is_const_v_head is_const_v_thm `tm:hol_term` perms_ok_is_const_v ALL_TAC);;

let CKFAUX_inferred_is_abs = prove
 (ckfaux_inferred_goal `is_abs_v`,
  ckfaux_pure1_case is_abs_v_head is_abs_v_thm `tm:hol_term` perms_ok_is_abs_v ALL_TAC);;

let CKFAUX_inferred_is_comb = prove
 (ckfaux_inferred_goal `is_comb_v`,
  ckfaux_pure1_case is_comb_v_head is_comb_v_thm `tm:hol_term` perms_ok_is_comb_v ALL_TAC);;

let CKFAUX_inferred_call_type_vars_in_term = prove
 (ckfaux_inferred_goal `call_type_vars_in_term_v`,
  ckfaux_pure1_case call_type_vars_in_term_v_head call_type_vars_in_term_v_thm `tm:hol_term`
    perms_ok_call_type_vars_in_term_v ALL_TAC);;
let CKFAUX_TERM_Var = prove
 (`holKernelProof_TERM ctxt (hol_Var x ty) <=> holKernelProof_TYPE ctxt ty`,
  REWRITE_TAC[holKernelProof_TERM_def; holKernelProof_TYPE_def; hol_term_ok_def]);;

let CKFAUX_inferred_mk_vartype = prove
 (ckfaux_inferred_goal `mk_vartype_v`,
  ckfaux_pure1_case mk_vartype_v_head mk_vartype_v_thm `x:mlstring` perms_ok_mk_vartype_v
   (REWRITE_TAC[holKernel_mk_vartype_def; holKernelProof_TYPE_def; type_ok_def]));;

let CKFAUX_inferred_mk_var = prove
 (ckfaux_inferred_goal `mk_var_v`,
  ckfaux_pure1_case mk_var_v_head mk_var_v_thm `p:mlstring#hol_type` perms_ok_mk_var_v
   (PAIR_CASES_ON `p:mlstring#hol_type` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
    ASM_REWRITE_TAC[holKernel_mk_var_def; CKFAUX_TERM_Var]));;

let CKFAUX_inferred_call_frees = prove
 (ckfaux_inferred_goal `call_frees_v`,
  ckfaux_pure1_case call_frees_v_head call_frees_v_thm `tm:hol_term` perms_ok_call_frees_v
   (REWRITE_TAC[call_frees_def; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tm:hol_term`; `x:hol_term`; `ctxt:update list`] MEM_frees) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CKFAUX_TERM_Var]));;

let CKFAUX_inferred_freesl = prove
 (ckfaux_inferred_goal `freesl_v`,
  ckfaux_pure1_case freesl_v_head freesl_v_thm `tms:hol_term list` perms_ok_freesl_v
   (REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tms:hol_term list`; `x:hol_term`; `ctxt:update list`] MEM_freesl) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CKFAUX_TERM_Var]));;

let CKFAUX_inferred_dest_thm = prove
 (ckfaux_inferred_goal `dest_thm_v`,
  ckfaux_pure1_case dest_thm_v_head dest_thm_v_thm `th:thm` perms_ok_dest_thm_v
   (ckfaux_state_tac THEN MATCH_MP_TAC dest_thm_thm THEN
    MAP_EVERY EXISTS_TAC [`th:thm`; `state:hol_refs`] THEN ASM_REWRITE_TAC[]));;

let CKFAUX_inferred_hyp = prove
 (ckfaux_inferred_goal `hyp_v`,
  ckfaux_pure1_case hyp_v_head hyp_v_thm `th:thm` perms_ok_hyp_v
   (ckfaux_state_tac THEN MATCH_MP_TAC hyp_thm THEN
    MAP_EVERY EXISTS_TAC [`th:thm`; `state:hol_refs`] THEN ASM_REWRITE_TAC[]));;
(* the absence of Clash failures, from a not_clash lemma of holKernelProof *)
let ckfaux_noclash_tac thl =
  X_GEN_TAC `t:hol_term` THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC thl;;

let CKFAUX_inferred_beta = prove
 (ckfaux_inferred_goal `beta_v`,
  ckfaux_monad1_case beta_v_head beta_v_thm `tm:hol_term` perms_ok_beta_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL BETA_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN ckfaux_noclash_tac[BETA_not_clash]));;

let CKFAUX_inferred_types = prove
 (ckfaux_inferred_goal `types_v`,
  ckfaux_monad1_case types_v_head types_v_thm `one` perms_ok_types_v
   (REWRITE_TAC[holKernel_types_def; holKernel_get_the_type_constants_def; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `M_success (hol_refs_the_type_constants refs):((mlstring#num)list,hol_exn)exc = r`);
      injectivity "exc"; distinctness "exc"; ALL_T]));;
let CKFAUX_inferred_constants = prove
 (ckfaux_inferred_goal `constants_v`,
  ckfaux_monad1_case constants_v_head constants_v_thm `one` perms_ok_constants_v
   (REWRITE_TAC[holKernel_constants_def; holKernel_get_the_term_constants_def; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP the_term_constants_TYPE) THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM]));;

let CKFAUX_inferred_axioms = prove
 (ckfaux_inferred_goal `axioms_v`,
  ckfaux_monad1_case axioms_v_head axioms_v_thm `one` perms_ok_axioms_v
   (REWRITE_TAC[holKernel_axioms_def; holKernel_get_the_axioms_def; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[the_axioms_THM]));;
(* the kernel functions without a not_clash lemma in holKernelProof *)
let CKFAUX_get_type_arity_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_get_type_arity a b = (M_failure (holKernel_Clash tm):(num,hol_exn)exc,refs))`,
  REWRITE_TAC[holKernel_get_type_arity_def; st_ex_bind_def;
              holKernel_get_the_type_constants_def] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[assoc_not_clash]);;

let CKFAUX_dest_vartype_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_dest_vartype a b = (M_failure (holKernel_Clash tm):(mlstring,hol_exn)exc,refs))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:hol_type` (CONJUNCT1 (cases "hol_type"))) THEN
  REWRITE_TAC[holKernel_dest_vartype_def; holKernel_raise_Failure_def; st_ex_return_def] THEN
  CAKE_REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "hol_exn";
                   distinctness "hol_exn"]);;

let CKFAUX_dest_const_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_dest_const a b =
       (M_failure (holKernel_Clash tm):(mlstring#hol_type,hol_exn)exc,refs))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[holKernel_dest_const_def; holKernel_raise_Failure_def; st_ex_return_def] THEN
  CAKE_REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "hol_exn";
                   distinctness "hol_exn"]);;

let CKFAUX_rand_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_rand a b = (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[holKernel_rand_def; holKernel_raise_Failure_def; st_ex_return_def] THEN
  CAKE_REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "hol_exn";
                   distinctness "hol_exn"]);;

let CKFAUX_rator_not_clash = prove
 (`!a b tm refs.
     ~(holKernel_rator a b = (M_failure (holKernel_Clash tm):(hol_term,hol_exn)exc,refs))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[holKernel_rator_def; holKernel_raise_Failure_def; st_ex_return_def] THEN
  CAKE_REWRITE_TAC[PAIR_EQ; injectivity "exc"; distinctness "exc"; injectivity "hol_exn";
                   distinctness "hol_exn"]);;
let CKFAUX_inferred_get_type_arity = prove
 (ckfaux_inferred_goal `get_type_arity_v`,
  ckfaux_monad1_case get_type_arity_v_head get_type_arity_v_thm `n:mlstring`
    perms_ok_get_type_arity_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL get_type_arity_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[CKFAUX_get_type_arity_not_clash]));;

let CKFAUX_inferred_mk_type = prove
 (ckfaux_inferred_goal `mk_type_v`,
  ckfaux_monad1_case mk_type_v_head mk_type_v_thm `p:mlstring#(hol_type)list` perms_ok_mk_type_v
   (PAIR_CASES_ON `p:mlstring#(hol_type)list` THEN RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL mk_type_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ckfaux_noclash_tac[mk_type_not_clash]]));;

let CKFAUX_inferred_dest_type = prove
 (ckfaux_inferred_goal `dest_type_v`,
  ckfaux_monad1_case dest_type_v_head dest_type_v_thm `ty:hol_type` perms_ok_dest_type_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL dest_type_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:mlstring#(hol_type)list`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[SND];
      ckfaux_noclash_tac[dest_type_not_clash]]));;

let CKFAUX_inferred_dest_vartype = prove
 (ckfaux_inferred_goal `dest_vartype_v`,
  ckfaux_monad1_case dest_vartype_v_head dest_vartype_v_thm `ty:hol_type`
    perms_ok_dest_vartype_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL dest_vartype_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[CKFAUX_dest_vartype_not_clash]));;

let CKFAUX_inferred_get_const_type = prove
 (ckfaux_inferred_goal `get_const_type_v`,
  ckfaux_monad1_case get_const_type_v_head get_const_type_v_thm `n:mlstring`
    perms_ok_get_const_type_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL get_const_type_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP the_term_constants_TYPE) THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `n:mlstring,x:hol_type`) THEN
      ASM_SIMP_TAC[];
      ckfaux_noclash_tac[get_const_type_not_clash]]));;

let CKFAUX_inferred_call_type_of = prove
 (ckfaux_inferred_goal `call_type_of_v`,
  ckfaux_monad1_case call_type_of_v_head call_type_of_v_thm `tm:hol_term`
    perms_ok_call_type_of_v
   (REWRITE_TAC[call_type_of_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `ctxt:update list`; `refs:hol_refs`] type_of_thm) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
    X_GEN_TAC `x:hol_type` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`ctxt:update list`; `tm:hol_term`] term_type) THEN
    ASM_MESON_TAC[holKernelProof_STATE_def]));;
let CKFAUX_inferred_mk_const = prove
 (ckfaux_inferred_goal `mk_const_v`,
  ckfaux_monad1_case mk_const_v_head mk_const_v_thm `p:mlstring#((hol_type#hol_type)list)`
    perms_ok_mk_const_v
   (PAIR_CASES_ON `p:mlstring#((hol_type#hol_type)list)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p0:mlstring`; `p1:(hol_type#hol_type)list`; `refs:hol_refs`;
                   `r:(hol_term,hol_exn)exc`; `refs2:hol_refs`; `ctxt:update list`]
             mk_const_thm) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `ALL (\p. holKernelProof_TYPE ctxt (FST p) /\
                            holKernelProof_TYPE ctxt (SND p)) (p1:(hol_type#hol_type)list)` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
      REWRITE_TAC[FORALL_PAIR_THM; FST; SND];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[mk_const_not_clash]));;

let CKFAUX_inferred_mk_abs = prove
 (ckfaux_inferred_goal `mk_abs_v`,
  ckfaux_monad1_case mk_abs_v_head mk_abs_v_thm `p:hol_term#hol_term` perms_ok_mk_abs_v
   (PAIR_CASES_ON `p:hol_term#hol_term` THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL mk_abs_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ckfaux_noclash_tac[mk_abs_not_clash]]));;

let CKFAUX_inferred_mk_comb = prove
 (ckfaux_inferred_goal `mk_comb_v`,
  ckfaux_monad1_case mk_comb_v_head mk_comb_v_thm `p:hol_term#hol_term` perms_ok_mk_comb_v
   (PAIR_CASES_ON `p:hol_term#hol_term` THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL mk_comb_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ckfaux_noclash_tac[mk_comb_not_clash]]));;

let CKFAUX_inferred_dest_var = prove
 (ckfaux_inferred_goal `dest_var_v`,
  ckfaux_monad1_case dest_var_v_head dest_var_v_thm `tm:hol_term` perms_ok_dest_var_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `refs2:hol_refs`;
                  `r:(mlstring#hol_type,hol_exn)exc`; `ctxt:update list`] dest_var_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_PAIR_THM; SND] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN ckfaux_noclash_tac[dest_var_not_clash]));;

let CKFAUX_inferred_dest_const = prove
 (ckfaux_inferred_goal `dest_const_v`,
  ckfaux_monad1_case dest_const_v_head dest_const_v_thm `tm:hol_term` perms_ok_dest_const_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `refs2:hol_refs`;
                  `r:(mlstring#hol_type,hol_exn)exc`; `ctxt:update list`]
             holKernelProof_dest_const_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_PAIR_THM; SND] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN ckfaux_noclash_tac[CKFAUX_dest_const_not_clash]));;

let CKFAUX_inferred_dest_comb = prove
 (ckfaux_inferred_goal `dest_comb_v`,
  ckfaux_monad1_case dest_comb_v_head dest_comb_v_thm `tm:hol_term` perms_ok_dest_comb_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `refs2:hol_refs`;
                  `r:(hol_term#hol_term,hol_exn)exc`; `ctxt:update list`] dest_comb_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN ckfaux_noclash_tac[dest_comb_not_clash]));;

let CKFAUX_inferred_dest_abs = prove
 (ckfaux_inferred_goal `dest_abs_v`,
  ckfaux_monad1_case dest_abs_v_head dest_abs_v_thm `tm:hol_term` perms_ok_dest_abs_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `refs2:hol_refs`;
                  `r:(hol_term#hol_term,hol_exn)exc`; `ctxt:update list`] dest_abs_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN ckfaux_noclash_tac[dest_abs_not_clash]));;

let CKFAUX_inferred_rand = prove
 (ckfaux_inferred_goal `rand_v`,
  ckfaux_monad1_case rand_v_head rand_v_thm `tm:hol_term` perms_ok_rand_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `refs2:hol_refs`;
                  `r:(hol_term,hol_exn)exc`; `ctxt:update list`] rand_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ckfaux_noclash_tac[CKFAUX_rand_not_clash]));;

let CKFAUX_inferred_rator = prove
 (ckfaux_inferred_goal `rator_v`,
  ckfaux_monad1_case rator_v_head rator_v_thm `tm:hol_term` perms_ok_rator_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `refs2:hol_refs`;
                  `r:(hol_term,hol_exn)exc`; `ctxt:update list`] rator_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ckfaux_noclash_tac[CKFAUX_rator_not_clash]));;

let CKFAUX_inferred_dest_eq = prove
 (ckfaux_inferred_goal `dest_eq_v`,
  ckfaux_monad1_case dest_eq_v_head dest_eq_v_thm `tm:hol_term` perms_ok_dest_eq_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL dest_eq_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN ckfaux_noclash_tac[dest_eq_not_clash]));;

let CKFAUX_inferred_refl = prove
 (ckfaux_inferred_goal `refl_v`,
  ckfaux_monad1_case refl_v_head refl_v_thm `tm:hol_term` perms_ok_refl_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`ctxt:update list`; `tm:hol_term`; `refs:hol_refs`;
                  `r:(thm,hol_exn)exc`; `refs2:hol_refs`] REFL_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ckfaux_noclash_tac[REFL_not_clash]));;

let CKFAUX_inferred_mk_comb_1 = prove
 (ckfaux_inferred_goal `mk_comb_1_v`,
  ckfaux_monad1_case mk_comb_1_v_head mk_comb_1_v_thm `p:thm#thm` perms_ok_mk_comb_1_v
   (PAIR_CASES_ON `p:thm#thm` THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL MK_COMB_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[MK_COMB_not_clash]));;

let CKFAUX_inferred_assume = prove
 (ckfaux_inferred_goal `assume_v`,
  ckfaux_monad1_case assume_v_head assume_v_thm `tm:hol_term` perms_ok_assume_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL ASSUME_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[ASSUME_not_clash]));;
(* the side condition of a monadic kernel function that may extend the     *)
(* context (new_type, new_constant, new_axiom, the definitions)              *)
let CKFAUX_monad_side_ext = prove
 (mk_imp(`!refs r refs2. holKernelProof_STATE ctxt refs /\
            (f:A->hol_refs->(B,hol_exn)exc#hol_refs) a refs = (r,refs2) ==>
            (!t. ~(r = M_failure (holKernel_Clash t))) /\
            (!e. r = M_failure e ==> refs2 = refs) /\
            (!x. r = M_success x ==>
                 ?ds. holKernelProof_STATE (APPEND ds ctxt) refs2 /\
                      (!th. holKernelProof_THM ctxt th ==>
                            holKernelProof_THM (APPEND ds ctxt) th) /\
                      (!rv. (B:B->v->bool) x rv ==> candle_v_ok (APPEND ds ctxt) rv))`,
          ckfaux_monad_side),
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`refs:hol_refs`; `r:(B,hol_exn)exc`; `refs2:hol_refs`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `y:B` SUBST_ALL_TAC) (X_CHOOSE_THEN `y:hol_exn` SUBST_ALL_TAC)
    (ISPEC `r:(B,hol_exn)exc` (cases "exc")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"; distinctness "exc"; FORALL_UNWIND_THM1;
    FORALL_UNWIND_THM2]) THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `ds:update list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `APPEND ds ctxt:update list` THEN
    ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"; FORALL_UNWIND_THM1;
      FORALL_UNWIND_THM2] THEN
    ASM_MESON_TAC[v_ok_APPEND; ref_ok_APPEND];
    EXISTS_TAC `ctxt:update list` THEN ASM_REWRITE_TAC[distinctness "exc"] THEN
    MP_TAC(ISPECL [`M_failure y:(B,hol_exn)exc`; `ctxt:update list`] CKFAUX_failure_ok) THEN
    ASM_REWRITE_TAC[injectivity "exc"]]);;
(* the monadic one-argument kernel functions that may extend the context *)
let ckfaux_monad1_ext_case head cert a perms_th spec_tac =
  ckfaux_head_tac head THEN ckfaux_typed_tac a THEN
  MP_TAC(ckfaux_drive CKFAUX_monad1_ok cert a) THEN
  ASM_REWRITE_TAC[perms_th] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ckfaux_arg_perms_tac; MATCH_MP_TAC CKFAUX_monad_side_ext THEN spec_tac];;

(* the result r of a kernel function, split into success and failure *)
let ckfaux_exc_cases_tac r ty_s =
  DISJ_CASES_THEN2 (X_CHOOSE_THEN (mk_var("y",ty_s)) SUBST_ALL_TAC)
                   (X_CHOOSE_THEN `e:hol_exn` SUBST_ALL_TAC)
    (ISPEC r (cases "exc"));;

let CKFAUX_inferred_new_axiom = prove
 (ckfaux_inferred_goal `new_axiom_v`,
  ckfaux_monad1_ext_case new_axiom_v_head new_axiom_v_thm `tm:hol_term` perms_ok_new_axiom_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `ctxt:update list`] new_axiom_thm) THEN
    ASM_REWRITE_TAC[] THEN ckfaux_exc_cases_tac `r:(thm,hol_exn)exc` `:thm` THEN
    CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THENL
     [DISCH_THEN(X_CHOOSE_THEN `d:update` STRIP_ASSUME_TAC) THEN
      X_GEN_TAC `x:thm` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      EXISTS_TAC `[d:update]` THEN ASM_REWRITE_TAC[APPEND] THEN
      ASM_MESON_TAC[THM_IMP_v_ok];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[new_axiom_not_clash]]));;

let CKFAUX_inferred_new_basic_definition = prove
 (ckfaux_inferred_goal `new_basic_definition_v`,
  ckfaux_monad1_ext_case new_basic_definition_v_head new_basic_definition_v_thm `tm:hol_term`
    perms_ok_new_basic_definition_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tm:hol_term`; `refs:hol_refs`; `ctxt:update list`]
             new_basic_definition_thm) THEN
    ASM_REWRITE_TAC[] THEN ckfaux_exc_cases_tac `r:(thm,hol_exn)exc` `:thm` THEN
    CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THENL
     [DISCH_THEN(X_CHOOSE_THEN `d:update` STRIP_ASSUME_TAC) THEN
      X_GEN_TAC `x:thm` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      EXISTS_TAC `[d:update]` THEN ASM_REWRITE_TAC[APPEND] THEN
      ASM_MESON_TAC[THM_IMP_v_ok];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ckfaux_noclash_tac[new_basic_definition_not_clash]]));;

let CKFAUX_inferred_new_specification = prove
 (ckfaux_inferred_goal `new_specification_v`,
  ckfaux_monad1_ext_case new_specification_v_head new_specification_v_thm `th:thm`
    perms_ok_new_specification_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`th:thm`; `refs:hol_refs`; `ctxt:update list`]
             new_specification_thm) THEN
    ASM_REWRITE_TAC[] THEN ckfaux_exc_cases_tac `r:(thm,hol_exn)exc` `:thm` THEN
    CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THENL
     [DISCH_THEN(X_CHOOSE_THEN `d:update` STRIP_ASSUME_TAC) THEN
      X_GEN_TAC `x:thm` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      EXISTS_TAC `[d:update]` THEN ASM_REWRITE_TAC[APPEND] THEN
      ASM_MESON_TAC[THM_IMP_v_ok];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ckfaux_noclash_tac[new_specification_not_clash]]));;

let CKFAUX_inferred_new_constant = prove
 (ckfaux_inferred_goal `new_constant_v`,
  ckfaux_monad1_ext_case new_constant_v_head new_constant_v_thm `p:mlstring#hol_type`
    perms_ok_new_constant_v
   (PAIR_CASES_ON `p:mlstring#hol_type` THEN RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p0:mlstring`; `p1:hol_type`; `refs:hol_refs`; `ctxt:update list`]
             new_constant_thm) THEN
    ASM_REWRITE_TAC[] THEN ckfaux_exc_cases_tac `r:(1,hol_exn)exc` `:1` THEN
    CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THENL
     [DISCH_THEN(X_CHOOSE_THEN `d:update` STRIP_ASSUME_TAC) THEN
      X_GEN_TAC `x:1` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      EXISTS_TAC `[d:update]` THEN ASM_REWRITE_TAC[APPEND] THEN
      MESON_TAC[CKFAUX_UNIT_TYPE_v_ok];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ckfaux_noclash_tac[new_constant_not_clash]]));;
let CKFAUX_inferred_call_new_type = prove
 (ckfaux_inferred_goal `call_new_type_v`,
  ckfaux_monad1_ext_case call_new_type_v_head call_new_type_v_thm `p:mlstring#int`
    perms_ok_call_new_type_v
   (PAIR_CASES_ON `p:mlstring#int` THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[call_new_type_def] THEN COND_CASES_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(SPECL [`p0:mlstring`; `num_of_int (abs p1)`; `refs:hol_refs`; `ctxt:update list`]
               new_type_thm) THEN
      ASM_REWRITE_TAC[] THEN ckfaux_exc_cases_tac `r:(1,hol_exn)exc` `:1` THEN
      CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THENL
       [DISCH_THEN(X_CHOOSE_THEN `d:update` STRIP_ASSUME_TAC) THEN
        X_GEN_TAC `x:1` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        EXISTS_TAC `[d:update]` THEN ASM_REWRITE_TAC[APPEND] THEN
        MESON_TAC[CKFAUX_UNIT_TYPE_v_ok];
        DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[new_type_not_clash]];
      REWRITE_TAC[holKernel_raise_Failure_def; PAIR_EQ] THEN STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
      REWRITE_TAC[injectivity "exc"; distinctness "exc"; distinctness "hol_exn"]]));;

let CKFAUX_inferred_new_basic_type_definition = prove
 (ckfaux_inferred_goal `new_basic_type_definition_v`,
  ckfaux_monad1_ext_case new_basic_type_definition_v_head new_basic_type_definition_v_thm
    `p:mlstring#mlstring#mlstring#thm` perms_ok_new_basic_type_definition_v
   (PAIR_CASES_ON `p:mlstring#mlstring#mlstring#thm` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p0:mlstring`; `p1:mlstring`; `p2:mlstring`; `p3:thm`; `refs:hol_refs`;
                  `ctxt:update list`] new_basic_type_definition_thm) THEN
    ASM_REWRITE_TAC[] THEN ckfaux_exc_cases_tac `r:(thm#thm,hol_exn)exc` `:thm#thm` THEN
    PAIR_CASES_ON `y:thm#thm` THEN
    CAKE_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THENL
     [DISCH_THEN(X_CHOOSE_THEN `ds:update list` STRIP_ASSUME_TAC) THEN
      X_GEN_TAC `x:thm#thm` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      EXISTS_TAC `ds:update list` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(INST [`APPEND ds ctxt:update list`,`ctxt:update list`]
               (snd(ckfaux_vok `PAIR_TYPE THM_TYPE THM_TYPE`))) THEN
      DISCH_THEN(MP_TAC o SPEC `(y0:thm,y1:thm)`) THEN
      ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ckfaux_noclash_tac[new_basic_type_definition_not_clash]]));;
(* the two-argument kernel functions: an application to one argument is a *)
(* partial application, a kernel value                                      *)
let CKFAUX_inferred_partial = prove
 (mk_imp(`f IN kernel_funs /\ f = Closure env1 n (Fun m e)`, ckfaux_inferred_goal `f:v`),
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  REWRITE_TAC[do_opapp_clos] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    fst(dest_var(rhs(concl th))) = "exp")) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl) o
    check (can (find_term (fun t -> try fst(dest_const t) = "evaluate" with _ -> false)) o concl)) THEN
  REWRITE_TAC[CKFAUX_evaluate_Fun; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)) &&
    mem (fst(dest_var(rhs(concl th)))) ["s'"; "res"]))) THEN
  DISJ2_TAC THEN EXISTS_TAC `ctxt:update list` THEN
  ASM_REWRITE_TAC[ALL; injectivity "result"; distinctness "result"; CONS_11] THEN
  SIMP[ALL] THEN MATCH_MP_TAC candle_v_ok_KernelVals THEN
  MATCH_MP_TAC candle_v_ok_PartialApp THEN
  MAP_EVERY EXISTS_TAC [`Closure env1 n (Fun m e)`; `v:v`] THEN
  ASM_REWRITE_TAC[do_partial_app_clos] THEN
  ASM_MESON_TAC[candle_v_ok_Inferred; candle_inferred_KernelFuns]);;

(* ------------------------------------------------------------------------- *)
(* print_thm: HOL4's stepwise evaluation of the closure body, here one     *)
(* evaluation lemma per Let (dereference, thm_to_string, Word8.fromInt,    *)
(* Word8Array.array, the FFI call)                                          *)
(* ------------------------------------------------------------------------- *)

let CKFAUX_store_lookup_oEL = prove
 (`!n (st:(A store_v)list). store_lookup n st = oEL n st`,
  REWRITE_TAC[store_lookup_def; oEL_THM]);;

(* evaluation of a dereference of a variable *)
let CKFAUX_evaluate_Opderef = prove
 (`nsLookup (sem_env_v env) (Short x) = SOME (Loc b n) /\
   oEL n (state_refs (s:(FFI)state)) = SOME (Refv v) ==>
   evaluate s env [App Opderef [Var (Short x)]] = (s,Rval [v])`,
  STRIP_TAC THEN ONCE_REWRITE_TAC[evaluate_def] THEN REWRITE_TAC[REVERSE; APPEND] THEN
  ONCE_REWRITE_TAC[evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[getOpClass_def] THEN
  REWRITE_TAC[REVERSE; APPEND; do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[CKFAUX_store_lookup_oEL] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[list_result_def] THEN
  REWRITE_TAC[state_component_equality] THEN SIMP[]);;

let ckfaux_deref_v_def = (try tr_fetch "deref_v_def" with _ -> ml_prog_fetch "deref_v_def");;

(* !the_context: the kernel's context *)
let CKFAUX_evaluate_deref = prove
 (`nsLookup (sem_env_v env) (Short (implode "!")) = SOME deref_v /\
   nsLookup (sem_env_v env) (Short (implode "the_context")) = SOME (Loc T n) /\
   oEL n (state_refs (s:(FFI)state)) = SOME (Refv cv) ==>
   evaluate s env [App Opapp [Var (Short (implode "!")); Var (Short (implode "the_context"))]] =
   if state_clock s = 0 then (s,Rerr (Rabort Rtimeout_error)) else (dec_clock s,Rval [cv])`,
  STRIP_TAC THEN ASM_REWRITE_TAC[CAN2AAUX_evaluate_Opapp_vars] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ckfaux_deref_v_def; do_opapp_def] THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (GEN_ALL CKFAUX_evaluate_Opderef) THEN EXISTS_TAC `T` THEN
  ASM_REWRITE_TAC[dec_clock_def] THEN SIMP[nsLookup_nsBind_compute]);;

let CKFAUX_evaluate_two = prove
 (`evaluate (s:(FFI)state) env [e2] = (s1,Rval [v2]) /\ evaluate s1 env [e1] = (s2,r) ==>
   evaluate s env [e2; e1] =
   (s2, match r with Rval vs -> Rval (CONS v2 vs) | Rerr err -> Rerr err)`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_cons] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[APPEND] THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `r:(v list,v)result` (cases "result")) THEN
  CAKE_REWRITE_TAC[APPEND]);;

(* evaluation of App Opapp [e1; e2] when both arguments give values *)
let CKFAUX_evaluate_Opapp2 = prove
 (CASE_TERM
  `evaluate (s:(FFI)state) env [e2] = (s1,Rval [v2]) /\ evaluate s1 env [e1] = (s2,Rval [v1]) ==>
   evaluate s env [App Opapp [e1; e2]] =
   match do_opapp [v1; v2] with
     NONE -> (s2,Rerr (Rabort Rtype_error))
   | SOME (env',e) -> if state_clock s2 = 0 then (s2,Rerr (Rabort Rtimeout_error))
                      else evaluate (dec_clock s2) env' [e]`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 -> REWRITE_TAC[MATCH_MP CKFAUX_evaluate_two (CONJ th th2)])) THEN
  CAKE_REWRITE_TAC[getOpClass_def; APPEND; REVERSE]);;

(* the first argument raises *)
let CKFAUX_evaluate_Opapp2_err1 = prove
 (`evaluate (s:(FFI)state) env [e2] = (s1,Rval [v2]) /\ evaluate s1 env [e1] = (s2,Rerr err) ==>
   evaluate s env [App Opapp [e1; e2]] = (s2,Rerr err)`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 -> REWRITE_TAC[MATCH_MP CKFAUX_evaluate_two (CONJ th th2)])) THEN
  CAKE_REWRITE_TAC[]);;

let CKFAUX_evaluate_Var = prove
 (`nsLookup (sem_env_v env) n = SOME x ==> evaluate (s:(FFI)state) env [Var n] = (s,Rval [x])`,
  SIMP[evaluate_def]);;

let CKFAUX_evaluate_Lit = prove
 (`evaluate (s:(FFI)state) env [Lit l] = (s,Rval [Litv l])`,
  REWRITE_TAC[evaluate_def]);;

(* the closure of a two-argument kernel function applied to one argument *)
let CKFAUX_partial_exists = prove
 (`!f v. (?env n m e. f = Closure env n (Fun m e)) ==> ?g. do_partial_app f v = SOME g`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[do_partial_app_def] THEN CAKE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let CKFAUX_evaluate_dec_clock = prove
 (`state_ffi (dec_clock (s:(FFI)state)) = state_ffi s /\
   state_refs (dec_clock s) = state_refs s /\
   state_eval_state (dec_clock s) = state_eval_state s /\
   state_next_type_stamp (dec_clock s) = state_next_type_stamp s`,
  SIMP[dec_clock_def]);;

(* thm_to_string ctxt th in print_thm (the certificate by Arrow2) *)
let CKFAUX_evaluate_thm_to_string = prove
 (`nsLookup (sem_env_v env) (Short (implode "thm_to_string")) = SOME thm_to_string_v /\
   nsLookup (sem_env_v env) (Short (implode "ctxt")) = SOME cv /\
   nsLookup (sem_env_v env) (Short (implode "th")) = SOME v /\
   LIST_TYPE UPDATE_TYPE c cv /\ THM_TYPE th v /\ perms_ok {} cv /\ perms_ok {} v /\
   evaluate (s:(FFI)state) env
     [App Opapp [App Opapp [Var (Short (implode "thm_to_string"));
                            Var (Short (implode "ctxt"))];
                 Var (Short (implode "th"))]] = (s1,r1) ==>
   state_ffi s1 = state_ffi s /\
   (r1 = Rerr (Rabort Rtimeout_error) \/ r1 = Rerr (Rabort Rtype_error) \/
    state_refs s1 = state_refs s /\ state_eval_state s1 = state_eval_state s /\
    state_next_type_stamp s1 = state_next_type_stamp s /\
    ?strv. r1 = Rval [strv] /\ STRING_TYPE (thm_to_string c th) strv)`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`thm_to_string_v`; `cv:v`] CKFAUX_partial_exists) THEN
  ANTS_TAC THENL [REWRITE_TAC[thm_to_string_v_def] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:v`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CKFAUX_do_partial_app_opapp) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`env0:v sem_env`; `x0:mlstring`; `e0:exp`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `evaluate (s:(FFI)state) env
     [App Opapp [Var (Short (implode "thm_to_string")); Var (Short (implode "ctxt"))]] =
     if state_clock s = 0 then (s,Rerr (Rabort Rtimeout_error)) else (dec_clock s,Rval [g])`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CAN2AAUX_evaluate_Opapp_vars] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[CKFAUX_evaluate_Fun];
    ALL_TAC] THEN
  SUBGOAL_THEN `evaluate (s:(FFI)state) env [Var (Short (implode "th"))] = (s,Rval [v])`
    ASSUME_TAC THENL [ASM_SIMP_TAC[CKFAUX_evaluate_Var]; ALL_TAC] THEN
  ASM_CASES_TAC `state_clock (s:(FFI)state) = 0` THENL
   [MP_TAC(INST [`s:(FFI)state`,`s1:(FFI)state`; `s:(FFI)state`,`s2:(FFI)state`;
                 `Rabort Rtimeout_error:v error_result`,`err:v error_result`;
                 `Var (Short (implode "th"))`,`e2:exp`; `v:v`,`v2:v`;
                 `App Opapp [Var (Short (implode "thm_to_string")); Var (Short (implode "ctxt"))]`,
                 `e1:exp`] CKFAUX_evaluate_Opapp2_err1) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`s:(FFI)state`,`s1:(FFI)state`; `dec_clock (s:(FFI)state)`,`s2:(FFI)state`;
               `Var (Short (implode "th"))`,`e2:exp`; `v:v`,`v2:v`; `g:v`,`v1:v`;
               `App Opapp [Var (Short (implode "thm_to_string")); Var (Short (implode "ctxt"))]`,
               `e1:exp`] CKFAUX_evaluate_Opapp2) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[do_opapp_def] THEN CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[CKFAUX_evaluate_dec_clock];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(INST [`LIST_TYPE UPDATE_TYPE`,`A:(update)list->v->bool`; `THM_TYPE`,`B:thm->v->bool`;
               `STRING_TYPE`,`C:mlstring->v->bool`; `thm_to_string`,`f:(update)list->thm->mlstring`;
               `thm_to_string_v`,`fv:v`; `cv:v`,`av:v`; `g:v`,`gv:v`; `v:v`,`bv:v`;
               `sem_env_v_fupd (combin_K (nsBind x0 (v:v) (sem_env_v (env0:v sem_env)))) env0`,
               `env:v sem_env`;
               `e0:exp`,`exp:exp`; `dec_clock (dec_clock (s:(FFI)state))`,`s:(FFI)state`;
               `s1:(FFI)state`,`s':(FFI)state`; `r1:(v list,v)result`,`res:(v list,v)result`;
               `c:update list`,`a:update list`; `th:thm`,`b:thm`]
    (INST_TYPE [`:update list`,`:A`; `:thm`,`:B`; `:mlstring`,`:C`] candle_Arrow2)) THEN
  ASM_REWRITE_TAC[thm_to_string_v_thm; perms_ok_thm_to_string_v; do_opapp_def] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[CKFAUX_evaluate_dec_clock] THEN MESON_TAC[]);;

let CKFAUX_do_opapp_Closure = prove
 (`!env n e (x:v). do_opapp [Closure env n e; x] =
                   SOME (sem_env_v_fupd (combin_K (nsBind n x (sem_env_v env))) env,e)`,
  REWRITE_TAC[do_opapp_def] THEN CAKE_REWRITE_TAC[]);;

(* |- !x. do_opapp [c; x] = SOME (env', e) for a closure constant c *)
let ckfaux_opapp_closure_thm v_def =
  let c = lhs(concl v_def) in
  let _,args = strip_comb(rhs(concl v_def)) in
  let th = ISPECL args CKFAUX_do_opapp_Closure in
  GEN_REWRITE_RULE (BINDER_CONV o LAND_CONV o RAND_CONV o LAND_CONV) [SYM v_def] th;;

let ckfaux_word8_fromint_v_def = (try tr_fetch "word8_fromint_v_def" with _ -> ml_prog_fetch "word8_fromint_v_def");;
let ckfaux_word8_fromint_v_thm = (try tr_fetch "word8_fromint_v_thm" with _ -> ml_prog_fetch "word8_fromint_v_thm");;

(* Word8.fromInt 0 in print_thm (the certificate by Arrow1) *)
let CKFAUX_evaluate_fromInt = prove
 (`nsLookup (sem_env_v env) (Long (implode "Word8") (Short (implode "fromInt"))) =
     SOME word8_fromint_v /\
   evaluate (s:(FFI)state) env
     [App Opapp [Var (Long (implode "Word8") (Short (implode "fromInt"))); Lit (IntLit (&0))]] =
     (s1,r1) ==>
   state_ffi s1 = state_ffi s /\
   (r1 = Rerr (Rabort Rtimeout_error) \/ r1 = Rerr (Rabort Rtype_error) \/
    state_refs s1 = state_refs s /\ state_eval_state s1 = state_eval_state s /\
    state_next_type_stamp s1 = state_next_type_stamp s /\
    ?w. r1 = Rval [w] /\ ml_WORD (word 0:byte) w)`,
  STRIP_TAC THEN
  MP_TAC(INST [`s:(FFI)state`,`s1:(FFI)state`; `s:(FFI)state`,`s2:(FFI)state`;
               `Lit (IntLit (&0))`,`e2:exp`; `Litv (IntLit (&0))`,`v2:v`;
               `word8_fromint_v`,`v1:v`;
               `Var (Long (implode "Word8") (Short (implode "fromInt")))`,`e1:exp`]
    CKFAUX_evaluate_Opapp2) THEN
  ASM_SIMP_TAC[CKFAUX_evaluate_Lit; CKFAUX_evaluate_Var;
               ckfaux_opapp_closure_thm ckfaux_word8_fromint_v_def] THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  let oth = SPEC `Litv (IntLit (&0))` (ckfaux_opapp_closure_thm ckfaux_word8_fromint_v_def) in
  let envx,expx = dest_pair(rand(rhs(concl oth))) in
  MP_TAC(INST [`ml_NUM`,`A:num->v->bool`; `ml_WORD:byte->v->bool`,`B:byte->v->bool`;
               `word:num->byte`,`f:num->byte`; `word8_fromint_v`,`fv:v`;
               `Litv (IntLit (&0))`,`av:v`; `dec_clock (s:(FFI)state)`,`s:(FFI)state`;
               `s1:(FFI)state`,`s':(FFI)state`; `r1:(v list,v)result`,`res:(v list,v)result`;
               `0`,`a:num`; envx,`env:v sem_env`; expx,`exp:exp`]
    (INST_TYPE [`:num`,`:A`; `:byte`,`:B`] candle_Arrow1)) THEN
  ASM_REWRITE_TAC[ckfaux_word8_fromint_v_thm; perms_ok_word8_fromint_v; perms_ok_Litv;
    ckfaux_opapp_closure_thm ckfaux_word8_fromint_v_def; ml_NUM_def; ml_INT_def] THEN
  REWRITE_TAC[CKFAUX_evaluate_dec_clock] THEN MESON_TAC[]);;

let ckfaux_Word8Array_array_v_def =
  (try tr_fetch "Word8Array_array_v_def" with _ -> ml_prog_fetch "Word8Array_array_v_def");;

(* the allocation of an empty byte array *)
let CKFAUX_evaluate_Aw8alloc = prove
 (`nsLookup (sem_env_v env) (Short x) = SOME (Litv (IntLit (&0))) /\
   nsLookup (sem_env_v env) (Short y) = SOME (Litv (Word8 b)) ==>
   evaluate (s:(FFI)state) env [App Aw8alloc [Var (Short x); Var (Short y)]] =
   (state_refs_fupd (combin_K (APPEND (state_refs s) [W8array []])) s,
    Rval [Loc T (LENGTH (state_refs s))])`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN
  MP_TAC(INST [`Var (Short x)`,`e1:exp`; `Var (Short y)`,`e2:exp`; `s:(FFI)state`,`s1:(FFI)state`;
               `s:(FFI)state`,`s2:(FFI)state`; `Litv (Word8 b)`,`v2:v`;
               `Rval [Litv (IntLit (&0))]:(v list,v)result`,`r:(v list,v)result`]
    CKFAUX_evaluate_two) THEN
  ASM_SIMP_TAC[CKFAUX_evaluate_Var] THEN DISCH_THEN SUBST1_TAC THEN
  CAKE_REWRITE_TAC[getOpClass_def; REVERSE; APPEND] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_LT_REFL; I_THM; INT_ABS_NUM; NUM_OF_INT_OF_NUM; REPLICATE;
              store_alloc_def] THEN
  CAKE_REWRITE_TAC[list_result_def] THEN
  REWRITE_TAC[PAIR_EQ; state_component_equality] THEN SIMP[]);;

(* Word8Array.array 0 v0 in print_thm *)
let CKFAUX_evaluate_array =
  let ath = SPEC `Litv (IntLit (&0))` (ckfaux_opapp_closure_thm ckfaux_Word8Array_array_v_def) in
  let e1,fe = dest_pair(rand(rhs(concl ath))) in
  let y,body = match strip_comb fe with _,[y;b] -> y,b | _ -> failwith "array" in
  let clo = list_mk_comb(`Closure`,[e1;y;body]) in
  prove
 (`nsLookup (sem_env_v env) (Long (implode "Word8Array") (Short (implode "array"))) =
     SOME Word8Array_array_v /\
   nsLookup (sem_env_v env) (Short (implode " v0")) = SOME (Litv (Word8 b)) ==>
   evaluate (s:(FFI)state) env
     [App Opapp [App Opapp [Var (Long (implode "Word8Array") (Short (implode "array")));
                            Lit (IntLit (&0))];
                 Var (Short (implode " v0"))]] =
   if state_clock s = 0 then (s,Rerr (Rabort Rtimeout_error))
   else if state_clock (dec_clock s) = 0 then (dec_clock s,Rerr (Rabort Rtimeout_error))
   else (state_refs_fupd (combin_K (APPEND (state_refs s) [W8array []])) (dec_clock (dec_clock s)),
         Rval [Loc T (LENGTH (state_refs s))])`,
  STRIP_TAC THEN
  SUBGOAL_THEN
   (mk_eq(`evaluate (s:(FFI)state) env
             [App Opapp [Var (Long (implode "Word8Array") (Short (implode "array")));
                         Lit (IntLit (&0))]]`,
          mk_cond(`state_clock (s:(FFI)state) = 0`, `(s:(FFI)state,Rerr (Rabort Rtimeout_error):(v list,v)result)`,
                  mk_pair(`dec_clock (s:(FFI)state)`,
                          mk_comb(`Rval:(v)list->(v list,v)result`,
                                  mk_list([clo],`:v`))))))
    ASSUME_TAC THENL
   [MP_TAC(INST [`s:(FFI)state`,`s1:(FFI)state`; `s:(FFI)state`,`s2:(FFI)state`;
                 `Lit (IntLit (&0))`,`e2:exp`; `Litv (IntLit (&0))`,`v2:v`;
                 `Word8Array_array_v`,`v1:v`;
                 `Var (Long (implode "Word8Array") (Short (implode "array")))`,`e1:exp`]
      CKFAUX_evaluate_Opapp2) THEN
    ASM_SIMP_TAC[CKFAUX_evaluate_Lit; CKFAUX_evaluate_Var] THEN
    REWRITE_TAC[ath] THEN CAKE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[CKFAUX_evaluate_Fun];
    ALL_TAC] THEN
  ASM_CASES_TAC `state_clock (s:(FFI)state) = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(INST [`s:(FFI)state`,`s1:(FFI)state`; `s:(FFI)state`,`s2:(FFI)state`;
                 `Rabort Rtimeout_error:v error_result`,`err:v error_result`;
                 `Var (Short (implode " v0"))`,`e2:exp`; `Litv (Word8 b)`,`v2:v`;
                 `App Opapp [Var (Long (implode "Word8Array") (Short (implode "array")));
                             Lit (IntLit (&0))]`,`e1:exp`] CKFAUX_evaluate_Opapp2_err1) THEN
    ASM_SIMP_TAC[CKFAUX_evaluate_Var];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(INST [`s:(FFI)state`,`s1:(FFI)state`; `dec_clock (s:(FFI)state)`,`s2:(FFI)state`;
               `Var (Short (implode " v0"))`,`e2:exp`; `Litv (Word8 b)`,`v2:v`; clo,`v1:v`;
               `App Opapp [Var (Long (implode "Word8Array") (Short (implode "array")));
                           Lit (IntLit (&0))]`,`e1:exp`]
    CKFAUX_evaluate_Opapp2) THEN
  ASM_SIMP_TAC[CKFAUX_evaluate_Var] THEN
  REWRITE_TAC[CKFAUX_do_opapp_Closure] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY(DISCH_THEN(K ALL_TAC)) THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) CKFAUX_evaluate_Aw8alloc (lhs w))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN CONV_TAC can2aaux_lookup_conv; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CKFAUX_evaluate_dec_clock]);;

(* the call of the kernel's FFI channel *)
let CKFAUX_evaluate_ffi = prove
 (CASE_TERM
  `nsLookup (sem_env_v env) (Short (implode "str")) = SOME (Litv (StrLit conf)) /\
   nsLookup (sem_env_v env) (Short (implode "arr")) = SOME (Loc T n) /\
   oEL n (state_refs (s:(FFI)state)) = SOME (W8array []) ==>
   evaluate s env [App (FFI (implode "kernel_ffi"))
                     [Var (Short (implode "str")); Var (Short (implode "arr"))]] =
   match call_FFI (state_ffi s) (ExtCall (implode "kernel_ffi"))
           (MAP (word o ORD) (explode conf)) [] with
     FFI_return t' ws' ->
       (state_refs_fupd (combin_K (LUPDATE (W8array ws') n (state_refs s))) (state_ffi_fupd (combin_K t') s),
        Rval [Conv NONE []])
   | FFI_final outcome -> (s,Rerr (Rabort (Rffi_error outcome)))`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN
  MP_TAC(INST [`Var (Short (implode "str"))`,`e1:exp`; `Var (Short (implode "arr"))`,`e2:exp`;
               `s:(FFI)state`,`s1:(FFI)state`; `s:(FFI)state`,`s2:(FFI)state`;
               `Loc T n`,`v2:v`;
               `Rval [Litv (StrLit conf)]:(v list,v)result`,`r:(v list,v)result`]
    CKFAUX_evaluate_two) THEN
  ASM_SIMP_TAC[CKFAUX_evaluate_Var] THEN DISCH_THEN SUBST1_TAC THEN
  CAKE_REWRITE_TAC[getOpClass_def; REVERSE; APPEND] THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[CKFAUX_store_lookup_oEL] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  UNDISCH_TAC `oEL n (state_refs (s:(FFI)state)) = SOME (W8array [])` THEN
  REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `call_FFI (state_ffi (s:(FFI)state)) (ExtCall (implode "kernel_ffi"))
             (MAP (word o ORD) (explode conf)) []` (cases "ffi_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[list_result_def] THEN
  ASM_REWRITE_TAC[store_assign_def] THEN
  REWRITE_TAC[GSYM(ASSUME `W8array [] = EL n (state_refs (s:(FFI)state))`)] THEN
  REWRITE_TAC[store_v_same_type_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[state_component_equality] THEN SIMP[]);;

(* the event of print_thm is an ok_event *)
let CKFAUX_print_ok_event = prove
 (`holKernelProof_STATE ctxt state /\ holKernelProof_THM ctxt th ==>
   ok_event (IO_event (ExtCall (implode "kernel_ffi"))
              (MAP (word o ORD) (explode (thm_to_string (hol_refs_the_context state) th))) bs)`,
  REWRITE_TAC[holKernelProof_STATE_def; ok_event_def; kernel_ffi_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "ctxt")) THEN
  MAP_EVERY EXISTS_TAC [`ctxt:update list`; `th:thm`] THEN
  ASM_REWRITE_TAC[GSYM holKernelProof_CONTEXT_def; thm2bytes_def; MAP_o]);;


let CKFAUX_oEL_APPEND1 = prove
 (`!n l (x:A). oEL n (APPEND l [x]) =
     if n < LENGTH l then oEL n l else if n = LENGTH l then SOME x else NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oEL_THM; LENGTH_APPEND; LENGTH] THEN
  ASM_CASES_TAC `n < LENGTH (l:A list)` THEN ASM_SIMP_TAC[EL_APPEND1; ARITH_RULE `a < b ==> a < b + 1`] THEN
  ASM_CASES_TAC `n = LENGTH (l:A list)` THEN
  ASM_SIMP_TAC[EL_APPEND2; LE_REFL; SUB_REFL; EL; HD; ARITH_RULE `n < n + 1`] THEN
  ASM_ARITH_TAC);;

(* the state after print_thm: the new byte array, then an ok FFI event *)
let CKFAUX_print_state_ok = prove
 (`candle_state_ok ctxt (s:(FFI)state) /\
   state_refs s1 = state_refs s /\ state_eval_state s1 = state_eval_state s /\
   state_next_type_stamp s1 = state_next_type_stamp s /\
   ALL ok_event (ffi_state_io_events t') ==>
   candle_state_ok ctxt
     (state_refs_fupd (combin_K (LUPDATE (W8array ws) (LENGTH (state_refs s))
                                  (APPEND (state_refs s) [W8array []])))
        (state_ffi_fupd (combin_K t') (s1:(FFI)state)))`,
  REWRITE_TAC[candle_state_ok_def] THEN SIMP[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `state:hol_refs` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CKFAUX_oEL_APPEND1] THEN CONJ_TAC THENL
   [X_GEN_TAC `loc:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `loc < LENGTH (state_refs (s:(FFI)state))` ASSUME_TAC THENL
     [ASM_MESON_TAC[kernel_loc_ok_LENGTH]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `loc:num` o check (is_forall o concl) o
      check (can (find_term (fun t -> try fst(dest_const t) = "candle_kernel_loc_ok"
                                      with _ -> false)) o concl)) THEN
    ASM_REWRITE_TAC[candle_kernel_loc_ok_def; CKFAUX_oEL_APPEND1];
    MAP_EVERY X_GEN_TAC [`loc:num`; `r:(v)store_v`] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[candle_ref_ok_def]]);;

let CKFAUX_evaluate_Let_val = prove
 (`evaluate (s:(FFI)state) env [e1] = (s1,Rval [x]) ==>
   evaluate s env [Let (SOME n) e1 e2] =
   evaluate s1 (sem_env_v_fupd (combin_K (nsBind n x (sem_env_v env))) env) [e2]`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[nsOptBind_def; HD]);;

let CKFAUX_evaluate_Let_err = prove
 (`evaluate (s:(FFI)state) env [e1] = (s1,Rerr err) ==>
   evaluate s env [Let xo e1 e2] = (s1,Rerr err)`,
  STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* the evaluation of a Let with a bound name: its first expression, then the error or the body *)
let CKFAUX_evaluate_Let_split = prove
 (`evaluate (s:(FFI)state) env [Let (SOME n) e1 e2] = (s',res) ==>
   ?s1 r1. evaluate s env [e1] = (s1,r1) /\
           ((?err. r1 = Rerr err) /\ s' = s1 /\ res = r1 \/
            (?x. r1 = Rval [x] /\
                 evaluate s1 (sem_env_v_fupd (combin_K (nsBind n x (sem_env_v env))) env) [e2] =
                 (s',res)))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `?s1 r1. evaluate (s:(FFI)state) env [e1] = (s1,r1)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s1:(FFI)state`; `r1:(v list,v)result`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r1:(v list,v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:v list` SUBST_ALL_TAC)
                              (X_CHOOSE_THEN `er:(v)error_result` SUBST_ALL_TAC)) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_sing) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:v` SUBST_ALL_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CKFAUX_evaluate_Let_val) THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `evaluate (s:(FFI)state) env [Let (SOME n) e1 e2] = (s',res)` THEN
                         REWRITE_TAC[th]) THEN
    REWRITE_TAC[distinctness "result"; injectivity "result"; CONS_11] THEN MESON_TAC[];
    FIRST_ASSUM(fun a -> let th = MATCH_MP CKFAUX_evaluate_Let_err a in
      UNDISCH_TAC `evaluate (s:(FFI)state) env [Let (SOME n) e1 e2] = (s',res)` THEN
      REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "result"] THEN MESON_TAC[]]);;

(* the kernel's context reference *)
let CKFAUX_the_context_ref = prove
 (`(!loc. loc IN kernel_locs ==> candle_kernel_loc_ok state loc (state_refs (s:(FFI)state))) ==>
   ?cv. oEL 5 (state_refs s) = SOME (Refv cv) /\
        LIST_TYPE UPDATE_TYPE (hol_refs_the_context state) cv`,
  DISCH_THEN(MP_TAC o SPEC `5`) THEN
  REWRITE_TAC[kernel_locs; candle_kernel_loc_ok_def; CKFAUX_kernel_loc_nums; injectivity "v"] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* apply a lemma |- A1 /\ .. /\ An ==> C at an evaluation of the goal: tm (if given) *)
(* is matched with the left side of an equation C, ev (if given) with the            *)
(* evaluation antecedent; then each nsLookup antecedent is evaluated by               *)
(* can2aaux_lookup_conv (then the kernel locations), each other antecedent is        *)
(* matched with a theorem of asl (instantiating only the lemma's variables)          *)
let ckfaux_apply_lemma (asl:thm list) lemma (ev:thm option) (tm:term option) =
  let l0 = SPEC_ALL lemma in
  let gvs = map (fun v -> genvar (type_of v), v) (frees (concl l0)) in
  let l1 = INST gvs l0 in
  let gvars = map fst gvs in
  let is_lookup a = is_eq a &&
    (try fst (dest_const (fst (strip_comb (lhs a)))) = "nsLookup" with Failure _ -> false) in
  let mtch a t = term_match (subtract (frees a) gvars) a t in
  let l2 = match tm with
      Some t -> INSTANTIATE (mtch (lhs (rand (concl l1))) t) l1
    | None -> l1 in
  let l2 = match ev with
      Some e -> let a = find can2aaux_is_eval_eq (conjuncts (lhand (concl l2))) in
                INSTANTIATE (mtch a (concl e)) l2
    | None -> l2 in
  let rec go th acc ants =
    match ants with
      [] -> MP th (end_itlist CONJ (rev acc))
    | a :: rest ->
        let ath =
          if is_lookup a then
            let eq = can2aaux_lookup_conv (lhs a) in
            if can (mtch (rhs a)) (rhs (concl eq)) then eq
            else CONV_RULE (RAND_CONV (REWRITE_CONV [CKFAUX_kernel_loc_nums])) eq
          else
            try find (fun th' -> can (mtch a) (concl th')) ((match ev with Some e -> [e] | None -> []) @ asl)
            with Failure _ -> failwith ("ckfaux_apply_lemma: " ^ string_of_term a) in
        let i = mtch a (concl ath) in
        let th' = INSTANTIATE i th in
        let a' = instantiate i a in
        go th' (EQ_MP (ALPHA (concl ath) a') ath :: acc) (map (instantiate i) rest) in
  go l2 [] (conjuncts (lhand (concl l2)));;

(* an evaluation fact evaluate s env [e] = (s1,r1) of the goal rewritten by an      *)
(* equational lemma: RHS = (s1,r1)                                                   *)
let ckfaux_eval_eq_tac lemma : tactic = fun (asl,w as g) ->
  let ev1 = snd (find (fun (_,th) -> can2aaux_is_eval_eq (concl th)) asl) in
  let eqth = ckfaux_apply_lemma (map snd asl) lemma None (Some (lhs (concl ev1))) in
  (UNDISCH_THEN (concl ev1) (K ALL_TAC) THEN ASSUME_TAC (TRANS (SYM eqth) ev1)) g;;

(* an evaluation fact of the goal through a relational lemma *)
let ckfaux_eval_rel_tac lemma : tactic = fun (asl,w as g) ->
  let ev1 = snd (find (fun (_,th) -> can2aaux_is_eval_eq (concl th)) asl) in
  let th = ckfaux_apply_lemma (map snd asl) lemma (Some ev1) None in
  (UNDISCH_THEN (concl ev1) (K ALL_TAC) THEN MP_TAC th) g;;

(* the error case of a Let: the first disjunct of the goal *)
let CKFAUX_LET_ERR_TAC : tactic =
  REWRITE_TAC[distinctness "result"; injectivity "result"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  DISJ1_TAC THEN
  ASM_REWRITE_TAC[CKFAUX_evaluate_dec_clock; injectivity "result"; injectivity "error_result"] THEN
  MESON_TAC[];;

(* the value case of a Let: the evaluation of its body *)
let CKFAUX_LET_VAL_TAC : tactic =
  REWRITE_TAC[distinctness "result"; injectivity "result"; CONS_11] THEN
  REWRITE_TAC[UNWIND_THM1] THEN DISCH_TAC;;

(* a byte value of the translator *)
let CKFAUX_WORD8_Litv = prove
 (`ml_WORD (x:byte) w ==> ?b. w = Litv (Word8 b)`,
  REWRITE_TAC[ml_WORD_def] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

(* the events after a returning call of a named FFI channel *)
let CKFAUX_call_FFI_events = prove
 (`!(st:(FFI)ffi_state) n conf bytes t' ws'.
     ~(n = ExtCall (implode "")) /\ call_FFI st n conf bytes = FFI_return t' ws' ==>
     ?bs. ffi_state_io_events t' = APPEND (ffi_state_io_events st) [IO_event n conf bs]`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = ExtCall (implode "")` THEN
  ASM_REWRITE_TAC[call_FFI_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[injectivity "ffi_result"; distinctness "ffi_result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN MESON_TAC[]);;

let CKFAUX_kernel_ffi_not_empty = prove
 (`~(ExtCall (implode "kernel_ffi") = ExtCall (implode ""))`,
  REWRITE_TAC[injectivity "ffiname"] THEN CONV_TAC(DEPTH_CONV ML_PROG_MLSTRING_EQ_CONV) THEN
  REWRITE_TAC[]);;

(* print_thm th: the theorem's string through the kernel's FFI channel; the  *)
(* context is read from the kernel's reference at location 5 (kernel_loc_ok)  *)
let CKFAUX_inferred_Kernel_print_thm = prove
 (ckfaux_inferred_goal `Kernel_print_thm_v`,
  ckfaux_head_tac candle_Kernel_print_thm_v_head THEN ckfaux_typed_tac `th:thm` THEN
  ckfaux_state_tac THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                              "do_opapp" with _ -> false)) THEN
  REWRITE_TAC[ckfaux_opapp_closure_thm candle_Kernel_print_thm_v_def; injectivity "option";
              PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  (* the match of the theorem *)
  FIRST_X_ASSUM(fun ev -> if can2aaux_is_eval_eq (concl ev)
                          then MP_TAC(can2aaux_apply_check evaluate_mat_thm ev) else NO_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> MATCH_MP_TAC CKFAUX_safe_error THEN ASM_REWRITE_TAC[th])
    (X_CHOOSE_THEN `tmsv:v` (X_CHOOSE_THEN `cv0:v` STRIP_ASSUME_TAC))) THEN
  (* ctxt = !the_context *)
  MP_TAC CKFAUX_the_context_ref THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cv:v` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CKFAUX_evaluate_Let_split o check (can2aaux_is_eval_eq o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v list,v)result`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ckfaux_eval_eq_tac CKFAUX_evaluate_deref THEN
  ASM_CASES_TAC `state_clock (s:(FFI)state) = 0` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THENL
  [CKFAUX_LET_ERR_TAC; CKFAUX_LET_VAL_TAC] THEN
  (* str = thm_to_string ctxt th *)
  SUBGOAL_THEN `perms_ok {} (v:v) /\ perms_ok {} (cv:v)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ckfaux_arg_perms_tac; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CKFAUX_evaluate_Let_split o check (can2aaux_is_eval_eq o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v list,v)result`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ckfaux_eval_rel_tac CKFAUX_evaluate_thm_to_string THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THENL
  [CKFAUX_LET_ERR_TAC; CKFAUX_LET_ERR_TAC;
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `r2:(v list,v)result`)) THEN
   CKFAUX_LET_VAL_TAC] THEN
  (* " v0" = Word8.fromInt 0 *)
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CKFAUX_evaluate_Let_split o check (can2aaux_is_eval_eq o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `r3:(v list,v)result`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ckfaux_eval_rel_tac CKFAUX_evaluate_fromInt THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THENL
  [CKFAUX_LET_ERR_TAC; CKFAUX_LET_ERR_TAC;
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `r3:(v list,v)result`)) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `b:byte` SUBST_ALL_TAC o MATCH_MP CKFAUX_WORD8_Litv) THEN
   CKFAUX_LET_VAL_TAC] THEN
  (* arr = Word8Array.array 0 " v0" *)
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CKFAUX_evaluate_Let_split o check (can2aaux_is_eval_eq o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:(FFI)state` (X_CHOOSE_THEN `r4:(v list,v)result`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  ckfaux_eval_eq_tac CKFAUX_evaluate_array THEN
  ASM_CASES_TAC `state_clock (s3:(FFI)state) = 0` THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   CKFAUX_LET_ERR_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `state_clock (dec_clock (s3:(FFI)state)) = 0` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THENL
  [CKFAUX_LET_ERR_TAC; CKFAUX_LET_VAL_TAC] THEN
  (* the FFI call *)
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[STRING_TYPE_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "STRING_TYPE"
                     with _ -> false)) THEN
  SUBGOAL_THEN `oEL (LENGTH (state_refs (dec_clock (s:(FFI)state))))
    (state_refs (state_refs_fupd (combin_K (APPEND (state_refs (dec_clock s)) [W8array []]))
                   (dec_clock (dec_clock (s3:(FFI)state))))) = SOME (W8array [])` ASSUME_TAC THENL
   [REWRITE_TAC[state_INFO.ri_accfupds; K_THM; CKFAUX_oEL_APPEND1; LT_REFL]; ALL_TAC] THEN
  ckfaux_eval_eq_tac CKFAUX_evaluate_ffi THEN
  SUBGOAL_THEN `state_ffi (s3:(FFI)state) = state_ffi s /\ state_refs s3 = state_refs s /\
                state_eval_state s3 = state_eval_state s /\
                state_next_type_stamp s3 = state_next_type_stamp s` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CKFAUX_evaluate_dec_clock]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(s',res):(FFI)state#(v list,v)result`)) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM; CKFAUX_evaluate_dec_clock; state_INFO.ri_fupdcanon;
              state_INFO.ri_fupdfupds; K_o_THM] THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CKFAUX_evaluate_dec_clock] THEN
  MP_TAC(ISPEC `call_FFI (state_ffi (s:(FFI)state)) (ExtCall (implode "kernel_ffi"))
                  (MAP (word o ORD) (explode (thm_to_string (hol_refs_the_context state) th))) []`
           (cases "ffi_result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `t':(FFI)ffi_state` (X_CHOOSE_THEN `ws':byte list` ASSUME_TAC))
    (X_CHOOSE_THEN `outcome:final_event` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THENL
  [(* FFI_return: the same context, a new ok event *)
   DISJ2_TAC THEN EXISTS_TAC `ctxt:update list` THEN
   REWRITE_TAC[distinctness "result"; injectivity "result"; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2;
               ALL; v_ok_Conv_NONE] THEN
   MATCH_MP_TAC CKFAUX_print_state_ok THEN
   ASM_REWRITE_TAC[CKFAUX_evaluate_dec_clock] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP CKFAUX_call_FFI_events o CONJ CKFAUX_kernel_ffi_not_empty) THEN
   DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
   ASM_REWRITE_TAC[ALL_APPEND; ALL] THEN MATCH_MP_TAC CKFAUX_print_ok_event THEN ASM_REWRITE_TAC[];
   (* FFI_final: an abort *)
   DISJ1_TAC THEN REWRITE_TAC[state_INFO.ri_accfupds; K_THM; CKFAUX_evaluate_dec_clock] THEN
   ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result"] THEN
   REWRITE_TAC[CKFAUX_evaluate_dec_clock] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* inferred_ok: one lemma per kernel function                              *)
(* ------------------------------------------------------------------------- *)

(* the closures of the two-argument kernel functions are Closure _ _ (Fun _ _) *)
let ckfaux_two_arg_defs =
  [call_type_subst_v_def; call_freesin_v_def; call_vfree_in_v_def; call_variant_v_def;
   vsubst_v_def; inst_v_def; trans_v_def; abs_1_v_def; eq_mp_v_def;
   deduct_antisym_rule_v_def; inst_type_v_def; inst_1_v_def; compute_add_v_def;
   compute_v_def];;

let ckfaux_partial_tac (asl,w as g) =
  let th = find (fun th -> exists (fun (_,a) -> can (find_term ((=) (lhs(concl th)))) (concl a))
                             asl) ckfaux_two_arg_defs in
  let r = rhs(concl th) in
  let _,args = strip_comb r in
  let e1 = el 0 args and n = el 1 args and fe = el 2 args in
  let m = rand(rator fe) and e = rand fe in
  (MP_TAC(INST [lhs(concl th),`f:v`; e1,`env1:v sem_env`; n,`n:mlstring`; m,`m:mlstring`;
                e,`e:exp`] CKFAUX_inferred_partial) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[kernel_funs_def; IN_INSERT; th];
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]) g;;

let ckfaux_one_arg_lemmas =
  [CKFAUX_inferred_concl; CKFAUX_inferred_is_type; CKFAUX_inferred_is_vartype;
   CKFAUX_inferred_call_tyvars; CKFAUX_inferred_is_var; CKFAUX_inferred_is_const;
   CKFAUX_inferred_is_abs; CKFAUX_inferred_is_comb; CKFAUX_inferred_call_type_vars_in_term;
   CKFAUX_inferred_mk_vartype; CKFAUX_inferred_mk_var; CKFAUX_inferred_call_frees;
   CKFAUX_inferred_freesl; CKFAUX_inferred_dest_thm; CKFAUX_inferred_hyp;
   CKFAUX_inferred_beta; CKFAUX_inferred_types; CKFAUX_inferred_constants;
   CKFAUX_inferred_axioms; CKFAUX_inferred_get_type_arity; CKFAUX_inferred_mk_type;
   CKFAUX_inferred_dest_type; CKFAUX_inferred_dest_vartype; CKFAUX_inferred_get_const_type;
   CKFAUX_inferred_call_type_of; CKFAUX_inferred_mk_const; CKFAUX_inferred_mk_abs;
   CKFAUX_inferred_mk_comb; CKFAUX_inferred_dest_var; CKFAUX_inferred_dest_const;
   CKFAUX_inferred_dest_comb; CKFAUX_inferred_dest_abs; CKFAUX_inferred_rand;
   CKFAUX_inferred_rator; CKFAUX_inferred_dest_eq; CKFAUX_inferred_refl;
   CKFAUX_inferred_mk_comb_1; CKFAUX_inferred_assume; CKFAUX_inferred_new_axiom;
   CKFAUX_inferred_new_basic_definition; CKFAUX_inferred_new_specification;
   CKFAUX_inferred_new_constant; CKFAUX_inferred_call_new_type;
   CKFAUX_inferred_new_basic_type_definition; CKFAUX_inferred_Kernel_print_thm];;

(* the values of the kernel's types are not closures *)
let CKFAUX_TYPE_TYPE_Conv = prove
 (`!ty v. TYPE_TYPE ty v ==> ?opt vs. v = Conv opt vs`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ty:hol_type` (CONJUNCT1 (cases "hol_type"))) THEN
  REWRITE_TAC[TYPE_TYPE_def] THEN MESON_TAC[]);;

let CKFAUX_TERM_TYPE_Conv = prove
 (`!tm v. TERM_TYPE tm v ==> ?opt vs. v = Conv opt vs`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `tm:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[TERM_TYPE_def] THEN MESON_TAC[]);;

let CKFAUX_THM_TYPE_Conv = prove
 (`!th v. THM_TYPE th v ==> ?opt vs. v = Conv opt vs`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `th:thm` (cases "thm")) THEN
  REWRITE_TAC[THM_TYPE_def] THEN MESON_TAC[]);;

let CKFAUX_do_opapp_Conv = prove
 (`!opt vs v. do_opapp [Conv opt vs; v] = NONE`,
  REWRITE_TAC[do_opapp_def] THEN CAKE_REWRITE_TAC[]);;

let inferred_ok = prove
 (mk_imp(`candle_inferred ctxt f /\ candle_state_ok ctxt (s:(FFI)state) /\
          candle_v_ok ctxt v /\ do_opapp [f; v] = SOME (env,exp) /\
          evaluate s env [exp] = (s',res)`, ckfaux_concl),
  ONCE_REWRITE_TAC[candle_inferred_cases] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THENL
   [ALL_TAC;
    ASM_MESON_TAC[CKFAUX_TYPE_TYPE_Conv; CKFAUX_do_opapp_Conv; distinctness "option"];
    ASM_MESON_TAC[CKFAUX_TERM_TYPE_Conv; CKFAUX_do_opapp_Conv; distinctness "option"];
    ASM_MESON_TAC[CKFAUX_THM_TYPE_Conv; CKFAUX_do_opapp_Conv; distinctness "option"]] THEN
  UNDISCH_TAC `(f:v) IN kernel_funs` THEN REWRITE_TAC[kernel_funs_def; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  (FIRST (map (fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) ckfaux_one_arg_lemmas)
   ORELSE ckfaux_partial_tac));;

(* ------------------------------------------------------------------------- *)
(* kernel_vals_ok and the partial applications                             *)
(* ------------------------------------------------------------------------- *)

(* no kernel function takes three curried arguments (HOL4: EVAL over the   *)
(* closures of kernel_funs_v_def)                                           *)
let CKFAUX_kernel_funs_twice = prove
 (`!f v g w. f IN kernel_funs /\ do_partial_app f v = SOME g ==> do_partial_app g w = NONE`,
  REWRITE_TAC[kernel_funs_def; IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[kernel_funs_v_def] THEN
  REWRITE_TAC[do_partial_app_def] THEN CAKE_REWRITE_TAC[distinctness "option"] THEN
  REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CAKE_REWRITE_TAC[]);;
let CKFAUX_do_partial_app_Conv = prove
 (`!opt vs v. do_partial_app (Conv opt vs) v = NONE`,
  REWRITE_TAC[do_partial_app_def] THEN CAKE_REWRITE_TAC[]);;

let kernel_vals_twice_partial_app = prove
 (`!ctxt f. candle_kernel_vals ctxt f ==>
            !v g w. do_partial_app f v = SOME g ==> do_partial_app g w = NONE`,
  MATCH_MP_TAC candle_kernel_vals_ind THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[candle_inferred_cases] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[CKFAUX_kernel_funs_twice];
      ASM_MESON_TAC[CKFAUX_TYPE_TYPE_Conv; CKFAUX_do_partial_app_Conv; distinctness "option"];
      ASM_MESON_TAC[CKFAUX_TERM_TYPE_Conv; CKFAUX_do_partial_app_Conv; distinctness "option"];
      ASM_MESON_TAC[CKFAUX_THM_TYPE_Conv; CKFAUX_do_partial_app_Conv; distinctness "option"]];
    MESON_TAC[distinctness "option"]]);;

let kernel_vals_max_app = prove
 (`candle_kernel_vals ctxt f /\
   do_partial_app f v = SOME g /\
   do_opapp [g; w] = SOME (env,exp) ==>
   f IN kernel_funs`,
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT1 candle_v_ok_cases]) THEN STRIP_TAC THENL
   [UNDISCH_TAC `candle_inferred ctxt f` THEN ONCE_REWRITE_TAC[candle_inferred_cases] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CKFAUX_TYPE_TYPE_Conv; CKFAUX_TERM_TYPE_Conv; CKFAUX_THM_TYPE_Conv;
                  CKFAUX_do_partial_app_Conv; distinctness "option"];
    ASM_MESON_TAC[kernel_vals_twice_partial_app; distinctness "option"]]);;


(* ------------------------------------------------------------------------- *)
(* kernel_vals_ok: the two-argument kernel functions (Arrow2 and ArrowM2)   *)
(* ------------------------------------------------------------------------- *)

(* a kernel function translated by translate, two arguments *)
let CKFAUX_pure2_ok = prove
 (mk_imp(`(A --> B --> C) (f:A->B->C) fv /\ do_partial_app fv v = SOME g /\
          do_opapp [g; w] = SOME (env,exp) /\
          evaluate (s:(FFI)state) env [exp] = (s',res) /\ A a v /\ B b w /\
          perms_ok {} v /\ perms_ok {} w /\ perms_ok {} fv /\ candle_state_ok ctxt s /\
          (!rv. C (f a b) rv ==> candle_v_ok ctxt rv)`, ckfaux_concl),
  STRIP_TAC THEN MP_TAC(INST [`v:v`,`av:v`; `w:v`,`bv:v`; `g:v`,`gv:v`] candle_Arrow2) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "result"; injectivity "result";
    injectivity "error_result"; distinctness "error_result"] THENL
   [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `ctxt:update list` THEN SIMP[ALL] THEN
  ASM_MESON_TAC[CKFAUX_state_ok_same]);;

(* the side condition of the monadic drivers, two arguments *)
let ckfaux_monad_side2 =
  `!refs r refs2. holKernelProof_STATE ctxt refs /\
     (f:A->B->hol_refs->(C,hol_exn)exc#hol_refs) a b refs = (r,refs2) ==>
     ?ctxt'. holKernelProof_STATE ctxt' refs2 /\
       (!v. candle_v_ok ctxt v ==> candle_v_ok ctxt' v) /\
       (!v. candle_kernel_vals ctxt v ==> candle_kernel_vals ctxt' v) /\
       (!r. candle_ref_ok ctxt r ==> candle_ref_ok ctxt' r) /\
       (!x rv. r = M_success x /\ (C:C->v->bool) x rv ==> candle_v_ok ctxt' rv) /\
       (!e rv. r = M_failure e /\ HOL_EXN_TYPE e rv ==> candle_v_ok ctxt' rv)`;;

(* a kernel function translated by m_translate, two arguments (ArrowM2) *)
let CKFAUX_monad2_ok = prove
 (mk_imp(list_mk_conj
   [`ArrowP F (HOL_STORE,(p:(FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)))
       (PURE A) (ArrowM F (HOL_STORE,p) (PURE B) (MONAD C HOL_EXN_TYPE))
       (f:A->B->hol_refs->(C,hol_exn)exc#hol_refs) fv`;
    `do_partial_app fv v = SOME g`; `do_opapp [g; w] = SOME (env,exp)`;
    `evaluate (s:(FFI)state) env [exp] = (s',res)`; `(A:A->v->bool) a v`;
    `(B:B->v->bool) b w`; `perms_ok kernel_perms v`; `perms_ok kernel_perms w`;
    `perms_ok kernel_perms fv`; `candle_state_ok ctxt (s:(FFI)state)`;
    ckfaux_monad_side2], ckfaux_concl),
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[candle_state_ok_def] o
    check (can (find_term ((=) `candle_state_ok:update list->(FFI)state->bool`)) o concl)) THEN
  MP_TAC(INST [`v:v`,`a1v:v`; `w:v`,`a2v:v`; `g:v`,`gv:v`; `a:A`,`a1:A`; `b:B`,`a2:B`;
               `A:A->v->bool`,`A1:A->v->bool`; `B:B->v->bool`,`A2:B->v->bool`;
               `C:C->v->bool`,`B:C->v->bool`; `HOL_EXN_TYPE`,`D:hol_exn->v->bool`;
               `state:hol_refs`,`refs:hol_refs`]
    (INST_TYPE [`:B`,`:X`; `:C`,`:B`; `:hol_exn`,`:C`] ArrowM2)) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "result"; injectivity "result";
    injectivity "error_result"; distinctness "error_result"] THENL
   [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`state:hol_refs`; `r:(C,hol_exn)exc`; `refs2:hol_refs`] o
    check (is_forall o concl) o
    check (can (find_term (fun t -> try fst(dest_const t) = "holKernelProof_STATE"
                                    with _ -> false)) o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ctxt':update list` STRIP_ASSUME_TAC) THEN
  DISJ2_TAC THEN EXISTS_TAC `ctxt':update list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[candle_state_ok_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[candle_state_ok_def]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `y:C` SUBST_ALL_TAC) (X_CHOOSE_THEN `y:hol_exn` SUBST_ALL_TAC)
    (ISPEC `r:(C,hol_exn)exc` (cases "exc")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"; distinctness "exc"; UNWIND_THM1;
    FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `rv:v` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; injectivity "error_result";
    distinctness "error_result"] THEN
  SIMP[ALL] THEN ASM_MESON_TAC[]);;
(* the statement of kernel_vals_ok for the partial application g of the     *)
(* closure fv of a two-argument kernel function to v                         *)
let ckfaux_kv_goal fv =
  vsubst [fv,`f:v`]
    (mk_imp(`candle_state_ok ctxt (s:(FFI)state) /\ candle_v_ok ctxt v /\ candle_v_ok ctxt w /\
             do_partial_app f v = SOME g /\ do_opapp [g; w] = SOME (env,exp) /\
             evaluate s env [exp] = (s',res)`, ckfaux_concl));;

(* a two-argument driver applied to a certificate, with the HOL arguments *)
let ckfaux_drive2 drv cert a b =
  let th = MATCH_MP (CONV_RULE (REWR_CONV (TAUT `(p /\ q ==> r) <=> (p ==> q ==> r)`)) drv)
             cert in
  let fv n = find (fun v -> fst(dest_var v) = n) (frees (concl th)) in
  INST [a,fv "a"; b,fv "b"] th;;

let ckfaux_head2_tac head =
  STRIP_TAC THEN DRULE_ALL head THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> MATCH_MP_TAC CKFAUX_safe_error THEN ASM_REWRITE_TAC[th]) STRIP_ASSUME_TAC);;

(* the head assumption h x of the value x as a typed value a, with its validity *)
let ckfaux_typed_on (x:term) (a:term) (asl,w as g) =
  let is_head c = try rand c = x && can ckfaux_head_thm (rator c) with _ -> false in
  let hth = snd(find (fun (_,th) -> is_head (concl th)) asl) in
  let th = ckfaux_head_thm (rator(concl hth)) in
  let valid_tac (asl,w as g) =
    let iv = concl(snd(hd asl)) in
    let _,vth = ckfaux_valid (rator(rator iv)) in
    let th = SPECL [a; rand iv] vth in
    (SUBGOAL_THEN (rand(concl th)) (STRIP_ASSUME_TAC o REWRITE_RULE[]) THENL
      [MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]; ALL_TAC]) g in
  (MP_TAC (SPEC x th) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC a) THEN
   valid_tac) g;;

(* a pure two-argument kernel function *)
let ckfaux_pure2_case head cert a b perms_th res_tac =
  ckfaux_head2_tac head THEN ckfaux_typed_on `v:v` a THEN ckfaux_typed_on `w:v` b THEN
  MP_TAC(ckfaux_drive2 CKFAUX_pure2_ok cert a b) THEN
  ASM_REWRITE_TAC[perms_th] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN TRY ckfaux_arg_perms_tac THEN ckfaux_res_tac THEN res_tac;;

(* the side condition of a monadic two-argument kernel function that does   *)
(* not change the kernel's state                                             *)
let CKFAUX_monad_side2_same = prove
 (mk_imp(`(!refs r refs2. holKernelProof_STATE ctxt refs /\
             (f:A->B->hol_refs->(C,hol_exn)exc#hol_refs) a b refs = (r,refs2) ==>
             refs2 = refs /\ (!x. r = M_success x ==> P x) /\
             (!t. ~(r = M_failure (holKernel_Clash t)))) /\
          (!x rv. (C:C->v->bool) x rv /\ P x ==> candle_v_ok ctxt rv)`, ckfaux_monad_side2),
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`refs:hol_refs`; `r:(C,hol_exn)exc`; `refs2:hol_refs`] o check (is_forall o concl) o
    check (can (find_term (fun t -> try fst(dest_const t) = "holKernelProof_STATE"
                                    with _ -> false)) o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `ctxt:update list` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC CKFAUX_failure_ok THEN ASM_REWRITE_TAC[]]);;

(* a monadic two-argument kernel function that does not change the state *)
let ckfaux_monad2_case head cert a b perms_th spec_tac =
  let args = snd(strip_comb(concl cert)) in
  let c = rand(rator(rand(el 3 args))) in
  let p,vth = ckfaux_vok c in
  ckfaux_head2_tac head THEN ckfaux_typed_on `v:v` a THEN ckfaux_typed_on `w:v` b THEN
  MP_TAC(ckfaux_drive2 CKFAUX_monad2_ok cert a b) THEN
  ASM_REWRITE_TAC[perms_th] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN TRY ckfaux_arg_perms_tac THEN
  MATCH_MP_TAC (GEN_ALL CKFAUX_monad_side2_same) THEN EXISTS_TAC p THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
   [spec_tac; MATCH_ACCEPT_TAC vth];;

let CKFAUX_ALL_PAIR = prove
 (`!P Q l. ALL (\(x:A,y:B). P x /\ Q y) l <=> ALL (\p. P (FST p) /\ Q (SND p)) l`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; FST; SND]);;
let CKFAUX_kv_call_type_subst = prove
 (ckfaux_kv_goal `call_type_subst_v`,
  ckfaux_pure2_case call_type_subst_v_head call_type_subst_v_thm
    `i:(hol_type#hol_type)list` `ty:hol_type` perms_ok_call_type_subst_v
   (REWRITE_TAC[call_type_subst_def] THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL holKernelProof_type_subst)) THEN
    ASM_REWRITE_TAC[CKFAUX_ALL_PAIR]));;

let CKFAUX_kv_call_freesin = prove
 (ckfaux_kv_goal `call_freesin_v`,
  ckfaux_pure2_case call_freesin_v_head call_freesin_v_thm `tms:hol_term list` `tm:hol_term`
    perms_ok_call_freesin_v ALL_TAC);;

let CKFAUX_kv_call_vfree_in = prove
 (ckfaux_kv_goal `call_vfree_in_v`,
  ckfaux_pure2_case call_vfree_in_v_head call_vfree_in_v_thm `tm1:hol_term` `tm:hol_term`
    perms_ok_call_vfree_in_v ALL_TAC);;

let CKFAUX_kv_call_variant = prove
 (ckfaux_kv_goal `call_variant_v`,
  ckfaux_pure2_case call_variant_v_head call_variant_v_thm `tms:hol_term list` `tm:hol_term`
    perms_ok_call_variant_v
   (REWRITE_TAC[call_variant_def] THEN ckfaux_state_tac THEN
    MATCH_MP_TAC variant_thm THEN ASM_MESON_TAC[]));;
let CKFAUX_kv_vsubst = prove
 (ckfaux_kv_goal `vsubst_v`,
  ckfaux_monad2_case vsubst_v_head vsubst_v_thm `theta:(hol_term#hol_term)list` `tm:hol_term`
    perms_ok_vsubst_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`theta:(hol_term#hol_term)list`; `tm:hol_term`; `refs:hol_refs`;
                  `r:(hol_term,hol_exn)exc`; `refs2:hol_refs`; `ctxt:update list`] vsubst_thm) THEN
    ASM_REWRITE_TAC[CKFAUX_ALL_PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN ckfaux_noclash_tac[vsubst_not_clash]));;

let CKFAUX_kv_inst = prove
 (ckfaux_kv_goal `inst_v`,
  ckfaux_monad2_case inst_v_head inst_v_thm `theta:(hol_type#hol_type)list` `tm:hol_term`
    perms_ok_inst_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`theta:(hol_type#hol_type)list`; `tm:hol_term`; `refs:hol_refs`;
                  `r:(hol_term,hol_exn)exc`; `refs2:hol_refs`; `ctxt:update list`] inst_thm) THEN
    ASM_REWRITE_TAC[CKFAUX_ALL_PAIR] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN ASM_MESON_TAC[]));;

let CKFAUX_kv_trans = prove
 (ckfaux_kv_goal `trans_v`,
  ckfaux_monad2_case trans_v_head trans_v_thm `th1:thm` `th2:thm` perms_ok_trans_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`ctxt:update list`; `th1:thm`; `th2:thm`; `refs:hol_refs`;
                  `r:(thm,hol_exn)exc`; `refs2:hol_refs`] TRANS_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ckfaux_noclash_tac[TRANS_not_clash]));;

let CKFAUX_kv_abs = prove
 (ckfaux_kv_goal `abs_v`,
  ckfaux_monad2_case abs_v_head abs_1_v_thm `tm:hol_term` `th:thm` perms_ok_abs_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN DRULE_ALL ABS_thm THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ckfaux_noclash_tac[ABS_not_clash]));;

let CKFAUX_kv_eq_mp = prove
 (ckfaux_kv_goal `eq_mp_v`,
  ckfaux_monad2_case eq_mp_v_head eq_mp_v_thm `th1:thm` `th2:thm` perms_ok_eq_mp_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`th1:thm`; `th2:thm`; `refs:hol_refs`; `r:(thm,hol_exn)exc`;
                  `refs2:hol_refs`; `ctxt:update list`] EQ_MP_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ckfaux_noclash_tac[EQ_MP_not_clash]));;

let CKFAUX_kv_deduct_antisym_rule = prove
 (ckfaux_kv_goal `deduct_antisym_rule_v`,
  ckfaux_monad2_case deduct_antisym_rule_v_head deduct_antisym_rule_v_thm `th1:thm` `th2:thm`
    perms_ok_deduct_antisym_rule_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`th1:thm`; `th2:thm`; `refs:hol_refs`; `r:(thm,hol_exn)exc`;
                  `refs2:hol_refs`; `ctxt:update list`] DEDUCT_ANTISYM_RULE_thm) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ckfaux_noclash_tac[DEDUCT_ANTISYM_RULE_not_clash]));;

let CKFAUX_kv_inst_type = prove
 (ckfaux_kv_goal `inst_type_v`,
  ckfaux_monad2_case inst_type_v_head inst_type_v_thm `theta:(hol_type#hol_type)list` `th:thm`
    perms_ok_inst_type_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`theta:(hol_type#hol_type)list`; `th:thm`; `refs:hol_refs`;
                  `r:(thm,hol_exn)exc`; `refs2:hol_refs`; `ctxt:update list`]
             INST_TYPE_thm) THEN
    ASM_REWRITE_TAC[CKFAUX_ALL_PAIR] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN ASM_MESON_TAC[]));;

let CKFAUX_kv_inst_1 = prove
 (ckfaux_kv_goal `inst_1_v`,
  ckfaux_monad2_case inst_1_v_head inst_1_v_thm `theta:(hol_term#hol_term)list` `th:thm`
    perms_ok_inst_1_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`theta:(hol_term#hol_term)list`; `th:thm`; `refs:hol_refs`;
                  `r:(thm,hol_exn)exc`; `refs2:hol_refs`; `ctxt:update list`] INST_thm) THEN
    ASM_REWRITE_TAC[CKFAUX_ALL_PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ckfaux_noclash_tac[INST_not_clash]));;

let CKFAUX_kv_compute_add = prove
 (ckfaux_kv_goal `compute_add_v`,
  ckfaux_monad2_case compute_add_v_head compute_add_v_thm `ths:thm list` `tm:hol_term`
    perms_ok_compute_add_v
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`ctxt:update list`; `refs:hol_refs`; `ths:thm list`; `tm:hol_term`;
                  `r:(thm,hol_exn)exc`; `refs2:hol_refs`] compute_add_thm) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]));;

let CKFAUX_kv_compute = prove
 (ckfaux_kv_goal `compute_v`,
  ckfaux_monad2_case compute_v_head compute_v_thm `p:(thm)list#(thm)list` `tm:hol_term`
    perms_ok_compute_v
   (PAIR_CASES_ON `p:(thm)list#(thm)list` THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`ctxt:update list`; `refs:hol_refs`; `p0:thm list`; `p1:thm list`;
                  `tm:hol_term`; `r:(thm,hol_exn)exc`; `refs2:hol_refs`] compute_thm) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]));;
let ckfaux_kv_lemmas =
  [CKFAUX_kv_call_type_subst; CKFAUX_kv_call_freesin; CKFAUX_kv_call_vfree_in;
   CKFAUX_kv_call_variant; CKFAUX_kv_vsubst; CKFAUX_kv_inst; CKFAUX_kv_trans; CKFAUX_kv_abs;
   CKFAUX_kv_eq_mp; CKFAUX_kv_deduct_antisym_rule; CKFAUX_kv_inst_type; CKFAUX_kv_inst_1;
   CKFAUX_kv_compute_add; CKFAUX_kv_compute];;

let kernel_vals_ok = prove
 (mk_forall(`ctxt:update list`, mk_forall(`f:v`,
    mk_imp(`candle_kernel_vals ctxt f`,
      list_mk_forall([`s:(FFI)state`; `v:v`; `env:v sem_env`; `exp:exp`; `s':(FFI)state`;
                      `res:(v list,v)result`],
        mk_imp(`do_opapp [f; v] = SOME (env,exp) /\ candle_state_ok ctxt (s:(FFI)state) /\
                candle_v_ok ctxt v /\ evaluate s env [exp] = (s',res)`, ckfaux_concl))))),
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 candle_v_ok_cases] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f0:v` (X_CHOOSE_THEN `v0:v` STRIP_ASSUME_TAC))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC inferred_ok THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the partial application of a two-argument kernel function *)
  MP_TAC(INST [`f0:v`,`f:v`; `v0:v`,`v:v`; `f:v`,`g:v`; `v:v`,`w:v`] kernel_vals_max_app) THEN
  ASM_REWRITE_TAC[kernel_funs_def; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  (FIRST (map (fun th -> MP_TAC(INST [`v0:v`,`v:v`; `v:v`,`w:v`; `f:v`,`g:v`] th) THEN
                         ASM_REWRITE_TAC[] THEN NO_TAC) ckfaux_kv_lemmas) ORELSE
   (FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                     "do_partial_app" with _ -> false)) THEN
    REWRITE_TAC[kernel_funs_v_def] THEN REWRITE_TAC[do_partial_app_def] THEN
    CAKE_REWRITE_TAC[distinctness "option"])));;
