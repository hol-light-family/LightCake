(* ========================================================================= *)
(* clos_knownProof: port of HOL4 compiler/backend/proofs/                    *)
(* clos_knownProofScript.sml (CakeML v3479).                                 *)
(* Correctness proof for clos_known.                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/proofs/clos_knownProps.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/proofs/clos_opProof.ml";;
needs "compiler/backend/proofs/clos_letopProof.ml";;
needs "compiler/backend/proofs/clos_ticksProof.ml";;
needs "compiler/backend/proofs/clos_fvsProof.ml";;

type_invention_error := true;;

(* CLOSP2AUX_ names are local helpers. *)

(* HOL4 lines 13-31: simpset and overload settings; va_case_eq, inlD_case_eq *)
(* and result_case_eq are ML values (case equations of TypeBase).          *)

(* ------------------------------------------------------------------------- *)
(* local tactics: unfolding known once in an induction case                  *)
(* ------------------------------------------------------------------------- *)

(* goal-only splits: the new equation is assumed, only the goal is          *)
(* rewritten (the induction hypotheses are left alone)                       *)
let CLOSP2AUX_GPAIR_TAC : tactic = fun (asl,w as gl) ->
  let is_cand t = is_case_app t &&
    (let c,x,fs = dest_case_app t in
     fst(dest_const c) = "pair_CASE" && not (is_pair x) && free_in x w) in
  let t = find_term is_cand w in
  let _,x,fs = dest_case_app t in
  let f = hd fs in
  let tya,tyb = match dest_type(type_of x) with
      "prod",[a;b] -> a,b | _ -> failwith "CLOSP2AUX_GPAIR_TAC" in
  let n1,n2 =
    try let a,b = dest_abs f in let b1,_ = dest_abs b in
        fst(dest_var a),fst(dest_var b1)
    with Failure _ -> "p1","p2" in
  let avoid = itlist (union o thm_frees o snd) asl (frees w) in
  let v1 = variant avoid (mk_var(n1,tya)) in
  let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
  let nch = ISPEC x (nchotomy_of_type (type_of x)) in
  (MP_TAC nch THEN
   DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
     (fun th -> if is_var x then SUBST_ALL_TAC th
                else ASSUME_TAC th THEN SUBST1_TAC th))) THEN
   CAKE_REWRITE_TAC[]) gl;;

let CLOSP2AUX_GCASE_TAC : tactic = fun (asl,w as gl) ->
  let x = first_case_scrutinee w w in
  if is_var x then TOP_CASE_TAC gl
  else if type_of x = bool_ty then
    (ASM_CASES_TAC x THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[th])) gl
  else
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(REPEAT_TCL STRIP_THM_THEN
       (fun th -> ASSUME_TAC th THEN SUBST1_TAC th)) THEN
     CAKE_REWRITE_TAC[]) gl;;

(* a case of clos_known_known_ind for a statement clos_known_known c xs vs g = (r,g') ==> ...:    *)
(* the induction hypotheses are assumed, the equation is unfolded once and   *)
(* its pairs and cases are split                                             *)
let CLOSP2AUX_KN_UNFOLD_TAC : tactic =
  let is_main tm =
    is_eq tm && (try fst(dest_const(fst(strip_comb(lhs tm)))) = "clos_known_known"
                 with Failure _ -> false) in
  REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(fun th -> if is_main (concl th) then MP_TAC th
                           else STRIP_ASSUME_TAC th)) THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN REPEAT CLOSP2AUX_GCASE_TAC THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]);;

let CLOSP2AUX_kn_gl_thms = [clos_set_globals_def; BAG_UNION_EMPTY; SET_OF_BAG_UNION;
  BAG_OF_EMPTY; IN_UNION; NOT_IN_EMPTY];;

(* known_op changes the global approximation only at SetGlobal *)
let CLOSP2AUX_known_op_g = prove
 (`!op as (g0:val_approx spt) a g.
     known_op op as g0 = (a,g) ==>
     g = g0 \/ ?n x. op = GlobOp (SetGlobal n) /\ g = insert n x g0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let CLOSP2AUX_chg_split = prove
 (`!(g0:val_approx spt) g1 g2 i.
     i IN domain g2 /\ (i IN domain g0 ==> ~(lookup i g2 = lookup i g0)) ==>
     (i IN domain g1 /\ (i IN domain g0 ==> ~(lookup i g1 = lookup i g0))) \/
     (i IN domain g2 /\ (i IN domain g1 ==> ~(lookup i g2 = lookup i g1)))`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* simple properties of constants from clos_known: i.e., merge and known    *)
(* ------------------------------------------------------------------------- *)

(* HOL4: known_op_changed_globals *)
let known_op_changed_globals = prove
 (`!opn aenv (g0:val_approx spt) a g.
     known_op opn aenv g0 = (a,g) ==>
     !i. i IN domain g /\ (i IN domain g0 ==> ~(lookup i g = lookup i g0)) ==>
         i IN SET_OF_BAG (clos_op_gbag opn)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_known_op_g) THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THENL
   [MESON_TAC[];
    REWRITE_TAC[clos_op_gbag_def; SET_OF_BAG_INSERT; IN_INSERT; domain_insert;
                lookup_insert] THEN
    ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* HOL4: known_changed_globals *)
let known_changed_globals = prove
 (`!c xs aenv (g0:val_approx spt) alist g.
     clos_known_known c xs aenv g0 = (alist,g) ==>
     !i. i IN domain g /\ (i IN domain g0 ==> ~(lookup i g = lookup i g0)) ==>
         i IN SET_OF_BAG (clos_elist_globals xs)`,
  MATCH_MP_TAC clos_known_known_ind THEN REPEAT CONJ_TAC THEN CLOSP2AUX_KN_UNFOLD_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kn_gl_thms) THEN
  REWRITE_TAC CLOSP2AUX_kn_gl_thms THEN
  TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP known_op_changed_globals)) THEN
  ASM_MESON_TAC[CLOSP2AUX_chg_split]);;

let CLOSP2AUX_known_op_unchanged = prove
 (`!op as (g0:val_approx spt) a g.
     known_op op as g0 = (a,g) /\ clos_op_gbag op = EMPTY_BAG ==> g = g0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN STRIP_ASSUME_TAC o
    MATCH_MP CLOSP2AUX_known_op_g) MP_TAC) THEN
  ASM_REWRITE_TAC[clos_op_gbag_def; BAG_INSERT_NOT_EMPTY]);;

(* HOL4: known_unchanged_globals *)
let known_unchanged_globals = prove
 (`!c xs aenv (g0:val_approx spt) eas1 g1.
     clos_known_known c xs aenv g0 = (eas1,g1) /\ clos_elist_globals xs = EMPTY_BAG ==> g0 = g1`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC clos_known_known_ind THEN REPEAT CONJ_TAC THEN CLOSP2AUX_KN_UNFOLD_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kn_gl_thms) THEN
  REWRITE_TAC CLOSP2AUX_kn_gl_thms THEN
  TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSP2AUX_known_op_unchanged))) THEN
  ASM_MESON_TAC[]);;

(* HOL4: known_op_changed_globals_alt *)
let known_op_changed_globals_alt = prove
 (`!opn aenv (g0:val_approx spt) a g.
     known_op opn aenv g0 = (a,g) ==>
     SUB_BAG (BAG_OF_SET (domain g)) (BAG_UNION (BAG_OF_SET (domain g0)) (clos_op_gbag opn))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP known_op_changed_globals) THEN
  REWRITE_TAC[SUB_BAG_LEQ; BAG_OF_SET; BAG_UNION] THEN X_GEN_TAC `i:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  REWRITE_TAC[IN_SET_OF_BAG; BAG_IN; BAG_INN] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4: known_op_changed_globals_alt_set *)
let known_op_changed_globals_alt_set = prove
 (`!opn aenv (g0:val_approx spt) a g.
     known_op opn aenv g0 = (a,g) ==>
     domain g SUBSET (domain g0 UNION SET_OF_BAG (clos_op_gbag opn))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP known_op_changed_globals) THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN ASM_MESON_TAC[]);;

(* HOL4: known_changed_globals_alt *)
let known_changed_globals_alt = prove
 (`!c xs aenv (g0:val_approx spt) alist g.
     clos_known_known c xs aenv g0 = (alist,g) ==>
     SUB_BAG (BAG_OF_SET (domain g)) (BAG_UNION (BAG_OF_SET (domain g0)) (clos_elist_globals xs))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP known_changed_globals) THEN
  REWRITE_TAC[SUB_BAG_LEQ; BAG_OF_SET; BAG_UNION] THEN X_GEN_TAC `i:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  REWRITE_TAC[IN_SET_OF_BAG; BAG_IN; BAG_INN] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4: known_changed_globals_alt_set *)
let known_changed_globals_alt_set = prove
 (`!c xs aenv (g0:val_approx spt) alist g.
     clos_known_known c xs aenv g0 = (alist,g) ==>
     domain g SUBSET (domain g0 UNION SET_OF_BAG (clos_elist_globals xs))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP known_changed_globals) THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN ASM_MESON_TAC[]);;

(* HOL4: first_n_exps_def *)
let first_n_exps_def = cake_def
  `first_n_exps (co:num -> A # B # C) n = list_of_seq (FST o SND o co) n`;;

(* HOL4: first_n_exps_shift_seq *)
let first_n_exps_shift_seq = prove
 (`!(co:num -> A # B # C) n k.
     first_n_exps co (n + k) = APPEND (first_n_exps co k) (first_n_exps (shift_seq k co) n)`,
  REWRITE_TAC[first_n_exps_def; GENLIST_APPEND] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; shift_seq_def]);;

(* HOL4: MEM_first_n_exps *)
let MEM_first_n_exps = prove
 (`!k n. k < n ==> !co:num -> A # B # C. MEM (FST (SND (co k))) (first_n_exps co n)`,
  REWRITE_TAC[first_n_exps_def; MEM_GENLIST; o_THM] THEN MESON_TAC[]);;

(* HOL4: unique_set_globals_def *)
let unique_set_globals_def = cake_def
  `unique_set_globals es (co:num -> A # clos_exp list # B) <=>
     !n. BAG_ALL_DISTINCT (clos_elist_globals (APPEND es (FLAT (first_n_exps co n))))`;;

(* HOL4: unique_set_globals_shift_seq *)
let unique_set_globals_shift_seq = prove
 (`!es (co:num -> A # clos_exp list # B).
     unique_set_globals es co ==> !k. unique_set_globals es (shift_seq k co)`,
  REWRITE_TAC[unique_set_globals_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + k:num`) THEN
  REWRITE_TAC[first_n_exps_shift_seq; FLAT_APPEND; clos_elist_globals_append;
              BAG_ALL_DISTINCT; BAG_UNION] THEN
  MESON_TAC[ARITH_RULE `a + b + c <= 1 ==> a + c <= 1`]);;

(* HOL4: unique_set_globals_evaluate *)
let unique_set_globals_evaluate = prove
 (`!es xs env (s1:(C,FFI)clos_state) s2 res.
     unique_set_globals xs (clos_state_compile_oracle s1) /\
     clos_evaluate (es,env,s1) = (res,s2) ==>
     unique_set_globals xs (clos_state_compile_oracle s2)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_code) THEN
  ASM_SIMP_TAC[unique_set_globals_shift_seq]);;

(* HOL4: unique_set_globals_subexps (HOL4 line 224 rebinds it with GEN_ALL; *)
(* the statement here is closed)                                           *)
let unique_set_globals_subexps = prove
 (`!(co:num -> A # clos_exp list # B) x1 x2 x3 xs t opn src_name loc_opt vsopt num_args
     src_names fns ticks dest.
     (unique_set_globals (CONS x1 (CONS x2 xs)) co ==>
        unique_set_globals [x1] co /\ unique_set_globals (CONS x2 xs) co) /\
     (unique_set_globals [clos_If t x1 x2 x3] co ==>
        unique_set_globals [x1] co /\ unique_set_globals [x2] co /\
        unique_set_globals [x3] co) /\
     (unique_set_globals [clos_Let t xs x2] co ==>
        unique_set_globals xs co /\ unique_set_globals [x2] co) /\
     (unique_set_globals [clos_Raise t x1] co ==> unique_set_globals [x1] co) /\
     (unique_set_globals [clos_Handle t x1 x2] co ==>
        unique_set_globals [x1] co /\ unique_set_globals [x2] co) /\
     (unique_set_globals [clos_Op t opn xs] co ==> unique_set_globals xs co) /\
     (unique_set_globals [Fn src_name loc_opt vsopt num_args x1] co ==>
        unique_set_globals [x1] co) /\
     (unique_set_globals [clos_Letrec src_names loc_opt vsopt fns x1] co ==>
        unique_set_globals [x1] co /\ unique_set_globals (MAP SND fns) co) /\
     (unique_set_globals [clos_App t loc_opt x1 xs] co ==>
        unique_set_globals [x1] co /\ unique_set_globals xs co) /\
     (unique_set_globals [clos_Tick t x1] co ==> unique_set_globals [x1] co) /\
     (unique_set_globals [clos_Call t ticks dest xs] co ==> unique_set_globals xs co)`,
  REWRITE_TAC[unique_set_globals_def; APPEND; clos_elist_globals_append;
              clos_set_globals_def; BAG_ALL_DISTINCT; BAG_UNION; EMPTY_BAG; K_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `e:num`]) THEN ARITH_TAC);;

(* HOL4: unique_set_globals_IMP_es_distinct_elist_globals *)
let unique_set_globals_IMP_es_distinct_elist_globals = prove
 (`!es (co:num -> A # clos_exp list # B).
     unique_set_globals es co ==> BAG_ALL_DISTINCT (clos_elist_globals es)`,
  REWRITE_TAC[unique_set_globals_def; clos_elist_globals_append;
              BAG_ALL_DISTINCT_BAG_UNION] THEN
  MESON_TAC[]);;

(* HOL4: set_globals_empty_unique_set_globals *)
let set_globals_empty_unique_set_globals = prove
 (`!e (co:num -> A # clos_exp list # B).
     clos_set_globals e = EMPTY_BAG ==>
     (unique_set_globals [e] co <=> unique_set_globals [] co)`,
  SIMP_TAC[unique_set_globals_def; APPEND; clos_elist_globals_append;
           clos_set_globals_def; BAG_UNION_EMPTY]);;

(* HOL4: nil_unique_set_globals *)
let nil_unique_set_globals = prove
 (`!es (co:num -> A # clos_exp list # B).
     unique_set_globals es co ==> unique_set_globals [] co`,
  REWRITE_TAC[unique_set_globals_def; clos_elist_globals_append; APPEND;
              clos_set_globals_def; BAG_UNION_EMPTY; BAG_ALL_DISTINCT_BAG_UNION] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Value approximation is sgc free                                           *)
(* ------------------------------------------------------------------------- *)

let CLOSP2AUX_kn_va_size_lemma = prove
 (`!v vl. MEM (v:val_approx) vl ==> val_approx_size v < list_size val_approx_size vl`,
  MESON_TAC[MEM_LIST_SIZE]);;

(* HOL4: val_approx_sgc_free_def [simp] (HOL4 line 257 rebinds it with     *)
(* SIMP_RULE ETA_ss: the same statement here)                              *)
let val_approx_sgc_free_def = sem1aux_def_wf
  `MEASURE val_approx_size`
  (SEM1AUX_TC_TAC ORELSE
   (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    RVEQ_TAC THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSP2AUX_kn_va_size_lemma)) THEN
    REWRITE_TAC(WF_REL_THMS @ [type_size_def "val_approx"] @ size_aux_eqs "val_approx") THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC))
  `(val_approx_sgc_free (ClosNoInline m n) <=> T) /\
   (val_approx_sgc_free (clos_known_Clos m n e s) <=> clos_set_globals e = EMPTY_BAG) /\
   (val_approx_sgc_free (clos_known_Tuple tag vas) <=> ALL val_approx_sgc_free vas) /\
   (val_approx_sgc_free _ <=> T)`;;
let _ = cake_add_simps [val_approx_sgc_free_def];;

let val_approx_sgc_free_ind = cake_ind "val_approx_sgc_free";;

let CLOSP2AUX_ALL_MAP2 = prove
 (`!(P:C->bool) (f:C->C->C) xs ys.
     LENGTH xs = LENGTH ys /\ ALL P xs /\ ALL P ys /\
     (!x y. MEM x xs /\ P x /\ P y ==> P (f x y)) ==>
     ALL P (MAP2 f xs ys)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP2_DEF; ALL; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MEM; HD; TL] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4: val_approx_sgc_free_merge *)
let val_approx_sgc_free_merge = prove
 (`!a1 a2. val_approx_sgc_free a1 /\ val_approx_sgc_free a2 ==>
           val_approx_sgc_free (merge a1 a2)`,
  MATCH_MP_TAC merge_ind THEN REWRITE_TAC[merge_def; val_approx_sgc_free_def] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[val_approx_sgc_free_def] THEN
  MATCH_MP_TAC CLOSP2AUX_ALL_MAP2 THEN ASM_MESON_TAC[]);;

(* HOL4: globals_approx_sgc_free_def *)
let globals_approx_sgc_free_def = cake_def
  `globals_approx_sgc_free (g:val_approx spt) <=>
     !n a. lookup n g = SOME a ==> val_approx_sgc_free a`;;

(* ------------------------------------------------------------------------- *)
(* alternative val_approx to value relation                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4: val_approx_val *)
let val_approx_val_rules,val_approx_val_ind,val_approx_val_cases,val_approx_val_strongind =
  cake_inductive
  `(!v. val_approx_val clos_known_Other v) /\
   (!i. val_approx_val (clos_known_Int i) (clos_Number i)) /\
   (!tg vas vs.
      ALL2 val_approx_val vas vs ==>
      val_approx_val (clos_known_Tuple tg vas) (clos_Block tg vs)) /\
   (!m n env b. val_approx_val (ClosNoInline m n) (clos_Closure (SOME m) [] env n b)) /\
   (!m n env base fs j.
      m = base + 2 * j /\ j < LENGTH fs /\ n = FST (EL j fs) ==>
      val_approx_val (ClosNoInline m n) (clos_Recclosure (SOME base) [] env fs j)) /\
   (!m n b s env. val_approx_val (clos_known_Clos m n b s) (clos_Closure (SOME m) [] env n b))`;;

(* HOL4: val_approx_val_simps [simp] (derived with SIMP_CONV from the cases) *)
let val_approx_val_simps = prove
 (`(!v. val_approx_val clos_known_Other v <=> T) /\
   (!i v. val_approx_val (clos_known_Int i) v <=> v = clos_Number i) /\
   (!tg vas v. val_approx_val (clos_known_Tuple tg vas) v <=>
               ?vs. v = clos_Block tg vs /\ ALL2 val_approx_val vas vs) /\
   (!m n v. val_approx_val (ClosNoInline m n) v <=>
            (?env b. v = clos_Closure (SOME m) [] env n b) \/
            (?env base fs j. v = clos_Recclosure (SOME base) [] env fs j /\
                             m = base + 2 * j /\ j < LENGTH fs /\ n = FST (EL j fs))) /\
   (!m n b1 s v. val_approx_val (clos_known_Clos m n b1 s) v <=>
                 ?env. v = clos_Closure (SOME m) [] env n b1) /\
   (!v. val_approx_val Impossible v <=> F)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [val_approx_val_cases] THEN
  REWRITE_TAC[distinctness "val_approx"; injectivity "val_approx"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [val_approx_val_simps];;

let CLOSP2AUX_ALL2_MAP2_merge = prove
 (`!vas ys vs.
     LENGTH vas = LENGTH ys /\
     ALL2 (\a1 v. !a2. val_approx_val (merge a1 a2) v) vas vs ==>
     ALL2 val_approx_val (MAP2 merge vas ys) vs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP2_DEF; ALL2; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; HD; TL] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_ALL2_merge_Impossible = prove
 (`!vas vs. ALL2 (\a1 v. !a2. val_approx_val (merge a1 a2) v) vas vs ==>
            ALL2 val_approx_val vas vs`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
  MESON_TAC[merge_Impossible]);;

(* HOL4: val_approx_val_merge_I_lemma *)
let val_approx_val_merge_I_lemma = prove
 (`!a1 v. val_approx_val a1 v ==> !a2. val_approx_val (merge a1 a2) v`,
  MATCH_MP_TAC val_approx_val_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> let a2 = rand(rand(rator w)) in
                   STRUCT_CASES_TAC(ISPEC a2 (CONJUNCT1 (cases "val_approx")))) THEN
  REWRITE_TAC[merge_def] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[val_approx_val_simps; injectivity "clos_v"; injectivity "option"] THEN
  TRY(FIRST_X_ASSUM(fun th -> if length(conjuncts(concl th)) = 4
                              then REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC th
                              else NO_TAC)) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_ALL2_MAP2_merge THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSP2AUX_ALL2_merge_Impossible) THEN
      MESON_TAC[]) THEN
  ASM_MESON_TAC[CLOSP2AUX_ALL2_MAP2_merge]);;

(* HOL4: val_approx_val_merge_I *)
let val_approx_val_merge_I = prove
 (`!a1 v a2. val_approx_val a1 v \/ val_approx_val a2 v ==> val_approx_val (merge a1 a2) v`,
  MESON_TAC[val_approx_val_merge_I_lemma; merge_comm]);;

(* HOL4: evaluate_IMP_shift_seq *)
let evaluate_IMP_shift_seq = prove
 (`!es env (s0:(C,FFI)clos_state) res s.
     clos_evaluate (es,env,s0) = (res,s) ==>
     ?k. clos_state_compile_oracle s = shift_seq k (clos_state_compile_oracle s0)`,
  MESON_TAC[clos_evaluate_code]);;

(* HOL4: shift_seq_zero [simp] *)
let shift_seq_zero = prove
 (`!co:num->A. shift_seq 0 co = co`,
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES; ETA_AX]);;
let _ = cake_add_simps [shift_seq_zero];;

(* HOL4: shift_seq_add [simp] *)
let shift_seq_add = prove
 (`!co:num->A k1 k2. shift_seq k2 (shift_seq k1 co) = shift_seq (k1 + k2) co`,
  REWRITE_TAC[shift_seq_def; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN ARITH_TAC);;
let _ = cake_add_simps [shift_seq_add];;

(* HOL4: do_install_IMP_shift_seq *)
let do_install_IMP_shift_seq = prove
 (`!xs (s0:(C,FFI)clos_state) res s.
     clos_do_install xs s0 = (res,s) ==>
     ?k. clos_state_compile_oracle s = shift_seq k (clos_state_compile_oracle s0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSPROPSAUX_do_install_code) THEN
  REWRITE_TAC[CLOSPROPSAUX_code_inv_def] THEN MESON_TAC[]);;

(* HOL4: evaluate_app_IMP_shift_seq *)
let evaluate_app_IMP_shift_seq = prove
 (`!lopt f args (s0:(C,FFI)clos_state) res s.
     evaluate_app lopt f args s0 = (res,s) ==>
     ?k. clos_state_compile_oracle s = shift_seq k (clos_state_compile_oracle s0)`,
  MESON_TAC[evaluate_app_code]);;

(* HOL4: state_globals_approx_def *)
let state_globals_approx_def = cake_def
  `state_globals_approx (s:(C,FFI)clos_state) (g:val_approx spt) <=>
     !k v a. get_global k (clos_state_globals s) = SOME (SOME v) /\ lookup k g = SOME a ==>
             val_approx_val a v`;;

(* HOL4: state_globals_approx_clock_fupd [simp] *)
let state_globals_approx_clock_fupd = prove
 (`!(s:(C,FFI)clos_state) f g.
     state_globals_approx (clos_state_clock_fupd f s) g <=> state_globals_approx s g`,
  REWRITE_TAC[state_globals_approx_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [state_globals_approx_clock_fupd];;

(* HOL4: state_globals_approx_dec_clock [simp] *)
let state_globals_approx_dec_clock = prove
 (`!n (s:(C,FFI)clos_state) g.
     state_globals_approx (clos_dec_clock n s) g <=> state_globals_approx s g`,
  REWRITE_TAC[state_globals_approx_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [state_globals_approx_dec_clock];;

(* HOL4: state_globals_approx_refsfupd [simp] *)
let state_globals_approx_refsfupd = prove
 (`!(s:(C,FFI)clos_state) f g.
     state_globals_approx (clos_state_refs_fupd f s) g <=> state_globals_approx s g`,
  REWRITE_TAC[state_globals_approx_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [state_globals_approx_refsfupd];;

(* HOL4: state_globals_approx_ffifupd [simp] *)
let state_globals_approx_ffifupd = prove
 (`!(s:(C,FFI)clos_state) f g.
     state_globals_approx (clos_state_ffi_fupd f s) g <=> state_globals_approx s g`,
  REWRITE_TAC[state_globals_approx_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [state_globals_approx_ffifupd];;

(* HOL4: state_globals_approx_codeupd [simp] *)
let state_globals_approx_codeupd = prove
 (`!(s:(C,FFI)clos_state) f g.
     state_globals_approx (clos_state_code_fupd f s) g <=> state_globals_approx s g`,
  REWRITE_TAC[state_globals_approx_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [state_globals_approx_codeupd];;

(* HOL4: state_globals_approx_coupd [simp] *)
let state_globals_approx_coupd = prove
 (`!(s:(C,FFI)clos_state) f g.
     state_globals_approx (clos_state_compile_oracle_fupd f s) g <=> state_globals_approx s g`,
  REWRITE_TAC[state_globals_approx_def; clos_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [state_globals_approx_coupd];;

(* ------------------------------------------------------------------------- *)
(* Mapped globals                                                            *)
(* ------------------------------------------------------------------------- *)

(* HOL4: mapped_globals_def *)
let mapped_globals_def = cake_def
  `mapped_globals (g:(A option) list) = { i | ?v. get_global i g = SOME (SOME v) }`;;

(* HOL4: mglobals_extend_def *)
let mglobals_extend_def = cake_def
  `mglobals_extend (g1:(A option) list) mgs g2 <=>
     mapped_globals g2 SUBSET (mapped_globals g1 UNION mgs) /\
     !k v. get_global k g2 = SOME (SOME v) /\ ~(k IN mgs) ==>
           get_global k g1 = SOME (SOME v)`;;

(* HOL4: mglobals_extend_refl [simp] *)
let mglobals_extend_refl = prove
 (`!(s:(A option) list) gs. mglobals_extend s gs s`,
  REWRITE_TAC[mglobals_extend_def; SUBSET_UNION] THEN MESON_TAC[]);;
let _ = cake_add_simps [mglobals_extend_refl];;

(* HOL4: mglobals_extend_trans *)
let mglobals_extend_trans = prove
 (`!(s0:(A option) list) s1 s2 g1 g2.
     mglobals_extend s0 g1 s1 /\ mglobals_extend s1 g2 s2 ==>
     mglobals_extend s0 (g1 UNION g2) s2`,
  REWRITE_TAC[mglobals_extend_def; SUBSET; IN_UNION] THEN MESON_TAC[]);;

(* HOL4: mglobals_extend_SUBSET *)
let mglobals_extend_SUBSET = prove
 (`!(s0:(A option) list) s g1 g2.
     mglobals_extend s0 g1 s /\ g1 SUBSET g2 ==> mglobals_extend s0 g2 s`,
  REWRITE_TAC[mglobals_extend_def; SUBSET; IN_UNION] THEN MESON_TAC[]);;

(* HOL4: subspt_better_definedg *)
let subspt_better_definedg = prove
 (`!sp1 sp2 (sp3:val_approx spt).
     subspt sp1 sp3 /\ better_definedg sp1 sp2 /\ better_definedg sp2 sp3 ==>
     subspt sp1 sp2`,
  REWRITE_TAC[subspt_def; better_definedg_def] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?v1 v2. lookup k (sp1:val_approx spt) = SOME v1 /\ lookup k (sp2:val_approx spt) = SOME v2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  ASM_REWRITE_TAC[injectivity "option"] THEN MATCH_MP_TAC subapprox_antisym THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup]) THEN
  ASM_MESON_TAC[THE_DEF; injectivity "option"]);;

(* HOL4: subspt_known_elist_globals *)
let subspt_known_elist_globals = prove
 (`!c es1 as1 (g0:val_approx spt) al1 g1 es2 as2 al2 g2.
     clos_known_known c es1 as1 g0 = (al1,g1) /\ clos_known_known c es2 as2 g1 = (al2,g2) /\
     subspt g0 g2 /\ BAG_DISJOINT (clos_elist_globals es1) (clos_elist_globals es2) ==>
     subspt g0 g1 /\ subspt g1 g2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `better_definedg (g0:val_approx spt) g1 /\ better_definedg g1 g2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[known_better_definedg]; ALL_TAC] THEN
  SUBGOAL_THEN `subspt (g0:val_approx spt) g1` ASSUME_TAC THENL
   [ASM_MESON_TAC[subspt_better_definedg]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[subspt_def] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k IN domain (g2:val_approx spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[better_definedg_def]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `k IN SET_OF_BAG (clos_elist_globals es2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[known_changed_globals]; ALL_TAC] THEN
  ASM_CASES_TAC `k IN domain (g0:val_approx spt)` THENL
   [ASM_MESON_TAC[subspt_def]; ALL_TAC] THEN
  SUBGOAL_THEN `k IN SET_OF_BAG (clos_elist_globals es1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[known_changed_globals]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BAG_DISJOINT; DISJOINT; EXTENSION; IN_INTER;
                              NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[]);;

(* HOL4: subspt_known_op_elist_globals *)
let subspt_known_op_elist_globals = prove
 (`!c es as1 (g0:val_approx spt) al1 g1 opn as2 g2 a.
     clos_known_known c es as1 g0 = (al1,g1) /\ known_op opn as2 g1 = (a,g2) /\ subspt g0 g2 /\
     BAG_DISJOINT (clos_op_gbag opn) (clos_elist_globals es) ==>
     subspt g0 g1 /\ subspt g1 g2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `better_definedg (g0:val_approx spt) g1 /\ better_definedg g1 g2`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[known_better_definedg; known_op_better_definedg]; ALL_TAC] THEN
  SUBGOAL_THEN `subspt (g0:val_approx spt) g1` ASSUME_TAC THENL
   [ASM_MESON_TAC[subspt_better_definedg]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[subspt_def] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k IN domain (g2:val_approx spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[better_definedg_def]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `k IN SET_OF_BAG (clos_op_gbag opn)` ASSUME_TAC THENL
   [ASM_MESON_TAC[known_op_changed_globals]; ALL_TAC] THEN
  ASM_CASES_TAC `k IN domain (g0:val_approx spt)` THENL
   [ASM_MESON_TAC[subspt_def]; ALL_TAC] THEN
  SUBGOAL_THEN `k IN SET_OF_BAG (clos_elist_globals es)` ASSUME_TAC THENL
   [ASM_MESON_TAC[known_changed_globals]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BAG_DISJOINT; DISJOINT; EXTENSION; IN_INTER;
                              NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* fv_max                                                                    *)
(* ------------------------------------------------------------------------- *)

(* HOL4: fv_max_def *)
let fv_max_def = cake_def
  `fv_max n xs <=> !v. clos_fv v xs ==> v < n`;;

(* HOL4: fv_max_SmartOp *)
let fv_max_SmartOp = prove
 (`!n t op xs. fv_max n [clos_Op t op xs] ==> fv_max n [clos_op_SmartOp t op xs]`,
  REWRITE_TAC[fv_max_def; fv1_intro] THEN MESON_TAC[fv1_SmartOp]);;

(* HOL4: fv_alt *)
let fv_alt = prove
 (`!n xs. clos_fv n xs <=> has_var n (SND (clos_known_free xs))`,
  MATCH_MP_TAC clos_fv_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[clos_fv_def] THEN ONCE_REWRITE_TAC[clos_known_free_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def; FST; SND;
              has_var_def; has_var_mk_Union; has_var_list_mk_Union] THEN
  ASM_REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; SND; has_var_def; EX_MAP; ADD_ASSOC; GSYM EX_MEM] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FST; SND] THEN ASM_MESON_TAC[]);;

(* HOL4: fv1_alt *)
let fv1_alt = prove
 (`!n x. clos_fv1 n x <=> has_var n (SND (clos_known_free [x]))`,
  REWRITE_TAC[clos_fv1_def; fv_alt]);;

let CLOSP2AUX_fv_shift = prove
 (`!xs k n. (!v. clos_fv (v + k) xs ==> v < n) <=> (!v. clos_fv v xs ==> v < n + k)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `v:num` THEN DISCH_TAC THENL
   [ASM_CASES_TAC `v < k:num` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v - k:num`) THEN
    SUBGOAL_THEN `v - k + k = v:num` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `v + k:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* HOL4: fv_max_rw *)
let fv_max_rw = prove
 (CASE_TERM
  `!n x y xs tr v x1 x2 x3 lopt opn src_name loc vs num_args src_names fns ticks dest.
     (fv_max n [] <=> T) /\
     (fv_max n (CONS x (CONS y xs)) <=> fv_max n [x] /\ fv_max n (CONS y xs)) /\
     (fv_max n [clos_Var tr v] <=> v < n) /\
     (fv_max n [clos_If tr x1 x2 x3] <=> fv_max n [x1] /\ fv_max n [x2] /\ fv_max n [x3]) /\
     (fv_max n [clos_Let tr xs x1] <=> fv_max n xs /\ fv_max (n + LENGTH xs) [x1]) /\
     (fv_max n [clos_Raise tr x1] <=> fv_max n [x1]) /\
     (fv_max n [clos_Tick tr x1] <=> fv_max n [x1]) /\
     (fv_max n [clos_Op tr opn xs] <=> fv_max n xs) /\
     (fv_max n [clos_App tr lopt x1 xs] <=> fv_max n [x1] /\ fv_max n xs) /\
     (fv_max n [Fn src_name loc vs num_args x1] <=> fv_max (n + num_args) [x1]) /\
     (fv_max n [clos_Letrec src_names loc vs fns x1] <=>
        ALL (\p. match p with
                   (num_args,x) -> fv_max (n + num_args + LENGTH fns) [x]) fns /\
        fv_max (n + LENGTH fns) [x1]) /\
     (fv_max n [clos_Handle tr x1 x2] <=> fv_max n [x1] /\ fv_max (n + 1) [x2]) /\
     (fv_max n [clos_Call tr ticks dest xs] <=> fv_max n xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fv_max_def; clos_fv_def] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM;
              CLOSP2AUX_fv_shift; GSYM ADD_ASSOC] THEN
  REWRITE_TAC[pair_CASE_def; GSYM EX_MEM; GSYM ALL_MEM] THEN
  REPEAT CONJ_TAC THEN TRY(MESON_TAC[]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SWAP_FORALL_THM] THEN
  REWRITE_TAC[TAUT `a /\ b ==> c <=> b ==> a ==> c`; RIGHT_FORALL_IMP_THM;
              CLOSP2AUX_fv_shift]);;

(* HOL4: fv_max_mk_Ticks [simp] *)
let fv_max_mk_Ticks = prove
 (`!n t trc i e. fv_max n [clos_known_mk_Ticks t trc i e] <=> fv_max n [e]`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[mk_Ticks_alt; fv_max_rw]);;
let _ = cake_add_simps [fv_max_mk_Ticks];;

(* HOL4: fv_max_cons *)
let fv_max_cons = prove
 (`!n h t. fv_max n (CONS h t) <=> fv_max n [h] /\ fv_max n t`,
  REWRITE_TAC[fv_max_def; fv_cons; fv_nil] THEN MESON_TAC[]);;

(* HOL4: fv_max_append [simp] *)
let fv_max_append = prove
 (`!xs ys n. fv_max n (APPEND xs ys) <=> fv_max n xs /\ fv_max n ys`,
  REWRITE_TAC[fv_max_def; fv_append] THEN MESON_TAC[]);;
let _ = cake_add_simps [fv_max_append];;

(* HOL4: fv_max_less *)
let fv_max_less = prove
 (`!m n xs. fv_max m xs /\ m <= n ==> fv_max n xs`,
  REWRITE_TAC[fv_max_def] THEN MESON_TAC[LTE_TRANS]);;

let CLOSP2AUX_get_global_LUPDATE = prove
 (`!k n (x:A) gl. get_global k (LUPDATE x n gl) =
                 if k = n /\ n < LENGTH gl then SOME x else get_global k gl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_global_def; LENGTH_LUPDATE; EL_LUPDATE] THEN
  ASM_CASES_TAC `k:num = n` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_get_global_APPEND_NONE = prove
 (`!k m (gl:(A option) list) v.
     get_global k (APPEND gl (REPLICATE m NONE)) = SOME (SOME v) ==>
     get_global k gl = SOME (SOME v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_global_def; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  ASM_CASES_TAC `k < LENGTH (gl:(A option) list)` THEN
  ASM_SIMP_TAC[EL_APPEND1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  REWRITE_TAC[EL_APPEND_EQN] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `k - LENGTH (gl:(A option) list) < m` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_REPLICATE; distinctness "option"]]);;

let CLOSP2AUX_do_app_mglobals = prove
 (`!opn args (s0:(C,FFI)clos_state) v s.
     clos_do_app opn args s0 = Rval (v,s) ==>
     clos_state_compile_oracle s = clos_state_compile_oracle s0 /\
     mglobals_extend (clos_state_globals s0) (SET_OF_BAG (clos_op_gbag opn))
       (clos_state_globals s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; mglobals_extend_refl] THEN
  REWRITE_TAC[mglobals_extend_def; mapped_globals_def; SUBSET; IN_ELIM_THM; IN_UNION;
              clos_op_gbag_def; SET_OF_BAG_INSERT; BAG_OF_EMPTY; IN_INSERT; NOT_IN_EMPTY;
              CLOSP2AUX_get_global_LUPDATE] THEN
  ASM_MESON_TAC[CLOSP2AUX_get_global_APPEND_NONE]);;

let CLOSP2AUX_DO_APP_OP_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];;

let CLOSP2AUX_do_app_SetGlobal = prove
 (`!n vs (s0:(C,FFI)clos_state) v s.
     clos_do_app (GlobOp (SetGlobal n)) vs s0 = Rval (v,s) ==>
     ?x. vs = [x] /\ get_global n (clos_state_globals s0) = SOME NONE /\
         s = clos_state_globals_fupd (combin_K (LUPDATE (SOME x) n (clos_state_globals s0))) s0`,
  CLOSP2AUX_DO_APP_OP_TAC);;

let CLOSP2AUX_do_app_Global0 = prove
 (`!n (s0:(C,FFI)clos_state) v s.
     clos_do_app (GlobOp (clos_Global n)) [] s0 = Rval (v,s) ==>
     get_global n (clos_state_globals s0) = SOME (SOME v) /\ s = s0`,
  CLOSP2AUX_DO_APP_OP_TAC);;

let CLOSP2AUX_do_app_Cons = prove
 (`!tg vs (s0:(C,FFI)clos_state) v s.
     clos_do_app (BlockOp (clos_Cons tg)) vs s0 = Rval (v,s) ==>
     v = clos_Block tg vs /\ s = s0`,
  CLOSP2AUX_DO_APP_OP_TAC);;

let CLOSP2AUX_do_app_Const = prove
 (`!i vs (s0:(C,FFI)clos_state) v s.
     clos_do_app (IntOp (clos_Const i)) vs s0 = Rval (v,s) ==>
     v = clos_Number i /\ s = s0`,
  REWRITE_TAC[CLOSPROPSAUX_do_app_IntOp] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  MESON_TAC[]);;

let CLOSP2AUX_do_app_El = prove
 (`!tag xs i (s0:(C,FFI)clos_state) v s.
     clos_do_app (MemOp clos_El) [clos_Block tag xs; clos_Number i] s0 = Rval (v,s) ==>
     v = EL (num_of_int i) xs /\ s = s0 /\ &0 <= i /\ num_of_int i < LENGTH xs`,
  CLOSP2AUX_DO_APP_OP_TAC);;

let CLOSP2AUX_sga_mglobals = prove
 (`!(s0:(C,FFI)clos_state) (s:(C,FFI)clos_state) g.
     state_globals_approx s0 g /\
     mglobals_extend (clos_state_globals s0) {} (clos_state_globals s) ==>
     state_globals_approx s g`,
  REWRITE_TAC[state_globals_approx_def; mglobals_extend_def; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let CLOSP2AUX_sga_SetGlobal = prove
 (`!(s0:(C,FFI)clos_state) g n x a.
     state_globals_approx s0 g /\ get_global n (clos_state_globals s0) = SOME NONE /\
     val_approx_val a x ==>
     state_globals_approx
       (clos_state_globals_fupd (combin_K (LUPDATE (SOME x) n (clos_state_globals s0))) s0)
       (insert n a g)`,
  REWRITE_TAC[state_globals_approx_def; clos_state_INFO.ri_accfupds; K_THM;
              CLOSP2AUX_get_global_LUPDATE; lookup_insert] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `k:num = n` THEN ASM_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  ASM_MESON_TAC[]);;

(* HOL4: known_op_correct_approx *)
let known_op_correct_approx = prove
 (`!opn args (g0:val_approx spt) a g vs (s0:(C,FFI)clos_state) v s.
     known_op opn args g0 = (a,g) /\ clos_do_app opn vs s0 = Rval (v,s) /\
     ALL2 val_approx_val args vs /\ state_globals_approx s0 g0 ==>
     state_globals_approx s g /\ val_approx_val a v`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_do_app_mglobals) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_op_gbag_def; BAG_OF_EMPTY; LIST_REL_CONS1;
                              LIST_REL_NIL; val_approx_val_simps; NULL_EQ_NIL]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN RVEQ_TAC THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_do_app_El)) THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_do_app_Cons)) THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_do_app_Const)) THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_do_app_Global0)) THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_do_app_SetGlobal) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL]) THEN
      POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[val_approx_val_simps] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_sga_mglobals THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_sga_SetGlobal THEN
      ASM_MESON_TAC[val_approx_val_merge_I] THEN NO_TAC) THEN
  ASM_MESON_TAC[LIST_REL_EL_EQN; state_globals_approx_def]);;

(* HOL4: ssgc_free_co_shift_seq *)
let ssgc_free_co_shift_seq = prove
 (`!s:(C,FFI)clos_state.
     ssgc_free s ==>
     !k. ssgc_free (clos_state_compile_oracle_fupd
                      (combin_K (shift_seq k (clos_state_compile_oracle s))) s)`,
  REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds; K_THM; shift_seq_def] THEN
  MESON_TAC[]);;

let CLOSP2AUX_elist_empty_MEM = prove
 (`!es e. clos_elist_globals es = EMPTY_BAG /\ MEM e es ==> clos_set_globals e = EMPTY_BAG`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_set_globals_def; MEM; BAG_UNION_EMPTY] THEN
  ASM_MESON_TAC[]);;

(* HOL4: ssgc_free_do_install *)
let ssgc_free_do_install = prove
 (`!s:(C,FFI)clos_state.
     ssgc_free s ==>
     ssgc_free (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s)))
                  (clos_state_code_fupd
                     (combin_K (clos_state_code s |++ SND (SND (clos_state_compile_oracle s 0)))) s))`,
  GEN_TAC THEN REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[flookup_fupdate_list] THEN
    MP_TAC(ISPEC `ALOOKUP (REVERSE (SND (SND (clos_state_compile_oracle (s:(C,FFI)clos_state) 0)))) n`
             (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[] THEN
                                           ASM_MESON_TAC[])
                                (X_CHOOSE_THEN `p:num#clos_exp` (fun th ->
                                   REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[] THEN
                                   MP_TAC(MATCH_MP ALOOKUP_MEM th)))) THEN
    REWRITE_TAC[MEM_REVERSE; injectivity "option"] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`0`; `FST (SND (clos_state_compile_oracle (s:(C,FFI)clos_state) 0))`;
       `SND (SND (clos_state_compile_oracle (s:(C,FFI)clos_state) 0))`]) THEN
    REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSP2AUX_elist_empty_MEM THEN
    EXISTS_TAC `MAP (SND o SND) (SND (SND (clos_state_compile_oracle (s:(C,FFI)clos_state) 0)))` THEN
    ASM_REWRITE_TAC[MEM_MAP; o_THM] THEN EXISTS_TAC `(n:num,(m:num,e:clos_exp))` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[shift_seq_def] THEN ASM_MESON_TAC[]]);;

let CLOSP2AUX_do_install_Rval = prove
 (`!vs (s0:(C,FFI)clos_state) es s1.
     clos_do_install vs s0 = (Rval es,s1) ==>
     FST (SND (clos_state_compile_oracle s0 0)) = es /\ ~(es = []) /\
     s1 = clos_state_code_fupd
            (combin_K (clos_state_code s0 |++ SND (SND (clos_state_compile_oracle s0 0))))
            (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s0)))
               (clos_state_clock_fupd (combin_K (clos_state_clock s0 - 1)) s0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (CLOSP2AUX_GPAIR_TAC ORELSE TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FST; SND]);;

(* HOL4: do_install_ssgc *)
let do_install_ssgc = prove
 (`!vs (s0:(C,FFI)clos_state) es s1.
     clos_do_install vs s0 = (Rval es,s1) /\ ssgc_free s0 ==>
     ssgc_free s1 /\ ALL clos_esgc_free es /\ ~(es = []) /\
     clos_state_compile_oracle s1 = shift_seq 1 (clos_state_compile_oracle s0) /\
     first_n_exps (clos_state_compile_oracle s0) 1 = [es] /\
     mglobals_extend (clos_state_globals s0) EMPTY (clos_state_globals s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_do_install_Rval) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; mglobals_extend_refl] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(MATCH_MP ssgc_free_do_install (ASSUME `ssgc_free (s0:(C,FFI)clos_state)`)) THEN
    REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds; K_THM];
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                  REWRITE_RULE[ssgc_free_def]) THEN
    DISCH_THEN(MP_TAC o SPECL
      [`0`; `FST (SND (clos_state_compile_oracle (s0:(C,FFI)clos_state) 0))`;
       `SND (SND (clos_state_compile_oracle (s0:(C,FFI)clos_state) 0))`]) THEN
    ASM_REWRITE_TAC[PAIR] THEN MESON_TAC[];
    REWRITE_TAC[first_n_exps_def; num_CONV `1`; list_of_seq; o_THM; APPEND] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 705: value_ind, an ML value (an instance of the induction     *)
(* theorem of closSem$v)                                                     *)

(* HOL4: not_less_zero_imp [local] *)
let not_less_zero_imp = prove
 (`!i:int. ~(i < &0) ==> ?k. i = &k`,
  GEN_TAC THEN REWRITE_TAC[INT_NOT_LT] THEN DISCH_TAC THEN
  EXISTS_TAC `num_of_int i` THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let CLOSP2AUX_vsgc_make_const = prove
 (`!c. vsgc_free (make_const c)`,
  MATCH_MP_TAC make_const_ind THEN REWRITE_TAC[make_const_def; vsgc_free_def] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN MESON_TAC[]);;

let CLOSP2AUX_vsgc_list_to_v = prove
 (`!xs. vsgc_free (clos_list_to_v xs) <=> ALL vsgc_free xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_list_to_v_def; vsgc_free_def; ALL]);;

let CLOSP2AUX_vsgc_v_to_list = prove
 (`!v xs. clos_v_to_list v = SOME xs /\ vsgc_free v ==> ALL vsgc_free xs`,
  MATCH_MP_TAC clos_v_to_list_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_v_to_list_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"; vsgc_free_def; ALL] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_vsgc_do_int_app = prove
 (`!i vs v. clos_do_int_app i vs = SOME v ==> vsgc_free v`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CLOSPROPSAUX_tree "clos_do_int_app"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[vsgc_free_def; clos_Boolv_def; ALL]);;

let CLOSP2AUX_vsgc_do_word_app = prove
 (`!i vs v. clos_do_word_app i vs = SOME v ==> vsgc_free v`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CLOSPROPSAUX_tree "clos_do_word_app"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[vsgc_free_def; clos_Boolv_def; ALL]);;

let CLOSP2AUX_get_global_MEM = prove
 (`!n gl (v:A). get_global n gl = SOME (SOME v) ==> MEM (SOME v) gl`,
  REWRITE_TAC[get_global_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  ASM_MESON_TAC[MEM_EL]);;

let CLOSP2AUX_ssgc_refs_upd = prove
 (`!(s0:(C,FFI)clos_state) p X.
     ssgc_free s0 /\ (!vl. X = clos_ValueArray vl ==> ALL vsgc_free vl) /\
     (!m v. X = clos_Thunk m v ==> vsgc_free v) ==>
     ssgc_free (clos_state_refs_fupd (combin_K (clos_state_refs s0 |+ (p,X))) s0)`,
  REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_ssgc_ffi_refs_upd = prove
 (`!(s0:(C,FFI)clos_state) p X f.
     ssgc_free s0 /\ (!vl. X = clos_ValueArray vl ==> ALL vsgc_free vl) /\
     (!m v. X = clos_Thunk m v ==> vsgc_free v) ==>
     ssgc_free (clos_state_refs_fupd (combin_K (clos_state_refs s0 |+ (p,X)))
                  (clos_state_ffi_fupd f s0))`,
  REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_ssgc_globals_upd = prove
 (`!(s0:(C,FFI)clos_state) gl.
     ssgc_free s0 /\ (!v. MEM (SOME v) gl ==> vsgc_free v) ==>
     ssgc_free (clos_state_globals_fupd (combin_K gl) s0)`,
  REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

let CLOSP2AUX_SGC_STATE_TAC : tactic =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC CLOSP2AUX_ssgc_refs_upd THEN ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN
           REPEAT STRIP_TAC THEN RVEQ_TAC THEN
           ASM_REWRITE_TAC[EVERY_REPLICATE] THEN NO_TAC;
         MATCH_MP_TAC CLOSP2AUX_ssgc_ffi_refs_upd THEN ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN NO_TAC;
         MATCH_MP_TAC CLOSP2AUX_ssgc_globals_upd THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         ALL_TAC];;

let CLOSP2AUX_do_app_sgc = prove
 (`!opn args (s0:(C,FFI)clos_state) v s.
     clos_do_app opn args s0 = Rval (v,s) /\ ALL vsgc_free args /\ ssgc_free s0 ==>
     vsgc_free v /\ ssgc_free s`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[ALL] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[vsgc_free_def; ALL; clos_Boolv_def; clos_Unit_def;
                 CLOSP2AUX_vsgc_list_to_v; CLOSP2AUX_vsgc_make_const; ALL_MAP; o_DEF;
                 ALL_APPEND] THEN ASM_REWRITE_TAC[];
     CLOSP2AUX_SGC_STATE_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[vsgc_free_def]) THEN
  FIRST
   [MATCH_ACCEPT_TAC ALL_T;
    MATCH_MP_TAC CLOSP2AUX_ssgc_refs_upd THEN
      ASM_REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN
      REPEAT STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC IMP_EVERY_LUPDATE THEN
      ASM_MESON_TAC[ssgc_free_def];
    MATCH_MP_TAC CLOSP2AUX_ssgc_globals_upd THEN
      ASM_REWRITE_TAC[MEM_APPEND; MEM_REPLICATE; distinctness "option"] THEN
      ASM_MESON_TAC[ssgc_free_def; MEM_LUPDATE_E; injectivity "option"];
    ASM_MESON_TAC[ssgc_free_def; EVERY_EL; CLOSP2AUX_get_global_MEM;
                  CLOSP2AUX_vsgc_v_to_list; CLOSP2AUX_vsgc_do_word_app;
                  CLOSP2AUX_vsgc_do_int_app; EVERY_TAKE; EVERY_DROP;
                  BASICAUX_num_of_int_lt]]);;

(* HOL4: do_app_ssgc *)
let do_app_ssgc = prove
 (`!opn args (s0:(C,FFI)clos_state) res.
     clos_do_app opn args s0 = res /\ ALL vsgc_free args /\ ssgc_free s0 ==>
     (!v s. res = Rval (v,s) ==>
            vsgc_free v /\ ssgc_free s /\
            clos_state_compile_oracle s = clos_state_compile_oracle s0 /\
            mglobals_extend (clos_state_globals s0) (SET_OF_BAG (clos_op_gbag opn))
              (clos_state_globals s)) /\
     (!v. res = Rerr (Rraise v) ==> vsgc_free v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[CLOSPROPSAUX_do_app_not_Rraise] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_MESON_TAC[CLOSP2AUX_do_app_sgc; CLOSP2AUX_do_app_mglobals]);;

let CLOSP2AUX_EL_SND_MEM = prove
 (`!i (fns:(num#clos_exp)list) n e.
     EL i fns = (n,e) /\ i < LENGTH fns ==> MEM e (MAP SND fns)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(n:num,e:clos_exp)` THEN
  REWRITE_TAC[SND] THEN ASM_MESON_TAC[MEM_EL]);;

(* HOL4: dest_closure_Full_sgc_free *)
let dest_closure_Full_sgc_free = prove
 (`!max_app loc_opt f arg0 args fbody env rest_args.
     dest_closure max_app loc_opt f (CONS arg0 args) =
       SOME (Full_app fbody env rest_args) /\
     vsgc_free f /\ vsgc_free arg0 /\ ALL vsgc_free args ==>
     clos_set_globals fbody = EMPTY_BAG /\ ALL vsgc_free env /\ ALL vsgc_free rest_args`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_closure_def] THEN
  STRUCT_CASES_TAC (ISPEC `f:clos_v` (CONJUNCT1 (cases "clos_v"))) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (CLOSP2AUX_GPAIR_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[vsgc_free_def; DE_MORGAN_THM; NOT_LE]) THEN
  ASM_REWRITE_TAC[ALL_APPEND; EVERY_REVERSE; ALL] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC EVERY_TAKE THEN ASM_REWRITE_TAC[EVERY_REVERSE; ALL] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC EVERY_DROP THEN ASM_REWRITE_TAC[EVERY_REVERSE; ALL] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[EVERY_GENLIST; vsgc_free_def; ALL] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[CLOSP2AUX_elist_empty_MEM; CLOSP2AUX_EL_SND_MEM]);;

(* HOL4: update_thunk_ssgc_free [local] *)
let update_thunk_ssgc_free = prove
 (`!(s:(C,FFI)clos_state) vs v ptr refs.
     ssgc_free s /\ ALL vsgc_free vs /\
     clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s) vs = SOME refs ==>
     ssgc_free (clos_state_refs_fupd (combin_K refs) s)`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CLOSPROPSAUX_tree "clos_update_thunk"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[store_thunk_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CLOSP2AUX_ssgc_refs_upd THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
  ASM_REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_shift_seq_add2 = prove
 (`!(co:num->A) k1 k2. shift_seq k2 (shift_seq k1 co) = shift_seq (k2 + k1) co`,
  REPEAT GEN_TAC THEN REWRITE_TAC[shift_seq_add] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let CLOSP2AUX_dec_clock_acc = prove
 (`!n (s:(C,FFI)clos_state).
     clos_state_compile_oracle (clos_dec_clock n s) = clos_state_compile_oracle s /\
     clos_state_globals (clos_dec_clock n s) = clos_state_globals s /\
     clos_state_code (clos_dec_clock n s) = clos_state_code s /\
     clos_state_refs (clos_dec_clock n s) = clos_state_refs s /\
     clos_state_max_app (clos_dec_clock n s) = clos_state_max_app s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;

let CLOSP2AUX_first_n_exps_0 = prove
 (`!co:num->A#B#C. first_n_exps co 0 = []`,
  REWRITE_TAC[first_n_exps_def; list_of_seq]);;

let CLOSP2AUX_CG_N_TAC : tactic = fun (asl,w as gl) ->
  let co_c = `clos_state_compile_oracle:(C,FFI)clos_state->num->C#clos_prog` in
  let co_of t = let f,a = dest_comb t in
                if f = co_c then a else failwith "co_of" in
  let nv,body = dest_exists w in
  let c1,c2 = dest_conj body in
  let s_fin = co_of (lhs c1) in
  let s_init = co_of (rand (rhs c1)) in
  let cofacts = mapfilter (fun (_,th) ->
      let l,r = dest_eq (concl th) in
      let b = co_of l in
      (try let f,args = strip_comb r in
           if fst(dest_const f) = "shift_seq" && length args = 2
           then (b,(co_of (el 1 args), Some (el 0 args), th)) else failwith ""
       with Failure _ -> (b,(co_of r, None, th)))) asl in
  let rec chain s = if s = s_init then [] else
     let (a,n,th) = assoc s cofacts in (a,s,n,th) :: chain a in
  let ch = rev (chain s_fin) in
  let ns = mapfilter (fun (_,_,n,_) -> match n with Some t -> t | None -> failwith "") ch in
  let witness = match rev ns with [] -> `0` | l -> end_itlist (fun a b -> mk_binop `(+):num->num->num` a b) l in
  let gl_c = `clos_state_globals:(C,FFI)clos_state->(clos_v option)list` in
  let mgfact a b =
    let ok th = try let f,args = strip_comb (concl th) in
                    fst(dest_const f) = "mglobals_extend" &&
                    el 0 args = mk_comb(gl_c,a) && el 2 args = mk_comb(gl_c,b)
                with Failure _ -> false in
    snd (find (fun (_,th) -> ok th) asl) in
  let mgs = map (fun (a,b,_,_) -> mgfact a b) ch in
  let total = match mgs with
      [] -> ISPECL [mk_comb(gl_c,s_init); `{}:num->bool`] mglobals_extend_refl
    | th::ths -> rev_itlist (fun th2 acc -> MATCH_MP mglobals_extend_trans (CONJ acc th2)) ths th in
  let cothms = map (fun (_,_,_,th) -> th) ch in
  let fnes = mapfilter (fun (_,th) ->
      let l = lhs (concl th) in
      if fst(dest_const(fst(strip_comb l))) = "first_n_exps"
      then REWRITE_RULE[CLOSP2AUX_shift_seq_add2; GSYM ADD_ASSOC]
             (REWRITE_RULE cothms (REWRITE_RULE cothms (REWRITE_RULE cothms th)))
      else failwith "") asl in
  let sgfacts = mapfilter (fun (_,th) ->
      let l,r = dest_eq (concl th) in
      if fst(dest_const(fst(strip_comb l))) = "clos_set_globals" && r = `EMPTY_BAG:num->num`
      then th else failwith "") asl in
  (EXISTS_TAC witness THEN CONJ_TAC THENL
    [REWRITE_TAC cothms THEN REWRITE_TAC cothms THEN REWRITE_TAC cothms THEN
     REWRITE_TAC[CLOSP2AUX_shift_seq_add2; shift_seq_zero; GSYM ADD_ASSOC];
     MATCH_MP_TAC mglobals_extend_SUBSET THEN
     EXISTS_TAC (rand(rator(concl total))) THEN CONJ_TAC THENL
      [ACCEPT_TAC total;
       REWRITE_TAC cothms THEN REWRITE_TAC cothms THEN REWRITE_TAC cothms THEN
       REWRITE_TAC[CLOSP2AUX_shift_seq_add2; shift_seq_zero; GSYM ADD_ASSOC] THEN
       REWRITE_TAC[first_n_exps_shift_seq] THEN REWRITE_TAC fnes THEN
       REWRITE_TAC[FLAT_APPEND; clos_elist_globals_append; FLAT; APPEND_NIL;
                   SET_OF_BAG_UNION; clos_set_globals_def; BAG_UNION_EMPTY;
                   CLOSP2AUX_first_n_exps_0; BAG_OF_EMPTY; APPEND;
                   clos_AppUnit_def; clos_op_gbag_def] THEN
       REWRITE_TAC sgfacts THEN REWRITE_TAC[BAG_OF_EMPTY; UNION_EMPTY] THEN
       SET_TAC[]]]) gl;;

let CLOSP2AUX_CG_SING_TAC : tactic =
  let is_cand th =
    try let l,r = dest_eq (concl th) in
        let f,a = dest_comb l in
        fst(dest_const f) = "clos_evaluate" &&
        (let es = fst(dest_pair a) in
         length (dest_list es) = 1) &&
        (let res = fst(dest_pair r) in
         let c,x = dest_comb res in
         fst(dest_const c) = "Rval" && is_var x)
    with Failure _ -> false in
  REPEAT(FIRST_ASSUM(fun th -> if is_cand th then
    let x = rand(fst(dest_pair(rhs(concl th)))) in
    X_CHOOSE_THEN (mk_var("v_"^fst(dest_var x), `:clos_v`)) SUBST_ALL_TAC
      (MATCH_MP clos_evaluate_SING th)
  else NO_TAC));;

let CLOSP2AUX_CG_RES_TAC : tactic =
  let rw = REWRITE_RULE[HD; EVERY_REVERSE; ALL] in
  fun (asl,w as gl) ->
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let asms = map snd asl in
  let rec full depth th =
    if not (is_impth th) then Some th else if depth = 0 then None else
    let mth = try MATCH_MP th with Failure _ -> fun _ -> failwith "MATCH_MP" in
    let rec try_list l = match l with
        [] -> None
      | a::rest -> (match (try Some (rw (mth a)) with Failure _ -> None) with
                      Some th' -> (match full (depth-1) th' with
                                     Some r -> Some r | None -> try_list rest)
                    | None -> try_list rest) in
    try_list asms in
  let rec go l = match l with
      [] -> failwith "CLOSP2AUX_CG_RES_TAC"
    | (lab,th)::rest ->
        if is_impth th then
          (match full 8 (curry th) with
             Some r -> (r,th)
           | None -> go rest)
        else go rest in
  let r,ih = go asl in
  (UNDISCH_THEN (concl ih) (K ALL_TAC) THEN CAKE_STRIP_ASSUME_TAC r) gl;;

let CLOSP2AUX_CG_NRM_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[ssgc_free_dec_clock; ssgc_free_clockupd;
    CLOSP2AUX_dec_clock_acc; clos_state_INFO.ri_accfupds; K_THM;
    clos_esgc_free_def; ALL; ALL_APPEND; rsgc_free_def; NOT_CONS_NIL;
    OPTION_MAP_EQ_SOME]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) || is_exists (concl th)
                                 then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN TRY RVEQ_TAC THEN
  CLOSP2AUX_CG_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; HD]);;

let CLOSP2AUX_ALL_EL = prove
 (`!(P:A->bool) l n. ALL P l /\ n < LENGTH l ==> P (EL n l)`,
  MESON_TAC[EVERY_EL]);;

let CLOSP2AUX_ALL_LAST = prove
 (`!(P:A->bool) l. ALL P l /\ ~(l = []) ==> P (LAST l)`,
  MESON_TAC[MEM_LAST_NOT_NIL; ALL_MEM]);;

let CLOSP2AUX_CG_RSGC_TAC : tactic =
  TRY RVEQ_TAC THEN ASM_REWRITE_TAC[rsgc_free_def] THEN
  (fun (asl,w as g) ->
     try let c,x = dest_comb w in
         if fst(dest_const c) = "rsgc_free" && is_var (rand x) then
           (CASES_ON (rand x) THEN ASM_REWRITE_TAC[rsgc_free_def] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[rsgc_free_def; CLOSPROPSAUX_do_app_not_Rraise]) THEN
            TRY(FIRST_ASSUM CONTR_TAC) THEN TRY(FIRST_ASSUM ACCEPT_TAC)) g
         else ALL_TAC g
     with Failure _ -> ALL_TAC g);;

let CLOSP2AUX_CG_FIN_TAC : tactic =
  REWRITE_TAC[ssgc_free_dec_clock; ssgc_free_clockupd; CLOSP2AUX_dec_clock_acc;
              clos_state_INFO.ri_accfupds; K_THM; rsgc_free_def; ALL; HD] THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w as g) ->
     if is_exists w then CLOSP2AUX_CG_N_TAC g
     else (TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REWRITE_TAC[] THEN
           TRY(MATCH_MP_TAC CLOSP2AUX_ALL_LAST THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
           TRY(MATCH_MP_TAC CLOSP2AUX_ALL_EL THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
           TRY(REWRITE_TAC[vsgc_free_def; ALL] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
           CLOSP2AUX_CG_RSGC_TAC) g);;

let CLOSP2AUX_dest_thunk_sgc = prove
 (`!vs (s:(C,FFI)clos_state) m v.
     clos_dest_thunk vs (clos_state_refs s) = clos_IsThunk m v /\ ssgc_free s ==>
     vsgc_free v`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [CLOSPROPSAUX_tree "clos_dest_thunk"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[distinctness "clos_dest_thunk_ret"; injectivity "clos_dest_thunk_ret"] THEN
  REWRITE_TAC[ssgc_free_def] THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_find_code_sgc = prove
 (`!dest (vs:clos_v list) (s:(C,FFI)clos_state) args exp.
     clos_find_code dest vs (clos_state_code s) = SOME (args,exp) /\ ssgc_free s ==>
     args = vs /\ clos_esgc_free exp /\ clos_set_globals exp = EMPTY_BAG`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_find_code_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `clos_set_globals exp = EMPTY_BAG` ASSUME_TAC THENL
   [ASM_MESON_TAC[ssgc_free_def]; ASM_SIMP_TAC[set_globals_empty_esgc_free]]);;

let CLOSP2AUX_dest_closure_sgc = prove
 (`!max_app loc_opt f arg0 args fbody env rest_args.
     dest_closure max_app loc_opt f (CONS arg0 args) =
       SOME (Full_app fbody env rest_args) /\
     vsgc_free f /\ vsgc_free arg0 /\ ALL vsgc_free args ==>
     clos_esgc_free fbody /\ clos_set_globals fbody = EMPTY_BAG /\
     ALL vsgc_free env /\ ALL vsgc_free rest_args`,
  MESON_TAC[dest_closure_Full_sgc_free; set_globals_empty_esgc_free]);;

let CLOSP2AUX_AppUnit_esgc = prove
 (`!x. clos_esgc_free (clos_AppUnit x) <=> clos_esgc_free x`,
  REWRITE_TAC[clos_AppUnit_def; clos_esgc_free_def; ALL]);;

let CLOSP2AUX_do_install_Rerr = prove
 (`!vs (s0:(C,FFI)clos_state) e s1.
     clos_do_install vs s0 = (Rerr e,s1) /\ ssgc_free s0 ==>
     ssgc_free s1 /\ (?a. e = Rabort a) /\
     ?k. clos_state_compile_oracle s1 = shift_seq k (clos_state_compile_oracle s0) /\
         mglobals_extend (clos_state_globals s0) {} (clos_state_globals s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (CLOSP2AUX_GPAIR_TAC ORELSE TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[injectivity "error_result"] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; mglobals_extend_refl] THEN
  TRY(CONJ_TAC THENL [ALL_TAC; MESON_TAC[shift_seq_zero]]) THEN
  TRY(CONJ_TAC THENL [ALL_TAC; MESON_TAC[]]) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MP_TAC(MATCH_MP ssgc_free_do_install (ASSUME `ssgc_free (s0:(C,FFI)clos_state)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REWRITE_TAC[ssgc_free_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_MESON_TAC[SND]);;

let CLOSP2AUX_update_thunk_ssgc = prove
 (`!(s:(C,FFI)clos_state) vs vs2 refs.
     clos_update_thunk vs (clos_state_refs s) vs2 = SOME refs /\
     ssgc_free s /\ ALL vsgc_free vs2 ==>
     ssgc_free (clos_state_refs_fupd (combin_K refs) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CLOSPROPSAUX_tree "clos_update_thunk"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[store_thunk_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSP2AUX_ssgc_refs_upd THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
  ASM_REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_eval_nonempty = prove
 (`!xs env (s:(C,FFI)clos_state) res s1.
     clos_evaluate (xs,env,s) = (Rval res,s1) /\ ~(xs = []) ==> ~(res = [])`,
  MESON_TAC[clos_evaluate_IMP_LENGTH; LENGTH_EQ_NIL]);;

let CLOSP2AUX_vsgc_recc = prove
 (`!fns (env:clos_v list) loc n.
     clos_elist_globals (MAP SND fns) = EMPTY_BAG /\ ALL vsgc_free env ==>
     ALL vsgc_free (list_of_seq (clos_Recclosure loc [] env fns) n)`,
  REWRITE_TAC[EVERY_GENLIST; vsgc_free_def; ALL] THEN MESON_TAC[]);;

let CLOSP2AUX_dest_closure_partial_sgc = prove
 (`!max_app loc_opt f arg0 args v.
     dest_closure max_app loc_opt f (CONS arg0 args) = SOME (Partial_app v) /\
     vsgc_free f /\ vsgc_free arg0 /\ ALL vsgc_free args ==>
     vsgc_free v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_closure_def] THEN
  STRUCT_CASES_TAC (ISPEC `f:clos_v` (CONJUNCT1 (cases "clos_v"))) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (CLOSP2AUX_GPAIR_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[vsgc_free_def]) THEN
  ASM_REWRITE_TAC[vsgc_free_def; ALL_APPEND; ALL]);;

let CLOSP2AUX_CG_RECC_TAC : tactic = fun (asl,w as g) ->
  let is_recc t =
    try let f,args = strip_comb t in
        fst(dest_const f) = "list_of_seq" && length args = 2 &&
        (let h,_ = strip_comb (hd args) in fst(dest_const h) = "clos_Recclosure")
    with Failure _ -> false in
  let tms = setify (find_terms is_recc (list_mk_conj (map (concl o snd) asl))) in
  let tms = filter (fun t -> subset (frees t) (freesl (map (concl o snd) asl))) tms in
  MAP_EVERY (fun t ->
    let goal = mk_comb(`ALL vsgc_free`, t) in
    TRY(SUBGOAL_THEN goal ASSUME_TAC THENL
          [MATCH_MP_TAC CLOSP2AUX_vsgc_recc THEN ASM_REWRITE_TAC[] THEN
           ASM_MESON_TAC[EVERY_lookup_vars]; ALL_TAC])) tms g;;

let CLOSP2AUX_cg_side = [CLOSP2AUX_dest_closure_partial_sgc; do_install_ssgc; CLOSP2AUX_do_install_Rerr;
  CLOSP2AUX_do_app_sgc; CLOSP2AUX_do_app_mglobals;
  CLOSP2AUX_dest_closure_sgc; CLOSP2AUX_update_thunk_ssgc; CLOSP2AUX_dest_thunk_sgc;
  CLOSP2AUX_find_code_sgc; EVERY_lookup_vars; CLOSP2AUX_eval_nonempty];;

let CLOSP2AUX_CG_CASE_TAC : tactic =
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSPROPSAUX_SPLIT_TAC THEN
  CLOSP2AUX_CG_NRM_TAC THEN
  MAP_EVERY (fun th -> ASSUME_TAC th) CLOSP2AUX_cg_side THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP2AUX_AppUnit_esgc]) THEN
  REPEAT(CLOSP2AUX_CG_RES_TAC THEN CLOSP2AUX_CG_NRM_TAC) THEN
  CLOSP2AUX_CG_RECC_TAC THEN
  REPEAT(CLOSP2AUX_CG_RES_TAC THEN CLOSP2AUX_CG_NRM_TAC) THEN
  CLOSP2AUX_CG_FIN_TAC;;

let CLOSP2AUX_cg_P = `\es env (s0:(C,FFI)clos_state).
   !res s. ssgc_free s0 /\ ALL clos_esgc_free es /\ ALL vsgc_free env /\
      clos_evaluate (es,env,s0) = (res,s) ==>
      ssgc_free s /\ rsgc_free res /\
      ?n. clos_state_compile_oracle s = shift_seq n (clos_state_compile_oracle s0) /\
          mglobals_extend (clos_state_globals s0)
            (SET_OF_BAG (clos_elist_globals es) UNION
             SET_OF_BAG (clos_elist_globals
                           (FLAT (first_n_exps (clos_state_compile_oracle s0) n))))
            (clos_state_globals s)`;;

let CLOSP2AUX_cg_Q = `\loc_opt f args (s0:(C,FFI)clos_state).
   !res s. ssgc_free s0 /\ vsgc_free f /\ ALL vsgc_free args /\
      evaluate_app loc_opt f args s0 = (res,s) ==>
      ssgc_free s /\ rsgc_free res /\
      ?n. clos_state_compile_oracle s = shift_seq n (clos_state_compile_oracle s0) /\
          mglobals_extend (clos_state_globals s0)
            (SET_OF_BAG (clos_elist_globals
                           (FLAT (first_n_exps (clos_state_compile_oracle s0) n))))
            (clos_state_globals s)`;;

let CLOSP2AUX_cg_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [CLOSP2AUX_cg_P; CLOSP2AUX_cg_Q] CLOSPROPSAUX_evaluate_ind);;

let CLOSP2AUX_cg_cases = conjuncts (lhand (concl CLOSP2AUX_cg_ind));;

let CLOSP2AUX_cg_thms = map (fun t -> prove(t, CLOSP2AUX_CG_CASE_TAC)) CLOSP2AUX_cg_cases;;

(* HOL4: evaluate_changed_globals_0 [local] *)
let evaluate_changed_globals_0 = prove
 (`(!es env (s0:(C,FFI)clos_state) res s.
      clos_evaluate (es,env,s0) = (res,s) /\
      ssgc_free s0 /\ ALL clos_esgc_free es /\ ALL vsgc_free env ==>
      ssgc_free s /\ rsgc_free res /\
      ?n. clos_state_compile_oracle s = shift_seq n (clos_state_compile_oracle s0) /\
          mglobals_extend (clos_state_globals s0)
            (SET_OF_BAG (clos_elist_globals es) UNION
             SET_OF_BAG (clos_elist_globals
                           (FLAT (first_n_exps (clos_state_compile_oracle s0) n))))
            (clos_state_globals s)) /\
   (!loc_opt f args (s0:(C,FFI)clos_state) res s.
      evaluate_app loc_opt f args s0 = (res,s) /\
      ssgc_free s0 /\ vsgc_free f /\ ALL vsgc_free args ==>
      ssgc_free s /\ rsgc_free res /\
      ?n. clos_state_compile_oracle s = shift_seq n (clos_state_compile_oracle s0) /\
          mglobals_extend (clos_state_globals s0)
            (SET_OF_BAG (clos_elist_globals
                           (FLAT (first_n_exps (clos_state_compile_oracle s0) n))))
            (clos_state_globals s))`,
  MP_TAC(MP CLOSP2AUX_cg_ind (end_itlist CONJ CLOSP2AUX_cg_thms)) THEN
  MESON_TAC[]);;

(* HOL4: evaluate_changed_globals (= CONJUNCT1 evaluate_changed_globals_0) *)
let evaluate_changed_globals = CONJUNCT1 evaluate_changed_globals_0;;

(* HOL4: evaluate_app_changed_globals (= CONJUNCT2 evaluate_changed_globals_0) *)
let evaluate_app_changed_globals = CONJUNCT2 evaluate_changed_globals_0;;

(* HOL4: mk_Ticks_set_globals [simp] *)
let mk_Ticks_set_globals = prove
 (`!t tc n exp. clos_set_globals (clos_known_mk_Ticks t tc n exp) = clos_set_globals exp`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[mk_Ticks_alt; clos_set_globals_def]);;
let _ = cake_add_simps [mk_Ticks_set_globals];;

(* HOL4: gapprox_disjoint_def *)
let gapprox_disjoint_def = cake_def
  `gapprox_disjoint (g:val_approx spt) xs <=>
     DISJOINT (domain g) (SET_OF_BAG (clos_elist_globals xs))`;;

(* HOL4: gapprox_disjoint_rw *)
let gapprox_disjoint_rw = prove
 (`!(g:val_approx spt) x y xs tr opn.
     (gapprox_disjoint g (CONS x (CONS y xs)) <=>
        gapprox_disjoint g [x] /\ gapprox_disjoint g (CONS y xs)) /\
     (gapprox_disjoint g [clos_Op tr opn xs] <=>
        gapprox_disjoint g xs /\ DISJOINT (domain g) (SET_OF_BAG (clos_op_gbag opn)))`,
  REWRITE_TAC[gapprox_disjoint_def; clos_set_globals_def; SET_OF_BAG_UNION;
              BAG_UNION_EMPTY] THEN SET_TAC[]);;

(* HOL4: oracle_gapprox_disjoint_def *)
let oracle_gapprox_disjoint_def = cake_def
  `oracle_gapprox_disjoint (g:val_approx spt) (co:num -> A # clos_exp list # B) <=>
     !n. gapprox_disjoint g (FST (SND (co n)))`;;

(* HOL4: oracle_gapprox_disjoint_shift_seq *)
let oracle_gapprox_disjoint_shift_seq = prove
 (`!(g:val_approx spt) (co:num -> A # clos_exp list # B).
     oracle_gapprox_disjoint g co ==> !k. oracle_gapprox_disjoint g (shift_seq k co)`,
  REWRITE_TAC[oracle_gapprox_disjoint_def; shift_seq_def] THEN MESON_TAC[]);;

(* HOL4: oracle_gapprox_disjoint_evaluate *)
let oracle_gapprox_disjoint_evaluate = prove
 (`!(g:val_approx spt) (s0:(C,FFI)clos_state) es env res s1.
     oracle_gapprox_disjoint g (clos_state_compile_oracle s0) /\
     clos_evaluate (es,env,s0) = (res,s1) ==>
     oracle_gapprox_disjoint g (clos_state_compile_oracle s1)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_code) THEN
  ASM_SIMP_TAC[oracle_gapprox_disjoint_shift_seq]);;

(* HOL4: oracle_gapprox_disjoint_first_n_exps *)
let oracle_gapprox_disjoint_first_n_exps = prove
 (`!(g:val_approx spt) (co:num -> A # clos_exp list # B).
     oracle_gapprox_disjoint g co <=> !n. gapprox_disjoint g (FLAT (first_n_exps co n))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[oracle_gapprox_disjoint_def; gapprox_disjoint_def; first_n_exps_def] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[list_of_seq; FLAT; clos_set_globals_def; BAG_OF_EMPTY;
                    DISJOINT_EMPTY; FLAT_APPEND; clos_elist_globals_append;
                    SET_OF_BAG_UNION; o_THM; APPEND_NIL; BAG_UNION_EMPTY] THEN
    ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN
    REWRITE_TAC[list_of_seq; FLAT_APPEND; clos_elist_globals_append; FLAT;
                SET_OF_BAG_UNION; o_THM; APPEND_NIL] THEN SET_TAC[]]);;

(* HOL4: mk_Ticks_esgc_free [simp] *)
let mk_Ticks_esgc_free = prove
 (`!t tc n exp. clos_esgc_free (clos_known_mk_Ticks t tc n exp) <=> clos_esgc_free exp`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[mk_Ticks_alt; clos_esgc_free_def]);;
let _ = cake_add_simps [mk_Ticks_esgc_free];;

let CLOSP2AUX_gsgc_insert = prove
 (`!(g:val_approx spt) n v.
     globals_approx_sgc_free g /\ val_approx_sgc_free v ==>
     globals_approx_sgc_free (insert n v g)`,
  REWRITE_TAC[globals_approx_sgc_free_def; lookup_insert] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

(* HOL4: known_op_preserves_esgc_free *)
let known_op_preserves_esgc_free = prove
 (`!opn args (g0:val_approx spt) a g.
     known_op opn args g0 = (a,g) /\ ALL val_approx_sgc_free args /\
     globals_approx_sgc_free g0 ==>
     val_approx_sgc_free a /\ globals_approx_sgc_free g`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; val_approx_sgc_free_def]) THEN
  ASM_REWRITE_TAC[val_approx_sgc_free_def] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_gsgc_insert THEN
      ASM_MESON_TAC[val_approx_sgc_free_merge; globals_approx_sgc_free_def] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_ALL_EL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BASICAUX_num_of_int_lt THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[globals_approx_sgc_free_def]);;

(* HOL4: elist_globals_empty *)
let clos_knownProof_elist_globals_empty = prove
 (`!es. clos_elist_globals es = EMPTY_BAG <=> !e. MEM e es ==> clos_set_globals e = EMPTY_BAG`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_set_globals_def; MEM; BAG_UNION_EMPTY] THEN
  MESON_TAC[]);;

(* HOL4: clos_gen_noinline_val_approx_sgc_free *)
let clos_gen_noinline_val_approx_sgc_free = prove
 (`!n i fns. ALL val_approx_sgc_free (clos_gen_noinline n i fns)`,
  MATCH_MP_TAC clos_gen_noinline_ind THEN
  REWRITE_TAC[clos_gen_noinline_def; ALL; val_approx_sgc_free_def] THEN MESON_TAC[]);;

(* HOL4: loptrel_def (HOL4's variable fv is fval here: fv was a constant, now clos_fv) *)
let loptrel_def = cake_def
  `loptrel fval numargs (lopt1:num option) lopt2 <=>
     lopt2 = lopt1 \/
     lopt1 = NONE /\
     (match (fval,lopt2) with
        (clos_Closure (SOME loc1) ae _ n bod, SOME loc2) ->
          loc1 = loc2 /\ n = numargs /\ ae = []
      | (clos_Recclosure (SOME loc1) ae _ fns i, SOME loc2) ->
          i < LENGTH fns /\ loc2 = loc1 + 2 * i /\ numargs = FST (EL i fns) /\ ae = []
      | _ -> F)`;;

let CLOSP2AUX_decide_inline_TAC : tactic =
  REPEAT GEN_TAC THEN CASES_ON `fapx:val_approx` THEN
  REWRITE_TAC[decide_inline_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

(* HOL4: decide_inline_LetInline_IMP_Clos *)
let decide_inline_LetInline_IMP_Clos = prove
 (`!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
     ?m s. fapx = clos_known_Clos m arity body s`,
  CLOSP2AUX_decide_inline_TAC);;

(* HOL4: decide_inline_LetInline_IMP_Clos_lopt *)
let decide_inline_LetInline_IMP_Clos_lopt = prove
 (`!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
     ?m s. fapx = clos_known_Clos m arity body s /\ (lopt = NONE \/ lopt = SOME m)`,
  CLOSP2AUX_decide_inline_TAC);;

let CLOSP2AUX_KN_UNFOLD2_TAC : tactic =
  let is_main tm =
    is_eq tm && (try fst(dest_const(fst(strip_comb(lhs tm)))) = "clos_known_known"
                 with Failure _ -> false) in
  REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(fun th -> if is_main (concl th) then MP_TAC th
                           else STRIP_ASSUME_TAC th)) THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN REPEAT CLOSP2AUX_GCASE_TAC THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]);;

let CLOSP2AUX_KN_SING_TAC : tactic =
  let is_cand th =
    try let l,r = dest_eq (concl th) in
        let f,args = strip_comb l in
        fst(dest_const f) = "clos_known_known" && length (dest_list (el 1 args)) = 1 &&
        is_var (fst(dest_pair r))
    with Failure _ -> false in
  REPEAT(FIRST_ASSUM(fun th -> if is_cand th then
    let x = fst(dest_pair(rhs(concl th))) in
    X_CHOOSE_THEN (mk_var("e_"^fst(dest_var x), `:clos_exp`))
      (X_CHOOSE_THEN (mk_var("a_"^fst(dest_var x), `:val_approx`)) SUBST_ALL_TAC)
      (MATCH_MP known_sing_EQ_E th)
  else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HD; PAIR_EQ; MAP; FST; SND]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY RVEQ_TAC;;

let CLOSP2AUX_kn_nrm_thms = [ALL; MAP; MAP_APPEND; ALL_APPEND; clos_set_globals_def;
  BAG_UNION_EMPTY; clos_esgc_free_def; clos_elist_globals_append; MAP_MAP_o; o_DEF;
  val_approx_sgc_free_def; EVERY_REPLICATE; clos_gen_noinline_val_approx_sgc_free;
  clos_op_gbag_def; SmartOp_simp; mk_Ticks_set_globals; mk_Ticks_esgc_free;
  SUB_BAG_REFL; SNOC_APPEND; LENGTH];;

let CLOSP2AUX_KN_NRM_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kn_nrm_thms) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC));;

(* |- !vs'. P[t/v] from th = |- !vs. v = t ==> P (or t = v), v one of vs not *)
(* free in t (checked before the renaming, which most candidates fail)       *)
let CLOSP2AUX_unwind th =
  let vs0,bod = strip_forall (concl th) in
  let l0,r0 = dest_eq (fst(dest_imp bod)) in
  let ok v t = is_var v && mem v vs0 && not (free_in v t) in
  if not (ok r0 l0 || ok l0 r0) then failwith "unwind" else
  let avoid = freesl (concl th :: hyp th) in
  let vs = itlist (fun v acc -> variant (acc @ avoid) v :: acc) vs0 [] in
  let th0 = SPECL vs th in
  let ant = fst(dest_imp (concl th0)) in
  let l,r = dest_eq ant in
  let pick v t = mem v vs && not (free_in v t) in
  let v,t = if is_var r && pick r l then r,l
            else if is_var l && pick l r then l,r else failwith "unwind" in
  let th2 = INST [t,v] th0 in
  GENL (subtract vs [v]) (MP th2 (REFL t));;

let CLOSP2AUX_RES_WITH (thms:thm list) : tactic =
  let rw = REWRITE_RULE thms in
  fun (asl,w as gl) ->
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let nrm th = curry (rw th) in
  let asms = map snd asl in
  let rec full depth th =
    if not (is_impth th) then Some th else if depth = 0 then None else
    match (try Some (nrm (CLOSP2AUX_unwind th)) with Failure _ -> None) with
      Some th' -> full (depth-1) th'
    | None ->
    let mth = try MATCH_MP th with Failure _ -> fun _ -> failwith "MATCH_MP" in
    let rec try_list l = match l with
        [] -> None
      | a::rest -> (match (try Some (nrm (mth a)) with Failure _ -> None) with
                      Some th' -> (match full (depth-1) th' with
                                     Some r -> Some r | None -> try_list rest)
                    | None -> try_list rest) in
    try_list asms in
  let rec go l = match l with
      [] -> failwith "CLOSP2AUX_RES_WITH"
    | (lab,th)::rest ->
        if is_impth th then
          (match full 16 (nrm th) with
             Some r -> (r,th)
           | None -> go rest)
        else go rest in
  let r,ih = go asl in
  (UNDISCH_THEN (concl ih) (K ALL_TAC) THEN CAKE_STRIP_ASSUME_TAC r) gl;;

let CLOSP2AUX_SBAG_TAC : tactic = fun (asl,w as g) ->
  (RULE_ASSUM_TAC(REWRITE_RULE[SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG; K_THM]) THEN
   REWRITE_TAC[SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG; K_THM] THEN
   X_GEN_TAC `xg:num` THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     let c = concl th in
     if is_forall c && type_of (fst(dest_forall c)) = `:num` &&
        (try let _,b = dest_forall c in is_binary "<=" b with Failure _ -> false)
     then MP_TAC (SPEC `xg:num` th) else NO_TAC)) THEN
   ARITH_TAC) g;;

let CLOSP2AUX_kn_letrec_sgc = prove
 (CASE_TERM `!c fns (g:val_approx spt) (nv:num->val_approx list).
   (!num_args x' new_vs. MEM (num_args,x') fns ==>
      !eas1 g'. clos_known_known c [x'] new_vs g = (eas1,g') ==> clos_esgc_free x' ==>
                ALL val_approx_sgc_free new_vs ==> globals_approx_sgc_free g ==>
                SUB_BAG (clos_elist_globals (MAP FST eas1)) (clos_set_globals x') /\
                ALL clos_esgc_free (MAP FST eas1) /\
                ALL val_approx_sgc_free (MAP SND eas1) /\ globals_approx_sgc_free g') /\
   clos_elist_globals (MAP SND fns) = EMPTY_BAG /\
   (!n. ALL val_approx_sgc_free (nv n)) /\ globals_approx_sgc_free g ==>
   clos_elist_globals
     (MAP (\p. SND (match p with
                      (num_args,x) -> (num_args, FST (HD (FST (clos_known_known c [x] (nv num_args) g))))))
          fns) = EMPTY_BAG`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[clos_knownProof_elist_globals_empty; MEM_MAP] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:clos_exp`; `n:num`; `x:clos_exp`] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `x:clos_exp`; `(nv:num->val_approx list) n`;
                 `g:val_approx spt`] known_sing) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD; FST; SND] THEN
  SUBGOAL_THEN `clos_set_globals x = EMPTY_BAG` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[clos_knownProof_elist_globals_empty] o
      check (fun th -> is_eq (concl th) && rhs (concl th) = `EMPTY_BAG:num->num`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MEM_MAP] THEN
    EXISTS_TAC `(n:num,x:clos_exp)` THEN ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:clos_exp`; `(nv:num->val_approx list) n`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[e':clos_exp,a:val_approx]`; `g':val_approx spt`]) THEN
  ASM_SIMP_TAC[set_globals_empty_esgc_free; MAP; clos_set_globals_def; BAG_UNION_EMPTY;
               SUB_BAG_EMPTY]);;

let CLOSP2AUX_sgc_clos_approx = prove
 (`!m loc n body. clos_set_globals body = EMPTY_BAG ==>
                  val_approx_sgc_free (clos_approx m loc n body)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_approx_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[val_approx_sgc_free_def]);;

let CLOSP2AUX_KN_LETREC_SGC_TAC : tactic = fun (asl,w as g) ->
  let is_cand t =
    try let f,args = strip_comb t in
        fst(dest_const f) = "clos_elist_globals" &&
        (let h,_ = strip_comb (hd args) in fst(dest_const h) = "MAP") &&
        can (find_term (fun u -> try fst(dest_const u) = "clos_known_known" with Failure _ -> false)) t
    with Failure _ -> false in
  let t = find_term is_cand w in
  (SUBGOAL_THEN (mk_eq(t, `EMPTY_BAG:num->num`)) ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSP2AUX_kn_letrec_sgc THEN
    ASM_REWRITE_TAC CLOSP2AUX_kn_nrm_thms;
    ASM_REWRITE_TAC[BAG_UNION_EMPTY]]) g;;

let CLOSP2AUX_KN_ESGC_FIN_TAC : tactic =
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[val_approx_sgc_free_def] THEN
      MATCH_MP_TAC CLOSP2AUX_ALL_EL THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC val_approx_sgc_free_merge THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_sgc_clos_approx THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CLOSP2AUX_KN_LETREC_SGC_TAC THEN NO_TAC) THEN
  TRY(CLOSP2AUX_KN_LETREC_SGC_TAC THEN CLOSP2AUX_SBAG_TAC THEN NO_TAC) THEN
  (fun (asl,w as g) ->
     let sgs = mapfilter (fun (_,th) -> let l,r = dest_eq (concl th) in
                 if fst(dest_const(fst(strip_comb l))) = "clos_set_globals" &&
                    r = `EMPTY_BAG:num->num` then th else failwith "") asl in
     (RULE_ASSUM_TAC(REWRITE_RULE (SUB_BAG_EMPTY :: sgs)) THEN
      ASM_REWRITE_TAC[] THEN TRY(CLOSP2AUX_SBAG_TAC THEN NO_TAC)) g);;

(* HOL4: known_preserves_esgc_free_0 *)
let known_preserves_esgc_free_0 = prove
 (`!c es aenv (g0:val_approx spt) eas1 g.
     clos_known_known c es aenv g0 = (eas1,g) /\ ALL clos_esgc_free es /\
     ALL val_approx_sgc_free aenv /\ globals_approx_sgc_free g0 ==>
     SUB_BAG (clos_elist_globals (MAP FST eas1)) (clos_elist_globals es) /\
     ALL clos_esgc_free (MAP FST eas1) /\
     ALL val_approx_sgc_free (MAP SND eas1) /\
     globals_approx_sgc_free g`,
  REWRITE_TAC[IMP_CONJ] THEN
   MATCH_MP_TAC clos_known_known_ind THEN REPEAT CONJ_TAC THEN CLOSP2AUX_KN_UNFOLD2_TAC THEN
   CLOSP2AUX_KN_SING_TAC THEN
   MAP_EVERY ASSUME_TAC [known_op_preserves_esgc_free; decide_inline_LetInline_IMP_Clos;
                         set_globals_empty_esgc_free] THEN
   CLOSP2AUX_KN_NRM_TAC THEN
   REPEAT(CLOSP2AUX_RES_WITH (PAIR_EQ :: EVERY_REVERSE :: HD :: CLOSP2AUX_kn_nrm_thms) THEN
          CLOSP2AUX_KN_SING_TAC THEN CLOSP2AUX_KN_NRM_TAC THEN TRY RVEQ_TAC) THEN
   CLOSP2AUX_KN_NRM_TAC THEN
   REWRITE_TAC CLOSP2AUX_kn_nrm_thms THEN
   REWRITE_TAC[SmartOp_simp; any_el_ALT] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
   TRY(CLOSP2AUX_SBAG_TAC THEN NO_TAC) THEN CLOSP2AUX_KN_ESGC_FIN_TAC);;

(* HOL4: known_preserves_esgc_free *)
let known_preserves_esgc_free = prove
 (`!c es aenv (g0:val_approx spt) eas1 g.
     clos_known_known c es aenv g0 = (eas1,g) /\ ALL clos_esgc_free es /\
     ALL val_approx_sgc_free aenv /\ globals_approx_sgc_free g0 ==>
     ALL clos_esgc_free (MAP FST eas1) /\
     ALL val_approx_sgc_free (MAP SND eas1) /\
     globals_approx_sgc_free g`,
  MESON_TAC[known_preserves_esgc_free_0]);;

(* HOL4: known_elglobals_dont_grow *)
let known_elglobals_dont_grow = prove
 (`!c es aenv (g0:val_approx spt) eas1 g.
     clos_known_known c es aenv g0 = (eas1,g) /\ ALL clos_esgc_free es /\
     ALL val_approx_sgc_free aenv /\ globals_approx_sgc_free g0 ==>
     SUB_BAG (clos_elist_globals (MAP FST eas1)) (clos_elist_globals es)`,
  MESON_TAC[known_preserves_esgc_free_0]);;

let CLOSP2AUX_kn_pure_thms = [pure_def; ALL; MAP; MAP_APPEND; ALL_APPEND; SmartOp_simp];;

(* HOL4: known_preserves_pure *)
let known_preserves_pure = prove
 (`!c es aenv (g0:val_approx spt) eas1 g.
     clos_known_known c es aenv g0 = (eas1,g) /\ ALL pure es ==> ALL pure (MAP FST eas1)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC clos_known_known_ind THEN REPEAT CONJ_TAC THEN CLOSP2AUX_KN_UNFOLD2_TAC THEN
  CLOSP2AUX_KN_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kn_pure_thms) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(CLOSP2AUX_RES_WITH (PAIR_EQ :: EVERY_REVERSE :: HD :: CLOSP2AUX_kn_pure_thms) THEN
         CLOSP2AUX_KN_SING_TAC THEN
         RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kn_pure_thms) THEN
         REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                        else NO_TAC))) THEN
  REWRITE_TAC CLOSP2AUX_kn_pure_thms THEN ASM_REWRITE_TAC[] THEN
  TRY(REWRITE_TAC[clos_pure_op_def] THEN CAKE_REWRITE_TAC[] THEN NO_TAC));;

let CLOSP2AUX_dec_clock_0 = prove
 (`!s:(C,FFI)clos_state. clos_dec_clock 0 s = s`,
  REWRITE_TAC[clos_dec_clock_def; SUB_0; clos_with_same_clock]);;

let CLOSP2AUX_dec_clock_SUC = prove
 (`!n (s:(C,FFI)clos_state). clos_dec_clock 1 (clos_dec_clock n s) = clos_dec_clock (SUC n) s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_fupdfupds; clos_state_INFO.ri_accfupds;
              o_DEF; K_THM] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; K_THM] THEN
  ARITH_TAC);;

(* HOL4: evaluate_mk_Ticks_rw *)
let evaluate_mk_Ticks_rw = prove
 (`!t tc n exp env (s:(C,FFI)clos_state).
     clos_evaluate ([clos_known_mk_Ticks t tc n exp],env,s) =
     if clos_state_clock s < n
     then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (combin_K 0) s)
     else clos_evaluate ([exp],env,clos_dec_clock n s)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[mk_Ticks_alt; CONJUNCT1 LT; CLOSP2AUX_dec_clock_0]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_Ticks_alt] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_evaluate_def; CLOSP2AUX_dec_clock_SUC] THEN
  ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) < n` THEN
  ASM_SIMP_TAC[ARITH_RULE `a < n ==> a < SUC n`] THEN
  SUBGOAL_THEN `clos_state_clock (s:(C,FFI)clos_state) < SUC n <=>
                clos_state_clock s - n = 0` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: evaluate_mk_Ticks_IMP *)
let evaluate_mk_Ticks_IMP = prove
 (`!t tc n exp env (s0:(C,FFI)clos_state) res s.
     clos_evaluate ([clos_known_mk_Ticks t tc n exp],env,s0) = (res,s) ==>
     (res = Rerr (Rabort Rtimeout_error) /\ s = clos_state_clock_fupd (combin_K 0) s0) \/
     clos_evaluate ([exp],env,clos_dec_clock n s0) = (res,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_mk_Ticks_rw] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4: clos_gen_noinline_eq *)
let clos_gen_noinline_eq = prove
 (`!n c fns.
     clos_gen_noinline n c fns =
     list_of_seq (\i. ClosNoInline (2 * (i + c) + n) (FST (EL i fns))) (LENGTH fns)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[clos_gen_noinline_def; LENGTH; list_of_seq]; ALL_TAC] THEN
  GEN_TAC THEN SPEC_TAC(`h:num#clos_exp`,`h:num#clos_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[clos_gen_noinline_def; LENGTH; GENLIST_CONS; o_DEF] THEN
  REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; FST; injectivity "list"] THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[ADD1; ADD_ASSOC]]);;

(* HOL4: letrec_case_eq [local] (HOL4 binds limit, which does not occur) *)
let letrec_case_eq = prove
 (CASE_TERM `!(loc:num option) (fns:(num # clos_exp) list).
     (match loc with
        NONE -> REPLICATE (LENGTH fns) clos_known_Other
      | SOME n -> clos_gen_noinline n 0 fns) =
     list_of_seq (match loc with
                    NONE -> combin_K clos_known_Other
                  | SOME n -> \i. ClosNoInline (n + 2 * i) (FST (EL i fns)))
                 (LENGTH fns)`,
  GEN_TAC THEN CASES_ON `loc:num option` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[REPLICATE_GENLIST; clos_gen_noinline_eq] THEN GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* HOL4: every_var_def *)
let clos_knownProof_every_var_def = cake_def
  `(clos_knownProof_every_var P db_vars_Empty <=> T) /\
   (clos_knownProof_every_var P (db_vars_Var v) <=> P v) /\
   (clos_knownProof_every_var P (db_vars_Shift k d) <=>
      clos_knownProof_every_var (\v. k <= v ==> P (v - k)) d) /\
   (clos_knownProof_every_var P (db_vars_Union d1 d2) <=>
      clos_knownProof_every_var P d1 /\ clos_knownProof_every_var P d2)`;;

(* HOL4: every_var_mk_Union [simp] *)
let every_var_mk_Union = prove
 (`!P d1 d2. clos_knownProof_every_var P (mk_Union d1 d2) <=>
             clos_knownProof_every_var P d1 /\ clos_knownProof_every_var P d2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_Union_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[clos_knownProof_every_var_def]);;
let _ = cake_add_simps [every_var_mk_Union];;

let CLOSP2AUX_closed_fv_max = prove
 (`!nm k body. clos_known_closed (Fn nm NONE NONE k body) ==> fv_max k [body]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_known_closed_def] THEN
  ONCE_REWRITE_TAC[clos_known_free_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def; SND] THEN
  DISCH_TAC THEN REWRITE_TAC[fv_max_def; fv_alt] THEN X_GEN_TAC `v:num` THEN
  DISCH_TAC THEN ASM_CASES_TAC `v < k:num` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  MP_TAC(INST [`v - k:num`,`n:num`; `SND (clos_known_free [body])`,`s:db_var_set`]
            lookup_db_to_set_Shift) THEN
  ASM_REWRITE_TAC[lookup_def] THEN
  SUBGOAL_THEN `v - k + k = v:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[lookup_db_to_set; distinctness "option"]);;

(* HOL4: decide_inline_LetInline_IMP_Clos_fv_max *)
let decide_inline_LetInline_IMP_Clos_fv_max = prove
 (`!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
     ?m s. fapx = clos_known_Clos m arity body s /\ fv_max arity [body]`,
  REPEAT GEN_TAC THEN CASES_ON `fapx:val_approx` THEN
  REWRITE_TAC[decide_inline_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONJ_ASSOC]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  ASM_MESON_TAC[CLOSP2AUX_closed_fv_max]);;

let CLOSP2AUX_kn_fv_thms = [fv_max_rw; MAP; MAP_APPEND; fv_max_append; fv_max_mk_Ticks;
  SNOC_APPEND; LENGTH_MAP; LENGTH_APPEND; LENGTH];;

let CLOSP2AUX_kn_letrec_fv = prove
 (CASE_TERM `!c fns (g:val_approx spt) (nv:num->val_approx list) (k:num->num).
   (!num_args x' new_vs. MEM (num_args,x') fns ==>
      !eas1 g' n. clos_known_known c [x'] new_vs g = (eas1,g') ==> fv_max n [x'] ==>
                  fv_max n (MAP FST eas1)) /\
   ALL (\p. match p with (num_args,x) -> fv_max (k num_args) [x]) fns ==>
   ALL (\p. match p with (num_args,x) -> fv_max (k num_args) [x])
     (MAP (\p. match p with
                 (num_args,x) -> (num_args, FST (HD (FST (clos_known_known c [x] (nv num_args) g)))))
          fns)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN CAKE_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n0:num`; `x0:clos_exp`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `x0:clos_exp`; `(nv:num->val_approx list) n0`;
                 `g:val_approx spt`] known_sing) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD; FST] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n0:num`; `x0:clos_exp`; `(nv:num->val_approx list) n0`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[e':clos_exp,a:val_approx]`; `g':val_approx spt`;
                             `(k:num->num) n0`]) THEN
  ASM_SIMP_TAC[MAP]);;

let CLOSP2AUX_KN_LENGTH_TAC : tactic = fun (asl,w as g) ->
  let facts = mapfilter (fun (_,th) -> MATCH_MP known_LENGTH_EQ_E th) asl in
  let facts = filter (fun th -> not (exists (fun (_,a) -> concl a = concl th) asl)) facts in
  MAP_EVERY ASSUME_TAC facts g;;

(* HOL4: known_preserves_fv_max *)
let known_preserves_fv_max = prove
 (`!c es aenv (g0:val_approx spt) eas1 g n.
     clos_known_known c es aenv g0 = (eas1,g) /\ fv_max n es ==> fv_max n (MAP FST eas1)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC clos_known_known_ind THEN REPEAT CONJ_TAC THEN CLOSP2AUX_KN_UNFOLD2_TAC THEN
  CLOSP2AUX_KN_SING_TAC THEN
  MAP_EVERY ASSUME_TAC [decide_inline_LetInline_IMP_Clos_fv_max] THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kn_fv_thms) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  REPEAT(CLOSP2AUX_RES_WITH (PAIR_EQ :: EVERY_REVERSE :: HD :: CLOSP2AUX_kn_fv_thms) THEN
         CLOSP2AUX_KN_SING_TAC THEN
         RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kn_fv_thms) THEN
         REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) || is_exists (concl th)
                                        then STRIP_ASSUME_TAC th else NO_TAC)) THEN
         TRY RVEQ_TAC) THEN
  CLOSP2AUX_KN_LENGTH_TAC THEN
  REWRITE_TAC CLOSP2AUX_kn_fv_thms THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC fv_max_SmartOp THEN ASM_REWRITE_TAC[fv_max_rw] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_kn_letrec_fv THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MATCH_MP_TAC fv_max_less THEN
  EXISTS_TAC `LENGTH (xs:clos_exp list)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4: oracle_gapprox_subspt_def *)
let oracle_gapprox_subspt_def = cake_def
  `oracle_gapprox_subspt (co:num -> ((A)spt # B) # C) <=>
     !n. subspt (FST (FST (co n))) (FST (FST (co (SUC n))))`;;

(* HOL4: oracle_gapprox_subspt_add *)
let oracle_gapprox_subspt_add = prove
 (`!co:num -> ((A)spt # B) # C.
     oracle_gapprox_subspt co <=>
     !n k. subspt (FST (FST (co n))) (FST (FST (co (n + k))))`,
  GEN_TAC THEN REWRITE_TAC[oracle_gapprox_subspt_def] THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; subspt_refl] THEN
    ASM_MESON_TAC[subspt_trans];
    DISCH_TAC THEN GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `1`]) THEN
    REWRITE_TAC[ADD1]]);;

(* HOL4: oracle_gapprox_subspt_alt *)
let oracle_gapprox_subspt_alt = prove
 (`!(co:num -> ((A)spt # B) # C) n k.
     oracle_gapprox_subspt co /\ n <= k ==> subspt (FST (FST (co n))) (FST (FST (co k)))`,
  REWRITE_TAC[oracle_gapprox_subspt_add; LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: oracle_gapprox_subspt_shift_seq *)
let oracle_gapprox_subspt_shift_seq = prove
 (`!co:num -> ((A)spt # B) # C.
     oracle_gapprox_subspt co ==> !k. oracle_gapprox_subspt (shift_seq k co)`,
  REWRITE_TAC[oracle_gapprox_subspt_def; shift_seq_def; ADD_CLAUSES] THEN MESON_TAC[]);;

(* HOL4: oracle_gapprox_subspt_evaluate (HOL4 binds s0 twice) *)
let oracle_gapprox_subspt_evaluate = prove
 (`!xs env (s0:((A)spt # B,FFI)clos_state) res s.
     oracle_gapprox_subspt (clos_state_compile_oracle s0) /\
     clos_evaluate (xs,env,s0) = (res,s) ==>
     oracle_gapprox_subspt (clos_state_compile_oracle s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_code) THEN
  ASM_SIMP_TAC[oracle_gapprox_subspt_shift_seq]);;

(* HOL4: oracle_state_sgc_free_def *)
let oracle_state_sgc_free_def = cake_def
  `oracle_state_sgc_free (co:num -> (val_approx spt # B) # C) <=>
     !n. globals_approx_sgc_free (FST (FST (co n)))`;;

(* HOL4: oracle_state_sgc_free_shift_seq *)
let oracle_state_sgc_free_shift_seq = prove
 (`!co:num -> (val_approx spt # B) # C.
     oracle_state_sgc_free co ==> !n. oracle_state_sgc_free (shift_seq n co)`,
  REWRITE_TAC[oracle_state_sgc_free_def; shift_seq_def] THEN MESON_TAC[]);;

(* HOL4: next_g_def *)
let next_g_def = cake_def
  `next_g (s:(val_approx spt # C,FFI)clos_state) =
     FST (FST (clos_state_compile_oracle s 0))`;;

(* HOL4: mglobals_disjoint_def *)
let mglobals_disjoint_def = cake_def
  `mglobals_disjoint (s:(A option) list) xs <=>
     DISJOINT (mapped_globals s) (SET_OF_BAG (clos_elist_globals xs))`;;

(* HOL4: mglobals_disjoint_rw *)
let mglobals_disjoint_rw = prove
 (`!(s:(A option) list) x y xs tr x1 x2 x3 ticks dest opn lopt src_names vs fns.
     (mglobals_disjoint s (CONS x (CONS y xs)) <=>
        mglobals_disjoint s [x] /\ mglobals_disjoint s (CONS y xs)) /\
     (mglobals_disjoint s [clos_Let tr xs x] <=>
        mglobals_disjoint s xs /\ mglobals_disjoint s [x]) /\
     (mglobals_disjoint s [clos_Handle tr x1 x2] <=>
        mglobals_disjoint s [x1] /\ mglobals_disjoint s [x2]) /\
     (mglobals_disjoint s [clos_If tr x1 x2 x3] <=>
        mglobals_disjoint s [x1] /\ mglobals_disjoint s [x2] /\ mglobals_disjoint s [x3]) /\
     (mglobals_disjoint s [clos_Raise tr x] <=> mglobals_disjoint s [x]) /\
     (mglobals_disjoint s [clos_Tick tr x] <=> mglobals_disjoint s [x]) /\
     (mglobals_disjoint s [clos_Call tr ticks dest xs] <=> mglobals_disjoint s xs) /\
     (mglobals_disjoint s [clos_Op tr opn xs] <=>
        mglobals_disjoint s xs /\
        DISJOINT (mapped_globals s) (SET_OF_BAG (clos_op_gbag opn))) /\
     (mglobals_disjoint s [clos_App tr lopt x1 xs] <=>
        mglobals_disjoint s [x1] /\ mglobals_disjoint s xs) /\
     (mglobals_disjoint s [clos_Letrec src_names lopt vs fns x1] <=>
        mglobals_disjoint s (MAP SND fns) /\ mglobals_disjoint s [x1])`,
  REWRITE_TAC[mglobals_disjoint_def; clos_set_globals_def; SET_OF_BAG_UNION;
              BAG_UNION_EMPTY] THEN SET_TAC[]);;

(* HOL4: known_changed_globals_cases *)
let known_changed_globals_cases = prove
 (`!c xs aenv (g0:val_approx spt) alist g.
     clos_known_known c xs aenv g0 = (alist,g) ==>
     !k a. lookup k g = SOME a ==>
           lookup k g0 = SOME a \/ k IN SET_OF_BAG (clos_elist_globals xs)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP known_changed_globals) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]);;

(* HOL4: known_op_changed_globals_cases *)
let known_op_changed_globals_cases = prove
 (`!opn aenv (g0:val_approx spt) ea g.
     known_op opn aenv g0 = (ea,g) ==>
     !k a. lookup k g = SOME a ==>
           lookup k g0 = SOME a \/ k IN SET_OF_BAG (clos_op_gbag opn)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP known_op_changed_globals) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]);;

(* HOL4: state_globals_approx_known_mglobals_disjoint *)
let state_globals_approx_known_mglobals_disjoint = prove
 (`!c xs aenv (g0:val_approx spt) eas g (s:(C,FFI)clos_state).
     clos_known_known c xs aenv g0 = (eas,g) /\ mglobals_disjoint (clos_state_globals s) xs /\
     state_globals_approx s g0 ==>
     state_globals_approx s g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP known_changed_globals_cases) MP_TAC) THEN
  REWRITE_TAC[state_globals_approx_def; mglobals_disjoint_def; mapped_globals_def;
              DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_distinct3 = prove
 (`!(a:num->num) b c i.
     BAG_ALL_DISTINCT (BAG_UNION (BAG_UNION a b) c) /\ i IN SET_OF_BAG a /\
     (i IN SET_OF_BAG b \/ i IN SET_OF_BAG c) ==> F`,
  REWRITE_TAC[BAG_ALL_DISTINCT; BAG_UNION; IN_SET_OF_BAG; BAG_IN; BAG_INN] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_ARITH_TAC);;

(* HOL4: mglobals_disjoint_evaluate *)
let mglobals_disjoint_evaluate = prove
 (`!(s0:(C,FFI)clos_state) xs ys env res s.
     clos_evaluate (ys,env,s0) = (res,s) /\
     ssgc_free s0 /\ ALL vsgc_free env /\ ALL clos_esgc_free ys /\
     unique_set_globals (APPEND xs ys) (clos_state_compile_oracle s0) /\
     mglobals_disjoint (clos_state_globals s0) xs ==>
     mglobals_disjoint (clos_state_globals s) xs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ys:clos_exp list`; `env:clos_v list`; `s0:(C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`; `s:(C,FFI)clos_state`]
                evaluate_changed_globals) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[unique_set_globals_def]) THEN
  REWRITE_TAC[clos_elist_globals_append] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mglobals_disjoint_def; mglobals_extend_def; SUBSET;
                              IN_UNION]) THEN
  REWRITE_TAC[mglobals_disjoint_def; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT1 o
    check (fun th -> is_conj (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[CLOSP2AUX_distinct3];
    ASM_MESON_TAC[CLOSP2AUX_distinct3]]);;

(* HOL4: gapprox_extend_def *)
let gapprox_extend_def = cake_def
  `gapprox_extend (g1:val_approx spt) gd g2 <=>
     !i. i IN domain g2 /\ (i IN domain g1 ==> ~(lookup i g2 = lookup i g1)) ==> i IN gd`;;

(* HOL4: state_globals_approx_disjoint_extends *)
let state_globals_approx_disjoint_extends = prove
 (`!(s1:(C,FFI)clos_state) mgx (s2:(C,FFI)clos_state) g1 gax g2.
     mglobals_extend (clos_state_globals s1) mgx (clos_state_globals s2) /\
     gapprox_extend g1 gax g2 /\
     DISJOINT (mapped_globals (clos_state_globals s1)) gax /\ DISJOINT gax mgx /\
     state_globals_approx s2 g1 ==>
     state_globals_approx s2 g2`,
  REWRITE_TAC[state_globals_approx_def; mglobals_extend_def; gapprox_extend_def;
              mapped_globals_def; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
              IN_ELIM_THM; domain_lookup] THEN
  MESON_TAC[]);;

let CLOSP2AUX_distinct3m = prove
 (`!(a:num->num) b c i.
     BAG_ALL_DISTINCT (BAG_UNION (BAG_UNION a b) c) /\ i IN SET_OF_BAG b /\
     (i IN SET_OF_BAG a \/ i IN SET_OF_BAG c) ==> F`,
  REWRITE_TAC[BAG_ALL_DISTINCT; BAG_UNION; IN_SET_OF_BAG; BAG_IN; BAG_INN] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_ARITH_TAC);;

(* HOL4: state_globals_approx_evaluate *)
let state_globals_approx_evaluate = prove
 (`!xs env (s0:(C,FFI)clos_state) res s c ys aenv (g0:val_approx spt) eas g.
     clos_evaluate (xs,env,s0) = (res,s) /\ clos_known_known c ys aenv g0 = (eas,g) /\
     ssgc_free s0 /\ ALL vsgc_free env /\ ALL clos_esgc_free xs /\
     mglobals_disjoint (clos_state_globals s0) ys /\
     unique_set_globals (APPEND xs ys) (clos_state_compile_oracle s0) /\
     state_globals_approx s g0 ==>
     state_globals_approx s g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `env:clos_v list`; `s0:(C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`; `s:(C,FFI)clos_state`]
                evaluate_changed_globals) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[unique_set_globals_def]) THEN
  REWRITE_TAC[clos_elist_globals_append] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP known_changed_globals_cases) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mglobals_disjoint_def; mglobals_extend_def; IN_UNION;
                              DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                              mapped_globals_def; IN_ELIM_THM]) THEN
  REWRITE_TAC[state_globals_approx_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `a:val_approx`] o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(lhand(snd(strip_forall
                     (concl th)))))))) = "lookup" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[state_globals_approx_def]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(k IN SET_OF_BAG (clos_elist_globals xs) \/
      k IN SET_OF_BAG (clos_elist_globals
                         (FLAT (first_n_exps (clos_state_compile_oracle
                                               (s0:(C,FFI)clos_state)) n))))`
   ASSUME_TAC THENL [ASM_MESON_TAC[CLOSP2AUX_distinct3m]; ALL_TAC] THEN
  SUBGOAL_THEN `get_global k (clos_state_globals (s0:(C,FFI)clos_state)) =
                SOME (SOME (v:clos_v))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

(* HOL4: state_globals_approx_known_op_evaluate *)
let state_globals_approx_known_op_evaluate = prove
 (`!xs env (s0:(C,FFI)clos_state) res s opn aargs (g0:val_approx spt) ea g tr.
     clos_evaluate (xs,env,s0) = (res,s) /\ known_op opn aargs g0 = (ea,g) /\
     ssgc_free s0 /\ ALL vsgc_free env /\ ALL clos_esgc_free xs /\
     DISJOINT (mapped_globals (clos_state_globals s0)) (SET_OF_BAG (clos_op_gbag opn)) /\
     unique_set_globals [clos_Op tr opn xs] (clos_state_compile_oracle s0) /\
     state_globals_approx s g0 ==>
     state_globals_approx s g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `env:clos_v list`; `s0:(C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`; `s:(C,FFI)clos_state`]
                evaluate_changed_globals) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[unique_set_globals_def]) THEN
  REWRITE_TAC[clos_elist_globals_append; APPEND; clos_set_globals_def;
              BAG_UNION_EMPTY] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP known_op_changed_globals_cases) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mglobals_extend_def; IN_UNION;
                              DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                              mapped_globals_def; IN_ELIM_THM]) THEN
  REWRITE_TAC[state_globals_approx_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `a:val_approx`] o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(lhand(snd(strip_forall
                     (concl th)))))))) = "lookup" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[state_globals_approx_def]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(k IN SET_OF_BAG (clos_elist_globals xs) \/
      k IN SET_OF_BAG (clos_elist_globals
                         (FLAT (first_n_exps (clos_state_compile_oracle
                                               (s0:(C,FFI)clos_state)) n))))`
   ASSUME_TAC THENL [ASM_MESON_TAC[CLOSP2AUX_distinct3]; ALL_TAC] THEN
  SUBGOAL_THEN `get_global k (clos_state_globals (s0:(C,FFI)clos_state)) =
                SOME (SOME (v:clos_v))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let CLOSP2AUX_BAG_IN_FLAT = prove
 (`!ls l i. MEM l ls /\ BAG_IN i (clos_elist_globals l) ==>
            BAG_IN i (clos_elist_globals (FLAT ls))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FLAT; clos_elist_globals_append; BAG_IN_BAG_UNION] THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_distinct2 = prove
 (`!(a:num->num) b i.
     BAG_ALL_DISTINCT (BAG_UNION a b) /\ BAG_IN i a /\ BAG_IN i b ==> F`,
  REWRITE_TAC[BAG_ALL_DISTINCT; BAG_UNION; BAG_IN; BAG_INN] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_ARITH_TAC);;

(* HOL4: elist_globals_first_n_exps_lemma *)
let elist_globals_first_n_exps_lemma = prove
 (`!i k (co:num -> A # clos_exp list # B).
     BAG_IN i (clos_elist_globals (FST (SND (co k)))) ==>
     !n. k < n ==> BAG_IN i (clos_elist_globals (FLAT (first_n_exps co n)))`,
  MESON_TAC[MEM_first_n_exps; CLOSP2AUX_BAG_IN_FLAT]);;

(* HOL4: elist_globals_first_n_exps_shift_seq_lemma *)
let elist_globals_first_n_exps_shift_seq_lemma = prove
 (`!i k (co:num -> A # clos_exp list # B).
     BAG_IN i (clos_elist_globals (FST (SND (co k)))) ==>
     !m n. m < k /\ k < m + n ==>
           BAG_IN i (clos_elist_globals (FLAT (first_n_exps (shift_seq m co) n)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `k - m:num`; `shift_seq m (co:num -> A # clos_exp list # B)`]
                elist_globals_first_n_exps_lemma) THEN
  REWRITE_TAC[shift_seq_def] THEN
  SUBGOAL_THEN `k - m + m = k:num` (fun th -> ASM_REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* HOL4: elist_globals_first_n_exps_exists *)
let elist_globals_first_n_exps_exists = prove
 (`!i (co:num -> A # clos_exp list # B) n.
     BAG_IN i (clos_elist_globals (FLAT (first_n_exps co n))) ==>
     ?k. k < n /\ BAG_IN i (clos_elist_globals (FST (SND (co k))))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[first_n_exps_def; list_of_seq; FLAT; clos_set_globals_def; BAG_IN;
              BAG_INN; EMPTY_BAG; K_THM] THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FLAT_APPEND; clos_elist_globals_append; FLAT; APPEND_NIL; GSYM BAG_INN;
              GSYM BAG_IN; BAG_IN_BAG_UNION; o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM BAG_INN; GSYM BAG_IN; GSYM first_n_exps_def]) THEN
  REWRITE_TAC[GSYM first_n_exps_def] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`];
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LT]]);;

let CLOSP2AUX_first_n_exps_SUC = prove
 (`!(co:num -> A # B # C) n.
     first_n_exps co (SUC n) = APPEND (first_n_exps co n) [FST (SND (co n))]`,
  REWRITE_TAC[first_n_exps_def; list_of_seq; o_THM]);;

let CLOSP2AUX_unique_two = prove
 (`!(co:num -> A # clos_exp list # B) xs i k n.
     unique_set_globals xs co /\ k < n /\
     BAG_IN i (clos_elist_globals (FST (SND (co k)))) /\
     BAG_IN i (clos_elist_globals (FST (SND (co n)))) ==> F`,
  REWRITE_TAC[unique_set_globals_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
  REWRITE_TAC[CLOSP2AUX_first_n_exps_SUC; FLAT_APPEND; clos_elist_globals_append;
              FLAT; APPEND_NIL] THEN
  DISCH_TAC THEN MATCH_MP_TAC CLOSP2AUX_distinct2 THEN
  MAP_EVERY EXISTS_TAC
   [`BAG_UNION (clos_elist_globals xs)
       (clos_elist_globals (FLAT (first_n_exps (co:num -> A # clos_exp list # B) n)))`;
    `clos_elist_globals (FST (SND ((co:num -> A # clos_exp list # B) n)))`; `i:num`] THEN
  ASM_REWRITE_TAC[GSYM ASSOC_BAG_UNION; BAG_IN_BAG_UNION] THEN
  DISJ2_TAC THEN ASM_MESON_TAC[elist_globals_first_n_exps_lemma]);;

(* HOL4: oracle_gapprox_disjoint_Install *)
let oracle_gapprox_disjoint_Install = prove
 (`!c (co:num -> A # clos_exp list # B) (g0:val_approx spt) eas g.
     clos_known_known c (FST (SND (co 0))) [] g0 = (eas,g) /\ unique_set_globals [] co /\
     oracle_gapprox_disjoint g0 co ==>
     oracle_gapprox_disjoint g (shift_seq 1 co)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP known_changed_globals_cases) THEN
  REWRITE_TAC[oracle_gapprox_disjoint_def; gapprox_disjoint_def; shift_seq_def] THEN
  X_GEN_TAC `nn:num` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; domain_lookup; IN_SET_OF_BAG] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:val_approx`) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `a:val_approx`]) THEN ASM_REWRITE_TAC[IN_SET_OF_BAG] THEN
  STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[oracle_gapprox_disjoint_def; gapprox_disjoint_def; DISJOINT;
                               EXTENSION; IN_INTER; NOT_IN_EMPTY; domain_lookup;
                               IN_SET_OF_BAG]) THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC CLOSP2AUX_unique_two THEN
    MAP_EVERY EXISTS_TAC [`co:num -> A # clos_exp list # B`; `[]:clos_exp list`; `i:num`;
                          `0`; `nn + 1`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* HOL4: oracle_gapprox_disjoint_shift_seq_unique_set_globals *)
let oracle_gapprox_disjoint_shift_seq_unique_set_globals = prove
 (`!c xs aenv (g0:val_approx spt) eas g (s0:(C,FFI)clos_state) k.
     clos_known_known c xs aenv g0 = (eas,g) /\
     unique_set_globals xs (clos_state_compile_oracle s0) /\
     oracle_gapprox_disjoint g0 (clos_state_compile_oracle s0) ==>
     oracle_gapprox_disjoint g (shift_seq k (clos_state_compile_oracle s0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP known_changed_globals_cases) THEN
  REWRITE_TAC[oracle_gapprox_disjoint_def; gapprox_disjoint_def; shift_seq_def] THEN
  X_GEN_TAC `nn:num` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; domain_lookup; IN_SET_OF_BAG] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:val_approx`) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `a:val_approx`]) THEN ASM_REWRITE_TAC[IN_SET_OF_BAG] THEN
  STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[oracle_gapprox_disjoint_def; gapprox_disjoint_def; DISJOINT;
                               EXTENSION; IN_INTER; NOT_IN_EMPTY; domain_lookup;
                               IN_SET_OF_BAG]) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC (nn + k)` o REWRITE_RULE[unique_set_globals_def]) THEN
    REWRITE_TAC[CLOSP2AUX_first_n_exps_SUC; FLAT_APPEND; clos_elist_globals_append;
                FLAT; APPEND_NIL] THEN
    DISCH_TAC THEN MATCH_MP_TAC CLOSP2AUX_distinct2 THEN
    MAP_EVERY EXISTS_TAC
     [`clos_elist_globals xs`;
      `BAG_UNION (clos_elist_globals (FLAT (first_n_exps
          (clos_state_compile_oracle (s0:(C,FFI)clos_state)) (nn + k))))
         (clos_elist_globals (FST (SND (clos_state_compile_oracle s0 (nn + k)))))`;
      `i:num`] THEN
    ASM_REWRITE_TAC[BAG_IN_BAG_UNION]]);;

(* HOL4: oracle_gapprox_disjoint_lemma *)
let oracle_gapprox_disjoint_lemma = prove
 (`!xs env (s0:(C,FFI)clos_state) res s c aenv (g0:val_approx spt) eas g.
     clos_evaluate (xs,env,s0) = (res,s) /\ clos_known_known c xs aenv g0 = (eas,g) /\
     unique_set_globals xs (clos_state_compile_oracle s0) /\
     oracle_gapprox_disjoint g0 (clos_state_compile_oracle s0) ==>
     oracle_gapprox_disjoint g (clos_state_compile_oracle s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST1_TAC o MATCH_MP evaluate_IMP_shift_seq) THEN
  ASM_MESON_TAC[oracle_gapprox_disjoint_shift_seq_unique_set_globals]);;

(* ------------------------------------------------------------------------- *)
(* known_correct_approx: clos_known_known_ind with one lemma per case; each case is      *)
(* unfolded once (known and evaluate) and closed by a saturation with the      *)
(* induction hypotheses and the lemmas of CLOSP2AUX_kca_fwd                    *)
(* ------------------------------------------------------------------------- *)

let CLOSP2AUX_kca_P = `\c xs aenv (g0:val_approx spt).
   !eas g env extra (s0:(val_approx spt # C,FFI)clos_state) res s.
     clos_known_known c xs aenv g0 = (eas,g) ==>
     clos_evaluate (xs,APPEND env extra,s0) = (res,s) ==>
     unique_set_globals xs (clos_state_compile_oracle s0) ==>
     ALL2 val_approx_val aenv env ==>
     state_globals_approx s0 g0 ==>
     mglobals_disjoint (clos_state_globals s0) xs ==>
     oracle_gapprox_disjoint g0 (clos_state_compile_oracle s0) ==>
     ssgc_free s0 ==> ALL vsgc_free (APPEND env extra) ==> ALL clos_esgc_free xs ==>
     ALL val_approx_sgc_free aenv ==> globals_approx_sgc_free g0 ==>
     state_globals_approx s g /\
     !vs. res = Rval vs ==> ALL2 val_approx_val (MAP SND eas) vs`;;

let CLOSP2AUX_kca_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC CLOSP2AUX_kca_P clos_known_known_ind);;

let CLOSP2AUX_kca_cases = conjuncts (lhand (concl CLOSP2AUX_kca_ind));;

(* the main evaluation of a case, unfolded once and split *)
let CLOSP2AUX_KCA_EVAL_TAC : tactic = fun (asl,w as g) ->
  let is_main th =
    try let l,r = dest_eq (concl th) in
        let f,a = dest_comb l in
        fst(dest_const f) = "clos_evaluate" &&
        (let res,st = dest_pair r in is_var res && is_var st) &&
        not (is_var (fst(dest_pair a)))
    with Failure _ -> false in
  let th = snd (find (fun (_,th) -> is_main th) asl) in
  (UNDISCH_THEN (concl th) MP_TAC THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
   REWRITE_TAC CLOSPROPSAUX_eval_case_eqs THEN
   REPEAT STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_CLEAN_TAC THEN
   CLOSPROPSAUX_CLEAN_TAC) g;;

let CLOSP2AUX_KCA_START_TAC : tactic =
  REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(fun th -> if is_eq (concl th) then MP_TAC th
                           else STRIP_ASSUME_TAC th)) THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN REPEAT CLOSP2AUX_GCASE_TAC THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
  CLOSP2AUX_KN_SING_TAC;;

let CLOSP2AUX_unique_SUB_BAG = prove
 (`!(co:num -> A # clos_exp list # B) a b.
     SUB_BAG (clos_elist_globals a) (clos_elist_globals b) /\ unique_set_globals b co ==>
     unique_set_globals a co`,
  REWRITE_TAC[unique_set_globals_def; clos_elist_globals_append; SUB_BAG_LEQ;
              BAG_ALL_DISTINCT; BAG_UNION] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `e:num`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:num`) THEN ARITH_TAC);;

(* ARITH_TAC on s <= t (s, t sums of atoms and numerals), failing at once    *)
(* when an atom has more occurrences (up to alpha) in s than in t or the     *)
(* numerals of s add up to more: then s <= t has a counterexample and        *)
(* ARITH_TAC fails too.  Other goals, and atoms with arithmetic or binders   *)
(* inside, go to ARITH_TAC                                                    *)
let CLOSP2AUX_SUM_LE_TAC : tactic =
  let ops = ["+"; "-"; "*"; "DIV"; "MOD"; "EXP"; "PRE"; "SUC"; "MIN"; "MAX"] in
  let plain t = not (can (find_term (fun u -> is_abs u ||
                           (is_const u && mem (fst(dest_const u)) ops))) t) in
  let rec summands t = try let a,b = dest_binary "+" t in summands a @ summands b
                       with Failure _ -> [t] in
  let total ns = itlist (fun n a -> dest_small_numeral n + a) ns 0 in
  let refuted w =
    try let s,t = dest_binary "<=" w in
        let ns,xs = partition is_numeral (summands s)
        and nt,xt = partition is_numeral (summands t) in
        forall plain (xs @ xt) &&
        (total ns > total nt ||
         exists (fun x -> length (filter (aconv x) xs) > length (filter (aconv x) xt)) xs)
    with Failure _ -> false in
  fun (asl,w as g) -> if refuted w then failwith "CLOSP2AUX_SUM_LE_TAC" else ARITH_TAC g;;

(* unique_set_globals a co from an assumption unique_set_globals b co, by a  *)
(* pointwise comparison of the global bags (the tactics and terms that do    *)
(* not depend on the goal are made once: a quotation in a tactic that runs   *)
(* per antecedent is parsed each time, milliseconds in a big session)        *)
let CLOSP2AUX_UNIQUE_TAC : tactic =
  let empty_bag = `EMPTY_BAG:num->num` in
  let sub_tac = MATCH_MP_TAC CLOSP2AUX_unique_SUB_BAG in
  let rw1 = REWRITE_TAC[clos_set_globals_def; clos_elist_globals_append; APPEND; MAP] in
  let rw2 = REWRITE_TAC[BAG_UNION_EMPTY; SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG; K_THM] in
  fun (asl,w as g) ->
  let co = rand w in
  let cands = mapfilter (fun (_,th) ->
      let f,args = strip_comb (concl th) in
      if fst(dest_const f) = "unique_set_globals" && el 1 args = co then th
      else failwith "") asl in
  let sgfacts = mapfilter (fun (_,th) ->
      let l,r = dest_eq (concl th) in
      if fst(dest_const(fst(strip_comb l))) = "clos_set_globals" && r = empty_bag
      then th else failwith "") asl in
  FIRST (map (fun th ->
    sub_tac THEN EXISTS_TAC (el 0 (snd(strip_comb(concl th)))) THEN
    CONJ_TAC THENL
     [rw1 THEN REWRITE_TAC sgfacts THEN rw2 THEN GEN_TAC THEN CLOSP2AUX_SUM_LE_TAC;
      ACCEPT_TAC th]) cands) g;;

(* the head constant of a term and its number of arguments (NONE for a      *)
(* variable head): MATCH_MP th a can only succeed when they agree for the    *)
(* antecedent of th and the conclusion of a                                  *)
let CLOSP2AUX_head_of t =
  let h,args = strip_comb t in
  if is_const h then Some (fst(dest_const h), length args) else None;;

(* the facts whose conclusion has the head hd (all of them for NONE), in     *)
(* their order                                                               *)
let CLOSP2AUX_fact_index (facts:thm list) =
  let tbl = Hashtbl.create 64 in
  do_list (fun th -> match CLOSP2AUX_head_of (concl th) with
             Some h -> Hashtbl.replace tbl h (th :: (try Hashtbl.find tbl h with Not_found -> []))
           | None -> ()) (rev facts);
  fun hd -> match hd with
              None -> facts
            | Some h -> (try Hashtbl.find tbl h with Not_found -> []);;

(* ASM_REWRITE_TAC thl, with the rewrite net of the assumptions kept for the *)
(* next goal with the same (physically equal) assumption list: the side      *)
(* provers of the saturations get one goal per antecedent, all with the      *)
(* assumptions of the round                                                  *)
let CLOSP2AUX_ASM_REWRITE_TAC (thl:thm list) : tactic =
  let cache = ref None in
  fun (asl,w as g) ->
    let cv = match !cache with
        Some (a,c) when a == asl -> c
      | _ -> let c = REWRITE_CONV (map snd asl @ thl) in cache := Some (asl,c); c in
    CONV_TAC cv g;;

(* saturation with a prover for ground antecedents that no assumption matches *)
(* (prover is tried only on antecedents whose head constant is in shapes).    *)
(* Each round derives everything again from all the facts; for speed the     *)
(* normalisations are memoised (by conclusion and hypotheses), MATCH_MP th   *)
(* is prepared once per th and only tried on facts with the antecedent's     *)
(* head, and a prover failure is remembered for the rest of the round (the   *)
(* derived facts are exactly those of the plain algorithm)                   *)
let CLOSP2AUX_SATP_GEN_TAC (shapes:string list) (prover:tactic) (thms:thm list)
    (nrm_thms:thm list) (rounds:int) : tactic =
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let nrm_conv = REWRITE_CONV nrm_thms in
  let nrm0 th = curry (CONV_RULE nrm_conv th) in
  let nthms = map nrm0 thms in
  fun g0 ->
  let nmemo = Hashtbl.create 1024 in
  let nrm th = let k = (concl th, hyp th) in
    try Hashtbl.find nmemo k with Not_found ->
    let r = nrm0 th in Hashtbl.add nmemo k r; r in
  let derived = ref ([]:term list) in
  let memo = ref ([]:(term * thm) list) in
  let provable_shape t =
    try mem (fst(dest_const(fst(strip_comb t)))) shapes
    with Failure _ -> false in
  let one_round (asl,w as g) =
    let failed = ref ([]:term list) in
    let asms = map snd asl in
    let facts = filter (fun th -> not (is_impth th) && not (is_forall (concl th))) asms in
    let facts_for = CLOSP2AUX_fact_index facts in
    let rec all_full depth th =
      if not (is_impth th) then [th] else if depth = 0 then [] else
      match (try Some (nrm (CLOSP2AUX_unwind th)) with Failure _ -> None) with
        Some th' -> all_full (depth-1) th'
      | None ->
      let vs,body = strip_forall (concl th) in
      let ant = fst(dest_imp body) in
      let mth = lazy (try MATCH_MP th with Failure _ -> fun _ -> failwith "MATCH_MP") in
      let rs = flat (map (fun a -> try all_full (depth-1) (nrm (Lazy.force mth a))
                                   with Failure _ -> [])
                       (facts_for (CLOSP2AUX_head_of ant))) in
      if rs <> [] then rs else
      if exists (fun v -> free_in v ant) vs || not (provable_shape ant) then [] else
      let r = try Some (assoc ant !memo) with Failure _ ->
                if mem ant !failed then None else
                (match (try Some (TAC_PROOF((asl,ant), prover)) with Failure _ -> None) with
                   Some ath -> (memo := (ant,ath) :: !memo; Some ath)
                 | None -> (failed := ant :: !failed; None)) in
      (match r with
         Some ath -> (try all_full (depth-1) (nrm (MATCH_MP th ath)) with Failure _ -> [])
       | None -> []) in
    let imps = nthms @ map nrm (filter is_impth asms) in
    let results = flat (map (all_full 24) imps) in
    let known_c = map concl asms in
    let rec dedup acc l = match l with
        [] -> rev acc
      | th::rest -> let c = concl th in
                    if c = `T` || mem c known_c || mem c !derived ||
                       exists (fun a -> concl a = c) acc
                    then dedup acc rest else dedup (th::acc) rest in
    let news = dedup [] results in
    derived := map concl news @ !derived;
    if news = [] then failwith "CLOSP2AUX_SATP_TAC: no new facts"
    else (MAP_EVERY CAKE_STRIP_ASSUME_TAC news) g in
  let rec loop n g = if n = 0 then ALL_TAC g else
    (try (one_round THEN loop (n-1)) g with Failure _ -> ALL_TAC g) in
  loop rounds g0;;

let CLOSP2AUX_SATP_TAC =
  CLOSP2AUX_SATP_GEN_TAC ["unique_set_globals"; "SUB_BAG"; "ALL2"; "DISJOINT";
                          "mglobals_disjoint"; "ALL"];;

let CLOSP2AUX_mgd_evaluate = prove
 (`!(s0:(C,FFI)clos_state) xs ys zs env res s.
     clos_evaluate (ys,env,s0) = (res,s) /\
     ssgc_free s0 /\ ALL vsgc_free env /\ ALL clos_esgc_free ys /\
     mglobals_disjoint (clos_state_globals s0) xs /\
     unique_set_globals zs (clos_state_compile_oracle s0) /\
     SUB_BAG (clos_elist_globals (APPEND xs ys)) (clos_elist_globals zs) ==>
     mglobals_disjoint (clos_state_globals s) xs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC mglobals_disjoint_evaluate THEN
  MAP_EVERY EXISTS_TAC [`s0:(C,FFI)clos_state`; `ys:clos_exp list`; `env:clos_v list`;
                        `res:(clos_v list,clos_v)result`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSP2AUX_unique_SUB_BAG THEN
  EXISTS_TAC `zs:clos_exp list` THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_SBAG_PROVE_TAC : tactic =
  REWRITE_TAC[clos_set_globals_def; clos_elist_globals_append; APPEND; MAP;
              BAG_UNION_EMPTY; SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG; K_THM] THEN
  GEN_TAC THEN CLOSP2AUX_SUM_LE_TAC;;

let CLOSP2AUX_kca_var = prove
 (`!vs env extra v.
     ALL2 val_approx_val vs env ==>
     val_approx_val (any_el v vs clos_known_Other) (EL v (APPEND env extra))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[any_el_ALT] THEN COND_CASES_TAC THEN
  REWRITE_TAC[val_approx_val_simps] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN
  SUBGOAL_THEN `v < LENGTH (env:clos_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_SIMP_TAC[EL_APPEND1]]);;

let CLOSP2AUX_ogd_known = prove
 (`!c xs aenv (g0:val_approx spt) eas g (co:num -> (val_approx spt # C) # clos_prog).
     clos_known_known c xs aenv g0 = (eas,g) /\ oracle_gapprox_disjoint g0 co /\
     unique_set_globals xs co ==> oracle_gapprox_disjoint g co`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `xs:clos_exp list`; `aenv:val_approx list`;
                 `g0:val_approx spt`; `eas:(clos_exp#val_approx)list`; `g:val_approx spt`;
                 `clos_state_compile_oracle_fupd (combin_K (co:num -> (val_approx spt # C) # clos_prog))
                    (ARB:(val_approx spt # C,FFI)clos_state)`; `0`]
         oracle_gapprox_disjoint_shift_seq_unique_set_globals) THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; shift_seq_zero]);;

(* evaluation facts with environments of the form APPEND (APPEND l env) extra *)
let CLOSP2AUX_KCA_ENV_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    try let l = lhs (concl th) in
        if fst(dest_const(fst(strip_comb l))) = "clos_evaluate"
        then REWRITE_RULE[APPEND_ASSOC; GSYM (CONJUNCT2 APPEND)] th else th
    with Failure _ -> th);;

let CLOSP2AUX_sga_eval_disj = prove
 (`!es env (s1:(val_approx spt # C,FFI)clos_state) res s2 g.
     clos_evaluate (es,env,s1) = (res,s2) /\ ssgc_free s1 /\ ALL clos_esgc_free es /\
     ALL vsgc_free env /\ state_globals_approx s1 g /\
     oracle_gapprox_disjoint g (clos_state_compile_oracle s1) /\
     DISJOINT (domain g) (SET_OF_BAG (clos_elist_globals es)) ==>
     state_globals_approx s2 g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`es:clos_exp list`; `env:clos_v list`; `s1:(val_approx spt # C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`; `s2:(val_approx spt # C,FFI)clos_state`]
                evaluate_changed_globals) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[state_globals_approx_def] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mglobals_extend_def; IN_UNION]) THEN
  SUBGOAL_THEN `(k:num) IN domain (g:val_approx spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  SUBGOAL_THEN `~(k IN SET_OF_BAG (clos_elist_globals es))` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(k IN SET_OF_BAG (clos_elist_globals (FLAT (first_n_exps
                   (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state)) n))))`
    ASSUME_TAC THENL
   [REWRITE_TAC[IN_SET_OF_BAG] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o MATCH_MP elist_globals_first_n_exps_exists) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[oracle_gapprox_disjoint_def; gapprox_disjoint_def; DISJOINT;
                                EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_BAG]) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[state_globals_approx_def]);;

let CLOSP2AUX_sga_eval_app = prove
 (`!lopt f args (s1:(val_approx spt # C,FFI)clos_state) res s2 g.
     evaluate_app lopt f args s1 = (res,s2) /\ ssgc_free s1 /\ vsgc_free f /\
     ALL vsgc_free args /\ state_globals_approx s1 g /\
     oracle_gapprox_disjoint g (clos_state_compile_oracle s1) ==>
     state_globals_approx s2 g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lopt:num option`; `f:clos_v`; `args:clos_v list`;
                 `s1:(val_approx spt # C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`; `s2:(val_approx spt # C,FFI)clos_state`]
                evaluate_app_changed_globals) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[state_globals_approx_def] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mglobals_extend_def; IN_UNION]) THEN
  SUBGOAL_THEN `(k:num) IN domain (g:val_approx spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  SUBGOAL_THEN `~(k IN SET_OF_BAG (clos_elist_globals (FLAT (first_n_exps
                   (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state)) n))))`
    ASSUME_TAC THENL
   [REWRITE_TAC[IN_SET_OF_BAG] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o MATCH_MP elist_globals_first_n_exps_exists) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[oracle_gapprox_disjoint_def; gapprox_disjoint_def; DISJOINT;
                                EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_BAG]) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[state_globals_approx_def]);;

let CLOSP2AUX_vav_clos_approx = prove
 (`!m loc n body env.
     val_approx_val (clos_approx m loc n body) (clos_Closure (SOME loc) [] env n body)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_approx_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[val_approx_val_simps] THEN MESON_TAC[]);;

let CLOSP2AUX_vav_letrec_SOME = prove
 (`!loc env fns.
     ALL2 val_approx_val (clos_gen_noinline loc 0 fns)
       (list_of_seq (clos_Recclosure (SOME loc) [] env fns) (LENGTH fns))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_gen_noinline_eq; LIST_REL_EL_EQN; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; val_approx_val_simps; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`env:clos_v list`; `loc:num`; `fns:(num#clos_exp)list`; `n:num`] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let CLOSP2AUX_vav_letrec_NONE = prove
 (`!(l:clos_v list) n. LENGTH l = n ==> ALL2 val_approx_val (REPLICATE n clos_known_Other) l`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[LENGTH; REPLICATE; ALL2; val_approx_val_simps]);;

let CLOSP2AUX_known_op_IF = prove
 (`(!as (g:val_approx spt). known_op clos_Install as g = (clos_known_Other,g)) /\
   (!as (g:val_approx spt).
      known_op (clos_ThunkOp ForceThunk) as g = (clos_known_Other,g)) /\
   (isGlobal clos_Install <=> F) /\ (isGlobal (clos_ThunkOp ForceThunk) <=> F)`,
  REWRITE_TAC[known_op_def; isGlobal_def]);;

let CLOSP2AUX_AppUnit_sgc = prove
 (`!x. (clos_esgc_free (clos_AppUnit x) <=> clos_esgc_free x) /\
       clos_set_globals (clos_AppUnit x) = clos_set_globals x`,
  REWRITE_TAC[clos_AppUnit_def; clos_esgc_free_def; clos_set_globals_def; ALL;
              clos_op_gbag_def; BAG_UNION_EMPTY]);;

let CLOSP2AUX_sga_mgext = prove
 (`!(s1:(val_approx spt # C,FFI)clos_state) (s2:(val_approx spt # C,FFI)clos_state) g n.
     state_globals_approx s1 g /\
     oracle_gapprox_disjoint g (clos_state_compile_oracle s1) /\
     mglobals_extend (clos_state_globals s1)
       (SET_OF_BAG (clos_elist_globals (FLAT (first_n_exps (clos_state_compile_oracle s1) n))))
       (clos_state_globals s2)
     ==> state_globals_approx s2 g`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[state_globals_approx_def] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mglobals_extend_def]) THEN
  SUBGOAL_THEN `(k:num) IN domain (g:val_approx spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
  SUBGOAL_THEN `~(k IN SET_OF_BAG (clos_elist_globals (FLAT (first_n_exps
                   (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state)) n))))`
    ASSUME_TAC THENL
   [REWRITE_TAC[IN_SET_OF_BAG] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o MATCH_MP elist_globals_first_n_exps_exists) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[oracle_gapprox_disjoint_def; gapprox_disjoint_def; DISJOINT;
                                EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_BAG]) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[state_globals_approx_def]);;

let CLOSP2AUX_sga_install_Rerr = prove
 (`!vs (s1:(C,FFI)clos_state) e s2 g.
     clos_do_install vs s1 = (Rerr e,s2) ==> ssgc_free s1 ==>
     state_globals_approx s1 g ==> state_globals_approx s2 g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CLOSP2AUX_do_install_Rerr)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[CLOSP2AUX_sga_mglobals]);;

let CLOSP2AUX_sga_install = prove
 (`!vs (s1:(val_approx spt # C,FFI)clos_state) es s2 res s g.
     clos_do_install vs s1 = (Rval es,s2) ==> clos_evaluate (es,[],s2) = (res,s) ==>
     ssgc_free s1 ==> state_globals_approx s1 g ==>
     oracle_gapprox_disjoint g (clos_state_compile_oracle s1) ==>
     state_globals_approx s g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] do_install_ssgc)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`es:clos_exp list`; `[]:clos_v list`; `s2:(val_approx spt # C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`; `s:(val_approx spt # C,FFI)clos_state`]
                evaluate_changed_globals) THEN
  ASM_REWRITE_TAC[ALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  MATCH_MP_TAC CLOSP2AUX_sga_mgext THEN
  MAP_EVERY EXISTS_TAC [`s1:(val_approx spt # C,FFI)clos_state`; `n + 1`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC mglobals_extend_SUBSET THEN
  EXISTS_TAC `{} UNION (SET_OF_BAG (clos_elist_globals es) UNION
     SET_OF_BAG (clos_elist_globals (FLAT (first_n_exps
       (clos_state_compile_oracle (s2:(val_approx spt # C,FFI)clos_state)) n))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC mglobals_extend_trans THEN
    EXISTS_TAC `clos_state_globals (s2:(val_approx spt # C,FFI)clos_state)` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[first_n_exps_shift_seq; FLAT_APPEND; FLAT; APPEND_NIL;
                    clos_elist_globals_append; SET_OF_BAG_UNION] THEN SET_TAC[]]);;

let CLOSP2AUX_evaluate_app_SING = prove
 (`!loc_opt f args (s:(C,FFI)clos_state) vs s1.
     evaluate_app loc_opt f args s = (Rval vs,s1) ==> ?v. vs = [v]`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_app_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL; ONE] THEN MESON_TAC[]);;

let CLOSP2AUX_letinline_eval = prove
 (`!loc_opt m n body env' args (s:(C,FFI)clos_state) vs s'.
     evaluate_app loc_opt (clos_Closure (SOME m) [] env' n body) args s = (Rval vs,s') ==>
     n = LENGTH args ==> n > 0 ==>
     clos_evaluate ([body],APPEND args env',clos_dec_clock n s) = (Rval vs,s')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(args:clos_v list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `TAKE (LENGTH args) (REVERSE args) = REVERSE (args:clos_v list) /\
                DROP (LENGTH args) (REVERSE args) = []` STRIP_ASSUME_TAC THENL
   [MESON_TAC[LENGTH_REVERSE; TAKE_LENGTH_ID; DROP_LENGTH_NIL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "evaluate_app" with Failure _ -> false))) THEN
  ASM_SIMP_TAC[evaluate_app_rw] THEN
  REWRITE_TAC[dest_closure_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES; LT_REFL; SUB_0; APPEND_NIL; REVERSE_REVERSE; REVERSE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GT]) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  REWRITE_TAC[LENGTH; SUB_0] THEN
  MP_TAC(ISPEC `clos_evaluate ([body],APPEND args env',clos_dec_clock (LENGTH args)
                                 (s:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[] THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN CAKE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:clos_v list` THEN CAKE_REWRITE_TAC[] THEN
      TRY(CASES_ON `a1:clos_v list` THEN CAKE_REWRITE_TAC[])) THEN
  REWRITE_TAC[evaluate_app_NIL; PAIR_EQ; injectivity "result"; distinctness "result"] THEN NO_TAC);;

let CLOSP2AUX_kca_nrm = [mglobals_disjoint_rw; ALL; APPEND_SING; CONJUNCT1 APPEND;
  APPEND_NIL; MAP; clos_esgc_free_def; PAIR_EQ; HD;
  ALL_APPEND; rsgc_free_def; injectivity "result"; distinctness "result"; ALL2;
  MAP_APPEND; state_globals_approx_dec_clock; CLOSP2AUX_dec_clock_acc; ssgc_free_dec_clock;
  state_globals_approx_clock_fupd; val_approx_val_simps; val_approx_sgc_free_def;
  EVERY_REPLICATE; clos_gen_noinline_val_approx_sgc_free; clos_set_globals_def;
  BAG_UNION_EMPTY; OPTION_MAP_EQ_SOME; CLOSP2AUX_known_op_IF; CLOSP2AUX_AppUnit_sgc;
  LIST_REL_REVERSE_EQ; state_globals_approx_refsfupd; vsgc_free_def; CONS_11;
  injectivity "val_approx"; injectivity "clos_v"];;

let CLOSP2AUX_KCA_SIDE_TAC : tactic =
  let sgrw = CLOSP2AUX_ASM_REWRITE_TAC
               [clos_set_globals_def; BAG_UNION_EMPTY; BAG_OF_EMPTY; DISJOINT_EMPTY] in
  FIRST [CLOSP2AUX_ASM_REWRITE_TAC CLOSP2AUX_kca_nrm THEN NO_TAC; CLOSP2AUX_UNIQUE_TAC;
         CLOSP2AUX_SBAG_PROVE_TAC;
         MATCH_MP_TAC LIST_REL_APPEND_suff THEN
           CLOSP2AUX_ASM_REWRITE_TAC[CLOSP2AUX_vav_letrec_SOME] THEN
           TRY(MATCH_MP_TAC CLOSP2AUX_vav_letrec_NONE THEN
               REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN NO_TAC) THEN NO_TAC;
         sgrw THEN NO_TAC;
         REWRITE_TAC[EVERY_GENLIST; vsgc_free_def; ALL; ALL_APPEND] THEN
           CLOSP2AUX_ASM_REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[mglobals_disjoint_def] THEN sgrw THEN NO_TAC];;

let CLOSP2AUX_lookup_vars_vsgc = prove
 (`!vs (env:clos_v list) extra env'.
     lookup_vars vs (APPEND env extra) = SOME env' ==>
     ALL vsgc_free env ==> ALL vsgc_free extra ==> ALL vsgc_free env'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vs:num list`; `APPEND env extra:clos_v list`; `env':clos_v list`]
    (INST [`vsgc_free`,`P:clos_v->bool`] (INST_TYPE [`:clos_v`,`:A`] EVERY_lookup_vars))) THEN
  ASM_REWRITE_TAC[ALL_APPEND]);;

let CLOSP2AUX_kca_fwd = [unique_set_globals_evaluate; evaluate_changed_globals;
  oracle_gapprox_disjoint_lemma; known_preserves_esgc_free; CLOSP2AUX_mgd_evaluate;
  state_globals_approx_evaluate; state_globals_approx_known_mglobals_disjoint;
  state_globals_approx_known_op_evaluate; CLOSP2AUX_ogd_known;
  CLOSP2AUX_sga_eval_disj; CLOSP2AUX_sga_eval_app; CLOSP2AUX_find_code_sgc;
  known_unchanged_globals; CLOSP2AUX_lookup_vars_vsgc; known_op_correct_approx;
  CLOSP2AUX_dest_thunk_sgc; CLOSP2AUX_sga_install; CLOSP2AUX_sga_install_Rerr;
  CLOSP2AUX_evaluate_app_SING; CLOSP2AUX_letinline_eval;
  decide_inline_LetInline_IMP_Clos_fv_max; set_globals_empty_esgc_free;
  clos_evaluate_IMP_LENGTH];;

let CLOSP2AUX_KCA_NRM1_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kca_nrm) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) || is_exists (concl th) ||
                                    concl th = `F`
                                 then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  TRY RVEQ_TAC;;

let CLOSP2AUX_KCA_NRM_TAC : tactic =
  CLOSP2AUX_KCA_NRM1_TAC THEN CLOSP2AUX_CG_SING_TAC THEN
  CLOSP2AUX_KCA_NRM1_TAC THEN CLOSP2AUX_KCA_NRM1_TAC;;

let CLOSP2AUX_KCA_CASE_TAC : tactic =
  CLOSP2AUX_KCA_START_TAC THEN CLOSP2AUX_KCA_EVAL_TAC THEN CLOSP2AUX_KCA_ENV_TAC THEN
  CLOSP2AUX_KCA_NRM_TAC THEN
  CLOSP2AUX_SATP_TAC CLOSP2AUX_KCA_SIDE_TAC CLOSP2AUX_kca_fwd CLOSP2AUX_kca_nrm 5 THEN
  CLOSP2AUX_KCA_NRM_TAC THEN
  CLOSP2AUX_SATP_TAC CLOSP2AUX_KCA_SIDE_TAC CLOSP2AUX_kca_fwd CLOSP2AUX_kca_nrm 4 THEN
  CLOSP2AUX_KCA_NRM_TAC THEN
  REWRITE_TAC CLOSP2AUX_kca_nrm THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_kca_var THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC val_approx_val_merge_I THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_ACCEPT_TAC CLOSP2AUX_vav_clos_approx);;

let CLOSP2AUX_kca_thm =
  MP CLOSP2AUX_kca_ind
    (end_itlist CONJ (map (fun t -> prove(t, CLOSP2AUX_KCA_CASE_TAC)) CLOSP2AUX_kca_cases));;

(* HOL4: known_correct_approx (the HOL4 statement has fv_max commented out) *)
let known_correct_approx = prove
 (`!c xs aenv (g0:val_approx spt) eas g env extra (s0:(val_approx spt # C,FFI)clos_state)
    res s.
     clos_known_known c xs aenv g0 = (eas,g) /\
     clos_evaluate (xs,APPEND env extra,s0) = (res,s) /\
     unique_set_globals xs (clos_state_compile_oracle s0) /\
     ALL2 val_approx_val aenv env /\
     state_globals_approx s0 g0 /\
     mglobals_disjoint (clos_state_globals s0) xs /\
     oracle_gapprox_disjoint g0 (clos_state_compile_oracle s0) /\
     ssgc_free s0 /\ ALL vsgc_free (APPEND env extra) /\ ALL clos_esgc_free xs /\
     ALL val_approx_sgc_free aenv /\ globals_approx_sgc_free g0 ==>
     state_globals_approx s g /\
     !vs. res = Rval vs ==> ALL2 val_approx_val (MAP SND eas) vs`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_ACCEPT_TAC CLOSP2AUX_kca_thm);;

(* HOL4: monotonic_gapprox_disjoint *)
let monotonic_gapprox_disjoint = prove
 (`!c xs aenv ys g (co:num -> A # clos_exp list # B) b.
     clos_known_known c xs aenv LN = (ys,g) ==>
     oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
       (SET_OF_BAG b) co ==>
     b = clos_elist_globals xs ==>
     oracle_gapprox_disjoint g co`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP known_changed_globals) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP oracle_monotonic_init) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM; domain_def; NOT_IN_EMPTY]) THEN
  REWRITE_TAC[oracle_gapprox_disjoint_def; gapprox_disjoint_def; DISJOINT; EXTENSION;
              IN_INTER; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[LT_REFL]);;

let CLOSP2AUX_elist_FLAT_FOLDR = prove
 (`!ys. clos_elist_globals (FLAT ys) = ITLIST BAG_UNION (MAP clos_elist_globals ys) EMPTY_BAG`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FLAT; MAP; ITLIST; clos_elist_globals_append; clos_set_globals_def]);;

(* HOL4: elist_globals_FLAT_APPEND_FOLDR *)
let elist_globals_FLAT_APPEND_FOLDR = prove
 (`!xs ys. clos_elist_globals (APPEND xs (FLAT ys)) =
           ITLIST BAG_UNION (MAP clos_elist_globals (CONS xs ys)) EMPTY_BAG`,
  REWRITE_TAC[clos_elist_globals_append; CLOSP2AUX_elist_FLAT_FOLDR; MAP; ITLIST]);;

(* HOL4: elist_globals_FLAT_FOLDR (an instance of the previous theorem)    *)
let elist_globals_FLAT_FOLDR = prove
 (`!ys. clos_elist_globals (FLAT ys) =
        BAG_UNION EMPTY_BAG (ITLIST BAG_UNION (MAP clos_elist_globals ys) EMPTY_BAG)`,
  REWRITE_TAC[CLOSP2AUX_elist_FLAT_FOLDR; BAG_UNION_EMPTY]);;

(* HOL4: monotonic_unique_set_globals *)
let monotonic_unique_set_globals = prove
 (`!xs (co:num -> A # clos_exp list # B).
     oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
       (SET_OF_BAG (clos_elist_globals xs)) co ==>
     BAG_ALL_DISTINCT (clos_elist_globals xs) /\
     (!n. BAG_ALL_DISTINCT (clos_elist_globals (FST (SND (co n))))) ==>
     unique_set_globals xs co`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP oracle_monotonic_init) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP oracle_monotonic_step) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM; IN_SET_OF_BAG]) THEN
  REWRITE_TAC[unique_set_globals_def] THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[first_n_exps_def; list_of_seq; FLAT; APPEND_NIL]; ALL_TAC] THEN
  REWRITE_TAC[CLOSP2AUX_first_n_exps_SUC; FLAT_APPEND; FLAT; APPEND_NIL; APPEND_ASSOC] THEN
  ONCE_REWRITE_TAC[clos_elist_globals_append] THEN
  ASM_REWRITE_TAC[BAG_ALL_DISTINCT_BAG_UNION; BAG_DISJOINT_BAG_IN] THEN
  X_GEN_TAC `e:num` THEN
  REWRITE_TAC[clos_elist_globals_append; BAG_IN_BAG_UNION; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `BAG_IN e (clos_elist_globals (FST (SND ((co:num -> A # clos_exp list # B) n))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
   [ASM_MESON_TAC[LT_REFL];
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o
      MATCH_MP elist_globals_first_n_exps_exists) THEN
    ASM_MESON_TAC[LT_REFL]]);;

(* HOL4: pure_co_oracle_props *)
let pure_co_oracle_props = prove
 (`!(f:P->Q) (co:num -> (val_approx spt # B) # P).
     oracle_gapprox_subspt (pure_co f o co) = oracle_gapprox_subspt co /\
     oracle_state_sgc_free (pure_co f o co) = oracle_state_sgc_free co`,
  REWRITE_TAC[oracle_gapprox_subspt_def; oracle_state_sgc_free_def; o_THM; FST_pure_co]);;

(* HOL4: state_oracle_domain *)
let state_oracle_domain = prove
 (`!c (co:num -> (val_approx spt # B) # clos_exp list # D) n.
     is_state_oracle (clos_known_compile_inc c) co ==>
     SUB_BAG (BAG_OF_SET (domain (FST (FST (co n)))))
             (BAG_UNION (BAG_OF_SET (domain (FST (FST (co 0)))))
                        (clos_elist_globals (FLAT (first_n_exps co n))))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[first_n_exps_def; list_of_seq; FLAT; clos_set_globals_def; BAG_UNION_EMPTY;
                SUB_BAG_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[is_state_oracle_def]) THEN
  MP_TAC(ISPEC `SND ((co:num -> (val_approx spt # B) # clos_exp list # D) n)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:clos_exp list` (X_CHOOSE_THEN `aux:D` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[clos_known_compile_inc_def; LET_DEF; LET_END_DEF;
                  pair_CASE_def; FST] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`reset_inline_factor c`; `es:clos_exp list`; `[]:val_approx list`;
    `FST (FST ((co:num -> (val_approx spt # B) # clos_exp list # D) n))`;
    `FST (clos_known_known (reset_inline_factor c) es []
              (FST (FST ((co:num -> (val_approx spt # B) # clos_exp list # D) n))))`;
    `SND (clos_known_known (reset_inline_factor c) es []
              (FST (FST ((co:num -> (val_approx spt # B) # clos_exp list # D) n))))`]
    known_changed_globals_alt) THEN
  REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSP2AUX_first_n_exps_SUC; FLAT_APPEND; FLAT; APPEND_NIL;
              clos_elist_globals_append] THEN
  ASM_REWRITE_TAC[] THEN CLOSP2AUX_SBAG_TAC);;

(* ------------------------------------------------------------------------- *)
(* code relation                                                             *)
(* ------------------------------------------------------------------------- *)

(* HOL4: exp_rel_def; c with inline_factor := k is                          *)
(* clos_known_config_inline_factor_fupd (K k) c                             *)
let clos_knownProof_exp_rel_def = cake_def
  `clos_knownProof_exp_rel c aenv (g':val_approx spt) e1 e2 <=>
     ?g0 g apx k.
       subspt g g' /\ ALL val_approx_sgc_free aenv /\ globals_approx_sgc_free g0 /\
       clos_known_known (clos_known_config_inline_factor_fupd (combin_K k) c) [e1] aenv g0 = ([(e2,apx)],g)`;;

(* HOL4: exp_rel_dec_inline_factor [simp] *)
let exp_rel_dec_inline_factor = prove
 (`!c aenv g e1 e2.
     clos_knownProof_exp_rel (dec_inline_factor c) aenv g e1 e2 <=>
     clos_knownProof_exp_rel c aenv g e1 e2`,
  REWRITE_TAC[clos_knownProof_exp_rel_def; dec_inline_factor_def;
              clos_known_config_INFO.ri_fupdfupds; K_o_THM]);;
let _ = cake_add_simps [exp_rel_dec_inline_factor];;

(* HOL4: f_rel_def *)
let clos_knownProof_f_rel_def = cake_def
  `clos_knownProof_f_rel c aenv (g:val_approx spt) (n1,e1) (n2,e2) <=>
     n1 = n2 /\
     clos_knownProof_exp_rel c (APPEND (REPLICATE n1 clos_known_Other) aenv) g e1 e2`;;

(* HOL4: v1_size_append; HOL4's v1_size (the size of a value list) is      *)
(* list_size clos_v_size                                                     *)
let v1_size_append = prove
 (`!xs ys. list_size clos_v_size (APPEND xs ys) =
           list_size clos_v_size xs + list_size clos_v_size ys`,
  REWRITE_TAC[list_size_append]);;

(* v_rel recurses through ALL2: the definition registers the admissibility *)
(* rule LISTAUX_ADMISSIBLE_ALL2 (a recursive call under ALL2 R l1 l2  *)
(* gets the context MEM y l1 /\ MEM z l2, as with HOL4's LIST_REL_CONG) for *)
(* this definition only                                                     *)

(* HOL4: v_rel_def (the definition; HOL4 rebinds v_rel_def at line 2619 to *)
(* its SIMP_RULE (bool_ss ++ ETA_ss) form, which is clos_knownProof_v_rel_def *)
(* below)                                                                    *)
(* TERM_TAC with list_size_append: the environments are split by APPEND *)
let CLOSP2AUX_kn_v_rel_TC_TAC : tactic =
  REPEAT BOSS_STRIP_TAC THEN RVEQ_TAC THEN
  (fun g -> let ths = WF_REL_THMS @ [FST; SND; pair_size_THM; sum_CASE] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REWRITE_TAC[list_size_append] THEN
  MEM_SIZE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pair_size_THM]) THEN
  ASM_ARITH_TAC;;

let CLOSP2AUX_kn_v_rel_raw_def =
  let saved = !cake_admissible_rules in
  cake_register_admissible "ALL2" LISTAUX_ADMISSIBLE_ALL2;
  let th = try cake_def_wf
    `MEASURE (\x:clos_known_config # val_approx spt # clos_v # clos_v.
                clos_v_size (FST (SND (SND x))))`
    CLOSP2AUX_kn_v_rel_TC_TAC
    `(clos_knownProof_v_rel c g (clos_Number iv) v <=> v = clos_Number iv) /\
     (clos_knownProof_v_rel c g (clos_Word64 w) v <=> v = clos_Word64 w) /\
     (clos_knownProof_v_rel c g (ByteVector ws) v <=> v = ByteVector ws) /\
     (clos_knownProof_v_rel c g (clos_RefPtr b n) v <=> v = clos_RefPtr b n) /\
     (clos_knownProof_v_rel c g (clos_Block n xs) v <=>
        ?ys. v = clos_Block n ys /\ ALL2 (clos_knownProof_v_rel c g) xs ys) /\
     (clos_knownProof_v_rel c g (clos_Closure loc_opt args1 env1 num_args e1) v <=>
        every_Fn_vs_NONE [e1] /\
        ?aenv env1a env1b args2 env2a env2b e2.
          if env1 = APPEND env1a env1b then
            fv_max (num_args + LENGTH env1a) [e1] /\
            ALL2 (clos_knownProof_v_rel c g) args1 args2 /\
            ALL2 (clos_knownProof_v_rel c g) env1a env2a /\
            ALL2 val_approx_val aenv env1a /\
            clos_knownProof_exp_rel c (APPEND (REPLICATE num_args clos_known_Other) aenv)
              g e1 e2 /\
            v = clos_Closure loc_opt args2 (APPEND env2a env2b) num_args e2
          else F) /\
     (clos_knownProof_v_rel c g (clos_Recclosure loc_opt args1 env1 funs1 i) v <=>
        ALL (\p. match p with (n,e) -> every_Fn_vs_NONE [e]) funs1 /\
        (let clos = (match loc_opt with
                       NONE -> REPLICATE (LENGTH funs1) clos_known_Other
                     | SOME loc -> clos_gen_noinline loc 0 funs1) in
         ?aenv env1a env1b args2 env2a env2b funs2.
           if env1 = APPEND env1a env1b then
             ALL (\p. match p with
                        (num_args,exp) ->
                          fv_max (num_args + LENGTH funs1 + LENGTH env1a) [exp]) funs1 /\
             ALL2 (clos_knownProof_v_rel c g) args1 args2 /\
             ALL2 (clos_knownProof_v_rel c g) env1a env2a /\
             ALL2 val_approx_val aenv env1a /\
             ALL2 (clos_knownProof_f_rel c (APPEND clos aenv) g) funs1 funs2 /\
             v = clos_Recclosure loc_opt args2 (APPEND env2a env2b) funs2 i
           else F))`
    with e -> (cake_admissible_rules := saved; raise e) in
  cake_admissible_rules := saved; th;;

let CLOSP2AUX_COND_F = prove
 (`!p q. (if p then q else F) <=> p /\ q`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4: v_rel_def [simp,compute] (the rebinding of HOL4 line 2619) *)
let clos_knownProof_v_rel_def = prove
 (CASE_TERM
  `(!c g iv v. clos_knownProof_v_rel c g (clos_Number iv) v <=> v = clos_Number iv) /\
   (!c g w v. clos_knownProof_v_rel c g (clos_Word64 w) v <=> v = clos_Word64 w) /\
   (!c g ws v. clos_knownProof_v_rel c g (ByteVector ws) v <=> v = ByteVector ws) /\
   (!c g b n v. clos_knownProof_v_rel c g (clos_RefPtr b n) v <=> v = clos_RefPtr b n) /\
   (!c g n xs v. clos_knownProof_v_rel c g (clos_Block n xs) v <=>
                 ?ys. v = clos_Block n ys /\ ALL2 (clos_knownProof_v_rel c g) xs ys) /\
   (!c g loc_opt args1 env1 num_args e1 v.
      clos_knownProof_v_rel c g (clos_Closure loc_opt args1 env1 num_args e1) v <=>
      every_Fn_vs_NONE [e1] /\
      ?aenv env1a env1b args2 env2a env2b e2.
        env1 = APPEND env1a env1b /\
        fv_max (num_args + LENGTH env1a) [e1] /\
        ALL2 (clos_knownProof_v_rel c g) args1 args2 /\
        ALL2 (clos_knownProof_v_rel c g) env1a env2a /\
        ALL2 val_approx_val aenv env1a /\
        clos_knownProof_exp_rel c (APPEND (REPLICATE num_args clos_known_Other) aenv)
          g e1 e2 /\
        v = clos_Closure loc_opt args2 (APPEND env2a env2b) num_args e2) /\
   (!c g loc_opt args1 env1 funs1 i v.
      clos_knownProof_v_rel c g (clos_Recclosure loc_opt args1 env1 funs1 i) v <=>
      ALL (\p. match p with (n,e) -> every_Fn_vs_NONE [e]) funs1 /\
      ?aenv env1a env1b args2 env2a env2b funs2.
        env1 = APPEND env1a env1b /\
        ALL (\p. match p with
                   (num_args,exp) ->
                     fv_max (num_args + LENGTH funs1 + LENGTH env1a) [exp]) funs1 /\
        ALL2 (clos_knownProof_v_rel c g) args1 args2 /\
        ALL2 (clos_knownProof_v_rel c g) env1a env2a /\
        ALL2 val_approx_val aenv env1a /\
        ALL2 (clos_knownProof_f_rel c
                (APPEND (match loc_opt with
                           NONE -> REPLICATE (LENGTH funs1) clos_known_Other
                         | SOME loc -> clos_gen_noinline loc 0 funs1) aenv) g) funs1 funs2 /\
        v = clos_Recclosure loc_opt args2 (APPEND env2a env2b) funs2 i)`,
  REWRITE_TAC[CLOSP2AUX_kn_v_rel_raw_def; LET_DEF; LET_END_DEF; CLOSP2AUX_COND_F]);;
let _ = cake_add_simps [clos_knownProof_v_rel_def];;

(* HOL4: val v_rel_ind = theorem "v_rel_ind" *)
let clos_knownProof_v_rel_ind = cake_ind "clos_knownProof_v_rel";;

(* HOL4: v_rel_app_def *)
let v_rel_app_def = cake_def
  `(v_rel_app c g (clos_Number iv) v (args1:(clos_v list)option) <=>
      clos_knownProof_v_rel c g (clos_Number iv) v) /\
   (v_rel_app c g (clos_Word64 w) v args1 <=> clos_knownProof_v_rel c g (clos_Word64 w) v) /\
   (v_rel_app c g (ByteVector ws) v args1 <=> clos_knownProof_v_rel c g (ByteVector ws) v) /\
   (v_rel_app c g (clos_RefPtr b n) v args1 <=> clos_knownProof_v_rel c g (clos_RefPtr b n) v) /\
   (v_rel_app c g (clos_Block n xs) v args1 <=> clos_knownProof_v_rel c g (clos_Block n xs) v) /\
   (v_rel_app c g (clos_Closure loc_opt pargs1 env1 num_args e1) v args1 <=>
      every_Fn_vs_NONE [e1] /\
      ?aenv env1a env1b pargs2 env2a env2b e2 aargs.
        env1 = APPEND env1a env1b /\
        fv_max (num_args + LENGTH env1a) [e1] /\
        ALL2 (clos_knownProof_v_rel c g) pargs1 pargs2 /\
        ALL2 (clos_knownProof_v_rel c g) env1a env2a /\
        ALL2 val_approx_val aenv env1a /\
        (match args1 with
           NONE -> aargs = REPLICATE num_args clos_known_Other
         | SOME args1' -> ALL2 val_approx_val aargs args1' /\ pargs1 = []) /\
        clos_knownProof_exp_rel c (APPEND aargs aenv) g e1 e2 /\
        v = clos_Closure loc_opt pargs2 (APPEND env2a env2b) num_args e2) /\
   (v_rel_app c g (clos_Recclosure loc_opt pargs1 env1 funs1 i) v args1 <=>
      clos_knownProof_v_rel c g (clos_Recclosure loc_opt pargs1 env1 funs1 i) v)`;;

(* HOL4: v_rel_app_NONE *)
let v_rel_app_NONE = prove
 (`!c g v1 v2. v_rel_app c g v1 v2 NONE <=> clos_knownProof_v_rel c g v1 v2`,
  REPEAT GEN_TAC THEN CASES_ON `v1:clos_v` THEN
  REWRITE_TAC[v_rel_app_def; clos_knownProof_v_rel_def] THEN CAKE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* HOL4: exp_rel_upd_inline_factor *)
let exp_rel_upd_inline_factor = prove
 (`!c k. clos_knownProof_exp_rel (clos_known_config_inline_factor_fupd (combin_K k) c) =
         clos_knownProof_exp_rel c`,
  REWRITE_TAC[FUN_EQ_THM; clos_knownProof_exp_rel_def;
              clos_known_config_INFO.ri_fupdfupds; K_o_THM]);;

(* HOL4: f_rel_upd_inline_factor *)
let f_rel_upd_inline_factor = prove
 (`!c k. clos_knownProof_f_rel (clos_known_config_inline_factor_fupd (combin_K k) c) =
         clos_knownProof_f_rel c`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; clos_knownProof_f_rel_def;
              exp_rel_upd_inline_factor]);;

let CLOSP2AUX_ALL2_MEM_MONO = prove
 (`!(R:A->B->bool) R' l1 l2.
     (!y z. MEM y l1 /\ MEM z l2 /\ R y z ==> R' y z) /\ ALL2 R l1 l2 ==> ALL2 R' l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[]);;

(* ALL2 R' l1 l2 from an assumption ALL2 R l1 l2: the pointwise step by    *)
(* ASM_MESON_TAC with the given theorems                                    *)
let CLOSP2AUX_ALL2_TRANSFER_TAC (thl:thm list) : tactic = fun (asl,w as gl) ->
  let f,args = strip_comb w in
  if not (fst(dest_const f) = "ALL2") || not (length args = 3)
  then failwith "CLOSP2AUX_ALL2_TRANSFER_TAC" else
  let l1 = el 1 args and l2 = el 2 args in
  let cands = filter (fun (_,th) -> let g,a = strip_comb (concl th) in
                 (try fst(dest_const g) = "ALL2" with Failure _ -> false) &&
                 length a = 3 && el 1 a = l1 && el 2 a = l2) asl in
  FIRST (map (fun (_,th) ->
     MATCH_MP_TAC CLOSP2AUX_ALL2_MEM_MONO THEN EXISTS_TAC (hd (snd (strip_comb (concl th)))) THEN
     CONJ_TAC THENL [ASM_MESON_TAC thl; ACCEPT_TAC th]) cands) gl;;

(* the witness of ?x. P is the free variable of the assumptions named as x  *)
(* without its primes (else x itself)                                        *)
let CLOSP2AUX_SAME_EXISTS_TAC : tactic = fun (asl,w as gl) ->
  let v,_ = dest_exists w in
  let n,ty = dest_var v in
  let rec strip s = let l = String.length s in
    if l > 0 && String.get s (l-1) = '\'' then strip (String.sub s 0 (l-1)) else s in
  let base = strip n in
  let fvs = freesl (map (concl o snd) asl) in
  let wit = try find (fun u -> dest_var u = (base,ty)) fvs with Failure _ -> v in
  EXISTS_TAC wit gl;;

(* HOL4: v_rel_upd_inline_factor *)
let v_rel_upd_inline_factor = prove
 (`!k c. clos_knownProof_v_rel (clos_known_config_inline_factor_fupd (combin_K k) c) =
         clos_knownProof_v_rel c`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MATCH_MP_TAC clos_knownProof_v_rel_ind THEN
  REWRITE_TAC[clos_knownProof_v_rel_def; exp_rel_upd_inline_factor; f_rel_upd_inline_factor] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CLOSP2AUX_SAME_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE CLOSP2AUX_ALL2_TRANSFER_TAC []));;

(* HOL4: v_rel_Block [simp] *)
let clos_knownProof_v_rel_Block = prove
 (`!c g x n ys. clos_knownProof_v_rel c g x (clos_Block n ys) <=>
                ?xs. x = clos_Block n xs /\ ALL2 (clos_knownProof_v_rel c g) xs ys`,
  REPEAT GEN_TAC THEN CASES_ON `x:clos_v` THEN
  REWRITE_TAC[clos_knownProof_v_rel_def; distinctness "clos_v"; injectivity "clos_v"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [clos_knownProof_v_rel_Block];;

(* HOL4: v_rel_Boolv [simp] *)
let clos_knownProof_v_rel_Boolv = prove
 (`!c g b v. (clos_knownProof_v_rel c g (clos_Boolv b) v <=> v = clos_Boolv b) /\
             (clos_knownProof_v_rel c g v (clos_Boolv b) <=> v = clos_Boolv b)`,
  REWRITE_TAC[clos_Boolv_def; clos_knownProof_v_rel_def; clos_knownProof_v_rel_Block;
              LIST_REL_NIL] THEN MESON_TAC[]);;
let _ = cake_add_simps [clos_knownProof_v_rel_Boolv];;

(* HOL4: v_rel_Unit [simp] *)
let clos_knownProof_v_rel_Unit = prove
 (`!c g v. (clos_knownProof_v_rel c g clos_Unit v <=> v = clos_Unit) /\
           (clos_knownProof_v_rel c g v clos_Unit <=> v = clos_Unit)`,
  REWRITE_TAC[clos_Unit_def; clos_knownProof_v_rel_def; clos_knownProof_v_rel_Block;
              LIST_REL_NIL] THEN MESON_TAC[]);;
let _ = cake_add_simps [clos_knownProof_v_rel_Unit];;

let CLOSP2AUX_kn_simple_val_rel = prove
 (`!c g. clos_simple_val_rel (clos_knownProof_v_rel c g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_simple_val_rel_def; isClos_cases] THEN
  REWRITE_TAC[clos_knownProof_v_rel_Block] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN CASES_ON `x:clos_v` THEN
  REWRITE_TAC[clos_knownProof_v_rel_def; distinctness "clos_v"; injectivity "clos_v"] THEN
  MESON_TAC[]);;

(* HOL4: v_rel_IMP_v_to_bytes_lemma [local] *)
let clos_knownProof_v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y c g.
     clos_knownProof_v_rel c g x y ==>
     !ns. (clos_v_to_list x = SOME (MAP (clos_Number o int_of_num o (val:byte->num)) ns) <=>
           clos_v_to_list y = SOME (MAP (clos_Number o int_of_num o (val:byte->num)) ns))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_ASSOC] THEN ONCE_REWRITE_TAC[MAP_o] THEN
  MP_TAC(MATCH_MP v_rel_to_list_byte1
    (SPECL [`c:clos_known_config`; `g:val_approx spt`] CLOSP2AUX_kn_simple_val_rel)) THEN
  DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `x:clos_v`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* HOL4: v_rel_IMP_v_to_bytes [local] *)
let clos_knownProof_v_rel_IMP_v_to_bytes = prove
 (`!c g x y. clos_knownProof_v_rel c g x y ==> clos_v_to_bytes y = clos_v_to_bytes x`,
  MESON_TAC[clos_simple_val_rel_v_to_bytes; CLOSP2AUX_kn_simple_val_rel]);;

(* HOL4: v_rel_IMP_v_to_words_lemma [local] *)
let clos_knownProof_v_rel_IMP_v_to_words_lemma = prove
 (`!x y c g.
     clos_knownProof_v_rel c g x y ==>
     !ns. (clos_v_to_list x = SOME (MAP clos_Word64 ns) <=>
           clos_v_to_list y = SOME (MAP clos_Word64 ns))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:clos_known_config`; `g:val_approx spt`] CLOSP2AUX_kn_simple_val_rel) THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `clos_v_to_list y` (cases "option")) THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`x:clos_v`; `y:clos_v`; `clos_knownProof_v_rel c g`] vr_list_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[distinctness "option"];
    FIRST_ASSUM(MP_TAC o MATCH_MP CLOSPROPSAUX_v_to_list_SOME) THEN
    DISCH_THEN(MP_TAC o SPECL [`y:clos_v`; `a:clos_v list`; `x:clos_v`]) THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[injectivity "option"] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP val_rel_to_words_lemma) THEN
    DISCH_THEN(MP_TAC o SPECL [`xs:clos_v list`; `a:clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* HOL4: v_rel_IMP_v_to_words [local] *)
let clos_knownProof_v_rel_IMP_v_to_words = prove
 (`!c g x y. clos_knownProof_v_rel c g x y ==> clos_v_to_words y = clos_v_to_words x`,
  MESON_TAC[clos_simple_val_rel_v_to_words; CLOSP2AUX_kn_simple_val_rel]);;

(* HOL4: ref_rel *)
let clos_knownProof_ref_rel_rules,clos_knownProof_ref_rel_ind,
    clos_knownProof_ref_rel_cases,clos_knownProof_ref_rel_strongind =
  cake_inductive
  `(!bs. clos_knownProof_ref_rel c (g:val_approx spt) (clos_ByteArray bs) (clos_ByteArray bs)) /\
   (!xs ys.
      ALL2 (clos_knownProof_v_rel c g) xs ys ==>
      clos_knownProof_ref_rel c g (clos_ValueArray xs) (clos_ValueArray ys)) /\
   (!m v w.
      clos_knownProof_v_rel c g v w ==>
      clos_knownProof_ref_rel c g (clos_Thunk m v) (clos_Thunk m w))`;;

(* HOL4: ref_rel_simps [simp] (derived with SIMP_CONV from the cases) *)
let clos_knownProof_ref_rel_simps = prove
 (`(!c g vs x. clos_knownProof_ref_rel c g (clos_ValueArray vs) x <=>
               ?ys. x = clos_ValueArray ys /\ ALL2 (clos_knownProof_v_rel c g) vs ys) /\
   (!c g bs x. clos_knownProof_ref_rel c g (clos_ByteArray bs) x <=> x = clos_ByteArray bs) /\
   (!c g m v x. clos_knownProof_ref_rel c g (clos_Thunk m v) x <=>
                ?w. x = clos_Thunk m w /\ clos_knownProof_v_rel c g v w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_knownProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN MESON_TAC[]);;
let _ = cake_add_simps [clos_knownProof_ref_rel_simps];;

(* HOL4: ref_rel_upd_inline_factor *)
let ref_rel_upd_inline_factor = prove
 (`!c k. clos_knownProof_ref_rel (clos_known_config_inline_factor_fupd (combin_K k) c) =
         clos_knownProof_ref_rel c`,
  REWRITE_TAC[FUN_EQ_THM; clos_knownProof_ref_rel_cases; v_rel_upd_inline_factor]);;

(* HOL4: state_rel_def *)
let clos_knownProof_state_rel_def = cake_def
  `clos_knownProof_state_rel c (g:val_approx spt) (s:(val_approx spt # C,FFI)clos_state)
                             (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     (!n. fv_max 0 (FST (SND (clos_state_compile_oracle s n)))) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_clock s = clos_state_clock t /\ clos_state_ffi s = clos_state_ffi t /\
     clos_state_max_app s = clos_state_max_app t /\
     ALL2 (OPTREL (clos_knownProof_v_rel c g)) (clos_state_globals s) (clos_state_globals t) /\
     fmap_rel (clos_knownProof_ref_rel c g) (clos_state_refs s) (clos_state_refs t) /\
     clos_state_compile s = state_cc (clos_known_compile_inc c) (clos_state_compile t) /\
     clos_state_compile_oracle t =
       state_co (clos_known_compile_inc c) (clos_state_compile_oracle s)`;;

(* HOL4: compile_inc_upd_inline_factor [local] *)
let compile_inc_upd_inline_factor = prove
 (`!c k. clos_known_compile_inc (clos_known_config_inline_factor_fupd (combin_K k) c) =
         (clos_known_compile_inc c:val_approx spt -> clos_exp list # A ->
                                   val_approx spt # clos_exp list # A)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; clos_known_compile_inc_def; reset_inline_factor_def;
              clos_known_config_INFO.ri_accfupds; clos_known_config_INFO.ri_fupdfupds;
              K_o_THM]);;

(* HOL4: state_rel_upd_inline_factor *)
let state_rel_upd_inline_factor = prove
 (`!c k. (clos_knownProof_state_rel (clos_known_config_inline_factor_fupd (combin_K k) c):
            val_approx spt -> (val_approx spt # C,FFI)clos_state -> (C,FFI)clos_state -> bool) =
         clos_knownProof_state_rel c`,
  REWRITE_TAC[FUN_EQ_THM; clos_knownProof_state_rel_def; compile_inc_upd_inline_factor;
              v_rel_upd_inline_factor; ref_rel_upd_inline_factor]);;

let CLOSP2AUX_exp_rel_subspt = prove
 (`!c aenv g g' e1 e2.
     clos_knownProof_exp_rel c aenv g e1 e2 /\ subspt g g' ==>
     clos_knownProof_exp_rel c aenv g' e1 e2`,
  REWRITE_TAC[clos_knownProof_exp_rel_def] THEN MESON_TAC[subspt_trans]);;

let CLOSP2AUX_f_rel_subspt = prove
 (`!c aenv g g' p1 p2.
     clos_knownProof_f_rel c aenv g p1 p2 /\ subspt g g' ==>
     clos_knownProof_f_rel c aenv g' p1 p2`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_knownProof_f_rel_def] THEN
  MESON_TAC[CLOSP2AUX_exp_rel_subspt]);;

(* HOL4: v_rel_subspt *)
let clos_knownProof_v_rel_subspt = prove
 (`!c g v1 v2 g'. clos_knownProof_v_rel c g v1 v2 /\ subspt g g' ==>
                  clos_knownProof_v_rel c g' v1 v2`,
  SUBGOAL_THEN `!c g v1 v2. clos_knownProof_v_rel c g v1 v2 ==>
                            !g'. subspt g g' ==> clos_knownProof_v_rel c g' v1 v2`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC clos_knownProof_v_rel_ind THEN
  REWRITE_TAC[clos_knownProof_v_rel_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CLOSP2AUX_SAME_EXISTS_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   CLOSP2AUX_ALL2_TRANSFER_TAC [CLOSP2AUX_f_rel_subspt] ORELSE
   (MATCH_MP_TAC CLOSP2AUX_exp_rel_subspt THEN ASM_MESON_TAC[])));;

(* HOL4: v_rel_LIST_REL_subspt *)
let v_rel_LIST_REL_subspt = prove
 (`!c g vs1 vs2. ALL2 (clos_knownProof_v_rel c g) vs1 vs2 ==>
                 !g'. subspt g g' ==> ALL2 (clos_knownProof_v_rel c g') vs1 vs2`,
  REPEAT STRIP_TAC THEN CLOSP2AUX_ALL2_TRANSFER_TAC [clos_knownProof_v_rel_subspt]);;

(* HOL4: ref_rel_subspt *)
let ref_rel_subspt = prove
 (`!c g r1 r2 g'. clos_knownProof_ref_rel c g r1 r2 /\ subspt g g' ==>
                  clos_knownProof_ref_rel c g' r1 r2`,
  REPEAT GEN_TAC THEN CASES_ON `r1:clos_v clos_ref` THEN
  REWRITE_TAC[clos_knownProof_ref_rel_simps] THEN
  MESON_TAC[v_rel_LIST_REL_subspt; clos_knownProof_v_rel_subspt]);;

(* HOL4: state_rel_subspt *)
let state_rel_subspt = prove
 (`!c g (s1:(val_approx spt # C,FFI)clos_state) (s2:(C,FFI)clos_state) g'.
     clos_knownProof_state_rel c g s1 s2 /\ subspt g g' ==>
     clos_knownProof_state_rel c g' s1 s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_knownProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [CLOSP2AUX_ALL2_TRANSFER_TAC [OPTREL_DEF; clos_knownProof_v_rel_subspt];
    UNDISCH_TAC `fmap_rel (clos_knownProof_ref_rel c g)
       (clos_state_refs (s1:(val_approx spt # C,FFI)clos_state))
       (clos_state_refs (s2:(C,FFI)clos_state))` THEN
    MATCH_MP_TAC fmap_rel_mono THEN ASM_MESON_TAC[ref_rel_subspt]]);;

(* HOL4: co_every_Fn_vs_NONE_def *)
let co_every_Fn_vs_NONE_def = cake_def
  `co_every_Fn_vs_NONE (co:num -> A # clos_exp list # (B # C # clos_exp) list) <=>
     !n exps aux. SND (co n) = (exps,aux) ==>
                  every_Fn_vs_NONE exps /\ every_Fn_vs_NONE (MAP (SND o SND) aux)`;;

(* HOL4: co_every_Fn_vs_NONE_shift_seq *)
let co_every_Fn_vs_NONE_shift_seq = prove
 (`!co:num -> A # clos_exp list # (B # C # clos_exp) list.
     co_every_Fn_vs_NONE co ==> !n. co_every_Fn_vs_NONE (shift_seq n co)`,
  REWRITE_TAC[co_every_Fn_vs_NONE_def; shift_seq_def] THEN MESON_TAC[]);;

(* HOL4: state_rel_co_elist_globals *)
let state_rel_co_elist_globals = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) n.
     clos_knownProof_state_rel c g s t /\ ssgc_free s /\
     oracle_state_sgc_free (clos_state_compile_oracle s) ==>
     SUB_BAG (clos_elist_globals (FST (SND (clos_state_compile_oracle t n))))
             (clos_elist_globals (FST (SND (clos_state_compile_oracle s n))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_knownProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SND_state_co] THEN
  MP_TAC(ISPEC `SND (clos_state_compile_oracle (s:(val_approx spt # C,FFI)clos_state) n)`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:clos_exp list`
    (X_CHOOSE_THEN `aux:(num#num#clos_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[clos_known_compile_inc_def; LET_DEF; LET_END_DEF;
                  pair_CASE_def; FST; SND] THEN
  MATCH_MP_TAC known_elglobals_dont_grow THEN
  MAP_EVERY EXISTS_TAC [`reset_inline_factor c`; `[]:val_approx list`;
    `FST (FST (clos_state_compile_oracle (s:(val_approx spt # C,FFI)clos_state) n))`;
    `SND (clos_known_known (reset_inline_factor c) es []
          (FST (FST (clos_state_compile_oracle (s:(val_approx spt # C,FFI)clos_state) n))))`] THEN
  REWRITE_TAC[PAIR; ALL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ssgc_free_def; oracle_state_sgc_free_def]) THEN
  ASM_MESON_TAC[]);;

(* HOL4: state_rel_first_n_exps *)
let state_rel_first_n_exps = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) n.
     clos_knownProof_state_rel c g s t /\ ssgc_free s /\
     oracle_state_sgc_free (clos_state_compile_oracle s) ==>
     SUB_BAG (clos_elist_globals (FLAT (first_n_exps (clos_state_compile_oracle t) n)))
             (clos_elist_globals (FLAT (first_n_exps (clos_state_compile_oracle s) n)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. SUB_BAG
      (clos_elist_globals (FST (SND (clos_state_compile_oracle (t:(C,FFI)clos_state) m))))
      (clos_elist_globals (FST (SND (clos_state_compile_oracle
         (s:(val_approx spt # C,FFI)clos_state) m))))` MP_TAC THENL
   [ASM_MESON_TAC[state_rel_co_elist_globals]; ALL_TAC] THEN
  REWRITE_TAC[SUB_BAG_LEQ] THEN DISCH_TAC THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[CLOSP2AUX_first_n_exps_0; CLOSP2AUX_first_n_exps_SUC; FLAT; FLAT_APPEND;
              APPEND_NIL; clos_elist_globals_append; clos_set_globals_def; BAG_UNION;
              LE_REFL] THEN
  ASM_MESON_TAC[LE_ADD2]);;

(* HOL4: state_rel_unique_set_globals *)
let state_rel_unique_set_globals = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) xs.
     clos_knownProof_state_rel c g s t /\ ssgc_free s /\
     oracle_state_sgc_free (clos_state_compile_oracle s) /\
     unique_set_globals xs (clos_state_compile_oracle s) ==>
     unique_set_globals xs (clos_state_compile_oracle t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. SUB_BAG
      (clos_elist_globals (FLAT (first_n_exps (clos_state_compile_oracle (t:(C,FFI)clos_state)) n)))
      (clos_elist_globals (FLAT (first_n_exps (clos_state_compile_oracle
         (s:(val_approx spt # C,FFI)clos_state)) n)))` MP_TAC THENL
   [ASM_MESON_TAC[state_rel_first_n_exps]; ALL_TAC] THEN
  UNDISCH_TAC `unique_set_globals xs (clos_state_compile_oracle
                 (s:(val_approx spt # C,FFI)clos_state))` THEN
  REWRITE_TAC[unique_set_globals_def; clos_elist_globals_append; BAG_ALL_DISTINCT;
              SUB_BAG_LEQ; BAG_UNION] THEN
  MESON_TAC[ARITH_RULE `a + b <= 1 /\ c <= b ==> a + c <= 1`]);;

(* HOL4: state_rel_get_global_IMP *)
let state_rel_get_global_IMP = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) n v1.
     clos_knownProof_state_rel c g s t /\ get_global n (clos_state_globals s) = SOME (SOME v1) ==>
     ?v2. get_global n (clos_state_globals t) = SOME (SOME v2) /\
          clos_knownProof_v_rel c g v1 v2`,
  REWRITE_TAC[clos_knownProof_state_rel_def; get_global_def; LIST_REL_EL_EQN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (clos_state_globals (t:(C,FFI)clos_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[injectivity "option"]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[OPTREL_SOME]);;

let CLOSP2AUX_kn_ref_rel_rsimps = prove
 (`(!c g x ys. clos_knownProof_ref_rel c g x (clos_ValueArray ys) <=>
               ?xs. x = clos_ValueArray xs /\ ALL2 (clos_knownProof_v_rel c g) xs ys) /\
   (!c g x bs. clos_knownProof_ref_rel c g x (clos_ByteArray bs) <=> x = clos_ByteArray bs) /\
   (!c g x m w. clos_knownProof_ref_rel c g x (clos_Thunk m w) <=>
                ?v. x = clos_Thunk m v /\ clos_knownProof_v_rel c g v w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_knownProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN MESON_TAC[]);;

let CLOSP2AUX_kn_simple_state_rel = prove
 (`!c g. clos_simple_state_rel (clos_knownProof_v_rel c g)
           (clos_knownProof_state_rel c g:
              (val_approx spt # C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_simple_state_rel_def] THEN
  REWRITE_TAC[clos_knownProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[fmap_rel_OPTREL_FLOOKUP]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ptr:num`) THEN ASM_REWRITE_TAC[OPTREL_NONE];
    RULE_ASSUM_TAC(REWRITE_RULE[fmap_rel_OPTREL_FLOOKUP]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ptr:num`) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_kn_ref_rel_rsimps] THEN MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[fmap_rel_OPTREL_FLOOKUP]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ptr:num`) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_kn_ref_rel_rsimps] THEN MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[fmap_rel_OPTREL_FLOOKUP]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ptr:num`) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP2AUX_kn_ref_rel_rsimps] THEN MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[fmap_rel_def]) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC fmap_rel_FUPDATE_same THEN ASM_REWRITE_TAC[clos_knownProof_ref_rel_simps];
    MATCH_MP_TAC fmap_rel_FUPDATE_same THEN ASM_REWRITE_TAC[clos_knownProof_ref_rel_simps] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC fmap_rel_FUPDATE_same THEN ASM_REWRITE_TAC[clos_knownProof_ref_rel_simps] THEN
    ASM_MESON_TAC[]]);;

(* HOL4: do_app_lemma [local] *)
let clos_knownProof_do_app_lemma = prove
 (CASE_TERM `!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) xs ys opp.
     clos_knownProof_state_rel c g s t /\ ALL2 (clos_knownProof_v_rel c g) xs ys ==>
     match clos_do_app opp xs s with
       Rerr err1 -> (?err2. clos_do_app opp ys t = Rerr err2 /\
                            exc_rel (clos_knownProof_v_rel c g) err1 err2)
     | Rval (x,s1) -> ?y t1. clos_knownProof_v_rel c g x y /\
                             clos_knownProof_state_rel c g s1 t1 /\
                             clos_do_app opp ys t = Rval (y,t1)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC simple_val_rel_do_app THEN
  REWRITE_TAC[CLOSP2AUX_kn_simple_val_rel; CLOSP2AUX_kn_simple_state_rel]);;

(* HOL4: evaluate_app_exact_rw *)
let evaluate_app_exact_rw = prove
 (`!args num_args loc env body (s:(C,FFI)clos_state).
     ~(args = []) /\ num_args = LENGTH args ==>
     evaluate_app (SOME loc) (clos_Closure (SOME loc) [] env num_args body) args s =
     if clos_state_clock s < LENGTH args
     then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (combin_K 0) s)
     else clos_evaluate ([body],APPEND args env,clos_dec_clock num_args s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN `0 < LENGTH (args:clos_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; LT_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `TAKE (LENGTH args) (REVERSE args) = REVERSE (args:clos_v list) /\
                DROP (LENGTH args) (REVERSE args) = []` STRIP_ASSUME_TAC THENL
   [MESON_TAC[LENGTH_REVERSE; TAKE_LENGTH_ID; DROP_LENGTH_NIL]; ALL_TAC] THEN
  ASM_SIMP_TAC[evaluate_app_rw] THEN
  REWRITE_TAC[dest_closure_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[check_loc_def; LENGTH; ADD_CLAUSES; LT_REFL; SUB_0; APPEND_NIL;
                  REVERSE_REVERSE; REVERSE] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH; SUB_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `clos_evaluate ([body],APPEND args env,clos_dec_clock (LENGTH args)
                                 (s:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[] THEN
  CASES_ON `r:(clos_v list,clos_v)result` THEN CAKE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:clos_v list` THEN CAKE_REWRITE_TAC[] THEN
      TRY(CASES_ON `a1:clos_v list` THEN CAKE_REWRITE_TAC[])) THEN
  REWRITE_TAC[evaluate_app_NIL]);;

(* HOL4 lines 2960-2970: v_caseT, optcaset and opt_caseT are ML values *)

(* HOL4: loptrel_arg1_SOME (derived from loptrel_def) *)
let loptrel_arg1_SOME = prove
 (`!fval numargs loc1 lopt2. loptrel fval numargs (SOME loc1) lopt2 <=> lopt2 = SOME loc1`,
  REWRITE_TAC[loptrel_def; distinctness "option"]);;

(* HOL4: loptrel_arg1_NONE (derived from loptrel_def) *)
let loptrel_arg1_NONE = prove
 (`!fval numargs lopt2.
     loptrel fval numargs NONE lopt2 <=>
     lopt2 = NONE \/
     ?loc2. lopt2 = SOME loc2 /\
            ((?loc1 ae e n bod. fval = clos_Closure (SOME loc1) ae e n bod /\
                                loc1 = loc2 /\ n = numargs /\ ae = []) \/
             (?loc1 ae e fns i. fval = clos_Recclosure (SOME loc1) ae e fns i /\
                                i < LENGTH fns /\ loc2 = loc1 + 2 * i /\
                                numargs = FST (EL i fns) /\ ae = []))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[loptrel_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; distinctness "clos_v";
              injectivity "clos_v"] THEN
  MESON_TAC[]);;

(* HOL4: dest_closure_SOME_IMP *)
let clos_knownProof_dest_closure_SOME_IMP = prove
 (`!max_app loc_opt f2 xs x.
     dest_closure max_app loc_opt f2 xs = SOME x ==>
     (?loc arg_env clo_env num_args e. f2 = clos_Closure loc arg_env clo_env num_args e) \/
     (?loc arg_env clo_env fns i. f2 = clos_Recclosure loc arg_env clo_env fns i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_closure_def] THEN
  CASES_ON `f2:clos_v` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "clos_v"] THEN MESON_TAC[]);;

(* HOL4: state_globals_approx_subspt *)
let state_globals_approx_subspt = prove
 (`!g0 g (s:(C,FFI)clos_state).
     subspt g0 g /\ state_globals_approx s g ==> state_globals_approx s g0`,
  REWRITE_TAC[state_globals_approx_def; subspt_def; domain_lookup] THEN MESON_TAC[]);;

(* HOL4: oracle_gapprox_disjoint_subspt *)
let oracle_gapprox_disjoint_subspt = prove
 (`!g0 g (co:num -> A # clos_exp list # B).
     subspt g0 g /\ oracle_gapprox_disjoint g co ==> oracle_gapprox_disjoint g0 co`,
  REWRITE_TAC[oracle_gapprox_disjoint_def; gapprox_disjoint_def; DISJOINT; EXTENSION;
              IN_INTER; NOT_IN_EMPTY; subspt_def] THEN MESON_TAC[]);;

(* HOL4: decide_inline_inlD_LetInline_sgc_free *)
let decide_inline_inlD_LetInline_sgc_free = prove
 (`!c a lopt n body.
     decide_inline c a lopt n = inlD_LetInline body /\ val_approx_sgc_free a ==>
     clos_set_globals body = EMPTY_BAG`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP decide_inline_LetInline_IMP_Clos_fv_max) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[val_approx_sgc_free_def]);;

(* HOL4: known_op_subspt *)
let known_op_subspt = prove
 (`!opn aargs (g0:val_approx spt) a g.
     known_op opn aargs g0 = (a,g) /\
     BAG_DISJOINT (BAG_OF_SET (domain g0)) (clos_op_gbag opn) ==>
     SUB_BAG (BAG_OF_SET (domain g)) (BAG_UNION (BAG_OF_SET (domain g0)) (clos_op_gbag opn)) /\
     subspt g0 g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP known_op_changed_globals_alt) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_known_op_g) THEN
  TRY RVEQ_TAC THEN REWRITE_TAC[subspt_refl] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_op_gbag_def; BAG_DISJOINT_BAG_IN; BAG_IN_BAG_OF_SET;
                              BAG_IN_BAG_INSERT; NOT_IN_EMPTY_BAG]) THEN
  REWRITE_TAC[subspt_lookup; lookup_insert] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[domain_lookup]);;

(* known_subspt: the subspt part by clos_known_known_ind *)
let CLOSP2AUX_ksub_P = `\c xs aenv (g0:val_approx spt).
   !eas g. clos_known_known c xs aenv g0 = (eas,g) ==> ALL clos_esgc_free xs ==>
     ALL val_approx_sgc_free aenv ==> globals_approx_sgc_free g0 ==>
     BAG_ALL_DISTINCT (BAG_UNION (BAG_OF_SET (domain g0)) (clos_elist_globals xs)) ==>
     subspt g0 g`;;

let CLOSP2AUX_ksub_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC CLOSP2AUX_ksub_P clos_known_known_ind);;

let CLOSP2AUX_ksub_nrm = [ALL; ALL_APPEND; clos_esgc_free_def; clos_set_globals_def;
  BAG_UNION_EMPTY; clos_elist_globals_append; MAP; HD; PAIR_EQ; EVERY_REPLICATE;
  val_approx_sgc_free_def; clos_gen_noinline_val_approx_sgc_free; APPEND_SING;
  CONJUNCT1 APPEND; APPEND_NIL];;

(* pointwise bag arithmetic for BAG_ALL_DISTINCT, BAG_DISJOINT and SUB_BAG *)
let CLOSP2AUX_KSUB_BAG_TAC : tactic =
  let thl = [BAG_ALL_DISTINCT; BAG_DISJOINT_BAG_IN; BAG_IN; BAG_INN; GE] in
  RULE_ASSUM_TAC(REWRITE_RULE thl) THEN REWRITE_TAC thl THEN CLOSP2AUX_SBAG_TAC;;

let CLOSP2AUX_KSUB_PROVE_TAC : tactic =
  FIRST [ASM_REWRITE_TAC CLOSP2AUX_ksub_nrm THEN NO_TAC; CLOSP2AUX_KSUB_BAG_TAC];;

let CLOSP2AUX_ksub_fwd = [known_preserves_esgc_free; known_changed_globals_alt;
  known_op_subspt; decide_inline_inlD_LetInline_sgc_free; set_globals_empty_esgc_free];;

let CLOSP2AUX_KSUB_CASE_TAC : tactic =
  CLOSP2AUX_KN_UNFOLD_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_ksub_nrm) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  CLOSP2AUX_SATP_GEN_TAC ["BAG_ALL_DISTINCT"; "BAG_DISJOINT"; "SUB_BAG"; "ALL"]
    CLOSP2AUX_KSUB_PROVE_TAC CLOSP2AUX_ksub_fwd CLOSP2AUX_ksub_nrm 4 THEN
  ASM_MESON_TAC[subspt_trans; subspt_refl];;

let CLOSP2AUX_ksub_thm =
  MP CLOSP2AUX_ksub_ind
    (end_itlist CONJ (map (fun t -> prove(t, CLOSP2AUX_KSUB_CASE_TAC))
                          (conjuncts (lhand (concl CLOSP2AUX_ksub_ind)))));;

(* HOL4: known_subspt *)
let known_subspt = prove
 (`!c xs aenv (g0:val_approx spt) eas g.
     clos_known_known c xs aenv g0 = (eas,g) /\ ALL clos_esgc_free xs /\
     ALL val_approx_sgc_free aenv /\ globals_approx_sgc_free g0 /\
     BAG_ALL_DISTINCT (BAG_UNION (BAG_OF_SET (domain g0)) (clos_elist_globals xs)) ==>
     SUB_BAG (BAG_OF_SET (domain g)) (BAG_UNION (BAG_OF_SET (domain g0)) (clos_elist_globals xs)) /\
     subspt g0 g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[known_changed_globals_alt];
    MP_TAC(SPECL [`c:clos_known_config`; `xs:clos_exp list`; `aenv:val_approx list`;
                  `g0:val_approx spt`] CLOSP2AUX_ksub_thm) THEN
    ASM_MESON_TAC[]]);;

(* HOL4: state_oracle_mglobals_disjoint_def *)
let state_oracle_mglobals_disjoint_def = cake_def
  `state_oracle_mglobals_disjoint (s:(C,FFI)clos_state) <=>
     !n. mglobals_disjoint (clos_state_globals s) (FST (SND (clos_state_compile_oracle s n)))`;;

(* HOL4: state_oracle_mglobals_disjoint_evaluate_suff *)
let state_oracle_mglobals_disjoint_evaluate_suff = prove
 (`!xs env (s0:(C,FFI)clos_state) res s.
     clos_evaluate (xs,env,s0) = (res,s) /\
     ssgc_free s0 /\ ALL clos_esgc_free xs /\ ALL vsgc_free env /\
     unique_set_globals xs (clos_state_compile_oracle s0) /\
     mglobals_disjoint (clos_state_globals s0) xs /\
     state_oracle_mglobals_disjoint s0 ==>
     state_oracle_mglobals_disjoint s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `env:clos_v list`; `s0:(C,FFI)clos_state`;
                 `res:(clos_v list,clos_v)result`; `s:(C,FFI)clos_state`]
                evaluate_changed_globals) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  REWRITE_TAC[state_oracle_mglobals_disjoint_def; mglobals_disjoint_def] THEN
  ASM_REWRITE_TAC[shift_seq_def] THEN BETA_TAC THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:num` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `BAG_ALL_DISTINCT (clos_elist_globals (APPEND xs (FLAT (first_n_exps
                  (clos_state_compile_oracle (s0:(C,FFI)clos_state)) (SUC (n + k))))))`
    MP_TAC THENL
   [ASM_MESON_TAC[unique_set_globals_def]; ALL_TAC] THEN
  REWRITE_TAC[CLOSP2AUX_first_n_exps_SUC; first_n_exps_shift_seq; FLAT_APPEND; FLAT;
              APPEND_NIL; clos_elist_globals_append; BAG_ALL_DISTINCT; BAG_UNION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
  UNDISCH_TAC `state_oracle_mglobals_disjoint (s0:(C,FFI)clos_state)` THEN
  REWRITE_TAC[state_oracle_mglobals_disjoint_def; mglobals_disjoint_def; DISJOINT; EXTENSION;
              IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPECL [`n + k:num`; `x:num`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mglobals_extend_def; SUBSET; IN_UNION]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `x IN SET_OF_BAG (clos_elist_globals (FST (SND (clos_state_compile_oracle
                 (s0:(C,FFI)clos_state) (n + k)))))` THEN
  REWRITE_TAC[IN_SET_OF_BAG; BAG_IN; BAG_INN] THEN
  ASM_CASES_TAC `x IN mapped_globals (clos_state_globals (s0:(C,FFI)clos_state))` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4: state_rel_opt_rel_refs [local] *)
let clos_knownProof_state_rel_opt_rel_refs = prove
 (`!c g (s1:(val_approx spt # C,FFI)clos_state) (s2:(C,FFI)clos_state) n r1 r2.
     (clos_knownProof_state_rel c g s1 s2 /\ FLOOKUP (clos_state_refs s1) n = r1 ==>
      ?r2. FLOOKUP (clos_state_refs s2) n = r2 /\ OPTREL (clos_knownProof_ref_rel c g) r1 r2) /\
     (clos_knownProof_state_rel c g s1 s2 /\ FLOOKUP (clos_state_refs s2) n = r2 ==>
      ?r1. FLOOKUP (clos_state_refs s1) n = r1 /\ OPTREL (clos_knownProof_ref_rel c g) r1 r2)`,
  REWRITE_TAC[clos_knownProof_state_rel_def; fmap_rel_OPTREL_FLOOKUP] THEN MESON_TAC[]);;

let CLOSP2AUX_kn_not_thunk = prove
 (`!c g (s1:(val_approx spt # C,FFI)clos_state) (s2:(C,FFI)clos_state) x y.
     clos_knownProof_state_rel c g s1 s2 /\ clos_knownProof_v_rel c g x y ==>
     (clos_dest_thunk [x] (clos_state_refs s1) = clos_NotThunk <=>
      clos_dest_thunk [y] (clos_state_refs s2) = clos_NotThunk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_knownProof_v_rel c g`;
                 `clos_knownProof_state_rel c g:
                    (val_approx spt # C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s1:(val_approx spt # C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                 `x:clos_v`; `y:clos_v`; `Evaluated`] CLOSPROPSAUX_bad_thunk_rel) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_kn_simple_val_rel; CLOSP2AUX_kn_simple_state_rel;
                  clos_bad_thunk_update_def] THEN
  MESON_TAC[]);;

let CLOSP2AUX_kn_flookup_rel = prove
 (`!c g (s1:(val_approx spt # C,FFI)clos_state) (s2:(C,FFI)clos_state) n.
     clos_knownProof_state_rel c g s1 s2 ==>
     OPTREL (clos_knownProof_ref_rel c g)
            (FLOOKUP (clos_state_refs s1) n) (FLOOKUP (clos_state_refs s2) n)`,
  REWRITE_TAC[clos_knownProof_state_rel_def; fmap_rel_OPTREL_FLOOKUP] THEN MESON_TAC[]);;

let CLOSP2AUX_kn_state_rel_refs_upd = prove
 (`!c g (s1:(val_approx spt # C,FFI)clos_state) (s2:(C,FFI)clos_state) p a b.
     clos_knownProof_state_rel c g s1 s2 /\ clos_knownProof_ref_rel c g a b ==>
     clos_knownProof_state_rel c g
       (clos_state_refs_fupd (combin_K (clos_state_refs s1 |+ (p,a))) s1)
       (clos_state_refs_fupd (combin_K (clos_state_refs s2 |+ (p,b))) s2)`,
  REWRITE_TAC[clos_knownProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[fmap_rel_FUPDATE_same]);;

(* HOL4: rel_update_thunk [local] *)
let clos_knownProof_rel_update_thunk = prove
 (`!c g (s1:(val_approx spt # C,FFI)clos_state) (s2:(C,FFI)clos_state) vs ys v ptr refs1.
     clos_knownProof_state_rel c g s1 s2 /\ ALL2 (clos_knownProof_v_rel c g) vs ys ==>
     (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 ==>
      ?refs2. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 /\
              clos_knownProof_state_rel c g (clos_state_refs_fupd (combin_K refs1) s1)
                                        (clos_state_refs_fupd (combin_K refs2) s2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(vs = [] /\ ys = []) \/
                (?x y. vs = [x] /\ ys = [y] /\ clos_knownProof_v_rel c g x y) \/
                (?x1 x2 r1 y1 y2 r2. vs = CONS x1 (CONS x2 r1) /\
                                     ys = CONS y1 (CONS y2 r2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 (clos_knownProof_v_rel c g) vs ys` THEN
    STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONS_11; NOT_CONS_NIL; UNWIND_THM1] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"];
    ALL_TAC;
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"]] THEN
  ASM_REWRITE_TAC[clos_update_thunk_def] THEN
  MP_TAC(SPECL [`c:clos_known_config`; `g:val_approx spt`;
                `s1:(val_approx spt # C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                `x:clos_v`; `y:clos_v`] CLOSP2AUX_kn_not_thunk) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `clos_dest_thunk [x] (clos_state_refs (s1:(val_approx spt # C,FFI)clos_state)) =
                 clos_NotThunk` THENL
   [SUBGOAL_THEN `clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                  clos_NotThunk` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    SUBGOAL_THEN `~(clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                    clos_NotThunk)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSSEMAUX_dest_thunk_NONE; distinctness "option"]] THEN
  REWRITE_TAC[store_thunk_def] THEN
  MP_TAC(SPECL [`c:clos_known_config`; `g:val_approx spt`;
                `s1:(val_approx spt # C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `ptr:num`]
               CLOSP2AUX_kn_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(val_approx spt # C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM; case_def "option"; distinctness "option"] THEN
  CASES_ON `a:(clos_v)clos_ref` THEN REWRITE_TAC[clos_knownProof_ref_rel_simps] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CAKE_REWRITE_TAC[distinctness "option"] THEN
  TRY(CASES_ON `a0:thunk_mode` THEN CAKE_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC CLOSP2AUX_kn_state_rel_refs_upd THEN
  ASM_REWRITE_TAC[clos_knownProof_ref_rel_simps; injectivity "clos_ref"; UNWIND_THM1]);;

(* ========================================================================= *)
(* known_correct0 (HOL4 lines 3187-4862): the statements of the induction.   *)
(* CLOSP2AUX_kc0_P and CLOSP2AUX_kc0_Q are the two conjuncts of HOL4's       *)
(* statement with the hypotheses reordered (evaluation, environment, known,  *)
(* state_rel and value relation first); CLOSP2AUX_kc0_ind is the induction   *)
(* of closProps on evaluate for them and CLOSP2AUX_kc0_cases its 15 cases:   *)
(*   0 NIL  1 CONS  2 Var  3 If  4 Let  5 Raise  6 Handle  7 Op  8 Fn        *)
(*   9 Letrec  10 App  11 Tick  12 Call  13 evaluate_app NIL                  *)
(*   14 evaluate_app CONS                                                     *)
(* FIXED: these statements do not change.                                    *)
(* ========================================================================= *)

let CLOSP2AUX_kc0_P = `\xs env1full (s0:(val_approx spt # C,FFI)clos_state).
  !res1 s env1 xenv1 env2 xenv2 (t0:(C,FFI)clos_state) c g0 g aenv eas.
      clos_evaluate (xs,env1full,s0) = (res1,s) ==>
      env1full = APPEND env1 xenv1 ==>
      clos_known_known c xs aenv g0 = (eas,g) ==>
      clos_knownProof_state_rel c (next_g s0) s0 t0 ==>
      ALL2 (clos_knownProof_v_rel c (next_g s0)) env1 env2 ==>
      every_Fn_vs_NONE xs ==>
      co_every_Fn_vs_NONE (clos_state_compile_oracle s0) ==>
      mglobals_disjoint (clos_state_globals s0) xs ==>
      oracle_gapprox_disjoint (next_g s0) (clos_state_compile_oracle s0) ==>
      state_oracle_mglobals_disjoint s0 ==>
      ALL clos_esgc_free xs ==> ssgc_free s0 ==>
      ALL vsgc_free env1full ==>
      ALL2 val_approx_val aenv env1 ==>
      oracle_state_sgc_free (clos_state_compile_oracle s0) ==>
      globals_approx_sgc_free g0 ==>
      ALL val_approx_sgc_free aenv ==>
      state_globals_approx s0 (next_g s0) ==>
      subspt g0 g ==> subspt g (next_g s0) ==>
      oracle_gapprox_subspt (clos_state_compile_oracle s0) ==>
      fv_max (LENGTH env1) xs ==>
      unique_set_globals xs (clos_state_compile_oracle s0) ==>
      is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s0) ==>
      ~(res1 = Rerr (Rabort Rtype_error)) ==>
      ?res2 t.
        clos_evaluate (MAP FST eas,APPEND env2 xenv2,t0) = (res2,t) /\
        result_rel (ALL2 (clos_knownProof_v_rel c (next_g s)))
                   (clos_knownProof_v_rel c (next_g s)) res1 res2 /\
        clos_knownProof_state_rel c (next_g s) s t /\
        state_globals_approx s (next_g s) /\
        is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s) /\
        oracle_gapprox_disjoint (next_g s) (clos_state_compile_oracle s)`;;

let CLOSP2AUX_kc0_Q = `\lopt1 f1 args1 (s0:(val_approx spt # C,FFI)clos_state).
  !res1 s lopt2 f2 args2 (t0:(C,FFI)clos_state) c argsopt.
      evaluate_app lopt1 f1 args1 s0 = (res1,s) ==>
      clos_knownProof_state_rel c (next_g s0) s0 t0 ==>
      ALL2 (clos_knownProof_v_rel c (next_g s0)) args1 args2 ==>
      v_rel_app c (next_g s0) f1 f2 argsopt ==>
      loptrel f2 (LENGTH args1) lopt1 lopt2 ==>
      oracle_gapprox_disjoint (next_g s0) (clos_state_compile_oracle s0) ==>
      state_oracle_mglobals_disjoint s0 ==>
      ssgc_free s0 ==> vsgc_free f1 ==> ALL vsgc_free args1 ==>
      oracle_state_sgc_free (clos_state_compile_oracle s0) ==>
      co_every_Fn_vs_NONE (clos_state_compile_oracle s0) ==>
      unique_set_globals [] (clos_state_compile_oracle s0) ==>
      is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s0) ==>
      state_globals_approx s0 (next_g s0) ==>
      oracle_gapprox_subspt (clos_state_compile_oracle s0) ==>
      (IS_SOME argsopt ==>
       argsopt = SOME args1 /\ ~(args1 = []) /\
       ?exp env. dest_closure (clos_state_max_app s0) lopt1 f1 args1 =
                 SOME (Full_app exp env [])) ==>
      ~(res1 = Rerr (Rabort Rtype_error)) ==>
      ?res2 t.
        evaluate_app lopt2 f2 args2 t0 = (res2,t) /\
        result_rel (ALL2 (clos_knownProof_v_rel c (next_g s)))
                   (clos_knownProof_v_rel c (next_g s)) res1 res2 /\
        clos_knownProof_state_rel c (next_g s) s t /\
        state_globals_approx s (next_g s) /\
        is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s) /\
        oracle_gapprox_disjoint (next_g s) (clos_state_compile_oracle s)`;;

let CLOSP2AUX_kc0_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [CLOSP2AUX_kc0_P; CLOSP2AUX_kc0_Q] CLOSPROPSAUX_evaluate_ind);;

let CLOSP2AUX_kc0_cases = conjuncts (lhand (concl CLOSP2AUX_kc0_ind));;

(* ------------------------------------------------------------------------- *)
(* Tactics for the cases                                                     *)
(* ------------------------------------------------------------------------- *)

(* instantiate the bound variables named in insts at any depth of ! and ==> *)
let rec CLOSP2AUX_spec_named (insts:(string*term) list) (th:thm) : thm =
  let c = concl th in
  if is_forall c then
    let v,_ = dest_forall c in
    let n,ty = dest_var v in
    (match (try Some (assoc n insts) with Failure _ -> None) with
       Some t when type_of t = ty -> CLOSP2AUX_spec_named insts (SPEC t th)
     | _ ->
       let v' = variant (thm_frees th) v in
       GEN v' (CLOSP2AUX_spec_named insts (SPEC v' th)))
  else if is_imp c then
    let a = lhand c in
    DISCH a (CLOSP2AUX_spec_named insts (UNDISCH th))
  else th;;

let CLOSP2AUX_subspt_refl1 = prove
 (`!sp:val_approx spt. subspt sp sp`,
  REWRITE_TAC[subspt_refl]);;

let CLOSP2AUX_subspt_trans1 = prove
 (`!sp1 sp2 (sp3:val_approx spt). subspt sp1 sp2 /\ subspt sp2 sp3 ==> subspt sp1 sp3`,
  REWRITE_TAC[subspt_trans]);;

(* a chain of subspt facts from a to b *)
let CLOSP2AUX_subspt_path (asms:thm list) (a:term) (b:term) : thm =
  let edges = mapfilter (fun th -> let c = concl th in
      let f,args = strip_comb c in
      if fst(dest_const f) = "subspt" && length args = 2 then (el 0 args, el 1 args, th)
      else failwith "") asms in
  let rec go seen x =
    if x = b then SPEC x CLOSP2AUX_subspt_refl1
    else
      let nexts = filter (fun (u,_,_) -> u = x) edges in
      tryfind (fun (_,v,th) -> if mem v seen then failwith "subspt_path" else
                 MATCH_MP CLOSP2AUX_subspt_trans1 (CONJ th (go (v::seen) v))) nexts in
  go [a] a;;

let CLOSP2AUX_SUBSPT_TAC : tactic = fun (asl,w as gl) ->
  let f,args = strip_comb w in
  if not (fst(dest_const f) = "subspt") then failwith "CLOSP2AUX_SUBSPT_TAC" else
  ACCEPT_TAC (CLOSP2AUX_subspt_path (map snd asl) (el 0 args) (el 1 args)) gl;;

let CLOSP2AUX_kc0_all2_cons = prove
 (`!(R:A->B->bool) h1 h2 t1 t2. R h1 h2 /\ ALL2 R t1 t2 ==> ALL2 R (CONS h1 t1) (CONS h2 t2)`,
  REWRITE_TAC[ALL2]);;

let CLOSP2AUX_kc0_all2_nil = prove
 (`!(R:A->B->bool). ALL2 R [] []`,
  REWRITE_TAC[ALL2]);;

let CLOSP2AUX_is_vrel c tm =
  try let f,args = strip_comb tm in
      fst(dest_const f) = "clos_knownProof_v_rel" && el 0 args = c
  with Failure _ -> false;;

(* |- v_rel c g h h' from a fact v_rel c g' h h' and a subspt chain g' .. g *)
let CLOSP2AUX_kc0_val (asms:thm list) (c:term) (g:term) (h:term) : thm =
  tryfind (fun th ->
    let f,args = strip_comb (concl th) in
    if fst(dest_const f) = "clos_knownProof_v_rel" && el 0 args = c && el 2 args = h then
      let g' = el 1 args in
      if g' = g then th else
      let sub = CLOSP2AUX_subspt_path asms g' g in
      MATCH_MP clos_knownProof_v_rel_subspt (CONJ th sub)
    else failwith "") asms;;

let CLOSP2AUX_v_rel_tm = `clos_knownProof_v_rel`;;

(* |- ALL2 (v_rel c g) l l' from facts *)
let rec CLOSP2AUX_kc0_env (asms:thm list) (c:term) (g:term) (l:term) : thm =
  try tryfind (fun th ->
    let f,args = strip_comb (concl th) in
    if fst(dest_const f) = "ALL2" && length args = 3 && el 1 args = l &&
       CLOSP2AUX_is_vrel c (el 0 args) then
      let g' = rand (el 0 args) in
      if g' = g then th else
      let sub = CLOSP2AUX_subspt_path asms g' g in
      MP (SPEC g (MATCH_MP v_rel_LIST_REL_subspt th)) sub
    else failwith "") asms
  with Failure _ ->
  let r = mk_comb(mk_comb(CLOSP2AUX_v_rel_tm, c), g) in
  if (try fst(dest_const(fst(strip_comb l))) = "APPEND" with Failure _ -> false) then
    MATCH_MP (ISPEC r EVERY2_APPEND_suff)
      (CONJ (CLOSP2AUX_kc0_env asms c g (lhand l)) (CLOSP2AUX_kc0_env asms c g (rand l)))
  else if is_cons l then
    let h,t = dest_cons l in
    MATCH_MP (ISPEC r CLOSP2AUX_kc0_all2_cons)
      (CONJ (CLOSP2AUX_kc0_val asms c g h) (CLOSP2AUX_kc0_env asms c g t))
  else if is_const l && fst(dest_const l) = "NIL" then ISPEC r CLOSP2AUX_kc0_all2_nil
  else failwith "CLOSP2AUX_kc0_env";;

let CLOSP2AUX_kc0_srel_basic = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state).
     clos_knownProof_state_rel c g s t ==>
     clos_state_clock t = clos_state_clock s /\
     clos_state_max_app t = clos_state_max_app s /\
     clos_state_ffi t = clos_state_ffi s /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY`,
  REWRITE_TAC[clos_knownProof_state_rel_def] THEN MESON_TAC[]);;

let CLOSP2AUX_find_code_empty = prove
 (`!p (args:clos_v list). clos_find_code p args (FEMPTY:(num,num#clos_exp)fmap) = NONE`,
  REWRITE_TAC[clos_find_code_def; FLOOKUP_EMPTY] THEN CAKE_REWRITE_TAC[]);;

let CLOSP2AUX_kc0_srel_dec_clock = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) n.
     clos_knownProof_state_rel c g s t ==>
     clos_knownProof_state_rel c g (clos_dec_clock n s) (clos_dec_clock n t)`,
  REWRITE_TAC[clos_knownProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

let CLOSP2AUX_kc0_srel_clock = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) k.
     clos_knownProof_state_rel c g s t ==>
     clos_knownProof_state_rel c g (clos_state_clock_fupd (combin_K k) s)
                                   (clos_state_clock_fupd (combin_K k) t)`,
  REWRITE_TAC[clos_knownProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

let CLOSP2AUX_next_g_upd = prove
 (`!n k (s:(val_approx spt # C,FFI)clos_state).
     next_g (clos_dec_clock n s) = next_g s /\
     next_g (clos_state_clock_fupd (combin_K k) s) = next_g s`,
  REWRITE_TAC[next_g_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds]);;

let CLOSP2AUX_somd_upd = prove
 (`!n k f (s:(C,FFI)clos_state).
     (state_oracle_mglobals_disjoint (clos_dec_clock n s) <=>
      state_oracle_mglobals_disjoint s) /\
     (state_oracle_mglobals_disjoint (clos_state_clock_fupd (combin_K k) s) <=>
      state_oracle_mglobals_disjoint s) /\
     (state_oracle_mglobals_disjoint (clos_state_refs_fupd f s) <=>
      state_oracle_mglobals_disjoint s)`,
  REWRITE_TAC[state_oracle_mglobals_disjoint_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds]);;

(* |- state_rel c g s t' for a source state s built from a related state *)
let rec CLOSP2AUX_kc0_srel (asms:thm list) (c:term) (g:term) (s:term) : thm =
  try tryfind (fun th ->
    let f,args = strip_comb (concl th) in
    if fst(dest_const f) = "clos_knownProof_state_rel" && el 0 args = c && el 2 args = s then
      let g' = el 1 args in
      if g' = g then th else
      let sub = CLOSP2AUX_subspt_path asms g' g in
      MATCH_MP state_rel_subspt (CONJ th sub)
    else failwith "") asms
  with Failure _ ->
  let f,args = strip_comb s in
  match fst(dest_const f) with
    "clos_dec_clock" ->
      SPEC (el 0 args) (MATCH_MP CLOSP2AUX_kc0_srel_dec_clock
                          (CLOSP2AUX_kc0_srel asms c g (el 1 args)))
  | "clos_state_clock_fupd" ->
      let k = rand (el 0 args) in
      SPEC k (MATCH_MP CLOSP2AUX_kc0_srel_clock (CLOSP2AUX_kc0_srel asms c g (el 1 args)))
  | _ -> failwith "CLOSP2AUX_kc0_srel";;

(* saturation for known_correct0: as CLOSP2AUX_SATP_GEN_TAC (with the same  *)
(* memos), and an antecedent ALL2 (v_rel c g) l x with x bound is resolved   *)
(* by constructing the target list from the facts                            *)
let CLOSP2AUX_KC0_SAT_TAC (shapes:string list) (prover:tactic) (thms:thm list)
    (nrm_thms:thm list) (rounds:int) : tactic =
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let nrm_conv = REWRITE_CONV nrm_thms in
  let nrm0 th = curry (CONV_RULE nrm_conv th) in
  let nthms = map nrm0 thms in
  fun g0 ->
  let nmemo = Hashtbl.create 1024 in
  let nrm th = let k = (concl th, hyp th) in
    try Hashtbl.find nmemo k with Not_found ->
    let r = nrm0 th in Hashtbl.add nmemo k r; r in
  let derived = ref ([]:term list) in
  let memo = ref ([]:(term * thm) list) in
  let provable_shape t =
    try mem (fst(dest_const(fst(strip_comb t)))) shapes
    with Failure _ -> false in
  let one_round (asl,w as g) =
    let failed = ref ([]:term list) in
    let asms = map snd asl in
    let facts = filter (fun th -> not (is_impth th) && not (is_forall (concl th))) asms in
    let facts_for = CLOSP2AUX_fact_index facts in
    let rename th =
      let vs0,_ = strip_forall (concl th) in
      let avoid = freesl (concl th :: hyp th) in
      let vs = itlist (fun v acc -> variant (acc @ avoid) v :: acc) vs0 [] in
      vs, SPECL vs th in
    let envb th =
      let vs,th0 = rename th in
      let ant = fst(dest_imp (concl th0)) in
      let f,args = strip_comb ant in
      if not (fst(dest_const f) = "ALL2") || not (length args = 3) then failwith "envb" else
      let r = el 0 args and l = el 1 args and x = el 2 args in
      if not (mem x vs) || free_in x l || exists (fun v -> free_in v l || free_in v r) vs
      then failwith "envb" else
      let rf,ra = strip_comb r in
      if not (fst(dest_const rf) = "clos_knownProof_v_rel") then failwith "envb" else
      let eth = CLOSP2AUX_kc0_env asms (el 0 ra) (el 1 ra) l in
      let th2 = INST [rand (concl eth),x] th0 in
      GENL (subtract vs [x]) (MP th2 eth) in
    let stb th =
      let vs,th0 = rename th in
      let ant = fst(dest_imp (concl th0)) in
      let f,args = strip_comb ant in
      if not (fst(dest_const f) = "clos_knownProof_state_rel") || not (length args = 4)
      then failwith "stb" else
      let x = el 3 args in
      if not (mem x vs) || exists (fun v -> exists (free_in v) [el 0 args; el 1 args; el 2 args]) vs
      then failwith "stb" else
      let sth = CLOSP2AUX_kc0_srel asms (el 0 args) (el 1 args) (el 2 args) in
      let th2 = INST [rand (concl sth),x] th0 in
      GENL (subtract vs [x]) (MP th2 sth) in
    let rec all_full depth th =
      if not (is_impth th) then [th] else if depth = 0 then [] else
      match (try Some (nrm (CLOSP2AUX_unwind th)) with Failure _ -> None) with
        Some th' -> all_full (depth-1) th'
      | None ->
      let vs,body = strip_forall (concl th) in
      let ant = fst(dest_imp body) in
      let mth = lazy (try MATCH_MP th with Failure _ -> fun _ -> failwith "MATCH_MP") in
      let rs = flat (map (fun a -> try all_full (depth-1) (nrm (Lazy.force mth a))
                                   with Failure _ -> [])
                       (facts_for (CLOSP2AUX_head_of ant))) in
      if rs <> [] then rs else
      match (try Some (nrm (envb th)) with Failure _ -> None) with
        Some th' -> all_full (depth-1) th'
      | None ->
      match (try Some (nrm (stb th)) with Failure _ -> None) with
        Some th' -> all_full (depth-1) th'
      | None ->
      if exists (fun v -> free_in v ant) vs || not (provable_shape ant) then [] else
      let r = try Some (assoc ant !memo) with Failure _ ->
                if mem ant !failed then None else
                (match (try Some (TAC_PROOF((asl,ant), prover)) with Failure _ -> None) with
                   Some ath -> (memo := (ant,ath) :: !memo; Some ath)
                 | None -> (failed := ant :: !failed; None)) in
      (match r with
         Some ath -> (try all_full (depth-1) (nrm (MATCH_MP th ath)) with Failure _ -> [])
       | None -> []) in
    let tres = flat (map (all_full 40) nthms) in
    let ares = map (fun th -> th, all_full 40 (nrm th)) (filter is_impth asms) in
    let used = map fst (filter (fun (_,r) -> r <> []) ares) in
    let results = tres @ flat (map snd ares) in
    let known_c = map concl asms in
    let rec dedup acc l = match l with
        [] -> rev acc
      | th::rest -> let c = concl th in
                    if c = `T` || mem c known_c || mem c !derived ||
                       exists (fun a -> concl a = c) acc
                    then dedup acc rest else dedup (th::acc) rest in
    let news = dedup [] results in
    derived := map concl news @ !derived;
    if news = [] then failwith "CLOSP2AUX_KC0_SAT_TAC: no new facts"
    else (MAP_EVERY (fun th -> UNDISCH_THEN (concl th) (K ALL_TAC)) used THEN
          MAP_EVERY STRIP_ASSUME_TAC news) g in
  let rec loop n g = if n = 0 then ALL_TAC g else
    (try (one_round THEN loop (n-1)) g with Failure _ -> ALL_TAC g) in
  loop rounds g0;;

let CLOSP2AUX_kc0_shift_cofn = prove
 (`!(s0:(val_approx spt # C,FFI)clos_state) (s1:(val_approx spt # C,FFI)clos_state) k.
     clos_state_compile_oracle s1 = shift_seq k (clos_state_compile_oracle s0) ==>
     co_every_Fn_vs_NONE (clos_state_compile_oracle s0) ==>
     co_every_Fn_vs_NONE (clos_state_compile_oracle s1)`,
  MESON_TAC[co_every_Fn_vs_NONE_shift_seq]);;

let CLOSP2AUX_kc0_shift_ossf = prove
 (`!(s0:(val_approx spt # C,FFI)clos_state) (s1:(val_approx spt # C,FFI)clos_state) k.
     clos_state_compile_oracle s1 = shift_seq k (clos_state_compile_oracle s0) ==>
     oracle_state_sgc_free (clos_state_compile_oracle s0) ==>
     oracle_state_sgc_free (clos_state_compile_oracle s1)`,
  MESON_TAC[oracle_state_sgc_free_shift_seq]);;

let CLOSP2AUX_kc0_shift_ogs = prove
 (`!(s0:(val_approx spt # C,FFI)clos_state) (s1:(val_approx spt # C,FFI)clos_state) k.
     clos_state_compile_oracle s1 = shift_seq k (clos_state_compile_oracle s0) ==>
     oracle_gapprox_subspt (clos_state_compile_oracle s0) ==>
     oracle_gapprox_subspt (clos_state_compile_oracle s1)`,
  MESON_TAC[oracle_gapprox_subspt_shift_seq]);;

let CLOSP2AUX_kc0_shift_next_g = prove
 (`!(s0:(val_approx spt # C,FFI)clos_state) (s1:(val_approx spt # C,FFI)clos_state) k.
     clos_state_compile_oracle s1 = shift_seq k (clos_state_compile_oracle s0) ==>
     oracle_gapprox_subspt (clos_state_compile_oracle s0) ==>
     subspt (next_g s0) (next_g s1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[next_g_def; shift_seq_def] THEN BETA_TAC THEN
  MATCH_MP_TAC oracle_gapprox_subspt_alt THEN ASM_REWRITE_TAC[ADD_CLAUSES; LE_0]);;

let CLOSP2AUX_known_cons2 = prove
 (`!c x y ys aenv (g0:val_approx spt) ea1 g1 ea2 g2.
     clos_known_known c [x] aenv g0 = (ea1,g1) ==> clos_known_known c (CONS y ys) aenv g1 = (ea2,g2) ==>
     clos_known_known c (CONS x (CONS y ys)) aenv g0 = (APPEND ea1 ea2,g2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* BAG_DISJOINT and BAG_ALL_DISTINCT goals from the unique_set_globals facts *)
let CLOSP2AUX_KC0_BAG_TAC : tactic =
  let mth = MATCH_MP unique_set_globals_IMP_es_distinct_elist_globals in
  let thl = [BAG_ALL_DISTINCT; BAG_DISJOINT_BAG_IN; BAG_IN; BAG_INN; GE; BAG_UNION;
             clos_set_globals_def; clos_elist_globals_append; BAG_UNION_EMPTY; EMPTY_BAG;
             K_THM; APPEND; MAP] in
  let rw = REWRITE_TAC thl and rwr = REWRITE_RULE thl and xg = `xg:num` in
  fun (asl,w as gl) ->
  let us' = map rwr (mapfilter (fun (_,th) -> mth th) asl) in
  (rw THEN
   (fun (asl,w as g) -> if is_forall w then X_GEN_TAC xg g else ALL_TAC g) THEN
   MAP_EVERY (fun th -> MP_TAC (try SPEC xg th with Failure _ -> th)) us' THEN
   ARITH_TAC) gl;;

let CLOSP2AUX_kc0_nrm = CLOSP2AUX_kca_nrm @
  [every_Fn_vs_NONE_def; fv_max_rw; result_rel_Rval; result_rel_Rerr1; exc_rel_raise1;
   exc_rel_type_error1; APPEND_RCANCEL; APPEND_ASSOC; LENGTH_APPEND; LENGTH_MAP;
   clos_knownProof_v_rel_Boolv; clos_knownProof_v_rel_Unit; LENGTH; ADD1;
   injectivity "error_result"; distinctness "error_result"; CLOSP2AUX_next_g_upd;
   CLOSP2AUX_somd_upd; distinctness "option"; injectivity "option";
   CLOSP2AUX_find_code_empty; EVALAUX_CONS_APPEND_RCANCEL; CONJUNCT2 APPEND];;

let CLOSP2AUX_KC0_FV_TAC : tactic = fun (asl,w as gl) ->
  let lens = mapfilter (fun (_,th) -> let l,r = dest_eq (concl th) in
      if fst(dest_const(fst(strip_comb l))) = "LENGTH" &&
         type_of (rand l) = `:clos_exp list` && type_of (rand r) = `:clos_v list`
      then GSYM th else failwith "") asl in
  (REWRITE_TAC (LENGTH_APPEND :: LENGTH_MAP :: LENGTH :: ADD1 :: lens) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ADD_AC; ADD1]) THEN REWRITE_TAC[ADD_AC] THEN
   ASM_REWRITE_TAC[] THEN NO_TAC) gl;;

let CLOSP2AUX_KC0_SIDE_TAC : tactic =
  FIRST [CLOSP2AUX_ASM_REWRITE_TAC CLOSP2AUX_kc0_nrm THEN NO_TAC; CLOSP2AUX_SUBSPT_TAC;
         CLOSP2AUX_UNIQUE_TAC; CLOSP2AUX_SBAG_PROVE_TAC; CLOSP2AUX_KC0_BAG_TAC;
         CLOSP2AUX_KC0_FV_TAC; CLOSP2AUX_KCA_SIDE_TAC];;

let CLOSP2AUX_kc0_shapes = ["unique_set_globals"; "SUB_BAG"; "ALL2"; "DISJOINT";
  "mglobals_disjoint"; "ALL"; "subspt"; "BAG_DISJOINT"; "BAG_ALL_DISTINCT"; "fv_max"; "~";
  "every_Fn_vs_NONE"];;

let CLOSP2AUX_kc0_fwd = [evaluate_changed_globals; CLOSP2AUX_kc0_shift_cofn;
  CLOSP2AUX_kc0_shift_ossf; CLOSP2AUX_kc0_shift_ogs; CLOSP2AUX_kc0_shift_next_g;
  unique_set_globals_evaluate; state_oracle_mglobals_disjoint_evaluate_suff;
  CLOSP2AUX_mgd_evaluate; known_preserves_esgc_free; subspt_known_elist_globals;
  subspt_known_op_elist_globals; CLOSP2AUX_known_cons2; known_correct_approx;
  INST_TYPE [`:val_approx spt # C`,`:C`] state_globals_approx_subspt;
  oracle_gapprox_disjoint_subspt; clos_evaluate_IMP_LENGTH];;

let CLOSP2AUX_KC0_START_TAC : tactic =
  REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(fun th -> if is_eq (concl th) then MP_TAC th
                           else STRIP_ASSUME_TAC th)) THEN
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let fv = frees w in
     let insts = mapfilter (fun n -> (n, find (fun v -> fst(dest_var v) = n) fv))
                   ["xenv1"; "xenv2"] in
     RULE_ASSUM_TAC(fun th -> try CLOSP2AUX_spec_named insts th with Failure _ -> th) g) THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN REPEAT CLOSP2AUX_GCASE_TAC THEN
  REPEAT CLOSP2AUX_GPAIR_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
  CLOSP2AUX_KN_SING_TAC;;

let CLOSP2AUX_kc0_fnrm = CLOSP2AUX_kc0_nrm @ [LIST_REL_CONS1; LIST_REL_NIL];;

(* rewrite the assumptions with the facts clos_state_code s = FEMPTY *)
let CLOSP2AUX_KC0_CODE_TAC : tactic =
  let fempty = `FEMPTY:(num,num#clos_exp)fmap` in
  fun (asl,w as g) ->
  let cf = mapfilter (fun (_,th) -> let l,r = dest_eq (concl th) in
      if fst(dest_const(fst(strip_comb l))) = "clos_state_code" &&
         r = fempty then th else failwith "") asl in
  if cf = [] then ALL_TAC g else
  (RULE_ASSUM_TAC(REWRITE_RULE (CLOSP2AUX_find_code_empty :: cf)) THEN
   MAP_EVERY ASSUME_TAC cf THEN REWRITE_TAC (CLOSP2AUX_find_code_empty :: cf)) g;;

let CLOSP2AUX_KC0_NRM1_TAC : tactic =
  CLOSP2AUX_KC0_CODE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kc0_fnrm) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) || is_exists (concl th) ||
                                    concl th = `F`
                                 then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  TRY RVEQ_TAC;;

let CLOSP2AUX_KC0_NRM_TAC : tactic =
  CLOSP2AUX_KC0_NRM1_TAC THEN CLOSP2AUX_CG_SING_TAC THEN CLOSP2AUX_KC0_NRM1_TAC;;

let CLOSP2AUX_kc0_var = prove
 (`!(R:clos_v->clos_v->bool) env1 env2 xenv1 xenv2 n.
     ALL2 R env1 env2 ==> n < LENGTH env1 ==>
     n < LENGTH (APPEND env2 xenv2) /\
     R (EL n (APPEND env1 xenv1)) (EL n (APPEND env2 xenv2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (env2:clos_v list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_APPEND1] THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN
  ASM_MESON_TAC[]);;

let CLOSP2AUX_kc0_fwd = CLOSP2AUX_kc0_fwd @ [CLOSP2AUX_kc0_var; CLOSP2AUX_kc0_srel_basic];;

(* the witnesses of ?res2 t. ... /\ (r,t') = (res2,t) /\ ... *)
let CLOSP2AUX_KC0_EX_TAC : tactic = fun (asl,w as gl) ->
  let vs,body = strip_exists w in
  if not (length vs = 2) then failwith "CLOSP2AUX_KC0_EX_TAC" else
  let rec cjs t = if is_conj t then cjs (lhand t) @ cjs (rand t) else [t] in
  let wit v = tryfind (fun t ->
      if is_eq t && rand t = v && not (free_in v (lhand t)) then lhand t
      else if is_eq t && lhand t = v && not (free_in v (rand t)) then rand t
      else failwith "") (cjs body) in
  let w1 = wit (el 0 vs) and w2 = wit (el 1 vs) in
  (EXISTS_TAC w1 THEN EXISTS_TAC w2 THEN REWRITE_TAC[]) gl;;

(* relation goals from the facts, with the subspt chains of the global      *)
(* approximations                                                            *)
let CLOSP2AUX_KC0_REL_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let f,args = strip_comb w in
  let th = match fst(dest_const f) with
      "clos_knownProof_v_rel" -> CLOSP2AUX_kc0_val asms (el 0 args) (el 1 args) (el 2 args)
    | "ALL2" ->
        let rf,ra = strip_comb (el 0 args) in
        if fst(dest_const rf) = "clos_knownProof_v_rel"
        then CLOSP2AUX_kc0_env asms (el 0 ra) (el 1 ra) (el 1 args) else failwith ""
    | "clos_knownProof_state_rel" -> CLOSP2AUX_kc0_srel asms (el 0 args) (el 1 args) (el 2 args)
    | _ -> failwith "CLOSP2AUX_KC0_REL_TAC" in
  if concl th = w then ACCEPT_TAC th gl else failwith "CLOSP2AUX_KC0_REL_TAC";;

(* unfold the target evaluation once (clos_evaluate_CONS for a list x::l    *)
(* whose tail is not a literal list)                                         *)
let CLOSP2AUX_KC0_UNFOLD_TAC : tactic = fun (asl,w as gl) ->
  let ev = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "clos_evaluate"
                               with Failure _ -> false) w in
  let xs = fst(dest_pair(rand ev)) in
  let lit l = is_cons l || l = `[]:clos_exp list` in
  if is_cons xs && not (lit (snd(dest_cons xs)))
  then ONCE_REWRITE_TAC[clos_evaluate_CONS] gl
  else ONCE_REWRITE_TAC[clos_evaluate_def] gl;;

let CLOSP2AUX_KC0_FIN_TAC : tactic =
  REWRITE_TAC CLOSP2AUX_kc0_nrm THEN
  CLOSP2AUX_KC0_UNFOLD_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC CLOSP2AUX_kc0_nrm THEN CAKE_REWRITE_TAC[])) THEN
  TRY CLOSP2AUX_KC0_EX_TAC THEN
  ASM_REWRITE_TAC (result_rel_def :: ALL2 :: UNWIND_THM1 :: UNWIND_THM2 :: CLOSP2AUX_kc0_nrm) THEN
  REPEAT CONJ_TAC THEN TRY CLOSP2AUX_KC0_REL_TAC;;

let CLOSP2AUX_KC0_CASE_TAC : tactic =
  CLOSP2AUX_KC0_START_TAC THEN CLOSP2AUX_KCA_EVAL_TAC THEN
  CLOSP2AUX_KC0_NRM_TAC THEN CLOSP2AUX_KC0_NRM_TAC THEN
  CLOSP2AUX_KC0_SAT_TAC CLOSP2AUX_kc0_shapes CLOSP2AUX_KC0_SIDE_TAC CLOSP2AUX_kc0_fwd
    CLOSP2AUX_kc0_nrm 4 THEN
  CLOSP2AUX_KC0_NRM_TAC THEN
  CLOSP2AUX_KC0_SAT_TAC CLOSP2AUX_kc0_shapes CLOSP2AUX_KC0_SIDE_TAC CLOSP2AUX_kc0_fwd
    CLOSP2AUX_kc0_nrm 4 THEN
  CLOSP2AUX_KC0_NRM_TAC THEN
  CLOSP2AUX_KC0_FIN_TAC;;

(* ========================================================================= *)
(* known_correct0: the cases NIL, CONS, Var, If, Let, Raise, Handle, Tick,   *)
(* Call and appNIL                                                           *)
(* ========================================================================= *)

(* case 0: NIL (HOL4 lines 3249-3253) *)
let CLOSP2AUX_kc0_NIL = prove
 (el 0 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 1: CONS (HOL4 lines 3254-3305) *)
let CLOSP2AUX_kc0_CONS = prove
 (el 1 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 2: Var (HOL4 lines 3306-3311) *)
let CLOSP2AUX_kc0_Var = prove
 (el 2 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 3: If (HOL4 lines 3312-3376) *)
let CLOSP2AUX_kc0_If = prove
 (el 3 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 4: Let (HOL4 lines 3377-3426) *)
let CLOSP2AUX_kc0_Let = prove
 (el 4 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 5: Raise (HOL4 lines 3427-3437) *)
let CLOSP2AUX_kc0_Raise = prove
 (el 5 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 6: Handle (HOL4 lines 3438-3483) *)
let CLOSP2AUX_kc0_Handle = prove
 (el 6 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 11: Tick (HOL4 lines 4382-4397) *)
let CLOSP2AUX_kc0_Tick = prove
 (el 11 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 12: Call (HOL4 lines 4398-4408) *)
let CLOSP2AUX_kc0_Call = prove
 (el 12 CLOSP2AUX_kc0_cases,
  CLOSP2AUX_KC0_CASE_TAC);;

(* case 13: appNIL (HOL4 lines 4409-4411) *)
let CLOSP2AUX_kc0_appNIL = prove
 (el 13 CLOSP2AUX_kc0_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_app_NIL; PAIR_EQ; LIST_REL_NIL; LENGTH] THEN
  REWRITE_TAC[TAUT `(p ==> a /\ F /\ b) <=> ~p`] THEN
  REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `argsopt:(clos_v list)option = NONE` SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    STRUCT_CASES_TAC(ISPEC `argsopt:(clos_v list)option` (cases "option")) THEN
    REWRITE_TAC[IS_SOME_DEF; distinctness "option"] THEN MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_app_NONE]) THEN
  REWRITE_TAC[evaluate_app_NIL; PAIR_EQ; result_rel_def; ALL2] THEN
  MAP_EVERY EXISTS_TAC [`Rval [f2]:(clos_v list,clos_v)result`; `t0:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[result_rel_def; ALL2]);;

(* ========================================================================= *)
(* known_correct0, case 7: Op (HOL4 clos_knownProofScript.sml lines          *)
(* 3484-3966).  Structure as in HOL4: the arguments raise an error           *)
(* (KNOWNC1AUX_op_err), or they give values and the operation is Install     *)
(* (KNOWNC1AUX_op_install), ForceThunk (KNOWNC1AUX_op_force), a global that  *)
(* known replaced by a constant (KNOWNC1AUX_op_global) or another primitive  *)
(* (KNOWNC1AUX_op_other).                                                    *)
(* ========================================================================= *)

(* shared helpers of the cases Op, Fn and Letrec (the same block is in each *)
(* of the three case files: keep one copy when they are pasted together)     *)
(* HOL4: c with inline_factor := c.inline_factor = c (config_component_equality) *)
let KNOWNC1AUX_config_fupd_id = prove
 (`!c. clos_known_config_inline_factor_fupd (combin_K (clos_known_config_inline_factor c)) c = c`,
  REWRITE_TAC[clos_known_config_INFO.ri_component_equality;
              clos_known_config_INFO.ri_accfupds; K_THM]);;

(* move the assumption clos_evaluate (...) = ... to the goal *)
let KNOWNC1AUX_ASM_EVAL_TAC : tactic =
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "clos_evaluate"
       with Failure _ -> false) then MP_TAC th else NO_TAC);;

(* the witnesses of ?res2 t. ... /\ (r,t') = (res2,t) /\ ..., read off the  *)
(* equations of the goal (pairs split first)                                *)
let KNOWNC1AUX_EX_TAC : tactic = REWRITE_TAC[PAIR_EQ] THEN fun (asl,w as gl) ->
  let vs,body = strip_exists w in
  let rec cjs t = if is_conj t then cjs (lhand t) @ cjs (rand t) else [t] in
  let wit v = tryfind (fun t ->
      if is_eq t && rand t = v && not (free_in v (lhand t)) then lhand t
      else if is_eq t && lhand t = v && not (free_in v (rand t)) then rand t
      else failwith "") (cjs body) in
  (MAP_EVERY (fun v -> EXISTS_TAC (wit v)) vs THEN REWRITE_TAC[]) gl;;

(* rewrite the assumptions that are not universally quantified, then split *)
(* their conjunctions                                                       *)
let KNOWNC1AUX_NRM_TAC (thl:thm list) : tactic =
  RULE_ASSUM_TAC(fun th -> if is_forall (concl th) then th else REWRITE_RULE thl th) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC));;
(* end of the shared helpers *)

(* selectors of assumptions: the evaluation of the source Op, a fact      *)
(* c args, an equation with a variable on the left, an equation whose left *)
(* side is c args (containing tm)                                           *)
let KNOWNC1AUX_is_res1 th = is_eq (concl th) &&
  rhs (concl th) = `res1:(clos_v list,clos_v)result,s':(val_approx spt # C,FFI)clos_state`;;

let KNOWNC1AUX_is_app name th =
  try fst(dest_const(fst(strip_comb(concl th)))) = name with Failure _ -> false;;

let KNOWNC1AUX_var_eq name th = is_eq (concl th) && is_var (lhs (concl th)) &&
  fst(dest_var(lhs(concl th))) = name;;

let KNOWNC1AUX_lhs_const name th = is_eq (concl th) &&
  (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = name with Failure _ -> false);;

let KNOWNC1AUX_lhs_has name tm th =
  KNOWNC1AUX_lhs_const name th && can (find_term ((=) tm)) (lhs (concl th));;

(* move the assumption clos_evaluate (es,...) = ... with p es to the goal *)
let KNOWNC1AUX_UNDISCH_EVAL_TAC (p:term -> bool) : tactic =
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
      (try let f,args = strip_comb(lhs(concl th)) in
           fst(dest_const f) = "clos_evaluate" && p (hd (snd (strip_comb (hd args))))
       with Failure _ -> false) then MP_TAC th else NO_TAC);;

(* discharge the antecedents of an instance of an induction hypothesis *)
let KNOWNC1AUX_ANTS_TAC (side:tactic) : tactic =
  REPEAT (ANTS_TAC THENL [side; ALL_TAC]);;

let KNOWNC1AUX_ASM_SIDE_TAC : tactic =
  FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[ALL_APPEND] THEN NO_TAC);;
(* the conclusion of the induction for xs env s (beta-reduced P of the frame) *)
let KNOWNC1AUX_P (xs:term) (env:term) (s:term) : term =
  rhs(concl(DEPTH_CONV BETA_CONV (list_mk_comb(CLOSP2AUX_kc0_P, [xs; env; s]))));;

let KNOWNC1AUX_isGlobal_eq = prove
 (`!op. isGlobal op <=> ?n. op = GlobOp (clos_Global n)`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN
  REWRITE_TAC[isGlobal_def; distinctness "clos_op"; injectivity "clos_op"] THEN
  CASES_ON `a:glob_op` THEN
  REWRITE_TAC[isGlobal_def; distinctness "glob_op"; injectivity "glob_op"] THEN
  MESON_TAC[]);;

(* known_op of an op whose compiled form is a constant (HOL4: the case      *)
(* isGlobal opn /\ gO_destApx apx <> gO_None)                                *)
let KNOWNC1AUX_known_op_global = prove
 (`!op as (g1:val_approx spt) apx g.
     known_op op as g1 = (apx,g) /\ isGlobal op /\ ~(gO_destApx apx = gO_None) ==>
     as = [] /\ g = g1 /\ ?n. op = GlobOp (clos_Global n) /\ lookup n g1 = SOME apx`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KNOWNC1AUX_isGlobal_eq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
  ASM_REWRITE_TAC[known_op_def] THEN
  CASES_ON `as:val_approx list` THEN REWRITE_TAC[NULL; NOT_CONS_NIL] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
   [CASES_ON `lookup n (g1:val_approx spt)` THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gO_destApx_def]) THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gO_destApx_def]) THEN ASM_MESON_TAC[]]);;

(* the compiled form of Op when it is not a constant *)
let KNOWNC1AUX_op_part = prove
 (CASE_TERM `!x op apx.
     ~(isGlobal op /\ ~(gO_destApx apx = gO_None)) ==>
     (if isGlobal op then
        (match gO_destApx apx with
           gO_Int i -> clos_Op x (IntOp (clos_Const i))
         | gO_NullTuple tag -> clos_Op x (BlockOp (clos_Cons tag))
         | gO_None -> clos_op_SmartOp x op)
      else clos_op_SmartOp x op) = clos_op_SmartOp x op`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;
(* the arguments of Op raise an error *)
let KNOWNC1AUX_op_err = prove
 (CASE_TERM `!x op apx (ea1:(clos_exp#val_approx)list) (g1:val_approx spt) g env
              (t0:(C,FFI)clos_state) e2 t1.
     known_op op (REVERSE (MAP SND ea1)) g1 = (apx,g) /\
     clos_evaluate (MAP FST ea1,env,t0) = (Rerr e2,t1) /\ ~(e2 = Rabort Rtype_error) ==>
     clos_evaluate ([(if isGlobal op then
        (match gO_destApx apx with
           gO_Int i -> clos_Op x (IntOp (clos_Const i))
         | gO_NullTuple tag -> clos_Op x (BlockOp (clos_Cons tag))
         | gO_None -> clos_op_SmartOp x op)
      else clos_op_SmartOp x op) (MAP FST ea1)],env,t0) = (Rerr e2,t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `isGlobal op /\ ~(gO_destApx apx = gO_None)` THENL
   [MP_TAC(ISPECL [`op:clos_op`; `REVERSE (MAP SND (ea1:(clos_exp#val_approx)list))`;
                   `g1:val_approx spt`; `apx:val_approx`; `g:val_approx spt`]
                  KNOWNC1AUX_known_op_global) THEN
    ASM_REWRITE_TAC[REVERSE_EQ_EMPTY; MAP_EQ_NIL] THEN STRIP_TAC THEN
    UNDISCH_TAC `clos_evaluate (MAP FST (ea1:(clos_exp#val_approx)list),env,
                                t0:(C,FFI)clos_state) = (Rerr e2,t1)` THEN
    ASM_REWRITE_TAC[MAP; clos_evaluate_def; PAIR_EQ; distinctness "result"];
    ASM_SIMP_TAC[KNOWNC1AUX_op_part] THEN MATCH_MP_TAC clos_opProof_SmartOp_thm THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[injectivity "result"; distinctness "result"]]);;
let KNOWNC1AUX_do_app_consts = prove
 (`!i tag n (t:(C,FFI)clos_state).
     clos_do_app (IntOp (clos_Const i)) [] t = Rval (clos_Number i,t) /\
     clos_do_app (BlockOp (clos_Cons tag)) [] t = Rval (clos_Block tag [],t) /\
     (!err. clos_do_app (GlobOp (clos_Global n)) [] t = Rerr err ==> err = Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSPROPSAUX_do_app_IntOp] THEN
  REWRITE_TAC[clos_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  MESON_TAC[]);;
let KNOWNC1AUX_op_const_eval = prove
 (`!x i tag env (t0:(C,FFI)clos_state).
     clos_evaluate ([clos_Op x (IntOp (clos_Const i)) []],env,t0) =
       (Rval [clos_Number i],t0) /\
     clos_evaluate ([clos_Op x (BlockOp (clos_Cons tag)) []],env,t0) =
       (Rval [clos_Block tag []],t0)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[clos_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; distinctness "clos_op"; KNOWNC1AUX_do_app_consts] THEN
  CAKE_REWRITE_TAC[]);;

(* the result of Op ... is the constant that known found for a global       *)
(* (HOL4: the case isGlobal opn /\ gO_destApx apx <> gO_None)                *)
let KNOWNC1AUX_op_global = prove
 (CASE_TERM `!x op apx xs (ea1:(clos_exp#val_approx)list) (g1:val_approx spt) g c aenv g0
      env env2 (s:(val_approx spt # C,FFI)clos_state) (t0:(C,FFI)clos_state) res1 s' vs s1.
   clos_known_known c xs aenv g0 = (ea1,g1) /\
   known_op op (REVERSE (MAP SND ea1)) g1 = (apx,g) /\ isGlobal op /\
   ~(gO_destApx apx = gO_None) /\
   clos_evaluate (xs,env,s) = (Rval vs,s1) /\
   (match clos_do_app op (REVERSE vs) s1 with
      Rval (v,s2) -> (Rval [v],s2)
    | Rerr err -> (Rerr err,s1)) = (res1,s') /\
   ~(res1 = Rerr (Rabort Rtype_error)) /\
   clos_knownProof_state_rel c (next_g s) s t0 /\ state_globals_approx s (next_g s) /\
   subspt g1 (next_g s) /\
   is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s) /\
   oracle_gapprox_disjoint (next_g s) (clos_state_compile_oracle s) ==>
   ?res2 t.
     clos_evaluate ([(if isGlobal op then
        (match gO_destApx apx with
           gO_Int i -> clos_Op x (IntOp (clos_Const i))
         | gO_NullTuple tag -> clos_Op x (BlockOp (clos_Cons tag))
         | gO_None -> clos_op_SmartOp x op)
      else clos_op_SmartOp x op) (MAP FST ea1)],env2,t0) = (res2,t) /\
     result_rel (ALL2 (clos_knownProof_v_rel c (next_g s')))
       (clos_knownProof_v_rel c (next_g s')) res1 res2 /\
     clos_knownProof_state_rel c (next_g s') s' t /\ state_globals_approx s' (next_g s') /\
     is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s') /\
     oracle_gapprox_disjoint (next_g s') (clos_state_compile_oracle s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`op:clos_op`; `REVERSE (MAP SND (ea1:(clos_exp#val_approx)list))`;
                 `g1:val_approx spt`; `apx:val_approx`; `g:val_approx spt`]
                KNOWNC1AUX_known_op_global) THEN
  ASM_REWRITE_TAC[REVERSE_EQ_EMPTY; MAP_EQ_NIL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `xs:clos_exp list = []` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP known_LENGTH_EQ_E) THEN
    REWRITE_TAC[LENGTH; GSYM LENGTH_EQ_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "clos_evaluate"
     with Failure _ -> false))) THEN
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ; injectivity "result"] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE]) THEN
  REWRITE_TAC[MAP; isGlobal_def] THEN
  (* the global read by the source program *)
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(ISPECL [`&0:int`; `0`; `n:num`;
    `s:(val_approx spt # C,FFI)clos_state`] KNOWNC1AUX_do_app_consts))) THEN
  MP_TAC(ISPECL [`n:num`; `s:(val_approx spt # C,FFI)clos_state`] CLOSP2AUX_do_app_Global0) THEN
  SPEC_TAC(`clos_do_app (GlobOp (clos_Global n)) [] (s:(val_approx spt # C,FFI)clos_state)`,
           `rr:(clos_v # (val_approx spt # C,FFI)clos_state, clos_v)result`) THEN
  GEN_TAC THEN CASES_ON `rr:(clos_v # (val_approx spt # C,FFI)clos_state, clos_v)result` THEN
  CAKE_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]] THEN
  SPEC_TAC(`a:clos_v # (val_approx spt # C,FFI)clos_state`,
           `a:clos_v # (val_approx spt # C,FFI)clos_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:clos_v`; `s2:(val_approx spt # C,FFI)clos_state`] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:clos_v`; `s2:(val_approx spt # C,FFI)clos_state`]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && fst(dest_var(lhs(concl th))) = "s2")) THEN
  SUBGOAL_THEN `val_approx_val apx (v:clos_v)` MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[state_globals_approx_def; subspt_lookup]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the constant of the compiled program *)
  UNDISCH_TAC `~(gO_destApx apx = gO_None)` THEN
  CASES_ON `apx:val_approx` THEN REWRITE_TAC[gO_destApx_def] THEN
  TRY (COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "globalOpt"] THEN
  REWRITE_TAC[val_approx_val_simps] THENL
   [DISCH_THEN(X_CHOOSE_THEN `vs:clos_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (KNOWNC1AUX_is_app "NULL")) THEN
    REWRITE_TAC[NULL_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[LIST_REL_NIL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[KNOWNC1AUX_op_const_eval] THEN
    KNOWNC1AUX_EX_TAC THEN ASM_REWRITE_TAC[result_rel_def; ALL2; clos_knownProof_v_rel_def] THEN
    REWRITE_TAC[injectivity "clos_v"; UNWIND_THM1; ALL2];
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[KNOWNC1AUX_op_const_eval] THEN
    KNOWNC1AUX_EX_TAC THEN ASM_REWRITE_TAC[result_rel_def; ALL2; clos_knownProof_v_rel_def]]);;
let KNOWNC1AUX_known_op_SetGlobal = prove
 (`!n a l (g1:val_approx spt) apx g.
     known_op (GlobOp (SetGlobal n)) (CONS a l) g1 = (apx,g) ==> ?b. lookup n g = SOME b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[known_op_def] THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `lookup n (g1:val_approx spt)` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[lookup_insert] THEN MESON_TAC[]);;

(* the global approximations after a primitive operation (HOL4: the end of  *)
(* the Op case, with known_op_correct_approx and do_app_ssgc)                *)
let KNOWNC1AUX_sga_do_app = prove
 (`!op (ea1:(clos_exp#val_approx)list) (g1:val_approx spt) apx g vs
     (s1:(val_approx spt # C,FFI)clos_state) v s2 gg.
     known_op op (REVERSE (MAP SND ea1)) g1 = (apx,g) /\
     clos_do_app op (REVERSE vs) s1 = Rval (v,s2) /\
     ALL2 val_approx_val (MAP SND ea1) vs /\ state_globals_approx s1 g1 /\
     state_globals_approx s1 gg /\ subspt g gg ==>
     state_globals_approx s2 gg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`op:clos_op`; `REVERSE (MAP SND (ea1:(clos_exp#val_approx)list))`;
    `g1:val_approx spt`; `apx:val_approx`; `g:val_approx spt`; `REVERSE vs:clos_v list`;
    `s1:(val_approx spt # C,FFI)clos_state`; `v:clos_v`;
    `s2:(val_approx spt # C,FFI)clos_state`] known_op_correct_approx) THEN
  ASM_REWRITE_TAC[LIST_REL_REVERSE_EQ] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`op:clos_op`; `REVERSE vs:clos_v list`;
    `s1:(val_approx spt # C,FFI)clos_state`; `v:clos_v`;
    `s2:(val_approx spt # C,FFI)clos_state`] CLOSP2AUX_do_app_mglobals) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `?n. op = GlobOp (SetGlobal n)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`n:num`; `REVERSE vs:clos_v list`;
      `s1:(val_approx spt # C,FFI)clos_state`; `v:clos_v`;
      `s2:(val_approx spt # C,FFI)clos_state`] CLOSP2AUX_do_app_SetGlobal) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:clos_v` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `LENGTH (REVERSE (MAP SND (ea1:(clos_exp#val_approx)list))) = 1`
      ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_REVERSE] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP LIST_REL_LENGTH) THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:clos_v list->num` o
        check (fun th -> is_eq (concl th) && is_cons (rhs (concl th)))) THEN
      REWRITE_TAC[LENGTH_REVERSE; LENGTH; ONE];
      ALL_TAC] THEN
    SUBGOAL_THEN `?b. lookup n (g:val_approx spt) = SOME b` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `REVERSE (MAP SND (ea1:(clos_exp#val_approx)list))` list_CASES) THEN
      DISCH_THEN(DISJ_CASES_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH]) THEN
          FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `0 = 1`)) THEN ARITH_TAC)
        (X_CHOOSE_THEN `h:val_approx` (X_CHOOSE_THEN `tl:val_approx list` ASSUME_TAC))) THEN
      MATCH_MP_TAC KNOWNC1AUX_known_op_SetGlobal THEN
      MAP_EVERY EXISTS_TAC [`h:val_approx`; `tl:val_approx list`; `g1:val_approx spt`;
                            `apx:val_approx`] THEN
      FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "known_op"
         with Failure _ -> false) then MP_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mglobals_extend_def; clos_op_gbag_def; SET_OF_BAG_INSERT;
                                BAG_OF_EMPTY; IN_INSERT; NOT_IN_EMPTY]) THEN
    UNDISCH_TAC `state_globals_approx (s2:(val_approx spt # C,FFI)clos_state)
                   (g:val_approx spt)` THEN
    UNDISCH_TAC `state_globals_approx (s1:(val_approx spt # C,FFI)clos_state)
                   (gg:val_approx spt)` THEN
    UNDISCH_TAC `subspt (g:val_approx spt) gg` THEN
    REWRITE_TAC[state_globals_approx_def; subspt_lookup] THEN
    REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `k:num = n` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `a = b:val_approx` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `g:val_approx spt`)) (concl th) &&
        not (can (find_term ((=) `gg:val_approx spt`)) (concl th)))) THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `clos_state_globals (s1:(val_approx spt # C,FFI)clos_state)`))
          (concl th) &&
        can (find_term ((=) `gg:val_approx spt`)) (concl th))) THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC CLOSP2AUX_sga_mglobals THEN
    EXISTS_TAC `s1:(val_approx spt # C,FFI)clos_state` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SET_OF_BAG (clos_op_gbag op) = {}` (fun th -> ASM_MESON_TAC[th]) THEN
    UNDISCH_TAC `~(?n. op = GlobOp (SetGlobal n))` THEN
    CASES_ON `op:clos_op` THEN REWRITE_TAC[clos_op_gbag_def; BAG_OF_EMPTY] THEN
    CASES_ON `a:glob_op` THEN REWRITE_TAC[clos_op_gbag_def; BAG_OF_EMPTY] THEN
    MESON_TAC[]]);;
(* the compiled primitive operation of Op (HOL4: the last case, with        *)
(* SmartOp_thm and do_app_lemma)                                             *)
let KNOWNC1AUX_op_other = prove
 (CASE_TERM `!x op apx (ea1:(clos_exp#val_approx)list) (g1:val_approx spt) g c env2
      (s1:(val_approx spt # C,FFI)clos_state) (t0:(C,FFI)clos_state) t1 res1 s' vs vs2.
   ~(op = clos_Install) /\ ~(op = clos_ThunkOp ForceThunk) /\
   known_op op (REVERSE (MAP SND ea1)) g1 = (apx,g) /\
   (match clos_do_app op (REVERSE vs) s1 with
      Rval (v,s2) -> (Rval [v],s2)
    | Rerr err -> (Rerr err,s1)) = (res1,s') /\
   ~(res1 = Rerr (Rabort Rtype_error)) /\
   clos_evaluate (MAP FST ea1,env2,t0) = (Rval vs2,t1) /\
   ALL2 (clos_knownProof_v_rel c (next_g s1)) vs vs2 /\
   clos_knownProof_state_rel c (next_g s1) s1 t1 /\
   state_globals_approx s1 (next_g s1) /\
   is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s1) /\
   oracle_gapprox_disjoint (next_g s1) (clos_state_compile_oracle s1) /\
   ALL2 val_approx_val (MAP SND ea1) vs /\ state_globals_approx s1 g1 /\
   subspt g (next_g s1) ==>
   ?res2 t.
     clos_evaluate ([clos_op_SmartOp x op (MAP FST ea1)],env2,t0) = (res2,t) /\
     result_rel (ALL2 (clos_knownProof_v_rel c (next_g s')))
       (clos_knownProof_v_rel c (next_g s')) res1 res2 /\
     clos_knownProof_state_rel c (next_g s') s' t /\ state_globals_approx s' (next_g s') /\
     is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s') /\
     oracle_gapprox_disjoint (next_g s') (clos_state_compile_oracle s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
    `s1:(val_approx spt # C,FFI)clos_state`; `t1:(C,FFI)clos_state`;
    `REVERSE vs:clos_v list`; `REVERSE vs2:clos_v list`; `op:clos_op`]
    clos_knownProof_do_app_lemma) THEN
  ASM_REWRITE_TAC[LIST_REL_REVERSE_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  MP_TAC(ISPECL [`op:clos_op`; `REVERSE vs:clos_v list`;
    `s1:(val_approx spt # C,FFI)clos_state`] CLOSP2AUX_do_app_mglobals) THEN
  MP_TAC(ISPECL [`op:clos_op`; `ea1:(clos_exp#val_approx)list`; `g1:val_approx spt`;
    `apx:val_approx`; `g:val_approx spt`; `vs:clos_v list`;
    `s1:(val_approx spt # C,FFI)clos_state`] KNOWNC1AUX_sga_do_app) THEN
  SPEC_TAC(`clos_do_app op (REVERSE vs) (s1:(val_approx spt # C,FFI)clos_state)`,
           `rr:(clos_v # (val_approx spt # C,FFI)clos_state, clos_v)result`) THEN
  GEN_TAC THEN CASES_ON `rr:(clos_v # (val_approx spt # C,FFI)clos_state, clos_v)result` THEN
  CAKE_REWRITE_TAC[] THENL
   [SPEC_TAC(`a:clos_v # (val_approx spt # C,FFI)clos_state`,
             `a:clos_v # (val_approx spt # C,FFI)clos_state`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`v:clos_v`; `s2:(val_approx spt # C,FFI)clos_state`] THEN
    DISCH_THEN(MP_TAC o SPECL [`v:clos_v`; `s2:(val_approx spt # C,FFI)clos_state`;
                               `next_g (s1:(val_approx spt # C,FFI)clos_state)`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`v:clos_v`; `s2:(val_approx spt # C,FFI)clos_state`]) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:clos_v` (X_CHOOSE_THEN `t2:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `next_g (s2:(val_approx spt # C,FFI)clos_state) =
                  next_g (s1:(val_approx spt # C,FFI)clos_state)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[next_g_def]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `Rval [w]:(clos_v list,clos_v)result` THEN
    EXISTS_TAC `t2:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[result_rel_def; ALL2] THEN
    MATCH_MP_TAC clos_opProof_SmartOp_thm THEN
    REWRITE_TAC[distinctness "result"] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    DISCH_THEN(X_CHOOSE_THEN `err2:(clos_v)error_result` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Rerr err2:(clos_v list,clos_v)result` THEN
    EXISTS_TAC `t1:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[result_rel_def] THEN
    MATCH_MP_TAC clos_opProof_SmartOp_thm THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
      UNDISCH_TAC `exc_rel (clos_knownProof_v_rel c
         (next_g (s1:(val_approx spt # C,FFI)clos_state))) a err2` THEN
      UNDISCH_TAC `~(Rerr a = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
      CASES_ON `a:(clos_v)error_result` THEN
      REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1; injectivity "result";
                  injectivity "error_result"] THEN
      STRIP_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result";
                      distinctness "error_result"]]]);;
(* facts about the oracle after an evaluation *)
let KNOWNC1AUX_eval_co = prove
 (`!xs env (s:(val_approx spt # C,FFI)clos_state) r s1.
     clos_evaluate (xs,env,s) = (r,s1) /\
     co_every_Fn_vs_NONE (clos_state_compile_oracle s) /\
     oracle_state_sgc_free (clos_state_compile_oracle s) /\
     oracle_gapprox_subspt (clos_state_compile_oracle s) ==>
     co_every_Fn_vs_NONE (clos_state_compile_oracle s1) /\
     oracle_state_sgc_free (clos_state_compile_oracle s1) /\
     oracle_gapprox_subspt (clos_state_compile_oracle s1) /\
     subspt (next_g s) (next_g s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o MATCH_MP evaluate_IMP_shift_seq) THEN
  ASM_SIMP_TAC[co_every_Fn_vs_NONE_shift_seq; oracle_state_sgc_free_shift_seq;
               oracle_gapprox_subspt_shift_seq] THEN
  ASM_REWRITE_TAC[next_g_def; shift_seq_def] THEN BETA_TAC THEN
  MATCH_MP_TAC oracle_gapprox_subspt_alt THEN ASM_REWRITE_TAC[ADD_CLAUSES; LE_0]);;
let KNOWNC1AUX_known_AppUnit = prove
 (`!c (g0:val_approx spt).
     clos_known_known c [clos_AppUnit (clos_Var backend_common_None 0)] [clos_known_Other] g0 =
     ([clos_AppUnit (clos_Var backend_common_None 0),clos_known_Other],g0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_AppUnit_def] THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[known_op_def; isGlobal_def; REVERSE; MAP; SmartOp_Cons] THEN
  CAKE_REWRITE_TAC[HD] THEN
  REWRITE_TAC[any_el_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[decide_inline_def] THEN CAKE_REWRITE_TAC[MAP; FST]);;

let KNOWNC1AUX_dest_thunk_IsThunk = prove
 (`!vs (refs:(num,(clos_v)clos_ref)fmap) m v.
     clos_dest_thunk vs refs = clos_IsThunk m v <=>
     ?ptr. vs = [clos_RefPtr F ptr] /\ FLOOKUP refs ptr = SOME (clos_Thunk m v)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[clos_dest_thunk_def] THEN CAKE_REWRITE_TAC[] THEN
    CASES_ON `m:thunk_mode` THEN CAKE_REWRITE_TAC[]] THEN
  STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_dest_thunk_def] THEN CAKE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_dest_thunk_def] THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `h:clos_v` THEN REWRITE_TAC[clos_dest_thunk_def] THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (refs:(num,(clos_v)clos_ref)fmap) a1` THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `a:(clos_v)clos_ref` THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `a0':thunk_mode` THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `a1:num` THEN ASM_REWRITE_TAC[]);;
let KNOWNC1AUX_AppUnit_facts = prove
 (`!(gl:(clos_v option) list) (co:num -> A # clos_exp list # B).
     every_Fn_vs_NONE [clos_AppUnit (clos_Var backend_common_None 0)] /\
     mglobals_disjoint gl [clos_AppUnit (clos_Var backend_common_None 0)] /\
     ALL clos_esgc_free [clos_AppUnit (clos_Var backend_common_None 0)] /\
     fv_max (SUC 0) [clos_AppUnit (clos_Var backend_common_None 0)] /\
     (unique_set_globals [clos_AppUnit (clos_Var backend_common_None 0)] co <=>
      unique_set_globals [] co)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `clos_set_globals (clos_AppUnit (clos_Var backend_common_None 0)) = EMPTY_BAG`
    ASSUME_TAC THENL
   [REWRITE_TAC[clos_AppUnit_def; clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[set_globals_empty_unique_set_globals] THEN
  REWRITE_TAC[clos_AppUnit_def; every_Fn_vs_NONE_def; fv_max_rw; ALL; clos_esgc_free_def] THEN
  REWRITE_TAC[mglobals_disjoint_def; clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY;
              BAG_OF_EMPTY; DISJOINT_EMPTY] THEN ARITH_TAC);;
(* the statement of the ForceThunk case (HOL4: Cases_on `opn = ThunkOp     *)
(* ForceThunk`): the induction hypothesis for the forced thunk, then the   *)
(* facts about the evaluation of the arguments                              *)
let KNOWNC1AUX_op_force_tm =
  let s1 = `s1:(val_approx spt # C,FFI)clos_state` and v' = `v':clos_v` in
  let ih = mk_forall(v', mk_imp(
     `clos_dest_thunk vs (clos_state_refs (s1:(val_approx spt # C,FFI)clos_state)) =
      clos_IsThunk NotEvaluated v'`,
     KNOWNC1AUX_P `[clos_AppUnit (clos_Var backend_common_None 0)]` `[v':clos_v]` s1)) in
  let body = CASE_TERM
   `(match clos_dest_thunk vs (clos_state_refs (s1:(val_approx spt # C,FFI)clos_state)) with
       clos_BadRef -> (Rerr (Rabort Rtype_error),s1)
     | clos_NotThunk -> (Rerr (Rabort Rtype_error),s1)
     | clos_IsThunk Evaluated v -> (Rval [v],s1)
     | clos_IsThunk NotEvaluated f ->
         (match clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[f],s1) with
            (Rval vs2,s2) ->
              (match clos_update_thunk vs (clos_state_refs s2) vs2 with
                 NONE -> (Rerr (Rabort Rtype_error),s2)
               | SOME refs -> (Rval vs2,clos_state_refs_fupd (combin_K refs) s2))
          | (Rerr e,s2) -> (Rerr e,s2))) = (res1,s') /\
    ~(res1 = Rerr (Rabort Rtype_error)) /\
    clos_evaluate (es2,env2,t0) = (Rval vs2,t1) /\
    ALL2 (clos_knownProof_v_rel c (next_g s1)) vs vs2 /\
    clos_knownProof_state_rel c (next_g s1) s1 (t1:(C,FFI)clos_state) /\
    state_globals_approx s1 (next_g s1) /\
    is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s1) /\
    oracle_gapprox_disjoint (next_g s1) (clos_state_compile_oracle s1) /\
    co_every_Fn_vs_NONE (clos_state_compile_oracle s1) /\
    state_oracle_mglobals_disjoint s1 /\ ssgc_free s1 /\
    oracle_state_sgc_free (clos_state_compile_oracle s1) /\
    globals_approx_sgc_free g0 /\ subspt g0 (next_g s1) /\
    oracle_gapprox_subspt (clos_state_compile_oracle s1) /\
    unique_set_globals [] (clos_state_compile_oracle s1) ==>
    ?res2 t.
      clos_evaluate ([clos_op_SmartOp x (clos_ThunkOp ForceThunk) es2],env2,t0) = (res2,t) /\
      result_rel (ALL2 (clos_knownProof_v_rel c (next_g s')))
        (clos_knownProof_v_rel c (next_g s')) res1 res2 /\
      clos_knownProof_state_rel c (next_g s') s' t /\ state_globals_approx s' (next_g s') /\
      is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s') /\
      oracle_gapprox_disjoint (next_g s') (clos_state_compile_oracle s')` in
  mk_imp(ih, body);;
(* the ForceThunk case of Op (HOL4: Cases_on `opn = ThunkOp ForceThunk`) *)
let KNOWNC1AUX_op_force = prove
 (KNOWNC1AUX_op_force_tm,
  DISCH_THEN(LABEL_TAC "ihf") THEN STRIP_TAC THEN
  (* the source thunk *)
  SUBGOAL_THEN `?m v. clos_dest_thunk vs (clos_state_refs (s1:(val_approx spt # C,FFI)clos_state)) =
                      clos_IsThunk m v` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
    MP_TAC(ISPEC `clos_dest_thunk vs (clos_state_refs (s1:(val_approx spt # C,FFI)clos_state))`
                 (cases "clos_dest_thunk_ret")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[KNOWNC1AUX_dest_thunk_IsThunk]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  (* the target thunk *)
  FIRST_X_ASSUM(MP_TAC o check (KNOWNC1AUX_is_app "ALL2")) THEN
  REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL; clos_knownProof_v_rel_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:clos_v` (X_CHOOSE_THEN `l:clos_v list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
    `s1:(val_approx spt # C,FFI)clos_state`; `t1:(C,FFI)clos_state`; `ptr:num`]
    CLOSP2AUX_kn_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[OPTREL_SOME; clos_knownProof_ref_rel_simps] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v)clos_ref` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:clos_v` STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `clos_dest_thunk [clos_RefPtr F ptr] (clos_state_refs (t1:(C,FFI)clos_state)) =
                clos_IsThunk m w` ASSUME_TAC THENL
   [REWRITE_TAC[KNOWNC1AUX_dest_thunk_IsThunk] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `m:thunk_mode` THEN CAKE_REWRITE_TAC[] THENL
   [(* an evaluated thunk *)
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `Rval [w]:(clos_v list,clos_v)result` THEN EXISTS_TAC `t1:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[result_rel_def; ALL2] THEN
    MATCH_MP_TAC clos_opProof_SmartOp_thm THEN REWRITE_TAC[distinctness "result"] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "clos_op"] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a thunk that is not evaluated yet: the induction hypothesis for it *)
  MP_TAC(ISPEC `clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[v:clos_v],
                               s1:(val_approx spt # C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ra:(clos_v list,clos_v)result`
    (X_CHOOSE_TAC `sa:(val_approx spt # C,FFI)clos_state`)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "ihf" (MP_TAC o SPEC `v:clos_v`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`ra:(clos_v list,clos_v)result`; `sa:(val_approx spt # C,FFI)clos_state`;
     `[v:clos_v]`; `[]:clos_v list`; `[w:clos_v]`; `[]:clos_v list`;
     `t1:(C,FFI)clos_state`; `c:clos_known_config`; `g0:val_approx spt`; `g0:val_approx spt`;
     `[clos_known_Other]`;
     `[clos_AppUnit (clos_Var backend_common_None 0),clos_known_Other]`]) THEN
  REWRITE_TAC[KNOWNC1AUX_known_AppUnit; APPEND; ALL2; MAP; FST; LENGTH] THEN
  KNOWNC1AUX_ANTS_TAC (FIRST [FIRST_ASSUM ACCEPT_TAC;
     REWRITE_TAC[KNOWNC1AUX_AppUnit_facts; val_approx_val_simps; ALL; val_approx_sgc_free_def;
                 subspt_refl] THEN NO_TAC;
     ASM_REWRITE_TAC[KNOWNC1AUX_AppUnit_facts] THEN NO_TAC;
     REWRITE_TAC[ALL] THEN ASM_MESON_TAC[ssgc_free_def]]) THEN
  ANTS_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `tb:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  FIRST_X_ASSUM(MP_TAC o check (KNOWNC1AUX_is_app "result_rel")) THEN
  CASES_ON `ra:(clos_v list,clos_v)result` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THENL
   [(* the thunk returned values: the thunk is updated *)
    DISCH_THEN(X_CHOOSE_THEN `vs4:clos_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:clos_known_config`; `next_g (sa:(val_approx spt # C,FFI)clos_state)`;
      `sa:(val_approx spt # C,FFI)clos_state`; `tb:(C,FFI)clos_state`; `a:clos_v list`;
      `vs4:clos_v list`; `F`; `ptr:num`] clos_knownProof_rel_update_thunk) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `clos_update_thunk [clos_RefPtr F ptr]
      (clos_state_refs (sa:(val_approx spt # C,FFI)clos_state)) a` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a':(num,(clos_v)clos_ref)fmap`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `refs2:(num,(clos_v)clos_ref)fmap` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `Rval vs4:(clos_v list,clos_v)result` THEN
    EXISTS_TAC `clos_state_refs_fupd (combin_K refs2) (tb:(C,FFI)clos_state)` THEN
    ASM_REWRITE_TAC[result_rel_def; next_g_def; clos_state_INFO.ri_accfupds;
                    state_globals_approx_refsfupd] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[next_g_def]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC clos_opProof_SmartOp_thm THEN REWRITE_TAC[distinctness "result"] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "clos_op"] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    (* the thunk raised an error *)
    DISCH_THEN(X_CHOOSE_THEN `e2:(clos_v)error_result`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    SUBGOAL_THEN `~(e2 = Rabort Rtype_error:(clos_v)error_result)` ASSUME_TAC THENL
     [UNDISCH_TAC `exc_rel (clos_knownProof_v_rel c
        (next_g (sa:(val_approx spt # C,FFI)clos_state))) a e2` THEN
      UNDISCH_TAC `~(Rerr a = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
      CASES_ON `a:(clos_v)error_result` THEN
      REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1; injectivity "result";
                  injectivity "error_result"] THEN
      STRIP_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result";
                      distinctness "error_result"];
      ALL_TAC] THEN
    EXISTS_TAC `Rerr e2:(clos_v list,clos_v)result` THEN EXISTS_TAC `tb:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[result_rel_def] THEN
    MATCH_MP_TAC clos_opProof_SmartOp_thm THEN ASM_REWRITE_TAC[injectivity "result"] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "clos_op"] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]]);;
(* a successful Install of the source semantics *)
let KNOWNC1AUX_do_install_cases = prove
 (`!vs (s:(C,FFI)clos_state) res s'.
  clos_do_install vs s = (res,s') /\ ~(res = Rerr (Rabort Rtype_error)) ==>
  ?v1 v2 bytes data.
      vs = [v1; v2] /\
      clos_v_to_bytes v1 = SOME bytes /\ clos_v_to_words v2 = SOME data /\
      DISJOINT (FDOM (clos_state_code s))
        (set_of_list (MAP FST (SND (SND (clos_state_compile_oracle s 0))))) /\
      ALL_DISTINCT (MAP FST (SND (SND (clos_state_compile_oracle s 0)))) /\
      clos_state_compile s (FST (clos_state_compile_oracle s 0))
        (SND (clos_state_compile_oracle s 0)) =
        SOME (bytes,data,FST (clos_state_compile_oracle s 1)) /\
      ~(FST (SND (clos_state_compile_oracle s 0)) = []) /\
      s' = clos_state_code_fupd
             (combin_K (clos_state_code s |++ SND (SND (clos_state_compile_oracle s 0))))
             (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s)))
               (clos_state_clock_fupd (combin_K (clos_state_clock s - 1)) s)) /\
      res = (if clos_state_clock s = 0 then Rerr (Rabort Rtimeout_error)
             else Rval (FST (SND (clos_state_compile_oracle s 0))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (CLOSP2AUX_GPAIR_TAC ORELSE TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; ADD_CLAUSES]) THEN
  RULE_ASSUM_TAC BETA_RULE THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  ASM_MESON_TAC[]);;
let KNOWNC1AUX_do_install_intro = prove
 (`!v1 v2 bytes data (t:(C,FFI)clos_state).
     clos_v_to_bytes v1 = SOME bytes /\ clos_v_to_words v2 = SOME data /\
     DISJOINT (FDOM (clos_state_code t))
       (set_of_list (MAP FST (SND (SND (clos_state_compile_oracle t 0))))) /\
     ALL_DISTINCT (MAP FST (SND (SND (clos_state_compile_oracle t 0)))) /\
     clos_state_compile t (FST (clos_state_compile_oracle t 0))
       (SND (clos_state_compile_oracle t 0)) =
       SOME (bytes,data,FST (clos_state_compile_oracle t 1)) /\
     ~(FST (SND (clos_state_compile_oracle t 0)) = []) ==>
     clos_do_install [v1; v2] t =
       ((if clos_state_clock t = 0 then Rerr (Rabort Rtimeout_error)
         else Rval (FST (SND (clos_state_compile_oracle t 0)))),
        clos_state_code_fupd
          (combin_K (clos_state_code t |++ SND (SND (clos_state_compile_oracle t 0))))
          (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle t)))
            (clos_state_clock_fupd (combin_K (clos_state_clock t - 1)) t)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_state_compile_oracle (t:(C,FFI)clos_state) 0` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cfg:C` (X_CHOOSE_THEN `pr:(clos_exp)list#(num#num#clos_exp)list`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `pr:(clos_exp)list#(num#num#clos_exp)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `exps:clos_exp list` (X_CHOOSE_THEN `aux:(num#num#clos_exp)list`
    SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  REWRITE_TAC[clos_do_install_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let KNOWNC1AUX_is_co0 th = is_eq (concl th) &&
  (try rand(lhs(concl th)) = `0` &&
       fst(dest_const(fst(strip_comb(lhs(concl th))))) = "clos_state_compile_oracle"
   with Failure _ -> false);;

(* the Install of the target semantics succeeds when the source one does   *)
(* (HOL4: the part of the Install case before the clock test)               *)
let KNOWNC1AUX_install_target = prove
 (`!c (gg:val_approx spt) (s1:(val_approx spt # C,FFI)clos_state) (t1:(C,FFI)clos_state)
     bytes data.
     clos_knownProof_state_rel c gg s1 t1 /\
     is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s1) /\
     clos_state_compile s1 (FST (clos_state_compile_oracle s1 0))
       (SND (clos_state_compile_oracle s1 0)) =
       SOME (bytes,data,FST (clos_state_compile_oracle s1 1)) /\
     ~(FST (SND (clos_state_compile_oracle s1 0)) = []) ==>
     DISJOINT (FDOM (clos_state_code t1))
       (set_of_list (MAP FST (SND (SND (clos_state_compile_oracle t1 0))))) /\
     ALL_DISTINCT (MAP FST (SND (SND (clos_state_compile_oracle t1 0)))) /\
     clos_state_compile t1 (FST (clos_state_compile_oracle t1 0))
       (SND (clos_state_compile_oracle t1 0)) =
       SOME (bytes,data,FST (clos_state_compile_oracle t1 1)) /\
     ~(FST (SND (clos_state_compile_oracle t1 0)) = []) /\
     SND (SND (clos_state_compile_oracle t1 0)) = [] /\
     ?eas. clos_known_known (reset_inline_factor c) (FST (SND (clos_state_compile_oracle s1 0))) []
             (FST (FST (clos_state_compile_oracle s1 0))) =
           (eas,FST (FST (clos_state_compile_oracle s1 1))) /\
           FST (SND (clos_state_compile_oracle t1 0)) = MAP FST eas`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_knownProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o REWRITE_RULE[is_state_oracle_def] o
    check (KNOWNC1AUX_is_app "is_state_oracle")) THEN
  ASM_REWRITE_TAC[FST_state_co; SND_state_co; ONE] THEN
  MP_TAC(ISPEC `clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:val_approx spt # C`
    (X_CHOOSE_THEN `pr:(clos_exp)list#(num#num#clos_exp)list` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `cf:val_approx spt # C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `gs:val_approx spt` (X_CHOOSE_THEN `cfg:C` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `pr:(clos_exp)list#(num#num#clos_exp)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `exps:clos_exp list`
    (X_CHOOSE_THEN `aux:(num#num#clos_exp)list` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `FST (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) (SUC 0))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `g1':val_approx spt` (X_CHOOSE_THEN `cfg1:C` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `clos_known_known (reset_inline_factor c) exps [] (gs:val_approx spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `eas:(clos_exp#val_approx)list`
    (X_CHOOSE_THEN `g2:val_approx spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND; clos_known_compile_inc_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `aux:(num#num#clos_exp)list = []` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `[]:(num#num#clos_exp)list`)) (concl th))) THEN
    FIRST_ASSUM(fun th -> if KNOWNC1AUX_is_co0 th then REWRITE_TAC[th; SND] else NO_TAC);
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ONE]) THEN
  FIRST_ASSUM(fun th -> if KNOWNC1AUX_is_co0 th then
    RULE_ASSUM_TAC(fun th' -> if th' == th then th' else REWRITE_RULE[th; FST; SND] th')
    else NO_TAC) THEN
  REWRITE_TAC[FDOM_FEMPTY; DISJOINT_EMPTY; MAP; ALL_DISTINCT] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `clos_state_compile (s1:(val_approx spt # C,FFI)clos_state) (gs,cfg) (exps,[]) =
                 SOME (bytes,data,FST (clos_state_compile_oracle s1 (SUC 0)))` THEN
    ASM_REWRITE_TAC[state_cc_def; clos_known_compile_inc_def; LET_DEF; LET_END_DEF] THEN
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `clos_state_compile (t1:(C,FFI)clos_state) cfg
                    (MAP FST (eas:(clos_exp#val_approx)list),[])` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN
    MP_TAC(ISPEC `a:((8)word)list#((64)word)list#C` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `cd:((8)word)list` (X_CHOOSE_THEN `rest:((64)word)list#C`
      SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `rest:((64)word)list#C` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `dt:((64)word)list` (X_CHOOSE_THEN `cf1:C` SUBST_ALL_TAC)) THEN
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP known_LENGTH_EQ_E) THEN
  UNDISCH_TAC `~(exps:clos_exp list = [])` THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_MAP] THEN
  DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
let KNOWNC1AUX_compile_inc_aux = prove
 (`!c (g:val_approx spt) (p:clos_exp list # A).
     SND (SND (clos_known_compile_inc c g p)) = SND p`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[clos_known_compile_inc_def; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_known_known (reset_inline_factor c) p1 [] (g:val_approx spt)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[FST; SND]);;

(* the states after an Install are related (HOL4: the state_rel goals of the *)
(* Install case, with v_rel_subspt and ref_rel_subspt)                       *)
let KNOWNC1AUX_state_rel_install = prove
 (`!c (gg:val_approx spt) gg' (s1:(val_approx spt # C,FFI)clos_state) (t1:(C,FFI)clos_state).
     clos_knownProof_state_rel c gg s1 t1 /\ subspt gg gg' ==>
     clos_knownProof_state_rel c gg'
       (clos_state_code_fupd
          (combin_K (clos_state_code s1 |++ SND (SND (clos_state_compile_oracle s1 0))))
          (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s1)))
            (clos_state_clock_fupd (combin_K (clos_state_clock s1 - 1)) s1)))
       (clos_state_code_fupd
          (combin_K (clos_state_code t1 |++ SND (SND (clos_state_compile_oracle t1 0))))
          (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle t1)))
            (clos_state_clock_fupd (combin_K (clos_state_clock t1 - 1)) t1)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC state_rel_subspt THEN
  EXISTS_TAC `gg:val_approx spt` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `clos_knownProof_state_rel c (gg:val_approx spt)
    (s1:(val_approx spt # C,FFI)clos_state) (t1:(C,FFI)clos_state)` THEN
  REWRITE_TAC[clos_knownProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SND_state_co; FUPDATE_LIST_THM] THEN
  REWRITE_TAC[shift_seq_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; state_co_def] THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[KNOWNC1AUX_compile_inc_aux; FUPDATE_LIST_THM]);;
(* the source state after an Install (HOL4: the state_globals_approx,    *)
(* is_state_oracle and oracle_gapprox_disjoint goals of the Install case)   *)
let KNOWNC1AUX_install_facts = prove
 (`!c (s1:(val_approx spt # C,FFI)clos_state) eas s2.
     clos_known_known (reset_inline_factor c) (FST (SND (clos_state_compile_oracle s1 0))) []
       (next_g s1) = (eas,FST (FST (clos_state_compile_oracle s1 1))) /\
     state_globals_approx s1 (next_g s1) /\ state_oracle_mglobals_disjoint s1 /\
     is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s1) /\
     oracle_gapprox_disjoint (next_g s1) (clos_state_compile_oracle s1) /\
     unique_set_globals [] (clos_state_compile_oracle s1) /\
     oracle_gapprox_subspt (clos_state_compile_oracle s1) /\
     s2 = clos_state_code_fupd
            (combin_K (clos_state_code s1 |++ SND (SND (clos_state_compile_oracle s1 0))))
            (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s1)))
              (clos_state_clock_fupd (combin_K (clos_state_clock s1 - 1)) s1)) ==>
     clos_state_compile_oracle s2 = shift_seq 1 (clos_state_compile_oracle s1) /\
     clos_state_globals s2 = clos_state_globals s1 /\
     next_g s2 = FST (FST (clos_state_compile_oracle s1 1)) /\
     subspt (next_g s1) (next_g s2) /\
     state_globals_approx s2 (next_g s2) /\
     is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s2) /\
     oracle_gapprox_disjoint (next_g s2) (clos_state_compile_oracle s2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  SUBGOAL_THEN `!s:(val_approx spt # C,FFI)clos_state.
      next_g (clos_state_code_fupd
               (combin_K (clos_state_code s |++ SND (SND (clos_state_compile_oracle s 0))))
            (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle s)))
              (clos_state_clock_fupd (combin_K (clos_state_clock s - 1)) s))) =
      FST (FST (clos_state_compile_oracle s 1))` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[next_g_def; clos_state_INFO.ri_accfupds; K_THM; shift_seq_def] THEN
    REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[state_globals_approx_codeupd; state_globals_approx_coupd;
              state_globals_approx_clock_fupd] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `oracle_gapprox_subspt (clos_state_compile_oracle
                   (s1:(val_approx spt # C,FFI)clos_state))` THEN
    REWRITE_TAC[oracle_gapprox_subspt_def; next_g_def] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ONE];
    MATCH_MP_TAC state_globals_approx_known_mglobals_disjoint THEN
    MAP_EVERY EXISTS_TAC [`reset_inline_factor c`;
      `FST (SND (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0))`;
      `[]:val_approx list`; `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
      `eas:(clos_exp#val_approx)list`] THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[state_oracle_mglobals_disjoint_def]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC is_state_oracle_shift_imp THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC oracle_gapprox_disjoint_Install THEN
    MAP_EVERY EXISTS_TAC [`reset_inline_factor c`;
      `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
      `eas:(clos_exp#val_approx)list`] THEN
    ASM_REWRITE_TAC[]]);;
(* HOL4: LIST_REL_IMP_LAST (listTheory) *)

(* the uniqueness of the set globals after an Install *)
let KNOWNC1AUX_unique_install = prove
 (`!xs (co:num -> A # clos_exp list # B).
     unique_set_globals xs co ==> unique_set_globals (FST (SND (co 0))) (shift_seq 1 co)`,
  REWRITE_TAC[unique_set_globals_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
  REWRITE_TAC[first_n_exps_shift_seq; ONE; CLOSP2AUX_first_n_exps_SUC; CLOSP2AUX_first_n_exps_0;
              APPEND; FLAT; FLAT_APPEND; clos_elist_globals_append; BAG_ALL_DISTINCT_BAG_UNION] THEN
  REWRITE_TAC[APPEND_NIL] THEN SIMP_TAC[]);;
(* the statement of the Install case (HOL4: Cases_on `opn = Install`): the *)
(* induction hypothesis for the installed code, then the facts about the    *)
(* evaluation of the arguments                                              *)
let KNOWNC1AUX_op_install_tm =
  let es = `es:clos_exp list` and s2 = `s2:(val_approx spt # C,FFI)clos_state` in
  let ih = list_mk_forall([es; s2], mk_imp(
     `clos_do_install (REVERSE vs) (s1:(val_approx spt # C,FFI)clos_state) =
      (Rval es,s2)`,
     KNOWNC1AUX_P es `[]:clos_v list` s2)) in
  let body = CASE_TERM
   `(match clos_do_install (REVERSE vs) (s1:(val_approx spt # C,FFI)clos_state) with
       (Rval es,s2) ->
         (match clos_evaluate (es,[],s2) with
            (Rval vs,s3) -> (Rval [LAST vs],s3)
          | res -> res)
     | (Rerr err,s2) -> (Rerr err,s2)) = (res1,s') /\
    ~(res1 = Rerr (Rabort Rtype_error)) /\
    clos_evaluate (es2,env2,t0) = (Rval vs2,t1) /\
    ALL2 (clos_knownProof_v_rel c (next_g s1)) vs vs2 /\
    clos_knownProof_state_rel c (next_g s1) s1 (t1:(C,FFI)clos_state) /\
    state_globals_approx s1 (next_g s1) /\
    is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s1) /\
    oracle_gapprox_disjoint (next_g s1) (clos_state_compile_oracle s1) /\
    co_every_Fn_vs_NONE (clos_state_compile_oracle s1) /\
    state_oracle_mglobals_disjoint s1 /\ ssgc_free s1 /\
    oracle_state_sgc_free (clos_state_compile_oracle s1) /\
    oracle_gapprox_subspt (clos_state_compile_oracle s1) /\
    unique_set_globals xs (clos_state_compile_oracle s1) ==>
    ?res2 t.
      clos_evaluate ([clos_Op x clos_Install es2],env2,t0) = (res2,t) /\
      result_rel (ALL2 (clos_knownProof_v_rel c (next_g s')))
        (clos_knownProof_v_rel c (next_g s')) res1 res2 /\
      clos_knownProof_state_rel c (next_g s') s' t /\ state_globals_approx s' (next_g s') /\
      is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s') /\
      oracle_gapprox_disjoint (next_g s') (clos_state_compile_oracle s')` in
  mk_imp(ih, body);;
let KNOWNC1AUX_CO_S2_TAC : tactic =
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) =
     `clos_state_compile_oracle (s2:(val_approx spt # C,FFI)clos_state)` then REWRITE_TAC[th]
     else NO_TAC);;

(* the Install case of Op (HOL4: Cases_on `opn = Install`) *)
let KNOWNC1AUX_op_install = prove
 (KNOWNC1AUX_op_install_tm,
  DISCH_THEN(LABEL_TAC "ihi") THEN STRIP_TAC THEN
  MP_TAC(ISPEC `clos_do_install (REVERSE vs) (s1:(val_approx spt # C,FFI)clos_state)`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ri:(clos_exp list,clos_v)result`
    (X_CHOOSE_TAC `s2:(val_approx spt # C,FFI)clos_state`)) THEN
  SUBGOAL_THEN `~(ri = Rerr (Rabort Rtype_error):(clos_exp list,clos_v)result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`REVERSE vs:clos_v list`; `s1:(val_approx spt # C,FFI)clos_state`;
    `ri:(clos_exp list,clos_v)result`; `s2:(val_approx spt # C,FFI)clos_state`]
    KNOWNC1AUX_do_install_cases) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:clos_v` (X_CHOOSE_THEN `v2:clos_v`
    (X_CHOOSE_THEN `bytes:((8)word)list` (X_CHOOSE_THEN `data:((64)word)list`
      STRIP_ASSUME_TAC)))) THEN
  (* the target arguments *)
  FIRST_X_ASSUM(MP_TAC o MATCH_MP EVERY2_REVERSE o check (KNOWNC1AUX_is_app "ALL2")) THEN
  ASM_REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:clos_v` (X_CHOOSE_THEN `l1:clos_v list`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `w2:clos_v` (X_CHOOSE_THEN `l2:clos_v list` STRIP_ASSUME_TAC)))))) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
    mem (fst (dest_var (lhs (concl th)))) ["l1"; "l2"] then SUBST_ALL_TAC th else NO_TAC)) THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
    `v1:clos_v`; `w1:clos_v`] clos_knownProof_v_rel_IMP_v_to_bytes) THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
    `v2:clos_v`; `w2:clos_v`] clos_knownProof_v_rel_IMP_v_to_words) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
    `s1:(val_approx spt # C,FFI)clos_state`; `t1:(C,FFI)clos_state`;
    `bytes:((8)word)list`; `data:((64)word)list`] KNOWNC1AUX_install_target) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `eas:(clos_exp#val_approx)list` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`w1:clos_v`; `w2:clos_v`; `bytes:((8)word)list`; `data:((64)word)list`;
    `t1:(C,FFI)clos_state`] KNOWNC1AUX_do_install_intro) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `clos_state_clock (t1:(C,FFI)clos_state) =
                clos_state_clock (s1:(val_approx spt # C,FFI)clos_state)` ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_knownProof_state_rel_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `s1:(val_approx spt # C,FFI)clos_state`;
    `eas:(clos_exp#val_approx)list`; `s2:(val_approx spt # C,FFI)clos_state`]
    KNOWNC1AUX_install_facts) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[next_g_def] THEN MATCH_MP_TAC nil_unique_set_globals THEN
    EXISTS_TAC `xs:clos_exp list` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
    `next_g (s2:(val_approx spt # C,FFI)clos_state)`;
    `s1:(val_approx spt # C,FFI)clos_state`; `t1:(C,FFI)clos_state`]
    KNOWNC1AUX_state_rel_install) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
    fst(dest_var(lhs(concl th))) = "s2" then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (KNOWNC1AUX_var_eq "s2")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `clos_state_clock (t1:(C,FFI)clos_state) =
     clos_state_clock (s1:(val_approx spt # C,FFI)clos_state)`)) THEN
  ABBREV_TAC `t2 = clos_state_code_fupd (combin_K (clos_state_code (t1:(C,FFI)clos_state) |++ []))
      (clos_state_compile_oracle_fupd (combin_K (shift_seq 1 (clos_state_compile_oracle t1)))
        (clos_state_clock_fupd
           (combin_K (clos_state_clock (s1:(val_approx spt # C,FFI)clos_state) - 1)) t1))` THEN
  FIRST_X_ASSUM(MP_TAC o check (KNOWNC1AUX_lhs_const "clos_known_known")) THEN
    REWRITE_TAC[GSYM next_g_def] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq (concl th) && lhs (concl th) = `next_g (s2:(val_approx spt # C,FFI)clos_state)`
    then REWRITE_TAC[GSYM th] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  FIRST_ASSUM(fun th ->
    if KNOWNC1AUX_lhs_has "clos_do_install" `s1:(val_approx spt # C,FFI)clos_state` th
    then REWRITE_TAC[th] else NO_TAC) THEN
  CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if KNOWNC1AUX_var_eq "ri" th then REWRITE_TAC[th] else NO_TAC) THEN
  ASM_CASES_TAC `clos_state_clock (s1:(val_approx spt # C,FFI)clos_state) = 0` THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THENL
  [(* the clock ran out *)
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result` THEN
    EXISTS_TAC `t2:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[result_rel_def; exc_rel_def] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    (* the installed code is evaluated *)
    MP_TAC(ISPEC `clos_evaluate (FST (SND (clos_state_compile_oracle
     (s1:(val_approx spt # C,FFI)clos_state) 0)),[],s2:(val_approx spt # C,FFI)clos_state)`
     PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:(clos_v list,clos_v)result`
    (X_CHOOSE_TAC `s3:(val_approx spt # C,FFI)clos_state`)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "ihi" (MP_TAC o SPECL
    [`FST (SND (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0))`;
     `s2:(val_approx spt # C,FFI)clos_state`]) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(fun th -> if KNOWNC1AUX_lhs_const "clos_do_install" th &&
      can (find_term ((=) `s1:(val_approx spt # C,FFI)clos_state`)) (lhs (concl th))
      then REWRITE_TAC[th] else NO_TAC) THEN
    ASM_REWRITE_TAC[PAIR_EQ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`r3:(clos_v list,clos_v)result`; `s3:(val_approx spt # C,FFI)clos_state`;
     `[]:clos_v list`; `[]:clos_v list`; `[]:clos_v list`; `[]:clos_v list`;
     `t2:(C,FFI)clos_state`; `reset_inline_factor c`;
     `next_g (s1:(val_approx spt # C,FFI)clos_state)`;
     `next_g (s2:(val_approx spt # C,FFI)clos_state)`;
     `[]:val_approx list`; `eas:(clos_exp#val_approx)list`]) THEN
  REWRITE_TAC[APPEND; ALL2; ALL; LENGTH; MAP] THEN
  REWRITE_TAC[reset_inline_factor_def; state_rel_upd_inline_factor; v_rel_upd_inline_factor;
              compile_inc_upd_inline_factor] THEN
  REWRITE_TAC[GSYM reset_inline_factor_def] THEN
  KNOWNC1AUX_ANTS_TAC KNOWNC1AUX_ASM_SIDE_TAC THEN
    ANTS_TAC THENL
   [UNDISCH_TAC `co_every_Fn_vs_NONE
       (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state))` THEN
    REWRITE_TAC[co_every_Fn_vs_NONE_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`0`;
      `FST (SND (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0))`;
      `SND (SND (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0))`]) THEN
    REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [KNOWNC1AUX_CO_S2_TAC THEN ASM_SIMP_TAC[co_every_Fn_vs_NONE_shift_seq];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `state_oracle_mglobals_disjoint (s1:(val_approx spt # C,FFI)clos_state)` THEN
    REWRITE_TAC[state_oracle_mglobals_disjoint_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `state_oracle_mglobals_disjoint (s1:(val_approx spt # C,FFI)clos_state)` THEN
    REWRITE_TAC[state_oracle_mglobals_disjoint_def] THEN ASM_REWRITE_TAC[] THEN
    KNOWNC1AUX_CO_S2_TAC THEN REWRITE_TAC[shift_seq_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ssgc_free (s1:(val_approx spt # C,FFI)clos_state)` THEN
    REWRITE_TAC[ssgc_free_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`0`;
      `FST (SND (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0))`;
      `SND (SND (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0))`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
    ANTS_TAC THENL
   [MP_TAC(ISPECL [`REVERSE vs:clos_v list`; `s1:(val_approx spt # C,FFI)clos_state`;
      `FST (SND (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state) 0))`;
      `s2:(val_approx spt # C,FFI)clos_state`] do_install_ssgc) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(fun th -> if KNOWNC1AUX_lhs_const "clos_do_install" th &&
        can (find_term ((=) `s1:(val_approx spt # C,FFI)clos_state`)) (lhs (concl th))
        then REWRITE_TAC[th] else NO_TAC) THEN
      ASM_REWRITE_TAC[PAIR_EQ];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [KNOWNC1AUX_CO_S2_TAC THEN ASM_SIMP_TAC[oracle_state_sgc_free_shift_seq]; ALL_TAC] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `oracle_state_sgc_free (clos_state_compile_oracle
                   (s1:(val_approx spt # C,FFI)clos_state))` THEN
    REWRITE_TAC[oracle_state_sgc_free_def; next_g_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [REWRITE_TAC[subspt_refl]; ALL_TAC] THEN
  ANTS_TAC THENL
   [KNOWNC1AUX_CO_S2_TAC THEN ASM_SIMP_TAC[oracle_gapprox_subspt_shift_seq]; ALL_TAC] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `clos_knownProof_state_rel c (next_g (s1:(val_approx spt # C,FFI)clos_state))
                   s1 (t1:(C,FFI)clos_state)` THEN
    REWRITE_TAC[clos_knownProof_state_rel_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [KNOWNC1AUX_CO_S2_TAC THEN MATCH_MP_TAC KNOWNC1AUX_unique_install THEN
    EXISTS_TAC `xs:clos_exp list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `tb:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  FIRST_X_ASSUM(MP_TAC o check (KNOWNC1AUX_is_app "result_rel")) THEN
  CASES_ON `r3:(clos_v list,clos_v)result` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[result_rel_Rval; result_rel_Rerr1; PAIR_EQ] THENL
   [DISCH_THEN(X_CHOOSE_THEN `vs4:clos_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `Rval [LAST vs4]:(clos_v list,clos_v)result` THEN
    EXISTS_TAC `tb:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[result_rel_def; ALL2] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th -> if KNOWNC1AUX_lhs_has "clos_evaluate" `t2:(C,FFI)clos_state` th
                              then REWRITE_TAC[th] else NO_TAC) THEN
      CAKE_REWRITE_TAC[];
      MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP clos_evaluate_IMP_LENGTH o
        check (KNOWNC1AUX_lhs_has "clos_evaluate" `s2:(val_approx spt # C,FFI)clos_state`)) THEN
      UNDISCH_TAC `~(FST (SND (clos_state_compile_oracle
                       (s1:(val_approx spt # C,FFI)clos_state) 0)) = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `e2:(clos_v)error_result`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `Rerr e2:(clos_v list,clos_v)result` THEN EXISTS_TAC `tb:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[result_rel_def] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if KNOWNC1AUX_lhs_has "clos_evaluate" `t2:(C,FFI)clos_state` th
                            then REWRITE_TAC[th] else NO_TAC) THEN
    CAKE_REWRITE_TAC[]]]);;

(* MESON with the lemmas thl and only the assumptions whose head constant is *)
(* in heads (ASM_MESON_TAC with the 50 assumptions of the Op case: 3-5 s per *)
(* subspt chain)                                                            *)
let CLOSP2AUX_MESON_HEADS_TAC (heads:string list) (thl:thm list) : tactic =
  fun (asl,w as g) ->
  let ok th = try mem (fst(dest_const(fst(strip_comb(concl th))))) heads
              with Failure _ -> false in
  MESON_TAC (thl @ filter ok (map snd asl)) g;;

(* case 7: Op (HOL4 lines 3484-3966) *)
let CLOSP2AUX_kc0_Op = prove
 (el 7 CLOSP2AUX_kc0_cases,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih_install")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih_force") (LABEL_TAC "ih_xs"))) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_known_known c xs aenv (g0:val_approx spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ea1:(clos_exp#val_approx)list` (X_CHOOSE_TAC `g1:val_approx spt`)) THEN
  MP_TAC(ISPEC `known_op op (REVERSE (MAP SND (ea1:(clos_exp#val_approx)list)))
                  (g1:val_approx spt)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `apx:val_approx` (X_CHOOSE_TAC `g2:val_approx spt`)) THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC) THEN
  REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (el 5 (CONJUNCTS (SPEC_ALL unique_set_globals_subexps)))) THEN
  DISCH_TAC THEN
  KNOWNC1AUX_NRM_TAC [every_Fn_vs_NONE_def; fv_max_rw; mglobals_disjoint_rw;
                      clos_esgc_free_def; ALL; ALL_APPEND] THEN
  SUBGOAL_THEN `BAG_DISJOINT (clos_op_gbag op) (clos_elist_globals xs)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP unique_set_globals_IMP_es_distinct_elist_globals o
      check (fun th -> can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "clos_Op"
                                                with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY; BAG_ALL_DISTINCT_BAG_UNION] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `xs:clos_exp list`; `aenv:val_approx list`;
    `g0:val_approx spt`; `ea1:(clos_exp#val_approx)list`; `g1:val_approx spt`; `op:clos_op`;
    `REVERSE (MAP SND (ea1:(clos_exp#val_approx)list))`; `g:val_approx spt`; `apx:val_approx`]
    subspt_known_op_elist_globals) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `subspt (g1:val_approx spt) (next_g (s:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL [CLOSP2AUX_MESON_HEADS_TAC ["subspt"] [subspt_trans]; ALL_TAC] THEN
  MP_TAC(ISPEC `clos_evaluate (xs,APPEND env1 xenv1,s:(val_approx spt # C,FFI)clos_state)`
     PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_TAC `s1:(val_approx spt # C,FFI)clos_state`)) THEN
  KNOWNC1AUX_UNDISCH_EVAL_TAC (fun es -> is_cons es) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(r = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "ih_xs" (MP_TAC o SPECL
    [`r:(clos_v list,clos_v)result`; `s1:(val_approx spt # C,FFI)clos_state`;
     `env1:clos_v list`; `xenv1:clos_v list`; `env2:clos_v list`; `xenv2:clos_v list`;
     `t0:(C,FFI)clos_state`; `c:clos_known_config`; `g0:val_approx spt`; `g1:val_approx spt`;
     `aenv:val_approx list`; `ea1:(clos_exp#val_approx)list`]) THEN
  KNOWNC1AUX_ANTS_TAC KNOWNC1AUX_ASM_SIDE_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `t1:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  CASES_ON `r:(clos_v list,clos_v)result` THENL
  [(* the arguments evaluate to values *)
   RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `vs2:clos_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
    REWRITE_RULE[result_rel_Rval] o check (KNOWNC1AUX_is_app "result_rel")) THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `APPEND env1 xenv1:clos_v list`;
    `s:(val_approx spt # C,FFI)clos_state`; `Rval a:(clos_v list,clos_v)result`;
    `s1:(val_approx spt # C,FFI)clos_state`] KNOWNC1AUX_eval_co) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   SUBGOAL_THEN `subspt (g0:val_approx spt) (next_g (s:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL [CLOSP2AUX_MESON_HEADS_TAC ["subspt"] [subspt_trans]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `xs:clos_exp list`; `aenv:val_approx list`;
    `g0:val_approx spt`; `ea1:(clos_exp#val_approx)list`; `g1:val_approx spt`;
    `env1:clos_v list`; `xenv1:clos_v list`; `s:(val_approx spt # C,FFI)clos_state`;
    `Rval a:(clos_v list,clos_v)result`; `s1:(val_approx spt # C,FFI)clos_state`]
    known_correct_approx) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_APPEND] THEN
    CLOSP2AUX_MESON_HEADS_TAC ["subspt"; "state_globals_approx"; "oracle_gapprox_disjoint"]
      [state_globals_approx_subspt; oracle_gapprox_disjoint_subspt];
    REWRITE_TAC[injectivity "result"; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN STRIP_TAC] THEN
   FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[FORALL_UNWIND_THM1] o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "val_approx_val"
                             with Failure _ -> false)) (concl th) &&
    not (can (find_term (fun t -> try fst(dest_const t) = "clos_evaluate"
                                  with Failure _ -> false)) (concl th)))) THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `APPEND env1 xenv1:clos_v list`;
    `s:(val_approx spt # C,FFI)clos_state`; `Rval a:(clos_v list,clos_v)result`;
    `s1:(val_approx spt # C,FFI)clos_state`] evaluate_changed_globals) THEN
  ASM_REWRITE_TAC[ALL_APPEND; rsgc_free_def] THEN
  DISCH_THEN(fun th -> ASSUME_TAC (CONJUNCT1 th) THEN ASSUME_TAC (CONJUNCT1 (CONJUNCT2 th))) THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `APPEND env1 xenv1:clos_v list`;
    `s:(val_approx spt # C,FFI)clos_state`; `Rval a:(clos_v list,clos_v)result`;
    `s1:(val_approx spt # C,FFI)clos_state`] state_oracle_mglobals_disjoint_evaluate_suff) THEN
  ASM_REWRITE_TAC[ALL_APPEND] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `xs:clos_exp list`; `APPEND env1 xenv1:clos_v list`;
    `s:(val_approx spt # C,FFI)clos_state`; `s1:(val_approx spt # C,FFI)clos_state`;
    `Rval a:(clos_v list,clos_v)result`] unique_set_globals_evaluate) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `subspt (g0:val_approx spt) (next_g (s1:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL [CLOSP2AUX_MESON_HEADS_TAC ["subspt"] [subspt_trans]; ALL_TAC] THEN
   ASM_CASES_TAC `op = clos_Install` THENL
   [(* Install *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `op = clos_Install`)) THEN
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (KNOWNC1AUX_lhs_const "known_op")) THEN
  REWRITE_TAC[CLOSP2AUX_known_op_IF; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[MAP; CLOSP2AUX_known_op_IF; SmartOp_Install] THEN
  USE_THEN "ih_install" (fun ih -> MP_TAC (GEN `es:clos_exp list`
     (GEN `s2:(val_approx spt # C,FFI)clos_state` (SPECL [`a:clos_v list`;
       `s1:(val_approx spt # C,FFI)clos_state`; `es:clos_exp list`;
       `s2:(val_approx spt # C,FFI)clos_state`] ih)))) THEN
  REWRITE_TAC[ASSUME `clos_evaluate (xs,APPEND env1 xenv1,s:(val_approx spt # C,FFI)clos_state) =
                      Rval a,s1`] THEN
  DISCH_THEN(fun ih -> MATCH_MP_TAC (MATCH_MP (GEN_ALL KNOWNC1AUX_op_install) ih)) THEN
    MAP_EVERY EXISTS_TAC [`vs2:clos_v list`; `t1:(C,FFI)clos_state`; `xs:clos_exp list`] THEN
  ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THENL
   [(* ForceThunk *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `op = clos_ThunkOp ForceThunk`)) THEN
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  REWRITE_TAC[distinctness "clos_op"] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (KNOWNC1AUX_lhs_const "known_op")) THEN
  REWRITE_TAC[CLOSP2AUX_known_op_IF; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[MAP; CLOSP2AUX_known_op_IF] THEN
  USE_THEN "ih_force" (fun ih -> MP_TAC (GEN `v:clos_v` (SPECL [`a:clos_v list`; `v:clos_v`;
     `s1:(val_approx spt # C,FFI)clos_state`] ih))) THEN
  REWRITE_TAC[ASSUME `clos_evaluate (xs,APPEND env1 xenv1,s:(val_approx spt # C,FFI)clos_state) =
                      Rval a,s1`] THEN
  DISCH_THEN(fun ih -> MATCH_MP_TAC (MATCH_MP (GEN_ALL KNOWNC1AUX_op_force) ih)) THEN
    MAP_EVERY EXISTS_TAC [`vs2:clos_v list`; `t1:(C,FFI)clos_state`; `g0:val_approx spt`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC nil_unique_set_globals THEN
  EXISTS_TAC `xs:clos_exp list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* the other operations *)
  FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[MAP] THEN
  ASM_CASES_TAC `isGlobal op /\ ~(gO_destApx apx = gO_None)` THENL
   [MATCH_MP_TAC KNOWNC1AUX_op_global THEN
    MAP_EVERY EXISTS_TAC [`xs:clos_exp list`; `g1:val_approx spt`; `g:val_approx spt`;
      `aenv:val_approx list`; `g0:val_approx spt`; `APPEND env1 xenv1:clos_v list`;
      `s:(val_approx spt # C,FFI)clos_state`; `a:clos_v list`;
      `s1:(val_approx spt # C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[KNOWNC1AUX_op_part] THEN MATCH_MP_TAC KNOWNC1AUX_op_other THEN
    MAP_EVERY EXISTS_TAC [`apx:val_approx`; `g1:val_approx spt`; `g:val_approx spt`;
      `s1:(val_approx spt # C,FFI)clos_state`; `t1:(C,FFI)clos_state`; `a:clos_v list`;
      `vs2:clos_v list`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_MESON_HEADS_TAC ["subspt"] [subspt_trans]];
   (* the arguments raise an error *)
   FIRST_X_ASSUM(MP_TAC o check KNOWNC1AUX_is_res1) THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e2:(clos_v)error_result` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
    REWRITE_RULE[result_rel_Rerr1] o check (KNOWNC1AUX_is_app "result_rel")) THEN
  SUBGOAL_THEN `~(e2 = Rabort Rtype_error:(clos_v)error_result)` ASSUME_TAC THENL
   [UNDISCH_TAC `exc_rel (clos_knownProof_v_rel c
       (next_g (s1:(val_approx spt # C,FFI)clos_state))) a e2` THEN
    UNDISCH_TAC `~(Rerr a = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
    CASES_ON `a:(clos_v)error_result` THEN
    REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1; injectivity "result";
                injectivity "error_result"] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result";
                    distinctness "error_result"];
    ALL_TAC] THEN
  EXISTS_TAC `Rerr e2:(clos_v list,clos_v)result` THEN EXISTS_TAC `t1:(C,FFI)clos_state` THEN
  ASM_REWRITE_TAC[result_rel_def; MAP] THEN
  MATCH_MP_TAC KNOWNC1AUX_op_err THEN
  MAP_EVERY EXISTS_TAC [`g1:val_approx spt`; `g:val_approx spt`] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* known_correct0, case 8: Fn (HOL4 clos_knownProofScript.sml lines          *)
(* 3967-3985).                                                               *)
(* ========================================================================= *)

(* (the shared helpers of the cases Op, Fn and Letrec are in the Op case) *)

(* the closure made by Fn is related to the closure of its compiled form *)
let KNOWNC1AUX_fn_closure = prove
 (`!c (gg:val_approx spt) g0 g aenv env1 xenv1 env2 xenv2 loc num_args exp body a1.
     clos_known_known c [exp] (APPEND (REPLICATE num_args clos_known_Other) aenv) g0 = ([body,a1],g) /\
     subspt g gg /\ globals_approx_sgc_free g0 /\ ALL val_approx_sgc_free aenv /\
     every_Fn_vs_NONE [exp] /\ fv_max (LENGTH env1 + num_args) [exp] /\
     ALL2 (clos_knownProof_v_rel c gg) env1 env2 /\ ALL2 val_approx_val aenv env1 ==>
     clos_knownProof_v_rel c gg (clos_Closure loc [] (APPEND env1 xenv1) num_args exp)
        (clos_Closure loc [] (APPEND env2 xenv2) num_args body)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_knownProof_v_rel_def] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`aenv:val_approx list`; `env1:clos_v list`; `xenv1:clos_v list`;
    `[]:clos_v list`; `env2:clos_v list`; `xenv2:clos_v list`; `body:clos_exp`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_REWRITE_TAC[ALL2; clos_knownProof_exp_rel_def] THEN
  MAP_EVERY EXISTS_TAC [`g0:val_approx spt`; `g:val_approx spt`; `a1:val_approx`;
    `clos_known_config_inline_factor c`] THEN
  ASM_REWRITE_TAC[ALL_APPEND; EVERY_REPLICATE; val_approx_sgc_free_def;
                  KNOWNC1AUX_config_fupd_id]);;

(* case 8: Fn (HOL4 lines 3967-3985) *)
let CLOSP2AUX_kc0_Fn = prove
 (el 8 CLOSP2AUX_kc0_cases,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `exp:clos_exp`;
     `APPEND (REPLICATE num_args clos_known_Other) aenv`; `g0:val_approx spt`] known_sing) THEN
  DISCH_THEN(X_CHOOSE_THEN `body:clos_exp` (X_CHOOSE_THEN `a1:val_approx`
     (X_CHOOSE_TAC `g1:val_approx spt`))) THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[HD] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC) THEN
  REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[every_Fn_vs_NONE_def; fv_max_rw]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `IS_NONE:(num list)option->bool`)) (concl th))) THEN
  CASES_ON `vsopt:(num list)option` THEN REWRITE_TAC[IS_NONE_DEF] THEN
  REWRITE_TAC[MAP; FST] THEN KNOWNC1AUX_ASM_EVAL_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `clos_state_max_app (t0:(C,FFI)clos_state) =
                clos_state_max_app (s:(val_approx spt # C,FFI)clos_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[clos_knownProof_state_rel_def]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  KNOWNC1AUX_EX_TAC THEN ASM_REWRITE_TAC[result_rel_def; ALL2] THEN
  MATCH_MP_TAC KNOWNC1AUX_fn_closure THEN
  MAP_EVERY EXISTS_TAC [`g0:val_approx spt`; `g:val_approx spt`; `aenv:val_approx list`;
                        `a1:val_approx`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* known_correct0, case 9: Letrec (HOL4 clos_knownProofScript.sml lines      *)
(* 3986-4044).                                                               *)
(* ========================================================================= *)

(* (the shared helpers of the cases Op, Fn and Letrec are in the Op case) *)

let KNOWNC1AUX_ALL2_MAP_SELF = prove
 (`!(R:A->B->bool) (f:A->B) l. ALL2 R l (MAP f l) <=> ALL (\x. R x (f x)) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP; ALL]);;

(* the approximations of the functions of a Letrec (HOL4: the clos of     *)
(* known_def)                                                               *)
let KNOWNC1AUX_letrec_clos_tm = CASE_TERM
  `match (loc:num option) with
     NONE -> REPLICATE (LENGTH (fns:(num#clos_exp)list)) clos_known_Other
   | SOME l -> clos_gen_noinline l 0 fns`;;

let KNOWNC1AUX_letrec_clos_sgc = prove
 (CASE_TERM `!loc (fns:(num#clos_exp)list).
    ALL val_approx_sgc_free
      (match loc with NONE -> REPLICATE (LENGTH fns) clos_known_Other
                    | SOME l -> clos_gen_noinline l 0 fns)`,
  GEN_TAC THEN CASES_ON `loc:num option` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[EVERY_REPLICATE; val_approx_sgc_free_def; clos_gen_noinline_val_approx_sgc_free]);;

let KNOWNC1AUX_letrec_vav = prove
 (CASE_TERM `!loc (fns:(num#clos_exp)list) env.
    ALL2 val_approx_val
      (match loc with NONE -> REPLICATE (LENGTH fns) clos_known_Other
                    | SOME l -> clos_gen_noinline l 0 fns)
      (list_of_seq (clos_Recclosure loc [] env fns) (LENGTH fns))`,
  GEN_TAC THEN CASES_ON `loc:num option` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSP2AUX_vav_letrec_SOME] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC CLOSP2AUX_vav_letrec_NONE THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ]);;

(* the compiled functions of a Letrec are related to the source ones *)
let KNOWNC1AUX_letrec_frel = prove
 (`!c (gg:val_approx spt) g0 aenv clos fns.
     globals_approx_sgc_free g0 /\ ALL val_approx_sgc_free aenv /\
     ALL val_approx_sgc_free clos /\ subspt g0 gg /\
     clos_elist_globals (MAP SND fns) = EMPTY_BAG ==>
     ALL2 (clos_knownProof_f_rel c (APPEND clos aenv) gg) fns
       (MAP (\p. pair_CASE p (\num_args x.
               (num_args, FST (HD (FST (clos_known_known c [x]
                  (APPEND (APPEND (REPLICATE num_args clos_known_Other) clos) aenv) g0))))))
            fns)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[KNOWNC1AUX_ALL2_MAP_SELF; GSYM ALL_MEM] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`num_args:num`; `e:clos_exp`] THEN DISCH_TAC THEN
  REWRITE_TAC[clos_knownProof_f_rel_def; clos_knownProof_exp_rel_def] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `e:clos_exp`;
     `APPEND (APPEND (REPLICATE num_args clos_known_Other) clos) aenv`; `g0:val_approx spt`]
     known_sing) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':clos_exp` (X_CHOOSE_THEN `apx:val_approx`
     (X_CHOOSE_TAC `g1:val_approx spt`))) THEN
  SUBGOAL_THEN `g1:val_approx spt = g0` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC known_unchanged_globals THEN
    MAP_EVERY EXISTS_TAC [`c:clos_known_config`; `[e:clos_exp]`;
      `APPEND (APPEND (REPLICATE num_args clos_known_Other) clos) aenv`;
      `[e':clos_exp,apx:val_approx]`] THEN
    ASM_REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY] THEN
    MATCH_MP_TAC CLOSP2AUX_elist_empty_MEM THEN
    EXISTS_TAC `MAP SND (fns:(num#clos_exp)list)` THEN ASM_REWRITE_TAC[MEM_MAP] THEN
    EXISTS_TAC `num_args:num,e:clos_exp` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[HD; FST] THEN
  MAP_EVERY EXISTS_TAC [`g0:val_approx spt`; `g0:val_approx spt`; `apx:val_approx`;
    `clos_known_config_inline_factor c`] THEN
  ASM_REWRITE_TAC[KNOWNC1AUX_config_fupd_id; GSYM APPEND_ASSOC; ALL_APPEND; EVERY_REPLICATE;
                  val_approx_sgc_free_def] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC]);;

(* the recursive closures made by a Letrec are related to those of its     *)
(* compiled form                                                            *)
let KNOWNC1AUX_letrec_rcs = prove
 (CASE_TERM `!c (gg:val_approx spt) g0 aenv env1 xenv1 env2 xenv2 loc fns.
   globals_approx_sgc_free g0 /\ ALL val_approx_sgc_free aenv /\ subspt g0 gg /\
   every_Fn_vs_NONE (MAP SND fns) /\
   ALL (\p. match p with (num_args,x) -> fv_max (LENGTH env1 + num_args + LENGTH fns) [x]) fns /\
   clos_elist_globals (MAP SND fns) = EMPTY_BAG /\
   ALL2 (clos_knownProof_v_rel c gg) env1 env2 /\ ALL2 val_approx_val aenv env1 ==>
   ALL2 (clos_knownProof_v_rel c gg)
     (list_of_seq (clos_Recclosure loc [] (APPEND env1 xenv1) fns) (LENGTH fns))
     (list_of_seq (clos_Recclosure loc [] (APPEND env2 xenv2)
        (MAP (\p. match p with (num_args,x) -> (num_args, FST (HD (FST (clos_known_known c [x]
            (APPEND (APPEND (REPLICATE num_args clos_known_Other)
                     (match loc with NONE -> REPLICATE (LENGTH fns) clos_known_Other
                                   | SOME l -> clos_gen_noinline l 0 fns)) aenv) g0))))) fns))
        (LENGTH fns))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[clos_knownProof_v_rel_def] THEN CONJ_TAC THENL
   [UNDISCH_TAC `every_Fn_vs_NONE (MAP SND (fns:(num#clos_exp)list))` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [every_Fn_vs_NONE_EVERY] THEN
    REWRITE_TAC[ALL_MAP; o_DEF] THEN MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`aenv:val_approx list`; `env1:clos_v list`; `xenv1:clos_v list`;
    `[]:clos_v list`; `env2:clos_v list`; `xenv2:clos_v list`] THEN
  REWRITE_TAC[APPEND; ALL2; injectivity "clos_v"; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC (CASE_TERM `ALL (\p. match p with (num_args,x) ->
       fv_max (LENGTH (env1:clos_v list) + num_args + LENGTH (fns:(num#clos_exp)list)) [x])
       fns`) THEN
    MATCH_MP_TAC MONO_ALL THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_AC];
    ALL_TAC] THEN
  KNOWNC1AUX_EX_TAC THEN
  MATCH_MP_TAC KNOWNC1AUX_letrec_frel THEN
  ASM_REWRITE_TAC[KNOWNC1AUX_letrec_clos_sgc]);;

let KNOWNC1AUX_is_ALL tm =
  try fst(dest_const(fst(strip_comb tm))) = "ALL" with Failure _ -> false;;

(* case 9: Letrec (HOL4 lines 3986-4044) *)
let CLOSP2AUX_kc0_Letrec = prove
 (el 9 CLOSP2AUX_kc0_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `exp:clos_exp`;
     mk_binop `APPEND:val_approx list -> val_approx list -> val_approx list`
       KNOWNC1AUX_letrec_clos_tm `aenv:val_approx list`; `g0:val_approx spt`] known_sing) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:clos_exp` (X_CHOOSE_THEN `a1:val_approx`
     (X_CHOOSE_TAC `g1:val_approx spt`))) THEN
  ONCE_REWRITE_TAC[clos_known_known_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[HD] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC) THEN
  REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (el 7 (CONJUNCTS (SPEC_ALL unique_set_globals_subexps)))) THEN
  STRIP_TAC THEN
  KNOWNC1AUX_NRM_TAC [every_Fn_vs_NONE_def; fv_max_rw; mglobals_disjoint_rw;
                      clos_esgc_free_def; ALL; ALL_APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `IS_NONE:(num list)option->bool`)) (concl th))) THEN
  CASES_ON `namesopt:(num list)option` THEN REWRITE_TAC[IS_NONE_DEF] THEN
  (* the evaluation of the source Letrec *)
  KNOWNC1AUX_ASM_EVAL_TAC THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]] THEN
  DISCH_TAC THEN
  (* the induction hypothesis for the body, with the recursive closures *)
  REMOVE_THEN "ih" (MP_TAC o SPEC
    `list_of_seq (clos_Recclosure loc [] (APPEND env1 xenv1) fns)
                 (LENGTH (fns:(num#clos_exp)list))`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`res1:(clos_v list,clos_v)result`; `s':(val_approx spt # C,FFI)clos_state`;
     `APPEND (list_of_seq (clos_Recclosure loc [] (APPEND env1 xenv1) fns)
                          (LENGTH (fns:(num#clos_exp)list))) env1`;
     `xenv1:clos_v list`;
     mk_binop `APPEND:clos_v list -> clos_v list -> clos_v list`
       (subst [KNOWNC1AUX_letrec_clos_tm, `clos:val_approx list`]
         `list_of_seq (clos_Recclosure loc [] (APPEND env2 xenv2)
           (MAP (\p. pair_CASE p (\num_args x. (num_args, FST (HD (FST (clos_known_known c [x]
            (APPEND (APPEND (REPLICATE num_args clos_known_Other) clos) aenv) g0)))))) fns))
           (LENGTH (fns:(num#clos_exp)list))`) `env2:clos_v list`;
     `xenv2:clos_v list`; `t0:(C,FFI)clos_state`; `c:clos_known_config`;
     `g0:val_approx spt`; `g:val_approx spt`;
     mk_binop `APPEND:val_approx list -> val_approx list -> val_approx list`
       KNOWNC1AUX_letrec_clos_tm `aenv:val_approx list`;
     `[e1:clos_exp,a1:val_approx]`]) THEN
  ANTS_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC KNOWNC1AUX_letrec_rcs THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[subspt_trans];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_APPEND] THEN MATCH_MP_TAC CLOSP2AUX_vsgc_recc THEN
    ASM_REWRITE_TAC[ALL_APPEND];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[KNOWNC1AUX_letrec_vav]; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ALL_APPEND; KNOWNC1AUX_letrec_clos_sgc]; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* the evaluation of the compiled Letrec *)
  DISCH_TAC THEN REWRITE_TAC[MAP; FST] THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `clos_state_max_app (t0:(C,FFI)clos_state) =
                clos_state_max_app (s:(val_approx spt # C,FFI)clos_state)` SUBST1_TAC THENL
   [ASM_MESON_TAC[clos_knownProof_state_rel_def]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; GSYM APPEND_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; FST; GSYM APPEND_ASSOC]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
                                          KNOWNC1AUX_is_ALL (rand (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> KNOWNC1AUX_is_ALL (concl th) &&
     can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "clos_state_max_app"
                              with Failure _ -> false)) (concl th))) THEN
  REWRITE_TAC[ALL_MAP; o_DEF; GSYM ALL_MEM; FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* known_correct0, case 10: App (HOL4 lines 4045-4381).                      *)
(* The first part (generic helpers for the cases of known_correct0) is also  *)
(* used by the case evaluate_app CONS (case 14).                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Generic helpers: resolving induction hypotheses and lemmas with the       *)
(* assumptions (HOL4 first_x_assum drule \\ rpt (disch_then drule))          *)
(* ------------------------------------------------------------------------- *)

(* instantiate the bound variables named in insts at any depth of ! and ==> *)
let rec KNOWNC2AUX_spec_named (insts:(string*term) list) (th:thm) : thm =
  let c = concl th in
  if is_forall c then
    let v,_ = dest_forall c in
    let n,ty = dest_var v in
    (match (try Some (assoc n insts) with Failure _ -> None) with
       Some t when type_of t = ty -> KNOWNC2AUX_spec_named insts (SPEC t th)
     | _ ->
       let v' = variant (thm_frees th) v in
       GEN v' (KNOWNC2AUX_spec_named insts (SPEC v' th)))
  else if is_imp c then
    let a = lhand c in
    DISCH a (KNOWNC2AUX_spec_named insts (UNDISCH th))
  else th;;

let KNOWNC2AUX_curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th;;

(* discharge the antecedents of th in order: by MATCH_MP with the first      *)
(* assumption that matches, by REFL for an equation, else (for an           *)
(* antecedent without bound variables) by the tactic side                    *)
let rec KNOWNC2AUX_res (side:tactic) (asl:(string*thm) list) (th:thm) : thm =
  let th = KNOWNC2AUX_curry (PURE_REWRITE_RULE[HD] th) in
  let vs,body = strip_forall (concl th) in
  if not (is_imp body) then th else
  let ant = fst(dest_imp body) in
  let mth = try MATCH_MP th with Failure _ -> fun _ -> failwith "MATCH_MP" in
  match (try Some (tryfind (fun (_,a) -> mth a) asl) with Failure _ -> None) with
    Some th' -> KNOWNC2AUX_res side asl th'
  | None ->
  match (try Some (MATCH_MP th (REFL (lhand ant))) with Failure _ -> None) with
    Some th' -> KNOWNC2AUX_res side asl th'
  | None ->
    if exists (fun v -> vfree_in v ant) vs then
      failwith ("KNOWNC2AUX_res: no match: " ^ string_of_term ant) else
    let ath = try TAC_PROOF((asl,ant), side) with Failure _ ->
      failwith ("KNOWNC2AUX_res: side: " ^ string_of_term ant) in
    KNOWNC2AUX_res side asl (MATCH_MP th ath);;

(* resolve the assumption labelled lab (named instances first) *)
let KNOWNC2AUX_RES_THEN (lab:string) (insts:(string*term) list) (side:tactic)
    (ttac:thm_tactic) : tactic =
  fun (asl,w as gl) ->
    let th = KNOWNC2AUX_spec_named insts (assoc lab asl) in
    let th' = KNOWNC2AUX_res side asl th in
    let th'' = KNOWNC2AUX_spec_named insts th' in
    ttac th'' gl;;

(* the result ?res2 t. ev /\ ... of an induction hypothesis: the witnesses  *)
(* get the names r and t, the evaluation ev the label evlab                  *)
let KNOWNC2AUX_RES_XL (lab:string) (insts:(string*term) list) (side:tactic)
    (r:term) (t:term) (evlab:string) : tactic =
  KNOWNC2AUX_RES_THEN lab insts side
    (X_CHOOSE_THEN r (X_CHOOSE_THEN t
       (CONJUNCTS_THEN2 (LABEL_TAC evlab o REWRITE_RULE[MAP; FST]) STRIP_ASSUME_TAC)));;

(* forward reasoning with a lemma: its first antecedent is the assumption    *)
(* labelled first, the others are resolved as by KNOWNC2AUX_res              *)
let KNOWNC2AUX_FWD_THEN (th:thm) (insts:(string*term) list) (first:string) (side:tactic)
    (ttac:thm_tactic) : tactic =
  fun (asl,w as gl) ->
    let th0 = KNOWNC2AUX_spec_named insts (KNOWNC2AUX_curry (GEN_ALL th)) in
    let th1 = MATCH_MP th0 (assoc first asl) in
    let th2 = KNOWNC2AUX_spec_named insts (KNOWNC2AUX_res side asl th1) in
    ttac th2 gl;;

let KNOWNC2AUX_FWD_TAC th insts first side =
  KNOWNC2AUX_FWD_THEN th insts first side CAKE_STRIP_ASSUME_TAC;;

(* the same with every antecedent resolved with the assumptions *)
let KNOWNC2AUX_FWD_ANY_THEN (th:thm) (insts:(string*term) list) (side:tactic)
    (ttac:thm_tactic) : tactic =
  fun (asl,w as gl) ->
    let th0 = KNOWNC2AUX_spec_named insts (KNOWNC2AUX_curry (GEN_ALL th)) in
    let th2 = KNOWNC2AUX_spec_named insts (KNOWNC2AUX_res side asl th0) in
    ttac th2 gl;;

(* the oracle facts carried along an evaluation (its oracle is shifted) *)
let KNOWNC2AUX_shift_facts = prove
 (`!(s0:(val_approx spt # C,FFI)clos_state) (s1:(val_approx spt # C,FFI)clos_state) k xs.
     clos_state_compile_oracle s1 = shift_seq k (clos_state_compile_oracle s0) /\
     co_every_Fn_vs_NONE (clos_state_compile_oracle s0) /\
     oracle_state_sgc_free (clos_state_compile_oracle s0) /\
     oracle_gapprox_subspt (clos_state_compile_oracle s0) /\
     unique_set_globals xs (clos_state_compile_oracle s0) ==>
     co_every_Fn_vs_NONE (clos_state_compile_oracle s1) /\
     oracle_state_sgc_free (clos_state_compile_oracle s1) /\
     oracle_gapprox_subspt (clos_state_compile_oracle s1) /\
     unique_set_globals xs (clos_state_compile_oracle s1) /\
     unique_set_globals [] (clos_state_compile_oracle s1) /\
     subspt (next_g s0) (next_g s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[co_every_Fn_vs_NONE_shift_seq; oracle_state_sgc_free_shift_seq;
               oracle_gapprox_subspt_shift_seq; unique_set_globals_shift_seq] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC nil_unique_set_globals THEN
    EXISTS_TAC `xs:clos_exp list` THEN ASM_SIMP_TAC[unique_set_globals_shift_seq];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[next_g_def; shift_seq_def] THEN BETA_TAC THEN
  MATCH_MP_TAC oracle_gapprox_subspt_alt THEN ASM_REWRITE_TAC[ADD_CLAUSES; LE_0]);;

let KNOWNC2AUX_subspt_refl = prove
 (`!sp:A spt. subspt sp sp`,
  REWRITE_TAC[subspt_refl]);;

(* a chain of subspt facts from a to b *)
let KNOWNC2AUX_subspt_path (asms:thm list) (a:term) (b:term) : thm =
  let edges = mapfilter (fun th -> let c = concl th in
      let f,args = strip_comb c in
      if fst(dest_const f) = "subspt" && length args = 2 then (el 0 args, el 1 args, th)
      else failwith "") asms in
  let rec go seen x =
    if x = b then ISPEC x KNOWNC2AUX_subspt_refl
    else
      let nexts = filter (fun (u,_,_) -> u = x) edges in
      tryfind (fun (_,v,th) -> if mem v seen then failwith "KNOWNC2AUX_subspt_path" else
                 MATCH_MP subspt_trans (CONJ th (go (v::seen) v))) nexts in
  go [a] a;;

let KNOWNC2AUX_SUBSPT_TAC : tactic = fun (asl,w as gl) ->
  let f,args = strip_comb w in
  if not (fst(dest_const f) = "subspt") then failwith "KNOWNC2AUX_SUBSPT_TAC" else
  ACCEPT_TAC (KNOWNC2AUX_subspt_path (map snd asl) (el 0 args) (el 1 args)) gl;;

(* v_rel c g x y or ALL2 (v_rel c g) l1 l2 lifted to g' along subspt facts *)
let KNOWNC2AUX_vrel_up (asms:thm list) (g':term) (th:thm) : thm =
  let f,args = strip_comb (concl th) in
  match fst(dest_const f) with
    "clos_knownProof_v_rel" ->
      let g = el 1 args in
      if g = g' then th else
      MATCH_MP clos_knownProof_v_rel_subspt (CONJ th (KNOWNC2AUX_subspt_path asms g g'))
  | "ALL2" ->
      let g = rand (el 0 args) in
      if g = g' then th else
      MATCH_MP (MATCH_MP v_rel_LIST_REL_subspt th) (KNOWNC2AUX_subspt_path asms g g')
  | _ -> failwith "KNOWNC2AUX_vrel_up";;

(* add the relation of the values l1 (a list or a value) at g' *)
let KNOWNC2AUX_UP_TAC (l1:term) (g':term) : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let ok th = try let f,args = strip_comb (concl th) in
                  (fst(dest_const f) = "clos_knownProof_v_rel" && el 2 args = l1) ||
                  (fst(dest_const f) = "ALL2" && el 1 args = l1 &&
                   fst(dest_const(fst(strip_comb(el 0 args)))) = "clos_knownProof_v_rel")
              with Failure _ -> false in
  let th = tryfind (fun th -> if ok th then KNOWNC2AUX_vrel_up asms g' th
                              else failwith "") asms in
  ASSUME_TAC th gl;;

(* result_rel R1 R2 (Rval x) w or (Rerr x) w with w a variable: w is       *)
(* replaced by Rval y or Rerr y (y named yname)                             *)
let KNOWNC2AUX_RR_TAC (yname:string) : tactic = fun (asl,w as gl) ->
  let ok th = try let f,args = strip_comb (concl th) in
                  fst(dest_const f) = "result_rel" && length args = 4 &&
                  is_var (el 3 args) && is_comb (el 2 args) &&
                  mem (fst(dest_const(rator (el 2 args)))) ["Rval";"Rerr"]
              with Failure _ -> false in
  let th = snd (find (fun (_,th) -> ok th) asl) in
  let th' = REWRITE_RULE[result_rel_Rval; result_rel_Rerr1] th in
  let v,_ = dest_exists (concl th') in
  let y = mk_var(yname, type_of v) in
  (MP_TAC th' THEN
   DISCH_THEN(X_CHOOSE_THEN y (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) gl;;

(* the witnesses of ?res2 t. ... /\ (r,t') = (res2,t) /\ ... *)
let KNOWNC2AUX_EX_TAC : tactic = fun (asl,w as gl) ->
  let vs,body = strip_exists w in
  if not (length vs = 2) then failwith "KNOWNC2AUX_EX_TAC" else
  let rec cjs t = if is_conj t then cjs (lhand t) @ cjs (rand t) else [t] in
  let eqs = flat (map (fun t -> if is_eq t && is_pair (lhand t) && is_pair (rand t)
                                then let a,b = dest_pair (lhand t)
                                     and c,d = dest_pair (rand t) in
                                     [mk_eq(a,c); mk_eq(b,d)]
                                else [t]) (cjs body)) in
  let wit v = tryfind (fun t ->
      if is_eq t && rand t = v && not (free_in v (lhand t)) then lhand t
      else if is_eq t && lhand t = v && not (free_in v (rand t)) then rand t
      else failwith "") eqs in
  let w1 = wit (el 0 vs) and w2 = wit (el 1 vs) in
  (EXISTS_TAC w1 THEN EXISTS_TAC w2 THEN REWRITE_TAC[]) gl;;

(* a conjunction of assumptions *)
let KNOWNC2AUX_ASMS_TAC : tactic =
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;;

let KNOWNC2AUX_SIDE_TAC : tactic =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[IS_SOME_DEF] THEN NO_TAC;
         KNOWNC2AUX_SUBSPT_TAC];;

(* ~(r = Rerr (Rabort Rtype_error)) from the assumption ev and res1 *)
let KNOWNC2AUX_NOTE_TAC : tactic =
  DISCH_THEN SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o CAKE_REWRITE_RULE[PAIR_EQ]) THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC `~(res1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
    REWRITE_TAC[GSYM (CONJUNCT1 th)]);;

let KNOWNC2AUX_ALL2_SING = prove
 (`!(R:A->B->bool) x l. ALL2 R [x] l <=> ?y. l = [y] /\ R x y`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; NOT_CONS_NIL] THEN
  STRUCT_CASES_TAC(ISPEC `t:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; CONS_11; NOT_CONS_NIL] THEN MESON_TAC[]);;

(* the functions related by f_rel have the same arities *)
let KNOWNC2AUX_frel_FST = prove
 (`!c aenv (g:val_approx spt) fs1 fs2.
     ALL2 (clos_knownProof_f_rel c aenv g) fs1 fs2 ==>
     LENGTH fs2 = LENGTH fs1 /\ !j. j < LENGTH fs1 ==> FST (EL j fs2) = FST (EL j fs1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`EL j (fs1:(num#clos_exp)list)`,`p1:num#clos_exp`) THEN
  SPEC_TAC(`EL j (fs2:(num#clos_exp)list)`,`p2:num#clos_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; clos_knownProof_f_rel_def; FST] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* App: known and the evaluation of the compiled expressions                 *)
(* ------------------------------------------------------------------------- *)

(* known on an App: the three decisions of decide_inline *)
let KNOWNC2AUX_known_App = prove
 (`!c t loc_opt x1 args aenv (g0:val_approx spt) eas g.
     clos_known_known c [clos_App t loc_opt x1 args] aenv g0 = (eas,g) ==>
     ?ea2 g1 e1 a1.
       clos_known_known c args aenv g0 = (ea2,g1) /\ clos_known_known c [x1] aenv g1 = ([e1,a1],g) /\
       ((decide_inline c a1 loc_opt (LENGTH args) = inlD_Nothing /\
         eas = [clos_App t loc_opt e1 (MAP FST ea2),clos_known_Other]) \/
        (?nl. decide_inline c a1 loc_opt (LENGTH args) = inlD_Annotate nl /\
              eas = [clos_App t (SOME nl) e1 (MAP FST ea2),clos_known_Other]) \/
        (?body ebody abody gdead.
           decide_inline c a1 loc_opt (LENGTH args) = inlD_LetInline body /\
           clos_known_known (dec_inline_factor c) [body] (MAP SND ea2) g = ([ebody,abody],gdead) /\
           eas = [(if pure x1
                   then clos_Let (mk_cons t 0) (MAP FST ea2)
                          (clos_known_mk_Ticks t 1 (LENGTH args) ebody)
                   else clos_Let (mk_cons t 0) (SNOC e1 (MAP FST ea2))
                          (clos_known_mk_Ticks t 1 (LENGTH args) ebody)),abody]))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[clos_known_known_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `args:clos_exp list`; `aenv:val_approx list`;
                 `g0:val_approx spt`] known_LENGTH) THEN
  SPEC_TAC(`clos_known_known c args aenv (g0:val_approx spt)`,
           `p:(clos_exp#val_approx) list # val_approx spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`ea2:(clos_exp#val_approx) list`; `g1:val_approx spt`] THEN
  DISCH_TAC THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:clos_known_config`; `x1:clos_exp`; `aenv:val_approx list`;
                 `g1:val_approx spt`] known_sing) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:clos_exp` (X_CHOOSE_THEN `a1:val_approx`
    (X_CHOOSE_THEN `g2:val_approx spt` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])))) THEN
  CAKE_REWRITE_TAC[HD] THEN
  MP_TAC(ISPEC `decide_inline c a1 loc_opt (LENGTH (args:clos_exp list))`
           (cases "inliningDecision")) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "inliningDecision"; injectivity "inliningDecision"] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "list"] THENL
   [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
      [`ea2:(clos_exp#val_approx) list`; `g1:val_approx spt`; `e1:clos_exp`;
       `a1:val_approx`] THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
      [`ea2:(clos_exp#val_approx) list`; `g1:val_approx spt`; `e1:clos_exp`;
       `a1:val_approx`] THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dec_inline_factor c`; `a:clos_exp`;
                 `MAP SND (ea2:(clos_exp#val_approx) list)`; `g2:val_approx spt`]
                known_sing) THEN
  DISCH_THEN(X_CHOOSE_THEN `eb:clos_exp` (X_CHOOSE_THEN `ab:val_approx`
    (X_CHOOSE_THEN `gd:val_approx spt` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])))) THEN
  CAKE_REWRITE_TAC[HD] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
      [`ea2:(clos_exp#val_approx) list`; `g1:val_approx spt`; `e1:clos_exp`;
       `a1:val_approx`] THEN
  RVEQ_TAC THEN
  ASM_REWRITE_TAC[distinctness "inliningDecision"; injectivity "inliningDecision"] THEN
  MAP_EVERY EXISTS_TAC [`a:clos_exp`; `eb:clos_exp`; `ab:val_approx`; `gd:val_approx spt`] THEN
  ASM_REWRITE_TAC[]);;

(* the parts of an App *)
let KNOWNC2AUX_App_parts = prove
 (`!t loc_opt x1 args.
     (every_Fn_vs_NONE [clos_App t loc_opt x1 args] <=>
      every_Fn_vs_NONE [x1] /\ every_Fn_vs_NONE args) /\
     (ALL clos_esgc_free [clos_App t loc_opt x1 args] <=>
      ALL clos_esgc_free [x1] /\ ALL clos_esgc_free args)`,
  REWRITE_TAC[every_Fn_vs_NONE_def; ALL; clos_esgc_free_def]);;

let KNOWNC2AUX_usg_App = prove
 (`!t loc_opt x1 args (co:num -> A # clos_exp list # B).
     unique_set_globals [clos_App t loc_opt x1 args] co ==>
     unique_set_globals [x1] co /\ unique_set_globals args co /\
     unique_set_globals (APPEND [x1] args) co /\
     BAG_DISJOINT (clos_elist_globals args) (clos_elist_globals [x1])`,
  REWRITE_TAC[unique_set_globals_def; APPEND; clos_elist_globals_append;
              clos_set_globals_def; BAG_ALL_DISTINCT; BAG_UNION; EMPTY_BAG; K_THM;
              BAG_DISJOINT_BAG_IN; BAG_IN; BAG_INN; GE] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `e:num`]) THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `e:num`]) THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `e:num`]) THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `e:num`]) THEN ARITH_TAC]);;

(* the evaluation of the compiled App and Let expressions *)
let KNOWNC2AUX_eval_App = prove
 (CASE_TERM `!t lopt e1 es env (t0:(C,FFI)clos_state).
     ~(es = []) ==>
     clos_evaluate ([clos_App t lopt e1 es],env,t0) =
     match clos_evaluate (es,env,t0) with
       (Rval y2,t1) ->
         (match clos_evaluate ([e1],env,t1) with
            (Rval y1,t2) -> evaluate_app lopt (HD y1) y2 t2
          | r -> r)
     | r -> r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (es:clos_exp list) > 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; GT; LT_NZ]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN ASM_REWRITE_TAC[]);;

let KNOWNC2AUX_eval_Let = prove
 (CASE_TERM `!t es b env (t0:(C,FFI)clos_state).
     clos_evaluate ([clos_Let t es b],env,t0) =
     match clos_evaluate (es,env,t0) with
       (Rval y2,t1) -> clos_evaluate ([b],APPEND y2 env,t1)
     | r -> r`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [clos_evaluate_def] THEN REFL_TAC);;

(* the location given by inlD_Annotate is the one of the target closure *)
let KNOWNC2AUX_loptrel_Annotate = prove
 (`!c a1 loc_opt n nl f1 f2 (g:val_approx spt).
     decide_inline c a1 loc_opt n = inlD_Annotate nl /\ val_approx_val a1 f1 /\
     clos_knownProof_v_rel c g f1 f2 ==> loptrel f2 n loc_opt (SOME nl)`,
  REPEAT GEN_TAC THEN CASES_ON `a1:val_approx` THEN
  REWRITE_TAC[decide_inline_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "inliningDecision"; injectivity "inliningDecision"] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
  REWRITE_TAC[val_approx_val_simps; loptrel_arg1_NONE] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_knownProof_v_rel_def]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) ||
                                                           is_exists (concl th)))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ALL2_DEF]) THEN RVEQ_TAC THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"; injectivity "clos_v";
              distinctness "clos_v"; UNWIND_THM1; UNWIND_THM2] THEN
  TRY (MESON_TAC[] THEN NO_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP KNOWNC2AUX_frel_FST) THEN
  ASM_MESON_TAC[]);;

(* inlD_LetInline: the approximation is a Clos of the call's arity, the call *)
(* has no location and the body has no free variables beyond the arguments   *)
let KNOWNC2AUX_decide_LetInline = prove
 (`!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
     ?m s. fapx = clos_known_Clos m arity body s /\ lopt = NONE /\ fv_max arity [body]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP decide_inline_LetInline_IMP_Clos_fv_max) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `s:num`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `decide_inline c fapx lopt arity = inlD_LetInline body` THEN
  ASM_REWRITE_TAC[decide_inline_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "inliningDecision"]);;

(* the inlined closure: the body compiled by known in the argument          *)
(* approximations is related to the original body                           *)
let KNOWNC2AUX_vrel_app_inline = prove
 (`!c gg m n body envf f2 fe ebody abody gdead (g:val_approx spt) aargs vs.
     clos_knownProof_v_rel c gg (clos_Closure (SOME m) [] envf n body) f2 /\
     fv_max n [body] /\ ALL2 val_approx_val aargs vs /\ ALL val_approx_sgc_free aargs /\
     globals_approx_sgc_free g /\ subspt gdead gg /\
     clos_known_known (dec_inline_factor c) [body] aargs g = ([ebody,abody],gdead) ==>
     v_rel_app c gg (clos_Closure (SOME m) [] envf n body)
       (clos_Closure (SOME m) [] fe n ebody) (SOME vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_knownProof_v_rel_def] THEN STRIP_TAC THEN
  REWRITE_TAC[v_rel_app_def] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`[]:val_approx list`; `[]:clos_v list`; `envf:clos_v list`;
    `[]:clos_v list`; `[]:clos_v list`; `fe:clos_v list`; `ebody:clos_exp`;
    `aargs:val_approx list`] THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES; ALL2; APPEND_NIL] THEN
  REWRITE_TAC[clos_knownProof_exp_rel_def] THEN
  MAP_EVERY EXISTS_TAC [`g:val_approx spt`; `gdead:val_approx spt`; `abody:val_approx`;
    `clos_known_config_inline_factor c DIV 2`] THEN
  ASM_REWRITE_TAC[GSYM dec_inline_factor_def]);;

(* the inlined call is a full application without remaining arguments      *)
let KNOWNC2AUX_inline_dest_closure = prove
 (`!m envf n body vs (s:(C,FFI)clos_state) r s'.
     evaluate_app NONE (clos_Closure (SOME m) [] envf n body) vs s = (r,s') /\
     ~(r = Rerr (Rabort Rtype_error)) /\ n = LENGTH vs /\ ~(vs = []) ==>
     ?exp env. dest_closure (clos_state_max_app s) NONE
                 (clos_Closure (SOME m) [] envf n body) vs = SOME (Full_app exp env [])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `0 < LENGTH (vs:clos_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; LT_NZ]; ALL_TAC] THEN
  REWRITE_TAC[dest_closure_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[check_loc_def; LENGTH; ADD_CLAUSES; LT_REFL; SUB_0] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DROP (LENGTH vs) (REVERSE vs:clos_v list) = []` SUBST1_TAC THENL
   [MESON_TAC[LENGTH_REVERSE; DROP_LENGTH_NIL]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[injectivity "option"; injectivity "app_kind"; REVERSE] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `evaluate_app NONE (clos_Closure (SOME m) [] envf (LENGTH vs) body) vs
                 (s:(C,FFI)clos_state) = r,s'` THEN
  ASM_SIMP_TAC[evaluate_app_rw] THEN
  REWRITE_TAC[dest_closure_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[check_loc_def; LENGTH] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

(* the inlined body evaluated after the ticks is the full application      *)
let KNOWNC2AUX_inline_target = prove
 (`!m tr n ebody vs2 env (t2:(C,FFI)clos_state).
     ~(vs2 = []) /\ LENGTH vs2 = n ==>
     clos_evaluate ([clos_known_mk_Ticks tr 1 n ebody],APPEND vs2 env,t2) =
     evaluate_app (SOME m) (clos_Closure (SOME m) [] env n ebody) vs2 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[evaluate_app_exact_rw; evaluate_mk_Ticks_rw]);;

let KNOWNC2AUX_loptrel_inline = prove
 (`!m fe n ebody k. n = k ==> loptrel (clos_Closure (SOME m) [] fe n ebody) k NONE (SOME m)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[loptrel_arg1_NONE; injectivity "option"; injectivity "clos_v";
              distinctness "clos_v"; distinctness "option"] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* App: the steps of the proof (as HOL4: the arguments, x1, then the three   *)
(* decisions of decide_inline, LetInline split on pure x1)                   *)
(* ------------------------------------------------------------------------- *)

(* the hypotheses of the case, the evaluation of the arguments, the        *)
(* induction hypothesis for them and the facts that follow                  *)
let KNOWNC2AUX_APP_START_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihapp")
    (CONJUNCTS_THEN2 (LABEL_TAC "ihx1") (LABEL_TAC "ihargs"))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "ev") THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ea2:(clos_exp#val_approx) list`
    (X_CHOOSE_THEN `g1:val_approx spt` (X_CHOOSE_THEN `e1:clos_exp`
    (X_CHOOSE_THEN `a1:val_approx` (CONJUNCTS_THEN2 (LABEL_TAC "knargs")
       (CONJUNCTS_THEN2 (LABEL_TAC "knx1") (LABEL_TAC "kcases")))))) o
            MATCH_MP KNOWNC2AUX_known_App) THEN
  REPEAT(DISCH_THEN(STRIP_ASSUME_TAC o
    REWRITE_RULE[KNOWNC2AUX_App_parts; fv_max_rw; mglobals_disjoint_rw])) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP KNOWNC2AUX_usg_App) THEN
  REMOVE_THEN "ev" (MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_def]) THEN
  ASM_CASES_TAC `LENGTH (args:clos_exp list) > 0` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT1) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `~(Rerr (Rabort Rtype_error) = Rerr (Rabort Rtype_error):
                     (clos_v list,clos_v)result)`)) THEN REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `clos_evaluate (args,APPEND env1 xenv1,s:(val_approx spt # C,FFI)clos_state)`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(val_approx spt # C,FFI)clos_state` (LABEL_TAC "evargs"))) THEN
  USE_THEN "evargs" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(LABEL_TAC "ev" o CAKE_REWRITE_RULE[]) THEN
  SUBGOAL_THEN `subspt (g0:val_approx spt) g1 /\ subspt g1 g` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC subspt_known_elist_globals THEN
    MAP_EVERY EXISTS_TAC [`c:clos_known_config`; `args:clos_exp list`; `aenv:val_approx list`;
      `ea2:(clos_exp#val_approx) list`; `[x1:clos_exp]`; `aenv:val_approx list`;
      `[e1:clos_exp,a1:val_approx]`] THEN KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `subspt (g1:val_approx spt) (next_g (s:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL [KNOWNC2AUX_SUBSPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(v = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC
  THENL [KNOWNC2AUX_NOTE_TAC; ALL_TAC] THEN
  KNOWNC2AUX_RES_XL "ihargs" ["xenv2",`xenv2:clos_v list`] NO_TAC
    `w:(clos_v list,clos_v)result` `t1:(C,FFI)clos_state` "tevargs" THEN
  KNOWNC2AUX_FWD_THEN evaluate_changed_globals [] "evargs" NO_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `n1:num` (CONJUNCTS_THEN2 (LABEL_TAC "sh1") (K ALL_TAC))))) THEN
  KNOWNC2AUX_FWD_TAC KNOWNC2AUX_shift_facts ["xs",`[x1:clos_exp]`] "sh1" NO_TAC THEN
  KNOWNC2AUX_FWD_TAC known_preserves_esgc_free [] "knargs" NO_TAC THEN
  SUBGOAL_THEN `subspt (g0:val_approx spt) (next_g (s:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL [KNOWNC2AUX_SUBSPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `state_globals_approx (s:(val_approx spt # C,FFI)clos_state) g0`
    ASSUME_TAC THENL
   [MATCH_MP_TAC state_globals_approx_subspt THEN
    EXISTS_TAC `next_g (s:(val_approx spt # C,FFI)clos_state)` THEN KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_gapprox_disjoint (g0:val_approx spt)
                  (clos_state_compile_oracle (s:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC oracle_gapprox_disjoint_subspt THEN
    EXISTS_TAC `next_g (s:(val_approx spt # C,FFI)clos_state)` THEN KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  KNOWNC2AUX_FWD_TAC known_correct_approx [] "knargs" NO_TAC THEN
  KNOWNC2AUX_FWD_TAC state_oracle_mglobals_disjoint_evaluate_suff [] "evargs" NO_TAC THEN
  USE_THEN "knargs" (ASSUME_TAC o MATCH_MP known_LENGTH_EQ_E) THEN
  SUBGOAL_THEN `~(MAP FST (ea2:(clos_exp#val_approx) list) = [])` (LABEL_TAC "nenil") THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_MAP] THEN
    UNDISCH_TAC `LENGTH (args:clos_exp list) > 0` THEN
    UNDISCH_TAC `LENGTH (ea2:(clos_exp#val_approx) list) = LENGTH (args:clos_exp list)` THEN
    ARITH_TAC;
    ALL_TAC];;

(* one step of the target: the compiled App / Let expressions *)
let KNOWNC2AUX_TGT_EVAL_TAC : tactic =
  USE_THEN "nenil" (fun th -> REWRITE_TAC[MATCH_MP KNOWNC2AUX_eval_App th]) THEN
  REWRITE_TAC[KNOWNC2AUX_eval_Let; clos_evaluate_SNOC];;

(* the evaluation of the arguments fails *)
let KNOWNC2AUX_ARGS_ERR_TAC : tactic =
  REMOVE_THEN "ev" (STRIP_ASSUME_TAC o GSYM o REWRITE_RULE[PAIR_EQ] o CAKE_REWRITE_RULE[]) THEN
  RVEQ_TAC THEN KNOWNC2AUX_RR_TAC "err2" THEN
  KNOWNC2AUX_TGT_EVAL_TAC THEN USE_THEN "tevargs" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN KNOWNC2AUX_EX_TAC THEN KNOWNC2AUX_ASMS_TAC;;

(* the arguments evaluate to vs: the induction hypothesis for x1 *)
let KNOWNC2AUX_X1_TAC : tactic =
  REMOVE_THEN "ev" (MP_TAC o CAKE_REWRITE_RULE[]) THEN
  MP_TAC(ISPEC `clos_evaluate ([x1],APPEND env1 xenv1,s1:(val_approx spt # C,FFI)clos_state)`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(val_approx spt # C,FFI)clos_state` (LABEL_TAC "evx1"))) THEN
  USE_THEN "evx1" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ev") THEN
  KNOWNC2AUX_RR_TAC "vs2" THEN
  KNOWNC2AUX_UP_TAC `env1:clos_v list` `next_g (s1:(val_approx spt # C,FFI)clos_state)` THEN
  SUBGOAL_THEN `subspt (g:val_approx spt) (next_g (s1:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL [KNOWNC2AUX_SUBSPT_TAC; ALL_TAC] THEN
  KNOWNC2AUX_FWD_TAC mglobals_disjoint_evaluate [] "evargs" NO_TAC THEN
  SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC
  THENL [KNOWNC2AUX_NOTE_TAC; ALL_TAC] THEN
  KNOWNC2AUX_RES_XL "ihx1" ["xenv2",`xenv2:clos_v list`] NO_TAC
    `w2:(clos_v list,clos_v)result` `t2:(C,FFI)clos_state` "tevx1";;

(* the evaluation of x1 fails (not for a pure x1) *)
let KNOWNC2AUX_X1_ERR_TAC : tactic =
  REMOVE_THEN "ev" (STRIP_ASSUME_TAC o GSYM o REWRITE_RULE[PAIR_EQ] o CAKE_REWRITE_RULE[]) THEN
  RVEQ_TAC THEN KNOWNC2AUX_RR_TAC "err2" THEN
  KNOWNC2AUX_TGT_EVAL_TAC THEN USE_THEN "tevargs" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN USE_THEN "tevx1" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN KNOWNC2AUX_EX_TAC THEN KNOWNC2AUX_ASMS_TAC;;

(* x1 evaluates to [f1]: the facts for the evaluate_app hypothesis *)
let KNOWNC2AUX_X1_VAL_TAC : tactic =
  USE_THEN "evx1" (X_CHOOSE_THEN `f1:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING) THEN
  REMOVE_THEN "ev" (LABEL_TAC "ev" o CAKE_REWRITE_RULE[HD]) THEN
  KNOWNC2AUX_RR_TAC "fv2" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `fnclos:clos_v` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                REWRITE_RULE[KNOWNC2AUX_ALL2_SING]) THEN
  KNOWNC2AUX_FWD_THEN evaluate_changed_globals [] "evx1" NO_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[rsgc_free_def; ALL])
       (X_CHOOSE_THEN `n2:num` (CONJUNCTS_THEN2 (LABEL_TAC "sh2") (K ALL_TAC))))) THEN
  KNOWNC2AUX_FWD_TAC KNOWNC2AUX_shift_facts ["xs",`[]:clos_exp list`] "sh2" NO_TAC THEN
  KNOWNC2AUX_FWD_THEN known_preserves_esgc_free [] "knx1" NO_TAC
    (STRIP_ASSUME_TAC o REWRITE_RULE[MAP; FST; SND; ALL]) THEN
  SUBGOAL_THEN `oracle_gapprox_disjoint (g1:val_approx spt)
                  (clos_state_compile_oracle (s1:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC oracle_gapprox_disjoint_subspt THEN
    EXISTS_TAC `next_g (s1:(val_approx spt # C,FFI)clos_state)` THEN
    CONJ_TAC THENL [KNOWNC2AUX_SUBSPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  KNOWNC2AUX_FWD_THEN known_correct_approx [] "knx1" NO_TAC
    (STRIP_ASSUME_TAC o REWRITE_RULE[MAP; SND; KNOWNC2AUX_ALL2_SING; injectivity "result";
                                     injectivity "list"; UNWIND_THM1; UNWIND_THM2;
                                     FORALL_UNWIND_THM1; FORALL_UNWIND_THM2]) THEN
  KNOWNC2AUX_FWD_TAC state_oracle_mglobals_disjoint_evaluate_suff [] "evx1" NO_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
                   (try fst(dest_const(fst(strip_comb(lhand(snd(dest_forall(concl th))))))) = "="
                    with Failure _ -> false) &&
                   free_in `v:(clos_v list,clos_v)result` (concl th) = false &&
                   free_in `MAP SND (ea2:(clos_exp#val_approx) list)` (concl th)
                 then MP_TAC (REWRITE_RULE[injectivity "result"; FORALL_UNWIND_THM2;
                                           FORALL_UNWIND_THM1] th)
                 else NO_TAC) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[rsgc_free_def] o
    check (fun th -> concl th = `rsgc_free (Rval vs:(clos_v list,clos_v)result)`)) THEN
  KNOWNC2AUX_UP_TAC `vs:clos_v list` `next_g (s2:(val_approx spt # C,FFI)clos_state)` THEN
  USE_THEN "evargs" (ASSUME_TAC o MATCH_MP clos_evaluate_IMP_LENGTH) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> try let f,args = strip_comb (concl th) in
                         fst(dest_const f) = "ALL2" && el 1 args = `vs:clos_v list`
                     with Failure _ -> false));;

(* the arguments and x1 evaluate to values (x1err: x1 fails) *)
let KNOWNC2AUX_APP_VAL_TAC (x1err:tactic) : tactic =
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:clos_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `err:(clos_v)error_result` SUBST_ALL_TAC)
    (ISPEC `v:(clos_v list,clos_v)result` (cases "result")) THENL
   [ALL_TAC; KNOWNC2AUX_ARGS_ERR_TAC] THEN
  KNOWNC2AUX_X1_TAC THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs1:clos_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `err:(clos_v)error_result` SUBST_ALL_TAC)
    (ISPEC `r2:(clos_v list,clos_v)result` (cases "result")) THENL
   [ALL_TAC; x1err] THEN
  KNOWNC2AUX_X1_VAL_TAC;;

(* the final step: the evaluate_app hypothesis, then the target evaluation *)
let KNOWNC2AUX_APP_FIN_TAC : tactic =
  KNOWNC2AUX_RES_XL "ihapp" [] KNOWNC2AUX_SIDE_TAC
    `res2:(clos_v list,clos_v)result` `t3:(C,FFI)clos_state` "tevapp" THEN
  KNOWNC2AUX_TGT_EVAL_TAC THEN USE_THEN "tevargs" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN USE_THEN "tevx1" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[HD] THEN USE_THEN "tevapp" (fun th -> REWRITE_TAC[th]) THEN
  KNOWNC2AUX_EX_TAC THEN KNOWNC2AUX_ASMS_TAC;;

(* inlD_Nothing: the same call *)
let KNOWNC2AUX_NOTHING_TAC : tactic =
  SUBGOAL_THEN `v_rel_app c (next_g (s2:(val_approx spt # C,FFI)clos_state)) f1 fnclos NONE /\
                loptrel fnclos (LENGTH (vs:clos_v list)) loc_opt loc_opt` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[v_rel_app_NONE; loptrel_def] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  KNOWNC2AUX_APP_FIN_TAC;;

(* inlD_Annotate: the call with the location of the closure *)
let KNOWNC2AUX_ANNOT_TAC : tactic =
  SUBGOAL_THEN `v_rel_app c (next_g (s2:(val_approx spt # C,FFI)clos_state)) f1 fnclos NONE`
    ASSUME_TAC THENL
   [REWRITE_TAC[v_rel_app_NONE] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `loptrel fnclos (LENGTH (vs:clos_v list)) loc_opt (SOME nl)` ASSUME_TAC THENL
   [MATCH_MP_TAC KNOWNC2AUX_loptrel_Annotate THEN
    MAP_EVERY EXISTS_TAC [`c:clos_known_config`; `a1:val_approx`; `f1:clos_v`;
                          `next_g (s2:(val_approx spt # C,FFI)clos_state)`] THEN
    FIRST_ASSUM(fun th ->
      if concl th = `LENGTH (args:clos_exp list) = LENGTH (vs:clos_v list)`
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  KNOWNC2AUX_APP_FIN_TAC;;

(* inlD_LetInline: the inlined closure (fe its environment) and the         *)
(* evaluate_app hypothesis for it                                            *)
let KNOWNC2AUX_INLINE_PREP_TAC (fe:term) : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP KNOWNC2AUX_decide_LetInline o
    check (fun th -> try rand (concl th) = `inlD_LetInline body` with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `sz:num`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `envf:clos_v list` SUBST_ALL_TAC o
    REWRITE_RULE[val_approx_val_simps] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "val_approx_val" &&
                         rand (concl th) = `f1:clos_v`
                     with Failure _ -> false)) THEN
  KNOWNC2AUX_FWD_ANY_THEN decide_inline_inlD_LetInline_sgc_free [] NO_TAC ASSUME_TAC THEN
  SUBGOAL_THEN `clos_elist_globals [body] = EMPTY_BAG` ASSUME_TAC THENL
   [REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:val_approx spt) = gdead` (SUBST_ALL_TAC o SYM) THENL
   [MATCH_MP_TAC known_unchanged_globals THEN
    MAP_EVERY EXISTS_TAC [`dec_inline_factor c`; `[body:clos_exp]`;
      `MAP SND (ea2:(clos_exp#val_approx) list)`; `[ebody:clos_exp,abody:val_approx]`] THEN
    KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `subspt (g:val_approx spt) (next_g (s2:(val_approx spt # C,FFI)clos_state))`
    ASSUME_TAC THENL [KNOWNC2AUX_SUBSPT_TAC; ALL_TAC] THEN
  KNOWNC2AUX_FWD_ANY_THEN KNOWNC2AUX_vrel_app_inline ["fe",fe] NO_TAC ASSUME_TAC THEN
  SUBGOAL_THEN `~(vs:clos_v list = []) /\ ~(vs2:clos_v list = [])` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    UNDISCH_TAC `LENGTH (args:clos_exp list) > 0` THEN
    UNDISCH_TAC `LENGTH (args:clos_exp list) = LENGTH (vs:clos_v list)` THEN
    UNDISCH_TAC `LENGTH (vs:clos_v list) = LENGTH (vs2:clos_v list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (vsubst [fe,`fe:clos_v list`]
    `loptrel (clos_Closure (SOME m) [] fe (LENGTH (args:clos_exp list)) ebody)
             (LENGTH (vs:clos_v list)) NONE (SOME m)`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC KNOWNC2AUX_loptrel_inline THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IS_SOME (SOME (vs:clos_v list)) ==>
                SOME vs = SOME vs /\ ~(vs = []) /\
                (?exp env. dest_closure
                   (clos_state_max_app (s2:(val_approx spt # C,FFI)clos_state)) NONE
                   (clos_Closure (SOME m) [] envf (LENGTH (args:clos_exp list)) body) vs =
                   SOME (Full_app exp env []))` ASSUME_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC KNOWNC2AUX_inline_dest_closure THEN
    MAP_EVERY EXISTS_TAC [`res1:(clos_v list,clos_v)result`;
                          `s':(val_approx spt # C,FFI)clos_state`] THEN
    KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  KNOWNC2AUX_RES_XL "ihapp" [] KNOWNC2AUX_SIDE_TAC
    `res2:(clos_v list,clos_v)result` `t3:(C,FFI)clos_state` "tevapp";;

(* a pure x1 cannot fail but with a type error *)
let KNOWNC2AUX_PURE_X1_ERR_TAC : tactic =
  MP_TAC(ISPECL [`x1:clos_exp`; `APPEND env1 xenv1:clos_v list`;
                 `s1:(val_approx spt # C,FFI)clos_state`] pure_correct) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "evx1" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `ra:clos_v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)
    (ISPEC `err:(clos_v)error_result` (cases "error_result")) THEN
  CAKE_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o CAKE_REWRITE_RULE[PAIR_EQ]) THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC `~(res1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
    REWRITE_TAC[GSYM (CONJUNCT1 th)]);;

(* the inlined call after the ticks: the target of the evaluate_app         *)
(* hypothesis                                                                *)
let KNOWNC2AUX_INLINE_LEN_TAC : tactic =
  SUBGOAL_THEN `LENGTH (vs2:clos_v list) = LENGTH (args:clos_exp list)` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH (args:clos_exp list) = LENGTH (vs:clos_v list)` THEN
    UNDISCH_TAC `LENGTH (vs:clos_v list) = LENGTH (vs2:clos_v list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = `LENGTH (vs2:clos_v list) = LENGTH (args:clos_exp list)`
    then REWRITE_TAC[MATCH_MP (SPEC `m:num` KNOWNC2AUX_inline_target)
                       (CONJ (ASSUME `~(vs2:clos_v list = [])`) th)]
    else NO_TAC);;

(* LetInline, x1 not pure: the target evaluates the arguments, then x1 *)
let KNOWNC2AUX_INLINE_TAC : tactic =
  KNOWNC2AUX_INLINE_PREP_TAC `CONS (fnclos:clos_v) (APPEND env2 xenv2)` THEN
  KNOWNC2AUX_TGT_EVAL_TAC THEN USE_THEN "tevargs" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN USE_THEN "tevx1" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  KNOWNC2AUX_INLINE_LEN_TAC THEN
  USE_THEN "tevapp" (fun th -> REWRITE_TAC[th]) THEN KNOWNC2AUX_EX_TAC THEN
  KNOWNC2AUX_ASMS_TAC;;

(* LetInline, x1 pure: e1 is pure, so its target evaluation does not change *)
(* the state, and the target does not evaluate it                          *)
let KNOWNC2AUX_PURE_INLINE_TAC : tactic =
  SUBGOAL_THEN `pure e1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:clos_known_config`; `[x1:clos_exp]`; `aenv:val_approx list`;
                   `g1:val_approx spt`; `[e1:clos_exp,a1:val_approx]`; `g:val_approx spt`]
                  known_preserves_pure) THEN
    REWRITE_TAC[MAP; FST; ALL] THEN DISCH_THEN MATCH_MP_TAC THEN KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e1:clos_exp`; `APPEND env2 xenv2:clos_v list`;
                 `t1:(C,FFI)clos_state`] pure_correct) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "tevx1" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT1) THEN
  KNOWNC2AUX_INLINE_PREP_TAC `APPEND env2 xenv2:clos_v list` THEN
  KNOWNC2AUX_TGT_EVAL_TAC THEN USE_THEN "tevargs" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN
  KNOWNC2AUX_INLINE_LEN_TAC THEN
  USE_THEN "tevapp" (fun th -> REWRITE_TAC[th]) THEN KNOWNC2AUX_EX_TAC THEN
  KNOWNC2AUX_ASMS_TAC;;

(* case 10: App (HOL4 lines 4045-4381) *)
let CLOSP2AUX_kc0_App = prove
 (el 10 CLOSP2AUX_kc0_cases,
  KNOWNC2AUX_APP_START_TAC THEN
  REMOVE_THEN "kcases" (REPEAT_TCL DISJ_CASES_THEN
     (fun th -> STRIP_ASSUME_TAC th THEN FIRST_X_ASSUM SUBST_ALL_TAC)) THEN
  REWRITE_TAC[MAP; FST] THEN TRY COND_CASES_TAC THENL
   [KNOWNC2AUX_APP_VAL_TAC KNOWNC2AUX_X1_ERR_TAC THEN KNOWNC2AUX_NOTHING_TAC;
    KNOWNC2AUX_APP_VAL_TAC KNOWNC2AUX_X1_ERR_TAC THEN KNOWNC2AUX_ANNOT_TAC;
    KNOWNC2AUX_APP_VAL_TAC KNOWNC2AUX_PURE_X1_ERR_TAC THEN KNOWNC2AUX_PURE_INLINE_TAC;
    KNOWNC2AUX_APP_VAL_TAC KNOWNC2AUX_X1_ERR_TAC THEN KNOWNC2AUX_INLINE_TAC]);;

(* ========================================================================= *)
(* known_correct0, case 14: evaluate_app CONS (HOL4 lines 4412-4861).  It    *)
(* uses the helpers of the App case (case 10), which comes first in the      *)
(* file.                                                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* dest_closure of related functions                                         *)
(* ------------------------------------------------------------------------- *)

(* dest_closure of related closures (lengths equal, loptrel) *)
let KNOWNC2AUX_dc_Closure = prove
 (`!max_app lopt1 lopt2 loc pargs1 cenv1 n e1 pargs2 cenv2 e2 (args:clos_v list)
    (args2:clos_v list).
     loptrel (clos_Closure loc pargs2 cenv2 n e2) (LENGTH args) lopt1 lopt2 /\
     LENGTH pargs2 = LENGTH pargs1 /\ LENGTH args2 = LENGTH args /\
     ~(dest_closure max_app lopt1 (clos_Closure loc pargs1 cenv1 n e1) args = NONE) ==>
     LENGTH pargs1 < n /\
     dest_closure max_app lopt1 (clos_Closure loc pargs1 cenv1 n e1) args =
       (if ~(LENGTH args + LENGTH pargs1 < n)
        then SOME (Full_app e1 (APPEND (APPEND (REVERSE (TAKE (n - LENGTH pargs1) (REVERSE args)))
                                pargs1) cenv1)
                    (REVERSE (DROP (n - LENGTH pargs1) (REVERSE args))))
        else SOME (Partial_app (clos_Closure loc (APPEND args pargs1) cenv1 n e1))) /\
     dest_closure max_app lopt2 (clos_Closure loc pargs2 cenv2 n e2) args2 =
       (if ~(LENGTH args + LENGTH pargs1 < n)
        then SOME (Full_app e2 (APPEND (APPEND (REVERSE (TAKE (n - LENGTH pargs1) (REVERSE args2)))
                                pargs2) cenv2)
                    (REVERSE (DROP (n - LENGTH pargs1) (REVERSE args2))))
        else SOME (Partial_app (clos_Closure loc (APPEND args2 pargs2) cenv2 n e2))) /\
     (~(lopt2 = lopt1) ==> pargs2 = [] /\ n = LENGTH args)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dest_closure_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `check_loc max_app (lopt1:num option) (loc:num option) n
                   (LENGTH (args:clos_v list)) (LENGTH (pargs1:clos_v list)) /\
                 LENGTH pargs1 < n` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(lopt2:num option) = lopt1 \/
                (lopt1 = NONE /\ ?l. (loc:num option) = SOME l /\ lopt2 = SOME l /\
                 n = LENGTH (args:clos_v list) /\ pargs2:clos_v list = [])` MP_TAC THENL
   [UNDISCH_TAC `loptrel (clos_Closure loc pargs2 cenv2 n e2) (LENGTH (args:clos_v list))
                   (lopt1:num option) lopt2` THEN
    REWRITE_TAC[loptrel_def] THEN
    STRUCT_CASES_TAC (ISPEC `loc:num option` (cases "option")) THEN
    STRUCT_CASES_TAC (ISPEC `lopt2:num option` (cases "option")) THEN
    CAKE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    RVEQ_TAC THEN
    SUBGOAL_THEN `LENGTH (pargs1:clos_v list) = 0` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[check_loc_def; LENGTH]]);;

let KNOWNC2AUX_dc_Recclosure = prove
 (`!max_app lopt1 lopt2 loc pargs1 cenv1 fns1 i pargs2 cenv2 fns2 (args:clos_v list)
    (args2:clos_v list).
     loptrel (clos_Recclosure loc pargs2 cenv2 fns2 i) (LENGTH args) lopt1 lopt2 /\
     LENGTH pargs2 = LENGTH pargs1 /\ LENGTH args2 = LENGTH args /\
     LENGTH fns2 = LENGTH fns1 /\ (i < LENGTH fns1 ==> FST (EL i fns2) = FST (EL i fns1)) /\
     ~(dest_closure max_app lopt1 (clos_Recclosure loc pargs1 cenv1 fns1 i) args = NONE) ==>
     i < LENGTH fns1 /\ LENGTH pargs1 < FST (EL i fns1) /\
     dest_closure max_app lopt1 (clos_Recclosure loc pargs1 cenv1 fns1 i) args =
       (if ~(LENGTH args + LENGTH pargs1 < FST (EL i fns1))
        then SOME (Full_app (SND (EL i fns1))
               (APPEND (APPEND (APPEND (REVERSE (TAKE (FST (EL i fns1) - LENGTH pargs1)
                                                      (REVERSE args))) pargs1)
                  (list_of_seq (clos_Recclosure loc [] cenv1 fns1) (LENGTH fns1))) cenv1)
               (REVERSE (DROP (FST (EL i fns1) - LENGTH pargs1) (REVERSE args))))
        else SOME (Partial_app (clos_Recclosure loc (APPEND args pargs1) cenv1 fns1 i))) /\
     dest_closure max_app lopt2 (clos_Recclosure loc pargs2 cenv2 fns2 i) args2 =
       (if ~(LENGTH args + LENGTH pargs1 < FST (EL i fns1))
        then SOME (Full_app (SND (EL i fns2))
               (APPEND (APPEND (APPEND (REVERSE (TAKE (FST (EL i fns1) - LENGTH pargs1)
                                                      (REVERSE args2))) pargs2)
                  (list_of_seq (clos_Recclosure loc [] cenv2 fns2) (LENGTH fns2))) cenv2)
               (REVERSE (DROP (FST (EL i fns1) - LENGTH pargs1) (REVERSE args2))))
        else SOME (Partial_app (clos_Recclosure loc (APPEND args2 pargs2) cenv2 fns2 i))) /\
     (~(lopt2 = lopt1) ==> pargs2 = [] /\ FST (EL i fns1) = LENGTH args)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `EL i (fns1:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `ex1:clos_exp` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `EL i (fns2:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `ex2:clos_exp` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[dest_closure_def; FST; SND] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `LENGTH (fns1:(num#clos_exp)list) <= i \/
                 ~check_loc max_app (lopt1:num option) (OPTION_MAP ((+) (2 * i)) loc) n1
                   (LENGTH (args:clos_v list)) (LENGTH (pargs1:clos_v list)) \/
                 ~(LENGTH pargs1 < n1)` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `n2:num = n1` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(lopt2:num option) = lopt1 \/
                (lopt1 = NONE /\ ?l. (loc:num option) = SOME l /\ lopt2 = SOME (l + 2 * i) /\
                 n1 = LENGTH (args:clos_v list) /\ pargs2:clos_v list = [])` MP_TAC THENL
   [UNDISCH_TAC `loptrel (clos_Recclosure loc pargs2 cenv2 fns2 i) (LENGTH (args:clos_v list))
                   (lopt1:num option) lopt2` THEN
    ASM_REWRITE_TAC[loptrel_def] THEN
    STRUCT_CASES_TAC (ISPEC `loc:num option` (cases "option")) THEN
    STRUCT_CASES_TAC (ISPEC `lopt2:num option` (cases "option")) THEN
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[injectivity "option"; distinctness "option"; FST] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(LENGTH (fns1:(num#clos_exp)list) <= i)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    RVEQ_TAC THEN
    SUBGOAL_THEN `LENGTH (pargs1:clos_v list) = 0` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[check_loc_def; LENGTH; NOT_LE; OPTION_MAP_DEF; injectivity "option";
                    ARITH_RULE `l + 2 * i = 2 * i + l`]]);;
let KNOWNC2AUX_partial_Closure = prove
 (`!c (g:val_approx spt) max_app lopt1 lopt2 loc pargs1 cenv1 n e1 f2 args args2 v.
     dest_closure max_app lopt1 (clos_Closure loc pargs1 cenv1 n e1) args =
       SOME (Partial_app v) /\
     clos_knownProof_v_rel c g (clos_Closure loc pargs1 cenv1 n e1) f2 /\
     loptrel f2 (LENGTH args) lopt1 lopt2 /\
     ALL2 (clos_knownProof_v_rel c g) args args2 ==>
     ?v2. dest_closure max_app lopt2 f2 args2 = SOME (Partial_app v2) /\
          clos_knownProof_v_rel c g v v2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_knownProof_v_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `aenv:val_approx list` (X_CHOOSE_THEN `env1a:clos_v list`
      (X_CHOOSE_THEN `env1b:clos_v list` (X_CHOOSE_THEN `pargs2:clos_v list`
      (X_CHOOSE_THEN `env2a:clos_v list` (X_CHOOSE_THEN `env2b:clos_v list`
      (X_CHOOSE_THEN `e2:clos_exp` STRIP_ASSUME_TAC)))))))) STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  MP_TAC(ISPECL [`max_app:num`; `lopt1:num option`; `lopt2:num option`; `loc:num option`;
    `pargs1:clos_v list`; `APPEND env1a env1b:clos_v list`; `n:num`; `e1:clos_exp`;
    `pargs2:clos_v list`; `APPEND env2a env2b:clos_v list`; `e2:clos_exp`;
    `args:clos_v list`; `args2:clos_v list`] KNOWNC2AUX_dc_Closure) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[distinctness "option"] THEN
    ASM_MESON_TAC[LIST_REL_LENGTH];
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (args:clos_v list) + LENGTH (pargs1:clos_v list) < n` THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "app_kind"; injectivity "app_kind"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; injectivity "app_kind"; UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[clos_knownProof_v_rel_def] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`aenv:val_approx list`; `env1a:clos_v list`; `env1b:clos_v list`;
    `APPEND args2 pargs2:clos_v list`; `env2a:clos_v list`; `env2b:clos_v list`;
    `e2:clos_exp`] THEN
  ASM_SIMP_TAC[LIST_REL_APPEND_suff]);;

let KNOWNC2AUX_partial_Recclosure = prove
 (`!c (g:val_approx spt) max_app lopt1 lopt2 loc pargs1 cenv1 fns1 i f2 args args2 v.
     dest_closure max_app lopt1 (clos_Recclosure loc pargs1 cenv1 fns1 i) args =
       SOME (Partial_app v) /\
     clos_knownProof_v_rel c g (clos_Recclosure loc pargs1 cenv1 fns1 i) f2 /\
     loptrel f2 (LENGTH args) lopt1 lopt2 /\
     ALL2 (clos_knownProof_v_rel c g) args args2 ==>
     ?v2. dest_closure max_app lopt2 f2 args2 = SOME (Partial_app v2) /\
          clos_knownProof_v_rel c g v v2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_knownProof_v_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `aenv:val_approx list` (X_CHOOSE_THEN `env1a:clos_v list`
      (X_CHOOSE_THEN `env1b:clos_v list` (X_CHOOSE_THEN `pargs2:clos_v list`
      (X_CHOOSE_THEN `env2a:clos_v list` (X_CHOOSE_THEN `env2b:clos_v list`
      (X_CHOOSE_THEN `fns2:(num#clos_exp)list` STRIP_ASSUME_TAC)))))))) STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP KNOWNC2AUX_frel_FST o
    check (fun th -> try rand (concl th) = `fns2:(num#clos_exp)list` with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`max_app:num`; `lopt1:num option`; `lopt2:num option`; `loc:num option`;
    `pargs1:clos_v list`; `APPEND env1a env1b:clos_v list`; `fns1:(num#clos_exp)list`; `i:num`;
    `pargs2:clos_v list`; `APPEND env2a env2b:clos_v list`; `fns2:(num#clos_exp)list`;
    `args:clos_v list`; `args2:clos_v list`] KNOWNC2AUX_dc_Recclosure) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[distinctness "option"] THEN
    ASM_MESON_TAC[LIST_REL_LENGTH];
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (args:clos_v list) + LENGTH (pargs1:clos_v list) <
                 FST (EL i (fns1:(num#clos_exp)list))` THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "app_kind"; injectivity "app_kind"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[injectivity "option"; injectivity "app_kind"; UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[clos_knownProof_v_rel_def] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`aenv:val_approx list`; `env1a:clos_v list`; `env1b:clos_v list`;
    `APPEND args2 pargs2:clos_v list`; `env2a:clos_v list`; `env2b:clos_v list`;
    `fns2:(num#clos_exp)list`] THEN
  ASM_SIMP_TAC[LIST_REL_APPEND_suff]);;

(* a partial application of related functions *)
let KNOWNC2AUX_partial = prove
 (`!c (g:val_approx spt) max_app lopt1 lopt2 f f2 args args2 argsopt v.
     dest_closure max_app lopt1 f args = SOME (Partial_app v) /\
     v_rel_app c g f f2 argsopt /\ loptrel f2 (LENGTH args) lopt1 lopt2 /\
     ALL2 (clos_knownProof_v_rel c g) args args2 /\
     (IS_SOME argsopt ==> argsopt = SOME args /\ ~(args = []) /\
        ?exp env. dest_closure max_app lopt1 f args = SOME (Full_app exp env [])) ==>
     ?v2. dest_closure max_app lopt2 f2 args2 = SOME (Partial_app v2) /\
          clos_knownProof_v_rel c g v v2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `argsopt:(clos_v list)option = NONE` SUBST_ALL_TAC THENL
   [MP_TAC(ISPEC `argsopt:(clos_v list)option` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IS_SOME (argsopt:(clos_v list)option) ==> argsopt = SOME args /\
        ~(args = []) /\
        (?exp env. dest_closure max_app lopt1 f args = SOME (Full_app exp env []))` THEN
    ASM_REWRITE_TAC[IS_SOME_DEF; injectivity "option"; distinctness "app_kind"];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_app_NONE]) THEN
  FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
              MATCH_MP clos_knownProof_dest_closure_SOME_IMP) THEN
  RVEQ_TAC THENL
   [MATCH_MP_TAC KNOWNC2AUX_partial_Closure; MATCH_MP_TAC KNOWNC2AUX_partial_Recclosure] THEN
  ASM_MESON_TAC[]);;

(* the arguments taken by a full application *)
let KNOWNC2AUX_full_lengths = prove
 (`!n p (args:A list).
     p < n /\ ~(LENGTH args + p < n) ==>
     LENGTH (REVERSE (TAKE (n - p) (REVERSE args))) = n - p /\
     LENGTH (REVERSE (TAKE (n - p) (REVERSE args))) + p = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n - p <= LENGTH (REVERSE (args:A list))` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REVERSE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_REVERSE; LENGTH_TAKE] THEN ASM_ARITH_TAC);;

(* no remaining arguments when all arguments are taken *)
let KNOWNC2AUX_DROP_ALL = prove
 (`!n (l:A list). LENGTH l <= n ==> REVERSE (DROP n (REVERSE l)) = []`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `DROP n (REVERSE l:A list) = []` SUBST1_TAC THENL
   [MATCH_MP_TAC DROP_LENGTH_TOO_LONG THEN ASM_REWRITE_TAC[LENGTH_REVERSE];
    REWRITE_TAC[REVERSE]]);;
(* a full application of a closure: the parts of the related target call *)
let KNOWNC2AUX_full_Closure = prove
 (`!c (g:val_approx spt) max_app lopt1 lopt2 loc pargs1 cenv1 n e1 f2 args args2 argsopt
    exp env rest.
     dest_closure max_app lopt1 (clos_Closure loc pargs1 cenv1 n e1) args =
       SOME (Full_app exp env rest) /\
     v_rel_app c g (clos_Closure loc pargs1 cenv1 n e1) f2 argsopt /\
     loptrel f2 (LENGTH args) lopt1 lopt2 /\
     ALL2 (clos_knownProof_v_rel c g) args args2 /\
     (IS_SOME argsopt ==> argsopt = SOME args /\ ~(args = []) /\
        ?exp env. dest_closure max_app lopt1 (clos_Closure loc pargs1 cenv1 n e1) args =
                  SOME (Full_app exp env [])) ==>
     ?env1 xenv1 env2 xenv2 aenv exp2 rest2 k g0 g' apx.
       env = APPEND env1 xenv1 /\
       dest_closure max_app lopt2 f2 args2 = SOME (Full_app exp2 (APPEND env2 xenv2) rest2) /\
       ALL2 (clos_knownProof_v_rel c g) rest rest2 /\
       ALL2 (clos_knownProof_v_rel c g) env1 env2 /\
       ALL2 val_approx_val aenv env1 /\ ALL val_approx_sgc_free aenv /\
       fv_max (LENGTH env1) [exp] /\ every_Fn_vs_NONE [exp] /\
       globals_approx_sgc_free g0 /\ subspt g' g /\
       clos_known_known (clos_known_config_inline_factor_fupd (combin_K k) c) [exp] aenv g0 = ([exp2,apx],g') /\
       (~(lopt1 = lopt2) ==> rest = [] /\ rest2 = [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_rel_app_def] THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `aenv:val_approx list` (X_CHOOSE_THEN `env1a:clos_v list`
      (X_CHOOSE_THEN `env1b:clos_v list` (X_CHOOSE_THEN `pargs2:clos_v list`
      (X_CHOOSE_THEN `env2a:clos_v list` (X_CHOOSE_THEN `env2b:clos_v list`
      (X_CHOOSE_THEN `e2:clos_exp` (X_CHOOSE_THEN `aargs:val_approx list`
         STRIP_ASSUME_TAC))))))))) STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  MP_TAC(ISPECL [`max_app:num`; `lopt1:num option`; `lopt2:num option`; `loc:num option`;
    `pargs1:clos_v list`; `APPEND env1a env1b:clos_v list`; `n:num`; `e1:clos_exp`;
    `pargs2:clos_v list`; `APPEND env2a env2b:clos_v list`; `e2:clos_exp`;
    `args:clos_v list`; `args2:clos_v list`] KNOWNC2AUX_dc_Closure) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[distinctness "option"] THEN
    ASM_MESON_TAC[LIST_REL_LENGTH];
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (args:clos_v list) + LENGTH (pargs1:clos_v list) < n` THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "app_kind"; injectivity "app_kind"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `g0:val_approx spt` (X_CHOOSE_THEN `g':val_approx spt`
     (X_CHOOSE_THEN `apx:val_approx` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) o
     REWRITE_RULE[clos_knownProof_exp_rel_def] o
     check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "clos_knownProof_exp_rel"
                      with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> try rand (concl th) = `args2:clos_v list` with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> try rand (concl th) = `pargs2:clos_v list` with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`n:num`; `LENGTH (pargs1:clos_v list)`; `args:clos_v list`]
           KNOWNC2AUX_full_lengths) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND (REVERSE (TAKE (n - LENGTH (pargs1:clos_v list))
       (REVERSE (args:clos_v list)))) pargs1) env1a`; `env1b:clos_v list`;
    `APPEND (APPEND (REVERSE (TAKE (n - LENGTH (pargs1:clos_v list))
       (REVERSE (args2:clos_v list)))) pargs2) env2a`; `env2b:clos_v list`;
    `APPEND aargs aenv:val_approx list`; `e2:clos_exp`;
    `REVERSE (DROP (n - LENGTH (pargs1:clos_v list)) (REVERSE (args2:clos_v list)))`;
    `k:num`; `g0:val_approx spt`; `g':val_approx spt`; `apx:val_approx`] THEN
  REWRITE_TAC[APPEND_ASSOC] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [FIRST_ASSUM(fun th -> if (try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                    "dest_closure" &&
                                  rand(lhs(concl th)) = `args2:clos_v list` with Failure _ -> false)
                          then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[APPEND_ASSOC];
    REPEAT(MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_DROP) THEN
    FIRST_ASSUM ACCEPT_TAC;
    REPEAT(MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC) THEN
    TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT(MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_TAKE) THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MP_TAC(ISPEC `argsopt:(clos_v list)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `aa:clos_v list` SUBST_ALL_TAC)) THEN
    RULE_ASSUM_TAC(CAKE_REWRITE_RULE[IS_SOME_DEF; injectivity "option"]) THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhand (concl th) = `aargs:val_approx list`
                                                     with Failure _ -> false)) THEN
      MATCH_MP_TAC CLOSP2AUX_vav_letrec_NONE THEN ASM_REWRITE_TAC[LENGTH_APPEND];
      ALL_TAC] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC o
      check (fun th -> is_conj (concl th) && rand (concl th) = `pargs1:clos_v list = []`)) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `exq:clos_exp` (X_CHOOSE_THEN `envq:clos_v list` MP_TAC))) o
      check (fun th -> is_conj (concl th) && lhand (concl th) = `aa:clos_v list = args`)) THEN
    FIRST_ASSUM(fun th -> if (try rand(lhs(concl th)) = `args:clos_v list` &&
                                 fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_closure"
                             with Failure _ -> false) then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[injectivity "option"; injectivity "app_kind"] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[LENGTH; SUB_0; APPEND_NIL; REVERSE_EQ_NIL; GSYM LENGTH_EQ_NIL; LENGTH_DROP;
                LENGTH_REVERSE] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `n = LENGTH (args:clos_v list)` SUBST_ALL_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ADD_CLAUSES]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `TAKE (LENGTH (args:clos_v list)) (REVERSE args) = REVERSE args`
      SUBST1_TAC THENL
     [MESON_TAC[LENGTH_REVERSE; TAKE_LENGTH_ID]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REVERSE_REVERSE];
    REWRITE_TAC[LENGTH_APPEND] THEN
    FIRST_ASSUM(fun th -> if (try rand (concl th) = `n:num` && is_comb (lhand (concl th))
                                with Failure _ -> false) then REWRITE_TAC[th] else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> try lhand (concl th) = `~((lopt2:num option) = lopt1)`
                                            with Failure _ -> false)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `LENGTH (pargs1:clos_v list) = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[LENGTH]; ALL_TAC] THEN
    REWRITE_TAC[SUB_0] THEN CONJ_TAC THEN MATCH_MP_TAC KNOWNC2AUX_DROP_ALL THEN
    ASM_ARITH_TAC]);;
(* a full application of a recursive closure: the parts of the related target call *)
let KNOWNC2AUX_full_Recclosure = prove
 (`!c (g:val_approx spt) max_app lopt1 lopt2 loc pargs1 cenv1 fns1 i f2 args args2 argsopt
    exp env rest.
     dest_closure max_app lopt1 (clos_Recclosure loc pargs1 cenv1 fns1 i) args =
       SOME (Full_app exp env rest) /\
     v_rel_app c g (clos_Recclosure loc pargs1 cenv1 fns1 i) f2 argsopt /\
     loptrel f2 (LENGTH args) lopt1 lopt2 /\
     ALL2 (clos_knownProof_v_rel c g) args args2 ==>
     ?env1 xenv1 env2 xenv2 aenv exp2 rest2 k g0 g' apx.
       env = APPEND env1 xenv1 /\
       dest_closure max_app lopt2 f2 args2 = SOME (Full_app exp2 (APPEND env2 xenv2) rest2) /\
       ALL2 (clos_knownProof_v_rel c g) rest rest2 /\
       ALL2 (clos_knownProof_v_rel c g) env1 env2 /\
       ALL2 val_approx_val aenv env1 /\ ALL val_approx_sgc_free aenv /\
       fv_max (LENGTH env1) [exp] /\ every_Fn_vs_NONE [exp] /\
       globals_approx_sgc_free g0 /\ subspt g' g /\
       clos_known_known (clos_known_config_inline_factor_fupd (combin_K k) c) [exp] aenv g0 = ([exp2,apx],g') /\
       (~(lopt1 = lopt2) ==> rest = [] /\ rest2 = [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_rel_app_def; clos_knownProof_v_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `aenv:val_approx list` (X_CHOOSE_THEN `env1a:clos_v list`
      (X_CHOOSE_THEN `env1b:clos_v list` (X_CHOOSE_THEN `pargs2:clos_v list`
      (X_CHOOSE_THEN `env2a:clos_v list` (X_CHOOSE_THEN `env2b:clos_v list`
      (X_CHOOSE_THEN `fns2:(num#clos_exp)list` STRIP_ASSUME_TAC)))))))) STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP KNOWNC2AUX_frel_FST o
    check (fun th -> try rand (concl th) = `fns2:(num#clos_exp)list` with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`max_app:num`; `lopt1:num option`; `lopt2:num option`; `loc:num option`;
    `pargs1:clos_v list`; `APPEND env1a env1b:clos_v list`; `fns1:(num#clos_exp)list`; `i:num`;
    `pargs2:clos_v list`; `APPEND env2a env2b:clos_v list`; `fns2:(num#clos_exp)list`;
    `args:clos_v list`; `args2:clos_v list`] KNOWNC2AUX_dc_Recclosure) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[distinctness "option"] THEN
    ASM_MESON_TAC[LIST_REL_LENGTH];
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (args:clos_v list) + LENGTH (pargs1:clos_v list) <
                 FST (EL i (fns1:(num#clos_exp)list))` THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "app_kind"; injectivity "app_kind"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN] o
    check (fun th -> try rand (concl th) = `fns2:(num#clos_exp)list` with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `EL i (fns1:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `ex1:clos_exp` (LABEL_TAC "el1"))) THEN
  MP_TAC(ISPEC `EL i (fns2:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `ex2:clos_exp` (LABEL_TAC "el2"))) THEN
  USE_THEN "el1" (fun th1 -> USE_THEN "el2" (fun th2 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th1; th2; FST; SND]) THEN REWRITE_TAC[th1; th2; FST; SND] THEN
    LABEL_TAC "el1" th1 THEN LABEL_TAC "el2" th2)) THEN
  REWRITE_TAC[clos_knownProof_f_rel_def; clos_knownProof_exp_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g0:val_approx spt` (X_CHOOSE_THEN `g':val_approx spt`
     (X_CHOOSE_THEN `apx:val_approx` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n1:num = n2`)) THEN
  MP_TAC(ISPECL [`n2:num`; `LENGTH (pargs1:clos_v list)`; `args:clos_v list`]
           KNOWNC2AUX_full_lengths) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> try rand (concl th) = `args2:clos_v list` with Failure _ -> false)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
    check (fun th -> try rand (concl th) = `pargs2:clos_v list` with Failure _ -> false)) THEN
  (fun (asl,w as gl) ->
     let th = snd(find (fun (_,th) -> try let l = lhs (concl th) in
                          fst(dest_const(fst(strip_comb l))) = "clos_known_known" &&
                          el 1 (snd(strip_comb l)) = `[ex1:clos_exp]`
                        with Failure _ -> false) asl) in
     let ae = el 2 (snd(strip_comb(lhs(concl th)))) in
     MAP_EVERY EXISTS_TAC
      [`APPEND (APPEND (APPEND (REVERSE (TAKE (n2 - LENGTH (pargs1:clos_v list))
          (REVERSE (args:clos_v list)))) pargs1)
          (list_of_seq (clos_Recclosure (loc:num option) [] (APPEND env1a env1b)
             (fns1:(num#clos_exp)list)) (LENGTH fns1)))
          (env1a:clos_v list)`; `env1b:clos_v list`;
       `APPEND (APPEND (APPEND (REVERSE (TAKE (n2 - LENGTH (pargs1:clos_v list))
          (REVERSE (args2:clos_v list)))) pargs2)
          (list_of_seq (clos_Recclosure (loc:num option) [] (APPEND env2a env2b)
             (fns2:(num#clos_exp)list)) (LENGTH (fns1:(num#clos_exp)list))))
          (env2a:clos_v list)`; `env2b:clos_v list`;
       ae; `ex2:clos_exp`;
       `REVERSE (DROP (n2 - LENGTH (pargs1:clos_v list)) (REVERSE (args2:clos_v list)))`;
       `k:num`; `g0:val_approx spt`; `g':val_approx spt`; `apx:val_approx`] gl) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [REPEAT(MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_DROP) THEN
      FIRST_ASSUM ACCEPT_TAC;
    REPEAT(MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC) THEN
      TRY (FIRST_ASSUM ACCEPT_TAC) THENL
       [REPEAT(MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_TAKE) THEN
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[LIST_REL_GENLIST] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[clos_knownProof_v_rel_def] THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY EXISTS_TAC [`aenv:val_approx list`; `env1a:clos_v list`; `env1b:clos_v list`;
          `[]:clos_v list`; `env2a:clos_v list`; `env2b:clos_v list`;
          `fns2:(num#clos_exp)list`] THEN
        ASM_REWRITE_TAC[ALL2]];
    MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSP2AUX_vav_letrec_NONE THEN REWRITE_TAC[LENGTH_APPEND] THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      STRUCT_CASES_TAC (ISPEC `loc:num option` (cases "option")) THEN CAKE_REWRITE_TAC[] THENL
       [MATCH_MP_TAC CLOSP2AUX_vav_letrec_NONE THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ];
        REWRITE_TAC[clos_gen_noinline_eq; LIST_REL_GENLIST; val_approx_val_simps] THEN
        REPEAT STRIP_TAC THEN DISJ2_TAC THEN
        REWRITE_TAC[injectivity "clos_v"; distinctness "clos_v"] THEN
        ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[ARITH_RULE `!a j. 2 * (j + 0) + a = a + 2 * j`]];
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `LENGTH (APPEND (APPEND (APPEND (REVERSE (TAKE (n2 - LENGTH (pargs1:clos_v list))
         (REVERSE (args:clos_v list)))) pargs1)
         (list_of_seq (clos_Recclosure (loc:num option) [] (APPEND env1a env1b)
            (fns1:(num#clos_exp)list)) (LENGTH fns1))) (env1a:clos_v list)) =
         n2 + LENGTH fns1 + LENGTH env1a` SUBST1_TAC THENL
       [REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN
        UNDISCH_TAC `LENGTH (REVERSE (TAKE (n2 - LENGTH (pargs1:clos_v list))
                       (REVERSE (args:clos_v list)))) + LENGTH pargs1 = n2` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[GSYM ALL_EL] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" &&
                             can (find_term (fun t -> try fst(dest_const t) = "fv_max"
                                                      with Failure _ -> false)) (concl th)
                         with Failure _ -> false)) THEN
      USE_THEN "el1" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[GSYM ALL_EL] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" &&
                             can (find_term (fun t -> try fst(dest_const t) = "every_Fn_vs_NONE"
                                                      with Failure _ -> false)) (concl th)
                         with Failure _ -> false)) THEN
      USE_THEN "el1" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> try lhand (concl th) = `~((lopt2:num option) = lopt1)`
                                              with Failure _ -> false)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `LENGTH (pargs1:clos_v list) = 0` SUBST1_TAC THENL
       [ASM_MESON_TAC[LENGTH]; ALL_TAC] THEN
      REWRITE_TAC[SUB_0] THEN CONJ_TAC THEN MATCH_MP_TAC KNOWNC2AUX_DROP_ALL THEN
      ASM_ARITH_TAC]);;
(* a full application of related functions: the parts of the target call *)
let KNOWNC2AUX_full = prove
 (`!c (g:val_approx spt) max_app lopt1 lopt2 f f2 args args2 argsopt exp env rest.
     dest_closure max_app lopt1 f args = SOME (Full_app exp env rest) /\
     v_rel_app c g f f2 argsopt /\ loptrel f2 (LENGTH args) lopt1 lopt2 /\
     ALL2 (clos_knownProof_v_rel c g) args args2 /\
     (IS_SOME argsopt ==> argsopt = SOME args /\ ~(args = []) /\
        ?exp env. dest_closure max_app lopt1 f args = SOME (Full_app exp env [])) ==>
     ?env1 xenv1 env2 xenv2 aenv exp2 rest2 k g0 g' apx.
       env = APPEND env1 xenv1 /\
       dest_closure max_app lopt2 f2 args2 = SOME (Full_app exp2 (APPEND env2 xenv2) rest2) /\
       ALL2 (clos_knownProof_v_rel c g) rest rest2 /\
       ALL2 (clos_knownProof_v_rel c g) env1 env2 /\
       ALL2 val_approx_val aenv env1 /\ ALL val_approx_sgc_free aenv /\
       fv_max (LENGTH env1) [exp] /\ every_Fn_vs_NONE [exp] /\
       globals_approx_sgc_free g0 /\ subspt g' g /\
       clos_known_known (clos_known_config_inline_factor_fupd (combin_K k) c) [exp] aenv g0 = ([exp2,apx],g') /\
       (~(lopt1 = lopt2) ==> rest = [] /\ rest2 = [])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
              MATCH_MP clos_knownProof_dest_closure_SOME_IMP) THEN
  RVEQ_TAC THENL
   [MATCH_MP_TAC KNOWNC2AUX_full_Closure; MATCH_MP_TAC KNOWNC2AUX_full_Recclosure] THEN
  ASM_MESON_TAC[]);;
(* the clock does not matter for the state relation and the oracle facts *)
let KNOWNC2AUX_state_rel_clock = prove
 (`!c g (s:(val_approx spt # C,FFI)clos_state) (t:(C,FFI)clos_state) n.
     clos_knownProof_state_rel c g s t ==>
     clos_knownProof_state_rel c g (clos_dec_clock n s) (clos_dec_clock n t) /\
     clos_knownProof_state_rel c g (clos_state_clock_fupd (combin_K 0) s) (clos_state_clock_fupd (combin_K 0) t)`,
  REWRITE_TAC[clos_knownProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

let KNOWNC2AUX_clock_simps = prove
 (`!n f (s:(val_approx spt # C,FFI)clos_state).
     clos_state_compile_oracle (clos_dec_clock n s) = clos_state_compile_oracle s /\
     clos_state_globals (clos_dec_clock n s) = clos_state_globals s /\
     clos_state_max_app (clos_dec_clock n s) = clos_state_max_app s /\
     next_g (clos_dec_clock n s) = next_g s /\
     (ssgc_free (clos_dec_clock n s) <=> ssgc_free s) /\
     (state_oracle_mglobals_disjoint (clos_dec_clock n s) <=>
      state_oracle_mglobals_disjoint s) /\
     clos_state_compile_oracle (clos_state_clock_fupd f s) = clos_state_compile_oracle s /\
     clos_state_globals (clos_state_clock_fupd f s) = clos_state_globals s /\
     next_g (clos_state_clock_fupd f s) = next_g s /\
     (ssgc_free (clos_state_clock_fupd f s) <=> ssgc_free s) /\
     (state_oracle_mglobals_disjoint (clos_state_clock_fupd f s) <=>
      state_oracle_mglobals_disjoint s)`,
  REWRITE_TAC[clos_dec_clock_def; next_g_def; ssgc_free_def;
              state_oracle_mglobals_disjoint_def; clos_state_INFO.ri_accfupds]);;
(* KNOWNC2AUX_res with a normalization of the theorem after each step *)
let rec KNOWNC2AUX_resn (nrm:thm list) (side:tactic) (asl:(string*thm) list) (th:thm) : thm =
  let th = KNOWNC2AUX_curry (PURE_REWRITE_RULE (HD :: nrm) th) in
  let vs,body = strip_forall (concl th) in
  if not (is_imp body) then th else
  let ant = fst(dest_imp body) in
  let mth = try MATCH_MP th with Failure _ -> fun _ -> failwith "MATCH_MP" in
  match (try Some (tryfind (fun (_,a) -> mth a) asl) with Failure _ -> None) with
    Some th' -> KNOWNC2AUX_resn nrm side asl th'
  | None ->
  match (try Some (MATCH_MP th (REFL (lhand ant))) with Failure _ -> None) with
    Some th' -> KNOWNC2AUX_resn nrm side asl th'
  | None ->
    if exists (fun v -> vfree_in v ant) vs then
      failwith ("KNOWNC2AUX_resn: no match: " ^ string_of_term ant) else
    let ath = try TAC_PROOF((asl,ant), side) with Failure _ ->
      failwith ("KNOWNC2AUX_resn: side: " ^ string_of_term ant) in
    KNOWNC2AUX_resn nrm side asl (MATCH_MP th ath);;

let KNOWNC2AUX_RESN_THEN (nrm:thm list) (lab:string) (insts:(string*term) list) (side:tactic)
    (ttac:thm_tactic) : tactic =
  fun (asl,w as gl) ->
    let th = KNOWNC2AUX_spec_named insts (assoc lab asl) in
    let th' = KNOWNC2AUX_resn nrm side asl th in
    let th'' = PURE_REWRITE_RULE nrm (KNOWNC2AUX_spec_named insts th') in
    ttac th'' gl;;

let KNOWNC2AUX_FWDN_THEN (nrm:thm list) (th:thm) (insts:(string*term) list) (first:string)
    (side:tactic) (ttac:thm_tactic) : tactic =
  fun (asl,w as gl) ->
    let th0 = KNOWNC2AUX_spec_named insts (KNOWNC2AUX_curry (GEN_ALL th)) in
    let th1 = MATCH_MP th0 (assoc first asl) in
    let th2 = PURE_REWRITE_RULE nrm
                (KNOWNC2AUX_spec_named insts (KNOWNC2AUX_resn nrm side asl th1)) in
    ttac th2 gl;;

(* the normalization for an evaluation from a state with a decremented clock *)
let KNOWNC2AUX_appcons_nrm =
  [KNOWNC2AUX_clock_simps; state_globals_approx_dec_clock; state_globals_approx_clock_fupd;
   v_rel_upd_inline_factor; state_rel_upd_inline_factor; compile_inc_upd_inline_factor];;

(* ------------------------------------------------------------------------- *)
(* evaluate_app CONS: the steps of the proof (as HOL4: the partial and full  *)
(* applications, the latter by the induction hypotheses for the body and    *)
(* for the remaining arguments)                                              *)
(* ------------------------------------------------------------------------- *)

(* the hypotheses, the target call unfolded, the cases of dest_closure *)
let KNOWNC2AUX_APPCONS_START_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihrest") (LABEL_TAC "ihexp")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[MATCH_MP evaluate_app_rw
    (ISPECL [`v4:clos_v`; `v5:clos_v list`] NOT_CONS_NIL)]) THEN
  DISCH_THEN(LABEL_TAC "ev") THEN
  DISCH_THEN(LABEL_TAC "sr") THEN DISCH_THEN(LABEL_TAC "argsrel") THEN
  DISCH_THEN(LABEL_TAC "vra") THEN DISCH_THEN(LABEL_TAC "lopt") THEN
  REPEAT DISCH_TAC THEN
  USE_THEN "argsrel" (ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  SUBGOAL_THEN `~(args2:clos_v list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `LENGTH (CONS (v4:clos_v) v5) = LENGTH ([]:clos_v list)`)) THEN
    REWRITE_TAC[LENGTH; NOT_SUC];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = `~(args2:clos_v list = [])`
                        then REWRITE_TAC[MATCH_MP evaluate_app_rw th] else NO_TAC) THEN
  SUBGOAL_THEN `clos_state_max_app (t0:(C,FFI)clos_state) =
                clos_state_max_app (s:(val_approx spt # C,FFI)clos_state) /\
                clos_state_clock t0 = clos_state_clock s` STRIP_ASSUME_TAC THENL
   [USE_THEN "sr" (MP_TAC o REWRITE_RULE[clos_knownProof_state_rel_def]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `dest_closure (clos_state_max_app (s:(val_approx spt # C,FFI)clos_state))
                  loc_opt f (CONS v4 v5)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "dc") (X_CHOOSE_THEN `ak:app_kind` (LABEL_TAC "dc"))) THENL
   [USE_THEN "dc" (fun th -> REMOVE_THEN "ev" (MP_TAC o REWRITE_RULE[th])) THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(fun th ->
      UNDISCH_TAC `~(res1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` THEN
      REWRITE_TAC[GSYM (CONJUNCT1 th)]);
    ALL_TAC] THEN
  MP_TAC(ISPEC `ak:app_kind` (cases "app_kind")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `pv:clos_v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `exp:clos_exp` (X_CHOOSE_THEN `env:clos_v list`
       (X_CHOOSE_THEN `rest:clos_v list` SUBST_ALL_TAC))));;

(* the results of a call that takes the clock to 0 or decrements it *)
let KNOWNC2AUX_APPCONS_CLOCK_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  KNOWNC2AUX_EX_TAC THEN
  REWRITE_TAC[KNOWNC2AUX_clock_simps; state_globals_approx_dec_clock;
              state_globals_approx_clock_fupd; result_rel_def; exc_rel_def; ALL2] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  USE_THEN "sr" (fun th -> REWRITE_TAC[MATCH_MP KNOWNC2AUX_state_rel_clock th]);;

(* a partial application *)
let KNOWNC2AUX_APPCONS_PARTIAL_TAC : tactic =
  KNOWNC2AUX_FWD_ANY_THEN KNOWNC2AUX_partial [] NO_TAC
    (X_CHOOSE_THEN `pv2:clos_v` (CONJUNCTS_THEN2 (LABEL_TAC "tdc") ASSUME_TAC)) THEN
  USE_THEN "dc" (fun th -> REMOVE_THEN "ev" (LABEL_TAC "ev" o CAKE_REWRITE_RULE[] o
                                             REWRITE_RULE[th])) THEN
  USE_THEN "tdc" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if concl th = `LENGTH (CONS (v4:clos_v) v5) = LENGTH (args2:clos_v list)`
                        then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  COND_CASES_TAC THEN
  REMOVE_THEN "ev" MP_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  KNOWNC2AUX_APPCONS_CLOCK_FIN_TAC;;

(* a full application: the body is evaluated (induction hypothesis ihexp), *)
(* then the remaining arguments are applied (induction hypothesis ihrest)  *)
let KNOWNC2AUX_APPCONS_FULL_TAC : tactic =
  KNOWNC2AUX_FWD_ANY_THEN KNOWNC2AUX_full [] NO_TAC
    (X_CHOOSE_THEN `envs1:clos_v list` (X_CHOOSE_THEN `xenvs1:clos_v list`
    (X_CHOOSE_THEN `envt:clos_v list` (X_CHOOSE_THEN `xenvt:clos_v list`
    (X_CHOOSE_THEN `aenvs:val_approx list` (X_CHOOSE_THEN `exp2:clos_exp`
    (X_CHOOSE_THEN `rest2:clos_v list` (X_CHOOSE_THEN `k:num`
    (X_CHOOSE_THEN `gk:val_approx spt` (X_CHOOSE_THEN `gk':val_approx spt`
    (X_CHOOSE_THEN `apx:val_approx`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC
         (CONJUNCTS_THEN2 (LABEL_TAC "tdc") STRIP_ASSUME_TAC))))))))))))) THEN
  USE_THEN "dc" (fun th -> REMOVE_THEN "ev" (LABEL_TAC "ev" o CAKE_REWRITE_RULE[] o
                                             REWRITE_RULE[th])) THEN
  USE_THEN "tdc" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (args2:clos_v list) - LENGTH (rest2:clos_v list) =
                LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list)` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `LENGTH (CONS (v4:clos_v) v5) = LENGTH (args2:clos_v list)`
                          then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(fun th -> if (try rand (concl th) = `rest2:clos_v list` with Failure _ -> false)
                          then ACCEPT_TAC (MATCH_MP LIST_REL_LENGTH th) else NO_TAC);
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  REMOVE_THEN "ev" MP_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [KNOWNC2AUX_APPCONS_CLOCK_FIN_TAC; ALL_TAC] THEN
  (* the evaluation of the body *)
  MP_TAC(ISPEC `clos_evaluate ([exp],APPEND envs1 xenvs1,
                  clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list))
                    (s:(val_approx spt # C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(val_approx spt # C,FFI)clos_state` (LABEL_TAC "evexp"))) THEN
  USE_THEN "evexp" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(LABEL_TAC "ev" o CAKE_REWRITE_RULE[]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ALL] o
    check (fun th -> concl th = `ALL vsgc_free (CONS (v4:clos_v) v5)`)) THEN
  KNOWNC2AUX_FWD_TAC dest_closure_Full_sgc_free [] "dc" NO_TAC THEN
  SUBGOAL_THEN `clos_elist_globals [exp] = EMPTY_BAG` ASSUME_TAC THENL
   [REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gk:val_approx spt) = gk'` (SUBST_ALL_TAC o SYM) THENL
   [MATCH_MP_TAC known_unchanged_globals THEN
    MAP_EVERY EXISTS_TAC [`clos_known_config_inline_factor_fupd (combin_K k) c`; `[exp:clos_exp]`;
      `aenvs:val_approx list`; `[exp2:clos_exp,apx:val_approx]`] THEN
    KNOWNC2AUX_ASMS_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `SET_OF_BAG (EMPTY_BAG:num->num) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_OF_BAG_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL clos_esgc_free [exp] /\
                mglobals_disjoint (clos_state_globals (s:(val_approx spt # C,FFI)clos_state))
                  [exp] /\
                unique_set_globals [exp] (clos_state_compile_oracle s)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALL; set_globals_empty_esgc_free; set_globals_empty_unique_set_globals] THEN
    ASM_REWRITE_TAC[mglobals_disjoint_def; DISJOINT_EMPTY];
    ALL_TAC] THEN
  USE_THEN "sr" (STRIP_ASSUME_TAC o
    SPEC `LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list)` o
    MATCH_MP KNOWNC2AUX_state_rel_clock) THEN
  SUBGOAL_THEN `~(r = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC
  THENL [KNOWNC2AUX_NOTE_TAC; ALL_TAC] THEN
  KNOWNC2AUX_RESN_THEN KNOWNC2AUX_appcons_nrm "ihexp" ["xenv2",`xenvt:clos_v list`]
    KNOWNC2AUX_SIDE_TAC
    (X_CHOOSE_THEN `w:(clos_v list,clos_v)result` (X_CHOOSE_THEN `t1:(C,FFI)clos_state`
       (CONJUNCTS_THEN2 (LABEL_TAC "tevexp" o REWRITE_RULE[MAP; FST]) STRIP_ASSUME_TAC))) THEN
  USE_THEN "tevexp" (fun th -> REWRITE_TAC[th]) THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `vs:clos_v list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `err:(clos_v)error_result` SUBST_ALL_TAC)
    (ISPEC `r:(clos_v list,clos_v)result` (cases "result")) THENL
   [ALL_TAC;
    REMOVE_THEN "ev" (STRIP_ASSUME_TAC o GSYM o REWRITE_RULE[PAIR_EQ] o CAKE_REWRITE_RULE[]) THEN
    RVEQ_TAC THEN KNOWNC2AUX_RR_TAC "err2" THEN CAKE_REWRITE_TAC[] THEN
    KNOWNC2AUX_EX_TAC THEN KNOWNC2AUX_ASMS_TAC] THEN
  (* the body evaluates to a value: the remaining arguments *)
  USE_THEN "evexp" (X_CHOOSE_THEN `v:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING) THEN
  REMOVE_THEN "ev" (LABEL_TAC "ev" o CAKE_REWRITE_RULE[]) THEN
  KNOWNC2AUX_RR_TAC "fv2" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v2:clos_v` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                REWRITE_RULE[KNOWNC2AUX_ALL2_SING]) THEN
  CAKE_REWRITE_TAC[] THEN
  KNOWNC2AUX_FWDN_THEN KNOWNC2AUX_appcons_nrm evaluate_changed_globals [] "evexp" NO_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[rsgc_free_def; ALL])
       (X_CHOOSE_THEN `n2:num` (CONJUNCTS_THEN2 (LABEL_TAC "sh2") (K ALL_TAC))))) THEN
  KNOWNC2AUX_FWD_TAC KNOWNC2AUX_shift_facts ["xs",`[]:clos_exp list`] "sh2" NO_TAC THEN
  KNOWNC2AUX_FWDN_THEN KNOWNC2AUX_appcons_nrm state_oracle_mglobals_disjoint_evaluate_suff []
    "evexp" NO_TAC ASSUME_TAC THEN
  ASM_CASES_TAC `loc_opt:num option = lopt2` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    KNOWNC2AUX_UP_TAC `rest:clos_v list` `next_g (s1:(val_approx spt # C,FFI)clos_state)` THEN
    SUBGOAL_THEN `v_rel_app c (next_g (s1:(val_approx spt # C,FFI)clos_state)) v v2 NONE /\
                  loptrel v2 (LENGTH (rest:clos_v list)) loc_opt loc_opt` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[v_rel_app_NONE; loptrel_def] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    KNOWNC2AUX_RES_XL "ihrest" [] KNOWNC2AUX_SIDE_TAC
      `res2:(clos_v list,clos_v)result` `t3:(C,FFI)clos_state` "tevrest" THEN
    USE_THEN "tevrest" (fun th -> REWRITE_TAC[th]) THEN
    KNOWNC2AUX_EX_TAC THEN KNOWNC2AUX_ASMS_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try lhand (concl th) = `~(loc_opt:num option = lopt2)` with Failure _ -> false)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    REMOVE_THEN "ev" (MP_TAC o REWRITE_RULE[evaluate_app_NIL; PAIR_EQ]) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[evaluate_app_NIL] THEN KNOWNC2AUX_EX_TAC THEN
    ASM_REWRITE_TAC[result_rel_def; ALL2]];;

(* case 14: evaluate_app CONS (HOL4 lines 4412-4861) *)
let CLOSP2AUX_kc0_appCONS = prove
 (el 14 CLOSP2AUX_kc0_cases,
  KNOWNC2AUX_APPCONS_START_TAC THENL
   [KNOWNC2AUX_APPCONS_PARTIAL_TAC; KNOWNC2AUX_APPCONS_FULL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* known_correct0 from its 15 cases                                          *)
(* ------------------------------------------------------------------------- *)

let CLOSP2AUX_kc0_thm =
  MP CLOSP2AUX_kc0_ind
    (end_itlist CONJ
      [CLOSP2AUX_kc0_NIL; CLOSP2AUX_kc0_CONS; CLOSP2AUX_kc0_Var; CLOSP2AUX_kc0_If;
       CLOSP2AUX_kc0_Let; CLOSP2AUX_kc0_Raise; CLOSP2AUX_kc0_Handle; CLOSP2AUX_kc0_Op;
       CLOSP2AUX_kc0_Fn; CLOSP2AUX_kc0_Letrec; CLOSP2AUX_kc0_App; CLOSP2AUX_kc0_Tick;
       CLOSP2AUX_kc0_Call; CLOSP2AUX_kc0_appNIL; CLOSP2AUX_kc0_appCONS]);;

(* HOL4: known_correct0 [local] *)
let known_correct0 = prove
 (`(!xs env1full (s0:(val_approx spt # C,FFI)clos_state) res1 s env1 xenv1 env2 xenv2
      (t0:(C,FFI)clos_state) c g0 g aenv eas.
      clos_evaluate (xs,env1full,s0) = (res1,s) /\
      clos_known_known c xs aenv g0 = (eas,g) /\
      clos_knownProof_state_rel c (next_g s0) s0 t0 /\
      every_Fn_vs_NONE xs /\
      co_every_Fn_vs_NONE (clos_state_compile_oracle s0) /\
      mglobals_disjoint (clos_state_globals s0) xs /\
      oracle_gapprox_disjoint (next_g s0) (clos_state_compile_oracle s0) /\
      state_oracle_mglobals_disjoint s0 /\
      ALL clos_esgc_free xs /\ ssgc_free s0 /\
      ALL vsgc_free env1full /\
      ALL2 val_approx_val aenv env1 /\
      oracle_state_sgc_free (clos_state_compile_oracle s0) /\
      globals_approx_sgc_free g0 /\
      ALL val_approx_sgc_free aenv /\
      state_globals_approx s0 (next_g s0) /\
      subspt g0 g /\ subspt g (next_g s0) /\
      oracle_gapprox_subspt (clos_state_compile_oracle s0) /\
      fv_max (LENGTH env1) xs /\
      ALL2 (clos_knownProof_v_rel c (next_g s0)) env1 env2 /\
      unique_set_globals xs (clos_state_compile_oracle s0) /\
      is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s0) /\
      env1full = APPEND env1 xenv1 /\
      ~(res1 = Rerr (Rabort Rtype_error)) ==>
      ?res2 t.
        clos_evaluate (MAP FST eas,APPEND env2 xenv2,t0) = (res2,t) /\
        result_rel (ALL2 (clos_knownProof_v_rel c (next_g s)))
                   (clos_knownProof_v_rel c (next_g s)) res1 res2 /\
        clos_knownProof_state_rel c (next_g s) s t /\
        state_globals_approx s (next_g s) /\
        is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s) /\
        oracle_gapprox_disjoint (next_g s) (clos_state_compile_oracle s)) /\
   (!lopt1 f1 args1 (s0:(val_approx spt # C,FFI)clos_state) res1 s lopt2 f2 args2
      (t0:(C,FFI)clos_state) c argsopt.
      evaluate_app lopt1 f1 args1 s0 = (res1,s) /\
      v_rel_app c (next_g s0) f1 f2 argsopt /\
      oracle_gapprox_disjoint (next_g s0) (clos_state_compile_oracle s0) /\
      state_oracle_mglobals_disjoint s0 /\
      ssgc_free s0 /\ vsgc_free f1 /\ ALL vsgc_free args1 /\
      oracle_state_sgc_free (clos_state_compile_oracle s0) /\
      co_every_Fn_vs_NONE (clos_state_compile_oracle s0) /\
      unique_set_globals [] (clos_state_compile_oracle s0) /\
      is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s0) /\
      ALL2 (clos_knownProof_v_rel c (next_g s0)) args1 args2 /\
      clos_knownProof_state_rel c (next_g s0) s0 t0 /\
      state_globals_approx s0 (next_g s0) /\
      oracle_gapprox_subspt (clos_state_compile_oracle s0) /\
      loptrel f2 (LENGTH args1) lopt1 lopt2 /\
      (IS_SOME argsopt ==>
       argsopt = SOME args1 /\ ~(args1 = []) /\
       ?exp env. dest_closure (clos_state_max_app s0) lopt1 f1 args1 =
                 SOME (Full_app exp env [])) /\
      ~(res1 = Rerr (Rabort Rtype_error)) ==>
      ?res2 t.
        evaluate_app lopt2 f2 args2 t0 = (res2,t) /\
        result_rel (ALL2 (clos_knownProof_v_rel c (next_g s)))
                   (clos_knownProof_v_rel c (next_g s)) res1 res2 /\
        clos_knownProof_state_rel c (next_g s) s t /\
        state_globals_approx s (next_g s) /\
        is_state_oracle (clos_known_compile_inc c) (clos_state_compile_oracle s) /\
        oracle_gapprox_disjoint (next_g s) (clos_state_compile_oracle s))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`xs:clos_exp list`; `env1full:clos_v list`;
                  `s0:(val_approx spt # C,FFI)clos_state`] (CONJUNCT1 CLOSP2AUX_kc0_thm)) THEN
    DISCH_THEN(MP_TAC o SPECL [`res1:(clos_v list,clos_v)result`;
      `s:(val_approx spt # C,FFI)clos_state`; `env1:clos_v list`; `xenv1:clos_v list`;
      `env2:clos_v list`; `xenv2:clos_v list`; `t0:(C,FFI)clos_state`; `c:clos_known_config`;
      `g0:val_approx spt`; `g:val_approx spt`; `aenv:val_approx list`;
      `eas:(clos_exp#val_approx)list`]) THEN
    REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN REWRITE_TAC[];
    MP_TAC(SPECL [`lopt1:num option`; `f1:clos_v`; `args1:clos_v list`;
                  `s0:(val_approx spt # C,FFI)clos_state`] (CONJUNCT2 CLOSP2AUX_kc0_thm)) THEN
    DISCH_THEN(MP_TAC o SPECL [`res1:(clos_v list,clos_v)result`;
      `s:(val_approx spt # C,FFI)clos_state`; `lopt2:num option`; `f2:clos_v`;
      `args2:clos_v list`; `t0:(C,FFI)clos_state`; `c:clos_known_config`;
      `argsopt:(clos_v list)option`]) THEN
    REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN REWRITE_TAC[]]);;

let CLOSP2AUX_exc_rel_T = prove
 (`!(R:A->B->bool) e1 e2. exc_rel R e1 e2 ==> exc_rel (\x:A y:B. T) e1 e2`,
  REPEAT GEN_TAC THEN CASES_ON `e1:(A)error_result` THEN CASES_ON `e2:(B)error_result` THEN
  REWRITE_TAC[exc_rel_def]);;

(* HOL4: semantics_known *)
let semantics_known = prove
 (`!(ffi:(FFI)ffi_state) max_app (co:num -> (val_approx spt # C) # clos_prog)
    (cc:C -> clos_prog -> (byte list # int64 list # C)option) c xs g eas.
     ~(clos_semantics ffi max_app FEMPTY co (state_cc (clos_known_compile_inc c) cc) xs =
       Fail) ==>
     (!n. SND (SND (co n)) = []) /\
     (!n. fv_max 0 (FST (SND (co n)))) /\
     (!n exps aux. SND (co n) = (exps,aux) ==> ALL clos_esgc_free exps) /\
     every_Fn_vs_NONE xs /\
     co_every_Fn_vs_NONE co /\
     oracle_gapprox_subspt co /\
     oracle_state_sgc_free co /\
     is_state_oracle (clos_known_compile_inc c) co /\
     unique_set_globals xs co /\
     ALL clos_esgc_free xs /\
     fv_max 0 xs /\
     FST (FST (co 0)) = g /\
     oracle_gapprox_disjoint g co /\
     clos_known_known c xs [] LN = (eas,g) ==>
     clos_semantics ffi max_app FEMPTY (state_co (clos_known_compile_inc c) co) cc
       (MAP FST eas) =
     clos_semantics ffi max_app FEMPTY co (state_cc (clos_known_compile_inc c) cc) xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `max_app:num`; `FEMPTY:(num,num#clos_exp)fmap`;
     `co:num -> (val_approx spt # C) # clos_prog`;
     `state_cc (clos_known_compile_inc c) (cc:C -> clos_prog -> (byte list # int64 list # C)option)`;
     `xs:clos_exp list`; `FEMPTY:(num,num#clos_exp)fmap`;
     `state_co (clos_known_compile_inc c) (co:num -> (val_approx spt # C) # clos_prog)`;
     `cc:C -> clos_prog -> (byte list # int64 list # C)option`;
     `MAP FST (eas:(clos_exp#val_approx)list)`;
     `\(code1:(num,num#clos_exp)fmap) (co1:num -> (val_approx spt # C) # clos_prog)
        (cc1:val_approx spt # C -> clos_prog -> (byte list # int64 list # (val_approx spt # C))option)
        (es1:clos_exp list) (code2:(num,num#clos_exp)fmap) (co2:num -> C # clos_prog)
        (cc2:C -> clos_prog -> (byte list # int64 list # C)option) (es2:clos_exp list). T`]
     clos_IMP_semantics_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[clos_eval_sim_def] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `res1:(clos_v list,clos_v)result`;
                       `s2:(val_approx spt # C,FFI)clos_state`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:clos_exp list`; `[]:clos_v list`;
     `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
        (co:num -> (val_approx spt # C) # clos_prog)
        (state_cc (clos_known_compile_inc c)
           (cc:C -> clos_prog -> (byte list # int64 list # C)option)) k`;
     `res1:(clos_v list,clos_v)result`; `s2:(val_approx spt # C,FFI)clos_state`;
     `[]:clos_v list`; `[]:clos_v list`; `[]:clos_v list`; `[]:clos_v list`;
     `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
        (state_co (clos_known_compile_inc c) (co:num -> (val_approx spt # C) # clos_prog))
        (cc:C -> clos_prog -> (byte list # int64 list # C)option) k`;
     `c:clos_known_config`; `LN:val_approx spt`; `g:val_approx spt`;
     `[]:val_approx list`; `eas:(clos_exp#val_approx)list`] (CONJUNCT1 known_correct0)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[clos_knownProof_state_rel_def; next_g_def; APPEND_NIL; ALL; ALL2; LENGTH;
                state_globals_approx_def; state_oracle_mglobals_disjoint_def;
                mglobals_disjoint_def; ssgc_free_def; globals_approx_sgc_free_def] THEN
    REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors] THEN
    ASM_REWRITE_TAC[LIST_REL_NIL; fmap_rel_def; FDOM_FEMPTY; NOT_IN_EMPTY; subspt_LN;
                    subspt_refl; lookup_rwts; distinctness "option"; get_global_def; LENGTH;
                    CONJUNCT1 LT; mapped_globals_def; EMPTY_GSPEC; DISJOINT_EMPTY;
                    FLOOKUP_EMPTY; MEM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_initial_state_def]) THEN
    REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_MESON_TAC[] THEN NO_TAC) THEN
    SUBGOAL_THEN `aux:(num#num#clos_exp)list = []` SUBST1_TAC THENL
     [ASM_MESON_TAC[SND]; REWRITE_TAC[MAP; clos_set_globals_def]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `t2:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`0`; `r2:(clos_v list,clos_v)result`; `t2:(C,FFI)clos_state`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CLOSP2AUX_letop_result_shape]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_knownProof_state_rel_def]) THEN ASM_REWRITE_TAC[]);;

(* HOL4: known_correct0 [local] *)

(* HOL4: code_locs_mk_Ticks [simp] *)
let code_locs_mk_Ticks = prove
 (`!a b c d. code_locs [clos_known_mk_Ticks a b c d] = code_locs [d]`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[code_locs_def]);;
let _ = cake_add_simps [code_locs_mk_Ticks];;

(* HOL4: contains_closures_code_locs *)
let contains_closures_code_locs = prove
 (`!es. ~contains_closures es ==> code_locs es = []`,
  MATCH_MP_TAC contains_closures_ind THEN
  REWRITE_TAC[contains_closures_def; TAUT `(if a then T else b) <=> a \/ b`;
              DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC[code_locs_def; LET_DEF; LET_END_DEF; APPEND]);;

(* HOL4: code_locs_decide_inline *)
let code_locs_decide_inline = prove
 (`!a b c d e. decide_inline a b c d = inlD_LetInline e ==> code_locs [e] = []`,
  REPEAT GEN_TAC THEN CASES_ON `b:val_approx` THEN
  REWRITE_TAC[decide_inline_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONJ_ASSOC]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[contains_closures_code_locs]);;

let CLOSP2AUX_kcl_P = `\c xs aenv (g0:val_approx spt).
   !eas g. clos_known_known c xs aenv g0 = (eas,g) ==>
     SUB_BAG (LIST_TO_BAG (code_locs (MAP FST eas))) (LIST_TO_BAG (code_locs xs))`;;

let CLOSP2AUX_kcl_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC CLOSP2AUX_kcl_P clos_known_known_ind);;

let CLOSP2AUX_kcl_nrm = [code_locs_def; LET_DEF; LET_END_DEF; code_locs_append;
  LIST_TO_BAG_APPEND; MAP; MAP_APPEND; HD; FST; SND; code_locs_mk_Ticks;
  CONJUNCT1 LIST_TO_BAG_def; code_locs_SmartOp; SNOC_APPEND; LENGTH_MAP; APPEND_NIL;
  BAG_UNION_EMPTY; PAIR_EQ];;

let CLOSP2AUX_KCL_NIL_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) -> let l,r = dest_eq (concl th) in
              if fst(dest_const(fst(strip_comb l))) = "code_locs" && r = `[]:num list`
              then th else failwith "") asl in
  (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) gl;;

(* pointwise bag arithmetic (the goal may become trivial) *)
let CLOSP2AUX_KCL_BAG_TAC : tactic = fun (asl,w as g) ->
  (RULE_ASSUM_TAC(REWRITE_RULE[SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG; K_THM]) THEN
   REWRITE_TAC[SUB_BAG_LEQ; BAG_UNION; EMPTY_BAG; K_THM; LE_REFL; LE_0] THEN
   X_GEN_TAC `xg:num` THEN
   REPEAT(FIRST_X_ASSUM(fun th ->
     let c = concl th in
     if is_forall c && type_of (fst(dest_forall c)) = `:num` &&
        (try let _,b = dest_forall c in is_binary "<=" b with Failure _ -> false)
     then MP_TAC (SPEC `xg:num` th) else NO_TAC)) THEN
   ARITH_TAC) g;;

let CLOSP2AUX_kcl_letrec = prove
 (`!(f:num#clos_exp->num#clos_exp) fns.
     (!n x. MEM (n,x) fns ==>
            SUB_BAG (LIST_TO_BAG (code_locs [SND (f (n,x))])) (LIST_TO_BAG (code_locs [x]))) ==>
     SUB_BAG (LIST_TO_BAG (code_locs (MAP SND (MAP f fns))))
             (LIST_TO_BAG (code_locs (MAP SND fns)))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; code_locs_def; SUB_BAG_REFL; MEM] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `x:clos_exp` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:clos_exp`]) THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[LIST_TO_BAG_APPEND; SND] THEN CLOSP2AUX_KCL_BAG_TAC);;

(* the Letrec case: the code_locs of the new function bodies *)
let CLOSP2AUX_KCL_LETREC_TAC : tactic = fun (asl,w as gl) ->
  let pat = `code_locs (MAP SND (MAP (f:num#clos_exp->num#clos_exp) fns))` in
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let inner = rand (rand t) in
  let ff = rand(rator inner) and fns = rand inner in
  let ih_tac : tactic = fun (asl,w as g) ->
    let kt = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "clos_known_known"
                                 with Failure _ -> false) w in
    let args = snd(strip_comb kt) in
    let xx = hd (dest_list (el 1 args)) and nv = el 2 args in
    let memth = snd (find (fun (_,th) -> try fst(dest_const(fst(strip_comb (concl th)))) = "MEM"
                                         with Failure _ -> false) asl) in
    let nn = fst(dest_pair(lhand(concl memth))) in
    (MP_TAC(ISPECL [el 0 args; xx; nv; el 3 args] known_sing) THEN
     DISCH_THEN(X_CHOOSE_THEN `ee:clos_exp` (X_CHOOSE_THEN `aa:val_approx`
       (X_CHOOSE_THEN `gg:val_approx spt` ASSUME_TAC))) THEN
     FIRST_X_ASSUM(fun kth -> if is_eq (concl kth) && lhs (concl kth) = kt then
       FIRST_ASSUM(fun ih -> try
         MP_TAC(MATCH_MP (MATCH_MP (SPECL [nn; xx; nv] ih) memth) kth)
         with Failure _ -> NO_TAC) THEN REWRITE_TAC[kth; MAP; HD; FST]
       else NO_TAC)) g in
  (MP_TAC(ISPECL [ff; fns] CLOSP2AUX_kcl_letrec) THEN ANTS_TAC THENL
    [MAP_EVERY X_GEN_TAC [`nn:num`; `xx:clos_exp`] THEN DISCH_TAC THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN CAKE_REWRITE_TAC[SND] THEN ih_tac;
     DISCH_TAC]) gl;;

let CLOSP2AUX_KCL_CASE_TAC : tactic =
  CLOSP2AUX_KN_UNFOLD_TAC THEN REPEAT DISCH_TAC THEN CLOSP2AUX_KN_SING_TAC THEN
  CLOSP2AUX_SATP_GEN_TAC [] NO_TAC [code_locs_decide_inline] CLOSP2AUX_kcl_nrm 3 THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kcl_nrm) THEN
  CLOSP2AUX_KCL_NIL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kcl_nrm) THEN
  REWRITE_TAC CLOSP2AUX_kcl_nrm THEN
  TRY CLOSP2AUX_KCL_LETREC_TAC THEN
  CLOSP2AUX_KCL_BAG_TAC;;

let CLOSP2AUX_kcl_thm =
  MP CLOSP2AUX_kcl_ind
    (end_itlist CONJ (map (fun t -> prove(t, CLOSP2AUX_KCL_CASE_TAC))
                          (conjuncts (lhand (concl CLOSP2AUX_kcl_ind)))));;

(* HOL4: known_code_locs_bag *)
let known_code_locs_bag = prove
 (`!c xs aenv (g0:val_approx spt) eas g.
     clos_known_known c xs aenv g0 = (eas,g) ==>
     SUB_BAG (LIST_TO_BAG (code_locs (MAP FST eas))) (LIST_TO_BAG (code_locs xs))`,
  MATCH_ACCEPT_TAC CLOSP2AUX_kcl_thm);;

(* HOL4: compile_code_locs_bag *)
let compile_code_locs_bag = prove
 (`!kc es kc' es'.
     clos_known_compile kc es = (kc',es') ==>
     SUB_BAG (LIST_TO_BAG (code_locs es')) (LIST_TO_BAG (code_locs es))`,
  REPEAT GEN_TAC THEN CASES_ON `kc:clos_known_config option` THEN
  REWRITE_TAC[clos_known_compile_def; PAIR_EQ] THENL
   [MESON_TAC[SUB_BAG_REFL]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[code_locs_let_op; code_locs_remove_ticks] THEN
  MP_TAC(ISPECL [`a:clos_known_config`; `clos_fvs_compile es`; `[]:val_approx list`;
                 `LN:val_approx spt`;
                 `FST (clos_known_known a (clos_fvs_compile es) [] (LN:val_approx spt))`;
                 `SND (clos_known_known a (clos_fvs_compile es) [] (LN:val_approx spt))`]
                known_code_locs_bag) THEN
  REWRITE_TAC[PAIR; clos_fvs_compile_def; code_locs_remove_fvs]);;

(* HOL4: compile_LENGTH *)
let clos_knownProof_compile_LENGTH = prove
 (`!kc es kc' es'. clos_known_compile kc es = (kc',es') ==> LENGTH es' = LENGTH es`,
  REPEAT GEN_TAC THEN CASES_ON `kc:clos_known_config option` THEN
  REWRITE_TAC[clos_known_compile_def; PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[clos_letop_LENGTH_let_op; clos_ticks_LENGTH_remove_ticks; LENGTH_MAP;
              known_LENGTH; clos_fvs_compile_def; clos_fvsProof_LENGTH_remove_fvs]);;

(* ------------------------------------------------------------------------- *)
(* syntactic oracle conditions and the compiler-level semantics theorem      *)
(* ------------------------------------------------------------------------- *)

(* HOL4: syntax_ok_def *)
let clos_knownProof_syntax_ok_def = cake_def
  `clos_knownProof_syntax_ok xs <=>
     every_Fn_vs_NONE xs /\
     BAG_ALL_DISTINCT (clos_elist_globals xs) /\
     ALL clos_esgc_free xs`;;

(* HOL4 lines 5010-5012: the overload fvs_compile and the ML value fvs_inc  *)
(* (clos_fvs_compile and clos_fvs_compile_inc at clos_prog->clos_prog).    *)

(* HOL4: syntax_oracle_ok_def *)
let clos_knownProof_syntax_oracle_ok_def = cake_def
  `clos_knownProof_syntax_oracle_ok c xs
     (co:num->((val_approx)spt#C)#clos_prog) (conf:(val_approx)spt) <=>
     clos_knownProof_syntax_ok xs /\
     is_state_oracle (clos_known_compile_inc c)
       (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
     conf = FST (FST (co 0)) /\
     oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
       (SET_OF_BAG (clos_elist_globals xs)) co /\
     (!n. clos_knownProof_syntax_ok (FST (SND (co n))) /\ SND (SND (co n)) = [])`;;

(* HOL4: known_cc_def *)
let known_cc_def = cake_def
  `known_cc known_conf (cc:B->clos_prog->(byte list#int64 list#B)option) =
     match known_conf with
       SOME kcfg ->
         (pure_cc (clos_fvs_compile_inc:clos_prog->clos_prog)
            (state_cc (clos_known_compile_inc kcfg)
               (pure_cc (clos_ticks_compile_inc:clos_prog->clos_prog)
                  (pure_cc (clos_letop_compile_inc:clos_prog->clos_prog) cc))))
     | NONE -> (state_cc (CURRY I) cc:
                ((val_approx)spt#B)->clos_prog->
                (byte list#int64 list#((val_approx)spt#B))option)`;;

(* HOL4: known_co_def *)
let known_co_def = cake_def
  `known_co known_conf (co:num->((val_approx)spt#B)#clos_prog) =
     match known_conf with
       SOME kcfg ->
         (pure_co (clos_letop_compile_inc:clos_prog->clos_prog) o
            (pure_co (clos_ticks_compile_inc:clos_prog->clos_prog) o
               state_co (clos_known_compile_inc kcfg)
                 (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co)))
     | NONE -> (state_co (CURRY I) co:num->B#clos_prog)`;;

(* HOL4: known_co_eq_pure_state *)
let known_co_eq_pure_state = prove
 (CASE_TERM `!known_conf (co:num->((val_approx)spt#B)#clos_prog).
   known_co known_conf co =
     pure_co (if IS_SOME known_conf
              then (clos_letop_compile_inc:clos_prog->clos_prog) o
                   (clos_ticks_compile_inc:clos_prog->clos_prog)
              else I) o
     state_co (match known_conf with
                 SOME kcfg -> clos_known_compile_inc kcfg
               | NONE -> CURRY I)
       (pure_co (if IS_SOME known_conf
                 then (clos_fvs_compile_inc:clos_prog->clos_prog) else I) o co)`,
  GEN_TAC THEN CASES_ON `known_conf:clos_known_config option` THEN
  REWRITE_TAC[known_co_def; IS_SOME_DEF] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[pure_co_I; I_O_ID; pure_co_comb_pure_co]);;

(* HOL4: known_mk_co_def *)
let known_mk_co_def = cake_def
  `known_mk_co kc kc' (mk:(num->clos_prog)->num->B) =
     add_state_co (if IS_SOME kc then clos_known_compile_inc (THE kc)
                   else CURRY I)
       (option_val_approx_spt kc')
       (mk o pure_co_progs (if IS_SOME kc
                            then (clos_letop_compile_inc:clos_prog->clos_prog) o
                                 (clos_ticks_compile_inc:clos_prog->clos_prog)
                            else I)) o
     pure_co_progs (if IS_SOME kc then (clos_fvs_compile_inc:clos_prog->clos_prog)
                    else I)`;;

(* HOL4: known_co_progs_def *)
let known_co_progs_def = cake_def
  `known_co_progs kc kc' =
     pure_co_progs (if IS_SOME kc
                    then (clos_letop_compile_inc:clos_prog->clos_prog) o
                         (clos_ticks_compile_inc:clos_prog->clos_prog)
                    else I) o
     state_co_progs (if IS_SOME kc then clos_known_compile_inc (THE kc)
                     else CURRY I)
       (match kc' with
          NONE -> LN
        | SOME kcfg -> clos_known_config_val_approx_spt kcfg) o
     pure_co_progs (if IS_SOME kc then (clos_fvs_compile_inc:clos_prog->clos_prog)
                    else I)`;;

(* HOL4: known_co_known_mk_co *)
let known_co_known_mk_co = prove
 (`!kc kc' (mk:(num->clos_prog)->num->B) (co:num->clos_prog).
   known_co kc (syntax_to_full_oracle (known_mk_co kc kc' mk) co) =
   syntax_to_full_oracle mk (known_co_progs kc kc' co)`,
  REPEAT GEN_TAC THEN CASES_ON `kc:clos_known_config option` THEN
  REWRITE_TAC[known_co_progs_def; known_mk_co_def; known_co_eq_pure_state; IS_SOME_DEF;
              THE_DEF; option_val_approx_spt_def] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[pure_co_syntax_to_full_oracle; state_co_add_state_co; o_THM] THEN
  REWRITE_TAC[pure_co_I; I_O_ID; o_THM] THEN
  CASES_ON `kc':clos_known_config option` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[pure_co_syntax_to_full_oracle; state_co_add_state_co; o_THM]);;

(* HOL4: fvs_compile_uncurry *)
let fvs_compile_uncurry = prove
 (`!p:clos_prog. clos_fvs_compile_inc p = (remove_fvs 0 (FST p),[]:(num#num#clos_exp)list)`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_fvs_compile_inc_def; clos_fvs_compile_def; FST]);;

(* HOL4: syntax_oracle_ok_state_sgc_free *)
let syntax_oracle_ok_state_sgc_free = prove
 (`!c xs (co:num->((val_approx)spt#C)#clos_prog) g ys.
     clos_knownProof_syntax_oracle_ok c xs co g ==>
     clos_known_known c (clos_fvs_compile xs) [] LN = (ys,g) ==>
     oracle_state_sgc_free co`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_knownProof_syntax_oracle_ok_def; clos_knownProof_syntax_ok_def;
              oracle_state_sgc_free_def; is_state_oracle_def; o_THM; FST_pure_co;
              SND_pure_co] THEN
  STRIP_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [UNDISCH_TAC `g = FST (FST ((co:num->((val_approx)spt#C)#clos_prog) 0))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] known_preserves_esgc_free) o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "clos_known_known"
                       with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[clos_fvs_compile_def; remove_fvs_esgc_free; ALL] THEN
    REWRITE_TAC[globals_approx_sgc_free_def; lookup_rwts; distinctness "option"] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `SND ((co:num->((val_approx)spt#C)#clos_prog) n)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `es:clos_exp list`
      (X_CHOOSE_THEN `aux:(num#num#clos_exp)list` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[fvs_compile_uncurry; clos_known_compile_inc_def; LET_DEF; LET_END_DEF;
                    pair_CASE_def; FST] THEN
    MP_TAC(ISPECL [`reset_inline_factor c`; `remove_fvs 0 es`; `[]:val_approx list`;
      `FST (FST ((co:num->((val_approx)spt#C)#clos_prog) n))`;
      `FST (clos_known_known (reset_inline_factor c) (remove_fvs 0 es) []
         (FST (FST ((co:num->((val_approx)spt#C)#clos_prog) n))))`;
      `SND (clos_known_known (reset_inline_factor c) (remove_fvs 0 es) []
         (FST (FST ((co:num->((val_approx)spt#C)#clos_prog) n))))`]
      known_preserves_esgc_free) THEN
    REWRITE_TAC[PAIR; remove_fvs_esgc_free; ALL] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      SIMP_TAC[]]]);;

let CLOSP2AUX_first_n_exps_fvs = prove
 (`!(co:num->((val_approx)spt#C)#clos_prog) n.
     clos_elist_globals (FLAT (first_n_exps (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) n)) =
     clos_elist_globals (FLAT (first_n_exps co n))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[CLOSP2AUX_first_n_exps_0; CLOSP2AUX_first_n_exps_SUC; FLAT_APPEND; FLAT;
                  APPEND_NIL; clos_elist_globals_append; o_THM; SND_pure_co;
                  fvs_compile_uncurry; remove_fvs_elist_globals]);;

(* HOL4: syntax_oracle_ok_gapprox_subspt *)
let syntax_oracle_ok_gapprox_subspt = prove
 (`!c xs (co:num->((val_approx)spt#C)#clos_prog) g ys.
     clos_knownProof_syntax_oracle_ok c xs co g ==>
     clos_known_known c (clos_fvs_compile xs) [] LN = (ys,g) ==>
     oracle_gapprox_subspt co`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `oracle_state_sgc_free (co:num->((val_approx)spt#C)#clos_prog)` ASSUME_TAC THENL
   [ASM_MESON_TAC[syntax_oracle_ok_state_sgc_free]; ALL_TAC] THEN
  UNDISCH_TAC `clos_knownProof_syntax_oracle_ok c xs
                 (co:num->((val_approx)spt#C)#clos_prog) g` THEN
  REWRITE_TAC[clos_knownProof_syntax_oracle_ok_def; clos_knownProof_syntax_ok_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `unique_set_globals xs (co:num->((val_approx)spt#C)#clos_prog)` MP_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] monotonic_unique_set_globals) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_knownProof_syntax_ok_def]) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "BAG_ALL_DISTINCT"
                               with Failure _ -> false)) (concl th))) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[unique_set_globals_def; clos_elist_globals_append; BAG_ALL_DISTINCT;
              BAG_UNION] THEN DISCH_TAC THEN
  REWRITE_TAC[oracle_gapprox_subspt_def] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPEC `SND ((co:num->((val_approx)spt#C)#clos_prog) n)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:clos_exp list`
    (X_CHOOSE_THEN `aux:(num#num#clos_exp)list` ASSUME_TAC)) THEN
  SUBGOAL_THEN `FST (FST ((co:num->((val_approx)spt#C)#clos_prog) (SUC n))) =
                SND (clos_known_known (reset_inline_factor c) (remove_fvs 0 es) []
                       (FST (FST (co n))))` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o REWRITE_RULE[is_state_oracle_def] o
      check (fun th -> try fst(dest_const(fst(strip_comb (concl th)))) = "is_state_oracle"
                       with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[o_THM; FST_pure_co; SND_pure_co; fvs_compile_uncurry;
                    clos_known_compile_inc_def; LET_DEF; LET_END_DEF;
                    pair_CASE_def; FST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`reset_inline_factor c`; `remove_fvs 0 es`; `[]:val_approx list`;
    `FST (FST ((co:num->((val_approx)spt#C)#clos_prog) n))`;
    `FST (clos_known_known (reset_inline_factor c) (remove_fvs 0 es) []
           (FST (FST ((co:num->((val_approx)spt#C)#clos_prog) n))))`;
    `SND (clos_known_known (reset_inline_factor c) (remove_fvs 0 es) []
           (FST (FST ((co:num->((val_approx)spt#C)#clos_prog) n))))`] known_subspt) THEN
  REWRITE_TAC[PAIR; remove_fvs_esgc_free; ALL; remove_fvs_elist_globals] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "BAG_ALL_DISTINCT"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ASM_MESON_TAC[oracle_state_sgc_free_def];
    ALL_TAC] THEN
  (* the domain of the approximation before step n *)
  MP_TAC(ISPECL [`c:clos_known_config`;
                 `pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o (co:num->((val_approx)spt#C)#clos_prog)`;
                 `n:num`] state_oracle_domain) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_first_n_exps_fvs; o_THM; FST_pure_co] THEN
  UNDISCH_TAC `g = FST (FST ((co:num->((val_approx)spt#C)#clos_prog) 0))` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP known_changed_globals_alt o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "clos_known_known"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[domain_def; SET_OF_EMPTY; BAG_UNION_EMPTY; clos_fvs_compile_def;
              remove_fvs_elist_globals] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC n` o check (fun th -> is_forall (concl th) &&
     can (find_term (fun t -> try fst(dest_const t) = "first_n_exps"
                              with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_first_n_exps_SUC; FLAT_APPEND; FLAT; APPEND_NIL;
                  clos_elist_globals_append; BAG_UNION] THEN DISCH_TAC THEN
  REWRITE_TAC[BAG_ALL_DISTINCT; BAG_UNION] THEN X_GEN_TAC `e:num` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o REWRITE_RULE[SUB_BAG_LEQ; BAG_UNION] o
     check (fun th -> try fst(dest_const(fst(strip_comb (concl th)))) = "SUB_BAG"
                      with Failure _ -> false))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o check (fun th -> is_forall (concl th) &&
     (try let _,b = dest_forall (concl th) in is_binary "<=" b with Failure _ -> false))) THEN
  ARITH_TAC);;

(* semantics_compile: the compilation is clos_fvs, known, clos_ticks,       *)
(* clos_letop; the semantics is preserved by each                           *)
(* (clos_fvsProof_semantics_compile, semantics_known,                       *)
(* clos_ticksProof_semantics_remove_ticks, semantics_let_op)                *)
(* the oracle condition oracle_monotonic of syntax_oracle_ok, transferred   *)
(* to the oracle after clos_fvs                                             *)
let KNOWNC1AUX_sc_monotonic = prove
 (`!xs (co:num->((val_approx)spt#C)#clos_prog).
     oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
       (SET_OF_BAG (clos_elist_globals xs)) co ==>
     oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
       (SET_OF_BAG (clos_elist_globals (clos_fvs_compile xs)))
       (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC oracle_monotonic_subset THEN
  REWRITE_TAC[o_THM; SND_pure_co; fvs_compile_uncurry; clos_fvs_compile_def;
              remove_fvs_elist_globals; SUBSET_REFL]);;

(* the hypotheses of semantics_known for the oracle after clos_fvs (HOL4: *)
(* the first impl_keep_tac of semantics_compile)                           *)
let KNOWNC1AUX_sc_conds = prove
 (`!c xs (co:num->((val_approx)spt#C)#clos_prog) eas g.
     clos_knownProof_syntax_oracle_ok c xs co g /\
     clos_known_known c (clos_fvs_compile xs) [] LN = (eas,g) ==>
     (!n. SND (SND ((pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) n)) = []) /\
     (!n. fv_max 0 (FST (SND ((pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) n)))) /\
     (!n exps aux.
        SND ((pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) n) = (exps,aux) ==>
        ALL clos_esgc_free exps) /\
     every_Fn_vs_NONE (clos_fvs_compile xs) /\
     co_every_Fn_vs_NONE (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
     oracle_gapprox_subspt (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
     oracle_state_sgc_free (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
     is_state_oracle (clos_known_compile_inc c)
       (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
     unique_set_globals (clos_fvs_compile xs)
       (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
     ALL clos_esgc_free (clos_fvs_compile xs) /\
     fv_max 0 (clos_fvs_compile xs) /\
     FST (FST ((pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) 0)) = g /\
     oracle_gapprox_disjoint g (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `oracle_gapprox_subspt (co:num->((val_approx)spt#C)#clos_prog) /\
                oracle_state_sgc_free co` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[syntax_oracle_ok_gapprox_subspt; syntax_oracle_ok_state_sgc_free];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP KNOWNC1AUX_sc_monotonic o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[clos_knownProof_syntax_oracle_ok_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                         "clos_knownProof_syntax_oracle_ok" with Failure _ -> false)) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[clos_knownProof_syntax_oracle_ok_def; clos_knownProof_syntax_ok_def;
                 FORALL_AND_THM] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                         "clos_knownProof_syntax_oracle_ok" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[o_THM; SND_pure_co; FST_pure_co; fvs_compile_uncurry; pure_co_oracle_props;
                  clos_fvs_compile_def; remove_fvs_every_Fn_vs_NONE; remove_fvs_esgc_free;
                  PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [(* fv_max of the oracle *)
    GEN_TAC THEN REWRITE_TAC[fv_max_def] THEN
    MATCH_MP_TAC fv_max_remove_fvs THEN ASM_REWRITE_TAC[];
    (* esgc_free of the oracle *)
    REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    ASM_REWRITE_TAC[remove_fvs_esgc_free];
    (* co_every_Fn_vs_NONE *)
    REWRITE_TAC[co_every_Fn_vs_NONE_def; o_THM; SND_pure_co; fvs_compile_uncurry; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    ASM_REWRITE_TAC[remove_fvs_every_Fn_vs_NONE; MAP; every_Fn_vs_NONE_def];
    (* unique_set_globals *)
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] monotonic_unique_set_globals) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_fvs_compile_def]) THEN
    ASM_REWRITE_TAC[remove_fvs_elist_globals; o_THM; SND_pure_co; fvs_compile_uncurry];
    (* fv_max of the program *)
    REWRITE_TAC[fv_max_def] THEN MATCH_MP_TAC fv_max_remove_fvs THEN ASM_REWRITE_TAC[];
    (* oracle_gapprox_disjoint *)
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] monotonic_gapprox_disjoint) THEN
    MAP_EVERY EXISTS_TAC [`c:clos_known_config`; `remove_fvs 0 xs`; `[]:val_approx list`;
      `eas:(clos_exp#val_approx)list`; `clos_elist_globals (remove_fvs 0 xs)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_fvs_compile_def]) THEN ASM_REWRITE_TAC[]]);;

(* the oracle after known has no auxiliary code *)
let KNOWNC1AUX_sc_state_co_aux = prove
 (`!c (co:num->((val_approx)spt#C)#clos_prog) n.
     SND (SND (state_co (clos_known_compile_inc c)
                 (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) n)) = []`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SND_state_co; o_THM; SND_pure_co; FST_pure_co; fvs_compile_uncurry] THEN
  REWRITE_TAC[clos_known_compile_inc_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `clos_known_known (reset_inline_factor c) (remove_fvs 0 (FST (SND
     ((co:num->((val_approx)spt#C)#clos_prog) n)))) [] (FST (FST (co n)))` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[SND]);;

(* HOL4: semantics_compile *)
let clos_knownProof_semantics_compile = prove
 (`!(ffi:(FFI)ffi_state) max_app (co:num->((val_approx)spt#C)#clos_prog)
    cc1 xs known_conf (cc:C->clos_prog->(byte list#int64 list#C)option)
    co1 known_conf' es.
     ~(clos_semantics ffi max_app FEMPTY co cc1 xs = Fail) /\
     cc1 = known_cc known_conf cc /\
     co1 = known_co known_conf co /\
     clos_known_compile known_conf xs = (known_conf',es) /\
     (IS_SOME known_conf ==>
        clos_knownProof_syntax_oracle_ok (THE known_conf) xs co
          (clos_known_config_val_approx_spt (THE known_conf')) /\
        1 <= max_app)
     ==>
     clos_semantics ffi max_app FEMPTY co1 cc es =
     clos_semantics ffi max_app FEMPTY co cc1 xs`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 SUBST1_TAC
    (CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)))) THEN
  CASES_ON `known_conf:clos_known_config option` THEN
  REWRITE_TAC[known_co_def; known_cc_def; clos_known_compile_def; IS_SOME_DEF; THE_DEF] THEN
  CAKE_REWRITE_TAC[] THENL
  [(* no clos_known: the identity compilation *)
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  DISCH_TAC THEN MATCH_MP_TAC clos_semantics_CURRY_I THEN ASM_REWRITE_TAC[];
   (* clos_known: clos_fvs, known, clos_ticks and clos_letop in turn *)
   STRIP_TAC THEN
  MP_TAC(ISPEC `clos_known_known a (clos_fvs_compile xs) [] LN` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `eas:(clos_exp#val_approx)list` (X_CHOOSE_TAC `g:val_approx spt`)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[THE_DEF; clos_known_config_INFO.ri_accfupds; K_THM]) THEN
   MP_TAC(MATCH_MP KNOWNC1AUX_sc_conds (CONJ
     (ASSUME `clos_knownProof_syntax_oracle_ok a xs
                (co:num->((val_approx)spt#C)#clos_prog) g`)
     (ASSUME `clos_known_known a (clos_fvs_compile xs) [] LN = eas,g`))) THEN
  STRIP_TAC THEN
  (* clos_fvs *)
  FIRST_ASSUM(MP_TAC o MATCH_MP clos_fvsProof_semantics_compile o check (is_neg o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `clos_knownProof_syntax_oracle_ok a xs
                   (co:num->((val_approx)spt#C)#clos_prog) g` THEN
    REWRITE_TAC[clos_knownProof_syntax_oracle_ok_def] THEN SIMP_TAC[];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th])] THEN
  (* known *)
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `max_app:num`;
    `pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o
     (co:num->((val_approx)spt#C)#clos_prog)`;
    `pure_cc (clos_ticks_compile_inc:clos_prog->clos_prog)
       (pure_cc (clos_letop_compile_inc:clos_prog->clos_prog)
          (cc:C->clos_prog->(byte list#int64 list#C)option))`;
    `a:clos_known_config`; `clos_fvs_compile xs`; `g:val_approx spt`;
    `eas:(clos_exp#val_approx)list`] semantics_known) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP clos_ticksProof_semantics_remove_ticks o
     check (is_neg o concl)) THEN
  ASM_REWRITE_TAC[KNOWNC1AUX_sc_state_co_aux] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP semantics_let_op o check (is_neg o concl)) THEN
  ASM_REWRITE_TAC[o_THM; SND_pure_co; KNOWNC1AUX_sc_state_co_aux] THEN
  ANTS_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPEC `SND (state_co (clos_known_compile_inc a)
        (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o
         (co:num->((val_approx)spt#C)#clos_prog)) n)` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[clos_ticks_compile_inc_def];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[o_ASSOC]]]);;

(* ------------------------------------------------------------------------- *)
(* preservation of every_Fn_SOME, every_Fn_vs_NONE, no_Labels, obeys_max_app *)
(* ------------------------------------------------------------------------- *)

(* HOL4: every_Fn_SOME_mk_Ticks *)
let every_Fn_SOME_mk_Ticks = prove
 (`!t tc n e. every_Fn_SOME [e] ==> every_Fn_SOME [clos_known_mk_Ticks t tc n e]`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[every_Fn_SOME_def]);;

(* HOL4: every_Fn_vs_NONE_mk_Ticks *)
let every_Fn_vs_NONE_mk_Ticks = prove
 (`!t tc n e. every_Fn_vs_NONE [e] ==> every_Fn_vs_NONE [clos_known_mk_Ticks t tc n e]`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[every_Fn_vs_NONE_def]);;

(* HOL4: val_approx_every_Fn_SOME_def [simp] (Termination: measure          *)
(* val_approx_size)                                                         *)
let val_approx_every_Fn_SOME_def = cake_def_wf
  `MEASURE val_approx_size`
  TERM_TAC
  `(val_approx_every_Fn_SOME (clos_known_Tuple _ vs) <=>
      ALL val_approx_every_Fn_SOME vs) /\
   (val_approx_every_Fn_SOME (clos_known_Clos _ _ b _) <=> every_Fn_SOME [b]) /\
   (val_approx_every_Fn_SOME _ <=> T)`;;

let val_approx_every_Fn_SOME_ind = cake_ind "val_approx_every_Fn_SOME";;

let _ = cake_add_simps [val_approx_every_Fn_SOME_def];;

(* HOL4: val_approx_every_Fn_SOME_merge *)
let val_approx_every_Fn_SOME_merge = prove
 (`!a b. val_approx_every_Fn_SOME a /\ val_approx_every_Fn_SOME b ==>
         val_approx_every_Fn_SOME (merge a b)`,
  MATCH_MP_TAC merge_ind THEN REWRITE_TAC[merge_def; val_approx_every_Fn_SOME_def] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[val_approx_every_Fn_SOME_def] THEN
  MATCH_MP_TAC CLOSP2AUX_ALL_MAP2 THEN ASM_MESON_TAC[]);;

(* HOL4: decide_inline_every_Fn_SOME *)
let decide_inline_every_Fn_SOME = prove
 (`!a b c d e.
     val_approx_every_Fn_SOME b /\ decide_inline a b c d = inlD_LetInline e ==>
     every_Fn_SOME [e]`,
  REPEAT GEN_TAC THEN CASES_ON `b:val_approx` THEN
  REWRITE_TAC[decide_inline_def; val_approx_every_Fn_SOME_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: globals_approx_every_Fn_SOME_def *)
let globals_approx_every_Fn_SOME_def = cake_def
  `globals_approx_every_Fn_SOME (g:(val_approx)spt) <=>
     !c d. lookup c g = SOME d ==> val_approx_every_Fn_SOME d`;;

let CLOSP2AUX_gFS_insert = prove
 (`!(g:val_approx spt) n v.
     globals_approx_every_Fn_SOME g /\ val_approx_every_Fn_SOME v ==>
     globals_approx_every_Fn_SOME (insert n v g)`,
  REWRITE_TAC[globals_approx_every_Fn_SOME_def; lookup_insert] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

(* HOL4: known_op_every_Fn_SOME *)
let known_op_every_Fn_SOME = prove
 (`!op x (y:(val_approx)spt) a b.
     known_op op x y = (a,b) /\
     ALL val_approx_every_Fn_SOME x /\
     globals_approx_every_Fn_SOME y
     ==> val_approx_every_Fn_SOME a /\
         globals_approx_every_Fn_SOME b`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; val_approx_every_Fn_SOME_def]) THEN
  ASM_REWRITE_TAC[val_approx_every_Fn_SOME_def] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_gFS_insert THEN
      ASM_MESON_TAC[val_approx_every_Fn_SOME_merge; globals_approx_every_Fn_SOME_def]
      THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_ALL_EL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BASICAUX_num_of_int_lt THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[globals_approx_every_Fn_SOME_def]);;

(* HOL4: clos_gen_no_inline_every_Fn_SOME *)
let clos_gen_no_inline_every_Fn_SOME = prove
 (`!(xs:(num#clos_exp)list) n x.
     ALL val_approx_every_Fn_SOME (clos_gen_noinline x n xs)`,
  SUBGOAL_THEN `!x n (xs:(num#clos_exp)list).
                  ALL val_approx_every_Fn_SOME (clos_gen_noinline x n xs)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC clos_gen_noinline_ind THEN
  REWRITE_TAC[clos_gen_noinline_def; ALL; val_approx_every_Fn_SOME_def] THEN MESON_TAC[]);;

let CLOSP2AUX_eFS_mk_Ticks = prove
 (`!t tc n e. every_Fn_SOME [clos_known_mk_Ticks t tc n e] <=> every_Fn_SOME [e]`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[every_Fn_SOME_def]);;

let CLOSP2AUX_eFS_clos_approx = prove
 (`!m loc n body. every_Fn_SOME [body] ==>
                  val_approx_every_Fn_SOME (clos_approx m loc n body)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_approx_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[val_approx_every_Fn_SOME_def]);;

let CLOSP2AUX_eFS_any_el = prove
 (`!vs n. ALL val_approx_every_Fn_SOME vs ==>
          val_approx_every_Fn_SOME (any_el n vs clos_known_Other)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[any_el_ALT] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[val_approx_every_Fn_SOME_def; CLOSP2AUX_ALL_EL]);;

let CLOSP2AUX_eFS_MEM = prove
 (`!(fns:(num#clos_exp)list) n x.
     every_Fn_SOME (MAP SND fns) /\ MEM (n,x) fns ==> every_Fn_SOME [x]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; ALL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(n:num,x:clos_exp)`) THEN
  ASM_REWRITE_TAC[SND]);;

let CLOSP2AUX_eFS_letrec = prove
 (`!(f:num#clos_exp->num#clos_exp) fns.
     (!n x. MEM (n,x) fns ==> every_Fn_SOME [SND (f (n,x))]) ==>
     every_Fn_SOME (MAP SND (MAP f fns))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; every_Fn_SOME_def; MEM] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] THEN REWRITE_TAC[ALL] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[every_Fn_SOME_EVERY]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `x:clos_exp` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:clos_exp`]) THEN
  REWRITE_TAC[ALL]);;

let CLOSP2AUX_kfs_P = `\a b c (d:val_approx spt).
   !eas g. clos_known_known a b c d = (eas,g) ==> every_Fn_SOME b ==>
     ALL val_approx_every_Fn_SOME c ==> globals_approx_every_Fn_SOME d ==>
     every_Fn_SOME (MAP FST eas) /\ ALL val_approx_every_Fn_SOME (MAP SND eas) /\
     globals_approx_every_Fn_SOME g`;;

let CLOSP2AUX_kfs_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC CLOSP2AUX_kfs_P clos_known_known_ind);;

let CLOSP2AUX_kfs_nrm = [every_Fn_SOME_def; every_Fn_SOME_APPEND; ALL; ALL_APPEND; MAP;
  MAP_APPEND; HD; PAIR_EQ; CONJUNCT1 APPEND; APPEND_NIL; val_approx_every_Fn_SOME_def;
  EVERY_REPLICATE; every_Fn_SOME_SmartOp; CLOSP2AUX_eFS_mk_Ticks; SNOC_APPEND;
  EVERY_REVERSE; clos_gen_no_inline_every_Fn_SOME; IS_SOME_DEF];;

let CLOSP2AUX_kfs_fwd = [known_op_every_Fn_SOME; decide_inline_every_Fn_SOME;
  CLOSP2AUX_eFS_clos_approx; CLOSP2AUX_eFS_any_el; val_approx_every_Fn_SOME_merge];;

let CLOSP2AUX_KFS_PROVE_TAC : tactic = ASM_REWRITE_TAC CLOSP2AUX_kfs_nrm THEN NO_TAC;;

(* the Letrec case: the new function bodies *)
let CLOSP2AUX_KFS_LETREC_TAC : tactic = fun (asl,w as gl) ->
  let pat = `every_Fn_SOME (MAP SND (MAP (f:num#clos_exp->num#clos_exp) fns))` in
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let inner = rand (rand t) in
  let ff = rand(rator inner) and fns = rand inner in
  let ih_tac : tactic = fun (asl,w as g) ->
    let kt = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "clos_known_known"
                                 with Failure _ -> false) w in
    let args = snd(strip_comb kt) in
    let xx = hd (dest_list (el 1 args)) and nv = el 2 args in
    let memth = snd (find (fun (_,th) -> try fst(dest_const(fst(strip_comb (concl th)))) = "MEM"
                                         with Failure _ -> false) asl) in
    let nn = fst(dest_pair(lhand(concl memth))) in
    (MP_TAC(ISPECL [el 0 args; xx; nv; el 3 args] known_sing) THEN
     DISCH_THEN(X_CHOOSE_THEN `ee:clos_exp` (X_CHOOSE_THEN `aa:val_approx`
       (X_CHOOSE_THEN `gg:val_approx spt` ASSUME_TAC))) THEN
     FIRST_X_ASSUM(fun kth -> if is_eq (concl kth) && lhs (concl kth) = kt then
       FIRST_ASSUM(fun ih -> try
         MP_TAC(MATCH_MP (MATCH_MP (SPECL [nn; xx; nv] ih) memth) kth)
         with Failure _ -> NO_TAC) THEN REWRITE_TAC[kth; MAP; HD; FST]
       else NO_TAC) THEN
     REWRITE_TAC CLOSP2AUX_kfs_nrm THEN ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[CLOSP2AUX_eFS_MEM]; SIMP_TAC[]]) g in
  (MP_TAC(ISPECL [ff; fns] CLOSP2AUX_eFS_letrec) THEN ANTS_TAC THENL
    [MAP_EVERY X_GEN_TAC [`nn:num`; `xx:clos_exp`] THEN DISCH_TAC THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN CAKE_REWRITE_TAC[SND] THEN ih_tac;
     DISCH_TAC THEN ASM_REWRITE_TAC[]]) gl;;

let CLOSP2AUX_KFS_CASE_TAC : tactic =
  CLOSP2AUX_KN_UNFOLD_TAC THEN REPEAT DISCH_TAC THEN CLOSP2AUX_KN_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kfs_nrm) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  CLOSP2AUX_SATP_GEN_TAC ["ALL"; "every_Fn_SOME"; "val_approx_every_Fn_SOME";
                          "globals_approx_every_Fn_SOME"]
    CLOSP2AUX_KFS_PROVE_TAC CLOSP2AUX_kfs_fwd CLOSP2AUX_kfs_nrm 4 THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kfs_nrm) THEN
  REWRITE_TAC CLOSP2AUX_kfs_nrm THEN ASM_REWRITE_TAC[] THEN
  TRY CLOSP2AUX_KFS_LETREC_TAC;;

let CLOSP2AUX_kfs_thm =
  MP CLOSP2AUX_kfs_ind
    (end_itlist CONJ (map (fun t -> prove(t, CLOSP2AUX_KFS_CASE_TAC))
                          (conjuncts (lhand (concl CLOSP2AUX_kfs_ind)))));;

(* HOL4: known_every_Fn_SOME *)
let known_every_Fn_SOME = prove
 (`!a b c (d:(val_approx)spt).
     every_Fn_SOME b /\ ALL val_approx_every_Fn_SOME c /\
     globals_approx_every_Fn_SOME d
     ==>
     every_Fn_SOME (MAP FST (FST (clos_known_known a b c d))) /\
     ALL val_approx_every_Fn_SOME (MAP SND (FST (clos_known_known a b c d))) /\
     globals_approx_every_Fn_SOME (SND (clos_known_known a b c d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:clos_known_config`; `b:clos_exp list`; `c:val_approx list`;
                `d:val_approx spt`] CLOSP2AUX_kfs_thm) THEN
  DISCH_THEN(MP_TAC o SPECL [`FST (clos_known_known a b c (d:val_approx spt))`;
                             `SND (clos_known_known a b c (d:val_approx spt))`]) THEN
  ASM_REWRITE_TAC[PAIR]);;

(* HOL4: val_approx_every_Fn_vs_NONE_def [simp] (Termination: measure      *)
(* val_approx_size)                                                         *)
let val_approx_every_Fn_vs_NONE_def = cake_def_wf
  `MEASURE val_approx_size`
  TERM_TAC
  `(val_approx_every_Fn_vs_NONE (clos_known_Tuple _ vs) <=>
      ALL val_approx_every_Fn_vs_NONE vs) /\
   (val_approx_every_Fn_vs_NONE (clos_known_Clos _ _ b _) <=> every_Fn_vs_NONE [b]) /\
   (val_approx_every_Fn_vs_NONE _ <=> T)`;;

let val_approx_every_Fn_vs_NONE_ind = cake_ind "val_approx_every_Fn_vs_NONE";;

let _ = cake_add_simps [val_approx_every_Fn_vs_NONE_def];;

(* HOL4: val_approx_every_Fn_vs_NONE_merge *)
let val_approx_every_Fn_vs_NONE_merge = prove
 (`!a b. val_approx_every_Fn_vs_NONE a /\ val_approx_every_Fn_vs_NONE b ==>
         val_approx_every_Fn_vs_NONE (merge a b)`,
  MATCH_MP_TAC merge_ind THEN REWRITE_TAC[merge_def; val_approx_every_Fn_vs_NONE_def] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[val_approx_every_Fn_vs_NONE_def] THEN
  MATCH_MP_TAC CLOSP2AUX_ALL_MAP2 THEN ASM_MESON_TAC[]);;

(* HOL4: decide_inline_every_Fn_vs_NONE *)
let decide_inline_every_Fn_vs_NONE = prove
 (`!a b c d e.
     val_approx_every_Fn_vs_NONE b /\ decide_inline a b c d = inlD_LetInline e ==>
     every_Fn_vs_NONE [e]`,
  REPEAT GEN_TAC THEN CASES_ON `b:val_approx` THEN
  REWRITE_TAC[decide_inline_def; val_approx_every_Fn_vs_NONE_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: globals_approx_every_Fn_vs_NONE_def *)
let globals_approx_every_Fn_vs_NONE_def = cake_def
  `globals_approx_every_Fn_vs_NONE (g:(val_approx)spt) <=>
     !c d. lookup c g = SOME d ==> val_approx_every_Fn_vs_NONE d`;;

let CLOSP2AUX_gFV_insert = prove
 (`!(g:val_approx spt) n v.
     globals_approx_every_Fn_vs_NONE g /\ val_approx_every_Fn_vs_NONE v ==>
     globals_approx_every_Fn_vs_NONE (insert n v g)`,
  REWRITE_TAC[globals_approx_every_Fn_vs_NONE_def; lookup_insert] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

(* HOL4: known_op_every_Fn_vs_NONE *)
let known_op_every_Fn_vs_NONE = prove
 (`!op x (y:(val_approx)spt) a b.
     known_op op x y = (a,b) /\
     ALL val_approx_every_Fn_vs_NONE x /\
     globals_approx_every_Fn_vs_NONE y
     ==> val_approx_every_Fn_vs_NONE a /\
         globals_approx_every_Fn_vs_NONE b`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; val_approx_every_Fn_vs_NONE_def]) THEN
  ASM_REWRITE_TAC[val_approx_every_Fn_vs_NONE_def] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_gFV_insert THEN
      ASM_MESON_TAC[val_approx_every_Fn_vs_NONE_merge; globals_approx_every_Fn_vs_NONE_def]
      THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_ALL_EL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BASICAUX_num_of_int_lt THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[globals_approx_every_Fn_vs_NONE_def]);;

(* HOL4: clos_gen_no_inline_every_Fn_vs_NONE *)
let clos_gen_no_inline_every_Fn_vs_NONE = prove
 (`!(xs:(num#clos_exp)list) n x.
     ALL val_approx_every_Fn_vs_NONE (clos_gen_noinline x n xs)`,
  SUBGOAL_THEN `!x n (xs:(num#clos_exp)list).
                  ALL val_approx_every_Fn_vs_NONE (clos_gen_noinline x n xs)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC clos_gen_noinline_ind THEN
  REWRITE_TAC[clos_gen_noinline_def; ALL; val_approx_every_Fn_vs_NONE_def] THEN MESON_TAC[]);;

let CLOSP2AUX_eFV_mk_Ticks = prove
 (`!t tc n e. every_Fn_vs_NONE [clos_known_mk_Ticks t tc n e] <=> every_Fn_vs_NONE [e]`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[every_Fn_vs_NONE_def]);;

let CLOSP2AUX_eFV_clos_approx = prove
 (`!m loc n body. every_Fn_vs_NONE [body] ==>
                  val_approx_every_Fn_vs_NONE (clos_approx m loc n body)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_approx_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[val_approx_every_Fn_vs_NONE_def]);;

let CLOSP2AUX_eFV_any_el = prove
 (`!vs n. ALL val_approx_every_Fn_vs_NONE vs ==>
          val_approx_every_Fn_vs_NONE (any_el n vs clos_known_Other)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[any_el_ALT] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[val_approx_every_Fn_vs_NONE_def; CLOSP2AUX_ALL_EL]);;

let CLOSP2AUX_eFV_MEM = prove
 (`!(fns:(num#clos_exp)list) n x.
     every_Fn_vs_NONE (MAP SND fns) /\ MEM (n,x) fns ==> every_Fn_vs_NONE [x]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; ALL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(n:num,x:clos_exp)`) THEN
  ASM_REWRITE_TAC[SND]);;

let CLOSP2AUX_eFV_letrec = prove
 (`!(f:num#clos_exp->num#clos_exp) fns.
     (!n x. MEM (n,x) fns ==> every_Fn_vs_NONE [SND (f (n,x))]) ==>
     every_Fn_vs_NONE (MAP SND (MAP f fns))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; every_Fn_vs_NONE_def; MEM] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN REWRITE_TAC[ALL] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[every_Fn_vs_NONE_EVERY]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `x:clos_exp` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:clos_exp`]) THEN
  REWRITE_TAC[ALL]);;

let CLOSP2AUX_kfv_P = `\a b c (d:val_approx spt).
   !eas g. clos_known_known a b c d = (eas,g) ==> every_Fn_vs_NONE b ==>
     ALL val_approx_every_Fn_vs_NONE c ==> globals_approx_every_Fn_vs_NONE d ==>
     every_Fn_vs_NONE (MAP FST eas) /\ ALL val_approx_every_Fn_vs_NONE (MAP SND eas) /\
     globals_approx_every_Fn_vs_NONE g`;;

let CLOSP2AUX_kfv_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC CLOSP2AUX_kfv_P clos_known_known_ind);;

let CLOSP2AUX_kfv_nrm = [every_Fn_vs_NONE_def; every_Fn_vs_NONE_APPEND; ALL; ALL_APPEND; MAP;
  MAP_APPEND; HD; PAIR_EQ; CONJUNCT1 APPEND; APPEND_NIL; val_approx_every_Fn_vs_NONE_def;
  EVERY_REPLICATE; CLOSP2AUX_eFV_mk_Ticks; SNOC_APPEND;
  EVERY_REVERSE; clos_gen_no_inline_every_Fn_vs_NONE; IS_NONE_DEF];;

let CLOSP2AUX_kfv_fwd = [known_op_every_Fn_vs_NONE; decide_inline_every_Fn_vs_NONE;
  every_Fn_vs_NONE_SmartOp;
  CLOSP2AUX_eFV_clos_approx; CLOSP2AUX_eFV_any_el; val_approx_every_Fn_vs_NONE_merge];;

let CLOSP2AUX_KFV_PROVE_TAC : tactic = ASM_REWRITE_TAC CLOSP2AUX_kfv_nrm THEN NO_TAC;;

(* the Letrec case: the new function bodies *)
let CLOSP2AUX_KFV_LETREC_TAC : tactic = fun (asl,w as gl) ->
  let pat = `every_Fn_vs_NONE (MAP SND (MAP (f:num#clos_exp->num#clos_exp) fns))` in
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let inner = rand (rand t) in
  let ff = rand(rator inner) and fns = rand inner in
  let ih_tac : tactic = fun (asl,w as g) ->
    let kt = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "clos_known_known"
                                 with Failure _ -> false) w in
    let args = snd(strip_comb kt) in
    let xx = hd (dest_list (el 1 args)) and nv = el 2 args in
    let memth = snd (find (fun (_,th) -> try fst(dest_const(fst(strip_comb (concl th)))) = "MEM"
                                         with Failure _ -> false) asl) in
    let nn = fst(dest_pair(lhand(concl memth))) in
    (MP_TAC(ISPECL [el 0 args; xx; nv; el 3 args] known_sing) THEN
     DISCH_THEN(X_CHOOSE_THEN `ee:clos_exp` (X_CHOOSE_THEN `aa:val_approx`
       (X_CHOOSE_THEN `gg:val_approx spt` ASSUME_TAC))) THEN
     FIRST_X_ASSUM(fun kth -> if is_eq (concl kth) && lhs (concl kth) = kt then
       FIRST_ASSUM(fun ih -> try
         MP_TAC(MATCH_MP (MATCH_MP (SPECL [nn; xx; nv] ih) memth) kth)
         with Failure _ -> NO_TAC) THEN REWRITE_TAC[kth; MAP; HD; FST]
       else NO_TAC) THEN
     REWRITE_TAC CLOSP2AUX_kfv_nrm THEN ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[CLOSP2AUX_eFV_MEM]; SIMP_TAC[]]) g in
  (MP_TAC(ISPECL [ff; fns] CLOSP2AUX_eFV_letrec) THEN ANTS_TAC THENL
    [MAP_EVERY X_GEN_TAC [`nn:num`; `xx:clos_exp`] THEN DISCH_TAC THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN CAKE_REWRITE_TAC[SND] THEN ih_tac;
     DISCH_TAC THEN ASM_REWRITE_TAC[]]) gl;;

let CLOSP2AUX_KFV_CASE_TAC : tactic =
  CLOSP2AUX_KN_UNFOLD_TAC THEN REPEAT DISCH_TAC THEN CLOSP2AUX_KN_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kfv_nrm) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  CLOSP2AUX_SATP_GEN_TAC ["ALL"; "every_Fn_vs_NONE"; "val_approx_every_Fn_vs_NONE";
                          "globals_approx_every_Fn_vs_NONE"]
    CLOSP2AUX_KFV_PROVE_TAC CLOSP2AUX_kfv_fwd CLOSP2AUX_kfv_nrm 4 THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kfv_nrm) THEN
  REWRITE_TAC CLOSP2AUX_kfv_nrm THEN ASM_REWRITE_TAC[] THEN
  TRY CLOSP2AUX_KFV_LETREC_TAC;;

let CLOSP2AUX_kfv_thm =
  MP CLOSP2AUX_kfv_ind
    (end_itlist CONJ (map (fun t -> prove(t, CLOSP2AUX_KFV_CASE_TAC))
                          (conjuncts (lhand (concl CLOSP2AUX_kfv_ind)))));;

(* HOL4: known_every_Fn_vs_NONE *)
let known_every_Fn_vs_NONE = prove
 (`!a b c (d:(val_approx)spt).
     every_Fn_vs_NONE b /\ ALL val_approx_every_Fn_vs_NONE c /\
     globals_approx_every_Fn_vs_NONE d
     ==>
     every_Fn_vs_NONE (MAP FST (FST (clos_known_known a b c d))) /\
     ALL val_approx_every_Fn_vs_NONE (MAP SND (FST (clos_known_known a b c d))) /\
     globals_approx_every_Fn_vs_NONE (SND (clos_known_known a b c d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:clos_known_config`; `b:clos_exp list`; `c:val_approx list`;
                `d:val_approx spt`] CLOSP2AUX_kfv_thm) THEN
  DISCH_THEN(MP_TAC o SPECL [`FST (clos_known_known a b c (d:val_approx spt))`;
                             `SND (clos_known_known a b c (d:val_approx spt))`]) THEN
  ASM_REWRITE_TAC[PAIR]);;

(* HOL4: val_approx_no_Labels_def (Termination: measure val_approx_size) *)
let val_approx_no_Labels_def = cake_def_wf
  `MEASURE val_approx_size`
  TERM_TAC
  `(val_approx_no_Labels (ClosNoInline m n) <=> T) /\
   (val_approx_no_Labels (clos_known_Clos m n e s) <=> no_Labels e) /\
   (val_approx_no_Labels (clos_known_Tuple tag vas) <=>
      ALL val_approx_no_Labels vas) /\
   (val_approx_no_Labels _ <=> T)`;;

let val_approx_no_Labels_ind = cake_ind "val_approx_no_Labels";;

(* HOL4: val_approx_no_Labels_simp [local,simp]: the clauses of             *)
(* val_approx_no_Labels_def that are not trivial; all of them here.         *)
let val_approx_no_Labels_simp = val_approx_no_Labels_def;;

let _ = cake_add_simps [val_approx_no_Labels_simp];;

(* HOL4: decide_inline_no_Labels *)
let decide_inline_no_Labels = prove
 (`!a b c d e.
     val_approx_no_Labels b /\ decide_inline a b c d = inlD_LetInline e ==>
     no_Labels e`,
  REPEAT GEN_TAC THEN CASES_ON `b:val_approx` THEN
  REWRITE_TAC[decide_inline_def; val_approx_no_Labels_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: globals_approx_no_Labels_def *)
let globals_approx_no_Labels_def = cake_def
  `globals_approx_no_Labels (g:(val_approx)spt) <=>
     !c d. lookup c g = SOME d ==> val_approx_no_Labels d`;;

(* HOL4: val_approx_no_Labels_merge *)
let val_approx_no_Labels_merge = prove
 (`!a b. val_approx_no_Labels a /\ val_approx_no_Labels b ==>
         val_approx_no_Labels (merge a b)`,
  MATCH_MP_TAC merge_ind THEN REWRITE_TAC[merge_def; val_approx_no_Labels_def] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[val_approx_no_Labels_def] THEN
  MATCH_MP_TAC CLOSP2AUX_ALL_MAP2 THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_gNL_insert = prove
 (`!(g:val_approx spt) n v.
     globals_approx_no_Labels g /\ val_approx_no_Labels v ==>
     globals_approx_no_Labels (insert n v g)`,
  REWRITE_TAC[globals_approx_no_Labels_def; lookup_insert] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

(* HOL4: known_op_no_Labels *)
let known_op_no_Labels = prove
 (`!op x (y:(val_approx)spt) a b.
     known_op op x y = (a,b) /\
     ALL val_approx_no_Labels x /\
     globals_approx_no_Labels y
     ==> val_approx_no_Labels a /\
         globals_approx_no_Labels b`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; val_approx_no_Labels_def]) THEN
  ASM_REWRITE_TAC[val_approx_no_Labels_def] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_gNL_insert THEN
      ASM_MESON_TAC[val_approx_no_Labels_merge; globals_approx_no_Labels_def]
      THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_ALL_EL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BASICAUX_num_of_int_lt THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[globals_approx_no_Labels_def]);;

(* HOL4: no_Labels_mk_Ticks *)
let no_Labels_mk_Ticks = prove
 (`!t tc n e. no_Labels e ==> no_Labels (clos_known_mk_Ticks t tc n e)`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[no_Labels_def]);;

(* HOL4: clos_gen_no_inline_no_Labels *)
let clos_gen_no_inline_no_Labels = prove
 (`!(xs:(num#clos_exp)list) n x.
     ALL val_approx_no_Labels (clos_gen_noinline x n xs)`,
  SUBGOAL_THEN `!x n (xs:(num#clos_exp)list).
                  ALL val_approx_no_Labels (clos_gen_noinline x n xs)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC clos_gen_noinline_ind THEN
  REWRITE_TAC[clos_gen_noinline_def; ALL; val_approx_no_Labels_def] THEN MESON_TAC[]);;

let CLOSP2AUX_nL_mk_Ticks = prove
 (`!t tc n e. no_Labels (clos_known_mk_Ticks t tc n e) <=> no_Labels e`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[no_Labels_def]);;

let CLOSP2AUX_nL_clos_approx = prove
 (`!m loc n body. no_Labels body ==>
                  val_approx_no_Labels (clos_approx m loc n body)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_approx_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[val_approx_no_Labels_def]);;

let CLOSP2AUX_nL_any_el = prove
 (`!vs n. ALL val_approx_no_Labels vs ==>
          val_approx_no_Labels (any_el n vs clos_known_Other)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[any_el_ALT] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[val_approx_no_Labels_def; CLOSP2AUX_ALL_EL]);;

let CLOSP2AUX_nL_MEM = prove
 (`!(fns:(num#clos_exp)list) n x.
     ALL no_Labels (MAP SND fns) /\ MEM (n,x) fns ==> no_Labels x`,
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(n:num,x:clos_exp)`) THEN ASM_REWRITE_TAC[SND]);;

let CLOSP2AUX_nL_letrec = prove
 (`!(f:num#clos_exp->num#clos_exp) fns.
     (!n x. MEM (n,x) fns ==> no_Labels (SND (f (n,x)))) ==>
     ALL no_Labels (MAP SND (MAP f fns))`,
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; FORALL_PAIR_THM] THEN MESON_TAC[]);;

let CLOSP2AUX_knl_P = `\a b c (d:val_approx spt).
   !eas g. clos_known_known a b c d = (eas,g) ==> ALL no_Labels b ==>
     ALL val_approx_no_Labels c ==> globals_approx_no_Labels d ==>
     ALL no_Labels (MAP FST eas) /\ ALL val_approx_no_Labels (MAP SND eas) /\
     globals_approx_no_Labels g`;;

let CLOSP2AUX_knl_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC CLOSP2AUX_knl_P clos_known_known_ind);;

let CLOSP2AUX_knl_nrm = [no_Labels_def; ALL; ALL_APPEND; MAP; MAP_APPEND; HD; PAIR_EQ;
  CONJUNCT1 APPEND; APPEND_NIL; val_approx_no_Labels_def; EVERY_REPLICATE; no_Labels_SmartOp;
  CLOSP2AUX_nL_mk_Ticks; SNOC_APPEND; EVERY_REVERSE; clos_gen_no_inline_no_Labels;
  distinctness "clos_op"];;

let CLOSP2AUX_knl_fwd = [known_op_no_Labels; decide_inline_no_Labels;
  CLOSP2AUX_nL_clos_approx; CLOSP2AUX_nL_any_el; val_approx_no_Labels_merge];;

let CLOSP2AUX_KNL_PROVE_TAC : tactic = ASM_REWRITE_TAC CLOSP2AUX_knl_nrm THEN NO_TAC;;

let CLOSP2AUX_KNL_LETREC_TAC : tactic = fun (asl,w as gl) ->
  let pat = `ALL no_Labels (MAP SND (MAP (f:num#clos_exp->num#clos_exp) fns))` in
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let inner = rand (rand t) in
  let ff = rand(rator inner) and fns = rand inner in
  let ih_tac : tactic = fun (asl,w as g) ->
    let kt = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "clos_known_known"
                                 with Failure _ -> false) w in
    let args = snd(strip_comb kt) in
    let xx = hd (dest_list (el 1 args)) and nv = el 2 args in
    let memth = snd (find (fun (_,th) -> try fst(dest_const(fst(strip_comb (concl th)))) = "MEM"
                                         with Failure _ -> false) asl) in
    let nn = fst(dest_pair(lhand(concl memth))) in
    (MP_TAC(ISPECL [el 0 args; xx; nv; el 3 args] known_sing) THEN
     DISCH_THEN(X_CHOOSE_THEN `ee:clos_exp` (X_CHOOSE_THEN `aa:val_approx`
       (X_CHOOSE_THEN `gg:val_approx spt` ASSUME_TAC))) THEN
     FIRST_X_ASSUM(fun kth -> if is_eq (concl kth) && lhs (concl kth) = kt then
       FIRST_ASSUM(fun ih -> try
         MP_TAC(MATCH_MP (MATCH_MP (SPECL [nn; xx; nv] ih) memth) kth)
         with Failure _ -> NO_TAC) THEN REWRITE_TAC[kth; MAP; HD; FST]
       else NO_TAC) THEN
     REWRITE_TAC CLOSP2AUX_knl_nrm THEN ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[CLOSP2AUX_nL_MEM]; SIMP_TAC[]]) g in
  (MP_TAC(ISPECL [ff; fns] CLOSP2AUX_nL_letrec) THEN ANTS_TAC THENL
    [MAP_EVERY X_GEN_TAC [`nn:num`; `xx:clos_exp`] THEN DISCH_TAC THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN CAKE_REWRITE_TAC[SND] THEN ih_tac;
     DISCH_TAC THEN ASM_REWRITE_TAC[]]) gl;;

let CLOSP2AUX_KNL_CASE_TAC : tactic =
  CLOSP2AUX_KN_UNFOLD_TAC THEN REPEAT DISCH_TAC THEN CLOSP2AUX_KN_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_knl_nrm) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  CLOSP2AUX_SATP_GEN_TAC ["ALL"; "no_Labels"; "val_approx_no_Labels";
                          "globals_approx_no_Labels"]
    CLOSP2AUX_KNL_PROVE_TAC CLOSP2AUX_knl_fwd CLOSP2AUX_knl_nrm 4 THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_knl_nrm) THEN
  REWRITE_TAC CLOSP2AUX_knl_nrm THEN ASM_REWRITE_TAC[] THEN
  TRY CLOSP2AUX_KNL_LETREC_TAC;;

let CLOSP2AUX_knl_thm =
  MP CLOSP2AUX_knl_ind
    (end_itlist CONJ (map (fun t -> prove(t, CLOSP2AUX_KNL_CASE_TAC))
                          (conjuncts (lhand (concl CLOSP2AUX_knl_ind)))));;

(* HOL4: known_no_Labels *)
let known_no_Labels = prove
 (`!a b c (d:(val_approx)spt).
     ALL no_Labels b /\ ALL val_approx_no_Labels c /\
     globals_approx_no_Labels d
     ==>
     ALL no_Labels (MAP FST (FST (clos_known_known a b c d))) /\
     ALL val_approx_no_Labels (MAP SND (FST (clos_known_known a b c d))) /\
     globals_approx_no_Labels (SND (clos_known_known a b c d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:clos_known_config`; `b:clos_exp list`; `c:val_approx list`;
                `d:val_approx spt`] CLOSP2AUX_knl_thm) THEN
  DISCH_THEN(MP_TAC o SPECL [`FST (clos_known_known a b c (d:val_approx spt))`;
                             `SND (clos_known_known a b c (d:val_approx spt))`]) THEN
  ASM_REWRITE_TAC[PAIR]);;

(* HOL4: compile_no_Labels *)
let compile_no_Labels = prove
 (`!c xs res ys.
     clos_known_compile (SOME c) xs = (res,ys) /\ ALL no_Labels xs ==>
     ?c1. res = SOME c1 /\ ALL no_Labels ys /\
          globals_approx_no_Labels (clos_known_config_val_approx_spt c1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_known_compile_def; LET_DEF; LET_END_DEF; pair_CASE_def;
              PAIR_EQ; clos_fvs_compile_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[injectivity "option"; UNWIND_THM1; clos_known_config_INFO.ri_accfupds;
              K_THM] THEN
  MP_TAC(SPECL [`c:clos_known_config`; `remove_fvs 0 xs`; `[]:val_approx list`;
                `LN:val_approx spt`] known_no_Labels) THEN
  ASM_REWRITE_TAC[remove_fvs_no_Labels; ALL; globals_approx_no_Labels_def; lookup_rwts;
                  distinctness "option"] THEN
  MESON_TAC[remove_ticks_no_Labels; let_op_no_Labels]);;

(* HOL4: val_approx_obeys_max_app_def (Termination: measure                 *)
(* (val_approx_size o SND))                                                 *)
let val_approx_obeys_max_app_def = cake_def_wf
  `MEASURE (\p:num#val_approx. val_approx_size (SND p))`
  TERM_TAC
  `(val_approx_obeys_max_app k (ClosNoInline m n) <=> T) /\
   (val_approx_obeys_max_app k (clos_known_Clos m n e s) <=> obeys_max_app k e) /\
   (val_approx_obeys_max_app k (clos_known_Tuple tag vas) <=>
      ALL (val_approx_obeys_max_app k) vas) /\
   (val_approx_obeys_max_app k _ <=> T)`;;

let val_approx_obeys_max_app_ind = cake_ind "val_approx_obeys_max_app";;

(* HOL4: decide_inline_obeys_max_app *)
let decide_inline_obeys_max_app = prove
 (`!k a b c d e.
     val_approx_obeys_max_app k b /\ decide_inline a b c d = inlD_LetInline e ==>
     obeys_max_app k e`,
  REPEAT GEN_TAC THEN CASES_ON `b:val_approx` THEN
  REWRITE_TAC[decide_inline_def; val_approx_obeys_max_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: globals_approx_obeys_max_app_def *)
let globals_approx_obeys_max_app_def = cake_def
  `globals_approx_obeys_max_app k (g:(val_approx)spt) <=>
     !c d. lookup c g = SOME d ==> val_approx_obeys_max_app k d`;;

(* HOL4: val_approx_obeys_max_app_merge *)
let val_approx_obeys_max_app_merge = prove
 (`!k a b. val_approx_obeys_max_app k a /\ val_approx_obeys_max_app k b ==>
           val_approx_obeys_max_app k (merge a b)`,
  GEN_TAC THEN
  MATCH_MP_TAC merge_ind THEN REWRITE_TAC[merge_def; val_approx_obeys_max_app_def] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[val_approx_obeys_max_app_def] THEN
  MATCH_MP_TAC CLOSP2AUX_ALL_MAP2 THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_gOM_insert = prove
 (`!k (g:val_approx spt) n v.
     globals_approx_obeys_max_app k g /\ val_approx_obeys_max_app k v ==>
     globals_approx_obeys_max_app k (insert n v g)`,
  REWRITE_TAC[globals_approx_obeys_max_app_def; lookup_insert] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

(* HOL4: known_op_obeys_max_app *)
let known_op_obeys_max_app = prove
 (`!k op x (y:(val_approx)spt) a b.
     known_op op x y = (a,b) /\
     ALL (val_approx_obeys_max_app k) x /\
     globals_approx_obeys_max_app k y
     ==> val_approx_obeys_max_app k a /\
         globals_approx_obeys_max_app k b`,
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; val_approx_obeys_max_app_def]) THEN
  ASM_REWRITE_TAC[val_approx_obeys_max_app_def] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_gOM_insert THEN
      ASM_MESON_TAC[val_approx_obeys_max_app_merge; globals_approx_obeys_max_app_def]
      THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_ALL_EL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BASICAUX_num_of_int_lt THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[globals_approx_obeys_max_app_def]);;

(* HOL4: obeys_max_app_mk_Ticks *)
let obeys_max_app_mk_Ticks = prove
 (`!k t tc n e. obeys_max_app k e ==> obeys_max_app k (clos_known_mk_Ticks t tc n e)`,
  GEN_TAC THEN MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[obeys_max_app_def]);;

(* HOL4: clos_gen_no_inline_obeys_max_app *)
let clos_gen_no_inline_obeys_max_app = prove
 (`!k (xs:(num#clos_exp)list) n x.
     ALL (val_approx_obeys_max_app k) (clos_gen_noinline x n xs)`,
  GEN_TAC THEN
  SUBGOAL_THEN `!x n (xs:(num#clos_exp)list).
                  ALL (val_approx_obeys_max_app k) (clos_gen_noinline x n xs)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC clos_gen_noinline_ind THEN
  REWRITE_TAC[clos_gen_noinline_def; ALL; val_approx_obeys_max_app_def] THEN MESON_TAC[]);;

(* HOL4: known_IMP_LENGTH *)
let known_IMP_LENGTH = prove
 (`!c xs vs (g:(val_approx)spt) ys g'.
     clos_known_known c xs vs g = (ys,g') ==> LENGTH ys = LENGTH xs`,
  MATCH_ACCEPT_TAC known_LENGTH_EQ_E);;

let CLOSP2AUX_oM_mk_Ticks = prove
 (`!k t tc n e. obeys_max_app k (clos_known_mk_Ticks t tc n e) <=> obeys_max_app k e`,
  GEN_TAC THEN
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[obeys_max_app_def]);;

let CLOSP2AUX_oM_clos_approx = prove
 (`!k m loc n body. obeys_max_app k body ==>
                    val_approx_obeys_max_app k (clos_approx m loc n body)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_approx_def] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[val_approx_obeys_max_app_def]);;

let CLOSP2AUX_oM_any_el = prove
 (`!k vs n. ALL (val_approx_obeys_max_app k) vs ==>
            val_approx_obeys_max_app k (any_el n vs clos_known_Other)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[any_el_ALT] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[val_approx_obeys_max_app_def; CLOSP2AUX_ALL_EL]);;

let CLOSP2AUX_oM_MEM = prove
 (`!k (fns:(num#clos_exp)list) n x.
     ALL (obeys_max_app k) (MAP SND fns) /\ MEM (n,x) fns ==> obeys_max_app k x`,
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(n:num,x:clos_exp)`) THEN ASM_REWRITE_TAC[SND]);;

let CLOSP2AUX_oM_letrec = prove
 (`!k (f:num#clos_exp->num#clos_exp) fns.
     (!n x. MEM (n,x) fns ==> obeys_max_app k (SND (f (n,x)))) ==>
     ALL (obeys_max_app k) (MAP SND (MAP f fns))`,
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM; FORALL_PAIR_THM] THEN MESON_TAC[]);;

let CLOSP2AUX_kom_P = `\a b c (d:val_approx spt).
   !k eas g. clos_known_known a b c d = (eas,g) ==> ALL (obeys_max_app k) b ==>
     ALL (val_approx_obeys_max_app k) c ==> globals_approx_obeys_max_app k d ==>
     ALL (obeys_max_app k) (MAP FST eas) /\ ALL (val_approx_obeys_max_app k) (MAP SND eas) /\
     globals_approx_obeys_max_app k g`;;

let CLOSP2AUX_kom_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPEC CLOSP2AUX_kom_P clos_known_known_ind);;

let CLOSP2AUX_kom_nrm = [obeys_max_app_def; ALL; ALL_APPEND; MAP; MAP_APPEND; HD; PAIR_EQ;
  CONJUNCT1 APPEND; APPEND_NIL; val_approx_obeys_max_app_def; EVERY_REPLICATE;
  CLOSP2AUX_oM_mk_Ticks; SNOC_APPEND; EVERY_REVERSE; clos_gen_no_inline_obeys_max_app;
  LENGTH_MAP];;

let CLOSP2AUX_kom_fwd = [known_op_obeys_max_app; decide_inline_obeys_max_app;
  CLOSP2AUX_oM_clos_approx; CLOSP2AUX_oM_any_el; val_approx_obeys_max_app_merge;
  GEN_ALL obeys_max_app_SmartOp; known_IMP_LENGTH];;

let CLOSP2AUX_KOM_PROVE_TAC : tactic = ASM_REWRITE_TAC CLOSP2AUX_kom_nrm THEN NO_TAC;;

let CLOSP2AUX_KOM_LETREC_TAC : tactic = fun (asl,w as gl) ->
  let pat = `ALL (obeys_max_app k) (MAP SND (MAP (f:num#clos_exp->num#clos_exp) fns))` in
  let t = find_term (fun t -> can (term_match [] pat) t) w in
  let inner = rand (rand t) in
  let kk = rand(rand(rator t)) in
  let ff = rand(rator inner) and fns = rand inner in
  let ih_tac : tactic = fun (asl,w as g) ->
    let kt = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "clos_known_known"
                                 with Failure _ -> false) w in
    let args = snd(strip_comb kt) in
    let xx = hd (dest_list (el 1 args)) and nv = el 2 args in
    let memth = snd (find (fun (_,th) -> try fst(dest_const(fst(strip_comb (concl th)))) = "MEM"
                                         with Failure _ -> false) asl) in
    let nn = fst(dest_pair(lhand(concl memth))) in
    (MP_TAC(ISPECL [el 0 args; xx; nv; el 3 args] known_sing) THEN
     DISCH_THEN(X_CHOOSE_THEN `ee:clos_exp` (X_CHOOSE_THEN `aa:val_approx`
       (X_CHOOSE_THEN `gg:val_approx spt` ASSUME_TAC))) THEN
     FIRST_X_ASSUM(fun kth -> if is_eq (concl kth) && lhs (concl kth) = kt then
       FIRST_ASSUM(fun ih -> try
         MP_TAC(MATCH_MP (SPEC kk (MATCH_MP (SPECL [nn; xx; nv] ih) memth)) kth)
         with Failure _ -> NO_TAC) THEN REWRITE_TAC[kth; MAP; HD; FST]
       else NO_TAC) THEN
     REWRITE_TAC CLOSP2AUX_kom_nrm THEN ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[CLOSP2AUX_oM_MEM]; SIMP_TAC[]]) g in
  (MP_TAC(ISPECL [kk; ff; fns] CLOSP2AUX_oM_letrec) THEN ANTS_TAC THENL
    [MAP_EVERY X_GEN_TAC [`nn:num`; `xx:clos_exp`] THEN DISCH_TAC THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN CAKE_REWRITE_TAC[SND] THEN ih_tac;
     DISCH_TAC THEN ASM_REWRITE_TAC[]]) gl;;

let CLOSP2AUX_KOM_CASE_TAC : tactic =
  CLOSP2AUX_KN_UNFOLD_TAC THEN REPEAT DISCH_TAC THEN CLOSP2AUX_KN_SING_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kom_nrm) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  CLOSP2AUX_SATP_GEN_TAC ["ALL"; "obeys_max_app"; "val_approx_obeys_max_app";
                          "globals_approx_obeys_max_app"]
    CLOSP2AUX_KOM_PROVE_TAC CLOSP2AUX_kom_fwd CLOSP2AUX_kom_nrm 4 THEN
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_kom_nrm) THEN
  REWRITE_TAC CLOSP2AUX_kom_nrm THEN ASM_REWRITE_TAC[] THEN
  TRY CLOSP2AUX_KOM_LETREC_TAC;;

let CLOSP2AUX_kom_thm =
  MP CLOSP2AUX_kom_ind
    (end_itlist CONJ (map (fun t -> prove(t, CLOSP2AUX_KOM_CASE_TAC))
                          (conjuncts (lhand (concl CLOSP2AUX_kom_ind)))));;

(* HOL4: known_obeys_max_app *)
let known_obeys_max_app = prove
 (`!k a b c (d:(val_approx)spt).
     ALL (obeys_max_app k) b /\ ALL (val_approx_obeys_max_app k) c /\
     globals_approx_obeys_max_app k d
     ==>
     ALL (obeys_max_app k) (MAP FST (FST (clos_known_known a b c d))) /\
     ALL (val_approx_obeys_max_app k) (MAP SND (FST (clos_known_known a b c d))) /\
     globals_approx_obeys_max_app k (SND (clos_known_known a b c d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:clos_known_config`; `b:clos_exp list`; `c:val_approx list`;
                `d:val_approx spt`] CLOSP2AUX_kom_thm) THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `FST (clos_known_known a b c (d:val_approx spt))`;
                             `SND (clos_known_known a b c (d:val_approx spt))`]) THEN
  ASM_REWRITE_TAC[PAIR]);;

(* HOL4: compile_obeys_max_app *)
let compile_obeys_max_app = prove
 (`!k c xs res ys.
     clos_known_compile (SOME c) xs = (res,ys) /\ ALL (obeys_max_app k) xs ==>
     ?c1. res = SOME c1 /\ ALL (obeys_max_app k) ys /\
          globals_approx_obeys_max_app k (clos_known_config_val_approx_spt c1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_known_compile_def; LET_DEF; LET_END_DEF; pair_CASE_def;
              PAIR_EQ; clos_fvs_compile_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[injectivity "option"; UNWIND_THM1; clos_known_config_INFO.ri_accfupds;
              K_THM] THEN
  MP_TAC(SPECL [`k:num`; `c:clos_known_config`; `remove_fvs 0 xs`; `[]:val_approx list`;
                `LN:val_approx spt`] known_obeys_max_app) THEN
  ASM_REWRITE_TAC[remove_fvs_obeys_max_app; ALL; globals_approx_obeys_max_app_def;
                  lookup_rwts; distinctness "option"] THEN
  MESON_TAC[remove_ticks_obeys_max_app; let_op_obeys_max_app]);;

(* HOL4: known_compile_IS_SOME *)
let clos_knownProof_known_compile_IS_SOME = prove
 (`!kc es kc' es'.
     clos_known_compile kc es = (kc',es') ==> (IS_SOME kc' <=> IS_SOME kc)`,
  REPEAT GEN_TAC THEN CASES_ON `kc:clos_known_config option` THEN
  REWRITE_TAC[clos_known_compile_def; LET_DEF; LET_END_DEF; pair_CASE_def;
              PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[IS_SOME_DEF]);;

(* HOL4: get_code_labels_mk_Ticks [simp] *)
let get_code_labels_mk_Ticks = prove
 (`!a b c d. clos_get_code_labels (clos_known_mk_Ticks a b c d) =
             clos_get_code_labels d`,
  MATCH_MP_TAC clos_known_mk_Ticks_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[clos_known_mk_Ticks_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[clos_get_code_labels_def; UNION_EMPTY]);;

let _ = cake_add_simps [get_code_labels_mk_Ticks];;
