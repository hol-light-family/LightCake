(* ========================================================================= *)
(* computeProof: port of HOL4 candle/prover/compute/computeProofScript.sml  *)
(* (CakeML v3479).  Proof of correctness for the compute primitive.         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The overloads of compute_syntax are read by its parser extension (see   *)
(*   the header of compute_syntax.ml); thyof ctxt is compute_evalProof's.    *)
(* - STATE, THM, TERM, CONTEXT are holKernelProof_STATE, holKernelProof_THM, *)
(*   holKernelProof_TERM, holKernelProof_CONTEXT; dest_const_thm is          *)
(*   holKernelProof_dest_const_thm (names.tsv); compute is compute_compute.  *)
(* - check_eqn_thm: HOL4 writes !f vs r. res = M_success (f,vs,cv) ==> ...   *)
(*   with r unused (shadowed by the ?l r below) and cv free; here the binder *)
(*   is cv.                                                                   *)
(* - The free variables of the HOL4 statements are universally quantified.   *)
(* - Local helpers that are not HOL4 theorems are CMPPAUX_.                  *)
(* ========================================================================= *)

needs "candle/prover/compute/compute.ml";;
needs "candle/prover/compute/compute_execProof.ml";;

prioritize_num();;
type_invention_error := true;;

compute_overloads_on ();;

(* ------------------------------------------------------------------------- *)
(* tactics for the monadic proofs                                            *)
(* ------------------------------------------------------------------------- *)

(* a relational lemma !xs. A ==> eq ==> C as !xs. eq ==> A ==> C *)
let CMPPAUX_EQ_FIRST (th:thm) : thm =
  let th1 = SPEC_ALL th in
  let a,rest = dest_imp (concl th1) in
  let e,_ = dest_imp rest in
  GEN_ALL (DISCH e (DISCH a (MP (MP th1 (ASSUME a)) (ASSUME e))));;

(* use a relational lemma (equation first, context last) on the latest     *)
(* matching equation of the assumptions; the state equation substituted    *)
let CMPPAUX_SUBST_STATE_TAC : thm_tactic = fun th ->
  let l,r = dest_eq (concl th) in
  let is_new v = try let n = fst (dest_var v) in
                     String.length n >= 2 && String.sub n 0 2 = "st"
                 with Failure _ -> false in
  if is_new r && not (is_new l) then SUBST_ALL_TAC (SYM th) else SUBST_ALL_TAC th;;

let CMPPAUX_REL_TAC (lem:thm) : tactic =
  FIRST_ASSUM(MP_TAC o SPEC `ctxt:(update)list` o MATCH_MP lem) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 CMPPAUX_SUBST_STATE_TAC ASSUME_TAC);;

(* the components of a pair variable *)
let CMPPAUX_PAIR_TAC (p:term) (x:term) (y:term) : tactic =
  X_CHOOSE_THEN x (X_CHOOSE_THEN y SUBST_ALL_TAC) (ISPEC p PAIR_SURJECTIVE);;

(* a result (R,st) = (res,s') with R a failure or success that is not a Clash *)
let CMPPAUX_RESULT_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[distinctness "exc"; injectivity "exc"; distinctness "hol_exn"];;

(* cases on a run of name (arity k) in the goal: its result and state (the *)
(* new names avoid the hypotheses of the assumptions too)                   *)
let CMPPAUX_CASES_TAC (name:string) (k:int) : tactic = fun (asl,w as g) ->
  let is_ex t = try let f,args = strip_comb t in
                    fst (dest_const f) = name && length args = k
                with Failure _ -> false in
  let t = find (fun t -> free_in t w) (find_terms is_ex w) in
  let [rty; sty] = snd (dest_type (type_of t)) in
  let avoid = frees w @ freesl (map (concl o snd) asl) @
              freesl (List.concat (map (hyp o snd) asl)) in
  let r = variant avoid (mk_var("r",rty)) in
  let s2 = variant (r::avoid) (mk_var("st",sty)) in
  let a = variant (s2::r::avoid) (mk_var("a",hd (snd (dest_type rty)))) in
  let b = variant (a::s2::r::avoid) (mk_var("e",hd (tl (snd (dest_type rty))))) in
  (MP_TAC (ISPEC t PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s2 (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
   DISJ_CASES_THEN2 (X_CHOOSE_THEN a SUBST_ALL_TAC) (X_CHOOSE_THEN b SUBST_ALL_TAC)
     (ISPEC r (cases "exc"))) g;;

(* RESULT_TAC with the facts about the failure among the assumptions *)
let CMPPAUX_RESULT2_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "exc"; distinctness "exc"]) THEN
  ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"; distinctness "hol_exn"];;

(* !xs. eq /\ A ==> C  as  !xs. eq ==> A ==> C *)
let CMPPAUX_EQ_FIRST2 (th:thm) : thm =
  let th1 = SPEC_ALL th in
  let a,_ = dest_imp (concl th1) in
  let e,rest = dest_conj a in
  GEN_ALL (DISCH e (DISCH rest (MP th1 (CONJ (ASSUME e) (ASSUME rest)))));;

(* !xs. A /\ B /\ eq ==> C  as  !xs. eq ==> A /\ B ==> C (eq the last conjunct) *)
let CMPPAUX_EQ_LAST (th:thm) : thm =
  let rec rconj t = try let l,r = dest_conj t in l :: rconj r with Failure _ -> [t] in
  let rec rsplit th = try let l,r = dest_conj (concl th) in CONJUNCT1 th :: rsplit (CONJUNCT2 th)
                      with Failure _ -> [th] in
  let th1 = SPEC_ALL th in
  let a,_ = dest_imp (concl th1) in
  let cs = rconj a in
  let e = last cs and rest = list_mk_conj (butlast cs) in
  let ath = end_itlist CONJ (rsplit (ASSUME rest) @ [ASSUME e]) in
  GEN_ALL (DISCH e (DISCH rest (MP th1 ath)));;

(* a failure M_failure e of the body of handle_Clash: either exception kind *)
(* ends as a Failure                                                        *)
let CMPPAUX_HFAIL_TAC : tactic = fun (asl,w as g) ->
  let e = find (fun v -> type_of v = `:hol_exn`) (frees w) in
  (STRUCT_CASES_TAC (SPEC e (cases "hol_exn")) THEN
   CAKE_REWRITE_TAC[holKernel_raise_Failure_def] THEN CMPPAUX_RESULT_TAC) g;;

let compute_init_thy_ok = prove
 (`!ths ctxt s.
     compute_init ths /\
     holKernelProof_STATE ctxt s /\
     ALL (holKernelProof_THM ctxt) ths ==>
       compute_thy_ok (thyof ctxt)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compute_init_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `theory_ok (thyof ctxt)` ASSUME_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] extends_theory_ok) THEN
    EXISTS_TAC `init_ctxt` THEN REWRITE_TAC[init_theory_ok] THEN
    ASM_MESON_TAC[holKernelProof_STATE_def; holKernelProof_CONTEXT_def];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  UNDISCH_TAC `ALL (holKernelProof_THM ctxt) compute_thms` THEN
  REWRITE_TAC[compute_thms_def; ALL; holKernelProof_THM_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[compute_thy_ok_def; numeral_thy_ok_def; bool_thy_ok_def]);;


(* ------------------------------------------------------------------------- *)
(* compute_add                                                               *)
(* ------------------------------------------------------------------------- *)

(* the equation of compute_add *)
let CMPPAUX_add_eqn = prove
 (`!thy l r x y.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) (_NUMERAL l) /\ hol_term_ok (FST thy) (_NUMERAL r) /\
     compute_dest_num l = SOME x /\ compute_dest_num r = SOME y ==>
     (thy,[]) |- _ADD (_NUMERAL l) (_NUMERAL r) === _NUMERAL (num2bit (x + y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) l /\ l has_type (Num) /\
                hol_term_ok (FST thy) r /\ r has_type (Num)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[term_ok_NUMERAL]; ALL_TAC] THEN
  MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `num2bit x` THEN CONJ_TAC THENL
   [MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `l:hol_term` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[dest_num_num2bit];
      MATCH_MP_TAC sym_equation THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn];
    ALL_TAC] THEN
  MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `num2bit y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `r:hol_term` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[dest_num_num2bit];
      MATCH_MP_TAC sym_equation THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn];
    ALL_TAC] THEN
  CMPSYNPAUX_TRANS_TAC ADD_num2bit THEN
  MATCH_MP_TAC sym_equation THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn);;

let CMPPAUX_TERM_NUMERAL = prove
 (`!ctxt n. numeral_thy_ok (thyof ctxt) ==>
            holKernelProof_TERM ctxt (_NUMERAL (num2bit n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[holKernelProof_TERM_def] THEN
  MP_TAC (SPECL [`thyof ctxt`; `num2bit n`] term_ok_NUMERAL) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[num2bit_has_type] THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP num2bit_term_ok) THEN REWRITE_TAC[FST]);;

let compute_add_thm = prove
 (`!ctxt s ths tm res s'.
     holKernelProof_STATE ctxt s /\
     ALL (holKernelProof_THM ctxt) ths /\
     holKernelProof_TERM ctxt tm ==>
     compute_add ths tm s = (res,s') ==>
       s' = s /\
       (!th. res = M_success th ==> holKernelProof_THM ctxt th) /\
       (!tm. ~(res = M_failure (holKernel_Clash tm)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compute_add_def] THEN
  ASM_CASES_TAC `compute_init ths` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[holKernel_raise_Failure_def] THEN CMPPAUX_RESULT_TAC] THEN
  SUBGOAL_THEN `compute_thy_ok (thyof ctxt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[compute_init_thy_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `holKernelProof_TERM ctxt _ADD_TM` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP compute_thy_ok_terms_ok) THEN
    SIMP_TAC[holKernelProof_TERM_def; FST]; ALL_TAC] THEN
  REWRITE_TAC[otherwise_def; st_ex_bind_def; LET_DEF; LET_END_DEF] THEN
  CMPPAUX_CASES_TAC "compute_dest_binary" 3 THEN
  CMPPAUX_REL_TAC (CMPPAUX_EQ_FIRST dest_binary_thm) THEN CMPEXPAUX_SIMP_TAC THENL
   [ALL_TAC; CMPPAUX_RESULT_TAC] THEN
  CMPPAUX_PAIR_TAC `a:hol_term#hol_term` `l:hol_term` `r:hol_term` THEN CMPEXPAUX_SIMP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o SPECL [`l:hol_term`; `r:hol_term`] o
                check (is_forall o concl)) THEN
  CMPPAUX_CASES_TAC "compute_dest_numeral" 2 THEN
  CMPPAUX_REL_TAC (CMPPAUX_EQ_FIRST dest_numeral_thm) THEN CMPEXPAUX_SIMP_TAC THENL
   [ALL_TAC; CMPPAUX_RESULT_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o SPEC `a:num` o
                check (is_forall o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs (concl th) = `l:hol_term`)) THEN
  CMPPAUX_CASES_TAC "compute_dest_numeral" 2 THEN
  CMPPAUX_REL_TAC (CMPPAUX_EQ_FIRST dest_numeral_thm) THEN CMPEXPAUX_SIMP_TAC THENL
   [ALL_TAC; CMPPAUX_RESULT_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o SPEC `a':num` o
                check (is_forall o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs (concl th) = `r:hol_term`)) THEN
  SUBGOAL_THEN `holKernelProof_TERM ctxt (_NUMERAL (num2bit (a + a')))` ASSUME_TAC THENL
    [MATCH_MP_TAC CMPPAUX_TERM_NUMERAL THEN ASM_SIMP_TAC[compute_thy_ok_numeral_thy_ok];
     ALL_TAC] THEN
   CMPPAUX_CASES_TAC "holKernel_mk_eq" 2 THEN
   CMPPAUX_REL_TAC mk_eq_thm THEN CMPEXPAUX_SIMP_TAC THENL
    [ALL_TAC; CMPPAUX_RESULT_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `a:hol_term` o CONJUNCT2) THEN REWRITE_TAC[] THEN
   STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
   GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `term_type tm = (Num)` SUBST1_TAC THENL
    [MP_TAC (SPECL [`ctxt:(update)list`; `tm:hol_term`] term_type) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
     DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[typeof_def; codomain_def];
     ALL_TAC] THEN
   REWRITE_TAC[holKernelProof_THM_def] THEN
   MP_TAC (SPECL [`thyof ctxt`; `tm':hol_term`; `tm'':hol_term`; `a:num`; `a':num`]
                 CMPPAUX_add_eqn) THEN
   ANTS_TAC THENL
    [ASM_SIMP_TAC[compute_thy_ok_numeral_thy_ok; FST] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_TERM_def]) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[equation_def; typeof_def; codomain_def]);;


(* ------------------------------------------------------------------------- *)
(* compute                                                                   *)
(* ------------------------------------------------------------------------- *)

let const_list_ok = prove
 (`!vs. set_of_list (const_list vs) = cexp_consts vs`,
  MATCH_MP_TAC const_list_ind THEN
  REWRITE_TAC[const_list_def; cexp_consts_def; SET_OF_LIST_APPEND; set_of_list] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIST_TO_SET_FLAT; GSYM MAP_o] THEN
  SUBGOAL_THEN `MAP (set_of_list o const_list) xs = MAP cexp_consts xs` SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_REWRITE_TAC[];
    SET_TAC[]]);;

let var_list_ok = prove
 (`!vs. set_of_list (var_list vs) = cexp_vars vs`,
  MATCH_MP_TAC var_list_ind THEN
  REWRITE_TAC[var_list_def; cexp_vars_def; SET_OF_LIST_APPEND; set_of_list;
              LIST_TO_SET_FILTER] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIST_TO_SET_FLAT; GSYM MAP_o] THENL
   [SET_TAC[];
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_REWRITE_TAC[]]);;

let check_cexp_closed_correct = prove
 (`!bvs v. check_cexp_closed bvs v ==> cexp_vars v DIFF set_of_list bvs = {}`,
  MATCH_MP_TAC check_cexp_closed_ind THEN
  REWRITE_TAC[check_cexp_closed_def; cexp_vars_def; ALL; set_of_list] THEN
  REPEAT CONJ_TAC THENL
   [(* Var *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_SING; NOT_IN_EMPTY; IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[];
    (* Num *)
    REWRITE_TAC[EMPTY_DIFF];
    (* (Uop is solved by the rewriting) Pair *)
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM SET_TAC[];
    (* Binop *)
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM SET_TAC[];
    (* If *)
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM SET_TAC[];
    (* Let *)
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM SET_TAC[];
    (* App *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!y. MEM y cs ==> cexp_vars y DIFF set_of_list bvs = {}` MP_TAC THENL
     [UNDISCH_TAC `ALL (check_cexp_closed bvs) cs` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; NOT_IN_EMPTY] THEN
    MESON_TAC[]]);;

let map_check_var_thm = prove
 (`!tms ctxt (s:hol_refs) res s'.
     holKernelProof_STATE ctxt s /\
     ALL (holKernelProof_TERM ctxt) tms /\
     compute_map check_var tms s = (res,s') ==>
       s = s' /\
       (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
       !ns. res = M_success ns ==>
            ALL2 (\tm n. tm = hol_Var n (Cexp)) tms ns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[compute_map_def; ALL] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN MESON_TAC[ALL2];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[st_ex_bind_def] THEN
  STRUCT_CASES_TAC (SPEC `h:hol_term` (cases "hol_term")) THEN
  REWRITE_TAC[check_var_def] THEN
  REWRITE_TAC[COND_RATOR] THEN TRY COND_CASES_TAC THEN
  CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def] THEN
  TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ctxt:(update)list`; `s:hol_refs`;
      `FST (compute_map check_var t (s:hol_refs))`;
      `SND (compute_map check_var t (s:hol_refs))`]) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  CMPPAUX_CASES_TAC "compute_map" 3 THEN CMPEXPAUX_SIMP_TAC THEN
  STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)))) THEN
  ASM_SIMP_TAC[ALL2]);;

let CMPPAUX_FOLDL_app_type = prove
 (`!xs tm sig.
     hol_term_ok sig tm /\
     (!x. MEM x xs ==> hol_term_ok sig x /\ typeof x = (Cexp)) /\
     hol_term_ok sig (FOLDL hol_Comb tm xs) /\ typeof (FOLDL hol_Comb tm xs) = (Cexp) ==>
     typeof tm = app_type (LENGTH xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; LENGTH; app_type; MEM] THEN
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) ->
      let sg = find_term (fun t -> is_var t && fst (dest_var t) = "sig")
                 (list_mk_conj (w :: map (concl o snd) asl)) in
      FIRST_X_ASSUM(MP_TAC o SPECL [`hol_Comb tm h`; sg])) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[term_ok_FOLDL_Comb]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `hol_term_ok sig (hol_Comb tm h)` MP_TAC THENL
   [ASM_MESON_TAC[term_ok_FOLDL_Comb]; ALL_TAC] THEN
  REWRITE_TAC[CMPSYNPAUX_term_ok_Comb_alt] THEN STRIP_TAC THEN
  UNDISCH_TAC `typeof (hol_Comb tm h) = app_type (LENGTH (t:hol_term list))` THEN
  REWRITE_TAC[typeof_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `typeof h = (Cexp)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let CMPPAUX_ALL2_Var = prove
 (`!vs args. ALL2 (\tm n. tm = hol_Var n (Cexp)) vs args ==>
             vs = MAP (\s. hol_Var s (Cexp)) args`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MAP; CONS_11] THEN
  ASM_MESON_TAC[]);;

(* HOL4 quantifies an unused r in the last conjunct, with cv free: the *)
(* binder here is cv                                                     *)
let check_eqn_thm = prove
 (`!ctxt th (s:hol_refs) res s'.
     compute_thy_ok (thyof ctxt) /\
     holKernelProof_STATE ctxt s /\
     holKernelProof_THM ctxt th /\
     check_eqn th s = (res,s') ==>
       s = s' /\
       (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
       !f vs cv. res = M_success (f,vs,cv) ==>
         ?l r. ALL_DISTINCT vs /\
               th = Sequent [] (l === r) /\
               list_dest_comb [] l = CONS (hol_Const f (app_type (LENGTH vs)))
                                          (MAP (\s. hol_Var s Cexp) vs) /\
               compute_dest_cexp r = SOME cv /\
               !v. v IN cexp_vars cv ==> MEM v vs`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `th:thm` (cases "thm")) THEN
   REWRITE_TAC[check_eqn_def] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
   REWRITE_TAC[st_ex_ignore_bind_def; COND_RATOR] THEN
   ASM_CASES_TAC `a0:hol_term list = []` THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `holKernelProof_TERM ctxt a1` ASSUME_TAC THENL
    [UNDISCH_TAC `holKernelProof_THM ctxt (Sequent [] a1)` THEN
     REWRITE_TAC[holKernelProof_THM_def; holKernelProof_TERM_def] THEN
     DISCH_THEN(MP_TAC o MATCH_MP proves_term_ok) THEN SIMP_TAC[ALL; FST; SND];
     ALL_TAC] THEN
   REWRITE_TAC[st_ex_bind_def] THEN
   CMPPAUX_CASES_TAC "holKernel_dest_eq" 2 THEN
   CMPPAUX_REL_TAC (CMPPAUX_EQ_FIRST2 dest_eq_thm) THEN CMPEXPAUX_SIMP_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
     REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
     GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[dest_eq_not_clash]] THEN
  CMPPAUX_PAIR_TAC `a:hol_term#hol_term` `l:hol_term` `r:hol_term` THEN CMPEXPAUX_SIMP_TAC THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o SPECL [`l:hol_term`; `r:hol_term`] o
                 check (is_forall o concl)) THEN
   DISJ_CASES_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `f0:hol_term` (X_CHOOSE_THEN `vs0:hol_term list` ASSUME_TAC))
     (ISPEC `list_dest_comb [] l` list_CASES) THEN
   ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[list_dest_comb_not_nil]; ALL_TAC] THEN
   CAKE_REWRITE_TAC[] THEN REWRITE_TAC[COND_RATOR] THEN
   ASM_CASES_TAC `ALL_DISTINCT (vs0:hol_term list)` THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP list_dest_comb_folds_back o check (fun th ->
     try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "list_dest_comb"
     with Failure _ -> false)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[APPEND_NIL] o
                 check (fun th -> lhs (concl th) = `vs0:hol_term list`)) THEN
   SUBGOAL_THEN `holKernelProof_TERM ctxt f0 /\ ALL (holKernelProof_TERM ctxt) xs`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `holKernelProof_TERM ctxt l` THEN
     FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs (concl th) = `l:hol_term`)) THEN
     REWRITE_TAC[holKernelProof_TERM_def] THEN
     DISCH_THEN(MP_TAC o MATCH_MP term_ok_FOLDL_Comb) THEN
     REWRITE_TAC[GSYM ALL_MEM; holKernelProof_TERM_def];
     ALL_TAC] THEN
   REWRITE_TAC[otherwise_def; st_ex_bind_def] THEN
   CMPPAUX_CASES_TAC "holKernel_dest_const" 2 THEN
   CMPPAUX_REL_TAC (CMPPAUX_EQ_FIRST holKernelProof_dest_const_thm) THEN
   CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_RESULT_TAC] THEN
  CMPPAUX_PAIR_TAC `a:mlstring#hol_type` `nm:mlstring` `ty:hol_type` THEN CMPEXPAUX_SIMP_TAC THEN
   SUBGOAL_THEN `f0 = hol_Const nm ty` SUBST_ALL_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th ->
       try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "holKernel_dest_const"
       with Failure _ -> false)) THEN
     STRUCT_CASES_TAC (SPEC `f0:hol_term` (cases "hol_term")) THEN
     REWRITE_TAC[holKernel_dest_const_def] THEN
     CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ;
                      injectivity "exc"; distinctness "exc"; injectivity "hol_term"] THEN
     MESON_TAC[];
     ALL_TAC] THEN
   CMPPAUX_CASES_TAC "compute_map" 3 THEN
   CMPPAUX_REL_TAC (CMPPAUX_EQ_LAST map_check_var_thm) THEN
   CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_RESULT2_TAC] THEN
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `cv1:compute_exp` ASSUME_TAC)
     (ISPEC `compute_dest_cexp r` (cases "option")) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
   REWRITE_TAC[COND_RATOR] THEN COND_CASES_TAC THEN
   CAKE_REWRITE_TAC[holKernel_raise_Failure_def; st_ex_return_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[injectivity "exc"; distinctness "exc"; PAIR_EQ] THEN
   REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `xs = MAP (\s. hol_Var s (Cexp)) (vs:mlstring list)` SUBST_ALL_TAC THENL
    [MATCH_MP_TAC CMPPAUX_ALL2_Var THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o check (fun th -> is_conj (concl th))) THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN `typeof r = (Cexp) /\ typeof l = typeof r` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC (SPEC `thyof ctxt` dest_cexp_thm) THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPECL [`r:hol_term`; `cv:compute_exp`]) THEN
       ASM_REWRITE_TAC[FST] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_TERM_def]) THEN ASM_SIMP_TAC[];
       UNDISCH_TAC `holKernelProof_TERM ctxt a1` THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[holKernelProof_TERM_def; GSYM equation_def] THEN
       MP_TAC (SPEC `thyof ctxt` compute_thy_ok_is_std_sig) THEN
       ASM_REWRITE_TAC[FST] THEN SIMP_TAC[term_ok_equation] THEN MESON_TAC[]];
     ALL_TAC] THEN
  SUBGOAL_THEN `ty = app_type (LENGTH (vs:mlstring list))` SUBST_ALL_TAC THENL
    [MP_TAC (ISPECL [`MAP (\s. hol_Var s (Cexp)) (vs:mlstring list)`; `hol_Const f ty`;
                     `(alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                       alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`]
                    CMPPAUX_FOLDL_app_type) THEN
     REWRITE_TAC[typeof_def; LENGTH_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
     UNDISCH_TAC `ALL (holKernelProof_TERM ctxt) (MAP (\s. hol_Var s (Cexp)) vs)` THEN
     RULE_ASSUM_TAC(REWRITE_RULE[holKernelProof_TERM_def]) THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[GSYM ALL_MEM; holKernelProof_TERM_def] THEN
     DISCH_TAC THEN X_GEN_TAC `x:hol_term` THEN DISCH_TAC THEN CONJ_TAC THENL
      [ASM_MESON_TAC[];
       UNDISCH_TAC `MEM (x:hol_term) (MAP (\s. hol_Var s (Cexp)) vs)` THEN
       REWRITE_TAC[MEM_MAP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[typeof_def]];
     ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:hol_term`; `r:hol_term`] THEN
   ASM_REWRITE_TAC[equation_def] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[ALL_DISTINCT_MAP];
     UNDISCH_TAC `ALL (\v. MEM v vs) (var_list cv)` THEN
     REWRITE_TAC[GSYM ALL_MEM; GSYM var_list_ok; IN_SET_OF_LIST] THEN MESON_TAC[]]);;

let map_check_eqn_thm = prove
 (`!ctxt. compute_thy_ok (thyof ctxt) ==>
     !ceqs (s:hol_refs) res s'.
       holKernelProof_STATE ctxt s /\
       ALL (holKernelProof_THM ctxt) ceqs /\
       compute_map check_eqn ceqs s = (res,s') ==>
         s = s' /\
         (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
         !eqs. res = M_success eqs ==>
           !n. n < LENGTH eqs ==>
               ?f vs cv l r.
                 ALL_DISTINCT vs /\
                 EL n eqs = (f,vs,cv) /\
                 EL n ceqs = Sequent [] (l === r) /\
                 list_dest_comb [] l = CONS (hol_Const f (app_type (LENGTH vs)))
                                            (MAP (\s. hol_Var s Cexp) vs) /\
                 compute_dest_cexp r = SOME cv /\
                 !v. v IN cexp_vars cv ==> MEM v vs`,
  GEN_TAC THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[compute_map_def; ALL] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; CONJUNCT1 LT]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[st_ex_bind_def] THEN
  CMPPAUX_CASES_TAC "check_eqn" 2 THEN
  CMPPAUX_REL_TAC (CMPPAUX_EQ_LAST check_eqn_thm) THEN
  CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_RESULT2_TAC] THEN
  CMPPAUX_PAIR_TAC `a:mlstring#mlstring list#compute_exp` `f0:mlstring`
    `p0:mlstring list#compute_exp` THEN
  CMPPAUX_PAIR_TAC `p0:mlstring list#compute_exp` `vs0:mlstring list` `cv0:compute_exp` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:hol_refs`;
      `FST (compute_map check_eqn t (s:hol_refs))`;
      `SND (compute_map check_eqn t (s:hol_refs))`]) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  CMPPAUX_CASES_TAC "compute_map" 3 THEN CMPEXPAUX_SIMP_TAC THEN
  STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)))) THEN
  POP_ASSUM MP_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `m:num` SUBST1_TAC) (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[LENGTH; LT_SUC; LT_0; EL; HD; TL] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`f0:mlstring`; `vs0:mlstring list`; `cv0:compute_exp`] o
                  CONJUNCT2 o check (fun th -> is_conj (concl th) &&
                     can (find_term (fun t -> t = `compute_dest_cexp`)) (concl th))) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:hol_term` (X_CHOOSE_THEN `r1:hol_term` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`f0:mlstring`; `vs0:mlstring list`; `cv0:compute_exp`;
                          `l1:hol_term`; `r1:hol_term`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FORALL_UNWIND_THM1]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let check_consts_thm = prove
 (`!ctxt (s:hol_refs) ars f r res s'.
     holKernelProof_STATE ctxt s /\
     check_consts ars f r s = (res,s') ==>
       s = s' /\
       (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
       !u. res = M_success u ==> ALL (\(c,n). MEM (c,n) ars) (const_list r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_consts_def; COND_RATOR] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"; distinctness "hol_exn"]);;

let map_check_consts_thm = prove
 (`!(ceqs:(mlstring#A#compute_exp)list) ars ctxt (s:hol_refs) res s'.
     holKernelProof_STATE ctxt s /\
     compute_map (\(f,(n,r)). check_consts ars f r) ceqs s = (res,s') ==>
       s = s' /\
       (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
       !u. res = M_success u ==>
           !f vs cv. MEM (f,vs,cv) ceqs ==>
                     ALL (\(c,n). MEM (c,n) ars) (const_list cv)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[compute_map_def; MEM] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[injectivity "exc"; distinctness "exc"];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:mlstring#A#compute_exp`,`h:mlstring#A#compute_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`f0:mlstring`; `n0:A`; `r0:compute_exp`] THEN
  REWRITE_TAC[st_ex_bind_def] THEN CAKE_REWRITE_TAC[] THEN
  CMPPAUX_CASES_TAC "check_consts" 4 THEN
  CMPPAUX_REL_TAC (CMPPAUX_EQ_FIRST (REWRITE_RULE[GSYM IMP_IMP] check_consts_thm)) THEN
  CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_RESULT2_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ars:(mlstring#num)list`; `ctxt:(update)list`; `s:hol_refs`;
      `FST (compute_map (\(f,(n,r)). check_consts ars f r) (t:(mlstring#A#compute_exp)list) (s:hol_refs))`;
      `SND (compute_map (\(f,(n,r)). check_consts ars f r) (t:(mlstring#A#compute_exp)list) (s:hol_refs))`]) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  CMPPAUX_CASES_TAC "compute_map" 3 THEN CMPEXPAUX_SIMP_TAC THEN
  STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th))) THEN
  ASM_MESON_TAC[]);;

(* the induction of const_list_imp_cexp_consts_ok, needed first by check_consts_ok *)
let CMPPAUX_const_list_imp = prove
 (`!(eqs:(mlstring#(A)list#B)list) cv.
     ALL (\(p1,p2). MEM (p1,p2) (MAP (\(f,n,r). (f,LENGTH n)) eqs)) (const_list cv) ==>
     cexp_consts_ok eqs cv`,
  MATCH_MP_TAC cexp_consts_ok_ind THEN
  REWRITE_TAC[const_list_def; cexp_consts_ok_def; ALL_APPEND; ALL] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `y:compute_exp` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:compute_exp` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `ALL (\(p1,p2). MEM (p1,p2) (MAP (\(f,n,r). f,LENGTH n)
                 (eqs:(mlstring#(A)list#B)list))) (FLAT (MAP const_list cs))` THEN
  REWRITE_TAC[EVERY_FLAT; ALL_MAP; GSYM ALL_MEM; o_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let check_consts_ok = prove
 (`!(eqs:(mlstring#(A)list#B)list) cexp (s:hol_refs) u s' fn.
     check_consts (MAP (\(f,vs,x). (f,LENGTH vs)) eqs) fn cexp s = (M_success u,s') ==>
     cexp_consts_ok eqs cexp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_consts_def; COND_RATOR] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def; PAIR_EQ;
              distinctness "exc"] THEN
  DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC CMPPAUX_const_list_imp THEN
  ASM_REWRITE_TAC[]);;

let cexp2term_from_cv = prove
 (`!v. cexp2term (from_cv v) = cv2term v`,
  MATCH_MP_TAC cv_INDUCT THEN REWRITE_TAC[from_cv_def; cexp2term_def; cv2term_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let const_list_imp_cexp_consts_ok = prove
 (`!(eqs:(mlstring#(A)list#B)list) cv.
     ALL (\(p1,p2). MEM (p1,p2) (MAP (\(f,n,r). (f,LENGTH n)) eqs)) (const_list cv) ==>
     cexp_consts_ok eqs cv`,
  MATCH_ACCEPT_TAC CMPPAUX_const_list_imp);;

(* an equation of compute, from map_check_eqn_thm *)
let CMPPAUX_compute_eqn = prove
 (`!ctxt ceqs (eqs:(mlstring#mlstring list#compute_exp)list) f vs cv.
     ALL (holKernelProof_THM ctxt) ceqs /\
     LENGTH ceqs = LENGTH eqs /\
     (!n. n < LENGTH eqs ==>
          ?f vs cv l r.
            ALL_DISTINCT vs /\
            EL n eqs = (f,vs,cv) /\
            EL n ceqs = Sequent [] (l === r) /\
            list_dest_comb [] l = CONS (hol_Const f (app_type (LENGTH vs)))
                                       (MAP (\s. hol_Var s Cexp) vs) /\
            compute_dest_cexp r = SOME cv /\
            !v. v IN cexp_vars cv ==> MEM v vs) /\
     MEM (f,vs,cv) eqs ==>
     ALL_DISTINCT vs /\ cexp_vars cv SUBSET set_of_list vs /\
     ?r. (thyof ctxt,[]) |- cexp2term (compute_App f (MAP compute_Var vs)) === r /\
         compute_dest_cexp r = SOME cv`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o REWRITE_RULE[MEM_EXISTS_EL]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:mlstring` (X_CHOOSE_THEN `vs1:mlstring list`
    (X_CHOOSE_THEN `cv1:compute_exp` (X_CHOOSE_THEN `l:hol_term`
    (X_CHOOSE_THEN `r:hol_term` STRIP_ASSUME_TAC))))) THEN
  UNDISCH_TAC `(f:mlstring,vs:mlstring list,cv:compute_exp) = EL n eqs` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
  EXISTS_TAC `r:hol_term` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(holKernelProof_THM ctxt) (EL n ceqs)` MP_TAC THENL
   [UNDISCH_TAC `ALL (holKernelProof_THM ctxt) ceqs` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[holKernelProof_THM_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_dest_comb_folds_back o check (fun th ->
     try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "list_dest_comb"
     with Failure _ -> false)) THEN
  REWRITE_TAC[APPEND_NIL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th)) &&
     fst (dest_var (rhs (concl th))) = "xs")) THEN
  REWRITE_TAC[cexp2term_def; LENGTH_MAP; GSYM MAP_o; o_DEF] THEN
  ASM_REWRITE_TAC[]);;

let CMPPAUX_compute_eqs = prove
 (`!ctxt ceqs (eqs:(mlstring#mlstring list#compute_exp)list).
     ALL (holKernelProof_THM ctxt) ceqs /\
     LENGTH ceqs = LENGTH eqs /\
     (!n. n < LENGTH eqs ==>
          ?f vs cv l r.
            ALL_DISTINCT vs /\
            EL n eqs = (f,vs,cv) /\
            EL n ceqs = Sequent [] (l === r) /\
            list_dest_comb [] l = CONS (hol_Const f (app_type (LENGTH vs)))
                                       (MAP (\s. hol_Var s Cexp) vs) /\
            compute_dest_cexp r = SOME cv /\
            !v. v IN cexp_vars cv ==> MEM v vs) /\
     (!f vs cv. MEM (f,vs,cv) eqs ==> cexp_consts_ok eqs cv) ==>
     ALL (\(f,vs,cv). ALL_DISTINCT vs /\ cexp_consts_ok eqs cv /\
           ?r. (thyof ctxt,[]) |- cexp2term (compute_App f (MAP compute_Var vs)) === r /\
               compute_dest_cexp r = SOME cv /\
               cexp_vars cv SUBSET set_of_list vs) eqs /\
     ALL (\(n,args,body). ALL_DISTINCT args /\ cexp_vars body SUBSET set_of_list args /\
                          cexp_consts_ok eqs body) eqs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC_ALL o
              MATCH_MP (CMPPAUX_EQ_LAST CMPPAUX_compute_eqn)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;

(* the type check can fail in many ways, but compute_eval (implemented by *)
(* exec) succeeds or raises the timeout (HOL4 comment)                      *)
let compute_thm = prove
 (`!ctxt (s:hol_refs) ths ceqs tm res s'.
     holKernelProof_STATE ctxt s /\
     ALL (holKernelProof_THM ctxt) ths /\
     ALL (holKernelProof_THM ctxt) ceqs /\
     holKernelProof_TERM ctxt tm ==>
     compute_compute (ths,ceqs) tm s = (res,s') ==>
       s' = s /\
       (!th. res = M_success th ==> holKernelProof_THM ctxt th) /\
       (!tm. ~(res = M_failure (holKernel_Clash tm)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[compute_compute_def; C_THM; holKernel_handle_Clash_def] THEN
   ASM_CASES_TAC `compute_init ths` THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[holKernel_raise_Failure_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
  SUBGOAL_THEN `compute_thy_ok (thyof ctxt)` ASSUME_TAC THENL
    [ASM_MESON_TAC[compute_init_thy_ok]; ALL_TAC] THEN
   DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `cv:compute_exp` ASSUME_TAC)
     (ISPEC `compute_dest_cexp tm` (cases "option")) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[holKernel_raise_Failure_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
   MP_TAC (SPEC `thyof ctxt` dest_cexp_thm) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`tm:hol_term`; `cv:compute_exp`]) THEN ASM_REWRITE_TAC[FST] THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM holKernelProof_TERM_def]; STRIP_TAC] THEN
   REWRITE_TAC[st_ex_ignore_bind_def; COND_RATOR] THEN
   COND_CASES_TAC THEN CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
   FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[set_of_list; DIFF_EMPTY] o
               MATCH_MP check_cexp_closed_correct) THEN
  REWRITE_TAC[st_ex_bind_def] THEN
   CMPPAUX_CASES_TAC "compute_map" 3 THEN
   (FIRST_ASSUM(fun thok ->
      let lem = CMPPAUX_EQ_LAST (MATCH_MP map_check_eqn_thm thok) in
      FIRST_ASSUM(MP_TAC o MATCH_MP lem)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 CMPPAUX_SUBST_STATE_TAC ASSUME_TAC)) THEN
   CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_HFAIL_TAC] THEN
  REWRITE_TAC[st_ex_ignore_bind_def; COND_RATOR; LET_DEF; LET_END_DEF] THEN
   COND_CASES_TAC THEN CAKE_REWRITE_TAC[st_ex_return_def; holKernel_raise_Failure_def] THEN
   TRY (CMPPAUX_RESULT_TAC THEN NO_TAC) THEN
   CMPPAUX_CASES_TAC "check_consts" 4 THEN
   CMPPAUX_REL_TAC (CMPPAUX_EQ_FIRST (REWRITE_RULE[GSYM IMP_IMP] check_consts_thm)) THEN
   CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_HFAIL_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP check_consts_ok o check (fun th ->
     try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "check_consts"
     with Failure _ -> false)) THEN
   CMPPAUX_CASES_TAC "compute_map" 3 THEN
   CMPPAUX_REL_TAC (CMPPAUX_EQ_LAST map_check_consts_thm) THEN
   CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_HFAIL_TAC] THEN
  SUBGOAL_THEN `!f vs cv. MEM (f,vs,cv) (a:(mlstring#mlstring list#compute_exp)list) ==>
                           cexp_consts_ok a cv` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN MATCH_MP_TAC const_list_imp_cexp_consts_ok THEN
     FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o check (fun th -> is_conj (concl th) &&
       can (find_term (fun t -> try fst (dest_const t) = "const_list" with Failure _ -> false))
           (concl th))) THEN
     REWRITE_TAC[injectivity "exc"; FORALL_UNWIND_THM1] THEN
     DISCH_THEN(MP_TAC o SPECL [`f:mlstring`; `vs:mlstring list`; `cv':compute_exp`]) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC (SPECL [`ctxt:(update)list`; `ceqs:thm list`;
                  `a:(mlstring#mlstring list#compute_exp)list`] CMPPAUX_compute_eqs) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP map_LENGTH o check (fun th ->
         try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "compute_map" &&
             rand (rator (rator (lhs (concl th)))) = `check_eqn`
         with Failure _ -> false));
       FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o check (fun th -> is_conj (concl th) &&
         can (find_term (fun t -> try fst (dest_const t) = "list_dest_comb" with Failure _ -> false))
             (concl th))) THEN
       REWRITE_TAC[injectivity "exc"; FORALL_UNWIND_THM1]];
     STRIP_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thyof ctxt)) (cexp2term cv)` ASSUME_TAC THENL
    [MATCH_MP_TAC CMPEVPAUX_proves_lhs_ok THEN EXISTS_TAC `tm:hol_term` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC (SPECL [`cv:compute_exp`; `a:(mlstring#mlstring list#compute_exp)list`;
                  `compute_default_clock`; `s:hol_refs`] compute_eval_eq_exec) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CMPPAUX_CASES_TAC "exec" 5 THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CMPEXPAUX_SIMP_TAC THEN DISCH_TAC THEN
   (FIRST_ASSUM(fun thok ->
      let lem = CMPPAUX_EQ_FIRST2 (CONJUNCT1 (MATCH_MP compute_eval_thm thok)) in
      FIRST_ASSUM(MP_TAC o MATCH_MP lem)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 CMPPAUX_SUBST_STATE_TAC ASSUME_TAC)) THEN
   CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_HFAIL_TAC] THEN
  SUBGOAL_THEN `(thyof ctxt,[]) |- cexp2term cv === cv2term a` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM cexp2term_from_cv] THEN
     FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o check (fun th -> is_conj (concl th) &&
       can (find_term (fun t -> try fst (dest_const t) = "from_cv" with Failure _ -> false))
           (concl th))) THEN
     REWRITE_TAC[injectivity "exc"; FORALL_UNWIND_THM1];
     ALL_TAC] THEN
   SUBGOAL_THEN `holKernelProof_TERM ctxt (cv2term a)` ASSUME_TAC THENL
    [REWRITE_TAC[holKernelProof_TERM_def] THEN
     MP_TAC (SPECL [`thyof ctxt`; `cexp2term cv`; `cv2term a`] CMPEVPAUX_proves_rhs_ok) THEN
     ASM_REWRITE_TAC[FST];
     ALL_TAC] THEN
   CMPPAUX_CASES_TAC "holKernel_mk_eq" 2 THEN
   CMPPAUX_REL_TAC mk_eq_thm THEN CMPEXPAUX_SIMP_TAC THENL [ALL_TAC; CMPPAUX_HFAIL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `a:hol_term` o CONJUNCT2) THEN REWRITE_TAC[] THEN
   STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
   REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   REWRITE_TAC[injectivity "exc"; distinctness "exc"] THEN
   GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `term_type tm = (Cexp)` SUBST1_TAC THENL
    [MP_TAC (SPECL [`ctxt:(update)list`; `tm:hol_term`] term_type) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[holKernelProof_STATE_def]; ALL_TAC] THEN
     DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[holKernelProof_THM_def] THEN
   SUBGOAL_THEN `(thyof ctxt,[]) |- tm === cv2term a` MP_TAC THENL
    [MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `cexp2term cv` THEN
     ASM_SIMP_TAC[sym_equation];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[equation_def]);;

compute_overloads_off ();;
