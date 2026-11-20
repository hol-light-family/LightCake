(* ========================================================================= *)
(* clos_mtiProof: port of HOL4 compiler/backend/proofs/                     *)
(* clos_mtiProofScript.sml (CakeML v3479).                                   *)
(* Correctness proof for the clos_mti compiler pass. The theorem is proved  *)
(* using a backwards simulation, i.e. against the direction of compilation. *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/semantics/closSem.ml";;

type_invention_error := true;;

(* code relation *)

(* HOL4: no_mti_def (closProps' no_mti_def, HOL4 eta-converts it) *)
let clos_mtiProof_no_mti_def = CONV_RULE (DEPTH_CONV ETA_CONV) no_mti_def;;

(* HOL4: code_rel_def *)
let clos_mtiProof_code_rel_def = cake_def
  `clos_mtiProof_code_rel max_app e1 e2 <=>
     ALL no_mti e1 /\ e2 = intro_multi max_app e1`;;

(* HOL4: code_rel_IMP_LENGTH *)
let clos_mtiProof_code_rel_IMP_LENGTH = prove
 (`clos_mtiProof_code_rel max_app xs ys ==> LENGTH ys = LENGTH xs`,
  SIMP_TAC[clos_mtiProof_code_rel_def; intro_multi_length]);;

(* HOL4: HD_intro_multi [simp] *)
let HD_intro_multi = prove
 (`[HD (intro_multi max_app [e2])] = intro_multi max_app [e2]`,
  MP_TAC(SPECL [`e2:clos_exp`; `max_app:num`] intro_multi_sing) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD]);;

let _ = cake_add_simps [HD_intro_multi];;

(* HOL4: intro_multi_cons *)
let intro_multi_cons = prove
 (`!xs x. intro_multi m (CONS x xs) = CONS (HD (intro_multi m [x])) (intro_multi m xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[intro_multi_def; HD_intro_multi]);;

(* HOL4: code_rel_CONS_CONS *)
let clos_mtiProof_code_rel_CONS_CONS = prove
 (`clos_mtiProof_code_rel m (CONS x1 (CONS x2 xs)) (CONS y1 (CONS y2 ys)) <=>
   clos_mtiProof_code_rel m [x1] [y1] /\
   clos_mtiProof_code_rel m (CONS x2 xs) (CONS y2 ys)`,
  REWRITE_TAC[clos_mtiProof_code_rel_def; ALL;
              ISPECL [`CONS (x2:clos_exp) xs`; `x1:clos_exp`] intro_multi_cons] THEN
  MP_TAC(SPECL [`x1:clos_exp`; `m:num`] intro_multi_sing) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HD; CONS_11] THEN MESON_TAC[]);;

(* value relation *)

(* HOL4: mk_Fns_def *)
let mk_Fns_def = cake_def
  `(mk_Fns [] e = e) /\
   (mk_Fns (CONS t ts) e = Fn t NONE NONE 1 (mk_Fns ts e))`;;

(* HOL4: f_rel_def *)
let clos_mtiProof_f_rel_def = cake_def
  `clos_mtiProof_f_rel max_app (a1:num,e1:clos_exp) (a2:num,e2:clos_exp) <=>
     ?b1 ts.
       clos_mtiProof_code_rel max_app [b1] [e2] /\ a2 <= max_app /\ no_mti b1 /\
       a1 = 1 /\ e1 = mk_Fns ts b1 /\ a2 = LENGTH ts + 1`;;

(* HOL4: v_rel (max_app is bound in each rule; HOL4's args1 ++ recc ++ env1 *)
(* is (args1 ++ recc) ++ env1)                                              *)
let clos_mtiProof_v_rel_rules,clos_mtiProof_v_rel_ind,
    clos_mtiProof_v_rel_cases,clos_mtiProof_v_rel_strongind =
  cake_inductive
  `(!max_app i. clos_mtiProof_v_rel max_app (clos_Number i) (clos_Number i)) /\
   (!max_app w. clos_mtiProof_v_rel max_app (clos_Word64 w) (clos_Word64 w)) /\
   (!max_app w. clos_mtiProof_v_rel max_app (ByteVector w) (ByteVector w)) /\
   (!max_app n b. clos_mtiProof_v_rel max_app (clos_RefPtr b n) (clos_RefPtr b n)) /\
   (!max_app tag xs ys.
      ALL2 (clos_mtiProof_v_rel max_app) xs ys ==>
      clos_mtiProof_v_rel max_app (clos_Block tag xs) (clos_Block tag ys)) /\
   (!max_app args1 args2 env1 env2 arg_count e1 ts e2.
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      ALL2 (clos_mtiProof_v_rel max_app) env1 env2 /\
      ALL2 (clos_mtiProof_v_rel max_app) args1 args2 ==>
      clos_mtiProof_v_rel max_app
        (clos_Closure NONE [] (APPEND args1 env1) 1 (mk_Fns ts e1))
        (clos_Closure NONE args2 env2 arg_count e2)) /\
   (!max_app env1 funs1 env2 funs2 n.
      ALL2 (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      ALL2 (clos_mtiProof_v_rel max_app) env1 env2 /\
      n < LENGTH funs2 ==>
      clos_mtiProof_v_rel max_app
        (clos_Recclosure NONE [] env1 funs1 n)
        (clos_Recclosure NONE [] env2 funs2 n)) /\
   (!max_app args1 env1 funs1 args2 env2 funs2 n recc ts e1 e2 arg_count.
      ALL2 (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      ALL2 (clos_mtiProof_v_rel max_app) env1 env2 /\
      ALL2 (clos_mtiProof_v_rel max_app) args1 args2 /\ ~(args2 = []) /\
      n < LENGTH funs2 /\ EL n funs2 = (arg_count,e2) /\
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      ALL2 (clos_mtiProof_v_rel max_app) recc
        (list_of_seq (clos_Recclosure NONE [] env2 funs2) (LENGTH funs2)) ==>
      clos_mtiProof_v_rel max_app
        (clos_Closure NONE [] (APPEND (APPEND args1 recc) env1) 1 (mk_Fns ts e1))
        (clos_Recclosure NONE args2 env2 funs2 n))`;;

(* HOL4: v_rel_opt_def *)
let v_rel_opt_def = cake_def
  `(v_rel_opt max_app NONE NONE <=> T) /\
   (v_rel_opt max_app (SOME x) (SOME y) <=> clos_mtiProof_v_rel max_app x y) /\
   (v_rel_opt max_app _ _ <=> F)`;;

(* HOL4: ref_rel *)
let clos_mtiProof_ref_rel_rules,clos_mtiProof_ref_rel_ind,
    clos_mtiProof_ref_rel_cases,clos_mtiProof_ref_rel_strongind =
  cake_inductive
  `(!max_app bs. clos_mtiProof_ref_rel max_app (clos_ByteArray bs) (clos_ByteArray bs)) /\
   (!max_app xs ys.
      ALL2 (clos_mtiProof_v_rel max_app) xs ys ==>
      clos_mtiProof_ref_rel max_app (clos_ValueArray xs) (clos_ValueArray ys)) /\
   (!max_app m v w.
      clos_mtiProof_v_rel max_app v w ==>
      clos_mtiProof_ref_rel max_app (clos_Thunk m v) (clos_Thunk m w))`;;

(* HOL4: ref_rel_simps [simp] (HOL4 computes it with SIMP_CONV) *)
let clos_mtiProof_ref_rel_simps = prove
 (`(!max_app vs x. clos_mtiProof_ref_rel max_app (clos_ValueArray vs) x <=>
                   ?ys. x = clos_ValueArray ys /\ ALL2 (clos_mtiProof_v_rel max_app) vs ys) /\
   (!max_app bs x. clos_mtiProof_ref_rel max_app (clos_ByteArray bs) x <=>
                   x = clos_ByteArray bs) /\
   (!max_app m v x. clos_mtiProof_ref_rel max_app (clos_Thunk m v) x <=>
                    ?w. x = clos_Thunk m w /\ clos_mtiProof_v_rel max_app v w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_mtiProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN MESON_TAC[]);;

let _ = cake_add_simps [clos_mtiProof_ref_rel_simps];;

(* HOL4: FMAP_REL_def *)
let clos_mtiProof_FMAP_REL_def = cake_def
  `clos_mtiProof_FMAP_REL (r:A->B->bool) (f1:(K,A)fmap) (f2:(K,B)fmap) <=>
     FDOM f1 = FDOM f2 /\
     !k v. FLOOKUP f1 k = SOME v ==> ?v2. FLOOKUP f2 k = SOME v2 /\ r v v2`;;

(* state relation *)

(* HOL4: SND_compile_inc [simp] *)
let SND_compile_inc = prove
 (`!max_app (p:clos_exp list # A). SND (clos_mti_compile_inc max_app p) = []:B list`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_mti_compile_inc_def]);;

let _ = cake_add_simps [SND_compile_inc];;

(* HOL4: state_rel_def *)
let clos_mtiProof_state_rel_def = cake_def
  `clos_mtiProof_state_rel (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = [] /\
          ALL no_mti (FST (SND (clos_state_compile_oracle s n)))) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_max_app t = clos_state_max_app s /\ 1 <= clos_state_max_app s /\
     clos_state_clock t = clos_state_clock s /\
     clos_state_ffi t = clos_state_ffi s /\
     ALL2 (v_rel_opt (clos_state_max_app s)) (clos_state_globals s) (clos_state_globals t) /\
     clos_mtiProof_FMAP_REL (clos_mtiProof_ref_rel (clos_state_max_app s))
       (clos_state_refs s) (clos_state_refs t) /\
     clos_state_compile s =
       pure_cc (clos_mti_compile_inc (clos_state_max_app s)) (clos_state_compile t) /\
     clos_state_compile_oracle t =
       pure_co (clos_mti_compile_inc (clos_state_max_app s)) o clos_state_compile_oracle s`;;

(* HOL4: state_rel_max_app [local] *)
let clos_mtiProof_state_rel_max_app = prove
 (`clos_mtiProof_state_rel (s:(C,FFI)clos_state) t ==>
   clos_state_max_app s = clos_state_max_app t /\ 1 <= clos_state_max_app t`,
  SIMP_TAC[clos_mtiProof_state_rel_def]);;

(* HOL4: state_rel_clocks [local] *)
let state_rel_clocks = prove
 (`clos_mtiProof_state_rel (s:(C,FFI)clos_state) t ==>
   clos_state_clock s = clos_state_clock t`,
  SIMP_TAC[clos_mtiProof_state_rel_def]);;

(* evaluation theorem *)

(* HOL4: collect_args_IMP *)
let collect_args_IMP = prove
 (`!max_app k e1 num_args e2.
     collect_args max_app k e1 = (num_args,e2) /\ k <= max_app ==>
     k <= num_args /\ num_args <= max_app`,
  MATCH_MP_TAC collect_args_ind THEN RW[collect_args_def] THEN
  FS[PAIR_EQ] THEN RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4: collect_args_ok_IMP *)
let collect_args_ok_IMP = prove
 (`!max_app k e num_args e2.
     collect_args max_app k e = (num_args,e2) /\ no_mti e ==>
     ?ts. e = mk_Fns ts e2 /\ num_args = k + LENGTH ts /\ no_mti e2`,
  MATCH_MP_TAC collect_args_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_args_def; PAIR_EQ] THENL
   [DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[no_mti_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`num_args'':num`; `e2:clos_exp`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `ts:mlstring list` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `CONS (t:mlstring) ts` THEN ASM_REWRITE_TAC[mk_Fns_def; LENGTH] THEN
      ARITH_TAC;
      RVEQ_TAC THEN EXISTS_TAC `[]:mlstring list` THEN
      ASM_REWRITE_TAC[mk_Fns_def; LENGTH; no_mti_def] THEN ARITH_TAC];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    ALL_TAC; ALL_TAC] THEN
  STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:mlstring list` THEN
  ASM_REWRITE_TAC[mk_Fns_def; LENGTH; ADD_CLAUSES]);;

(* HOL4: dest_closure_SOME_IMP *)
let clos_mtiProof_dest_closure_SOME_IMP = prove
 (`dest_closure max_app loc_opt f2 xs = SOME x ==>
   (?loc arg_env clo_env num_args e. f2 = clos_Closure loc arg_env clo_env num_args e) \/
   (?loc arg_env clo_env fns i. f2 = clos_Recclosure loc arg_env clo_env fns i)`,
  CASES_ON `f2:clos_v` THEN
  REWRITE_TAC[injectivity "clos_v"; distinctness "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[dest_closure_def] THEN
  CASE_REWRITE_TAC[distinctness "option"]);;

(* HOL4: collect_apps_acc [local] *)
let collect_apps_acc = prove
 (`!max_app acc e res s.
     collect_apps max_app acc e = (res,s) ==> ?other. res = APPEND acc other`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN TRY DISCH_TAC THEN REPEAT GEN_TAC THEN
  (COND_CASES_TAC ORELSE ALL_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST
   [EXISTS_TAC `[]:clos_exp list` THEN ASM_REWRITE_TAC[APPEND_NIL] THEN NO_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:clos_exp list`; `s:clos_exp`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `APPEND (es:clos_exp list) other` THEN
    ASM_REWRITE_TAC[APPEND_ASSOC]]);;

(* a local helper: collect_apps with a longer accumulator *)
let CLOSP1AUX_mti_collect_apps_app = prove
 (`!m acc e ys.
     collect_apps (m + LENGTH ys) (APPEND ys acc) e =
     (APPEND ys (FST (collect_apps m acc e)), SND (collect_apps m acc e))`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; FST; SND] THEN
  DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `(a + b) + c <= m + a <=> b + c <= m`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND; GSYM APPEND_ASSOC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* HOL4: collect_apps_cons_lemma [local] *)
let collect_apps_cons_lemma = prove
 (`!e1 m ys other e2.
     collect_apps (m + LENGTH ys) ys e1 = (APPEND ys other,e2) <=>
     collect_apps m [] e1 = (other,e2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`m:num`; `[]:clos_exp list`; `e1:clos_exp`; `ys:clos_exp list`]
               CLOSP1AUX_mti_collect_apps_app) THEN
  REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[GSYM PAIR] THEN REWRITE_TAC[PAIR_EQ; FST; SND; APPEND_LCANCEL]);;

(* HOL4: collect_apps_cons [local] *)
let collect_apps_cons = prove
 (`!e1 m x other e2.
     collect_apps m [x] e1 = (CONS x other,e2) /\ ~(m = 0) ==>
     collect_apps (m - 1) [] e1 = (other,e2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e1:clos_exp`; `m - 1`; `[x:clos_exp]`; `other:clos_exp list`; `e2:clos_exp`]
               collect_apps_cons_lemma) THEN
  ASM_SIMP_TAC[LENGTH; ARITH_RULE `~(m = 0) ==> m - 1 + SUC 0 = m`; APPEND]);;

(* HOL4: mk_Apps_def *)
let mk_Apps_def = cake_def
  `(mk_Apps e [] = e) /\
   (mk_Apps e (CONS (t,other) ts) = clos_App t NONE (mk_Apps e ts) [other])`;;

(* a local helper: induction on expressions with one predicate *)
let CLOSP1AUX_mti_exp_ind =
  let th = ISPECL [`P:clos_exp->bool`; `\x:clos_exp list. T`; `\x:(num#clos_exp)list. T`;
                   `\x:num#clos_exp. T`] clos_exp_INDUCT in
  GEN `P:clos_exp->bool` (REWRITE_RULE[] (CONV_RULE (DEPTH_CONV BETA_CONV) th));;

(* discharge the induction hypotheses of a goal (an antecedent that is a   *)
(* universal statement or a conjunction with one) *)
let CLOSP1AUX_MTI_DISCH_IH_TAC : tactic = fun (asl,w as gl) ->
  let isih c = is_forall c || is_imp c in
  if is_imp w &&
     (let ant = lhand w in isih ant || (is_conj ant && exists isih (conjuncts ant)))
  then (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC) gl
  else ALL_TAC gl;;

(* HOL4: collect_apps_IMP_mk_Apps (acc is unused, as in HOL4; HOL4 ZIP     *)
(* (ts,other) is ZIP ts other, the lists have the same length)             *)
let collect_apps_IMP_mk_Apps = prove
 (`!e max_app (acc:clos_exp list) other e3.
     collect_apps max_app [] e = (other,e3) /\ no_mti e ==>
     ?ts. e = mk_Apps e3 (ZIP ts other) /\ LENGTH other = LENGTH ts /\
          LENGTH other <= max_app`,
  MATCH_MP_TAC CLOSP1AUX_mti_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CLOSP1AUX_MTI_DISCH_IH_TAC THEN REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  FIRST
   [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:tra list` THEN
    REWRITE_TAC[mk_Apps_def; ZIP; LENGTH; LE_0] THEN NO_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[no_mti_def; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  REWRITE_TAC[collect_apps_def; LENGTH; APPEND; ADD_CLAUSES] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:tra list` THEN
    REWRITE_TAC[mk_Apps_def; ZIP; LENGTH; LE_0]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP collect_apps_acc) THEN
  REWRITE_TAC[APPEND] THEN DISCH_THEN(X_CHOOSE_THEN `other':clos_exp list` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`a2:clos_exp`; `max_app:num`; `h:clos_exp`; `other':clos_exp list`;
                `e3:clos_exp`] collect_apps_cons) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`max_app - 1`; `acc:clos_exp list`; `other':clos_exp list`;
                                `e3:clos_exp`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ts:tra list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (a0:tra) ts` THEN
  ASM_REWRITE_TAC[ZIP; mk_Apps_def; LENGTH] THEN ASM_ARITH_TAC);;

(* local tactics for evaluation lemmas: close a goal with the assumption F; *)
(* normalize the assumptions (pairs, results, conjunctions, variables);     *)
(* rewrite the goal with the assumptions and reduce its case expressions   *)
let CLOSP1AUX_MTI_FALSE_TAC : tactic =
  FIRST_ASSUM(fun th -> if concl th = `F` then CONTR_TAC th else NO_TAC);;

let CLOSP1AUX_MTI_NORM_TAC : tactic =
  let rw = [PAIR_EQ; injectivity "result"; distinctness "result";
            GSYM (distinctness "result")] in
  REPEAT(CHANGED_TAC(
    RULE_ASSUM_TAC(REWRITE_RULE rw) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                   else NO_TAC)) THEN
    RVEQ_TAC)) THEN TRY CLOSP1AUX_MTI_FALSE_TAC;;

let CLOSP1AUX_MTI_EVAL_TAC : tactic =
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]));;

(* split the hypothesis on the evaluation of a list CONS x xs *)
let CLOSP1AUX_MTI_SPLIT_CONS_TAC : tactic =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_case_eq_thms; pair_case_eq] o
    ONCE_REWRITE_RULE[clos_evaluate_CONS] o
    check (fun th -> let c = concl th in is_eq c &&
                     CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
                     (let l = fst (dest_pair (rand (lhs c))) in
                      is_cons l && not (rand l = `[]:clos_exp list`)))) THEN
  CLOSP1AUX_MTI_NORM_TAC;;

(* HOL4: mk_Apps_err_1 [local] *)
let mk_Apps_err_1 = prove
 (`!ts other env1 (s1:(C,FFI)clos_state) e3.
     clos_evaluate (other,env1,s1) = (Rerr e2,s2) /\ LENGTH other = LENGTH (ts:tra list) ==>
     clos_evaluate ([mk_Apps e3 (ZIP ts other)],env1,s1) = (Rerr e2,s2)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `other:clos_exp list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ; distinctness "result"] THEN
  REWRITE_TAC[ZIP; mk_Apps_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP1AUX_MTI_SPLIT_CONS_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  REWRITE_TAC[clos_evaluate_def; LENGTH; ARITH_RULE `SUC 0 > 0`] THEN
  CLOSP1AUX_MTI_EVAL_TAC);;

(* HOL4: mk_Apps_err_2 [local] *)
let mk_Apps_err_2 = prove
 (`!ts other env1 (s1:(C,FFI)clos_state) e3 vs.
     clos_evaluate ([e3],env1,s2) = (Rerr e2,s2') /\
     clos_evaluate (other,env1,s1) = (Rval vs,s2) /\ LENGTH other = LENGTH (ts:tra list) ==>
     clos_evaluate ([mk_Apps e3 (ZIP ts other)],env1,s1) = (Rerr e2,s2')`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `other:clos_exp list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[ZIP; mk_Apps_def] THENL
   [REWRITE_TAC[clos_evaluate_def; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP1AUX_MTI_SPLIT_CONS_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  REWRITE_TAC[clos_evaluate_def; LENGTH; ARITH_RULE `SUC 0 > 0`] THEN
  CLOSP1AUX_MTI_EVAL_TAC);;

(* HOL4: collect_apps_no_mti *)
let collect_apps_no_mti = prove
 (`!k aux e res e1.
     collect_apps k aux e = (res,e1) /\ no_mti e /\ ALL no_mti aux ==>
     ALL no_mti res /\ no_mti e1`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CLOSP1AUX_MTI_DISCH_IH_TAC THEN REWRITE_TAC[collect_apps_def] THEN
  (COND_CASES_TAC ORELSE ALL_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[no_mti_def]) THEN ASM_REWRITE_TAC[ALL_APPEND]);;

(* HOL4: evaluate_mk_Apps_err [local] *)
let evaluate_mk_Apps_err = prove
 (`!other ts env1 (s1:(C,FFI)clos_state) vs.
     clos_evaluate (other,env1,s1) = (Rval vs,s3) /\
     clos_evaluate ([e],env1,s3) = (Rerr e3,s2') /\ LENGTH other = LENGTH (ts:tra list) ==>
     clos_evaluate ([mk_Apps e (ZIP ts other)],env1,s1) = (Rerr e3,s2')`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ts:tra list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[ZIP; mk_Apps_def] THENL
   [REWRITE_TAC[clos_evaluate_def; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP1AUX_MTI_SPLIT_CONS_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  REWRITE_TAC[clos_evaluate_def; LENGTH; ARITH_RULE `SUC 0 > 0`] THEN
  CLOSP1AUX_MTI_EVAL_TAC);;

(* HOL4: evaluate_apps_def *)
let evaluate_apps_def = cake_def
  `(evaluate_apps f [] (s:(C,FFI)clos_state) = (Rval [f], s)) /\
   (evaluate_apps f (CONS x xs) s =
      match evaluate_apps f xs s with
        (Rval [v], s1) -> evaluate_app NONE v [x] s1
      | res -> res)`;;

(* a local helper: evaluate_apps gives one value *)
let CLOSP1AUX_mti_evaluate_apps_SING = prove
 (`!xs f (s:(C,FFI)clos_state) r s'.
     evaluate_apps f xs s = (Rval r,s') ==> ?v. r = [v]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[evaluate_apps_def; PAIR_EQ; injectivity "result"] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[clos_case_eq_thms; pair_case_eq] THEN REPEAT STRIP_TAC THEN
  CLOSP1AUX_MTI_NORM_TAC THEN
  RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL]) THEN
  TRY CLOSP1AUX_MTI_FALSE_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_app_IMP_LENGTH o
    check (fun th -> CLOSPROPSAUX_is_app "evaluate_app" (lhs (concl th)))) THEN
  REWRITE_TAC[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

(* name the value of a term tm (a pair whose first part is a result) and *)
(* split the result *)
let CLOSP1AUX_MTI_NAME_SPLIT_TAC (tm:term) : tactic = fun (asl,w as gl) ->
  let rty,sty = (match dest_type (type_of tm) with (_,[a;b]) -> a,b | _ -> failwith "NS") in
  let r = genvar rty and s = genvar sty in
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
   CASES_ON r THEN CASE_REWRITE_TAC[]) gl;;

(* HOL4: evaluate_mk_Apps_ok [local] *)
let evaluate_mk_Apps_ok = prove
 (`!other ts env1 (s1:(C,FFI)clos_state) vs.
     clos_evaluate ([e],env1,s3) = (Rval [f],s2') /\
     clos_evaluate (other,env1,s1) = (Rval vs,s3) /\ LENGTH other = LENGTH (ts:tra list) ==>
     clos_evaluate ([mk_Apps e (ZIP ts other)],env1,s1) = evaluate_apps f vs s2'`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ts:tra list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; mk_Apps_def] THENL
   [REWRITE_TAC[clos_evaluate_def; PAIR_EQ; injectivity "result"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[evaluate_apps_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SPLIT_CONS_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN
  REWRITE_TAC[clos_evaluate_def; LENGTH; ARITH_RULE `SUC 0 > 0`] THEN CLOSP1AUX_MTI_EVAL_TAC THEN
  REWRITE_TAC[evaluate_apps_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP clos_evaluate_SING o
    check (fun th -> let c = concl th in is_eq c &&
                     CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
                     fst (dest_pair (rand (lhs c))) = `[h:clos_exp]`)) THEN
  RVEQ_TAC THEN REWRITE_TAC[HD] THEN
  CLOSP1AUX_MTI_NAME_SPLIT_TAC `evaluate_apps f (a':clos_v list) (s2':(C,FFI)clos_state)` THEN
  FIRST_ASSUM(fun th -> try STRIP_ASSUME_TAC (MATCH_MP CLOSP1AUX_mti_evaluate_apps_SING th)
                        with Failure _ -> NO_TAC) THEN
  RVEQ_TAC THEN CASE_REWRITE_TAC[HD]);;

(* HOL4: dest_closure_NONE_IMP_apps [local] *)
let dest_closure_NONE_IMP_apps = prove
 (`!xs f1 (s1:(C,FFI)clos_state).
     dest_closure (clos_state_max_app s1) NONE f1 [LAST xs] = NONE /\ ~(xs = []) ==>
     evaluate_apps f1 xs s1 = (Rerr (Rabort Rtype_error),s1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN
  CASES_ON `t:clos_v list` THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL] THEN STRIP_TAC THENL
   [REWRITE_TAC[evaluate_apps_def] THEN CASE_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ONCE_REWRITE_TAC[evaluate_apps_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f1:clos_v`; `s1:(C,FFI)clos_state`]) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; LAST] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]]);;

(* a local helper: evaluate_app gives one value *)
let CLOSP1AUX_mti_evaluate_app_SING = prove
 (`!lo f xs (s:(C,FFI)clos_state) r s'.
     evaluate_app lo f xs s = (Rval r,s') ==> ?v. r = [v]`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP evaluate_app_IMP_LENGTH) THEN
  REWRITE_TAC[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

(* HOL4: evaluate_apps_SNOC [local] *)
let evaluate_apps_SNOC = prove
 (CASE_TERM `!xs x f (s:(C,FFI)clos_state).
     evaluate_apps f (SNOC x xs) s =
     match evaluate_app NONE f [x] s with
       (Rval [v], s) -> evaluate_apps v xs s
     | res -> res`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[evaluate_apps_def] THEN CASE_REWRITE_TAC[];
    ONCE_REWRITE_TAC[evaluate_apps_def] THEN ASM_REWRITE_TAC[]] THEN
  CLOSP1AUX_MTI_NAME_SPLIT_TAC `evaluate_app NONE f [x:clos_v] (s:(C,FFI)clos_state)` THEN
  FIRST_ASSUM(fun th -> try STRIP_ASSUME_TAC (MATCH_MP CLOSP1AUX_mti_evaluate_app_SING th)
                        with Failure _ -> NO_TAC) THEN
  RVEQ_TAC THEN CASE_REWRITE_TAC[evaluate_apps_def]);;

(* local helpers: a function of one argument applied to one value; the     *)
(* evaluation of a function of one argument                                *)
let CLOSP1AUX_mti_app_Clos1 = prove
 (`!env body x (s:(C,FFI)clos_state).
     1 <= clos_state_max_app s ==>
     evaluate_app NONE (clos_Closure NONE [] env 1 body) [x] s =
     if clos_state_clock s = 0
     then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
     else clos_evaluate ([body],CONS x env,clos_dec_clock 1 s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[dest_closure_def] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[check_loc_def; LENGTH; REVERSE; TAKE_DEF; DROP_DEF;
                                     APPEND; ARITH_RULE `n < 1 <=> n = 0`] THEN
                     CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[])) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CLOSP1AUX_MTI_NAME_SPLIT_TAC `clos_evaluate ([body],CONS (x:clos_v) env,
                                  clos_dec_clock 1 (s:(C,FFI)clos_state))` THEN
  FIRST_ASSUM(fun th -> try STRIP_ASSUME_TAC (MATCH_MP clos_evaluate_SING th)
                        with Failure _ -> NO_TAC) THEN
  RVEQ_TAC THEN CASE_REWRITE_TAC[evaluate_app_NIL]);;

let CLOSP1AUX_mti_eval_Fn1 = prove
 (`!t e env (s:(C,FFI)clos_state).
     1 <= clos_state_max_app s ==>
     clos_evaluate ([Fn t NONE NONE 1 e],env,s) = (Rval [clos_Closure NONE [] env 1 e],s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_evaluate_def; ARITH] THEN CASE_REWRITE_TAC[]);;

(* the closure of a function of one argument, applied to the last value of *)
(* SNOC x l; ts nonempty *)
let CLOSP1AUX_MTI_CLOS_STEP_TAC : tactic =
  REWRITE_TAC[LENGTH_SNOC] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[evaluate_apps_SNOC; CLOSP1AUX_mti_app_Clos1] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[];;

(* HOL4: evaluate_apps_Clos_timeout [local] *)
let evaluate_apps_Clos_timeout = prove
 (`!ys ts (s1:(C,FFI)clos_state) e1 env.
     clos_state_clock s1 < LENGTH ys /\ LENGTH ys <= LENGTH (ts:mlstring list) /\
     1 <= clos_state_max_app s1 ==>
     evaluate_apps (clos_Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
     (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s1)`,
  MATCH_MP_TAC SNOC_INDUCT THEN REWRITE_TAC[LENGTH; LT] THEN
  X_GEN_TAC `l:clos_v list` THEN DISCH_TAC THEN X_GEN_TAC `x:clos_v` THEN REPEAT GEN_TAC THEN
  CLOSP1AUX_MTI_CLOS_STEP_TAC THEN
  CASES_ON `ts:mlstring list` THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[mk_Fns_def; CLOSP1AUX_mti_eval_Fn1; CLOSPROPSAUX_max_app_dec_clock] THEN
  CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM (SPEC `1` CLOSPROPSAUX_dec_clock_clock0)] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[CLOSPROPSAUX_max_app_dec_clock] THEN ASM_ARITH_TAC);;

(* HOL4: evaluate_apps_Clos_timeout_alt [local] *)
let evaluate_apps_Clos_timeout_alt = prove
 (`!ys ts (s1:(C,FFI)clos_state) e1 env.
     clos_state_clock s1 <= LENGTH (ts:mlstring list) /\ LENGTH ts < LENGTH ys /\
     1 <= clos_state_max_app s1 ==>
     evaluate_apps (clos_Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
     (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s1)`,
  MATCH_MP_TAC SNOC_INDUCT THEN REWRITE_TAC[LENGTH; LT] THEN
  X_GEN_TAC `l:clos_v list` THEN DISCH_TAC THEN X_GEN_TAC `x:clos_v` THEN REPEAT GEN_TAC THEN
  CLOSP1AUX_MTI_CLOS_STEP_TAC THEN
  CASES_ON `ts:mlstring list` THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[mk_Fns_def; CLOSP1AUX_mti_eval_Fn1; CLOSPROPSAUX_max_app_dec_clock] THEN
  CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM (SPEC `1` CLOSPROPSAUX_dec_clock_clock0)] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[CLOSPROPSAUX_max_app_dec_clock] THEN ASM_ARITH_TAC);;

(* a local helper: no decrement of the clock *)
let CLOSP1AUX_mti_dec_clock_0 = prove
 (`!s:(C,FFI)clos_state. clos_dec_clock 0 s = s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM; SUB_0]);;

(* HOL4: evaluate_apps_Clos_short [local] *)
let evaluate_apps_Clos_short = prove
 (`!ys ts (s1:(C,FFI)clos_state) e1 env.
     LENGTH ys <= clos_state_clock s1 /\ LENGTH ys <= LENGTH (ts:mlstring list) /\
     1 <= clos_state_max_app s1 ==>
     evaluate_apps (clos_Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
     (Rval [clos_Closure NONE [] (APPEND ys env) 1 (mk_Fns (DROP (LENGTH ys) ts) e1)],
      clos_dec_clock (LENGTH ys) s1)`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; evaluate_apps_def; APPEND; DROP; CLOSP1AUX_mti_dec_clock_0];
    ALL_TAC] THEN
  X_GEN_TAC `l:clos_v list` THEN DISCH_TAC THEN X_GEN_TAC `x:clos_v` THEN REPEAT GEN_TAC THEN
  CLOSP1AUX_MTI_CLOS_STEP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CASES_ON `ts:mlstring list` THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[mk_Fns_def; CLOSP1AUX_mti_eval_Fn1; CLOSPROPSAUX_max_app_dec_clock] THEN
  CASE_REWRITE_TAC[] THEN
  W(fun (asl,w) -> FIRST_X_ASSUM(fun ih -> MP_TAC(PART_MATCH (lhand o rand) ih (lhand w)))) THEN
  REWRITE_TAC[CLOSPROPSAUX_max_app_dec_clock] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LENGTH_SNOC; DROP; CLOSPROPSAUX_dec_clock_dec_clock; SNOC_APPEND;
              GSYM APPEND_ASSOC; APPEND; ADD1; ADD_SYM]);;

(* HOL4: evaluate_apps_Clos_long [local] *)
let evaluate_apps_Clos_long = prove
 (CASE_TERM `!ys ts (s1:(C,FFI)clos_state) e1 env.
     LENGTH (ts:mlstring list) < clos_state_clock s1 /\ LENGTH ts < LENGTH ys /\
     1 <= clos_state_max_app s1 ==>
     evaluate_apps (clos_Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
     match clos_evaluate ([e1],APPEND (REVERSE (TAKE (1 + LENGTH ts) (REVERSE ys))) env,
                          clos_dec_clock (1 + LENGTH ts) s1) with
       (Rval [v],s) -> evaluate_apps v (REVERSE (DROP (1 + LENGTH ts) (REVERSE ys))) s
     | res -> res`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  X_GEN_TAC `l:clos_v list` THEN DISCH_TAC THEN X_GEN_TAC `x:clos_v` THEN REPEAT GEN_TAC THEN
  CLOSP1AUX_MTI_CLOS_STEP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REVERSE_SNOC] THEN
  CASES_ON `ts:mlstring list` THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  REWRITE_TAC[LENGTH; mk_Fns_def] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[TAKE_DEF; DROP_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[TAKE; DROP; REVERSE; APPEND; REVERSE_REVERSE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSP1AUX_mti_eval_Fn1; CLOSPROPSAUX_max_app_dec_clock] THEN
  CASE_REWRITE_TAC[] THEN
  W(fun (asl,w) -> FIRST_X_ASSUM(fun ih -> MP_TAC(PART_MATCH (lhand o rand) ih (lhand w)))) THEN
  REWRITE_TAC[CLOSPROPSAUX_max_app_dec_clock] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ARITH_RULE `1 + SUC n = SUC (1 + n)`; ARITH_RULE `1 + 1 + n = SUC (1 + n)`;
              TAKE; DROP; REVERSE; CLOSPROPSAUX_dec_clock_dec_clock; GSYM APPEND_ASSOC;
              APPEND]);;

(* HOL4: LIST_REL_f_rel_IMP [local] *)
let LIST_REL_f_rel_IMP = prove
 (`!fns funs1. ALL2 (clos_mtiProof_f_rel max_app) funs1 fns ==> !x. ~(MEM (0,x) fns)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; LIST_REL_CONS2] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:num#clos_exp` (X_CHOOSE_THEN `t1:(num#clos_exp)list`
    STRIP_ASSUME_TAC)) THEN
  GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `clos_mtiProof_f_rel max_app h1 (0,x)` THEN
  MP_TAC(ISPEC `h1:num#clos_exp` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_mtiProof_f_rel_def] THEN ARITH_TAC);;

(* HOL4: v_rel_simps [simp] (HOL4 computes it with SIMP_CONV from v_rel_cases) *)
let clos_mtiProof_v_rel_simps = prove
 (`(!max_app x n. clos_mtiProof_v_rel max_app x (clos_Number n) <=> x = clos_Number n) /\
   (!max_app x n p. clos_mtiProof_v_rel max_app x (clos_Block n p) <=>
                    ?xs. x = clos_Block n xs /\ ALL2 (clos_mtiProof_v_rel max_app) xs p) /\
   (!max_app x p. clos_mtiProof_v_rel max_app x (clos_Word64 p) <=> x = clos_Word64 p) /\
   (!max_app x p. clos_mtiProof_v_rel max_app x (ByteVector p) <=> x = ByteVector p) /\
   (!max_app x b p. clos_mtiProof_v_rel max_app x (clos_RefPtr b p) <=> x = clos_RefPtr b p) /\
   (!max_app x x1 x2 x3 x4 x5.
      clos_mtiProof_v_rel max_app x (clos_Closure x1 x2 x3 x4 x5) <=>
      x1 = NONE /\
      ?args1 env1 e1 ts.
        x = clos_Closure NONE [] (APPEND args1 env1) 1 (mk_Fns ts e1) /\
        1 + LENGTH ts + LENGTH args1 = x4 /\
        clos_mtiProof_code_rel max_app [e1] [x5] /\
        ALL2 (clos_mtiProof_v_rel max_app) env1 x3 /\
        ALL2 (clos_mtiProof_v_rel max_app) args1 x2) /\
   (!max_app x y1 y2 y3 y4 y5.
      clos_mtiProof_v_rel max_app x (clos_Recclosure y1 y2 y3 y4 y5) <=>
      (y1 = NONE /\ y2 = [] /\
       ?env1 funs1.
         x = clos_Recclosure NONE [] env1 funs1 y5 /\
         ALL2 (clos_mtiProof_f_rel max_app) funs1 y4 /\
         ALL2 (clos_mtiProof_v_rel max_app) env1 y3 /\ y5 < LENGTH y4) \/
      (y1 = NONE /\
       ?args1 env1 funs1 recc ts e1 e2 arg_count.
         x = clos_Closure NONE [] (APPEND (APPEND args1 recc) env1) 1 (mk_Fns ts e1) /\
         ALL2 (clos_mtiProof_f_rel max_app) funs1 y4 /\
         ALL2 (clos_mtiProof_v_rel max_app) env1 y3 /\
         ALL2 (clos_mtiProof_v_rel max_app) args1 y2 /\ ~(y2 = []) /\
         y5 < LENGTH y4 /\ EL y5 y4 = (arg_count,e2) /\
         1 + LENGTH ts + LENGTH args1 = arg_count /\
         clos_mtiProof_code_rel max_app [e1] [e2] /\
         ALL2 (clos_mtiProof_v_rel max_app) recc
           (list_of_seq (clos_Recclosure NONE [] y3 y4) (LENGTH y4)))) /\
   (!max_app x b. clos_mtiProof_v_rel max_app x (clos_Boolv b) <=> x = clos_Boolv b) /\
   (!max_app x. clos_mtiProof_v_rel max_app x clos_Unit <=> x = clos_Unit)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_Boolv_def; clos_Unit_def] THEN
  GEN_REWRITE_TAC LAND_CONV [clos_mtiProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC; LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[LIST_REL_NIL] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let _ = cake_add_simps [clos_mtiProof_v_rel_simps];;

(* HOL4: v_rel_opt_thm [local] *)
let v_rel_opt_thm = prove
 (`!m. v_rel_opt m = OPTREL (clos_mtiProof_v_rel m)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  CASES_ON `x:clos_v option` THEN CASES_ON `x':clos_v option` THEN
  REWRITE_TAC[v_rel_opt_def; OPTREL_THM]);;

(* HOL4: simple_val_rel *)
let clos_mtiProof_simple_val_rel = prove
 (`clos_simple_val_rel (clos_mtiProof_v_rel max_app_n)`,
  REWRITE_TAC[clos_simple_val_rel_def; clos_mtiProof_v_rel_simps] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[clos_isClos_def]);;

(* local helpers: an update of related finite maps; clos_ref_rel... with   *)
(* the right side known; the references of related states                 *)
let CLOSP1AUX_mti_FMAP_REL_FUPDATE = prove
 (`!(r:A->B->bool) (f1:(K,A)fmap) f2 k a b.
     clos_mtiProof_FMAP_REL r f1 f2 /\ r a b ==>
     clos_mtiProof_FMAP_REL r (f1 |+ (k,a)) (f2 |+ (k,b))`,
  REWRITE_TAC[clos_mtiProof_FMAP_REL_def; FDOM_FUPDATE; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

let CLOSP1AUX_mti_ref_rel_right = prove
 (`(!max_app x bs. clos_mtiProof_ref_rel max_app x (clos_ByteArray bs) <=>
                   x = clos_ByteArray bs) /\
   (!max_app x ys. clos_mtiProof_ref_rel max_app x (clos_ValueArray ys) <=>
                   ?xs. x = clos_ValueArray xs /\ ALL2 (clos_mtiProof_v_rel max_app) xs ys) /\
   (!max_app x m w. clos_mtiProof_ref_rel max_app x (clos_Thunk m w) <=>
                    ?v. x = clos_Thunk m v /\ clos_mtiProof_v_rel max_app v w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_mtiProof_ref_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN MESON_TAC[]);;

let CLOSP1AUX_mti_flookup_rel = prove
 (`!(s1:(C,FFI)clos_state) s2 n.
     clos_mtiProof_state_rel s1 s2 ==>
     OPTREL (clos_mtiProof_ref_rel (clos_state_max_app s1))
            (FLOOKUP (clos_state_refs s1) n) (FLOOKUP (clos_state_refs s2) n)`,
  REWRITE_TAC[clos_mtiProof_state_rel_def; clos_mtiProof_FMAP_REL_def] THEN
  REPEAT STRIP_TAC THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n` THENL
   [SUBGOAL_THEN `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) n = NONE` SUBST1_TAC THENL
     [UNDISCH_TAC `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) n = NONE` THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[distinctness "option"];
      REWRITE_TAC[OPTREL_THM]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `a:(clos_v)clos_ref`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPTREL_THM]]);;

(* a local helper: updating related references keeps the states related *)
let CLOSP1AUX_mti_state_rel_refs_upd = prove
 (`!(s1:(C,FFI)clos_state) s2 p a b.
     clos_mtiProof_state_rel s1 s2 /\
     clos_mtiProof_ref_rel (clos_state_max_app s1) a b ==>
     clos_mtiProof_state_rel
       (clos_state_refs_fupd (K (clos_state_refs s1 |+ (p,a))) s1)
       (clos_state_refs_fupd (K (clos_state_refs s2 |+ (p,b))) s2)`,
  REWRITE_TAC[clos_mtiProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[CLOSP1AUX_mti_FMAP_REL_FUPDATE]);;

(* HOL4: simple_state_rel *)
let clos_mtiProof_simple_state_rel = prove
 (`clos_simple_state_rel (clos_mtiProof_v_rel max_app_n)
     (\(s:(C,FFI)clos_state) (t:(C,FFI)clos_state).
        clos_state_max_app s = max_app_n /\ clos_mtiProof_state_rel s t)`,
  REWRITE_TAC[clos_simple_state_rel_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq (concl th) && rhs (concl th) = `max_app_n:num`)) THENL
   [FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_mti_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_NONE];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_mti_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP1AUX_mti_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_mti_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP1AUX_mti_ref_rel_right] THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `ptr:num` o MATCH_MP CLOSP1AUX_mti_flookup_rel) THEN
    ASM_REWRITE_TAC[OPTREL_SOME; CLOSP1AUX_mti_ref_rel_right] THEN MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_mtiProof_state_rel_def; v_rel_opt_thm]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "clos_mtiProof_FMAP_REL" (concl th)
                        then ASSUME_TAC (CONJUNCT1 (REWRITE_RULE[clos_mtiProof_FMAP_REL_def] th))
                        else NO_TAC) THEN
  ASM_REWRITE_TAC[clos_mtiProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
                  v_rel_opt_thm] THEN
  MATCH_MP_TAC CLOSP1AUX_mti_FMAP_REL_FUPDATE THEN
  ASM_REWRITE_TAC[clos_mtiProof_ref_rel_simps; injectivity "clos_ref"; UNWIND_THM1]);;

(* HOL4: state_rel_opt_rel_refs [local] *)
let clos_mtiProof_state_rel_opt_rel_refs = prove
 (`(clos_mtiProof_state_rel (s1:(C,FFI)clos_state) s2 /\
    FLOOKUP (clos_state_refs s1) n = r1 ==>
    ?r2. FLOOKUP (clos_state_refs s2) n = r2 /\
         OPTREL (clos_mtiProof_ref_rel (clos_state_max_app s1)) r1 r2) /\
   (clos_mtiProof_state_rel s1 s2 /\ FLOOKUP (clos_state_refs s2) n = r2 ==>
    ?r1. FLOOKUP (clos_state_refs s1) n = r1 /\
         OPTREL (clos_mtiProof_ref_rel (clos_state_max_app s1)) r1 r2)`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[UNWIND_THM1] THEN
  ASM_SIMP_TAC[CLOSP1AUX_mti_flookup_rel]);;

(* a local helper: dest_thunk of related values agree on NotThunk *)
let CLOSP1AUX_mti_not_thunk = prove
 (`!(s1:(C,FFI)clos_state) s2 x y.
     clos_mtiProof_state_rel s1 s2 /\ clos_mtiProof_v_rel (clos_state_max_app s1) x y ==>
     (clos_dest_thunk [x] (clos_state_refs s1) = clos_NotThunk <=>
      clos_dest_thunk [y] (clos_state_refs s2) = clos_NotThunk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_mtiProof_v_rel (clos_state_max_app (s1:(C,FFI)clos_state))`;
                 `\(r:(C,FFI)clos_state) (t:(C,FFI)clos_state).
                    clos_state_max_app r = clos_state_max_app (s1:(C,FFI)clos_state) /\
                    clos_mtiProof_state_rel r t`;
                 `s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                 `x:clos_v`; `y:clos_v`; `Evaluated`] CLOSPROPSAUX_bad_thunk_rel) THEN
  ASM_REWRITE_TAC[GEN_ALL clos_mtiProof_simple_val_rel;
                  GEN_ALL clos_mtiProof_simple_state_rel; clos_bad_thunk_update_def] THEN
  MESON_TAC[]);;

(* HOL4: rel_update_thunk [local] *)
let clos_mtiProof_rel_update_thunk = prove
 (`clos_mtiProof_state_rel (s1:(C,FFI)clos_state) s2 /\
   ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) vs ys ==>
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = NONE ==>
    clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = NONE) /\
   (clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 ==>
    ?refs1. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 /\
            clos_mtiProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                    (clos_state_refs_fupd (K refs2) s2))`,
  STRIP_TAC THEN
  SUBGOAL_THEN `(vs = [] /\ ys = []) \/
                (?x y. vs = [x] /\ ys = [y] /\
                       clos_mtiProof_v_rel (clos_state_max_app (s1:(C,FFI)clos_state)) x y) \/
                (?x1 x2 r1 y1 y2 r2. vs = CONS x1 (CONS x2 r1) /\
                                     ys = CONS y1 (CONS y2 r2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 (clos_mtiProof_v_rel (clos_state_max_app (s1:(C,FFI)clos_state)))
                      vs ys` THEN
    STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONS_11; NOT_CONS_NIL; UNWIND_THM1] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"];
    ALL_TAC;
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"]] THEN
  ASM_REWRITE_TAC[clos_update_thunk_def] THEN
  MP_TAC(SPECL [`s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `x:clos_v`; `y:clos_v`]
               CLOSP1AUX_mti_not_thunk) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                 clos_NotThunk` THENL
   [SUBGOAL_THEN `clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                  clos_NotThunk` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    SUBGOAL_THEN `~(clos_dest_thunk [x] (clos_state_refs (s1:(C,FFI)clos_state)) =
                    clos_NotThunk)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSSEMAUX_dest_thunk_NONE; distinctness "option"]] THEN
  REWRITE_TAC[store_thunk_def] THEN
  MP_TAC(SPECL [`s1:(C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `ptr:num`]
               CLOSP1AUX_mti_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM; case_def "option"; distinctness "option"] THEN
  CASES_ON `a':(clos_v)clos_ref` THEN REWRITE_TAC[CLOSP1AUX_mti_ref_rel_right] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[distinctness "option"] THEN
  TRY(CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC CLOSP1AUX_mti_state_rel_refs_upd THEN
  ASM_REWRITE_TAC[clos_mtiProof_ref_rel_simps; injectivity "clos_ref"; UNWIND_THM1]);;

(* HOL4: do_app_lemma *)
let clos_mtiProof_do_app_lemma = prove
 (CASE_TERM
  `clos_mtiProof_state_rel s (t:(C,FFI)clos_state) /\
   ALL2 (clos_mtiProof_v_rel (clos_state_max_app s)) xs ys ==>
   match clos_do_app opp ys t with
     Rerr err2 -> (?err1. clos_do_app opp xs s = Rerr err1 /\
                          exc_rel (clos_mtiProof_v_rel (clos_state_max_app s)) err1 err2)
   | Rval (y,t1) -> ?x s1. clos_mtiProof_v_rel (clos_state_max_app s) x y /\
                           clos_mtiProof_state_rel s1 t1 /\
                           clos_do_app opp xs s = Rval (x,s1)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_mtiProof_v_rel (clos_state_max_app (s:(C,FFI)clos_state))`;
                 `\(r:(C,FFI)clos_state) (t:(C,FFI)clos_state).
                     clos_state_max_app r = clos_state_max_app (s:(C,FFI)clos_state) /\
                     clos_mtiProof_state_rel r t`;
                 `s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `xs:clos_v list`;
                 `ys:clos_v list`; `opp:clos_op`] simple_val_rel_do_app_rev) THEN
  REWRITE_TAC[GEN_ALL clos_mtiProof_simple_val_rel; GEN_ALL clos_mtiProof_simple_state_rel] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `clos_do_app opp ys (t:(C,FFI)clos_state)` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:clos_v#(C,FFI)clos_state` THEN CASE_REWRITE_TAC[]) THEN MESON_TAC[]);;

(* HOL4: v_rel_IMP_v_to_bytes [local] *)
let clos_mtiProof_v_rel_IMP_v_to_bytes = prove
 (`clos_mtiProof_v_rel max_app x y ==> clos_v_to_bytes y = clos_v_to_bytes x`,
  MESON_TAC[clos_mtiProof_simple_val_rel; clos_simple_val_rel_v_to_bytes]);;

(* HOL4: v_rel_IMP_v_to_words [local] *)
let clos_mtiProof_v_rel_IMP_v_to_words = prove
 (`clos_mtiProof_v_rel max_app x y ==> clos_v_to_words y = clos_v_to_words x`,
  MESON_TAC[clos_mtiProof_simple_val_rel; clos_simple_val_rel_v_to_words]);;

(* a local helper: the oracle conditions of simple_val_rel_do_install *)
let CLOSP1AUX_mti_simple_compile_state_rel = prove
 (`!m. simple_compile_state_rel (clos_mtiProof_v_rel m)
        (\(r:(C,FFI)clos_state) (t:(C,FFI)clos_state).
           clos_state_max_app r = m /\ clos_mtiProof_state_rel r t)
        (clos_mti_compile_inc m) (clos_mtiProof_code_rel m)`,
  GEN_TAC THEN
  REWRITE_TAC[simple_compile_state_rel_def; clos_mtiProof_simple_state_rel] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq (concl th) && rhs (concl th) = `m:num`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_mtiProof_state_rel_def]) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; clos_mti_compile_inc_def; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[intro_multi_length; clos_mtiProof_code_rel_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    GEN_TAC THEN
    REWRITE_TAC[clos_mtiProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
                shift_seq_def] THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

(* HOL4: do_install_lemma [local] *)
let clos_mtiProof_do_install_lemma = prove
 (CASE_TERM
  `clos_mtiProof_state_rel (s:(C,FFI)clos_state) t /\
   ALL2 (clos_mtiProof_v_rel (clos_state_max_app s)) xs ys ==>
   match clos_do_install xs s with
     (Rerr err1,s1) -> ?err2 t1. clos_do_install ys t = (Rerr err2,t1) /\
                                 exc_rel (clos_mtiProof_v_rel (clos_state_max_app s)) err1 err2 /\
                                 clos_state_max_app s1 = clos_state_max_app s /\
                                 clos_mtiProof_state_rel s1 t1
   | (Rval exps1,s1) -> ?exps2 t1. (clos_state_max_app s1 = clos_state_max_app s /\
                                    clos_mtiProof_state_rel s1 t1) /\ ~(exps1 = []) /\
                                   clos_mtiProof_code_rel (clos_state_max_app s) exps1 exps2 /\
                                   clos_do_install ys t = (Rval exps2,t1)`,
  STRIP_TAC THEN
  MP_TAC(ISPECL [`clos_mti_compile_inc (clos_state_max_app (s:(C,FFI)clos_state)):
                    clos_prog->clos_prog`;
                 `clos_mtiProof_v_rel (clos_state_max_app (s:(C,FFI)clos_state))`;
                 `\(r:(C,FFI)clos_state) (t:(C,FFI)clos_state).
                     clos_state_max_app r = clos_state_max_app (s:(C,FFI)clos_state) /\
                     clos_mtiProof_state_rel r t`;
                 `clos_mtiProof_code_rel (clos_state_max_app (s:(C,FFI)clos_state))`;
                 `s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `xs:clos_v list`;
                 `ys:clos_v list`] simple_val_rel_do_install) THEN
  REWRITE_TAC[GEN_ALL clos_mtiProof_simple_val_rel; CLOSP1AUX_mti_simple_compile_state_rel] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `clos_do_install xs (s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_exp list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` SUBST1_TAC)) THEN
  CASES_ON `r:(clos_exp list,clos_v)result` THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4: intro_multi_EQ_NIL [simp] *)
let intro_multi_EQ_NIL = prove
 (`!max_app es. intro_multi max_app es = [] <=> es = []`,
  ONCE_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN REWRITE_TAC[intro_multi_length]);;

let _ = cake_add_simps [intro_multi_EQ_NIL];;

(* HOL4: intro_multi_nil *)
let intro_multi_nil = prove
 (`intro_multi x [] = []`,
  REWRITE_TAC[intro_multi_EQ_NIL]);;

(* HOL4: result_rel_Rval2 (as closProps' clos_result_rel_Rval2) *)
let clos_mtiProof_result_rel_Rval2 = prove
 (`!(P:A->B->bool) (P':C->D->bool) x v'.
     result_rel P P' x (Rval v') <=> ?v. x = Rval v /\ P v v'`,
  REWRITE_TAC[clos_result_rel_Rval2]);;

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The backwards simulation (HOL4: evaluate_intro_multi), proved by the      *)
(* induction of closProps (CLOSPROPSAUX_evaluate_ind) on the evaluation of   *)
(* the target, with one lemma per case and local tactics: the source         *)
(* expression is found by inverting intro_multi; an induction hypothesis is  *)
(* applied to a named sub-evaluation of the target and the matching source   *)
(* sub-expression, which gives the source sub-evaluation                     *)
(* ------------------------------------------------------------------------- *)

let CLOSP1AUX_mti_ind =
  let p = `\ys env2 (t1:(C,FFI)clos_state).
     !res2 t2 env1 s1 xs.
       clos_evaluate (ys,env2,t1) = (res2,t2) /\
       ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) env1 env2 /\
       clos_mtiProof_state_rel s1 t1 /\
       clos_mtiProof_code_rel (clos_state_max_app s1) xs ys ==>
       ?res1 s2.
         clos_evaluate (xs,env1,s1) = (res1,s2) /\
         result_rel (ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)))
                    (clos_mtiProof_v_rel (clos_state_max_app s1)) res1 res2 /\
         clos_mtiProof_state_rel s2 t2`
  and q = `\loc_opt f2 args2 (t1:(C,FFI)clos_state).
     !res2 t2 f1 args1 s1.
       evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\ loc_opt = NONE /\
       clos_mtiProof_v_rel (clos_state_max_app s1) f1 f2 /\
       ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) args1 args2 /\
       clos_mtiProof_state_rel s1 t1 /\ LENGTH args1 <= clos_state_max_app s1 ==>
       ?res1 s2.
         evaluate_apps f1 args1 s1 = (res1,s2) /\
         result_rel (ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)))
                    (clos_mtiProof_v_rel (clos_state_max_app s1)) res1 res2 /\
         clos_mtiProof_state_rel s2 t2` in
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL [p;q] CLOSPROPSAUX_evaluate_ind);;
let CLOSP1AUX_mti_cases = conjuncts (lhand (concl CLOSP1AUX_mti_ind));;

(* local helpers: a source of a singleton or a CONS CONS target *)
let CLOSP1AUX_mti_code_rel_sing = prove
 (`!m xs t. clos_mtiProof_code_rel m xs [t] ==>
            ?y. xs = [y] /\ no_mti y /\ [t] = intro_multi m [y]`,
  REWRITE_TAC[clos_mtiProof_code_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:clos_exp list->num`) THEN
  REWRITE_TAC[intro_multi_length; LENGTH; ONE] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `h:clos_exp` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN ASM_REWRITE_TAC[]);;

let CLOSP1AUX_mti_code_rel_cons = prove
 (`!m xs a b rest. clos_mtiProof_code_rel m xs (CONS a (CONS b rest)) ==>
     ?y1 y2 ys. xs = CONS y1 (CONS y2 ys) /\
                clos_mtiProof_code_rel m [y1] [a] /\
                clos_mtiProof_code_rel m (CONS y2 ys) (CONS b rest)`,
  REWRITE_TAC[clos_mtiProof_code_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:clos_exp list->num`) THEN
  REWRITE_TAC[intro_multi_length; LENGTH] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[LENGTH_EQ_CONS] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`h:clos_exp`; `h':clos_exp`; `t':clos_exp list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN ASM_REWRITE_TAC[ALL] THEN
  UNDISCH_TAC `CONS (a:clos_exp) (CONS b rest) = intro_multi m (CONS h (CONS h' t'))` THEN
  REWRITE_TAC[ISPECL [`CONS (h':clos_exp) t'`; `h:clos_exp`] intro_multi_cons] THEN
  MP_TAC(SPECL [`h:clos_exp`; `m:num`] intro_multi_sing) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HD; CONS_11] THEN SIMP_TAC[]);;

(* invert the code relation of a singleton target: the source is a single  *)
(* expression, split by its constructor; the wrong constructors are refuted *)
let CLOSP1AUX_MTI_SING_INV_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSPROPSAUX_is_app "clos_mtiProof_code_rel" c &&
       (try length (dest_list (rand c)) = 1 with Failure _ -> false)
    then X_CHOOSE_THEN `y:clos_exp` STRIP_ASSUME_TAC (MATCH_MP CLOSP1AUX_mti_code_rel_sing th)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                             rhs (concl th) = `[y:clos_exp]` then SUBST_ALL_TAC th
                          else NO_TAC) THEN
  CASES_ON `y:clos_exp` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[no_mti_def]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[intro_multi_def]) THEN
  REPEAT PAIRARG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; injectivity "clos_exp"; distinctness "clos_exp"]) THEN
  TRY CLOSP1AUX_MTI_FALSE_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  RVEQ_TAC;;

(* local helpers: evaluate_apps keeps max_app; values related to booleans  *)
let CLOSP1AUX_mti_evaluate_apps_const = prove
 (`!xs f (s:(C,FFI)clos_state) r s'.
     evaluate_apps f xs s = (r,s') ==> clos_state_max_app s' = clos_state_max_app s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[evaluate_apps_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[clos_case_eq_thms; pair_case_eq] THEN REPEAT STRIP_TAC THEN
  CLOSP1AUX_MTI_NORM_TAC THEN RES_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_app_const o
        check (fun th -> CLOSPROPSAUX_is_app "evaluate_app" (lhs (concl th))))) THEN
  ASM_MESON_TAC[]);;

let CLOSP1AUX_mti_v_rel_Block_left = prove
 (`!m n xs y. clos_mtiProof_v_rel m (clos_Block n xs) y <=>
              ?ys. y = clos_Block n ys /\ ALL2 (clos_mtiProof_v_rel m) xs ys`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [clos_mtiProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"] THEN MESON_TAC[]);;

let CLOSP1AUX_mti_Boolv_HD = prove
 (`!m a v' b. ALL2 (clos_mtiProof_v_rel m) a v' /\ ~(a = []) ==>
              (clos_Boolv b = HD v' <=> clos_Boolv b = HD a)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HD] THEN
  EQ_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_mtiProof_v_rel_simps; clos_Boolv_def;
                              CLOSP1AUX_mti_v_rel_Block_left; LIST_REL_NIL]) THEN
  ASM_REWRITE_TAC[clos_Boolv_def] THEN ASM_MESON_TAC[]);;

(* the P- and Q-shaped facts *)
let CLOSP1AUX_mti_is_PQ name th =
  let c = snd(strip_forall(concl th)) in
  is_imp c && is_conj (lhand c) &&
  (let a = lhand (lhand c) in
   is_eq a && CLOSPROPSAUX_is_app name (lhs a) && is_pair (rhs a) &&
   is_var (lhand (rhs a)));;
let CLOSP1AUX_mti_is_P = CLOSP1AUX_mti_is_PQ "clos_evaluate";;
let CLOSP1AUX_mti_is_Q = CLOSP1AUX_mti_is_PQ "evaluate_app";;

(* resolve the conditional induction hypotheses with the assumptions *)
let CLOSP1AUX_MTI_COND_IH_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let mentions_eval t =
    can (find_term (fun t -> try let n = fst(dest_const t) in
                                 n = "clos_evaluate" || n = "evaluate_app"
                             with Failure _ -> false)) t in
  let is_cond_ih th =
    not (CLOSP1AUX_mti_is_P th) && not (CLOSP1AUX_mti_is_Q th) &&
    (let c = snd(strip_forall(concl th)) in
     is_imp c && mentions_eval (rand c) && is_forall (rand c)) in
  let cihs = filter is_cond_ih asms in
  let rec resolve depth th =
    if CLOSP1AUX_mti_is_P th || CLOSP1AUX_mti_is_Q th then [th]
    else if depth = 0 then [] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    flat (map (resolve (depth-1)) rs) in
  let res = flat (map (fun th -> resolve 4 (CLOSPROPSAUX_curry_top th)) cihs) in
  let res = filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

(* name the first clos_evaluate of the antecedent of the goal that is not   *)
(* yet the left side of an assumption; the result variable is remembered   *)
let CLOSP1AUX_mti_counter = ref 0;;
let CLOSP1AUX_mti_last = ref `T`;;
let rec CLOSP1AUX_mti_free_evals tm =
  if is_abs tm then [] else
  (if is_comb tm && CLOSPROPSAUX_is_app "clos_evaluate" tm then [tm] else []) @
  (if is_comb tm then CLOSP1AUX_mti_free_evals (rator tm) @ CLOSP1AUX_mti_free_evals (rand tm)
   else []);;
let CLOSP1AUX_MTI_NAME_EVAL_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let named = mapfilter (fun (_,th) -> lhs (concl th)) asl in
  let evs = filter (fun t -> not (mem t named)) (CLOSP1AUX_mti_free_evals ant) in
  let tm = hd evs in
  let rty,sty = (match dest_type (type_of tm) with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  incr CLOSP1AUX_mti_counter;
  let k = string_of_int (!CLOSP1AUX_mti_counter) in
  let r = mk_var("rr" ^ k, rty) and s = mk_var("tt" ^ k, sty) in
  CLOSP1AUX_mti_last := r;
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)) gl;;

(* max_app of all states is that of the first source state *)
let CLOSP1AUX_mti_maxapp_rws =
  GEN_ALL (CONJUNCT1 (SPEC_ALL CLOSPROPSAUX_max_app_dec_clock)) ::
  filter (fun th -> CLOSPROPSAUX_is_app "clos_state_max_app" (lhs (concl (SPEC_ALL th))))
         (CONJUNCTS clos_state_INFO.ri_accfupds);;
let CLOSP1AUX_mti_maxapp_eqs (asl:(string*thm) list) : thm list =
  let fs = [MATCH_MP evaluate_const; MATCH_MP evaluate_app_const;
            MATCH_MP CLOSP1AUX_mti_evaluate_apps_const;
            (fun th -> CONJUNCT1 (MATCH_MP do_install_const th));
            (fun th -> CONJUNCT1 (CONJUNCT2 (MATCH_MP clos_do_app_const th)));
            (fun th -> SYM (CONJUNCT1 (MATCH_MP clos_mtiProof_state_rel_max_app th)))] in
  let eqs = flat (map (fun (_,th) -> mapfilter (fun f -> f th) fs) asl) in
  let eqs = filter (fun th -> let c = concl th in is_eq c && not (lhs c = rhs c)) eqs in
  eqs @ CLOSP1AUX_mti_maxapp_rws;;
let CLOSP1AUX_MTI_MAXAPP_TAC : tactic = fun (asl,w as gl) ->
  let rws = CLOSP1AUX_mti_maxapp_eqs asl in
  (RULE_ASSUM_TAC(REWRITE_RULE rws) THEN REWRITE_TAC rws) gl;;

(* the source expressions of the target expressions y *)
let CLOSP1AUX_mti_source (asms:term list) (y:term) : term =
  try lhand (find (fun c -> CLOSPROPSAUX_is_app "clos_mtiProof_code_rel" c &&
                            rand c = y) asms)
  with Failure _ ->
  try (match dest_list y with
         [e] -> if CLOSPROPSAUX_is_app "HD" e && CLOSPROPSAUX_is_app "intro_multi" (rand e)
                then rand (rand e) else failwith "src"
       | _ -> failwith "src")
  with Failure _ ->
  if CLOSPROPSAUX_is_app "intro_multi" y then rand y else
  rand (rhs (find (fun c -> is_eq c && lhs c = y &&
                            CLOSPROPSAUX_is_app "intro_multi" (rhs c)) asms));;

(* prove a code relation from the assumptions *)
let CLOSP1AUX_mti_prove_code_rel (asms:thm list) (tm:term) : thm =
  try find (fun th -> concl th = tm) asms with Failure _ ->
  let useful th = let c = concl th in
    CLOSPROPSAUX_is_app "no_mti" c || CLOSPROPSAUX_is_app "ALL" c ||
    (is_eq c && CLOSPROPSAUX_is_app "intro_multi" (rhs c)) in
  EQT_ELIM (REWRITE_CONV (clos_mtiProof_code_rel_def :: HD_intro_multi :: ALL ::
                          filter useful asms) tm);;

(* apply an induction hypothesis of P shape to a target evaluation *)
let CLOSP1AUX_mti_apply (asl:(string*thm) list) (ih:thm) (ev:thm) : thm =
  let asms = map snd asl in
  let cs = map concl asms in
  let th1 = MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) ev in
  let vs,bod = strip_forall (concl th1) in
  let y,et = dest_pair (rand (lhs (concl ev))) in
  let e2,t = dest_pair et in
  let s = lhand (find (fun c -> CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" c &&
                                rand c = t) cs) in
  let e1 = lhand (find (fun c -> CLOSPROPSAUX_is_app "ALL2" c && rand c = e2) cs) in
  let x = CLOSP1AUX_mti_source cs y in
  let inst v = let ty = type_of v in
    if ty = type_of s then s else if ty = type_of x then x
    else if ty = type_of e1 then e1 else failwith "inst" in
  let th2 = REWRITE_RULE (CLOSP1AUX_mti_maxapp_eqs asl) (SPECL (map inst vs) th1) in
  let rec go th =
    if is_imp (concl th) then
      let a = lhand (concl th) in
      go (MP th (try find (fun x -> concl x = a) asms
                 with Failure _ -> CLOSP1AUX_mti_prove_code_rel asms a))
    else th in
  go th2;;

(* the named target evaluation *)
let CLOSP1AUX_mti_named (asms:thm list) : thm =
  let r = !CLOSP1AUX_mti_last in
  find (fun th -> let c = concl th in is_eq c &&
          CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
          is_pair (rhs c) && fst (dest_pair (rhs c)) = r) asms;;

let CLOSP1AUX_MTI_IH_ON_NEW_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let ev = CLOSP1AUX_mti_named asms in
  let ihs = filter CLOSP1AUX_mti_is_P asms in
  let res = mapfilter (fun ih -> CLOSP1AUX_mti_apply asl ih ev) ihs in
  (if res = [] then NO_TAC else STRIP_ASSUME_TAC (hd res)) gl;;

(* after an induction hypothesis gave the source evaluation (X,E,S) = (r1,s2) *)
(* and result_rel R1 R2 r1 rr: rewrite the source with it and split rr      *)
let CLOSP1AUX_MTI_SPLIT_RES_TAC : tactic = fun (asl,w as gl) ->
  let rr = !CLOSP1AUX_mti_last in
  let rl = find (fun (_,th) -> CLOSPROPSAUX_is_app "result_rel" (concl th) &&
                               rand (concl th) = rr) asl in
  let r1 = rand (rator (concl (snd rl))) in
  let src = find (fun (_,th) -> is_eq (concl th) && is_pair (rhs (concl th)) &&
                                fst (dest_pair (rhs (concl th))) = r1) asl in
  (REWRITE_TAC[snd src] THEN
   CASES_ON rr THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "result_rel" (concl th) &&
                                           rand (rator (concl th)) = r1)) THEN
   REWRITE_TAC[clos_result_rel_Rval2; result_rel_Rerr2] THEN
   DISCH_THEN(STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = r1 then SUBST_ALL_TAC th
                           else NO_TAC) THEN
   CASE_REWRITE_TAC[]) gl;;

(* singleton results: clos_evaluate ([e],env,s) = (Rval a,s') gives a = [r] *)
let CLOSP1AUX_MTI_SING_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
       (let r = fst(dest_pair(rhs c)) in
        CLOSPROPSAUX_is_app "Rval" r && is_var (rand r))
    then (STRIP_ASSUME_TAC(MATCH_MP clos_evaluate_SING th) THEN ASSUME_TAC th)
    else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                              is_cons (rhs (concl th)) then SUBST_ALL_TAC th else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSPROPSAUX_is_app "ALL2" c &&
       ((is_cons (lhand c) && (is_var (rand c) || is_cons (rand c))) ||
        (is_var (lhand c) && is_cons (rand c)))
    then MP_TAC th THEN REWRITE_TAC[LIST_REL_CONS1; LIST_REL_CONS2; LIST_REL_NIL; ALL2] THEN
         STRIP_TAC THEN RVEQ_TAC
    else NO_TAC));;

(* the end of a case: the results are related *)
let CLOSP1AUX_MTI_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CLOSP1AUX_MTI_SING_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; injectivity "result"; distinctness "result";
                  HD; ALL2];;

(* split a related pair of errors exc_rel R e1 a (a a variable, the target) *)
let CLOSP1AUX_MTI_SPLIT_EXC_TAC : tactic = fun (asl,w as gl) ->
  let er = find (fun (_,th) -> CLOSPROPSAUX_is_app "exc_rel" (concl th) &&
                               is_var (rand (concl th))) asl in
  let a = rand (concl (snd er)) and e1 = rand (rator (concl (snd er))) in
  (CASES_ON a THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "exc_rel" (concl th) &&
                                           rand (rator (concl th)) = e1)) THEN
   REWRITE_TAC[exc_rel_raise2; exc_rel_type_error2] THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[]) gl;;

(* related states with decreased clocks *)
let CLOSP1AUX_mti_state_rel_dec_clock = prove
 (`!(s:(C,FFI)clos_state) t k.
     clos_mtiProof_state_rel s t ==>
     clos_mtiProof_state_rel (clos_dec_clock k s) (clos_dec_clock k t)`,
  REWRITE_TAC[clos_mtiProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[]);;

let CLOSP1AUX_MTI_DEC_CLOCK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let dcs = find_terms (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_dec_clock" t &&
                                 length (snd (strip_comb t)) = 2) ant in
  let srs = filter (fun th -> CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" (concl th))
                   (map snd asl) in
  let ths = flat (map (fun dc ->
     let [k;x] = snd (strip_comb dc) in
     mapfilter (fun sr -> if rand (concl sr) = x
                          then SPEC k (MATCH_MP CLOSP1AUX_mti_state_rel_dec_clock sr)
                          else failwith "DEC") srs) dcs) in
  let ths = filter (fun th -> not (exists (fun (_,a) -> concl a = concl th) asl)) ths in
  MAP_EVERY ASSUME_TAC ths gl;;

(* relate the environments of the named evaluation and of its source *)
let CLOSP1AUX_MTI_ENV_ALL2_TAC : tactic =
  REPEAT((MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC) ORELSE
         MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_TAKE ORELSE
         MATCH_MP_TAC EVERY2_DROP) THEN
  ASM_REWRITE_TAC[ALL2; LENGTH_MAP; LIST_REL_GENLIST] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_mtiProof_v_rel_simps; LENGTH_MAP] THEN ASM_MESON_TAC[];;

let CLOSP1AUX_MTI_ENV_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let cs = map concl asms in
  let ev = CLOSP1AUX_mti_named asms in
  let y,et = dest_pair (rand (lhs (concl ev))) in
  let e2 = fst (dest_pair et) in
  if exists (fun c -> CLOSPROPSAUX_is_app "ALL2" c && rand c = e2) cs then ALL_TAC gl else
  let x = CLOSP1AUX_mti_source cs y in
  let con = rand w in
  let sev = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_evaluate" t &&
                                fst (dest_pair (rand t)) = x) con in
  let e1 = fst (dest_pair (snd (dest_pair (rand sev)))) in
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_mtiProof_v_rel`) con) in
  let all2 = list_mk_comb(`ALL2:(clos_v->clos_v->bool)->clos_v list->clos_v list->bool`,
                          [mk_comb(`clos_mtiProof_v_rel`, m); e1; e2]) in
  (SUBGOAL_THEN all2 ASSUME_TAC THENL [CLOSP1AUX_MTI_ENV_ALL2_TAC; ALL_TAC]) gl;;

let CLOSP1AUX_MTI_STEP_TAC : tactic =
  CLOSP1AUX_MTI_COND_IH_TAC THEN CLOSP1AUX_MTI_DEC_CLOCK_TAC THEN
  CLOSP1AUX_MTI_NAME_EVAL_TAC THEN CLOSP1AUX_MTI_MAXAPP_TAC THEN
  CLOSP1AUX_MTI_ENV_TAC THEN CLOSP1AUX_MTI_IH_ON_NEW_TAC THEN CLOSP1AUX_MTI_SPLIT_RES_TAC;;

(* unfold the evaluation of both sides *)
let CLOSP1AUX_MTI_UNFOLD_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def];;

let CLOSP1AUX_mti_nil = prove
 (el 0 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_evaluate_def; clos_mtiProof_code_rel_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq (concl th) &&
                                      CLOSPROPSAUX_is_app "intro_multi" (rhs (concl th)))) THEN
  REWRITE_TAC[intro_multi_EQ_NIL] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`Rval []:(clos_v list,clos_v)result`; `s1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[clos_evaluate_def; result_rel_def; ALL2]);;

let CLOSP1AUX_mti_cons = prove
 (el 1 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if CLOSPROPSAUX_is_app "clos_mtiProof_code_rel" (concl th)
                          then STRIP_ASSUME_TAC (MATCH_MP CLOSP1AUX_mti_code_rel_cons th)
                          else NO_TAC) THEN
  RVEQ_TAC THEN CLOSP1AUX_MTI_UNFOLD_TAC THEN
  REPEAT CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_FIN_TAC);;

let CLOSP1AUX_mti_var = prove
 (el 2 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN
  FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "ALL2" (concl th)
                        then ASSUME_TAC (MATCH_MP LIST_REL_LENGTH th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CLOSP1AUX_MTI_FIN_TAC THEN ASM_MESON_TAC[LIST_REL_EL_EQN]);;

(* rewrite the boolean tests on the head of a target result to the source *)
let CLOSP1AUX_MTI_BOOLV_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let nes = mapfilter (MATCH_MP CLOSPROPSAUX_eval_SING_NIL) asms in
  let ths = flat (map (fun ne -> mapfilter (fun a ->
               MATCH_MP CLOSP1AUX_mti_Boolv_HD (CONJ a ne)) asms) nes) in
  REWRITE_TAC (map GSYM ths) gl;;

let CLOSP1AUX_mti_if = prove
 (el 3 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN
  CLOSP1AUX_MTI_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_MTI_FIN_TAC] THEN
  CLOSP1AUX_MTI_BOOLV_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  REPEAT CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_FIN_TAC);;

let CLOSP1AUX_mti_let = prove
 (el 4 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN
  CLOSP1AUX_MTI_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_MTI_FIN_TAC] THEN
  REPEAT CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_FIN_TAC);;

let CLOSP1AUX_mti_raise = prove
 (el 5 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN
  REPEAT CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_FIN_TAC);;

let CLOSP1AUX_mti_handle = prove
 (el 6 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN
  CLOSP1AUX_MTI_STEP_TAC THENL [CLOSP1AUX_MTI_FIN_TAC; ALL_TAC] THEN
  CLOSP1AUX_MTI_SPLIT_EXC_TAC THENL [ALL_TAC; CLOSP1AUX_MTI_FIN_TAC] THEN
  REPEAT CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_FIN_TAC);;

let CLOSP1AUX_mti_tick = prove
 (el 11 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel_clocks th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [CLOSP1AUX_MTI_FIN_TAC; ALL_TAC] THEN
  REPEAT CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_FIN_TAC);;

let CLOSP1AUX_mti_call = prove
 (el 12 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC);;

let CLOSP1AUX_mti_app_nil = prove
 (el 13 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_app_NIL; LIST_REL_NIL; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`Rval [f1]:(clos_v list,clos_v)result`; `s1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[evaluate_apps_def; result_rel_def; ALL2]);;

(* local tactics for the Op case: install, force a thunk, do_app; the      *)
(* target drives the case splits, except for do_install                    *)
let CLOSP1AUX_MTI_SPLIT_PAIR_TAC (tm:term) : tactic = fun (asl,w as gl) ->
  let th = snd (find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = tm) asl) in
  let r = rhs (concl th) in
  if CLOSPROPSAUX_is_app "Rval" r && is_var (rand r) && is_type (type_of (rand r)) &&
     fst (dest_type (type_of (rand r))) = "prod"
  then (CASES_ON (rand r) THEN CASE_REWRITE_TAC[]) gl
  else ALL_TAC gl;;

let CLOSP1AUX_MTI_DO_APP_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_da t = is_comb t && CLOSPROPSAUX_is_app "clos_do_app" t &&
                length (snd (strip_comb t)) = 3 in
  let db = find_term is_da ant in
  let [op; ys; t] = snd (strip_comb db) in
  let da = find_term (fun t -> is_da t && hd (snd (strip_comb t)) = op) con in
  let [_; xs; s] = snd (strip_comb da) in
  let th = REWRITE_RULE (CLOSP1AUX_mti_maxapp_eqs asl)
             (INST [s,`s:(C,FFI)clos_state`; t,`t:(C,FFI)clos_state`;
                    xs,`xs:clos_v list`; ys,`ys:clos_v list`; op,`opp:clos_op`]
                   clos_mtiProof_do_app_lemma) in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_SIMP_TAC[EVERY2_REVERSE]; ALL_TAC] THEN
   CASES_ON db THEN CASE_REWRITE_TAC[] THEN
   CLOSP1AUX_MTI_SPLIT_PAIR_TAC db THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

(* the do_install of the source (in the consequent) and of the target *)
let CLOSP1AUX_MTI_DO_INSTALL_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_di t = is_comb t && CLOSPROPSAUX_is_app "clos_do_install" t &&
                length (snd (strip_comb t)) = 2 in
  let db = find_term is_di ant and da = find_term is_di con in
  let [ys; t] = snd (strip_comb db) and [xs; s] = snd (strip_comb da) in
  let th = REWRITE_RULE (CLOSP1AUX_mti_maxapp_eqs asl)
             (INST [s,`s:(C,FFI)clos_state`; t,`t:(C,FFI)clos_state`;
                    xs,`xs:clos_v list`; ys,`ys:clos_v list`] clos_mtiProof_do_install_lemma) in
  let rty,sty = (match dest_type (type_of da) with (_,[a;b]) -> a,b | _ -> failwith "DI") in
  let r = genvar rty and s' = genvar sty in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_SIMP_TAC[EVERY2_REVERSE]; ALL_TAC] THEN
   MP_TAC(ISPEC da PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s' ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   CASES_ON r THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   (fun (asl,w as gl) ->
      let teq = snd (find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = db) asl) in
      REWRITE_TAC[teq] gl) THEN
   CASE_REWRITE_TAC[]) gl;;

(* the last value of the evaluation of installed code *)
let CLOSP1AUX_MTI_LAST_TAC : tactic =
  MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w as gl) ->
     let asms = map snd asl in
     let lens = mapfilter (MATCH_MP clos_evaluate_IMP_LENGTH) asms in
     (MAP_EVERY MP_TAC lens THEN ASM_MESON_TAC[LENGTH_EQ_NIL]) gl);;

(* the dest_thunk of the target (antecedent) and of the source (consequent) *)
let CLOSP1AUX_MTI_DEST_THUNK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_dt t = is_comb t && CLOSPROPSAUX_is_app "clos_dest_thunk" t &&
                length (snd (strip_comb t)) = 2 in
  let db = find_term is_dt ant and da = find_term is_dt con in
  let [ys; rt] = snd (strip_comb db) and [xs; rs] = snd (strip_comb da) in
  let s = rand rs and t = rand rt in
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_mtiProof_v_rel`) con) in
  let sr = vsubst [m,`M:num`]
    `\(r:(C,FFI)clos_state) (t:(C,FFI)clos_state).
        clos_state_max_app r = M /\ clos_mtiProof_state_rel r t` in
  let th = ISPECL [mk_comb(`clos_mtiProof_v_rel`, m); sr; s; t; xs; ys]
                  CLOSPROPSAUX_dest_thunk_rel in
  (MP_TAC th THEN
   ANTS_TAC THENL
    [REWRITE_TAC[GEN_ALL clos_mtiProof_simple_val_rel;
                 GEN_ALL clos_mtiProof_simple_state_rel] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC(CLOSP1AUX_mti_maxapp_eqs asl) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   CASES_ON db THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

let CLOSP1AUX_MTI_MODE_CASES_TAC : tactic = fun (asl,w as gl) ->
  let v = find_term (fun t -> is_var t && type_of t = `:thunk_mode`) w in
  (CASES_ON v THEN CASE_REWRITE_TAC[]) gl;;

(* the arguments of a forced thunk are a single reference *)
let CLOSP1AUX_MTI_THUNK_ARGS_TAC : tactic = fun (asl,w as gl) ->
  let dt = snd (find (fun (_,th) -> is_eq (concl th) &&
                       CLOSPROPSAUX_is_app "clos_dest_thunk" (lhs (concl th)) &&
                       CLOSPROPSAUX_is_app "clos_IsThunk" (rhs (concl th)) &&
                       is_var (lhand (lhs (concl th)))) asl) in
  let xs = lhand (lhs (concl dt)) in
  let all2 = snd (find (fun (_,th) -> CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                         (lhand (concl th) = xs || rand (concl th) = xs)) asl) in
  let xs1 = lhand (concl all2) and ys1 = rand (concl all2) in
  let vr = rand (rator (rator (concl all2))) in
  (MP_TAC(ISPECL [vr; xs1; ys1] CLOSPROPSAUX_vr_RefPtr_shape) THEN
   ASM_REWRITE_TAC[GEN_ALL clos_mtiProof_simple_val_rel] THEN STRIP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
             (lhs (concl th) = xs1 || lhs (concl th) = ys1) then SUBST_ALL_TAC th else NO_TAC));
    MP_TAC(SPECL [xs; rand (lhs (concl dt))] CLOSSEMAUX_dest_thunk_NotThunk) THEN
    ASM_REWRITE_TAC[distinctness "clos_dest_thunk_ret"]]) gl;;

(* the update_thunk of the target (antecedent) and of the source *)
let CLOSP1AUX_mti_rel_update_thunk_match = prove
 (CASE_TERM
  `clos_mtiProof_state_rel (s1:(C,FFI)clos_state) s2 /\
   ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) vs ys ==>
   match clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys with
     NONE -> clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = NONE
   | SOME refs2 ->
       ?refs1. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 /\
               clos_mtiProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                       (clos_state_refs_fupd (K refs2) s2)`,
  DISCH_THEN(fun th -> MP_TAC(GEN `refs2:(num,(clos_v)clos_ref)fmap`
                                (MATCH_MP (INST_TYPE [] clos_mtiProof_rel_update_thunk) th))) THEN
  CASES_ON `clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs (s2:(C,FFI)clos_state)) ys` THEN
  CASE_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let CLOSP1AUX_MTI_UPDATE_THUNK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_ut t = is_comb t && CLOSPROPSAUX_is_app "clos_update_thunk" t &&
                length (snd (strip_comb t)) = 3 in
  let ub = find_term is_ut ant and ua = find_term is_ut con in
  let [xs; rt; ws] = snd (strip_comb ub) and [_; rs; vs] = snd (strip_comb ua) in
  let s1 = rand rs and s2 = rand rt in
  let [rp] = dest_list xs in
  let [b; ptr] = snd (strip_comb rp) in
  let th0 = REWRITE_RULE (CLOSP1AUX_mti_maxapp_eqs asl)
     (INST [s1,`s1:(C,FFI)clos_state`; s2,`s2:(C,FFI)clos_state`; vs,`vs:clos_v list`;
            ws,`ys:clos_v list`; b,`v:bool`; ptr,`ptr:num`]
           CLOSP1AUX_mti_rel_update_thunk_match) in
  (MP_TAC th0 THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CASES_ON ub THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

(* a local helper: the application of a thunk is its own intro_multi *)
let CLOSP1AUX_mti_code_rel_AppUnit = prove
 (`!m. 1 <= m ==>
       clos_mtiProof_code_rel m [clos_AppUnit (clos_Var backend_common_None 0)]
                                [clos_AppUnit (clos_Var backend_common_None 0)]`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[clos_mtiProof_code_rel_def; clos_AppUnit_def; ALL; no_mti_def; LENGTH] THEN
  REWRITE_TAC[ONE] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[intro_multi_def; collect_apps_def; LENGTH; APPEND;
                                     ADD_CLAUSES; GSYM ONE; HD] THEN
                     CASE_REWRITE_TAC[])));;

let CLOSP1AUX_mti_state_rel_one = prove
 (`!(s:(C,FFI)clos_state) t. clos_mtiProof_state_rel s t ==> 1 <= clos_state_max_app s`,
  SIMP_TAC[clos_mtiProof_state_rel_def]);;

let CLOSP1AUX_MTI_APPUNIT_CODE_TAC : tactic = fun (asl,w as gl) ->
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_mtiProof_v_rel`) (rand w)) in
  let sr = snd (find (fun (_,th) -> CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" (concl th) &&
                                    lhand (concl th) = rand m) asl) in
  ASSUME_TAC (MATCH_MP CLOSP1AUX_mti_code_rel_AppUnit
                (MATCH_MP CLOSP1AUX_mti_state_rel_one sr)) gl;;

let CLOSP1AUX_mti_op = prove
 (el 7 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN
  CLOSP1AUX_MTI_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_MTI_FIN_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [CLOSP1AUX_MTI_DO_INSTALL_TAC THENL
     [CLOSP1AUX_MTI_STEP_TAC THENL
       [CLOSP1AUX_MTI_FIN_TAC THEN CLOSP1AUX_MTI_LAST_TAC; CLOSP1AUX_MTI_FIN_TAC];
      CLOSP1AUX_MTI_FIN_TAC];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [CLOSP1AUX_MTI_DEST_THUNK_TAC THEN TRY(CLOSP1AUX_MTI_FIN_TAC THEN NO_TAC) THEN
    CLOSP1AUX_MTI_MODE_CASES_TAC THENL [CLOSP1AUX_MTI_FIN_TAC; ALL_TAC] THEN
    CLOSP1AUX_MTI_THUNK_ARGS_TAC THEN CLOSP1AUX_MTI_APPUNIT_CODE_TAC THEN
    CLOSP1AUX_MTI_STEP_TAC THENL
     [CLOSP1AUX_MTI_UPDATE_THUNK_TAC THEN CLOSP1AUX_MTI_FIN_TAC; CLOSP1AUX_MTI_FIN_TAC];
    CLOSP1AUX_MTI_DO_APP_TAC THEN CLOSP1AUX_MTI_FIN_TAC]);;

(* arithmetic with the numeric assumptions only *)
let CLOSP1AUX_MTI_ARITH_TAC : tactic = fun (asl,w as gl) ->
  let is_num_rel t =
    let t = if is_neg t then dest_neg t else t in
    (is_comb t && is_comb (rator t) &&
     (let h = rator (rator t) in
      is_const h && mem (fst (dest_const h)) ["<"; "<="; ">"; ">="] &&
      type_of (rand t) = `:num`)) ||
    (is_eq t && type_of (lhs t) = `:num`) in
  let rec is_num_prop t =
    is_num_rel t ||
    ((is_disj t || is_conj t) && is_num_prop (lhand t) && is_num_prop (rand t)) ||
    (is_neg t && is_num_prop (dest_neg t)) in
  let ths = filter (fun th -> is_num_prop (concl th)) (map snd asl) in
  (MAP_EVERY MP_TAC ths THEN ARITH_TAC) gl;;

(* the arity facts of a collected function (collect_args_IMP and         *)
(* collect_args_ok_IMP at the equations collect_args m k e = (n,e'))      *)
let CLOSP1AUX_MTI_COLLECT_ARGS_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let eqs = filter (fun th -> let c = concl th in is_eq c &&
                      CLOSPROPSAUX_is_app "collect_args" (lhs c)) asms in
  let srs = filter (fun th -> CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" (concl th)) asms in
  let ones = map (MATCH_MP CLOSP1AUX_mti_state_rel_one) srs in
  let ths1 = flat (map (fun eq -> mapfilter (fun one ->
      let th = MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_args_IMP) eq in
      MP th (EQT_ELIM (REWRITE_CONV (one :: CLOSP1AUX_mti_maxapp_eqs asl) (lhand (concl th)))))
      ones) eqs) in
  let ths2 = mapfilter (fun eq ->
      let th = MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_args_ok_IMP) eq in
      MP th (tryfind (fun a -> if concl a = lhand (concl th) then a else failwith "") asms)) eqs in
  (MAP_EVERY ASSUME_TAC (ones @ ths1) THEN MAP_EVERY STRIP_ASSUME_TAC ths2) gl;;

let CLOSP1AUX_mti_fn = prove
 (el 8 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_UNFOLD_TAC THEN CLOSP1AUX_MTI_MAXAPP_TAC THEN
  CLOSP1AUX_MTI_COLLECT_ARGS_TAC THEN
  SUBGOAL_THEN `~(num_args' = 0)` ASSUME_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0)`] THEN CASE_REWRITE_TAC[] THEN
  CLOSP1AUX_MTI_FIN_TAC THEN
  REWRITE_TAC[clos_mtiProof_v_rel_simps; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  MAP_EVERY EXISTS_TAC [`[]:clos_v list`; `env1:clos_v list`; `e':clos_exp`;
                        `ts:mlstring list`] THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; ALL2; ALL; ADD_CLAUSES; clos_mtiProof_code_rel_def;
                  HD_intro_multi] THEN
  CLOSP1AUX_MTI_ARITH_TAC);;

(* a local helper: the functions of a Letrec after intro_multi *)
let CLOSP1AUX_mti_letrec_funs = prove
 (CASE_TERM `!m f (funs:(num#clos_exp)list).
     (!n e. f (n,e) = (FST (collect_args m n e),
                       HD (intro_multi m [SND (collect_args m n e)]))) /\
     1 <= m /\ ALL (\x. FST x = 1 /\ no_mti (SND x)) funs ==>
     ALL (\p. match p with (num_args,e) -> num_args <= m /\ ~(num_args = 0)) (MAP f funs) /\
     ALL2 (clos_mtiProof_f_rel m) funs (MAP f funs) /\
     ALL (\p. match p with (num_args,e) -> num_args <= m /\ ~(num_args = 0)) funs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL; ALL2] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `e0:clos_exp` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `collect_args m 1 e0` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `e1:clos_exp` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_args_IMP)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_args_ok_IMP)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[clos_mtiProof_f_rel_def; clos_mtiProof_code_rel_def; ALL; HD_intro_multi;
              ARITH_RULE `~(1 = 0)`] THEN
  CONJ_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e1:clos_exp`; `ts:mlstring list`] THEN
  ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC);;

let CLOSP1AUX_MTI_LETREC_FUNS_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let mp = find_term (fun t -> CLOSPROPSAUX_is_app "MAP" t && is_comb t &&
                               (let f = lhand t in is_abs f)) ant in
  let f = lhand mp and funs = rand mp in
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_mtiProof_v_rel`) (rand w)) in
  let sr = snd (find (fun (_,th) -> CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" (concl th) &&
                                    lhand (concl th) = rand m) asl) in
  let one = MATCH_MP CLOSP1AUX_mti_state_rel_one sr in
  (MP_TAC(ISPECL [m; f; funs] CLOSP1AUX_mti_letrec_funs) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[one] THEN REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CASE_REWRITE_TAC[] THEN
     MP_TAC(ISPEC (list_mk_comb(`collect_args`, [m; `n:num`; `e:clos_exp`])) PAIR_SURJECTIVE) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN CASE_REWRITE_TAC[];
     STRIP_TAC THEN ASM_REWRITE_TAC[]]) gl;;

let CLOSP1AUX_mti_letrec = prove
 (el 9 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP1AUX_MTI_SING_INV_TAC THEN CLOSP1AUX_MTI_UNFOLD_TAC THEN CLOSP1AUX_MTI_MAXAPP_TAC THEN
  CLOSP1AUX_MTI_LETREC_FUNS_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN
  CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_FIN_TAC);;

(* a local helper: the source of a multi-argument application *)
let CLOSP1AUX_mti_app_source = prove
 (`!m a3 a2 es' e'.
     1 <= m /\ LENGTH a3 = 1 /\ ALL no_mti a3 /\ no_mti a2 /\
     collect_apps m a3 a2 = (es',e') ==>
     ?x other (ts:tra list).
       a3 = [x] /\ es' = CONS x other /\ ALL no_mti es' /\ no_mti e' /\
       a2 = mk_Apps e' (ZIP ts other) /\ LENGTH other = LENGTH ts /\
       LENGTH other <= m - 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP collect_apps_acc) THEN
  REWRITE_TAC[APPEND] THEN DISCH_THEN(X_CHOOSE_THEN `other:clos_exp list` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`m:num`; `[h:clos_exp]`; `a2:clos_exp`; `CONS (h:clos_exp) other`;
                `e':clos_exp`] collect_apps_no_mti) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`a2:clos_exp`; `m:num`; `h:clos_exp`; `other:clos_exp list`;
                `e':clos_exp`] collect_apps_cons) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`a2:clos_exp`; `m - 1`; `[]:clos_exp list`; `other:clos_exp list`;
                `e':clos_exp`] collect_apps_IMP_mk_Apps) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ts:tra list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`h:clos_exp`; `other:clos_exp list`; `ts:tra list`] THEN
  ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC);;

(* the source of the application: arguments CONS x other, function mk_Apps *)
let CLOSP1AUX_MTI_APP_SOURCE_TAC : tactic = fun (asl,w as gl) ->
  let eq = concl (snd (find (fun (_,th) -> is_eq (concl th) &&
                               CLOSPROPSAUX_is_app "collect_apps" (lhs (concl th))) asl)) in
  let [m; a3; a2] = snd (strip_comb (lhs eq)) in
  let es,e = dest_pair (rhs eq) in
  (FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" (concl th) &&
                            lhand (concl th) = rand m
                         then ASSUME_TAC (MATCH_MP CLOSP1AUX_mti_state_rel_one th) else NO_TAC) THEN
   MP_TAC(SPECL [m; a3; a2; es; e] CLOSP1AUX_mti_app_source) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC) gl;;

let CLOSP1AUX_mti_App_mk_Apps = prove
 (`!e t ts x other.
     clos_App t NONE (mk_Apps e (ZIP ts other)) [x] = mk_Apps e (ZIP (CONS t ts) (CONS x other))`,
  REWRITE_TAC[ZIP; mk_Apps_def]);;

(* the target arguments are not empty *)
let CLOSP1AUX_MTI_APP_LEN_TAC : tactic = fun (asl,w as gl) ->
  let t = find_term (fun t -> CLOSPROPSAUX_is_app "LENGTH" t && is_comb t &&
                              CLOSPROPSAUX_is_app "intro_multi" (rand t)) w in
  let g = mk_binop `(>):num->num->bool` t `0` in
  (SUBGOAL_THEN g ASSUME_TAC THENL
   [REWRITE_TAC[intro_multi_length; LENGTH] THEN ARITH_TAC; ALL_TAC]) gl;;

(* the source mk_Apps evaluation from the evaluations of its parts *)
let CLOSP1AUX_MTI_MKAPPS_TAC : tactic = fun (asl,w as gl) ->
  let mk = find_term (fun t -> CLOSPROPSAUX_is_app "mk_Apps" t && is_comb t &&
                               CLOSPROPSAUX_is_app "ZIP" (rand t)) (rand w) in
  let z = rand mk in
  let ts = lhand z and other = rand z in
  let lg = mk_eq(mk_comb(`LENGTH:clos_exp list->num`, other),
                 mk_comb(`LENGTH:tra list->num`, ts)) in
  (SUBGOAL_THEN lg ASSUME_TAC THENL [ASM_REWRITE_TAC[LENGTH]; ALL_TAC] THEN
   (fun (asl,w as gl) ->
      let asms = map snd asl in
      let try_lem lem =
        let rec go th =
          if is_imp (snd (strip_forall (concl th)))
          then tryfind go (mapfilter (fun a -> MATCH_MP th a) asms) else th in
        go (REWRITE_RULE[IMP_CONJ] (GEN_ALL lem)) in
      let ths = mapfilter try_lem [evaluate_mk_Apps_ok; mk_Apps_err_2; mk_Apps_err_1] in
      REWRITE_TAC ths gl)) gl;;

(* the evaluate_app of the target, by the Q-shaped hypothesis *)
let CLOSP1AUX_MTI_APP_Q_TAC : tactic =
  CLOSP1AUX_MTI_SING_TAC THEN CLOSP1AUX_MTI_COND_IH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN
  CLOSP1AUX_MTI_MAXAPP_TAC THEN DISCH_TAC THEN
  (fun (asl,w as gl) ->
     let asms = map snd asl in
     let ev = find (fun th -> is_eq (concl th) &&
                     CLOSPROPSAUX_is_app "evaluate_app" (lhs (concl th))) asms in
     let r,t = dest_pair (rhs (concl ev)) in
     let ea = find_term (fun t -> CLOSPROPSAUX_is_app "evaluate_apps" t &&
                                  length (snd (strip_comb t)) = 3) w in
     let [f1; args1; s] = snd (strip_comb ea) in
     let use q =
       let th = REWRITE_RULE (CLOSP1AUX_mti_maxapp_eqs asl) (SPECL [r; t; f1; args1; s] q) in
       if lhand (lhand (concl th)) = concl ev then th else failwith "use" in
     let th = tryfind use (filter CLOSP1AUX_mti_is_Q asms) in
     (MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
      (fun (asl,w as gl) ->
         let lens = mapfilter (MATCH_MP clos_evaluate_IMP_LENGTH) (map snd asl) in
         (MAP_EVERY MP_TAC lens THEN REWRITE_TAC[LENGTH] THEN
          CLOSP1AUX_MTI_ARITH_TAC) gl)) gl);;

let CLOSP1AUX_mti_app = prove
 (el 10 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_MTI_SING_INV_TAC THEN
  CLOSP1AUX_MTI_APP_SOURCE_TAC THEN
  REWRITE_TAC[CLOSP1AUX_mti_App_mk_Apps] THEN CLOSP1AUX_MTI_UNFOLD_TAC THEN
  CLOSP1AUX_MTI_APP_LEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CLOSP1AUX_MTI_STEP_TAC THENL
   [CLOSP1AUX_MTI_STEP_TAC THEN CLOSP1AUX_MTI_SING_TAC THEN CLOSP1AUX_MTI_MKAPPS_TAC THENL
     [CLOSP1AUX_MTI_APP_Q_TAC; CLOSP1AUX_MTI_FIN_TAC];
    CLOSP1AUX_MTI_MKAPPS_TAC THEN CLOSP1AUX_MTI_FIN_TAC]);;

(* local helpers for the application of related closures: the lengths of *)
(* related lists; the function of a related Recclosure                    *)
let CLOSP1AUX_MTI_LENS_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) -> MATCH_MP LIST_REL_LENGTH th) asl in
  let ths = filter (fun th -> not (exists (fun (_,a) -> concl a = concl th) asl)) ths in
  MAP_EVERY ASSUME_TAC ths gl;;

let CLOSP1AUX_mti_EL_f_rel = prove
 (`!m funs1 funs2 n. ALL2 (clos_mtiProof_f_rel m) funs1 funs2 /\ n < LENGTH funs2 ==>
     ?b1 ts e2. EL n funs1 = (1,mk_Fns ts b1) /\ EL n funs2 = (LENGTH ts + 1,e2) /\
                clos_mtiProof_code_rel m [b1] [e2] /\ LENGTH ts + 1 <= m /\ no_mti b1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  MP_TAC(ISPEC `EL n (funs1:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  MP_TAC(ISPEC `EL n (funs2:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "clos_mtiProof_f_rel" o concl)) THEN
  ASM_REWRITE_TAC[clos_mtiProof_f_rel_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`b1:clos_exp`; `ts:mlstring list`; `y:clos_exp`] THEN
  ASM_REWRITE_TAC[]);;

(* the function n of related Recclosures *)
let CLOSP1AUX_MTI_EL_F_REL_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let frs = filter (fun th -> let c = concl th in CLOSPROPSAUX_is_app "ALL2" c &&
                     CLOSPROPSAUX_is_app "clos_mtiProof_f_rel" (rand (rator (rator c)))) asms in
  let use fr =
    let funs2 = rand (concl fr) in
    let lt = find (fun th -> let c = concl th in
                    CLOSPROPSAUX_is_app "<" c &&
                    rand c = mk_comb(`LENGTH:(num#clos_exp)list->num`, funs2)) asms in
    MATCH_MP CLOSP1AUX_mti_EL_f_rel (CONJ fr lt) in
  MAP_EVERY STRIP_ASSUME_TAC (mapfilter use frs) gl;;

(* the target dest_closure of a related closure is not NONE (for arguments *)
(* within max_app); the source dest_closure of a non-closure is NONE      *)
let CLOSP1AUX_mti_dest_closure_NONE = prove
 (`!m f1 f args1 args.
     clos_mtiProof_v_rel m f1 f /\ ALL2 (clos_mtiProof_v_rel m) args1 args /\
     ~(args = []) /\ LENGTH args <= m /\ dest_closure m NONE f args = NONE ==>
     dest_closure m NONE f1 [LAST args1] = NONE`,
  REPEAT GEN_TAC THEN CASES_ON `f:clos_v` THEN REWRITE_TAC[clos_mtiProof_v_rel_simps] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  TRY(REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN NO_TAC) THEN
  CLOSP1AUX_MTI_LENS_TAC THEN
  CLOSP1AUX_MTI_EL_F_REL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CASE_REWRITE_RULE[] o CONV_RULE(DEPTH_CONV BETA_CONV) o
                REWRITE_RULE[dest_closure_def; check_loc_def; LET_DEF; LET_END_DEF] o
                check (fun th -> is_eq (concl th) &&
                                 CLOSPROPSAUX_is_app "dest_closure" (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN CLOSP1AUX_MTI_ARITH_TAC);;

(* a local helper: a Recclosure of a function of one argument applied to one *)
(* value *)
let CLOSP1AUX_mti_app_Rec1_lemma = prove
 (`!env funs i body y (s:(C,FFI)clos_state).
     EL i funs = (1,body) /\ i < LENGTH funs /\ 1 <= clos_state_max_app s ==>
     evaluate_app NONE (clos_Recclosure NONE [] env funs i) [y] s =
     if clos_state_clock s = 0
     then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
     else clos_evaluate ([body],
                         CONS y (APPEND (list_of_seq (clos_Recclosure NONE [] env funs)
                                                     (LENGTH funs)) env),
                         clos_dec_clock 1 s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[check_loc_def; LENGTH; REVERSE; TAKE_DEF; DROP_DEF;
                                     APPEND; ARITH_RULE `n < 1 <=> n = 0`; NOT_LE;
                                     LET_DEF; LET_END_DEF] THEN
                     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
                     CONV_TAC NUM_REDUCE_CONV THEN CASE_REWRITE_TAC[])) THEN
  ASM_SIMP_TAC[ARITH_RULE `i < n ==> ~(n <= i)`; ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; SUB_0; ARITH_RULE `n < 1 <=> n = 0`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CLOSP1AUX_MTI_NAME_SPLIT_TAC
    `clos_evaluate ([body],
       CONS (y:clos_v) (APPEND (list_of_seq (clos_Recclosure NONE [] env funs) (LENGTH funs)) env),
       clos_dec_clock 1 (s:(C,FFI)clos_state))` THEN
  FIRST_ASSUM(fun th -> try STRIP_ASSUME_TAC (MATCH_MP clos_evaluate_SING th)
                        with Failure _ -> NO_TAC) THEN
  RVEQ_TAC THEN CASE_REWRITE_TAC[evaluate_app_NIL]);;

let CLOSP1AUX_mti_app_Rec1 = prove
 (`!env funs i y (s:(C,FFI)clos_state).
     FST (EL i funs) = 1 /\ i < LENGTH funs /\ 1 <= clos_state_max_app s ==>
     evaluate_app NONE (clos_Recclosure NONE [] env funs i) [y] s =
     if clos_state_clock s = 0
     then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
     else clos_evaluate ([SND (EL i funs)],
                         CONS y (APPEND (list_of_seq (clos_Recclosure NONE [] env funs)
                                                     (LENGTH funs)) env),
                         clos_dec_clock 1 s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSP1AUX_mti_app_Rec1_lemma THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ]);;

(* Partial application step of the backward simulation (app_cons case) *)
let CLOSP1AUX_mti_partial = prove
 (`!(s1:(C,FFI)clos_state) s f1 f args1 args v.
    clos_mtiProof_state_rel s1 s /\
    clos_mtiProof_v_rel (clos_state_max_app s1) f1 f /\
    ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) args1 args /\ ~(args = []) /\
    LENGTH args1 <= clos_state_max_app s1 /\
    dest_closure (clos_state_max_app s1) NONE f args = SOME (Partial_app v) ==>
    (clos_state_clock s < LENGTH args ==>
       evaluate_apps f1 args1 s1 =
       (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s1)) /\
    (~(clos_state_clock s < LENGTH args) ==>
       ?v1. evaluate_apps f1 args1 s1 = (Rval [v1],clos_dec_clock (LENGTH args) s1) /\
            clos_mtiProof_v_rel (clos_state_max_app s1) v1 v)`,
  REPEAT GEN_TAC THEN CASES_ON `f:clos_v` THEN REWRITE_TAC[clos_mtiProof_v_rel_simps] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   TRY(UNDISCH_TAC `dest_closure (clos_state_max_app (s1:(C,FFI)clos_state)) NONE f args =
                    SOME (Partial_app v)` THEN
       REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[distinctness "option"] THEN NO_TAC) THEN
   CLOSP1AUX_MTI_LENS_TAC THEN CLOSP1AUX_MTI_EL_F_REL_TAC THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (MATCH_MP state_rel_clocks th)]) THEN
   FIRST_X_ASSUM(MP_TAC o CASE_REWRITE_RULE[] o CONV_RULE(DEPTH_CONV BETA_CONV) o
                REWRITE_RULE[dest_closure_def; check_loc_def; LET_DEF; LET_END_DEF] o
                check (fun th -> is_eq (concl th) &&
                                 CLOSPROPSAUX_is_app "dest_closure" (lhs (concl th)))) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THENL
  [(* Closure *)
   SUBGOAL_THEN `LENGTH (args:clos_v list) <= clos_state_max_app (s1:(C,FFI)clos_state) /\
                LENGTH (a1:clos_v list) < 1 + LENGTH (ts:mlstring list) + LENGTH a1`
     (fun th -> REWRITE_TAC[th]) THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; injectivity "app_kind";
                                   distinctness "app_kind"] THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP1AUX_mti_state_rel_one) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
   CONJ_TAC THEN DISCH_TAC THENL
    [MATCH_MP_TAC evaluate_apps_Clos_timeout THEN ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(SPECL [`args1:clos_v list`; `ts:mlstring list`; `s1:(C,FFI)clos_state`; `e1:clos_exp`;
                `APPEND args1' env1:clos_v list`] evaluate_apps_Clos_short) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   ASM_REWRITE_TAC[injectivity "result"; PAIR_EQ; CONS_11; UNWIND_THM1] THEN
   REWRITE_TAC[clos_mtiProof_v_rel_simps; injectivity "clos_v"] THEN
   MAP_EVERY EXISTS_TAC [`APPEND (args1:clos_v list) args1'`; `env1:clos_v list`; `e1:clos_exp`;
                         `DROP (LENGTH (args1:clos_v list)) (ts:mlstring list)`] THEN
   ASM_REWRITE_TAC[APPEND_ASSOC; LENGTH_APPEND; LENGTH_DROP] THEN
   CONJ_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[]];
   (* Recclosure, no arguments yet *)
   SUBGOAL_THEN `~(LENGTH (a3:(num#clos_exp)list) <= a4) /\
                LENGTH (args:clos_v list) <= clos_state_max_app (s1:(C,FFI)clos_state) /\
                LENGTH ([]:clos_v list) < LENGTH (ts:mlstring list) + 1`
     (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[LENGTH] THEN CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; injectivity "app_kind";
                                   distinctness "app_kind"] THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP1AUX_mti_state_rel_one) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; LENGTH; ADD_CLAUSES]) THEN
   MP_TAC(ISPEC `args1:clos_v list` SNOC_CASES) THEN STRIP_TAC THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
   ASM_MESON_TAC[LENGTH_EQ_NIL];
     FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_SNOC]) THEN
     SUBGOAL_THEN `a4 < LENGTH (funs1:(num#clos_exp)list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[evaluate_apps_SNOC; CLOSP1AUX_mti_app_Rec1] THEN
   CASES_ON `ts:mlstring list` THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN CLOSP1AUX_MTI_ARITH_TAC;
      REWRITE_TAC[mk_Fns_def] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THENL
    [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     (CLOSP1AUX_MTI_ARITH_TAC ORELSE
      (MATCH_MP_TAC(TAUT `F ==> p`) THEN CLOSP1AUX_MTI_ARITH_TAC));
     ALL_TAC] THEN
   ASM_SIMP_TAC[CLOSP1AUX_mti_eval_Fn1; CLOSPROPSAUX_max_app_dec_clock] THEN CASE_REWRITE_TAC[] THEN
   CONJ_TAC THEN DISCH_TAC THENL
    [ONCE_REWRITE_TAC[GSYM (SPEC `1` CLOSPROPSAUX_dec_clock_clock0)] THEN
     MATCH_MP_TAC evaluate_apps_Clos_timeout THEN
     REWRITE_TAC[CLOSPROPSAUX_max_app_dec_clock] THEN ASM_REWRITE_TAC[] THEN
     CLOSP1AUX_MTI_ARITH_TAC;
     ALL_TAC] THEN
      MP_TAC(SPECL [`l':clos_v list`; `a1:mlstring list`; `clos_dec_clock 1 (s1:(C,FFI)clos_state)`;
                    `b1:clos_exp`;
                    `CONS (x:clos_v) (APPEND (list_of_seq (clos_Recclosure NONE [] env1 funs1)
                       (LENGTH (a3:(num#clos_exp)list))) env1)`] evaluate_apps_Clos_short) THEN
       REWRITE_TAC[CLOSPROPSAUX_max_app_dec_clock] THEN
       ANTS_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
       REWRITE_TAC[CLOSPROPSAUX_dec_clock_dec_clock; injectivity "result"; PAIR_EQ; CONS_11] THEN
       SUBGOAL_THEN `1 + LENGTH (l':clos_v list) = LENGTH (args:clos_v list)` SUBST1_TAC THENL
        [CLOSP1AUX_MTI_ARITH_TAC; REWRITE_TAC[UNWIND_THM1]] THEN
       SUBGOAL_THEN
         `APPEND (l':clos_v list)
            (CONS x (APPEND (list_of_seq (clos_Recclosure NONE [] env1 funs1)
                               (LENGTH (a3:(num#clos_exp)list))) env1)) =
          APPEND (APPEND (SNOC x l')
            (list_of_seq (clos_Recclosure NONE [] env1 funs1) (LENGTH a3))) env1`
         SUBST1_TAC THENL
        [REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND]; REWRITE_TAC[APPEND_NIL]] THEN
       MATCH_MP_TAC (el 7 (CONJUNCTS clos_mtiProof_v_rel_rules)) THEN
       MAP_EVERY EXISTS_TAC [`funs1:(num#clos_exp)list`; `e2:clos_exp`;
                            `SUC (LENGTH (a1:mlstring list)) + 1`] THEN
       ASM_REWRITE_TAC[LENGTH_DROP; LENGTH_SNOC; LIST_REL_GENLIST] THEN CONJ_TAC THENL
        [CLOSP1AUX_MTI_ARITH_TAC;
         REPEAT STRIP_TAC THEN MATCH_MP_TAC (el 6 (CONJUNCTS clos_mtiProof_v_rel_rules)) THEN
         ASM_REWRITE_TAC[]]]];
   (* Recclosure, some arguments *)
   SUBGOAL_THEN `~(LENGTH (a3:(num#clos_exp)list) <= a4) /\
                 LENGTH (args:clos_v list) <= clos_state_max_app (s1:(C,FFI)clos_state) /\
                 LENGTH (a1:clos_v list) < 1 + LENGTH (ts:mlstring list) + LENGTH a1`
     (fun th -> REWRITE_TAC[th]) THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; injectivity "app_kind";
                                   distinctness "app_kind"] THEN
   DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP1AUX_mti_state_rel_one) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
   CONJ_TAC THEN DISCH_TAC THENL
    [MATCH_MP_TAC evaluate_apps_Clos_timeout THEN ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(SPECL [`args1:clos_v list`; `ts:mlstring list`; `s1:(C,FFI)clos_state`; `e1:clos_exp`;
                 `APPEND (APPEND args1' recc) env1:clos_v list`] evaluate_apps_Clos_short) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   ASM_REWRITE_TAC[injectivity "result"; PAIR_EQ; CONS_11; UNWIND_THM1] THEN
   REWRITE_TAC[APPEND_ASSOC] THEN
   MATCH_MP_TAC (el 7 (CONJUNCTS clos_mtiProof_v_rel_rules)) THEN
   MAP_EVERY EXISTS_TAC [`funs1:(num#clos_exp)list`; `e2:clos_exp`;
                        `1 + LENGTH (ts:mlstring list) + LENGTH (args1':clos_v list)`] THEN
   ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_DROP; APPEND_EQ_NIL] THEN
   CONJ_TAC THENL [MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CLOSP1AUX_MTI_ARITH_TAC]);;

(* a Recclosure of a function of one argument applies like a Closure *)
let CLOSP1AUX_mti_apps_Rec_Clos = prove
 (`!env funs i args (s:(C,FFI)clos_state).
     FST (EL i funs) = 1 /\ i < LENGTH funs /\ 1 <= clos_state_max_app s /\ ~(args = []) ==>
     evaluate_apps (clos_Recclosure NONE [] env funs i) args s =
     evaluate_apps (clos_Closure NONE []
                      (APPEND (list_of_seq (clos_Recclosure NONE [] env funs) (LENGTH funs)) env)
                      1 (SND (EL i funs))) args s`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `args:clos_v list` SNOC_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_SNOC_NIL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[evaluate_apps_SNOC; CLOSP1AUX_mti_app_Rec1; CLOSP1AUX_mti_app_Clos1]);;

(* Full application step of the backward simulation (app_cons case): the  *)
(* source evaluates the related body in a related environment            *)
let CLOSP1AUX_mti_full = prove
 (CASE_TERM `!(s1:(C,FFI)clos_state) s f1 f args1 args exp env rest.
    clos_mtiProof_state_rel s1 s /\
    clos_mtiProof_v_rel (clos_state_max_app s1) f1 f /\
    ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) args1 args /\ ~(args = []) /\
    LENGTH args1 <= clos_state_max_app s1 /\
    dest_closure (clos_state_max_app s1) NONE f args = SOME (Full_app exp env rest) ==>
    LENGTH rest < LENGTH args /\
    (clos_state_clock s < LENGTH args - LENGTH rest ==>
       evaluate_apps f1 args1 s1 =
       (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s1)) /\
    (~(clos_state_clock s < LENGTH args - LENGTH rest) ==>
       ?e1 env1 rest1.
         clos_mtiProof_code_rel (clos_state_max_app s1) [e1] [exp] /\
         ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) env1 env /\
         ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) rest1 rest /\
         evaluate_apps f1 args1 s1 =
         (match clos_evaluate ([e1],env1,clos_dec_clock (LENGTH args - LENGTH rest) s1) with
            (Rval [v],s') -> evaluate_apps v rest1 s'
          | res -> res))`,
  REPEAT GEN_TAC THEN CASES_ON `f:clos_v` THEN REWRITE_TAC[clos_mtiProof_v_rel_simps] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   CLOSP1AUX_MTI_LENS_TAC THEN CLOSP1AUX_MTI_EL_F_REL_TAC THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (MATCH_MP state_rel_clocks th)]) THEN
   FIRST_X_ASSUM(MP_TAC o CASE_REWRITE_RULE[] o CONV_RULE(DEPTH_CONV BETA_CONV) o
                REWRITE_RULE[dest_closure_def; check_loc_def; LET_DEF; LET_END_DEF] o
                check (fun th -> is_eq (concl th) &&
                                 CLOSPROPSAUX_is_app "dest_closure" (lhs (concl th)))) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THENL
  [(* Closure *)
   SUBGOAL_THEN `LENGTH (args:clos_v list) <= clos_state_max_app (s1:(C,FFI)clos_state) /\
                 LENGTH (a1:clos_v list) < 1 + LENGTH (ts:mlstring list) + LENGTH a1`
      (fun th -> REWRITE_TAC[th]) THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; injectivity "app_kind";
                                    distinctness "app_kind"] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP1AUX_mti_state_rel_one) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    REWRITE_TAC[LENGTH_REVERSE; LENGTH_DROP; ARITH_RULE `(1 + a + b) - b = 1 + a`] THEN
    SUBGOAL_THEN `LENGTH (args:clos_v list) - (LENGTH args - (1 + LENGTH (ts:mlstring list))) =
                  1 + LENGTH ts` SUBST1_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; DISCH_TAC; DISCH_TAC] THENL
    [MATCH_MP_TAC evaluate_apps_Clos_timeout_alt THEN ASM_REWRITE_TAC[] THEN
     CLOSP1AUX_MTI_ARITH_TAC;
     MP_TAC(SPECL [`args1:clos_v list`; `ts:mlstring list`; `s1:(C,FFI)clos_state`; `e1:clos_exp`;
                   `APPEND args1' env1:clos_v list`] evaluate_apps_Clos_long) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MAP_EVERY EXISTS_TAC
        [`e1:clos_exp`;
         `APPEND (REVERSE (TAKE (1 + LENGTH (ts:mlstring list)) (REVERSE (args1:clos_v list))))
                 (APPEND args1' env1)`;
         `REVERSE (DROP (1 + LENGTH (ts:mlstring list)) (REVERSE (args1:clos_v list)))`] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
     CONJ_TAC THEN CLOSP1AUX_MTI_ENV_ALL2_TAC];
   (* Recclosure, no arguments yet *)
   SUBGOAL_THEN `~(LENGTH (a3:(num#clos_exp)list) <= a4) /\
                 LENGTH (args:clos_v list) <= clos_state_max_app (s1:(C,FFI)clos_state) /\
                 LENGTH ([]:clos_v list) < LENGTH (ts:mlstring list) + 1`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[LENGTH] THEN CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; injectivity "app_kind";
                                    distinctness "app_kind"] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP1AUX_mti_state_rel_one) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; LENGTH; ADD_CLAUSES]) THEN
    REWRITE_TAC[LENGTH; APPEND_NIL; SUB_0; LENGTH_REVERSE; LENGTH_DROP] THEN
    SUBGOAL_THEN `a4 < LENGTH (funs1:(num#clos_exp)list) /\ ~(args1:clos_v list = [])`
      STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSP1AUX_mti_apps_Rec_Clos] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (ts:mlstring list) + 1 = 1 + LENGTH ts` SUBST_ALL_TAC THENL
     [REWRITE_TAC[ADD_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (args:clos_v list) - (LENGTH args - (1 + LENGTH (ts:mlstring list))) =
                  1 + LENGTH ts` SUBST1_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; DISCH_TAC; DISCH_TAC] THENL
    [MATCH_MP_TAC evaluate_apps_Clos_timeout_alt THEN ASM_REWRITE_TAC[] THEN
     CLOSP1AUX_MTI_ARITH_TAC;
     MP_TAC(SPECL [`args1:clos_v list`; `ts:mlstring list`; `s1:(C,FFI)clos_state`; `b1:clos_exp`;
                   `APPEND (list_of_seq (clos_Recclosure NONE [] env1 funs1)
                              (LENGTH (a3:(num#clos_exp)list))) env1`]
             evaluate_apps_Clos_long) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MAP_EVERY EXISTS_TAC
        [`b1:clos_exp`;
         `APPEND (REVERSE (TAKE (1 + LENGTH (ts:mlstring list)) (REVERSE (args1:clos_v list))))
                 (APPEND (list_of_seq (clos_Recclosure NONE [] env1 funs1)
                            (LENGTH (a3:(num#clos_exp)list))) env1)`;
         `REVERSE (DROP (1 + LENGTH (ts:mlstring list)) (REVERSE (args1:clos_v list)))`] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN CONJ_TAC THEN CLOSP1AUX_MTI_ENV_ALL2_TAC];
   (* Recclosure, some arguments *)
   SUBGOAL_THEN `~(LENGTH (a3:(num#clos_exp)list) <= a4) /\
                 LENGTH (args:clos_v list) <= clos_state_max_app (s1:(C,FFI)clos_state) /\
                 LENGTH (a1:clos_v list) < 1 + LENGTH (ts:mlstring list) + LENGTH a1`
      (fun th -> REWRITE_TAC[th]) THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"; injectivity "app_kind";
                                    distinctness "app_kind"] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP1AUX_mti_state_rel_one) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    REWRITE_TAC[LENGTH_REVERSE; LENGTH_DROP; ARITH_RULE `(1 + a + b) - b = 1 + a`] THEN
    SUBGOAL_THEN `LENGTH (args:clos_v list) - (LENGTH args - (1 + LENGTH (ts:mlstring list))) =
                  1 + LENGTH ts` SUBST1_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [CLOSP1AUX_MTI_ARITH_TAC; DISCH_TAC; DISCH_TAC] THENL
     [MATCH_MP_TAC evaluate_apps_Clos_timeout_alt THEN ASM_REWRITE_TAC[] THEN
      CLOSP1AUX_MTI_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`args1:clos_v list`; `ts:mlstring list`; `s1:(C,FFI)clos_state`; `e1:clos_exp`;
                  `APPEND (APPEND args1' recc) env1:clos_v list`] evaluate_apps_Clos_long) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXISTS_TAC
      [`e1:clos_exp`;
       `APPEND (REVERSE (TAKE (1 + LENGTH (ts:mlstring list)) (REVERSE (args1:clos_v list))))
               (APPEND (APPEND args1' recc) env1)`;
       `REVERSE (DROP (1 + LENGTH (ts:mlstring list)) (REVERSE (args1:clos_v list)))`] THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN CONJ_TAC THEN CLOSP1AUX_MTI_ENV_ALL2_TAC]);;

(* related states with the clock set to zero *)
let CLOSP1AUX_mti_state_rel_clock0 = prove
 (`!(s:(C,FFI)clos_state) t.
     clos_mtiProof_state_rel s t ==>
     clos_mtiProof_state_rel (clos_state_clock_fupd (K 0) s) (clos_state_clock_fupd (K 0) t)`,
  REWRITE_TAC[clos_mtiProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[]);;

(* the application of a value to a non-empty list of arguments *)
let CLOSP1AUX_mti_app_cons = prove
 (el 14 CLOSP1AUX_mti_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHQ") (LABEL_TAC "IHP")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)) &&
                                                  rhs (concl th) = `NONE:num option`)) THEN
   FIRST_ASSUM(fun th ->
     if CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" (concl th) &&
        rand (concl th) = `s:(C,FFI)clos_state`
     then RULE_ASSUM_TAC(REWRITE_RULE
            [SYM (CONJUNCT1 (MATCH_MP clos_mtiProof_state_rel_max_app th))])
     else NO_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSPROPSAUX_is_app "evaluate_app" (lhs (concl th)))) THEN
   ONCE_REWRITE_TAC[clos_evaluate_def] THEN
   FIRST_ASSUM(fun th ->
     if CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" (concl th) &&
        rand (concl th) = `s:(C,FFI)clos_state`
     then REWRITE_TAC[SYM (CONJUNCT1 (MATCH_MP clos_mtiProof_state_rel_max_app th))]
     else NO_TAC) THEN
   FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "ALL2" (concl th)
                         then ASSUME_TAC (MATCH_MP LIST_REL_LENGTH th) else NO_TAC) THEN
  CASES_ON `dest_closure (clos_state_max_app (s1:(C,FFI)clos_state)) NONE f
              (CONS (v4:clos_v) v5)` THEN
   CASE_REWRITE_TAC[] THENL
  [(* dest_closure gives NONE *)
   REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`Rerr (Rabort Rtype_error):(clos_v list,clos_v)result`;
                          `s1:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[result_rel_def; exc_rel_def] THEN
    MATCH_MP_TAC dest_closure_NONE_IMP_apps THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSP1AUX_mti_dest_closure_NONE THEN
      MAP_EVERY EXISTS_TAC [`f:clos_v`; `CONS (v4:clos_v) v5`] THEN
      ASM_REWRITE_TAC[NOT_CONS_NIL] THEN CLOSP1AUX_MTI_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH; NOT_SUC]];
   CASES_ON `a:app_kind` THEN CASE_REWRITE_TAC[] THENL
   [(* a partial application *)
    FIRST_ASSUM(fun th -> let c = concl th in
       if is_eq c && CLOSPROPSAUX_is_app "dest_closure" (lhs c) then
         MP_TAC (SPECL [`s1:(C,FFI)clos_state`; `s:(C,FFI)clos_state`; `f1:clos_v`; `f:clos_v`;
                        `args1:clos_v list`; `CONS (v4:clos_v) v5`; rand (rand (rhs c))]
                       CLOSP1AUX_mti_partial)
       else NO_TAC) THEN
     ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
     FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (MATCH_MP state_rel_clocks th)]) THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
     STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN
     CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
     ASM_SIMP_TAC[result_rel_def; exc_rel_def; CLOSP1AUX_mti_state_rel_clock0;
                  CLOSP1AUX_mti_state_rel_dec_clock; ALL2];
    (* a full application *)
    FIRST_ASSUM(fun th -> let c = concl th in
       if is_eq c && CLOSPROPSAUX_is_app "dest_closure" (lhs c) then
         let [e;en;r] = snd (strip_comb (rand (rhs c))) in
         MP_TAC (SPECL [`s1:(C,FFI)clos_state`; `s:(C,FFI)clos_state`; `f1:clos_v`; `f:clos_v`;
                        `args1:clos_v list`; `CONS (v4:clos_v) v5`; e; en; r]
                       CLOSP1AUX_mti_full)
       else NO_TAC) THEN
     ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
      [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
       ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
       ASM_SIMP_TAC[result_rel_def; exc_rel_def; CLOSP1AUX_mti_state_rel_clock0];
       ALL_TAC] THEN
    MP_TAC(ISPEC `clos_evaluate ([a0:clos_exp],a1:clos_v list,
                     clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (a2:clos_v list))
                       (s:(C,FFI)clos_state))` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `rr:(clos_v list,clos_v)result`
       (X_CHOOSE_THEN `tt:(C,FFI)clos_state` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
     REMOVE_THEN "IHP" (MP_TAC o SPECL [`a0:clos_exp`; `a1:clos_v list`; `a2:clos_v list`]) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN(MP_TAC o SPECL [`rr:(clos_v list,clos_v)result`; `tt:(C,FFI)clos_state`;
       `env1:clos_v list`;
       `clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (a2:clos_v list))
          (s1:(C,FFI)clos_state)`; `[e1:clos_exp]`]) THEN
     REWRITE_TAC[CLOSPROPSAUX_max_app_dec_clock] THEN
     ANTS_TAC THENL [ASM_SIMP_TAC[CLOSP1AUX_mti_state_rel_dec_clock]; ALL_TAC] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `rr:(clos_v list,clos_v)result` THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "result_rel" (concl th))) THEN
     REWRITE_TAC[clos_result_rel_Rval2; result_rel_Rerr2] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                                lhs (concl th) = `res1:(clos_v list,clos_v)result`
                             then SUBST_ALL_TAC th else NO_TAC) THEN
     CASE_REWRITE_TAC[] THENL
    [CLOSP1AUX_MTI_SING_TAC THEN CASE_REWRITE_TAC[] THEN
     DISCH_TAC THEN
      REMOVE_THEN "IHQ" (MP_TAC o SPECL [`a0:clos_exp`; `a1:clos_v list`; `r1':clos_v`;
                                         `a2:clos_v list`; `tt:(C,FFI)clos_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`res2:(clos_v list,clos_v)result`; `t2:(C,FFI)clos_state`;
                                 `r1:clos_v`; `rest1:clos_v list`; `s2:(C,FFI)clos_state`]) THEN
      CLOSP1AUX_MTI_MAXAPP_TAC THEN
     ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                                 rand (concl th) = `a2:clos_v list`
                              then ASSUME_TAC (MATCH_MP LIST_REL_LENGTH th) else NO_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN CLOSP1AUX_MTI_ARITH_TAC;
        REWRITE_TAC[]];
     CLOSP1AUX_MTI_FIN_TAC]]]);;

(* HOL4: evaluate_intro_multi *)
let evaluate_intro_multi = prove
 (`(!ys env2 (t1:(C,FFI)clos_state) env1 t2 s1 res2 xs.
      clos_evaluate (ys,env2,t1) = (res2,t2) /\
      ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) env1 env2 /\
      clos_mtiProof_state_rel s1 t1 /\ clos_mtiProof_code_rel (clos_state_max_app s1) xs ys ==>
      ?res1 s2.
        clos_evaluate (xs,env1,s1) = (res1,s2) /\
        result_rel (ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)))
                   (clos_mtiProof_v_rel (clos_state_max_app s1)) res1 res2 /\
        clos_mtiProof_state_rel s2 t2) /\
   (!loc_opt f2 args2 (t1:(C,FFI)clos_state) res2 t2 f1 args1 s1.
      evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\ loc_opt = NONE /\
      clos_mtiProof_v_rel (clos_state_max_app s1) f1 f2 /\
      ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) args1 args2 /\
      clos_mtiProof_state_rel s1 t1 /\ LENGTH args1 <= clos_state_max_app s1 ==>
      ?res1 s2.
        evaluate_apps f1 args1 s1 = (res1,s2) /\
        result_rel (ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)))
                   (clos_mtiProof_v_rel (clos_state_max_app s1)) res1 res2 /\
        clos_mtiProof_state_rel s2 t2)`,
  let th = MATCH_MP CLOSP1AUX_mti_ind
             (end_itlist CONJ
                [CLOSP1AUX_mti_nil; CLOSP1AUX_mti_cons; CLOSP1AUX_mti_var; CLOSP1AUX_mti_if;
                 CLOSP1AUX_mti_let; CLOSP1AUX_mti_raise; CLOSP1AUX_mti_handle;
                 CLOSP1AUX_mti_op; CLOSP1AUX_mti_fn; CLOSP1AUX_mti_letrec; CLOSP1AUX_mti_app;
                 CLOSP1AUX_mti_tick; CLOSP1AUX_mti_call; CLOSP1AUX_mti_app_nil;
                 CLOSP1AUX_mti_app_cons]) in
  CONJ_TAC THENL [MATCH_ACCEPT_TAC (CONJUNCT1 th); MATCH_ACCEPT_TAC (CONJUNCT2 th)]);;

(* HOL4: intro_multi_correct *)
let intro_multi_correct = prove
 (`!xs env1 (s1:(C,FFI)clos_state) res1 s2 env2 (t2:(C,FFI)clos_state) t1.
     clos_evaluate (xs,env1,s1) = (res1,s2) /\ ALL no_mti xs /\
     ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)) env1 env2 /\
     clos_mtiProof_state_rel s1 t1 ==>
     ?res2 t2.
       clos_evaluate (intro_multi (clos_state_max_app s1) xs,env2,t1) = (res2,t2) /\
       result_rel (ALL2 (clos_mtiProof_v_rel (clos_state_max_app s1)))
                  (clos_mtiProof_v_rel (clos_state_max_app s1)) res1 res2 /\
       clos_mtiProof_state_rel s2 t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `clos_evaluate (intro_multi (clos_state_max_app (s1:(C,FFI)clos_state)) xs,
                               env2,t1:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `t:(C,FFI)clos_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:(clos_v list,clos_v)result`; `t:(C,FFI)clos_state`] THEN
  MP_TAC(SPECL [`intro_multi (clos_state_max_app (s1:(C,FFI)clos_state)) xs`;
                `env2:clos_v list`; `t1:(C,FFI)clos_state`; `env1:clos_v list`;
                `t:(C,FFI)clos_state`; `s1:(C,FFI)clos_state`; `r:(clos_v list,clos_v)result`;
                `xs:clos_exp list`] (CONJUNCT1 evaluate_intro_multi)) THEN
  ASM_REWRITE_TAC[clos_mtiProof_code_rel_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s3:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `res1:(clos_v list,clos_v)result = r1 /\ s2:(C,FFI)clos_state = s3`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[PAIR_EQ]; ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* syntax well-formedness                                                    *)
(* ------------------------------------------------------------------------- *)

(* HOL4: contains_App_SOME_collect_args *)
let contains_App_SOME_collect_args = prove
 (`!m x y a b. collect_args m x y = (a,b) ==>
               (contains_App_SOME m [y] <=> contains_App_SOME m [b])`,
  MATCH_MP_TAC collect_args_ind THEN RW[collect_args_def; contains_App_SOME_def] THEN
  FS[contains_App_SOME_def]);;

(* local helpers: contains_App_SOME of a CONS and of an APPEND (flat_to_clos- *)
(* Proof's contains_App_SOME_APPEND)                                         *)
let CLOSP1AUX_mti_contains_cons = prove
 (`!m x xs. contains_App_SOME m (CONS x xs) <=>
            contains_App_SOME m [x] \/ contains_App_SOME m xs`,
  REPEAT GEN_TAC THEN CASES_ON `xs:clos_exp list` THEN REWRITE_TAC[contains_App_SOME_def]);;

let CLOSP1AUX_mti_contains_APPEND = prove
 (`!m l1 l2. contains_App_SOME m (APPEND l1 l2) <=>
             contains_App_SOME m l1 \/ contains_App_SOME m l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; contains_App_SOME_def] THEN
  ONCE_REWRITE_TAC[CLOSP1AUX_mti_contains_cons] THEN ASM_REWRITE_TAC[DISJ_ACI]);;

(* HOL4: contains_App_SOME_collect_apps *)
let contains_App_SOME_collect_apps = prove
 (`!max_app x y a b. collect_apps max_app x y = (a,b) ==>
     (max_app < LENGTH x \/ contains_App_SOME max_app x \/ contains_App_SOME max_app [y] <=>
      max_app < LENGTH a \/ contains_App_SOME max_app a \/ contains_App_SOME max_app [b])`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_TAC; STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:clos_exp list`; `b:clos_exp`] o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; CLOSP1AUX_mti_contains_APPEND] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[contains_App_SOME_def; IS_SOME_DEF] THEN
  SUBGOAL_THEN `~(max_app < LENGTH (args:clos_exp list)) /\
                ~(max_app < LENGTH (es:clos_exp list)) /\
                ~(max_app < LENGTH args + LENGTH es)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[DISJ_ACI]]);;

(* the hypotheses about the parts named by PAIRARG_TAC, unwound *)
let CLOSP1AUX_MTI_UNWIND_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1]);;

(* local helper: contains_App_SOME of the bodies of mapped functions *)
let CLOSP1AUX_mti_contains_MAP = prove
 (`!m (f:num#clos_exp->num#clos_exp) funs.
     (!p. MEM p funs ==> (contains_App_SOME m [SND (f p)] <=> contains_App_SOME m [SND p])) ==>
     (contains_App_SOME m (MAP SND (MAP f funs)) <=> contains_App_SOME m (MAP SND funs))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CLOSP1AUX_mti_contains_cons] THEN
  BINOP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* the thunk operation of the goal, split *)
let CLOSP1AUX_MTI_THUNKOP_TAC (thl:thm list) : tactic = fun (asl,w as gl) ->
  let tm = find_term (fun t -> is_comb t && is_const (rator t) &&
                               fst (dest_const (rator t)) = "clos_ThunkOp") w in
  (CASES_ON (rand tm) THEN REWRITE_TAC thl THEN ASM_REWRITE_TAC[]) gl;;

(* HOL4: contains_App_SOME_intro_multi [simp] *)
let contains_App_SOME_intro_multi = prove
 (`!max_app es. contains_App_SOME max_app (intro_multi max_app es) <=>
                contains_App_SOME max_app es`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[intro_multi_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[contains_App_SOME_def] THEN
  ONCE_REWRITE_TAC[CLOSP1AUX_mti_contains_cons] THEN
  REWRITE_TAC[HD_intro_multi; contains_App_SOME_def; intro_multi_length; IS_SOME_DEF] THEN
  ASM_REWRITE_TAC[] THENL
   [(* App NONE *)
    CLOSP1AUX_MTI_UNWIND_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP contains_App_SOME_collect_apps) THEN
    REWRITE_TAC[DISJ_ACI] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    (* Fn NONE NONE *)
    CLOSP1AUX_MTI_UNWIND_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP contains_App_SOME_collect_args) THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    (* Letrec NONE NONE *)
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CLOSP1AUX_mti_contains_MAP THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `e0:clos_exp`] THEN
    DISCH_TAC THEN CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN REWRITE_TAC[HD_intro_multi] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP contains_App_SOME_collect_args) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[];
    (* Op *)
    CASES_ON `op:clos_op` THEN REWRITE_TAC[contains_App_SOME_def] THEN
    ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_THUNKOP_TAC[contains_App_SOME_def]]);;
let _ = cake_add_simps [contains_App_SOME_intro_multi];;

(* HOL4: contains_App_SOME_compile [simp] *)
let contains_App_SOME_compile = prove
 (`!do_mti es. contains_App_SOME max_app (clos_mti_compile do_mti max_app es) <=>
               contains_App_SOME max_app es`,
  REPEAT GEN_TAC THEN CASES_ON `do_mti:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; contains_App_SOME_intro_multi]);;
let _ = cake_add_simps [contains_App_SOME_compile];;

(* HOL4: collect_args_preserves_esgc_free *)
let collect_args_preserves_esgc_free = prove
 (`!max_app n e n' e'. collect_args max_app n e = (n',e') /\ clos_esgc_free e ==>
                       clos_esgc_free e'`,
  MATCH_MP_TAC collect_args_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_args_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `num_args + num_args' <= max_app`)) THEN
  DISCH_THEN(MATCH_MP_TAC o SPECL [`n':num`; `e':clos_exp`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC set_globals_empty_esgc_free THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_esgc_free_def]) THEN ASM_REWRITE_TAC[]);;

(* HOL4: every_Fn_vs_NONE_collect_apps [local] *)
let every_Fn_vs_NONE_collect_apps = prove
 (`!max_app es e x y. collect_apps max_app es e = (x,y) ==>
     (every_Fn_vs_NONE x /\ every_Fn_vs_NONE [y] <=>
      every_Fn_vs_NONE es /\ every_Fn_vs_NONE [e])`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_TAC; STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:clos_exp list`; `y:clos_exp`] o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  ASM_REWRITE_TAC[every_Fn_vs_NONE_APPEND; every_Fn_vs_NONE_def] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

(* HOL4: every_Fn_vs_NONE_collect_args [local] *)
let every_Fn_vs_NONE_collect_args = prove
 (`!max_app es e x y. collect_args max_app es e = (x,y) ==>
     (every_Fn_vs_NONE [y] <=> every_Fn_vs_NONE [e])`,
  MATCH_MP_TAC collect_args_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_args_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:clos_exp`] o C MP (ASSUME
    `num_args + num_args' <= max_app`)) THEN
  ASM_REWRITE_TAC[every_Fn_vs_NONE_def; IS_NONE_DEF] THEN DISCH_THEN ACCEPT_TAC);;

(* local helper: every_Fn_vs_NONE of the bodies of mapped functions *)
let CLOSP1AUX_mti_every_Fn_vs_NONE_MAP = prove
 (`!(f:num#clos_exp->num#clos_exp) funs.
     (!p. MEM p funs ==> (every_Fn_vs_NONE [SND (f p)] <=> every_Fn_vs_NONE [SND p])) ==>
     (every_Fn_vs_NONE (MAP SND (MAP f funs)) <=> every_Fn_vs_NONE (MAP SND funs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_vs_NONE_cons] THEN
  BINOP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4: every_Fn_vs_NONE_intro_multi [simp] *)
let every_Fn_vs_NONE_intro_multi = prove
 (`!max_app es. every_Fn_vs_NONE (intro_multi max_app es) <=> every_Fn_vs_NONE es`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[intro_multi_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[every_Fn_vs_NONE_def] THEN
  ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_vs_NONE_cons] THEN
  REWRITE_TAC[HD_intro_multi; every_Fn_vs_NONE_def; IS_NONE_DEF] THEN
  ASM_REWRITE_TAC[] THENL
   [(* App NONE *)
    CLOSP1AUX_MTI_UNWIND_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP every_Fn_vs_NONE_collect_apps) THEN
    REWRITE_TAC[CONJ_ACI];
    (* Fn NONE NONE *)
    CLOSP1AUX_MTI_UNWIND_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP every_Fn_vs_NONE_collect_args);
    (* Letrec NONE NONE *)
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CLOSP1AUX_mti_every_Fn_vs_NONE_MAP THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `e0:clos_exp`] THEN
    DISCH_TAC THEN CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN REWRITE_TAC[HD_intro_multi] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP every_Fn_vs_NONE_collect_args) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[]]);;
let _ = cake_add_simps [every_Fn_vs_NONE_intro_multi];;

(* HOL4: compile_EQ_NIL [simp] *)
let compile_EQ_NIL = prove
 (`!do_mti es. clos_mti_compile do_mti max_app es = [] <=> es = []`,
  REPEAT GEN_TAC THEN CASES_ON `do_mti:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; intro_multi_EQ_NIL]);;
let _ = cake_add_simps [compile_EQ_NIL];;

(* HOL4: compile_length [simp] *)
let clos_mtiProof_compile_length = prove
 (`LENGTH (clos_mti_compile do_mti max_app es) = LENGTH es`,
  CASES_ON `do_mti:bool` THEN REWRITE_TAC[clos_mti_compile_def; intro_multi_length]);;
let _ = cake_add_simps [clos_mtiProof_compile_length];;

(* HOL4: EVERY_HD [local] *)
let EVERY_HD = prove
 (`ALL (P:A->bool) l /\ ~(l = []) ==> P (HD l)`,
  CASES_ON `l:A list` THEN SIMP_TAC[ALL; HD]);;

(* HOL4: collect_apps_preserves_set_globals *)
let collect_apps_preserves_set_globals = prove
 (`!max_app es e es' e'.
     collect_apps max_app es e = (es',e') ==>
     BAG_UNION (clos_elist_globals es) (clos_set_globals e) =
     BAG_UNION (clos_elist_globals es') (clos_set_globals e')`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_TAC; STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`es':clos_exp list`; `e':clos_exp`] o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  ASM_REWRITE_TAC[clos_elist_globals_append; clos_set_globals_def] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[BAG_UNION; FUN_EQ_THM] THEN ARITH_TAC);;

(* HOL4: collect_apps_preserves_esgc_free *)
let collect_apps_preserves_esgc_free = prove
 (`!max_app es e es' e'.
     collect_apps max_app es e = (es',e') /\ ALL clos_esgc_free es /\ clos_esgc_free e ==>
     ALL clos_esgc_free es' /\ clos_esgc_free e'`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  DISCH_THEN(MATCH_MP_TAC o SPECL [`es':clos_exp list`; `e':clos_exp`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_esgc_free_def]) THEN
  ASM_REWRITE_TAC[ALL_APPEND]);;

(* HOL4: collect_args_preserves_set_globals *)
let collect_args_preserves_set_globals = prove
 (`!max_app n e n' e'. collect_args max_app n e = (n',e') ==>
                       clos_set_globals e' = clos_set_globals e`,
  MATCH_MP_TAC collect_args_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_args_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n':num`; `e':clos_exp`] o C MP (ASSUME
    `num_args + num_args' <= max_app`)) THEN
  ASM_REWRITE_TAC[clos_set_globals_def]);;

(* local helpers: the globals of a HD of intro_multi, and of mapped bodies *)
let CLOSP1AUX_mti_set_globals_HD = prove
 (`!m e. clos_set_globals (HD (intro_multi m [e])) = clos_elist_globals (intro_multi m [e])`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`e:clos_exp`; `m:num`] intro_multi_sing) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD; clos_set_globals_def; BAG_UNION_EMPTY]);;

let CLOSP1AUX_mti_elist_MAP = prove
 (`!(f:num#clos_exp->num#clos_exp) funs.
     (!p. MEM p funs ==> clos_set_globals (SND (f p)) = clos_set_globals (SND p)) ==>
     clos_elist_globals (MAP SND (MAP f funs)) = clos_elist_globals (MAP SND funs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; clos_set_globals_def] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4: intro_multi_preserves_elist_globals *)
let intro_multi_preserves_elist_globals = prove
 (`!max_app es. clos_elist_globals (intro_multi max_app es) = clos_elist_globals es`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[intro_multi_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[clos_set_globals_def; CLOSP1AUX_mti_set_globals_HD] THEN
  ASM_REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY] THEN
  CLOSP1AUX_MTI_UNWIND_TAC THEN
  ASM_REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY] THENL
   [(* App NONE *)
    FIRST_ASSUM(MP_TAC o MATCH_MP collect_apps_preserves_set_globals) THEN
    MESON_TAC[COMM_BAG_UNION];
    (* Fn NONE NONE *)
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP collect_args_preserves_set_globals);
    (* Letrec NONE NONE *)
    AP_TERM_TAC THEN MATCH_MP_TAC CLOSP1AUX_mti_elist_MAP THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `e0:clos_exp`] THEN
    DISCH_TAC THEN CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN
    REWRITE_TAC[CLOSP1AUX_mti_set_globals_HD] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP collect_args_preserves_set_globals) THEN
    SUBGOAL_THEN `clos_set_globals e' = clos_elist_globals [e']` SUBST1_TAC THENL
     [REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[]]);;

(* local helper: the globals of the bodies of the functions of a Letrec, *)
(* after intro_multi                                                      *)
let CLOSP1AUX_mti_letrec_elist = prove
 (CASE_TERM `!max_app funs.
     clos_elist_globals
       (MAP SND (MAP (\p. match p with
                            (num_args,e) ->
                              let (num_args',e') = collect_args max_app num_args e in
                                (num_args', HD (intro_multi max_app [e'])))
                     funs)) =
     clos_elist_globals (MAP SND funs)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CLOSP1AUX_mti_elist_MAP THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `e0:clos_exp`] THEN
  DISCH_TAC THEN CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN
  REWRITE_TAC[CLOSP1AUX_mti_set_globals_HD; intro_multi_preserves_elist_globals;
              clos_set_globals_def; BAG_UNION_EMPTY] THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP collect_args_preserves_set_globals));;

(* local helper: ALL of a singleton intro_multi *)
let CLOSP1AUX_mti_ALL_HD = prove
 (`!P m e. ALL P (intro_multi m [e]) <=> P (HD (intro_multi m [e]))`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`e:clos_exp`; `m:num`] intro_multi_sing) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ALL; HD]);;

(* HOL4: intro_multi_preserves_esgc_free *)
let intro_multi_preserves_esgc_free = prove
 (`!max_app es. ALL clos_esgc_free es ==> ALL clos_esgc_free (intro_multi max_app es)`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[intro_multi_def] THEN REPEAT PAIRARG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP1AUX_mti_ALL_HD; ALL]) THEN
  REWRITE_TAC[ALL; clos_esgc_free_def; CLOSP1AUX_mti_letrec_elist;
              CLOSP1AUX_mti_set_globals_HD; intro_multi_preserves_elist_globals] THEN
  CLOSP1AUX_MTI_UNWIND_TAC THEN
  REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [(* App NONE *)
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_apps_preserves_esgc_free)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    (* Fn NONE NONE *)
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP collect_args_preserves_set_globals) THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4: compile_preserves_elist_globals *)
let compile_preserves_elist_globals = prove
 (`!do_mti es. clos_elist_globals (clos_mti_compile do_mti max_app es) =
               clos_elist_globals es`,
  REPEAT GEN_TAC THEN CASES_ON `do_mti:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; intro_multi_preserves_elist_globals]);;

(* HOL4: compile_preserves_esgc_free *)
let compile_preserves_esgc_free = prove
 (`!do_mti es. ALL clos_esgc_free es ==>
               ALL clos_esgc_free (clos_mti_compile do_mti max_app es)`,
  REPEAT GEN_TAC THEN CASES_ON `do_mti:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; intro_multi_preserves_esgc_free]);;

(* HOL4: EVERY_intro_multi *)
let EVERY_intro_multi = prove
 (`!m xs. ALL (P:clos_exp->bool) (intro_multi m xs) <=>
          ALL (\x. P (HD (intro_multi m [x]))) xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[intro_multi_def; ALL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [intro_multi_cons] THEN ASM_REWRITE_TAC[ALL]);;

(* local helper: collect_apps keeps the length of the arguments within max_app *)
let CLOSP1AUX_mti_collect_apps_len = prove
 (`!max_app args e es e'.
     collect_apps max_app args e = (es,e') /\ LENGTH args <= max_app ==>
     LENGTH es <= max_app`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  DISCH_THEN(MATCH_MP_TAC o SPECL [`es':clos_exp list`; `e':clos_exp`]) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND]);;

(* HOL4: intro_multi_obeys_max_app *)
let intro_multi_obeys_max_app = prove
 (`!m xs. ~(m = 0) /\ ALL no_mti xs ==> ALL (obeys_max_app m) (intro_multi m xs)`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[intro_multi_def] THEN REPEAT PAIRARG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP1AUX_mti_ALL_HD; ALL]) THEN
  REWRITE_TAC[ALL; obeys_max_app_def; no_mti_def; intro_multi_length;
              distinctness "option"] THEN
  CLOSP1AUX_MTI_UNWIND_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [(* App NONE *)
    SUBGOAL_THEN `ALL no_mti (es':clos_exp list) /\ no_mti e'` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC collect_apps_no_mti THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (es':clos_exp list) <= max_app` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSP1AUX_mti_collect_apps_len THEN
      MAP_EVERY EXISTS_TAC [`es:clos_exp list`; `e:clos_exp`; `e':clos_exp`] THEN
      ASM_REWRITE_TAC[] THEN CLOSP1AUX_MTI_ARITH_TAC;
      ASM_SIMP_TAC[]];
    (* Fn NONE NONE *)
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_args_ok_IMP)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    (* Letrec NONE NONE *)
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `e0:clos_exp`] THEN DISCH_TAC THEN
    CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN REWRITE_TAC[SND] THEN
    UNDISCH_TAC `ALL (\x. FST x = 1 /\ no_mti (SND x)) (funs:(num#clos_exp)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(n:num,e0:clos_exp)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_args_ok_IMP)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[]]);;

(* HOL4: collect_apps_no_Labels *)
let collect_apps_no_Labels = prove
 (`!m es e es' e'.
     collect_apps m es e = (es',e') /\ ALL no_Labels es /\ no_Labels e ==>
     ALL no_Labels es' /\ no_Labels e'`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  DISCH_THEN(MATCH_MP_TAC o SPECL [`es':clos_exp list`; `e':clos_exp`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[no_Labels_def]) THEN
  ASM_REWRITE_TAC[ALL_APPEND]);;

(* HOL4: collect_args_no_Labels *)
let collect_args_no_Labels = prove
 (`!m na e es' e'.
     collect_args m na e = (es',e') /\ no_Labels e ==> no_Labels e'`,
  MATCH_MP_TAC collect_args_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_args_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `num_args + num_args' <= max_app`)) THEN
  DISCH_THEN(MATCH_MP_TAC o SPECL [`es':num`; `e':clos_exp`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[no_Labels_def]) THEN ASM_REWRITE_TAC[]);;

(* HOL4: intro_multi_no_Labels *)
let intro_multi_no_Labels = prove
 (`!m xs. ALL no_Labels xs ==> ALL no_Labels (intro_multi m xs)`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REWRITE_TAC[intro_multi_def] THEN REPEAT PAIRARG_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP1AUX_mti_ALL_HD; ALL]) THEN
  REWRITE_TAC[ALL; no_Labels_def] THEN
  CLOSP1AUX_MTI_UNWIND_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [(* App NONE *)
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] collect_apps_no_Labels)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    (* Fn NONE NONE *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC collect_args_no_Labels THEN
    ASM_MESON_TAC[];
    (* Letrec NONE NONE *)
    UNDISCH_TAC `ALL no_Labels (MAP SND (funs:(num#clos_exp)list))` THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `e0:clos_exp`] THEN DISCH_TAC THEN
    CASE_REWRITE_TAC[] THEN PAIRARG_TAC THEN REWRITE_TAC[SND] THEN
    SUBGOAL_THEN `no_Labels e'` ASSUME_TAC THENL
     [MATCH_MP_TAC collect_args_no_Labels THEN
      MAP_EVERY EXISTS_TAC [`max_app:num`; `n:num`; `e0:clos_exp`; `num_args':num`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SND] o
        SPECL [`n:num`; `e0:clos_exp`] o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[]]]);;

(* preservation of observable semantics *)

(* HOL4: semantics_intro_multi *)
let semantics_intro_multi = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num->C#clos_prog)
       (pure_cc (clos_mti_compile_inc max_app)
                (cc:C->clos_prog->(byte list#int64 list#C)option)) xs = Fail) ==>
   (!n. SND (SND (co n)) = [] /\ ALL no_mti (FST (SND (co n)))) /\
   1 <= max_app /\ ALL no_mti xs ==>
   clos_semantics ffi max_app FEMPTY (pure_co (clos_mti_compile_inc max_app) o co) cc
     (intro_multi max_app xs) =
   clos_semantics ffi max_app FEMPTY co (pure_cc (clos_mti_compile_inc max_app) cc) xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `max_app:num`; `FEMPTY:(num,num#clos_exp)fmap`;
                 `co:num->C#clos_prog`;
                 `(pure_cc (clos_mti_compile_inc max_app)
                    (cc:C->clos_prog->(byte list#int64 list#C)option)):
                  C->clos_prog->(byte list#int64 list#C)option`;
                 `xs:clos_exp list`; `FEMPTY:(num,num#clos_exp)fmap`;
                 `(pure_co (clos_mti_compile_inc max_app) o (co:num->C#clos_prog)):
                  num->C#clos_prog`;
                 `cc:C->clos_prog->(byte list#int64 list#C)option`;
                 `intro_multi max_app xs`;
                 `\(c1:(num,num#clos_exp)fmap) (o1:num->C#clos_prog)
                   (k1:C->clos_prog->(byte list#int64 list#C)option)
                   (e1:clos_exp list) (c2:(num,num#clos_exp)fmap) (o2:num->C#clos_prog)
                   (k2:C->clos_prog->(byte list#int64 list#C)option) (e2:clos_exp list). T`]
                clos_IMP_semantics_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[clos_eval_sim_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(SPECL [`xs:clos_exp list`; `[]:clos_v list`;
                `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY (co:num->C#clos_prog)
                   (pure_cc (clos_mti_compile_inc max_app)
                      (cc:C->clos_prog->(byte list#int64 list#C)option)) k`;
                `res1:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`; `[]:clos_v list`;
                `s2:(C,FFI)clos_state`;
                `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                   (pure_co (clos_mti_compile_inc max_app) o (co:num->C#clos_prog))
                   (cc:C->clos_prog->(byte list#int64 list#C)option) k`]
               intro_multi_correct) THEN
  ASM_REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[clos_mtiProof_state_rel_def; clos_state_INFO.ri_accessors; ALL2;
                clos_mtiProof_FMAP_REL_def; FLOOKUP_EMPTY; distinctness "option"] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM clos_initial_state_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`res2:(clos_v list,clos_v)result`; `t2:(C,FFI)clos_state`] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_mtiProof_state_rel_def] o
    check (CLOSPROPSAUX_is_app "clos_mtiProof_state_rel" o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "result_rel" o concl)) THEN
  CASES_ON `res1:(clos_v list,clos_v)result` THEN
  CASES_ON `res2:(clos_v list,clos_v)result` THEN
  REWRITE_TAC[result_rel_def] THEN
  TRY(CASES_ON `a:(clos_v)error_result` THEN CASES_ON `a':(clos_v)error_result`) THEN
  REWRITE_TAC[exc_rel_def]);;

(* HOL4: semantics_compile *)
let clos_mtiProof_semantics_compile = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num->C#clos_prog) cc1 xs = Fail) /\
   cc1 = (if do_mti then pure_cc (clos_mti_compile_inc max_app) else I)
           (cc:C->clos_prog->(byte list#int64 list#C)option) /\
   co1 = (if do_mti then pure_co (clos_mti_compile_inc max_app) else I) o co /\
   (do_mti ==> (!n. SND (SND (co n)) = [] /\ ALL no_mti (FST (SND (co n)))) /\
               1 <= max_app /\ ALL no_mti xs) ==>
   clos_semantics ffi max_app FEMPTY co1 cc (clos_mti_compile do_mti max_app xs) =
   clos_semantics ffi max_app FEMPTY co cc1 xs`,
  CASES_ON `do_mti:bool` THEN REWRITE_TAC[clos_mti_compile_def; I_THM; I_O_ID] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] semantics_intro_multi) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_MESON_TAC[]);;
