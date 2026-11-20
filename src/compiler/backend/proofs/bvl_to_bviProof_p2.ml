(* ========================================================================= *)
(* bvl_to_bviProof_p2: part 2 of 2 (HOL4 lines 2201-5878) of bvl_to_bviProof, *)
(* port of HOL4 compiler/backend/proofs/bvl_to_bviProofScript.sml (CakeML    *)
(* v3479).  Correctness proof for bvl_to_bvi: compile_exps_correct, the     *)
(* composed correctness of compile_prog and compile, the no_mutcons lemmas  *)
(* for bvi_tmc's input condition, the distinctness of the generated names    *)
(* and the code labels.  B2BP2AUX_ names are local helpers (not HOL4         *)
(* names).  The rendering notes of part 1 (bvl_to_bviProof_p1.ml) apply.     *)
(* ========================================================================= *)

needs "compiler/backend/proofs/bvl_to_bviProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 2201-5878 ===== *)

(* HOL4 line 2184: val goal (the statement of compile_exps_correct as a   *)
(* predicate of (xs,env,s1)); here the helper definition B2BP2AUX_cec, one *)
(* top-level lemma per case of eval_ind_alt (HOL4 suspend/Resume)         *)
let B2BP2AUX_cec_def = new_definition
  `B2BP2AUX_cec (xs,env,s1:(num#C,FFI)bvl_state) <=>
     !n res s2 (t1:(C,FFI)bvi_state) n2 ys aux b1.
       bvl_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
       bvl_to_bvi_compile_exps n xs = (ys,aux,n2) /\
       bvl_to_bviProof_state_rel b1 s1 t1 /\
       bvl_to_bviProof_state_ok s1 /\ ALL (bv_ok (bvl_state_refs s1)) env /\
       aux_code_installed (append aux) (bvi_state_code t1) /\
       handle_ok xs /\ IS_SOME (bvi_state_global t1)
       ==> ?t2 b2 c.
             bvi_evaluate (ys,MAP (adjust_bv b2) env,bvi_inc_clock c t1) =
               (map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) res,t2) /\
             bvl_to_bviProof_state_rel b2 s2 t2 /\
             MAP (adjust_bv b1) env = MAP (adjust_bv b2) env /\
             (!a. a IN FDOM (bvl_state_refs s1) ==> b1 a = b2 a)`;;

(* local tactics: name the two components of a pair-valued term (HOL4    *)
(* `?r s. e = (r,s)` by METIS_TAC [PAIR] followed by fs) *)
let B2BP2AUX_dest_pair_ty ty =
  match dest_type ty with ("prod",[a;b]) -> a,b | _ -> failwith "B2BP2AUX_dest_pair_ty";;

let B2BP2AUX_PAIR_TAC tm a b : tactic =
  let ta,tb = B2BP2AUX_dest_pair_ty (type_of tm) in
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN (mk_var(a,ta)) (X_CHOOSE_THEN (mk_var(b,tb))
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th THEN REWRITE_TAC[th])));;

(* case split of a term of type result (Rval / Rerr) or error_result     *)
(* (Rraise / Rabort) into the given variable names, substituting it       *)
let B2BP2AUX_CASES2_TAC tyname tm v1 v2 : tactic =
  let th = ISPEC tm (case_info_of_tyname tyname).ci_nchotomy in
  let d1,d2 = dest_disj (concl th) in
  let x1 = fst(dest_exists d1) and x2 = fst(dest_exists d2) in
  DISJ_CASES_THEN2 (X_CHOOSE_THEN (mk_var(v1,type_of x1)) SUBST_ALL_TAC)
                   (X_CHOOSE_THEN (mk_var(v2,type_of x2)) SUBST_ALL_TAC) th;;

let B2BP2AUX_RESULT_TAC = B2BP2AUX_CASES2_TAC "result";;
let B2BP2AUX_ERROR_TAC = B2BP2AUX_CASES2_TAC "error_result";;

(* HOL4 drule_all on an induction hypothesis: discharge the antecedents of *)
(* th (curried) with assumptions, in order (with backtracking); a closed     *)
(* antecedent that no assumption matches is proved by the tactic prv under  *)
(* the assumptions                                                           *)
let rec B2BP2AUX_drule_all (prv:tactic) asl th =
  let c = concl th in
  if not (is_imp (snd (strip_forall c))) then th else
  let mp = MATCH_MP_CURRIED th in
  try tryfind (fun a -> B2BP2AUX_drule_all prv asl (mp a)) (map snd asl)
  with Failure _ ->
    let vs,body = strip_forall c in
    let a,_ = dest_imp body in
    if intersect (frees a) vs <> [] then failwith "B2BP2AUX_drule_all" else
    let tha = TAC_PROOF((asl,a),prv) in
    B2BP2AUX_drule_all prv asl (GENL vs (MP (SPECL vs th) tha));;

let B2BP2AUX_cec_of th =
  let c = concl th in
  let f,args = strip_comb c in
  if is_const f && fst(dest_const f) = "B2BP2AUX_cec" then fst(dest_pair(hd args))
  else failwith "B2BP2AUX_cec_of";;

(* apply the induction hypothesis B2BP2AUX_cec (xs,env,s) for the given     *)
(* expression list xs: MP_TAC its conclusion ?t2 b2 c. ...                   *)
let B2BP2AUX_IH_TAC (xs:term) (prv:tactic) : tactic = fun (asl,w as g) ->
  let _,ih = find (fun (_,th) -> try aconv (B2BP2AUX_cec_of th) xs with Failure _ -> false) asl in
  let ih' = IMP_CURRY_RULE (REWRITE_RULE[B2BP2AUX_cec_def] ih) in
  MP_TAC (B2BP2AUX_drule_all prv asl ih') g;;

let B2BP2AUX_PRV_TAC : tactic =
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result";
                  distinctness "error_result"; injectivity "error_result"] THEN NO_TAC;;

(* for every assumption compile_exps n [e] = (c,aux,n1): add c = [y]        *)
(* (HOL4 IMP_RES_TAC compile_exps_SING), substituting c                     *)
let B2BP2AUX_SING_TAC : tactic =
  ASSUM_LIST(fun thl -> MAP_EVERY (fun th ->
    try let th' = MATCH_MP bvl_to_bvi_compile_exps_SING th in
        CHOOSE_THEN SUBST_ALL_TAC th'
    with Failure _ -> ALL_TAC) thl);;

(* HOL4 drule_all th with the fallback prover B2BP2AUX_PRV_TAC *)
let B2BP2AUX_DRULE_ALL_TAC th : tactic = fun (asl,w as g) ->
  MP_TAC (B2BP2AUX_drule_all B2BP2AUX_PRV_TAC asl (IMP_CURRY_RULE (GEN_ALL th))) g;;

(* substitute an assumption v = tm (v the given variable) everywhere *)
let B2BP2AUX_SUBST_VAR_TAC (v:term) : tactic =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let c = concl th in is_eq c && lhs c = v));;
(* local helpers for compile_exps_correct *)
let B2BP2AUX_bvl_eval_facts = prove
 (`!xs env (s:(num#C,FFI)bvl_state) res s5.
     bvl_evaluate (xs,env,s) = (res,s5) /\
     bvl_to_bviProof_state_ok s /\ ALL (bv_ok (bvl_state_refs s)) env
     ==> bvl_to_bviProof_state_ok s5 /\ ALL (bv_ok (bvl_state_refs s5)) env /\
         FDOM (bvl_state_refs s) SUBSET FDOM (bvl_state_refs s5) /\
         (!vs. res = Rval vs ==> ALL (bv_ok (bvl_state_refs s5)) vs) /\
         (!v. res = Rerr (Rraise v) ==> bv_ok (bvl_state_refs s5) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvl_evaluate_refs_SUBSET) THEN
  MP_TAC(ISPECL [`xs:bvl_exp list`; `env:bvl_v list`; `s:(num#C,FFI)bvl_state`;
                `res:(bvl_v list,bvl_v)result`; `s5:(num#C,FFI)bvl_state`] evaluate_ok) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[]);;

let B2BP2AUX_bvi_eval_mono = prove
 (`!xs E c (t1:(C,FFI)bvi_state) r t2 (aux:(num#num#bvi_exp)list).
     bvi_evaluate (xs,E,bvi_inc_clock c t1) = (r,t2) /\
     aux_code_installed aux (bvi_state_code t1) /\ IS_SOME (bvi_state_global t1)
     ==> aux_code_installed aux (bvi_state_code t2) /\ IS_SOME (bvi_state_global t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC aux_code_installed_subspt THEN
    EXISTS_TAC `bvi_state_code (t1:(C,FFI)bvi_state)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_code_mono) THEN
    REWRITE_TAC[bvi_inc_clock_code];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_global_mono) THEN
    ASM_REWRITE_TAC[inc_clock_global]]);;

let B2BP2AUX_agree_trans = prove
 (`!(b1:num->num) b2 b3 (r1:num->bool) r2.
     (!a. a IN r1 ==> b1 a = b2 a) /\ (!a. a IN r2 ==> b2 a = b3 a) /\ r1 SUBSET r2
     ==> (!a. a IN r1 ==> b1 a = b3 a)`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let B2BP2AUX_MAP_adjust_eq = prove
 (`!refs (b1:num->num) b2 vs.
     ALL (bv_ok refs) vs /\ (!a. a IN FDOM refs ==> b1 a = b2 a)
     ==> MAP (adjust_bv b1) vs = MAP (adjust_bv b2) vs`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CONS_11] THEN
  MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq THEN ASM_MESON_TAC[]);;

let B2BP2AUX_adjust_update = prove
 (`!refs (b:num->num) x y v.
     bv_ok refs v /\ ~(x IN FDOM refs) ==> adjust_bv ((x =+ y) b) v = adjust_bv b v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq THEN
  EXISTS_TAC `refs:(num,(bvl_v)bvl_ref)fmap` THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
  ASM_MESON_TAC[]);;

let B2BP2AUX_MAP_adjust_update = prove
 (`!refs (b:num->num) x y vs.
     ALL (bv_ok refs) vs /\ ~(x IN FDOM refs)
     ==> MAP (adjust_bv ((x =+ y) b)) vs = MAP (adjust_bv b) vs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
  EXISTS_TAC `refs:(num,(bvl_v)bvl_ref)fmap` THEN ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
  ASM_MESON_TAC[]);;

let B2BP2AUX_bvl_eval_facts_Rval = prove
 (`!xs env (s:(num#C,FFI)bvl_state) vs s5.
     bvl_evaluate (xs,env,s) = (Rval vs,s5) /\
     bvl_to_bviProof_state_ok s /\ ALL (bv_ok (bvl_state_refs s)) env
     ==> bvl_to_bviProof_state_ok s5 /\ ALL (bv_ok (bvl_state_refs s5)) env /\
         FDOM (bvl_state_refs s) SUBSET FDOM (bvl_state_refs s5) /\
         ALL (bv_ok (bvl_state_refs s5)) vs`,
  MESON_TAC[B2BP2AUX_bvl_eval_facts]);;

let B2BP2AUX_ALL_bv_ok_SUBSET = prove
 (`!refs refs2 (vs:bvl_v list).
     ALL (bv_ok refs) vs /\ FDOM refs SUBSET FDOM refs2 ==> ALL (bv_ok refs2) vs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[bv_ok_SUBSET_IMP]);;
(* HOL4 line 3521: Resume compile_exps_correct[NIL] *)
let B2BP2AUX_cec_NIL = prove
 (`!env (s:(num#C,FFI)bvl_state). B2BP2AUX_cec ([],env,s)`,
  REWRITE_TAC[B2BP2AUX_cec_def; bvl_evaluate_def; bvl_to_bvi_compile_exps_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `b1:num->num`; `0`] THEN
  ASM_REWRITE_TAC[inc_clock_ZERO; bvi_evaluate_def; map_result_def; MAP]);;

(* HOL4 line 3587: Resume compile_exps_correct[Var] *)
let B2BP2AUX_cec_Var = prove
 (`!n env (s:(num#C,FFI)bvl_state). B2BP2AUX_cec ([bvl_Var n],env,s)`,
  REWRITE_TAC[B2BP2AUX_cec_def; bvl_evaluate_def; bvl_to_bvi_compile_exps_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `b1:num->num`; `0`] THEN
  ASM_REWRITE_TAC[inc_clock_ZERO; bvi_evaluate_def; map_result_def; MAP; LENGTH_MAP] THEN
  ASM_SIMP_TAC[EL_MAP]);;
(* HOL4 line 3529: Resume compile_exps_correct[CONS] *)
let B2BP2AUX_cec_CONS = prove
 (`!x y xs env (s:(num#C,FFI)bvl_state).
     (!v3 s1 v1. bvl_evaluate ([x],env,s) = (v3,s1) /\ v3 = Rval v1
                 ==> B2BP2AUX_cec (CONS y xs,env,s1)) /\
     B2BP2AUX_cec ([x],env,s)
     ==> B2BP2AUX_cec (CONS x (CONS y xs),env,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[handle_ok_def] THEN
  B2BP2AUX_PAIR_TAC `bvl_evaluate ([x],env,s:(num#C,FFI)bvl_state)` "res5" "s5" THEN
  B2BP2AUX_RESULT_TAC `res5:(bvl_v list,bvl_v)result` "v1" "e" THEN CASE_REWRITE_TAC[] THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`Rval v1:(bvl_v list,bvl_v)result`; `s5:(num#C,FFI)bvl_state`;
                                 `v1:bvl_v list`]) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   B2BP2AUX_PAIR_TAC `bvl_evaluate (CONS y xs,env,s5:(num#C,FFI)bvl_state)` "res6" "s6" THEN
   REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend]) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND) THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`[x:bvl_exp]`; `env:bvl_v list`; `s:(num#C,FFI)bvl_state`;
                  `Rval v1:(bvl_v list,bvl_v)result`; `s5:(num#C,FFI)bvl_state`]
                 B2BP2AUX_bvl_eval_facts) THEN
   ASM_REWRITE_TAC[injectivity "result"; distinctness "result"] THEN STRIP_TAC THEN
   B2BP2AUX_IH_TAC `[x:bvl_exp]` B2BP2AUX_PRV_TAC THEN REWRITE_TAC[map_result_def] THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
     (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `~(res6 = Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
     FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN STRIP_TAC THEN RVEQ_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
     ALL_TAC] THEN
   MP_TAC(ISPECL [`c1:bvi_exp list`; `MAP (adjust_bv b2) env`; `ck1:num`; `t1:(C,FFI)bvi_state`;
      `Rval (MAP (adjust_bv b2) v1):(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`;
      `append (aux2:(num#num#bvi_exp)app_list)`] B2BP2AUX_bvi_eval_mono) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   B2BP2AUX_IH_TAC `CONS (y:bvl_exp) xs` B2BP2AUX_PRV_TAC THEN
   DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `b3:num->num`
     (X_CHOOSE_THEN `ck2:num` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `b3:num->num`; `ck2 + ck1:num`] THEN
   MP_TAC(ISPECL [`c1:bvi_exp list`; `MAP (adjust_bv b2) env`;
      `bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)`;
      `Rval (MAP (adjust_bv b2) v1):(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`]
      bvi_evaluate_add_clock) THEN
   ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN
   ASM_REWRITE_TAC[inc_clock_ADD] THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC[bvi_evaluate_APPEND] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN
   B2BP2AUX_RESULT_TAC `res6:(bvl_v list,bvl_v)result` "vs" "e6" THEN
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
   CASE_REWRITE_TAC[map_result_def] THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   TRY(MATCH_MP_TAC B2BP2AUX_agree_trans THEN
     EXISTS_TAC `b2:num->num` THEN EXISTS_TAC `FDOM (bvl_state_refs (s5:(num#C,FFI)bvl_state))` THEN
     ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_evaluate_SING) THEN RVEQ_TAC THEN
   REWRITE_TAC[MAP; HD; APPEND; CONS_11; injectivity "result"] THEN
   MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq THEN
   EXISTS_TAC `bvl_state_refs (s5:(num#C,FFI)bvl_state)` THEN
   ASM_MESON_TAC[ALL];
   REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend]) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND) THEN STRIP_TAC THEN
   B2BP2AUX_IH_TAC `[x:bvl_exp]` B2BP2AUX_PRV_TAC THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
     (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
   ONCE_REWRITE_TAC[bvi_evaluate_APPEND] THEN ASM_REWRITE_TAC[map_result_def] THEN
   CASE_REWRITE_TAC[]]);;

(* HOL4 line 3787: Resume compile_exps_correct[Raise] *)
let B2BP2AUX_cec_Raise = prove
 (`!x1 env (s:(num#C,FFI)bvl_state).
     B2BP2AUX_cec ([x1],env,s) ==> B2BP2AUX_cec ([bvl_Raise x1],env,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[handle_ok_def] THEN
  B2BP2AUX_PAIR_TAC `bvl_evaluate ([x1],env,s:(num#C,FFI)bvl_state)` "res5" "s5" THEN
  REPEAT PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_to_bvi_compile_exps_SING) THEN
  B2BP2AUX_RESULT_TAC `res5:(bvl_v list,bvl_v)result` "v1" "e" THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  B2BP2AUX_IH_TAC `[x1:bvl_exp]` B2BP2AUX_PRV_TAC THEN REWRITE_TAC[map_result_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[map_result_def] THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_evaluate_SING) THEN RVEQ_TAC THEN
      REWRITE_TAC[MAP; HD; map_error_result_def]));;

(* state_rel is preserved by setting both clocks to the same value *)
let B2BP2AUX_state_rel_clock = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) k.
     bvl_to_bviProof_state_rel b s t
     ==> bvl_to_bviProof_state_rel b (bvl_state_clock_fupd (K k) s)
           (bvi_state_clock_fupd (K k) t)`,
  REWRITE_TAC[bvl_to_bviProof_state_rel_def; bvl_state_INFO.ri_accfupds;
              bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REFL_TAC);;

let B2BP2AUX_state_rel_dec_clock = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) k.
     bvl_to_bviProof_state_rel b s t
     ==> bvl_to_bviProof_state_rel b (bvl_dec_clock k s) (bvi_dec_clock k t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_dec_clock_def; bvi_dec_clock_def] THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP (MESON[] `p = q ==> p - k = q - k`)
    (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (REWRITE_RULE[bvl_to_bviProof_state_rel_def] th)))))))) THEN
  MATCH_MP_TAC B2BP2AUX_state_rel_clock THEN ASM_REWRITE_TAC[]);;

let B2BP2AUX_state_rel_clock_eq = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state).
     bvl_to_bviProof_state_rel b s t ==> bvl_state_clock s = bvi_state_clock t`,
  SIMP_TAC[bvl_to_bviProof_state_rel_def]);;

(* HOL4 line 4028: Resume compile_exps_correct[Tick] *)
let B2BP2AUX_cec_Tick = prove
 (`!x env (s:(num#C,FFI)bvl_state).
     (~(bvl_state_clock s = 0) ==> B2BP2AUX_cec ([x],env,bvl_dec_clock 1 s))
     ==> B2BP2AUX_cec ([bvl_Tick x],env,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[handle_ok_def] THEN
  REPEAT PAIRARG_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_to_bvi_compile_exps_SING) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_clock_eq) THENL
   [MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `b1:num->num`; `0`] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[inc_clock_ZERO; map_result_def; map_error_result_def; HD] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `1` o MATCH_MP B2BP2AUX_state_rel_dec_clock) THEN
  MP_TAC(ISPEC `s:(num#C,FFI)bvl_state` (SPEC `1` evaluate_ok_lemma)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvl_to_bviProof_state_ok (bvl_dec_clock 1 (s:(num#C,FFI)bvl_state)) /\
                ALL (bv_ok (bvl_state_refs (bvl_dec_clock 1 s))) env /\
                aux_code_installed (append aux) (bvi_state_code (bvi_dec_clock 1 (t1:(C,FFI)bvi_state))) /\
                IS_SOME (bvi_state_global (bvi_dec_clock 1 t1))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bvi_dec_clock_code; dec_clock_global]; ALL_TAC] THEN
  B2BP2AUX_IH_TAC `[x:bvl_exp]` B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  SUBGOAL_THEN `~(bvi_state_clock (bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[bvi_inc_clock_clock] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[HD] THEN
  SUBGOAL_THEN `~(bvi_state_clock (t1:(C,FFI)bvi_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[dec_clock_inv_clock1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_dec_clock_refs]) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 3597: Resume compile_exps_correct[If] *)
let B2BP2AUX_IF_BRANCH_TAC (xb:term) (dv:term) : tactic =
  B2BP2AUX_IH_TAC xb B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `b3:num->num`
    (X_CHOOSE_THEN `ck2:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `b3:num->num`; `ck2 + ck1:num`] THEN
  MP_TAC(ISPECL [`[y'':bvi_exp]`; `MAP (adjust_bv b2) env`;
     `bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)`;
     mk_comb(`Rval:bvl_v list->(bvl_v list,exn_or_ret)result`,
             mk_list([mk_comb(`adjust_bv b2`,dv)],`:bvl_v`)); `t2:(C,FFI)bvi_state`]
     bvi_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN
  ASM_REWRITE_TAC[inc_clock_ADD] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[HD; adjust_bv_Boolv; bvl_Boolv_11] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[HD; adjust_bv_Boolv; bvl_Boolv_11] THEN
  MATCH_MP_TAC B2BP2AUX_agree_trans THEN
  EXISTS_TAC `b2:num->num` THEN EXISTS_TAC `FDOM (bvl_state_refs (s5:(num#C,FFI)bvl_state))` THEN
  ASM_REWRITE_TAC[];;

let B2BP2AUX_cec_If = prove
 (`!x1 x2 x3 env (s:(num#C,FFI)bvl_state).
     (!v2 s1 vs.
        bvl_evaluate ([x1],env,s) = (v2,s1) /\ v2 = Rval vs /\
        ~(bvl_Boolv T = HD vs) /\ bvl_Boolv F = HD vs
        ==> B2BP2AUX_cec ([x3],env,s1)) /\
     (!v2 s1 vs.
        bvl_evaluate ([x1],env,s) = (v2,s1) /\ v2 = Rval vs /\ bvl_Boolv T = HD vs
        ==> B2BP2AUX_cec ([x2],env,s1)) /\
     B2BP2AUX_cec ([x1],env,s)
     ==> B2BP2AUX_cec ([bvl_If x1 x2 x3],env,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[handle_ok_def] THEN
  B2BP2AUX_PAIR_TAC `bvl_evaluate ([x1],env,s:(num#C,FFI)bvl_state)` "res5" "s5" THEN
  REPEAT PAIRARG_TAC THEN B2BP2AUX_SING_TAC THEN
  B2BP2AUX_RESULT_TAC `res5:(bvl_v list,bvl_v)result` "v1" "e" THEN CASE_REWRITE_TAC[] THENL
  [ALL_TAC;
   ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend]) THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND) THEN STRIP_TAC) THEN
   B2BP2AUX_IH_TAC `[x1:bvl_exp]` B2BP2AUX_PRV_TAC THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
     (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
   ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[HD; map_result_def] THEN
   CASE_REWRITE_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_evaluate_SING) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`Rval [d1]:(bvl_v list,bvl_v)result`;
                                       `s5:(num#C,FFI)bvl_state`; `[d1:bvl_v]`])) THEN
  ASM_REWRITE_TAC[HD] THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`[x1:bvl_exp]`; `env:bvl_v list`; `s:(num#C,FFI)bvl_state`;
                 `[d1]:bvl_v list`; `s5:(num#C,FFI)bvl_state`]
                B2BP2AUX_bvl_eval_facts_Rval) THEN
  ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND) THEN STRIP_TAC) THEN
  B2BP2AUX_IH_TAC `[x1:bvl_exp]` B2BP2AUX_PRV_TAC THEN REWRITE_TAC[map_result_def; MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`[y'':bvi_exp]`; `MAP (adjust_bv b2) env`; `ck1:num`; `t1:(C,FFI)bvi_state`;
     `Rval [adjust_bv b2 d1]:(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`;
     `append (aux2:(num#num#bvi_exp)app_list)`] B2BP2AUX_bvi_eval_mono) THEN
  MP_TAC(ISPECL [`[y'':bvi_exp]`; `MAP (adjust_bv b2) env`; `ck1:num`; `t1:(C,FFI)bvi_state`;
     `Rval [adjust_bv b2 d1]:(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`;
     `append (aux3:(num#num#bvi_exp)app_list)`] B2BP2AUX_bvi_eval_mono) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `bvl_Boolv T = d1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    B2BP2AUX_IF_BRANCH_TAC `[x2:bvl_exp]` `bvl_Boolv T`;
    ALL_TAC] THEN
  ASM_CASES_TAC `bvl_Boolv F = d1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN RULE_ASSUM_TAC(REWRITE_RULE[bvl_Boolv_11]) THEN
    B2BP2AUX_IF_BRANCH_TAC `[x3:bvl_exp]` `bvl_Boolv F`;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC);;

(* the result of a bvi Call without handler on a mapped bvl result *)
let B2BP2AUX_CALL_RESULT_TAC (r:term) : tactic =
  B2BP2AUX_RESULT_TAC r "v" "e" THEN CASE_REWRITE_TAC[map_result_def] THEN
  B2BP2AUX_ERROR_TAC `e:(bvl_v)error_result` "v" "a" THEN
  CASE_REWRITE_TAC[map_error_result_def];;

let B2BP2AUX_not_type_error_map = prove
 (`!(f:A->B) (g:C->exn_or_ret) (r:(A,C)result).
     ~(r = Rerr (Rabort Rtype_error)) ==> ~(map_result f g r = Rerr (Rabort Rtype_error))`,
  REPEAT GEN_TAC THEN B2BP2AUX_RESULT_TAC `r:(A,C)result` "v" "e" THEN
  REWRITE_TAC[map_result_def; distinctness "result"; injectivity "result"] THEN
  B2BP2AUX_ERROR_TAC `e:(C)error_result` "v" "a" THEN
  REWRITE_TAC[map_error_result_def; distinctness "error_result"; injectivity "error_result"]);;

(* HOL4 line 3667: Resume compile_exps_correct[Let], the case of an empty  *)
(* list of bindings (x2 is then a Let of variables, a call to an aux       *)
(* function) *)
let B2BP2AUX_cec_Let_NIL = prove
 (`!x2 env (s:(num#C,FFI)bvl_state).
     (!ys env. list_size bvl_exp_size ys <= bvl_exp_size x2 ==> B2BP2AUX_cec (ys,env,s))
     ==> B2BP2AUX_cec ([bvl_Let [] x2],env,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[handle_ok_def; LENGTH; NULL] THEN
  ASM_CASES_TAC `let_ok x2` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `let_ok x2`)) THEN
  CASES_ON `x2:bvl_exp` THEN REWRITE_TAC[let_ok_def] THEN STRIP_TAC THEN
  REWRITE_TAC[destLet_def] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a0:bvl_exp list`; `n:num`] compile_exps_Var_list) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `aux1:(num#num#bvi_exp)app_list` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT PAIRARG_TAC THEN B2BP2AUX_SING_TAC THEN
  REWRITE_TAC[injectivity "bvl_exp";
              MESON[] `(!ys y. (a:bvl_exp list) = ys /\ (b:bvl_exp) = y ==> P y) <=> P b`] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[bvl_evaluate_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; LET_DEF; LET_END_DEF; HD] THEN
  MP_TAC(ISPECL [`a0:bvl_exp list`; `env:bvl_v list`; `s:(num#C,FFI)bvl_state`]
    evaluate_Var_list) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend; compile_aux_def; append_thm; APPEND]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "aux_code_installed"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[APPEND; aux_code_installed_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvl_evaluate ([a1],vs,s:(num#C,FFI)bvl_state) = (res,s2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      can (term_match [] `bvl_evaluate ([a1],APPEND vs env,s:(num#C,FFI)bvl_state)`)
          (lhs (concl th)))) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC bEval_bVarBound THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (bv_ok (bvl_state_refs (s:(num#C,FFI)bvl_state))) vs` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a0:bvl_exp list`; `env:bvl_v list`; `vs:bvl_v list`;
                   `s:(num#C,FFI)bvl_state`; `s:(num#C,FFI)bvl_state`]
                  EVERY_isVar_evaluate_Rval_MEM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `ALL (bv_ok (bvl_state_refs (s:(num#C,FFI)bvl_state))) env` THEN
    UNDISCH_TAC `ALL (\x. MEM x env) (vs:bvl_v list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`[a1:bvl_exp]`; `vs:bvl_v list`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[type_size_def "bvl_exp"] THEN REWRITE_TAC(size_aux_eqs "bvl_exp") THEN
    REWRITE_TAC[list_size] THEN ARITH_TAC;
    DISCH_TAC] THEN
  B2BP2AUX_IH_TAC `[a1:bvl_exp]` B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1 + 1:num`] THEN
  SUBGOAL_THEN `MAP (adjust_bv b1) env = MAP (adjust_bv b2) env` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
    EXISTS_TAC `bvl_state_refs (s:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[IS_NONE_DEF] THEN
  MP_TAC(ISPECL [`a0:bvl_exp list`; `env:bvl_v list`; `vs:bvl_v list`; `b2:num->num`;
                 `bvi_inc_clock (ck1 + 1) (t1:(C,FFI)bvi_state)`] evaluate_MAP_Var) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_find_code_def; bvi_inc_clock_code; LENGTH_MAP] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_inc_clock_clock; ARITH_RULE `~(a + c + 1 < 0 + 1)`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SIMP_TAC[bvi_dec_clock_1_inc_clock; ARITH_RULE `~(c + 1 = 0)`; ADD_SUB] THEN
  MP_TAC(ISPECL [`y:bvi_exp`; `MAP (adjust_bv b2) vs`; `bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)`;
     `map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) (res:(bvl_v list,bvl_v)result)`;
     `t2:(C,FFI)bvi_state`] bvi_letProof_evaluate_compile_exp) THEN
  ASM_SIMP_TAC[B2BP2AUX_not_type_error_map] THEN DISCH_THEN SUBST1_TAC THEN
  B2BP2AUX_CALL_RESULT_TAC `res:(bvl_v list,bvl_v)result`);;

(* HOL4 line 3667: Resume compile_exps_correct[Let], a non-empty list of  *)
(* bindings *)
let B2BP2AUX_cec_Let_CONS = prove
 (`!xs x2 env (s:(num#C,FFI)bvl_state).
     ~(xs = []) /\
     (!v2 s1 vs. bvl_evaluate (xs,env,s) = (v2,s1) /\ v2 = Rval vs
                 ==> B2BP2AUX_cec ([x2],APPEND vs env,s1)) /\
     B2BP2AUX_cec (xs,env,s)
     ==> B2BP2AUX_cec ([bvl_Let xs x2],env,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  ASM_REWRITE_TAC[handle_ok_def; LENGTH_EQ_NIL; NULL_EQ] THEN
  B2BP2AUX_PAIR_TAC `bvl_evaluate (xs,env,s:(num#C,FFI)bvl_state)` "res5" "s5" THEN
  REPEAT PAIRARG_TAC THEN B2BP2AUX_SING_TAC THEN
  B2BP2AUX_RESULT_TAC `res5:(bvl_v list,bvl_v)result` "vs" "e" THEN CASE_REWRITE_TAC[] THENL
  [ALL_TAC;
   ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend]) THEN
   REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND) THEN STRIP_TAC) THEN
   B2BP2AUX_IH_TAC `xs:bvl_exp list` B2BP2AUX_PRV_TAC THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
     (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
   ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[HD; map_result_def] THEN
   CASE_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Rval vs:(bvl_v list,bvl_v)result`;
                                `s5:(num#C,FFI)bvl_state`; `vs:bvl_v list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`xs:bvl_exp list`; `env:bvl_v list`; `s:(num#C,FFI)bvl_state`;
                 `vs:bvl_v list`; `s5:(num#C,FFI)bvl_state`] B2BP2AUX_bvl_eval_facts_Rval) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL (bv_ok (bvl_state_refs (s5:(num#C,FFI)bvl_state))) (APPEND vs env)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[ALL_APPEND]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND) THEN STRIP_TAC) THEN
  B2BP2AUX_IH_TAC `xs:bvl_exp list` B2BP2AUX_PRV_TAC THEN REWRITE_TAC[map_result_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c1:bvi_exp list`; `MAP (adjust_bv b2) env`; `ck1:num`; `t1:(C,FFI)bvi_state`;
     `Rval (MAP (adjust_bv b2) vs):(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`;
     `append (aux2:(num#num#bvi_exp)app_list)`] B2BP2AUX_bvi_eval_mono) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  B2BP2AUX_IH_TAC `[x2:bvl_exp]` B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `b3:num->num`
    (X_CHOOSE_THEN `ck2:num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `b3:num->num`; `ck2 + ck1:num`] THEN
  SUBGOAL_THEN `MAP (adjust_bv b2) env = MAP (adjust_bv b3) env /\
                MAP (adjust_bv b2) vs = MAP (adjust_bv b3) vs` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
    EXISTS_TAC `bvl_state_refs (s5:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:bvi_exp list`; `MAP (adjust_bv b2) env`;
     `bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)`;
     `Rval (MAP (adjust_bv b2) vs):(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`]
     bvi_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN
  ASM_REWRITE_TAC[inc_clock_ADD] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP_APPEND]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC B2BP2AUX_agree_trans THEN
  EXISTS_TAC `b2:num->num` THEN EXISTS_TAC `FDOM (bvl_state_refs (s5:(num#C,FFI)bvl_state))` THEN
  ASM_REWRITE_TAC[]);;

let B2BP2AUX_cec_Let = prove
 (`!xs x2 env (s:(num#C,FFI)bvl_state).
     (!ys v2 s1 vs.
        list_size bvl_exp_size ys <= bvl_exp_size x2 /\ bvl_evaluate (xs,env,s) = (v2,s1)
        ==> B2BP2AUX_cec (ys,vs,s1)) /\
     (!ys env. list_size bvl_exp_size ys <= bvl_exp_size x2 ==> B2BP2AUX_cec (ys,env,s)) /\
     (!v2 s1 vs.
        bvl_evaluate (xs,env,s) = (v2,s1) /\ v2 = Rval vs
        ==> B2BP2AUX_cec ([x2],APPEND vs env,s1)) /\
     B2BP2AUX_cec (xs,env,s)
     ==> B2BP2AUX_cec ([bvl_Let xs x2],env,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `xs:bvl_exp list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC B2BP2AUX_cec_Let_NIL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC B2BP2AUX_cec_Let_CONS THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 3810: Resume compile_exps_correct[Handle] *)
(* the call of the aux function: the variables, the code lookup and the clock *)
let B2BP2AUX_HANDLE_CALL_TAC (ck:term) (bb:term) : tactic =
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[IS_NONE_DEF; IS_SOME_DEF] THEN
  MP_TAC(ISPECL [`a0:bvl_exp list`; `env:bvl_v list`; `vs:bvl_v list`; bb;
                 vsubst [ck,`cc0:num`] `bvi_inc_clock cc0 (t1:(C,FFI)bvi_state)`]
                evaluate_MAP_Var) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_find_code_def; bvi_inc_clock_code; LENGTH_MAP] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_inc_clock_clock; ARITH_RULE `~(a + c + 1 < 0 + 1)`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SIMP_TAC[bvi_dec_clock_1_inc_clock; ARITH_RULE `~(c + 1 = 0)`; ADD_SUB];;

let B2BP2AUX_cec_Handle = prove
 (`!x1 x2 env (s1:(num#C,FFI)bvl_state).
     (!v3 s v8 v.
        bvl_evaluate ([x1],env,s1) = (v3,s) /\ v3 = Rerr v8 /\ v8 = Rraise v
        ==> B2BP2AUX_cec ([x2],CONS v env,s)) /\
     (!xs env. list_size bvl_exp_size xs <= bvl_exp_size x1 ==> B2BP2AUX_cec (xs,env,s1))
     ==> B2BP2AUX_cec ([bvl_Handle x1 x2],env,s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN REWRITE_TAC[handle_ok_def] THEN
  CASES_ON `x1:bvl_exp` THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[destLet_def] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ALL isVar (a0:bvl_exp list)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a0:bvl_exp list`; `n:num`] compile_exps_Var_list) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `aux1:(num#num#bvi_exp)app_list` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REPEAT PAIRARG_TAC THEN B2BP2AUX_SING_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; HD] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[bvl_evaluate_def] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a0:bvl_exp list`; `env:bvl_v list`; `s1:(num#C,FFI)bvl_state`]
    evaluate_Var_list) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[append_SmartAppend; compile_aux_def; append_thm; APPEND]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "aux_code_installed"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[APPEND; aux_code_installed_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP aux_code_installed_APPEND) THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvl_evaluate ([a1],APPEND vs env,s1:(num#C,FFI)bvl_state) =
                bvl_evaluate ([a1],vs,s1)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC bEval_bVarBound THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (bv_ok (bvl_state_refs (s1:(num#C,FFI)bvl_state))) vs` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a0:bvl_exp list`; `env:bvl_v list`; `vs:bvl_v list`;
                   `s1:(num#C,FFI)bvl_state`; `s1:(num#C,FFI)bvl_state`]
                  EVERY_isVar_evaluate_Rval_MEM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `ALL (bv_ok (bvl_state_refs (s1:(num#C,FFI)bvl_state))) env` THEN
    UNDISCH_TAC `ALL (\x. MEM x env) (vs:bvl_v list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`[a1:bvl_exp]`; `vs:bvl_v list`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[type_size_def "bvl_exp"] THEN REWRITE_TAC(size_aux_eqs "bvl_exp") THEN
    REWRITE_TAC[list_size] THEN ARITH_TAC;
    DISCH_TAC] THEN
  B2BP2AUX_PAIR_TAC `bvl_evaluate ([a1],vs,s1:(num#C,FFI)bvl_state)` "r1" "s5" THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  B2BP2AUX_IH_TAC `[a1:bvl_exp]` B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `MAP (adjust_bv b1) env = MAP (adjust_bv b2) env` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
    EXISTS_TAC `bvl_state_refs (s1:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y':bvi_exp`; `MAP (adjust_bv b2) vs`; `bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)`;
     `map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) (r1:(bvl_v list,bvl_v)result)`;
     `t2:(C,FFI)bvi_state`] bvi_letProof_evaluate_compile_exp) THEN
  ASM_SIMP_TAC[B2BP2AUX_not_type_error_map] THEN DISCH_TAC THEN
  B2BP2AUX_RESULT_TAC `r1:(bvl_v list,bvl_v)result` "v1" "e" THENL
  [RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1 + 1:num`] THEN
   ASM_REWRITE_TAC[] THEN B2BP2AUX_HANDLE_CALL_TAC `ck1 + 1` `b2:num->num` THEN
   ASM_REWRITE_TAC[map_result_def] THEN CASE_REWRITE_TAC[];
   ALL_TAC] THEN
  B2BP2AUX_ERROR_TAC `e:(bvl_v)error_result` "v" "a" THENL
  [ALL_TAC;
   RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1 + 1:num`] THEN
   ASM_REWRITE_TAC[] THEN B2BP2AUX_HANDLE_CALL_TAC `ck1 + 1` `b2:num->num` THEN
   ASM_REWRITE_TAC[map_result_def; map_error_result_def] THEN CASE_REWRITE_TAC[]] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  SUBGOAL_THEN `bvl_evaluate ([bvl_Let a0 a1],env,s1:(num#C,FFI)bvl_state) =
                (Rerr (Rraise v),s5)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bvl_evaluate ([a1],APPEND vs env,s1:(num#C,FFI)bvl_state) =
                  bvl_evaluate ([a1],vs,s1)` SUBST1_TAC THENL
     [MATCH_MP_TAC bEval_bVarBound THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Rerr (Rraise v):(bvl_v list,bvl_v)result`;
     `s5:(num#C,FFI)bvl_state`; `Rraise v:(bvl_v)error_result`; `v:bvl_v`] o
     check (fun th -> try let vs,_ = strip_forall (concl th) in length vs = 4
                      with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`[a1:bvl_exp]`; `vs:bvl_v list`; `s1:(num#C,FFI)bvl_state`;
                 `Rerr (Rraise v):(bvl_v list,bvl_v)result`; `s5:(num#C,FFI)bvl_state`]
                B2BP2AUX_bvl_eval_facts) THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; injectivity "error_result"] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL (bv_ok (bvl_state_refs (s5:(num#C,FFI)bvl_state))) (CONS v env)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ALL] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC B2BP2AUX_ALL_bv_ok_SUBSET THEN
    EXISTS_TAC `bvl_state_refs (s1:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`[y':bvi_exp]`; `MAP (adjust_bv b2) vs`; `ck1:num`; `t1:(C,FFI)bvi_state`;
     `map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) (Rerr (Rraise v)):
        (bvl_v list,exn_or_ret)result`;
     `t2:(C,FFI)bvi_state`;
     `append (aux3:(num#num#bvi_exp)app_list)`] B2BP2AUX_bvi_eval_mono) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  B2BP2AUX_IH_TAC `[x2:bvl_exp]` B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `b3:num->num`
    (X_CHOOSE_THEN `ck2:num` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; CONS_11]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
     can (term_match [] `adjust_bv b2 v = adjust_bv b3 v`) (lhand (concl th)))) THEN
  SUBGOAL_THEN `MAP (adjust_bv b2) vs = MAP (adjust_bv b3) vs` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
    EXISTS_TAC `bvl_state_refs (s1:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `b3:num->num`; `(ck2 + ck1) + 1:num`] THEN
  B2BP2AUX_HANDLE_CALL_TAC `(ck2 + ck1) + 1` `b3:num->num` THEN
  REWRITE_TAC[GSYM inc_clock_ADD] THEN
  MP_TAC(ISPECL [`[bvi_let_compile_exp y']`; `MAP (adjust_bv b2) vs`;
     `bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)`;
     `map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) (Rerr (Rraise v)):
        (bvl_v list,exn_or_ret)result`;
     `t2:(C,FFI)bvi_state`] bvi_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[map_result_def; map_error_result_def; distinctness "result";
                  injectivity "result"; distinctness "error_result"] THEN
  DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `MAP (adjust_bv b2) vs = MAP (adjust_bv b3) vs`)) THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [B2BP2AUX_RESULT_TAC `res:(bvl_v list,bvl_v)result` "w" "e2" THEN
    CASE_REWRITE_TAC[map_result_def] THEN
    B2BP2AUX_ERROR_TAC `e2:(bvl_v)error_result` "w" "a" THEN
    CASE_REWRITE_TAC[map_error_result_def];
    ASM_MESON_TAC[SUBSET]]);;

(* HOL4 line 3967: Resume compile_exps_correct[Force] *)
let B2BP2AUX_dest_thunk_IsThunk = prove
 (`!v refs m f.
     bvl_dest_thunk v refs = bvl_IsThunk m f
     ==> ?ptr. v = bvl_RefPtr F ptr /\ FLOOKUP refs ptr = SOME (bvl_Thunk m f)`,
  GEN_TAC THEN CASES_ON `v:bvl_v` THEN REWRITE_TAC[bvl_dest_thunk_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  CASES_ON `FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) a1` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a0':thunk_mode` THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `a1:num` THEN ASM_REWRITE_TAC[]);;

let B2BP2AUX_dest_thunk_adjust = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) v m f.
     bvl_to_bviProof_state_rel b s t /\
     bvl_dest_thunk v (bvl_state_refs s) = bvl_IsThunk m f
     ==> bvi_dest_thunk (adjust_bv b v) (bvi_state_refs t) = bvi_IsThunk m (adjust_bv b f)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_dest_thunk_IsThunk) THEN
  RVEQ_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_FLOOKUP_Thunk o
    CONJ (ASSUME `bvl_to_bviProof_state_rel b s (t:(C,FFI)bvi_state)`)) THEN
  ASM_REWRITE_TAC[adjust_bv_def; bvi_dest_thunk_def] THEN
  CASES_ON `m:thunk_mode` THEN CASE_REWRITE_TAC[]);;

let B2BP2AUX_find_code_SOME = prove
 (`!p (args:bvl_v list) (code:(num#A)spt) args' exp.
     bvl_find_code (SOME p) args code = SOME (args',exp) <=>
     lookup p code = SOME (LENGTH args,exp) /\ args' = args`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_find_code_def] THEN
  CASES_ON `lookup p (code:(num#A)spt)` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `a:num#A` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:A` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let B2BP2AUX_state_rel_lookup = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) name arity exp.
     bvl_to_bviProof_state_rel b s t /\ lookup name (bvl_state_code s) = SOME (arity,exp)
     ==> ?n c1 aux1 n1.
           bvl_to_bvi_compile_exps n [exp] = (c1,aux1,n1) /\
           lookup (bvl_num_stubs + bvl_to_bvi_namespaces * name) (bvi_state_code t) =
             SOME (arity,bvi_let_compile_exp (HD c1)) /\
           aux_code_installed (append aux1) (bvi_state_code t) /\
           handle_ok [exp]`,
  REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`name:num`; `arity:num`; `exp:bvl_exp`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  REPEAT PAIRARG_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c1:bvi_exp list`; `aux1:(num#num#bvi_exp)app_list`; `n1:num`] THEN
  ASM_REWRITE_TAC[]);;

let B2BP2AUX_cec_Force = prove
 (`!force_loc n env (s:(num#C,FFI)bvl_state).
     (!thunk_v m1 v v' args exp.
        n < LENGTH env /\ thunk_v = EL n env /\
        bvl_dest_thunk thunk_v (bvl_state_refs s) = bvl_IsThunk m1 v /\
        m1 = NotEvaluated /\
        ~(bvl_state_clock s = 0) /\
        bvl_find_code (SOME force_loc) [thunk_v; v] (bvl_state_code s) = SOME v' /\
        v' = (args,exp) /\ ~(bvl_state_clock s = 0)
        ==> B2BP2AUX_cec ([exp],args,bvl_dec_clock 1 s))
     ==> B2BP2AUX_cec ([bvl_Force force_loc n],env,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  ASM_CASES_TAC `n < LENGTH (env:bvl_v list)` THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
   [ALL_TAC; STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_ASSUM CONTR_TAC] THEN
  CASES_ON `bvl_dest_thunk (EL n env) (bvl_state_refs (s:(num#C,FFI)bvl_state))` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  TRY(STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`b1:num->num`; `s:(num#C,FFI)bvl_state`; `t1:(C,FFI)bvi_state`; `EL n env:bvl_v`;
                 `a0:thunk_mode`; `a1:bvl_v`] B2BP2AUX_dest_thunk_adjust) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_clock_eq) THEN
  CASES_ON `a0:thunk_mode` THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
    MAP_EVERY EXISTS_TAC [`t1:(C,FFI)bvi_state`; `b1:num->num`; `0`] THEN
    ASM_REWRITE_TAC[inc_clock_ZERO] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[map_result_def; MAP];
    ALL_TAC] THEN
  CASES_ON `bvl_find_code (SOME force_loc) [EL n env; a1]
              (bvl_state_code (s:(num#C,FFI)bvl_state))` THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THENL
  [FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
   ALL_TAC] THEN
  B2BP2AUX_PAIR_TAC `a:bvl_v list#bvl_exp` "args" "exp" THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[PAIR_EQ]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[B2BP2AUX_find_code_SOME] o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvl_find_code"
                     with Failure _ -> false)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`]) THEN
  MP_TAC(ISPECL [`b1:num->num`; `s:(num#C,FFI)bvl_state`; `t1:(C,FFI)bvi_state`; `force_loc:num`;
                 `2`; `exp:bvl_exp`] B2BP2AUX_state_rel_lookup) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `c1:bvi_exp list` (X_CHOOSE_THEN
    `aux1:(num#num#bvi_exp)app_list` (X_CHOOSE_THEN `m1:num` STRIP_ASSUME_TAC)))) THEN
  B2BP2AUX_SING_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
  SUBGOAL_THEN `bvl_find_code (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * force_loc))
     [adjust_bv b1 (EL n env); adjust_bv b1 a1] (bvi_state_code (t1:(C,FFI)bvi_state)) =
     SOME ([adjust_bv b1 (EL n env); adjust_bv b1 a1],bvi_let_compile_exp y)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[B2BP2AUX_find_code_SOME; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
  [MAP_EVERY EXISTS_TAC [`bvi_state_clock_fupd (K 0) (t1:(C,FFI)bvi_state)`; `b1:num->num`; `0`] THEN
   ASM_SIMP_TAC[inc_clock_ZERO; B2BP2AUX_state_rel_clock] THEN
   ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
   ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[map_result_def; map_error_result_def] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `bvi_state_clock (t1:(C,FFI)bvi_state) = 0` (fun th -> REWRITE_TAC[th]) THEN
   UNDISCH_TAC `bvl_state_clock (s:(num#C,FFI)bvl_state) = bvi_state_clock (t1:(C,FFI)bvi_state)` THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`EL n env:bvl_v`; `NotEvaluated`; `a1:bvl_v`;
     `[EL n env:bvl_v; a1],(exp:bvl_exp)`; `[EL n env:bvl_v; a1]`; `exp:bvl_exp`]) THEN
  ASM_REWRITE_TAC[B2BP2AUX_find_code_SOME; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `1` o MATCH_MP B2BP2AUX_state_rel_dec_clock) THEN
  MP_TAC(ISPEC `s:(num#C,FFI)bvl_state` (SPEC `1` evaluate_ok_lemma)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvl_to_bviProof_state_ok (bvl_dec_clock 1 (s:(num#C,FFI)bvl_state)) /\
                ALL (bv_ok (bvl_state_refs (bvl_dec_clock 1 s))) [EL n env; a1] /\
                aux_code_installed (append aux1)
                  (bvi_state_code (bvi_dec_clock 1 (t1:(C,FFI)bvi_state))) /\
                IS_SOME (bvi_state_global (bvi_dec_clock 1 t1))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bvi_dec_clock_code; dec_clock_global; ALL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ALL (bv_ok (bvl_state_refs (s:(num#C,FFI)bvl_state))) env` THEN
      REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_dest_thunk_IsThunk o
        check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvl_dest_thunk"
                         with Failure _ -> false)) THEN
      UNDISCH_TAC `bvl_to_bviProof_state_ok (s:(num#C,FFI)bvl_state)` THEN
      REWRITE_TAC[bvl_to_bviProof_state_ok_def] THEN
      DISCH_THEN(MP_TAC o SPEC `ptr:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[]];
    ALL_TAC] THEN
  B2BP2AUX_IH_TAC `[exp:bvl_exp]` B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; CONS_11; bvl_dec_clock_refs]) THEN
  MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
  SUBGOAL_THEN `MAP (adjust_bv b1) env = MAP (adjust_bv b2) env` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
    EXISTS_TAC `bvl_state_refs (s:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; LET_DEF; LET_END_DEF; bvi_inc_clock_refs; bvi_inc_clock_code] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (ASSUME_TAC o SYM) o check (fun th -> is_conj (concl th) &&
     can (term_match [] `adjust_bv b1 (EL n env) = adjust_bv b2 (EL n env)`) (lhand (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(bvi_state_clock (t1:(C,FFI)bvi_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `bvl_state_clock (s:(num#C,FFI)bvl_state) = bvi_state_clock (t1:(C,FFI)bvi_state)` THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[bvi_inc_clock_clock; ARITH_RULE `a + c = 0 <=> a = 0 /\ c = 0`] THEN
  ASM_SIMP_TAC[dec_clock_inv_clock1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `adjust_bv b2 (EL n env) = adjust_bv b1 (EL n env)`;
                              ASSUME `adjust_bv b2 a1 = adjust_bv b1 a1`]) THEN
  MP_TAC(ISPECL [`y:bvi_exp`; `[adjust_bv b1 (EL n env); adjust_bv b1 a1]`;
     `bvi_inc_clock ck1 (bvi_dec_clock 1 (t1:(C,FFI)bvi_state))`;
     `map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) (res:(bvl_v list,bvl_v)result)`;
     `t2:(C,FFI)bvi_state`] bvi_letProof_evaluate_compile_exp) THEN
  ASM_SIMP_TAC[B2BP2AUX_not_type_error_map] THEN DISCH_THEN SUBST1_TAC THEN
  B2BP2AUX_CALL_RESULT_TAC `res:(bvl_v list,bvl_v)result`);;

(* HOL4 line 4056: Resume compile_exps_correct[Call] *)
(* the code found by a bvl call and by the compiled bvi call *)
let B2BP2AUX_find_code_adjust = prove
 (CASE_TERM
  `!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) dest vs args exp.
     bvl_to_bviProof_state_rel b s t /\
     bvl_find_code dest vs (bvl_state_code s) = SOME (args,exp)
     ==> ?n c1 aux1 n1.
           bvl_to_bvi_compile_exps n [exp] = (c1,aux1,n1) /\
           bvl_find_code
             (match dest with NONE -> NONE
                            | SOME n -> SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n))
             (MAP (adjust_bv b) vs) (bvi_state_code t) =
             SOME (MAP (adjust_bv b) args,bvi_let_compile_exp (HD c1)) /\
           aux_code_installed (append aux1) (bvi_state_code t) /\
           handle_ok [exp]`,
  REPEAT GEN_TAC THEN CASES_ON `dest:num option` THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[bvl_find_code_def; MAP_EQ_NIL] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT] THEN
    ASM_SIMP_TAC[LAST_MAP] THEN
    CASES_ON `LAST (vs:bvl_v list)` THEN ASM_REWRITE_TAC[adjust_bv_def] THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `lookup a (bvl_state_code (s:(num#C,FFI)bvl_state))` THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    MP_TAC(ISPEC `a':num#bvl_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(ISPECL [`b:num->num`; `s:(num#C,FFI)bvl_state`; `t:(C,FFI)bvi_state`; `a:num`;
                   `ar:num`; `exp:bvl_exp`] B2BP2AUX_state_rel_lookup) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c1:bvi_exp list`; `aux1:(num#num#bvi_exp)app_list`; `n1:num`] THEN
    ASM_REWRITE_TAC[LENGTH_MAP; MAP_FRONT] THEN CASE_REWRITE_TAC[];
    REWRITE_TAC[B2BP2AUX_find_code_SOME; LENGTH_MAP] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(ISPECL [`b:num->num`; `s:(num#C,FFI)bvl_state`; `t:(C,FFI)bvi_state`; `a:num`;
                   `LENGTH (vs:bvl_v list)`; `exp:bvl_exp`] B2BP2AUX_state_rel_lookup) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c1:bvi_exp list`; `aux1:(num#num#bvi_exp)app_list`; `n1:num`] THEN
    ASM_REWRITE_TAC[]]);;

let B2BP2AUX_cec_Call = prove
 (`!ticks dest xs env (s1:(num#C,FFI)bvl_state).
     (!v2 s vs v' args exp.
        bvl_evaluate (xs,env,s1) = (v2,s) /\ v2 = Rval vs /\
        bvl_find_code dest vs (bvl_state_code s) = SOME v' /\ v' = (args,exp) /\
        ~(bvl_state_clock s < ticks + 1)
        ==> B2BP2AUX_cec ([exp],args,bvl_dec_clock (ticks + 1) s)) /\
     B2BP2AUX_cec (xs,env,s1)
     ==> B2BP2AUX_cec ([bvl_Call ticks dest xs],env,s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[handle_ok_def] THEN
  B2BP2AUX_PAIR_TAC `bvl_evaluate (xs,env,s1:(num#C,FFI)bvl_state)` "res5" "s5" THEN
  REPEAT PAIRARG_TAC THEN
  B2BP2AUX_RESULT_TAC `res5:(bvl_v list,bvl_v)result` "vs" "e" THEN CASE_REWRITE_TAC[] THENL
  [ALL_TAC;
   ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   B2BP2AUX_IH_TAC `xs:bvl_exp list` B2BP2AUX_PRV_TAC THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
     (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
   ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[IS_SOME_DEF; map_result_def] THEN
   CASE_REWRITE_TAC[]] THEN
  CASES_ON `bvl_find_code dest vs (bvl_state_code (s5:(num#C,FFI)bvl_state))` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
  [STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
   ALL_TAC] THEN
  B2BP2AUX_PAIR_TAC `a:bvl_v list#bvl_exp` "args" "exp" THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`xs:bvl_exp list`; `env:bvl_v list`; `s1:(num#C,FFI)bvl_state`;
                 `vs:bvl_v list`; `s5:(num#C,FFI)bvl_state`] B2BP2AUX_bvl_eval_facts_Rval) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  B2BP2AUX_IH_TAC `xs:bvl_exp list` B2BP2AUX_PRV_TAC THEN REWRITE_TAC[map_result_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`;
                 `dest:num option`; `vs:bvl_v list`; `args:bvl_v list`; `exp:bvl_exp`]
                B2BP2AUX_find_code_adjust) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `c7:bvi_exp list` (X_CHOOSE_THEN
    `aux7:(num#num#bvi_exp)app_list` (X_CHOOSE_THEN `m7:num` STRIP_ASSUME_TAC)))) THEN
  B2BP2AUX_SING_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_clock_eq o
    check (fun th -> concl th = `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
  [MAP_EVERY EXISTS_TAC [`bvi_state_clock_fupd (K 0) (t2:(C,FFI)bvi_state)`; `b2:num->num`;
                         `ck1:num`] THEN
   ASM_SIMP_TAC[B2BP2AUX_state_rel_clock] THEN
   ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
   CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `bvi_state_clock (t2:(C,FFI)bvi_state) < ticks + 1` (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[map_result_def; map_error_result_def] THEN
   UNDISCH_TAC `bvl_state_clock (s5:(num#C,FFI)bvl_state) = bvi_state_clock (t2:(C,FFI)bvi_state)` THEN
   UNDISCH_TAC `bvl_state_clock (s5:(num#C,FFI)bvl_state) < ticks + 1` THEN ARITH_TAC;
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Rval vs:(bvl_v list,bvl_v)result`; `s5:(num#C,FFI)bvl_state`;
     `vs:bvl_v list`; `(args:bvl_v list),(exp:bvl_exp)`; `args:bvl_v list`; `exp:bvl_exp`] o
     check (fun th -> try let vs,_ = strip_forall (concl th) in length vs = 6
                      with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `ticks + 1` o MATCH_MP B2BP2AUX_state_rel_dec_clock o
    check (fun th -> concl th = `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)`)) THEN
  MP_TAC(ISPEC `s5:(num#C,FFI)bvl_state` (SPEC `ticks + 1` evaluate_ok_lemma)) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:bvi_exp list`; `MAP (adjust_bv b2) env`; `ck1:num`; `t1:(C,FFI)bvi_state`;
     `Rval (MAP (adjust_bv b2) vs):(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`;
     `append (aux:(num#num#bvi_exp)app_list)`] B2BP2AUX_bvi_eval_mono) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bvl_to_bviProof_state_ok (bvl_dec_clock (ticks + 1) (s5:(num#C,FFI)bvl_state)) /\
                ALL (bv_ok (bvl_state_refs (bvl_dec_clock (ticks + 1) s5))) args /\
                aux_code_installed (append aux7)
                  (bvi_state_code (bvi_dec_clock (ticks + 1) (t2:(C,FFI)bvi_state))) /\
                IS_SOME (bvi_state_global (bvi_dec_clock (ticks + 1) t2))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bvi_dec_clock_code; dec_clock_global] THEN
    MP_TAC(ISPECL [`dest:num option`; `vs:bvl_v list`;
                   `bvl_state_code (s5:(num#C,FFI)bvl_state)`; `args:bvl_v list`; `exp:bvl_exp`;
                   `bvl_state_refs (s5:(num#C,FFI)bvl_state)`] find_code_bv_ok) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  B2BP2AUX_IH_TAC `[exp:bvl_exp]` B2BP2AUX_PRV_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` (X_CHOOSE_THEN `b3:num->num`
    (X_CHOOSE_THEN `ck2:num` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_dec_clock_refs]) THEN
  MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `b3:num->num`; `ck2 + ck1:num`] THEN
  SUBGOAL_THEN `MAP (adjust_bv b2) env = MAP (adjust_bv b3) env` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
    EXISTS_TAC `bvl_state_refs (s5:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:bvi_exp list`; `MAP (adjust_bv b2) env`;
     `bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)`;
     `Rval (MAP (adjust_bv b2) vs):(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`]
     bvi_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[distinctness "result"] THEN DISCH_THEN(MP_TAC o SPEC `ck2:num`) THEN
  ASM_REWRITE_TAC[inc_clock_ADD] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvi_inc_clock_code] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(bvi_state_clock (t2:(C,FFI)bvi_state) < ticks + 1)` ASSUME_TAC THENL
   [UNDISCH_TAC `bvl_state_clock (s5:(num#C,FFI)bvl_state) = bvi_state_clock (t2:(C,FFI)bvi_state)` THEN
    UNDISCH_TAC `~(bvl_state_clock (s5:(num#C,FFI)bvl_state) < ticks + 1)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bvi_inc_clock_clock; ARITH_RULE `~(a < t) ==> ~(a + c < t)`] THEN
  ASM_SIMP_TAC[dec_clock_inv_clock; ARITH_RULE `~(a < t) ==> ~(a + c < t)`] THEN
  MP_TAC(ISPECL [`y:bvi_exp`; `MAP (adjust_bv b3) args`;
     `bvi_inc_clock ck2 (bvi_dec_clock (ticks + 1) (t2:(C,FFI)bvi_state))`;
     `map_result (MAP (adjust_bv b3)) (\v. Exn (adjust_bv b3 v)) (res:(bvl_v list,bvl_v)result)`;
     `t3:(C,FFI)bvi_state`] bvi_letProof_evaluate_compile_exp) THEN
  ASM_SIMP_TAC[B2BP2AUX_not_type_error_map] THEN DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL
   [B2BP2AUX_CALL_RESULT_TAC `res:(bvl_v list,bvl_v)result`;
    MATCH_MP_TAC B2BP2AUX_agree_trans THEN
    EXISTS_TAC `b2:num->num` THEN EXISTS_TAC `FDOM (bvl_state_refs (s5:(num#C,FFI)bvl_state))` THEN
    ASM_REWRITE_TAC[]]);;

(* the Op case: compile_op keeps an error of the arguments *)
let B2BP2AUX_ERR_FIN_TAC : tactic =
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    ASM_REWRITE_TAC[IS_NONE_DEF; IS_SOME_DEF; bvi_evaluate_APPEND] THEN CASE_REWRITE_TAC[]));;

let B2BP2AUX_op_err = prove
 (`!op c1 E (t0:(C,FFI)bvi_state) e t2.
     bvi_evaluate (c1,E,t0) = (Rerr e,t2)
     ==> bvi_evaluate ([bvl_to_bvi_compile_op op c1],E,t0) = (Rerr e,t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(c1:bvi_exp list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[bvi_evaluate_def; PAIR_EQ; distinctness "result"];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bvl_to_bvi_compile_op_def; NULL_EQ] THEN
  REPEAT TOP_CASE_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN B2BP2AUX_ERR_FIN_TAC);;

(* rewriting with the assumptions and the case equations until nothing      *)
(* changes *)
let B2BP2AUX_ASM_CASE_TAC thl : tactic =
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC thl THEN CASE_REWRITE_TAC thl));;

let B2BP2AUX_do_app_GlobalsPtr = prove
 (`!(s:(C,FFI)bvi_state) p.
     bvi_state_global s = SOME p
     ==> bvi_do_app (GlobOp GlobalsPtr) [] s = Rval (bvl_RefPtr T p,s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let B2BP2AUX_do_app_Add = prove
 (`!i j (s:(C,FFI)bvi_state).
     bvi_do_app (IntOp clos_Add) [bvl_Number i; bvl_Number j] s = Rval (bvl_Number (i + j),s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_int_app_def] THEN CASE_REWRITE_TAC[bvl_to_bvi_id]);;

let B2BP2AUX_do_app_El = prove
 (`!(s:(C,FFI)bvi_state) p xs i f.
     FLOOKUP (bvi_state_refs s) p = SOME (bvl_ValueArray xs) /\ &0 <= i /\ i < &(LENGTH xs)
     ==> bvi_do_app (MemOp clos_El) [bvl_RefPtr f p; bvl_Number i] s =
         Rval (EL (num_of_int i) xs,s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_ASM_CASE_TAC[bvi_bvi_to_bvl_refs; bvl_to_bvi_id]);;

let B2BP2AUX_do_app_RefByte0 = prove
 (`!(s:(C,FFI)bvi_state) f i.
     &0 <= i
     ==> bvi_do_app (MemOp (RefByte f)) [bvl_Number i; bvl_Number (&0)] s =
         Rval (bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),
               bvi_state_refs_fupd (K (bvi_state_refs s |+
                 ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),
                  bvl_ByteArray f (REPLICATE (num_of_int i) (iword (&0)))))) s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?w:byte. (&0:int) = &(val w)` (fun th -> ASM_REWRITE_TAC[th]) THENL
   [EXISTS_TAC `word 0:byte` THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[]);;

let B2BP2AUX_do_app_CopyByteF = prove
 (`!(s:(C,FFI)bvi_state) f1 src srcoff len f2 dst dstoff fw ws fl ds ds'.
     FLOOKUP (bvi_state_refs s) src = SOME (bvl_ByteArray fw ws) /\
     FLOOKUP (bvi_state_refs s) dst = SOME (bvl_ByteArray fl ds) /\
     copy_array (ws,srcoff) len (SOME (ds,dstoff)) = SOME ds'
     ==> bvi_do_app (MemOp (CopyByte F))
           [bvl_RefPtr f1 src; bvl_Number srcoff; bvl_Number len; bvl_RefPtr f2 dst;
            bvl_Number dstoff] s =
         Rval (bvl_Unit,
               bvi_state_refs_fupd (K (bvi_state_refs s |+ (dst,bvl_ByteArray fl ds'))) s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_ASM_CASE_TAC[bvi_bvi_to_bvl_refs; bvl_to_bvi_with_refs; bvl_to_bvi_id]);;

(* the Op case: an error of do_app (only an FFI error is possible) *)
let B2BP2AUX_do_app_FFI_Rerr = prove
 (`!i vs (s:(C,FFI)bvl_state) e.
     bvl_do_app (clos_FFI i) vs s = Rerr e /\ ~(e = Rabort Rtype_error)
     ==> ?f1 cptr f2 ptr cws ws outcome.
           vs = [bvl_RefPtr f1 cptr; bvl_RefPtr f2 ptr] /\
           FLOOKUP (bvl_state_refs s) cptr = SOME (bvl_ByteArray T cws) /\
           FLOOKUP (bvl_state_refs s) ptr = SOME (bvl_ByteArray F ws) /\
           call_FFI (bvl_state_ffi s) (ExtCall i) cws ws = FFI_final outcome /\
           e = Rabort (Rffi_error outcome)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; injectivity "error_result";
              distinctness "error_result"] THEN
  TRY(STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`a0':bool`; `a1':num`; `a0'':bool`; `a1:num`; `a1'':byte list`;
                        `a1''':byte list`; `a'':final_event`] THEN
  ASM_REWRITE_TAC[]);;

let B2BP2AUX_op_Rerr = prove
 (`!op c1 a (s5:(num#C,FFI)bvl_state) e b2 (t0:(C,FFI)bvi_state) t2 E.
     bvl_do_app op (REVERSE a) s5 = Rerr e /\ ~(e = Rabort Rtype_error) /\
     bvi_evaluate (c1,E,t0) = (Rval (MAP (adjust_bv b2) a),t2) /\
     bvl_to_bviProof_state_rel b2 s5 t2
     ==> bvi_evaluate ([bvl_to_bvi_compile_op op c1],E,t0) =
         (Rerr (map_error_result (\v. Exn (adjust_bv b2 v)) e),t2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvl_do_app_err) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:mlstring` (X_CHOOSE_THEN `x:final_event`
    (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
  B2BP2AUX_DRULE_ALL_TAC B2BP2AUX_do_app_FFI_Rerr THEN
  REWRITE_TAC[distinctness "error_result"; injectivity "error_result";
              distinctness "abort"; injectivity "abort"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP_REVERSE] THEN ASM_REWRITE_TAC[MAP; adjust_bv_def] THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_bvi_to_bvl_refs; bvi_to_bvl_ffi] THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`; `T`;
                 `cws:byte list`; `cptr:num`] state_rel_FLOOKUP_byteArray) THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`; `F`;
                 `ws:byte list`; `ptr:num`] state_rel_FLOOKUP_byteArray) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bvi_state_ffi (t2:(C,FFI)bvi_state) = bvl_state_ffi (s5:(num#C,FFI)bvl_state)`
    SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)`)) THEN
    SIMP_TAC[bvl_to_bviProof_state_rel_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[map_error_result_def]);;

(* the Op case for a value of do_app: one lemma per operation that         *)
(* compile_op treats specially (HOL4 Cases_on `op = ...` in the Resume of   *)
(* compile_exps_correct[Op]); B2BP2AUX_opv op is the statement for op      *)
let B2BP2AUX_opv_template =
 `!op c1 a (s5:(num#C,FFI)bvl_state) q r b2 (t0:(C,FFI)bvi_state) t2 E.
     bvl_do_app op (REVERSE a) s5 = Rval (q,r) /\
     bvi_evaluate (c1,E,t0) = (Rval (MAP (adjust_bv b2) a),t2) /\
     bvl_to_bviProof_state_rel b2 s5 t2 /\ bvl_to_bviProof_state_ok s5 /\
     ALL (bv_ok (bvl_state_refs s5)) a /\ IS_SOME (bvi_state_global t2)
     ==> ?ck t3 b3.
           bvi_evaluate ([bvl_to_bvi_compile_op op c1],E,bvi_inc_clock ck t0) =
             (Rval [adjust_bv b3 q],t3) /\
           bvl_to_bviProof_state_rel b3 r t3 /\
           (!x. x IN FDOM (bvl_state_refs s5) ==> b3 x = b2 x)`;;

let B2BP2AUX_opv (op:term) =
  let vs,bod = strip_forall B2BP2AUX_opv_template in
  list_mk_forall(frees op @ tl vs, vsubst [op,hd vs] bod);;

(* the evaluation of the compiled arguments with more clock *)
let B2BP2AUX_c1_clock = prove
 (`!c1 E (t0:(C,FFI)bvi_state) vs t2 ck.
     bvi_evaluate (c1,E,t0) = (Rval vs,t2)
     ==> bvi_evaluate (c1,E,bvi_inc_clock ck t0) = (Rval vs,bvi_inc_clock ck t2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC evaluate_inv_clock THEN
  ASM_REWRITE_TAC[distinctness "result"]);;

(* the start of each operation lemma: the do_app assumption split into its *)
(* clauses *)
let B2BP2AUX_OPV_START_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvl_do_app"
    with Failure _ -> false)) THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ;
              option_INJ; option_DISTINCT];;

(* c1 evaluates to the empty list: then t2 = t0 *)
let B2BP2AUX_c1_NIL = prove
 (`!c1 E (t0:(C,FFI)bvi_state) t2.
     bvi_evaluate (c1,E,t0) = (Rval [],t2) ==> c1 = [] /\ t2 = t0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[bvi_evaluate_def; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 2503: Cases_on `?i. op = IntOp (Const i)` *)
let B2BP2AUX_opv_Const = prove
 (B2BP2AUX_opv `IntOp (clos_Const i)`,
  B2BP2AUX_OPV_START_TAC THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  POP_ASSUM MP_TAC THEN CASES_ON `REVERSE (a:bvl_v list)` THEN
  REWRITE_TAC[bvl_do_int_app_def; option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE_EQ_EMPTY]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_c1_NIL) THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `t0:(C,FFI)bvi_state`; `b2:num->num`] THEN
  ASM_REWRITE_TAC[bvl_to_bvi_compile_op_def; inc_clock_ZERO; compile_int_thm; adjust_bv_def] THEN
  CASE_REWRITE_TAC[compile_int_thm]);;

(* HOL4 line 2514: Cases_on `?n. op = Label n` *)
let B2BP2AUX_opv_Label = prove
 (B2BP2AUX_opv `clos_Label n`,
  B2BP2AUX_OPV_START_TAC THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE_EQ_EMPTY]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_c1_NIL) THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `t0:(C,FFI)bvi_state`; `b2:num->num`] THEN
  ASM_REWRITE_TAC[bvl_to_bvi_compile_op_def; inc_clock_ZERO; adjust_bv_def] THEN
  CASE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[bvi_evaluate_def; REVERSE] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bvl_num_stubs + bvl_to_bvi_namespaces * n IN
                domain (bvi_state_code (t0:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:num#bvl_exp` MP_TAC o
      check (fun th -> is_exists (concl th))) THEN
    MP_TAC(ISPEC `v:num#bvl_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`b2:num->num`; `r:(num#C,FFI)bvl_state`; `t0:(C,FFI)bvi_state`; `n:num`;
                   `ar:num`; `e:bvl_exp`] B2BP2AUX_state_rel_lookup) THEN
    ASM_REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

(* the globals array of state_rel *)
let B2BP2AUX_state_rel_global = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state).
     bvl_to_bviProof_state_rel b s t /\ IS_SOME (bvi_state_global t)
     ==> ?p z. bvi_state_global t = SOME p /\ ~(p IN IMAGE b (FDOM (bvl_state_refs s))) /\
               FLOOKUP (bvi_state_refs t) p =
                 SOME (bvl_ValueArray
                   (CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals s)))))
                      (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b))
                                 (bvl_state_globals s))
                         (REPLICATE (z - SUC (LENGTH (bvl_state_globals s)))
                            (bvl_Number (&0)))))) /\
               SUC (LENGTH (bvl_state_globals s)) <= z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_SOME_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `p:num`)) THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  DISCH_THEN(MP_TAC o SPEC `p:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `z:num`] THEN ASM_REWRITE_TAC[]);;

(* state_rel after a change of the globals mirrored in the globals array *)
let B2BP2AUX_state_rel_set_globals = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) p z gs.
     bvl_to_bviProof_state_rel b s t /\ bvi_state_global t = SOME p /\
     SUC (LENGTH gs) <= z
     ==> bvl_to_bviProof_state_rel b (bvl_state_globals_fupd (K gs) s)
           (bvi_state_refs_fupd (K (bvi_state_refs t |+
              (p,bvl_ValueArray
                   (CONS (bvl_Number (&(SUC (LENGTH gs))))
                      (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b)) gs)
                         (REPLICATE (z - SUC (LENGTH gs)) (bvl_Number (&0)))))))) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
    (ASSUME `bvi_state_global (t:(C,FFI)bvi_state) = SOME p`) o check (fun th ->
    try let v,b = dest_forall (concl th) in name_of v = "p" && is_imp b with Failure _ -> false)) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC INJ_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))`;
                          `FDOM (bvi_state_refs (t:(C,FFI)bvi_state))`] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE; SUBSET_REFL] THEN SET_TAC[];
    X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      try let v,b = dest_forall (concl th) in name_of v = "k" with Failure _ -> false)) THEN
    CASES_ON `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k` THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(p = (b:num->num) k)` (fun th -> REWRITE_TAC[FLOOKUP_UPDATE; th]) THEN
    UNDISCH_TAC `~(p IN IMAGE (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))))` THEN
    REWRITE_TAC[IN_IMAGE; CONTRAPOS_THM] THEN DISCH_TAC THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k = SOME a` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT];
    X_GEN_TAC `p':num` THEN ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2943: Cases_on `?n. op = GlobOp (SetGlobal n)` *)
let B2BP2AUX_opv_SetGlobal = prove
 (B2BP2AUX_opv `GlobOp (SetGlobal n)`,
  B2BP2AUX_OPV_START_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[MAP; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:bvi_exp` (X_CHOOSE_THEN `tl:bvi_exp list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[get_global_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`]
    B2BP2AUX_state_rel_global) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`;
   `bvi_state_refs_fupd (K (bvi_state_refs t2 |+ (p,bvl_ValueArray
      (LUPDATE (adjust_bv b2 a0) (n + 1)
        (CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))))))
          (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b2))
                     (bvl_state_globals s5))
             (REPLICATE (z - SUC (LENGTH (bvl_state_globals s5))) (bvl_Number (&0)))))))))
      (t2:(C,FFI)bvi_state)`;
   `b2:num->num`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[MAP] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE] THEN
  SUBGOAL_THEN `n + 1 < SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state)) +
                  z - SUC (LENGTH (bvl_state_globals s5)))` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `n < LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))` THEN
    UNDISCH_TAC `SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))) <= z` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CASE_REWRITE_TAC[adjust_bv_Unit] THEN
  SUBGOAL_THEN `LUPDATE (adjust_bv b2 a0) (n + 1)
      (CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))))))
        (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b2)) (bvl_state_globals s5))
           (REPLICATE (z - SUC (LENGTH (bvl_state_globals s5))) (bvl_Number (&0))))) =
      CONS (bvl_Number (&(SUC (LENGTH (LUPDATE (SOME a0) n (bvl_state_globals s5))))))
        (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b2))
                   (LUPDATE (SOME a0) n (bvl_state_globals s5)))
           (REPLICATE (z - SUC (LENGTH (LUPDATE (SOME a0) n (bvl_state_globals s5))))
              (bvl_Number (&0))))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM ADD1; LUPDATE_def; LENGTH_LUPDATE; CONS_11] THEN
    ASM_SIMP_TAC[LUPDATE_APPEND1; LENGTH_MAP; LUPDATE_MAP] THEN
    REWRITE_TAC[o_THM; OPTION_MAP_DEF; the_def];
    MATCH_MP_TAC B2BP2AUX_state_rel_set_globals THEN
    ASM_REWRITE_TAC[LENGTH_LUPDATE]]);;

(* HOL4 line 2890: Cases_on `?n. op = GlobOp (Global n)` *)
let B2BP2AUX_opv_Global = prove
 (B2BP2AUX_opv `GlobOp (clos_Global n)`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[get_global_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`]
    B2BP2AUX_state_rel_global) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THENL
  [FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_c1_NIL) THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `t0:(C,FFI)bvi_state`; `b2:num->num`] THEN
  ASM_REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def; NULL] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE] THEN
  SUBGOAL_THEN `n + 1 < SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state)) +
                  z - SUC (LENGTH (bvl_state_globals s5)))` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `n < LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))` THEN
    UNDISCH_TAC `SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))) <= z` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; EL; TL] THEN ASM_SIMP_TAC[EL_APPEND1; LENGTH_MAP; EL_MAP] THEN
  ASM_REWRITE_TAC[o_THM; OPTION_MAP_DEF; the_def];
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[MAP; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:bvi_exp` (X_CHOOSE_THEN `tl:bvi_exp list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[num_added_globals_def; MAP; adjust_bv_def]) THEN
  MAP_EVERY EXISTS_TAC [`0`; `t2:(C,FFI)bvi_state`; `b2:num->num`] THEN
  ASM_REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def; NULL; NOT_CONS_NIL] THEN
  CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND] THEN
  REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    REWRITE_TAC[LENGTH; EL; HD; TL; ARITH_RULE `0 < SUC n`] THEN CASE_REWRITE_TAC[])) THEN
  SUBGOAL_THEN `small_enough_int (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[small_enough_int_def] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REVERSE; APPEND; BVITAILAUX_do_app_Const] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; REVERSE; APPEND; B2BP2AUX_do_app_Add] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[B2BP2AUX_do_app_GlobalsPtr] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; REVERSE; APPEND] THEN
  SUBGOAL_THEN `?j. (a':int) = &j` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `num_of_int a'` THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    UNDISCH_TAC `~((a':int) < &0)` THEN INT_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NUM_OF_INT_OF_NUM]) THEN
  REWRITE_TAC[INT_OF_NUM_ADD] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [`t2:(C,FFI)bvi_state`; `p:num`;
     `CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))))))
        (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b2)) (bvl_state_globals s5))
           (REPLICATE (z - SUC (LENGTH (bvl_state_globals s5))) (bvl_Number (&0))))`;
     `&(j + 2):int`; `T`] B2BP2AUX_do_app_El)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE; INT_OF_NUM_LE;
                    INT_OF_NUM_LT; LE_0] THEN
    UNDISCH_TAC `j + 1 < LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))` THEN
    UNDISCH_TAC `SUC (LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))) <= z` THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM; ARITH_RULE `j + 2 = SUC (j + 1)`; EL; TL] THEN
    ASM_SIMP_TAC[EL_APPEND1; LENGTH_MAP; EL_MAP] THEN
    ASM_REWRITE_TAC[o_THM; OPTION_MAP_DEF; the_def]]]);;

(* state_rel after allocating a fresh value array (HOL4 does this inline in  *)
(* the cases Ref and RefArray, as state_rel_add_thunk does for thunks)       *)
let B2BP2AUX_state_rel_add_valuearray = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) pp qq vs.
     bvl_to_bviProof_state_rel b s t /\ bvl_to_bviProof_state_ok s /\
     ~(pp IN FDOM (bvl_state_refs s)) /\ ~(qq IN FDOM (bvi_state_refs t))
     ==> bvl_to_bviProof_state_rel ((pp =+ qq) b)
           (bvl_state_refs_fupd (K (bvl_state_refs s |+ (pp,bvl_ValueArray vs))) s)
           (bvi_state_refs_fupd
              (K (bvi_state_refs t |+ (qq,bvl_ValueArray (MAP (adjust_bv ((pp =+ qq) b)) vs))))
              t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[FDOM_FUPDATE] THEN MATCH_MP_TAC INJ_EXTEND THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[FLOOKUP_UPDATE; APPLY_UPDATE_THM] THEN
    ASM_CASES_TAC `pp:num = k` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      try let v,b = dest_forall (concl th) in name_of v = "k" with Failure _ -> false)) THEN
    CASES_ON `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k` THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(qq = (b:num->num) k)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((b:num->num) k IN FDOM (bvi_state_refs (t:(C,FFI)bvi_state)))` THEN
      REWRITE_TAC[] THEN
      UNDISCH_TAC `INJ (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state)))
                     (FDOM (bvi_state_refs (t:(C,FFI)bvi_state)))` THEN
      REWRITE_TAC[INJ] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      UNDISCH_TAC `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k = SOME a` THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    CASES_ON `a:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
    UNDISCH_TAC `bvl_to_bviProof_state_ok (s:(num#C,FFI)bvl_state)` THEN
    REWRITE_TAC[bvl_to_bviProof_state_ok_def] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    (MATCH_MP_TAC B2BP2AUX_MAP_adjust_update ORELSE MATCH_MP_TAC B2BP2AUX_adjust_update) THEN
    EXISTS_TAC `bvl_state_refs (s:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `bvi_state_global (t:(C,FFI)bvi_state) = SOME p`) o check (fun th ->
      try let v,b = dest_forall (concl th) in name_of v = "p" && is_imp b
      with Failure _ -> false)) THEN
    SUBGOAL_THEN `~(qq:num = p)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(p IN FDOM (bvi_state_refs (t:(C,FFI)bvi_state)))` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
         "FLOOKUP" with Failure _ -> false)) THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FDOM_FUPDATE; IN_IMAGE; IN_INSERT; APPLY_UPDATE_THM] THEN
      UNDISCH_TAC `~(p IN IMAGE (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))))` THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
      REWRITE_TAC[option_INJ; injectivity "bvl_ref"; CONS_11; APPEND_RCANCEL] THEN
      MATCH_MP_TAC MAP_EQ THEN
      UNDISCH_TAC `bvl_to_bviProof_state_ok (s:(num#C,FFI)bvl_state)` THEN
      REWRITE_TAC[bvl_to_bviProof_state_ok_def] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC MONO_ALL THEN
      X_GEN_TAC `o1:bvl_v option` THEN CASES_ON `o1:bvl_v option` THEN
      CASE_REWRITE_TAC[o_THM; OPTION_MAP_DEF; the_def] THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC B2BP2AUX_adjust_update THEN
      EXISTS_TAC `bvl_state_refs (s:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[]]]);;

(* the fresh pointers of an allocation *)
let B2BP2AUX_FRESH_TAC : tactic =
  MAP_EVERY ABBREV_TAC
    [`x = minimal ptr. ~(ptr IN FDOM (bvl_state_refs (s5:(num#C,FFI)bvl_state)))`;
     `y = minimal ptr. ~(ptr IN FDOM (bvi_state_refs (t2:(C,FFI)bvi_state)))`] THEN
  SUBGOAL_THEN `~(x IN FDOM (bvl_state_refs (s5:(num#C,FFI)bvl_state))) /\
                ~(y IN FDOM (bvi_state_refs (t2:(C,FFI)bvi_state)))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN REWRITE_TAC[LEAST_NOTIN_FDOM]; ALL_TAC];;

(* HOL4 line 2589: Cases_on `op = MemOp Ref` *)
let B2BP2AUX_opv_Ref = prove
 (B2BP2AUX_opv `MemOp clos_Ref`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN B2BP2AUX_FRESH_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       (y,bvl_ValueArray (MAP (adjust_bv b2) (REVERSE a))))) (t2:(C,FFI)bvi_state)`;
    `((x:num) =+ (y:num)) b2`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_to_bviProof_do_app_Ref; MAP_REVERSE; bvl_to_bvi_with_refs; bvl_to_bvi_id;
                  bvi_bvi_to_bvl_refs] THEN
  CASE_REWRITE_TAC[adjust_bv_def; APPLY_UPDATE_THM] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `MAP (adjust_bv b2) (REVERSE a) = MAP (adjust_bv ((x =+ y) b2)) (REVERSE a)`
      SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC B2BP2AUX_MAP_adjust_update THEN
      EXISTS_TAC `bvl_state_refs (s5:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[EVERY_REVERSE];
      MATCH_MP_TAC B2BP2AUX_state_rel_add_valuearray THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

(* HOL4 line 2693: Cases_on `op = MemOp RefArray` *)
let B2BP2AUX_opv_RefArray = prove
 (B2BP2AUX_opv `MemOp RefArray`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  B2BP2AUX_FRESH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; adjust_bv_def]) THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       (y,bvl_ValueArray (REPLICATE (num_of_int a') (adjust_bv b2 a0'))))) (t2:(C,FFI)bvi_state)`;
    `((x:num) =+ (y:num)) b2`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs] THEN BETA_TAC THEN
  B2BP2AUX_ASM_CASE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id; adjust_bv_def; APPLY_UPDATE_THM] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `REPLICATE (num_of_int a') (adjust_bv b2 a0') =
                  MAP (adjust_bv ((x =+ y) b2)) (REPLICATE (num_of_int a') a0')` SUBST1_TAC THENL
     [REWRITE_TAC[map_replicate] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC B2BP2AUX_adjust_update THEN
      EXISTS_TAC `bvl_state_refs (s5:(num#C,FFI)bvl_state)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC B2BP2AUX_state_rel_add_valuearray THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

(* HOL4 line 2788: Cases_on `?flag. op = MemOp (RefByte flag)` *)
let B2BP2AUX_opv_RefByte = prove
 (B2BP2AUX_opv `MemOp (RefByte flag)`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  B2BP2AUX_FRESH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; adjust_bv_def]) THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       (y,bvl_ByteArray F (REPLICATE (num_of_int a') (iword a''))))) (t2:(C,FFI)bvi_state)`;
    `((x:num) =+ (y:num)) b2`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  B2BP2AUX_ASM_CASE_TAC[adjust_bv_def; APPLY_UPDATE_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_add_bytearray THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* rewrite with the bvi refs of a bvl ref (state_rel_FLOOKUP_valueArray,    *)
(* _byteArray, _MutBlock, _Thunk) for the assumptions FLOOKUP s.refs k = .. *)
let B2BP2AUX_REFS_TAC (srel:term) : tactic =
  let lems = [state_rel_FLOOKUP_valueArray; state_rel_FLOOKUP_byteArray;
              state_rel_FLOOKUP_MutBlock; state_rel_FLOOKUP_Thunk] in
  ASSUM_LIST(fun thl -> MAP_EVERY (fun th -> fun g ->
    try REWRITE_TAC[tryfind (fun l -> MATCH_MP l (CONJ (ASSUME srel) th)) lems] g
    with Failure _ -> ALL_TAC g) thl);;

let B2BP2AUX_bad_thunk_adjust = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) m v.
     bvl_to_bviProof_state_rel b s t /\ ~bvl_bad_thunk_update m v (bvl_state_refs s)
     ==> ~bvl_bad_thunk_update m (adjust_bv b v) (bvi_state_refs t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_bad_thunk_update_def; DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `v:bvl_v` THEN
  REWRITE_TAC[adjust_bv_def; bvl_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) a1` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a0':thunk_mode` THEN CASE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      CASE_REWRITE_TAC[] THEN NO_TAC) THEN
  B2BP2AUX_REFS_TAC `bvl_to_bviProof_state_rel b s (t:(C,FFI)bvi_state)` THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 2425: Cases_on `?m. op = ThunkOp (AllocThunk m)` *)
let B2BP2AUX_opv_AllocThunk = prove
 (B2BP2AUX_opv `clos_ThunkOp (AllocThunk m)`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  B2BP2AUX_FRESH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL]) THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`; `m:thunk_mode`;
                 `a0:bvl_v`] B2BP2AUX_bad_thunk_adjust) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       (y,bvl_Thunk m (adjust_bv b2 a0)))) (t2:(C,FFI)bvi_state)`;
    `((x:num) =+ (y:num)) b2`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs] THEN BETA_TAC THEN
  B2BP2AUX_ASM_CASE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id; adjust_bv_def; APPLY_UPDATE_THM] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `adjust_bv b2 a0 = adjust_bv ((x =+ y) b2) a0` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC B2BP2AUX_adjust_update THEN
      EXISTS_TAC `bvl_state_refs (s5:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC state_rel_add_thunk THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

(* HOL4 line 2480: Cases_on `?m. op = ThunkOp (UpdateThunk m)` *)
let B2BP2AUX_opv_UpdateThunk = prove
 (B2BP2AUX_opv `clos_ThunkOp (UpdateThunk m)`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL; adjust_bv_def]) THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`; `m:thunk_mode`;
                 `a0'':bvl_v`] B2BP2AUX_bad_thunk_adjust) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_FLOOKUP_Thunk o
    CONJ (ASSUME `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)`) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "FLOOKUP"
                     with Failure _ -> false)) THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       ((b2:num->num) a1',bvl_Thunk m (adjust_bv b2 a0'')))) (t2:(C,FFI)bvi_state)`;
    `b2:num->num`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs] THEN BETA_TAC THEN
  B2BP2AUX_ASM_CASE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id; adjust_bv_def; adjust_bv_Unit] THEN
  MATCH_MP_TAC bvl_to_bviProof_state_rel_update_thunk THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `FLOOKUP (bvl_state_refs (s5:(num#C,FFI)bvl_state)) a1' =
               SOME (bvl_Thunk NotEvaluated a1''')` THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT]);;

(* state_rel after overwriting an existing byte array (HOL4 inline in the  *)
(* cases XorByte and CopyByte F) *)
let B2BP2AUX_state_rel_update_bytearray = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) dst fl ws.
     bvl_to_bviProof_state_rel b s t /\ dst IN FDOM (bvl_state_refs s)
     ==> bvl_to_bviProof_state_rel b
           (bvl_state_refs_fupd (K (bvl_state_refs s |+ (dst,bvl_ByteArray fl ws))) s)
           (bvi_state_refs_fupd (K (bvi_state_refs t |+ (b dst,bvl_ByteArray fl ws))) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[FDOM_FUPDATE] THEN MATCH_MP_TAC INJ_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))`;
                          `FDOM (bvi_state_refs (t:(C,FFI)bvi_state))`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    ASM_CASES_TAC `dst:num = k` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      try let v,b = dest_forall (concl th) in name_of v = "k" with Failure _ -> false)) THEN
    CASES_ON `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k` THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((b:num->num) dst = b k)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `INJ (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state)))
                   (FDOM (bvi_state_refs (t:(C,FFI)bvi_state)))` THEN
    REWRITE_TAC[INJ] THEN
    UNDISCH_TAC `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k = SOME a` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN ASM_MESON_TAC[option_DISTINCT];
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `bvi_state_global (t:(C,FFI)bvi_state) = SOME p`) o check (fun th ->
      try let v,b = dest_forall (concl th) in name_of v = "p" && is_imp b
      with Failure _ -> false)) THEN
    SUBGOAL_THEN `~((b:num->num) dst = p)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(p IN IMAGE (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))))` THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(p IN IMAGE (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))))` THEN
      REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN ASM_MESON_TAC[];
      EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[]]]);;

(* add the bvi refs of the assumptions FLOOKUP s.refs k = SOME r *)
let B2BP2AUX_TRANSFER_REFS_TAC (srel:term) : tactic =
  let lems = [state_rel_FLOOKUP_valueArray; state_rel_FLOOKUP_byteArray;
              state_rel_FLOOKUP_MutBlock; state_rel_FLOOKUP_Thunk] in
  ASSUM_LIST(fun thl -> MAP_EVERY (fun th -> fun g ->
    try ASSUME_TAC (tryfind (fun l -> MATCH_MP l (CONJ (ASSUME srel) th)) lems) g
    with Failure _ -> ALL_TAC g) thl);;

(* HOL4 line 3363: Cases_on `op = MemOp XorByte` *)
let B2BP2AUX_opv_XorByte = prove
 (B2BP2AUX_opv `MemOp XorByte`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL; adjust_bv_def]) THEN
  B2BP2AUX_TRANSFER_REFS_TAC `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)` THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       ((b2:num->num) a1',bvl_ByteArray a0''''' a'''))) (t2:(C,FFI)bvi_state)`;
    `b2:num->num`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs] THEN BETA_TAC THEN
  B2BP2AUX_ASM_CASE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id; adjust_bv_def; adjust_bv_Unit] THEN
  MATCH_MP_TAC B2BP2AUX_state_rel_update_bytearray THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `FLOOKUP (bvl_state_refs (s5:(num#C,FFI)bvl_state)) a1' =
               SOME (bvl_ByteArray a0''''' a1''''')` THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT]);;

(* HOL4 line 3407: Cases_on `op = MemOp (CopyByte F)` *)
let B2BP2AUX_opv_CopyByteF = prove
 (B2BP2AUX_opv `MemOp (CopyByte F)`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL; adjust_bv_def]) THEN
  B2BP2AUX_TRANSFER_REFS_TAC `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)` THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       ((b2:num->num) a1''''',bvl_ByteArray a0'''''''' a''''''))) (t2:(C,FFI)bvi_state)`;
    `b2:num->num`] THEN
  REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs] THEN BETA_TAC THEN
  B2BP2AUX_ASM_CASE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id; adjust_bv_def; adjust_bv_Unit] THEN
  MATCH_MP_TAC B2BP2AUX_state_rel_update_bytearray THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `FLOOKUP (bvl_state_refs (s5:(num#C,FFI)bvl_state)) a1''''' =
               SOME (bvl_ByteArray a0'''''''' a1'''''''')` THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT]);;

(* state_ok after adding a byte array *)
let B2BP2AUX_state_ok_add_bytearray = prove
 (`!(s:(num#C,FFI)bvl_state) ptr fl bs.
     bvl_to_bviProof_state_ok s /\ ~(ptr IN FDOM (bvl_state_refs s))
     ==> bvl_to_bviProof_state_ok
           (bvl_state_refs_fupd (K (bvl_state_refs s |+ (ptr,bvl_ByteArray fl bs))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_ok_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state)) SUBSET
                FDOM (bvl_state_refs s |+ (ptr,bvl_ByteArray fl bs))` ASSUME_TAC THENL
   [REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false)) THEN
    MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC `o1:bvl_v option` THEN CASES_ON `o1:bvl_v option` THEN
    CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[bv_ok_SUBSET_IMP];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    CASES_ON `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k` THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `a:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[bv_ok_SUBSET_IMP; B2BP2AUX_ALL_bv_ok_SUBSET]]);;

(* the built constant of Build: do_build on the bvi refs gives the adjusted   *)
(* value (HOL4: induction on parts in the case Build) *)
let B2BP2AUX_DB_SIMPLE_TAC (x1:term) (x2:term) : tactic =
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [vsubst [x1,`xx:bvl_v`] `((l:num) =+ xx) (m1:num->bvl_v)`;
     vsubst [x2,`xx:bvl_v`] `((l:num) =+ xx) (m2:num->bvl_v)`; `l + 1`; `b:num->num`;
     `s:(num#C,FFI)bvl_state`; `t':(C,FFI)bvi_state`; `q:bvl_v`;
     `rs:(num,(bvl_v)bvl_ref)fmap`]) THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bv_ok_def; adjust_bv_def; ALL_MAP; MAP_MAP_o; injectivity "bvl_v"] THEN
    TRY(MATCH_MP_TAC MAP_EQ) THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[]];;

let B2BP2AUX_do_build_adjust = prove
 (`!parts m1 m2 l b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) q rs.
     bvl_do_build m1 l parts (bvl_state_refs s) = (q,rs) /\
     bvl_to_bviProof_state_rel b s t /\ bvl_to_bviProof_state_ok s /\
     (!k. bv_ok (bvl_state_refs s) (m1 k)) /\ (!k. m2 k = adjust_bv b (m1 k))
     ==> ?b' rs'. bvl_do_build m2 l parts (bvi_state_refs t) = (adjust_bv b' q,rs') /\
                  bvl_to_bviProof_state_rel b' (bvl_state_refs_fupd (K rs) s)
                    (bvi_state_refs_fupd (K rs') t) /\
                  (!a. a IN FDOM (bvl_state_refs s) ==> b' a = b a)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_build_def; PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`b:num->num`; `bvi_state_refs (t:(C,FFI)bvi_state)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!(x:(num#C,FFI)bvl_state). bvl_state_refs_fupd (K (bvl_state_refs x)) x = x /\
                  !(y:(C,FFI)bvi_state). bvi_state_refs_fupd (K (bvi_state_refs y)) y = y`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[bvl_state_component_equality; bvi_state_component_equality;
                bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  CASES_ON `h:const_part` THEN REWRITE_TAC[bvl_do_part_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN CASE_REWRITE_TAC[] THENL
  [STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`((l:num) =+ bvl_Block a0 (MAP m1 a1)) (m1:num->bvl_v)`;
     `((l:num) =+ bvl_Block a0 (MAP m2 a1)) (m2:num->bvl_v)`; `l + 1`; `b:num->num`;
     `s:(num#C,FFI)bvl_state`; `t':(C,FFI)bvi_state`; `q:bvl_v`;
     `rs:(num,(bvl_v)bvl_ref)fmap`]) THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bv_ok_def; adjust_bv_def; ALL_MAP; MAP_MAP_o; injectivity "bvl_v"] THEN
    TRY(MATCH_MP_TAC MAP_EQ) THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[]];
   B2BP2AUX_DB_SIMPLE_TAC `bvl_Number a` `bvl_Number a`;
   STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
    [`x = minimal ptr. ~(ptr IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state)))`;
     `y = minimal ptr. ~(ptr IN FDOM (bvi_state_refs (t':(C,FFI)bvi_state)))`] THEN
  SUBGOAL_THEN `~(x IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))) /\
                ~(y IN FDOM (bvi_state_refs (t':(C,FFI)bvi_state)))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN REWRITE_TAC[LEAST_NOTIN_FDOM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`((l:num) =+ bvl_RefPtr T x) (m1:num->bvl_v)`;
     `((l:num) =+ bvl_RefPtr T y) (m2:num->bvl_v)`; `l + 1`; `((x:num) =+ (y:num)) b`;
     `bvl_state_refs_fupd (K (bvl_state_refs s |+
        (x,bvl_ByteArray T (MAP (word o ORD) (explode a))))) (s:(num#C,FFI)bvl_state)`;
     `bvi_state_refs_fupd (K (bvi_state_refs t' |+
        (y,bvl_ByteArray T (MAP (word o ORD) (explode a))))) (t':(C,FFI)bvi_state)`;
     `q:bvl_v`; `rs:(num,(bvl_v)bvl_ref)fmap`]) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM;
              bvl_state_INFO.ri_fupdfupds; bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC state_rel_add_bytearray THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC B2BP2AUX_state_ok_add_bytearray THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN COND_CASES_TAC THEN
      REWRITE_TAC[bv_ok_def; FDOM_FUPDATE; IN_INSERT] THEN
      MATCH_MP_TAC bv_ok_SUBSET_IMP THEN
      EXISTS_TAC `bvl_state_refs (s:(num#C,FFI)bvl_state)` THEN
      ASM_REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[];
      X_GEN_TAC `k:num` THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[adjust_bv_def; APPLY_UPDATE_THM] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC B2BP2AUX_adjust_update THEN
      EXISTS_TAC `bvl_state_refs (s:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `b':num->num` (X_CHOOSE_THEN `rs':(num,(bvl_v)bvl_ref)fmap`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`b':num->num`; `rs':(num,(bvl_v)bvl_ref)fmap`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `a':num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a':num` o check (fun th -> is_forall (concl th))) THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT; APPLY_UPDATE_THM] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[]];
   B2BP2AUX_DB_SIMPLE_TAC `bvl_Word64 a` `bvl_Word64 a`]);;

(* HOL4 line 3049: Cases_on `?parts. op = BlockOp (Build parts)` *)
let B2BP2AUX_opv_Build = prove
 (B2BP2AUX_opv `BlockOp (Build parts)`,
  B2BP2AUX_OPV_START_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[bvl_do_build_const_def]) THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE_EQ_EMPTY]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_c1_NIL) THEN RVEQ_TAC THEN
  (fun (asl,w as g) -> MP_TAC (B2BP2AUX_drule_all
     (ASM_REWRITE_TAC[bv_ok_def; adjust_bv_def] THEN NO_TAC) asl
     (IMP_CURRY_RULE (ISPECL [`parts:const_part list`; `\x:num. bvl_Number (&0)`;
                              `\x:num. bvl_Number (&0)`] B2BP2AUX_do_build_adjust))) g) THEN
  DISCH_THEN(X_CHOOSE_THEN `b3:num->num` (X_CHOOSE_THEN `rs':(num,(bvl_v)bvl_ref)fmap`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`0`; `bvi_state_refs_fupd (K (rs':(num,(bvl_v)bvl_ref)fmap)) (t0:(C,FFI)bvi_state)`;
                        `b3:num->num`] THEN
  ASM_REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN REWRITE_TAC[bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_build_const_def; bvi_bvi_to_bvl_refs] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[bvl_to_bvi_with_refs; bvl_to_bvi_id]);;

let B2BP2AUX_find_code_lookup = prove
 (`!p (args:bvl_v list) (code:(num#A)spt) exp.
     lookup p code = SOME (LENGTH args,exp) ==> bvl_find_code (SOME p) args code = SOME (args,exp)`,
  MESON_TAC[B2BP2AUX_find_code_SOME]);;

(* a call of a stub (or any code) whose arguments are evaluated without a   *)
(* change of the state *)
let B2BP2AUX_call_stub = prove
 (`!loc xs env (s:(C,FFI)bvi_state) args body c r s'.
     bvi_evaluate (xs,env,bvi_inc_clock (c + 1) s) = (Rval args,bvi_inc_clock (c + 1) s) /\
     lookup loc (bvi_state_code s) = SOME (LENGTH args,body) /\
     bvi_evaluate ([body],args,bvi_inc_clock c s) = (Rval r,s')
     ==> bvi_evaluate ([bvi_Call 0 (SOME loc) xs NONE],env,bvi_inc_clock (c + 1) s) =
         (Rval r,s')`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[IS_NONE_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_inc_clock_code] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP B2BP2AUX_find_code_lookup th]) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_inc_clock_clock; ARITH_RULE `~(a + c + 1 < 0 + 1)`; ADD_CLAUSES;
              ARITH_RULE `~(a + c + 1 < 1)`] THEN
  SIMP_TAC[bvi_dec_clock_1_inc_clock; ARITH_RULE `~(c + 1 = 0)`; ADD_SUB] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let B2BP2AUX_eval_Var0_Const0 = prove
 (`!v env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []],CONS v env,s) =
     (Rval [v; bvl_Number (&0)],s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[bvi_evaluate_def; LENGTH; EL; HD; ARITH_RULE `0 < SUC n`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE] THEN
  SUBGOAL_THEN `small_enough_int (&0)` ASSUME_TAC THENL
   [REWRITE_TAC[small_enough_int_def] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BVITAILAUX_do_app_Const] THEN CASE_REWRITE_TAC[HD]);;

(* the stubs installed in a related bvi state, with their arities *)
let B2BP2AUX_state_rel_stubs = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state).
     bvl_to_bviProof_state_rel b s t
     ==> lookup AllocGlobal_location (bvi_state_code t) = SOME (1,SND AllocGlobal_code) /\
         lookup CopyGlobals_location (bvi_state_code t) = SOME (3,SND CopyGlobals_code) /\
         lookup ListLength_location (bvi_state_code t) = SOME (2,SND ListLength_code) /\
         lookup FromListByte_location (bvi_state_code t) = SOME (3,SND FromListByte_code) /\
         lookup ToListByte_location (bvi_state_code t) = SOME (3,SND ToListByte_code) /\
         lookup SumListLength_location (bvi_state_code t) = SOME (2,SND SumListLength_code) /\
         lookup ConcatByte_location (bvi_state_code t) = SOME (3,SND ConcatByte_code)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[AllocGlobal_code_def; CopyGlobals_code_def; ListLength_code_def;
              FromListByte_code_def; ToListByte_code_def; SumListLength_code_def;
              ConcatByte_code_def]);;

let B2BP2AUX_eval_Var = prove
 (`!n env (s:(C,FFI)bvi_state).
     n < LENGTH env ==> bvi_evaluate ([bvi_Var n],env,s) = (Rval [EL n env],s)`,
  SIMP_TAC[bvi_evaluate_def]);;

let B2BP2AUX_eval_Var_CONS = prove
 (`!v w env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Var 0],CONS v env,s) = (Rval [v],s) /\
     bvi_evaluate ([bvi_Var 1],CONS v (CONS w env),s) = (Rval [w],s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_evaluate_def; LENGTH; ONE; EL; HD; TL] THEN
  REWRITE_TAC[ARITH_RULE `0 < SUC n /\ SUC 0 < SUC (SUC n)`]);;

(* HOL4 line 2527: Cases_on `?i. op = BlockOp (FromList i)` *)
let B2BP2AUX_opv_FromList = prove
 (B2BP2AUX_opv `BlockOp (FromList n)`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[MAP; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:bvi_exp` (X_CHOOSE_THEN `tl:bvi_exp list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_stubs) THEN
  MP_TAC(ISPECL [`adjust_bv b2 a0`; `MAP (adjust_bv b2) a'`; `0`; `t2:(C,FFI)bvi_state`]
    evaluate_ListLength_code) THEN
  ASM_REWRITE_TAC[v_to_list_adjust; OPTION_MAP_DEF; ADD_CLAUSES; LENGTH_MAP] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  MAP_EVERY EXISTS_TAC [`c + 1`; `t2:(C,FFI)bvi_state`; `b2:num->num`] THEN
  REWRITE_TAC[bvl_to_bvi_compile_op_def; NULL; NOT_CONS_NIL] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  SUBGOAL_THEN `bvi_evaluate ([d],E,bvi_inc_clock (c + 1) (t0:(C,FFI)bvi_state)) =
                (Rval [adjust_bv b2 a0],bvi_inc_clock (c + 1) t2)` SUBST1_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_Var 0; bvi_Call 0 (SOME ListLength_location)
                   [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE],
                 CONS (adjust_bv b2 a0) E,bvi_inc_clock (c + 1) (t2:(C,FFI)bvi_state)) =
                (Rval [adjust_bv b2 a0; bvl_Number (&(LENGTH (a':bvl_v list)))],t2)`
    ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ListLength_location`; `[bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []]`;
                   `CONS (adjust_bv b2 a0) E`; `t2:(C,FFI)bvi_state`;
                   `[adjust_bv b2 a0; bvl_Number (&0)]`; `SND ListLength_code`; `c:num`;
                   `[bvl_Number (&(LENGTH (a':bvl_v list)))]`; `t2:(C,FFI)bvi_state`]
      B2BP2AUX_call_stub) THEN
    ASM_REWRITE_TAC[B2BP2AUX_eval_Var0_Const0; LENGTH; ARITH_RULE `SUC (SUC 0) = 2`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[HD];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[v_to_list_adjust; OPTION_MAP_DEF] THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  CASE_REWRITE_TAC[LENGTH_MAP; adjust_bv_def]);;

(* HOL4 line 2557: Cases_on `op = MemOp ToListByte` *)
let B2BP2AUX_opv_ToListByte = prove
 (B2BP2AUX_opv `MemOp ToListByte`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL; adjust_bv_def]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[MAP; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:bvi_exp` (X_CHOOSE_THEN `tl:bvi_exp list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  B2BP2AUX_TRANSFER_REFS_TAC `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_stubs) THEN
  MP_TAC(ISPECL [`a1'':byte list`; `[]:byte list`; `(b2:num->num) a1'`; `t2:(C,FFI)bvi_state`;
                 `a0'':bool`; `a0':bool`] evaluate_ToListByte_code) THEN
  ASM_REWRITE_TAC[APPEND_NIL; MAP] THEN DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  MAP_EVERY EXISTS_TAC [`c + 1`; `t2:(C,FFI)bvi_state`; `b2:num->num`] THEN
  REWRITE_TAC[bvl_to_bvi_compile_op_def; NULL; NOT_CONS_NIL] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  SUBGOAL_THEN `bvi_evaluate ([d],E,bvi_inc_clock (c + 1) (t0:(C,FFI)bvi_state)) =
                (Rval [bvl_RefPtr a0' ((b2:num->num) a1')],bvi_inc_clock (c + 1) t2)` SUBST1_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_Op (BlockOp (clos_Cons 0)) []; bvi_Op (MemOp LengthByte) [bvi_Var 0];
                   bvi_Var 0], CONS (bvl_RefPtr a0' ((b2:num->num) a1')) E,
                   bvi_inc_clock (c + 1) (t2:(C,FFI)bvi_state)) =
                (Rval [bvl_list_to_v []; bvl_Number (&(LENGTH (a1'':byte list)));
                       bvl_RefPtr a0' (b2 a1')], bvi_inc_clock (c + 1) t2)` ASSUME_TAC THENL
   [REPEAT(CHANGED_TAC(ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
      REWRITE_TAC[B2BP2AUX_eval_Var_CONS; REVERSE; APPEND; HD] THEN CASE_REWRITE_TAC[])) THEN
    REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
    B2BP2AUX_ASM_CASE_TAC[bvi_bvi_to_bvl_refs; bvi_inc_clock_refs; bvl_to_bvi_id; HD;
                          bvl_list_to_v_def; nil_tag_def];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ToListByte_location`; `[bvi_Op (BlockOp (clos_Cons 0)) [];
                   bvi_Op (MemOp LengthByte) [bvi_Var 0]; bvi_Var 0]`;
                 `CONS (bvl_RefPtr a0' ((b2:num->num) a1')) E`; `t2:(C,FFI)bvi_state`;
                 `[bvl_list_to_v []; bvl_Number (&(LENGTH (a1'':byte list)));
                   bvl_RefPtr a0' ((b2:num->num) a1')]`; `SND ToListByte_code`; `c:num`]
    B2BP2AUX_call_stub) THEN
  ASM_REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC (SUC 0)) = 3`] THEN
  DISCH_THEN(MP_TAC o SPECL [`[bvl_list_to_v (MAP (\x. bvl_Number (&(val (x:byte)))) a1'')]`;
     `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
        ((b2:num->num) a1',bvl_ByteArray a0'' a1''))) (t2:(C,FFI)bvi_state)`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM list_to_v_adjust; MAP_MAP_o; o_DEF; adjust_bv_def];
    REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC FUPDATE_ELIM THEN
    UNDISCH_TAC `FLOOKUP (bvi_state_refs (t2:(C,FFI)bvi_state)) ((b2:num->num) a1') =
                 SOME (bvl_ByteArray a0'' a1'')` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT; option_INJ]]);;

(* a call whose arguments end in the state inc_clock (c + 1) s *)
let B2BP2AUX_call_stub2 = prove
 (`!loc xs env (s0:(C,FFI)bvi_state) s args body c r s'.
     bvi_evaluate (xs,env,s0) = (Rval args,bvi_inc_clock (c + 1) s) /\
     lookup loc (bvi_state_code s) = SOME (LENGTH args,body) /\
     bvi_evaluate ([body],args,bvi_inc_clock c s) = (Rval r,s')
     ==> bvi_evaluate ([bvi_Call 0 (SOME loc) xs NONE],env,s0) = (Rval r,s')`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[IS_NONE_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_inc_clock_code] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP B2BP2AUX_find_code_lookup th]) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_inc_clock_clock; ARITH_RULE `~(a + c + 1 < 0 + 1)`; ADD_CLAUSES;
              ARITH_RULE `~(a + c + 1 < 1)`] THEN
  SIMP_TAC[bvi_dec_clock_1_inc_clock; ARITH_RULE `~(c + 1 = 0)`; ADD_SUB] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let B2BP2AUX_inc_clock_refs_fupd = prove
 (`!c f (t:(C,FFI)bvi_state).
     bvi_state_refs_fupd f (bvi_inc_clock c t) = bvi_inc_clock c (bvi_state_refs_fupd f t)`,
  REWRITE_TAC[bvi_inc_clock_def; bvi_state_component_equality; bvi_state_INFO.ri_accfupds;
              K_THM]);;

(* HOL4 line 3146: Cases_on `?str. op = MemOp FromListByte` *)
let B2BP2AUX_opv_FromListByte = prove
 (B2BP2AUX_opv `MemOp FromListByte`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BASICAUX_some_SOME) THEN BETA_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[MAP; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:bvi_exp` (X_CHOOSE_THEN `tl:bvi_exp list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_stubs) THEN
  B2BP2AUX_FRESH_TAC THEN
  SUBGOAL_THEN `bvl_v_to_list (adjust_bv b2 a0) = SOME (MAP (bvl_Number o int_of_num) a')`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[v_to_list_adjust; OPTION_MAP_DEF; option_INJ; MAP_MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM; adjust_bv_def];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`adjust_bv b2 a0`; `MAP (bvl_Number o int_of_num) a'`; `0`; `t2:(C,FFI)bvi_state`]
    evaluate_ListLength_code) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LENGTH_MAP] THEN DISCH_THEN(X_CHOOSE_TAC `cl:num`) THEN
  ABBREV_TAC `bs = REPLICATE (LENGTH (a':num list)) (iword (&0):byte)` THEN
  ABBREV_TAC `t2' = bvi_state_refs_fupd (K (bvi_state_refs t2 |+ (y,bvl_ByteArray T bs)))
                      (t2:(C,FFI)bvi_state)` THEN
  MP_TAC(ISPECL [`adjust_bv b2 a0`; `a':num list`; `0`; `bs:byte list`; `t2':(C,FFI)bvi_state`;
                 `y:num`; `T`; `T`] evaluate_FromListByte_code) THEN
  MAP_EVERY EXPAND_TAC ["t2'"; "bs"] THEN
  ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_REPLICATE; LE_REFL;
                  SUB_REFL] THEN
  DISCH_THEN(X_CHOOSE_TAC `cf:num`) THEN
  MAP_EVERY EXISTS_TAC [`(cl + 1) + (cf + 1)`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       (y,bvl_ByteArray T (MAP word (a':num list))))) (t2:(C,FFI)bvi_state)`;
    `((x:num) =+ (y:num)) b2`] THEN
  REWRITE_TAC[bvl_to_bvi_compile_op_def; NULL; NOT_CONS_NIL] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  SUBGOAL_THEN `bvi_evaluate ([d],E,bvi_inc_clock ((cl + 1) + (cf + 1)) (t0:(C,FFI)bvi_state)) =
                (Rval [adjust_bv b2 a0],bvi_inc_clock ((cl + 1) + (cf + 1)) t2)` SUBST1_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_Op (MemOp (RefByte T))
                   [bvi_Op (IntOp (clos_Const (&0))) [];
                    bvi_Call 0 (SOME ListLength_location)
                      [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]],
                 CONS (adjust_bv b2 a0) E,
                 bvi_inc_clock ((cl + 1) + (cf + 1)) (t2:(C,FFI)bvi_state)) =
                (Rval [bvl_RefPtr T y],bvi_inc_clock (cf + 1) t2')` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
    REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ListLength_location`; `[bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []]`;
                   `CONS (adjust_bv b2 a0) E`; `bvi_inc_clock (cf + 1) (t2:(C,FFI)bvi_state)`;
                   `[adjust_bv b2 a0; bvl_Number (&0)]`; `SND ListLength_code`; `cl:num`;
                   `[bvl_Number (&(LENGTH (a':num list)))]`;
                   `bvi_inc_clock (cf + 1) (t2:(C,FFI)bvi_state)`]
      B2BP2AUX_call_stub) THEN
    REWRITE_TAC[inc_clock_ADD; B2BP2AUX_eval_Var0_Const0; LENGTH; bvi_inc_clock_code] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC (SUC 0) = 2`] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `bvi_inc_clock (cl + cf + 1) (t2:(C,FFI)bvi_state) =
                    bvi_inc_clock (cf + 1) (bvi_inc_clock cl t2)` SUBST1_TAC THENL
       [REWRITE_TAC[inc_clock_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
        MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    CASE_REWRITE_TAC[HD; REVERSE; APPEND] THEN
    REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_inc_clock_refs] THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 <= &(LENGTH (a':num list)):int /\ (?w:byte. (&0:int) = &(val w))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[INT_POS] THEN EXISTS_TAC `word 0:byte` THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[B2BP2AUX_inc_clock_refs_fupd] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) [];
                   bvi_Op (MemOp (RefByte T))
                     [bvi_Op (IntOp (clos_Const (&0))) [];
                      bvi_Call 0 (SOME ListLength_location)
                        [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]],
                 CONS (adjust_bv b2 a0) E,
                 bvi_inc_clock ((cl + 1) + (cf + 1)) (t2:(C,FFI)bvi_state)) =
                (Rval [adjust_bv b2 a0; bvl_Number (&0); bvl_RefPtr T y],
                 bvi_inc_clock (cf + 1) t2')` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN
    CASE_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && can (term_match [] `bvi_evaluate ([SND FromListByte_code],xx,yy:(C,FFI)bvi_state)`)
                      (lhs c)
    then MP_TAC(ISPECL [`FromListByte_location`;
     `[bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) [];
       bvi_Op (MemOp (RefByte T))
         [bvi_Op (IntOp (clos_Const (&0))) [];
          bvi_Call 0 (SOME ListLength_location)
            [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]]`;
     `CONS (adjust_bv b2 a0) E`; `bvi_inc_clock ((cl + 1) + (cf + 1)) (t2:(C,FFI)bvi_state)`;
     `t2':(C,FFI)bvi_state`; `[adjust_bv b2 a0; bvl_Number (&0); bvl_RefPtr T y]`;
     `SND FromListByte_code`; `cf:num`; `[bvl_RefPtr T y]`; snd(dest_pair(rhs c))]
     B2BP2AUX_call_stub2) else failwith "") THEN
  ASM_REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC (SUC 0)) = 3`] THEN
  SUBGOAL_THEN `bvi_state_code (t2':(C,FFI)bvi_state) = bvi_state_code (t2:(C,FFI)bvi_state)` SUBST1_TAC THENL
   [EXPAND_TAC "t2'" THEN REWRITE_TAC[bvi_state_INFO.ri_accfupds]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXPAND_TAC "t2'" THEN
  REWRITE_TAC[bvi_state_INFO.ri_fupdfupds; K_o_THM; FUPDATE_EQ; TAKE_0; APPEND;
              adjust_bv_def; APPLY_UPDATE_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_add_bytearray THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* evaluation of argument lists that do not change the state *)
let B2BP2AUX_eval_CONS_pure = prove
 (`!x xs env (s:(C,FFI)bvi_state) v vs.
     bvi_evaluate ([x],env,s) = (Rval [v],s) /\ bvi_evaluate (xs,env,s) = (Rval vs,s)
     ==> bvi_evaluate (CONS x xs,env,s) = (Rval (CONS v vs),s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  B2BP2AUX_ASM_CASE_TAC[HD]);;

let B2BP2AUX_eval_Var_pure = prove
 (`!n env (s:(C,FFI)bvi_state) v.
     n < LENGTH env /\ EL n env = v ==> bvi_evaluate ([bvi_Var n],env,s) = (Rval [v],s)`,
  SIMP_TAC[bvi_evaluate_def]);;

let B2BP2AUX_PURE_ARGS_TAC : tactic =
  REPEAT(FIRST
   [MATCH_ACCEPT_TAC BVLPROPSAUX_bvi_evaluate_Const0;
    MATCH_MP_TAC B2BP2AUX_eval_Var_pure THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `2 = SUC 1 /\ 3 = SUC 2 /\ 4 = SUC 3`; ONE; EL; HD; TL] THEN
    ARITH_TAC;
    REWRITE_TAC[bvi_evaluate_def] THEN NO_TAC;
    MATCH_MP_TAC B2BP2AUX_eval_CONS_pure THEN CONJ_TAC]);;

(* byte arrays of a list of pointers in related states *)
let B2BP2AUX_MAP_FLOOKUP_byteArray = prove
 (`!ps wss b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state).
     bvl_to_bviProof_state_rel b s t /\
     MAP (FLOOKUP (bvl_state_refs s)) ps = MAP (SOME o bvl_ByteArray T) wss
     ==> MAP (FLOOKUP (bvi_state_refs t)) (MAP b ps) = MAP (SOME o bvl_ByteArray T) wss`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL] THEN
  REWRITE_TAC[CONS_11; o_THM] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC state_rel_FLOOKUP_byteArray THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let B2BP2AUX_MAP_FLOOKUP_IN_FDOM = prove
 (`!(f:(A,B)fmap) l (vs:B list) x. MAP (FLOOKUP f) l = MAP SOME vs /\ MEM x l ==> x IN FDOM f`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; MEM; NOT_CONS_NIL; CONS_11] THEN
  REWRITE_TAC[FLOOKUP_DEF] THEN ASM_MESON_TAC[option_DISTINCT; FLOOKUP_DEF]);;

(* HOL4 line 3267: Cases_on `op = MemOp ConcatByteVec` *)
let B2BP2AUX_opv_ConcatByteVec = prove
 (B2BP2AUX_opv `MemOp ConcatByteVec`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BASICAUX_some_SOME) THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `ps:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[MAP; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:bvi_exp` (X_CHOOSE_THEN `tl:bvi_exp list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_stubs) THEN
  B2BP2AUX_FRESH_TAC THEN
  SUBGOAL_THEN `bvl_v_to_list (adjust_bv b2 a0) = SOME (MAP (bvl_RefPtr T) (MAP (b2:num->num) ps))`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[v_to_list_adjust; OPTION_MAP_DEF; option_INJ; MAP_MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM; adjust_bv_def];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ps:num list`; `a':(byte list)list`; `b2:num->num`; `s5:(num#C,FFI)bvl_state`;
                 `t2:(C,FFI)bvi_state`] B2BP2AUX_MAP_FLOOKUP_byteArray) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(MEM y (MAP (b2:num->num) ps))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(y IN FDOM (bvi_state_refs (t2:(C,FFI)bvi_state)))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC B2BP2AUX_MAP_FLOOKUP_IN_FDOM THEN
    EXISTS_TAC `MAP (b2:num->num) ps` THEN
    EXISTS_TAC `MAP (bvl_ByteArray T:byte list->(bvl_v)bvl_ref) (a':(byte list)list)` THEN
    ASM_REWRITE_TAC[GSYM MAP_o];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`adjust_bv b2 a0`; `MAP (b2:num->num) ps`; `a':(byte list)list`; `0`;
                 `t2:(C,FFI)bvi_state`] evaluate_SumListLength_code) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(X_CHOOSE_TAC `cl:num`) THEN
  ABBREV_TAC `bs = REPLICATE (LENGTH (FLAT (a':(byte list)list))) (iword (&0):byte)` THEN
  ABBREV_TAC `t2' = bvi_state_refs_fupd (K (bvi_state_refs t2 |+ (y,bvl_ByteArray T bs)))
                      (t2:(C,FFI)bvi_state)` THEN
  MP_TAC(ISPECL [`adjust_bv b2 a0`; `MAP (b2:num->num) ps`; `a':(byte list)list`;
                 `t2':(C,FFI)bvi_state`; `[]:byte list`; `bs:byte list`; `0`; `y:num`; `T`]
    evaluate_ConcatByte_code) THEN
  MAP_EVERY EXPAND_TAC ["t2'"; "bs"] THEN
  ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_REPLICATE; APPEND;
                  LENGTH] THEN
  ASM_SIMP_TAC[B2BP1AUX_MAP_FLOOKUP_UPDATE; IN_SET_OF_LIST] THEN
  DISCH_THEN(X_CHOOSE_TAC `cf:num`) THEN
  MAP_EVERY EXISTS_TAC [`(cl + 1) + (cf + 1)`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+
       (y,bvl_ByteArray T (FLAT (a':(byte list)list))))) (t2:(C,FFI)bvi_state)`;
    `((x:num) =+ (y:num)) b2`] THEN
  REWRITE_TAC[bvl_to_bvi_compile_op_def; NULL; NOT_CONS_NIL] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  SUBGOAL_THEN `bvi_evaluate ([d],E,bvi_inc_clock ((cl + 1) + (cf + 1)) (t0:(C,FFI)bvi_state)) =
                (Rval [adjust_bv b2 a0],bvi_inc_clock ((cl + 1) + (cf + 1)) t2)` SUBST1_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_Op (MemOp (RefByte T))
                   [bvi_Op (IntOp (clos_Const (&0))) [];
                    bvi_Call 0 (SOME SumListLength_location)
                      [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]],
                 CONS (adjust_bv b2 a0) E,
                 bvi_inc_clock ((cl + 1) + (cf + 1)) (t2:(C,FFI)bvi_state)) =
                (Rval [bvl_RefPtr T y],bvi_inc_clock (cf + 1) t2')` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
    REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`SumListLength_location`; `[bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []]`;
                   `CONS (adjust_bv b2 a0) E`; `bvi_inc_clock (cf + 1) (t2:(C,FFI)bvi_state)`;
                   `[adjust_bv b2 a0; bvl_Number (&0)]`; `SND SumListLength_code`; `cl:num`;
                   `[bvl_Number (&(LENGTH (FLAT (a':(byte list)list))))]`;
                   `bvi_inc_clock (cf + 1) (t2:(C,FFI)bvi_state)`]
      B2BP2AUX_call_stub) THEN
    REWRITE_TAC[inc_clock_ADD; B2BP2AUX_eval_Var0_Const0; LENGTH; bvi_inc_clock_code] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC (SUC 0) = 2`] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `bvi_inc_clock (cl + cf + 1) (t2:(C,FFI)bvi_state) =
                    bvi_inc_clock (cf + 1) (bvi_inc_clock cl t2)` SUBST1_TAC THENL
       [REWRITE_TAC[inc_clock_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
        MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    CASE_REWRITE_TAC[HD; REVERSE; APPEND] THEN
    REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_inc_clock_refs] THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 <= &(LENGTH (FLAT (a':(byte list)list))):int /\ (?w:byte. (&0:int) = &(val w))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[INT_POS] THEN EXISTS_TAC `word 0:byte` THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[B2BP2AUX_inc_clock_refs_fupd] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_evaluate ([bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) [];
                   bvi_Op (MemOp (RefByte T))
                     [bvi_Op (IntOp (clos_Const (&0))) [];
                      bvi_Call 0 (SOME SumListLength_location)
                        [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]],
                 CONS (adjust_bv b2 a0) E,
                 bvi_inc_clock ((cl + 1) + (cf + 1)) (t2:(C,FFI)bvi_state)) =
                (Rval [adjust_bv b2 a0; bvl_Number (&0); bvl_RefPtr T y],
                 bvi_inc_clock (cf + 1) t2')` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN
    CASE_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && can (term_match [] `bvi_evaluate ([SND ConcatByte_code],xx,yy:(C,FFI)bvi_state)`)
                      (lhs c)
    then MP_TAC(ISPECL [`ConcatByte_location`;
     `[bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) [];
       bvi_Op (MemOp (RefByte T))
         [bvi_Op (IntOp (clos_Const (&0))) [];
          bvi_Call 0 (SOME SumListLength_location)
            [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]]`;
     `CONS (adjust_bv b2 a0) E`; `bvi_inc_clock ((cl + 1) + (cf + 1)) (t2:(C,FFI)bvi_state)`;
     `t2':(C,FFI)bvi_state`; `[adjust_bv b2 a0; bvl_Number (&0); bvl_RefPtr T y]`;
     `SND ConcatByte_code`; `cf:num`; `[bvl_RefPtr T y]`; snd(dest_pair(rhs c))]
     B2BP2AUX_call_stub2) else failwith "") THEN
  ASM_REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC (SUC 0)) = 3`] THEN
  SUBGOAL_THEN `bvi_state_code (t2':(C,FFI)bvi_state) = bvi_state_code (t2:(C,FFI)bvi_state)` SUBST1_TAC THENL
   [EXPAND_TAC "t2'" THEN REWRITE_TAC[bvi_state_INFO.ri_accfupds]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXPAND_TAC "t2'" THEN
  REWRITE_TAC[bvi_state_INFO.ri_fupdfupds; K_o_THM; FUPDATE_EQ; TAKE_0; APPEND;
              adjust_bv_def; APPLY_UPDATE_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_add_bytearray THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;


(* copying into a fresh array of the right length (the code of CopyByte T) *)
let B2BP2AUX_copy_array_fresh = prove
 (`!(ws:A list) srcoff len ds x.
     copy_array (ws,srcoff) len NONE = SOME ds
     ==> &0 <= len /\
         copy_array (ws,srcoff) len (SOME (REPLICATE (num_of_int len) x,&0)) = SOME ds`,
  REPEAT GEN_TAC THEN REWRITE_TAC[copy_array_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[I_THM; INT_ADD_LID; INT_LT_REFL; LENGTH_REPLICATE] THEN
  SUBGOAL_THEN `&0 <= (len:int)` ASSUME_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs (len:int) = len` SUBST1_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_REFL; option_INJ; INT_ABS_NUM; NUM_OF_INT_OF_NUM; TAKE_0; APPEND] THEN
  SIMP_TAC[DROP_LENGTH_NIL_rwt; LENGTH_REPLICATE; APPEND_NIL]);;

(* HOL4 line 3451: Cases_on `op = MemOp (CopyByte T)` *)
let B2BP2AUX_opv_CopyByteT = prove
 (B2BP2AUX_opv `MemOp (CopyByte T)`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL; adjust_bv_def]) THEN
  B2BP2AUX_TRANSFER_REFS_TAC `bvl_to_bviProof_state_rel b2 s5 (t2:(C,FFI)bvi_state)` THEN
  B2BP2AUX_FRESH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a1'''':byte list`; `a':int`; `a'':int`; `a'''':byte list`; `iword (&0):byte`]
    B2BP2AUX_copy_array_fresh) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y = (b2:num->num) a1')` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((b2:num->num) a1' IN FDOM (bvi_state_refs (t2:(C,FFI)bvi_state)))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `FLOOKUP (bvi_state_refs (t2:(C,FFI)bvi_state)) ((b2:num->num) a1') =
                 SOME (bvl_ByteArray a0'''' a1'''')` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`0`;
    `bvi_state_refs_fupd (K (bvi_state_refs t2 |+ (y,bvl_ByteArray T a''''))) (t2:(C,FFI)bvi_state)`;
    `((x:num) =+ (y:num)) b2`] THEN
  ASM_REWRITE_TAC[inc_clock_ZERO; bvl_to_bvi_compile_op_def; ARITH_RULE `~(SUC (SUC (SUC 0)) < 3)`] THEN
  CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0; B2BP2AUX_eval_Var_CONS] THEN
  CASE_REWRITE_TAC[HD; REVERSE; APPEND] THEN
  ASM_SIMP_TAC[B2BP2AUX_do_app_RefByte0] THEN CASE_REWRITE_TAC[APPEND] THEN
  ABBREV_TAC `t2a = bvi_state_refs_fupd (K (bvi_state_refs t2 |+
     (y,bvl_ByteArray T (REPLICATE (num_of_int a'') (iword (&0)))))) (t2:(C,FFI)bvi_state)` THEN
  SUBGOAL_THEN `bvi_evaluate
             ([bvi_Op (MemOp (CopyByte F))
               [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0; bvi_Var 1;
                bvi_Var 2; bvi_Var 3]],
              CONS (bvl_RefPtr T y)
              (CONS (bvl_Number a'')
              (CONS (bvl_Number a') (CONS (bvl_RefPtr a0' ((b2:num->num) a1')) E))),
              t2a:(C,FFI)bvi_state) =
            (Rval [bvl_Unit],
             bvi_state_refs_fupd (K (bvi_state_refs t2a |+ (y, bvl_ByteArray T a''''))) t2a)`
    SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
    SUBGOAL_THEN `bvi_evaluate ([bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0; bvi_Var 1;
                    bvi_Var 2; bvi_Var 3],
              CONS (bvl_RefPtr T y)
              (CONS (bvl_Number a'')
              (CONS (bvl_Number a') (CONS (bvl_RefPtr a0' ((b2:num->num) a1')) E))),
              t2a:(C,FFI)bvi_state) =
             (Rval [bvl_Number (&0); bvl_RefPtr T y; bvl_Number a''; bvl_Number a';
                    bvl_RefPtr a0' (b2 a1')],t2a)` SUBST1_TAC THENL
     [B2BP2AUX_PURE_ARGS_TAC; ALL_TAC] THEN
    CASE_REWRITE_TAC[REVERSE; APPEND] THEN
    MP_TAC(ISPECL [`t2a:(C,FFI)bvi_state`; `a0':bool`; `(b2:num->num) a1'`; `a':int`; `a'':int`;
                   `T`; `y:num`; `&0:int`; `a0'''':bool`; `a1'''':byte list`; `T`;
                   `REPLICATE (num_of_int a'') (iword (&0):byte)`; `a'''':byte list`]
      B2BP2AUX_do_app_CopyByteF) THEN
    EXPAND_TAC "t2a" THEN ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_evaluate_def; HD; APPEND; LENGTH; ONE; EL; TL; ARITH_RULE `SUC 0 < SUC (SUC n)`] THEN
  CASE_REWRITE_TAC[HD] THEN
  EXPAND_TAC "t2a" THEN
  REWRITE_TAC[bvi_state_INFO.ri_fupdfupds; bvi_state_INFO.ri_accfupds; K_o_THM; K_THM; FUPDATE_EQ;
              adjust_bv_def; APPLY_UPDATE_THM] THEN
  B2BP2AUX_ASM_CASE_TAC[APPEND; LENGTH; ONE; EL; HD; TL; ARITH_RULE `SUC 0 < SUC (SUC n)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC state_rel_add_bytearray THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* state_rel after AllocGlobal_code (HOL4 inline in the case AllocGlobal) *)
let B2BP2AUX_state_rel_alloc_globals = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) p p1 z extra k.
     bvl_to_bviProof_state_rel b s t /\ bvi_state_global t = SOME p /\
     FLOOKUP (bvi_state_refs t) p =
       SOME (bvl_ValueArray
         (CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals s)))))
            (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b))
                       (bvl_state_globals s))
               (REPLICATE (z - SUC (LENGTH (bvl_state_globals s))) (bvl_Number (&0)))))) /\
     SUC (LENGTH (bvl_state_globals s)) <= z /\
     (~(p1 = p) ==> ~(p1 IN FDOM (bvi_state_refs t))) /\
     LENGTH (bvl_state_globals s) + k + 1 <=
       LENGTH (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b))
                         (bvl_state_globals s))
                 (REPLICATE (z - SUC (LENGTH (bvl_state_globals s))) (bvl_Number (&0)))) +
       extra
     ==> bvl_to_bviProof_state_rel b
           (bvl_state_globals_fupd
              (K (APPEND (bvl_state_globals s) (REPLICATE k NONE))) s)
           (bvi_state_global_fupd (K (SOME p1))
              (bvi_state_refs_fupd
                 (K (bvi_state_refs t |+
                     (p,bvl_ValueArray
                          (CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals s) + k))))
                             (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b))
                                        (bvl_state_globals s))
                                (REPLICATE (z - SUC (LENGTH (bvl_state_globals s)))
                                   (bvl_Number (&0)))))) |+
                     (p1,bvl_ValueArray
                          (APPEND
                             (CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals s) + k))))
                                (APPEND (MAP (the (bvl_Number (&0)) o
                                              OPTION_MAP (adjust_bv b))
                                           (bvl_state_globals s))
                                   (REPLICATE (z - SUC (LENGTH (bvl_state_globals s)))
                                      (bvl_Number (&0)))))
                             (REPLICATE extra (bvl_Number (&0))))))) t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
    (ASSUME `bvi_state_global (t:(C,FFI)bvi_state) = SOME p`) o check (fun th ->
    try let v,b = dest_forall (concl th) in name_of v = "p" && is_imp b with Failure _ -> false)) THEN
  SUBGOAL_THEN `!k'. k' IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))
                     ==> ~((b:num->num) k' = p) /\ ~(b k' = p1)` ASSUME_TAC THENL
   [X_GEN_TAC `k':num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(p IN IMAGE (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))))` THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      ASM_CASES_TAC `p1:num = p` THENL
       [UNDISCH_TAC `~(p IN IMAGE (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))))` THEN
        REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
        UNDISCH_TAC `INJ (b:num->num) (FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state)))
                       (FDOM (bvi_state_refs (t:(C,FFI)bvi_state)))` THEN
        REWRITE_TAC[INJ] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC INJ_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))`;
                          `FDOM (bvi_state_refs (t:(C,FFI)bvi_state))`] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE; SUBSET_REFL] THEN SET_TAC[];
    X_GEN_TAC `k':num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k':num` o check (fun th ->
      try let v,b = dest_forall (concl th) in name_of v = "k" with Failure _ -> false)) THEN
    CASES_ON `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k'` THEN CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `k' IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))` ASSUME_TAC THENL
     [UNDISCH_TAC `FLOOKUP (bvl_state_refs (s:(num#C,FFI)bvl_state)) k' = SOME a` THEN
      REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k':num` o check (fun th ->
      try let v,b = dest_forall (concl th) in name_of v = "k'" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FLOOKUP_UPDATE];
    X_GEN_TAC `p':num` THEN REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      EXISTS_TAC `extra + z:num` THEN
      REWRITE_TAC[FLOOKUP_UPDATE; LENGTH_APPEND; LENGTH_REPLICATE; MAP_APPEND] THEN
      REWRITE_TAC[APPEND; GSYM APPEND_ASSOC; option_INJ; injectivity "bvl_ref"; CONS_11] THEN
      REWRITE_TAC[APPEND_LCANCEL] THEN
      REWRITE_TAC[map_replicate; o_THM; OPTION_MAP_DEF; the_def; REPLICATE_APPEND] THEN
      UNDISCH_TAC `LENGTH (bvl_state_globals (s:(num#C,FFI)bvl_state)) + k + 1 <=
        LENGTH (APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b))
                         (bvl_state_globals s))
                 (REPLICATE (z - SUC (LENGTH (bvl_state_globals s))) (bvl_Number (&0)))) +
        extra` THEN
      UNDISCH_TAC `SUC (LENGTH (bvl_state_globals (s:(num#C,FFI)bvl_state))) <= z` THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE] THEN
      REPEAT STRIP_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN ASM_ARITH_TAC]]);;

(* HOL4 line 2973: Cases_on `op = GlobOp AllocGlobal` *)
let B2BP2AUX_opv_AllocGlobal = prove
 (B2BP2AUX_opv `GlobOp AllocGlobal`,
  B2BP2AUX_OPV_START_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN
  REWRITE_TAC[INT_NOT_LT; GSYM INT_OF_NUM_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[adjust_bv_def]) THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[MAP; LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:bvi_exp` (X_CHOOSE_THEN `tl:bvi_exp list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_stubs) THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`]
    B2BP2AUX_state_rel_global) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t2:(C,FFI)bvi_state`; `p:num`; `LENGTH (bvl_state_globals (s5:(num#C,FFI)bvl_state))`;
    `APPEND (MAP (the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b2))
                (bvl_state_globals (s5:(num#C,FFI)bvl_state)))
        (REPLICATE (z - SUC (LENGTH (bvl_state_globals s5))) (bvl_Number (&0)))`; `k:num`]
    evaluate_AllocGlobal_code) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `extra:num`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(fun th -> let cn = concl th in
    if is_eq cn && free_in `SND AllocGlobal_code` (lhs cn) then
      MAP_EVERY EXISTS_TAC [`c + 1`; snd(dest_pair(rhs cn)); `b2:num->num`] else NO_TAC) THEN
  REWRITE_TAC[adjust_bv_Unit] THEN CONJ_TAC THENL
   [REWRITE_TAC[bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC B2BP2AUX_call_stub2 THEN
    MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `[bvl_Number (&k)]`; `SND AllocGlobal_code`;
                          `c:num`] THEN
    CONJ_TAC THENL [MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LENGTH; GSYM ONE] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC B2BP2AUX_state_rel_alloc_globals THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP]]);;

(* ---- the Install case (HOL4 lines 2294-2424) ---- *)

(* the names installed by Install are new in the bvi code *)
let B2BP2AUX_install_disjoint = prove
 (`!(s_code:(num#bvl_exp)spt) (t_code:(num#bvi_exp)spt)
    (co:num->(num#C)#(num#num#bvl_exp)list) next1 cfg0 prog1 next2 prog2.
     bvl_to_bviProof_names_ok s_code t_code co /\
     co 0 = ((next1,cfg0),prog1) /\
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2) /\
     DISJOINT (domain s_code) (set_of_list (MAP FST prog1))
     ==> DISJOINT (domain t_code) (set_of_list (MAP FST prog2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_names_ok_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `bvl_num_stubs` (concl th))) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN
  UNDISCH_TAC `DISJOINT (domain (s_code:(num#bvl_exp)spt)) (set_of_list (MAP FST (prog1:(num#num#bvl_exp)list)))` THEN
  REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`next1:num`; `prog1:(num#num#bvl_exp)list`; `next2:num`;
                 `prog2:(num#num#bvi_exp)list`; `x:num`] compile_inc_next_range) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th -> free_in `bvl_num_stubs` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* names_ok after Install *)
let B2BP2AUX_names_ok_install = prove
 (`!(s_code:(num#bvl_exp)spt) (t_code:(num#bvi_exp)spt)
    (co:num->(num#C)#(num#num#bvl_exp)list) next1 cfg0 prog1 next2 prog2.
     bvl_to_bviProof_names_ok s_code t_code co /\
     co 0 = ((next1,cfg0),prog1) /\ FST (FST (co 1)) = next2 /\
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2)
     ==> bvl_to_bviProof_names_ok (union s_code (fromAList prog1))
           (union t_code (fromAList prog2)) (shift_seq 1 co)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_to_bviProof_names_ok_def; LET_DEF; LET_END_DEF; shift_seq_def] THEN
  BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `bvl_num_stubs` (concl th))) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN
  REWRITE_TAC[domain_union; domain_fromAList; IN_UNION; IN_SET_OF_LIST] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`next1:num`; `prog1:(num#num#bvl_exp)list`; `next2:num`;
                   `prog2:(num#num#bvi_exp)list`] compile_inc_next) THEN
    ASM_REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN ARITH_TAC;
    MP_TAC(ISPECL [`next1:num`; `prog1:(num#num#bvl_exp)list`; `next2:num`;
                   `prog2:(num#num#bvi_exp)list`; `x:num`] compile_inc_next_range) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* the code relation of state_rel after Install *)
let B2BP2AUX_install_code_rel = prove
 (CASE_TERM
  `!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) next1 cfg0 prog1 next2 prog2.
     bvl_to_bviProof_state_rel b s t /\
     bvl_state_compile_oracle s 0 = ((next1,cfg0),prog1) /\
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2) /\
     DISJOINT (domain (bvi_state_code t)) (set_of_list (MAP FST prog2)) /\
     ALL_DISTINCT (MAP FST prog2)
     ==> !name arity exp.
           lookup name (union (bvl_state_code s) (fromAList prog1)) = SOME (arity,exp)
           ==> ?n. let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [exp] in
                     lookup (bvl_num_stubs + bvl_to_bvi_namespaces * name)
                       (union (bvi_state_code t) (fromAList prog2)) =
                       SOME (arity,bvi_let_compile_exp (HD c1)) /\
                     aux_code_installed (append aux1)
                       (union (bvi_state_code t) (fromAList prog2)) /\
                     handle_ok [exp]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union] THEN
  ASM_CASES_TAC `lookup name (bvl_state_code (s:(num#C,FFI)bvl_state)) = NONE` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM IS_SOME_EQ_NOT_NONE; IS_SOME_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_TAC `v:num#bvl_exp`) THEN
    ASM_REWRITE_TAC[option_CASE; option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `bvl_to_bviProof_state_rel b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state)` THEN
    REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`name:num`; `arity:num`; `exp:bvl_exp`] o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_exps n [exp]` "c1" "p" THEN
    B2BP2AUX_PAIR_TAC `p:(num#num#bvi_exp)app_list#num` "aux1" "n1" THEN
    CASE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
    MATCH_MP_TAC aux_code_installed_subspt THEN EXISTS_TAC `bvi_state_code (t:(C,FFI)bvi_state)` THEN
    ASM_REWRITE_TAC[subspt_union]] THEN
  ASM_REWRITE_TAC[option_CASE; lookup_fromAList] THEN DISCH_TAC THEN
  UNDISCH_TAC `bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2)` THEN
  REWRITE_TAC[bvl_to_bvi_compile_inc_def] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list next1 (prog1:(num#num#bvl_exp)list)` "code" "n2" THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPECL [`next1:num`; `prog1:(num#num#bvl_exp)list`; `code:(num#num#bvi_exp)app_list`;
                 `n2:num`; `name:num`; `arity:num`; `exp:bvl_exp`] compile_list_imp) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `c:bvi_exp`
    (X_CHOOSE_THEN `aux:(num#num#bvi_exp)app_list` (X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `n0:num` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THEN
  SUBGOAL_THEN `!x. MEM x (MAP FST (append (code:(num#num#bvi_exp)app_list)))
                    ==> lookup x (bvi_state_code (t:(C,FFI)bvi_state)) = NONE` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (domain (bvi_state_code (t:(C,FFI)bvi_state)))
                   (set_of_list (MAP FST (append (code:(num#num#bvi_exp)app_list))))` THEN
    REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; NOT_EXISTS_THM; domain_lookup] THEN
    MESON_TAC[option_nchotomy];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (bvl_num_stubs + bvl_to_bvi_namespaces * name)
                  (MAP FST (append (code:(num#num#bvi_exp)app_list)))` ASSUME_TAC THENL
   [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    EXISTS_TAC `bvl_num_stubs + bvl_to_bvi_namespaces * name` THEN
    EXISTS_TAC `arity:num` THEN EXISTS_TAC `bvi_let_compile_exp c` THEN REWRITE_TAC[FST] THEN
    MATCH_MP_TAC ALOOKUP_MEM THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [RES_TAC THEN ASM_REWRITE_TAC[option_CASE; lookup_fromAList] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC aux_code_installed_subspt THEN
    EXISTS_TAC `fromAList (append (code:(num#num#bvi_exp)app_list))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC aux_code_installed_sublist THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[subspt_lookup; lookup_union] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `lookup x (bvi_state_code (t:(C,FFI)bvi_state)) = NONE` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM IN_SET_OF_LIST; GSYM domain_fromAList] THEN
        REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[option_CASE]]];
    ALL_TAC] THEN
  UNDISCH_TAC `bvl_to_bviProof_state_rel b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def; bvl_to_bviProof_names_ok_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`0`; `(next1:num,cfg0:C)`; `prog1:(num#num#bvl_exp)list`] o
             find (fun th -> can (find_term (fun u -> is_const u && fst(dest_const u) = "ALL"))
                                 (concl th)) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `(name:num,arity:num,exp:bvl_exp)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* state_rel after Install *)
let B2BP2AUX_state_rel_install = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) next1 cfg0 prog1 next2 prog2.
     bvl_to_bviProof_state_rel b s t /\
     bvl_state_compile_oracle s 0 = ((next1,cfg0),prog1) /\
     FST (FST (bvl_state_compile_oracle s 1)) = next2 /\
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2) /\
     DISJOINT (domain (bvi_state_code t)) (set_of_list (MAP FST prog2)) /\
     ALL_DISTINCT (MAP FST prog2)
     ==> bvl_to_bviProof_state_rel b
           (bvl_state_code_fupd (K (union (bvl_state_code s) (fromAList prog1)))
              (bvl_state_compile_oracle_fupd
                 (K (shift_seq 1 (bvl_state_compile_oracle s))) s))
           (bvi_state_code_fupd (K (union (bvi_state_code t) (fromAList prog2)))
              (bvi_state_compile_oracle_fupd
                 (K (shift_seq 1 (bvi_state_compile_oracle t))) t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL B2BP2AUX_install_code_rel) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `bvl_to_bviProof_state_rel b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN STRIP_TAC THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[lookup_union; option_CASE] THEN CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; shift_seq_def; state_co_def]; ALL_TAC] THEN
  MATCH_MP_TAC B2BP2AUX_names_ok_install THEN
  MAP_EVERY EXISTS_TAC [`next1:num`; `cfg0:C`; `next2:num`] THEN ASM_REWRITE_TAC[]);;

let B2BP2AUX_eval_Var1_Const0 = prove
 (`!v w env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Var 1; bvi_Op (IntOp (clos_Const (&0))) []],CONS v (CONS w env),s) =
     (Rval [w; bvl_Number (&0)],s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN CASE_REWRITE_TAC[HD]);;

(* the arguments of the Op Install of compile_op *)
let B2BP2AUX_eval_install_args = prove
 (`!v1 v2 vs1 vs2 env (t:(C,FFI)bvi_state).
     lookup ListLength_location (bvi_state_code t) = SOME (2,SND ListLength_code) /\
     bvl_v_to_list v1 = SOME vs1 /\ bvl_v_to_list v2 = SOME vs2
     ==> ?ck. bvi_evaluate
                ([bvi_Call 0 (SOME ListLength_location)
                    [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE;
                  bvi_Call 0 (SOME ListLength_location)
                    [bvi_Var 1; bvi_Op (IntOp (clos_Const (&0))) []] NONE;
                  bvi_Var 0; bvi_Var 1],CONS v2 (CONS v1 env),bvi_inc_clock ck t) =
              (Rval [bvl_Number (&(LENGTH vs2)); bvl_Number (&(LENGTH vs1)); v2; v1],t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v1:bvl_v`; `vs1:bvl_v list`; `0`; `t:(C,FFI)bvi_state`]
    evaluate_ListLength_code) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(X_CHOOSE_TAC `cB:num`) THEN
  MP_TAC(ISPECL [`v2:bvl_v`; `vs2:bvl_v list`; `0`; `bvi_inc_clock (cB + 1) (t:(C,FFI)bvi_state)`]
    evaluate_ListLength_code) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; bvi_inc_clock_code] THEN DISCH_THEN(X_CHOOSE_TAC `cA:num`) THEN
  EXISTS_TAC `(cA + 1) + (cB + 1)` THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  SUBGOAL_THEN
   `bvi_evaluate ([bvi_Call 0 (SOME ListLength_location)
                    [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE],
                  CONS v2 (CONS v1 env),bvi_inc_clock ((cA + 1) + (cB + 1)) (t:(C,FFI)bvi_state)) =
    (Rval [bvl_Number (&(LENGTH (vs2:bvl_v list)))],bvi_inc_clock (cB + 1) t)` SUBST1_TAC THENL
   [SUBGOAL_THEN `bvi_inc_clock ((cA + 1) + (cB + 1)) (t:(C,FFI)bvi_state) =
                  bvi_inc_clock (cA + 1) (bvi_inc_clock (cB + 1) t)` SUBST1_TAC THENL
     [REWRITE_TAC[inc_clock_ADD]; ALL_TAC] THEN
    MATCH_MP_TAC B2BP2AUX_call_stub THEN
    MAP_EVERY EXISTS_TAC [`[v2; bvl_Number (&0)]`; `SND ListLength_code`] THEN
    ASM_REWRITE_TAC[B2BP2AUX_eval_Var0_Const0; bvi_inc_clock_code; LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `SUC (SUC 0) = 2`];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  SUBGOAL_THEN
   `bvi_evaluate ([bvi_Call 0 (SOME ListLength_location)
                    [bvi_Var 1; bvi_Op (IntOp (clos_Const (&0))) []] NONE],
                  CONS v2 (CONS v1 env),bvi_inc_clock (cB + 1) (t:(C,FFI)bvi_state)) =
    (Rval [bvl_Number (&(LENGTH (vs1:bvl_v list)))],t)` SUBST1_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_call_stub THEN
    MAP_EVERY EXISTS_TAC [`[v1; bvl_Number (&0)]`; `SND ListLength_code`] THEN
    ASM_REWRITE_TAC[B2BP2AUX_eval_Var1_Const0; LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `SUC (SUC 0) = 2`];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN CASE_REWRITE_TAC[HD]);;

(* the first name compiled by compile_inc (HOL4 inline in the Install case) *)
let B2BP2AUX_compile_inc_CONS = prove
 (`!n k arity exp rest n2 prog2.
     bvl_to_bvi_compile_inc n (CONS (k,arity,exp) rest) = (n2,prog2)
     ==> ?e rest2. prog2 = CONS (bvl_num_stubs + bvl_to_bvi_namespaces * k,arity,e) rest2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_to_bvi_compile_inc_def; bvl_to_bvi_compile_list_def;
              bvl_to_bvi_compile_single_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_exps n [exp]` "c" "p" THEN
  B2BP2AUX_PAIR_TAC `p:(num#num#bvi_exp)app_list#num` "aux" "n1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n1 rest` "code2" "n3" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; append_SmartAppend; append_thm; APPEND] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN MESON_TAC[]);;

(* the compile function of a state_cc oracle *)
let B2BP2AUX_state_cc_SOME = prove
 (`!(f:S->P->T#Q) (cc:C->Q->(D#E#G)option) st cfg prog code data cfg'.
     state_cc f cc (st,cfg) prog = SOME (code,data,cfg')
     ==> ?st1 prog1 cfg1. f st prog = (st1,prog1) /\ cc cfg prog1 = SOME (code,data,cfg1) /\
                          cfg' = (st1,cfg1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[state_cc_def] THEN BETA_TAC THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `(f:S->P->T#Q) st prog` "st1" "prog1" THEN CASE_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`st1:T`; `prog1:Q`; `y':G`] THEN
  ASM_REWRITE_TAC[]);;

(* split every free variable of a pair type in the goal and the assumptions *)
let B2BP2AUX_SPLIT_PAIRS_TAC : tactic = fun (asl,w as g) ->
  let fvs = freesl (w :: map (concl o snd) asl) in
  let v = find (fun v -> can B2BP2AUX_dest_pair_ty (type_of v)) fvs in
  let n = fst(dest_var v) in
  let ta,tb = B2BP2AUX_dest_pair_ty (type_of v) in
  (MP_TAC(ISPEC v PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN (mk_var(n^"_1",ta))
     (X_CHOOSE_THEN (mk_var(n^"_2",tb)) SUBST_ALL_TAC))) g;;

(* an Install of the bvl semantics that succeeds *)
let B2BP2AUX_do_install_Rval = prove
 (`!vs (s:(num#C,FFI)bvl_state) v r.
     bvl_do_install vs s = (Rval (v,r):(bvl_v#(num#C,FFI)bvl_state,bvl_v)result)
     ==> ?v1 v2 bytes data next1 cfg0 k arity exp rest next2 cfg1.
           vs = [v1; v2] /\ bvl_v_to_bytes v1 = SOME bytes /\
           bvl_v_to_words v2 = SOME data /\
           bvl_state_compile_oracle s 0 = ((next1,cfg0),CONS (k,arity,exp) rest) /\
           DISJOINT (domain (bvl_state_code s))
             (set_of_list (MAP FST (CONS (k,arity,exp) rest))) /\
           ALL_DISTINCT (MAP FST (CONS (k,arity,exp) rest)) /\
           bvl_state_compile s (next1,cfg0) (CONS (k,arity,exp) rest) =
             SOME (bytes,data,(next2,cfg1)) /\
           FST (bvl_state_compile_oracle s 1) = (next2,cfg1) /\
           v = bvl_CodePtr k /\
           r = bvl_state_code_fupd
                 (K (union (bvl_state_code s) (fromAList (CONS (k,arity,exp) rest))))
                 (bvl_state_compile_oracle_fupd
                    (K (shift_seq 1 (bvl_state_compile_oracle s))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_install_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT B2BP2AUX_SPLIT_PAIRS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND; shift_seq_def; ADD_CLAUSES]) THEN
  REWRITE_TAC[shift_seq_def] THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ASM_MESON_TAC[]);;

let B2BP2AUX_state_rel_oracle = prove
 (`!b (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state).
     bvl_to_bviProof_state_rel b s t
     ==> bvi_state_compile_oracle t =
           state_co bvl_to_bvi_compile_inc (bvl_state_compile_oracle s) /\
         bvl_state_compile s = state_cc bvl_to_bvi_compile_inc (bvi_state_compile t) /\
         bvl_to_bviProof_names_ok (bvl_state_code s) (bvi_state_code t)
           (bvl_state_compile_oracle s)`,
  SIMP_TAC[bvl_to_bviProof_state_rel_def]);;

(* HOL4 line 2294: Cases_on `op = Install` *)
let B2BP2AUX_opv_Install = prove
 (B2BP2AUX_opv `clos_Install`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                              "bvl_do_app" with Failure _ -> false)) THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_do_install_Rval) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SWAP_REVERSE_SYM; REVERSE; APPEND]) THEN
  B2BP2AUX_SUBST_VAR_TAC `a:bvl_v list` THEN B2BP2AUX_SUBST_VAR_TAC `q:bvl_v` THEN
  B2BP2AUX_SUBST_VAR_TAC `r:(num#C,FFI)bvl_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; ALL]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_oracle) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_state_rel_stubs) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                                              "bvl_state_compile" &&
                                              length(snd(strip_comb(lhs(concl th)))) = 3
                                          with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP B2BP2AUX_state_cc_SOME) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `nx2:num` (X_CHOOSE_THEN `prog2:(num#num#bvi_exp)list`
    (X_CHOOSE_THEN `cfg2:C` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `nx2:num`
                                                     with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `cfg2:C`
                                                     with Failure _ -> false)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e2:bvi_exp` (X_CHOOSE_THEN `rest2:(num#num#bvi_exp)list`
    SUBST_ALL_TAC) o MATCH_MP B2BP2AUX_compile_inc_CONS) THEN
  MP_TAC(ISPECL [`bvl_state_code (s5:(num#C,FFI)bvl_state)`; `bvi_state_code (t2:(C,FFI)bvi_state)`;
                 `bvl_state_compile_oracle (s5:(num#C,FFI)bvl_state)`; `next1:num`; `cfg0:C`;
                 `CONS (k:num,arity:num,exp:bvl_exp) rest`; `next2:num`;
                 `CONS (bvl_num_stubs + bvl_to_bvi_namespaces * k,arity:num,e2:bvi_exp) rest2`]
    B2BP2AUX_install_disjoint) THEN
  ASM_REWRITE_TAC[MAP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`next1:num`; `CONS (k:num,arity:num,exp:bvl_exp) rest`; `next2:num`;
                 `CONS (bvl_num_stubs + bvl_to_bvi_namespaces * k,arity:num,e2:bvi_exp) rest2`]
    compile_inc_DISTINCT) THEN
  ASM_REWRITE_TAC[MAP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `bvl_v_to_list v1 = SOME (MAP (bvl_Number o int_of_num o (val:byte->num)) bytes)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `bvl_v_to_bytes v1 = SOME (bytes:byte list)` THEN
    REWRITE_TAC[bvl_v_to_bytes_def] THEN
    DISCH_THEN(MP_TAC o MATCH_MP BASICAUX_some_SOME) THEN BETA_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvl_v_to_list v2 = SOME (MAP bvl_Word64 (data:int64 list))` ASSUME_TAC THENL
   [UNDISCH_TAC `bvl_v_to_words v2 = SOME (data:int64 list)` THEN
    REWRITE_TAC[bvl_v_to_words_def] THEN
    DISCH_THEN(MP_TAC o MATCH_MP BASICAUX_some_SOME) THEN BETA_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`adjust_bv b2 v1`; `adjust_bv b2 v2`;
     `MAP (adjust_bv b2) (MAP (bvl_Number o int_of_num o (val:byte->num)) bytes)`;
     `MAP (adjust_bv b2) (MAP bvl_Word64 (data:int64 list))`; `E:bvl_v list`;
     `t2:(C,FFI)bvi_state`] B2BP2AUX_eval_install_args) THEN
  ASM_REWRITE_TAC[v_to_list_adjust; OPTION_MAP_DEF; LENGTH_MAP] THEN
  DISCH_THEN(X_CHOOSE_TAC `ck:num`) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`;
    `bvi_state_code_fupd (K (union (bvi_state_code t2)
       (fromAList (CONS (bvl_num_stubs + bvl_to_bvi_namespaces * k,arity:num,e2:bvi_exp) rest2))))
       (bvi_state_compile_oracle_fupd (K (shift_seq 1 (bvi_state_compile_oracle t2)))
          (t2:(C,FFI)bvi_state))`; `b2:num->num`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC B2BP2AUX_state_rel_install THEN
    MAP_EVERY EXISTS_TAC [`next1:num`; `cfg0:C`; `next2:num`] THEN
    ASM_REWRITE_TAC[FST; MAP]] THEN
  REWRITE_TAC[bvl_to_bvi_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP bvi_evaluate_IMP_LENGTH o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvi_evaluate" &&
        free_in `c1:bvi_exp list` (lhs(concl th)) with Failure _ -> false)) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  SUBGOAL_THEN `bvi_evaluate (c1,E,bvi_inc_clock ck (t0:(C,FFI)bvi_state)) =
                (Rval [adjust_bv b2 v2; adjust_bv b2 v1],bvi_inc_clock ck t2)` SUBST1_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_c1_clock THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; bvi_do_app_def; bvi_do_install_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bvl_v_to_bytes (adjust_bv b2 v1) = SOME (bytes:byte list)` SUBST1_TAC THENL
   [MATCH_MP_TAC IMP_v_to_bytes THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvl_v_to_words (adjust_bv b2 v2) = SOME (data:int64 list)` SUBST1_TAC THENL
   [MATCH_MP_TAC IMP_v_to_words THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bvi_state_compile_oracle (t2:(C,FFI)bvi_state) 0 =
                (cfg0,CONS (bvl_num_stubs + bvl_to_bvi_namespaces * k,arity:num,e2:bvi_exp) rest2)`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[state_co_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST (shift_seq 1 (bvi_state_compile_oracle (t2:(C,FFI)bvi_state)) 0) = cfg1`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[shift_seq_def; ADD_CLAUSES; FST_state_co; SND];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN ASM_REWRITE_TAC[MAP] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[adjust_bv_def; MAP]);;

(* ---- the remaining operations (HOL4 lines 3500-3518) ---- *)

(* compile_op leaves the other operations alone *)
let B2BP2AUX_compile_op_default = prove
 (`!op c1.
     (!i. ~(op = IntOp (clos_Const i))) /\
     (!n. ~(op = GlobOp (clos_Global n))) /\ (!n. ~(op = GlobOp (SetGlobal n))) /\
     ~(op = GlobOp AllocGlobal) /\ ~(op = clos_Install) /\
     (!n. ~(op = BlockOp (FromList n))) /\ ~(op = MemOp FromListByte) /\
     ~(op = MemOp ToListByte) /\ ~(op = MemOp ConcatByteVec) /\ ~(op = MemOp (CopyByte T)) /\
     (!n. ~(op = clos_Label n)) /\
     (!tag i. ~(op = MemOp (MutCons tag i))) /\ ~(op = MemOp UpdateCons) /\
     ~(op = MemOp FinaliseCons)
     ==> bvl_to_bvi_compile_op op c1 = bvi_Op op c1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_op_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 3504: the operations that compile_op leaves alone *)
let B2BP2AUX_opv_default = prove
 (`!op c1 a (s5:(num#C,FFI)bvl_state) q r b2 (t0:(C,FFI)bvi_state) t2 E.
     (!i. ~(op = IntOp (clos_Const i))) /\ ~(op = MemOp clos_Ref) /\
     (!flag. ~(op = MemOp (RefByte flag))) /\ ~(op = MemOp RefArray) /\
     (!n. ~(op = GlobOp (clos_Global n))) /\ (!n. ~(op = GlobOp (SetGlobal n))) /\
     ~(op = GlobOp AllocGlobal) /\
     ~(op = clos_Install) /\
     (!t. ~(op = clos_ThunkOp t)) /\
     (!n. ~(op = BlockOp (FromList n))) /\ ~(op = MemOp FromListByte) /\
     ~(op = MemOp ToListByte) /\ (!c. ~(op = BlockOp (Build c))) /\ ~(op = MemOp XorByte) /\
     (!b. ~(op = MemOp (CopyByte b))) /\ ~(op = MemOp ConcatByteVec) /\
     (!n. ~(op = clos_Label n)) /\
     (!tag i. ~(op = MemOp (MutCons tag i))) /\ ~(op = MemOp UpdateCons) /\
     ~(op = MemOp FinaliseCons) /\
     bvl_do_app op (REVERSE a) s5 = Rval (q,r) /\
     bvi_evaluate (c1,E,t0) = (Rval (MAP (adjust_bv b2) a),t2) /\
     bvl_to_bviProof_state_rel b2 s5 t2 /\ bvl_to_bviProof_state_ok s5 /\
     ALL (bv_ok (bvl_state_refs s5)) a /\ IS_SOME (bvi_state_global t2)
     ==> ?ck t3 b3.
           bvi_evaluate ([bvl_to_bvi_compile_op op c1],E,bvi_inc_clock ck t0) =
             (Rval [adjust_bv b3 q],t3) /\
           bvl_to_bviProof_state_rel b3 r t3 /\
           (!x. x IN FDOM (bvl_state_refs s5) ==> b3 x = b2 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`; `op:clos_op`;
                 `a:bvl_v list`; `q:bvl_v`; `r:(num#C,FFI)bvl_state`] do_app_adjust) THEN
  ASM_REWRITE_TAC[EVERY_REVERSE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(C,FFI)bvi_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`0`; `t3:(C,FFI)bvi_state`; `b2:num->num`] THEN
  ASM_REWRITE_TAC[inc_clock_ZERO] THEN
  MP_TAC(SPECL [`op:clos_op`; `c1:bvi_exp list`] B2BP2AUX_compile_op_default) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[MAP_REVERSE] THEN CASE_REWRITE_TAC[]);;

(* the operations on which bvlSem do_app is an error (HOL4 lines 2253-2271) *)
let B2BP2AUX_do_app_not_Rval = prove
 (`!vs (s:(num#C,FFI)bvl_state) q r.
     ~(bvl_do_app (clos_ThunkOp ForceThunk) vs s = Rval (q,r)) /\
     (!tag i. ~(bvl_do_app (MemOp (MutCons tag i)) vs s = Rval (q,r))) /\
     ~(bvl_do_app (MemOp UpdateCons) vs s = Rval (q,r)) /\
     ~(bvl_do_app (MemOp FinaliseCons) vs s = Rval (q,r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let B2BP2AUX_NOT_ThunkOp = prove
 (`!op. (!t. ~(op = clos_ThunkOp t)) <=>
        (!m. ~(op = clos_ThunkOp (AllocThunk m))) /\
        (!m. ~(op = clos_ThunkOp (UpdateThunk m))) /\ ~(op = clos_ThunkOp ForceThunk)`,
  MESON_TAC[cases "thunk_op"]);;

let B2BP2AUX_NOT_CopyByte = prove
 (`!op. (!b. ~(op = MemOp (CopyByte b))) <=>
        ~(op = MemOp (CopyByte T)) /\ ~(op = MemOp (CopyByte F))`,
  REWRITE_TAC[FORALL_BOOL_THM]);;

(* the Op case for a value of do_app, all operations (dispatch on op) *)
let B2BP2AUX_op_Rval = prove
 (`!op c1 a (s5:(num#C,FFI)bvl_state) q r b2 (t0:(C,FFI)bvi_state) t2 E.
     bvl_do_app op (REVERSE a) s5 = Rval (q,r) /\
     bvi_evaluate (c1,E,t0) = (Rval (MAP (adjust_bv b2) a),t2) /\
     bvl_to_bviProof_state_rel b2 s5 t2 /\ bvl_to_bviProof_state_ok s5 /\
     ALL (bv_ok (bvl_state_refs s5)) a /\ IS_SOME (bvi_state_global t2)
     ==> ?ck t3 b3.
           bvi_evaluate ([bvl_to_bvi_compile_op op c1],E,bvi_inc_clock ck t0) =
             (Rval [adjust_bv b3 q],t3) /\
           bvl_to_bviProof_state_rel b3 r t3 /\
           (!x. x IN FDOM (bvl_state_refs s5) ==> b3 x = b2 x)`,
  let EX_CASE tm th =
    ASM_CASES_TAC tm THENL
     [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN MATCH_ACCEPT_TAC th; ALL_TAC] in
  let EQ_CASE tm th =
    ASM_CASES_TAC tm THENL [FIRST_X_ASSUM SUBST1_TAC THEN MATCH_ACCEPT_TAC th; ALL_TAC] in
  let NO_CASE tm =
    ASM_CASES_TAC tm THENL
     [FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
      REWRITE_TAC[B2BP2AUX_do_app_not_Rval];
      ALL_TAC] in
  GEN_TAC THEN
  EX_CASE `?i. op = IntOp (clos_Const i)` B2BP2AUX_opv_Const THEN
  EX_CASE `?n. op = clos_Label n` B2BP2AUX_opv_Label THEN
  EX_CASE `?n. op = GlobOp (SetGlobal n)` B2BP2AUX_opv_SetGlobal THEN
  EX_CASE `?n. op = GlobOp (clos_Global n)` B2BP2AUX_opv_Global THEN
  EQ_CASE `op = GlobOp AllocGlobal` B2BP2AUX_opv_AllocGlobal THEN
  EQ_CASE `op = MemOp clos_Ref` B2BP2AUX_opv_Ref THEN
  EQ_CASE `op = MemOp RefArray` B2BP2AUX_opv_RefArray THEN
  EX_CASE `?flag. op = MemOp (RefByte flag)` B2BP2AUX_opv_RefByte THEN
  EX_CASE `?m. op = clos_ThunkOp (AllocThunk m)` B2BP2AUX_opv_AllocThunk THEN
  EX_CASE `?m. op = clos_ThunkOp (UpdateThunk m)` B2BP2AUX_opv_UpdateThunk THEN
  NO_CASE `op = clos_ThunkOp ForceThunk` THEN
  EQ_CASE `op = MemOp XorByte` B2BP2AUX_opv_XorByte THEN
  EQ_CASE `op = MemOp (CopyByte F)` B2BP2AUX_opv_CopyByteF THEN
  EQ_CASE `op = MemOp (CopyByte T)` B2BP2AUX_opv_CopyByteT THEN
  EX_CASE `?parts. op = BlockOp (Build parts)` B2BP2AUX_opv_Build THEN
  EX_CASE `?n. op = BlockOp (FromList n)` B2BP2AUX_opv_FromList THEN
  EQ_CASE `op = MemOp ToListByte` B2BP2AUX_opv_ToListByte THEN
  EQ_CASE `op = MemOp FromListByte` B2BP2AUX_opv_FromListByte THEN
  EQ_CASE `op = MemOp ConcatByteVec` B2BP2AUX_opv_ConcatByteVec THEN
  EQ_CASE `op = clos_Install` B2BP2AUX_opv_Install THEN
  NO_CASE `?tag i. op = MemOp (MutCons tag i)` THEN
  NO_CASE `op = MemOp UpdateCons` THEN
  NO_CASE `op = MemOp FinaliseCons` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC B2BP2AUX_opv_default THEN
  MAP_EVERY EXISTS_TAC [`a:bvl_v list`; `t2:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[B2BP2AUX_NOT_ThunkOp; B2BP2AUX_NOT_CopyByte]);;

(* HOL4 line 2232: Resume compile_exps_correct[Op] *)
let B2BP2AUX_cec_Op = prove
 (`!op xs env (s:(num#C,FFI)bvl_state).
     B2BP2AUX_cec (xs,env,s) ==> B2BP2AUX_cec ([bvl_Op op xs],env,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [B2BP2AUX_cec_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[handle_ok_def] THEN
  B2BP2AUX_PAIR_TAC `bvl_evaluate (xs,env,s:(num#C,FFI)bvl_state)` "res5" "s5" THEN
  REPEAT PAIRARG_TAC THEN
  B2BP2AUX_RESULT_TAC `res5:(bvl_v list,bvl_v)result` "a" "e" THEN CASE_REWRITE_TAC[] THENL
  [ALL_TAC;
   ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   B2BP2AUX_IH_TAC `xs:bvl_exp list` B2BP2AUX_PRV_TAC THEN
   DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
     (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
   ASM_REWRITE_TAC[map_result_def] THEN MATCH_MP_TAC B2BP2AUX_op_err THEN
   FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[map_result_def])] THEN
  CASES_ON `bvl_do_app op (REVERSE a) (s5:(num#C,FFI)bvl_state)` THEN
  CASE_REWRITE_TAC[] THENL
  [B2BP2AUX_PAIR_TAC `a':bvl_v#(num#C,FFI)bvl_state` "q" "r" THEN CASE_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`xs:bvl_exp list`; `env:bvl_v list`; `s:(num#C,FFI)bvl_state`;
                 `a:bvl_v list`; `s5:(num#C,FFI)bvl_state`] B2BP2AUX_bvl_eval_facts_Rval) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  B2BP2AUX_IH_TAC `xs:bvl_exp list` B2BP2AUX_PRV_TAC THEN REWRITE_TAC[map_result_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvi_state` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `ck1:num` STRIP_ASSUME_TAC))) THENL
  [MP_TAC(ISPECL [`c1:bvi_exp list`; `MAP (adjust_bv b2) env`; `ck1:num`; `t1:(C,FFI)bvi_state`;
      `Rval (MAP (adjust_bv b2) a):(bvl_v list,exn_or_ret)result`; `t2:(C,FFI)bvi_state`;
      `append (aux:(num#num#bvi_exp)app_list)`] B2BP2AUX_bvi_eval_mono) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   B2BP2AUX_DRULE_ALL_TAC B2BP2AUX_op_Rval THEN
   DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t3:(C,FFI)bvi_state`
     (X_CHOOSE_THEN `b3:num->num` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`t3:(C,FFI)bvi_state`; `b3:num->num`; `ck + ck1:num`] THEN
   SUBGOAL_THEN `MAP (adjust_bv b2) env = MAP (adjust_bv b3) env` ASSUME_TAC THENL
    [MATCH_MP_TAC B2BP2AUX_MAP_adjust_eq THEN
     EXISTS_TAC `bvl_state_refs (s5:(num#C,FFI)bvl_state)` THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if is_eq (concl th) && can (term_match []
       `bvi_evaluate ([bvl_to_bvi_compile_op op c1],MAP (adjust_bv b2) env,
                      bvi_inc_clock ck (bvi_inc_clock ck1 (t1:(C,FFI)bvi_state)))`) (lhs (concl th))
     then ASSUME_TAC (REWRITE_RULE[inc_clock_ADD] th) else failwith "") THEN
   ASM_REWRITE_TAC[map_result_def; MAP] THEN
   ASM_MESON_TAC[SUBSET];
   SUBGOAL_THEN `~(a' = Rabort Rtype_error:(bvl_v)error_result)` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
     ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`t2:(C,FFI)bvi_state`; `b2:num->num`; `ck1:num`] THEN
   ASM_REWRITE_TAC[map_result_def] THEN
   B2BP2AUX_DRULE_ALL_TAC B2BP2AUX_op_Rerr THEN SIMP_TAC[]]);;

let B2BP2AUX_cec_all = prove
 (`!xs env (s1:(num#C,FFI)bvl_state). B2BP2AUX_cec (xs,env,s1)`,
  MATCH_MP_TAC eval_ind_alt THEN
  REWRITE_TAC[B2BP2AUX_cec_NIL; B2BP2AUX_cec_Var; B2BP2AUX_cec_CONS; B2BP2AUX_cec_If;
              B2BP2AUX_cec_Let; B2BP2AUX_cec_Raise; B2BP2AUX_cec_Op; B2BP2AUX_cec_Handle;
              B2BP2AUX_cec_Force; B2BP2AUX_cec_Tick; B2BP2AUX_cec_Call]);;

(* HOL4 line 2201 (the first evaluate is bvlSem's, the second bviSem's) *)
let bvl_to_bviProof_compile_exps_correct = prove
 (`!xs env s1 n res s2 (t1:(C,FFI)bvi_state) n2 ys aux b1.
     bvl_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     bvl_to_bvi_compile_exps n xs = (ys,aux,n2) /\
     bvl_to_bviProof_state_rel b1 s1 t1 /\
     bvl_to_bviProof_state_ok s1 /\ ALL (bv_ok (bvl_state_refs s1)) env /\
     aux_code_installed (append aux) (bvi_state_code t1) /\
     handle_ok xs /\ IS_SOME (bvi_state_global t1)
     ==> ?t2 b2 c.
           bvi_evaluate (ys,MAP (adjust_bv b2) env,bvi_inc_clock c t1) =
             (map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) res,t2) /\
           bvl_to_bviProof_state_rel b2 s2 t2 /\
           MAP (adjust_bv b1) env = MAP (adjust_bv b2) env /\
           (!a. a IN FDOM (bvl_state_refs s1) ==> b1 a = b2 a)`,
  MATCH_ACCEPT_TAC(REWRITE_RULE[B2BP2AUX_cec_def] B2BP2AUX_cec_all));;

(* ===== the remaining theorems of PART 2 ===== *)

(* HOL4 line 4177 (proved here as an instance of compile_exps_correct) *)
let compile_single_evaluate = prove
 (`!start s1 res s2 b1 (t1:(C,FFI)bvi_state).
     bvl_evaluate ([bvl_Call 0 (SOME start) []],[],s1) = (res,s2) /\
     bvl_to_bviProof_state_rel b1 s1 t1 /\ IS_SOME (bvi_state_global t1) /\
     bvl_to_bviProof_state_ok s1 /\
     ~(res = Rerr (Rabort Rtype_error))
     ==> ?ck b2 t2.
           bvi_evaluate ([bvi_Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * start)) [] NONE],
                         [],bvi_inc_clock ck t1) =
             (map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v)) res,t2) /\
           bvl_to_bviProof_state_rel b2 s2 (t2:(C,FFI)bvi_state)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[bvl_Call 0 (SOME start) []]`; `[]:bvl_v list`; `s1:(num#C,FFI)bvl_state`;
                 `0`; `res:(bvl_v list,bvl_v)result`; `s2:(num#C,FFI)bvl_state`;
                 `t1:(C,FFI)bvi_state`; `0`;
                 `[bvi_Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * start)) [] NONE]`;
                 `Nil:(num#num#bvi_exp)app_list`; `b1:num->num`]
    bvl_to_bviProof_compile_exps_correct) THEN
  ASM_REWRITE_TAC[ALL; MAP; append_thm; aux_code_installed_def; handle_ok_def] THEN
  REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* HOL4 line 4220 [local] *)
let evaluate_REPLICATE_0 = prove
 (`!n env (s:(C,FFI)bvi_state).
     bvi_evaluate (REPLICATE n (bvi_Op (IntOp (clos_Const (&0))) []),env,s) =
     (Rval (REPLICATE n (bvl_Number (&0))),s)`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; bvi_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN ASM_REWRITE_TAC[BVLPROPSAUX_bvi_evaluate_Const0] THEN
  CASE_REWRITE_TAC[HD]);;

(* a call with the handler Var 0 (InitGlobals_code) and one without *)
let B2BP2AUX_call_handler_Var0 = prove
 (CASE_TERM
  `!start env (s:(C,FFI)bvi_state).
     bvi_evaluate ([bvi_Call 0 (SOME start) [] (SOME (bvi_Var 0))],env,s) =
     (let (r,s') = bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],s) in
        ((match r with Rerr (Rraise (Exn v)) -> Rval [v] | _ -> r),s'))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[IS_NONE_DEF; IS_SOME_DEF; bvi_evaluate_def; B2BP2AUX_eval_Var_CONS] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `bvl_find_code (SOME start) ([]:bvl_v list) (bvi_state_code (s:(C,FFI)bvi_state))` THEN
  CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `a:bvl_v list#bvi_exp` "args" "exp" THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_evaluate ([exp],args,bvi_dec_clock (0 + 1) (s:(C,FFI)bvi_state))` "r0" "s0" THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN CASE_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN
  CASE_REWRITE_TAC[bvi_evaluate_def; LENGTH; EL; HD; ARITH_RULE `0 < SUC n`]);;

let B2BP2AUX_minimal_FEMPTY = prove
 (`(minimal ptr. ~(ptr IN FDOM (FEMPTY:(num,A)fmap))) = 0`,
  REWRITE_TAC[FDOM_FEMPTY; NOT_IN_EMPTY] THEN
  MP_TAC(ISPEC `\ptr:num. T` MINIMAL) THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN ARITH_TAC);;

let B2BP2AUX_lookup_stubs = prove
 (`!start kk (code:(num#num#bvi_exp)list).
     lookup InitGlobals_location (fromAList (APPEND (bvl_to_bvi_stubs start kk) code)) =
       SOME (InitGlobals_code start kk)`,
  REWRITE_TAC[lookup_fromAList; ALOOKUP_APPEND; bvl_to_bvi_stubs_def; ALOOKUP_THM;
              AllocGlobal_location_eq; CopyGlobals_location_eq; InitGlobals_location_eq] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[option_CASE]);;

(* a call without arguments and handler never returns Rraise (Ret _) *)
let B2BP2AUX_call_NONE_not_Ret = prove
 (`!loc env (s:(C,FFI)bvi_state) r s' a.
     bvi_evaluate ([bvi_Call 0 (SOME loc) [] NONE],env,s) = (r,s')
     ==> ~(r = Rerr (Rraise (Ret a)))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[IS_NONE_DEF; bvi_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result";
              injectivity "error_result"; distinctness "exn_or_ret"] THEN
  ASM_MESON_TAC[]);;

(* single clauses of bviSem evaluate (for symbolic evaluation without Call) *)
let B2BP2AUX_bvi_clause (c:string) =
  find (fun th -> try let l = lhs(snd(strip_forall(concl th))) in
                      let x = hd(dest_list(fst(dest_pair(rand l)))) in
                      fst(dest_const(fst(strip_comb x))) = c
                  with Failure _ -> false) (CONJUNCTS bvi_evaluate_def);;

let B2BP2AUX_small_num = prove
 (`!m. m <= 10000 ==> small_enough_int (&m)`,
  REWRITE_TAC[small_enough_int_def; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let B2BP2AUX_eval_CONS2 = prove
 (CASE_TERM
  `!x y ys env (s:(C,FFI)bvi_state).
     bvi_evaluate (CONS x (CONS y ys),env,s) =
     match bvi_evaluate ([x],env,s) with
       (Rval v,s2) ->
         (match bvi_evaluate (CONS y ys,env,s2) with
            (Rval vs,s1) -> (Rval (CONS (HD v) vs),s1)
          | t -> t)
     | t -> t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [bvi_evaluate_CONS] THEN REFL_TAC);;

let B2BP2AUX_eval_init_RefArray = prove
 (`!m k cc co code (ffi0:(FFI)ffi_state).
     m <= 10000
     ==> bvi_evaluate ([bvi_Op (MemOp RefArray) [bvi_Op (IntOp (clos_Const (&0))) [];
                                                 bvi_Op (IntOp (clos_Const (&m))) []]],[],
                       bvi_state_REC FEMPTY k NONE cc co code ffi0:(C,FFI)bvi_state) =
         (Rval [bvl_RefPtr T 0],
          bvi_state_REC (FEMPTY |+ (0,bvl_ValueArray (REPLICATE m (bvl_Number (&0)))))
            k NONE cc co code ffi0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP B2BP2AUX_small_num) THEN
  SUBGOAL_THEN `small_enough_int (&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_small_num THEN ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [B2BP2AUX_bvi_clause "bvi_Op"] THEN
  REWRITE_TAC[B2BP2AUX_eval_CONS2] THEN ASM_SIMP_TAC[BVITMCAUX_eval_Const] THEN
  CASE_REWRITE_TAC[HD; REVERSE; APPEND] THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_POS; LET_DEF; LET_END_DEF; bvi_to_bvl_def; bvl_state_INFO.ri_accfupds;
              bvi_state_INFO.ri_accessors; K_THM; B2BP2AUX_minimal_FEMPTY; NUM_OF_INT_OF_NUM] THEN
  BETA_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_to_bvi_def; bvi_state_INFO.ri_fupds; bvl_state_INFO.ri_accfupds; K_THM]);;

let B2BP2AUX_eval_init_Update = prove
 (`!m k cc co code (ffi0:(FFI)ffi_state).
     1 <= m
     ==> bvi_evaluate ([bvi_Op (MemOp Update)
                          [bvi_Op (IntOp (clos_Const (&1))) [];
                           bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0]],[bvl_RefPtr T 0],
                       bvi_state_REC (FEMPTY |+ (0,bvl_ValueArray (REPLICATE m (bvl_Number (&0)))))
                         k NONE cc co code ffi0:(C,FFI)bvi_state) =
         (Rval [bvl_Unit],
          bvi_state_REC (FEMPTY |+ (0,bvl_ValueArray (APPEND [bvl_Number (&1)]
                           (REPLICATE (m - 1) (bvl_Number (&0))))))
            k NONE cc co code ffi0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `small_enough_int (&0) /\ small_enough_int (&1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC B2BP2AUX_small_num THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `REPLICATE m (bvl_Number (&0)) = CONS (bvl_Number (&0)) (REPLICATE (m - 1) (bvl_Number (&0)))`
    SUBST1_TAC THENL
   [UNDISCH_TAC `1 <= m` THEN SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[REPLICATE; SUC_SUB1] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [B2BP2AUX_bvi_clause "bvi_Op"] THEN
  REWRITE_TAC[B2BP2AUX_eval_CONS2] THEN ASM_SIMP_TAC[BVITMCAUX_eval_Const] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[B2BP2AUX_eval_Var_CONS; bvi_evaluate_def; LENGTH; EL; HD; ARITH_RULE `0 < SUC n`] THEN
  CASE_REWRITE_TAC[HD; REVERSE; APPEND] THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_to_bvl_def; bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accessors; K_THM;
              FLOOKUP_UPDATE] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_POS; LENGTH; INT_OF_NUM_LT; LT_0; NUM_OF_INT_OF_NUM; LUPDATE_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_to_bvi_def; bvi_state_INFO.ri_fupds; bvl_state_INFO.ri_accfupds; K_THM;
              FUPDATE_EQ; APPEND]);;

let B2BP2AUX_eval_init_SetGlobalsPtr = prove
 (`!refs k cc co code (ffi0:(FFI)ffi_state).
     bvi_evaluate ([bvi_Op (GlobOp SetGlobalsPtr) [bvi_Var 1]],[bvl_Unit; bvl_RefPtr T 0],
                   bvi_state_REC refs k NONE cc co code ffi0:(C,FFI)bvi_state) =
     (Rval [bvl_Unit],bvi_state_REC refs k (SOME 0) cc co code ffi0)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [B2BP2AUX_bvi_clause "bvi_Op"] THEN
  REWRITE_TAC[B2BP2AUX_eval_Var_CONS] THEN CASE_REWRITE_TAC[HD; REVERSE; APPEND] THEN
  REWRITE_TAC[bvi_do_app_def; distinctness "clos_op"; bvi_do_app_aux_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvi_state_INFO.ri_fupds; K_THM]);;

(* the body of InitGlobals_code up to the call of start *)
let B2BP2AUX_eval_init_body = prove
 (`!m start k cc co code (ffi0:(FFI)ffi_state).
     1 <= m /\ m <= 10000
     ==> bvi_evaluate
           ([bvi_Let [bvi_Op (MemOp RefArray) [bvi_Op (IntOp (clos_Const (&0))) [];
                                               bvi_Op (IntOp (clos_Const (&m))) []]]
               (bvi_Let [bvi_Op (MemOp Update)
                           [bvi_Op (IntOp (clos_Const (&1))) [];
                            bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0]]
                  (bvi_Let [bvi_Op (GlobOp SetGlobalsPtr) [bvi_Var 1]]
                     (bvi_Call 0 (SOME start) [] (SOME (bvi_Var 0)))))],[],
            bvi_state_REC FEMPTY k NONE cc co code ffi0:(C,FFI)bvi_state) =
         bvi_evaluate ([bvi_Call 0 (SOME start) [] (SOME (bvi_Var 0))],
           [bvl_Unit; bvl_Unit; bvl_RefPtr T 0],
           bvi_state_REC (FEMPTY |+ (0,bvl_ValueArray (APPEND [bvl_Number (&1)]
                            (REPLICATE (m - 1) (bvl_Number (&0))))))
             k (SOME 0) cc co code ffi0)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [B2BP2AUX_bvi_clause "bvi_Let"] THEN
  ASM_SIMP_TAC[B2BP2AUX_eval_init_RefArray] THEN CASE_REWRITE_TAC[APPEND] THEN
  GEN_REWRITE_TAC LAND_CONV [B2BP2AUX_bvi_clause "bvi_Let"] THEN
  ASM_SIMP_TAC[B2BP2AUX_eval_init_Update] THEN CASE_REWRITE_TAC[APPEND] THEN
  GEN_REWRITE_TAC LAND_CONV [B2BP2AUX_bvi_clause "bvi_Let"] THEN
  REWRITE_TAC[B2BP2AUX_eval_init_SetGlobalsPtr] THEN CASE_REWRITE_TAC[APPEND]);;

(* case analysis on the free variable of a given type in the goal *)
let B2BP2AUX_CASES_TY_TAC (ty:hol_type) (cth:thm) : tactic = fun (asl,w as g) ->
  let v = find (fun v -> type_of v = ty) (frees w) in
  STRUCT_CASES_TAC (ISPEC v cth) g;;

let B2BP2AUX_eval_NIL = prove
 (`!env (s:(C,FFI)bvi_state). bvi_evaluate ([],env,s) = (Rval [],s)`,
  REWRITE_TAC[bvi_evaluate_def]);;

(* HOL4 line 4230 (cc and co are free in HOL4; the record literal is        *)
(* bvi_state_REC with the fields in declaration order: refs, clock, global,  *)
(* compile, compile_oracle, code, ffi) *)
let bvi_stubs_evaluate = prove
 (CASE_TERM
  `!kk start ffi0 code k cc co.
     0 < k /\ bvl_num_stubs <= start
     ==> let t0 = (bvi_state_REC
                     (FEMPTY |+
                      (0,bvl_ValueArray
                           (APPEND [bvl_Number (&1)]
                              (REPLICATE (MIN (MAX kk 1) InitGlobals_max - 1)
                                 (bvl_Number (&0))))))
                     k (SOME 0) cc co (fromAList (APPEND (bvl_to_bvi_stubs start kk) code))
                     ffi0:(C,FFI)bvi_state) in
         bvi_evaluate ([bvi_Call 0 (SOME InitGlobals_location) [] NONE],[],
                       bvi_initial_state ffi0 (fromAList (APPEND (bvl_to_bvi_stubs start kk) code))
                         co cc (k + 1)) =
         (let (r,s) = bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],t0) in
            ((match r with Rerr (Rraise (Exn v)) -> Rval [v] | _ -> r),s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`start:num`; `kk:num`; `code:(num#num#bvi_exp)list`] B2BP2AUX_lookup_stubs) THEN
  ABBREV_TAC `code' = fromAList (APPEND (bvl_to_bvi_stubs start kk) (code:(num#num#bvi_exp)list))` THEN
  REWRITE_TAC[InitGlobals_code_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ABBREV_TAC `m = MIN (MAX kk 1) InitGlobals_max` THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= m /\ m <= 10000` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[InitGlobals_max_def] THEN ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [B2BP2AUX_bvi_clause "bvi_Call"] THEN
  REWRITE_TAC[IS_NONE_DEF; B2BP2AUX_eval_NIL] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvi_initial_state_def; bvi_state_INFO.ri_accessors] THEN
  REWRITE_TAC[bvl_find_code_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `~(k + 1 < 0 + 1)`; bvi_dec_clock_def; bvi_state_INFO.ri_fupds;
              bvi_state_INFO.ri_accessors; K_THM; ARITH_RULE `(k + 1) - (0 + 1) = k`] THEN
  ASM_SIMP_TAC[B2BP2AUX_eval_init_body] THEN REWRITE_TAC[B2BP2AUX_call_handler_Var0] THEN
  REWRITE_TAC[APPEND] THEN
  B2BP2AUX_PAIR_TAC `bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
      bvi_state_REC (FEMPTY |+ (0,bvl_ValueArray (CONS (bvl_Number (&1))
                      (REPLICATE (m - 1) (bvl_Number (&0))))))
        k (SOME 0) cc co code' ffi0:(C,FFI)bvi_state)` "r" "s1" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP B2BP2AUX_call_NONE_not_Ret) THEN
  CASE_REWRITE_TAC[] THEN
  B2BP2AUX_CASES_TY_TAC `:(bvl_v list,exn_or_ret)result` (cases "result") THEN
  CASE_REWRITE_TAC[] THEN
  B2BP2AUX_CASES_TY_TAC `:(exn_or_ret)error_result` (cases "error_result") THEN
  CASE_REWRITE_TAC[] THEN
  B2BP2AUX_CASES_TY_TAC `:exn_or_ret` (cases "exn_or_ret") THEN
  CASE_REWRITE_TAC[injectivity "result"; injectivity "error_result"; injectivity "exn_or_ret"] THEN
  MESON_TAC[]);;

(* compile_list on a CONS (HOL4 inline in compile_list_distinct_locs) *)
let B2BP2AUX_compile_list_CONS = prove
 (`!n name arity exp prog code_app n'.
     bvl_to_bvi_compile_list n (CONS (name,arity,exp) prog) = (code_app,n')
     ==> ?c aux n1 code2.
           bvl_to_bvi_compile_exps n [exp] = (c,aux,n1) /\
           bvl_to_bvi_compile_list n1 prog = (code2,n') /\
           append code_app =
             CONS (bvl_num_stubs + bvl_to_bvi_namespaces * name,arity,bvi_let_compile_exp (HD c))
               (APPEND (append aux) (append code2))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_to_bvi_compile_list_def; bvl_to_bvi_compile_single_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_exps n [exp]` "c" "p" THEN
  B2BP2AUX_PAIR_TAC `p:(num#num#bvi_exp)app_list#num` "aux" "n1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n1 prog` "code2" "n2" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c:bvi_exp list`; `aux:(num#num#bvi_exp)app_list`; `n1:num`;
                        `code2:(num#num#bvi_exp)app_list`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `code_app:(num#num#bvi_exp)app_list` with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[append_SmartAppend; append_thm; APPEND]);;

let B2BP2AUX_in_ns_name = prove
 (`!k x. in_ns k ((bvl_num_stubs + bvl_to_bvi_namespaces * x) - bvl_num_stubs) <=> k = 0`,
  REWRITE_TAC[ADD_SUB2] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[mult_nss_in_ns]);;

let B2BP2AUX_in_ns_aux = prove
 (`!k x. in_ns k ((bvl_num_stubs + bvl_to_bvi_namespaces * x + 1) - bvl_num_stubs) <=> k = 1`,
  REWRITE_TAC[ADD_SUB2] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[mult_nss_in_ns_1]);;
(* HOL4 line 4281 *)
let compile_list_distinct_locs = prove
 (`!n prog code_app code n'.
     ALL_DISTINCT (MAP FST prog) /\
     bvl_to_bvi_compile_list n prog = (code_app,n') /\
     code = append code_app
     ==> ALL_DISTINCT (MAP FST code) /\
         ALL (between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
                (bvl_num_stubs + bvl_to_bvi_namespaces * n'))
           (FILTER (\n. in_ns 1 (n - bvl_num_stubs)) (MAP FST code)) /\
         FILTER (\n. in_ns 0 (n - bvl_num_stubs)) (MAP FST code) =
           MAP (\n. bvl_num_stubs + bvl_to_bvi_namespaces * n) (MAP FST prog) /\
         ALL ((<=) bvl_num_stubs) (MAP FST code) /\
         ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs)) (MAP FST code) /\
         n <= n'`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_to_bvi_compile_list_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `misc_List [] = (code_app:(num#num#bvi_exp)app_list)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `n:num = n'` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[append_thm; MAP; ALL_DISTINCT; ALL; FILTER; LE_REFL];
    ALL_TAC] THEN
  B2BP2AUX_PAIR_TAC `h:num#num#bvl_exp` "name" "p" THEN
  B2BP2AUX_PAIR_TAC `p:num#bvl_exp` "arity" "exp" THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `code_app:(num#num#bvi_exp)app_list`;
                       `code:(num#num#bvi_exp)list`; `n':num`] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP B2BP2AUX_compile_list_CONS) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:bvi_exp list` (X_CHOOSE_THEN `aux:(num#num#bvi_exp)app_list`
    (X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `code2:(num#num#bvi_exp)app_list`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n1:num`; `code2:(num#num#bvi_exp)app_list`;
    `append (code2:(num#num#bvi_exp)app_list)`; `n':num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exps_aux_sorted o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                         "bvl_to_bvi_compile_exps" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[MAP; MAP_APPEND; FST] THEN
  ABBREV_TAC `A = MAP FST (append (aux:(num#num#bvi_exp)app_list))` THEN
  ABBREV_TAC `B = MAP FST (append (code2:(num#num#bvi_exp)app_list))` THEN
  SUBGOAL_THEN `!x. MEM x A ==> in_ns 1 (x - bvl_num_stubs) /\ bvl_num_stubs <= x /\
                    ~in_ns 0 (x - bvl_num_stubs) /\ ~in_ns 2 (x - bvl_num_stubs) /\
                    ~in_ns 3 (x - bvl_num_stubs) /\
                    bvl_num_stubs + bvl_to_bvi_namespaces * n <= x /\
                    x < bvl_num_stubs + bvl_to_bvi_namespaces * n1` ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `ALL (between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
                   (bvl_num_stubs + bvl_to_bvi_namespaces * n1)) A` THEN
    UNDISCH_TAC `ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1) A` THEN
    REWRITE_TAC[GSYM ALL_MEM; between_def] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `bvl_num_stubs + bvl_to_bvi_namespaces * k + 1`) THEN
    ASM_REWRITE_TAC[B2BP2AUX_in_ns_aux] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. MEM x B ==> bvl_num_stubs <= x /\ ~in_ns 2 (x - bvl_num_stubs) /\
                    ~in_ns 3 (x - bvl_num_stubs) /\
                    (in_ns 1 (x - bvl_num_stubs)
                     ==> bvl_num_stubs + bvl_to_bvi_namespaces * n1 <= x /\
                         x < bvl_num_stubs + bvl_to_bvi_namespaces * n') /\
                    (in_ns 0 (x - bvl_num_stubs)
                     ==> ?q. MEM q (MAP FST (t:(num#num#bvl_exp)list)) /\
                             x = bvl_num_stubs + bvl_to_bvi_namespaces * q)` ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `ALL ((<=) bvl_num_stubs) B` THEN
    UNDISCH_TAC `ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs)) B` THEN
    UNDISCH_TAC `ALL (between (bvl_num_stubs + bvl_to_bvi_namespaces * n1)
                   (bvl_num_stubs + bvl_to_bvi_namespaces * n'))
                   (FILTER (\n. in_ns 1 (n - bvl_num_stubs)) B)` THEN
    UNDISCH_TAC `FILTER (\n. in_ns 0 (n - bvl_num_stubs)) B =
                 MAP (\n. bvl_num_stubs + bvl_to_bvi_namespaces * n)
                   (MAP FST (t:(num#num#bvl_exp)list))` THEN
    REWRITE_TAC[ALL_FILTER; GSYM ALL_MEM; between_def] THEN
    DISCH_THEN(MP_TAC o AP_TERM `MEM (x:num)`) THEN
    REWRITE_TAC[MEM_FILTER; MEM_MAP] THEN BETA_TAC THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `in_ns 0 ((bvl_num_stubs + bvl_to_bvi_namespaces * name) - bvl_num_stubs) /\
                ~in_ns 1 ((bvl_num_stubs + bvl_to_bvi_namespaces * name) - bvl_num_stubs) /\
                ~in_ns 2 ((bvl_num_stubs + bvl_to_bvi_namespaces * name) - bvl_num_stubs) /\
                ~in_ns 3 ((bvl_num_stubs + bvl_to_bvi_namespaces * name) - bvl_num_stubs)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[B2BP2AUX_in_ns_name] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ALL_DISTINCT; ALL_DISTINCT_APPEND; MEM_APPEND; DE_MORGAN_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `bvl_num_stubs + 4 * name` o
        check (fun th -> can (find_term (fun u -> u = `B:num list`)) (concl th) &&
                         is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `name:num = q` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `bvl_num_stubs + 4 * name = bvl_num_stubs + 4 * q` THEN ARITH_TAC;
        ASM_MESON_TAC[]];
      MATCH_MP_TAC(MESON[SORTED_ALL_DISTINCT]
        `!R (ls:num list). irreflexive R /\ transitive R /\ SORTED R ls ==> ALL_DISTINCT ls`) THEN
      EXISTS_TAC `(<):num->num->bool` THEN
      ASM_REWRITE_TAC[irreflexive_DEF; transitive_DEF; LT_REFL] THEN MESON_TAC[LT_TRANS];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `e:num` THEN DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o
        check (fun th -> can (find_term (fun u -> u = `B:num list`)) (concl th) &&
                         is_forall (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:num` o
        check (fun th -> can (find_term (fun u -> u = `A:num list`)) (concl th) &&
                         is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[NOT_LT]];
    REWRITE_TAC[ALL_FILTER; GSYM ALL_MEM; between_def; MEM; MEM_APPEND] THEN BETA_TAC THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `!x a b c. x < a + 4 * b /\ b <= c ==> x < a + 4 * c`;
                  ARITH_RULE `!x a b c. a + 4 * b <= x /\ c <= b ==> a + 4 * c <= x`];
    SUBGOAL_THEN `FILTER (\n. in_ns 0 (n - bvl_num_stubs)) A = []` ASSUME_TAC THENL
     [REWRITE_TAC[FILTER_EQ_NIL; GSYM ALL_MEM] THEN BETA_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[FILTER; FILTER_APPEND; APPEND];
    ASM_REWRITE_TAC[ALL; ALL_APPEND; LE_ADD] THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[ALL; ALL_APPEND] THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    ASM_ARITH_TAC]);;

let B2BP2AUX_num_stubs_eq = prove
 (`bvl_num_stubs = 72`,
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* the locations of the stubs are below bvl_num_stubs *)
let B2BP2AUX_MAP_FST_stubs = prove
 (`!start kk. MAP FST (bvl_to_bvi_stubs start kk) = [62; 63; 64; 65; 66; 67; 68; 69]`,
  REWRITE_TAC[bvl_to_bvi_stubs_def; MAP; AllocGlobal_location_eq; CopyGlobals_location_eq;
              InitGlobals_location_eq; ListLength_location_eq; FromListByte_location_eq;
              ToListByte_location_eq; SumListLength_location_eq; ConcatByte_location_eq]);;


let B2BP2AUX_MOD4_shift = prove
 (`!m. bvl_num_stubs <= m ==> (m - bvl_num_stubs) MOD 4 = m MOD 4`,
  REWRITE_TAC[B2BP2AUX_num_stubs_eq] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m = 18 * 4 + (m - 72)` (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

(* names_ok of the initial states (HOL4 inline in compile_prog_evaluate) *)
let B2BP2AUX_names_ok_init = prove
 (`!start n prog code n1 kk (co:num->(num#C)#(num#num#bvl_exp)list).
     bvl_to_bvi_compile_list n prog = (code,n1) /\ ALL_DISTINCT (MAP FST prog) /\
     (!n. ALL ((\e. handle_ok [e]) o SND o SND) (SND (co n))) /\ n1 <= FST (FST (co 0))
     ==> bvl_to_bviProof_names_ok (fromAList prog)
           (fromAList (APPEND (bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk)
                              (append code))) co`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvl_to_bviProof_names_ok_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `kc:num#C`; `pr:(num#num#bvl_exp)list`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[SND; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `prog:(num#num#bvl_exp)list`; `code:(num#num#bvi_exp)app_list`;
                 `append (code:(num#num#bvi_exp)app_list)`; `n1:num`] compile_list_distinct_locs) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM; ALL_FILTER; between_def] THEN BETA_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[domain_fromAList; IN_SET_OF_LIST; MAP_APPEND; MEM_APPEND; B2BP2AUX_MAP_FST_stubs] THEN
  X_GEN_TAC `m:num` THEN
  REWRITE_TAC[MEM; B2BP2AUX_num_stubs_eq] THEN
  ASM_CASES_TAC `MEM m (MAP FST (append (code:(num#num#bvi_exp)app_list)))` THEN
  ASM_REWRITE_TAC[] THENL [ALL_TAC; ARITH_TAC] THEN
  DISCH_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[in_ns_def; bvl_to_bvi_namespaces_def; B2BP2AUX_num_stubs_eq]) THEN
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
  SUBGOAL_THEN `(m - 72) MOD 4 = m MOD 4` ASSUME_TAC THENL
   [MP_TAC(SPEC `m:num` B2BP2AUX_MOD4_shift) THEN ASM_REWRITE_TAC[B2BP2AUX_num_stubs_eq];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> can (find_term ((=) `1`)) (concl th) &&
      is_forall (concl th))) THEN
    REWRITE_TAC[ASSUME `(m - 72) MOD 4 = m MOD 4`; ASSUME `m MOD 4 = 1`;
                ASSUME `MEM m (MAP FST (append (code:(num#num#bvi_exp)app_list)))`] THEN
    UNDISCH_TAC `n1 <= FST (FST ((co:num->(num#C)#(num#num#bvl_exp)list) 0))` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m MOD 4 = 0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:num`; `4`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MEM (m:num) (FILTER (\n. (n - 72) MOD 4 = 0)
                  (MAP FST (append (code:(num#num#bvi_exp)app_list))))` MP_TAC THENL
   [REWRITE_TAC[MEM_FILTER] THEN BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [MEM_MAP]) THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(72 + 4 * q) - 72 = 4 * q`] THEN
  SIMP_TAC[DIV_MULT; ARITH_RULE `~(4 = 0)`] THEN ASM_REWRITE_TAC[]);;

(* the code relation of the initial states (HOL4 inline in compile_prog_evaluate) *)
let B2BP2AUX_code_rel_init = prove
 (CASE_TERM
  `!start n prog code n1 kk.
     bvl_to_bvi_compile_list n prog = (code,n1) /\ ALL_DISTINCT (MAP FST prog) /\
     handle_ok (MAP (SND o SND) prog)
     ==> !name arity exp.
           lookup name (fromAList prog) = SOME (arity,exp)
           ==> ?n. let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [exp] in
                     lookup (bvl_num_stubs + bvl_to_bvi_namespaces * name)
                       (fromAList (APPEND (bvl_to_bvi_stubs
                          (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk) (append code))) =
                       SOME (arity,bvi_let_compile_exp (HD c1)) /\
                     aux_code_installed (append aux1)
                       (fromAList (APPEND (bvl_to_bvi_stubs
                          (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk) (append code))) /\
                     handle_ok [exp]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lookup_fromAList] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `prog:(num#num#bvl_exp)list`; `code:(num#num#bvi_exp)app_list`;
                 `n1:num`; `name:num`; `arity:num`; `exp:bvl_exp`] compile_list_imp) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `c:bvi_exp`
    (X_CHOOSE_THEN `aux:(num#num#bvi_exp)app_list` (X_CHOOSE_THEN `m1:num` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `n0:num` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD] THEN
  MP_TAC(ISPECL [`n:num`; `prog:(num#num#bvl_exp)list`; `code:(num#num#bvi_exp)app_list`;
                 `append (code:(num#num#bvi_exp)app_list)`; `n1:num`] compile_list_distinct_locs) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk)
                  (bvl_num_stubs + bvl_to_bvi_namespaces * name) = NONE` ASSUME_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE; B2BP2AUX_MAP_FST_stubs; MEM; B2BP2AUX_num_stubs_eq] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (APPEND (bvl_to_bvi_stubs
                  (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk)
                  (append (code:(num#num#bvi_exp)app_list))))` ASSUME_TAC THENL
   [REWRITE_TAC[MAP_APPEND; ALL_DISTINCT_APPEND; B2BP2AUX_MAP_FST_stubs] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ALL_DISTINCT; MEM] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    X_GEN_TAC `e:num` THEN REWRITE_TAC[MEM] THEN DISCH_TAC THEN DISCH_TAC THEN
    RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[B2BP2AUX_num_stubs_eq]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lookup_fromAList; ALOOKUP_APPEND] THEN
    REWRITE_TAC[ASSUME `ALOOKUP (bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk)
                  (bvl_num_stubs + bvl_to_bvi_namespaces * name) = NONE`; option_CASE] THEN
    SUBGOAL_THEN `bvl_num_stubs + bvl_to_bvi_namespaces * name =
                  bvl_to_bvi_namespaces * name + bvl_num_stubs` SUBST1_TAC THENL
     [ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC aux_code_installed_sublist THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IS_SUBLIST (append (code:(num#num#bvi_exp)app_list))
                   (append (aux:(num#num#bvi_exp)app_list))` THEN
    REWRITE_TAC[IS_SUBLIST_DEF] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:(num#num#bvi_exp)list` (X_CHOOSE_THEN `l1:(num#num#bvi_exp)list`
      SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC
      [`APPEND (bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk) l0`;
       `l1:(num#num#bvi_exp)list`] THEN
    REWRITE_TAC[APPEND_ASSOC];
    UNDISCH_TAC `handle_ok (MAP (SND o SND) (prog:(num#num#bvl_exp)list))` THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[handle_ok_EVERY]) THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(name:num,arity:num,exp:bvl_exp)`) THEN
    REWRITE_TAC[SND] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC ALOOKUP_MEM THEN ASM_REWRITE_TAC[]]);;
let B2BP2AUX_state_rel_init = prove
 (CASE_TERM
  `!start n prog code n1 kk (co:num->(num#C)#(num#num#bvl_exp)list)
    (cc:C->(num#num#bvi_exp)list->(byte list#int64 list#C)option) (ffi0:(FFI)ffi_state) k b.
     bvl_to_bvi_compile_list n prog = (code,n1) /\
     ALL_DISTINCT (MAP FST prog) /\
     handle_ok (MAP (SND o SND) prog) /\
     (!n. ALL ((\e. handle_ok [e]) o SND o SND) (SND (co n))) /\
     n1 <= FST (FST (co 0))
     ==> bvl_to_bviProof_state_rel b
           (bvl_initial_state ffi0 (fromAList prog) co (state_cc bvl_to_bvi_compile_inc cc) k)
           (bvi_state_REC
              (FEMPTY |+ (0,bvl_ValueArray (APPEND [bvl_Number (&1)]
                 (REPLICATE (MIN (MAX kk 1) InitGlobals_max - 1) (bvl_Number (&0))))))
              k (SOME 0) cc (state_co bvl_to_bvi_compile_inc co)
              (fromAList (APPEND (bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk)
                                 (append code)))
              ffi0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def; bvl_initial_state_def; bvl_state_INFO.ri_accessors;
              bvi_state_INFO.ri_accessors] THEN
  REWRITE_TAC[FDOM_FEMPTY; INJ; NOT_IN_EMPTY; FLOOKUP_EMPTY; IMAGE_CLAUSES; LENGTH; MAP; APPEND;
              option_INJ; FLOOKUP_UPDATE] THEN CASE_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    EXISTS_TAC `MIN (MAX kk 1) InitGlobals_max` THEN
    REWRITE_TAC[option_INJ; injectivity "bvl_ref"; CONS_11; ONE; InitGlobals_max_def] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `stb = bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk` THEN
  SUBGOAL_THEN
   `lookup AllocGlobal_location (fromAList (APPEND stb (append (code:(num#num#bvi_exp)app_list)))) =
      SOME AllocGlobal_code /\
    lookup CopyGlobals_location (fromAList (APPEND stb (append code))) = SOME CopyGlobals_code /\
    lookup ListLength_location (fromAList (APPEND stb (append code))) = SOME ListLength_code /\
    lookup FromListByte_location (fromAList (APPEND stb (append code))) = SOME FromListByte_code /\
    lookup ToListByte_location (fromAList (APPEND stb (append code))) = SOME ToListByte_code /\
    lookup SumListLength_location (fromAList (APPEND stb (append code))) =
      SOME SumListLength_code /\
    lookup ConcatByte_location (fromAList (APPEND stb (append code))) = SOME ConcatByte_code`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "stb" THEN
    REWRITE_TAC[lookup_fromAList; ALOOKUP_APPEND; bvl_to_bvi_stubs_def; ALOOKUP_THM;
                AllocGlobal_location_eq; CopyGlobals_location_eq;
                InitGlobals_location_eq; ListLength_location_eq; FromListByte_location_eq;
                ToListByte_location_eq; SumListLength_location_eq; ConcatByte_location_eq] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  EXPAND_TAC "stb" THEN CONJ_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_names_ok_init THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `n1:num`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC B2BP2AUX_code_rel_init THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `n1:num`] THEN ASM_REWRITE_TAC[]]);;
(* HOL4 line 4352 *)
let bvl_to_bviProof_compile_prog_evaluate = prove
 (CASE_TERM
  `!start n prog start' prog' n' ffi0 co cc k r s.
     bvl_to_bvi_compile_prog start n prog = (start',prog',n') /\
     bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                   bvl_initial_state ffi0 (fromAList prog) co
                     (state_cc bvl_to_bvi_compile_inc cc) k) = (r,s) /\
     0 < k /\
     ALL_DISTINCT (MAP FST prog) /\
     handle_ok (MAP (SND o SND) prog) /\
     (!n. ALL ((\e. handle_ok [e]) o SND o SND) (SND (co n))) /\
     n' <= FST (FST (co 0)) /\
     ~(r = Rerr (Rabort Rtype_error))
     ==> ?ck b2 s2.
           bvi_evaluate ([bvi_Call 0 (SOME start') [] NONE],[],
                         bvi_initial_state ffi0 (fromAList prog')
                           (state_co bvl_to_bvi_compile_inc co) cc (k + ck)) =
             (map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v))
                (match r with Rerr (Rraise v) -> Rval [v] | _ -> r),s2) /\
           bvl_to_bviProof_state_rel b2 s (s2:(C,FFI)bvi_state)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `bvl_to_bvi_compile_prog start n prog = (start',prog',n')` THEN
  REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n prog` "code" "n1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(rator u)) = "alloc_glob_count"
                                 with Failure _ -> false) w in
     ABBREV_TAC (mk_eq(mk_var("kk",`:num`),t)) g) THEN
  ABBREV_TAC `t1 = bvi_state_REC
    (FEMPTY |+ (0,bvl_ValueArray (APPEND [bvl_Number (&1)]
       (REPLICATE (MIN (MAX kk 1) InitGlobals_max - 1) (bvl_Number (&0))))))
    k (SOME 0) (cc:C->(num#num#bvi_exp)list->(byte list#int64 list#C)option)
    (state_co bvl_to_bvi_compile_inc (co:num->(num#C)#(num#num#bvl_exp)list))
    (fromAList (APPEND (bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) kk)
                       (append (code:(num#num#bvi_exp)app_list))))
    (ffi0:(FFI)ffi_state):(C,FFI)bvi_state` THEN
  MP_TAC(ISPECL [`start:num`;
    `bvl_initial_state ffi0 (fromAList prog) co (state_cc bvl_to_bvi_compile_inc cc) k:
       (num#C,FFI)bvl_state`;
    `r:(bvl_v list,bvl_v)result`; `s:(num#C,FFI)bvl_state`; `I:num->num`;
    `t1:(C,FFI)bvi_state`] compile_single_evaluate) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "t1" THEN MATCH_MP_TAC B2BP2AUX_state_rel_init THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `n1:num`] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "t1" THEN REWRITE_TAC[bvi_state_INFO.ri_accessors; IS_SOME_DEF];
      REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_initial_state_def;
                  bvl_state_INFO.ri_accessors; ALL; FLOOKUP_EMPTY] THEN
      CASE_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck0:num` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `t2:(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`ck0 + 1`; `b2:num->num`; `t2:(C,FFI)bvi_state`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`kk:num`; `bvl_num_stubs + bvl_to_bvi_namespaces * start`;
                 `ffi0:(FFI)ffi_state`; `append (code:(num#num#bvi_exp)app_list)`; `k + ck0:num`;
                 `cc:C->(num#num#bvi_exp)list->(byte list#int64 list#C)option`;
                 `state_co bvl_to_bvi_compile_inc (co:num->(num#C)#(num#num#bvl_exp)list)`]
    bvi_stubs_evaluate) THEN
  ANTS_TAC THENL [UNDISCH_TAC `0 < k` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  SUBGOAL_THEN `k + ck0 + 1 = (k + ck0) + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun u -> u = `t1:(C,FFI)bvi_state`)) (lhs (concl th)))) THEN
  EXPAND_TAC "t1" THEN
  REWRITE_TAC[bvi_inc_clock_def; bvi_state_INFO.ri_fupds; bvi_state_INFO.ri_accessors; K_THM] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_CASES_TY_TAC `:(bvl_v list,bvl_v)result` (cases "result") THEN
  CASE_REWRITE_TAC[map_result_def; map_error_result_def; MAP] THEN
  B2BP2AUX_CASES_TY_TAC `:(bvl_v)error_result` (cases "error_result") THEN
  CASE_REWRITE_TAC[map_result_def; map_error_result_def; MAP]);;

(* ---- the semantics of compile_prog (HOL4 lines 4510-4708) ---- *)

let B2BP2AUX_bvl_inc_initial = prove
 (`!ck (ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvl_exp) list) cc k.
     bvl_inc_clock ck (bvl_initial_state ffi code co cc k) =
     bvl_initial_state ffi code co cc (k + ck)`,
  REWRITE_TAC[bvl_inc_clock_def; bvl_initial_state_def; bvl_state_INFO.ri_accessors;
              bvl_state_INFO.ri_fupds; K_THM]);;

(* runs from an initial state with more clock *)
let B2BP2AUX_bvi_init_mono = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvi_exp) list) cc k1 k2 r1 s1.
     bvi_evaluate (es,env,bvi_initial_state ffi p co cc k1) = (r1,s1) /\
     ~(r1 = Rerr (Rabort Rtimeout_error)) /\ k1 <= k2
     ==> FST (bvi_evaluate (es,env,bvi_initial_state ffi p co cc k2)) = r1 /\
         bvi_state_ffi (SND (bvi_evaluate (es,env,bvi_initial_state ffi p co cc k2))) =
         bvi_state_ffi s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`es:bvi_exp list`; `env:bvl_v list`;
                 `bvi_initial_state ffi p co cc k1:(C,FFI)bvi_state`; `r1:bvi_result`;
                 `s1:(C,FFI)bvi_state`] bvi_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d:num`) THEN
  REWRITE_TAC[BVITAILAUX_inc_initial_state] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FST; SND; bvi_inc_clock_def; bvi_state_INFO.ri_accfupds]);;

let B2BP2AUX_bvl_init_mono = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvl_exp) list) cc k1 k2 r1 s1.
     bvl_evaluate (es,env,bvl_initial_state ffi p co cc k1) = (r1,s1) /\
     ~(r1 = Rerr (Rabort Rtimeout_error)) /\ k1 <= k2
     ==> FST (bvl_evaluate (es,env,bvl_initial_state ffi p co cc k2)) = r1 /\
         bvl_state_ffi (SND (bvl_evaluate (es,env,bvl_initial_state ffi p co cc k2))) =
         bvl_state_ffi s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`es:bvl_exp list`; `env:bvl_v list`; `ffi:(FFI)ffi_state`;
                 `p:(num#bvl_exp)spt`; `co:num -> C # (num#num#bvl_exp) list`;
                 `cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option`;
                 `k1:num`; `r1:(bvl_v list,bvl_v)result`; `s1:(C,FFI)bvl_state`]
                bvl_evaluate_add_clock_initial_state) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FST; SND; bvl_state_INFO.ri_accfupds]);;

let B2BP2AUX_bvl_init_io_mono = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvl_exp) list) cc k1 k2.
     k1 <= k2 ==>
     ffi_state_io_events
       (bvl_state_ffi (SND (bvl_evaluate (es,env,bvl_initial_state ffi p co cc k1)))) <<=
     ffi_state_io_events
       (bvl_state_ffi (SND (bvl_evaluate (es,env,bvl_initial_state ffi p co cc k2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`es:bvl_exp list`; `env:bvl_v list`;
                 `bvl_initial_state ffi p co cc k1:(C,FFI)bvl_state`; `d:num`]
                bvl_evaluate_add_to_clock_io_events_mono) THEN
  REWRITE_TAC[B2BP2AUX_bvl_inc_initial]);;

let B2BP2AUX_bvl_init_io_chain = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvl_exp) list) cc.
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (bvl_state_ffi
          (SND (bvl_evaluate (es,env,bvl_initial_state ffi p co cc k)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[B2BP2AUX_bvl_init_io_mono; LE_CASES]);;

let B2BP2AUX_E1 = `\k. bvl_evaluate ([bvl_Call 0 (SOME start1) []],[]:bvl_v list,
     bvl_initial_state (ffi:(FFI)ffi_state) (p1:(num#bvl_exp)spt)
       (o1:num -> D # (num#num#bvl_exp) list)
       (c1:D->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#D)option) k)`;;
let B2BP2AUX_E2 = `\k. bvi_evaluate ([bvi_Call 0 (SOME start2) [] NONE],[]:bvl_v list,
     bvi_initial_state (ffi:(FFI)ffi_state) (p2:(num#bvi_exp)spt)
       (o2:num -> C # (num#num#bvi_exp) list)
       (c2:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) k)`;;
let B2BP2AUX_e1 k = rhs(concl(BETA_CONV (mk_comb(B2BP2AUX_E1,k))));;
let B2BP2AUX_e2 k = rhs(concl(BETA_CONV (mk_comb(B2BP2AUX_E2,k))));;

(* the run of a program as a pair (r,s) *)
let B2BP2AUX_RUN_TAC (ev:term) (r:term) (x:term) : tactic =
  MP_TAC(ISPEC ev PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [r; x] THEN DISCH_TAC;;

(* the instance of a labelled fact at k, rewritten with the evaluation    *)
(* equations among the assumptions (not ASM_REWRITE_TAC, which would       *)
(* rewrite the instance to T with the labelled fact itself)                *)
let B2BP2AUX_is_ev (t:term) =
  try let c = fst(dest_const(fst(strip_comb t))) in
      c = "bvl_evaluate" || c = "bvi_evaluate"
  with Failure _ -> false;;

let B2BP2AUX_LAB_INST_TAC (lab:string) (k:term) : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> let c = concl th in is_eq c && B2BP2AUX_is_ev (lhs c))
              (map snd asl) in
  USE_THEN lab (fun th -> MP_TAC (REWRITE_RULE (FST :: SND :: evs) (SPEC k th))) g;;

(* the instance of a labelled implication at tms, its antecedent proved by *)
(* rewriting with the assumptions *)
let B2BP2AUX_LAB_MP_TAC (lab:string) (tms:term list) : tactic = fun (asl,w as g) ->
  USE_THEN lab (fun th ->
    let th' = SPECL tms th in
    let ant = lhand (concl th') in
    let ath = EQT_ELIM (REWRITE_CONV (FST :: SND :: injectivity "result" ::
                 injectivity "error_result" :: distinctness "result" :: map snd asl) ant) in
    MP_TAC (MP th' ath)) g;;

(* case analyses of a bvl and a bvi result variable (in all assumptions) *)
let B2BP2AUX_ABORT_CASES_TAC (ab:term) : tactic =
  REPEAT_TCL DISJ_CASES_THEN (fun th -> if is_exists (concl th)
    then X_CHOOSE_THEN (mk_var("f_"^fst(dest_var ab),`:final_event`)) SUBST_ALL_TAC th
    else SUBST_ALL_TAC th) (ISPEC ab (cases "abort"));;

let B2BP2AUX_BVL_RES_CASES_TAC (r:term) : tactic =
  let n = fst(dest_var r) in
  let er = mk_var("er_"^n,`:(bvl_v)error_result`) and ab = mk_var("ab_"^n,`:abort`) in
  DISJ_CASES_THEN2 (X_CHOOSE_THEN (mk_var("v_"^n,`:bvl_v list`)) SUBST_ALL_TAC)
    (X_CHOOSE_THEN er SUBST_ALL_TAC) (ISPEC r (cases "result")) THENL
   [ALL_TAC;
    DISJ_CASES_THEN2 (X_CHOOSE_THEN (mk_var("x_"^n,`:bvl_v`)) SUBST_ALL_TAC)
      (X_CHOOSE_THEN ab SUBST_ALL_TAC) (ISPEC er (cases "error_result")) THENL
     [ALL_TAC; B2BP2AUX_ABORT_CASES_TAC ab]];;

let B2BP2AUX_BVI_RES_CASES_TAC (r:term) : tactic =
  let n = fst(dest_var r) in
  let er = mk_var("er_"^n,`:(exn_or_ret)error_result`) and ab = mk_var("ab_"^n,`:abort`)
  and ex = mk_var("ex_"^n,`:exn_or_ret`) in
  DISJ_CASES_THEN2 (X_CHOOSE_THEN (mk_var("v_"^n,`:bvl_v list`)) SUBST_ALL_TAC)
    (X_CHOOSE_THEN er SUBST_ALL_TAC) (ISPEC r (cases "result")) THENL
   [ALL_TAC;
    DISJ_CASES_THEN2 (X_CHOOSE_THEN ex SUBST_ALL_TAC)
      (X_CHOOSE_THEN ab SUBST_ALL_TAC) (ISPEC er (cases "error_result")) THENL
     [DISJ_CASES_THEN2 (X_CHOOSE_THEN (mk_var("x_"^n,`:bvl_v`)) SUBST_ALL_TAC)
        (X_CHOOSE_THEN (mk_var("y_"^n,`:bvl_v list`)) SUBST_ALL_TAC)
        (ISPEC ex (cases "exn_or_ret"));
      B2BP2AUX_ABORT_CASES_TAC ab]];;

let B2BP2AUX_RES_SIMP_TAC : tactic =
  let ths = [injectivity "result"; injectivity "error_result"; injectivity "abort";
             injectivity "exn_or_ret"; distinctness "result"; distinctness "error_result";
             distinctness "abort"; distinctness "exn_or_ret";
             prove(`!a:A. (?x. a = x) <=> T`, MESON_TAC[])] in
  RULE_ASSUM_TAC(CASE_REWRITE_RULE ths) THEN CASE_REWRITE_TAC ths THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let v,bd = dest_forall(concl th) in let l,_ = dest_imp bd in
    if is_eq l && rand l = v && not (free_in v (lhand l))
    then ASSUME_TAC (REWRITE_RULE[] (SPEC (lhand l) th)) else failwith "")) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> try let v,b = dest_forall (concl th) in
        is_neg b && is_eq (dest_neg b) && rand (dest_neg b) = v with Failure _ -> false)) THEN
      MESON_TAC[]);;

let B2BP2AUX_bvl_sem_Fail = prove
 (`!(ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvl_exp) list) cc start.
     ~(bvl_semantics ffi p co cc start = Fail) ==>
     !k. ~(FST (bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                              bvl_initial_state ffi p co cc k)) = Rerr (Rabort Rtype_error))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the semantics of a bvl program and of a bvi program that simulates it  *)
(* (Rraise of the source is Rval of the target, as with InitGlobals_code) *)
let B2BP2AUX_semantics_sim = prove
 (`!(ffi:(FFI)ffi_state) p1 (o1:num -> D # (num#num#bvl_exp) list) c1 start1
     p2 (o2:num -> C # (num#num#bvi_exp) list) c2 start2.
     (!k r s. bvl_evaluate ([bvl_Call 0 (SOME start1) []],[],
                            bvl_initial_state ffi p1 o1 c1 k) = (r,s) /\
              ~(r = Rerr (Rabort Rtype_error))
        ==> ?ck r2 s2. bvi_evaluate ([bvi_Call 0 (SOME start2) [] NONE],[],
                                     bvi_initial_state ffi p2 o2 c2 (k + ck)) = (r2,s2) /\
                       bvi_state_ffi s2 = bvl_state_ffi s /\
                       (r = Rerr (Rabort Rtimeout_error) ==> r2 = Rerr (Rabort Rtimeout_error)) /\
                       (!e. r = Rerr (Rabort (Rffi_error e)) ==> r2 = Rerr (Rabort (Rffi_error e))) /\
                       ((?v. r = Rval v) \/ (?v. r = Rerr (Rraise v)) ==> ?v. r2 = Rval v)) /\
     ~(bvl_semantics ffi p1 o1 c1 start1 = Fail)
     ==> bvi_semantics ffi p2 o2 c2 start2 = bvl_semantics ffi p1 o1 c1 start1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim") ASSUME_TAC) THEN
  FIRST_ASSUM(LABEL_TAC "oks" o MATCH_MP B2BP2AUX_bvl_sem_Fail) THEN
  let e1 = B2BP2AUX_e1 and e2 = B2BP2AUX_e2 in
  let k = `k:num` in
  let fst1 = `FST:(bvl_v list,bvl_v)result#(D,FFI)bvl_state->(bvl_v list,bvl_v)result` in
  let fst2 = `FST:bvi_result#(C,FFI)bvi_state->bvi_result` in
  let tmo1 = `Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result` in
  let tmo2 = `Rerr (Rabort Rtimeout_error):bvi_result` in
  let r1 = `r1:(bvl_v list,bvl_v)result` and r2 = `r2:bvi_result` in
  let s1 = `s1:(D,FFI)bvl_state` and t2 = `t2:(C,FFI)bvi_state` in
  let mono k k' r x =
    MP_TAC(ISPECL [`[bvi_Call 0 (SOME start2) [] NONE]`; `[]:bvl_v list`; `ffi:(FFI)ffi_state`;
                   `p2:(num#bvi_exp)spt`; `o2:num -> C # (num#num#bvi_exp) list`;
                   `c2:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option`;
                   k; k'; r; x] B2BP2AUX_bvi_init_mono) in
  SUBGOAL_THEN (mk_forall(k, mk_imp(mk_eq(mk_comb(fst1, e1 k), tmo1),
                                    mk_eq(mk_comb(fst2, e2 k), tmo2))))
    (LABEL_TAC "tmo") THENL
   [GEN_TAC THEN B2BP2AUX_RUN_TAC (e1 k) r1 s1 THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "sim" (MP_TAC o SPECL [k; tmo1; s1]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result"; distinctness "abort"];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r3:bvi_result`
      (X_CHOOSE_THEN `t3:(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
    B2BP2AUX_RUN_TAC (e2 k) r2 t2 THEN ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    mono k `k + ck:num` r2 t2 THEN ASM_REWRITE_TAC[LE_ADD; FST] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  let te1 = `Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result` in
  SUBGOAL_THEN
   (mk_forall(k, mk_forall(r2, mk_forall(t2,
      mk_imp(mk_conj(mk_eq(e2 k, mk_pair(r2,t2)), mk_neg(mk_eq(r2, tmo2))),
             list_mk_exists([r1;s1], list_mk_conj[mk_eq(e1 k, mk_pair(r1,s1));
               mk_eq(mk_comb(`bvl_state_ffi:(D,FFI)bvl_state->(FFI)ffi_state`, s1),
                     mk_comb(`bvi_state_ffi:(C,FFI)bvi_state->(FFI)ffi_state`, t2));
               mk_neg(mk_eq(r1,tmo1)); mk_neg(mk_eq(r1,te1));
               `!e. (r1:(bvl_v list,bvl_v)result) = Rerr (Rabort (Rffi_error e))
                    ==> (r2:bvi_result) = Rerr (Rabort (Rffi_error e))`;
               `(?v. (r1:(bvl_v list,bvl_v)result) = Rval v) \/
                (?v. r1 = Rerr (Rraise v)) ==> ?v. (r2:bvi_result) = Rval v`]))))))
    (LABEL_TAC "back") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN B2BP2AUX_RUN_TAC (e1 k) r1 s1 THEN
    SUBGOAL_THEN (mk_neg(mk_eq(r1, tmo1))) ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN B2BP2AUX_LAB_INST_TAC "tmo" k THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_neg(mk_eq(r1, te1))) ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN B2BP2AUX_LAB_INST_TAC "oks" k THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    B2BP2AUX_LAB_MP_TAC "sim" [k; r1; s1] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r3:bvi_result`
      (X_CHOOSE_THEN `t3:(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
    mono k `k + ck:num` r2 t2 THEN ASM_REWRITE_TAC[LE_ADD; FST; SND] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [r1; s1] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  let ev = `ev:exn_or_ret` and tt = `t:(C,FFI)bvi_state` in
  let erre = `Rerr e:bvi_result` in
  SUBGOAL_THEN
   (mk_forall(k, mk_forall(`e:(exn_or_ret)error_result`, mk_forall(tt,
      mk_imp(mk_eq(e2 k, mk_pair(erre,tt)),
             `(e:(exn_or_ret)error_result) = Rabort Rtimeout_error \/
              ?f. e = Rabort (Rffi_error f)`)))))
    (LABEL_TAC "okt") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `e = Rabort Rtimeout_error:(exn_or_ret)error_result` THEN
    ASM_REWRITE_TAC[] THEN
    B2BP2AUX_LAB_MP_TAC "back" [k; erre; tt] THEN
    DISCH_THEN(X_CHOOSE_THEN r1 (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:bvl_v list` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `er:(bvl_v)error_result` SUBST_ALL_TAC)
      (ISPEC r1 (cases "result")) THENL
     [ASM_MESON_TAC[distinctness "result"]; ALL_TAC] THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `v:bvl_v` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)
      (ISPEC `er:(bvl_v)error_result` (cases "error_result")) THENL
     [ASM_MESON_TAC[distinctness "result"]; ALL_TAC] THEN
    REPEAT_TCL DISJ_CASES_THEN (fun th -> if is_exists (concl th)
      then X_CHOOSE_THEN `f:final_event` SUBST_ALL_TAC th else SUBST_ALL_TAC th)
      (ISPEC `ab:abort` (cases "abort")) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_MESON_TAC[injectivity "result"];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_semantics_def; bvl_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN k (X_CHOOSE_THEN `e:(exn_or_ret)error_result`
      STRIP_ASSUME_TAC)) THEN
    B2BP2AUX_RUN_TAC (e2 k) r2 t2 THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      (try fst(dest_const(rator(lhs(concl th)))) = "FST" with Failure _ -> false))) THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    B2BP2AUX_LAB_MP_TAC "okt" [k; `e:(exn_or_ret)error_result`; t2] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN k (fun th -> USE_THEN "oks" (fun oks ->
      MP_TAC (EQ_MP (EQF_INTRO (SPEC k oks)) th)))) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC BASICAUX_option_CASE_cong THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN k (X_CHOOSE_THEN t2
        (X_CHOOSE_THEN r2 (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
      SUBGOAL_THEN (mk_neg(mk_eq(r2, tmo2))) ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      B2BP2AUX_LAB_MP_TAC "back" [k; r2; t2] THEN
      DISCH_THEN(X_CHOOSE_THEN r1 (X_CHOOSE_THEN s1 STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [k; s1; r1; `outcome:outcome`] THEN ASM_REWRITE_TAC[] THEN
      B2BP2AUX_BVL_RES_CASES_TAC r1 THEN B2BP2AUX_BVI_RES_CASES_TAC r2 THEN
      B2BP2AUX_RES_SIMP_TAC;
      DISCH_THEN(X_CHOOSE_THEN k (X_CHOOSE_THEN s1
        (X_CHOOSE_THEN r1 (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
      SUBGOAL_THEN (mk_neg(mk_eq(r1, te1))) ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN B2BP2AUX_LAB_INST_TAC "oks" k THEN REWRITE_TAC[];
        ALL_TAC] THEN
      B2BP2AUX_LAB_MP_TAC "sim" [k; r1; s1] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN r2 (X_CHOOSE_THEN t2
        STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`k + ck:num`; t2; r2; `outcome:outcome`] THEN ASM_REWRITE_TAC[] THEN
      B2BP2AUX_BVL_RES_CASES_TAC r1 THEN B2BP2AUX_BVI_RES_CASES_TAC r2 THEN
      B2BP2AUX_RES_SIMP_TAC];
    DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN
    REWRITE_TAC[B2BP2AUX_bvl_init_io_chain; BVITAILAUX_init_io_chain] THEN
    REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
    let pre = X_GEN_TAC k THEN
      B2BP2AUX_RUN_TAC (e1 k) r1 s1 THEN
      SUBGOAL_THEN (mk_neg(mk_eq(r1, te1))) ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN B2BP2AUX_LAB_INST_TAC "oks" k THEN REWRITE_TAC[];
        ALL_TAC] THEN
      B2BP2AUX_LAB_MP_TAC "sim" [k; r1; s1] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN r2 (X_CHOOSE_THEN t2
        STRIP_ASSUME_TAC))) in
    CONJ_TAC THENL
     [pre THEN EXISTS_TAC k THEN ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; SND] THEN
      MP_TAC(ISPECL [`[bvi_Call 0 (SOME start2) [] NONE]`; `[]:bvl_v list`; `ffi:(FFI)ffi_state`;
                     `p2:(num#bvi_exp)spt`; `o2:num -> C # (num#num#bvi_exp) list`;
                     `c2:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option`;
                     k; `k + ck:num`] BVITAILAUX_init_io_mono) THEN
      ASM_REWRITE_TAC[LE_ADD; SND];
      pre THEN EXISTS_TAC `k + ck:num` THEN
      ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL; SND]]]);;
(* HOL4 line 4510 *)
let bvl_to_bviProof_compile_prog_semantics = prove
 (`!start n prog start' prog' n' (co:num->(num#C)#(num#num#bvl_exp)list)
     (ffi0:(FFI)ffi_state) cc.
     bvl_to_bvi_compile_prog start n prog = (start',prog',n') /\
     ALL_DISTINCT (MAP FST prog) /\
     handle_ok (MAP (SND o SND) prog) /\
     (!n. ALL ((\e. handle_ok [e]) o SND o SND) (SND (co n))) /\
     n' <= FST (FST (co 0)) /\
     ~(bvl_semantics ffi0 (fromAList prog) co (state_cc bvl_to_bvi_compile_inc cc) start = Fail)
     ==> bvi_semantics ffi0 (fromAList prog') (state_co bvl_to_bvi_compile_inc co) cc start' =
         bvl_semantics ffi0 (fromAList prog) co (state_cc bvl_to_bvi_compile_inc cc) start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC B2BP2AUX_semantics_sim THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `r:(bvl_v list,bvl_v)result`; `s:(num#C,FFI)bvl_state`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
      is_eq c && B2BP2AUX_is_ev (lhs c))) THEN
    ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    REWRITE_TAC[bvl_evaluate_def; bvl_initial_state_simp] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[bvl_initial_state_simp] THEN
    STRUCT_CASES_TAC (ISPEC `bvl_find_code (SOME start) ([]:bvl_v list)
      (fromAList (prog:(num#num#bvl_exp)list))` (cases "option")) THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL
     [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
    B2BP2AUX_PAIR_TAC `a:bvl_v list#bvl_exp` "args" "exp" THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `0 < 0 + 1`; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `bvl_to_bvi_compile_prog start n prog = (start',prog',n')` THEN
    REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
    B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n prog` "code" "n1" THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    (fun (asl,w as g) ->
       let init = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) =
                    "bvi_initial_state" with Failure _ -> false) w in
       let init0 = mk_comb(rator init, `0`) in
       MAP_EVERY EXISTS_TAC [`0`; `Rerr (Rabort Rtimeout_error):bvi_result`;
         mk_comb(`bvi_state_clock_fupd (K 0):(C,FFI)bvi_state->(C,FFI)bvi_state`, init0)] g) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [B2BP2AUX_bvi_clause "bvi_Call"] THEN
    REWRITE_TAC[IS_NONE_DEF; B2BP2AUX_eval_NIL] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[bvi_initial_state_simp; bvl_find_code_def; B2BP2AUX_lookup_stubs;
                InitGlobals_code_def; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[LENGTH; ARITH_RULE `0 < 0 + 1`] THEN
    REWRITE_TAC[bvi_state_INFO.ri_accfupds; bvl_state_INFO.ri_accfupds; bvi_initial_state_simp;
                bvl_initial_state_simp; distinctness "result"; injectivity "result";
                distinctness "error_result"; injectivity "error_result"; distinctness "abort"];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`start:num`; `n:num`; `prog:(num#num#bvl_exp)list`; `start':num`;
                 `prog':(num#num#bvi_exp)list`; `n':num`; `ffi0:(FFI)ffi_state`;
                 `co:num->(num#C)#(num#num#bvl_exp)list`;
                 `cc:C->(num#num#bvi_exp)list->(byte list#int64 list#C)option`; `k:num`;
                 `r:(bvl_v list,bvl_v)result`; `s:(num#C,FFI)bvl_state`]
    bvl_to_bviProof_compile_prog_evaluate) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `b2:num->num`
    (X_CHOOSE_THEN `s2:(C,FFI)bvi_state` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `ck:num` THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && B2BP2AUX_is_ev (lhs c) &&
       fst(dest_const(fst(strip_comb(lhs c)))) = "bvi_evaluate"
    then let a,b = dest_pair (rhs c) in MAP_EVERY EXISTS_TAC [a; b] else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
    "bvl_to_bviProof_state_rel" with Failure _ -> false)) THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  B2BP2AUX_BVL_RES_CASES_TAC `r:(bvl_v list,bvl_v)result` THEN
  CASE_REWRITE_TAC[map_result_def; map_error_result_def; injectivity "result";
    injectivity "error_result"; injectivity "abort"; distinctness "result";
    distinctness "error_result"; distinctness "abort"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN MESON_TAC[]);;
(* HOL4 line 4709 *)
let compile_prog_distinct_locs = prove
 (`!start n prog k prog1 n1.
     bvl_to_bvi_compile_prog start n prog = (k,prog1,n1) /\ ALL_DISTINCT (MAP FST prog)
     ==> ALL_DISTINCT (MAP FST prog1) /\
         ALL (between (bvl_to_bvi_namespaces * n + bvl_num_stubs)
                (bvl_to_bvi_namespaces * n1 + bvl_num_stubs))
           (FILTER (\n. in_ns 1 (n - bvl_num_stubs)) (MAP FST prog1)) /\
         ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs)) (MAP FST prog1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n prog` "code" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th))))) THEN
  MP_TAC(ISPECL [`n:num`; `prog:(num#num#bvl_exp)list`; `code:(num#num#bvi_exp)app_list`;
                 `append (code:(num#num#bvi_exp)app_list)`; `m1:num`] compile_list_distinct_locs) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; ALL_FILTER] THEN STRIP_TAC THEN
  REWRITE_TAC[MAP_APPEND; B2BP2AUX_MAP_FST_stubs; ALL_DISTINCT_APPEND; FILTER_APPEND;
              ALL_APPEND; GSYM ALL_MEM; ALL_FILTER; MEM; B2BP2AUX_num_stubs_eq] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[B2BP2AUX_num_stubs_eq]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. MEM x [62; 63; 64; 65; 66; 67; 68; 69] ==> x - 72 = 0` ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MEM_APPEND] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ALL_DISTINCT; MEM] THEN CONV_TAC NUM_REDUCE_CONV;
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `x:num` THEN STRIP_TAC THENL
     [RES_TAC THEN ASM_REWRITE_TAC[in_ns_def; bvl_to_bvi_namespaces_def] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC THEN RES_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_forall (concl th)) &&
        can (find_term (fun u -> try fst(dest_const u) = "between" with Failure _ -> false))
          (concl th))) THEN
      REWRITE_TAC[between_def] THEN ARITH_TAC];
    X_GEN_TAC `x:num` THEN STRIP_TAC THENL
     [RES_TAC THEN ASM_REWRITE_TAC[in_ns_def; bvl_to_bvi_namespaces_def] THEN
      CONV_TAC NUM_REDUCE_CONV;
      RES_TAC THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 4730 [local] *)
let ODD_lemma = prove
 (`!n k. ODD (2 * n + k) <=> ODD k`,
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]);;

(* HOL4 line 4736 (compile_inc limit split cut is bvl_inline's, compile_inc *)
(* of one argument bvl_to_bvi's) *)
let full_cc_def = cake_def
  `full_cc (c:bvl_to_bvi_config) (cc:C->(num#num#bvi_exp)list->(byte list#int64 list#C)option) =
     let limit = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_cc (bvl_inline_compile_inc limit split cut)
         (state_cc bvl_to_bvi_compile_inc
            (state_cc (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c))
               (state_cc (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c))
                  (state_cc bvi_inline_compile_inc cc))))`;;

(* HOL4 line 4747 *)
let full_co_def = cake_def
  `full_co (c:bvl_to_bvi_config)
     (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list) =
     let limit = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_co bvi_inline_compile_inc
         (state_co (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c))
            (state_co (bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c))
               (state_co bvl_to_bvi_compile_inc
                  (state_co (bvl_inline_compile_inc limit split cut) co))))`;;

(* HOL4 line 4759 *)
let bvl_to_bviProof_compile_prog_avoids_nss_2 = prove
 (`!start f prog loc code new_state k.
     bvl_to_bvi_compile_prog start f prog = (loc,code,new_state) /\
     ALL_DISTINCT (MAP FST prog) /\
     k MOD bvl_to_bvi_namespaces = 2 /\ MEM k (MAP FST code)
     ==> k <= bvl_num_stubs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list f prog` "c" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th))))) THEN
  MP_TAC(ISPECL [`f:num`; `prog:(num#num#bvl_exp)list`; `c:(num#num#bvi_exp)app_list`;
                 `append (c:(num#num#bvi_exp)app_list)`; `m1:num`] compile_list_distinct_locs) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "MEM"
                                          with Failure _ -> false)) THEN
  REWRITE_TAC[MAP_APPEND; MEM_APPEND; B2BP2AUX_MAP_FST_stubs; MEM; B2BP2AUX_num_stubs_eq] THEN
  STRIP_TAC THEN TRY(FIRST_X_ASSUM SUBST1_TAC THEN ARITH_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[B2BP2AUX_num_stubs_eq; in_ns_def; bvl_to_bvi_namespaces_def]) THEN
  RES_TAC THEN MP_TAC(SPEC `k:num` B2BP2AUX_MOD4_shift) THEN
  ASM_REWRITE_TAC[B2BP2AUX_num_stubs_eq] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 4780 *)
let compile_prog_avoids_nss_3 = prove
 (`!start f prog loc code new_state k.
     bvl_to_bvi_compile_prog start f prog = (loc,code,new_state) /\
     ALL_DISTINCT (MAP FST prog) /\
     k MOD bvl_to_bvi_namespaces = 3 /\ MEM k (MAP FST code)
     ==> k <= bvl_num_stubs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list f prog` "c" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th))))) THEN
  MP_TAC(ISPECL [`f:num`; `prog:(num#num#bvl_exp)list`; `c:(num#num#bvi_exp)app_list`;
                 `append (c:(num#num#bvi_exp)app_list)`; `m1:num`] compile_list_distinct_locs) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "MEM"
                                          with Failure _ -> false)) THEN
  REWRITE_TAC[MAP_APPEND; MEM_APPEND; B2BP2AUX_MAP_FST_stubs; MEM; B2BP2AUX_num_stubs_eq] THEN
  STRIP_TAC THEN TRY(FIRST_X_ASSUM SUBST1_TAC THEN ARITH_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[B2BP2AUX_num_stubs_eq; in_ns_def; bvl_to_bvi_namespaces_def]) THEN
  RES_TAC THEN MP_TAC(SPEC `k:num` B2BP2AUX_MOD4_shift) THEN
  ASM_REWRITE_TAC[B2BP2AUX_num_stubs_eq] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN ASM_REWRITE_TAC[]);;

(* HOL4 lines 4801-4810: comment (no_mutcons: syntactic absence of MutCons, *)
(* the no_mutcons conjunct of bvi_tmc's input condition)                     *)

(* HOL4 line 4813 [local] *)
let bvi_let_delete_var_no_mutcons = prove
 (`!x. no_mutcons x ==> no_mutcons (bvi_let_delete_var x)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:bvi_exp` (CONJUNCT1 (cases "bvi_exp"))) THEN
  REWRITE_TAC[bvi_let_delete_var_def; no_mutcons_def; no_mutcons_op_def; ALL;
              distinctness "clos_op"]);;

let B2BP2AUX_ALL_BUTLAST_LAST = prove
 (`!(P:A->bool) xs. ~(LENGTH xs = 0) /\ ALL P xs ==> ALL P (BUTLAST xs) /\ P (LAST xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_NIL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
    (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false))) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [GSYM (MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[ALL_APPEND; ALL]);;

let B2BP2AUX_ALL_delete_var = prove
 (`!ys. ALL no_mutcons ys ==> ALL no_mutcons (MAP bvi_let_delete_var ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  ASM_MESON_TAC[bvi_let_delete_var_no_mutcons]);;

(* HOL4 line 4819 [local] *)
let bvi_let_compile_no_mutcons = prove
 (`(!env d e. no_mutcons e ==> no_mutcons (bvi_let_compile_sing env d e)) /\
   (!env d es. ALL no_mutcons es ==> ALL no_mutcons (bvi_let_compile_list env d es))`,
  MATCH_MP_TAC bvi_let_compile_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_let_compile_sing_def; no_mutcons_def; ALL; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN
  (fun (asl,w as g) -> if mem `h:bvi_exp option` (frees w) then
     DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `hh:bvi_exp` SUBST_ALL_TAC)
       (ISPEC `h:bvi_exp option` (cases "option")) g else ALL_TAC g) THEN
  CASE_REWRITE_TAC[option_INJ; option_DISTINCT; no_mutcons_def] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[option_INJ; option_DISTINCT]) THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  ASM_REWRITE_TAC[no_mutcons_def; ALL] THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[B2BP2AUX_ALL_BUTLAST_LAST; B2BP2AUX_ALL_delete_var]);;

(* HOL4 line 4840 [local] *)
let bvi_let_compile_exp_no_mutcons = prove
 (`!x. no_mutcons x ==> no_mutcons (bvi_let_compile_exp x)`,
  REWRITE_TAC[bvi_let_compile_exp_eq] THEN MESON_TAC[bvi_let_compile_no_mutcons]);;

(* HOL4 line 4848 [local,simp] *)
let compile_int_no_mutcons = prove
 (`!i. no_mutcons (compile_int i)`,
  GEN_TAC THEN REWRITE_TAC[compile_int_def; no_mutcons_def; ALL] THEN COND_CASES_TAC THEN
  REWRITE_TAC[no_mutcons_op_def; distinctness "clos_op"]);;

let _ = cake_add_simps [compile_int_no_mutcons];;

(* HOL4 line 4854 [local] *)
let compile_op_no_mutcons = prove
 (`!c1 op. ALL no_mutcons c1 ==> no_mutcons (bvl_to_bvi_compile_op op c1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_op_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  ASM CASE_REWRITE_TAC[no_mutcons_def; ALL; ALL_APPEND; EVERY_REPLICATE; compile_int_no_mutcons;
                  no_mutcons_op_def; distinctness "clos_op"; injectivity "clos_op";
                  distinctness "mem_op"; injectivity "mem_op"; distinctness "glob_op";
                  distinctness "block_op"; distinctness "int_op"]);;

(* HOL4 line 4862 [local] (the list c of the second conjunct is cs) *)
let compile_exps_sing_no_mutcons = prove
 (`(!n e c aux n1.
      compile_exps_sing n e = (c,aux,n1)
      ==> no_mutcons c /\ ALL (no_mutcons o SND o SND) (append aux)) /\
   (!n es cs aux n1.
      compile_exps_list n es = (cs,aux,n1)
      ==> ALL no_mutcons cs /\ ALL (no_mutcons o SND o SND) (append aux))`,
  MATCH_MP_TAC compile_exps_sing_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  RW[compile_exps_sing_def] THEN REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  GVS[compile_aux_def; bvi_let_compile_exp_no_mutcons; compile_op_no_mutcons;
      no_mutcons_op_def; append_thm; append_SmartAppend; ALL_APPEND; ALL; o_THM;
      no_mutcons_def]);;

(* HOL4 line 4878 [local] *)
let compile_exps_no_mutcons = prove
 (`!n xs c aux n1.
     bvl_to_bvi_compile_exps n xs = (c,aux,n1)
     ==> ALL no_mutcons c /\ ALL (no_mutcons o SND o SND) (append aux)`,
  REWRITE_TAC[GSYM (CONJUNCT2 compile_exps_sing)] THEN
  MESON_TAC[CONJUNCT2 compile_exps_sing_no_mutcons]);;

(* HOL4 line 4886 [local] *)
let stubs_no_mutcons = prove
 (`!start n. ALL (no_mutcons o SND o SND) (bvl_to_bvi_stubs start n)`,
  REWRITE_TAC[bvl_to_bvi_stubs_def; AllocGlobal_code_def; CopyGlobals_code_def;
              InitGlobals_code_def; ListLength_code_def; FromListByte_code_def;
              ToListByte_code_def; SumListLength_code_def; ConcatByte_code_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; ALL; o_THM; SND] THEN BETA_TAC THEN
  REWRITE_TAC[no_mutcons_def; ALL; no_mutcons_op_def; distinctness "clos_op";
              injectivity "clos_op"; distinctness "mem_op"] THEN
  CASE_REWRITE_TAC[no_mutcons_def; ALL]);;

(* HOL4 line 4896 [local] *)
let compile_single_no_mutcons = prove
 (`!n p q n1.
     bvl_to_bvi_compile_single n p = (q,n1) ==> ALL (no_mutcons o SND o SND) (append q)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `q2:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `q2:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[compile_single_eq] THEN
  B2BP2AUX_PAIR_TAC `compile_exps_sing n e` "c" "p2" THEN
  B2BP2AUX_PAIR_TAC `p2:(num#num#bvi_exp)app_list#num` "aux" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `q:(num#num#bvi_exp)app_list`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 compile_exps_sing_no_mutcons) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "compile_exps_sing"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[append_SmartAppend; append_thm; APPEND; ALL; o_THM] THEN
  ASM_SIMP_TAC[bvi_let_compile_exp_no_mutcons]);;

(* HOL4 line 4907 [local] *)
let compile_list_no_mutcons = prove
 (`!n progs q n1.
     bvl_to_bvi_compile_list n progs = (q,n1) ==> ALL (no_mutcons o SND o SND) (append q)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_to_bvi_compile_list_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `q:(num#num#bvi_exp)app_list`)) THEN
    REWRITE_TAC[append_thm; ALL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_list_def; LET_DEF; LET_END_DEF] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_single n h` "code1" "m1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list m1 t` "code2" "m2" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `q:(num#num#bvi_exp)app_list`)) THEN
  REWRITE_TAC[append_SmartAppend; ALL_APPEND] THEN
  ASM_MESON_TAC[compile_single_no_mutcons]);;

(* HOL4 line 4919 *)
let compile_inc_no_mutcons = prove
 (`!n prog n1 prog1.
     bvl_to_bvi_compile_inc n prog = (n1,prog1) ==> ALL (no_mutcons o SND o SND) prog1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_inc_def] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n prog` "q" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `prog1:(num#num#bvi_exp)list`)) THEN
  ASM_MESON_TAC[compile_list_no_mutcons]);;

(* HOL4 line 4928 *)
let compile_prog_no_mutcons = prove
 (`!start n prog loc code n1.
     bvl_to_bvi_compile_prog start n prog = (loc,code,n1)
     ==> ALL (no_mutcons o SND o SND) code`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n prog` "q" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `code:(num#num#bvi_exp)list`)) THEN
  REWRITE_TAC[ALL_APPEND; stubs_no_mutcons] THEN ASM_MESON_TAC[compile_list_no_mutcons]);;

(* HOL4 line 4940 [local,simp] *)
let to_op_no_mutcons = prove
 (`!op. no_mutcons_op (to_op op)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:assoc_op` (cases "assoc_op")) THEN
  REWRITE_TAC[to_op_def; no_mutcons_op_def; distinctness "clos_op"]);;

let _ = cake_add_simps [to_op_no_mutcons];;

(* HOL4 line 4947 [local,simp] *)
let apply_op_no_mutcons = prove
 (`!op e1 e2. no_mutcons (apply_op op e1 e2) <=> no_mutcons e1 /\ no_mutcons e2`,
  REWRITE_TAC[apply_op_def; no_mutcons_def; ALL; to_op_no_mutcons]);;

let _ = cake_add_simps [apply_op_no_mutcons];;

(* HOL4 line 4953 [local,simp] *)
let id_from_op_no_mutcons = prove
 (`!op. no_mutcons (id_from_op op)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:assoc_op` (cases "assoc_op")) THEN
  REWRITE_TAC[id_from_op_def; bvi_tailrec_dummy_def; no_mutcons_def; no_mutcons_op_def; ALL;
              distinctness "clos_op"]);;

let _ = cake_add_simps [id_from_op_no_mutcons];;

(* HOL4 line 4961 [local,simp] (HOL4's variable id is id': linear_scanProof *)
(* defines a constant id) *)
let let_wrap_no_mutcons = prove
 (`!arity id' x. no_mutcons (let_wrap arity id' x) <=> no_mutcons id' /\ no_mutcons x`,
  REWRITE_TAC[let_wrap_def; no_mutcons_def; ALL_APPEND; ALL; EVERY_GENLIST] THEN BETA_TAC THEN
  REWRITE_TAC[no_mutcons_def]);;

let _ = cake_add_simps [let_wrap_no_mutcons];;

(* HOL4 line 4967 [local] *)
let get_bin_args_no_mutcons = prove
 (`!exp e1 e2.
     get_bin_args exp = SOME (e1,e2) /\ no_mutcons exp ==> no_mutcons e1 /\ no_mutcons e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_bin_args_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ; no_mutcons_def; ALL] THEN MESON_TAC[]);;

(* HOL4 line 4974 [local] *)
let opbinargs_no_mutcons = prove
 (`!opr exp e1 e2.
     opbinargs opr exp = SOME (e1,e2) /\ no_mutcons exp ==> no_mutcons e1 /\ no_mutcons e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[opbinargs_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[get_bin_args_no_mutcons]);;

(* HOL4 line 4982 [local] *)
let try_swap_no_mutcons = prove
 (`!loc opr exp. no_mutcons exp ==> no_mutcons (try_swap loc opr exp)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRUCT_CASES_TAC (ISPEC `opr:assoc_op` (cases "assoc_op")) THEN
  REWRITE_TAC[try_swap_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN ASM_REWRITE_TAC[apply_op_no_mutcons] THEN
  ASM_MESON_TAC[opbinargs_no_mutcons]);;

(* HOL4 line 4991 [local] *)
let check_op_no_mutcons = prove
 (`!ts opr loc exp exp2.
     check_op ts opr loc exp = SOME exp2 /\ no_mutcons exp ==> no_mutcons exp2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_op_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[apply_op_no_mutcons] THEN
  ASM_MESON_TAC[opbinargs_no_mutcons; try_swap_no_mutcons]);;

(* HOL4 line 4999 [local] *)
let args_from_no_mutcons = prove
 (CASE_TERM
  `!f t d args hdl.
     args_from f = SOME (t,d,args,hdl) /\ no_mutcons f
     ==> ALL no_mutcons args /\ (match hdl with NONE -> T | SOME h -> no_mutcons h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[args_from_PMATCH] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ; no_mutcons_def] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th))))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th))))) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM CASE_REWRITE_TAC[]);;

(* HOL4 line 5007 [local] *)
let push_call_no_mutcons = prove
 (`!x f n op acc.
     no_mutcons x /\ no_mutcons f ==> no_mutcons (push_call n op acc x (args_from f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `a:num#num#bvi_exp list#bvi_exp option` ASSUME_TAC)
    (ISPEC `args_from f` (cases "option")) THEN
  ASM_REWRITE_TAC[push_call_def; bvi_tailrec_dummy_def; no_mutcons_def] THEN
  REPEAT B2BP2AUX_SPLIT_PAIRS_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP args_from_no_mutcons o
    C CONJ (ASSUME `no_mutcons f`) o check (fun th -> is_eq (concl th))) THEN
  REWRITE_TAC[push_call_def; no_mutcons_def; ALL_APPEND; ALL; apply_op_no_mutcons] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5020 [local] *)
let rewrite_catchall_no_mutcons = prove
 (CASE_TERM
  `!ts opr loc exp next acc r y.
     (match check_op ts opr loc exp with
        NONE -> (F,apply_op opr (bvi_Var acc) exp)
      | SOME v1 ->
          (match opbinargs opr v1 with
             NONE -> (F,apply_op opr (bvi_Var acc) v1)
           | SOME (xs,f) -> (T,push_call next opr acc xs (args_from f)))) = (r,y) /\
     no_mutcons exp
     ==> no_mutcons y`,
  REPEAT GEN_TAC THEN REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `y:bvi_exp`
                                                     with Failure _ -> false)) THEN
  REWRITE_TAC[apply_op_no_mutcons; no_mutcons_def] THEN
  TRY(MATCH_MP_TAC push_call_no_mutcons) THEN
  ASM_MESON_TAC[check_op_no_mutcons; opbinargs_no_mutcons]);;

(* HOL4 line 5039 [local] *)
let rewrite_no_mutcons = prove
 (`!loc next opr acc ts exp r y.
     rewrite loc next opr acc ts exp = (r,y) /\ no_mutcons exp ==> no_mutcons y`,
  MATCH_MP_TAC rewrite_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  RW[rewrite_def] THEN REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  GVS[no_mutcons_def; apply_op_no_mutcons] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[apply_op_no_mutcons; no_mutcons_def] THEN
  TRY(FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "option_CASE"
                   with Failure _ -> false)
    then MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ] rewrite_catchall_no_mutcons) th)
    else NO_TAC) THEN
    REWRITE_TAC[no_mutcons_def] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5054 [local] *)
let tailrec_compile_exp_no_mutcons = prove
 (`!loc next arity exp aux opt.
     bvi_tailrec_compile_exp loc next arity exp = SOME (aux,opt) /\ no_mutcons exp
     ==> no_mutcons aux /\ no_mutcons opt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrec_compile_exp_def] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN REWRITE_TAC[option_DISTINCT; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "rewrite"
                                 with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "rr" "yy" g) THEN
  CASE_REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  REWRITE_TAC[let_wrap_no_mutcons; id_from_op_no_mutcons] THEN
  ASM_MESON_TAC[rewrite_no_mutcons]);;

(* HOL4 line 5064 [local] *)
let bvi_tailrec_compile_each_no_mutcons = prove
 (`!next prog next1 prog1.
     bvi_tailrec_compile_each next prog = (next1,prog1) /\
     ALL (no_mutcons o SND o SND) prog
     ==> ALL (no_mutcons o SND o SND) prog1`,
  MATCH_MP_TAC bvi_tailrec_compile_each_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  RW[bvi_tailrec_compile_each_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c &&
    (try fst(dest_const(fst(strip_comb(lhs c)))) = "option_CASE" with Failure _ -> false))) THEN
  DISJ_CASES_THEN2 (fun th -> SUBST1_TAC th THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `a:bvi_exp#bvi_exp` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))
    (ISPEC `bvi_tailrec_compile_exp loc next arity exp` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REPEAT B2BP2AUX_SPLIT_PAIRS_TAC THEN CASE_REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
                                   "bvi_tailrec_compile_each" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "n2" "ys" g) THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) =
    `prog1:(num#num#bvi_exp)list` with Failure _ -> false)) THEN
  REWRITE_TAC[ALL; o_THM] THEN
  ASM_MESON_TAC[tailrec_compile_exp_no_mutcons]);;

(* HOL4 line 5077 *)
let bvi_tailrec_compile_prog_no_mutcons = prove
 (`!b next prog next1 prog1.
     bvi_tailrec_compile_prog b next prog = (next1,prog1) /\
     ALL (no_mutcons o SND o SND) prog
     ==> ALL (no_mutcons o SND o SND) prog1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrec_compile_prog_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[bvi_tailrec_compile_each_no_mutcons]);;

(* HOL4 line 5091 [local] (free_names is bvi_tailrecProof's) *)
let EVERY_free_names_not_in_ns_2 = prove
 (`!(xs:(num#A)list).
     ALL (\n. ~in_ns 2 (n - bvl_num_stubs)) (MAP FST xs)
     ==> ALL (bvi_tailrecProof_free_names (bvl_num_stubs + 2) o FST) xs`,
  GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; o_THM; bvi_tailrecProof_free_names_def] THEN
  DISCH_TAC THEN X_GEN_TAC `x:num#A` THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `FST (x:num#A)`) THEN
  ANTS_TAC THENL [EXISTS_TAC `x:num#A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[in_ns_def; bvl_to_bvi_namespaces_def;
              ARITH_RULE `((a + 2) + 4 * k) - a = k * 4 + 2`; MOD_MULT_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV);;
(* ---- helpers for compile_semantics and the names lemmas ---- *)

let B2BP2AUX_inline_inc_names = prove
 (`!l s c (cs:(num#bvl_exp)spt) prog.
     MAP FST (SND (bvl_inline_compile_inc l s c cs prog)) = MAP FST prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_inline_compile_inc_def; tick_compile_prog_def] THEN
  MP_TAC(ISPECL [`l:num`; `cs:(num#bvl_exp)spt`; `prog:(num#num#bvl_exp)list`]
    MAP_FST_tick_inline_all) THEN
  B2BP2AUX_PAIR_TAC `tick_inline_all l (cs:(num#bvl_exp)spt) prog []` "cs1" "prog1" THEN
  CASE_REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; bvl_inline_optimise_def]);;

let B2BP2AUX_MOD4_add = prove
 (`!a k. (a + bvl_to_bvi_namespaces * k) MOD bvl_to_bvi_namespaces =
         a MOD bvl_to_bvi_namespaces /\
         (a + k * bvl_to_bvi_namespaces) MOD bvl_to_bvi_namespaces =
         a MOD bvl_to_bvi_namespaces`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

(* ---- side conditions of the composed semantics (HOL4 inline in the proof *)
(* of compile_semantics) ---- *)

let B2BP2AUX_inline_handle_ok = prove
 (`!l s c (cs:(num#bvl_exp)spt) prog.
     ALL ((\e. handle_ok [e]) o SND o SND) (SND (bvl_inline_compile_inc l s c cs prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_inline_compile_inc_def] THEN
  B2BP2AUX_PAIR_TAC `tick_compile_prog l (cs:(num#bvl_exp)spt) prog` "cs1" "prog1" THEN
  CASE_REWRITE_TAC[SND] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; bvl_inline_optimise_def] THEN
  REWRITE_TAC[compile_any_handle_ok]);;

let B2BP2AUX_MOD4_sub = prove
 (`!x. bvl_num_stubs <= x ==>
       (x - bvl_num_stubs) MOD bvl_to_bvi_namespaces = x MOD bvl_to_bvi_namespaces`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN MESON_TAC[B2BP2AUX_MOD4_shift]);;

(* the input condition of bvi_tailrec for the code of compile_prog *)
let B2BP2AUX_tailrec_input_code = prove
 (`!start prog loc code m.
     bvl_to_bvi_compile_prog start 0 prog = (loc,code,m) /\ ALL_DISTINCT (MAP FST prog)
     ==> bvi_tailrecProof_input_condition (bvl_num_stubs + 2) code`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_prog_distinct_locs) THEN
  REWRITE_TAC[bvi_tailrecProof_input_condition_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EVERY_free_names_not_in_ns_2 THEN
    UNDISCH_TAC `ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs))
                   (MAP FST (code:(num#num#bvi_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    UNDISCH_TAC `ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs))
                   (MAP FST (code:(num#num#bvi_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; ALL_FILTER; MEM_MAP; o_THM; in_ns_def] THEN
    BETA_TAC THEN MESON_TAC[B2BP2AUX_MOD4_sub];
    ARITH_TAC;
    REWRITE_TAC[B2BP2AUX_num_stubs_eq; bvl_to_bvi_namespaces_def] THEN ARITH_TAC]);;

(* the input condition of bvi_tailrec for the code of compile_inc *)
let B2BP2AUX_tailrec_input_inc = prove
 (`!n1 prog nx prog2 n2.
     bvl_to_bvi_compile_inc n1 prog = (nx,prog2) /\ ALL_DISTINCT (MAP FST prog) /\
     bvl_num_stubs <= n2 /\ n2 MOD bvl_to_bvi_namespaces = 2
     ==> bvi_tailrecProof_input_condition n2 prog2 /\
         ALL (\x. ~(x MOD bvl_to_bvi_namespaces = 3)) (MAP FST prog2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. MEM x (MAP FST (prog2:(num#num#bvi_exp)list)) ==>
                    x MOD bvl_to_bvi_namespaces = 0 \/ x MOD bvl_to_bvi_namespaces = 1`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n1:num`; `prog:(num#num#bvl_exp)list`; `nx:num`;
                  `prog2:(num#num#bvi_exp)list`; `x:num`] compile_inc_next_range) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_tailrecProof_input_condition_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; o_THM; bvi_tailrecProof_free_names_def] THEN
    X_GEN_TAC `e:num#num#bvi_exp` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `FST (e:num#num#bvi_exp)`) THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[B2BP2AUX_MOD4_add] THEN ARITH_TAC;
    MATCH_MP_TAC compile_inc_DISTINCT THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; ALL_FILTER; o_THM] THEN
    X_GEN_TAC `e:num#num#bvi_exp` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `FST (e:num#num#bvi_exp)`) THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN ARITH_TAC;
    REWRITE_TAC[GSYM ALL_MEM] THEN BETA_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* the input condition of bvi_tmc for the code of bvi_tailrec *)
let B2BP2AUX_tmc_input = prove
 (`!b n2 prog2 m prog3 n3.
     bvi_tailrec_compile_prog b n2 prog2 = (m,prog3) /\
     bvi_tailrecProof_input_condition n2 prog2 /\
     ALL (\x. bvl_num_stubs <= x ==> ~(x MOD bvl_to_bvi_namespaces = 3)) (MAP FST prog2) /\
     ALL (no_mutcons o SND o SND) prog2 /\
     bvl_num_stubs <= n3 /\ n3 MOD bvl_to_bvi_namespaces = 3
     ==> bvi_tmcProof_input_condition n3 prog3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_tailrecProof_input_condition_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b:bool`; `n2:num`; `prog2:(num#num#bvi_exp)list`; `m:num`;
                 `prog3:(num#num#bvi_exp)list`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`] bvi_tailrecProof_compile_prog_ALL_DISTINCT)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. MEM x (MAP FST (prog3:(num#num#bvi_exp)list)) ==>
                    MEM x (MAP FST (prog2:(num#num#bvi_exp)list)) \/
                    x MOD bvl_to_bvi_namespaces = 2` ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`b:bool`; `n2:num`; `prog2:(num#num#bvi_exp)list`; `m:num`;
                   `prog3:(num#num#bvi_exp)list`; `x:num`]
      (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
             `ys:(num#num#bvi_exp)list`; `e:num`] bvi_tailrecProof_compile_prog_MEM)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[B2BP2AUX_MOD4_add];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_tmcProof_input_condition_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; o_THM; bvi_tmcProof_free_names_def] THEN
    X_GEN_TAC `e:num#num#bvi_exp` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `FST (e:num#num#bvi_exp)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `prog3:(num#num#bvi_exp)list`)) (concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "MOD" with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs (concl th) =
      `FST (e:num#num#bvi_exp)` with Failure _ -> false)) THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `ALL (\x. bvl_num_stubs <= x ==> ~(x MOD bvl_to_bvi_namespaces = 3))
                     (MAP FST (prog2:(num#num#bvi_exp)list))` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `n3 + bvl_to_bvi_namespaces * j`) THEN
      ASM_REWRITE_TAC[B2BP2AUX_MOD4_add] THEN BETA_TAC THEN ASM_ARITH_TAC;
      UNDISCH_TAC `(n3 + bvl_to_bvi_namespaces * j) MOD bvl_to_bvi_namespaces = 2` THEN
      ASM_REWRITE_TAC[B2BP2AUX_MOD4_add] THEN ARITH_TAC];
    MATCH_MP_TAC bvi_tailrec_compile_prog_no_mutcons THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; ALL_FILTER; o_THM] THEN
    X_GEN_TAC `e:num#num#bvi_exp` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `FST (e:num#num#bvi_exp)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `prog3:(num#num#bvi_exp)list`)) (concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "MOD" with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `ALL (\x. bvl_num_stubs <= x ==> ~(x MOD bvl_to_bvi_namespaces = 3))
                     (MAP FST (prog2:(num#num#bvi_exp)list))` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `FST (e:num#num#bvi_exp)`) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

(* the inputs of bvi_tailrec and bvi_tmc made by the oracle *)
let B2BP2AUX_oracle_tailrec = prove
 (`!l s cut (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list).
     (!n. ALL_DISTINCT (MAP FST (SND (co n))) /\
          bvl_num_stubs <= FST (SND (SND (FST (co n)))) /\
          in_ns 2 (FST (SND (SND (FST (co n))))) /\
          bvl_num_stubs <= FST (SND (SND (SND (FST (co n))))) /\
          in_ns 3 (FST (SND (SND (SND (FST (co n)))))))
     ==> !k n cfg prog.
           state_co bvl_to_bvi_compile_inc
             (state_co (bvl_inline_compile_inc l s cut) co) k = ((n,cfg),prog)
           ==> bvi_tailrecProof_input_condition n prog /\
               ALL (\x. ~(x MOD bvl_to_bvi_namespaces = 3)) (MAP FST prog) /\
               ALL (no_mutcons o SND o SND) prog`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC (AP_TERM `\x:(num#num#(num#bvi_exp)spt#C)#(num#num#bvi_exp)list.
                                          FST (FST x)` th) THEN
                       MP_TAC (AP_TERM `SND:(num#num#(num#bvi_exp)spt#C)#(num#num#bvi_exp)list->
                                           (num#num#bvi_exp)list` th)) THEN
  BETA_TAC THEN REWRITE_TAC[FST_state_co; SND_state_co; FST; SND] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvl_to_bvi_compile_inc" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "nx" "p2" g) THEN REWRITE_TAC[SND] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`FST (SND (FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#
                                       (num#num#bvl_exp)list) k)))`;
                 `SND (bvl_inline_compile_inc l s cut (FST (FST ((co:num->((num#bvl_exp)spt#num#
                     num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list) k))) (SND (co k)))`;
                 `nx:num`; `p2:(num#num#bvi_exp)list`;
                 `FST (SND (SND (FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#
                                            (num#num#bvl_exp)list) k))))`]
    B2BP2AUX_tailrec_input_inc) THEN
  ASM_REWRITE_TAC[B2BP2AUX_inline_inc_names] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[in_ns_def]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC compile_inc_no_mutcons THEN ASM_MESON_TAC[]);;

let B2BP2AUX_oracle_tmc = prove
 (`!l s cut b (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list).
     (!n. ALL_DISTINCT (MAP FST (SND (co n))) /\
          bvl_num_stubs <= FST (SND (SND (FST (co n)))) /\
          in_ns 2 (FST (SND (SND (FST (co n))))) /\
          bvl_num_stubs <= FST (SND (SND (SND (FST (co n))))) /\
          in_ns 3 (FST (SND (SND (SND (FST (co n)))))))
     ==> !k n cfg prog.
           state_co (bvi_tailrec_compile_prog b)
             (state_co bvl_to_bvi_compile_inc
                (state_co (bvl_inline_compile_inc l s cut) co)) k = ((n,cfg),prog)
           ==> bvi_tmcProof_input_condition n prog`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP B2BP2AUX_oracle_tailrec) THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC (AP_TERM `\x:(num#(num#bvi_exp)spt#C)#(num#num#bvi_exp)list.
                                          FST (FST x)` th) THEN
                       MP_TAC (AP_TERM `SND:(num#(num#bvi_exp)spt#C)#(num#num#bvi_exp)list->
                                           (num#num#bvi_exp)list` th)) THEN
  BETA_TAC THEN REWRITE_TAC[FST_state_co; SND_state_co; FST; SND] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvi_tailrec_compile_prog" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "mx" "p3" g) THEN REWRITE_TAC[SND] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvl_to_bvi_compile_inc" with Failure _ -> false) (concl (snd (hd asl))) in
     B2BP2AUX_PAIR_TAC t "nx" "p2" g) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "in_ns" with Failure _ -> false)) (concl th))) THEN
  MP_TAC(ISPECL [`FST (SND (FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#
                                       (num#num#bvl_exp)list) k)))`;
                 `SND (bvl_inline_compile_inc l s cut (FST (FST ((co:num->((num#bvl_exp)spt#num#
                     num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list) k))) (SND (co k)))`;
                 `nx:num`; `p2:(num#num#bvi_exp)list`;
                 `FST (SND (SND (FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#
                                            (num#num#bvl_exp)list) k))))`]
    B2BP2AUX_tailrec_input_inc) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[in_ns_def]) THEN
  ASM_REWRITE_TAC[B2BP2AUX_inline_inc_names] THEN STRIP_TAC THEN
  MATCH_MP_TAC B2BP2AUX_tmc_input THEN
  MAP_EVERY EXISTS_TAC [`b:bool`;
    `FST (SND (SND (FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#
                                 (num#num#bvl_exp)list) k))))`;
    `p2:(num#num#bvi_exp)list`; `mx:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `ALL (\x. ~(x MOD bvl_to_bvi_namespaces = 3)) (MAP FST (p2:(num#num#bvi_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN BETA_TAC THEN MESON_TAC[];
    MATCH_MP_TAC compile_inc_no_mutcons THEN ASM_MESON_TAC[]]);;

(* HOL4 line 5103 (the first semantics is bviSem's, the others bvlSem's) *)
let bvl_to_bviProof_compile_semantics = prove
 (`!start c names prog start' prog' inlines bvi_inlines n1 n2 n3 names'
     (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list)
     (ffi0:(FFI)ffi_state) cc.
     bvl_to_bvi_compile start c names prog =
       (start',prog',inlines,bvi_inlines,n1,n2,n3,names') /\
     FST (FST (co 0)) = inlines /\
     FST (SND (FST (co 0))) = n1 /\
     FST (SND (SND (FST (co 0)))) = n2 /\
     FST (SND (SND (SND (FST (co 0))))) = n3 /\
     FST (SND (SND (SND (SND (FST (co 0)))))) = bvi_inlines /\
     (!n. ALL_DISTINCT (MAP FST (SND (co n))) /\
          bvl_num_stubs <= FST (SND (SND (FST (co n)))) /\
          in_ns 2 (FST (SND (SND (FST (co n))))) /\
          bvl_num_stubs <= FST (SND (SND (SND (FST (co n))))) /\
          in_ns 3 (FST (SND (SND (SND (FST (co n))))))) /\
     ALL_DISTINCT (MAP FST prog)
     ==> ~(bvl_semantics ffi0 (fromAList prog) co (full_cc c cc) start = Fail)
     ==> bvi_semantics ffi0 (fromAList prog') (full_co c co) cc start' =
         bvl_semantics ffi0 (fromAList prog) co (full_cc c cc) start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `bvl_to_bvi_compile start c names prog =
                 (start',prog',inlines,bvi_inlines,n1,n2,n3,names')` THEN
  REWRITE_TAC[bvl_to_bvi_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvl_inline_compile_prog" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "inl" "prog1" g) THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_prog start 0 prog1` "loc" "q1" THEN
  B2BP2AUX_PAIR_TAC `q1:(num#num#bvi_exp)list#num` "code1" "m1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
                       (bvl_num_stubs + 2) code1` "m2" "code2" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)
                       (bvl_num_stubs + 3) code2` "m3" "code3" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_inline_compile_prog code3` "bi" "code4" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) &&
    mem (fst (dest_var (rhs (concl th))))
      ["start'"; "prog'"; "inlines"; "bvi_inlines"; "n1"; "n2"; "n3"; "names'"]))) THEN
  REWRITE_TAC[full_cc_def; full_co_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[full_cc_def; LET_DEF; LET_END_DEF]) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  ABBREV_TAC `L = bvl_inline_compile_inc (bvl_to_bvi_config_inline_size_limit c)
                    (bvl_to_bvi_config_split_main_at_seq c) (bvl_to_bvi_config_exp_cut c)` THEN
  ABBREV_TAC `TR = bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)` THEN
  ABBREV_TAC `TM = bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)` THEN
  ABBREV_TAC `cc4 = state_cc bvi_inline_compile_inc
                      (cc:C->(num#num#bvi_exp)list->(byte list#int64 list#C)option)` THEN
  ABBREV_TAC `cc3 = state_cc (TM:num->(num#num#bvi_exp)list->num#(num#num#bvi_exp)list)
                      (cc4:((num#bvi_exp)spt#C)->(num#num#bvi_exp)list->
                           (byte list#int64 list#(num#bvi_exp)spt#C)option)` THEN
  ABBREV_TAC `S0 = bvl_semantics (ffi0:(FFI)ffi_state) (fromAList prog)
     (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list)
     (state_cc (L:(num#bvl_exp)spt->(num#num#bvl_exp)list->(num#bvl_exp)spt#(num#num#bvl_exp)list)
       (state_cc bvl_to_bvi_compile_inc
         (state_cc (TR:num->(num#num#bvi_exp)list->num#(num#num#bvi_exp)list)
           (cc3:(num#(num#bvi_exp)spt#C)->(num#num#bvi_exp)list->
                (byte list#int64 list#(num#(num#bvi_exp)spt#C))option)))) start` THEN
  (* bvl_inline *)
  SUBGOAL_THEN `bvl_semantics (ffi0:(FFI)ffi_state) (fromAList prog1)
     (state_co (L:(num#bvl_exp)spt->(num#num#bvl_exp)list->(num#bvl_exp)spt#(num#num#bvl_exp)list)
       (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list))
     (state_cc bvl_to_bvi_compile_inc
       (state_cc (TR:num->(num#num#bvi_exp)list->num#(num#num#bvi_exp)list)
         (cc3:(num#(num#bvi_exp)spt#C)->(num#num#bvi_exp)list->
              (byte list#int64 list#(num#(num#bvi_exp)spt#C))option))) start = S0`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "L"] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] bvl_inlineProof_compile_prog_semantics) THEN
    EXISTS_TAC `inl:(num#bvl_exp)spt` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((S0:behaviour) = Fail)` THEN MAP_EVERY EXPAND_TAC ["S0"; "L"] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* facts about the intermediate programs *)
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (prog1:(num#num#bvl_exp)list))` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_prog_names o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
        "bvl_inline_compile_prog" with Failure _ -> false)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c) (bvl_num_stubs + 2)
                  (code1:(num#num#bvi_exp)list) = (m2,code2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c) (bvl_num_stubs + 3)
                  (code2:(num#num#bvi_exp)list) = (m3,code3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bvi_tailrecProof_input_condition (bvl_num_stubs + 2)
                  (code1:(num#num#bvi_exp)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_tailrec_input_code THEN
    MAP_EVERY EXISTS_TAC [`start:num`; `prog1:(num#num#bvl_exp)list`; `loc:num`; `m1:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvi_tmcProof_input_condition (bvl_num_stubs + 3)
                  (code2:(num#num#bvi_exp)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_tmc_input THEN
    MAP_EVERY EXISTS_TAC [`bvl_to_bvi_config_do_tailrec c`; `bvl_num_stubs + 2`;
                          `code1:(num#num#bvi_exp)list`; `m2:num`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`start:num`; `0`; `prog1:(num#num#bvl_exp)list`; `loc:num`;
                   `code1:(num#num#bvi_exp)list`; `m1:num`] compile_prog_distinct_locs) THEN
    MP_TAC(ISPECL [`start:num`; `0`; `prog1:(num#num#bvl_exp)list`; `loc:num`;
                   `code1:(num#num#bvi_exp)list`; `m1:num`] compile_prog_no_mutcons) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs))
                     (MAP FST (code1:(num#num#bvi_exp)list))` THEN
      MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC `x:num` THEN BETA_TAC THEN
      REWRITE_TAC[in_ns_def] THEN STRIP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~((x - bvl_num_stubs) MOD bvl_to_bvi_namespaces = 3)` THEN
      ASM_SIMP_TAC[B2BP2AUX_MOD4_sub];
      REWRITE_TAC[B2BP2AUX_num_stubs_eq; bvl_to_bvi_namespaces_def] THEN ARITH_TAC];
    ALL_TAC] THEN
  (* bvl_to_bvi *)
  SUBGOAL_THEN `bvi_semantics (ffi0:(FFI)ffi_state) (fromAList code1)
     (state_co bvl_to_bvi_compile_inc
       (state_co (L:(num#bvl_exp)spt->(num#num#bvl_exp)list->(num#bvl_exp)spt#(num#num#bvl_exp)list)
         (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list)))
     (state_cc (TR:num->(num#num#bvi_exp)list->num#(num#num#bvi_exp)list)
       (cc3:(num#(num#bvi_exp)spt#C)->(num#num#bvi_exp)list->
            (byte list#int64 list#(num#(num#bvi_exp)spt#C))option)) loc = S0`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN ASSUME_TAC th) o
      check (fun th -> is_eq (concl th) && rhs (concl th) = `S0:behaviour` &&
                       is_comb (lhs (concl th)))) THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] bvl_to_bviProof_compile_prog_semantics) THEN
    MAP_EVERY EXISTS_TAC [`0`; `m1:num`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP compile_prog_handle_ok o
        check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
          "bvl_inline_compile_prog" with Failure _ -> false));
      EXPAND_TAC "L" THEN REWRITE_TAC[SND_state_co; B2BP2AUX_inline_handle_ok];
      ASM_REWRITE_TAC[FST_state_co; LE_REFL]];
    ALL_TAC] THEN
  (* bvi_tailrec *)
  SUBGOAL_THEN `bvi_semantics (ffi0:(FFI)ffi_state) (fromAList code2)
     (state_co (TR:num->(num#num#bvi_exp)list->num#(num#num#bvi_exp)list)
       (state_co bvl_to_bvi_compile_inc
         (state_co (L:(num#bvl_exp)spt->(num#num#bvl_exp)list->(num#bvl_exp)spt#(num#num#bvl_exp)list)
           (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list))))
     (cc3:(num#(num#bvi_exp)spt#C)->(num#num#bvi_exp)list->
          (byte list#int64 list#(num#(num#bvi_exp)spt#C))option) loc = S0`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN ASSUME_TAC th) o
      check (fun th -> is_eq (concl th) && rhs (concl th) = `S0:behaviour` &&
                       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "bvi_semantics"
                        with Failure _ -> false))) THEN
    CONV_TAC SYM_CONV THEN EXPAND_TAC "TR" THEN
    MATCH_MP_TAC bvi_tailrecProof_compile_prog_semantics THEN
    EXISTS_TAC `bvl_num_stubs + 2` THEN ASM_REWRITE_TAC[SND; FST_state_co] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "L" THEN FIRST_ASSUM(MP_TAC o MATCH_MP B2BP2AUX_oracle_tailrec) THEN
      DISCH_THEN(fun th -> REPEAT GEN_TAC THEN
        DISCH_THEN(fun h -> ACCEPT_TAC(CONJUNCT1(MATCH_MP th h))));
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`bvl_to_bvi_config_do_tailrec c`; `bvl_num_stubs + 2`;
                     `code1:(num#num#bvi_exp)list`; `m2:num`; `code2:(num#num#bvi_exp)list`]
                    bvi_tailrecProof_compile_prog_next_mono) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(MATCH_MP (GEN_ALL bvi_tailrecProof_compile_prog_MEM)
        (CONJ (ASSUME `bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
                         (bvl_num_stubs + 2) (code1:(num#num#bvi_exp)list) = (m2,code2)`)
              (ASSUME `MEM (k:num) (MAP FST (code2:(num#num#bvi_exp)list))`))) THEN
      (* the second case is closed by STRIP_TAC itself (k < m2) *)
      STRIP_TAC THEN
      MP_TAC(ISPECL [`start:num`; `0`; `prog1:(num#num#bvl_exp)list`; `loc:num`;
                     `code1:(num#num#bvi_exp)list`; `m1:num`; `k:num`]
                    bvl_to_bviProof_compile_prog_avoids_nss_2) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  (* bvi_tmc *)
  SUBGOAL_THEN `bvi_semantics (ffi0:(FFI)ffi_state) (fromAList code3)
     (state_co (TM:num->(num#num#bvi_exp)list->num#(num#num#bvi_exp)list)
       (state_co (TR:num->(num#num#bvi_exp)list->num#(num#num#bvi_exp)list)
         (state_co bvl_to_bvi_compile_inc
           (state_co (L:(num#bvl_exp)spt->(num#num#bvl_exp)list->(num#bvl_exp)spt#(num#num#bvl_exp)list)
             (co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list)))))
     (cc4:((num#bvi_exp)spt#C)->(num#num#bvi_exp)list->
          (byte list#int64 list#(num#bvi_exp)spt#C)option) loc = S0`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN ASSUME_TAC th) o
      check (fun th -> is_eq (concl th) && rhs (concl th) = `S0:behaviour` &&
                       free_in `fromAList (code2:(num#num#bvi_exp)list)` (lhs (concl th)))) THEN
    CONV_TAC SYM_CONV THEN EXPAND_TAC "cc3" THEN EXPAND_TAC "TM" THEN
    MATCH_MP_TAC(GEN_ALL bvi_tmcProof_compile_prog_semantics) THEN
    EXISTS_TAC `bvl_num_stubs + 3` THEN ASM_REWRITE_TAC[SND; FST_state_co] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "L" THEN EXPAND_TAC "TR" THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP B2BP2AUX_oracle_tmc) THEN
      DISCH_THEN(fun th -> REPEAT GEN_TAC THEN
        DISCH_THEN(fun h -> ACCEPT_TAC(MATCH_MP th h)));
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`bvl_to_bvi_config_do_tmc c`; `bvl_num_stubs + 3`;
                     `code2:(num#num#bvi_exp)list`; `m3:num`; `code3:(num#num#bvi_exp)list`]
                    bvi_tmcProof_compile_prog_next_mono) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(MATCH_MP (GEN_ALL bvi_tmcProof_compile_prog_MEM)
        (CONJ (ASSUME `bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)
                         (bvl_num_stubs + 3) (code2:(num#num#bvi_exp)list) = (m3,code3)`)
              (ASSUME `MEM (k:num) (MAP FST (code3:(num#num#bvi_exp)list))`))) THEN
      (* the second case is closed by STRIP_TAC itself (k < m3) *)
      STRIP_TAC THEN
      MP_TAC(MATCH_MP (GEN_ALL bvi_tailrecProof_compile_prog_MEM)
        (CONJ (ASSUME `bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
                         (bvl_num_stubs + 2) (code1:(num#num#bvi_exp)list) = (m2,code2)`)
              (ASSUME `MEM (k:num) (MAP FST (code2:(num#num#bvi_exp)list))`))) THEN
      STRIP_TAC THENL
       [MP_TAC(ISPECL [`start:num`; `0`; `prog1:(num#num#bvl_exp)list`; `loc:num`;
                       `code1:(num#num#bvi_exp)list`; `m1:num`; `k:num`]
                      compile_prog_avoids_nss_3) THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        (* a fresh tailrec name is in namespace 2, not 3 *)
        UNDISCH_TAC `k MOD bvl_to_bvi_namespaces = 3` THEN
        ASM_REWRITE_TAC[B2BP2AUX_MOD4_add] THEN
        REWRITE_TAC[B2BP2AUX_num_stubs_eq; bvl_to_bvi_namespaces_def] THEN
        CONV_TAC NUM_REDUCE_CONV]];
    ALL_TAC] THEN
  (* bvi_inline *)
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN ASSUME_TAC th) o
    check (fun th -> is_eq (concl th) && rhs (concl th) = `S0:behaviour` &&
                     free_in `fromAList (code3:(num#num#bvi_exp)list)` (lhs (concl th)))) THEN
  EXPAND_TAC "cc4" THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] bvi_inlineProof_compile_prog_semantics) THEN
  EXISTS_TAC `bi:(num#bvi_exp)spt` THEN ASM_REWRITE_TAC[FST_state_co] THEN
  UNDISCH_TAC `bvi_tmcProof_input_condition (bvl_num_stubs + 3) (code2:(num#num#bvi_exp)list)` THEN
  REWRITE_TAC[bvi_tmcProof_input_condition_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] bvi_tmcProof_compile_prog_ALL_DISTINCT)) THEN
  ASM_SIMP_TAC[]);;


(* the names made by compile_prog are not below data_num_stubs *)
let B2BP2AUX_compile_prog_names_ge = prove
 (`!s n prog k code m.
     bvl_to_bvi_compile_prog s n prog = (k,code,m) /\ ALL_DISTINCT (MAP FST prog)
     ==> ALL (\x. data_num_stubs <= x) (MAP FST code)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n prog` "c" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  MP_TAC(ISPECL [`n:num`; `prog:(num#num#bvl_exp)list`; `c:(num#num#bvi_exp)app_list`;
                 `append (c:(num#num#bvi_exp)app_list)`; `m1:num`] compile_list_distinct_locs) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MAP_APPEND; ALL_APPEND; B2BP2AUX_MAP_FST_stubs; ALL] THEN
  REWRITE_TAC[data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `ALL ((<=) bvl_num_stubs) (MAP FST (append (c:(num#num#bvi_exp)app_list)))` THEN
  REWRITE_TAC[GSYM ALL_MEM; B2BP2AUX_num_stubs_eq] THEN BETA_TAC THEN
  MESON_TAC[ARITH_RULE `72 <= x ==> 62 <= x`]);;

(* no name of compile_prog's code is a fresh name of bvi_tmc (ns 3) *)
let B2BP2AUX_tmc_free_names = prove
 (`!b xs n2 code2.
     bvi_tailrec_compile_prog b (bvl_num_stubs + 2) xs = (n2,code2) /\
     ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs)) (MAP FST xs)
     ==> ALL (bvi_tmcProof_free_names (bvl_num_stubs + 3) o FST) code2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM; bvi_tmcProof_free_names_def] THEN
  X_GEN_TAC `e:num#num#bvi_exp` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b:bool`; `bvl_num_stubs + 2`; `xs:(num#num#bvi_exp)list`; `n2:num`;
                 `code2:(num#num#bvi_exp)list`; `FST (e:num#num#bvi_exp)`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`; `e:num`] bvi_tailrecProof_compile_prog_MEM)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `e:num#num#bvi_exp` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs (concl th) = `FST (e:num#num#bvi_exp)`
                                                    with Failure _ -> false)) THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs))
                   (MAP FST (xs:(num#num#bvi_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC
      `(bvl_num_stubs + 3) + bvl_to_bvi_namespaces * j`) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    REWRITE_TAC[in_ns_def; bvl_to_bvi_namespaces_def;
                ARITH_RULE `((a + 3) + 4 * j) - a = j * 4 + 3`; MOD_MULT_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV;
    UNDISCH_TAC `(bvl_num_stubs + 3) + bvl_to_bvi_namespaces * j =
                 (bvl_num_stubs + 2) + k * bvl_to_bvi_namespaces` THEN
    REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 4`) THEN BETA_TAC THEN
    REWRITE_TAC[B2BP2AUX_num_stubs_eq; ARITH_RULE `(72 + 3) + 4 * j = (j + 18) * 4 + 3`;
                ARITH_RULE `(72 + 2) + k * 4 = (k + 18) * 4 + 2`; MOD_MULT_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* HOL4 line 5394 (ns' is the pair of n3 and the names, as in HOL4) *)
let compile_distinct_names = prove
 (`!n0 c ns p2 k p3 l bl n1 n2 ns' n02.
     bvl_to_bvi_compile n0 c ns p2 = (k,p3,l,bl,n1,n2,ns') /\
     ALL_DISTINCT (MAP FST p2) /\
     bvl_to_bvi_config_next_name2 c = (bvl_num_stubs + 2) + n02 * bvl_to_bvi_namespaces
     ==> ALL (\n. data_num_stubs <= n) (MAP FST p3) /\ ALL_DISTINCT (MAP FST p3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvl_inline_compile_prog" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "inl" "prog" g) THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_prog n0 0 prog` "loc" "q1" THEN
  B2BP2AUX_PAIR_TAC `q1:(num#num#bvi_exp)list#num` "code" "m1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
                       (bvl_num_stubs + 2) code` "m2" "code2" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)
                       (bvl_num_stubs + 3) code2` "m3" "code3" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_inline_compile_prog code3` "bi" "code4" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs (concl th) =
    `p3:(num#num#bvi_exp)list` with Failure _ -> false)) THEN
  SUBGOAL_THEN `MAP FST (code4:(num#num#bvi_exp)list) = MAP FST (code3:(num#num#bvi_exp)list)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC compile_inc_MAP_FST THEN
    MAP_EVERY EXISTS_TAC [`LN:(num#bvi_exp)spt`; `bi:(num#bvi_exp)spt`] THEN
    ASM_REWRITE_TAC[GSYM bvi_inline_compile_prog_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (prog:(num#num#bvl_exp)list))` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_prog_names o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
        "bvl_inline_compile_prog" with Failure _ -> false)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n0:num`; `0`; `prog:(num#num#bvl_exp)list`; `loc:num`;
                 `code:(num#num#bvi_exp)list`; `m1:num`] compile_prog_distinct_locs) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n0:num`; `0`; `prog:(num#num#bvl_exp)list`; `loc:num`;
                 `code:(num#num#bvi_exp)list`; `m1:num`] B2BP2AUX_compile_prog_names_ge) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ALL (bvi_tailrecProof_free_names (bvl_num_stubs + 2) o FST)
                  (code:(num#num#bvi_exp)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC EVERY_free_names_not_in_ns_2 THEN
    UNDISCH_TAC `ALL (\n. ~in_ns 2 (n - bvl_num_stubs) /\ ~in_ns 3 (n - bvl_num_stubs))
                   (MAP FST (code:(num#num#bvi_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bvl_to_bvi_config_do_tailrec c`; `bvl_num_stubs + 2`;
                 `code:(num#num#bvi_exp)list`; `m2:num`; `code2:(num#num#bvi_exp)list`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`] bvi_tailrecProof_compile_prog_ALL_DISTINCT)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bvl_to_bvi_config_do_tailrec c`; `code:(num#num#bvi_exp)list`; `m2:num`;
                 `code2:(num#num#bvi_exp)list`] B2BP2AUX_tmc_free_names) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`bvl_to_bvi_config_do_tmc c`; `bvl_num_stubs + 3`;
                 `code2:(num#num#bvi_exp)list`; `m3:num`; `code3:(num#num#bvi_exp)list`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`] bvi_tmcProof_compile_prog_ALL_DISTINCT)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`bvl_to_bvi_config_do_tmc c`; `bvl_num_stubs + 3`;
                 `code2:(num#num#bvi_exp)list`; `m3:num`; `code3:(num#num#bvi_exp)list`; `x:num`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`; `e:num`] bvi_tmcProof_compile_prog_MEM)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `bvl_num_stubs + 3 <= x` THEN
    REWRITE_TAC[B2BP2AUX_num_stubs_eq; data_num_stubs_def; word_num_stubs_def;
                stack_num_stubs_def] THEN ARITH_TAC] THEN
  MP_TAC(ISPECL [`bvl_to_bvi_config_do_tailrec c`; `bvl_num_stubs + 2`;
                 `code:(num#num#bvi_exp)list`; `m2:num`; `code2:(num#num#bvi_exp)list`; `x:num`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`; `e:num`] bvi_tailrecProof_compile_prog_MEM)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [UNDISCH_TAC `ALL (\x. data_num_stubs <= x) (MAP FST (code:(num#num#bvi_exp)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN BETA_TAC THEN ASM_MESON_TAC[];
    UNDISCH_TAC `bvl_num_stubs + 2 <= x` THEN
    REWRITE_TAC[B2BP2AUX_num_stubs_eq; data_num_stubs_def; word_num_stubs_def;
                stack_num_stubs_def] THEN ARITH_TAC]);;

(* HOL4 line 5471 *)
let ALL_DISTINCT_MAP_FST_SND_full_co = prove
 (`!(co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list) n c.
     ALL_DISTINCT (MAP FST (SND (co n))) /\
     FST (SND (SND (FST (co n)))) MOD bvl_to_bvi_namespaces = 2 /\
     FST (SND (SND (SND (FST (co n))))) MOD bvl_to_bvi_namespaces = 3
     ==> ALL_DISTINCT (MAP FST (SND (full_co c co n)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[full_co_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[SND_state_co; FST_state_co] THEN
  ABBREV_TAC `n2 = FST (SND (SND (FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list) n))))` THEN
  ABBREV_TAC `n3 = FST (SND (SND (SND (FST ((co:num->((num#bvl_exp)spt#num#num#num#(num#bvi_exp)spt#C)#(num#num#bvl_exp)list) n)))))` THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvl_inline_compile_inc" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "cs1" "p1" g) THEN REWRITE_TAC[SND] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvl_to_bvi_compile_inc" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "nx2" "p2" g) THEN REWRITE_TAC[SND] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvi_tailrec_compile_prog" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "m3" "p3" g) THEN REWRITE_TAC[SND] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvi_tmc_compile_prog" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "m4" "p4" g) THEN REWRITE_TAC[SND] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvi_inline_compile_inc" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "cs5" "p5" g) THEN REWRITE_TAC[SND] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP compile_inc_MAP_FST o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
      "bvi_inline_compile_inc" with Failure _ -> false)) THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (p1:(num#num#bvl_exp)list))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `\x:(num#bvl_exp)spt#(num#num#bvl_exp)list. MAP FST (SND x)` o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
        "bvl_inline_compile_inc" with Failure _ -> false)) THEN
    BETA_TAC THEN REWRITE_TAC[B2BP2AUX_inline_inc_names; SND] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (p2:(num#num#bvi_exp)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC compile_inc_DISTINCT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. MEM x (MAP FST (p2:(num#num#bvi_exp)list)) ==>
                    x MOD bvl_to_bvi_namespaces = 0 \/ x MOD bvl_to_bvi_namespaces = 1`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `MEM (x:num) (MAP FST (p2:(num#num#bvi_exp)list))`) o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] compile_inc_next_range) o
      check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
        "bvl_to_bvi_compile_inc" with Failure _ -> false)) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bvl_to_bvi_config_do_tailrec c`; `n2:num`;
                 `p2:(num#num#bvi_exp)list`; `m3:num`; `p3:(num#num#bvi_exp)list`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`] bvi_tailrecProof_compile_prog_ALL_DISTINCT)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM ALL_MEM; o_THM; bvi_tailrecProof_free_names_def] THEN
    X_GEN_TAC `e:num#num#bvi_exp` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `FST (e:num#num#bvi_exp)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun u -> u = `p2:(num#num#bvi_exp)list`)) (concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "MOD" with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[B2BP2AUX_MOD4_add] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`bvl_to_bvi_config_do_tmc c`; `n3:num`;
                 `p3:(num#num#bvi_exp)list`; `m4:num`; `p4:(num#num#bvi_exp)list`]
    (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
           `ys:(num#num#bvi_exp)list`] bvi_tmcProof_compile_prog_ALL_DISTINCT)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM ALL_MEM; o_THM; bvi_tmcProof_free_names_def] THEN
    X_GEN_TAC `e:num#num#bvi_exp` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`bvl_to_bvi_config_do_tailrec c`; `n2:num`; `p2:(num#num#bvi_exp)list`;
                   `m3:num`; `p3:(num#num#bvi_exp)list`; `FST (e:num#num#bvi_exp)`]
      (GENL [`b:bool`; `n:num`; `xs:(num#num#bvi_exp)list`; `n1:num`;
             `ys:(num#num#bvi_exp)list`; `e:num`] bvi_tailrecProof_compile_prog_MEM)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rhs (concl th) =
      `FST (e:num#num#bvi_exp)` with Failure _ -> false)) THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n3 + bvl_to_bvi_namespaces * j` o check (fun th ->
        is_forall (concl th) && can (find_term (fun u -> u = `p2:(num#num#bvi_exp)list`)) (concl th) &&
        can (find_term (fun u -> try fst(dest_const u) = "MOD" with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[B2BP2AUX_MOD4_add] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD bvl_to_bvi_namespaces`) THEN BETA_TAC THEN
      ASM_REWRITE_TAC[B2BP2AUX_MOD4_add] THEN ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5554 (bvlProps' get_code_labels) *)
let destLet_code_labels = prove
 (`!x y z.
     destLet x = (y,z)
     ==> UNIONS (set_of_list (MAP bvl_get_code_labels y)) UNION bvl_get_code_labels z SUBSET
         bvl_get_code_labels x`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:bvl_exp` (CONJUNCT1 (cases "bvl_exp"))) THEN
  REWRITE_TAC[destLet_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[bvl_get_code_labels_def; MAP; set_of_list; UNIONS_0; UNION_EMPTY; EMPTY_SUBSET;
              SUBSET_REFL]);;

(* HOL4 line 5563 [simp] (bviProps' get_code_labels) *)
let compile_int_code_labels = prove
 (`!i. bvi_get_code_labels (compile_int i) = {}`,
  GEN_TAC THEN REWRITE_TAC[compile_int_def; bvi_get_code_labels_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[assign_get_code_label_def; MAP; set_of_list; UNIONS_0; UNION_EMPTY]);;

let _ = cake_add_simps [compile_int_code_labels];;

(* HOL4 line 5569 (HOL4 UNION is left-associative) *)
let compile_op_code_labels = prove
 (`!op c x y.
     bvi_get_code_labels (bvl_to_bvi_compile_op op c) SUBSET
     (UNIONS (set_of_list (MAP bvi_get_code_labels c)) UNION
      IMAGE (\n. bvl_num_stubs + n * bvl_to_bvi_namespaces) (assign_get_code_label op)) UNION
     set_of_list (MAP FST (bvl_to_bvi_stubs x y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_op_def; B2BP2AUX_MAP_FST_stubs] THEN
  REPEAT (COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  REWRITE_TAC[bvi_get_code_labels_def; assign_get_code_label_def; compile_int_code_labels;
              MAP; MAP_APPEND; set_of_list; SET_OF_LIST_APPEND; UNIONS_0; UNION_EMPTY; UNIONS_INSERT;
              UNIONS_UNION; IMAGE_CLAUSES; AllocGlobal_location_eq; CopyGlobals_location_eq;
              InitGlobals_location_eq; ListLength_location_eq; FromListByte_location_eq;
              ToListByte_location_eq; SumListLength_location_eq; ConcatByte_location_eq] THEN
  CASE_REWRITE_TAC[bvi_get_code_labels_def; UNION_EMPTY; UNIONS_0; set_of_list; MAP] THEN
  REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; EMPTY_SUBSET; IMAGE_CLAUSES; MULT_SYM] THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; REPLICATE; MAP; set_of_list;
              bvi_get_code_labels_def; assign_get_code_label_def; UNIONS_INSERT; UNIONS_0;
              UNION_EMPTY; INSERT_AC; EMPTY_SUBSET] THEN
  SET_TAC[]);;

let B2BP2AUX_R_mono = prove
 (`!a b c d. c <= a /\ b <= d ==>
     {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | a <= k /\ k < b} SUBSET
     {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | c <= k /\ k < d}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let B2BP2AUX_R_mem = prove
 (`!t c d. c <= t /\ t < d ==>
     bvl_num_stubs + bvl_to_bvi_namespaces * t + 1 IN
     {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | c <= k /\ k < d}`,
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `t:num` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let B2BP2AUX_Rpat =
  `{bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | a <= k /\ k < b}`;;

let B2BP2AUX_R_terms (tm:term) =
  find_terms (fun t -> can (term_match [] B2BP2AUX_Rpat) t) tm;;

let B2BP2AUX_R_bounds (t:term) =
  let _,i,_ = term_match [] B2BP2AUX_Rpat t in
  rev_assoc `a:num` i, rev_assoc `b:num` i;;

let B2BP2AUX_is_arith (c:term) =
  let c = if is_neg c then dest_neg c else c in
  try let op,_ = dest_comb (rator c) in
      (op = `(<=):num->num->bool` || op = `(<):num->num->bool` ||
       (op = `(=):num->num->bool`))
  with Failure _ -> false;;

(* prove an arithmetic fact from the arithmetic assumptions *)
let B2BP2AUX_arith_prove (asl:(string*thm) list) (tm:term) =
  let ths = filter (fun th -> B2BP2AUX_is_arith (concl th)) (map snd asl) in
  if ths = [] then ARITH_RULE tm else
  let ant = end_itlist CONJ ths in
  MP (ARITH_RULE (mk_imp(concl ant, tm))) ant;;

(* drule_all with equations t = v or v = t (v bound) in the antecedent     *)
(* instantiated by v := t *)
let rec B2BP2AUX_drule_all2 (prv:tactic) asl th =
  let vs0,_ = strip_forall (concl th) in
  let th = GENL vs0 (REWRITE_RULE[IMP_CONJ] (SPECL vs0 th)) in
  let vs,body = strip_forall (concl th) in
  if not (is_imp body) then th else
  let a,_ = dest_imp body in
  let inst_eq v t =
    let vs' = filter (fun u -> u <> v) vs in
    let th1 = INST [t,v] (SPECL vs th) in
    let a1,_ = dest_imp (concl th1) in
    let eqth = if lhs a1 = rhs a1 then REFL (lhs a1) else failwith "inst_eq" in
    B2BP2AUX_drule_all2 prv asl (GENL vs' (MP th1 eqth)) in
  try
    if is_eq a && is_var (rhs a) && mem (rhs a) vs && not (free_in (rhs a) (lhs a))
    then inst_eq (rhs a) (lhs a)
    else if is_eq a && is_var (lhs a) && mem (lhs a) vs && not (free_in (lhs a) (rhs a))
    then inst_eq (lhs a) (rhs a)
    else failwith "not eq"
  with Failure _ ->
  let mp = MATCH_MP_CURRIED th in
  try tryfind (fun a -> B2BP2AUX_drule_all2 prv asl (mp a)) (map snd asl)
  with Failure _ ->
    if intersect (frees a) vs <> [] then failwith "B2BP2AUX_drule_all2" else
    let tha = TAC_PROOF((asl,a),prv) in
    B2BP2AUX_drule_all2 prv asl (GENL vs (MP (SPECL vs th) tha));;

(* instantiate the induction hypotheses with the facts among the assumptions *)
let B2BP2AUX_IH_ALL_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun ih (asl,w as g) ->
    if not (is_forall (concl ih) || is_imp (concl ih)) then failwith "IH_ALL" else
    let th = B2BP2AUX_drule_all2 B2BP2AUX_PRV_TAC asl ih in
    if is_imp (snd (strip_forall (concl th))) || is_forall (concl th)
    then failwith "IH_ALL" else STRIP_ASSUME_TAC th g));;

let B2BP2AUX_LABEL_RWS =
  [bvi_get_code_labels_def; bvl_get_code_labels_def; MAP; set_of_list; UNIONS_INSERT;
   UNIONS_0; UNION_EMPTY; MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION; append_SmartAppend;
   append_thm; compile_aux_def; bvi_letProof_compile_exp_code_labels; IMAGE_UNION; APPEND;
   o_THM];;

let B2BP2AUX_sing_image = prove
 (`!a. {bvl_num_stubs + bvl_to_bvi_namespaces * a} SUBSET
       IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces) {a}`,
  REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[MULT_SYM]);;

let rec B2BP2AUX_set_atoms (tm:term) =
  if (try fst(dest_const(fst(strip_comb tm))) = "UNION" with Failure _ -> false)
  then union (B2BP2AUX_set_atoms (lhand tm)) (B2BP2AUX_set_atoms (rand tm))
  else [tm];;

let B2BP2AUX_subset_sides (c:term) =
  if (try fst(dest_const(fst(strip_comb c))) = "SUBSET" with Failure _ -> false)
  then [lhand c; rand c] else failwith "subset_sides";;

let B2BP2AUX_INSERT_SING = prove
 (`!(x:A) s. x INSERT s = {x} UNION s`,
  SET_TAC[]);;

let B2BP2AUX_INSERT_CONV (tm:term) =
  match tm with
    Comb(Comb(Const("INSERT",_),x),s) when not (is_const s && fst(dest_const s) = "EMPTY") ->
      ISPECL [x; s] B2BP2AUX_INSERT_SING
  | _ -> failwith "B2BP2AUX_INSERT_CONV";;

(* SET_TAC on the subset facts and the goal with the non-union sets made  *)
(* variables (atoms) *)
let B2BP2AUX_ABS_SET_TAC (facts:thm list) : tactic = fun (asl,w as g) ->
  let facts = map (CONV_RULE (DEPTH_CONV B2BP2AUX_INSERT_CONV)) facts in
  (CONV_TAC (DEPTH_CONV B2BP2AUX_INSERT_CONV) THEN
   (fun (asl,w as g) ->
     let sides = flat (map (fun th -> try B2BP2AUX_subset_sides (concl th)
                                      with Failure _ -> []) facts) @
                 B2BP2AUX_subset_sides w in
     let atoms = setify (flat (map B2BP2AUX_set_atoms sides)) in
     let size t = String.length (string_of_term t) in
     let atoms = sort (fun a b -> size a > size b) atoms in
     let vars = map (fun (i,a) -> mk_var("XS"^string_of_int i, type_of a))
                  (zip (0--(length atoms - 1)) atoms) in
     if facts = [] then SET_TAC[] g else
     (MP_TAC (end_itlist CONJ facts) THEN
      MAP_EVERY (fun (a,v) -> SPEC_TAC(a,v)) (zip atoms vars) THEN
      SET_TAC[]) g)) g;;

let B2BP2AUX_LABELS_ONE_TAC : tactic = fun (asl,w as g) ->
  let a = lhand w in
  let gR = setify (B2BP2AUX_R_terms w) in
  let aR = setify (flat (map (fun (_,th) -> B2BP2AUX_R_terms (concl th)) asl)) in
  let mono = flat (map (fun r1 -> let a,b = B2BP2AUX_R_bounds r1 in
    mapfilter (fun r2 -> let c,d = B2BP2AUX_R_bounds r2 in
      MATCH_MP B2BP2AUX_R_mono
        (B2BP2AUX_arith_prove asl (mk_conj(mk_binop `(<=):num->num->bool` c a,
                                           mk_binop `(<=):num->num->bool` b d)))) gR) aR) in
  let elpat = `bvl_num_stubs + bvl_to_bvi_namespaces * t + 1` in
  let els = setify (find_terms (fun t -> can (term_match [] elpat) t) w) in
  let mems = flat (map (fun e -> let _,i,_ = term_match [] elpat e in
    let t = rev_assoc `t:num` i in
    mapfilter (fun r2 -> let c,d = B2BP2AUX_R_bounds r2 in
      REWRITE_RULE[GSYM SING_SUBSET] (MATCH_MP B2BP2AUX_R_mem
        (B2BP2AUX_arith_prove asl (mk_conj(mk_binop `(<=):num->num->bool` c t,
                                           mk_binop `(<):num->num->bool` t d))))) gR) els) in
  let elpat2 = `{bvl_num_stubs + bvl_to_bvi_namespaces * t}` in
  let els2 = setify (find_terms (fun t -> can (term_match [] elpat2) t) w) in
  let sings = map (fun e -> let _,i,_ = term_match [] elpat2 e in
    SPEC (rev_assoc `t:num` i) B2BP2AUX_sing_image) els2 in
  let issub c = (try fst(dest_const(fst(strip_comb c))) = "SUBSET" with Failure _ -> false) in
  let allsets = filter (fun th -> issub (concl th)) (map snd asl) in
  let rec close front acc n =
    if n = 0 then acc else
    let fa = setify (flat (map B2BP2AUX_set_atoms front)) in
    let newf = filter (fun th -> not (mem th acc) &&
                 exists (fun at -> mem at fa)
                   (B2BP2AUX_set_atoms (lhand (concl th)))) allsets in
    if newf = [] then acc else
    close (map (fun th -> rand (concl th)) newf) (acc @ newf) (n - 1) in
  let sets = close [a] [] 4 in
  let f = `\k. bvl_num_stubs + k * bvl_to_bvi_namespaces` in
  let bvl = filter (fun th -> let c = concl th in issub c &&
               can (find_term (fun u -> try fst(dest_const u) = "bvl_get_code_labels"
                                         with Failure _ -> false)) (lhand c))
               (map snd asl) in
  let imgs = map (fun th -> REWRITE_RULE[IMAGE_UNION]
                 (MATCH_MP (ISPEC f IMAGE_SUBSET) th)) bvl in
  B2BP2AUX_ABS_SET_TAC (sets @ mono @ mems @ sings @ imgs) g;;

let B2BP2AUX_LABELS_FINISH_TAC : tactic =
  REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN B2BP2AUX_LABELS_ONE_TAC;;

(* the code labels of compile_exps_sing and compile_exps_list (HOL4 proves *)
(* compile_exps_get_code_labels by recInduct on compile_exps) *)
let B2BP2AUX_labels_sing = prove
 (`!x y.
   (!n e c aux m.
     compile_exps_sing n e = (c,aux,m)
     ==> n <= m /\
         bvi_get_code_labels c UNION
         UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (append aux))) SUBSET
         (IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces) (bvl_get_code_labels e) UNION
          {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n <= k /\ k < m}) UNION
         set_of_list (MAP FST (bvl_to_bvi_stubs x y))) /\
   (!n es cs aux m.
     compile_exps_list n es = (cs,aux,m)
     ==> n <= m /\
         UNIONS (set_of_list (MAP bvi_get_code_labels cs)) UNION
         UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (append aux))) SUBSET
         (IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
            (UNIONS (set_of_list (MAP bvl_get_code_labels es))) UNION
          {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n <= k /\ k < m}) UNION
         set_of_list (MAP FST (bvl_to_bvi_stubs x y)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC compile_exps_sing_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) -> if is_imp w && not (is_eq (fst (dest_imp w)))
     then DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) g else ALL_TAC g) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_exps_sing_def] THEN
  REPEAT PAIRARG_TAC THEN TRY COND_CASES_TAC THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  B2BP2AUX_IH_ALL_TAC THEN
  REPEAT (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP destLet_code_labels o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "destLet"
                     with Failure _ -> false))) THEN
  (fun (asl,w as g) ->
     try let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
                   "bvl_to_bvi_compile_op" with Failure _ -> false) w in
         let _,args = strip_comb t in
         (MP_TAC (CONV_RULE (ONCE_DEPTH_CONV (fun t -> if is_abs t then ALPHA_CONV `k:num` t
                                                    else failwith "")) 
                    (ISPECL [el 0 args; el 1 args; `x:num`; `y:num`] compile_op_code_labels)) THEN
          DISCH_TAC) g
     with Failure _ -> ALL_TAC g) THEN
  TRY (B2BP2AUX_CASES_TY_TAC `:num option` (cases "option")) THEN
  REWRITE_TAC B2BP2AUX_LABEL_RWS THEN CASE_REWRITE_TAC B2BP2AUX_LABEL_RWS THEN
  REPEAT CONJ_TAC THEN
  FIRST [(fun (asl,w as g) -> ACCEPT_TAC (B2BP2AUX_arith_prove asl w) g);
         B2BP2AUX_LABELS_FINISH_TAC]);;

(* HOL4 line 5581 (bviProps' get_code_labels on the left, bvlProps' for xs) *)
let compile_exps_get_code_labels = prove
 (`!n xs ys aux m x y.
     bvl_to_bvi_compile_exps n xs = (ys,aux,m)
     ==> UNIONS (set_of_list (MAP bvi_get_code_labels ys)) UNION
         UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (append aux)))
         SUBSET
         (IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
            (UNIONS (set_of_list (MAP bvl_get_code_labels xs))) UNION
          {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n <= k /\ k < m}) UNION
         set_of_list (MAP FST (bvl_to_bvi_stubs x y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM (CONJUNCT2 compile_exps_sing)] THEN
  MESON_TAC[CONJUNCT2 (SPECL [`x:num`; `y:num`] B2BP2AUX_labels_sing)]);;

(* the names of the auxiliary functions made by compile_exps (HOL4 proves *)
(* compile_exps_aux_contains by induction on compile_exps) *)
let B2BP2AUX_RANGE_TAC : tactic = fun (asl,w as g) ->
  let kv = `k:num` in
  let isih th = try let k0,bd = dest_forall (concl th) in
                    let ant,con = dest_imp bd in
                    is_conj ant && type_of k0 = `:num` &&
                    (try fst(dest_const(fst(strip_comb con))) = "MEM" with Failure _ -> false)
                with Failure _ -> false in
  let ihs = filter isih (map snd asl) in
  let bounds = setify (map (fun ih -> let _,bd = dest_forall (concl ih) in
                                      rand (rand (fst (dest_imp bd)))) ihs) in
  let try_ih ih (asl,w as g) =
    let k0,bd = dest_forall (concl ih) in
    let ant,_ = dest_imp bd in
    let th = B2BP2AUX_arith_prove asl (vsubst [kv,k0] ant) in
    (MP_TAC (MP (SPEC kv ih) th) THEN
     REWRITE_TAC[MEM_APPEND; MAP_APPEND; append_SmartAppend] THEN MESON_TAC[]) g in
  let elpat = `bvl_num_stubs + bvl_to_bvi_namespaces * t + 1` in
  let try_new (asl,w as g) =
    let e = find_term (fun u -> can (term_match [] elpat) u) w in
    let _,i,_ = term_match [] elpat e in
    let t = rev_assoc `t:num` i in
    let th = B2BP2AUX_arith_prove asl (mk_eq(kv,t)) in
    (SUBST1_TAC th THEN
     REWRITE_TAC[ARITH_RULE `!a b t. (a + (t * b + 1) = a + b * t + 1) <=> T`]) g in
  (REWRITE_TAC[MAP_APPEND; MEM_APPEND; append_SmartAppend; append_thm; compile_aux_def;
               MAP; MEM; FST] THEN
   MAP_EVERY (fun b -> ASM_CASES_TAC (mk_binop `(<):num->num->bool` kv b)) bounds THEN
   FIRST ((fun (asl,w as g) -> CONTR_TAC (B2BP2AUX_arith_prove asl `F`) g) ::
          map try_ih ihs @ [try_new])) g;;

let B2BP2AUX_aux_contains_sing = prove
 (`(!n e c aux m.
     compile_exps_sing n e = (c,aux,m)
     ==> n <= m /\
         !k. n <= k /\ k < m
             ==> MEM (bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1)) (MAP FST (append aux))) /\
   (!n es cs aux m.
     compile_exps_list n es = (cs,aux,m)
     ==> n <= m /\
         !k. n <= k /\ k < m
             ==> MEM (bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1)) (MAP FST (append aux)))`,
  MATCH_MP_TAC compile_exps_sing_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) -> if is_imp w && not (is_eq (fst (dest_imp w)))
     then DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) g else ALL_TAC g) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_exps_sing_def] THEN
  REPEAT PAIRARG_TAC THEN TRY COND_CASES_TAC THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  B2BP2AUX_IH_ALL_TAC THEN (CONJ_TAC THENL
   [(fun (asl,w as g) -> ACCEPT_TAC (B2BP2AUX_arith_prove asl w) g);
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP]) THEN
    FIRST [(fun (asl,w as g) -> CONTR_TAC (B2BP2AUX_arith_prove asl `F`) g);
           B2BP2AUX_RANGE_TAC]]));;

(* HOL4 line 5655 *)
let compile_exps_aux_contains = prove
 (`!n es c aux n1.
     bvl_to_bvi_compile_exps n es = (c,aux,n1)
     ==> {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n <= k /\ k < n1} SUBSET
         set_of_list (MAP FST (append aux))`,
  REWRITE_TAC[GSYM (CONJUNCT2 compile_exps_sing)] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 B2BP2AUX_aux_contains_sing)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SET_OF_LIST] THEN MESON_TAC[]);;

let B2BP2AUX_R_SUBSET_of = prove
 (`!n m l. (!k. n <= k /\ k < m ==> MEM (bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1)) l)
           ==> {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n <= k /\ k < m} SUBSET
               set_of_list l`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SET_OF_LIST] THEN MESON_TAC[]);;

(* HOL4 line 5697 *)
let compile_single_get_code_labels = prove
 (`!n p code m x y.
     bvl_to_bvi_compile_single n p = (code,m)
     ==> UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (append code))) SUBSET
         (IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces) (bvl_get_code_labels (SND (SND p)))
          UNION set_of_list (MAP FST (append code))) UNION
         set_of_list (MAP FST (bvl_to_bvi_stubs x y))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `q2:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `q2:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[compile_single_eq; SND] THEN
  B2BP2AUX_PAIR_TAC `compile_exps_sing n e` "c" "p2" THEN
  B2BP2AUX_PAIR_TAC `p2:(num#num#bvi_exp)app_list#num` "aux" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) =
    `code:(num#num#bvi_exp)app_list` with Failure _ -> false)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 (SPECL [`x:num`; `y:num`] B2BP2AUX_labels_sing)) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "compile_exps_sing"
                     with Failure _ -> false)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 B2BP2AUX_aux_contains_sing) o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "compile_exps_sing"
                     with Failure _ -> false)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP B2BP2AUX_R_SUBSET_of o CONJUNCT2) THEN
  REWRITE_TAC[append_SmartAppend; append_thm; APPEND; MAP; set_of_list; UNIONS_INSERT; o_THM;
              bvi_letProof_compile_exp_code_labels; SND; FST] THEN
  REPEAT STRIP_TAC THEN
  (fun (asl,w as g) ->
     let sets = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET"
                                  with Failure _ -> false) (map snd asl) in
     let ins = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "INSERT"
                                   with Failure _ -> false) w in
     B2BP2AUX_ABS_SET_TAC (ISPECL [lhand ins; rand ins] SUBSET_OF_INSERT :: sets) g));;

let B2BP2AUX_compile_single_mono = prove
 (`!n p code m. bvl_to_bvi_compile_single n p = (code,m) ==> n <= m`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `p:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `name:num` (X_CHOOSE_THEN `q2:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `q2:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ar:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[compile_single_eq] THEN
  B2BP2AUX_PAIR_TAC `compile_exps_sing n e` "c" "p2" THEN
  B2BP2AUX_PAIR_TAC `p2:(num#num#bvi_exp)app_list#num` "aux" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> try rhs(concl th) = `m:num`
                                                     with Failure _ -> false)) THEN
  ASM_MESON_TAC[CONJUNCT1 B2BP2AUX_aux_contains_sing]);;

(* HOL4 line 5719 *)
let compile_list_get_code_labels = prove
 (`!n p code m x y.
     bvl_to_bvi_compile_list n p = (code,m)
     ==> n <= m /\
         UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (append code))) SUBSET
         (set_of_list (MAP FST (append code)) UNION
          IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
            (UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) p)))) UNION
         set_of_list (MAP FST (bvl_to_bvi_stubs x y))`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_to_bvi_compile_list_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_var (rhs (concl th))))) THEN
    REWRITE_TAC[append_thm; MAP; set_of_list; UNIONS_0; EMPTY_SUBSET; LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_list_def; LET_DEF; LET_END_DEF] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_single n h` "code1" "n1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n1 t` "code2" "n2" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n1:num`; `code2:(num#num#bvi_exp)app_list`; `n2:num`;
                                `x:num`; `y:num`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `h:num#num#bvl_exp`; `code1:(num#num#bvi_exp)app_list`; `n1:num`;
                `x:num`; `y:num`] compile_single_get_code_labels) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n <= n1` ASSUME_TAC THENL
   [MATCH_MP_TAC B2BP2AUX_compile_single_mono THEN
    MAP_EVERY EXISTS_TAC [`h:num#num#bvl_exp`; `code1:(num#num#bvi_exp)app_list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[append_SmartAppend; MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION; MAP;
              set_of_list; UNIONS_INSERT; o_THM; IMAGE_UNION] THEN
  (fun (asl,w as g) ->
     let sets = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET"
                                  with Failure _ -> false) (map snd asl) in
     B2BP2AUX_ABS_SET_TAC sets g));;

(* the code labels of the stubs *)
let B2BP2AUX_stubs_labels = prove
 (`!st kk. UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) (bvl_to_bvi_stubs st kk)))
           SUBSET st INSERT set_of_list (MAP FST (bvl_to_bvi_stubs st kk))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[B2BP2AUX_MAP_FST_stubs] THEN
  REWRITE_TAC[bvl_to_bvi_stubs_def; MAP; set_of_list; UNIONS_INSERT; UNIONS_0; o_THM; SND;
              AllocGlobal_code_def; CopyGlobals_code_def; InitGlobals_code_def;
              ListLength_code_def; FromListByte_code_def; ToListByte_code_def;
              SumListLength_code_def; ConcatByte_code_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  REWRITE_TAC[bvi_get_code_labels_def; assign_get_code_label_def; MAP; set_of_list;
              UNIONS_INSERT; UNIONS_0; UNION_EMPTY; AllocGlobal_location_eq;
              CopyGlobals_location_eq; InitGlobals_location_eq; ListLength_location_eq;
              FromListByte_location_eq; ToListByte_location_eq; SumListLength_location_eq;
              ConcatByte_location_eq] THEN
  CASE_REWRITE_TAC[bvi_get_code_labels_def; UNION_EMPTY; UNIONS_0; set_of_list; MAP;
                   assign_get_code_label_def] THEN
  SET_TAC[]);;

(* HOL4 line 5761 (HOL4 UNION binds tighter than INSERT) *)
let bvl_to_bviProof_compile_prog_get_code_labels = prove
 (`!s n p t q m.
     bvl_to_bvi_compile_prog s n p = (t,q,m)
     ==> UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) q)) SUBSET
         (bvl_num_stubs + s * bvl_to_bvi_namespaces) INSERT
         (set_of_list (MAP FST q) UNION
          IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
            (UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) p))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n p` "code" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  (fun (asl,w as g) ->
     let st = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "bvl_to_bvi_stubs"
                                  with Failure _ -> false) w in
     let _,args = strip_comb st in
     (MP_TAC(SPECL [el 0 args; el 1 args] B2BP2AUX_stubs_labels) THEN
      MP_TAC(SPECL [`n:num`; `p:(num#num#bvl_exp)list`; `code:(num#num#bvi_exp)app_list`;
                    `m1:num`; el 0 args; el 1 args] compile_list_get_code_labels)) g) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION] THEN
  SUBGOAL_THEN `bvl_num_stubs + bvl_to_bvi_namespaces * s = bvl_num_stubs + s * bvl_to_bvi_namespaces`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
  (fun (asl,w as g) ->
     let sets = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET"
                                  with Failure _ -> false) (map snd asl) in
     B2BP2AUX_ABS_SET_TAC sets g));;

(* HOL4 line 5790 *)
let compile_get_code_labels = prove
 (`!start c names prog loc code inlines bvi_inlines n1 n2 n3 names'.
     bvl_to_bvi_compile start c names prog = (loc,code,inlines,bvi_inlines,n1,n2,n3,names')
     ==> UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) code)) SUBSET
         (bvl_num_stubs + start * bvl_to_bvi_namespaces) INSERT
         (((set_of_list (MAP FST code) UNION
            IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
              (UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) prog)))) UNION
           {(bvl_num_stubs + 2) + k * bvl_to_bvi_namespaces | k |
            (bvl_num_stubs + 2) + k * bvl_to_bvi_namespaces < n2}) UNION
          {(bvl_num_stubs + 3) + k * bvl_to_bvi_namespaces | k |
           (bvl_num_stubs + 3) + k * bvl_to_bvi_namespaces < n3})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  (fun (asl,w as g) ->
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u))) =
               "bvl_inline_compile_prog" with Failure _ -> false) w in
     B2BP2AUX_PAIR_TAC t "inl" "prog1" g) THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_prog start 0 prog1` "loc1" "q1" THEN
  B2BP2AUX_PAIR_TAC `q1:(num#num#bvi_exp)list#num` "code1" "m1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
                       (bvl_num_stubs + 2) code1` "m2" "code2" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)
                       (bvl_num_stubs + 3) code2` "m3" "code3" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvi_inline_compile_prog code3` "bi" "code4" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND)
                (code3:(num#num#bvi_exp)list)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC bvi_inlineProof_compile_prog_code_labels THEN
    EXISTS_TAC `bi:(num#bvi_exp)spt` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(GEN_ALL bvi_tmcProof_compile_prog_good_code_labels) THEN
  MAP_EVERY EXISTS_TAC [`bvl_to_bvi_config_do_tmc c`; `bvl_num_stubs + 3`;
                        `code2:(num#num#bvi_exp)list`; `n3:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUBSET; IN_INSERT; IN_UNION] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC(GEN_ALL bvi_tailrecProof_compile_prog_good_code_labels) THEN
  MAP_EVERY EXISTS_TAC [`bvl_to_bvi_config_do_tailrec c`; `bvl_num_stubs + 2`;
                        `code1:(num#num#bvi_exp)list`; `n2:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUBSET; IN_INSERT; IN_UNION] THEN MESON_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && is_var (rhs (concl th)) &&
    mem (fst (dest_var (lhs (concl th)))) ["code4"; "m2"; "m3"; "m1"; "loc1"]))) THEN
  MP_TAC(ISPECL [`start:num`; `0`; `prog1:(num#num#bvl_exp)list`; `loc:num`;
                 `code1:(num#num#bvi_exp)list`; `n1:num`]
    bvl_to_bviProof_compile_prog_get_code_labels) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `set_of_list (MAP FST (code1:(num#num#bvi_exp)list)) SUBSET
                set_of_list (MAP FST (code:(num#num#bvi_exp)list))` ASSUME_TAC THENL
   [SUBGOAL_THEN `MAP FST (code:(num#num#bvi_exp)list) = MAP FST (code3:(num#num#bvi_exp)list)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC compile_inc_MAP_FST THEN
      MAP_EVERY EXISTS_TAC [`LN:(num#bvi_exp)spt`; `bi:(num#bvi_exp)spt`] THEN
      ASM_REWRITE_TAC[GSYM bvi_inline_compile_prog_def];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(GEN_ALL bvi_tmcProof_compile_prog_keeps_names) THEN
    MAP_EVERY EXISTS_TAC [`bvl_to_bvi_config_do_tmc c`; `bvl_num_stubs + 3`;
                          `code2:(num#num#bvi_exp)list`; `n3:num`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(GEN_ALL bvi_tailrecProof_compile_prog_keeps_names) THEN
    MAP_EVERY EXISTS_TAC [`bvl_to_bvi_config_do_tailrec c`; `bvl_num_stubs + 2`;
                          `code1:(num#num#bvi_exp)list`; `n2:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ISPEC `\k. bvl_num_stubs + k * bvl_to_bvi_namespaces`
    IMAGE_SUBSET) o MATCH_MP bvl_inlineProof_compile_prog_get_code_labels o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
      "bvl_inline_compile_prog" with Failure _ -> false)) THEN
  (fun (asl,w as g) ->
     let sets = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET"
                                  with Failure _ -> false) (map snd asl) in
     B2BP2AUX_ABS_SET_TAC sets g));;

let B2BP2AUX_R2_split = prove
 (`!a b c. a <= b /\ b <= c ==>
     {(bvl_num_stubs + k * bvl_to_bvi_namespaces) + 1 | k | a <= k /\ k < c} =
     {(bvl_num_stubs + k * bvl_to_bvi_namespaces) + 1 | k | a <= k /\ k < b} UNION
     {(bvl_num_stubs + k * bvl_to_bvi_namespaces) + 1 | k | b <= k /\ k < c}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `z:num` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `k < b` THENL
     [DISJ1_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* the names of the auxiliary functions of compile_exps_sing *)
let B2BP2AUX_aux_names = prove
 (`!n e c aux m.
     compile_exps_sing n e = (c,aux,m)
     ==> n <= m /\
         set_of_list (MAP FST (append aux)) =
         {(bvl_num_stubs + k * bvl_to_bvi_namespaces) + 1 | k | n <= k /\ k < m}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 B2BP2AUX_aux_contains_sing)) THEN
  SUBGOAL_THEN `bvl_to_bvi_compile_exps n [e] = ([c],aux,m)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONJUNCT1 compile_exps_sing] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exps_aux_sorted) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_ELIM_THM] THEN
  X_GEN_TAC `z:num` THEN EQ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1)
                   (MAP FST (append (aux:(num#num#bvi_exp)app_list)))` THEN
    UNDISCH_TAC `ALL (between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
                   (bvl_num_stubs + bvl_to_bvi_namespaces * m))
                   (MAP FST (append (aux:(num#num#bvi_exp)app_list)))` THEN
    REWRITE_TAC[GSYM ALL_MEM; between_def] THEN
    DISCH_THEN(MP_TAC o SPEC `z:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `z:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN EXISTS_TAC `j:num` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN
    REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "MEM" with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[GSYM ADD_ASSOC]]);;

(* HOL4 line 5830 *)
let compile_list_code_labels_domain = prove
 (`!n p code m.
     bvl_to_bvi_compile_list n p = (code,m)
     ==> n <= m /\
         set_of_list (MAP FST (append code)) =
         IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces) (set_of_list (MAP FST p)) UNION
         {(bvl_num_stubs + k * bvl_to_bvi_namespaces) + 1 | k | n <= k /\ k < m}`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_to_bvi_compile_list_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_var (rhs (concl th))))) THEN
    REWRITE_TAC[append_thm; MAP; set_of_list; IMAGE_CLAUSES; UNION_EMPTY; LE_REFL] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_list_def; LET_DEF; LET_END_DEF] THEN
  B2BP2AUX_PAIR_TAC `h:num#num#bvl_exp` "name" "q2" THEN
  B2BP2AUX_PAIR_TAC `q2:num#bvl_exp` "ar" "e" THEN
  REWRITE_TAC[compile_single_eq] THEN
  B2BP2AUX_PAIR_TAC `compile_exps_sing n e` "c" "p2" THEN
  B2BP2AUX_PAIR_TAC `p2:(num#num#bvi_exp)app_list#num` "aux" "n1" THEN CASE_REWRITE_TAC[] THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n1 t` "code2" "n2" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n1:num`; `code2:(num#num#bvi_exp)app_list`; `n2:num`] o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP2AUX_aux_names o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "compile_exps_sing"
                     with Failure _ -> false)) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `n1:num`; `n2:num`] B2BP2AUX_R2_split) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[append_SmartAppend; append_thm; APPEND; MAP_APPEND; SET_OF_LIST_APPEND; MAP;
                  set_of_list; FST; IMAGE_CLAUSES] THEN BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `bvl_num_stubs + bvl_to_bvi_namespaces * name =
                          bvl_num_stubs + name * bvl_to_bvi_namespaces`] THEN
  CONV_TAC(DEPTH_CONV B2BP2AUX_INSERT_CONV) THEN REWRITE_TAC[UNION_ACI]);;

(* HOL4 line 5864 (x and y are free in HOL4) *)
let compile_prog_code_labels_domain = prove
 (`!s n p t q m x y.
     bvl_to_bvi_compile_prog s n p = (t,q,m)
     ==> set_of_list (MAP FST q) =
         (IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces) (set_of_list (MAP FST p)) UNION
          {(bvl_num_stubs + k * bvl_to_bvi_namespaces) + 1 | k | n <= k /\ k < m}) UNION
         set_of_list (MAP FST (bvl_to_bvi_stubs x y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  B2BP2AUX_PAIR_TAC `bvl_to_bvi_compile_list n p` "code" "m1" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && not (is_var (lhs (concl th)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_list_code_labels_domain o
    check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
      "bvl_to_bvi_compile_list" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[MAP_APPEND; SET_OF_LIST_APPEND; B2BP2AUX_MAP_FST_stubs] THEN
  REWRITE_TAC[UNION_ACI]);;
