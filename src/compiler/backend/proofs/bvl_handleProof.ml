(* ========================================================================= *)
(* bvl_handleProof: port of HOL4 compiler/backend/proofs/                    *)
(* bvl_handleProofScript.sml (CakeML v3479).  Correctness proof for          *)
(* bvl_handle.  BVLPROPSAUX_ names are local helpers (not HOL4 names).       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;

type_invention_error := true;;

(* a local helper: do_app never raises *)
let BVLPROPSAUX_do_app_not_Rraise = prove
 (`!op vs (s:(A,B)bvl_state) a. ~(bvl_do_app op vs s = Rerr (Rraise a))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP bvl_do_app_err) THEN
  REWRITE_TAC[distinctness "error_result"; injectivity "error_result"] THEN
  MESON_TAC[distinctness "error_result"]);;

(* HOL4 leaves a and r free (and binds s twice); here a and r are bound *)
(* in each conjunct                                                       *)
let can_raise_thm = prove
 (`(!e env (s:(A,B)bvl_state) (a:bvl_v) r.
      bvl_evaluate ([e],env,s) = (Rerr (Rraise a),r) ==> can_raise e) /\
   (!es env (s:(A,B)bvl_state) (a:bvl_v) r.
      bvl_evaluate (es,env,s) = (Rerr (Rraise a),r) ==> can_raise1 es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                          BVLPROPSAUX_is_ev (lhs (concl th)))) THEN
  REWRITE_TAC[can_raise_def] THEN
  (fun (asl,w as g) ->
     let ev = find_term BVLPROPSAUX_is_ev w in
     let lst = fst (dest_pair (rand ev)) in
     if is_comb lst && is_comb (rator lst) && is_var (rand lst)
     then ONCE_REWRITE_TAC[bvl_evaluate_CONS] g
     else ONCE_REWRITE_TAC[bvl_evaluate_def] g) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC BVLPROPSAUX_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_do_app_not_Rraise]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  ASM_MESON_TAC[]);;

(* HOL4 [simp] *)
let handle_adj_vars_0 = prove
 (`(!x l. handle_adj_vars l 0 x = x) /\ (!x l. handle_adj_vars1 l 0 x = x)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  REWRITE_TAC[handle_adj_vars_def; ADD_CLAUSES; COND_ID] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [handle_adj_vars_0];;

(* local helpers: Var and Force read the environment only at their index *)
let BVLPROPSAUX_evaluate_Var_Force_env = prove
 (`!n n' env env' (s:(A,B)bvl_state).
     (n' < LENGTH env' <=> n < LENGTH env) /\
     (n < LENGTH env ==> EL n' env' = EL n env) ==>
     bvl_evaluate ([bvl_Var n'],env',s) = bvl_evaluate ([bvl_Var n],env,s) /\
     !loc. bvl_evaluate ([bvl_Force loc n'],env',s) =
           bvl_evaluate ([bvl_Force loc n],env,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `n < LENGTH (env:bvl_v list)` THEN
  ASM_SIMP_TAC[]);;

let BVLPROPSAUX_hav_index = prove
 (`!v (xs:A list) (a:A list) env.
     ((if v < LENGTH xs then v else v + LENGTH a) < LENGTH (APPEND xs (APPEND a env)) <=>
      v < LENGTH (APPEND xs env)) /\
     (v < LENGTH (APPEND xs env) ==>
      EL (if v < LENGTH xs then v else v + LENGTH a) (APPEND xs (APPEND a env)) =
      EL v (APPEND xs env))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EL_APPEND] THEN
  ASM_SIMP_TAC[ARITH_RULE `v < l ==> v < l + n`; ARITH_RULE `~(v < l) ==> ~(v + a < l)`;
               ARITH_RULE `~(v < l) ==> (v + a) - l = (v - l) + a`;
               ARITH_RULE `~(v < l) ==> ((v + a < l + a + e) <=> v < l + e)`;
               ARITH_RULE `~(v < l) ==> ~((v - l) + a < a)`; ADD_SUB]);;

let BVLPROPSAUX_evaluate_Var_Force_hav = prove
 (`!v (xs:bvl_v list) a env (r:(A,B)bvl_state).
     bvl_evaluate ([bvl_Var (if v < LENGTH xs then v else v + LENGTH a)],
                   APPEND xs (APPEND a env),r) =
     bvl_evaluate ([bvl_Var v],APPEND xs env,r) /\
     !loc. bvl_evaluate ([bvl_Force loc (if v < LENGTH xs then v else v + LENGTH a)],
                         APPEND xs (APPEND a env),r) =
           bvl_evaluate ([bvl_Force loc v],APPEND xs env,r)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC BVLPROPSAUX_evaluate_Var_Force_env THEN
  REWRITE_TAC[BVLPROPSAUX_hav_index]);;

let evaluate_handle_adj_vars_lemma = prove
 (`(!x xs a env (r:(A,B)bvl_state).
      bvl_evaluate ([handle_adj_vars (LENGTH xs) (LENGTH a) x],
                    APPEND xs (APPEND a env),r) =
      bvl_evaluate ([x],APPEND xs env,r)) /\
   (!x xs a env (r:(A,B)bvl_state).
      bvl_evaluate (handle_adj_vars1 (LENGTH xs) (LENGTH a) x,
                    APPEND xs (APPEND a env),r) =
      bvl_evaluate (x,APPEND xs env,r))`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[handle_adj_vars_def; BVLPROPSAUX_evaluate_Var_Force_hav] THEN
  TRY (ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THENL
   [(* Let *)
    MP_TAC(ISPEC `bvl_evaluate (a0,APPEND xs env,r:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
      (X_CHOOSE_THEN `s1:(A,B)bvl_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    CASES_ON `r1:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH o
                check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND (a':bvl_v list) xs`; `a:bvl_v list`;
                                  `env:bvl_v list`; `s1:(A,B)bvl_state`] o
                  check (fun th -> is_forall (concl th) &&
                                   free_in `a1:bvl_exp` (concl th))) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; APPEND_ASSOC] THEN REWRITE_TAC[ADD_AC];
    (* Handle *)
    FIRST_X_ASSUM(fun ih ->
      if is_forall (concl ih) && free_in `a1:bvl_exp` (concl ih) then
        let v = `hav_v:bvl_v` in
        let th = GEN v (GEN `xs:bvl_v list`
                   (REWRITE_RULE[LENGTH; APPEND; ADD1]
                      (SPEC (mk_comb(mk_comb(`CONS:bvl_v->bvl_v list->bvl_v list`,v),
                                     `xs:bvl_v list`)) ih))) in
        REWRITE_TAC[th]
      else NO_TAC)]);;

(* HOL4 leaves x2 free *)
let evaluate_handle_adj_vars = prove
 (`!x2 xs l a env (r:(A,B)bvl_state).
     l <= LENGTH env ==>
     bvl_evaluate ([handle_adj_vars (LENGTH xs) (l + LENGTH a) x2],
                   APPEND xs (APPEND a env),r) =
     bvl_evaluate ([handle_adj_vars (LENGTH xs) l x2],APPEND xs env,r)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ys1:bvl_v list` (X_CHOOSE_THEN `ys2:bvl_v list`
    STRIP_ASSUME_TAC) o MATCH_MP LESS_EQ_LENGTH) THEN
  RVEQ_TAC THEN
  MP_TAC(ISPECL [`x2:bvl_exp`; `xs:bvl_v list`; `APPEND (a:bvl_v list) ys1`;
                 `ys2:bvl_v list`; `r:(A,B)bvl_state`]
                (CONJUNCT1 evaluate_handle_adj_vars_lemma)) THEN
  MP_TAC(ISPECL [`x2:bvl_exp`; `xs:bvl_v list`; `ys1:bvl_v list`;
                 `ys2:bvl_v list`; `r:(A,B)bvl_state`]
                (CONJUNCT1 evaluate_handle_adj_vars_lemma)) THEN
  REWRITE_TAC[LENGTH_APPEND; APPEND_ASSOC] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[ADD_AC]);;

(* HOL4 leaves x1, x2, r, d, l, env free *)
let handle_adj_vars_evaluate = prove
 (`!x1 x2 (r:(A,B)bvl_state) d l env.
     (!env. bvl_evaluate ([x1],env,r) = bvl_evaluate ([x2],env,r)) /\
     d + l <= LENGTH env ==>
     bvl_evaluate ([handle_adj_vars d l x1],env,r) =
     bvl_evaluate ([handle_adj_vars d l x2],env,r)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ys1:bvl_v list` (X_CHOOSE_THEN `ys2:bvl_v list`
    STRIP_ASSUME_TAC) o MATCH_MP LESS_EQ_LENGTH) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
                                          rator (lhs (concl th)) = `LENGTH:bvl_v list->num`)) THEN
  REWRITE_TAC[LENGTH_EQ_SUM] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`x1:bvl_exp`; `l1:bvl_v list`; `l2:bvl_v list`;
                 `ys2:bvl_v list`; `r:(A,B)bvl_state`]
                (CONJUNCT1 evaluate_handle_adj_vars_lemma)) THEN
  MP_TAC(ISPECL [`x2:bvl_exp`; `l1:bvl_v list`; `l2:bvl_v list`;
                 `ys2:bvl_v list`; `r:(A,B)bvl_state`]
                (CONJUNCT1 evaluate_handle_adj_vars_lemma)) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* local helpers for evaluate_handle_simp: a Handle around an expression    *)
(* that cannot raise is transparent                                         *)
let BVLPROPSAUX_no_raise = prove
 (`!e env (s:(A,B)bvl_state) r. ~can_raise e ==>
     !a. ~(bvl_evaluate ([e],env,s) = (Rerr (Rraise a),r))`,
  MESON_TAC[can_raise_thm]);;

let BVLPROPSAUX_no_raise1 = prove
 (`!es env (s:(A,B)bvl_state) r. ~can_raise1 es ==>
     !a. ~(bvl_evaluate (es,env,s) = (Rerr (Rraise a),r))`,
  MESON_TAC[can_raise_thm]);;

let BVLPROPSAUX_Handle_no_raise = prove
 (`!e x env (s:(A,B)bvl_state).
     ~can_raise e ==>
     bvl_evaluate ([bvl_Handle e x],env,s) = bvl_evaluate ([e],env,s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate ([e],env,s:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"] THEN
  CASES_ON `a:(bvl_v)error_result` THEN REWRITE_TAC[case_def "error_result"] THEN
  ASM_MESON_TAC[BVLPROPSAUX_no_raise]);;

(* local helpers for the make_handle case of evaluate_handle_simp: moving a *)
(* Handle into Raise, Let and If whose tested parts cannot raise           *)
let BVLPROPSAUX_Handle_Raise = prove
 (`!r x env (s:(A,B)bvl_state).
     ~can_raise r ==>
     bvl_evaluate ([bvl_Handle (bvl_Raise r) x],env,s) =
     bvl_evaluate ([bvl_Let [r] x],env,s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate ([r],env,s:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[case_def "result"; case_def "error_result"; pair_CASE] THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING) THEN
    REWRITE_TAC[HD; APPEND];
    CASES_ON `a:(bvl_v)error_result` THEN REWRITE_TAC[case_def "error_result"] THEN
    ASM_MESON_TAC[BVLPROPSAUX_no_raise]]);;

let BVLPROPSAUX_Handle_Let = prove
 (`!xs b x2 l env (s:(A,B)bvl_state).
     ~can_raise1 xs /\ l <= LENGTH env ==>
     bvl_evaluate ([bvl_Handle (bvl_Let xs b) (handle_adj_vars 1 l x2)],env,s) =
     bvl_evaluate ([bvl_Let xs (bvl_Handle b (handle_adj_vars 1 (l + LENGTH xs) x2))],
                   env,s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate (xs,env,s:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[case_def "result"; case_def "error_result"; pair_CASE] THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH) THEN
    ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!v r. bvl_evaluate ([handle_adj_vars 1 (l + LENGTH (a:bvl_v list)) x2],
                          CONS v (APPEND a env),r:(A,B)bvl_state) =
            bvl_evaluate ([handle_adj_vars 1 l x2],CONS v env,r)`
     (fun th -> REWRITE_TAC[th]) THEN
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`x2:bvl_exp`; `[v:bvl_v]`; `l:num`; `a:bvl_v list`;
                   `env:bvl_v list`; `r:(A,B)bvl_state`] evaluate_handle_adj_vars) THEN
    ASM_REWRITE_TAC[LENGTH; APPEND; ONE];
    CASES_ON `a:(bvl_v)error_result` THEN REWRITE_TAC[case_def "error_result"] THEN
    ASM_MESON_TAC[BVLPROPSAUX_no_raise1]]);;

let BVLPROPSAUX_Handle_If = prove
 (`!b1 b2 b3 x env (s:(A,B)bvl_state).
     ~can_raise b1 ==>
     bvl_evaluate ([bvl_Handle (bvl_If b1 b2 b3) x],env,s) =
     bvl_evaluate ([bvl_If b1 (bvl_Handle b2 x) (bvl_Handle b3 x)],env,s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate ([b1],env,s:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[case_def "result"; case_def "error_result"; pair_CASE] THENL
   [REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    TRY (FIRST_ASSUM CONTR_TAC) THEN
    REWRITE_TAC[case_def "result"; case_def "error_result"; pair_CASE];
    CASES_ON `a:(bvl_v)error_result` THEN REWRITE_TAC[case_def "error_result"] THEN
    ASM_MESON_TAC[BVLPROPSAUX_no_raise]]);;

let BVLPROPSAUX_INST_B_TAC (bs:term list) : tactic =
  RULE_ASSUM_TAC(fun th ->
    let vs,_ = strip_forall (concl th) in
    let names = map (fst o dest_var) vs in
    if length vs = 3 && forall (fun n -> mem n ["b1";"b2";"b3"]) names then
      SPECL (map (fun n -> assoc n [("b1",el 0 bs); ("b2",el 1 bs); ("b3",el 2 bs)]) names) th
    else th);;


let evaluate_handle_simp = prove
 (`(!x env (s:(A,B)bvl_state).
      bvl_evaluate ([handle_simp x],env,s) = bvl_evaluate ([x],env,s)) /\
   (!xs env (s:(A,B)bvl_state).
      bvl_evaluate (handle_simp_list xs,env,s) = bvl_evaluate (xs,env,s)) /\
   (!x1 x2 l env (s:(A,B)bvl_state).
      l <= LENGTH env ==>
      bvl_evaluate ([make_handle x1 x2 l],env,s) =
      bvl_evaluate ([bvl_Handle x1 (handle_adj_vars 1 l x2)],env,s))`,
  MATCH_MP_TAC handle_simp_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [ONCE_REWRITE_TAC[handle_simp_def] THEN ASM_SIMP_TAC[LE_0; handle_adj_vars_0];
    REWRITE_TAC[handle_simp_def];
    ONCE_REWRITE_TAC[handle_simp_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[handle_simp_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[handle_simp_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[handle_simp_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[handle_simp_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[handle_simp_def];
    ONCE_REWRITE_TAC[handle_simp_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[handle_simp_def];
    ONCE_REWRITE_TAC[handle_simp_def] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
    ASM_REWRITE_TAC[];
    (ONCE_REWRITE_TAC[handle_simp_def] THEN
    CASES_ON `dest_handle_Raise x` THEN ASM_REWRITE_TAC[case_def "option"] THENL
     [CASES_ON `dest_handle_Let x` THEN ASM_REWRITE_TAC[case_def "option"] THENL
       [CASES_ON `dest_handle_If x` THEN ASM_REWRITE_TAC[case_def "option"] THENL
         [(RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN
  SUBGOAL_THEN `!v (s1:(A,B)bvl_state).
      bvl_evaluate ([handle_adj_vars 1 l (handle_simp x2)],CONS v env,s1) =
      bvl_evaluate ([handle_adj_vars 1 l x2],CONS v env,s1)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC handle_adj_vars_evaluate THEN
    ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[]);
          (FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BVLPAUX_dest_handle_If_eq] o
                check (fun th -> concl th = `dest_handle_If x = SOME a`)) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  BVLPROPSAUX_INST_B_TAC [`dhi1:bvl_exp`; `dhi2:bvl_exp`; `dhi3:bvl_exp`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; injectivity "sum";
                              distinctness "sum"; PAIR_EQ]) THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[BVLPROPSAUX_Handle_If] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_SIMP_TAC[BVLPROPSAUX_Handle_no_raise])];
        (FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BVLPAUX_dest_handle_Let_eq] o
                check (fun th -> concl th = `dest_handle_Let x = SOME a`)) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    let vs,_ = strip_forall (concl th) in
    if length vs = 2 && type_of (el 1 vs) = `:bvl_exp list` &&
       type_of (el 0 vs) = `:bvl_exp`
    then SPECL [`dhl2:bvl_exp`; `dhl1:bvl_exp list`] th else th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[BVLPROPSAUX_Handle_Let] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `bvl_evaluate (dhl1,env,s:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH o
              check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)) &&
                               fst (dest_pair (rand (concl th))) = `Rval a':(bvl_v list,bvl_v)result`)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC)];
      (FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BVLPAUX_dest_handle_Raise_eq] o
                check (fun th -> concl th = `dest_handle_Raise x = SOME a`)) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    let vs,_ = strip_forall (concl th) in
    if length vs = 1 && type_of (hd vs) = `:bvl_exp` then SPEC `a:bvl_exp` th else th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ]) THEN
  ASM_SIMP_TAC[BVLPROPSAUX_Handle_Raise] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate ([a],env,s:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING o
              check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)))) THEN
  MATCH_MP_TAC handle_adj_vars_evaluate THEN
  ASM_REWRITE_TAC[LENGTH; APPEND] THEN ASM_ARITH_TAC)])]);;

(* HOL4 [simp] *)
let evaluate_SmartLet = prove
 (`!xs x env (s:(A,B)bvl_state).
     bvl_evaluate ([SmartLet xs x],env,s) = bvl_evaluate ([bvl_Let xs x],env,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartLet_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN
  ASM_REWRITE_TAC[bvl_evaluate_def; pair_CASE; case_def "result"; APPEND]);;
let _ = cake_add_simps [evaluate_SmartLet];;

let let_ok_def = sem1aux_def
  `(let_ok (bvl_Let xs b) <=> ALL isVar xs /\ bVarBound (LENGTH xs) [b]) /\
   (let_ok _ <=> F)`;;

(* HOL4: Termination WF_REL_TAC with measure exp1_size *)
let handle_ok_def = sem1aux_def_wf
  `measure (list_size bvl_exp_size)`
  SEM1AUX_TC_TAC
  `(handle_ok [] <=> T) /\
   (handle_ok (CONS (x:bvl_exp) (CONS y xs)) <=>
      handle_ok [x] /\ handle_ok (CONS y xs)) /\
   (handle_ok [bvl_Var v] <=> T) /\
   (handle_ok [bvl_If x1 x2 x3] <=>
      handle_ok [x1] /\ handle_ok [x2] /\ handle_ok [x3]) /\
   (handle_ok [bvl_Let xs x2] <=>
      if LENGTH xs = 0 then
        let_ok x2 /\ (!ys y. x2 = bvl_Let ys y ==> handle_ok [y])
      else
        handle_ok xs /\ handle_ok [x2]) /\
   (handle_ok [bvl_Raise x1] <=> handle_ok [x1]) /\
   (handle_ok [bvl_Tick x1] <=> handle_ok [x1]) /\
   (handle_ok [bvl_Op op xs] <=> handle_ok xs) /\
   (handle_ok [bvl_Handle x1 x2] <=>
      match x1 with
        bvl_Let xs b ->
          ALL isVar xs /\ bVarBound (LENGTH xs) [b] /\
          handle_ok [b] /\ handle_ok [x2]
      | _ -> F) /\
   (handle_ok [bvl_Force loc n] <=> T) /\
   (handle_ok [bvl_Call ticks dest xs] <=> handle_ok xs)`;;

let handle_ok_ind = cake_ind "handle_ok";;

(* HOL4: evaluate_genlist_vars specialised to 0, env ++ ys, LENGTH env, s *)
(* and simplified with TAKE_APPEND1 *)
let evaluate_GENLIST = prove
 (`!env ys (s:(C,FFI)bvl_state).
     bvl_evaluate (list_of_seq bvl_Var (LENGTH env),APPEND env ys,s) = (Rval env,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`0`; `APPEND (env:bvl_v list) ys`; `LENGTH (env:bvl_v list)`;
                 `s:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
  REWRITE_TAC[ADD_CLAUSES; LENGTH_APPEND; LE_ADD; DROP; ETA_AX; TAKE_LENGTH_APPEND]);;

let bvl_handleProof_env_rel_def = cake_def
  `bvl_handleProof_env_rel l (env:bvl_v list) env1 <=>
     LIST_RELi (\i v1 v2. has_var i l ==> v1 = v2) env env1`;;

let env_rel_mk_Union = prove
 (`!env env1 lx ly.
     bvl_handleProof_env_rel (mk_Union lx ly) env env1 <=>
     bvl_handleProof_env_rel lx env env1 /\ bvl_handleProof_env_rel ly env env1`,
  REWRITE_TAC[LIST_RELi_EL_EQN; bvl_handleProof_env_rel_def; has_var_mk_Union] THEN
  MESON_TAC[]);;

let bvl_handleProof_env_rel_length = prove
 (`!l env env1. bvl_handleProof_env_rel l env env1 ==> LENGTH env1 = LENGTH env`,
  SIMP_TAC[LIST_RELi_EL_EQN; bvl_handleProof_env_rel_def]);;

let env_rel_MAPi = prove
 (`!l1 env.
     bvl_handleProof_env_rel l1 env
       (MAPi (\i v. if has_var i l1 then v else bvl_Number (&0)) env)`,
  SIMP_TAC[LIST_RELi_EL_EQN; bvl_handleProof_env_rel_def; LENGTH_MAPi; EL_MAPi]);;

let IMP_EL_SING = prove
 (`!k xs (x:A) ys. k = LENGTH xs ==> EL k (APPEND (APPEND xs [x]) ys) = x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

(* local helper: the general forms of the two ALOOKUP lemmas *)
let BVLPROPSAUX_ALOOKUP_MAPi_gen = prove
 (`!(xs:A list) z.
     (!n k. ~(n = k) ==>
            ALOOKUP (MAPi (\i x. (x,i + z)) (APPEND xs [k])) n =
            ALOOKUP (MAPi (\i x. (x,i + z)) xs) n) /\
     (!k. ~MEM k xs ==>
          ALOOKUP (MAPi (\i x. (x,i + z)) (APPEND xs [k])) k = SOME (LENGTH xs + z))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; MAPi_DEF; ALOOKUP_def; MEM; LENGTH; ADD_CLAUSES] THEN
  REWRITE_TAC[o_DEF] THENL [MESON_TAC[]; ALL_TAC] THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC z`) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  ASM_MESON_TAC[]);;

let ALOOKUP_MAPi_SWAP = prove
 (`!n k (xs:A list).
     ~(n = k) ==>
     ALOOKUP (MAPi (\i x. (x,i)) (APPEND xs [k])) n = ALOOKUP (MAPi (\i x. (x,i)) xs) n`,
  MP_TAC(GEN `xs:A list` (CONJUNCT1 (SPECL [`xs:A list`; `0`] BVLPROPSAUX_ALOOKUP_MAPi_gen))) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[]);;

let ALOOKUP_MAPi_APPEND2 = prove
 (`!(xs:A list) k.
     ~MEM k xs ==>
     ALOOKUP (MAPi (\i x. (x,i)) (APPEND xs [k])) k = SOME (LENGTH xs)`,
  MP_TAC(GEN `xs:A list` (CONJUNCT2 (SPECL [`xs:A list`; `0`] BVLPROPSAUX_ALOOKUP_MAPi_gen))) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[]);;

let IS_SOME_lookup_db_to_set = prove
 (`!n l. IS_SOME (lookup n (db_to_set l)) <=> has_var n l`,
  REWRITE_TAC[lookup_db_to_set] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `lookup n (db_to_set l):(1)option` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF; option_DISTINCT; option_INJ] THEN
  MESON_TAC[one]);;

(* local helpers for evaluate_LetLet *)
let BVLPROPSAUX_evaluate_list_of_seq = prove
 (`!f g n env (s:(A,B)bvl_state).
     (!j. j < n ==> bvl_evaluate ([f j],env,s) = (Rval [g j],s)) ==>
     bvl_evaluate (list_of_seq f n,env,s) = (Rval (list_of_seq g n),s)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; bvl_evaluate_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_evaluate_APPEND] THEN
  SUBGOAL_THEN `bvl_evaluate (list_of_seq f n,env,s:(A,B)bvl_state) =
                (Rval (list_of_seq g n),s)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE; case_def "result"] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE; case_def "result"]);;

let BVLPROPSAUX_evaluate_MAP_Var = prove
 (`!qs env (s:(A,B)bvl_state).
     ALL (\n. n < LENGTH env) qs ==>
     bvl_evaluate (MAP bvl_Var qs,env,s) = (Rval (MAP (\n. EL n env) qs),s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; bvl_evaluate_def; ALL] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  ASM_SIMP_TAC[bvl_evaluate_def; pair_CASE; case_def "result"; HD]);;

let BVLPROPSAUX_ALOOKUP_MAPi_MEM = prove
 (`!(zs:A list) z j.
     ALL_DISTINCT zs /\ MEM j zs ==>
     ?k. k < LENGTH zs /\ EL k zs = j /\
         ALOOKUP (MAPi (\i x. (x,i + z)) zs) j = SOME (k + z)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; ALL_DISTINCT; MAPi_DEF; ALOOKUP_def] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LENGTH; LT_0; EL; HD; ADD_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SUC z`; `j:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `SUC k` THEN
  ASM_REWRITE_TAC[LENGTH; LT_SUC; EL; TL; o_DEF; ADD_CLAUSES] THEN
  SUBGOAL_THEN `~(h:A = j)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     is_comb (lhs (concl th)) && is_comb (rator (lhs (concl th))))) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let BVLPROPSAUX_ALOOKUP_MAPi_NOT_MEM = prove
 (`!(zs:A list) j. ~MEM j zs ==> ALOOKUP (MAPi (\i x. (x,i)) zs) j = NONE`,
  REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; MEM_MAPi] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN ASM_MESON_TAC[MEM_EL]);;

let evaluate_LetLet = prove
 (`!y env env1 extra l1 (s1:(A,B)bvl_state) res.
     (!env2 extra. bvl_handleProof_env_rel l1 env env2 ==>
                   bvl_evaluate ([y],APPEND env2 extra,s1) = res) /\
     bvl_handleProof_env_rel l1 env env1 ==>
     bvl_evaluate ([LetLet (LENGTH env) (db_to_set l1) y],APPEND env1 extra,s1) = res`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LetLet_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[IS_SOME_lookup_db_to_set; ETA_AX] THEN
  ABBREV_TAC `zs = FILTER (\n. has_var n l1) (list_of_seq I (LENGTH (env:bvl_v list)))` THEN
  SUBGOAL_THEN `!j. MEM j zs <=> j < LENGTH (env:bvl_v list) /\ has_var j l1`
    ASSUME_TAC THENL
   [EXPAND_TAC "zs" THEN REWRITE_TAC[MEM_FILTER; MEM_GENLIST; I_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (zs:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "zs" THEN MATCH_MP_TAC FILTER_ALL_DISTINCT THEN
    REWRITE_TAC[ALL_DISTINCT_GENLIST; I_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_handleProof_env_rel_length) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  SUBGOAL_THEN `bvl_evaluate (MAP bvl_Var zs,APPEND env1 extra,s1:(A,B)bvl_state) =
                (Rval (MAP (\n. EL n env) zs),s1)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`zs:num list`; `APPEND (env1:bvl_v list) extra`; `s1:(A,B)bvl_state`]
                  BVLPROPSAUX_evaluate_MAP_Var) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[PAIR_EQ; injectivity "result"] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[EL_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE; case_def "result"; evaluate_SmartLet] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  SUBGOAL_THEN
   (CASE_TERM `!ex. bvl_evaluate (list_of_seq (\n. match ALOOKUP (MAPi (\i x. (x,i)) zs) n with
                                         NONE -> bvl_Op (IntOp (clos_Const (&0))) []
                                       | SOME a -> bvl_Var a) (LENGTH (env:bvl_v list)),
                               APPEND (MAP (\n. EL n env) zs) ex,s1:(A,B)bvl_state) =
         (Rval (MAPi (\i v. if has_var i l1 then v else bvl_Number (&0)) env),s1)`)
   (fun th -> REWRITE_TAC[REWRITE_RULE[ETA_AX] th]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `MAPi (\i v. if has_var i l1 then v else bvl_Number (&0)) (env:bvl_v list) =
                  list_of_seq (\j. if has_var j l1 then EL j env else bvl_Number (&0))
                    (LENGTH env)` SUBST1_TAC THENL
     [REWRITE_TAC[LIST_EQ; LENGTH_MAPi; LENGTH_LIST_OF_SEQ] THEN
      SIMP_TAC[EL_MAPi; EL_LIST_OF_SEQ];
      ALL_TAC] THEN
    MATCH_MP_TAC BVLPROPSAUX_evaluate_list_of_seq THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `has_var j l1` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`zs:num list`; `0`; `j:num`] BVLPROPSAUX_ALOOKUP_MAPi_MEM) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[case_def "option"; bvl_evaluate_def; LENGTH_APPEND; LENGTH_MAP] THEN
      ASM_SIMP_TAC[ARITH_RULE `k < l ==> k < l + m`; EL_APPEND; LENGTH_MAP; EL_MAP];
      MP_TAC(ISPECL [`zs:num list`; `j:num`] BVLPROPSAUX_ALOOKUP_MAPi_NOT_MEM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[case_def "option"; bvl_evaluate_def; BVLPROPSAUX_do_app_IntOp] THEN
      CASE_REWRITE_TAC[REVERSE; bvl_do_int_app_def]];
    ALL_TAC] THEN
  REWRITE_TAC[pair_CASE; case_def "result"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[env_rel_MAPi]);;

let env_rel_refl = prove
 (`!l env. bvl_handleProof_env_rel l env env`,
  REWRITE_TAC[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN]);;

(* HOL4 [local] *)
let opt_lemma = prove
 (`!x y:(1)option. x = y <=> (x = SOME one <=> y = SOME one)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:(1)option` (cases "option")) THEN
  MP_TAC(ISPEC `y:(1)option` (cases "option")) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[one]);;

(* a local helper: the liveness of OptionalLetLet *)
let BVLPROPSAUX_env_rel_flatten = prove
 (`!lx env env1.
     bvl_handleProof_env_rel (vars_from_list (MAP FST (toAList (db_to_set lx)))) env env1 <=>
     bvl_handleProof_env_rel lx env env1`,
  REWRITE_TAC[GSYM vars_to_list_def; GSYM vars_flatten_def; bvl_handleProof_env_rel_def;
              has_var_vars_flatten]);;

(* HOL4 [local] *)
let OptionalLetLet_IMP = prove
 (`!ys l s' nr' y env lx s1 limit nr (s:(A,B)bvl_state) res env1 b extra.
     (ys,l,s',nr') = OptionalLetLet y (LENGTH env) lx s1 limit nr /\
     (!env2 extra. bvl_handleProof_env_rel l env env2 ==>
                   bvl_evaluate ([y],APPEND env2 extra,s) = res) /\
     bvl_handleProof_env_rel l env env1 /\ b ==>
     bvl_evaluate (ys,APPEND env1 extra,s) = res /\ b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OptionalLetLet_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_env_rel_flatten]) THEN
  REWRITE_TAC[bvl_evaluate_def; APPEND; pair_CASE; case_def "result"] THEN
  MATCH_MP_TAC evaluate_LetLet THEN ASM_REWRITE_TAC[]);;

let OptionalLetLet_limit = prove
 (`!ys l s' nr' e env lx s1 limit nr env1.
     (ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr /\
     bvl_handleProof_env_rel l env env1 ==> bvl_handleProof_env_rel lx env env1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OptionalLetLet_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_env_rel_flatten]) THEN
  ASM_REWRITE_TAC[]);;

let OptionalLetLet_nr = prove
 (`!ys l s' nr' e (env:bvl_v list) lx s1 limit nr.
     (ys,l,s',nr') = OptionalLetLet e (LENGTH env) lx s1 limit nr ==> nr' = nr`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OptionalLetLet_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN MESON_TAC[]);;

(* local tactics for compile_correct *)
let BVLPROPSAUX_CC_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     BVLPROPSAUX_has_const "bvl_handle_compile" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[bvl_handle_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[pair_case_eq; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[env_rel_mk_Union]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;
let BVLPROPSAUX_OLL_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && BVLPROPSAUX_has_const "OptionalLetLet" (lhs c) then
      let th' = SYM th in
      let imp = REWRITE_RULE[IMP_IMP]
                  (MATCH_MP (REWRITE_RULE[IMP_CONJ] OptionalLetLet_IMP) th') in
      let lim = MATCH_MP (REWRITE_RULE[IMP_CONJ] OptionalLetLet_limit) th' in
      let nrth = MATCH_MP OptionalLetLet_nr th' in
      ASSUME_TAC lim THEN ASSUME_TAC nrth THEN MATCH_MP_TAC imp
    else NO_TAC) THEN
  REPEAT CONJ_TAC;;
let BVLPROPSAUX_CC_SING_TAC : tactic =
  let step (asl,w as g) =
    let ok th =
      let c = concl th in
      is_eq c && BVLPROPSAUX_has_const "bvl_handle_compile" (lhs c) &&
      (try length (dest_list (rand (lhs c))) = 1 with Failure _ -> false) &&
      is_var (fst (dest_pair (rand c))) in
    let th = snd (find (fun (_,th) -> ok th) asl) in
    let avoid = freesl (w :: map (concl o snd) asl) in
    let d = variant avoid (mk_var("d",`:bvl_exp`)) in
    X_CHOOSE_THEN d SUBST_ALL_TAC (MATCH_MP (GEN_ALL bvl_handle_compile_sing) th) g in
  REPEAT step;;
let BVLPROPSAUX_CC_EVSPLIT_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE BVLPROPSAUX_eval_case_eqs o
                ONCE_REWRITE_RULE[bvl_evaluate_def] o
                check (fun th -> is_eq (concl th) &&
     BVLPROPSAUX_is_ev (lhs (concl th)) &&
     not (BVLPROPSAUX_has_const "bvl_handle_compile" (concl th)) &&
     not (free_in `env2:bvl_v list` (concl th)) &&
     not (free_in `env1:bvl_v list` (concl th)))) THEN
  DISCH_THEN BVLPROPSAUX_FRESH_STRIP_TAC THEN TRY RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[env_rel_mk_Union]) THEN BVLPROPSAUX_CLEAN_TAC THEN
  REPEAT (BVLPROPSAUX_RES4_TAC (env_rel_mk_Union :: BVLPROPSAUX_eval_simps) THEN
          BVLPROPSAUX_CLEAN_TAC);;
let BVLPROPSAUX_DROP_IMPS_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
    is_imp (snd (strip_forall (concl th))))));;
let BVLPROPSAUX_env_rel_Shift = prove
 (`!a l2 env env2.
     bvl_handleProof_env_rel (db_vars_Shift (LENGTH a) l2) env env2 ==>
     bvl_handleProof_env_rel l2 (APPEND a env) (APPEND a env2)`,
  REWRITE_TAC[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN; LENGTH_APPEND; has_var_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EL_APPEND] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i < a) ==> (i - a) + a = i`] THEN ASM_ARITH_TAC);;
let BVLPROPSAUX_CC_MAIN_TAC : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun lim -> FIRST_ASSUM(fun er ->
    ASSUME_TAC (REWRITE_RULE[env_rel_mk_Union] (MATCH_MP lim er)))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  BVLPROPSAUX_CC_SING_TAC THEN BVLPROPSAUX_CC_EVSPLIT_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[HD] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; case_def "option"];;
let BVLPROPSAUX_CC_NR_TAC : tactic =
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN BVLPROPSAUX_CC_SING_TAC THEN
  BVLPROPSAUX_CC_EVSPLIT_TAC THEN BVLPROPSAUX_DROP_IMPS_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN ASM_MESON_TAC[];;
let BVLPROPSAUX_CC_OLL_CASE_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  BVLPROPSAUX_CC_SPLIT_TAC THEN BVLPROPSAUX_OLL_TAC THENL
   [BVLPROPSAUX_CC_MAIN_TAC; FIRST_ASSUM ACCEPT_TAC; BVLPROPSAUX_CC_NR_TAC];;

(* a local helper: HOL4's first compile_correct (before its specialisation) *)
let BVLPROPSAUX_compile_correct_gen = prove
 (`!xs env (s1:(A,B)bvl_state) ys env1 res s2 extra l s nr limit.
     bvl_handle_compile limit (LENGTH env) xs = (ys,l,s,nr) /\
     bvl_handleProof_env_rel l env env1 /\
     bvl_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (ys,APPEND env1 extra,s1) = (res,s2) /\
     (nr ==> !e. ~(res = Rerr (Rraise e)))`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THENL
   [(REPEAT GEN_TAC THEN REWRITE_TAC[bvl_handle_compile_def; bvl_evaluate_def; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvl_evaluate_def; distinctness "result"]);
    (* next case *)
    ((REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  BVLPROPSAUX_CC_SPLIT_TAC) THEN
    (FIRST_ASSUM(X_CHOOSE_THEN `d:bvl_exp` SUBST_ALL_TAC o
              MATCH_MP (GEN_ALL bvl_handle_compile_sing) o
              check (fun th -> is_eq (concl th) &&
                               BVLPROPSAUX_has_const "bvl_handle_compile" (lhs (concl th)) &&
                               length (dest_list (rand (lhs (concl th)))) = 1)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     BVLPROPSAUX_is_ev (lhs (concl th)) &&
     not (BVLPROPSAUX_has_const "bvl_handle_compile" (concl th)))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC BVLPROPSAUX_eval_case_eqs THEN
  DISCH_THEN BVLPROPSAUX_FRESH_STRIP_TAC THEN TRY RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN
  REPEAT (BVLPROPSAUX_RES4_TAC BVLPROPSAUX_eval_simps THEN BVLPROPSAUX_CLEAN_TAC) THEN
  REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; distinctness "result";
                  injectivity "result"] THEN
  ASM_MESON_TAC[]));
    (* next case *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `bvl_evaluate ([bvl_Var n],env,s1:(A,B)bvl_state) = (res,s2)` THEN
  REWRITE_TAC[bvl_evaluate_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     BVLPROPSAUX_has_const "bvl_handle_compile" (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[bvl_handle_compile_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN; has_var_def]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `n < LENGTH (env1:bvl_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[bvl_evaluate_def; LENGTH_APPEND; EL_APPEND; distinctness "result";
               ARITH_RULE `n < l ==> n < l + m`]);
    (* next case *)
    ((REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  BVLPROPSAUX_CC_SPLIT_TAC) THEN (BVLPROPSAUX_OLL_TAC) THENL
     [(REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun lim -> FIRST_ASSUM(fun er ->
    ASSUME_TAC (REWRITE_RULE[env_rel_mk_Union] (MATCH_MP lim er)))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  BVLPROPSAUX_CC_SING_TAC THEN BVLPROPSAUX_CC_EVSPLIT_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[HD] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"]);
      (FIRST_ASSUM ACCEPT_TAC);
      (ASM_REWRITE_TAC[] THEN STRIP_TAC THEN BVLPROPSAUX_CC_SING_TAC THEN
  BVLPROPSAUX_CC_EVSPLIT_TAC THEN BVLPROPSAUX_DROP_IMPS_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN ASM_MESON_TAC[])]);
    (* next case *)
    ((REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `NULL (xs:bvl_exp list)` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       BVLPROPSAUX_has_const "bvl_handle_compile" (lhs (concl th)))) THEN
    ONCE_REWRITE_TAC[bvl_handle_compile_def] THEN REWRITE_TAC[NULL] THEN DISCH_TAC THEN
    UNDISCH_TAC `bvl_evaluate ([bvl_Let [] x2],env,s1:(A,B)bvl_state) = (res,s2)` THEN
    REWRITE_TAC[bvl_evaluate_def; pair_CASE; case_def "result"; APPEND] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[]:bvl_v list`; `s1:(A,B)bvl_state`] o
                  check (fun th -> free_in `x2:bvl_exp` (concl th) && is_forall (concl th))) THEN
    REWRITE_TAC[bvl_evaluate_def; APPEND] THEN ASM_MESON_TAC[];
    ALL_TAC]) THEN (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     BVLPROPSAUX_has_const "bvl_handle_compile" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[bvl_handle_compile_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[pair_case_eq; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  BVLPROPSAUX_OLL_TAC) THENL
     [((REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun lim -> FIRST_ASSUM(fun er ->
    ASSUME_TAC (REWRITE_RULE[env_rel_mk_Union] (MATCH_MP lim er)))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)))) THEN (BVLPROPSAUX_CC_SING_TAC) THEN (UNDISCH_TAC `bvl_evaluate ([bvl_Let xs x2],env,s1:(A,B)bvl_state) = (res,s2)` THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def]) THEN (MP_TAC(ISPEC `bvl_evaluate (xs,env,s1:(A,B)bvl_state)` PAIR_SURJECTIVE)) THEN (DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `t1:(A,B)bvl_state` ASSUME_TAC))) THEN (ASM_REWRITE_TAC[pair_CASE]) THEN (CASES_ON `r1:(bvl_v list,bvl_v)result`) THENL
       [(REWRITE_TAC[case_def "result"] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH o
    check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)) &&
                     fst (dest_pair (rand (lhs (concl th)))) = `xs:bvl_exp list`)) THEN
  SUBGOAL_THEN `LENGTH (env:bvl_v list) + LENGTH (xs:bvl_exp list) = LENGTH (APPEND a env)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> BVLPROPSAUX_has_const "db_vars_Shift" (concl th) &&
                                          not (is_forall (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP BVLPROPSAUX_env_rel_Shift) THEN
  REPEAT (BVLPROPSAUX_RES4_TAC (env_rel_mk_Union :: BVLPROPSAUX_eval_simps) THEN
          BVLPROPSAUX_CLEAN_TAC) THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; HD] THEN
  REWRITE_TAC[APPEND_ASSOC] THEN ASM_REWRITE_TAC[]);
        (REWRITE_TAC[case_def "result"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  BVLPROPSAUX_CLEAN_TAC THEN
  REPEAT (BVLPROPSAUX_RES4_TAC (env_rel_mk_Union :: BVLPROPSAUX_eval_simps) THEN
          BVLPROPSAUX_CLEAN_TAC) THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"])]);
      (FIRST_ASSUM ACCEPT_TAC);
      (ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun lim -> FIRST_ASSUM(fun er ->
    ASSUME_TAC (REWRITE_RULE[env_rel_mk_Union] (MATCH_MP lim er)))) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  BVLPROPSAUX_CC_SING_TAC THEN
  UNDISCH_TAC `bvl_evaluate ([bvl_Let xs x2],env,s1:(A,B)bvl_state) = (res,s2)` THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate (xs,env,s1:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `t1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THENL
   [REWRITE_TAC[case_def "result"] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH o
      check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)) &&
                       fst (dest_pair (rand (lhs (concl th)))) = `xs:bvl_exp list`)) THEN
    SUBGOAL_THEN `LENGTH (env:bvl_v list) + LENGTH (xs:bvl_exp list) = LENGTH (APPEND a env)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> BVLPROPSAUX_has_const "db_vars_Shift" (concl th) &&
                                            not (is_forall (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP BVLPROPSAUX_env_rel_Shift);
    REWRITE_TAC[case_def "result"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    BVLPROPSAUX_CLEAN_TAC] THEN
  REPEAT (BVLPROPSAUX_RES4_TAC (env_rel_mk_Union :: BVLPROPSAUX_eval_simps) THEN
          BVLPROPSAUX_CLEAN_TAC) THEN
  BVLPROPSAUX_DROP_IMPS_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN ASM_MESON_TAC[])]);
    (* next case *)
    (BVLPROPSAUX_CC_OLL_CASE_TAC);
    (* next case *)
    ((REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     BVLPROPSAUX_has_const "bvl_handle_compile" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[bvl_handle_compile_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[pair_case_eq; PAIR_EQ; COND_CASE_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC) THENL
     [(BVLPROPSAUX_CC_EVSPLIT_TAC THEN BVLPROPSAUX_DROP_IMPS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "result"; distinctness "result";
                              injectivity "error_result"; distinctness "error_result"]) THEN
  ASM_REWRITE_TAC[injectivity "result"; distinctness "result";
                  injectivity "error_result"; distinctness "error_result"] THEN
  ASM_MESON_TAC[]);
      (RULE_ASSUM_TAC(REWRITE_RULE[env_rel_mk_Union]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  BVLPROPSAUX_CC_SING_TAC THEN REWRITE_TAC[HD]) THEN (MP_TAC(ISPEC `bvl_evaluate ([x1],env,s1:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `t1:(A,B)bvl_state` ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `bvl_evaluate ([bvl_Handle x1 x2],env,s1:(A,B)bvl_state) = (res,s2)` THEN
    PURE_ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE; case_def "result";
      case_def "error_result"; PAIR_EQ] THEN BVLPROPSAUX_DROP_IMPS_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvl_evaluate ([LetLet (LENGTH (env:bvl_v list)) (db_to_set x') d'],
                              APPEND env1 extra,s1:(A,B)bvl_state) = (r1,t1)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_LetLet THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `env2:bvl_v list` THEN X_GEN_TAC `ex:bvl_v list` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[d']:bvl_exp list`; `env2:bvl_v list`;
      `r1:(bvl_v list,bvl_v)result`; `t1:(A,B)bvl_state`; `ex:bvl_v list`;
      `x':db_var_set`; `x'':num`; `y'':bool`; `limit:num`] o
      check (fun th -> is_forall (concl th) && not (free_in `x2:bvl_exp` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC]) THEN (UNDISCH_TAC `bvl_evaluate ([bvl_Handle x1 x2],env,s1:(A,B)bvl_state) = (res,s2)` THEN
  PURE_ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[distinctness "result"];
    ALL_TAC] THEN
  CASES_ON `a:(bvl_v)error_result` THEN REWRITE_TAC[case_def "error_result"] THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`[a':bvl_v]`; `x'''':db_var_set`; `env:bvl_v list`; `env1:bvl_v list`]
                  BVLPROPSAUX_env_rel_Shift) THEN
    ASM_REWRITE_TAC[LENGTH; GSYM ONE; APPEND] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a':bvl_v`; `t1:(A,B)bvl_state`] o
      check (fun th -> is_forall (concl th) && free_in `x2:bvl_exp` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`[d]:bvl_exp list`; `CONS (a':bvl_v) env1`;
      `res:(bvl_v list,bvl_v)result`; `s2:(A,B)bvl_state`; `extra:bvl_v list`;
      `x'''':db_var_set`; `s:num`; `nr:bool`; `limit:num`]) THEN
    ASM_REWRITE_TAC[LENGTH; ADD1; APPEND];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result"]])]);
    (* next case *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  BVLPROPSAUX_CC_SPLIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN
    BVLPROPSAUX_CC_EVSPLIT_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
    ASM_REWRITE_TAC[pair_CASE; case_def "result"];
    DISCH_TAC THEN BVLPROPSAUX_OLL_TAC THENL
     [BVLPROPSAUX_CC_MAIN_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN BVLPROPSAUX_CC_SING_TAC THEN
      BVLPROPSAUX_CC_EVSPLIT_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_do_app_not_Rraise]) THEN
      BVLPROPSAUX_DROP_IMPS_TAC THEN
      REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
      ASM_MESON_TAC[BVLPROPSAUX_do_app_not_Rraise]]]);
    (* next case *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  BVLPROPSAUX_CC_SPLIT_TAC THEN BVLPROPSAUX_CC_SING_TAC THEN BVLPROPSAUX_CC_EVSPLIT_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[HD] THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"; distinctness "error_result"] THEN
  BVLPROPSAUX_DROP_IMPS_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN ASM_MESON_TAC[]);
    (* next case *)
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n < LENGTH (env:bvl_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result)` THEN
    UNDISCH_TAC `bvl_evaluate ([bvl_Force force_loc n],env,s1:(A,B)bvl_state) = (res,s2)` THEN
    REWRITE_TAC[bvl_evaluate_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     BVLPROPSAUX_has_const "bvl_handle_compile" (lhs (concl th)))) THEN
  ASM_REWRITE_TAC[bvl_handle_compile_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_handleProof_env_rel_def; LIST_RELi_EL_EQN; has_var_def]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `n < LENGTH (env1:bvl_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th))
                          then SUBST1_TAC (SYM th) else NO_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `n:num`; `env:bvl_v list`; `APPEND (env1:bvl_v list) extra`;
                 `s1:(A,B)bvl_state`] BVLPROPSAUX_evaluate_Var_Force_env) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LENGTH_APPEND; EL_APPEND; ARITH_RULE `n < l ==> n < l + m`];
    ASM_SIMP_TAC[]]);
    (* next case *)
    (BVLPROPSAUX_CC_OLL_CASE_TAC)]);;

(* a local helper: HOL4's compile_correct specialised to env1 = env and   *)
(* extra = [] (bound to compile_correct in HOL4 before the final version) *)
let BVLPROPSAUX_compile_correct_spec = prove
 (`!xs env (s1:(A,B)bvl_state) ys res s2 l s nr limit.
     bvl_handle_compile limit (LENGTH env) xs = (ys,l,s,nr) /\
     bvl_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (ys,env,s1) = (res,s2) /\
     (nr ==> !e. ~(res = Rerr (Rraise e)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:bvl_exp list`; `env:bvl_v list`; `s1:(A,B)bvl_state`;
                 `ys:bvl_exp list`; `env:bvl_v list`; `res:(bvl_v list,bvl_v)result`;
                 `s2:(A,B)bvl_state`; `[]:bvl_v list`; `l:db_var_set`; `s:num`; `nr:bool`;
                 `limit:num`] BVLPROPSAUX_compile_correct_gen) THEN
  ASM_REWRITE_TAC[APPEND_NIL; env_rel_refl]);;

(* HOL4 binds compile_correct three times (allow_rebind); this is the last *)
(* binding, the first two are BVLPROPSAUX_compile_correct_gen and _spec   *)
let bvl_handleProof_compile_correct = prove
 (`!x env (s1:(A,B)bvl_state) res s2 k l.
     bvl_evaluate ([x],env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     k = LENGTH env ==>
     bvl_evaluate ([bvl_handle_compile_exp l k x],env,s1) = (res,s2)`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[bvl_handle_compile_exp_def] THEN
  MP_TAC(ISPEC `bvl_handle_compile l (LENGTH (env:bvl_v list))
                  [handle_simp (bvl_const_compile_exp x)]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:bvl_exp list` (X_CHOOSE_THEN `p:db_var_set#num#bool`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `p:db_var_set#num#bool` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:db_var_set` (X_CHOOSE_THEN `q:num#bool` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `q:num#bool` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` (X_CHOOSE_THEN `nr:bool` SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:bvl_exp` SUBST_ALL_TAC o
              MATCH_MP (GEN_ALL bvl_handle_compile_sing)) THEN
  REWRITE_TAC[HD] THEN
  MP_TAC(ISPECL [`[handle_simp (bvl_const_compile_exp x)]`; `env:bvl_v list`;
                 `s1:(A,B)bvl_state`; `[d]:bvl_exp list`; `res:(bvl_v list,bvl_v)result`;
                 `s2:(A,B)bvl_state`; `l1:db_var_set`; `s:num`; `nr:bool`; `l:num`]
                BVLPROPSAUX_compile_correct_spec) THEN
  ASM_REWRITE_TAC[CONJUNCT1 evaluate_handle_simp] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC bvl_constProof_evaluate_compile_exp THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

let dest_Seq_thm = prove
 (`!x y0 y1. bvl_handle_dest_Seq x = SOME (y0,y1) <=> x = bvl_Let [y0; y1] (bvl_Var 1)`,
  REWRITE_TAC[BVLPAUX_dest_Seq_eq; PAIR_EQ] THEN MESON_TAC[]);;

let compile_seqs_correct = prove
 (CASE_TERM `!l x acc (s1:(A,B)bvl_state) s2 s3 res res3.
     bvl_evaluate ([x],[],s1) = (res,s2) /\
     (!y r. acc = SOME y /\ res = Rval r ==>
            ~(res3 = Rerr (Rabort Rtype_error)) /\ bvl_evaluate ([y],[],s2) = (res3,s3)) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([compile_seqs l x acc],[],s1) =
     if acc = NONE then (res,s2) else
       match res with Rval _ -> (res3,s3) | _ -> (res,s2)`,
  MATCH_MP_TAC compile_seqs_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[compile_seqs_def] THEN
  CASES_ON `bvl_handle_dest_Seq e` THEN ASM_REWRITE_TAC[case_def "option"] THENL
   [(REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  CASES_ON `acc:bvl_exp option` THEN REWRITE_TAC[case_def "option"; option_DISTINCT] THENL
   [MATCH_MP_TAC bvl_handleProof_compile_correct THEN ASM_REWRITE_TAC[LENGTH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:bvl_exp`; `[]:bvl_v list`; `s1:(A,B)bvl_state`;
                 `res:(bvl_v list,bvl_v)result`; `s2:(A,B)bvl_state`; `0`; `cut_size:num`]
                bvl_handleProof_compile_correct) THEN
  ASM_REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `res:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[case_def "result"] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:bvl_exp`; `a':bvl_v list`] o
                check (is_forall o concl)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING o
    check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)) &&
                     BVLPROPSAUX_has_const "bvl_handle_compile_exp" (lhs (concl th)))) THEN
  REWRITE_TAC[bvl_evaluate_def; APPEND; pair_CASE; case_def "result"] THEN
  MP_TAC(ISPECL [`[a:bvl_exp]`; `[]:bvl_v list`; `s2:(A,B)bvl_state`; `[w:bvl_v]`]
                bvl_evaluate_expand_env) THEN
  ASM_REWRITE_TAC[APPEND; FST]);
    ((MP_TAC(ISPEC `a:bvl_exp#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:bvl_exp` (X_CHOOSE_THEN `e2:bvl_exp` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN
  RULE_ASSUM_TAC(fun th -> try MP (SPECL [`e1:bvl_exp`; `e2:bvl_exp`] th)
                                   (REFL `SOME (e1:bvl_exp,e2:bvl_exp)`)
                           with Failure _ -> th) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[dest_Seq_thm] o
                check (fun th -> concl th = `bvl_handle_dest_Seq e = SOME (e1,e2)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)))) THEN
  REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate ([e1],[],s1:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s0:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r0:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"]) THENL
     [((MP_TAC(ISPEC `bvl_evaluate ([e2],[],s0:(A,B)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `t1:(A,B)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r1:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"]) THENL
       [(FIRST_ASSUM(X_CHOOSE_THEN `w1:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING o
    check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)) &&
                     fst (dest_pair (rand (lhs (concl th)))) = `[e2:bvl_exp]`)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w0:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING o
    check (fun th -> is_eq (concl th) && BVLPROPSAUX_is_ev (lhs (concl th)) &&
                     fst (dest_pair (rand (lhs (concl th)))) = `[e1:bvl_exp]`)) THEN
  REWRITE_TAC[pair_CASE; case_def "result"; HD; APPEND; LENGTH; EL; TL; ONE;
              ARITH_RULE `SUC 0 < SUC (SUC 0)`] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[case_def "result"] THEN
  MP_TAC(ISPEC `acc:bvl_exp option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `y:bvl_exp` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[option_DISTINCT] THENL
   [SUBGOAL_THEN `bvl_evaluate ([compile_seqs cut_size e2 NONE],[],s0:(A,B)bvl_state) =
                  (Rval [w1],s2)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`s0:(A,B)bvl_state`; `s2:(A,B)bvl_state`;
        `s3:(A,B)bvl_state`; `Rval [w1]:(bvl_v list,bvl_v)result`;
        `res3:(bvl_v list,bvl_v)result`] o
        check (fun th -> is_forall (concl th) && free_in `e2:bvl_exp` (concl th) &&
                         not (free_in `e1:bvl_exp` (concl th)))) THEN
      ASM_REWRITE_TAC[distinctness "result"; option_DISTINCT];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,B)bvl_state`; `s0:(A,B)bvl_state`;
      `s2:(A,B)bvl_state`; `Rval [w0]:(bvl_v list,bvl_v)result`;
      `Rval [w1]:(bvl_v list,bvl_v)result`] o
      check (fun th -> is_forall (concl th) && free_in `e1:bvl_exp` (concl th))) THEN
    ASM_REWRITE_TAC[distinctness "result"; option_DISTINCT; option_INJ; case_def "result"] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"];
    SUBGOAL_THEN `bvl_evaluate ([compile_seqs cut_size e2 (SOME y)],[],s0:(A,B)bvl_state) =
                  (res3,s3) /\ ~(res3 = Rerr (Rabort Rtype_error))` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`y:bvl_exp`; `[w1]:bvl_v list`] o
        check (fun th -> is_forall (concl th) &&
                         free_in `res3:(bvl_v list,bvl_v)result` (concl th) &&
                         not (free_in `e2:bvl_exp` (concl th)))) THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s0:(A,B)bvl_state`; `s2:(A,B)bvl_state`;
        `s3:(A,B)bvl_state`; `Rval [w1]:(bvl_v list,bvl_v)result`;
        `res3:(bvl_v list,bvl_v)result`] o
        check (fun th -> is_forall (concl th) && free_in `e2:bvl_exp` (concl th) &&
                         not (free_in `e1:bvl_exp` (concl th)))) THEN
      ASM_REWRITE_TAC[distinctness "result"; option_DISTINCT; option_INJ; case_def "result";
                      injectivity "result"] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,B)bvl_state`; `s0:(A,B)bvl_state`;
      `s3:(A,B)bvl_state`; `Rval [w0]:(bvl_v list,bvl_v)result`;
      `res3:(bvl_v list,bvl_v)result`] o
      check (fun th -> is_forall (concl th) && free_in `e1:bvl_exp` (concl th))) THEN
    ASM_REWRITE_TAC[distinctness "result"; option_DISTINCT; option_INJ; case_def "result"] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[distinctness "result"]]);
        (REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `bvl_evaluate ([compile_seqs cut_size e2 acc],[],s0:(A,B)bvl_state) =
                (Rerr a'',s2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`s0:(A,B)bvl_state`; `s2:(A,B)bvl_state`;
      `s3:(A,B)bvl_state`; `Rerr a'':(bvl_v list,bvl_v)result`;
      `res3:(bvl_v list,bvl_v)result`] o
      check (fun th -> is_forall (concl th) && free_in `e2:bvl_exp` (concl th) &&
                       not (free_in `e1:bvl_exp` (concl th)))) THEN
    ASM_REWRITE_TAC[distinctness "result"; case_def "result"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,B)bvl_state`; `s0:(A,B)bvl_state`;
      `s2:(A,B)bvl_state`; `Rval a':(bvl_v list,bvl_v)result`;
      `Rerr a'':(bvl_v list,bvl_v)result`] o
      check (fun th -> is_forall (concl th) && free_in `e1:bvl_exp` (concl th))) THEN
  ASM_REWRITE_TAC[distinctness "result"; option_DISTINCT; option_INJ; case_def "result"] THEN
  ANTS_TAC THENL [REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[case_def "result"])]);
      (REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,B)bvl_state`; `s2:(A,B)bvl_state`;
      `s2:(A,B)bvl_state`; `Rerr a':(bvl_v list,bvl_v)result`;
      `Rerr a':(bvl_v list,bvl_v)result`] o
      check (fun th -> is_forall (concl th) && free_in `e1:bvl_exp` (concl th))) THEN
  ASM_REWRITE_TAC[distinctness "result"; option_DISTINCT; option_INJ; case_def "result"] THEN
  DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[case_def "result"])])]);;

(* HOL4 leaves x, env, s1, res, s2, k, split_seq and l free *)
let compile_any_correct = prove
 (`!x env (s1:(A,B)bvl_state) res s2 k split_seq l.
     bvl_evaluate ([x],env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     k = LENGTH env ==>
     bvl_evaluate ([compile_any split_seq l k x],env,s1) = (res,s2)`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[compile_any_def] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_EQ_NIL]) THEN RVEQ_TAC THEN
    MP_TAC(ISPECL [`l:num`; `x:bvl_exp`; `NONE:bvl_exp option`; `s1:(A,B)bvl_state`;
                   `s2:(A,B)bvl_state`; `s2:(A,B)bvl_state`; `res:(bvl_v list,bvl_v)result`;
                   `res:(bvl_v list,bvl_v)result`] compile_seqs_correct) THEN
    ASM_REWRITE_TAC[option_DISTINCT];
    MATCH_MP_TAC bvl_handleProof_compile_correct THEN ASM_REWRITE_TAC[]]);;

let compile_IMP_LENGTH = prove
 (`!l n xs ys l1 (s1:num#bool).
     bvl_handle_compile l n xs = (ys,l1,s1) ==> LENGTH ys = LENGTH xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:num`; `n:num`; `xs:bvl_exp list`] bvl_handle_compile_length) THEN
  ASM_REWRITE_TAC[FST]);;

let bVarBound_CONS = prove
 (`!m x xs. bVarBound m [x] /\ bVarBound m xs ==> bVarBound m (CONS x xs)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[bVarBound_def]);;

let bVarBound_MEM = prove
 (`!n xs. bVarBound n xs <=> !x. MEM x xs ==> bVarBound n [x]`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [bVarBound_EVERY] THEN
  REWRITE_TAC[ALL_MEM]);;

let bEvery_MEM = prove
 (`!p xs. bEvery p xs <=> !x. MEM x xs ==> bEvery p [x]`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [bEvery_EVERY] THEN
  REWRITE_TAC[ALL_MEM]);;

let bVarBound_LESS_EQ = prove
 (`!m xs n. bVarBound m xs /\ m <= n ==> bVarBound n xs`,
  MATCH_MP_TAC bVarBound_ind THEN REWRITE_TAC[bVarBound_def] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[LE_ADD_RCANCEL; LTE_TRANS]);;

(* HOL4 also quantifies a vacuous i (of an unconstrained type) and leaves n *)
(* free                                                                      *)
let ALOOKUP_MAPi = prove
 (`!(xs:A list) (i:B) (x:num) (n:A).
     ALOOKUP (MAPi (\i x. (x,i)) xs) n = SOME x ==> x < LENGTH xs`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_MAPi] THEN BETA_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 [simp] *)
let bVarBound_SmartLet = prove
 (`!m x xs. bVarBound m [SmartLet x xs] <=> bVarBound m [bvl_Let x xs]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartLet_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN
  ASM_REWRITE_TAC[bVarBound_def; LENGTH; ADD_CLAUSES]);;
let _ = cake_add_simps [bVarBound_SmartLet];;

let bVarBound_LetLet = prove
 (`!m y n (l1:num_set). bVarBound m [y] /\ n <= m ==> bVarBound m [LetLet n l1 y]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LetLet_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[bVarBound_def; bVarBound_SmartLet; LENGTH_MAP] THEN
  ABBREV_TAC `zs = FILTER (\n. IS_SOME (lookup n (l1:num_set))) (list_of_seq I n)` THEN
  SUBGOAL_THEN `!j. MEM j zs ==> j < n` ASSUME_TAC THENL
   [EXPAND_TAC "zs" THEN REWRITE_TAC[MEM_FILTER; MEM_GENLIST; I_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[bVarBound_MEM] THEN REWRITE_TAC[MEM_MAP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bVarBound_def] THEN
    ASM_MESON_TAC[LTE_TRANS];
    ONCE_REWRITE_TAC[bVarBound_MEM] THEN REWRITE_TAC[MEM_GENLIST] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TOP_CASE_TAC THEN
    REWRITE_TAC[bVarBound_def] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL ALOOKUP_MAPi)) THEN ARITH_TAC;
    MATCH_MP_TAC bVarBound_LESS_EQ THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let bVarBound_OptionalLetLet = prove
 (`!m e n l s limit nr.
     bVarBound m [e] /\ n <= m ==> bVarBound m (FST (OptionalLetLet e n l s limit nr))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OptionalLetLet_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ASM_REWRITE_TAC[FST; bVarBound_def; LENGTH; ADD_CLAUSES] THEN
  MATCH_MP_TAC bVarBound_LetLet THEN ASM_REWRITE_TAC[]);;

(* local helpers: bvl_handle_compile_ind with the induction hypotheses of *)
(* the pair lets resolved (the Let hypothesis for the body is taken at    *)
(* the shift LENGTH xs only), and tactics for the proofs by it: unfold the *)
(* compile clause of the goal, split its pairs and conditionals, make the  *)
(* singleton results explicit, and rewrite the induction hypotheses with  *)
(* the pair equations                                                       *)
let BVLPROPSAUX_PAIR4_EQ = prove
 (`!(p:A#B#C#D) a b c d.
     p = (a,b,c,d) <=>
     a = FST p /\ b = FST (SND p) /\ c = FST (SND (SND p)) /\ d = SND (SND (SND p))`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN MESON_TAC[]);;

let BVLPROPSAUX_compile_ind = prove
 (`!P. (!l n. P l n []) /\
       (!l n x y xs. P l n [x] /\ P l n (CONS y xs) ==> P l n (CONS x (CONS y xs))) /\
       (!l n v. P l n [bvl_Var v]) /\
       (!l n x1 x2 x3.
          P l n [x1] /\ P l n [x2] /\ P l n [x3] ==> P l n [bvl_If x1 x2 x3]) /\
       (!l n xs x2.
          (NULL xs ==> P l n [x2]) /\ (~NULL xs ==> P l n xs) /\
          (~NULL xs ==> P l (n + LENGTH xs) [x2]) ==> P l n [bvl_Let xs x2]) /\
       (!l n x1 x2.
          P l n [x1] /\
          (~SND (SND (SND (bvl_handle_compile l n [x1]))) ==> P l (n + 1) [x2])
          ==> P l n [bvl_Handle x1 x2]) /\
       (!l n x1. P l n [x1] ==> P l n [bvl_Raise x1]) /\
       (!l n op xs. P l n xs ==> P l n [bvl_Op op xs]) /\
       (!l n x. P l n [x] ==> P l n [bvl_Tick x]) /\
       (!l n m v. P l n [bvl_Force m v]) /\
       (!l n t dest xs. P l n xs ==> P l n [bvl_Call t dest xs])
       ==> !l n xs. P l n xs`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC bvl_handle_compile_ind THEN
  REWRITE_TAC[BVLPROPSAUX_PAIR4_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV (CHANGED_CONV FORALL_UNWIND_CONV)) THEN
  ASM_MESON_TAC[]);;

let BVLPROPSAUX_HC_IH_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun th -> let c = concl th in is_eq c &&
               BVLPROPSAUX_has_const "bvl_handle_compile" (lhs c)) (map snd asl) in
  RULE_ASSUM_TAC (fun a -> if exists (fun e -> concl e = concl a) eqs then a
                           else REWRITE_RULE (FST :: SND :: eqs) a) g;;

let BVLPROPSAUX_HC_MP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  RULE_ASSUM_TAC (fun a -> let c = concl a in
     if is_imp c then
       (try MP a (find (fun h -> aconv (concl h) (lhand c)) asms) with Failure _ -> a)
     else a) g;;

let BVLPROPSAUX_HC_LEN_TAC : tactic = fun (asl,w as g) ->
  let ok th = let c = concl th in is_eq c &&
     BVLPROPSAUX_has_const "bvl_handle_compile" (lhs c) &&
     is_var (fst (dest_pair (rand c))) in
  let ths = filter ok (map snd asl) in
  MAP_EVERY (fun th -> ASSUME_TAC (MATCH_MP compile_IMP_LENGTH th)) ths g;;

let BVLPROPSAUX_HC_PRE_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[bvl_handle_compile_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT (BVLPAUX_PAIRARG_TAC ORELSE COND_CASES_TAC) THEN
  BVLPROPSAUX_CC_SING_TAC THEN REWRITE_TAC[HD; FST; SND; APPEND] THEN
  BVLPROPSAUX_HC_IH_TAC THEN BVLPROPSAUX_HC_MP_TAC THEN BVLPROPSAUX_HC_LEN_TAC;;

let bVarBound_compile = prove
 (`!l n xs m. n <= m ==> bVarBound m (FST (bvl_handle_compile l n xs))`,
  MATCH_MP_TAC BVLPROPSAUX_compile_ind THEN REPEAT CONJ_TAC THEN
  BVLPROPSAUX_HC_PRE_TAC THEN REWRITE_TAC[bVarBound_def] THEN
  TRY (MATCH_MP_TAC bVarBound_OptionalLetLet ORELSE MATCH_MP_TAC bVarBound_CONS) THEN
  REWRITE_TAC[bVarBound_def] THEN REPEAT CONJ_TAC THEN
  TRY (MATCH_MP_TAC bVarBound_LetLet) THEN
  ASM_SIMP_TAC[LE_ADD_RCANCEL] THEN ASM_ARITH_TAC);;

let compile_IMP_bVarBound = prove
 (`!l n xs ys l2 (s2:num#bool).
     bvl_handle_compile l n xs = (ys,l2,s2) ==> bVarBound n ys`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:num`; `n:num`; `xs:bvl_exp list`; `n:num`] bVarBound_compile) THEN
  ASM_REWRITE_TAC[LE_REFL; FST]);;

(* a local helper: the first component of a compiled singleton *)
let BVLPROPSAUX_compile_FST_sing = prove
 (`!l n x. ?y. FST (bvl_handle_compile l n [x]) = [y]`,
  REPEAT GEN_TAC THEN
  MP_TAC(INST [`FST (bvl_handle_compile l n [x])`,`dx:bvl_exp list`;
               `FST (SND (bvl_handle_compile l n [x]))`,`lx:db_var_set`;
               `SND (SND (bvl_handle_compile l n [x]))`,`s:num#bool`]
              bvl_handle_compile_sing) THEN
  REWRITE_TAC[PAIR]);;

let compile_exp_bVarBound = prove
 (`!n l x. bVarBound n [bvl_handle_compile_exp l n x]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_handle_compile_exp_def] THEN
  MP_TAC(SPECL [`l:num`; `n:num`; `[handle_simp (bvl_const_compile_exp x)]`; `n:num`]
           bVarBound_compile) THEN
  X_CHOOSE_THEN `y:bvl_exp` SUBST1_TAC
    (SPECL [`l:num`; `n:num`; `handle_simp (bvl_const_compile_exp x)`]
           BVLPROPSAUX_compile_FST_sing) THEN
  REWRITE_TAC[LE_REFL; HD]);;

let compile_seqs_bVarBound = prove
 (`!l x acc. (!y. acc = SOME y ==> bVarBound 0 [y]) ==>
             bVarBound 0 [compile_seqs l x acc]`,
  MATCH_MP_TAC compile_seqs_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[compile_seqs_def] THEN
  CASES_ON `bvl_handle_dest_Seq e` THEN ASM_REWRITE_TAC[case_def "option"] THENL
   [REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
    CASES_ON `acc:bvl_exp option` THEN
    REWRITE_TAC[case_def "option"; compile_exp_bVarBound] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; FORALL_UNWIND_THM1]) THEN
    REWRITE_TAC[bVarBound_def; LENGTH; ADD_CLAUSES; compile_exp_bVarBound] THEN
    MATCH_MP_TAC bVarBound_LESS_EQ THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[LE_0];
    MP_TAC(ISPEC `a:bvl_exp#bvl_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:bvl_exp` (X_CHOOSE_THEN `e2:bvl_exp` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[pair_CASE] THEN
    RULE_ASSUM_TAC(fun th -> try MP (SPECL [`e1:bvl_exp`; `e2:bvl_exp`] th)
                                     (REFL `SOME (e1:bvl_exp,e2:bvl_exp)`)
                             with Failure _ -> th) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    REWRITE_TAC[option_INJ; FORALL_UNWIND_THM1] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[]]);;

let bEvery_CONS = prove
 (`!p x xs. bEvery p [x] /\ bEvery p xs ==> bEvery p (CONS x xs)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[bEvery_def]);;

let handle_ok_Var_Const_list = prove
 (`!xs. ALL (\x. ?v i. x = bvl_Var v \/ x = bvl_Op (IntOp (clos_Const i)) []) xs ==>
        handle_ok xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; handle_ok_def] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[ALL; handle_ok_def] THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN TRY (ASM_REWRITE_TAC[handle_ok_def] THEN NO_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let handle_ok_SmartLet = prove
 (`!xs x. handle_ok [SmartLet xs x] <=> handle_ok xs /\ handle_ok [x]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SmartLet_def] THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN
  ASM_REWRITE_TAC[handle_ok_def; LENGTH_EQ_NIL]);;

(* a local helper: LetLet makes a Let of variables whose body only uses the *)
(* bound variables (the common part of handle_ok_OptionalLetLet and         *)
(* compile_handle_ok)                                                        *)
let BVLPROPSAUX_LetLet_handle_ok = prove
 (`!n (fvs:A spt) e.
     handle_ok [e] /\ bVarBound n [e] ==>
     ?xs b. LetLet n fvs e = bvl_Let xs b /\ ALL isVar xs /\
            bVarBound (LENGTH xs) [b] /\ handle_ok [b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LetLet_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ABBREV_TAC `zs = FILTER (\n. IS_SOME (lookup n (fvs:A spt))) (list_of_seq I n)` THEN
  REWRITE_TAC[injectivity "bvl_exp"] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[ALL_MAP; o_DEF; isVar_def; ALL_T; LENGTH_MAP; bVarBound_SmartLet;
              handle_ok_SmartLet; bVarBound_def] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[bVarBound_MEM] THEN REWRITE_TAC[MEM_GENLIST] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TOP_CASE_TAC THEN
    REWRITE_TAC[bVarBound_def] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SPEC_ALL ALOOKUP_MAPi)) THEN ARITH_TAC;
    MATCH_MP_TAC bVarBound_LESS_EQ THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[LENGTH_GENLIST] THEN ARITH_TAC;
    MATCH_MP_TAC handle_ok_Var_Const_list THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_GENLIST] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN TOP_CASE_TAC THEN MESON_TAC[]]);;

let handle_ok_OptionalLetLet = prove
 (`!e n lx s l nr. handle_ok [e] /\ bVarBound n [e] ==>
                   handle_ok (FST (OptionalLetLet e n lx s l nr))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OptionalLetLet_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[FST] THEN
  MP_TAC(ISPECL [`n:num`; `db_to_set lx`; `e:bvl_exp`] BVLPROPSAUX_LetLet_handle_ok) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[handle_ok_def; LENGTH; let_ok_def; injectivity "bvl_exp"] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* local helpers for compile_handle_ok: the bounds of the compiled parts,  *)
(* the CONS step (HOL4 does a case split inline) and the Handle body       *)
let BVLPROPSAUX_HC_BOUND_TAC : tactic = fun (asl,w as g) ->
  let ok th = let c = concl th in is_eq c &&
     BVLPROPSAUX_has_const "bvl_handle_compile" (lhs c) in
  let ths = filter ok (map snd asl) in
  MAP_EVERY (fun th -> ASSUME_TAC (MATCH_MP compile_IMP_bVarBound th)) ths g;;

let BVLPROPSAUX_handle_ok_CONS_IMP = prove
 (`!x xs. handle_ok [x] /\ handle_ok xs ==> handle_ok (CONS x xs)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[handle_ok_def]);;

let BVLPROPSAUX_LETLET_OK_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> let f,args = strip_comb t in
                       is_const f && fst (dest_const f) = "LetLet" && length args = 3) w in
  (MP_TAC (ISPECL (snd (strip_comb t)) BVLPROPSAUX_LetLet_handle_ok) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[case_def "bvl_exp"]) g;;

let compile_handle_ok = prove
 (`!l n xs. handle_ok (FST (bvl_handle_compile l n xs))`,
  MATCH_MP_TAC BVLPROPSAUX_compile_ind THEN REPEAT CONJ_TAC THEN
  BVLPROPSAUX_HC_PRE_TAC THEN BVLPROPSAUX_HC_BOUND_TAC THEN REWRITE_TAC[handle_ok_def] THEN
  TRY (MATCH_MP_TAC handle_ok_OptionalLetLet ORELSE
       MATCH_MP_TAC BVLPROPSAUX_handle_ok_CONS_IMP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ]) THEN REWRITE_TAC[handle_ok_def] THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[handle_ok_def; bVarBound_def; LENGTH_EQ_NIL] THEN
  TRY BVLPROPSAUX_LETLET_OK_TAC);;

let compile_exp_handle_ok = prove
 (`!l n x. handle_ok [bvl_handle_compile_exp l n x]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_handle_compile_exp_def] THEN
  MP_TAC(SPECL [`l:num`; `n:num`; `[handle_simp (bvl_const_compile_exp x)]`]
           compile_handle_ok) THEN
  X_CHOOSE_THEN `y:bvl_exp` SUBST1_TAC
    (SPECL [`l:num`; `n:num`; `handle_simp (bvl_const_compile_exp x)`]
           BVLPROPSAUX_compile_FST_sing) THEN
  REWRITE_TAC[HD]);;

let compile_seqs_handle_ok = prove
 (`!l x acc. (!y. acc = SOME y ==> handle_ok [y] /\ bVarBound 0 [y]) ==>
             handle_ok [compile_seqs l x acc]`,
  MATCH_MP_TAC compile_seqs_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[compile_seqs_def] THEN
  CASES_ON `bvl_handle_dest_Seq e` THEN ASM_REWRITE_TAC[case_def "option"] THENL
   [REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
    CASES_ON `acc:bvl_exp option` THEN
    REWRITE_TAC[case_def "option"; compile_exp_handle_ok] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; FORALL_UNWIND_THM1]) THEN
    ASM_REWRITE_TAC[handle_ok_def; LENGTH; NOT_SUC; let_ok_def; ALL;
                    compile_exp_handle_ok; injectivity "bvl_exp"] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    MP_TAC(ISPEC `a:bvl_exp#bvl_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:bvl_exp` (X_CHOOSE_THEN `e2:bvl_exp` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[pair_CASE] THEN
    RULE_ASSUM_TAC(fun th -> try MP (SPECL [`e1:bvl_exp`; `e2:bvl_exp`] th)
                                     (REFL `SOME (e1:bvl_exp,e2:bvl_exp)`)
                             with Failure _ -> th) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    REWRITE_TAC[option_INJ; FORALL_UNWIND_THM1] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC compile_seqs_bVarBound THEN ASM_MESON_TAC[]]]);;

let compile_any_handle_ok = prove
 (`!split_seq l n x. handle_ok [compile_any split_seq l n x]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_any_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[compile_exp_handle_ok] THEN MATCH_MP_TAC compile_seqs_handle_ok THEN
  REWRITE_TAC[option_DISTINCT]);;

let handle_ok_CONS = prove
 (`!x xs. handle_ok (CONS x xs) <=> handle_ok [x] /\ handle_ok xs`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[handle_ok_def]);;

let handle_ok_EVERY = prove
 (`!xs. handle_ok xs <=> ALL (\x. handle_ok [x]) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[handle_ok_def; ALL] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [handle_ok_CONS] THEN ASM_REWRITE_TAC[]);;

(* a local helper: a list of expressions without code labels *)
let BVLPROPSAUX_UNIONS_MAP_EMPTY = prove
 (`!l. (!e. MEM e l ==> bvl_get_code_labels e = {}) ==>
       UNIONS (set_of_list (MAP bvl_get_code_labels l)) = {}`,
  REWRITE_TAC[EMPTY_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[]);;

(* HOL4 [simp] *)
let LetLet_code_labels = prove
 (`!x (y:A spt) z. bvl_get_code_labels (LetLet x y z) = bvl_get_code_labels z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LetLet_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[SmartLet_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[bvl_get_code_labels_def] THEN
  REPEAT (W(fun (asl,w) ->
     let t = find_term (fun t -> is_comb t &&
               (try fst (dest_const (rator t)) = "UNIONS" with Failure _ -> false) &&
               is_comb (rand t)) w in
     let l = rand (rand (rand t)) in
     MP_TAC (ISPEC l BVLPROPSAUX_UNIONS_MAP_EMPTY) THEN ANTS_TAC THENL
      [REWRITE_TAC[MEM_MAP; MEM_GENLIST] THEN REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC[] THEN BETA_TAC THEN TRY TOP_CASE_TAC THEN
       REWRITE_TAC BVLPROPSAUX_LABELS_RWS;
       DISCH_THEN SUBST1_TAC])) THEN
  REWRITE_TAC[UNION_EMPTY]);;
let _ = cake_add_simps [LetLet_code_labels];;

(* a local helper: the labels of OptionalLetLet (HOL4 unfolds it inline) *)
let BVLPROPSAUX_OptionalLetLet_code_labels = prove
 (`!e n l s limit nr.
     UNIONS (set_of_list (MAP bvl_get_code_labels
               (FST (OptionalLetLet e n l s limit nr)))) = bvl_get_code_labels e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OptionalLetLet_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC(FST :: LetLet_code_labels :: BVLPROPSAUX_LABELS_RWS));;

let BVLPROPSAUX_HCL_RWS =
  [LetLet_code_labels; BVLPROPSAUX_OptionalLetLet_code_labels; MAP_APPEND;
   SET_OF_LIST_APPEND; UNIONS_UNION; HD; FST] @ BVLPROPSAUX_LABELS_RWS;;

let bvl_handleProof_compile_code_labels = prove
 (`!a b c. UNIONS (set_of_list (MAP bvl_get_code_labels (FST (bvl_handle_compile a b c))))
           SUBSET UNIONS (set_of_list (MAP bvl_get_code_labels c))`,
  MATCH_MP_TAC BVLPROPSAUX_compile_ind THEN REPEAT CONJ_TAC THEN
  BVLPROPSAUX_HC_PRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (NULL_EQ :: BVLPROPSAUX_HCL_RWS)) THEN
  ASM_REWRITE_TAC BVLPROPSAUX_HCL_RWS THEN ASM SET_TAC[]);;

(* HOL4 [local] *)
let get_code_labels_dest_handle_Raise = prove
 (`!c x. dest_handle_Raise c = SOME x ==> bvl_get_code_labels c = bvl_get_code_labels x`,
  REWRITE_TAC[BVLPAUX_dest_handle_Raise_eq] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[bvl_get_code_labels_def]);;

(* HOL4 [local] *)
let get_code_labels_handle_adj_vars = prove
 (`(!x d l. bvl_get_code_labels (handle_adj_vars d l x) = bvl_get_code_labels x) /\
   (!x d l. MAP bvl_get_code_labels (handle_adj_vars1 d l x) =
            MAP bvl_get_code_labels x)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  REWRITE_TAC[handle_adj_vars_def; bvl_get_code_labels_def; MAP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* local tactics for get_code_labels_handle_simp: the cases other than *)
(* make_handle, and the make_handle case (as in evaluate_handle_simp)   *)
let BVLPROPSAUX_HSL_SIMPLE_TAC : tactic =
  ONCE_REWRITE_TAC[handle_simp_def] THEN REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN
  ASM SET_TAC[];;

let BVLPROPSAUX_HSL_MAKE_TAC : tactic =
  ONCE_REWRITE_TAC[handle_simp_def] THEN
  CASES_ON `dest_handle_Raise c` THEN ASM_REWRITE_TAC[case_def "option"] THENL
   [CASES_ON `dest_handle_Let c` THEN ASM_REWRITE_TAC[case_def "option"] THENL
     [CASES_ON `dest_handle_If c` THEN ASM_REWRITE_TAC[case_def "option"] THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN
        REWRITE_TAC(get_code_labels_handle_adj_vars :: BVLPROPSAUX_LABELS_RWS) THEN
        ASM SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BVLPAUX_dest_handle_If_eq] o
              check (fun th -> concl th = `dest_handle_If c = SOME a`)) THEN
        STRIP_TAC THEN RVEQ_TAC THEN
        BVLPROPSAUX_INST_B_TAC [`dhi1:bvl_exp`; `dhi2:bvl_exp`; `dhi3:bvl_exp`] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; injectivity "sum";
                                    distinctness "sum"; PAIR_EQ]) THEN
        CASE_REWRITE_TAC[] THEN REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN ASM SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BVLPAUX_dest_handle_Let_eq] o
            check (fun th -> concl th = `dest_handle_Let c = SOME a`)) THEN
      STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(fun th ->
        let vs,_ = strip_forall (concl th) in
        if length vs = 2 && type_of (el 1 vs) = `:bvl_exp list` &&
           type_of (el 0 vs) = `:bvl_exp`
        then SPECL [`dhl2:bvl_exp`; `dhl1:bvl_exp list`] th else th) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN ASM SET_TAC[]];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BVLPAUX_dest_handle_Raise_eq] o
          check (fun th -> concl th = `dest_handle_Raise c = SOME a`)) THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(fun th ->
      let vs,_ = strip_forall (concl th) in
      if length vs = 1 && type_of (hd vs) = `:bvl_exp` then SPEC `a:bvl_exp` th else th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ]) THEN
    REWRITE_TAC(get_code_labels_handle_adj_vars :: BVLPROPSAUX_LABELS_RWS) THEN
    ASM SET_TAC[]];;

let get_code_labels_handle_simp = prove
 (`(!c. bvl_get_code_labels (handle_simp c) SUBSET bvl_get_code_labels c) /\
   (!c. UNIONS (set_of_list (MAP bvl_get_code_labels (handle_simp_list c))) SUBSET
        UNIONS (set_of_list (MAP bvl_get_code_labels c))) /\
   (!c d l. bvl_get_code_labels (make_handle c d l) SUBSET
            bvl_get_code_labels c UNION bvl_get_code_labels d)`,
  MATCH_MP_TAC handle_simp_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   (map (fun _ -> BVLPROPSAUX_HSL_SIMPLE_TAC) (1--11) @ [BVLPROPSAUX_HSL_MAKE_TAC]));;

let bvl_handleProof_compile_exp_code_labels = prove
 (`!a b c. bvl_get_code_labels (bvl_handle_compile_exp a b c) SUBSET
           bvl_get_code_labels c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_handle_compile_exp_def] THEN
  MP_TAC(SPECL [`a:num`; `b:num`; `[handle_simp (bvl_const_compile_exp c)]`]
           bvl_handleProof_compile_code_labels) THEN
  X_CHOOSE_THEN `y:bvl_exp` SUBST1_TAC
    (SPECL [`a:num`; `b:num`; `handle_simp (bvl_const_compile_exp c)`]
           BVLPROPSAUX_compile_FST_sing) THEN
  REWRITE_TAC(HD :: BVLPROPSAUX_LABELS_RWS) THEN
  MP_TAC(SPEC `bvl_const_compile_exp c` (CONJUNCT1 get_code_labels_handle_simp)) THEN
  MP_TAC(SPEC `c:bvl_exp` bvl_constProof_compile_exp_code_labels) THEN
  SET_TAC[]);;

let compile_seqs_code_labels = prove
 (CASE_TERM `!cut e acc.
     bvl_get_code_labels (compile_seqs cut e acc) SUBSET
     bvl_get_code_labels e UNION
     (match acc with NONE -> {} | SOME r -> bvl_get_code_labels r)`,
  MATCH_MP_TAC compile_seqs_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[compile_seqs_def] THEN
  CASES_ON `bvl_handle_dest_Seq e` THEN ASM_REWRITE_TAC[case_def "option"] THENL
   [REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
    CASES_ON `acc:bvl_exp option` THEN
    REWRITE_TAC(case_def "option" :: BVLPROPSAUX_LABELS_RWS) THEN
    MP_TAC(SPECL [`cut_size:num`; `0`; `e:bvl_exp`]
             bvl_handleProof_compile_exp_code_labels) THEN
    SET_TAC[];
    MP_TAC(ISPEC `a:bvl_exp#bvl_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:bvl_exp` (X_CHOOSE_THEN `e2:bvl_exp` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[pair_CASE] THEN
    RULE_ASSUM_TAC(fun th -> try MP (SPECL [`e1:bvl_exp`; `e2:bvl_exp`] th)
                                     (REFL `SOME (e1:bvl_exp,e2:bvl_exp)`)
                             with Failure _ -> th) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[dest_Seq_thm] o
                  check (fun th -> concl th = `bvl_handle_dest_Seq e = SOME (e1,e2)`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN
    REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN ASM SET_TAC[]]);;
