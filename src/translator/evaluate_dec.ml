(* ========================================================================= *)
(* evaluate_dec: port of HOL4 translator/evaluate_decScript.sml (CakeML      *)
(* v3479).  Defines evaluate_dec_list which is an alternative version of    *)
(* evaluate_decs from evaluateTheory.  This alternative version is adjusted *)
(* to make translation faster.                                               *)
(* ========================================================================= *)

needs "hol4/alist_tree.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "hol4/lprefix_lub.ml";;

type_invention_error := true;;

(* --- define an alternative to evaluate_decs --- *)

(* Same as evaluate_decs from evaluateTheory but modified to not have the  *)
(* cons checks (every_exp one_con_check)                                    *)
let evaluate_dec_list_def = cake_def_wf
  `MEASURE (\x:(FFI)state#v sem_env#dec list. list_size dec_size (SND (SND x)))`
  TERM_TAC
  `(evaluate_dec_list (st:(FFI)state) (env:v sem_env) [] =
      (st,Rval (sem_env_REC nsEmpty nsEmpty):(v sem_env,v)result)) /\
   (evaluate_dec_list st env (CONS d1 (CONS d2 ds)) =
      match evaluate_dec_list st env [d1] with
        (st1,Rval env1) ->
          (match evaluate_dec_list st1 (extend_dec_env env1 env) (CONS d2 ds) with
             (st2,r) -> (st2,combine_dec_result env1 r))
      | (st1,Rerr v7) -> (st1,Rerr v7)) /\
   (evaluate_dec_list st env [Dlet locs p e] =
      if ALL_DISTINCT (pat_bindings p)
      then
        (match evaluate st env [e] with
           (st',Rval v) ->
             (st',
              (match pmatch (sem_env_c env) (state_refs st') p (HD v) [] with
                 No_match -> Rerr (Rraise bind_exn_v)
               | Match_type_error -> Rerr (Rabort Rtype_error)
               | Match new_vals -> Rval (sem_env_REC (alist_to_ns new_vals) nsEmpty)))
         | (st',Rerr err) -> (st',Rerr err))
      else (st,Rerr (Rabort Rtype_error))) /\
   (evaluate_dec_list st env [Dletrec locs funs] =
      (st,
       if ALL_DISTINCT (MAP (\xyz. match xyz with (x,y,z) -> x) funs)
       then Rval (sem_env_REC (build_rec_env funs env nsEmpty) nsEmpty)
       else Rerr (Rabort Rtype_error))) /\
   (evaluate_dec_list st env [Dtype locs tds] =
      if ALL check_dup_ctors tds then
        (state_next_type_stamp_fupd (K (state_next_type_stamp st + LENGTH tds)) st,
         Rval (sem_env_REC nsEmpty (build_tdefs (state_next_type_stamp st) tds)))
      else (st,Rerr (Rabort Rtype_error))) /\
   (evaluate_dec_list st env [Dtabbrev locs tvs tn t] =
      (st,Rval (sem_env_REC nsEmpty nsEmpty))) /\
   (evaluate_dec_list st env [Denv n] =
      match declare_env (state_eval_state st) env with
        NONE -> (st,Rerr (Rabort Rtype_error))
      | SOME (x,es') ->
          (state_eval_state_fupd (K es') st,Rval (sem_env_REC (nsSing n x) nsEmpty))) /\
   (evaluate_dec_list st env [Dexn locs cn ts] =
      (state_next_exn_stamp_fupd (K (state_next_exn_stamp st + 1)) st,
       Rval (sem_env_REC nsEmpty
               (nsSing cn (LENGTH ts,ExnStamp (state_next_exn_stamp st)))))) /\
   (evaluate_dec_list st env [Dmod mn ds] =
      match evaluate_dec_list st env ds with
        (st',r) ->
          (st',
           (match r with
              Rval env' ->
                Rval (sem_env_REC (nsLift mn (sem_env_v env'))
                                  (nsLift mn (sem_env_c env')))
            | Rerr err -> Rerr err))) /\
   (evaluate_dec_list st env [Dlocal lds ds] =
      match evaluate_dec_list st env lds with
        (st1,Rval env1) -> evaluate_dec_list st1 (extend_dec_env env1 env) ds
      | (st1,Rerr v7) -> (st1,Rerr v7))`;;

let evaluate_dec_list_ind = cake_ind "evaluate_dec_list";;

let evaluate_dec_list_with_clock_def = cake_def
  `evaluate_dec_list_with_clock (st:(FFI)state) (env:v sem_env) (k:num)
                                (prog:dec list) =
     let (st',r) = evaluate_dec_list (state_clock_fupd (K k) st) env prog in
     (state_ffi st',r)`;;

(* Terminate: there is a clock for which evaluation terminates, either      *)
(* internally or via FFI, and the accumulated io events match the given     *)
(* io_list.  Diverge: for all clocks, evaluation times out, and the         *)
(* io_trace is the least upper bound of the set of traces produced for each *)
(* clock.  Fail: there is a clock for which evaluation produces a runtime   *)
(* type error.                                                               *)
let semantics_dec_list_def = sem1aux_def
  `(semantics_dec_list (st:(FFI)state) (env:v sem_env) (prog:dec list)
                       (Terminate outcome io_list) <=>
      ?k ffi r.
        evaluate_dec_list_with_clock st env k prog = (ffi,r) /\
        (match r with
           Rerr (Rabort (Rffi_error outcome')) -> outcome = FFI_outcome outcome'
         | r -> ~(r = Rerr (Rabort Rtimeout_error)) /\ outcome = Success) /\
        io_list = ffi_state_io_events ffi /\
        ~(r = Rerr (Rabort Rtype_error))) /\
   (semantics_dec_list st env prog (Diverge io_trace) <=>
      (!k. ?ffi.
         evaluate_dec_list_with_clock st env k prog =
         (ffi,Rerr (Rabort Rtimeout_error))) /\
      lprefix_lub
        (IMAGE
           (\k. llist_fromList
                  (ffi_state_io_events
                     (FST (evaluate_dec_list_with_clock st env k prog))))
           UNIV)
        io_trace) /\
   (semantics_dec_list st env prog Fail <=>
      ?k. SND (evaluate_dec_list_with_clock st env k prog) = Rerr (Rabort Rtype_error))`;;

(* --- define a check that implies evaluate_dec_list is same as evalaute_decs --- *)

let check_cons_dec_list_def = cake_def_wf
  `MEASURE (\x:((mlstring,mlstring,num#stamp)namespace # dec list) +
               ((mlstring,mlstring,num#stamp)namespace # dec).
              sum_CASE x (\p. list_size dec_size (SND p)) (\p. dec_size (SND p)))`
  TERM_TAC
  `(check_cons_dec_list (env_c:(mlstring,mlstring,num#stamp)namespace) [] =
      SOME nsEmpty) /\
   (check_cons_dec_list env_c (CONS d1 ds) =
      match check_cons_dec env_c d1 with
        NONE -> NONE
      | SOME env_c0 ->
          (match check_cons_dec_list (nsAppend env_c0 env_c) ds with
             NONE -> NONE
           | SOME env_c1 -> SOME (nsAppend env_c1 env_c0))) /\
   (check_cons_dec env_c (Dlet locs p e) =
      if every_exp (one_con_check env_c) e then SOME nsEmpty else NONE) /\
   (check_cons_dec env_c (Dletrec locs funs) =
      if ALL (\fne. match fne with (f,n,e) -> every_exp (one_con_check env_c) e) funs
      then SOME nsEmpty else NONE) /\
   (check_cons_dec env_c (Dtype locs tds) = SOME (build_tdefs 0 tds)) /\
   (check_cons_dec env_c (Dtabbrev locs tvs tn t) = SOME nsEmpty) /\
   (check_cons_dec env_c (Denv _) = SOME nsEmpty) /\
   (check_cons_dec env_c (Dexn locs cn ts) =
      SOME (nsSing cn (LENGTH ts,ExnStamp 0))) /\
   (check_cons_dec env_c (Dmod mn ds) =
      match check_cons_dec_list env_c ds with
        NONE -> NONE
      | SOME env_c0 -> SOME (nsLift mn env_c0)) /\
   (check_cons_dec env_c (Dlocal lds ds) =
      match check_cons_dec_list env_c lds with
        NONE -> NONE
      | SOME env_c0 -> check_cons_dec_list (nsAppend env_c0 env_c) ds)`;;

let check_cons_dec_list_ind = cake_ind "check_cons_dec_list";;

let check_cons_dec_list_isPREFIX = prove
 (`!env_c xs ys x.
     check_cons_dec_list env_c xs = SOME x /\ isPREFIX ys xs ==>
     ?y. check_cons_dec_list env_c ys = SOME y`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN CASES_ON `ys:dec list` THEN
  REWRITE_TAC[isPREFIX; check_cons_dec_list_def] THEN SIMP[] THEN
  STRIP_TAC THEN QCASES_ON "check_cons_dec env_c h" THEN FS[] THEN
  QCASES_ON "check_cons_dec_list (nsAppend a env_c) t" THEN FS[] THEN
  FIRST_X_ASSUM (QSPECL_THEN ["nsAppend a env_c"; "a1"; "a'"] MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 [local,simp]: not registered (descendants do not see it in HOL4) *)
let check_cons_dec_list_sing = prove
 (`check_cons_dec_list env_c [d] = check_cons_dec env_c d`,
  REWRITE_TAC[check_cons_dec_list_def] THEN
  QCASES_ON "check_cons_dec env_c d" THEN SIMP[nsAppend_nsEmpty]);;

(* --- theorems --- *)

(* recursion under ALL2 (HOL4 LIST_REL): the admissibility rule of          *)
(* hol4/list.ml, registered for this definition only                         *)
let con_check_eqv_def =
  let saved = !cake_admissible_rules in
  cake_register_admissible "ALL2" LISTAUX_ADMISSIBLE_ALL2;
  let th = try cake_def
    `con_check_eqv (x:(mlstring,mlstring,num#stamp)namespace)
                   (y:(mlstring,mlstring,num#stamp)namespace) <=>
       match (x,y) with
         (Bind xs ys,Bind xs1 ys1) ->
           ALL2 (\p q. match (p,q) with ((a,x1,_),(b,y1,_)) -> a = b /\ x1 = y1)
             xs xs1 /\
           ALL2 (\p q. match (p,q) with ((a,x1),(b,y1)) -> a = b /\ con_check_eqv x1 y1)
             ys ys1`
    with e -> (cake_admissible_rules := saved; raise e) in
  cake_admissible_rules := saved; th;;

let con_check_eqv_ind = cake_ind "con_check_eqv";;

(* HOL4 [local,simp]: not registered (descendants do not see it in HOL4) *)
let con_check_eqv_refl = prove
 (`!x. con_check_eqv x x`,
  SUBGOAL_THEN `!x y. x = y ==> con_check_eqv x x` (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC con_check_eqv_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN QCASES_ON "x" THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[con_check_eqv_def] THEN SIMP[] THEN
  CONJ_TAC THEN MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  SIMP[] THEN ASM_MESON_TAC[]);;

let con_check_eqv_nsAppend = prove
 (`con_check_eqv x1 y1 /\ con_check_eqv x2 y2 ==>
   con_check_eqv (nsAppend x1 x2) (nsAppend y1 y2)`,
  ONCE_REWRITE_TAC[con_check_eqv_def] THEN
  QCASES_ON "x1" THEN QCASES_ON "y1" THEN QCASES_ON "x2" THEN QCASES_ON "y2" THEN
  SIMP[nsAppend_def] THEN STRIP_TAC THEN
  ASM_MESON_TAC[LIST_REL_APPEND_suff]);;

(* helper: ALOOKUP in two alists related key by key *)
let EVDECAUX_ALL2_ALOOKUP = prove
 (`!(R:B->C->bool) (l1:(A#B)list) (l2:(A#C)list) k.
     ALL2 (\p q. FST p = FST q /\ R (SND p) (SND q)) l1 l2 ==>
     OPTREL R (ALOOKUP l1 k) (ALOOKUP l2 k)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALOOKUP_def; OPTREL_THM] THEN
  PAIR_CASES_ON `h:A#B` THEN PAIR_CASES_ON `h':A#C` THEN
  REWRITE_TAC[ALOOKUP_def; FST; SND] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[OPTREL_THM]);;

(* helper: con_check_eqv_def on Bind, with the paired lambdas as FST/SND *)
let EVDECAUX_con_check_eqv_Bind = prove
 (`con_check_eqv (Bind xs ys) (Bind xs1 ys1) <=>
   ALL2 (\p q. FST p = FST q /\ (\a b. FST a = FST b) (SND p) (SND q)) xs xs1 /\
   ALL2 (\p q. FST p = FST q /\ con_check_eqv (SND p) (SND q)) ys ys1`,
  GEN_REWRITE_TAC LAND_CONV [con_check_eqv_def] THEN SIMP[] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN SIMP[]);;

(* helper: con_check_eqv relates the lookups (arities agree) *)
let EVDECAUX_con_check_eqv_nsLookup = prove
 (`!(id:(mlstring,mlstring)id) x y. con_check_eqv x y ==>
     OPTREL (\a b. FST a = FST b) (nsLookup x id) (nsLookup y id)`,
  MATCH_MP_TAC id_INDUCT THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC; DISCH_TAC THEN REPEAT GEN_TAC] THEN
  QCASES_ON "x" THEN QCASES_ON "y" THEN REWRITE_TAC[EVDECAUX_con_check_eqv_Bind] THEN
  SIMP[nsLookup_def] THEN STRIP_TAC THENL
   [MATCH_MP_TAC EVDECAUX_ALL2_ALOOKUP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP EVDECAUX_ALL2_ALOOKUP) THEN
  DISCH_THEN (MP_TAC o SPEC `a0:mlstring`) THEN EVERY_CASE_TAC THEN
  SIMP[OPTREL_THM] THEN ASM_MESON_TAC[]);;

(* helper: con_check_eqv gives the same constructor checks *)
let EVDECAUX_do_con_check = prove
 (`con_check_eqv env2 env1 ==>
   !cn l. do_con_check env1 cn l = do_con_check env2 cn l`,
  DISCH_TAC THEN MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[do_con_check_def] THEN
  SIMP[] THEN X_GEN_TAC `id:(mlstring,mlstring)id` THEN GEN_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `id:(mlstring,mlstring)id` o
                 MATCH_MP EVDECAUX_con_check_eqv_nsLookup) THEN
  EVERY_CASE_TAC THEN SIMP[OPTREL_THM] THEN MESON_TAC[]);;

let con_check_eqv_switch = prove
 (`con_check_eqv env2 env1 ==>
   every_exp (one_con_check env1) e = every_exp (one_con_check env2) e`,
  DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN QCASES_ON "x" THEN REWRITE_TAC[one_con_check_def] THEN
  ASM_MESON_TAC[EVDECAUX_do_con_check]);;

(* HOL4 [local] *)
let con_check_eqv_build_tdefs = prove
 (`!m n. con_check_eqv (build_tdefs m tds) (build_tdefs n tds)`,
  SUBGOAL_THEN `!tds m n. con_check_eqv (build_tdefs m tds) (build_tdefs n tds)`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[build_tdefs_def; con_check_eqv_refl] THEN
  PAIR_CASES_ON `h:tvarN list # typeN # (conN # ast_t list) list` THEN
  REWRITE_TAC[build_tdefs_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC con_check_eqv_nsAppend THEN
  ASM_REWRITE_TAC[alist_to_ns_def; EVDECAUX_con_check_eqv_Bind; ALL2] THEN
  REWRITE_TAC[build_constrs_def] THEN
  SPEC_TAC (`h2:(conN # ast_t list) list`, `l:(conN # ast_t list) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; REVERSE; ALL2] THEN
  MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[ALL2] THEN
  PAIR_CASES_ON `h:conN # ast_t list` THEN SIMP[]);;

let EVDECAUX_check_CONS = prove
 (`check_cons_dec_list env_c (CONS d1 ds) = SOME env_c1 <=>
   ?env_c0 env_c2. check_cons_dec env_c d1 = SOME env_c0 /\
                   check_cons_dec_list (nsAppend env_c0 env_c) ds = SOME env_c2 /\
                   env_c1 = nsAppend env_c2 env_c0`,
  ONCE_REWRITE_TAC[check_cons_dec_list_def] THEN
  QCASES_ON "check_cons_dec env_c d1" THEN SIMP[] THEN
  QCASES_ON "check_cons_dec_list (nsAppend a env_c) ds" THEN SIMP[] THEN MESON_TAC[]);;

let EVDECAUX_CONS_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[EVDECAUX_check_CONS] THEN
  DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[evaluate_dec_list_def; evaluate_decs_def] THEN
  MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env [d1]` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result`
    ASSUME_TAC)) THEN
  REMOVE_THEN "IH1" (MP_TAC o SPECL [`s1:(FFI)state`; `r1:(v sem_env,v)result`;
    `env_c:(mlstring,mlstring,num#stamp)namespace`;
    `env_c0:(mlstring,mlstring,num#stamp)namespace`]) THEN
  ASM_REWRITE_TAC[check_cons_dec_list_sing] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "r1" THEN SIMP[] THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `a:v sem_env`) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    REMOVE_THEN "IH2" (MP_TAC o SPECL [`s1:(FFI)state`; `a:v sem_env`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (ISPEC `evaluate_dec_list (s1:(FFI)state) (extend_dec_env a env) (CONS d2 ds)`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`;
      `nsAppend env_c0 env_c:(mlstring,mlstring,num#stamp)namespace`;
      `env_c2:(mlstring,mlstring,num#stamp)namespace`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[extend_dec_env_def; sem_env_INFO.ri_accessors] THEN
      MATCH_MP_TAC con_check_eqv_nsAppend THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
    QPAT_X_ASSUM "combine_dec_result _ _ = _" (SUBST_ALL_TAC o SYM) THEN
    QCASES_ON "r2" THEN SIMP[combine_dec_result_def] THEN
    FS[] THEN MATCH_MP_TAC con_check_eqv_nsAppend THEN ASM_REWRITE_TAC[];
    DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN SIMP[]];;

let EVDECAUX_FINISH_TAC thl : tactic =
  DISCH_THEN (MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
  DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN SIMP thl;;

let EVDECAUX_SING_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[check_cons_dec_list_sing; check_cons_dec_list_def; option_INJ] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[evaluate_dec_list_def; evaluate_decs_def];;

(* evaluate_dec_list and evaluate_decs agree when the constructor checks   *)
(* succeed; the induction keeps an environment con_check_eqv to env.c       *)
let EVDECAUX_eq_evaluate_decs = prove
 (`!(st:(FFI)state) env ds st1 res env_c env_c1.
      check_cons_dec_list env_c ds = SOME env_c1 /\
      con_check_eqv (sem_env_c env) env_c /\
      evaluate_dec_list st env ds = (st1,res)
      ==>
      evaluate_decs st env ds = (st1,res) /\
      (!r. res = Rval r ==> con_check_eqv (sem_env_c r) env_c1)`,
  MATCH_MP_TAC evaluate_dec_list_ind THEN REPEAT CONJ_TAC THENL
   [(* [] *)
    REWRITE_TAC[evaluate_dec_list_def; evaluate_decs_def; check_cons_dec_list_def] THEN
    SIMP[con_check_eqv_refl];
    (* d1::d2::ds *)
    EVDECAUX_CONS_TAC;
    (* Dlet *)
    REPEAT GEN_TAC THEN REWRITE_TAC[check_cons_dec_list_sing; check_cons_dec_list_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN `every_exp (one_con_check (sem_env_c (env:v sem_env))) e` ASSUME_TAC THENL
     [ASM_MESON_TAC[con_check_eqv_switch]; ALL_TAC] THEN
    SUBGOAL_THEN `evaluate_decs (st:(FFI)state) env [Dlet locs p e] =
                  evaluate_dec_list st env [Dlet locs p e]`
      SUBST1_TAC THENL
     [REWRITE_TAC[evaluate_dec_list_def; evaluate_decs_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN (fun th -> REWRITE_TAC[th] THEN MP_TAC th) THEN
    REWRITE_TAC[evaluate_dec_list_def] THEN EVERY_CASE_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN SIMP[con_check_eqv_refl];
    (* Dletrec *)
    REPEAT GEN_TAC THEN REWRITE_TAC[check_cons_dec_list_sing; check_cons_dec_list_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM (fun th -> let sw = GEN `e:exp` (MATCH_MP con_check_eqv_switch th) in
                           RULE_ASSUM_TAC (REWRITE_RULE[sw])) THEN
    SUBGOAL_THEN `evaluate_decs (st:(FFI)state) env [Dletrec locs funs] =
                  evaluate_dec_list st env [Dletrec locs funs]`
      SUBST1_TAC THENL
     [REWRITE_TAC[evaluate_dec_list_def; evaluate_decs_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN (fun th -> REWRITE_TAC[th] THEN MP_TAC th) THEN
    REWRITE_TAC[evaluate_dec_list_def] THEN COND_CASES_TAC THEN
    DISCH_THEN (MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
    DISCH_THEN (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN SIMP[con_check_eqv_refl];
    (* Dtype *)
    EVDECAUX_SING_TAC THEN COND_CASES_TAC THEN
    EVDECAUX_FINISH_TAC[con_check_eqv_build_tdefs];
    (* Dtabbrev *)
    EVDECAUX_SING_TAC THEN EVDECAUX_FINISH_TAC[con_check_eqv_refl];
    (* Denv *)
    EVDECAUX_SING_TAC THEN EVERY_CASE_TAC THEN EVDECAUX_FINISH_TAC[con_check_eqv_refl];
    (* Dexn *)
    EVDECAUX_SING_TAC THEN
    EVDECAUX_FINISH_TAC[nsSing_def; EVDECAUX_con_check_eqv_Bind; ALL2];
    (* Dmod *)
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[check_cons_dec_list_sing; check_cons_dec_list_def; option_case_eq;
                option_DISTINCT; option_INJ] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `c0:(mlstring,mlstring,num#stamp)namespace` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[evaluate_dec_list_def; evaluate_decs_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`s1:(FFI)state`; `r1:(v sem_env,v)result`;
      `env_c:(mlstring,mlstring,num#stamp)namespace`;
      `c0:(mlstring,mlstring,num#stamp)namespace`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (is_var o rhs o concl)) THEN
    QCASES_ON "r1" THEN SIMP[] THEN EVDECAUX_FINISH_TAC[] THEN
    REWRITE_TAC[nsLift_def; EVDECAUX_con_check_eqv_Bind; ALL2] THEN FS[];
    (* Dlocal *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[check_cons_dec_list_sing; check_cons_dec_list_def; option_case_eq;
                option_DISTINCT] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `c0:(mlstring,mlstring,num#stamp)namespace` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[evaluate_dec_list_def; evaluate_decs_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env lds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    REMOVE_THEN "IH1" (MP_TAC o SPECL [`s1:(FFI)state`; `r1:(v sem_env,v)result`;
      `env_c:(mlstring,mlstring,num#stamp)namespace`;
      `c0:(mlstring,mlstring,num#stamp)namespace`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    QCASES_ON "r1" THEN SIMP[] THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC `a:v sem_env`) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s1:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`st1:(FFI)state`; `res:(v sem_env,v)result`;
        `nsAppend c0 env_c:(mlstring,mlstring,num#stamp)namespace`;
        `env_c1:(mlstring,mlstring,num#stamp)namespace`]) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `con_check_eqv (sem_env_c (extend_dec_env (a:v sem_env) env))
                      (nsAppend c0 env_c)` (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[extend_dec_env_def; sem_env_INFO.ri_accessors] THEN
      MATCH_MP_TAC con_check_eqv_nsAppend THEN ASM_REWRITE_TAC[];
      EVDECAUX_FINISH_TAC[]]]);;

(* HOL4 also quantifies two variables st1 and res that do not occur *)
let evaluate_dec_list_eq_evaluate_decs = prove
 (`!(st:(FFI)state) env ds.
     IS_SOME (check_cons_dec_list (sem_env_c env) ds) ==>
     evaluate_dec_list st env ds = evaluate_decs st env ds`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN
  MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_MESON_TAC[EVDECAUX_eq_evaluate_decs; con_check_eqv_refl]);;

(* discharge a conjunction: assume the conjuncts that are not equations     *)
(* with a variable on one side, then substitute those equations (the       *)
(* variable on the right is replaced when both sides are variables)        *)
let EVDECAUX_SUBST_DISCH_TAC : tactic =
  DISCH_THEN (fun th ->
    let ths = CONJUNCTS th in
    let is_veq t = is_eq t && (is_var (rhs t) || is_var (lhs t)) in
    let eqs,others = partition (fun th -> is_veq (concl th)) ths in
    MAP_EVERY ASSUME_TAC others THEN
    MAP_EVERY (fun e -> let t = concl e in
                 if is_var (rhs t) then SUBST_ALL_TAC (SYM e) else SUBST_ALL_TAC e) eqs);;

let EVDECAUX_SC_SIMPLE_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN GEN_TAC THEN
  EXISTS_TAC `ck:num` THEN EVERY_CASE_TAC THEN GVS[];;

let evaluate_dec_list_set_clock = prove
 (`!(s:(FFI)state) env decs s1 res.
     evaluate_dec_list s env decs = (s1,res) /\
     ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !ck. ?ck1. evaluate_dec_list (state_clock_fupd (K ck1) s) env decs =
                (state_clock_fupd (K ck) s1,res)`,
  MATCH_MP_TAC evaluate_dec_list_ind THEN REPEAT CONJ_TAC THENL
   [(* [] *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def; PAIR_EQ] THEN STRIP_TAC THEN
    GEN_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[];
    (* d1::d2::ds *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env [d1]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN SIMP[] THENL
     [MP_TAC (ISPEC `evaluate_dec_list (s2:(FFI)state) (extend_dec_env a env) (CONS d2 ds)`
        PAIR_SURJECTIVE) THEN
      DISCH_THEN (X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `r3:(v sem_env,v)result`
        ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN GEN_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s3:(FFI)state`; `r3:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `~(res = Rerr (Rabort Rtimeout_error):(v sem_env,v)result)` THEN
        QPAT_X_ASSUM "combine_dec_result _ _ = _" (SUBST1_TAC o SYM) THEN
          REWRITE_TAC[combine_dec_result_eq_Rerr];
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_TAC `ck2:num` o SPEC `ck:num`) THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rval a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN
      DISCH_THEN (X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
      EXISTS_TAC `ck1:num` THEN ASM_REWRITE_TAC[] THEN SIMP[];
      EVDECAUX_SUBST_DISCH_TAC THEN GEN_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rerr a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
      EXISTS_TAC `ck1:num` THEN ASM_REWRITE_TAC[] THEN SIMP[]];
    (* Dlet *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [ALL_TAC;
      REWRITE_TAC[PAIR_EQ] THEN EVDECAUX_SUBST_DISCH_TAC THEN GEN_TAC THEN
      EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[]] THEN
    MP_TAC (ISPEC `evaluate (st:(FFI)state) env [e]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v list,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN GEN_TAC THEN
    MP_TAC (SPECL [`st:(FFI)state`; `env:v sem_env`; `[e:exp]`; `s2:(FFI)state`;
                   `r2:(v list,v)result`] evaluate_set_clock) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [QCASES_ON "r2" THEN GVS[]; ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
    EXISTS_TAC `ck1:num` THEN ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN GVS[];
    (* Dletrec, Dtype, Dtabbrev, Denv, Dexn *)
    EVDECAUX_SC_SIMPLE_TAC; EVDECAUX_SC_SIMPLE_TAC; EVDECAUX_SC_SIMPLE_TAC;
    EVDECAUX_SC_SIMPLE_TAC; EVDECAUX_SC_SIMPLE_TAC;
    (* Dmod *)
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN GEN_TAC THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [QCASES_ON "r2" THEN GVS[]; ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
    EXISTS_TAC `ck1:num` THEN ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN GVS[];
    (* Dlocal *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env lds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN SIMP[] THENL
     [DISCH_TAC THEN GEN_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s1:(FFI)state`; `res:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (X_CHOOSE_TAC `ck2:num` o SPEC `ck:num`) THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rval a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN
      DISCH_THEN (X_CHOOSE_TAC `ck1:num` o SPEC `ck2:num`) THEN
      EXISTS_TAC `ck1:num` THEN ASM_REWRITE_TAC[] THEN SIMP[];
      EVDECAUX_SUBST_DISCH_TAC THEN GEN_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rerr a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (X_CHOOSE_TAC `ck1:num` o SPEC `ck:num`) THEN
      EXISTS_TAC `ck1:num` THEN ASM_REWRITE_TAC[] THEN SIMP[]]]);;

(* helpers: the empty environment and combine_dec_result *)
let EVDECAUX_extend_dec_env_empty = prove
 (`!env:v sem_env. extend_dec_env (sem_env_REC nsEmpty nsEmpty) env = env`,
  REWRITE_TAC[extend_dec_env_def; sem_env_INFO.ri_accessors; nsAppend_nsEmpty;
              sem_env_component_equality]);;

let EVDECAUX_combine_dec_result_empty = prove
 (`!r:(v sem_env,v)result. combine_dec_result (sem_env_REC nsEmpty nsEmpty) r = r`,
  GEN_TAC THEN QCASES_ON "r" THEN
  REWRITE_TAC[combine_dec_result_def; sem_env_INFO.ri_accessors; nsAppend_nsEmpty] THEN
  SIMP[sem_env_component_equality; sem_env_INFO.ri_accessors]);;

let EVDECAUX_combine_dec_result_Rval_empty = prove
 (`!env:v sem_env.
     combine_dec_result env (Rval (sem_env_REC nsEmpty nsEmpty):(v sem_env,v)result) =
     Rval env`,
  REWRITE_TAC[combine_dec_result_def; sem_env_INFO.ri_accessors; nsAppend_nsEmpty] THEN
  SIMP[sem_env_component_equality; sem_env_INFO.ri_accessors]);;

let EVDECAUX_combine_dec_result_combine = prove
 (`!env1 env2 (r:(v sem_env,v)result).
     combine_dec_result env1 (combine_dec_result env2 r) =
     combine_dec_result (extend_dec_env env2 env1) r`,
  REPEAT GEN_TAC THEN QCASES_ON "r" THEN
  SIMP[combine_dec_result_def; extend_dec_env_def; sem_env_INFO.ri_accessors;
       nsAppend_assoc]);;

let EVDECAUX_combine_dec_result_thm = prove
 (`(!env env'. combine_dec_result env (Rval env':(v sem_env,v)result) =
               Rval (extend_dec_env env' env)) /\
   (!env e. combine_dec_result env (Rerr e:(v sem_env,v)result) = Rerr e)`,
  REWRITE_TAC[combine_dec_result_def; extend_dec_env_def] THEN SIMP[]);;

let evaluate_dec_list_cons = prove
 (CASE_TERM `!(s:(FFI)state) env d ds.
     evaluate_dec_list s env (CONS d ds) =
     match evaluate_dec_list s env [d] with
       (s1,Rval env1) ->
         (match evaluate_dec_list s1 (extend_dec_env env1 env) ds with
            (s2,r) -> (s2,combine_dec_result env1 r))
     | (s1,Rerr v7) -> (s1,Rerr v7)`,
  REPEAT GEN_TAC THEN QCASES_ON "ds" THENL
   [MP_TAC (ISPEC `evaluate_dec_list (s:(FFI)state) env [d]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result`
      SUBST1_TAC)) THEN
    QCASES_ON "r1" THEN
    SIMP[evaluate_dec_list_def; EVDECAUX_combine_dec_result_Rval_empty];
    GEN_REWRITE_TAC LAND_CONV [evaluate_dec_list_def] THEN REFL_TAC]);;

let evaluate_dec_list_append = prove
 (CASE_TERM `!(s:(FFI)state) env xs ds.
     evaluate_dec_list s env (APPEND xs ds) =
     match evaluate_dec_list s env xs with
       (s1,Rval env1) ->
         (match evaluate_dec_list s1 (extend_dec_env env1 env) ds with
            (s2,r) -> (s2,combine_dec_result env1 r))
     | (s1,Rerr v7) -> (s1,Rerr v7)`,
  INDUCT_ON `xs:dec list` THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; evaluate_dec_list_def] THEN SIMP[] THEN
    REWRITE_TAC[EVDECAUX_extend_dec_env_empty] THEN
    MP_TAC (ISPEC `evaluate_dec_list (s:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      SUBST1_TAC)) THEN
    SIMP[EVDECAUX_combine_dec_result_empty];
    ALL_TAC] THEN
  X_GEN_TAC `h:dec` THEN X_GEN_TAC `t:dec list` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[evaluate_dec_list_cons] THEN
  MP_TAC (ISPEC `evaluate_dec_list (s:(FFI)state) env [h]` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(v sem_env,v)result`
    SUBST1_TAC)) THEN
  QCASES_ON "r1" THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPEC `evaluate_dec_list (s1:(FFI)state) (extend_dec_env a env) t`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
    SUBST1_TAC)) THEN
  QCASES_ON "r2" THEN SIMP[EVDECAUX_combine_dec_result_thm] THEN
  MP_TAC (ISPEC `evaluate_dec_list (s2:(FFI)state)
                   (extend_dec_env (extend_dec_env a' a) env) ds` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `r3:(v sem_env,v)result`
    SUBST1_TAC)) THEN
  SIMP[EVDECAUX_combine_dec_result_combine]);;

let evaluate_dec_list_add_to_clock = prove
 (`!(s:(FFI)state) e p s' r extra.
     evaluate_dec_list s e p = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
     evaluate_dec_list (state_clock_fupd (K (state_clock s + extra)) s) e p =
     (state_clock_fupd (K (state_clock s' + extra)) s',r)`,
  MATCH_MP_TAC evaluate_dec_list_ind THEN REPEAT CONJ_TAC THENL
   [(* [] *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def; PAIR_EQ] THEN
    EVDECAUX_SUBST_DISCH_TAC THEN REWRITE_TAC[];
    (* d1::d2::ds *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env [d1]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN SIMP[] THENL
     [MP_TAC (ISPEC `evaluate_dec_list (s2:(FFI)state) (extend_dec_env a env) (CONS d2 ds)`
        PAIR_SURJECTIVE) THEN
      DISCH_THEN (X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `r3:(v sem_env,v)result`
        ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s3:(FFI)state`; `r3:(v sem_env,v)result`;
                                  `extra:num`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `~(r = Rerr (Rabort Rtimeout_error):(v sem_env,v)result)` THEN
        QPAT_X_ASSUM "combine_dec_result _ _ = _" (SUBST1_TAC o SYM) THEN
        REWRITE_TAC[combine_dec_result_eq_Rerr];
        ALL_TAC] THEN
      DISCH_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rval a:(v sem_env,v)result`;
                                         `extra:num`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN SIMP[];
      EVDECAUX_SUBST_DISCH_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rerr a:(v sem_env,v)result`;
                                         `extra:num`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[]];
    (* Dlet *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN EVDECAUX_SUBST_DISCH_TAC THEN REWRITE_TAC[]] THEN
    MP_TAC (ISPEC `evaluate (st:(FFI)state) env [e]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v list,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`st:(FFI)state`; `env:v sem_env`; `[e:exp]`; `s2:(FFI)state`;
                   `r2:(v list,v)result`; `extra:num`] evaluate_add_to_clock) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [QCASES_ON "r2" THEN GVS[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN QCASES_ON "r2" THEN GVS[];
    (* Dletrec *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Dtype *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Dtabbrev *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Denv *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Dexn *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Dmod *)
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`;
                                      `extra:num`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [QCASES_ON "r2" THEN GVS[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN QCASES_ON "r2" THEN GVS[];
    (* Dlocal *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env lds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN SIMP[] THENL
     [DISCH_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s':(FFI)state`; `r:(v sem_env,v)result`;
                                  `extra:num`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rval a:(v sem_env,v)result`;
                                         `extra:num`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN SIMP[];
      EVDECAUX_SUBST_DISCH_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rerr a:(v sem_env,v)result`;
                                         `extra:num`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP[]]]);;

let eval_dec_list_no_eval_simulation = prove
 (`!(s:(FFI)state) env decs s' res.
     evaluate_dec_list s env decs = (s',res) /\ state_eval_state s = NONE /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     state_eval_state s' = NONE /\
     evaluate_dec_list (state_eval_state_fupd (K es) s) env decs =
     (state_eval_state_fupd (K es) s',res)`,
  MATCH_MP_TAC evaluate_dec_list_ind THEN REPEAT CONJ_TAC THENL
   [(* [] *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def; PAIR_EQ] THEN
    EVDECAUX_SUBST_DISCH_TAC THEN ASM_REWRITE_TAC[];
    (* d1::d2::ds *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env [d1]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN SIMP[] THENL
     [MP_TAC (ISPEC `evaluate_dec_list (s2:(FFI)state) (extend_dec_env a env) (CONS d2 ds)`
        PAIR_SURJECTIVE) THEN
      DISCH_THEN (X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `r3:(v sem_env,v)result`
        ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rval a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s3:(FFI)state`; `r3:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `~(res = Rerr (Rabort Rtype_error):(v sem_env,v)result)` THEN
        QPAT_X_ASSUM "combine_dec_result _ _ = _" (SUBST1_TAC o SYM) THEN
        REWRITE_TAC[combine_dec_result_eq_Rerr];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
      FIRST_X_ASSUM (SUBST1_TAC o SYM o check (is_var o rhs o concl)) THEN
      ASM_REWRITE_TAC[];
      EVDECAUX_SUBST_DISCH_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rerr a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]];
    (* Dlet *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]] THEN
    MP_TAC (ISPEC `evaluate (st:(FFI)state) env [e]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v list,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC (SPECL [`st:(FFI)state`; `env:v sem_env`; `[e:exp]`; `s2:(FFI)state`;
                   `r2:(v list,v)result`] (CONJUNCT1 eval_no_eval_simulation)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [QCASES_ON "r2" THEN GVS[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN GVS[];
    (* Dletrec *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Dtype *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Dtabbrev *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Denv *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[declare_env_def];
    (* Dexn *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN STRIP_TAC THEN
    EVERY_CASE_TAC THEN GVS[];
    (* Dmod *)
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [QCASES_ON "r2" THEN GVS[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN GVS[];
    (* Dlocal *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env lds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN QCASES_ON "r2" THEN SIMP[] THENL
     [STRIP_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rval a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s':(FFI)state`; `res:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
      EVDECAUX_SUBST_DISCH_TAC THEN
      REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `Rerr a:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]]]);;

let evaluate_dec_list_call_FFI_rel_imp = prove
 (`!(s:(FFI)state) e p s' r.
     evaluate_dec_list s e p = (s',r) ==> RTC call_FFI_rel (state_ffi s) (state_ffi s')`,
  MATCH_MP_TAC evaluate_dec_list_ind THEN REPEAT CONJ_TAC THENL
   [(* [] *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def; PAIR_EQ] THEN
    DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[RTC_REFL];
    (* d1::d2::ds *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env [d1]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    QCASES_ON "r2" THEN SIMP[] THENL
     [MP_TAC (ISPEC `evaluate_dec_list (s2:(FFI)state) (extend_dec_env a env) (CONS d2 ds)`
        PAIR_SURJECTIVE) THEN
      DISCH_THEN (X_CHOOSE_THEN `s3:(FFI)state` (X_CHOOSE_THEN `r3:(v sem_env,v)result`
        ASSUME_TAC)) THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s3:(FFI)state`; `r3:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SIMP[] THEN STRIP_TAC THEN
      ASM_MESON_TAC[RTC_TRANS];
      STRIP_TAC THEN ASM_MESON_TAC[]];
    (* Dlet *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[RTC_REFL]] THEN
    MP_TAC (ISPEC `evaluate (st:(FFI)state) env [e]` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v list,v)result`
      ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `RTC call_FFI_rel (state_ffi (st:(FFI)state)) (state_ffi s2)` ASSUME_TAC THENL
     [MATCH_MP_TAC (CONJUNCT1 evaluate_call_FFI_rel_imp) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    QCASES_ON "r2" THEN SIMP[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    (* Dletrec *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT1) THEN SIMP[RTC_REFL];
    (* Dtype *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT1) THEN SIMP[RTC_REFL];
    (* Dtabbrev *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT1) THEN SIMP[RTC_REFL];
    (* Denv *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT1) THEN SIMP[RTC_REFL];
    (* Dexn *)
    REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_dec_list_def] THEN EVERY_CASE_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT1) THEN SIMP[RTC_REFL];
    (* Dmod *)
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env ds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    REMOVE_THEN "IH" (MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SIMP[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    (* Dlocal *)
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[evaluate_dec_list_def] THEN
    MP_TAC (ISPEC `evaluate_dec_list (st:(FFI)state) env lds` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(v sem_env,v)result`
      ASSUME_TAC)) THEN
    REMOVE_THEN "IH1" (MP_TAC o SPECL [`s2:(FFI)state`; `r2:(v sem_env,v)result`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    QCASES_ON "r2" THEN SIMP[] THENL
     [DISCH_TAC THEN
      REMOVE_THEN "IH2" (MP_TAC o SPECL [`s2:(FFI)state`; `a:v sem_env`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN (MP_TAC o SPECL [`s':(FFI)state`; `r:(v sem_env,v)result`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RTC_TRANS];
      STRIP_TAC THEN ASM_MESON_TAC[]]]);;
