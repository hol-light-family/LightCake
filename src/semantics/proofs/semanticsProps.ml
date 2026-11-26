(* ========================================================================= *)
(* semanticsProps: port of HOL4 semantics/proofs/semanticsPropsScript.sml    *)
(* (CakeML v3479).  Theorems about the top-level semantics, including        *)
(* totality and determinism.                                                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 fromList is llist_fromList; HOL4 xs isPREFIX ys is isPREFIX xs ys  *)
(*   (infix <<=).                                                            *)
(* - HOL4 reads A UNION B UNION C as (A UNION B) UNION C (its UNION is left  *)
(*   associative, HOL Light's is right associative): written with the       *)
(*   parentheses.                                                            *)
(* - HOL4's tac1 and tac2 of semantics_prog_deterministic are replaced by    *)
(*   lemmas on pairs of behaviours (SEMPROPSAUX_ names are local helpers).   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/semantics.ml";;
needs "semantics/proofs/typeSound.ml";;

type_invention_error := true;;

(* HOL4's ELIM_UNCURRY form of evaluate_prog_with_clock_def *)

let SEMPROPSAUX_evaluate_prog_with_clock = prove
 (`!(st:(FFI)state) env k (prog:dec list).
     evaluate_prog_with_clock st env k prog =
     (state_ffi (FST (evaluate_decs (state_clock_fupd (combin_K k) st) env prog)),
      SND (evaluate_decs (state_clock_fupd (combin_K k) st) env prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_prog_with_clock_def] THEN
  SPEC_TAC(`evaluate_decs (state_clock_fupd (combin_K k) (st:(FFI)state)) env prog`,
           `q:(FFI)state#(v sem_env,v)result`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let evaluate_prog_events_determ = prove
 (`!(st:(FFI)state) env k (p:dec list) k'.
     LENGTH (ffi_state_io_events (FST (evaluate_prog_with_clock st env k p))) =
     LENGTH (ffi_state_io_events (FST (evaluate_prog_with_clock st env k' p)))
     ==> ffi_state_io_events (FST (evaluate_prog_with_clock st env k p)) =
         ffi_state_io_events (FST (evaluate_prog_with_clock st env k' p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEMPROPSAUX_evaluate_prog_with_clock] THEN
  DISJ_CASES_TAC(SPECL [`k:num`; `k':num`] LE_CASES) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`st:(FFI)state`; `env:v sem_env`; `p:dec list`] o
    MATCH_MP evaluate_decs_ffi_mono_clock) THEN
  REWRITE_TAC[io_events_mono_def] THEN MESON_TAC[IS_PREFIX_LENGTH_ANTI]);;

let evaluate_prog_io_events_chain = prove
 (`lprefix_chain
     (IMAGE (\k. llist_fromList
                   (ffi_state_io_events
                      (FST (evaluate_prog_with_clock (st:(FFI)state) (env:v sem_env) k
                              (prog:dec list)))))
            UNIV)`,
  SUBGOAL_THEN
   `IMAGE (\k. llist_fromList
                 (ffi_state_io_events
                    (FST (evaluate_prog_with_clock (st:(FFI)state) (env:v sem_env) k
                            (prog:dec list)))))
          UNIV =
    IMAGE llist_fromList
      (IMAGE (\k. ffi_state_io_events (FST (evaluate_prog_with_clock st env k prog)))
             UNIV)`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; FORALL_IN_IMAGE_2; IN_UNIV;
              SEMPROPSAUX_evaluate_prog_with_clock] THEN
  MAP_EVERY X_GEN_TAC [`k1:num`; `k2:num`] THEN
  DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`st:(FFI)state`; `env:v sem_env`; `prog:dec list`] o
    MATCH_MP evaluate_decs_ffi_mono_clock) THEN
  SIMP_TAC[io_events_mono_def]);;

let semantics_prog_total = prove
 (`!(s:(FFI)state) (e:v sem_env) (p:dec list). ?b. semantics_prog s e p b`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `?k. SND (evaluate_prog_with_clock (s:(FFI)state) (e:v sem_env) k
                          (p:dec list)) = Rerr (Rabort Rtype_error)` THENL
   [EXISTS_TAC `Fail` THEN ASM_REWRITE_TAC[semantics_prog_def]; ALL_TAC] THEN
  ASM_CASES_TAC
   `?k ffi r. evaluate_prog_with_clock (s:(FFI)state) (e:v sem_env) k (p:dec list) =
              (ffi,r) /\
              ~(r = Rerr (Rabort Rtype_error)) /\ ~(r = Rerr (Rabort Rtimeout_error))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ffi:(FFI)ffi_state`
      (X_CHOOSE_THEN `r:(v sem_env,v)result` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC (CASE_TERM
     `Terminate (match r:(v sem_env,v)result with
                   Rerr (Rabort (Rffi_error outcome)) -> FFI_outcome outcome
                 | _ -> Success)
                (ffi_state_io_events (ffi:(FFI)ffi_state))`) THEN
    REWRITE_TAC[semantics_prog_def] THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `ffi:(FFI)ffi_state`; `r:(v sem_env,v)result`] THEN
    ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `Diverge (build_lprefix_lub
              (IMAGE (\k. llist_fromList
                            (ffi_state_io_events
                               (FST (evaluate_prog_with_clock (s:(FFI)state)
                                       (e:v sem_env) k (p:dec list)))))
                     UNIV))` THEN
  REWRITE_TAC[semantics_prog_def] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPEC `evaluate_prog_with_clock (s:(FFI)state) (e:v sem_env) k (p:dec list)`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ffi:(FFI)ffi_state`
      (X_CHOOSE_THEN `r:(v sem_env,v)result` ASSUME_TAC)) THEN
    EXISTS_TAC `ffi:(FFI)ffi_state` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    ASM_MESON_TAC[SND];
    MATCH_MP_TAC build_lprefix_lub_thm THEN
    REWRITE_TAC[evaluate_prog_io_events_chain]]);;

(* HOL4 [local] *)
let semanticsProps_with_clock_ffi = prove
 (`state_ffi (state_clock_fupd (combin_K x) (s:(FFI)state)) = state_ffi s`,
  REWRITE_TAC[state_INFO.ri_accfupds]);;

(* the parts of semantics_prog_deterministic (HOL4's tac1 and tac2)        *)

let SEMPROPSAUX_prog_clock_determ = prove
 (`!(st:(FFI)state) env (p:dec list) k1 k2 ffi1 r1 ffi2 r2.
     evaluate_prog_with_clock st env k1 p = (ffi1,r1) /\
     evaluate_prog_with_clock st env k2 p = (ffi2,r2) /\
     ~(r1 = Rerr (Rabort Rtimeout_error)) /\ ~(r2 = Rerr (Rabort Rtimeout_error))
     ==> ffi1 = ffi2 /\ r1 = r2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_prog_with_clock_def] THEN
  MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (combin_K k1) (st:(FFI)state)) env p`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state`
    (X_CHOOSE_THEN `q1:(v sem_env,v)result` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `evaluate_decs (state_clock_fupd (combin_K k2) (st:(FFI)state)) env p`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state`
    (X_CHOOSE_THEN `q2:(v sem_env,v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && is_var(rhs(concl th))))) THEN
  MP_TAC(SPECL [`st:(FFI)state`; `env:v sem_env`; `p:dec list`; `s1:(FFI)state`;
                `q1:(v sem_env,v)result`; `s2:(FFI)state`; `q2:(v sem_env,v)result`;
                `k1:num`; `k2:num`] evaluate_decs_clock_determ) THEN
  ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC);;

let SEMPROPSAUX_Terminate_thm = prove
 (CASE_TERM `!(st:(FFI)state) env prog outcome io_list.
     semantics_prog st env prog (Terminate outcome io_list) ==>
     ?k ffi r. evaluate_prog_with_clock st env k prog = (ffi,r) /\
               ~(r = Rerr (Rabort Rtimeout_error)) /\
               ~(r = Rerr (Rabort Rtype_error)) /\
               io_list = ffi_state_io_events ffi /\
               outcome = (match r with
                            Rerr (Rabort (Rffi_error outcome')) -> FFI_outcome outcome'
                          | _ -> Success)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[semantics_prog_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ffi:(FFI)ffi_state`
    (X_CHOOSE_THEN `r:(v sem_env,v)result` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `ffi:(FFI)ffi_state`; `r:(v sem_env,v)result`] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  EVERY_CASE_TAC THEN MESON_TAC[]);;

let SEMPROPSAUX_Fail_determ = prove
 (`!(st:(FFI)state) env prog b.
     semantics_prog st env prog Fail /\ semantics_prog st env prog b ==> b = Fail`,
  REPEAT GEN_TAC THEN CASES_ON `b:behaviour` THEN REWRITE_TAC[] THENL
   [REWRITE_TAC[semantics_prog_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `k:num`)
      (MP_TAC o SPEC `k:num` o CONJUNCT1)) THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `SND:(FFI)ffi_state#(v sem_env,v)result
                                                     ->(v sem_env,v)result`) THEN
    ASM_REWRITE_TAC[SND; injectivity "result"; injectivity "error_result";
                    distinctness "abort"];
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o MATCH_MP SEMPROPSAUX_Terminate_thm)) THEN
    REWRITE_TAC[semantics_prog_def] THEN STRIP_TAC THEN
    DISCH_THEN(X_CHOOSE_TAC `k':num`) THEN
    MP_TAC(ISPEC `evaluate_prog_with_clock (st:(FFI)state) env k' prog`
      PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ffi':(FFI)ffi_state`
      (X_CHOOSE_THEN `r':(v sem_env,v)result` ASSUME_TAC)) THEN
    MP_TAC(SPECL [`st:(FFI)state`; `env:v sem_env`; `prog:dec list`; `k:num`; `k':num`;
                  `ffi:(FFI)ffi_state`; `r:(v sem_env,v)result`;
                  `ffi':(FFI)ffi_state`; `r':(v sem_env,v)result`]
                 SEMPROPSAUX_prog_clock_determ) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl) o
      check (free_in `SND:(FFI)ffi_state#(v sem_env,v)result->(v sem_env,v)result` o concl)) THEN
    ASM_REWRITE_TAC[SND] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result";
                    distinctness "abort"]]);;

let SEMPROPSAUX_Diverge_determ = prove
 (`!(st:(FFI)state) env prog l b.
     semantics_prog st env prog (Diverge l) /\ semantics_prog st env prog b
     ==> b = Diverge l`,
  REPEAT GEN_TAC THEN CASES_ON `b:behaviour` THENL
   [REWRITE_TAC[semantics_prog_def; injectivity "behaviour"] THEN
    MESON_TAC[unique_lprefix_lub];
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o MATCH_MP SEMPROPSAUX_Terminate_thm)) THEN
    REWRITE_TAC[semantics_prog_def] THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    REWRITE_TAC[semantics_prog_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1) (X_CHOOSE_TAC `k:num`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `ffi:(FFI)ffi_state` o SPEC `k:num`) THEN
    UNDISCH_TAC `SND (evaluate_prog_with_clock (st:(FFI)state) env k prog) =
                 Rerr (Rabort Rtype_error)` THEN
    ASM_REWRITE_TAC[SND; injectivity "result"; injectivity "error_result";
                    distinctness "abort"]]);;

let SEMPROPSAUX_Terminate_determ = prove
 (`!(st:(FFI)state) env prog o1 l1 o2 l2.
     semantics_prog st env prog (Terminate o1 l1) /\
     semantics_prog st env prog (Terminate o2 l2)
     ==> o1 = o2 /\ l1 = l2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP SEMPROPSAUX_Terminate_thm)) THEN
  MP_TAC(SPECL [`st:(FFI)state`; `env:v sem_env`; `prog:dec list`; `k:num`; `k':num`;
                `ffi:(FFI)ffi_state`; `r:(v sem_env,v)result`;
                `ffi':(FFI)ffi_state`; `r':(v sem_env,v)result`]
               SEMPROPSAUX_prog_clock_determ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let semantics_prog_deterministic = prove
 (`!(s:(FFI)state) e p b b'.
     semantics_prog s e p b /\ semantics_prog s e p b' ==> b = b'`,
  REPEAT GEN_TAC THEN CASES_ON `b:behaviour` THEN CASES_ON `b':behaviour` THEN
  ASM_MESON_TAC[SEMPROPSAUX_Fail_determ; SEMPROPSAUX_Diverge_determ;
                SEMPROPSAUX_Terminate_determ]);;

let semantics_prog_Terminate_not_Fail = prove
 (`semantics_prog (s:(FFI)state) e p (Terminate x y) ==>
   ~semantics_prog s e p Fail /\ semantics_prog s e p = {Terminate x y}`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[semantics_prog_deterministic; distinctness "behaviour"];
    REWRITE_TAC[EXTENSION; IN_SING] THEN REWRITE_TAC[IN] THEN
    ASM_MESON_TAC[semantics_prog_deterministic]]);;

let semantics_prog_Diverge_not_Fail = prove
 (`semantics_prog (s:(FFI)state) e p (Diverge y) ==>
   ~semantics_prog s e p Fail /\ semantics_prog s e p = {Diverge y}`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[semantics_prog_deterministic; distinctness "behaviour"];
    REWRITE_TAC[EXTENSION; IN_SING] THEN REWRITE_TAC[IN] THEN
    ASM_MESON_TAC[semantics_prog_deterministic]]);;

let state_invariant_def = cake_def
  `state_invariant (st:(FFI)semantics_state) <=>
     ?ctMap tenvS.
       FRANGE ((SND o SND) o_f ctMap) SUBSET semantics_state_type_ids st /\
       type_sound_invariant (semantics_state_sem_st st) (semantics_state_sem_env st)
         ctMap tenvS {} (semantics_state_tenv st)`;;

(* HOL4 [local] *)
let clock_lemmas = prove
 (`state_clock (state_clock_fupd (combin_K c) (x:(FFI)state)) = c /\
   state_clock_fupd (combin_K d) (state_clock_fupd (combin_K c) x) = state_clock_fupd (combin_K d) x /\
   state_clock_fupd (combin_K (state_clock x)) x = x`,
  REWRITE_TAC[state_INFO.ri_accfupds; state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

let semantics_deterministic = prove
 (`state_invariant (st:(FFI)semantics_state) ==>
   semantics st prelude inp = Execute bs
   ==> ?b. bs = {b} /\ ~(b = Fail)`,
  REWRITE_TAC[state_invariant_def; semantics_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `ctMap:ctMap`
    (X_CHOOSE_THEN `tenvS:tenv_store` STRIP_ASSUME_TAC)) THEN
  EVERY_CASE_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `new_tids:type_ident->bool`
    (X_CHOOSE_THEN `new_tenv:type_env` STRIP_ASSUME_TAC) o
    REWRITE_RULE[can_type_prog_def]) THEN
  X_CHOOSE_TAC `b:behaviour`
    (SPECL [`semantics_state_sem_st (st:(FFI)semantics_state)`;
            `semantics_state_sem_env (st:(FFI)semantics_state)`;
            `APPEND prelude (a:dec list)`] semantics_prog_total) THEN
  EXISTS_TAC `b:behaviour` THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SING] THEN REWRITE_TAC[IN] THEN
    ASM_MESON_TAC[semantics_prog_deterministic];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`semantics_state_sem_st (st:(FFI)semantics_state)`;
                 `semantics_state_sem_env (st:(FFI)semantics_state)`;
                 `APPEND prelude (a:dec list)`; `b:behaviour`; `T`; `ctMap:ctMap`;
                 `tenvS:tenv_store`; `semantics_state_tenv (st:(FFI)semantics_state)`;
                 `new_tenv:type_env`; `new_tids:type_ident->bool`]
                semantics_type_sound) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `type_sound_invariant (semantics_state_sem_st (st:(FFI)semantics_state))
                 (semantics_state_sem_env st) ctMap tenvS {} (semantics_state_tenv st)` THEN
  REWRITE_TAC[type_sound_invariant_def; consistent_ctMap_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`FRANGE ((SND o SND) o_f (ctMap:ctMap)) SUBSET
     semantics_state_type_ids (st:(FFI)semantics_state)`;
    `DISJOINT (semantics_state_type_ids (st:(FFI)semantics_state)) new_tids`] THEN
  SET_TAC[]);;

let extend_with_resource_limit_def = cake_def
  `extend_with_resource_limit (behaviours:behaviour->bool) =
     (behaviours UNION
      {Terminate Resource_limit_hit io_list | io_list |
         ?t l. Terminate t l IN behaviours /\ io_list <<= l}) UNION
     {Terminate Resource_limit_hit io_list | io_list |
        ?ll. Diverge ll IN behaviours /\ LPREFIX (llist_fromList io_list) ll}`;;

let extend_with_resource_limit'_def = cake_def
  `extend_with_resource_limit' precise (behaviours:behaviour->bool) =
     if precise then behaviours else extend_with_resource_limit behaviours`;;

let implements_def = cake_def
  `implements (x:behaviour->bool) y <=>
     (~(Fail IN y) ==> x SUBSET extend_with_resource_limit y)`;;

let implements'_def = cake_def
  `implements' precise (x:behaviour->bool) y <=>
     ~(Fail IN y) ==> x SUBSET extend_with_resource_limit' precise y`;;

let extend_with_resource_limit_not_fail = prove
 (`x IN extend_with_resource_limit y /\ ~(Fail IN y) ==> ~(x = Fail)`,
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[distinctness "behaviour"]);;

let implements_intro = prove
 (`(b /\ ~(x = Fail) ==> y = x) ==> b ==> implements {y} {x}`,
  REWRITE_TAC[implements_def; extend_with_resource_limit_def; SING_SUBSET;
              IN_UNION; IN_SING] THEN
  MESON_TAC[]);;

let implements_trivial_intro = prove
 (`(y = x) ==> implements {y} {x}`,
  REWRITE_TAC[implements_def; extend_with_resource_limit_def; SING_SUBSET;
              IN_UNION; IN_SING] THEN
  MESON_TAC[]);;

let implements_intro_ext = prove
 (`(b /\ ~(x = Fail) ==> y IN extend_with_resource_limit {x}) ==>
   b ==> implements {y} {x}`,
  REWRITE_TAC[implements_def; SING_SUBSET; IN_SING] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let isPREFIX_IMP_LPREFIX = prove
 (`!xs ys:A list. isPREFIX xs ys ==> LPREFIX (llist_fromList xs) (llist_fromList ys)`,
  REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE]);;

(* HOL4 proves implements_trans in one step; here the extension is shown   *)
(* to be monotone and idempotent first                                     *)

let SEMPROPSAUX_extend_mono = prove
 (`!x y. x SUBSET y ==> extend_with_resource_limit x SUBSET extend_with_resource_limit y`,
  REWRITE_TAC[extend_with_resource_limit_def; SUBSET; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let SEMPROPSAUX_extend_extend = prove
 (`!z. extend_with_resource_limit (extend_with_resource_limit z) SUBSET
       extend_with_resource_limit z`,
  GEN_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:behaviour` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [extend_with_resource_limit_def] THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[extend_with_resource_limit_def; IN_UNION; IN_ELIM_THM;
              injectivity "behaviour"; distinctness "behaviour"] THEN
  MESON_TAC[IS_PREFIX_TRANS; isPREFIX_IMP_LPREFIX; GEN_ALL LPREFIX_TRANS]);;

let implements_trans = prove
 (`implements y z ==> implements x y ==> implements x z`,
  REWRITE_TAC[implements_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(Fail IN y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; extend_with_resource_limit_not_fail]; ALL_TAC] THEN
  ASM_MESON_TAC[SUBSET_TRANS; SEMPROPSAUX_extend_mono; SEMPROPSAUX_extend_extend]);;

let implements'_F = prove
 (`implements' F = implements`,
  REWRITE_TAC[FUN_EQ_THM; implements'_def; extend_with_resource_limit'_def;
              implements_def]);;

let implements'_trans = prove
 (`!x y z b. implements' b y z /\ implements' b x y ==> implements' b x z`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[implements'_F] THENL
   [REWRITE_TAC[implements'_def; extend_with_resource_limit'_def; SUBSET] THEN
    MESON_TAC[];
    MESON_TAC[implements_trans]]);;

let implements'_strengthen = prove
 (`!b b' x y. (b' ==> b) /\ implements' b x y ==> implements' b' x y`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN BOOL_CASES_TAC `b':bool` THEN
  REWRITE_TAC[implements'_def; extend_with_resource_limit'_def] THEN
  REWRITE_TAC[extend_with_resource_limit_def; SUBSET; IN_UNION] THEN MESON_TAC[]);;

let implements'_IMP_implements = prove
 (`implements' b x y ==> implements x y`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[implements'_F] THEN
  REWRITE_TAC[implements'_def; implements_def; extend_with_resource_limit'_def;
              extend_with_resource_limit_def; SUBSET; IN_UNION] THEN
  MESON_TAC[]);;

let extend_with_resource_limit'_SUBSET = prove
 (`extend_with_resource_limit' b s SUBSET extend_with_resource_limit s`,
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[extend_with_resource_limit'_def; SUBSET_REFL] THEN
  REWRITE_TAC[extend_with_resource_limit_def; SUBSET; IN_UNION] THEN MESON_TAC[]);;
