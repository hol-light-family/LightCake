(* ========================================================================= *)
(* bvl_inlineProof: port of HOL4 compiler/backend/proofs/                    *)
(* bvl_inlineProofScript.sml (CakeML v3479).  Correctness proof for          *)
(* bvl_inline.  BVLPROPSAUX_ names are local helpers (not HOL4 names).       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;

type_invention_error := true;;

(* removal of ticks *)

let bvl_inlineProof_state_rel_def = cake_def
  `bvl_inlineProof_state_rel (s:(C,FFI)bvl_state) (t:(C,FFI)bvl_state) <=>
     t = bvl_state_code_fupd
           (K (map (I ## (\x. HD (bvl_inline_remove_ticks [x]))) (bvl_state_code s)))
           (bvl_state_compile_fupd (K (bvl_state_compile t))
              (bvl_state_compile_oracle_fupd
                 (K ((I ## MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x])))) o
                     bvl_state_compile_oracle s)) s)) /\
     bvl_state_compile s =
       (\cfg prog. bvl_state_compile t cfg
                     (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))) prog))`;;

(* HOL4 rebinds state_rel_def to the definition simplified with the record *)
(* equality; here it is the local helper BVLPROPSAUX_state_rel_eq          *)
let BVLPROPSAUX_state_rel_eq = prove
 (`!(s:(C,FFI)bvl_state) t.
     bvl_inlineProof_state_rel s t <=>
     bvl_state_globals t = bvl_state_globals s /\
     bvl_state_refs t = bvl_state_refs s /\
     bvl_state_clock t = bvl_state_clock s /\
     bvl_state_compile_oracle t =
       (I ## MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x])))) o
       bvl_state_compile_oracle s /\
     bvl_state_code t = map (I ## (\x. HD (bvl_inline_remove_ticks [x]))) (bvl_state_code s) /\
     bvl_state_ffi t = bvl_state_ffi s /\
     bvl_state_compile s =
       (\cfg prog. bvl_state_compile t cfg
                     (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))) prog))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_inlineProof_state_rel_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [bvl_state_component_equality] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN CONV_TAC TAUT);;

(* local helpers: the clock of a state as inc_clock, and the induction on *)
(* the clock and then the size of the expression list                      *)
let BVLPROPSAUX_clock_fupd_inc = prove
 (`!(t:(C,FFI)bvl_state) ck.
     bvl_state_clock_fupd (K (bvl_state_clock t + ck)) t = bvl_inc_clock ck t`,
  REWRITE_TAC[bvl_inc_clock_def]);;

let BVLPROPSAUX_clock_size_ind = prove
 (`!P. (!xs (s:(C,FFI)bvl_state).
          (!xs' (s':(C,FFI)bvl_state).
             bvl_state_clock s' < bvl_state_clock s \/
             (bvl_state_clock s' = bvl_state_clock s /\
              list_size bvl_exp_size xs' < list_size bvl_exp_size xs) ==> P xs' s')
          ==> P xs s)
       ==> !xs s. P xs s`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\(r1:num,s1:num) (r2,s2). r1 < r2 \/ r1 = r2 /\ s1 < s2`;
                 `\p:bvl_exp list # (C,FFI)bvl_state.
                     (bvl_state_clock (SND p),list_size bvl_exp_size (FST p))`]
                WF_MEASURE_GEN) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`(<):num->num->bool`; `(<):num->num->bool`] WF_LEX) THEN
    REWRITE_TAC[WF_num];
    ALL_TAC] THEN
  REWRITE_TAC[WF_IND] THEN
  DISCH_THEN(MP_TAC o SPEC `\p:bvl_exp list # (C,FFI)bvl_state. P (FST p) (SND p):bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[]);;

(* local helpers for the two do_app_lemma: the first components of a mapped *)
(* list, a paired lambda as a pair map, and do_app on states that differ    *)
(* only in the code, the compiler and the oracle, by a map f of the code    *)
(* (state_rel for the removal of ticks, let_state_rel for let_op)           *)
let BVLPROPSAUX_MAP_FST_PAIR_MAP = prove
 (`!(f:B->C) (l:(A#B)list). MAP FST (MAP (I ## f) l) = MAP FST l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; PAIR_MAP; FST; I_THM]);;

let BVLPROPSAUX_PAIR_LAMBDA_MAP = prove
 (`!(g:B->C). (\(k:A,v). k,g v) = (I ## g)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let BVLPROPSAUX_do_app_map = prove
 (CASE_TERM `!(f:num#bvl_exp->num#bvl_exp) op a (s:(C,FFI)bvl_state) t.
     bvl_state_globals t = bvl_state_globals s /\ bvl_state_refs t = bvl_state_refs s /\
     bvl_state_clock t = bvl_state_clock s /\
     bvl_state_compile_oracle t = (I ## MAP (I ## f)) o bvl_state_compile_oracle s /\
     bvl_state_code t = map f (bvl_state_code s) /\ bvl_state_ffi t = bvl_state_ffi s /\
     bvl_state_compile s = (\cfg prog. bvl_state_compile t cfg (MAP (I ## f) prog)) ==>
     match bvl_do_app op a s with
       Rerr e -> bvl_do_app op a t = Rerr e
     | Rval (v,s2) -> ?t2.
         (bvl_state_globals t2 = bvl_state_globals s2 /\ bvl_state_refs t2 = bvl_state_refs s2 /\
          bvl_state_clock t2 = bvl_state_clock s2 /\
          bvl_state_compile_oracle t2 = (I ## MAP (I ## f)) o bvl_state_compile_oracle s2 /\
          bvl_state_code t2 = map f (bvl_state_code s2) /\ bvl_state_ffi t2 = bvl_state_ffi s2 /\
          bvl_state_compile s2 = (\cfg prog. bvl_state_compile t2 cfg (MAP (I ## f) prog))) /\
         bvl_do_app op a t = Rval (v,t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [ASM_REWRITE_TAC[BVLPROPSAUX_do_app_Install; bvl_do_install_def] THEN
    QCASES_ON "bvl_state_compile_oracle s 0" THEN
    FS[shift_seq_def; domain_map; BVLPROPSAUX_MAP_FST_PAIR_MAP] THEN
    REPEAT (TOP_CASE_TAC THEN GVS[MAP_EQ_CONS; list_MAP_EQ_NIL]) THEN
    RW[FUN_EQ_THM; o_THM; map_union; map_insert; map_fromAList; BVLPROPSAUX_PAIR_LAMBDA_MAP];
    SUBGOAL_THEN `t = bvl_state_code_fupd (K (bvl_state_code t))
                   (bvl_state_compile_fupd (K (bvl_state_compile t))
                     (bvl_state_compile_oracle_fupd (K (bvl_state_compile_oracle t))
                       (s:(C,FFI)bvl_state)))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[bvl_state_component_equality; bvl_state_INFO.ri_accfupds; K_THM];
      TOP_CASE_TAC THEN TRY TOP_CASE_TAC] THENL
     [IMP_RES_TAC bvl_do_app_with_code THEN IMP_RES_TAC bvl_do_app_const THEN
      RFS[domain_map; SUBSET_REFL; bvl_state_INFO.ri_accfupds; K_THM];
      IMP_RES_TAC do_app_with_code_err_not_Install THEN RFS[domain_map; SUBSET_REFL]]]);;

(* HOL4 [local]; HOL4 binds do_app_lemma twice: this first one is for the  *)
(* removal of ticks (the second, for let_op, is bvl_inlineProof_do_app_lemma) *)
let BVLPROPSAUX_rt_do_app_lemma = prove
 (CASE_TERM `!op a (t':(C,FFI)bvl_state) r.
    bvl_inlineProof_state_rel t' r ==>
    match bvl_do_app op (REVERSE a) r with
      Rerr err -> bvl_do_app op (REVERSE a) t' = Rerr err
    | Rval (v,r2) -> ?t2. bvl_inlineProof_state_rel t2 r2 /\
                          bvl_do_app op (REVERSE a) t' = Rval (v,t2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_state_rel_eq] THEN
  DISCH_THEN (MP_TAC o SPECL [`op:clos_op`; `REVERSE a:bvl_v list`] o MATCH_MP
    (ISPEC `(I:num->num) ## (\x. HD (bvl_inline_remove_ticks [x]))` BVLPROPSAUX_do_app_map)) THEN
  REPEAT TOP_CASE_TAC THEN RW[] THEN FS[]);;

(* local helpers for evaluate_remove_ticks: find_code in a mapped code     *)
(* table, the clock, refs and code of related states, and the induction    *)
let BVLPROPSAUX_find_code_map = prove
 (`!dest args code (f:bvl_exp->bvl_exp).
     bvl_find_code dest args (map (I ## f) code) =
     OPTION_MAP (I ## f) (bvl_find_code dest args code)`,
  GEN_TAC THEN CASES_ON `dest:num option` THEN
  RW[bvl_find_code_def; lookup_map] THEN REPEAT (TOP_CASE_TAC THEN FS[]));;

let BVLPROPSAUX_dec_clock_clock = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_clock (bvl_dec_clock n s) = bvl_state_clock s - n`,
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM]);;

let BVLPROPSAUX_state_rel_clock = prove
 (`!(t:(C,FFI)bvl_state) s. bvl_inlineProof_state_rel t s ==>
     bvl_state_clock t = bvl_state_clock s /\ bvl_state_refs t = bvl_state_refs s /\
     bvl_inlineProof_state_rel (bvl_dec_clock 1 t) (bvl_dec_clock 1 s) /\
     bvl_inlineProof_state_rel (bvl_state_clock_fupd (K 0) t) (bvl_state_clock_fupd (K 0) s)`,
  SIMP_TAC[BVLPROPSAUX_state_rel_eq; bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM]);;

let BVLPROPSAUX_dec_inc_1 = prove
 (`!k (t:(C,FFI)bvl_state). bvl_dec_clock 1 (bvl_inc_clock (k + 1) t) = bvl_inc_clock k t`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[bvl_dec_clock_1_inc_clock; ARITH_RULE `~(k + 1 = 0)`; ADD_SUB]);;

let BVLPROPSAUX_dec_inc_ticks = prove
 (`!ticks c (t:(C,FFI)bvl_state).
     ~(bvl_state_clock t = 0) ==>
     bvl_dec_clock (ticks + 1) (bvl_inc_clock (ticks + c) t) =
     bvl_inc_clock c (bvl_dec_clock 1 t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_dec_clock_def; bvl_inc_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
              bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let BVLPROPSAUX_find_code_rel = prove
 (`(!(t:(C,FFI)bvl_state) s d vs args e'.
      bvl_find_code d vs (bvl_state_code s) = SOME (args,e') /\
      bvl_inlineProof_state_rel t s ==>
      ?e. bvl_find_code d vs (bvl_state_code t) = SOME (args,e) /\
          e' = HD (bvl_inline_remove_ticks [e])) /\
   (!(t:(C,FFI)bvl_state) s d vs.
      bvl_find_code d vs (bvl_state_code s) = NONE /\ bvl_inlineProof_state_rel t s ==>
      bvl_find_code d vs (bvl_state_code t) = NONE)`,
  RW[BVLPROPSAUX_state_rel_eq] THEN
  RFS[BVLPROPSAUX_find_code_map; OPTION_MAP_EQ_SOME; OPTION_MAP_EQ_NONE; EXISTS_PAIR_THM] THEN
  RFS[PAIR_MAP]);;

(* the induction for evaluate_remove_ticks (HOL4: completeInduct_on the    *)
(* clock, then recInduct remove_ticks_ind): the induction hypothesis for   *)
(* the runs of the compiled code with less clock, or the same clock and a  *)
(* smaller expression                                                       *)
let BVLPROPSAUX_rt_ind = prove
 (`!P. (!xs env (s:(C,FFI)bvl_state) res s' t.
          (!xs1 env1 s1 res1 s1' t1.
             bvl_evaluate (bvl_inline_remove_ticks xs1,env1,s1) = (res1,s1') /\
             bvl_inlineProof_state_rel t1 s1 /\
             (bvl_state_clock s1 <= bvl_state_clock s /\
              list_size bvl_exp_size xs1 < list_size bvl_exp_size xs \/
              bvl_state_clock s1 < bvl_state_clock s) ==> P xs1 env1 s1 res1 s1' t1) ==>
          bvl_evaluate (bvl_inline_remove_ticks xs,env,s) = (res,s') /\
          bvl_inlineProof_state_rel t s ==> P xs env s res s' t) ==>
       !xs env s res s' t.
         bvl_evaluate (bvl_inline_remove_ticks xs,env,s) = (res,s') /\
         bvl_inlineProof_state_rel t s ==> P xs env s res s' t`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!xs (s:(C,FFI)bvl_state) env res s' t.
                  bvl_evaluate (bvl_inline_remove_ticks xs,env,s) = (res,s') /\
                  bvl_inlineProof_state_rel t s ==> P xs env s res s' t`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC BVLPROPSAUX_clock_size_ind THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  LAST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* the simulation of a run of the compiled code by a run of the source with *)
(* more clock; each clause splits the compiled run alone, then uses the     *)
(* induction hypothesis (IMP_RES_TAC) and chains the extra clocks           *)
let BVLPROPSAUX_rt_sim = prove
 (`!xs env (s:(C,FFI)bvl_state) res s' t.
     bvl_evaluate (bvl_inline_remove_ticks xs,env,s) = (res,s') /\
     bvl_inlineProof_state_rel t s ==>
     ?ck t'. bvl_evaluate (xs,env,bvl_inc_clock ck t) = (res,t') /\
             bvl_inlineProof_state_rel t' s'`,
  let split thl = QPAT_X_ASSUM "bvl_evaluate _ = (res,s')" (CAKE_STRIP_ASSUME_TAC o
                    CAKE_SIMP_RULE (bvl_inline_remove_ticks_def :: thl @ all_case_eqs())) THEN
                  RVEQ_TAC in
  let sz = type_size_def "bvl_exp" :: list_size :: ARITH_ss :: BVLPROPSAUX_dec_clock_clock ::
           size_aux_eqs "bvl_exp" in
  let ih th = IMP_RES_TAC bvl_evaluate_clock THEN IMP_RES_TAC th THEN FS sz THEN
              RES_TAC THEN RFS[] in
  let case thl f = DISCH_THEN (fun th -> STRIP_TAC THEN split thl THEN f th) in
  let fin0 = QEXISTS_TAC "0" THEN RFS[bvl_evaluate_def] in
  let fin1 = QEXISTS_TAC "ck" THEN RFS[bvl_evaluate_def; ARITH_ss] in
  let fin2 = QEXISTS_TAC "ck' + ck" THEN IMP_RES_TAC bvl_evaluate_add_clock THEN
             RFS[bvl_evaluate_def; inc_clock_add] in
  let fin = FIRST [fin1 THEN NO_TAC; fin2] in
  let code = IMP_RES_TAC BVLPROPSAUX_state_rel_clock THEN
             IMP_RES_TAC BVLPROPSAUX_find_code_rel THEN RVEQ_TAC THEN RFS[] in
  MATCH_MP_TAC BVLPROPSAUX_rt_ind THEN REPEAT GEN_TAC THEN
  QCASES_ON "xs" THENL [ALL_TAC; QCASES_ON "a1" THENL [QCASES_ON "a0"; ALL_TAC]] THENL
   [(* Nil *) case [bvl_evaluate_def] (K fin0);
    (* Var *) case [bvl_evaluate_def] (K fin0);
    (* If *) case [bvl_evaluate_def] (fun th -> ih th THEN fin);
    (* Let *) case [bvl_evaluate_def] (fun th -> ih th THEN fin);
    (* Raise *) case [bvl_evaluate_def] (fun th -> ih th THEN fin);
    (* Handle *) case [bvl_evaluate_def] (fun th -> ih th THEN fin);
    (* Tick *)
    case [bvl_evaluate_def] (fun th -> ih th THEN QEXISTS_TAC "ck + 1" THEN
      RFS[bvl_evaluate_def; BVLPROPSAUX_dec_inc_1; ARITH_ss]);
    (* Call *)
    case [bvl_evaluate_def] (fun th -> ih th THEN code THEN FIRST [fin1 THEN NO_TAC;
      QPAT_ASSUM "bvl_evaluate (_,_,bvl_dec_clock 1 _) = _" (IMP_RES_TAC o MATCH_MP_CURRIED th) THEN
      FS sz THEN RES_TAC THEN RFS[] THEN QEXISTS_TAC "(a0' + ck') + ck" THEN
      IMP_RES_TAC bvl_evaluate_add_clock THEN
      RFS[bvl_evaluate_def; inc_clock_add; BVLPROPSAUX_dec_inc_ticks; ARITH_ss]]);
    (* Force *)
    case [bvl_evaluate_def] (fun th -> code THEN ih th THEN FIRST [fin0 THEN NO_TAC;
      QEXISTS_TAC "ck" THEN RFS[bvl_evaluate_def; bvl_dec_clock_1_inc_clock2]]);
    (* Op *)
    case [bvl_evaluate_def] (fun th -> ih th THEN FIRST [fin1 THEN NO_TAC;
      RENAME1 "bvl_do_app op (REVERSE vs) _ = _" THEN fin1 THEN
      DRULE BVLPROPSAUX_rt_do_app_lemma THEN DISCH_THEN(QSPECL_THEN ["op"; "vs"] MP_TAC) THEN
      RFS[] THEN RW[] THEN RFS[]]);
    (* Cons *) case [ONCE bvl_evaluate_CONS] (fun th -> ih th THEN fin)]);;

let bvl_inlineProof_evaluate_remove_ticks = prove
 (`!k xs env (s:(C,FFI)bvl_state) t res s'.
     bvl_inlineProof_state_rel t s /\ bvl_state_clock s = k /\
     bvl_evaluate (bvl_inline_remove_ticks xs,env,s) = (res,s') ==>
     ?ck t'. bvl_evaluate (xs,env,bvl_state_clock_fupd (K (bvl_state_clock t + ck)) t) =
             (res,t') /\
             bvl_inlineProof_state_rel t' s'`,
  REWRITE_TAC[BVLPROPSAUX_clock_fupd_inc] THEN MESON_TAC[BVLPROPSAUX_rt_sim]);;

let bvl_inlineProof_remove_ticks_cc_def = cake_def
  `bvl_inlineProof_remove_ticks_cc (cc:C->(num#num#bvl_exp)list->D) =
     (\cfg prog'. cc cfg (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))) prog'))`;;

let bvl_inlineProof_remove_ticks_co_def = cake_def
  `bvl_inlineProof_remove_ticks_co =
     ((I:C->C) ## MAP ((I:num->num) ## (I:num->num) ##
                       (\x. HD (bvl_inline_remove_ticks [x]))))`;;

(* a local helper: extra clock for an initial state *)
let BVLPROPSAUX_inc_initial_state = prove
 (`!ck (ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvl_exp) list) cc k.
     bvl_inc_clock ck (bvl_initial_state ffi code co cc k) =
     bvl_initial_state ffi code co cc (k + ck)`,
  REWRITE_TAC[bvl_inc_clock_def; bvl_initial_state_def; bvl_state_INFO.ri_accessors;
              bvl_state_INFO.ri_fupds; K_THM]);;

let bvl_inlineProof_evaluate_compile_prog = prove
 (`!start ffi0 prog (co:num -> C # (num#num#bvl_exp) list) cc k r (s:(C,FFI)bvl_state).
     bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
        bvl_initial_state ffi0 (map (I ## (\x. HD (bvl_inline_remove_ticks [x]))) prog)
          (bvl_inlineProof_remove_ticks_co o co) cc k) = (r,s) ==>
     ?ck (s2:(C,FFI)bvl_state).
       bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
          bvl_initial_state ffi0 prog co (bvl_inlineProof_remove_ticks_cc cc) (k + ck)) =
       (r,s2) /\
       bvl_state_ffi s2 = bvl_state_ffi s`,
  REPEAT STRIP_TAC THEN
  DRULE (REWRITE_RULE[bvl_inline_remove_ticks_def]
          (ISPEC `[bvl_Call 0 (SOME start) []]` BVLPROPSAUX_rt_sim)) THEN
  DISCH_THEN (QSPEC_THEN "bvl_initial_state ffi0 prog co (bvl_inlineProof_remove_ticks_cc cc) k"
    MP_TAC) THEN
  RW[BVLPROPSAUX_state_rel_eq; bvl_initial_state_def; bvl_inlineProof_remove_ticks_co_def;
     bvl_inlineProof_remove_ticks_cc_def; GSYM BVLPROPSAUX_inc_initial_state] THEN
  ASM_EXISTS_TAC THEN FS[]);;

(* local helpers for the semantics theorems: the runs of a program from    *)
(* its initial state with more clock, and the generic simulation lemma     *)
(* (HOL4 repeats the semantics argument for each of the three passes)      *)
let BVLPROPSAUX_bvl_init_mono = prove
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

let BVLPROPSAUX_bvl_init_io_mono = prove
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
  REWRITE_TAC[BVLPROPSAUX_inc_initial_state]);;

let BVLPROPSAUX_bvl_init_io_chain = prove
 (`!es env (ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvl_exp) list) cc.
     lprefix_chain
       (IMAGE (\k. llist_fromList (ffi_state_io_events (bvl_state_ffi
          (SND (bvl_evaluate (es,env,bvl_initial_state ffi p co cc k)))))) (:num))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `IMAGE (\k. (g:B->C) ((f:A->B) k)) s = IMAGE g (IMAGE f s)`] THEN
  MATCH_MP_TAC prefix_chain_lprefix_chain THEN
  REWRITE_TAC[prefix_chain_def; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  MESON_TAC[BVLPROPSAUX_bvl_init_io_mono; LE_CASES]);;

let BVLPROPSAUX_option_CASE_cong = prove
 (`!(a:B option) b (n1:D) n2 f.
     a = b /\ (b = NONE ==> n1 = n2) ==> option_CASE a n1 f = option_CASE b n2 f`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `b:B option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN MESON_TAC[option_CASE]);;

(* the type of the compiler configuration is taken from the oracle *)
let BVLPROPSAUX_bvl_ev (p:term) (oo:term) (c:term) (k:term) =
  let cty = hd (snd (dest_type (hd (tl (snd (dest_type (type_of oo))))))) in
  let ins = inst [cty,`:C`] in
  vsubst [p,`p:(num#bvl_exp)spt`; oo,ins `co:num -> C # (num#num#bvl_exp) list`;
          c,ins `cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option`;
          k,`k:num`]
   (ins `bvl_evaluate ([bvl_Call 0 (SOME start) []],[]:bvl_v list,
                  bvl_initial_state (ffi:(FFI)ffi_state) (p:(num#bvl_exp)spt)
                    (co:num -> C # (num#num#bvl_exp) list)
                    (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option)
                    (k:num))`);;

let BVLPROPSAUX_bvl_RUN_TAC (p:term) (oo:term) (c:term) (k:term) (r:term) (x:term) : tactic =
  MP_TAC(ISPEC (BVLPROPSAUX_bvl_ev p oo c k) PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [r; x] THEN DISCH_TAC;;

(* the instance of a labelled fact at k, simplified with the equations of *)
(* the runs among the assumptions (not ASM_REWRITE_TAC: the labelled fact  *)
(* itself would rewrite its instance to T)                                  *)
let BVLPROPSAUX_LAB_INST_TAC (lab:string) (k:term) : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c))
              (map snd asl) in
  USE_THEN lab (fun th -> MP_TAC (REWRITE_RULE (FST :: SND :: evs) (SPEC k th))) g;;

let BVLPROPSAUX_LAB_MP_TAC (lab:string) (tms:term list) : tactic = fun (asl,w as g) ->
  USE_THEN lab (fun th ->
    let th' = SPECL tms th in
    let ant = lhand (concl th') in
    let ath = EQT_ELIM (REWRITE_CONV (FST :: SND :: map snd asl) ant) in
    MP_TAC (MP th' ath)) g;;

(* the source configuration type D and the target one C may differ *)
let BVLPROPSAUX_bvl_semantics_sim = prove
 (`!(ffi:(FFI)ffi_state) p1 (o1:num -> D # (num#num#bvl_exp) list) c1 p2
     (o2:num -> C # (num#num#bvl_exp) list) c2 start.
     (!k r s. bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                            bvl_initial_state ffi p1 o1 c1 k) = (r,s) /\
              ~(r = Rerr (Rabort Rtype_error))
        ==> ?ck s2. bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                                  bvl_initial_state ffi p2 o2 c2 (k + ck)) = (r,s2) /\
                    bvl_state_ffi s2 = bvl_state_ffi s) /\
     ~(bvl_semantics ffi p1 o1 c1 start = Fail)
     ==> bvl_semantics ffi p2 o2 c2 start = bvl_semantics ffi p1 o1 c1 start`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim") ASSUME_TAC) THEN
  let pp1 = `p1:(num#bvl_exp)spt` and oo1 = `o1:num -> D # (num#num#bvl_exp) list`
  and cc1 = `c1:D->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#D)option`
  and pp2 = `p2:(num#bvl_exp)spt` and oo2 = `o2:num -> C # (num#num#bvl_exp) list`
  and cc2 = `c2:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option` in
  let e1 = BVLPROPSAUX_bvl_ev pp1 oo1 cc1 and e2 = BVLPROPSAUX_bvl_ev pp2 oo2 cc2 in
  let fst1 = `FST:(bvl_v list,bvl_v)result#(D,FFI)bvl_state->(bvl_v list,bvl_v)result` in
  let fst2 = `FST:(bvl_v list,bvl_v)result#(C,FFI)bvl_state->(bvl_v list,bvl_v)result` in
  let te = `Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result` in
  let tmo = `Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result` in
  let rv = `r:(bvl_v list,bvl_v)result` and r0 = `r0:(bvl_v list,bvl_v)result`
  and r2 = `r2:(bvl_v list,bvl_v)result` in
  let s1 = `s1:(D,FFI)bvl_state` and t1 = `t1:(C,FFI)bvl_state`
  and t2 = `t2:(C,FFI)bvl_state` in
  let mono pp oo cc k k' r x =
    MP_TAC(ISPECL [`[bvl_Call 0 (SOME start) []]`; `[]:bvl_v list`; `ffi:(FFI)ffi_state`;
                   pp; oo; cc; k; k'; r; x] BVLPROPSAUX_bvl_init_mono) in
  SUBGOAL_THEN (mk_forall(`k:num`, mk_neg(mk_eq(mk_comb(fst1, e1 `k:num`), te))))
    (LABEL_TAC "oks") THENL
   [UNDISCH_TAC `~(bvl_semantics (ffi:(FFI)ffi_state) (p1:(num#bvl_exp)spt)
                     (o1:num -> D # (num#num#bvl_exp) list) c1 start = Fail)` THEN
    REWRITE_TAC[bvl_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_forall(`k:num`, mk_imp(mk_eq(mk_comb(fst1, e1 `k:num`), tmo),
                                          mk_eq(mk_comb(fst2, e2 `k:num`), tmo))))
    (LABEL_TAC "tmo") THENL
   [GEN_TAC THEN BVLPROPSAUX_bvl_RUN_TAC pp1 oo1 cc1 `k:num` rv s1 THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; tmo; s1]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC BVLPROPSAUX_eval_simps; ALL_TAC] THEN
    STRIP_TAC THEN BVLPROPSAUX_bvl_RUN_TAC pp2 oo2 cc2 `k:num` r2 t2 THEN
    ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    mono pp2 oo2 cc2 `k:num` `k + ck:num` r2 t2 THEN
    ASM_REWRITE_TAC[LE_ADD; FST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_forall(`k:num`, mk_forall(rv, mk_forall(t1,
      mk_imp(mk_conj(mk_eq(e2 `k:num`, mk_pair(rv,t1)), mk_neg(mk_eq(rv, tmo))),
             mk_exists(s1, mk_conj(mk_eq(e1 `k:num`, mk_pair(rv,s1)),
               mk_eq(mk_comb(`bvl_state_ffi:(D,FFI)bvl_state->(FFI)ffi_state`, s1),
                     mk_comb(`bvl_state_ffi:(C,FFI)bvl_state->(FFI)ffi_state`, t1)))))))))
    (LABEL_TAC "back") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN BVLPROPSAUX_bvl_RUN_TAC pp1 oo1 cc1 `k:num` r0 s1 THEN
    SUBGOAL_THEN (mk_neg(mk_eq(r0, tmo))) ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN BVLPROPSAUX_LAB_INST_TAC "tmo" `k:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_neg(mk_eq(r0, te))) ASSUME_TAC THENL
     [BVLPROPSAUX_LAB_INST_TAC "oks" `k:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; r0; s1]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    mono pp2 oo2 cc2 `k:num` `k + ck:num` rv t1 THEN
    ASM_REWRITE_TAC[LE_ADD; FST; SND] THEN STRIP_TAC THEN
    EXISTS_TAC s1 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_forall(`k:num`, mk_neg(mk_eq(mk_comb(fst2, e2 `k:num`), te))))
    (LABEL_TAC "okt") THENL
   [GEN_TAC THEN BVLPROPSAUX_bvl_RUN_TAC pp2 oo2 cc2 `k:num` rv t1 THEN
    ASM_REWRITE_TAC[FST] THEN
    ASM_CASES_TAC (mk_eq(rv, tmo)) THEN ASM_REWRITE_TAC BVLPROPSAUX_eval_simps THEN
    BVLPROPSAUX_LAB_MP_TAC "back" [`k:num`; rv; t1] THEN
    DISCH_THEN(X_CHOOSE_THEN s1 STRIP_ASSUME_TAC) THEN
    BVLPROPSAUX_LAB_INST_TAC "oks" `k:num` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
    USE_THEN "okt" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
    USE_THEN "oks" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC BVLPROPSAUX_option_CASE_cong THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN (mk_neg(mk_eq(rv, tmo))) ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      BVLPROPSAUX_LAB_MP_TAC "back" [`k:num`; rv; `s:(C,FFI)bvl_state`] THEN
      DISCH_THEN(X_CHOOSE_THEN s1 STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`k:num`; s1; rv; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN (mk_neg(mk_eq(rv, te))) ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        BVLPROPSAUX_LAB_INST_TAC "oks" `k:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "sim" (MP_TAC o SPECL [`k:num`; rv; `s:(D,FFI)bvl_state`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`k + ck:num`; `s2:(C,FFI)bvl_state`; rv; `outcome:outcome`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REWRITE_TAC[BVLPROPSAUX_bvl_init_io_chain] THEN
    REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THEN
    BVLPROPSAUX_bvl_RUN_TAC pp1 oo1 cc1 `k:num` rv s1 THEN
    BVLPROPSAUX_LAB_INST_TAC "oks" `k:num` THEN DISCH_TAC THEN
    BVLPROPSAUX_LAB_MP_TAC "sim" [`k:num`; rv; s1] THEN STRIP_TAC THENL
     [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
      MP_TAC(ISPECL [`[bvl_Call 0 (SOME start) []]`; `[]:bvl_v list`; `ffi:(FFI)ffi_state`;
                     pp2; oo2; cc2; `k:num`; `k + ck:num`] BVLPROPSAUX_bvl_init_io_mono) THEN
      ASM_REWRITE_TAC[LE_ADD; SND];
      EXISTS_TAC `k + ck:num` THEN
      ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL; SND]]]);;

let BVLPROPSAUX_bvl_semantics_Fail = prove
 (`!(ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvl_exp) list) cc start.
     bvl_semantics ffi p co cc start = Fail <=>
     ?k. FST (bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                            bvl_initial_state ffi p co cc k)) = Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_semantics_def; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_CASE; distinctness "behaviour"] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "behaviour"]);;

let BVLPROPSAUX_bvl_semantics_sim_all = prove
 (`!(ffi:(FFI)ffi_state) p1 (o1:num -> C # (num#num#bvl_exp) list) c1 p2
     (o2:num -> C # (num#num#bvl_exp) list) c2 start.
     (!k r s. bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                            bvl_initial_state ffi p1 o1 c1 k) = (r,s)
        ==> ?ck s2. bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                                  bvl_initial_state ffi p2 o2 c2 (k + ck)) = (r,s2) /\
                    bvl_state_ffi s2 = bvl_state_ffi s)
     ==> bvl_semantics ffi p1 o1 c1 start = bvl_semantics ffi p2 o2 c2 start`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `bvl_semantics (ffi:(FFI)ffi_state) p1 (o1:num -> C # (num#num#bvl_exp) list)
                   c1 start = Fail` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BVLPROPSAUX_bvl_semantics_Fail]) THEN
    REWRITE_TAC[BVLPROPSAUX_bvl_semantics_Fail] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o check (is_exists o concl)) THEN
    QCASES_ON "bvl_evaluate ([bvl_Call 0 (SOME start) []],[],bvl_initial_state ffi p1 o1 c1 k)" THEN
    RES_TAC THEN QEXISTS_TAC "k + ck" THEN FS[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC BVLPROPSAUX_bvl_semantics_sim THEN
    ASM_SIMP_TAC[]]);;

let bvl_inlineProof_semantics_remove_ticks = prove
 (`!(ffi:(FFI)ffi_state) prog (co:num -> C # (num#num#bvl_exp) list) cc start.
     bvl_semantics ffi (map (I ## (\x. HD (bvl_inline_remove_ticks [x]))) prog)
       (bvl_inlineProof_remove_ticks_co o co) cc start =
     bvl_semantics ffi prog co (bvl_inlineProof_remove_ticks_cc cc) start`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC BVLPROPSAUX_bvl_semantics_sim_all THEN
  REWRITE_TAC[bvl_inlineProof_evaluate_compile_prog]);;

(* correctness of tick_inline *)

let bvl_inlineProof_exp_rel_rules,bvl_inlineProof_exp_rel_ind,
    bvl_inlineProof_exp_rel_cases,bvl_inlineProof_exp_rel_strongind =
  cake_inductive
  `(!(cs:(num#bvl_exp)spt) v. bvl_inlineProof_exp_rel cs [bvl_Var v] [bvl_Var v]) /\
   (!cs. bvl_inlineProof_exp_rel cs [] []) /\
   (!cs x x1 xs y y1 ys.
      bvl_inlineProof_exp_rel cs [x] [y] /\
      bvl_inlineProof_exp_rel cs (CONS x1 xs) (CONS y1 ys) ==>
      bvl_inlineProof_exp_rel cs (CONS x (CONS x1 xs)) (CONS y (CONS y1 ys))) /\
   (!cs x1 x2 x3 y1 y2 y3.
      bvl_inlineProof_exp_rel cs [x1] [y1] /\
      bvl_inlineProof_exp_rel cs [x2] [y2] /\
      bvl_inlineProof_exp_rel cs [x3] [y3] ==>
      bvl_inlineProof_exp_rel cs [bvl_If x1 x2 x3] [bvl_If y1 y2 y3]) /\
   (!cs xs ys x y.
      bvl_inlineProof_exp_rel cs xs ys /\
      bvl_inlineProof_exp_rel cs [x] [y] ==>
      bvl_inlineProof_exp_rel cs [bvl_Let xs x] [bvl_Let ys y]) /\
   (!cs x1 x2 y1 y2.
      bvl_inlineProof_exp_rel cs [x1] [y1] /\
      bvl_inlineProof_exp_rel cs [x2] [y2] ==>
      bvl_inlineProof_exp_rel cs [bvl_Handle x1 x2] [bvl_Handle y1 y2]) /\
   (!cs x y.
      bvl_inlineProof_exp_rel cs [x] [y] ==>
      bvl_inlineProof_exp_rel cs [bvl_Raise x] [bvl_Raise y]) /\
   (!cs x y.
      bvl_inlineProof_exp_rel cs [x] [y] ==>
      bvl_inlineProof_exp_rel cs [bvl_Tick x] [bvl_Tick y]) /\
   (!cs op xs ys.
      bvl_inlineProof_exp_rel cs xs ys ==>
      bvl_inlineProof_exp_rel cs [bvl_Op op xs] [bvl_Op op ys]) /\
   (!cs loc n. bvl_inlineProof_exp_rel cs [bvl_Force loc n] [bvl_Force loc n]) /\
   (!cs ticks dest xs ys.
      bvl_inlineProof_exp_rel cs xs ys ==>
      bvl_inlineProof_exp_rel cs [bvl_Call ticks dest xs] [bvl_Call ticks dest ys]) /\
   (!cs xs ys n arity x y ticks.
      bvl_inlineProof_exp_rel cs xs ys /\ lookup n cs = SOME (arity,x) /\
      bvl_inlineProof_exp_rel cs [x] [y] ==>
      bvl_inlineProof_exp_rel cs [bvl_Call ticks (SOME n) xs]
                                 [bvl_Let ys (mk_tick (SUC ticks) y)])`;;

let bvl_inlineProof_in_cc_def = cake_def
  (CASE_TERM `bvl_inlineProof_in_cc limit
                (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) =
     (\(cs,cfg) prog.
        let (cs1,prog1) = tick_compile_prog limit (cs:(num#bvl_exp)spt) prog in
          match cc cfg prog1 with
            NONE -> NONE
          | SOME (code,data,cfg1) -> SOME (code,data,(cs1,cfg1)))`);;

let bvl_inlineProof_in_state_rel_def = cake_def
  `bvl_inlineProof_in_state_rel limit (s:((num#bvl_exp)spt#C,FFI)bvl_state)
                                (t:(C,FFI)bvl_state) <=>
     bvl_state_globals t = bvl_state_globals s /\
     bvl_state_refs t = bvl_state_refs s /\
     bvl_state_clock t = bvl_state_clock s /\
     bvl_state_ffi t = bvl_state_ffi s /\
     bvl_state_compile_oracle t =
       (\n. let ((cs,cfg),progs) = bvl_state_compile_oracle s n in
            let (cs1,progs) = tick_compile_prog limit cs progs in
              (cfg,progs)) /\
     subspt (FST (FST (bvl_state_compile_oracle s 0))) (bvl_state_code t) /\
     bvl_state_compile s = bvl_inlineProof_in_cc limit (bvl_state_compile t) /\
     domain (bvl_state_code t) = domain (bvl_state_code s) /\
     (!k arity exp.
        lookup k (bvl_state_code s) = SOME (arity,exp) ==>
        ?exp2. lookup k (bvl_state_code t) = SOME (arity,exp2) /\
               bvl_inlineProof_exp_rel (bvl_state_code s) [exp] [exp2])`;;

let subspt_exp_rel = prove
 (`!s1 s2 xs ys. subspt s1 s2 /\ bvl_inlineProof_exp_rel s1 xs ys ==>
                 bvl_inlineProof_exp_rel s2 xs ys`,
  SUBGOAL_THEN
   `!s1 xs ys. bvl_inlineProof_exp_rel s1 xs ys ==>
               !s2. subspt s1 s2 ==> bvl_inlineProof_exp_rel s2 xs ys`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC bvl_inlineProof_exp_rel_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[bvl_inlineProof_exp_rel_cases] THEN RFS[subspt_lookup] THEN
  RES_TAC THEN ASM_EXISTS_TAC THEN FS[]);;

(* HOL4 [local val] tick_inline_all_acc (the let of HOL4 as FST and SND) *)
let BVLPROPSAUX_tick_inline_all_acc = prove
 (`!limit (cs:(num#bvl_exp)spt) t aux.
     tick_inline_all limit cs t aux =
     (FST (tick_inline_all limit cs t []),
      APPEND (REVERSE aux) (SND (tick_inline_all limit cs t [])))`,
  SUBGOAL_THEN
   `!t limit (cs:(num#bvl_exp)spt) aux.
     tick_inline_all limit cs t aux =
     (FST (tick_inline_all limit cs t []),
      APPEND (REVERSE aux) (SND (tick_inline_all limit cs t [])))`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tick_inline_all_def; REVERSE; APPEND_NIL; FST; SND]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC(ISPEC `y:num#bvl_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[tick_inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT GEN_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FST; SND; REVERSE; APPEND; GSYM APPEND_ASSOC]);;

let tick_inline_all_names = prove
 (`!limit (cs:(num#bvl_exp)spt) t aux cs1 xs.
     tick_inline_all limit cs t aux = (cs1,xs) ==>
     APPEND (MAP FST (REVERSE aux)) (MAP FST t) = MAP FST xs`,
  REC_IND_TAC (cake_ind "tick_inline_all") THEN
  RW[tick_inline_all_def; tick_inline_all_eq; CONJUNCT1 tick_inline_sing; HD] THEN RES_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[REVERSE; MAP_APPEND; MAP; GSYM APPEND_ASSOC; APPEND]) THEN
  ASM_REWRITE_TAC[REVERSE; MAP_APPEND; MAP; GSYM APPEND_ASSOC; APPEND]);;

(* HOL4 [local val] tick_compile_prog_IMP *)
let BVLPROPSAUX_tick_compile_prog_IMP = prove
 (`!limit (q0:(num#bvl_exp)spt) k (prog:num#bvl_exp) t cs1 prog1.
     tick_compile_prog limit q0 (CONS (k,prog) t) = (cs1,prog1) ==>
     ?p1 vs. prog1 = CONS (k,p1) vs /\ MAP FST vs = MAP FST t`,
  RW[tick_compile_prog_def] THEN IMP_RES_TAC tick_inline_all_names THEN
  RULE_ASSUM_TAC (REWRITE_RULE[REVERSE; MAP; APPEND]) THEN
  QPAT_X_ASSUM "CONS _ _ = _" (STRIP_ASSUME_TAC o REWRITE_RULE[MAP_EQ_CONS] o SYM) THEN
  PAIR_CASES_ON `x0:num#num#bvl_exp` THEN FS[]);;

(* HOL4 [local val] subspt_union_lemma (the spt x of HOL4 is renamed) *)
let BVLPROPSAUX_subspt_union_lemma = prove
 (`!(t1:A spt) t2 c x.
     (!k. lookup k t1 = lookup k t2) ==>
     subspt x (union c t1) ==> subspt x (union c t2)`,
  REWRITE_TAC[subspt_def; domain_union; lookup_union; domain_lookup] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* local helpers for tick_compile_prog_res_range: an insertion at a fresh *)
(* key, and the reassociation of the final union                          *)
let BVLPROPSAUX_subspt_insert_union = prove
 (`!(cs0:A spt) c x v.
     subspt cs0 c /\ ~(x IN domain c) ==>
     subspt (insert x v cs0) (union c (insert x v LN)) /\
     subspt cs0 (union c (insert x v LN))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[subspt_lookup; lookup_insert; lookup_union; lookup_def] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM lookup_NONE_domain]) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[case_def "option"];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[subspt_lookup] o check
        (fun th -> BVLPROPSAUX_has_const "subspt" (concl th))) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `lookup x' (cs0:A spt) = SOME y`)]) THEN
      REWRITE_TAC[case_def "option"]];
    MATCH_MP_TAC (GEN_ALL subspt_trans) THEN EXISTS_TAC `c:A spt` THEN
    ASM_REWRITE_TAC[subspt_union]]);;

let BVLPROPSAUX_union_insert_LN = prove
 (`!x (v:A) r k. lookup k (union (insert x v LN) r) = lookup k (insert x v r)`,
  REWRITE_TAC[lookup_union; lookup_insert; lookup_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "option"]);;

let tick_compile_prog_res_range = prove
 (`!in1 limit in2 c (cs0:(num#bvl_exp)spt) cs1.
     tick_compile_prog limit cs0 in1 = (cs1,in2) /\
     ALL_DISTINCT (MAP FST in1) /\
     subspt cs0 c /\ domain c INTER set_of_list (MAP FST in1) = {} ==>
     subspt cs1 (union c (fromAList in2))`,
  REWRITE_TAC[tick_compile_prog_def] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tick_inline_all_def; REVERSE; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[fromAList_def; union_LN];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC(ISPEC `y:num#bvl_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[tick_inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ONCE_REWRITE_TAC[BVLPROPSAUX_tick_inline_all_acc] THEN
  REWRITE_TAC[REVERSE; APPEND; PAIR_EQ; MAP; FST; ALL_DISTINCT; set_of_list] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e2 = HD (tick_inline (cs0:(num#bvl_exp)spt) [y'])` THEN
  ABBREV_TAC `cs2 = if must_inline x limit e2 then insert x (x',e2) (cs0:(num#bvl_exp)spt)
                    else cs0` THEN
  SUBGOAL_THEN `~(x IN domain (c:(num#bvl_exp)spt))` ASSUME_TAC THENL
   [UNDISCH_TAC `domain (c:(num#bvl_exp)spt) INTER
                 (x INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list))) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`limit:num`; `SND (tick_inline_all limit (cs2:(num#bvl_exp)spt) t [])`;
     `union c (insert x (x',e2) LN):(num#bvl_exp)spt`; `cs2:(num#bvl_exp)spt`;
     `FST (tick_inline_all limit (cs2:(num#bvl_exp)spt) t [])`]) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "cs2" THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[BVLPROPSAUX_subspt_insert_union];
      REWRITE_TAC[domain_union; domain_insert; domain_def] THEN
      UNDISCH_TAC `domain (c:(num#bvl_exp)spt) INTER
                   (x INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list))) = {}` THEN
      UNDISCH_TAC `~MEM (x:num) (MAP FST (t:(num#num#bvl_exp)list))` THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `cs1:(num#bvl_exp)spt`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `in2:(num#num#bvl_exp)list`)) THEN
  REWRITE_TAC[fromAList_def; GSYM union_assoc] THEN
  MATCH_MP_TAC BVLPROPSAUX_subspt_union_lemma THEN
  REWRITE_TAC[BVLPROPSAUX_union_insert_LN]);;

(* HOL4 [local val] exp_rel_swap_lemma *)
let BVLPROPSAUX_exp_rel_swap_lemma = prove
 (`!x1 x2 x3. bvl_inlineProof_exp_rel x1 x2 x3 ==>
              !y1. (!k. lookup k x1 = lookup k y1) ==> bvl_inlineProof_exp_rel y1 x2 x3`,
  MATCH_MP_TAC bvl_inlineProof_exp_rel_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[bvl_inlineProof_exp_rel_cases] THEN RES_TAC THEN RFS[] THEN
  ASM_EXISTS_TAC THEN FS[]);;

let exp_rel_swap = prove
 (`!x1 x2 x3 y1.
     (!k. lookup k x1 = lookup k y1) ==>
     (bvl_inlineProof_exp_rel x1 x2 x3 <=> bvl_inlineProof_exp_rel y1 x2 x3)`,
  MESON_TAC[BVLPROPSAUX_exp_rel_swap_lemma]);;

(* HOL4 [local val] exp_rel_rw (the first one) *)
let BVLPROPSAUX_exp_rel_rw1 = prove
 (`!src_code p1 p2 p3 in1 exp exp2.
     bvl_inlineProof_exp_rel
       (union (union src_code (insert p1 (p2,p3) LN)) (fromAList in1)) [exp] [exp2] <=>
     bvl_inlineProof_exp_rel
       (union src_code (fromAList (CONS (p1,p2,p3) in1))) [exp] [exp2]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC exp_rel_swap THEN
  REWRITE_TAC[fromAList_def; GSYM union_assoc] THEN
  REWRITE_TAC[lookup_union; BVLPROPSAUX_union_insert_LN]);;

(* HOL4 exp_rel_tick_inline *)
let exp_rel_tick_inline = prove
 (`!(cs0:(num#bvl_exp)spt) xs src_code.
     (!k arity v. lookup k cs0 = SOME (arity,v) ==>
                  ?exp. lookup k src_code = SOME (arity,exp) /\
                        bvl_inlineProof_exp_rel src_code [exp] [v]) ==>
     bvl_inlineProof_exp_rel src_code xs (tick_inline cs0 xs)`,
  REC_IND_TAC tick_inline_ind THEN RW[tick_inline_def] THEN
  ONCE_REWRITE_TAC[bvl_inlineProof_exp_rel_cases] THEN FS[HD_tick_inline] THEN
  REPEAT (TOP_CASE_TAC THEN FS[]) THEN RES_TAC THEN RFS[] THEN
  TRY (QEXISTS_TAC "y" THEN RFS[] THEN NO_TAC) THEN
  MP_TAC (ISPECL [`cs:(num#bvl_exp)spt`; `CONS (y:bvl_exp) xs`] LENGTH_tick_inline) THEN
  RW[LENGTH; LENGTH_EQ_CONS] THEN RFS[]);;

let BVLPROPSAUX_cs2_rel = prove
 (`!(cs0:(num#bvl_exp)spt) src_code x arity y e2 b.
     (!k arity v. lookup k cs0 = SOME (arity,v) ==>
                  ?exp. lookup k src_code = SOME (arity,exp) /\
                        bvl_inlineProof_exp_rel src_code [exp] [v]) /\
     ~(x IN domain src_code) /\ ~(x IN domain cs0) /\
     bvl_inlineProof_exp_rel src_code [y] [e2] ==>
     !k a v. lookup k (if b then insert x (arity,e2) cs0 else cs0) = SOME (a,v) ==>
             ?exp. lookup k (union src_code (insert x (arity,y) LN)) = SOME (a,exp) /\
                   bvl_inlineProof_exp_rel (union src_code (insert x (arity,y) LN))
                     [exp] [v]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `subspt (src_code:(num#bvl_exp)spt) (union src_code (insert x (arity,y) LN))`
    ASSUME_TAC THENL [REWRITE_TAC[subspt_union]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM lookup_NONE_domain]) THEN
  ASM_CASES_TAC `k = (x:num)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[lookup_insert; option_INJ; PAIR_EQ;
                                        option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[lookup_union; lookup_insert; case_def "option"] THEN
    EXISTS_TAC `y:bvl_exp` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC subspt_exp_rel THEN EXISTS_TAC `src_code:(num#bvl_exp)spt` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup k (if b then insert x (arity,e2) (cs0:(num#bvl_exp)spt) else cs0) =
                lookup k cs0` SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[lookup_insert]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `a:num`; `v:bvl_exp`] o
                check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[lookup_union; case_def "option"] THEN
  EXISTS_TAC `exp:bvl_exp` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC subspt_exp_rel THEN EXISTS_TAC `src_code:(num#bvl_exp)spt` THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let tick_compile_prog_IMP_exp_rel = prove
 (`!limit (cs0:(num#bvl_exp)spt) in1 cs1 in2 k arity exp src_code.
     tick_compile_prog limit cs0 in1 = (cs1,in2) /\
     ALOOKUP in1 k = SOME (arity,exp) /\
     ALL_DISTINCT (MAP FST in1) /\
     (!k arity v. lookup k cs0 = SOME (arity,v) ==>
                  ?exp. lookup k src_code = SOME (arity,exp) /\
                        bvl_inlineProof_exp_rel src_code [exp] [v]) /\
     DISJOINT (domain src_code) (set_of_list (MAP FST in1)) /\
     DISJOINT (domain cs0) (set_of_list (MAP FST in1)) ==>
     ?exp2. ALOOKUP in2 k = SOME (arity,exp2) /\
            bvl_inlineProof_exp_rel (union src_code (fromAList in1)) [exp] [exp2]`,
  SUBGOAL_THEN
   `!in1 limit (cs0:(num#bvl_exp)spt) cs1 in2 k arity exp src_code.
     tick_compile_prog limit cs0 in1 = (cs1,in2) /\
     ALOOKUP in1 k = SOME (arity,exp) /\
     ALL_DISTINCT (MAP FST in1) /\
     (!k arity v. lookup k cs0 = SOME (arity,v) ==>
                  ?exp. lookup k src_code = SOME (arity,exp) /\
                        bvl_inlineProof_exp_rel src_code [exp] [v]) /\
     DISJOINT (domain src_code) (set_of_list (MAP FST in1)) /\
     DISJOINT (domain cs0) (set_of_list (MAP FST in1)) ==>
     ?exp2. ALOOKUP in2 k = SOME (arity,exp2) /\
            bvl_inlineProof_exp_rel (union src_code (fromAList in1)) [exp] [exp2]`
   (fun th -> REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (SPEC_ALL th)) THEN
  REWRITE_TAC[tick_compile_prog_def] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ALOOKUP_def; option_DISTINCT]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC(ISPEC `y:num#bvl_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[tick_inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ONCE_REWRITE_TAC[BVLPROPSAUX_tick_inline_all_acc] THEN
  REWRITE_TAC[REVERSE; APPEND; PAIR_EQ; MAP; FST; ALL_DISTINCT; set_of_list;
              ALOOKUP_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e2 = HD (tick_inline (cs0:(num#bvl_exp)spt) [y'])` THEN
  SUBGOAL_THEN
   `bvl_inlineProof_exp_rel (union src_code (fromAList (CONS (x,x',y') t))) [y'] [e2]`
   ASSUME_TAC THENL
   [MATCH_MP_TAC subspt_exp_rel THEN EXISTS_TAC `src_code:(num#bvl_exp)spt` THEN
    REWRITE_TAC[subspt_union] THEN EXPAND_TAC "e2" THEN
    REWRITE_TAC[HD_tick_inline] THEN MATCH_MP_TAC exp_rel_tick_inline THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     rhs (concl th) = `in2:(num#num#bvl_exp)list`)) THEN
  REWRITE_TAC[ALOOKUP_def] THEN
  ASM_CASES_TAC `x = (k:num)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; PAIR_EQ]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o check (is_conj o concl)) THEN
    EXISTS_TAC `e2:bvl_exp` THEN ASM_REWRITE_TAC[option_INJ; PAIR_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cs2 = if must_inline x limit e2 then insert x (x',e2) (cs0:(num#bvl_exp)spt)
                    else cs0` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`limit:num`; `cs2:(num#bvl_exp)spt`;
     `FST (tick_inline_all limit (cs2:(num#bvl_exp)spt) t [])`;
     `SND (tick_inline_all limit (cs2:(num#bvl_exp)spt) t [])`;
     `k:num`; `arity:num`; `exp:bvl_exp`;
     `union src_code (insert x (x',y') LN):(num#bvl_exp)spt`] o
     check (is_forall o concl)) THEN
  REWRITE_TAC[PAIR; BVLPROPSAUX_exp_rel_rw1] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x IN domain (src_code:(num#bvl_exp)spt)) /\
                ~(x IN domain (cs0:(num#bvl_exp)spt)) /\
                ~(x IN set_of_list (MAP FST (t:(num#num#bvl_exp)list)))`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (domain (src_code:(num#bvl_exp)spt))
                   (x INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list)))` THEN
    UNDISCH_TAC `DISJOINT (domain (cs0:(num#bvl_exp)spt))
                   (x INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list)))` THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(if x = k then SOME (x',y') else ALOOKUP (t:(num#num#bvl_exp)list) k) =
                 SOME (arity,exp)` THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "cs2" THEN MATCH_MP_TAC BVLPROPSAUX_cs2_rel THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "e2" THEN REWRITE_TAC[HD_tick_inline] THEN
    MATCH_MP_TAC exp_rel_tick_inline THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[DISJOINT; domain_union; domain_insert; domain_def] THEN
    UNDISCH_TAC `DISJOINT (domain (src_code:(num#bvl_exp)spt))
                   (x INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list)))` THEN
    UNDISCH_TAC `~(x IN set_of_list (MAP FST (t:(num#num#bvl_exp)list)))` THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    EXPAND_TAC "cs2" THEN COND_CASES_TAC THEN
    REWRITE_TAC[DISJOINT; domain_insert] THEN
    UNDISCH_TAC `DISJOINT (domain (cs0:(num#bvl_exp)spt))
                   (x INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list)))` THEN
    UNDISCH_TAC `~(x IN set_of_list (MAP FST (t:(num#num#bvl_exp)list)))` THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[]]);;

(* local helpers: the shape of a successful or failing bvl do_install *)
let BVLPROPSAUX_do_install_Rerr = prove
 (`!vs (s:(C,FFI)bvl_state) err.
     bvl_do_install vs s = (Rerr err:(bvl_v#(C,FFI)bvl_state,E)result) ==>
     err = Rabort Rtype_error`,
  RW[bvl_do_install_def] THEN GVS(all_case_eqs()));;

let BVLPROPSAUX_do_install_Rval = prove
 (`!vs (s:(C,FFI)bvl_state) v s'.
     bvl_do_install vs s = (Rval (v,s'):(bvl_v#(C,FFI)bvl_state,E)result) ==>
     ?v1 v2 bytes data cfg progs k prog rest cfg'.
       vs = [v1; v2] /\ bvl_v_to_bytes v1 = SOME bytes /\
       bvl_v_to_words v2 = SOME data /\
       bvl_state_compile_oracle s 0 = (cfg,progs) /\
       DISJOINT (domain (bvl_state_code s)) (set_of_list (MAP FST progs)) /\
       ALL_DISTINCT (MAP FST progs) /\
       bvl_state_compile s cfg progs = SOME (bytes,data,cfg') /\
       progs = CONS (k,prog) rest /\
       FST (bvl_state_compile_oracle s 1) = cfg' /\
       v = bvl_CodePtr k /\
       s' = bvl_state_code_fupd (K (union (bvl_state_code s) (fromAList progs)))
              (bvl_state_compile_oracle_fupd
                 (K (shift_seq 1 (bvl_state_compile_oracle s))) s)`,
  RW[bvl_do_install_def] THEN GVS(shift_seq_def :: all_case_eqs()) THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES]);;

(* local helper: a successful inlining compiler call *)
let BVLPROPSAUX_in_cc_SOME = prove
 (`!limit (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option)
     (cs:(num#bvl_exp)spt) cfg prog bytes data cfg'.
     bvl_inlineProof_in_cc limit cc (cs,cfg) prog = SOME (bytes,data,cfg') <=>
     ?cfg1. cc cfg (SND (tick_compile_prog limit cs prog)) = SOME (bytes,data,cfg1) /\
            cfg' = (FST (tick_compile_prog limit cs prog),cfg1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_inlineProof_in_cc_def] THEN
  QCASES_ON "tick_compile_prog limit cs prog" THEN FS[] THEN
  REPEAT (TOP_CASE_TAC THEN FS[]) THEN MESON_TAC[]);;

(* local helpers: the inlining relation, the entries of the inlining cache  *)
(* and the relation after an Install                                       *)
let BVLPROPSAUX_in_state_rel_cs = prove
 (`!limit (s1:((num#bvl_exp)spt#C,FFI)bvl_state) (t1:(C,FFI)bvl_state) k arity v.
     bvl_inlineProof_in_state_rel limit s1 t1 /\
     lookup k (FST (FST (bvl_state_compile_oracle s1 0))) = SOME (arity,v) ==>
     ?exp. lookup k (bvl_state_code s1) = SOME (arity,exp) /\
           bvl_inlineProof_exp_rel (bvl_state_code s1) [exp] [v]`,
  RW[bvl_inlineProof_in_state_rel_def; subspt_lookup] THEN RES_TAC THEN
  QCASES_ON "lookup k (bvl_state_code s1)" THEN FS[] THENL
   [ASM_MESON_TAC[domain_lookup; option_DISTINCT];
    PAIR_CASES_ON `a:num#bvl_exp` THEN RES_TAC THEN RFS[]]);;

let BVLPROPSAUX_in_state_rel_install = prove
 (`!limit (s1:((num#bvl_exp)spt#C,FFI)bvl_state) (t1:(C,FFI)bvl_state)
     cs cfg progs cs1 prog1.
     bvl_inlineProof_in_state_rel limit s1 t1 /\
     bvl_state_compile_oracle s1 0 = ((cs,cfg),progs) /\
     tick_compile_prog limit cs progs = (cs1,prog1) /\
     DISJOINT (domain (bvl_state_code s1)) (set_of_list (MAP FST progs)) /\
     ALL_DISTINCT (MAP FST progs) /\
     FST (FST (bvl_state_compile_oracle s1 1)) = cs1 ==>
     bvl_inlineProof_in_state_rel limit
       (bvl_state_code_fupd (K (union (bvl_state_code s1) (fromAList progs)))
          (bvl_state_compile_oracle_fupd
             (K (shift_seq 1 (bvl_state_compile_oracle s1))) s1))
       (bvl_state_code_fupd (K (union (bvl_state_code t1) (fromAList prog1)))
          (bvl_state_compile_oracle_fupd
             (K (shift_seq 1 (bvl_state_compile_oracle t1))) t1))`,
  REPEAT STRIP_TAC THEN QPAT_ASSUM "bvl_inlineProof_in_state_rel _ _ _"
    (CAKE_STRIP_ASSUME_TAC o REWRITE_RULE[bvl_inlineProof_in_state_rel_def]) THEN
  REWRITE_TAC[bvl_inlineProof_in_state_rel_def] THEN REPEAT STRIP_TAC THEN
  QPAT_ASSUM "tick_compile_prog _ _ _ = _" (MP_TAC o MATCH_MP tick_inline_all_names o
    REWRITE_RULE[tick_compile_prog_def]) THEN
  FS[shift_seq_def; domain_union; domain_fromAList; REVERSE; MAP; APPEND] THEN DISCH_TAC THENL
   [MATCH_MP_TAC tick_compile_prog_res_range THEN
    MAP_EVERY QEXISTS_TAC ["progs"; "limit"; "cs"] THEN RFS[GSYM DISJOINT];
    ALL_TAC] THEN
  FS[lookup_union] THEN QCASES_ON "lookup k (bvl_state_code s1)" THEN FS[] THENL
   [SUBGOAL_THEN `lookup k (bvl_state_code (t1:(C,FFI)bvl_state)) = NONE` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[lookup_NONE_domain] THEN ASM_REWRITE_TAC[GSYM lookup_NONE_domain];
      ALL_TAC] THEN
    FS[lookup_fromAList] THEN MATCH_MP_TAC tick_compile_prog_IMP_exp_rel THEN
    ASM_EXISTS_TAC THEN RFS[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC BVLPROPSAUX_in_state_rel_cs THEN ASM_EXISTS_TAC THEN
      RFS[];
      IMP_RES_TAC subspt_domain_SUBSET THEN RFS[] THEN ASM SET_TAC[]];
    RES_TAC THEN FS[] THEN MATCH_MP_TAC subspt_exp_rel THEN ASM_EXISTS_TAC THEN
    REWRITE_TAC[subspt_union]]);;

(* local helper: a successful Install under the inlining relation *)
let BVLPROPSAUX_in_do_install = prove
 (`!limit vs (s1:((num#bvl_exp)spt#C,FFI)bvl_state) (t1:(C,FFI)bvl_state) v s2.
     bvl_inlineProof_in_state_rel limit s1 t1 /\
     bvl_do_install vs s1 =
       (Rval (v,s2):(bvl_v#((num#bvl_exp)spt#C,FFI)bvl_state,bvl_v)result) ==>
     ?t2. bvl_inlineProof_in_state_rel limit s2 t2 /\
          bvl_do_install vs t1 = (Rval (v,t2):(bvl_v#(C,FFI)bvl_state,bvl_v)result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP BVLPROPSAUX_do_install_Rval) THEN RVEQ_TAC THEN
  PAIR_CASES_ON `cfg:(num#bvl_exp)spt#C` THEN
  QCASES_ON "tick_compile_prog limit cfg0 (CONS (k,prog) rest)" THEN
  QPAT_ASSUM "bvl_inlineProof_in_state_rel _ _ _"
    (CAKE_STRIP_ASSUME_TAC o REWRITE_RULE[bvl_inlineProof_in_state_rel_def]) THEN
  QPAT_X_ASSUM "bvl_state_compile s1 _ _ = _" MP_TAC THEN
  ASM_REWRITE_TAC[BVLPROPSAUX_in_cc_SOME] THEN STRIP_TAC THEN
  IMP_RES_TAC BVLPROPSAUX_in_state_rel_install THEN FS[] THEN ASM_EXISTS_TAC THEN
  IMP_RES_TAC BVLPROPSAUX_tick_compile_prog_IMP THEN RVEQ_TAC THEN
  QCASES_ON "bvl_state_compile_oracle s1 1" THEN
  RFS[bvl_do_install_def; shift_seq_def; MAP] THEN PAIRARG_TAC THEN RFS[]);;

(* a local helper: a state of another type with the fields of s *)
let BVLPROPSAUX_REC_eq = prove
 (`!(s:(A,B)bvl_state) (t:(C,B)bvl_state).
     bvl_state_globals t = bvl_state_globals s /\ bvl_state_refs t = bvl_state_refs s /\
     bvl_state_clock t = bvl_state_clock s /\ bvl_state_ffi t = bvl_state_ffi s ==>
     bvl_state_REC (bvl_state_globals s) (bvl_state_refs s) (bvl_state_clock s)
       (bvl_state_compile t) (bvl_state_compile_oracle t) (bvl_state_code t)
       (bvl_state_ffi s) = t`,
  SIMP_TAC[bvl_state_component_equality; bvl_state_INFO.ri_accessors]);;

(* HOL4 [local] in_do_app_lemma *)
let bvl_inlineProof_in_do_app_lemma = prove
 (CASE_TERM `!limit op a (s1:((num#bvl_exp)spt#C,FFI)bvl_state) (t1:(C,FFI)bvl_state).
    bvl_inlineProof_in_state_rel limit s1 t1 ==>
    match bvl_do_app op a s1 with
      Rerr err -> (~(err = Rabort Rtype_error) ==> bvl_do_app op a t1 = Rerr err)
    | Rval (v,s2) -> ?t2. bvl_inlineProof_in_state_rel limit s2 t2 /\
                          bvl_do_app op a t1 = Rval (v,t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `op = clos_Install` THEN
  ASM_REWRITE_TAC[BVLPROPSAUX_do_app_Install] THEN TOP_CASE_TAC THEN TRY TOP_CASE_TAC THENL
   [ASM_MESON_TAC[BVLPROPSAUX_in_do_install];
    ASM_MESON_TAC[BVLPROPSAUX_do_install_Rerr];
    QPAT_ASSUM "bvl_inlineProof_in_state_rel _ _ _"
      (CAKE_STRIP_ASSUME_TAC o REWRITE_RULE[bvl_inlineProof_in_state_rel_def]) THEN
    IMP_RES_TAC bvl_do_app_const THEN
    MP_TAC (ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:((num#bvl_exp)spt#C,FFI)bvl_state`;
      `x:bvl_v`; `y:((num#bvl_exp)spt#C,FFI)bvl_state`; `t1:(C,FFI)bvl_state`]
      do_app_Rval_swap) THEN
    RFS[SUBSET_REFL; BVLPROPSAUX_REC_eq; bvl_inlineProof_in_state_rel_def;
        bvl_state_INFO.ri_accessors];
    QPAT_ASSUM "bvl_inlineProof_in_state_rel _ _ _"
      (CAKE_STRIP_ASSUME_TAC o REWRITE_RULE[bvl_inlineProof_in_state_rel_def]) THEN
    MP_TAC (ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:((num#bvl_exp)spt#C,FFI)bvl_state`;
      `a':(bvl_v)error_result`; `t1:(C,FFI)bvl_state`] do_app_Rerr_swap) THEN
    RFS[SUBSET_REFL; BVLPROPSAUX_REC_eq]]);;

(* HOL4 exp_rel_refl *)
let bvl_inlineProof_exp_rel_refl = prove
 (`!(cs:(num#bvl_exp)spt) xs. bvl_inlineProof_exp_rel cs xs xs`,
  REC_IND_TAC tick_inline_ind THEN RW[] THEN
  ONCE_REWRITE_TAC[bvl_inlineProof_exp_rel_cases] THEN FS[] THEN
  ASM_MESON_TAC[cases "option"; PAIR_SURJECTIVE]);;

(* local helper: inversion of exp_rel on the shape of the source *)
let BVLPROPSAUX_exp_rel_inv = prove
 (`(!(cs:(num#bvl_exp)spt) zs. bvl_inlineProof_exp_rel cs [] zs <=> zs = []) /\
   (!(cs:(num#bvl_exp)spt) v zs.
      bvl_inlineProof_exp_rel cs [bvl_Var v] zs <=> zs = [bvl_Var v]) /\
   (!(cs:(num#bvl_exp)spt) x x1 xs zs.
      bvl_inlineProof_exp_rel cs (CONS x (CONS x1 xs)) zs <=>
      ?y y1 ys. zs = CONS y (CONS y1 ys) /\ bvl_inlineProof_exp_rel cs [x] [y] /\
                bvl_inlineProof_exp_rel cs (CONS x1 xs) (CONS y1 ys)) /\
   (!(cs:(num#bvl_exp)spt) x1 x2 x3 zs.
      bvl_inlineProof_exp_rel cs [bvl_If x1 x2 x3] zs <=>
      ?y1 y2 y3. zs = [bvl_If y1 y2 y3] /\ bvl_inlineProof_exp_rel cs [x1] [y1] /\
                 bvl_inlineProof_exp_rel cs [x2] [y2] /\
                 bvl_inlineProof_exp_rel cs [x3] [y3]) /\
   (!(cs:(num#bvl_exp)spt) xs x zs.
      bvl_inlineProof_exp_rel cs [bvl_Let xs x] zs <=>
      ?ys y. zs = [bvl_Let ys y] /\ bvl_inlineProof_exp_rel cs xs ys /\
             bvl_inlineProof_exp_rel cs [x] [y]) /\
   (!(cs:(num#bvl_exp)spt) x1 x2 zs.
      bvl_inlineProof_exp_rel cs [bvl_Handle x1 x2] zs <=>
      ?y1 y2. zs = [bvl_Handle y1 y2] /\ bvl_inlineProof_exp_rel cs [x1] [y1] /\
              bvl_inlineProof_exp_rel cs [x2] [y2]) /\
   (!(cs:(num#bvl_exp)spt) x zs.
      bvl_inlineProof_exp_rel cs [bvl_Raise x] zs <=>
      ?y. zs = [bvl_Raise y] /\ bvl_inlineProof_exp_rel cs [x] [y]) /\
   (!(cs:(num#bvl_exp)spt) x zs.
      bvl_inlineProof_exp_rel cs [bvl_Tick x] zs <=>
      ?y. zs = [bvl_Tick y] /\ bvl_inlineProof_exp_rel cs [x] [y]) /\
   (!(cs:(num#bvl_exp)spt) op xs zs.
      bvl_inlineProof_exp_rel cs [bvl_Op op xs] zs <=>
      ?ys. zs = [bvl_Op op ys] /\ bvl_inlineProof_exp_rel cs xs ys) /\
   (!(cs:(num#bvl_exp)spt) loc n zs.
      bvl_inlineProof_exp_rel cs [bvl_Force loc n] zs <=> zs = [bvl_Force loc n]) /\
   (!(cs:(num#bvl_exp)spt) ticks dest xs zs.
      bvl_inlineProof_exp_rel cs [bvl_Call ticks dest xs] zs <=>
      (?ys. zs = [bvl_Call ticks dest ys] /\ bvl_inlineProof_exp_rel cs xs ys) \/
      (?ys n arity x y. dest = SOME n /\
                        zs = [bvl_Let ys (mk_tick (SUC ticks) y)] /\
                        bvl_inlineProof_exp_rel cs xs ys /\
                        lookup n cs = SOME (arity,x) /\
                        bvl_inlineProof_exp_rel cs [x] [y]))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [bvl_inlineProof_exp_rel_cases] THEN
  REWRITE_TAC(BVLPROPSAUX_both (distinctness "list") @
              BVLPROPSAUX_both (distinctness "bvl_exp") @
              [injectivity "list"; injectivity "bvl_exp"]) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[] THEN TRY (MESON_TAC[]));;

(* local helpers for evaluate_inline: the clock and refs, find_code, the  *)
(* inlined calls and the environment of an inlined body                   *)
let BVLPROPSAUX_in_state_rel_clock = prove
 (`!limit (s:((num#bvl_exp)spt#C,FFI)bvl_state) (t:(C,FFI)bvl_state).
     bvl_inlineProof_in_state_rel limit s t ==>
     bvl_state_clock t = bvl_state_clock s /\ bvl_state_refs t = bvl_state_refs s /\
     (!n. bvl_inlineProof_in_state_rel limit (bvl_dec_clock n s) (bvl_dec_clock n t)) /\
     bvl_inlineProof_in_state_rel limit (bvl_state_clock_fupd (K 0) s)
                                        (bvl_state_clock_fupd (K 0) t)`,
  SIMP_TAC[bvl_inlineProof_in_state_rel_def; bvl_dec_clock_def; bvl_state_INFO.ri_accfupds;
           K_THM]);;

let BVLPROPSAUX_in_find_code = prove
 (`!limit (s:((num#bvl_exp)spt#C,FFI)bvl_state) (t:(C,FFI)bvl_state) dest vs args exp.
     bvl_inlineProof_in_state_rel limit s t /\
     bvl_find_code dest vs (bvl_state_code s) = SOME (args,exp) ==>
     ?exp2. bvl_find_code dest vs (bvl_state_code t) = SOME (args,exp2) /\
            bvl_inlineProof_exp_rel (bvl_state_code s) [exp] [exp2]`,
  REPEAT GEN_TAC THEN CASES_ON `dest:num option` THEN
  RW[bvl_find_code_def; bvl_inlineProof_in_state_rel_def] THEN GVS(all_case_eqs()) THEN
  RES_TAC THEN FS[]);;

let BVLPROPSAUX_in_inline_find_code = prove
 (`!(c0:(num#A)spt) c n vs args e arity x.
     bvl_find_code (SOME n) vs c = SOME (args,e) /\ lookup n c0 = SOME (arity,x) /\
     subspt c0 c ==> args = vs /\ e = x /\ LENGTH vs = arity`,
  RW[subspt_lookup; bvl_find_code_def] THEN RES_TAC THEN GVS(all_case_eqs()));;

let BVLPROPSAUX_expand_env_run = prove
 (`!xs a env (s:(C,FFI)bvl_state) res (P:(C,FFI)bvl_state->bool).
     ~(res = Rerr (Rabort Rtype_error)) /\ (?t. bvl_evaluate (xs,a,s) = (res,t) /\ P t) ==>
     ?t. bvl_evaluate (xs,APPEND a env,s) = (res,t) /\ P t`,
  MESON_TAC[bvl_evaluate_expand_env; FST]);;

(* HOL4 evaluate_inline (the free limit of HOL4 is quantified); the source *)
(* run is split alone, as in evaluate_let_op                                *)
let bvl_inlineProof_evaluate_inline = prove
 (`!limit es env (s1:((num#bvl_exp)spt#C,FFI)bvl_state) res (t1:(C,FFI)bvl_state) s2 es2.
     bvl_inlineProof_in_state_rel limit s1 t1 /\
     bvl_inlineProof_exp_rel (bvl_state_code s1) es es2 /\
     bvl_evaluate (es,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     ?t2. bvl_evaluate (es2,env,t1) = (res,t2) /\
          bvl_inlineProof_in_state_rel limit s2 t2`,
  let split = QPAT_X_ASSUM "_ = (res,s2)" (CAKE_STRIP_ASSUME_TAC o
                CAKE_SIMP_RULE (all_case_eqs())) THEN RVEQ_TAC THEN RFS[] in
  let ih = split THEN RES_TAC THEN RFS[] in
  let ih2 = split THEN IMP_RES_TAC bvl_evaluate_mono THEN IMP_RES_TAC subspt_exp_rel THEN
            RES_TAC THEN RES_TAC THEN RFS[] in
  let clk = IMP_RES_TAC BVLPROPSAUX_in_state_rel_clock in
  let call = clk THEN IMP_RES_TAC BVLPROPSAUX_in_find_code THEN RFS[bvl_dec_clock_code] THEN
             RES_TAC THEN RFS[] in
  GEN_TAC THEN REC_IND_TAC (cake_ind "bvl_evaluate") THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN RFS[BVLPROPSAUX_exp_rel_inv] THEN RVEQ_TAC THEN
  RFS[bvl_evaluate_def] THENL
   [(* Cons *) ih2;
    (* Var *) split;
    (* If *) ih2;
    (* Let *) ih2;
    (* Raise *) ih;
    (* Handle *) ih2;
    (* Op *)
    ih THEN RENAME1 "bvl_evaluate (xs,env,s) = (Rval vs,_)" THEN
    DRULE bvl_inlineProof_in_do_app_lemma THEN
    DISCH_THEN(QSPECL_THEN ["op"; "REVERSE vs"] MP_TAC) THEN RFS[] THEN RW[] THEN RFS[];
    (* Tick *) clk THEN RFS[bvl_dec_clock_code] THEN ih;
    (* Force *) split THEN call;
    (* Call *) ih THEN call;
    (* Call, inlined *)
    ih THEN clk THEN IMP_RES_TAC bvl_evaluate_mono THEN
    IMP_RES_TAC BVLPROPSAUX_in_inline_find_code THEN RVEQ_TAC THEN
    RFS[evaluate_mk_tick; ADD1; bvl_dec_clock_code; ARITH_ss] THEN
    MATCH_MP_TAC BVLPROPSAUX_expand_env_run THEN IMP_RES_TAC subspt_exp_rel THEN RFS[]]);;

let bvl_inlineProof_in_co_def = cake_def
  `bvl_inlineProof_in_co limit (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list) =
     (\n. let ((cs,cfg),progs) = co n in
          let (cs1,progs) = tick_compile_prog limit cs progs in
            (cfg,progs))`;;

let MAP_FST_tick_inline_all = prove
 (`!limit (cs:(num#bvl_exp)spt) prog.
     MAP FST (SND (tick_inline_all limit cs prog [])) = MAP FST prog`,
  REPEAT GEN_TAC THEN QCASES_ON "tick_inline_all limit cs prog []" THEN
  IMP_RES_TAC tick_inline_all_names THEN FS[REVERSE; MAP; APPEND]);;

(* local helpers: HOL4 [local val] exp_rel_rw (the second one) *)
let BVLPROPSAUX_lookup_insert_swap = prove
 (`!x (y:A) (prog:(num#A)list) acc k.
     ~MEM x (MAP FST prog) ==>
     lookup k (union (insert x y (fromAList prog)) acc) =
     lookup k (union (fromAList prog) (insert x y acc))`,
  RW[lookup_union; lookup_insert; lookup_fromAList] THEN FS[GSYM ALOOKUP_NONE]);;

let BVLPROPSAUX_exp_rel_rw2 = prove
 (`!x y (prog:(num#num#bvl_exp)list) acc exp exp2.
     ~MEM x (MAP FST prog) ==>
     (bvl_inlineProof_exp_rel (union (insert x y (fromAList prog)) acc) [exp] [exp2] <=>
      bvl_inlineProof_exp_rel (union (fromAList prog) (insert x y acc)) [exp] [exp2])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC exp_rel_swap THEN GEN_TAC THEN
  MATCH_MP_TAC BVLPROPSAUX_lookup_insert_swap THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local val] lookup_tick_inline_all (limit quantified) *)
let BVLPROPSAUX_lookup_tick_inline_all = prove
 (`!prog limit (cs0:(num#bvl_exp)spt) acc.
     (!k arity v. lookup k cs0 = SOME (arity,v) ==>
        ?exp. lookup k (union (fromAList prog) acc) = SOME (arity,exp) /\
              bvl_inlineProof_exp_rel (union (fromAList prog) acc) [exp] [v]) /\
     DISJOINT (set_of_list (MAP FST prog)) (domain cs0) /\
     DISJOINT (set_of_list (MAP FST prog)) (domain acc) /\
     ALL_DISTINCT (MAP FST prog) ==>
     !k arity exp.
       lookup k (fromAList prog) = SOME (arity,exp) ==>
       ?exp2. lookup k (fromAList (SND (tick_inline_all limit cs0 prog []))) =
                SOME (arity,exp2) /\
              bvl_inlineProof_exp_rel (union (fromAList prog) acc) [exp] [exp2]`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[fromAList_def; lookup_fromAList; ALOOKUP_DEF; distinctness "option"];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `pr:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `pr:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num` (X_CHOOSE_THEN `p3:bvl_exp` SUBST1_TAC)) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tick_inline_all_eq; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ONCE_REWRITE_TAC[BVLPROPSAUX_tick_inline_all_acc] THEN
  REWRITE_TAC[REVERSE; APPEND; fromAList_def; MAP; set_of_list; ALL_DISTINCT] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN
  FIRST_ASSUM(ASSUME_TAC o GEN `e:bvl_exp` o REWRITE_RULE[CONJUNCT1 tick_inline_sing] o
              SPEC `[e:bvl_exp]` o MATCH_MP exp_rel_tick_inline) THEN
   ASM_CASES_TAC `k:num = p1` THEN ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    EXISTS_TAC `tick_inline_sing (cs0:(num#bvl_exp)spt) p3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`limit:num`;
     `if must_inline p1 limit (tick_inline_sing (cs0:(num#bvl_exp)spt) p3)
      then insert p1 (p2,tick_inline_sing cs0 p3) cs0 else cs0`;
     `insert p1 (p2,p3) (acc:(num#bvl_exp)spt)`] o
     check (fun th -> BVLPROPSAUX_has_const "tick_inline_all" (concl th))) THEN
   ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [REPEAT GEN_TAC THEN
       ASM_SIMP_TAC[GSYM BVLPROPSAUX_lookup_insert_swap; GSYM BVLPROPSAUX_exp_rel_rw2] THEN
       COND_CASES_TAC THEN REWRITE_TAC[lookup_insert] THEN
       TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
       TRY (REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
            DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
            EXISTS_TAC `p3:bvl_exp` THEN
            ASM_REWRITE_TAC[lookup_union; lookup_insert] THEN CASE_REWRITE_TAC[] THEN NO_TAC) THEN
       DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       COND_CASES_TAC THEN REWRITE_TAC[domain_insert] THEN
       UNDISCH_TAC `DISJOINT (p1 INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list)))
                             (domain (cs0:(num#bvl_exp)spt))` THEN
       UNDISCH_TAC `~MEM p1 (MAP FST (t:(num#num#bvl_exp)list))` THEN
       REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN SET_TAC[];
       REWRITE_TAC[domain_insert] THEN
       UNDISCH_TAC `DISJOINT (p1 INSERT set_of_list (MAP FST (t:(num#num#bvl_exp)list)))
                             (domain (acc:(num#bvl_exp)spt))` THEN
       UNDISCH_TAC `~MEM p1 (MAP FST (t:(num#num#bvl_exp)list))` THEN
       REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN SET_TAC[];
       ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL [`k:num`; `arity:num`; `exp:bvl_exp`]) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `exp2:bvl_exp` THEN
   ASM_SIMP_TAC[BVLPROPSAUX_exp_rel_rw2]);;

(* HOL4 [local val] subspt_tick_inline (limit quantified) *)
let BVLPROPSAUX_subspt_tick_inline = prove
 (`!prog limit (cs:(num#bvl_exp)spt) aux.
     subspt cs (fromAList (REVERSE aux)) /\
     ALL (\x. ~(FST x IN domain cs)) prog /\
     ALL_DISTINCT (APPEND (MAP FST prog) (MAP FST aux)) ==>
     subspt (FST (tick_inline_all limit cs prog aux))
            (fromAList (SND (tick_inline_all limit cs prog aux)))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tick_inline_all_def; FST; SND] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `pr:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `pr:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e1:bvl_exp` SUBST1_TAC)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[tick_inline_all_eq; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[ALL; MAP; APPEND; ALL_DISTINCT; FST] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (REVERSE (aux:(num#num#bvl_exp)list)) n = NONE` ASSUME_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE; GSYM MAP_REVERSE; MEM_REVERSE] THEN
    UNDISCH_TAC `~MEM n (APPEND (MAP FST (t:(num#num#bvl_exp)list))
                                (MAP FST (aux:(num#num#bvl_exp)list)))` THEN
    REWRITE_TAC[MEM_APPEND; DE_MORGAN_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `subspt (cs:(num#bvl_exp)spt) (fromAList (REVERSE aux))` THEN
    REWRITE_TAC[subspt_lookup; lookup_fromAList; REVERSE; ALOOKUP_APPEND] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[lookup_insert] THEN TRY COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[ALOOKUP_THM];
      ALL_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `lookup x (cs:(num#bvl_exp)spt) = SOME y`)) THEN
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[];
    UNDISCH_TAC `ALL (\x:num#num#bvl_exp. ~(FST x IN domain (cs:(num#bvl_exp)spt))) t` THEN
    UNDISCH_TAC `~MEM n (APPEND (MAP FST (t:(num#num#bvl_exp)list))
                                (MAP FST (aux:(num#num#bvl_exp)list)))` THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[GSYM ALL_MEM; domain_insert; IN_INSERT; MEM_APPEND; MEM_MAP] THEN
    MESON_TAC[];
    UNDISCH_TAC `ALL_DISTINCT (APPEND (MAP FST (t:(num#num#bvl_exp)list))
                                      (MAP FST (aux:(num#num#bvl_exp)list)))` THEN
    UNDISCH_TAC `~MEM n (APPEND (MAP FST (t:(num#num#bvl_exp)list))
                                (MAP FST (aux:(num#num#bvl_exp)list)))` THEN
    REWRITE_TAC[ALL_DISTINCT_APPEND; MAP; ALL_DISTINCT; MEM; MEM_APPEND; FST] THEN
    MESON_TAC[]]);;


(* HOL4 [local val] evaluate_initial_state, in its final form (after HOL4's *)
(* GEN_ALL and SIMP_RULE, which eliminate co1 and cc)                        *)
let BVLPROPSAUX_evaluate_initial_state = prove
 (`!limit start env (ffi0:(FFI)ffi_state) prog
     (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list)
     (cc1:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) k res s2.
     bvl_evaluate ([bvl_Call 0 (SOME start) []],env,
                   bvl_initial_state ffi0 (fromAList prog) co
                     (bvl_inlineProof_in_cc limit cc1) k) = (res,s2) /\
     FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
     ALL_DISTINCT (MAP FST prog) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     ?t2. bvl_evaluate ([bvl_Call 0 (SOME start) []],env,
                        bvl_initial_state ffi0
                          (fromAList (SND (tick_compile_prog limit LN prog)))
                          (bvl_inlineProof_in_co limit co) cc1 k) = (res,t2) /\
          bvl_inlineProof_in_state_rel limit s2 t2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC bvl_inlineProof_evaluate_inline THEN
  MAP_EVERY EXISTS_TAC
   [`[bvl_Call 0 (SOME start) []]`;
    `bvl_initial_state (ffi0:(FFI)ffi_state) (fromAList prog)
       (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list)
       (bvl_inlineProof_in_cc limit
         (cc1:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option)) k`] THEN
  ASM_REWRITE_TAC[bvl_inlineProof_exp_rel_refl] THEN
  REWRITE_TAC[bvl_inlineProof_in_state_rel_def; bvl_initial_state_simp] THEN
  ASM_REWRITE_TAC[bvl_inlineProof_in_co_def] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[tick_compile_prog_def] THEN
    MATCH_MP_TAC BVLPROPSAUX_subspt_tick_inline THEN
    ASM_REWRITE_TAC[REVERSE; fromAList_def; subspt_LN; domain_def; NOT_IN_EMPTY; MAP;
                    APPEND_NIL; ALL_T];
    REWRITE_TAC[domain_fromAList; tick_compile_prog_def; MAP_FST_tick_inline_all];
    MP_TAC(ISPECL [`prog:(num#num#bvl_exp)list`; `limit:num`; `LN:(num#bvl_exp)spt`;
                   `LN:(num#bvl_exp)spt`] BVLPROPSAUX_lookup_tick_inline_all) THEN
    ASM_REWRITE_TAC[union_LN; lookup_rwts; domain_def; DISJOINT_EMPTY;
                    distinctness "option"; tick_compile_prog_def]]);;

(* HOL4 [local val] in_evaluate_Call *)
let BVLPROPSAUX_in_evaluate_Call = prove
 (`!limit start env (ffi0:(FFI)ffi_state) prog
     (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list)
     (cc1:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) k res s2.
     bvl_evaluate ([bvl_Call 0 (SOME start) []],env,
                   bvl_initial_state ffi0 (fromAList prog) co
                     (bvl_inlineProof_in_cc limit cc1) k) = (res,s2) /\
     FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
     ALL_DISTINCT (MAP FST prog) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     ?t2. bvl_evaluate ([bvl_Call 0 (SOME start) []],env,
                        bvl_initial_state ffi0
                          (fromAList (SND (tick_compile_prog limit LN prog)))
                          (bvl_inlineProof_in_co limit co) cc1 k) = (res,t2) /\
          bvl_state_ffi s2 = bvl_state_ffi t2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP BVLPROPSAUX_evaluate_initial_state) THEN
  REWRITE_TAC[bvl_inlineProof_in_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 [local val] semantics_tick_inline *)
let BVLPROPSAUX_semantics_tick_inline = prove
 (`!limit (ffi:(FFI)ffi_state) prog (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list)
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) start.
     FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
     ALL_DISTINCT (MAP FST prog) ==>
     ~(bvl_semantics ffi (fromAList prog) co (bvl_inlineProof_in_cc limit cc) start = Fail) ==>
     bvl_semantics ffi (fromAList (SND (tick_compile_prog limit LN prog)))
       (bvl_inlineProof_in_co limit co) cc start =
     bvl_semantics ffi (fromAList prog) co (bvl_inlineProof_in_cc limit cc) start`,
  RW[] THEN MATCH_MP_TAC BVLPROPSAUX_bvl_semantics_sim THEN RW[] THEN QEXISTS_TAC "0" THEN
  IMP_RES_TAC BVLPROPSAUX_in_evaluate_Call THEN FS[] THEN ASM_EXISTS_TAC THEN FS[]);;


(* let_op *)

let let_opt_def = cake_def
  `let_opt split_seq cut_size (arity:num,prog:bvl_exp) =
     (arity,compile_any split_seq cut_size arity (bvl_inline_let_op_sing prog))`;;

let let_state_rel_def = cake_def
  `let_state_rel split_seq cut_size (s:(C,FFI)bvl_state) (t:(C,FFI)bvl_state) <=>
     t = bvl_state_code_fupd (K (map (let_opt split_seq cut_size) (bvl_state_code s)))
           (bvl_state_compile_fupd (K (bvl_state_compile t))
              (bvl_state_compile_oracle_fupd
                 (K ((I ## MAP (I ## let_opt split_seq cut_size)) o
                     bvl_state_compile_oracle s)) s)) /\
     bvl_state_compile s =
       (\cfg prog. bvl_state_compile t cfg (MAP (I ## let_opt split_seq cut_size) prog))`;;

(* HOL4 rebinds let_state_rel_def to the definition simplified with the     *)
(* record equality (and keeps the original as let_state_rel_alt); here the *)
(* simplified form is the local helper BVLPROPSAUX_let_state_rel_eq         *)
let BVLPROPSAUX_let_state_rel_eq = prove
 (`!split_seq cut_size (s:(C,FFI)bvl_state) t.
     let_state_rel split_seq cut_size s t <=>
     bvl_state_globals t = bvl_state_globals s /\
     bvl_state_refs t = bvl_state_refs s /\
     bvl_state_clock t = bvl_state_clock s /\
     bvl_state_compile_oracle t =
       (I ## MAP (I ## let_opt split_seq cut_size)) o bvl_state_compile_oracle s /\
     bvl_state_code t = map (let_opt split_seq cut_size) (bvl_state_code s) /\
     bvl_state_ffi t = bvl_state_ffi s /\
     bvl_state_compile s =
       (\cfg prog. bvl_state_compile t cfg (MAP (I ## let_opt split_seq cut_size) prog))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[let_state_rel_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [bvl_state_component_equality] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN CONV_TAC TAUT);;

(* HOL4 [simp] *)
let HD_let_op = prove
 (`!x. [HD (bvl_inline_let_op [x])] = bvl_inline_let_op [x]`,
  REWRITE_TAC[let_op_one; HD]);;

(* HOL4 [local val] var_list_IMP_evaluate, the first (general) one, by the *)
(* induction of var_list (HOL4: Induct on a2); the free env of HOL4 is      *)
(* quantified                                                               *)
let BVLPROPSAUX_var_list_IMP_evaluate_gen = prove
 (`!n l (xs:bvl_exp list) a1 a2 env (s:(C,FFI)bvl_state).
     bvl_inline_var_list n l xs /\ n = LENGTH a1 /\ LENGTH xs = LENGTH a2 ==>
     bvl_evaluate (l,APPEND (APPEND a1 a2) env,s) = (Rval a2,s)`,
  REC_IND_TAC (cake_ind "bvl_inline_var_list") THEN
  RW[bvl_inline_var_list_def; LENGTH_EQ_NIL; bvl_evaluate_def] THEN
  QCASES_ON "a2" THEN FS[LENGTH] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  FIRST_X_ASSUM (QSPECL_THEN ["APPEND a1 [a0]"; "a1'"; "env"; "s"] MP_TAC) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_APPEND; LENGTH; GSYM ONE] THEN
  DISCH_TAC THEN SIMP[bvl_evaluate_def; EL_APPEND; ARITH_ss]);;

(* HOL4 [local val] var_list_IMP_evaluate, the second one (env quantified) *)
let BVLPROPSAUX_var_list_IMP_evaluate = prove
 (`!l (xs:bvl_exp list) a env (s:(C,FFI)bvl_state).
     bvl_inline_var_list 0 l xs /\ LENGTH xs = LENGTH a ==>
     bvl_evaluate (l,APPEND a env,s) = (Rval a,s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `l:bvl_exp list`; `xs:bvl_exp list`; `[]:bvl_v list`; `a:bvl_v list`;
                 `env:bvl_v list`; `s:(C,FFI)bvl_state`]
                BVLPROPSAUX_var_list_IMP_evaluate_gen) THEN
  ASM_REWRITE_TAC[LENGTH; APPEND]);;

let bvl_inlineProof_LENGTH_let_op = prove
 (`!xs. LENGTH (bvl_inline_let_op xs) = LENGTH xs`,
  REWRITE_TAC[GSYM (CONJUNCT2 let_op_one)] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[let_op_one_def; LENGTH]);;


(* HOL4 [local] do_app_lemma, the second one (for let_op) *)
let bvl_inlineProof_do_app_lemma = prove
 (CASE_TERM `!q4 l4 op a (s1:(C,FFI)bvl_state) t1.
    let_state_rel q4 l4 s1 t1 ==>
    match bvl_do_app op a s1 with
      Rerr err -> bvl_do_app op a t1 = Rerr err
    | Rval (v,s2) -> ?t2. let_state_rel q4 l4 s2 t2 /\
                          bvl_do_app op a t1 = Rval (v,t2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_let_state_rel_eq] THEN
  MATCH_ACCEPT_TAC (ISPEC `let_opt q4 l4` BVLPROPSAUX_do_app_map));;


(* local helpers for evaluate_let_op: the clock and refs, find_code and     *)
(* compile_any                                                              *)
let BVLPROPSAUX_let_state_rel_clock = prove
 (`!q l (s:(C,FFI)bvl_state) t.
     let_state_rel q l s t ==>
     bvl_state_clock t = bvl_state_clock s /\ bvl_state_refs t = bvl_state_refs s /\
     (!n. let_state_rel q l (bvl_dec_clock n s) (bvl_dec_clock n t)) /\
     let_state_rel q l (bvl_state_clock_fupd (K 0) s) (bvl_state_clock_fupd (K 0) t)`,
  SIMP_TAC[BVLPROPSAUX_let_state_rel_eq; bvl_dec_clock_def; bvl_state_INFO.ri_accfupds;
           K_THM]);;

let BVLPROPSAUX_let_find_code = prove
 (`!q l (s:(C,FFI)bvl_state) t dest vs args exp.
     let_state_rel q l s t /\ bvl_find_code dest vs (bvl_state_code s) = SOME (args,exp) ==>
     bvl_find_code dest vs (bvl_state_code t) =
       SOME (args,compile_any q l (LENGTH args) (bvl_inline_let_op_sing exp))`,
  REPEAT GEN_TAC THEN CASES_ON `dest:num option` THEN
  RW[bvl_find_code_def; BVLPROPSAUX_let_state_rel_eq; lookup_map] THEN
  GVS(let_opt_def :: all_case_eqs()) THEN FS[LENGTH_FRONT; GSYM ADD1; PRE]);;

let BVLPROPSAUX_compile_any_run = prove
 (`!q l e args (s:(C,FFI)bvl_state) res (P:(C,FFI)bvl_state->bool).
     ~(res = Rerr (Rabort Rtype_error)) /\ (?t. bvl_evaluate ([e],args,s) = (res,t) /\ P t) ==>
     ?t. bvl_evaluate ([compile_any q l (LENGTH args) e],args,s) = (res,t) /\ P t`,
  MESON_TAC[compile_any_correct]);;

(* the Let case: let_op turns Let xs (Op op ys) into Op op xs when ys are *)
(* the variables of xs                                                      *)
let BVLPROPSAUX_dest_op_SOME = prove
 (`!e (args:A list) op.
     bvl_inline_dest_op e args = SOME op ==>
     ?ys. e = bvl_Op op ys /\ bvl_inline_var_list 0 ys args`,
  GEN_TAC THEN CASES_ON `e:bvl_exp` THEN
  REWRITE_TAC[bvl_inline_dest_op_def; distinctness "option"] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; injectivity "bvl_exp"] THEN
  DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `a1:bvl_exp list` THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_let_op_Op_eq = prove
 (`!op ys xs vs (t:(C,FFI)bvl_state) env0 t0.
     bvl_inline_var_list 0 ys xs /\ bvl_evaluate (xs,env0,t0) = (Rval vs,t) ==>
     bvl_evaluate ([bvl_Op op xs],env0,t0) = bvl_evaluate ([bvl_Op op ys],APPEND vs env0,t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ys:bvl_exp list`; `xs:bvl_exp list`; `vs:bvl_v list`; `env0:bvl_v list`;
                 `t:(C,FFI)bvl_state`] BVLPROPSAUX_var_list_IMP_evaluate) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH);
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[]);;

(* HOL4 evaluate_let_op (the free q4 and l4 of HOL4 are quantified); the   *)
(* source run is split alone (splitting the target's case expressions too  *)
(* took more time); let_op [x] is let_op_one x                              *)
let bvl_inlineProof_evaluate_let_op = prove
 (`!q4 l4 es env (s1:(C,FFI)bvl_state) res t1 s2.
     let_state_rel q4 l4 s1 t1 /\
     bvl_evaluate (es,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     ?t2. bvl_evaluate (bvl_inline_let_op es,env,t1) = (res,t2) /\
          let_state_rel q4 l4 s2 t2`,
  let split = QPAT_X_ASSUM "_ = (res,s2)" (CAKE_STRIP_ASSUME_TAC o
                CAKE_SIMP_RULE (all_case_eqs())) THEN RVEQ_TAC THEN RFS[] in
  let ih = split THEN RES_TAC THEN RFS[] in
  let ih2 = split THEN RES_TAC THEN RES_TAC THEN RFS[] in
  let call = IMP_RES_TAC BVLPROPSAUX_let_state_rel_clock THEN
    IMP_RES_TAC BVLPROPSAUX_let_find_code THEN RFS[bvl_inline_let_op_sing_eq] THEN
    MATCH_MP_TAC BVLPROPSAUX_compile_any_run THEN RES_TAC THEN RFS[] in
  GEN_TAC THEN GEN_TAC THEN REC_IND_TAC (cake_ind "bvl_evaluate") THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RFS[bvl_inline_let_op_def; let_op_one; let_op_one_def; bvl_evaluate_def] THENL
   [(* Cons *) ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN ih2;
    (* Var *) split;
    (* If *) ih2;
    (* Let *)
    ih2 THEN TOP_CASE_TAC THEN TRY (RFS[bvl_evaluate_def] THEN NO_TAC) THEN
    IMP_RES_TAC BVLPROPSAUX_dest_op_SOME THEN IMP_RES_TAC BVLPROPSAUX_let_op_Op_eq THEN RFS[];
    (* Raise *) ih;
    (* Handle *) ih2;
    (* Op *)
    ih2 THEN RENAME1 "bvl_evaluate (xs,env,s) = (Rval vs,_)" THEN
    DRULE bvl_inlineProof_do_app_lemma THEN
    DISCH_THEN(QSPECL_THEN ["op"; "REVERSE vs"] MP_TAC) THEN RFS[] THEN RW[] THEN RFS[];
    (* Tick *) IMP_RES_TAC BVLPROPSAUX_let_state_rel_clock THEN ih;
    (* Force *) split THEN call;
    (* Call *) ih THEN call]);;

let let_op_cc_def = cake_def
  `let_op_cc q4 l4
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) =
     (\cfg prog. cc cfg (MAP (I ## let_opt q4 l4) prog))`;;

(* HOL4 [local] let_evaluate_Call (the free variables are quantified) *)
let let_evaluate_Call = prove
 (`!q4 l4 start (ffi0:(FFI)ffi_state) prog (co:num->C#(num#num#bvl_exp)list)
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) k r s.
     bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                   bvl_initial_state ffi0 prog co (let_op_cc q4 l4 cc) k) = (r,s) /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?s2. bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                        bvl_initial_state ffi0 (map (let_opt q4 l4) prog)
                          ((I ## MAP (I ## let_opt q4 l4)) o co) cc k) = (r,s2) /\
          bvl_state_ffi s2 = bvl_state_ffi s /\ bvl_state_clock s = bvl_state_clock s2`,
  REPEAT STRIP_TAC THEN DRULE_AT (Pos (el 1)) bvl_inlineProof_evaluate_let_op THEN
  DISCH_THEN (QSPECL_THEN ["q4"; "l4"; "bvl_initial_state ffi0 (map (let_opt q4 l4) prog)
    ((I ## MAP (I ## let_opt q4 l4)) o co) cc k"] MP_TAC) THEN
  RW[BVLPROPSAUX_let_state_rel_eq; bvl_initial_state_simp; let_op_cc_def;
     bvl_inline_let_op_def] THEN ASM_EXISTS_TAC THEN FS[]);;

(* HOL4 [local val] semantics_let_op *)
let BVLPROPSAUX_semantics_let_op = prove
 (`!q4 l4 (ffi:(FFI)ffi_state) prog (co:num->C#(num#num#bvl_exp)list)
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) start.
     ~(bvl_semantics ffi prog co (let_op_cc q4 l4 cc) start = Fail) ==>
     bvl_semantics ffi (map (let_opt q4 l4) prog)
       ((I ## MAP (I ## let_opt q4 l4)) o co) cc start =
     bvl_semantics ffi prog co (let_op_cc q4 l4 cc) start`,
  RW[] THEN MATCH_MP_TAC BVLPROPSAUX_bvl_semantics_sim THEN RW[] THEN QEXISTS_TAC "0" THEN
  IMP_RES_TAC let_evaluate_Call THEN FS[] THEN ASM_EXISTS_TAC THEN FS[]);;


let let_opt_remove_def = cake_def
  `let_opt_remove b l (arity:num,prog:bvl_exp) =
     let_opt b l (arity,HD (bvl_inline_remove_ticks [prog]))`;;

(* HOL4 map_fromAList; sptree.ml already has map_fromAList (the form with *)
(* a paired lambda), hence the prefix                                       *)
let bvl_inlineProof_map_fromAList = prove
 (`!xs (f:A->B). map f (fromAList xs) = fromAList (MAP (I ## f) xs)`,
  REWRITE_TAC[map_fromAList; BVLPROPSAUX_PAIR_LAMBDA_MAP]);;

(* HOL4 [local val] ticks and lets: the semantics of remove_ticks and of  *)
(* let_op for a code table built with fromAList                            *)
let BVLPROPSAUX_ticks = prove
 (`!(ffi:(FFI)ffi_state) p (co:num -> C # (num#num#bvl_exp) list) cc start.
     bvl_semantics ffi
       (fromAList (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))) p))
       (bvl_inlineProof_remove_ticks_co o co) cc start =
     bvl_semantics ffi (fromAList p) co (bvl_inlineProof_remove_ticks_cc cc) start`,
  REWRITE_TAC[GSYM bvl_inlineProof_map_fromAList; bvl_inlineProof_semantics_remove_ticks]);;

let BVLPROPSAUX_lets = prove
 (`!q4 l4 (ffi:(FFI)ffi_state) p (co:num->C#(num#num#bvl_exp)list)
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) start.
     ~(bvl_semantics ffi (fromAList p) co (let_op_cc q4 l4 cc) start = Fail) ==>
     bvl_semantics ffi (fromAList (MAP (I ## let_opt q4 l4) p))
       ((I ## MAP (I ## let_opt q4 l4)) o co) cc start =
     bvl_semantics ffi (fromAList p) co (let_op_cc q4 l4 cc) start`,
  REWRITE_TAC[GSYM bvl_inlineProof_map_fromAList; BVLPROPSAUX_semantics_let_op]);;

(* HOL4 [local val] inline_ticks *)
let BVLPROPSAUX_inline_ticks = prove
 (`!limit (ffi:(FFI)ffi_state) prog (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list)
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) start.
     FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
     ALL_DISTINCT (MAP FST prog) ==>
     ~(bvl_semantics ffi (fromAList prog) co
         (bvl_inlineProof_in_cc limit (bvl_inlineProof_remove_ticks_cc cc)) start = Fail) ==>
     bvl_semantics ffi
       (fromAList (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x])))
                     (SND (tick_compile_prog limit LN prog))))
       (bvl_inlineProof_remove_ticks_co o bvl_inlineProof_in_co limit co) cc start =
     bvl_semantics ffi (fromAList prog) co
       (bvl_inlineProof_in_cc limit (bvl_inlineProof_remove_ticks_cc cc)) start`,
  REWRITE_TAC[BVLPROPSAUX_ticks] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] BVLPROPSAUX_semantics_tick_inline) THEN
  ASM_REWRITE_TAC[]);;

let bvl_inline_cc_def = cake_def
  `bvl_inline_cc limit q4 l4
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) =
     bvl_inlineProof_in_cc limit
       (bvl_inlineProof_remove_ticks_cc (let_op_cc q4 l4 cc))`;;

let bvl_inline_co_def = cake_def
  `bvl_inline_co limit q4 l4 (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list) =
     (\x. (I ## MAP (I ## let_opt q4 l4))
            (bvl_inlineProof_remove_ticks_co (bvl_inlineProof_in_co limit co x)))`;;

(* HOL4 [local val] MAP_optimise *)
let BVLPROPSAUX_MAP_optimise = prove
 (`!o1 o2 (prog:(num#num#bvl_exp)list).
     MAP (bvl_inline_optimise o1 o2) prog =
     MAP (I ## let_opt o1 o2)
       (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))) prog)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  PAIR_CASES_ON `h:num#num#bvl_exp` THEN
  REWRITE_TAC[bvl_inline_optimise_def; PAIR_MAP_THM; I_THM; let_opt_def]);;


let bvl_inlineProof_state_cc_compile_inc_eq = prove
 (`!limit o1 o2 (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option).
     state_cc (bvl_inline_compile_inc limit o1 o2) cc =
     bvl_inlineProof_in_cc limit (bvl_inlineProof_remove_ticks_cc (let_op_cc o1 o2 cc))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; state_cc_def; bvl_inlineProof_in_cc_def;
    bvl_inline_compile_inc_def; bvl_inlineProof_remove_ticks_cc_def; let_op_cc_def] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN FS[BVLPROPSAUX_MAP_optimise]);;

let bvl_inlineProof_state_co_compile_inc_eq = prove
 (`!limit o1 o2 (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list).
     state_co (bvl_inline_compile_inc limit o1 o2) co =
     ((I ## MAP (I ## let_opt o1 o2)) o bvl_inlineProof_remove_ticks_co o
      bvl_inlineProof_in_co limit co)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; state_co_def; bvl_inlineProof_in_co_def;
    bvl_inline_compile_inc_def; bvl_inlineProof_remove_ticks_co_def] THEN
  REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN FS[BVLPROPSAUX_MAP_optimise]);;

let bvl_inlineProof_compile_prog_semantics = prove
 (`!limit o1 o2 prog s1 prog1 (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list)
     (ffi:(FFI)ffi_state)
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) start.
     bvl_inline_compile_prog limit o1 o2 prog = (s1,prog1) /\
     FST (FST (co 0)) = s1 /\ ALL_DISTINCT (MAP FST prog) ==>
     ~(bvl_semantics ffi (fromAList prog) co
         (state_cc (bvl_inline_compile_inc limit o1 o2) cc) start = Fail) ==>
     bvl_semantics ffi (fromAList prog1) (state_co (bvl_inline_compile_inc limit o1 o2) co)
       cc start =
     bvl_semantics ffi (fromAList prog) co (state_cc (bvl_inline_compile_inc limit o1 o2) cc)
       start`,
  REWRITE_TAC[bvl_inlineProof_state_cc_compile_inc_eq; bvl_inlineProof_state_co_compile_inc_eq;
              bvl_inline_compile_prog_def; bvl_inline_compile_inc_def] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN RW[BVLPROPSAUX_MAP_optimise] THEN
  MP_TAC (ISPECL [`limit:num`; `ffi:(FFI)ffi_state`; `prog:(num#num#bvl_exp)list`;
    `co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list`;
    `let_op_cc o1 o2 (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option)`;
    `start:num`]
    BVLPROPSAUX_inline_ticks) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> FS[GSYM th]) THEN
  MATCH_MP_TAC BVLPROPSAUX_lets THEN FS[]);;


let handle_ok_optimise = prove
 (`!b i (prog:(A#num#bvl_exp)list).
     handle_ok (MAP (SND o SND o bvl_inline_optimise b i) prog)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; handle_ok_def] THEN
  ONCE_REWRITE_TAC[handle_ok_CONS] THEN PAIR_CASES_ON `h:A#num#bvl_exp` THEN
  ASM_REWRITE_TAC[o_THM; bvl_inline_optimise_def; compile_any_handle_ok]);;

let compile_prog_handle_ok = prove
 (`!l b i prog inlines prog3.
     bvl_inline_compile_prog l b i prog = (inlines,prog3) ==>
     handle_ok (MAP (SND o SND) prog3)`,
  REWRITE_TAC[bvl_inline_compile_prog_def; bvl_inline_compile_inc_def] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN RW[] THEN
  REWRITE_TAC[GSYM MAP_o; GSYM o_ASSOC; handle_ok_optimise]);;

(* HOL4 [simp] *)
let MAP_FST_MAP_optimise = prove
 (`!x y (z:(A#num#bvl_exp)list).
     MAP FST (MAP (bvl_inline_optimise x y) z) = MAP FST z`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  PAIR_CASES_ON `h:A#num#bvl_exp` THEN REWRITE_TAC[bvl_inline_optimise_def; FST]);;

let compile_prog_names = prove
 (`!l b i prog inlines prog3.
     bvl_inline_compile_prog l b i prog = (inlines,prog3) ==>
     MAP FST prog3 = MAP FST prog`,
  REWRITE_TAC[bvl_inline_compile_prog_def; bvl_inline_compile_inc_def] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN RW[MAP_FST_MAP_optimise] THEN
  IMP_RES_TAC (REWRITE_RULE[GSYM tick_compile_prog_def] (ISPECL
    [`limit:num`; `cs:(num#bvl_exp)spt`; `t:(num#num#bvl_exp)list`; `[]:(num#num#bvl_exp)list`]
    tick_inline_all_names)) THEN FS[REVERSE; MAP; APPEND]);;


(* code labels *)

let bvl_inlineProof_var_list_code_labels_imp = prove
 (`!n x (y:A list). bvl_inline_var_list n x y ==>
     UNIONS (set_of_list (MAP bvl_get_code_labels x)) = {}`,
  REC_IND_TAC (cake_ind "bvl_inline_var_list") THEN
  RW[bvl_inline_var_list_def] THEN FS BVLPROPSAUX_LABELS_RWS);;

(* a local helper: the code labels of let_op_one and let_op_list *)
let BVLPROPSAUX_let_op_one_code_labels = prove
 (`(!e. bvl_get_code_labels (let_op_one e) = bvl_get_code_labels e) /\
   (!es. UNIONS (set_of_list (MAP bvl_get_code_labels (bvl_inline_let_op_list es))) =
         UNIONS (set_of_list (MAP bvl_get_code_labels es)))`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN RW[let_op_one_def] THEN FS BVLPROPSAUX_LABELS_RWS THEN
  TOP_CASE_TAC THEN FS BVLPROPSAUX_LABELS_RWS THEN IMP_RES_TAC BVLPROPSAUX_dest_op_SOME THEN
  IMP_RES_TAC bvl_inlineProof_var_list_code_labels_imp THEN
  RFS BVLPROPSAUX_LABELS_RWS THEN ASM SET_TAC[]);;

let let_op_code_labels = prove
 (`!x. UNIONS (set_of_list (MAP bvl_get_code_labels (bvl_inline_let_op x))) =
       UNIONS (set_of_list (MAP bvl_get_code_labels x))`,
  REWRITE_TAC[GSYM (CONJUNCT2 let_op_one); BVLPROPSAUX_let_op_one_code_labels]);;

(* HOL4 [simp] *)
let let_op_sing_code_labels = prove
 (`!x. bvl_get_code_labels (bvl_inline_let_op_sing x) = bvl_get_code_labels x`,
  REWRITE_TAC[bvl_inline_let_op_sing_eq; BVLPROPSAUX_let_op_one_code_labels]);;

(* a local helper: the code labels of remove_ticks_sing and remove_ticks_list *)
let BVLPROPSAUX_remove_ticks_sing_code_labels = prove
 (`(!e. bvl_get_code_labels (bvl_inline_remove_ticks_sing e) = bvl_get_code_labels e) /\
   (!es. UNIONS (set_of_list (MAP bvl_get_code_labels (bvl_inline_remove_ticks_list es))) =
         UNIONS (set_of_list (MAP bvl_get_code_labels es)))`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN REWRITE_TAC[bvl_inline_remove_ticks_sing_def] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC BVLPROPSAUX_LABELS_RWS);;

let bvl_inlineProof_remove_ticks_code_labels = prove
 (`!x. UNIONS (set_of_list (MAP bvl_get_code_labels (bvl_inline_remove_ticks x))) =
       UNIONS (set_of_list (MAP bvl_get_code_labels x))`,
  REWRITE_TAC[GSYM (CONJUNCT2 remove_ticks_sing); BVLPROPSAUX_remove_ticks_sing_code_labels]);;

(* a local helper: compile_any does not add code labels *)
let BVLPROPSAUX_compile_any_code_labels = prove
 (`!s c a e. bvl_get_code_labels (compile_any s c a e) SUBSET bvl_get_code_labels e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_any_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[bvl_handleProof_compile_exp_code_labels] THEN
  MP_TAC(CASE_REWRITE_RULE[] (SPECL [`c:num`; `e:bvl_exp`; `NONE:bvl_exp option`]
                                    compile_seqs_code_labels)) THEN
  REWRITE_TAC[UNION_EMPTY]);;

let optimise_get_code_labels = prove
 (`!x y (z:A#num#bvl_exp).
     bvl_get_code_labels (SND (SND (bvl_inline_optimise x y z))) SUBSET
     bvl_get_code_labels (SND (SND z))`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `z:A#num#bvl_exp` THEN
  REWRITE_TAC[optimise_eq; SND] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  QEXISTS_TAC "bvl_get_code_labels (bvl_inline_let_op_sing (bvl_inline_remove_ticks_sing z2))" THEN
  REWRITE_TAC[BVLPROPSAUX_compile_any_code_labels; let_op_sing_code_labels;
              BVLPROPSAUX_remove_ticks_sing_code_labels; SUBSET_REFL]);;


(* a local helper: the code labels of the values of a code table *)
let BVLPROPSAUX_toList_insert_labels = prove
 (`!(cs:(A#bvl_exp)spt) n a e.
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList (insert n (a,e) cs))))
     SUBSET bvl_get_code_labels e UNION
            UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; o_THM; IN_UNION; MEM_toList;
              lookup_insert; PULL_EXISTS] THEN
  RW[] THEN FS[] THEN ASM_MESON_TAC[SND]);;

let tick_inline_code_labels = prove
 (`!(cs:(A#bvl_exp)spt) xs.
     UNIONS (set_of_list (MAP bvl_get_code_labels (tick_inline cs xs))) SUBSET
     UNIONS (set_of_list (MAP bvl_get_code_labels xs)) UNION
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(!e. bvl_get_code_labels (tick_inline_sing (cs:(A#bvl_exp)spt) e) SUBSET
         bvl_get_code_labels e UNION
         UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))) /\
    (!es. UNIONS (set_of_list (MAP bvl_get_code_labels (tick_inline_list cs es))) SUBSET
          UNIONS (set_of_list (MAP bvl_get_code_labels es)) UNION
          UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs))))`
    (fun th -> REWRITE_TAC[GSYM (CONJUNCT2 tick_inline_sing); CONJUNCT2 th]) THEN
  MATCH_MP_TAC bvl_exp_INDUCT THEN REWRITE_TAC[tick_inline_sing_def] THEN REPEAT STRIP_TAC THEN
  REPEAT TOP_CASE_TAC THEN FS(mk_tick_code_labels :: BVLPROPSAUX_LABELS_RWS) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SUBSET; IN_UNION]) THEN REWRITE_TAC[SUBSET; IN_UNION] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN FS[IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; MEM_toList; PULL_EXISTS] THEN
  ASM_EXISTS_TAC THEN FS[]);;

let tick_inline_all_code_labels = prove
 (`!limit (cs:(num#bvl_exp)spt) xs aux cs1 xs1.
     tick_inline_all limit cs xs aux = (cs1,xs1) ==>
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) xs1)) SUBSET
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) xs)) UNION
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux)) UNION
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))`,
  SUBGOAL_THEN
   `!xs limit (cs:(num#bvl_exp)spt) aux cs1 xs1.
     tick_inline_all limit cs xs aux = (cs1,xs1) ==>
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) xs1)) SUBSET
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) xs)) UNION
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux)) UNION
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tick_inline_all_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC[GSYM MAP_REVERSE; LIST_TO_SET_REVERSE] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `ae:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ae:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e1:bvl_exp` SUBST1_TAC)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[tick_inline_all_eq; LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  MP_TAC(ISPECL [`cs:(num#bvl_exp)spt`; `[e1:bvl_exp]`] tick_inline_code_labels) THEN
  REWRITE_TAC[CONJUNCT1 tick_inline_sing] THEN
  SUBGOAL_THEN
   `UNIONS (set_of_list (MAP (bvl_get_code_labels o SND)
      (toList (if must_inline n limit (tick_inline_sing (cs:(num#bvl_exp)spt) e1)
               then insert n (arity,tick_inline_sing cs e1) cs else cs)))) SUBSET
    bvl_get_code_labels (tick_inline_sing cs e1) UNION
    UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))` MP_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[BVLPROPSAUX_toList_insert_labels] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC(o_THM :: BVLPROPSAUX_LABELS_RWS) THEN
  MATCH_ACCEPT_TAC(SET_RULE
   `!X B C D E F G:num->bool.
      G SUBSET B UNION F ==> B SUBSET E UNION F ==>
      X SUBSET C UNION (B UNION D) UNION G ==>
      X SUBSET (E UNION C) UNION D UNION F`));;

(* a local helper: UNIONS of a MAP is monotone in the mapped function *)
let BVLPROPSAUX_UNIONS_MAP_MONO = prove
 (`!(f:A->B->bool) g l. (!x. MEM x l ==> f x SUBSET g x) ==>
     UNIONS (set_of_list (MAP f l)) SUBSET UNIONS (set_of_list (MAP g l))`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[]);;

let bvl_inlineProof_compile_prog_get_code_labels = prove
 (`!x y z p inlines q.
     bvl_inline_compile_prog x y z p = (inlines,q) ==>
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) q)) SUBSET
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) p))`,
  REWRITE_TAC[bvl_inline_compile_prog_def; bvl_inline_compile_inc_def;
              tick_compile_prog_def] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN RW[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP tick_inline_all_code_labels) THEN
  REWRITE_TAC[toList_def; toListA_def; MAP; set_of_list; UNIONS_0; UNION_EMPTY] THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
  REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC BVLPROPSAUX_UNIONS_MAP_MONO THEN
  REWRITE_TAC[o_THM; optimise_get_code_labels]);;

(* the HOL4 [simp] theorems of this theory, registered for the files that  *)
(* load this one (the proofs above do not rely on them through the simpset) *)
let _ = cake_add_simps [HD_let_op; MAP_FST_MAP_optimise; let_op_sing_code_labels];;
