(* ========================================================================= *)
(* evaluateProps: port of HOL4 semantics/proofs/evaluatePropsScript.sml      *)
(* (CakeML v3479).  Properties of the operational semantics.                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The HOL4 type-changing record update s with ffi := nffi (s of type    *)
(*   (A)state, nffi of type (B)ffi_state) is written with the record        *)
(*   constructor, state_REC (state_clock s) (state_refs s) nffi ... (the    *)
(*   record updates of the kit keep the type).                               *)
(* - HOL4's is_clock_io_mono_if_safe, .._option_case_safe, .._match_case_   *)
(*   safe and .._match_case_pair_safe are derived with ISPEC, SPEC and       *)
(*   SIMP_RULE bool_ss []; here they are stated as the results.             *)
(* - The inductions over evaluate use their own tactics (EVPROPSAUX_..);    *)
(*   EVPROPSAUX_ names are local helpers.                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;

type_invention_error := true;;

let call_FFI_LENGTH = prove
 (`!(st:(FFI)ffi_state) index conf x new_st new_bytes.
     call_FFI st index conf x = FFI_return new_st new_bytes
     ==> LENGTH x = LENGTH new_bytes`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def] THEN
  EVERY_CASE_TAC THEN RW[] THEN ASM_REWRITE_TAC[]);;

let call_FFI_rel_def = cake_def
  `call_FFI_rel (s1:(FFI)ffi_state) s2 <=>
     ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t`;;

let call_FFI_rel_consts = prove
 (`!(s1:(FFI)ffi_state) s2.
     call_FFI_rel s1 s2 ==> ffi_state_oracle s2 = ffi_state_oracle s1`,
  REWRITE_TAC[call_FFI_rel_def; call_FFI_def] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN RW[] THEN
  SIMP[]);;

let RTC_call_FFI_rel_consts = prove
 (`!(s1:(FFI)ffi_state) s2.
     RTC call_FFI_rel s1 s2 ==> ffi_state_oracle s2 = ffi_state_oracle s1`,
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC RTC_lifts_equalities THEN
  MESON_TAC[call_FFI_rel_consts]);;

let dest_IO_event_def = cake_def
  `dest_IO_event (IO_event s c b) = (s,c,b)`;;
let _ = cake_add_simps [dest_IO_event_def];;

let io_events_mono_def = cake_def
  `io_events_mono (s1:(FFI)ffi_state) s2 <=>
     ffi_state_io_events s1 <<= ffi_state_io_events s2 /\
     (ffi_state_io_events s2 = ffi_state_io_events s1 ==> s2 = s1)`;;

let io_events_mono_refl = prove
 (`!ffi:(FFI)ffi_state. io_events_mono ffi ffi`,
  RW[io_events_mono_def; IS_PREFIX_REFL]);;
let _ = cake_add_simps [io_events_mono_refl];;

let io_events_mono_trans = prove
 (`!ffi1 ffi2 (ffi3:(FFI)ffi_state).
     io_events_mono ffi1 ffi2 /\ io_events_mono ffi2 ffi3 ==>
     io_events_mono ffi1 ffi3`,
  REWRITE_TAC[io_events_mono_def] THEN
  MESON_TAC[IS_PREFIX_TRANS; IS_PREFIX_ANTISYM]);;

let io_events_mono_antisym = prove
 (`!(s1:(FFI)ffi_state) s2.
     io_events_mono s1 s2 /\ io_events_mono s2 s1 ==> s1 = s2`,
  REWRITE_TAC[io_events_mono_def] THEN MESON_TAC[IS_PREFIX_ANTISYM]);;

let call_FFI_rel_io_events_mono = prove
 (`!(s1:(FFI)ffi_state) s2. RTC call_FFI_rel s1 s2 ==> io_events_mono s1 s2`,
  SUBGOAL_THEN `!x y:(FFI)ffi_state. call_FFI_rel x y ==> io_events_mono x y`
    ASSUME_TAC THENL
   [REWRITE_TAC[call_FFI_rel_def; call_FFI_def] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN RW[] THEN
    SIMP[io_events_mono_def; IS_PREFIX_APPEND] THEN
    DISCH_THEN(MP_TAC o AP_TERM `LENGTH:io_event list->num`) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    MATCH_MP_TAC RTC_INDUCT_R THEN REWRITE_TAC[io_events_mono_refl] THEN
    ASM_MESON_TAC[io_events_mono_trans]]);;

let do_app_call_FFI_rel = prove
 (`!r (ffi:(FFI)ffi_state) op vs r' ffi' res.
     do_app (r,ffi) op vs = SOME ((r',ffi'),res) ==> RTC call_FFI_rel ffi ffi'`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `ffi:(FFI)ffi_state = ffi'` THEN
  ASM_REWRITE_TAC[RTC_REFL] THEN MATCH_MP_TAC RTC_INC THEN
  MP_TAC(ISPECL [`r:(v store_v)list`; `ffi:(FFI)ffi_state`; `op:op`; `vs:v list`;
                 `r':(v store_v)list`; `ffi':(FFI)ffi_state`; `res:(v,v)result`]
                do_app_ffi_changed) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[call_FFI_rel_def] THEN
  MAP_EVERY EXISTS_TAC [`ExtCall s`; `MAP (\c. word (ORD c):byte) (explode conf)`;
                        `ws:byte list`; `ws':byte list`] THEN
  ASM_REWRITE_TAC[call_FFI_def; injectivity "ffiname"] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ffi_state_component_equality; ffi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The inductions over evaluate below unfold the hypothesis evaluate .. =    *)
(* (s1,res) once and split it into its cases (HOL4: every_case_tac, gvs     *)
(* [AllCaseEqs()]); the induction hypotheses are then instantiated by       *)
(* resolution with the runs found (HOL4: imp_res_tac, metis_tac).           *)
(* ------------------------------------------------------------------------- *)

let EVPROPSAUX_is_const_app names tm =
  let h,_ = strip_comb tm in is_const h && mem (fst(dest_const h)) names;;

let EVPROPSAUX_REC_RW =
  [state_INFO.ri_fupdcanon; state_INFO.ri_accfupds; state_INFO.ri_fupdfupds;
   state_INFO.ri_accessors; state_INFO.ri_fupds; K_o_THM; K_THM; dec_clock_def];;

let EVPROPSAUX_is_eval_eq tm =
  is_eq tm &&
  (let h,args = strip_comb (lhs tm) in
   is_const h &&
   (match fst(dest_const h),length args with
      ("evaluate",3) | ("evaluate_decs",3) | ("evaluate_match",5) -> true
    | _ -> false));;

let EVPROPSAUX_do_eval_res_Rval = prove
 (`!vs (s:(FFI)state) s1 env1 decs.
     do_eval_res vs s = (s1,Rval (env1,decs):(v sem_env#dec list,A)result) ==>
     ?es1. do_eval vs (state_eval_state s) = SOME (env1,decs,es1) /\
           s1 = state_eval_state_fupd (combin_K es1) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_eval_res_def] THEN
  CASES_ON `do_eval vs (state_eval_state (s:(FFI)state))` THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN REPEAT PAIRARG_TAC THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let EVPROPSAUX_do_eval_res_Rerr = prove
 (`!vs (s:(FFI)state) s1 e.
     do_eval_res vs s = (s1,Rerr e:(v sem_env#dec list,A)result) ==>
     do_eval vs (state_eval_state s) = NONE /\ s1 = s /\ e = Rabort Rtype_error`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_eval_res_def] THEN
  CASES_ON `do_eval vs (state_eval_state (s:(FFI)state))` THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN REPEAT PAIRARG_TAC THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* the do_eval facts behind the do_eval_res steps among the assumptions *)
let EVPROPSAUX_DO_EVAL_RES_TAC : tactic = fun (asl,w as gl) ->
  let facts = flat (map (fun (_,th) ->
      mapfilter (fun r -> MATCH_MP r th)
        [EVPROPSAUX_do_eval_res_Rval; EVPROPSAUX_do_eval_res_Rerr]) asl) in
  (MAP_EVERY STRIP_ASSUME_TAC facts THEN RVEQ_TAC) gl;;

(* the hypothesis evaluate .. = (s1,res) of the goal, unfolded once and     *)
(* split into its cases (without the induction hypotheses, which are then   *)
(* instantiated by resolution: much faster than GVS for the App clause)     *)
let EVPROPSAUX_APP_PRESPLIT_TAC : tactic = fun (asl,w as gl) ->
  try
    let l = lhs (lhand w) in
    let e = hd (dest_list (el 2 (snd (strip_comb l)))) in
    let c,cargs = strip_comb e in
    if fst(dest_const c) = "App" then
      (CASES_ON (mk_comb(mk_const("getOpClass",[]),hd cargs)) THEN
       RULE_ASSUM_TAC(CAKE_REWRITE_RULE[])) gl
    else ALL_TAC gl
  with Failure _ -> ALL_TAC gl;;

let EVPROPSAUX_HYP_SPLIT2_TAC thl : tactic =
  REPEAT(GEN_TAC ORELSE
         (fun (asl,w as gl) ->
            if is_imp w && not (EVPROPSAUX_is_eval_eq (lhand w))
            then DISCH_THEN STRIP_ASSUME_TAC gl else failwith "")) THEN
  EVPROPSAUX_APP_PRESPLIT_TAC THEN
  (fun (asl,w as gl) ->
     let ocs = filter (fun th -> let c = concl th in
                         is_eq c && EVPROPSAUX_is_const_app ["getOpClass"] (lhs c))
                      (map snd asl) in
     DISCH_THEN(STRIP_ASSUME_TAC o CAKE_SIMP_RULE (EVALAUX_clock_case_eqs @ ocs @ thl) o
                REWRITE_RULE ocs o ONCE_REWRITE_RULE[full_evaluate_def]) gl) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE thl) THEN RES_TAC;;

(* RTC call_FFI_rel from the RTC facts and ffi equations among the assumptions *)
let EVPROPSAUX_RTC_CLOSE_TAC : tactic = fun (asl,w as gl) ->
  let facts = filter (fun th ->
      let c = concl th in
      EVPROPSAUX_is_const_app ["RTC"] c ||
      (is_eq c && (try fst(dest_type(type_of(lhs c))) = "ffi_state"
                   with Failure _ -> false)))
    (map snd asl) in
  (REWRITE_TAC EVPROPSAUX_REC_RW THEN MESON_TAC(RTC_TRANS :: RTC_REFL :: facts)) gl;;

(* HOL4 proves this by induction on the FST form; here the induction is on  *)
(* the form with an equation evaluate .. = (s',r), from which both follow    *)

let evaluate_call_FFI_rel = prove
 (`(!(s:(FFI)state) e exp.
      RTC call_FFI_rel (state_ffi s) (state_ffi (FST (evaluate s e exp)))) /\
   (!(s:(FFI)state) e v pes errv.
      RTC call_FFI_rel (state_ffi s)
        (state_ffi (FST (evaluate_match s e v pes errv)))) /\
   (!(s:(FFI)state) e ds.
      RTC call_FFI_rel (state_ffi s) (state_ffi (FST (evaluate_decs s e ds))))`,
  SUBGOAL_THEN
   `(!(s:(FFI)state) e p s' r. evaluate s e p = (s',r) ==>
       RTC call_FFI_rel (state_ffi s) (state_ffi s')) /\
    (!(s:(FFI)state) e v pes errv s' r. evaluate_match s e v pes errv = (s',r) ==>
       RTC call_FFI_rel (state_ffi s) (state_ffi s')) /\
    (!(s:(FFI)state) e p s' r. evaluate_decs s e p = (s',r) ==>
       RTC call_FFI_rel (state_ffi s) (state_ffi s'))`
   (fun th -> MESON_TAC[th; PAIR]) THEN
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP do_app_call_FFI_rel)) THEN
  EVPROPSAUX_RTC_CLOSE_TAC);;

let evaluate_call_FFI_rel_imp = prove
 (`(!(s:(FFI)state) e p s' r.
      evaluate s e p = (s',r) ==> RTC call_FFI_rel (state_ffi s) (state_ffi s')) /\
   (!(s:(FFI)state) e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ==>
      RTC call_FFI_rel (state_ffi s) (state_ffi s')) /\
   (!(s:(FFI)state) e p s' r.
      evaluate_decs s e p = (s',r) ==> RTC call_FFI_rel (state_ffi s) (state_ffi s'))`,
  MESON_TAC[PAIR; FST; evaluate_call_FFI_rel]);;

(* HOL4 [local] *)
let evaluate_decs_call_FFI_rel = prove
 (`!(s:(FFI)state) e d.
     RTC call_FFI_rel (state_ffi s) (state_ffi (FST (evaluate_decs s e d)))`,
  REWRITE_TAC[evaluate_call_FFI_rel]);;

let evaluate_decs_call_FFI_rel_imp = prove
 (`!(s:(FFI)state) e p s' r.
     evaluate_decs s e p = (s',r) ==> RTC call_FFI_rel (state_ffi s) (state_ffi s')`,
  REWRITE_TAC[evaluate_call_FFI_rel_imp]);;

let do_app_io_events_mono = prove
 (`!r (ffi:(FFI)ffi_state) op vs r' ffi' res.
     do_app (r,ffi) op vs = SOME ((r',ffi'),res) ==> io_events_mono ffi ffi'`,
  MESON_TAC[do_app_call_FFI_rel; call_FFI_rel_io_events_mono]);;

let evaluate_io_events_mono = prove
 (`(!(s:(FFI)state) e exp.
      io_events_mono (state_ffi s) (state_ffi (FST (evaluate s e exp)))) /\
   (!(s:(FFI)state) e v pes errv.
      io_events_mono (state_ffi s) (state_ffi (FST (evaluate_match s e v pes errv)))) /\
   (!(s:(FFI)state) e d.
      io_events_mono (state_ffi s) (state_ffi (FST (evaluate_decs s e d))))`,
  MESON_TAC[evaluate_call_FFI_rel; call_FFI_rel_io_events_mono]);;

let evaluate_io_events_mono_imp = prove
 (`(!(s:(FFI)state) e p s' r.
      evaluate s e p = (s',r) ==> io_events_mono (state_ffi s) (state_ffi s')) /\
   (!(s:(FFI)state) e v pes errv s' r.
      evaluate_match s e v pes errv = (s',r) ==>
      io_events_mono (state_ffi s) (state_ffi s')) /\
   (!(s:(FFI)state) e p s' r.
      evaluate_decs s e p = (s',r) ==> io_events_mono (state_ffi s) (state_ffi s'))`,
  MESON_TAC[PAIR; FST; evaluate_io_events_mono]);;

let is_clock_io_mono_def = cake_def
  `is_clock_io_mono (f:(FFI)state->(FFI)state#(A,B)result) (s:(FFI)state) <=>
     match f s with
       (s',r) ->
         io_events_mono (state_ffi s) (state_ffi s') /\
         state_clock s' <= state_clock s /\
         state_next_type_stamp s <= state_next_type_stamp s' /\
         state_next_exn_stamp s <= state_next_exn_stamp s' /\
         LENGTH (state_refs s) <= LENGTH (state_refs s') /\
         (!clk. match f (state_clock_fupd (combin_K clk) s) with
                  (s'',r') ->
                    (~(r' = Rerr (Rabort Rtimeout_error))
                     ==> ~(r = Rerr (Rabort Rtimeout_error))
                     ==> r' = r /\
                         s'' = state_clock_fupd
                                 (combin_K (clk - (state_clock s - state_clock s'))) s') /\
                    (~(r = Rerr (Rabort Rtimeout_error))
                     ==> (clk >= state_clock s - state_clock s' <=>
                          ~(r' = Rerr (Rabort Rtimeout_error)))) /\
                    (~(r' = Rerr (Rabort Rtimeout_error))
                     ==> clk <= state_clock s
                     ==> ~(r = Rerr (Rabort Rtimeout_error))) /\
                    (clk <= state_clock s
                     ==> io_events_mono (state_ffi s'') (state_ffi s')))`;;

let is_clock_io_mono_cong = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) g s t.
     s = t ==>
     (!s. state_eval_state s = state_eval_state t /\ state_refs s = state_refs t /\
          state_ffi s = state_ffi t ==> f s = g s) ==>
     (is_clock_io_mono f s <=> is_clock_io_mono g t)`,
  SIMP[is_clock_io_mono_def]);;

let is_clock_io_mono_return = prove
 (`!(r:A) s:(FFI)state. is_clock_io_mono (\s. (s,(Rval r:(A,B)result))) s`,
  SIMP[is_clock_io_mono_def; ARITH_ss]);;

let is_clock_io_mono_err = prove
 (`!(r:(B)error_result) s:(FFI)state. is_clock_io_mono (\s. (s,(Rerr r:(A,B)result))) s`,
  SIMP[is_clock_io_mono_def; ARITH_ss]);;

let pair_CASE_eq_forall = prove
 (CASE_TERM `!(x:A#B) (P:A->B->bool).
    (match x with (a,b) -> P a b) <=> (!a b. x = (a,b) ==> P a b)`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `x:A#B` THEN SIMP[]);;

(* is_clock_io_mono with its pair cases as universal statements *)
let EVPROPSAUX_icim_ALT = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) s.
     is_clock_io_mono f s <=>
     !s' r. f s = (s',r) ==>
       io_events_mono (state_ffi s) (state_ffi s') /\
       state_clock s' <= state_clock s /\
       state_next_type_stamp s <= state_next_type_stamp s' /\
       state_next_exn_stamp s <= state_next_exn_stamp s' /\
       LENGTH (state_refs s) <= LENGTH (state_refs s') /\
       (!clk s'' r'. f (state_clock_fupd (combin_K clk) s) = (s'',r') ==>
          (~(r' = Rerr (Rabort Rtimeout_error))
           ==> ~(r = Rerr (Rabort Rtimeout_error))
           ==> r' = r /\
               s'' = state_clock_fupd (combin_K (clk - (state_clock s - state_clock s'))) s') /\
          (~(r = Rerr (Rabort Rtimeout_error))
           ==> (clk >= state_clock s - state_clock s' <=>
                ~(r' = Rerr (Rabort Rtimeout_error)))) /\
          (~(r' = Rerr (Rabort Rtimeout_error))
           ==> clk <= state_clock s
           ==> ~(r = Rerr (Rabort Rtimeout_error))) /\
          (clk <= state_clock s ==> io_events_mono (state_ffi s'') (state_ffi s')))`,
  REWRITE_TAC[is_clock_io_mono_def; pair_CASE_eq_forall]);;

(* the arithmetic facts among the assumptions, then ARITH_TAC *)
let EVPROPSAUX_ARITH_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (EVALAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* the clock arithmetic of is_clock_io_mono_bind *)
let EVPROPSAUX_bind_arith = prove
 (`!S S1 S2 clk. S2 <= S1 /\ S1 <= S /\ clk >= S - S1 ==>
     (clk - (S - S1)) - (S1 - S2) = clk - (S - S2) /\
     ((clk - (S - S1)) >= S1 - S2 <=> clk >= S - S2) /\
     (clk <= S ==> clk - (S - S1) <= S1)`,
  REPEAT STRIP_TAC THEN TRY DISCH_TAC THEN DECIDE_TAC);;

let is_clock_io_mono_bind = prove
 (CASE_TERM `!(f:(FFI)state->(FFI)state#(A,B)result)
     (g:(A,B)result->(FFI)state->(FFI)state#(C,D)result) s.
     is_clock_io_mono f s /\
     (!s' r. f s = (s',r) ==> is_clock_io_mono (g r) s') /\
     (!s'. g (Rerr (Rabort Rtimeout_error)) s' = (s',Rerr (Rabort Rtimeout_error)))
     ==> is_clock_io_mono (\s. match f s with (s',r) -> g r s') s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(f:(FFI)state->(FFI)state#(A,B)result) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(FFI)state` (X_CHOOSE_THEN `r1:(A,B)result`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `(g:(A,B)result->(FFI)state->(FFI)state#(C,D)result) r1 s1`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(FFI)state` (X_CHOOSE_THEN `r2:(C,D)result`
    ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o SPECL [`s1:(FFI)state`; `r1:(A,B)result`] o
     REWRITE_RULE[EVPROPSAUX_icim_ALT])
    (CONJUNCTS_THEN2 (MP_TAC o SPECL [`s1:(FFI)state`; `r1:(A,B)result`])
                     ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[EVPROPSAUX_icim_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`s2:(FFI)state`; `r2:(C,D)result`]) THEN
  ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_UNWIND_THM1] THEN
  REWRITE_TAC[GSYM IMP_CONJ] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[io_events_mono_trans];
    ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `clk:num` THEN
  MP_TAC(ISPEC `(f:(FFI)state->(FFI)state#(A,B)result) (state_clock_fupd (combin_K clk) s)`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(FFI)state` (X_CHOOSE_THEN `q1:(A,B)result`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  MAP_EVERY X_GEN_TAC [`t2:(FFI)state`; `q2:(C,D)result`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`clk:num`; `t1:(FFI)state`; `q1:(A,B)result`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `r1:(A,B)result = Rerr (Rabort Rtimeout_error)` THENL
   [(* the first computation timed out *)
    SUBGOAL_THEN `s2:(FFI)state = s1 /\ r2:(C,D)result = Rerr (Rabort Rtimeout_error)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(g:(A,B)result->(FFI)state->(FFI)state#(C,D)result) r1 s1 = s2,r2` THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `clk <= state_clock (s:(FFI)state)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q1:(A,B)result = Rerr (Rabort Rtimeout_error)` SUBST_ALL_TAC THENL
     [RFS[]; ALL_TAC] THEN
    UNDISCH_TAC `(g:(A,B)result->(FFI)state->(FFI)state#(C,D)result)
                   (Rerr (Rabort Rtimeout_error)) t1 = t2,q2` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    RFS[];
    ALL_TAC] THEN
  ASM_CASES_TAC `q1:(A,B)result = Rerr (Rabort Rtimeout_error)` THENL
   [(* the first computation times out with the new clock only *)
    UNDISCH_TAC `(g:(A,B)result->(FFI)state->(FFI)state#(C,D)result) q1 t1 = t2,q2` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(clk >= state_clock (s:(FFI)state) - state_clock (s1:(FFI)state))`
      ASSUME_TAC THENL [RFS[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN EVPROPSAUX_ARITH_TAC; ASM_MESON_TAC[io_events_mono_trans]];
    ALL_TAC] THEN
  (* neither times out: the second computation runs with the adjusted clock *)
  SUBGOAL_THEN `clk >= state_clock (s:(FFI)state) - state_clock (s1:(FFI)state)`
    ASSUME_TAC THENL [RFS[]; ALL_TAC] THEN
  UNDISCH_TAC `~(q1:(A,B)result = Rerr (Rabort Rtimeout_error)) /\
      ~(r1:(A,B)result = Rerr (Rabort Rtimeout_error))
      ==> q1 = r1 /\
          t1 = state_clock_fupd (combin_K (clk - (state_clock (s:(FFI)state) -
                                           state_clock (s1:(FFI)state)))) s1` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`clk - (state_clock (s:(FFI)state) -
                                        state_clock (s1:(FFI)state))`;
                                `t2:(FFI)state`; `q2:(C,D)result`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `clk - (state_clock (s:(FFI)state) - state_clock (s1:(FFI)state)) -
                (state_clock s1 - state_clock (s2:(FFI)state)) =
                clk - (state_clock s - state_clock s2) /\
                (clk - (state_clock s - state_clock s1) >= state_clock s1 - state_clock s2
                 <=> clk >= state_clock s - state_clock s2) /\
                (clk <= state_clock s ==> clk - (state_clock s - state_clock s1) <=
                                          state_clock s1)`
    STRIP_ASSUME_TAC THENL [MATCH_MP_TAC EVPROPSAUX_bind_arith THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RFS[]);;

let adj_clock_def = cake_def
  `adj_clock inc dec (s:(FFI)state) =
     state_clock_fupd (combin_K ((state_clock s + inc) - dec)) s`;;

(* the clock arithmetic of is_clock_io_mono_check *)
let EVPROPSAUX_check_arith = prove
 (`(!k c x. 1 <= k /\ x + 1 <= c ==> (k - 1) - ((c - 1) - x) = k - (c - x)) /\
   (!k c x. ~(k = 0) /\ x <= c - 1 ==> ((k - 1) >= (c - 1) - x <=> k >= c - x))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN DECIDE_TAC);;

let is_clock_io_mono_check = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) s.
     (~(state_clock s = 0) ==>
      is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
     ==> is_clock_io_mono (\s. if state_clock s = 0
                               then (s,Rerr (Rabort Rtimeout_error)) else f s) s`,
  REPEAT GEN_TAC THEN SIMP[is_clock_io_mono_def; dec_clock_def; adj_clock_def; with_same_clock] THEN
  REPEAT (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE
          CHANGED_TAC (RFS[ARITH_ss; with_same_clock; SUB_ADD])) THEN
  FIRST_X_ASSUM (QSPEC_THEN "clk - 1" MP_TAC) THEN SIMP[ARITH_ss; SUB_ADD] THEN
  REPEAT (CASE_TAC ORELSE DISCH_TAC ORELSE GEN_TAC ORELSE
          CHANGED_TAC (RFS[ARITH_ss; SUB_ADD; EVPROPSAUX_check_arith])) THEN
  FS[ARITH_ss; EVPROPSAUX_check_arith]);;

let dec_inc_clock = prove
 (`!s:(FFI)state. dec_clock (adj_clock 1 0 s) = s`,
  REWRITE_TAC[dec_clock_def; adj_clock_def; state_INFO.ri_fupdfupds; K_o_THM;
              state_INFO.ri_accfupds; K_THM; ADD_SUB; SUB_0; with_same_clock]);;

let do_app_refs_length = prove
 (`!(refs_ffi:(v store_v)list#(FFI)ffi_state) op vs res.
     do_app refs_ffi op vs = SOME res ==>
     LENGTH (FST refs_ffi) <= LENGTH (FST (FST res))`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `refs_ffi:(v store_v)list#(FFI)ffi_state` THEN
  PAIR_CASES_ON `res:((v store_v)list#(FFI)ffi_state)#(v,v)result` THEN
  PAIR_CASES_ON `res0:(v store_v)list#(FFI)ffi_state` THEN
  REWRITE_TAC[FST; do_app_cases] THEN
  RW[] THEN GVS([thunk_op_def; store_alloc_def; store_assign_def; sum_case_eq;
                 case_eq "ffi_result"; case_eq "thunk_op"; case_eq "thunk_mode"] @
                EVALAUX_do_app_eqs) THEN
  REWRITE_TAC[LENGTH_LUPDATE; LENGTH_APPEND; LE_REFL; LE_ADD]);;

(* a computation that only changes fields other than the clock, and in a    *)
(* way that does not depend on the clock                                     *)
let EVPROPSAUX_is_clock_io_mono_leaf = prove
 (`!(h:(FFI)state->(FFI)state) (r:(A,B)result) s.
     (!clk x. h (state_clock_fupd (combin_K clk) x) = state_clock_fupd (combin_K clk) (h x)) /\
     (!x. state_clock (h x) = state_clock x) /\
     io_events_mono (state_ffi s) (state_ffi (h s)) /\
     state_next_type_stamp s <= state_next_type_stamp (h s) /\
     state_next_exn_stamp s <= state_next_exn_stamp (h s) /\
     LENGTH (state_refs s) <= LENGTH (state_refs (h s))
     ==> is_clock_io_mono (\x. (h x,r)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[is_clock_io_mono_def; pair_CASE; LE_REFL; SUB_REFL; SUB_0; GE; LE_0;
                  state_INFO.ri_accfupds; state_INFO.ri_fupdfupds; K_o_THM; K_THM;
                  io_events_mono_refl] THEN
  MESON_TAC[]);;

(* functions that agree at s with every clock are interchangeable *)
let EVPROPSAUX_cong_ext = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) g s.
     (!clk. f (state_clock_fupd (combin_K clk) s) = g (state_clock_fupd (combin_K clk) s))
     ==> (is_clock_io_mono f s <=> is_clock_io_mono g s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:(FFI)state->(FFI)state#(A,B)result) s = g s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `state_clock (s:(FFI)state)`) THEN
    REWRITE_TAC[with_same_clock];
    ASM_REWRITE_TAC[is_clock_io_mono_def]]);;

(* in is_clock_io_mono (\x. B[x]) s0, the fields of x other than the clock  *)
(* are those of s0 (the generalisation of HOL4's Cong is_clock_io_mono_cong *)
(* to all fields other than the clock)                                       *)
let EVPROPSAUX_CONG_TAC : tactic = fun (asl,w as gl) ->
  let ic,args = strip_comb w in
  if not (is_const ic && fst(dest_const ic) = "is_clock_io_mono" &&
          length args = 2) then failwith "EVPROPSAUX_CONG_TAC" else
  let f = hd args and s0 = el 1 args in
  let x0,b0 = dest_abs f in
  (* a bound variable apart from s0, so that the replacement is not captured *)
  let x = variant (frees w) x0 in
  let b = vsubst [x,x0] b0 in
  let tms = filter (fun t -> free_in t b)
              (map (fun n -> mk_icomb(mk_const(n,[]),x))
                   ["state_refs"; "state_ffi"; "state_eval_state";
                    "state_next_type_stamp"; "state_next_exn_stamp"]) in
  if tms = [] then failwith "EVPROPSAUX_CONG_TAC: nothing to do" else
  let g = mk_abs(x,subst (map (fun t -> mk_comb(rator t,s0),t) tms) b) in
  let th1 = ISPECL [f; g; s0] EVPROPSAUX_cong_ext in
  let pth = prove(lhand(concl th1),
                  GEN_TAC THEN BETA_TAC THEN REWRITE_TAC[state_INFO.ri_accfupds]) in
  (GEN_REWRITE_TAC I [MP th1 pth]) gl;;

let is_clock_io_mono_do_app_simple = prove
 (CASE_TERM `!xs (st:(FFI)state).
    is_clock_io_mono (\st'.
      match do_app (state_refs st',state_ffi st') op xs with
        NONE -> (st',Rerr (Rabort Rtype_error))
      | SOME ((refs,ffi),r) ->
          (state_refs_fupd (combin_K refs) (state_ffi_fupd (combin_K ffi) st'),list_result r)) st`,
  REPEAT GEN_TAC THEN EVPROPSAUX_CONG_TAC THEN
  CASES_ON `do_app (state_refs (st:(FFI)state),state_ffi st) op xs` THEN
  ASM_REWRITE_TAC[option_CASE; is_clock_io_mono_err] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`a:((v store_v)list#(FFI)ffi_state)#(v,v)result`,
           `a:((v store_v)list#(FFI)ffi_state)#(v,v)result`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC EVPROPSAUX_is_clock_io_mono_leaf THEN
  REWRITE_TAC[state_INFO.ri_fupdcanon; state_INFO.ri_accfupds; K_THM; LE_REFL] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[do_app_io_events_mono];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP do_app_refs_length) THEN REWRITE_TAC[FST]]);;

let is_clock_io_mono_acc_safe = prove
 (`!(f:(FFI)state->X) st v (g:X->(FFI)state->(FFI)state#(A,B)result).
     (!st clk. f (state_clock_fupd (combin_K clk) st) = f st) /\
     (f st = v \/ ~(f st = v)) /\
     is_clock_io_mono (\st'. g (f st) st') st ==>
     is_clock_io_mono (\st'. g (f st') st') st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_REWRITE_TAC[is_clock_io_mono_def]);;

(* HOL4 derives the next four from is_clock_io_mono_acc_safe with ISPEC,    *)
(* SPEC and SIMP_RULE bool_ss []; here they are stated as the result         *)

let is_clock_io_mono_if_safe = prove
 (`!(f:(FFI)state->bool) st (j:(FFI)state->(FFI)state#(A,B)result) k.
     (!st clk. f (state_clock_fupd (combin_K clk) st) = f st) /\
     is_clock_io_mono (\st'. if f st then j st' else k st') st ==>
     is_clock_io_mono (\st'. if f st' then j st' else k st') st`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(FFI)state->bool`; `st:(FFI)state`; `T`;
                 `\b (st:(FFI)state). if b then (j:(FFI)state->(FFI)state#(A,B)result) st
                                      else k st`] is_clock_io_mono_acc_safe) THEN
  ASM_REWRITE_TAC[EXCLUDED_MIDDLE]);;

let is_clock_io_mono_option_case_safe = prove
 (CASE_TERM `!(f:(FFI)state->X option) st (g:(FFI)state->(FFI)state#(A,B)result) h.
     (!st clk. f (state_clock_fupd (combin_K clk) st) = f st) /\
     is_clock_io_mono (\st'. match f st with NONE -> g st' | SOME x -> h x st') st ==>
     is_clock_io_mono (\st'. match f st' with NONE -> g st' | SOME x -> h x st') st`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(FFI)state->X option`; `st:(FFI)state`; `NONE:X option`;
                 CASE_TERM `\(v:X option) (st:(FFI)state).
                   match v with NONE -> (g:(FFI)state->(FFI)state#(A,B)result) st
                              | SOME (x:X) ->
                                  (h:X->(FFI)state->(FFI)state#(A,B)result) x st`]
                is_clock_io_mono_acc_safe) THEN
  ASM_REWRITE_TAC[EXCLUDED_MIDDLE]);;

let is_clock_io_mono_match_case_safe = prove
 (CASE_TERM `!(f:(FFI)state->(X)match_result) st
     (g:(FFI)state->(FFI)state#(A,B)result) h j.
     (!st clk. f (state_clock_fupd (combin_K clk) st) = f st) /\
     is_clock_io_mono (\st'. match f st with
                               No_match -> g st'
                             | Match_type_error -> h st'
                             | Match env -> j env st') st ==>
     is_clock_io_mono (\st'. match f st' with
                               No_match -> g st'
                             | Match_type_error -> h st'
                             | Match env -> j env st') st`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(FFI)state->(X)match_result`; `st:(FFI)state`;
                 `No_match:(X)match_result`;
                 CASE_TERM `\(m:(X)match_result) (st:(FFI)state).
                   match m with
                     No_match -> (g:(FFI)state->(FFI)state#(A,B)result) st
                   | Match_type_error -> (h:(FFI)state->(FFI)state#(A,B)result) st
                   | Match (env:X) ->
                       (j:X->(FFI)state->(FFI)state#(A,B)result) env st`]
                is_clock_io_mono_acc_safe) THEN
  ASM_REWRITE_TAC[EXCLUDED_MIDDLE]);;

let is_clock_io_mono_match_case_pair_safe = prove
 (CASE_TERM `!(f:(FFI)state->(X)match_result) st
     (g:(FFI)state->(A,B)result) h j.
     (!st clk. f (state_clock_fupd (combin_K clk) st) = f st) /\
     is_clock_io_mono (\st'. (st',match f st with
                                    No_match -> g st'
                                  | Match_type_error -> h st'
                                  | Match env -> j env st')) st ==>
     is_clock_io_mono (\st'. (st',match f st' with
                                    No_match -> g st'
                                  | Match_type_error -> h st'
                                  | Match env -> j env st')) st`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(FFI)state->(X)match_result`; `st:(FFI)state`;
                 `No_match:(X)match_result`;
                 CASE_TERM `\(m:(X)match_result) (st:(FFI)state).
                   (st,match m with
                         No_match -> (g:(FFI)state->(A,B)result) st
                       | Match_type_error -> (h:(FFI)state->(A,B)result) st
                       | Match (env:X) -> (j:X->(FFI)state->(A,B)result) env st)`]
                is_clock_io_mono_acc_safe) THEN
  ASM_REWRITE_TAC[EXCLUDED_MIDDLE]);;

let EVPROPSAUX_update_thunk_LENGTH = prove
 (`!vs (st:(v store_v)list) vs2 refs.
     update_thunk vs st vs2 = SOME refs ==> LENGTH refs = LENGTH st`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vs:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `h:v` (nchotomy_of_type `:v`)) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `t:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  GEN_TAC THEN X_GEN_TAC `vs2:v list` THEN
  STRUCT_CASES_TAC(ISPEC `vs2:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `t:v list` list_CASES) THEN
  REWRITE_TAC[update_thunk_def; option_DISTINCT] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASE_TAC THEN REWRITE_TAC[option_DISTINCT; store_assign_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH_LUPDATE]);;

(* ------------------------------------------------------------------------- *)
(* The step tactic of the proof of is_clock_io_mono_evaluate (HOL4 step_tac: *)
(* strip, is_clock_io_mono_bind, is_clock_io_mono_check, fs with the         *)
(* congruence rule is_clock_io_mono_cong, return, err, dec_inc_clock, and    *)
(* TOP_CASE_TAC), applied by the shape of the goal.                         *)
(* ------------------------------------------------------------------------- *)

let EVPROPSAUX_dest_icim w =
  let h,args = strip_comb w in
  if is_const h && fst(dest_const h) = "is_clock_io_mono" && length args = 2
  then hd args,el 1 args else failwith "EVPROPSAUX_dest_icim";;

(* the leaves: final states that change fields other than the clock *)
let EVPROPSAUX_LEAF_TAC : tactic =
  MATCH_MP_TAC EVPROPSAUX_is_clock_io_mono_leaf THEN BETA_TAC THEN
  REWRITE_TAC[state_INFO.ri_fupdcanon; state_INFO.ri_accfupds; K_THM; LE_REFL; LE_ADD;
              io_events_mono_refl] THEN
  ASM_MESON_TAC[EVPROPSAUX_update_thunk_LENGTH; LE_REFL];;

let EVPROPSAUX_icim_do_eval_res = prove
 (`!vs (s:(FFI)state).
     is_clock_io_mono (\s. do_eval_res vs s:(FFI)state#(v sem_env#dec list,A)result) s`,
  REWRITE_TAC[do_eval_res_def] THEN REPEAT GEN_TAC THEN EVPROPSAUX_CONG_TAC THEN
  TOP_CASE_TAC THEN REWRITE_TAC[is_clock_io_mono_err] THEN
  REPEAT TOP_CASE_TAC THEN EVPROPSAUX_LEAF_TAC);;

let EVPROPSAUX_ICIM_TAC : tactic = fun (asl,w as gl) ->
  let f,s0 = EVPROPSAUX_dest_icim w in
  if not (is_abs f) then CHANGED_TAC BETA_TAC gl else
  let x,b = dest_abs f in
  let scrut_has_x t = try free_in x (scrutinee_of t) with Failure _ -> false in
  let fallback = FIRST [TOP_CASE_TAC; EVPROPSAUX_CONG_TAC; EVPROPSAUX_LEAF_TAC] in
  if is_pair b && fst(dest_pair b) = x &&
     not (free_in x (snd(dest_pair b))) then
    FIRST [MATCH_ACCEPT_TAC is_clock_io_mono_return;
           MATCH_ACCEPT_TAC is_clock_io_mono_err; fallback] gl
  else if EVPROPSAUX_is_const_app ["do_eval_res"] b then
    MATCH_ACCEPT_TAC EVPROPSAUX_icim_do_eval_res gl
  else if EVPROPSAUX_is_const_app ["evaluate"; "evaluate_match"; "evaluate_decs"] b then
    (FIRST_ASSUM MATCH_ACCEPT_TAC ORELSE ASM_MESON_TAC[]) gl
  else if is_case_app b && scrut_has_x b &&
          EVPROPSAUX_is_const_app ["do_app"] (scrutinee_of b) then
    (MATCH_ACCEPT_TAC is_clock_io_mono_do_app_simple ORELSE fallback) gl
  else if is_case_app b && scrut_has_x b &&
          EVPROPSAUX_is_const_app ["pair_CASE"] b then
    ((MATCH_MP_TAC is_clock_io_mono_bind THEN BETA_TAC) ORELSE fallback) gl
  else if is_cond b && is_eq (scrutinee_of b) &&
          lhs (scrutinee_of b) = mk_icomb(mk_const("state_clock",[]),x) then
    (MATCH_MP_TAC is_clock_io_mono_check THEN BETA_TAC THEN
     REWRITE_TAC[dec_inc_clock]) gl
  else fallback gl;;

let EVPROPSAUX_STEP_TAC : tactic =
  REPEAT(FIRST
   [CONJ_TAC; GEN_TAC; DISCH_TAC;
    EVPROPSAUX_ICIM_TAC;
    CHANGED_TAC(CAKE_REWRITE_TAC[combine_dec_result_def])]);;

let is_clock_io_mono_evaluate = prove
 (`(!(s:(FFI)state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s:(FFI)state) env v pes err_v.
      is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s:(FFI)state) env ds. is_clock_io_mono (\s. evaluate_decs s env ds) s)`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[full_evaluate_def; combine_dec_result_def] THEN EVPROPSAUX_STEP_TAC);;

let is_clock_io_mono_evaluate_decs = prove
 (`!(s:(FFI)state) e p. is_clock_io_mono (\s. evaluate_decs s e p) s`,
  REWRITE_TAC[is_clock_io_mono_evaluate]);;

let is_clock_io_mono_extra = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) s s' r extra.
     (!s. is_clock_io_mono f s)
     ==> f s = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error))
     ==> f (state_clock_fupd (combin_K (state_clock s + extra)) s) =
         (state_clock_fupd (combin_K (state_clock s' + extra)) s',r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM (QSPEC_THEN "state_clock_fupd (combin_K (state_clock s + extra)) s" MP_TAC) THEN
  SIMP[is_clock_io_mono_def] THEN CASE_TAC THEN REPEAT (DISCH_TAC ORELSE GEN_TAC) THEN FS[] THEN
  FIRST_X_ASSUM (QSPEC_THEN "state_clock s" MP_TAC) THEN FS[with_same_clock] THEN
  REPEAT DISCH_TAC THEN
  FS[with_same_clock; ARITH_RULE `!S e X. X <= S + e /\ S >= (S + e) - X ==>
                                          S - ((S + e) - X) + e = X`]);;

let is_clock_io_mono_extra_mono = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) s extra.
     (!s. is_clock_io_mono f s)
     ==> io_events_mono (state_ffi (FST (f s)))
           (state_ffi (FST (f (state_clock_fupd (combin_K (state_clock s + extra)) s))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM (QSPEC_THEN "state_clock_fupd (combin_K (state_clock s + extra)) s" MP_TAC) THEN
  SIMP[is_clock_io_mono_def] THEN CASE_TAC THEN REPEAT (DISCH_TAC ORELSE GEN_TAC) THEN FS[] THEN
  FIRST_X_ASSUM (QSPEC_THEN "state_clock s" MP_TAC) THEN FS[with_same_clock] THEN
  CASE_TAC THEN SIMP[]);;

(* HOL4 mk_extra_lemmas / prove_extra: the rule applied to each conjunct of *)
(* is_clock_io_mono_evaluate                                                 *)
let EVPROPSAUX_extra_lemmas mp_rule monad_rule =
  map (BETA_RULE o MATCH_MP mp_rule o GEN `s:(FFI)state` o SPEC_ALL)
      (CONJUNCTS monad_rule);;

let evaluate_add_to_clock = prove
 (`!(s:(FFI)state) env es s' r extra.
     evaluate s env es = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
     evaluate (state_clock_fupd (combin_K (state_clock s + extra)) s) env es =
     (state_clock_fupd (combin_K (state_clock s' + extra)) s',r)`,
  MESON_TAC(EVPROPSAUX_extra_lemmas is_clock_io_mono_extra is_clock_io_mono_evaluate));;

let evaluate_match_add_to_clock = prove
 (`!(s:(FFI)state) env v pes err_v s' r extra.
     evaluate_match s env v pes err_v = (s',r) /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     evaluate_match (state_clock_fupd (combin_K (state_clock s + extra)) s) env v pes err_v =
     (state_clock_fupd (combin_K (state_clock s' + extra)) s',r)`,
  MESON_TAC(EVPROPSAUX_extra_lemmas is_clock_io_mono_extra is_clock_io_mono_evaluate));;

let list_result_eq_Rval = prove
 (`!(r:(A,B)result) r'. list_result r = Rval r' <=> ?v. r' = [v] /\ r = Rval v`,
  GEN_TAC THEN CASES_ON `r:(A,B)result` THEN
  REWRITE_TAC[list_result_def; injectivity "result"; distinctness "result"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [list_result_eq_Rval];;

let list_result_eq_Rerr = prove
 (`!(r:(A,B)result) e. list_result r = Rerr e <=> r = Rerr e`,
  GEN_TAC THEN CASES_ON `r:(A,B)result` THEN
  REWRITE_TAC[list_result_def; injectivity "result"; distinctness "result"]);;
let _ = cake_add_simps [list_result_eq_Rerr];;

let result_rel_list_result = prove
 (`!(R:A->B->bool) (Q:C->D->bool) r1 r2.
     result_rel (ALL2 R) Q (list_result r1) (list_result r2) <=> result_rel R Q r1 r2`,
  REPEAT GEN_TAC THEN CASES_ON `r1:(A,C)result` THEN CASES_ON `r2:(B,D)result` THEN
  REWRITE_TAC[list_result_def; result_rel_def; ALL2]);;
let _ = cake_add_simps [result_rel_list_result];;

let list_result_inj = prove
 (`!(x:(A,B)result) y. list_result x = list_result y ==> x = y`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `x:(A,B)result` THEN CASES_ON `y:(A,B)result` THEN
  REWRITE_TAC[list_result_def; injectivity "result"; distinctness "result"; CONS_11] THEN
  MESON_TAC[]);;

let evaluate_length = prove
 (`(!(s:(FFI)state) e p s' r. evaluate s e p = (s',Rval r) ==> LENGTH r = LENGTH p) /\
   (!(s:(FFI)state) e v p er s' r.
      evaluate_match s e v p er = (s',Rval r) ==> LENGTH r = 1) /\
   (!(s:(FFI)state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ==> T)`,
  MATCH_MP_TAC full_evaluate_ind THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  ASM_REWRITE_TAC[LENGTH; ONE]);;

let evaluate_nil = prove
 (`!(s:(FFI)state) env. evaluate s env [] = (s,Rval [])`,
  REWRITE_TAC[evaluate_def]);;
let _ = cake_add_simps [evaluate_nil];;

let evaluate_sing = prove
 (`!(s:(FFI)state) env e s' vs. evaluate s env [e] = (s',Rval vs) ==> ?v. vs = [v]`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 evaluate_length)) THEN
  STRUCT_CASES_TAC(ISPEC `vs:v list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL; CONS_11] THEN MESON_TAC[]);;

let evaluate_cons = prove
 (CASE_TERM `!(s:(FFI)state) env e es.
    evaluate s env (CONS e es) =
    match evaluate s env [e] with
      (s',Rval vs) ->
        (match evaluate s' env es with
           (s'',Rval vs') -> (s'',Rval (APPEND vs vs'))
         | err -> err)
    | err -> err`,
  REPEAT GEN_TAC THEN CASES_ON `es:exp list` THEN SIMP[evaluate_def] THEN
  REPEAT TOP_CASE_TAC THEN IMP_RES_TAC evaluate_sing THEN FS[]);;

let evaluate_append = prove
 (CASE_TERM `!(s:(FFI)state) env xs ys.
    evaluate s env (APPEND xs ys) =
    match evaluate s env xs with
      (s',Rval vs) ->
        (match evaluate s' env ys with
           (s'',Rval vs') -> (s'',Rval (APPEND vs vs'))
         | err -> err)
    | err -> err`,
  SUBGOAL_THEN (CASE_TERM `!xs (s:(FFI)state) env ys.
    evaluate s env (APPEND xs ys) =
    match evaluate s env xs with
      (s',Rval vs) ->
        (match evaluate s' env ys with
           (s'',Rval vs') -> (s'',Rval (APPEND vs vs'))
         | err -> err)
    | err -> err`) (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN SIMP[APPEND] THEN REPEAT GEN_TAC THENL
   [REPEAT TOP_CASE_TAC;
    ONCE_REWRITE_TAC[evaluate_cons] THEN ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN
    FS[APPEND_ASSOC]]);;

let evaluate_decs_nil = prove
 (`!(s:(FFI)state) env.
     evaluate_decs s env [] = (s,Rval (sem_env_REC nsEmpty nsEmpty))`,
  REWRITE_TAC[evaluate_decs_def]);;
let _ = cake_add_simps [evaluate_decs_nil];;

let evaluate_decs_cons = prove
 (CASE_TERM `!(s:(FFI)state) env d ds.
    evaluate_decs s env (CONS d ds) =
    match evaluate_decs s env [d] with
      (s1,Rval env1) ->
        (match evaluate_decs s1 (extend_dec_env env1 env) ds with
           (s2,r) -> (s2,combine_dec_result env1 r))
    | err -> err`,
  REPEAT GEN_TAC THEN CASES_ON `ds:dec list` THEN SIMP[evaluate_decs_def] THEN
  REPEAT TOP_CASE_TAC THEN SIMP[combine_dec_result_def; sem_env_component_equality]);;

let evaluate_decs_append = prove
 (CASE_TERM `!ds1 (s:(FFI)state) env ds2.
    evaluate_decs s env (APPEND ds1 ds2) =
    match evaluate_decs s env ds1 with
      (s1,Rval env1) ->
        (match evaluate_decs s1 (extend_dec_env env1 env) ds2 with
           (s2,r) -> (s2,combine_dec_result env1 r))
    | (s1,Rerr v7) -> (s1,Rerr v7)`,
  LIST_INDUCT_TAC THEN RW[APPEND] THENL
   [RW[extend_dec_env_def; combine_dec_result_def] THEN REPEAT CASE_TAC THEN
    SIMP[sem_env_component_equality];
    ONCE_REWRITE_TAC[evaluate_decs_cons] THEN SIMP[] THEN
    FS[combine_dec_result_def; extend_dec_env_def] THEN REPEAT CASE_TAC THEN FS[nsAppend_assoc]]);;

let evaluate_match_list_result = prove
 (`!(s:(FFI)state) e v p er s' r.
     evaluate_match s e v p er = (s',r) ==> ?r'. r = list_result r'`,
  REPEAT GEN_TAC THEN CASES_ON `r:(v list,v)result` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1(CONJUNCT2 evaluate_length))) THEN
    STRUCT_CASES_TAC(ISPEC `a:v list` list_CASES) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 1) /\ (SUC n = 1 <=> n = 0)`; LENGTH_EQ_NIL] THEN
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `Rval h:(v,v)result`;
    EXISTS_TAC `Rerr a:(v,v)result`] THEN
  REWRITE_TAC[list_result_def]);;

let evaluate_decs_add_to_clock = prove
 (`!(s:(FFI)state) e p s' r extra.
     evaluate_decs s e p = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
     evaluate_decs (state_clock_fupd (combin_K (state_clock s + extra)) s) e p =
     (state_clock_fupd (combin_K (state_clock s' + extra)) s',r)`,
  MESON_TAC(EVPROPSAUX_extra_lemmas is_clock_io_mono_extra
              is_clock_io_mono_evaluate_decs));;

(* HOL4 [local] *)
let add_lemma = prove
 (`!(k:num) k'. ?extra. k = k' + extra \/ k' = k + extra`,
  MESON_TAC[LE_EXISTS; LE_CASES]);;

(* HOL4 [local] *)
let with_clock_ffi = prove
 (`!(s:(FFI)state) k. state_ffi (state_clock_fupd (combin_K k) s) = state_ffi s`,
  REWRITE_TAC[state_INFO.ri_accfupds]);;

let EVPROPSAUX_decs_clock_le = prove
 (`!(s:(FFI)state) e p k1 k2 s1 r1 s2 r2.
     evaluate_decs (state_clock_fupd (combin_K k1) s) e p = (s1,r1) /\
     evaluate_decs (state_clock_fupd (combin_K k2) s) e p = (s2,r2) /\
     ~(r1 = Rerr (Rabort Rtimeout_error)) /\ k1 <= k2
     ==> r2 = r1 /\ state_ffi s2 = state_ffi s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`state_clock_fupd (combin_K k1) (s:(FFI)state)`; `e:v sem_env`; `p:dec list`;
                `s1:(FFI)state`; `r1:(v sem_env,v)result`; `d:num`]
               evaluate_decs_add_to_clock) THEN
  ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM;
                  PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[state_INFO.ri_accfupds]);;

let evaluate_decs_clock_determ = prove
 (CASE_TERM `!s e p s1 r1 s2 r2 k1 k2.
    evaluate_decs (state_clock_fupd (combin_K k1) (s:(FFI)state)) e p = (s1,r1) /\
    evaluate_decs (state_clock_fupd (combin_K k2) s) e p = (s2,r2)
    ==>
    match (r1,r2) with
      (Rerr (Rabort Rtimeout_error),Rerr (Rabort Rtimeout_error)) -> T
    | (Rerr (Rabort Rtimeout_error),_) -> k1 < k2
    | (_,Rerr (Rabort Rtimeout_error)) -> k2 < k1
    | _ -> state_ffi s1 = state_ffi s2 /\ r1 = r2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(~(r1 = Rerr (Rabort Rtimeout_error)) /\ ~(r2 = Rerr (Rabort Rtimeout_error))
     ==> state_ffi s1 = state_ffi (s2:(FFI)state) /\ r1:(v sem_env,v)result = r2) /\
    (r1 = Rerr (Rabort Rtimeout_error) /\ ~(r2 = Rerr (Rabort Rtimeout_error))
     ==> k1 < k2) /\
    (~(r1 = Rerr (Rabort Rtimeout_error)) /\ r2 = Rerr (Rabort Rtimeout_error)
     ==> k2 < k1)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN STRIP_TAC THENL
     [DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
      ASM_MESON_TAC[EVPROPSAUX_decs_clock_le];
      REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`s:(FFI)state`; `e:v sem_env`; `p:dec list`; `k2:num`; `k1:num`;
                    `s2:(FFI)state`; `r2:(v sem_env,v)result`; `s1:(FFI)state`;
                    `r1:(v sem_env,v)result`] EVPROPSAUX_decs_clock_le) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`s:(FFI)state`; `e:v sem_env`; `p:dec list`; `k1:num`; `k2:num`;
                    `s1:(FFI)state`; `r1:(v sem_env,v)result`; `s2:(FFI)state`;
                    `r2:(v sem_env,v)result`] EVPROPSAUX_decs_clock_le) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN
    CASES_ON `r1:(v sem_env,v)result` THEN CASES_ON `r2:(v sem_env,v)result` THEN
    REPEAT CASE_TAC THEN
    REWRITE_TAC[distinctness "result"; distinctness "error_result";
                distinctness "abort"; injectivity "result";
                injectivity "error_result"] THEN MESON_TAC[]]);;

let evaluate_add_to_clock_io_events_mono = prove
 (`(!(s:(FFI)state) e d extra.
      io_events_mono (state_ffi (FST (evaluate s e d)))
        (state_ffi (FST (evaluate (state_clock_fupd (combin_K (state_clock s + extra)) s) e d)))) /\
   (!(s:(FFI)state) e v d er extra.
      io_events_mono (state_ffi (FST (evaluate_match s e v d er)))
        (state_ffi (FST (evaluate_match (state_clock_fupd (combin_K (state_clock s + extra)) s)
                           e v d er))))`,
  MESON_TAC(EVPROPSAUX_extra_lemmas is_clock_io_mono_extra_mono
              is_clock_io_mono_evaluate));;

let evaluate_decs_add_to_clock_io_events_mono = prove
 (`!(s:(FFI)state) e d.
     io_events_mono (state_ffi (FST (evaluate_decs s e d)))
       (state_ffi (FST (evaluate_decs (state_clock_fupd (combin_K (state_clock s + extra)) s)
                          e d)))`,
  MESON_TAC(EVPROPSAUX_extra_lemmas is_clock_io_mono_extra_mono
              is_clock_io_mono_evaluate_decs));;

let evaluate_decs_ffi_mono_clock = prove
 (`!k1 k2 (s:(FFI)state) e p.
     k1 <= k2 ==>
     io_events_mono (state_ffi (FST (evaluate_decs (state_clock_fupd (combin_K k1) s) e p)))
       (state_ffi (FST (evaluate_decs (state_clock_fupd (combin_K k2) s) e p)))`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["state_clock_fupd (combin_K k2) s"; "e"; "p"] MP_TAC is_clock_io_mono_evaluate_decs THEN
  SIMP[is_clock_io_mono_def] THEN CASE_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (QSPEC_THEN "k1" MP_TAC) THEN CASE_TAC THEN FS[]);;

(* HOL4: evaluate_state_unchanged is commented out in the script (no longer *)
(* true because of Eval)                                                     *)

(* the first five facts of is_clock_io_mono for one run *)
let EVPROPSAUX_icim_part1 = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) s s' r.
     is_clock_io_mono f s /\ f s = (s',r) ==>
     io_events_mono (state_ffi s) (state_ffi s') /\
     state_clock s' <= state_clock s /\
     state_next_type_stamp s <= state_next_type_stamp s' /\
     state_next_exn_stamp s <= state_next_exn_stamp s' /\
     LENGTH (state_refs s) <= LENGTH (state_refs s')`,
  REWRITE_TAC[EVPROPSAUX_icim_ALT] THEN MESON_TAC[]);;

let EVPROPSAUX_evaluate_mono = prove
 (`(!(s:(FFI)state) env es s' r.
      evaluate s env es = (s',r) ==>
      io_events_mono (state_ffi s) (state_ffi s') /\
      state_clock s' <= state_clock s /\
      state_next_type_stamp s <= state_next_type_stamp s' /\
      state_next_exn_stamp s <= state_next_exn_stamp s' /\
      LENGTH (state_refs s) <= LENGTH (state_refs s')) /\
   (!(s:(FFI)state) env v pes err_v s' r.
      evaluate_match s env v pes err_v = (s',r) ==>
      io_events_mono (state_ffi s) (state_ffi s') /\
      state_clock s' <= state_clock s /\
      state_next_type_stamp s <= state_next_type_stamp s' /\
      state_next_exn_stamp s <= state_next_exn_stamp s' /\
      LENGTH (state_refs s) <= LENGTH (state_refs s')) /\
   (!(s:(FFI)state) env ds s' r.
      evaluate_decs s env ds = (s',r) ==>
      io_events_mono (state_ffi s) (state_ffi s') /\
      state_clock s' <= state_clock s /\
      state_next_type_stamp s <= state_next_type_stamp s' /\
      state_next_exn_stamp s <= state_next_exn_stamp s' /\
      LENGTH (state_refs s) <= LENGTH (state_refs s'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`\s:(FFI)state. evaluate s env es`; `s:(FFI)state`; `s':(FFI)state`;
                   `r:(v list,v)result`] EVPROPSAUX_icim_part1);
    MP_TAC(ISPECL [`\s:(FFI)state. evaluate_match s env v pes err_v`; `s:(FFI)state`;
                   `s':(FFI)state`; `r:(v list,v)result`] EVPROPSAUX_icim_part1);
    MP_TAC(ISPECL [`\s:(FFI)state. evaluate_decs s env ds`; `s:(FFI)state`;
                   `s':(FFI)state`; `r:(v sem_env,v)result`] EVPROPSAUX_icim_part1)] THEN
  ASM_REWRITE_TAC[is_clock_io_mono_evaluate]);;

let evaluate_next_type_stamp_mono = prove
 (`(evaluate (s:(FFI)state) env es = (s',res1) ==>
    state_next_type_stamp s <= state_next_type_stamp s') /\
   (evaluate_match (s:(FFI)state) env v pes err_v = (s',res2) ==>
    state_next_type_stamp s <= state_next_type_stamp s') /\
   (evaluate_decs (s:(FFI)state) env ds = (s',res3) ==>
    state_next_type_stamp s <= state_next_type_stamp s')`,
  MESON_TAC[EVPROPSAUX_evaluate_mono]);;

let evaluate_next_exn_stamp_mono = prove
 (`(evaluate (s:(FFI)state) env es = (s',res1) ==>
    state_next_exn_stamp s <= state_next_exn_stamp s') /\
   (evaluate_match (s:(FFI)state) env v pes err_v = (s',res2) ==>
    state_next_exn_stamp s <= state_next_exn_stamp s') /\
   (evaluate_decs (s:(FFI)state) env ds = (s',res3) ==>
    state_next_exn_stamp s <= state_next_exn_stamp s')`,
  MESON_TAC[EVPROPSAUX_evaluate_mono]);;

(* HOL4: LIST_CONJ [pair_case_eq, result_case_eq, error_result_case_eq,     *)
(* bool_case_eq, option_case_eq, list_case_eq, exp_or_val_case_eq,           *)
(* match_result_case_eq]                                                     *)
let evaluate_case_eqs = end_itlist CONJ
  [pair_case_eq; case_eq "result"; case_eq "error_result"; COND_CASE_EQ;
   option_case_eq; list_case_eq; case_eq "exp_or_val"; case_eq "match_result"];;

(* ------------------------------------------------------------------------- *)
(* Simulation proofs: a run of evaluate on a modified state (HOL4: fs with   *)
(* evaluate_case_eqs, dec_clock_def, do_eval_res_def, imp_res_tac of the     *)
(* monotonicity theorems, then rw).  The hypothesis evaluate .. = (s1,res)   *)
(* is unfolded once and split; the induction hypotheses are discharged with  *)
(* facts about the runs found; the goal is unfolded once and rewritten.     *)
(* ------------------------------------------------------------------------- *)

(* the monotonicity facts of every run among the assumptions *)
let EVPROPSAUX_MONO_TAC : tactic = fun (asl,w as gl) ->
  let rules = CONJUNCTS EVPROPSAUX_evaluate_mono in
  let facts = flat (map (fun (_,th) ->
      if EVPROPSAUX_is_eval_eq (concl th) then
        mapfilter (fun r -> MATCH_MP r th) rules else []) asl) in
  MAP_EVERY STRIP_ASSUME_TAC facts gl;;

(* for every run evaluate a .. = (t,r) among the assumptions: acc t = acc a, *)
(* by arithmetic from the monotonicity facts                                *)
let EVPROPSAUX_ACC_EQ_TAC (acc:string) : tactic = fun (asl,w as gl) ->
  let runs = filter (fun (_,th) -> EVPROPSAUX_is_eval_eq (concl th)) asl in
  let eqs = map (fun (_,th) ->
      let l,r = dest_eq (concl th) in
      let a = hd(snd(strip_comb l)) and t = fst(dest_pair r) in
      let c = mk_const(acc,[]) in
      mk_eq(mk_icomb(c,t),mk_icomb(c,a))) runs in
  MAP_EVERY (fun e -> SUBGOAL_THEN e ASSUME_TAC THENL
                        [REWRITE_TAC EVPROPSAUX_REC_RW THEN DECIDE_TAC;
                         ALL_TAC]) eqs gl;;

(* the induction hypotheses whose antecedents follow from the assumptions   *)
(* by rewriting: replaced by their conclusions                               *)
let EVPROPSAUX_IH_DISCH_TAC : tactic =
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_imp c then MP_TAC th else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC;;

(* the form ~ALL P l of the simplifier's EX ((~) o P) l *)
let EVPROPSAUX_EX_NOT_o = prove
 (`!(P:A->bool) l. EX ((~) o P) l <=> ~ALL P l`,
  REWRITE_TAC[NOT_ALL; o_DEF]);;

(* unfold the goal's evaluate once and rewrite with the assumptions *)
let EVPROPSAUX_GOAL_EVAL_TAC thl : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE (EVPROPSAUX_EX_NOT_o :: EVPROPSAUX_REC_RW)) THEN
  ONCE_REWRITE_TAC[full_evaluate_def] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC (EVPROPSAUX_REC_RW @ thl) THEN CAKE_REWRITE_TAC[]));;

let EVPROPSAUX_add_eq_self = ARITH_RULE `!m n. m + n = m <=> n = 0`;;

let EVPROPSAUX_STAMP_CONJ_TAC acc : tactic =
  TRY DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o
                 REWRITE_RULE[EVPROPSAUX_add_eq_self; LENGTH_EQ_NIL]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN RVEQ_TAC THEN
  EVPROPSAUX_ACC_EQ_TAC acc THEN EVPROPSAUX_IH_DISCH_TAC THEN
  EVPROPSAUX_GOAL_EVAL_TAC [do_eval_res_def; build_tdefs_def; LENGTH; ADD_CLAUSES; ALL];;

let EVPROPSAUX_mentions_const c tm =
  can (find_term (fun t -> is_const t && fst(dest_const t) = c)) tm;;

let EVPROPSAUX_STAMPS_TAC : tactic =
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN EVPROPSAUX_MONO_TAC THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w as gl) ->
     EVPROPSAUX_STAMP_CONJ_TAC
       (if EVPROPSAUX_mentions_const "state_next_type_stamp_fupd" w
        then "state_next_type_stamp" else "state_next_exn_stamp") gl);;

let evaluate_set_next_stamps = prove
 (`(!(s0:(A)state) env xs s1 res.
     evaluate s0 env xs = (s1,res) ==>
     (state_next_type_stamp s1 = state_next_type_stamp s0 ==>
        !k. evaluate (state_next_type_stamp_fupd (combin_K k) s0) env xs =
            (state_next_type_stamp_fupd (combin_K k) s1,res)) /\
     (state_next_exn_stamp s1 = state_next_exn_stamp s0 ==>
        !k. evaluate (state_next_exn_stamp_fupd (combin_K k) s0) env xs =
            (state_next_exn_stamp_fupd (combin_K k) s1,res))) /\
   (!(s0:(A)state) env v pes errv s1 res.
     evaluate_match s0 env v pes errv = (s1,res) ==>
     (state_next_type_stamp s1 = state_next_type_stamp s0 ==>
        !k. evaluate_match (state_next_type_stamp_fupd (combin_K k) s0) env v pes errv =
            (state_next_type_stamp_fupd (combin_K k) s1,res)) /\
     (state_next_exn_stamp s1 = state_next_exn_stamp s0 ==>
        !k. evaluate_match (state_next_exn_stamp_fupd (combin_K k) s0) env v pes errv =
            (state_next_exn_stamp_fupd (combin_K k) s1,res))) /\
   (!(s0:(A)state) env ds s1 res.
     evaluate_decs s0 env ds = (s1,res) ==>
     (state_next_type_stamp s1 = state_next_type_stamp s0 ==>
        !k. evaluate_decs (state_next_type_stamp_fupd (combin_K k) s0) env ds =
            (state_next_type_stamp_fupd (combin_K k) s1,res)) /\
     (state_next_exn_stamp s1 = state_next_exn_stamp s0 ==>
        !k. evaluate_decs (state_next_exn_stamp_fupd (combin_K k) s0) env ds =
            (state_next_exn_stamp_fupd (combin_K k) s1,res)))`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN EVPROPSAUX_STAMPS_TAC);;

let call_FFI_return_unchanged = prove
 (`!(ffi:(FFI)ffi_state) s conf bytes bytes'.
     call_FFI ffi s conf bytes = FFI_return ffi bytes' <=>
     s = ExtCall (implode "") /\ bytes' = bytes`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC EVALAUX_call_FFI_same;
    STRIP_TAC THEN ASM_REWRITE_TAC[call_FFI_def]]);;

(* HOL4: do_app_ffi_unchanged (the name is taken by semanticPrimitivesProps) *)
let evaluateProps_do_app_ffi_unchanged = prove
 (`!refs (ffi:(FFI)ffi_state) op vs refs' r.
     do_app (refs,ffi) op vs = SOME ((refs',ffi),r) ==>
     (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome)))) ==>
     !ffi2:(B)ffi_state. do_app (refs,ffi2) op vs = SOME ((refs',ffi2),r)`,
  MESON_TAC[do_app_SOME_ffi_same]);;

(* HOL4's s with ffi := nffi changes the type of the state; here it is      *)
(* written with the record constructor                                      *)

(* the monotonicity facts of every do_app step among the assumptions *)
let EVPROPSAUX_DO_APP_MONO_TAC : tactic = fun (asl,w as gl) ->
  let facts = mapfilter (fun (_,th) -> MATCH_MP do_app_io_events_mono th) asl in
  MAP_EVERY ASSUME_TAC facts gl;;

(* HOL4 proves this later (after evaluate_refs_length_mono); the simulation *)
(* proofs below need it                                                      *)
let combine_dec_result_eq_Rerr = prove
 (`!env (r:(v sem_env,A)result) e. combine_dec_result env r = Rerr e <=> r = Rerr e`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `r:(v sem_env,A)result` THEN
  REWRITE_TAC[combine_dec_result_def] THEN CAKE_REWRITE_TAC[]);;

(* for every run evaluate a .. = (t,r) among the assumptions:              *)
(* state_ffi t = state_ffi a, from the io_events_mono facts and the ffi     *)
(* equations only                                                           *)
let EVPROPSAUX_FFI_EQ_TAC : tactic = fun (asl,w as gl) ->
  let runs = filter (fun (_,th) -> EVPROPSAUX_is_eval_eq (concl th)) asl in
  let ffity t = try fst(dest_type(type_of t)) = "ffi_state" with Failure _ -> false in
  let facts = filter (fun th ->
      let c = concl th in
      (is_comb c && is_comb (rator c) &&
       (try fst(dest_const(rator(rator c))) = "io_events_mono" with Failure _ -> false)) ||
      (is_eq c && ffity (lhs c))) (map snd asl) in
  let eqs = map (fun (_,th) ->
      let l,r = dest_eq (concl th) in
      let a = hd(snd(strip_comb l)) and t = fst(dest_pair r) in
      let c = mk_const("state_ffi",[]) in
      mk_eq(mk_icomb(c,t),mk_icomb(c,a))) runs in
  MAP_EVERY (fun e -> SUBGOAL_THEN e ASSUME_TAC THENL
                        [REWRITE_TAC EVPROPSAUX_REC_RW THEN
                         MESON_TAC(io_events_mono_antisym :: io_events_mono_trans :: facts);
                         ALL_TAC]) eqs gl;;

(* do_app with another ffi state, when the ffi state does not change *)
let EVPROPSAUX_DO_APP_FFI_TAC : tactic = fun (asl,w as gl) ->
  let tac_of th =
    let c = concl th in
    try
      let l,r = dest_eq c in
      let h,args = strip_comb l in
      if fst(dest_const h) <> "do_app" then failwith "" else
      if is_const r then
        ASSUME_TAC(MATCH_MP do_app_NONE_ffi th)
      else
        let f0 = snd(dest_pair(hd args)) in
        let f1 = snd(dest_pair(fst(dest_pair(rand r)))) in
        TRY(SUBGOAL_THEN (mk_eq(f1,f0)) (fun eq ->
              MP_TAC(MATCH_MP evaluateProps_do_app_ffi_unchanged
                       (REWRITE_RULE[eq] th)) THEN
              ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC) THENL
            [ASM_REWRITE_TAC[]; ALL_TAC])
    with Failure _ -> ALL_TAC in
  EVERY (map (tac_of o snd) asl) gl;;

let EVPROPSAUX_FFI_INTRO_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (list_result_eq_Rerr :: combine_dec_result_eq_Rerr ::
                               EVPROPSAUX_REC_RW)) THEN
  EVPROPSAUX_MONO_TAC THEN EVPROPSAUX_DO_APP_MONO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN
  EVPROPSAUX_FFI_EQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (EVPROPSAUX_REC_RW)) THEN
  EVPROPSAUX_IH_DISCH_TAC THEN EVPROPSAUX_IH_DISCH_TAC THEN EVPROPSAUX_DO_APP_FFI_TAC THEN
  EVPROPSAUX_GOAL_EVAL_TAC [do_eval_res_def; build_tdefs_def; LENGTH; ADD_CLAUSES; ALL];;

let evaluate_ffi_intro = prove
 (`(!(s:(A)state) env e s' r.
     evaluate s env e = (s',r) /\ state_ffi s' = state_ffi s /\
     (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome))))
     ==> !nffi:(B)ffi_state.
           evaluate (state_REC (state_clock s) (state_refs s) nffi
                       (state_next_type_stamp s) (state_next_exn_stamp s)
                       (state_eval_state s)) env e =
           (state_REC (state_clock s') (state_refs s') nffi
              (state_next_type_stamp s') (state_next_exn_stamp s')
              (state_eval_state s'),r)) /\
   (!(s:(A)state) env v pes errv s' r.
     evaluate_match s env v pes errv = (s',r) /\ state_ffi s' = state_ffi s /\
     (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome))))
     ==> !nffi:(B)ffi_state.
           evaluate_match (state_REC (state_clock s) (state_refs s) nffi
                             (state_next_type_stamp s) (state_next_exn_stamp s)
                             (state_eval_state s)) env v pes errv =
           (state_REC (state_clock s') (state_refs s') nffi
              (state_next_type_stamp s') (state_next_exn_stamp s')
              (state_eval_state s'),r)) /\
   (!(s:(A)state) env ds s' r.
     evaluate_decs s env ds = (s',r) /\ state_ffi s' = state_ffi s /\
     (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome))))
     ==> !nffi:(B)ffi_state.
           evaluate_decs (state_REC (state_clock s) (state_refs s) nffi
                            (state_next_type_stamp s) (state_next_exn_stamp s)
                            (state_eval_state s)) env ds =
           (state_REC (state_clock s') (state_refs s') nffi
              (state_next_type_stamp s') (state_next_exn_stamp s')
              (state_eval_state s'),r))`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN EVPROPSAUX_FFI_INTRO_TAC);;

let is_clock_io_mono_set_clock = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) s s' r ck1.
     is_clock_io_mono f s
     ==> f s = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error))
     ==> ?ck0. f (state_clock_fupd (combin_K ck0) s) = (state_clock_fupd (combin_K ck1) s',r)`,
  REPEAT GEN_TAC THEN SIMP[is_clock_io_mono_def] THEN REPEAT STRIP_TAC THEN RFS[] THEN
  FIRST_X_ASSUM (QSPEC_THEN "ck1 + (state_clock s - state_clock s')" MP_TAC) THEN CASE_TAC THEN
  SIMP[ARITH_ss; ADD_SUB] THEN STRIP_TAC THEN
  QEXISTS_TAC "ck1 + (state_clock s - state_clock s')" THEN RFS[]);;

(* HOL4 evaluate_set_clock_lemmas *)
let EVPROPSAUX_set_clock_lemmas =
  map (BETA_RULE o MATCH_MP is_clock_io_mono_set_clock o SPEC_ALL)
      (CONJUNCTS is_clock_io_mono_evaluate @ [is_clock_io_mono_evaluate_decs]);;

let evaluate_set_clock = prove
 (`!(s:(FFI)state) env exps s1 res.
     evaluate s env exps = (s1,res) /\ ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !ck. ?ck1. evaluate (state_clock_fupd (combin_K ck1) s) env exps =
                (state_clock_fupd (combin_K ck) s1,res)`,
  MESON_TAC EVPROPSAUX_set_clock_lemmas);;

let evaluate_decs_set_clock = prove
 (`!(s:(FFI)state) env decs s1 res.
     evaluate_decs s env decs = (s1,res) /\ ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !ck. ?ck1. evaluate_decs (state_clock_fupd (combin_K ck1) s) env decs =
                (state_clock_fupd (combin_K ck) s1,res)`,
  MESON_TAC EVPROPSAUX_set_clock_lemmas);;

let is_clock_io_mono_minimal = prove
 (`!(f:(FFI)state->(FFI)state#(A,B)result) s s' r k.
     is_clock_io_mono f s
     ==> f s = (s',r) /\ state_clock s' = 0 /\ ~(r = Rerr (Rabort Rtimeout_error)) /\
         state_clock s > k
     ==> ?s''. f (state_clock_fupd (combin_K k) s) = (s'',Rerr (Rabort Rtimeout_error)) /\
               io_events_mono (state_ffi s'') (state_ffi s')`,
  REPEAT GEN_TAC THEN SIMP[is_clock_io_mono_def] THEN REPEAT STRIP_TAC THEN RFS[] THEN
  FIRST_X_ASSUM (QSPEC_THEN "k" MP_TAC) THEN CASE_TAC THEN SIMP[ARITH_ss] THEN STRIP_TAC THEN
  RFS[ARITH_ss]);;

(* HOL4 evaluate_minimal_lemmas *)
let EVPROPSAUX_minimal_lemmas =
  map (BETA_RULE o MATCH_MP is_clock_io_mono_minimal o SPEC_ALL)
      (CONJUNCTS is_clock_io_mono_evaluate);;

let evaluate_minimal_clock = prove
 (`!(s:(FFI)state) env es s' r k.
     evaluate s env es = (s',r) /\ state_clock s' = 0 /\
     ~(r = Rerr (Rabort Rtimeout_error)) /\ state_clock s > k
     ==> ?s''. evaluate (state_clock_fupd (combin_K k) s) env es =
               (s'',Rerr (Rabort Rtimeout_error)) /\
               io_events_mono (state_ffi s'') (state_ffi s')`,
  MESON_TAC EVPROPSAUX_minimal_lemmas);;

let evaluate_match_minimal_clock = prove
 (`!(s:(FFI)state) env v pes err_v s' r k.
     evaluate_match s env v pes err_v = (s',r) /\ state_clock s' = 0 /\
     ~(r = Rerr (Rabort Rtimeout_error)) /\ state_clock s > k
     ==> ?s''. evaluate_match (state_clock_fupd (combin_K k) s) env v pes err_v =
               (s'',Rerr (Rabort Rtimeout_error)) /\
               io_events_mono (state_ffi s'') (state_ffi s')`,
  MESON_TAC EVPROPSAUX_minimal_lemmas);;

let evaluate_set_init_clock = prove
 (`!(st:(FFI)state) env xs st' res.
     evaluate st env xs = (st',res) /\ ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !k. ?ck res1 st1.
       evaluate (state_clock_fupd (combin_K k) st) env xs = (st1,res1) /\
       (res1 = res /\ st1 = state_clock_fupd (combin_K ck) st' \/
        res1 = Rerr (Rabort Rtimeout_error) /\
        io_events_mono (state_ffi st1) (state_ffi st'))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`st:(FFI)state`; `env:v sem_env`; `xs:exp list`; `st':(FFI)state`;
                 `res:(v list,v)result`] evaluate_set_clock) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ck1:num` o SPEC `0`) THEN
  DISJ_CASES_TAC(ARITH_RULE `ck1 <= k \/ k < ck1`) THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (st:(FFI)state)`; `env:v sem_env`;
                   `xs:exp list`; `state_clock_fupd (combin_K 0) (st':(FFI)state)`;
                   `res:(v list,v)result`; `p:num`] evaluate_add_to_clock) THEN
    ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM;
                    ADD_CLAUSES] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC
     [`p:num`; `res:(v list,v)result`; `state_clock_fupd (combin_K p) (st':(FFI)state)`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`state_clock_fupd (combin_K ck1) (st:(FFI)state)`; `env:v sem_env`;
                   `xs:exp list`; `state_clock_fupd (combin_K 0) (st':(FFI)state)`;
                   `res:(v list,v)result`; `k:num`] evaluate_minimal_clock) THEN
    ASM_REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; state_INFO.ri_accfupds; K_THM;
                    GT] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`0`; `Rerr (Rabort Rtimeout_error):(v list,v)result`; `s'':(FFI)state`] THEN
    ASM_REWRITE_TAC[]]);;

let can_pmatch_all_EVERY = prove
 (`!envC refs ps v.
     can_pmatch_all envC refs ps v <=>
     ALL (\p. ~(pmatch envC refs p v [] = Match_type_error)) ps`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[can_pmatch_all_def; ALL] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let same_type_trans = prove
 (`!t1 t2 t3. same_type t1 t2 /\ same_type t1 t3 ==> same_type t2 t3`,
  REPEAT GEN_TAC THEN CASES_ON `t1:stamp` THEN CASES_ON `t2:stamp` THEN
  CASES_ON `t3:stamp` THEN REWRITE_TAC[same_type_def] THEN MESON_TAC[]);;

let evaluate_refs_length_mono = prove
 (`(!(s:(FFI)state) env es s' r.
      evaluate s env es = (s',r) ==> LENGTH (state_refs s) <= LENGTH (state_refs s')) /\
   (!(s:(FFI)state) env v pes err_v s' r.
      evaluate_match s env v pes err_v = (s',r) ==>
      LENGTH (state_refs s) <= LENGTH (state_refs s'))`,
  MESON_TAC[EVPROPSAUX_evaluate_mono]);;

(* the contradictions of a run with no eval state that reaches Eval or Denv *)
let EVPROPSAUX_NO_EVAL_CONTR_TAC : tactic = fun (asl,w as gl) ->
  let is_none c = is_eq c && EVPROPSAUX_is_const_app ["state_eval_state"] (lhs c) &&
                  is_const (rhs c) in
  let nones = filter (is_none o concl) (map snd asl) in
  let rw th = if is_none (concl th) then th
              else CAKE_REWRITE_RULE[do_eval_def; declare_env_def]
                     (REWRITE_RULE nones th) in
  (RULE_ASSUM_TAC rw THEN
   TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)))) gl;;

let EVPROPSAUX_NO_EVAL_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (list_result_eq_Rerr :: combine_dec_result_eq_Rerr ::
                               EVPROPSAUX_REC_RW)) THEN
  EVPROPSAUX_IH_DISCH_TAC THEN EVPROPSAUX_IH_DISCH_TAC THEN EVPROPSAUX_IH_DISCH_TAC THEN
  EVPROPSAUX_NO_EVAL_CONTR_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN
  (fun (asl,w as gl) ->
     let ev = EVPROPSAUX_GOAL_EVAL_TAC [do_eval_res_def; build_tdefs_def; LENGTH;
                                       ADD_CLAUSES; ALL] in
     if is_conj w then (CONJ_TAC THENL [ASM_REWRITE_TAC EVPROPSAUX_REC_RW; ev]) gl
     else ev gl);;

let eval_no_eval_simulation = prove
 (`(!(s:(FFI)state) env exps s' res.
     evaluate s env exps = (s',res) /\ state_eval_state s = NONE /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     state_eval_state s' = NONE /\
     evaluate (state_eval_state_fupd (combin_K es) s) env exps =
     (state_eval_state_fupd (combin_K es) s',res)) /\
   (!(s:(FFI)state) env x pes err_x s' res.
     evaluate_match s env x pes err_x = (s',res) /\ state_eval_state s = NONE /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     state_eval_state s' = NONE /\
     evaluate_match (state_eval_state_fupd (combin_K es) s) env x pes err_x =
     (state_eval_state_fupd (combin_K es) s',res)) /\
   (!(s:(FFI)state) env decs s' res.
     evaluate_decs s env decs = (s',res) /\ state_eval_state s = NONE /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     state_eval_state s' = NONE /\
     evaluate_decs (state_eval_state_fupd (combin_K es) s) env decs =
     (state_eval_state_fupd (combin_K es) s',res))`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN EVPROPSAUX_NO_EVAL_TAC);;

let evaluate_ffi_etc_intro = prove
 (`!(s0:(A)state) env xs s1 res (s:(B)state).
     evaluate s0 env xs = (s1,res) /\
     (!outcome. ~(res = Rerr (Rabort (Rffi_error outcome)))) /\
     state_ffi s1 = state_ffi s0 /\
     state_next_type_stamp s1 = state_next_type_stamp s0 /\
     state_next_exn_stamp s1 = state_next_exn_stamp s0 /\
     state_eval_state s0 = NONE /\
     ~(res = Rerr (Rabort Rtype_error)) /\
     state_refs s = state_refs s0
     ==> ?ck1 ck2. evaluate (state_clock_fupd (combin_K ck1) s) env xs =
                   (state_refs_fupd (combin_K (state_refs s1)) (state_clock_fupd (combin_K ck2) s),res)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s0:(A)state`; `env:v sem_env`; `xs:exp list`; `s1:(A)state`;
                `res:(v list,v)result`] (CONJUNCT1 evaluate_ffi_intro)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o ISPEC `state_ffi (s:(B)state)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 evaluate_set_next_stamps)) THEN
  REWRITE_TAC[state_INFO.ri_accessors] THEN
  DISCH_THEN(MP_TAC o SPEC `state_next_type_stamp (s:(B)state)` o CONJUNCT1) THEN
  REWRITE_TAC[state_INFO.ri_fupds; K_THM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT1 evaluate_set_next_stamps)) THEN
  REWRITE_TAC[state_INFO.ri_accessors] THEN
  DISCH_THEN(MP_TAC o SPEC `state_next_exn_stamp (s:(B)state)` o CONJUNCT2) THEN
  REWRITE_TAC[state_INFO.ri_fupds; K_THM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (INST [`state_eval_state (s:(B)state)`,`es:eval_state option`]
          (INST_TYPE [`:B`,`:FFI`] (CONJUNCT1 eval_no_eval_simulation))))) THEN
  ASM_REWRITE_TAC[state_INFO.ri_accessors; state_INFO.ri_fupds; K_THM] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`state_clock (s0:(A)state)`; `state_clock (s1:(A)state)`] THEN
  SUBGOAL_THEN `!c. state_clock_fupd (combin_K c) (s:(B)state) =
                    state_REC c (state_refs s) (state_ffi s) (state_next_type_stamp s)
                      (state_next_exn_stamp s) (state_eval_state s)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[state_component_equality; state_INFO.ri_accessors;
                state_INFO.ri_accfupds; K_THM];
    REWRITE_TAC[state_INFO.ri_fupds; K_THM] THEN ASM_REWRITE_TAC[]]);;

let same_type_sym = prove
 (`!t1 t2. same_type t1 t2 ==> same_type t2 t1`,
  REPEAT GEN_TAC THEN CASES_ON `t1:stamp` THEN CASES_ON `t2:stamp` THEN
  REWRITE_TAC[same_type_def] THEN MESON_TAC[]);;

let pmatch_not_type_error_EQ = prove
 (`(!envC refs v acc. ~(pmatch envC refs Pany v acc = Match_type_error) <=> T) /\
   (!envC refs n v acc. ~(pmatch envC refs (Pvar n) v acc = Match_type_error) <=> T) /\
   (!envC refs name xs v acc.
      ~(pmatch envC refs (Pcon (SOME name) xs) v acc = Match_type_error) <=>
      ?ys t l stamp.
        v = Conv (SOME t) ys /\
        nsLookup envC name = SOME (l,stamp) /\ LENGTH xs = l /\
        same_type stamp t /\
        (t = stamp ==> l = LENGTH ys /\
                       ~(pmatch_list envC refs xs ys acc = Match_type_error))) /\
   (!envC refs xs v acc.
      ~(pmatch envC refs (Pcon NONE xs) v acc = Match_type_error) <=>
      ?ys. v = Conv NONE ys /\ LENGTH xs = LENGTH ys /\
           ~(pmatch_list envC refs xs ys acc = Match_type_error)) /\
   (!envC refs acc. ~(pmatch_list envC refs [] [] acc = Match_type_error) <=> T) /\
   (!envC refs v vs acc.
      ~(pmatch_list envC refs [] (CONS v vs) acc = Match_type_error) <=> F) /\
   (!envC refs p ps acc.
      ~(pmatch_list envC refs (CONS p ps) [] acc = Match_type_error) <=> F) /\
   (!envC refs p ps v vs acc.
      ~(pmatch_list envC refs (CONS p ps) (CONS v vs) acc = Match_type_error) <=>
      ~(pmatch envC refs p v acc = Match_type_error) /\
      (!a:(varN#v)list. pmatch envC refs p v acc = No_match ==>
           ~(pmatch_list envC refs ps vs acc = Match_type_error)) /\
      (!a. pmatch envC refs p v acc = Match a ==>
           ~(pmatch_list envC refs ps vs a = Match_type_error)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[pmatch_def] THEN
  CAKE_REWRITE_TAC[] THENL
   [CASES_ON `v:v` THEN REWRITE_TAC[pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
    CASES_ON `a0:stamp option` THEN REWRITE_TAC[pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[UNWIND_THM1; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
                GSYM CONJ_ASSOC] THEN
    CASES_ON `nsLookup (envC:env_ctor) (name:(mlstring,mlstring)id)` THEN
    CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `a':num#stamp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `stamp:stamp` SUBST_ALL_TAC)) THEN
    CAKE_REWRITE_TAC[PAIR_EQ; same_ctor_def] THEN
    REWRITE_TAC[UNWIND_THM1; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "match_result"] THEN
    ASM_MESON_TAC[];
    CASES_ON `v:v` THEN REWRITE_TAC[pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
    CASES_ON `a0:stamp option` THEN REWRITE_TAC[pmatch_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[UNWIND_THM1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[distinctness "match_result"];
    CASES_ON `pmatch envC refs p v acc:((varN#v)list)match_result` THEN
    CAKE_REWRITE_TAC[] THEN
    TRY(CASES_ON `pmatch_list envC refs ps vs acc:((varN#v)list)match_result` THEN
        CAKE_REWRITE_TAC[] THEN NO_TAC) THEN
    MESON_TAC[]]);;

let EVPROPSAUX_call_FFI_io_return = prove
 (`!(ffi:(FFI)ffi_state) s conf bytes ffi' bytes' l.
     call_FFI ffi s conf bytes = FFI_return ffi' bytes' ==>
     call_FFI (ffi_state_io_events_fupd (combin_K l) ffi) s conf bytes =
     FFI_return (ffi_state_io_events_fupd
                   (combin_K (APPEND l (DROP (LENGTH (ffi_state_io_events ffi))
                                      (ffi_state_io_events ffi')))) ffi') bytes'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def; ffi_state_INFO.ri_accfupds; K_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CASES_ON `ffi_state_oracle (ffi:(FFI)ffi_state) s (ffi_state_ffi_state ffi) conf bytes` THEN
    CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[ffi_state_INFO.ri_accfupds; ffi_state_INFO.ri_fupdfupds; K_o_THM; K_THM;
                ffi_state_INFO.ri_fupdcanon] THEN
    REWRITE_TAC[DROP_LENGTH_APPEND];
    CAKE_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[DROP_LENGTH_NIL; APPEND_NIL; ffi_state_INFO.ri_fupdfupds; K_o_THM]]);;

let EVPROPSAUX_call_FFI_io_final = prove
 (`!(ffi:(FFI)ffi_state) s conf bytes outcome l.
     call_FFI ffi s conf bytes = FFI_final outcome ==>
     call_FFI (ffi_state_io_events_fupd (combin_K l) ffi) s conf bytes = FFI_final outcome`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def; ffi_state_INFO.ri_accfupds; K_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `ffi_state_oracle (ffi:(FFI)ffi_state) s (ffi_state_ffi_state ffi) conf bytes` THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN CAKE_REWRITE_TAC[]);;

let do_app_ffi_mono = prove
 (`!refs (ffi:(FFI)ffi_state) op args refs' ffi' r.
     do_app (refs,ffi) op args = SOME ((refs',ffi'),r) ==>
     ?l. ffi_state_io_events ffi' = APPEND (ffi_state_io_events ffi) l`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `ffi:(FFI)ffi_state = ffi'` THENL
   [EXISTS_TAC `[]:io_event list` THEN ASM_REWRITE_TAC[APPEND_NIL];
    MP_TAC(ISPECL [`refs:(v store_v)list`; `ffi:(FFI)ffi_state`; `op:op`; `args:v list`;
                   `refs':(v store_v)list`; `ffi':(FFI)ffi_state`; `r:(v,v)result`]
                  do_app_ffi_changed) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

let do_app_SOME_ffi_same_oracle_state = prove
 (`!refs (ffi:(FFI)ffi_state) op args refs' ffi' r l.
     do_app (refs,ffi) op args = SOME ((refs',ffi'),r) ==>
     do_app (refs,ffi_state_io_events_fupd (combin_K l) ffi) op args =
     SOME ((refs',ffi_state_io_events_fupd
                    (combin_K (APPEND l (DROP (LENGTH (ffi_state_io_events ffi))
                                       (ffi_state_io_events ffi')))) ffi'),r)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `?n. op = FFI n` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
    STRIP_TAC THEN GVS(EVALAUX_do_app_eqs @ [case_eq "ffi_result"]) THENL
     [ASM_MESON_TAC[EVPROPSAUX_call_FFI_io_return];
      ASM_MESON_TAC[EVPROPSAUX_call_FFI_io_final]];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN DISCH_TAC THEN
    SUBGOAL_THEN `ffi':(FFI)ffi_state = ffi` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[do_app_ffi_unchanged]; ALL_TAC] THEN
    MP_TAC(ISPECL [`refs:(v store_v)list`; `ffi:(FFI)ffi_state`;
                   `ffi_state_io_events_fupd (combin_K l) (ffi:(FFI)ffi_state)`; `op:op`;
                   `args:v list`] EVALAUX_do_app_ffi_indep) THEN
    ASM_REWRITE_TAC[DROP_LENGTH_NIL; APPEND_NIL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[OPTION_MAP_DEF; pair_CASE]]);;

(* the do_app steps among the assumptions with another io history *)
let EVPROPSAUX_DO_APP_IO_TAC : tactic = fun (asl,w as gl) ->
  let tac_of th =
    try
      let l,r = dest_eq (concl th) in
      let h,_ = strip_comb l in
      if fst(dest_const h) <> "do_app" then failwith "" else
      if is_const r then ASSUME_TAC(MATCH_MP do_app_NONE_ffi th)
      else (STRIP_ASSUME_TAC(MATCH_MP do_app_ffi_mono th) THEN
            ASSUME_TAC(MATCH_MP do_app_SOME_ffi_same_oracle_state th))
    with Failure _ -> ALL_TAC in
  EVERY (map (tac_of o snd) asl) gl;;

(* the witness DROP (LENGTH h0) h1 of ?new_io. h1 = APPEND h0 new_io /\ .. *)
let EVPROPSAUX_IO_WITNESS_TAC : tactic = fun (asl,w as gl) ->
  let _,body = dest_exists w in
  let c1 = fst(dest_conj body) in
  let h1 = lhs c1 and h0 = lhand(rhs c1) in
  EXISTS_TAC (list_mk_icomb "DROP" [mk_icomb(mk_const("LENGTH",[]),h0); h1]) gl;;

let EVPROPSAUX_DROP_LENGTH_ADD = prove
 (`!(a:A list) n l. DROP (LENGTH a + n) (APPEND a l) = DROP n l`,
  SIMP_TAC[DROP_APPEND2; LE_ADD; ADD_SUB2]);;

let EVPROPSAUX_IO_RW =
  [GSYM APPEND_ASSOC; DROP_LENGTH_APPEND; DROP_LENGTH_NIL; APPEND_NIL; LENGTH_APPEND;
   EVPROPSAUX_DROP_LENGTH_ADD];;

let EVPROPSAUX_HISTORY_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN
  EVPROPSAUX_HYP_SPLIT2_TAC [dec_clock_def] THEN EVPROPSAUX_DO_EVAL_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  EVPROPSAUX_DO_APP_IO_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE EVPROPSAUX_REC_RW) THEN
  REWRITE_TAC EVPROPSAUX_REC_RW THEN
  EVPROPSAUX_IO_WITNESS_TAC THEN
  (CONJ_TAC THENL
    [ASM_REWRITE_TAC EVPROPSAUX_IO_RW;
     GEN_TAC THEN
     EVPROPSAUX_GOAL_EVAL_TAC ([do_eval_res_def; build_tdefs_def; LENGTH; ADD_CLAUSES;
                                ALL] @ EVPROPSAUX_IO_RW)]);;

let evaluate_history_irrelevance = prove
 (`(!(st:(FFI)state) env exp st' res.
     evaluate st env exp = (st',res) ==>
     ?new_io. ffi_state_io_events (state_ffi st') =
              APPEND (ffi_state_io_events (state_ffi st)) new_io /\
       !l. evaluate (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K l) (state_ffi st))) st)
                    env exp =
           (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K (APPEND l new_io))
                                 (state_ffi st'))) st',res)) /\
   (!(st:(FFI)state) env v pes err_v st' res.
     evaluate_match st env v pes err_v = (st',res) ==>
     ?new_io. ffi_state_io_events (state_ffi st') =
              APPEND (ffi_state_io_events (state_ffi st)) new_io /\
       !l. evaluate_match
             (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K l) (state_ffi st))) st)
             env v pes err_v =
           (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K (APPEND l new_io))
                                 (state_ffi st'))) st',res)) /\
   (!(st:(FFI)state) env ds st' res.
     evaluate_decs st env ds = (st',res) ==>
     ?new_io. ffi_state_io_events (state_ffi st') =
              APPEND (ffi_state_io_events (state_ffi st)) new_io /\
       !l. evaluate_decs
             (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K l) (state_ffi st))) st)
             env ds =
           (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K (APPEND l new_io))
                                 (state_ffi st'))) st',res))`,
  (* the bound variables renamed apart from those of full_evaluate_ind (the  *)
  (* resolution of the induction hypotheses needs distinct binder names)     *)
  SUBGOAL_THEN
   `(!(st:(FFI)state) env exp s2 r2.
     evaluate st env exp = (s2,r2) ==>
     ?new_io. ffi_state_io_events (state_ffi s2) =
              APPEND (ffi_state_io_events (state_ffi st)) new_io /\
       !l. evaluate (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K l) (state_ffi st))) st)
                    env exp =
           (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K (APPEND l new_io))
                                 (state_ffi s2))) s2,r2)) /\
   (!(st:(FFI)state) env v pes err_v s2 r2.
     evaluate_match st env v pes err_v = (s2,r2) ==>
     ?new_io. ffi_state_io_events (state_ffi s2) =
              APPEND (ffi_state_io_events (state_ffi st)) new_io /\
       !l. evaluate_match
             (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K l) (state_ffi st))) st)
             env v pes err_v =
           (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K (APPEND l new_io))
                                 (state_ffi s2))) s2,r2)) /\
   (!(st:(FFI)state) env ds s2 r2.
     evaluate_decs st env ds = (s2,r2) ==>
     ?new_io. ffi_state_io_events (state_ffi s2) =
              APPEND (ffi_state_io_events (state_ffi st)) new_io /\
       !l. evaluate_decs
             (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K l) (state_ffi st))) st)
             env ds =
           (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K (APPEND l new_io))
                                 (state_ffi s2))) s2,r2))`
   ACCEPT_TAC THEN
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN EVPROPSAUX_HISTORY_TAC);;

let evaluate_add_history = prove
 (`(!(st:(FFI)state) env exp st' res.
     evaluate (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K []) (state_ffi st))) st)
       env exp = (st',res)
     ==> evaluate st env exp =
         (state_ffi_fupd (combin_K (ffi_state_io_events_fupd
            (combin_K (APPEND (ffi_state_io_events (state_ffi st))
                       (ffi_state_io_events (state_ffi st')))) (state_ffi st'))) st',res)) /\
   (!(st:(FFI)state) env v pes err_v st' res.
     evaluate_match
       (state_ffi_fupd (combin_K (ffi_state_io_events_fupd (combin_K []) (state_ffi st))) st)
       env v pes err_v = (st',res)
     ==> evaluate_match st env v pes err_v =
         (state_ffi_fupd (combin_K (ffi_state_io_events_fupd
            (combin_K (APPEND (ffi_state_io_events (state_ffi st))
                       (ffi_state_io_events (state_ffi st')))) (state_ffi st'))) st',res))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (el 0 (CONJUNCTS evaluate_history_irrelevance)));
    DISCH_THEN(MP_TAC o MATCH_MP (el 1 (CONJUNCTS evaluate_history_irrelevance)))] THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM; ffi_state_INFO.ri_accfupds; APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `new_io:io_event list` (CONJUNCTS_THEN2 SUBST1_TAC
    (MP_TAC o SPEC `ffi_state_io_events (state_ffi (st:(FFI)state))`))) THEN
  REWRITE_TAC[state_INFO.ri_fupdfupds; K_o_THM; ffi_state_INFO.ri_fupdfupds] THEN
  SUBGOAL_THEN `ffi_state_io_events_fupd (combin_K (ffi_state_io_events (state_ffi st)))
                  (state_ffi st) = state_ffi (st:(FFI)state) /\
                state_ffi_fupd (combin_K (state_ffi st)) st = st`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[state_component_equality; ffi_state_component_equality;
              state_INFO.ri_accfupds; ffi_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: Apps_append *)
let evaluateProps_Apps_append = prove
 (`!xs ys f. Apps f (APPEND xs ys) = Apps (Apps f xs) ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; ast_Apps_def]);;

(* App Opapp with two arguments: the evaluation of the arguments (right to left) *)
let EVPROPSAUX_App2_Opapp = prove
 (CASE_TERM `!(st:(FFI)state) env g h s1 v1 s2 v2.
     evaluate st env [h] = (s1,Rval [v1]) /\ evaluate s1 env [g] = (s2,Rval [v2])
     ==> evaluate st env [App Opapp [g; h]] =
         match do_opapp [v2; v1] with
           SOME (env',e) ->
             (if state_clock s2 = 0 then (s2,Rerr (Rabort Rtimeout_error))
              else evaluate (dec_clock s2) env' [e])
         | NONE -> (s2,Rerr (Rabort Rtype_error))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [evaluate_def] THEN
  REWRITE_TAC[REVERSE; APPEND] THEN ONCE_REWRITE_TAC[evaluate_cons] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[getOpClass_def; APPEND; REVERSE] THEN
                     CAKE_REWRITE_TAC[])));;

let evaluate_Apps_Rerr = prove
 (`!xs f (st:(FFI)state) env s1 e.
     evaluate st env xs = (s1,Rerr e) ==>
     evaluate st env [Apps f (REVERSE xs)] = (s1,Rerr e)`,
  LIST_INDUCT_TAC THEN GVS[evaluate_def] THEN
  SIMP[ONCE evaluate_cons; evaluateProps_Apps_append; ast_Apps_def; REVERSE] THEN
  REPEAT GEN_TAC THEN GVS[evaluate_def] THEN REPEAT TOP_CASE_TAC THEN GVS[] THEN
  RES_TAC THEN GVS[]);;

let EVPROPSAUX_nsAppend_alist_SNOC = prove
 (`!(a:(N#V)list) n v (e:(M,N,V)namespace).
     nsAppend (alist_to_ns (APPEND a [(n,v)])) e = nsAppend (alist_to_ns a) (nsBind n v e)`,
  REPEAT GEN_TAC THEN CASES_ON `e:(M,N,V)namespace` THEN
  REWRITE_TAC[alist_to_ns_def; nsAppend_def; nsBind_def; APPEND_NIL] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

(* one application of a closure to a value *)
let EVPROPSAUX_App_Opapp_Closure = prove
 (`!(s0:(FFI)state) env x y s1 vy s2 env1 n e.
     evaluate s0 env [y] = (s1,Rval [vy]) /\
     evaluate s1 env [x] = (s2,Rval [Closure env1 n e]) /\ ~(state_clock s2 = 0)
     ==> evaluate s0 env [App Opapp [x; y]] =
         evaluate (dec_clock s2) (sem_env_v_fupd (combin_K (nsBind n vy (sem_env_v env1))) env1)
           [e]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s0:(FFI)state`; `env:v sem_env`; `x:exp`; `y:exp`; `s1:(FFI)state`;
                 `vy:v`; `s2:(FFI)state`; `Closure env1 n e`] EVPROPSAUX_App2_Opapp) THEN
  ASM_REWRITE_TAC[do_opapp_def] THEN CAKE_REWRITE_TAC[]);;

let EVPROPSAUX_evaluate_Funs_CONS = prove
 (`!(s:(FFI)state) env n ns e.
     evaluate s env [Funs (CONS n ns) e] = (s,Rval [Closure env n (Funs ns e)])`,
  REWRITE_TAC[ast_Funs_def; evaluate_def]);;

let evaluate_Apps_Funs = prove
 (`!l x ns vs (st:(FFI)state) s1 s2 env env1 e.
     evaluate st env l = (s1,Rval vs) /\
     evaluate s1 env [x] = (s2,Rval [Closure env1 (HD ns) (Funs (TL ns) e)]) /\
     LENGTH l = LENGTH ns /\ ~(ns = []) /\ LENGTH ns <= state_clock s2 ==>
     evaluate st env [Apps x (REVERSE l)] =
     evaluate (state_clock_fupd (combin_K (state_clock s2 - LENGTH ns)) s2)
       (sem_env_v_fupd (combin_K (nsAppend (alist_to_ns (ZIP (REVERSE ns) vs)) (sem_env_v env1)))
          env1) [e]`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH] THEN MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  X_GEN_TAC `l:exp list` THEN DISCH_TAC THEN X_GEN_TAC `y:exp` THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SNOC_APPEND; evaluate_append; REVERSE_APPEND; REVERSE;
                                  APPEND; ast_Apps_def; LENGTH_APPEND; LENGTH] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env l` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(FFI)state` (X_CHOOSE_THEN `q1:(v list,v)result`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASES_ON `q1:(v list,v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPEC `evaluate (t1:(FFI)state) env [y]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(FFI)state` (X_CHOOSE_THEN `q2:(v list,v)result`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `q2:(v list,v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `?vy. a':v list = [vy]` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[evaluate_sing]; ALL_TAC] THEN
  ASM_CASES_TAC `l:exp list = []` THENL
   [(* one argument *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[evaluate_nil; PAIR_EQ; LENGTH; ADD_CLAUSES;
                                injectivity "result"]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN CASES_ON `ns:varN list` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL; HD; TL]) THEN
    TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
    SUBGOAL_THEN `a1:varN list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    REWRITE_TAC[REVERSE; APPEND; ast_Apps_def; ZIP; LENGTH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ast_Funs_def; LENGTH]) THEN
    MP_TAC(ISPECL [`t1:(FFI)state`; `env:v sem_env`; `x':exp`; `y:exp`; `s1:(FFI)state`;
                   `vy:v`; `s2:(FFI)state`; `env1:v sem_env`; `a0:varN`; `e:exp`]
                  EVPROPSAUX_App_Opapp_Closure) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [EVPROPSAUX_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[dec_clock_def; alist_to_ns_cons; nsAppend_nsBind; alist_to_ns_nil;
                nsAppend_nsEmpty; ARITH_RULE `SUC 0 = 1`];
    ALL_TAC] THEN
  (* more arguments: the induction hypothesis for the partial application *)
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n:varN` (X_CHOOSE_THEN `ns1:varN list` SUBST_ALL_TAC))
    (ISPEC `ns:varN list` list_CASES) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; HD; TL; NOT_CONS_NIL; ADD_CLAUSES; SUC_INJ]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n2:varN` (X_CHOOSE_THEN `ns2:varN list` SUBST_ALL_TAC))
    (ISPEC `ns1:varN list` list_CASES) THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; LENGTH]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ast_Funs_def]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`App Opapp [x'; y]`; `CONS (n2:varN) ns2`; `a:v list`; `st:(FFI)state`;
     `t1:(FFI)state`; `dec_clock (s2:(FFI)state)`; `env:v sem_env`;
     `sem_env_v_fupd (combin_K (nsBind n vy (sem_env_v env1))) (env1:v sem_env)`; `e:exp`]) THEN
  REWRITE_TAC[HD; TL; NOT_CONS_NIL; LENGTH] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t1:(FFI)state`; `env:v sem_env`; `x':exp`; `y:exp`; `s1:(FFI)state`;
                     `vy:v`; `s2:(FFI)state`; `env1:v sem_env`; `n:varN`;
                     `Fun n2 (Funs ns2 e)`] EVPROPSAUX_App_Opapp_Closure) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EVPROPSAUX_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[evaluate_def]];
      REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds; K_THM; LENGTH] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN EVPROPSAUX_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `LENGTH (a:v list) = LENGTH (REVERSE (CONS (n2:varN) ns2))` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REVERSE; LENGTH] THEN
    MP_TAC(MATCH_MP (CONJUNCT1 evaluate_length)
      (ASSUME `evaluate (st:(FFI)state) env l = (t1,Rval a)`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[dec_clock_def; state_INFO.ri_fupdfupds; state_INFO.ri_accfupds; K_o_THM;
              K_THM; sem_env_INFO.ri_fupdfupds; sem_env_INFO.ri_accfupds] THEN
  ONCE_REWRITE_TAC[REVERSE] THEN
  ASM_SIMP_TAC[GSYM ZIP_APPEND; LENGTH] THEN
  REWRITE_TAC[ZIP; EVPROPSAUX_nsAppend_alist_SNOC] THEN
  REWRITE_TAC[REVERSE; ARITH_RULE `!m n. m - 1 - SUC n = m - SUC (SUC n)`]);;

let evaluate_Apps_f_err = prove
 (`!xs vs (st:(FFI)state) (envs1:A) f s1 s2.
     evaluate st env xs = (s1,Rval vs) /\
     evaluate s1 env [f] = (s2,Rerr r) ==>
     evaluate st env [Apps f (REVERSE xs)] = (s2,Rerr r)`,
  MATCH_MP_TAC SNOC_INDUCT THEN GVS[evaluate_def; ast_Apps_def] THEN
  SIMP[evaluate_append; SNOC_APPEND] THEN GVS(all_case_eqs()) THEN RW[] THEN
  GVS[evaluateProps_Apps_append; ast_Apps_def; REVERSE_APPEND] THEN
  LAST_X_ASSUM IRULE THEN GVS[evaluate_def]);;

let evaluate_Apps_Funs_timeout = prove
 (`!l x ns vs (st:(FFI)state) s1 s2 env env1 e.
     evaluate st env l = (s1,Rval vs) /\
     evaluate s1 env [x] = (s2,Rval [Closure env1 (HD ns) (Funs (TL ns) e)]) /\
     LENGTH l = LENGTH ns /\ ~(ns = []) /\ state_clock s2 < LENGTH ns ==>
     evaluate st env [Apps x (REVERSE l)] =
     (state_clock_fupd (combin_K 0) s2,Rerr (Rabort Rtimeout_error))`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH] THEN MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  X_GEN_TAC `l:exp list` THEN DISCH_TAC THEN X_GEN_TAC `y:exp` THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SNOC_APPEND; evaluate_append; REVERSE_APPEND; REVERSE;
                                  APPEND; ast_Apps_def; LENGTH_APPEND; LENGTH] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env l` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(FFI)state` (X_CHOOSE_THEN `q1:(v list,v)result`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASES_ON `q1:(v list,v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPEC `evaluate (t1:(FFI)state) env [y]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(FFI)state` (X_CHOOSE_THEN `q2:(v list,v)result`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `q2:(v list,v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `?vy. a':v list = [vy]` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[evaluate_sing]; ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n:varN` (X_CHOOSE_THEN `ns1:varN list` SUBST_ALL_TAC))
    (ISPEC `ns:varN list` list_CASES) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; HD; TL; NOT_CONS_NIL; ADD_CLAUSES; SUC_INJ]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  ASM_CASES_TAC `state_clock (s2:(FFI)state) = 0` THENL
   [(* no clock for the first application *)
    SUBGOAL_THEN `state_clock_fupd (combin_K 0) s2 = s2:(FFI)state` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[with_same_clock]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:exp list`; `a:v list`; `st:(FFI)state`; `env:v sem_env`;
                   `App Opapp [x'; y]`; `t1:(FFI)state`; `s2:(FFI)state`]
            (INST [`env:v sem_env`,`env:v sem_env`;
                   `Rabort Rtimeout_error:(v)error_result`,`r:(v)error_result`]
                  (INST_TYPE [`:v sem_env`,`:A`] evaluate_Apps_f_err))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`t1:(FFI)state`; `env:v sem_env`; `x':exp`; `y:exp`; `s1:(FFI)state`;
                   `vy:v`; `s2:(FFI)state`; `Closure env1 n (Funs ns1 e)`]
                  EVPROPSAUX_App2_Opapp) THEN
    ASM_REWRITE_TAC[do_opapp_def] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n2:varN` (X_CHOOSE_THEN `ns2:varN list` SUBST_ALL_TAC))
    (ISPEC `ns1:varN list` list_CASES) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN EVPROPSAUX_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ast_Funs_def]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`App Opapp [x'; y]`; `CONS (n2:varN) ns2`; `a:v list`; `st:(FFI)state`;
     `t1:(FFI)state`; `dec_clock (s2:(FFI)state)`; `env:v sem_env`;
     `sem_env_v_fupd (combin_K (nsBind n vy (sem_env_v env1))) (env1:v sem_env)`; `e:exp`]) THEN
  REWRITE_TAC[HD; TL; NOT_CONS_NIL; LENGTH] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t1:(FFI)state`; `env:v sem_env`; `x':exp`; `y:exp`; `s1:(FFI)state`;
                     `vy:v`; `s2:(FFI)state`; `env1:v sem_env`; `n:varN`;
                     `Fun n2 (Funs ns2 e)`] EVPROPSAUX_App_Opapp_Closure) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[evaluate_def];
      REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds; K_THM; LENGTH] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN EVPROPSAUX_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[dec_clock_def; state_INFO.ri_fupdfupds; K_o_THM]);;

let EVPROPSAUX_clock_fupd_same = prove
 (`!(s:(FFI)state) c. state_clock s = c ==> state_clock_fupd (combin_K c) s = s`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[with_same_clock]);;

let evaluate_Apps = prove
 (`!xs (st:(FFI)state) env s1 (s2:(FFI)state) vs.
     evaluate st env xs = (s1,Rval vs) /\
     LENGTH xs = SUC (LENGTH ns) /\
     nsLookup (sem_env_v env) n = SOME clos_v /\
     do_opapp [clos_v; LAST vs] = SOME (env1,Funs ns e) ==>
     evaluate st env [Apps (Var n) (REVERSE xs)] =
     if state_clock s1 < LENGTH xs
     then (state_clock_fupd (combin_K 0) s1,Rerr (Rabort Rtimeout_error))
     else evaluate (state_clock_fupd (combin_K (state_clock s1 - LENGTH xs)) s1)
            (sem_env_v_fupd (combin_K (nsAppend (alist_to_ns (ZIP (REVERSE ns) (BUTLAST vs)))
                                  (sem_env_v env1))) env1) [e]`,
  GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `x0:exp` (X_CHOOSE_THEN `xs1:exp list` SUBST1_TAC))
    (ISPEC `xs:exp list` SNOC_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SNOC_APPEND; evaluate_append; REVERSE_APPEND; REVERSE;
                                  APPEND; ast_Apps_def; LENGTH_APPEND; LENGTH] THEN
  MP_TAC(ISPEC `evaluate (st:(FFI)state) env xs1` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(FFI)state` (X_CHOOSE_THEN `q1:(v list,v)result`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASES_ON `q1:(v list,v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPEC `evaluate (t1:(FFI)state) env [x0]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(FFI)state` (X_CHOOSE_THEN `q2:(v list,v)result`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `q2:(v list,v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `?v0. a':v list = [v0]` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[evaluate_sing]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST_APPEND; NOT_CONS_NIL; LAST]) THEN
  REWRITE_TAC[BUTLAST_APPEND; NOT_CONS_NIL; BUTLAST; APPEND_NIL] THEN
  (* the first application, of the function to the last argument *)
  SUBGOAL_THEN
   `evaluate (t1:(FFI)state) env [App Opapp [Var n; x0]] =
    if state_clock s1 = 0 then (s1,Rerr (Rabort Rtimeout_error))
    else evaluate (dec_clock s1) env1 [Funs ns e]`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t1:(FFI)state`; `env:v sem_env`; `Var n`; `x0:exp`; `s1:(FFI)state`;
                   `v0:v`; `s1:(FFI)state`; `clos_v:v`] EVPROPSAUX_App2_Opapp) THEN
    ASM_REWRITE_TAC[evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `n1:varN` (X_CHOOSE_THEN `ns1:varN list` SUBST_ALL_TAC))
    (ISPEC `ns:varN list` list_CASES) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ADD_CLAUSES; SUC_INJ; LENGTH_EQ_NIL]) THENL
   [(* one argument *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[evaluate_nil; PAIR_EQ; injectivity "result"]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN
    ASM_REWRITE_TAC[REVERSE; ast_Apps_def; ZIP; LENGTH; ADD_CLAUSES; ast_Funs_def;
                    alist_to_ns_nil; nsAppend_nsEmpty; with_same_v;
                    ARITH_RULE `x < SUC 0 <=> x = 0`; dec_clock_def; ONE] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[EVPROPSAUX_clock_fupd_same];
    ALL_TAC] THEN
  ASM_CASES_TAC `state_clock (s1:(FFI)state) = 0` THENL
   [(* no clock for the first application *)
    ASM_REWRITE_TAC[ARITH_RULE `0 < n + SUC 0`] THEN
    ASM_SIMP_TAC[EVPROPSAUX_clock_fupd_same] THEN
    MATCH_MP_TAC (INST [`Rabort Rtimeout_error:(v)error_result`,`r:(v)error_result`]
                    (INST_TYPE [`:v sem_env`,`:A`] evaluate_Apps_f_err)) THEN
    MAP_EVERY EXISTS_TAC [`a:v list`; `t1:(FFI)state`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EVPROPSAUX_evaluate_Funs_CONS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(state_clock (s1:(FFI)state) = 0)`]) THEN
  ASM_CASES_TAC `state_clock (s1:(FFI)state) < LENGTH (xs1:exp list) + SUC 0` THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`xs1:exp list`; `App Opapp [Var n; x0]`; `CONS (n1:varN) ns1`;
                   `a:v list`; `st:(FFI)state`; `t1:(FFI)state`; `dec_clock (s1:(FFI)state)`;
                   `env:v sem_env`; `env1:v sem_env`; `e:exp`]
                  evaluate_Apps_Funs_timeout) THEN
    ASM_REWRITE_TAC[HD; TL; NOT_CONS_NIL; LENGTH] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds; K_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN EVPROPSAUX_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[dec_clock_def; state_INFO.ri_fupdfupds; K_o_THM]];
    MP_TAC(ISPECL [`xs1:exp list`; `App Opapp [Var n; x0]`; `CONS (n1:varN) ns1`;
                   `a:v list`; `st:(FFI)state`; `t1:(FFI)state`; `dec_clock (s1:(FFI)state)`;
                   `env:v sem_env`; `env1:v sem_env`; `e:exp`]
                  evaluate_Apps_Funs) THEN
    ASM_REWRITE_TAC[HD; TL; NOT_CONS_NIL; LENGTH] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds; K_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN EVPROPSAUX_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[dec_clock_def; state_INFO.ri_fupdfupds; K_o_THM;
                  state_INFO.ri_accfupds; K_THM] THEN
      REWRITE_TAC[ARITH_RULE `!x m. x - 1 - SUC m = x - (SUC m + SUC 0)`]]]);;
