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

(* local helpers for do_app_lemma: the first components of a mapped list, *)
(* a paired lambda as a pair map, and the Install case                     *)
let BVLPROPSAUX_MAP_FST_PAIR_MAP = prove
 (`!(f:B->C) (l:(A#B)list). MAP FST (MAP (I ## f) l) = MAP FST l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; PAIR_MAP; FST; I_THM]);;

let BVLPROPSAUX_PAIR_LAMBDA_MAP = prove
 (`!(g:B->C). (\(k:A,v). k,g v) = (I ## g)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let BVLPROPSAUX_rt_do_install = prove
 (CASE_TERM `!vs (t:(C,FFI)bvl_state) r. bvl_inlineProof_state_rel t r ==>
  (match (bvl_do_install vs r:(bvl_v#(C,FFI)bvl_state,bvl_v)result) with
     Rerr err -> bvl_do_install vs t = Rerr err
   | Rval (v,r2) -> ?t2. bvl_inlineProof_state_rel t2 r2 /\
                         bvl_do_install vs t = (Rval (v,t2):(bvl_v#(C,FFI)bvl_state,bvl_v)result))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVLPROPSAUX_state_rel_eq]) THEN
   MP_TAC(ISPEC `bvl_state_compile_oracle (t:(C,FFI)bvl_state) 0` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `cfg:C` (X_CHOOSE_THEN `progs:(num#num#bvl_exp)list`
     ASSUME_TAC)) THEN
   REWRITE_TAC[bvl_do_install_def] THEN
   ASM_REWRITE_TAC[o_THM; domain_map; PAIR_MAP_THM; I_THM; LET_DEF; LET_END_DEF;
                   BVLPROPSAUX_MAP_FST_PAIR_MAP; shift_seq_def] THEN BETA_TAC THEN
   REWRITE_TAC[o_THM; FST_PAIR_MAP; I_THM] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[BVLPROPSAUX_MAP_FST_PAIR_MAP] THEN
   FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
     `bvl_state_compile_oracle (t:(C,FFI)bvl_state) 0 = (cfg,progs)`)) THEN
   SPEC_TAC(`progs:(num#num#bvl_exp)list`,`progs:(num#num#bvl_exp)list`) THEN
   GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `progs:(num#num#bvl_exp)list` list_CASES) THEN
   REWRITE_TAC[MAP] THENL
    [ALL_TAC;
     MP_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ae:num#bvl_exp` SUBST1_TAC)) THEN
     MP_TAC(ISPEC `ae:num#bvl_exp` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
     REWRITE_TAC[PAIR_MAP_THM; I_THM]] THEN
   CASE_REWRITE_TAC[] THEN REPEAT CASE_TAC THEN
   REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
   REWRITE_TAC[BVLPROPSAUX_state_rel_eq; bvl_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM; map_union; map_fromAList; BVLPROPSAUX_PAIR_LAMBDA_MAP] THEN
   REWRITE_TAC[MAP; PAIR_MAP_THM; I_THM; ETA_AX]);;

(* HOL4 [local]; HOL4 binds do_app_lemma twice: this first one is for the  *)
(* removal of ticks (the second, for let_op, is bvl_inlineProof_do_app_lemma) *)
let BVLPROPSAUX_rt_do_app_lemma = prove
 (CASE_TERM `!op a (t':(C,FFI)bvl_state) r.
    bvl_inlineProof_state_rel t' r ==>
    match bvl_do_app op (REVERSE a) r with
      Rerr err -> bvl_do_app op (REVERSE a) t' = Rerr err
    | Rval (v,r2) -> ?t2. bvl_inlineProof_state_rel t2 r2 /\
                          bvl_do_app op (REVERSE a) t' = Rval (v,t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[BVLPROPSAUX_do_app_Install] THEN
    MATCH_MP_TAC BVLPROPSAUX_rt_do_install THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVLPROPSAUX_state_rel_eq] o
              check (fun th -> BVLPROPSAUX_has_const "bvl_inlineProof_state_rel" (concl th))) THEN
  SUBGOAL_THEN
   `bvl_state_code_fupd (K (bvl_state_code t'))
      (bvl_state_compile_fupd (K (bvl_state_compile t'))
        (bvl_state_compile_oracle_fupd (K (bvl_state_compile_oracle t'))
          (r:(C,FFI)bvl_state))) = t'` ASSUME_TAC THENL
   [REWRITE_TAC[bvl_state_component_equality; bvl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvl_do_app op (REVERSE a) (r:(C,FFI)bvl_state)` (cases "result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `a':bvl_v#(C,FFI)bvl_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `r2:(C,FFI)bvl_state`
      SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `REVERSE (a:bvl_v list)`; `r:(C,FFI)bvl_state`;
                   `v:bvl_v`; `r2:(C,FFI)bvl_state`; `bvl_state_code (t':(C,FFI)bvl_state)`;
                   `bvl_state_compile (t':(C,FFI)bvl_state)`;
                   `bvl_state_compile_oracle (t':(C,FFI)bvl_state)`]
                  bvl_do_app_with_code) THEN
    ASM_REWRITE_TAC[domain_map; SUBSET_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_do_app_const) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(op = clos_Install)`]) THEN
    REWRITE_TAC[BVLPROPSAUX_state_rel_eq; bvl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`op:clos_op`; `REVERSE (a:bvl_v list)`; `r:(C,FFI)bvl_state`;
                   `a':(bvl_v)error_result`; `bvl_state_code (t':(C,FFI)bvl_state)`;
                   `bvl_state_compile (t':(C,FFI)bvl_state)`;
                   `bvl_state_compile_oracle (t':(C,FFI)bvl_state)`]
                  do_app_with_code_err_not_Install) THEN
    ASM_REWRITE_TAC[domain_map; SUBSET_REFL]]);;

(* local helpers for evaluate_remove_ticks: find_code in a mapped code     *)
(* table, and the clock of dec_clock                                        *)
let BVLPROPSAUX_find_code_map = prove
 (`!dest args code (f:bvl_exp->bvl_exp).
     bvl_find_code dest args (map (I ## f) code) =
     OPTION_MAP (I ## f) (bvl_find_code dest args code)`,
  GEN_TAC THEN CASES_ON `dest:num option` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_find_code_def; lookup_map] THEN
  TRY (COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
       CASES_ON `LAST (args:bvl_v list)` THEN CASE_REWRITE_TAC[OPTION_MAP_DEF]) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
              (try fst (dest_const (rator (rator t))) = "lookup" with Failure _ -> false)) w in
    CASES_ON t) THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF] THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> is_var t && type_of t = `:num#bvl_exp`) w in
    CASES_ON t) THEN
  CASE_REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

let BVLPROPSAUX_dec_clock_clock = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_clock (bvl_dec_clock n s) = bvl_state_clock s - n`,
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM]);;

(* local tactics for evaluate_remove_ticks: the split of the compiled      *)
(* evaluation, the measure of the induction (clock, then size) and the     *)
(* instances of the induction hypothesis for the compiled sub-evaluations  *)
let BVLPROPSAUX_bvl_size_rws =
  filter (fun th -> exists (fun c -> let c = snd (strip_forall c) in is_eq c &&
            (try fst (dest_const (rator (lhs c))) = "bvl_exp_size" with Failure _ -> false))
            (conjuncts (concl th))) !the_size_defs @
  filter (fun th -> can (find_term (fun t -> is_const t &&
            (let n = fst (dest_const t) in String.length n > 12 &&
                                           String.sub n 0 12 = "bvl_exp_size")))
            (concl th)) (flat (map snd (!the_size_aux_eqs)));;

let BVLPROPSAUX_RT_SPLIT_TAC (cons:bool) : tactic =
  FIRST_X_ASSUM(BVLPROPSAUX_FRESH_STRIP_TAC o REWRITE_RULE BVLPROPSAUX_eval_case_eqs o
     BETA_RULE o REWRITE_RULE[LET_DEF; LET_END_DEF; bvl_inline_remove_ticks_SING] o
     PURE_ONCE_REWRITE_RULE[if cons then bvl_evaluate_CONS else bvl_evaluate_def] o
     PURE_REWRITE_RULE[bvl_inline_remove_ticks_def] o
     check (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
            BVLPROPSAUX_has_const "bvl_inline_remove_ticks" (lhs c))) THEN
  TRY RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN BVLPROPSAUX_CLEAN_TAC;;

let BVLPROPSAUX_is_num_fact (t:term) =
  let t = if is_neg t then rand t else t in
  (is_comb t && is_comb (rator t) &&
   (try mem (fst (dest_const (rator (rator t)))) ["<"; "<="] with Failure _ -> false)) ||
  (is_eq t && type_of (lhs t) = `:num`);;

let BVLPROPSAUX_RT_MEASURE_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c))
              (map snd asl) in
  let cls = mapfilter (MATCH_MP bvl_evaluate_clock) evs in
  let nums = filter (fun th -> BVLPROPSAUX_is_num_fact (concl th)) (map snd asl) in
  (MAP_EVERY MP_TAC (cls @ nums) THEN
   REWRITE_TAC(BVLPROPSAUX_dec_clock_clock :: bvl_inc_clock_clock :: list_size ::
               BVLPROPSAUX_bvl_size_rws) THEN
   ARITH_TAC) g;;

let BVLPROPSAUX_RT_IH1_TAC : tactic = fun (asl,w as g) ->
  let ihth = snd (find (fun (_,th) -> let c = concl th in is_forall c &&
        (let v,b = dest_forall c in type_of v = `:bvl_exp list` &&
          BVLPROPSAUX_has_const "list_size" b)) asl) in
  let is_rt_ev th = let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
        (let l = fst (dest_pair (rand (lhs c))) in
         is_comb l && is_const (rator l) &&
         fst (dest_const (rator l)) = "bvl_inline_remove_ticks") in
  let rels = filter (fun th -> let c = concl th in
                       (try fst (dest_const (fst (strip_comb c))) =
                            "bvl_inlineProof_state_rel" with Failure _ -> false))
                    (map snd asl) in
  let ok th = is_rt_ev th &&
    (let s1 = snd (dest_pair (snd (dest_pair (rand (lhs (concl th)))))) in
     exists (fun r -> rand (concl r) = s1) rels) in
  let ev = find ok (map snd asl) in
  let args = rand (lhs (concl ev)) in
  let l = rand (fst (dest_pair args)) in
  let s1 = snd (dest_pair (snd (dest_pair args))) in
  let rel = find (fun r -> rand (concl r) = s1) rels in
  (MP_TAC (SPECL [l; s1] ihth) THEN ANTS_TAC THENL
    [BVLPROPSAUX_RT_MEASURE_TAC;
     DISCH_THEN(fun th -> BVLPROPSAUX_FRESH_STRIP_TAC (MATCH_MP th (CONJ rel ev))) THEN
     ASSUME_TAC (MATCH_MP bvl_evaluate_clock ev) THEN
     FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = concl ev))]) g;;

let BVLPROPSAUX_RT_IH_TAC : tactic = REPEAT BVLPROPSAUX_RT_IH1_TAC;;

(* a local tactic for evaluate_remove_ticks: the source evaluations given  *)
(* by the induction hypothesis (each with its own extra clock) are chained *)
(* with evaluate_add_clock; the witness is the sum of the extra clocks     *)
let BVLPROPSAUX_RT_CHAIN_TAC (final:term option) : tactic = fun (asl,w as g) ->
  let st_of th = snd (dest_pair (snd (dest_pair (rand (lhs (concl th)))))) in
  let is_inc st = is_comb st && is_comb (rator st) &&
    (try fst (dest_const (rator (rator st))) = "bvl_inc_clock" with Failure _ -> false) &&
    is_var (rand (rator st)) in
  let srcs = filter (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
                       is_inc (st_of th)) (map snd asl) in
  let ckv,body = dest_exists w in
  let tv,body2 = dest_exists body in
  let t0 = rand (snd (dest_pair (snd (dest_pair (rand (lhs (lhand body2))))))) in
  let rec chain u acc =
    match (try Some (find (fun th -> rand (st_of th) = u) srcs) with Failure _ -> None) with
      Some th -> chain (snd (dest_pair (rhs (concl th)))) (th :: acc)
    | None -> rev acc in
  let ths = chain t0 [] in
  let cks = map (fun th -> rand (rator (st_of th))) ths in
  let rec tots l = match l with
      [] -> []
    | [c] -> [c]
    | c :: rest -> let tr = tots rest in mk_binop `(+):num->num->num` (hd tr) c :: tr in
  let tl = tots cks in
  let shifted =
    let rec go ths tl = match ths, tl with
        [th], [_] -> [th]
      | th :: ths', _ :: (tnext :: _ as tl') ->
          let r = fst (dest_pair (rhs (concl th))) in
          let ntm = mk_neg (mk_eq (r, `Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result`)) in
          let nt = EQT_ELIM (REWRITE_CONV BVLPROPSAUX_eval_simps ntm) in
          let sh = REWRITE_RULE[inc_clock_add]
                     (SPEC tnext (MATCH_MP bvl_evaluate_add_clock (CONJ th nt))) in
          sh :: go ths' tl'
      | _ -> [] in
    go ths tl in
  let total = if tl = [] then `0` else hd tl in
  let tfin = match final with Some f -> f | None ->
    if ths = [] then t0 else snd (dest_pair (rhs (concl (last ths)))) in
  (EXISTS_TAC total THEN EXISTS_TAC tfin THEN
   REWRITE_TAC[inc_clock0] THEN
   MAP_EVERY ASSUME_TAC shifted) g;;

(* local helpers for the Tick, Force and Call cases of evaluate_remove_ticks *)
let BVLPROPSAUX_state_rel_dec_clock = prove
 (`!(t:(C,FFI)bvl_state) s n.
     bvl_inlineProof_state_rel t s ==>
     bvl_inlineProof_state_rel (bvl_dec_clock n t) (bvl_dec_clock n s)`,
  REWRITE_TAC[BVLPROPSAUX_state_rel_eq; bvl_dec_clock_def; bvl_state_INFO.ri_accfupds;
              K_THM] THEN MESON_TAC[]);;

let BVLPROPSAUX_state_rel_clock0 = prove
 (`!(t:(C,FFI)bvl_state) s.
     bvl_inlineProof_state_rel t s ==>
     bvl_inlineProof_state_rel (bvl_state_clock_fupd (K 0) t) (bvl_state_clock_fupd (K 0) s)`,
  REWRITE_TAC[BVLPROPSAUX_state_rel_eq; bvl_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

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
 (`!(t:(C,FFI)bvl_state) s d vs.
     bvl_inlineProof_state_rel t s ==>
     (!args e'. bvl_find_code d vs (bvl_state_code s) = SOME (args,e') ==>
                ?e. bvl_find_code d vs (bvl_state_code t) = SOME (args,e) /\
                    e' = HD (bvl_inline_remove_ticks [e])) /\
     (bvl_find_code d vs (bvl_state_code s) = NONE ==>
      bvl_find_code d vs (bvl_state_code t) = NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_state_rel_eq] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[BVLPROPSAUX_find_code_map] THEN
  STRUCT_CASES_TAC(ISPEC `bvl_find_code d vs (bvl_state_code (t:(C,FFI)bvl_state))`
                         (cases "option")) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `a:bvl_v list # bvl_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* the source facts for the compiled code lookups, and the relation for   *)
(* the states of the compiled bodies (idempotent)                          *)
let BVLPROPSAUX_RT_PREP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = filter (fun th -> let c = concl th in
                       (try fst (dest_const (fst (strip_comb c))) =
                            "bvl_inlineProof_state_rel" with Failure _ -> false)) asms in
  let rel_of s = find (fun r -> rand (concl r) = s) rels in
  let is_fc th = let c = concl th in is_eq c &&
    (try fst (dest_const (fst (strip_comb (lhs c)))) = "bvl_find_code"
     with Failure _ -> false) in
  let fcs = filter is_fc asms in
  let done_fc th =
    let _,[d;vs;cd] = strip_comb (lhs (concl th)) in
    let s = rand cd in
    let u = rand (rator (concl (rel_of s))) in
    exists (fun th' -> let _,[d';vs';cd'] = strip_comb (lhs (concl th')) in
                       d' = d && vs' = vs && rand cd' = u) fcs in
  let fc_tac th =
    if done_fc th then ALL_TAC else
    let _,[d;vs;cd] = strip_comb (lhs (concl th)) in
    let s = rand cd in
    let r = rel_of s in
    let lem = MATCH_MP (SPECL [rand (rator (concl r)); s; d; vs] BVLPROPSAUX_find_code_rel) r in
    if rhs (concl th) = `NONE:(bvl_v list # bvl_exp)option` then
      ASSUME_TAC (MP (CONJUNCT2 lem) th)
    else
      BVLPROPSAUX_FRESH_STRIP_TAC (MATCH_MP (CONJUNCT1 lem) th) in
  let evs = filter (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c)) asms in
  let dec_states = setify (mapfilter (fun th ->
    let st = snd (dest_pair (snd (dest_pair (rand (lhs (concl th)))))) in
    let f,args = strip_comb st in
    if is_const f && fst (dest_const f) = "bvl_dec_clock" then (el 0 args, el 1 args)
    else failwith "") evs) in
  let dec_tac (n,s) =
    let r = rel_of s in
    let th = SPEC n (MATCH_MP BVLPROPSAUX_state_rel_dec_clock r) in
    if exists (fun r' -> concl r' = concl th) rels then failwith "done"
    else ASSUME_TAC th in
  (EVERY (mapfilter fc_tac fcs) THEN TRY RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[bvl_inline_remove_ticks_SING]) THEN
   EVERY (mapfilter dec_tac dec_states)) g;;

let BVLPROPSAUX_RT_SRC_START (w:term) =
  let ckv,body = dest_exists w in
  let tv,body2 = dest_exists body in
  rand (snd (dest_pair (snd (dest_pair (rand (lhs (lhand body2)))))));;

let BVLPROPSAUX_RT_is_src st = is_comb st && is_comb (rator st) &&
    (try fst (dest_const (rator (rator st))) = "bvl_inc_clock" with Failure _ -> false) &&
    is_var (rand (rator st));;

let BVLPROPSAUX_RT_st_of th = snd (dest_pair (snd (dest_pair (rand (lhs (concl th))))));;

let BVLPROPSAUX_RT_TICK_TAC : tactic = fun (asl,w as g) ->
  let t0 = BVLPROPSAUX_RT_SRC_START w in
  let th = find (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
                   let st = BVLPROPSAUX_RT_st_of th in
                   BVLPROPSAUX_RT_is_src st && rand st = t0) (map snd asl) in
  let c = rand (rator (BVLPROPSAUX_RT_st_of th)) in
  let t1 = snd (dest_pair (rhs (concl th))) in
  (EXISTS_TAC (mk_binop `(+):num->num->num` c `1`) THEN EXISTS_TAC t1 THEN
   ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
   REWRITE_TAC[bvl_inc_clock_clock; ARITH_RULE `!a c. ~(a + c + 1 = 0)`;
               BVLPROPSAUX_dec_inc_1] THEN
   ASM_REWRITE_TAC[]) g;;

let BVLPROPSAUX_RT_CASES = [pair_CASE; case_def "result"; case_def "error_result";
  case_def "option"; case_def "bvl_dest_thunk_ret"; case_def "thunk_mode"];;

let BVLPROPSAUX_RT_OP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let da = find (fun th -> let c = concl th in is_eq c &&
     (try fst (dest_const (fst (strip_comb (lhs c)))) = "bvl_do_app" with Failure _ -> false))
     asms in
  let _,[op;rv;s1] = strip_comb (lhs (concl da)) in
  let rel = find (fun th -> let c = concl th in
     (try fst (dest_const (fst (strip_comb c))) = "bvl_inlineProof_state_rel"
      with Failure _ -> false) && rand c = s1) asms in
  let t1 = rand (rator (concl rel)) in
  let lem = CASE_REWRITE_RULE[] (REWRITE_RULE[da]
              (MATCH_MP (SPECL [op; rand rv; t1; s1] BVLPROPSAUX_rt_do_app_lemma) rel)) in
  let fin = ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
            ASM_REWRITE_TAC BVLPROPSAUX_RT_CASES in
  if is_exists (concl lem) then
    let v = variant (freesl (w :: map concl asms)) `t2:(C,FFI)bvl_state` in
    X_CHOOSE_THEN v (fun th2 -> STRIP_ASSUME_TAC th2 THEN
       BVLPROPSAUX_RT_CHAIN_TAC (Some v) THEN fin) lem g
  else (ASSUME_TAC lem THEN BVLPROPSAUX_RT_CHAIN_TAC None THEN fin) g;;

let BVLPROPSAUX_RT_is_rel th = let c = concl th in
  (try fst (dest_const (fst (strip_comb c))) = "bvl_inlineProof_state_rel"
   with Failure _ -> false);;

let BVLPROPSAUX_RT_SRC_FACT asms (stp:term -> bool) =
  find (fun th -> let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
          let st = BVLPROPSAUX_RT_st_of th in
          BVLPROPSAUX_RT_is_src st && stp (rand st)) asms;;

(* the field equations of a state_rel u s for the refs and the clock *)
let BVLPROPSAUX_RT_FIELDS rel =
  filter (fun th -> let l = lhs (concl th) in
            (try mem (fst (dest_const (rator l))) ["bvl_state_refs"; "bvl_state_clock"]
             with Failure _ -> false))
         (CONJUNCTS (REWRITE_RULE[BVLPROPSAUX_state_rel_eq] rel));;

let BVLPROPSAUX_RT_FORCE_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let t0 = BVLPROPSAUX_RT_SRC_START w in
  let rel0 = find (fun th -> BVLPROPSAUX_RT_is_rel th && rand (rator (concl th)) = t0) asms in
  let flds = BVLPROPSAUX_RT_FIELDS rel0 in
  let dect = mk_comb (mk_comb (`bvl_dec_clock:num->(C,FFI)bvl_state->(C,FFI)bvl_state`, `1`), t0) in
  let res = fst (dest_pair (rhs (lhand (snd (dest_exists (snd (dest_exists w))))))) in
  let wck,wfin =
    try let th = BVLPROPSAUX_RT_SRC_FACT asms (fun u -> u = dect) in
        rand (rator (BVLPROPSAUX_RT_st_of th)), snd (dest_pair (rhs (concl th)))
    with Failure _ ->
      if res = `Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result`
      then `0`, mk_comb (`bvl_state_clock_fupd (K 0):(C,FFI)bvl_state->(C,FFI)bvl_state`, t0)
      else `0`, t0 in
  (RULE_ASSUM_TAC(REWRITE_RULE flds) THEN
   ASSUME_TAC (MATCH_MP BVLPROPSAUX_state_rel_clock0 rel0) THEN
   EXISTS_TAC wck THEN EXISTS_TAC wfin THEN
   ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; inc_clock0] THEN BETA_TAC THEN
   ASM_SIMP_TAC (BVLPROPSAUX_RT_CASES @ [bvl_inc_clock_refs; bvl_inc_clock_code;
     bvl_inc_clock_clock; bvl_dec_clock_1_inc_clock2; ADD_EQ_0])) g;;

let BVLPROPSAUX_RT_CALL_CORE_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let t0 = BVLPROPSAUX_RT_SRC_START w in
  let ev = lhs (lhand (snd (dest_exists (snd (dest_exists w))))) in
  let ticks = el 0 (snd (strip_comb (hd (dest_list (fst (dest_pair (rand ev))))))) in
  let res = fst (dest_pair (rhs (lhand (snd (dest_exists (snd (dest_exists w))))))) in
  let a1th = BVLPROPSAUX_RT_SRC_FACT asms (fun u -> u = t0) in
  let c1 = rand (rator (BVLPROPSAUX_RT_st_of a1th)) in
  let t1 = snd (dest_pair (rhs (concl a1th))) in
  let rel1 = find (fun th -> BVLPROPSAUX_RT_is_rel th && rand (rator (concl th)) = t1) asms in
  let flds = BVLPROPSAUX_RT_FIELDS rel1 in
  let dect = mk_comb (mk_comb (`bvl_dec_clock:num->(C,FFI)bvl_state->(C,FFI)bvl_state`, `1`), t1) in
  try
    let bth = BVLPROPSAUX_RT_SRC_FACT asms (fun u -> u = dect) in
    let c2 = rand (rator (BVLPROPSAUX_RT_st_of bth)) in
    let t2 = snd (dest_pair (rhs (concl bth))) in
    let tc = mk_binop `(+):num->num->num` ticks c2 in
    let total = mk_binop `(+):num->num->num` tc c1 in
    let nt = EQT_ELIM (REWRITE_CONV BVLPROPSAUX_eval_simps
               (mk_neg (mk_eq (fst (dest_pair (rhs (concl a1th))),
                               `Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result`)))) in
    let sh = REWRITE_RULE[inc_clock_add]
               (SPEC tc (MATCH_MP bvl_evaluate_add_clock (CONJ a1th nt))) in
    let ctm = mk_comb (`bvl_state_clock:(C,FFI)bvl_state->num`, t1) in
    (RULE_ASSUM_TAC(REWRITE_RULE flds) THEN ASSUME_TAC sh THEN
     SUBGOAL_THEN (mk_neg (mk_eq (ctm, `0`))) ASSUME_TAC THENL
      [REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th -> BVLPROPSAUX_is_num_fact (concl th) &&
                 free_in ctm (concl th)))) THEN ARITH_TAC; ALL_TAC] THEN
     EXISTS_TAC total THEN EXISTS_TAC t2 THEN
     ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
     ASM_SIMP_TAC (BVLPROPSAUX_RT_CASES @ [bvl_inc_clock_code; bvl_inc_clock_clock;
       BVLPROPSAUX_dec_inc_ticks; ARITH_RULE `~(c = 0) ==> ~(c + t + d < t + 1)`])) g
  with Failure _ ->
    let fin = if res = `Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result`
              then Some (mk_comb (`bvl_state_clock_fupd (K 0):(C,FFI)bvl_state->(C,FFI)bvl_state`, t1))
              else None in
    (RULE_ASSUM_TAC(REWRITE_RULE flds) THEN
     ASSUME_TAC (MATCH_MP BVLPROPSAUX_state_rel_clock0 rel1) THEN
     BVLPROPSAUX_RT_CHAIN_TAC fin THEN
     ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
     ASM_SIMP_TAC (BVLPROPSAUX_RT_CASES @ [bvl_inc_clock_code; bvl_inc_clock_clock;
       ARITH_RULE `c < 1 ==> c + t < t + 1`; ARITH_RULE `c < 1 ==> c < t + 1`])) g;;

let BVLPROPSAUX_RT_CALL_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `0 + 1 = 1`]) THEN BVLPROPSAUX_RT_CALL_CORE_TAC;;

(* the simulation of a source run by a run with fewer ticks (HOL4 proves  *)
(* evaluate_remove_ticks by completeInduct_on the clock and recInduct     *)
(* remove_ticks_ind; here the induction is on the clock and then the size  *)
(* of the expression list, as BVLPROPSAUX_clock_size_ind)                   *)
let BVLPROPSAUX_RT_FIN_TAC : tactic =
  BVLPROPSAUX_RT_CHAIN_TAC None THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; case_def "error_result"];;

let BVLPROPSAUX_RT_CASE_TAC : tactic =
  FIRST [BVLPROPSAUX_RT_FIN_TAC THEN NO_TAC; BVLPROPSAUX_RT_TICK_TAC THEN NO_TAC;
         BVLPROPSAUX_RT_OP_TAC THEN NO_TAC; BVLPROPSAUX_RT_FORCE_TAC THEN NO_TAC;
         BVLPROPSAUX_RT_CALL_TAC THEN NO_TAC];;

let BVLPROPSAUX_rt_sim = prove
 (`!xs (s:(C,FFI)bvl_state) env t res s'.
     bvl_inlineProof_state_rel t s /\
     bvl_evaluate (bvl_inline_remove_ticks xs,env,s) = (res,s') ==>
     ?ck t'. bvl_evaluate (xs,env,bvl_inc_clock ck t) = (res,t') /\
             bvl_inlineProof_state_rel t' s'`,
  MATCH_MP_TAC BVLPROPSAUX_clock_size_ind THEN
  MAP_EVERY X_GEN_TAC [`xs:bvl_exp list`; `s:(C,FFI)bvl_state`] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`env:bvl_v list`; `t:(C,FFI)bvl_state`;
    `res:(bvl_v list,bvl_v)result`; `s':(C,FFI)bvl_state`] THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THENL
   [ALL_TAC;
    STRUCT_CASES_TAC(ISPEC `t':bvl_exp list` list_CASES) THENL
     [CASES_ON `h:bvl_exp`; ALL_TAC]] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> t = `CONS (h:bvl_exp) (CONS h' t'')`)) w
     then BVLPROPSAUX_RT_SPLIT_TAC true g else BVLPROPSAUX_RT_SPLIT_TAC false g) THEN
  BVLPROPSAUX_RT_PREP_TAC THEN BVLPROPSAUX_RT_IH_TAC THEN
  BVLPROPSAUX_RT_PREP_TAC THEN BVLPROPSAUX_RT_IH_TAC THEN
  BVLPROPSAUX_RT_CASE_TAC);;

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
  MP_TAC(ISPECL [`[bvl_Call 0 (SOME start) []]`;
     `bvl_initial_state ffi0 (map (I ## (\x. HD (bvl_inline_remove_ticks [x]))) prog)
        (bvl_inlineProof_remove_ticks_co o co) cc k:(C,FFI)bvl_state`;
     `[]:bvl_v list`;
     `bvl_initial_state ffi0 prog co (bvl_inlineProof_remove_ticks_cc cc) k:(C,FFI)bvl_state`;
     `r:(bvl_v list,bvl_v)result`; `s:(C,FFI)bvl_state`] BVLPROPSAUX_rt_sim) THEN
  REWRITE_TAC[bvl_inline_remove_ticks_def] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BVLPROPSAUX_state_rel_eq; bvl_initial_state_def;
                bvl_state_INFO.ri_accessors; bvl_inlineProof_remove_ticks_co_def;
                bvl_inlineProof_remove_ticks_cc_def];
    ALL_TAC] THEN
  REWRITE_TAC[BVLPROPSAUX_inc_initial_state; BVLPROPSAUX_state_rel_eq] THEN
  MESON_TAC[]);;

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

let BVLPROPSAUX_some_NONE = prove
 (`!P:A->bool. (some) P = NONE <=> !x. ~P x`,
  GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[option_DISTINCT]);;

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
    MP_TAC(ISPEC `bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                    bvl_initial_state (ffi:(FFI)ffi_state) p1
                      (o1:num -> C # (num#num#bvl_exp) list) c1 k)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,bvl_v)result`
      (X_CHOOSE_THEN `s:(C,FFI)bvl_state` ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `r:(bvl_v list,bvl_v)result`;
                                  `s:(C,FFI)bvl_state`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `k + ck:num` THEN
    ASM_MESON_TAC[FST];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC BVLPROPSAUX_bvl_semantics_sim THEN
    ASM_MESON_TAC[]]);;

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
  ASM_MESON_TAC[bvl_inlineProof_exp_rel_rules; subspt_lookup]);;

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
  SUBGOAL_THEN
   `!t limit (cs:(num#bvl_exp)spt) aux cs1 xs.
     tick_inline_all limit cs t aux = (cs1,xs) ==>
     APPEND (MAP FST (REVERSE aux)) (MAP FST t) = MAP FST xs`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tick_inline_all_def; PAIR_EQ; MAP; APPEND_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC(ISPEC `y:num#bvl_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[tick_inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REVERSE; MAP_APPEND; MAP; FST; GSYM APPEND_ASSOC; APPEND]);;

(* HOL4 [local val] tick_compile_prog_IMP *)
let BVLPROPSAUX_tick_compile_prog_IMP = prove
 (`!limit (q0:(num#bvl_exp)spt) k (prog:num#bvl_exp) t cs1 prog1.
     tick_compile_prog limit q0 (CONS (k,prog) t) = (cs1,prog1) ==>
     ?p1 vs. prog1 = CONS (k,p1) vs /\ MAP FST vs = MAP FST t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tick_compile_prog_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP tick_inline_all_names) THEN
  REWRITE_TAC[REVERSE; MAP; APPEND; FST] THEN
  STRUCT_CASES_TAC(ISPEC `prog1:(num#num#bvl_exp)list` list_CASES) THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[FST; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 [local val] subspt_union_lemma (the spt x of HOL4 is renamed) *)
let BVLPROPSAUX_subspt_union_lemma = prove
 (`!(t1:A spt) t2 c x.
     (!k. lookup k t1 = lookup k t2) ==>
     subspt x (union c t1) ==> subspt x (union c t2)`,
  REWRITE_TAC[subspt_def; domain_union; lookup_union; domain_lookup] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local val] tick_inline_all_domain, for any accumulator *)
let BVLPROPSAUX_tick_inline_all_domain = prove
 (`!limit (cs0:(num#bvl_exp)spt) in1 aux cs1 xs.
     tick_inline_all limit cs0 in1 aux = (cs1,xs) ==>
     domain cs1 SUBSET domain cs0 UNION set_of_list (MAP FST xs)`,
  SUBGOAL_THEN
   `!in1 limit (cs0:(num#bvl_exp)spt) aux cs1 xs.
     tick_inline_all limit cs0 in1 aux = (cs1,xs) ==>
     domain cs1 SUBSET domain cs0 UNION set_of_list (MAP FST xs)`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tick_inline_all_def; PAIR_EQ] THEN SET_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC(ISPEC `y:num#bvl_exp` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[tick_inline_all_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP tick_inline_all_names) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_X_ASSUM(MP_TAC o MATCH_MP ih)) THEN
  REWRITE_TAC[REVERSE; MAP_APPEND; MAP; FST] THEN
  COND_CASES_TAC THEN REWRITE_TAC[domain_insert] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SET_OF_LIST_APPEND; set_of_list]) THEN
  REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN ASM SET_TAC[]);;

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
  ASM_MESON_TAC[bvl_inlineProof_exp_rel_rules]);;

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

(* a local helper: exp_rel_tick_inline for tick_inline_sing and          *)
(* tick_inline_list, by structural induction                             *)
let BVLPROPSAUX_exp_rel_rule (i:int) = el i (CONJUNCTS bvl_inlineProof_exp_rel_rules);;

let BVLPROPSAUX_exp_rel_tick_inline_sing = prove
 (`!(cs0:(num#bvl_exp)spt) src_code.
     (!k arity v. lookup k cs0 = SOME (arity,v) ==>
                  ?exp. lookup k src_code = SOME (arity,exp) /\
                        bvl_inlineProof_exp_rel src_code [exp] [v]) ==>
     (!e. bvl_inlineProof_exp_rel src_code [e] [tick_inline_sing cs0 e]) /\
     (!es. bvl_inlineProof_exp_rel src_code es (tick_inline_list cs0 es))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC bvl_exp_INDUCT THEN
  REWRITE_TAC[tick_inline_sing_def] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_ACCEPT_TAC (BVLPROPSAUX_exp_rel_rule 0);
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 3) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 4) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 6) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 5) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 7) THEN ASM_REWRITE_TAC[];
    CASES_ON `a1:num option` THEN CASE_REWRITE_TAC[] THENL
     [MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 10) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CASES_ON `lookup a (cs0:(num#bvl_exp)spt)` THEN CASE_REWRITE_TAC[] THENL
     [MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 10) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `a':num#bvl_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `code:bvl_exp` SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `arity:num`; `code:bvl_exp`] o
                  check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 11) THEN
    MAP_EVERY EXISTS_TAC [`arity:num`; `exp:bvl_exp`] THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC (BVLPROPSAUX_exp_rel_rule 9);
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 8) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC (BVLPROPSAUX_exp_rel_rule 1);
    POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `a1:bvl_exp list` list_CASES) THEN
    REWRITE_TAC[tick_inline_sing_def] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 2) THEN ASM_REWRITE_TAC[]]);;

let exp_rel_tick_inline = prove
 (`!(cs0:(num#bvl_exp)spt) xs src_code.
     (!k arity v. lookup k cs0 = SOME (arity,v) ==>
                  ?exp. lookup k src_code = SOME (arity,exp) /\
                        bvl_inlineProof_exp_rel src_code [exp] [v]) ==>
     bvl_inlineProof_exp_rel src_code xs (tick_inline cs0 xs)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM (CONJUNCT2 tick_inline_sing)] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_exp_rel_tick_inline_sing) THEN
  SIMP_TAC[]);;

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
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_install_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
  MESON_TAC[]);;

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
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_install_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; ADD_CLAUSES]) THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[injectivity "option"; injectivity "list"; PAIR_EQ; GSYM CONJ_ASSOC;
                  injectivity "bvl_v"] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_do_install_eq_Rval = prove
 (`!v1 v2 bytes data (s:(C,FFI)bvl_state) cfg k prog rest cfg'.
     bvl_v_to_bytes v1 = SOME bytes /\ bvl_v_to_words v2 = SOME data /\
     bvl_state_compile_oracle s 0 = (cfg,CONS (k,prog) rest) /\
     DISJOINT (domain (bvl_state_code s))
              (set_of_list (MAP FST (CONS (k,prog) rest))) /\
     ALL_DISTINCT (MAP FST (CONS (k,prog) rest)) /\
     bvl_state_compile s cfg (CONS (k,prog) rest) = SOME (bytes,data,cfg') /\
     FST (bvl_state_compile_oracle s 1) = cfg' ==>
     bvl_do_install [v1; v2] s =
       (Rval (bvl_CodePtr k,
              bvl_state_code_fupd
                (K (union (bvl_state_code s) (fromAList (CONS (k,prog) rest))))
                (bvl_state_compile_oracle_fupd
                   (K (shift_seq 1 (bvl_state_compile_oracle s))) s))
        :(bvl_v#(C,FFI)bvl_state,E)result)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_do_install_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* local helper: a successful inlining compiler call *)
let BVLPROPSAUX_in_cc_SOME = prove
 (`!limit (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option)
     (cs:(num#bvl_exp)spt) cfg prog bytes data cfg'.
     bvl_inlineProof_in_cc limit cc (cs,cfg) prog = SOME (bytes,data,cfg') <=>
     ?cfg1. cc cfg (SND (tick_compile_prog limit cs prog)) = SOME (bytes,data,cfg1) /\
            cfg' = (FST (tick_compile_prog limit cs prog),cfg1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_inlineProof_in_cc_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  MP_TAC(ISPEC `tick_compile_prog limit (cs:(num#bvl_exp)spt) prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `prog1:(num#num#bvl_exp)list` SUBST1_TAC)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; FST; SND] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN
  SPEC_TAC(`(cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) cfg prog1`,
           `r:(((8)word)list#((64)word)list#C)option`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(((8)word)list#((64)word)list#C)option`
                                       (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MP_TAC(ISPEC `a:((8)word)list#((64)word)list#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:((8)word)list` (X_CHOOSE_THEN
    `r1:((64)word)list#C` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r1:((64)word)list#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:((64)word)list` (X_CHOOSE_THEN
    `c1:C` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  MESON_TAC[]);;

(* local helper: the inlining relation after an Install *)
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvl_inlineProof_in_state_rel_def] o
    check (fun th -> BVLPROPSAUX_has_const "bvl_inlineProof_in_state_rel" (concl th))) THEN
  SUBGOAL_THEN `MAP FST (prog1:(num#num#bvl_exp)list) =
                MAP FST (progs:(num#num#bvl_exp)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP tick_inline_all_names o
      REWRITE_RULE[tick_compile_prog_def] o
      check (fun th -> BVLPROPSAUX_has_const "tick_compile_prog" (concl th))) THEN
    REWRITE_TAC[REVERSE; MAP; APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `subspt (cs:(num#bvl_exp)spt) (bvl_state_code (t1:(C,FFI)bvl_state))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `subspt (FST (FST (bvl_state_compile_oracle
       (s1:((num#bvl_exp)spt#C,FFI)bvl_state) 0))) (bvl_state_code (t1:(C,FFI)bvl_state))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k arity v. lookup k (cs:(num#bvl_exp)spt) = SOME (arity,v) ==>
     ?exp. lookup k (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state)) =
             SOME (arity,exp) /\
           bvl_inlineProof_exp_rel (bvl_state_code s1) [exp] [v]` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `lookup k (bvl_state_code (t1:(C,FFI)bvl_state)) = SOME (arity,v)`
      ASSUME_TAC THENL [ASM_MESON_TAC[subspt_lookup]; ALL_TAC] THEN
    SUBGOAL_THEN `?y. lookup k (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state)) =
                      SOME y` MP_TAC THENL
     [REWRITE_TAC[GSYM domain_lookup] THEN
      UNDISCH_TAC `domain (bvl_state_code (t1:(C,FFI)bvl_state)) =
                   domain (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[domain_lookup] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num#bvl_exp` MP_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `y:num#bvl_exp` PAIR_SURJECTIVE) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `lookup k (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state)) = SOME (x,y')`) o
      check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_inlineProof_in_state_rel_def; bvl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[shift_seq_def; FUN_EQ_THM];
    REWRITE_TAC[shift_seq_def; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC tick_compile_prog_res_range THEN
    MAP_EVERY EXISTS_TAC [`progs:(num#num#bvl_exp)list`; `limit:num`;
                          `cs:(num#bvl_exp)spt`] THEN
    ASM_REWRITE_TAC[GSYM DISJOINT];
    REWRITE_TAC[domain_union; domain_fromAList] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union; lookup_fromAList] THEN
  CASES_ON `lookup k (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state))` THEN
  CASE_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `lookup k (bvl_state_code (t1:(C,FFI)bvl_state)) = NONE` ASSUME_TAC THENL
     [REWRITE_TAC[lookup_NONE_domain] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM lookup_NONE_domain] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC tick_compile_prog_IMP_exp_rel THEN
    MAP_EVERY EXISTS_TAC [`limit:num`; `cs:(num#bvl_exp)spt`; `cs1:(num#bvl_exp)spt`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (domain (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state)))
                          (set_of_list (MAP FST (progs:(num#num#bvl_exp)list)))` THEN
    SUBGOAL_THEN `domain (cs:(num#bvl_exp)spt) SUBSET
                  domain (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state))` MP_TAC THENL
     [UNDISCH_TAC `domain (bvl_state_code (t1:(C,FFI)bvl_state)) =
                   domain (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `subspt (cs:(num#bvl_exp)spt) (bvl_state_code (t1:(C,FFI)bvl_state))` THEN
      REWRITE_TAC[subspt_def; SUBSET] THEN MESON_TAC[];
      SET_TAC[]];
    REWRITE_TAC[injectivity "option"] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `lookup k (bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state)) = SOME (arity,exp)`) o
      check (is_forall o concl)) THEN
    STRIP_TAC THEN EXISTS_TAC `exp2:bvl_exp` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN MATCH_MP_TAC subspt_exp_rel THEN
    EXISTS_TAC `bvl_state_code (s1:((num#bvl_exp)spt#C,FFI)bvl_state)` THEN
    ASM_REWRITE_TAC[subspt_union]]);;

(* local tactic: substitute the assumptions var = t for the given names *)
let BVLPROPSAUX_SUBST_VAR_TAC (names:string list) : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> let l = lhs(concl th) in
    if is_var l && mem (fst(dest_var l)) names then SUBST_ALL_TAC th
    else failwith "BVLPROPSAUX_SUBST_VAR_TAC"));;

(* local helper: a successful Install under the inlining relation *)
let BVLPROPSAUX_in_do_install = prove
 (`!limit vs (s1:((num#bvl_exp)spt#C,FFI)bvl_state) (t1:(C,FFI)bvl_state) v s2.
     bvl_inlineProof_in_state_rel limit s1 t1 /\
     bvl_do_install vs s1 =
       (Rval (v,s2):(bvl_v#((num#bvl_exp)spt#C,FFI)bvl_state,bvl_v)result) ==>
     ?t2. bvl_inlineProof_in_state_rel limit s2 t2 /\
          bvl_do_install vs t1 = (Rval (v,t2):(bvl_v#(C,FFI)bvl_state,bvl_v)result)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_do_install_Rval) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v1:bvl_v`; `v2:bvl_v`; `bytes:((8)word)list`; `data:((64)word)list`;
    `csc:(num#bvl_exp)spt#C`; `progs:(num#num#bvl_exp)list`; `k:num`; `prog:num#bvl_exp`;
    `rest:(num#num#bvl_exp)list`; `cfg':(num#bvl_exp)spt#C`] THEN
  STRIP_TAC THEN BVLPROPSAUX_SUBST_VAR_TAC ["vs"; "progs"; "v"; "s2"] THEN
  MP_TAC(ISPEC `csc:(num#bvl_exp)spt#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(num#bvl_exp)spt` (X_CHOOSE_THEN `cfg:C` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvl_inlineProof_in_state_rel_def] o
    check (fun th -> BVLPROPSAUX_has_const "bvl_inlineProof_in_state_rel" (concl th))) THEN
  MP_TAC(ISPEC `tick_compile_prog limit (cs:(num#bvl_exp)spt) (CONS (k,prog) rest)`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `prog1:(num#num#bvl_exp)list` ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p1:num#bvl_exp` (X_CHOOSE_THEN `vs1:(num#num#bvl_exp)list`
    STRIP_ASSUME_TAC) o MATCH_MP BVLPROPSAUX_tick_compile_prog_IMP) THEN
  BVLPROPSAUX_SUBST_VAR_TAC ["prog1"] THEN
  UNDISCH_TAC `bvl_state_compile (s1:((num#bvl_exp)spt#C,FFI)bvl_state) (cs,cfg)
                 (CONS (k,prog) rest) = SOME (bytes,data,cfg')` THEN
  ASM_REWRITE_TAC[BVLPROPSAUX_in_cc_SOME; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `cfg1:C` STRIP_ASSUME_TAC) THEN
  BVLPROPSAUX_SUBST_VAR_TAC ["cfg'"] THEN
  SUBGOAL_THEN `FST (bvl_state_compile_oracle (t1:(C,FFI)bvl_state) 1) = cfg1`
    ASSUME_TAC THENL
   [MP_TAC(ISPEC `bvl_state_compile_oracle (s1:((num#bvl_exp)spt#C,FFI)bvl_state) 1`
                 PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1p:(num#bvl_exp)spt#C` (X_CHOOSE_THEN
      `pr1:(num#num#bvl_exp)list` ASSUME_TAC)) THEN
    SUBGOAL_THEN `c1p = (cs1:(num#bvl_exp)spt,cfg1:C)` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[FST]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `tick_compile_prog limit (cs1:(num#bvl_exp)spt) pr1` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:(num#bvl_exp)spt` (X_CHOOSE_THEN
      `x2:(num#num#bvl_exp)list` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP FST (CONS (k:num,p1:num#bvl_exp) vs1) =
                MAP FST (CONS (k,prog:num#bvl_exp) rest)` ASSUME_TAC THENL
   [REWRITE_TAC[MAP; FST] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v1:bvl_v`; `v2:bvl_v`; `bytes:((8)word)list`; `data:((64)word)list`;
                 `t1:(C,FFI)bvl_state`; `cfg:C`; `k:num`; `p1:num#bvl_exp`;
                 `vs1:(num#num#bvl_exp)list`; `cfg1:C`]
     (INST_TYPE [`:bvl_v`,`:E`] BVLPROPSAUX_do_install_eq_Rval)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  MATCH_MP_TAC BVLPROPSAUX_in_state_rel_install THEN
  MAP_EVERY EXISTS_TAC [`cs:(num#bvl_exp)spt`; `cfg:C`; `cs1:(num#bvl_exp)spt`] THEN
  ASM_REWRITE_TAC[FST]);;

(* HOL4 [local] in_do_app_lemma *)
let bvl_inlineProof_in_do_app_lemma = prove
 (CASE_TERM `!limit op a (s1:((num#bvl_exp)spt#C,FFI)bvl_state) (t1:(C,FFI)bvl_state).
    bvl_inlineProof_in_state_rel limit s1 t1 ==>
    match bvl_do_app op a s1 with
      Rerr err -> (~(err = Rabort Rtype_error) ==> bvl_do_app op a t1 = Rerr err)
    | Rval (v,s2) -> ?t2. bvl_inlineProof_in_state_rel limit s2 t2 /\
                          bvl_do_app op a t1 = Rval (v,t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[BVLPROPSAUX_do_app_Install] THEN
    MP_TAC(ISPEC `bvl_do_install a (s1:((num#bvl_exp)spt#C,FFI)bvl_state):
                    (bvl_v#((num#bvl_exp)spt#C,FFI)bvl_state,bvl_v)result`
                 (cases "result")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `a':bvl_v#((num#bvl_exp)spt#C,FFI)bvl_state` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN
        `s2:((num#bvl_exp)spt#C,FFI)bvl_state` SUBST_ALL_TAC)) THEN
      CASE_REWRITE_TAC[] THEN MATCH_MP_TAC BVLPROPSAUX_in_do_install THEN
      EXISTS_TAC `s1:((num#bvl_exp)spt#C,FFI)bvl_state` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_do_install_Rerr) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bvl_inlineProof_in_state_rel_def] o
    check (fun th -> BVLPROPSAUX_has_const "bvl_inlineProof_in_state_rel" (concl th))) THEN
  SUBGOAL_THEN
   `bvl_state_REC (bvl_state_globals (s1:((num#bvl_exp)spt#C,FFI)bvl_state))
      (bvl_state_refs s1) (bvl_state_clock s1)
      (bvl_state_compile (t1:(C,FFI)bvl_state)) (bvl_state_compile_oracle t1)
      (bvl_state_code t1) (bvl_state_ffi s1) = t1` ASSUME_TAC THENL
   [REWRITE_TAC[bvl_state_component_equality; bvl_state_INFO.ri_accessors] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvl_do_app op a (s1:((num#bvl_exp)spt#C,FFI)bvl_state)` (cases "result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `a':bvl_v#((num#bvl_exp)spt#C,FFI)bvl_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `s2:((num#bvl_exp)spt#C,FFI)bvl_state`
      SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:((num#bvl_exp)spt#C,FFI)bvl_state`;
                   `v:bvl_v`; `s2:((num#bvl_exp)spt#C,FFI)bvl_state`;
                   `t1:(C,FFI)bvl_state`] do_app_Rval_swap) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_do_app_const) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(op = clos_Install)`]) THEN
    REWRITE_TAC[bvl_inlineProof_in_state_rel_def; bvl_state_INFO.ri_accessors] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:((num#bvl_exp)spt#C,FFI)bvl_state`;
                   `a':(bvl_v)error_result`; `t1:(C,FFI)bvl_state`] do_app_Rerr_swap) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* HOL4 exp_rel_refl *)
let bvl_inlineProof_exp_rel_refl = prove
 (`!(cs:(num#bvl_exp)spt) xs. bvl_inlineProof_exp_rel cs xs xs`,
  GEN_TAC THEN
  SUBGOAL_THEN `(!e. bvl_inlineProof_exp_rel (cs:(num#bvl_exp)spt) [e] [e]) /\
                (!es. bvl_inlineProof_exp_rel cs es es)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC bvl_exp_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_ACCEPT_TAC (BVLPROPSAUX_exp_rel_rule 0);
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 3) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 4) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 6) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 5) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 7) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 10) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC (BVLPROPSAUX_exp_rel_rule 9);
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 8) THEN ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC (BVLPROPSAUX_exp_rel_rule 1);
    POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `a1:bvl_exp list` list_CASES) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (BVLPROPSAUX_exp_rel_rule 2) THEN ASM_REWRITE_TAC[]]);;

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

(* local helpers for evaluate_inline: the clock updates and find_code *)
let BVLPROPSAUX_in_state_rel_dec_clock = prove
 (`!limit (s:((num#bvl_exp)spt#C,FFI)bvl_state) (t:(C,FFI)bvl_state) n.
     bvl_inlineProof_in_state_rel limit s t ==>
     bvl_inlineProof_in_state_rel limit (bvl_dec_clock n s) (bvl_dec_clock n t)`,
  REWRITE_TAC[bvl_inlineProof_in_state_rel_def; bvl_dec_clock_def;
              bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_in_state_rel_clock0 = prove
 (`!limit (s:((num#bvl_exp)spt#C,FFI)bvl_state) (t:(C,FFI)bvl_state).
     bvl_inlineProof_in_state_rel limit s t ==>
     bvl_inlineProof_in_state_rel limit (bvl_state_clock_fupd (K 0) s)
                                        (bvl_state_clock_fupd (K 0) t)`,
  REWRITE_TAC[bvl_inlineProof_in_state_rel_def; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_in_find_code = prove
 (`!limit (s:((num#bvl_exp)spt#C,FFI)bvl_state) (t:(C,FFI)bvl_state) dest vs args exp.
     bvl_inlineProof_in_state_rel limit s t /\
     bvl_find_code dest vs (bvl_state_code s) = SOME (args,exp) ==>
     ?exp2. bvl_find_code dest vs (bvl_state_code t) = SOME (args,exp2) /\
            bvl_inlineProof_exp_rel (bvl_state_code s) [exp] [exp2]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_inlineProof_in_state_rel_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!loc arity e. lookup loc (bvl_state_code (s:((num#bvl_exp)spt#C,FFI)bvl_state)) =
                    SOME (arity,e) ==>
      ?e2. lookup loc (bvl_state_code (t:(C,FFI)bvl_state)) = SOME (arity,e2) /\
           bvl_inlineProof_exp_rel (bvl_state_code s) [e] [e2]` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    BVLPROPSAUX_has_const "bvl_find_code" (concl th))) THEN
  CASES_ON `dest:num option` THEN REWRITE_TAC[bvl_find_code_def] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `LAST (vs:bvl_v list)` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `lookup a (bvl_state_code (s:((num#bvl_exp)spt#C,FFI)bvl_state))` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"];
    CASES_ON `lookup a (bvl_state_code (s:((num#bvl_exp)spt#C,FFI)bvl_state))` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"]] THEN
  MP_TAC(ISPEC `a':num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
    `lookup a (bvl_state_code (s:((num#bvl_exp)spt#C,FFI)bvl_state)) = SOME (arity,e)`)) THEN
  STRIP_TAC THEN EXISTS_TAC `e2:bvl_exp` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* local tactics for evaluate_inline: invert exp_rel, split the source     *)
(* evaluation, apply the induction hypotheses to the source                *)
(* sub-evaluations, and compute the inlined evaluation                     *)
let BVLPROPSAUX_in_src_ty = `:((num#bvl_exp)spt#C,FFI)bvl_state`;;

let BVLPROPSAUX_in_inline_find_code = prove
 (`!(c0:(num#A)spt) c n vs args e arity x.
     subspt c0 c /\ lookup n c0 = SOME (arity,x) /\
     bvl_find_code (SOME n) vs c = SOME (args,e) ==>
     args = vs /\ e = x /\ LENGTH vs = arity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subspt_lookup] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `lookup n (c0:(num#A)spt) = SOME (arity,x)`)) THEN
  DISCH_TAC THEN UNDISCH_TAC `bvl_find_code (SOME n) vs (c:(num#A)spt) = SOME (args,e)` THEN
  ASM_REWRITE_TAC[bvl_find_code_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  MESON_TAC[]);;

let BVLPROPSAUX_bvl_expand_env_eq = prove
 (`!xs a (s:(C,FFI)bvl_state) r s'.
     bvl_evaluate (xs,a,s) = (r,s') /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     !env. bvl_evaluate (xs,APPEND a env,s) = (r,s')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`xs:bvl_exp list`; `a:bvl_v list`; `s:(C,FFI)bvl_state`;
                 `env:bvl_v list`] bvl_evaluate_expand_env) THEN
  ASM_REWRITE_TAC[FST]);;

let BVLPROPSAUX_is_in_rel (t:term) =
  try fst (dest_const (fst (strip_comb t))) = "bvl_inlineProof_in_state_rel"
  with Failure _ -> false;;

let BVLPROPSAUX_is_exp_rel (t:term) =
  try fst (dest_const (fst (strip_comb t))) = "bvl_inlineProof_exp_rel"
  with Failure _ -> false;;

let BVLPROPSAUX_is_src_ev (t:term) =
  is_eq t && BVLPROPSAUX_is_ev (lhs t) &&
  type_of (snd (dest_pair (snd (dest_pair (rand (lhs t)))))) = BVLPROPSAUX_in_src_ty;;

let BVLPROPSAUX_in_is_main (t:term) =
  let vs,b = strip_forall t in
  length vs >= 4 && is_imp b && is_conj (lhand b) &&
  BVLPROPSAUX_is_in_rel (lhand (lhand b));;

let rec BVLPROPSAUX_UNDER_FORALL_CONV (conv:conv) (tm:term) =
  if is_forall tm then BINDER_CONV (BVLPROPSAUX_UNDER_FORALL_CONV conv) tm else conv tm;;

let rec BVLPROPSAUX_in_discharge (asms:thm list) (depth:int) (th:thm) =
  if BVLPROPSAUX_in_is_main (concl th) then [th]
  else if depth = 0 then []
  else
    let th' = try CONV_RULE (BVLPROPSAUX_UNDER_FORALL_CONV (REWR_CONV IMP_CONJ)) th
              with Failure _ -> th in
    let rs = mapfilter (fun a -> MATCH_MP th' a) asms in
    flat (map (BVLPROPSAUX_in_discharge asms (depth - 1)) rs);;

let BVLPROPSAUX_IN_INV_TAC : tactic =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVLPROPSAUX_exp_rel_inv] o
    check (fun th -> BVLPROPSAUX_is_exp_rel (concl th))) THEN
  BVLPROPSAUX_SUBST_VAR_TAC ["es2"; "dest"];;

let BVLPROPSAUX_IN_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(BVLPROPSAUX_FRESH_STRIP_TAC o REWRITE_RULE BVLPROPSAUX_eval_case_eqs o
     BETA_RULE o REWRITE_RULE[LET_DEF; LET_END_DEF] o
     PURE_ONCE_REWRITE_RULE[bvl_evaluate_def] o
     check (fun th -> let c = concl th in BVLPROPSAUX_is_src_ev c &&
            not (is_var (fst (dest_pair (rand (lhs c))))))) THEN
  TRY RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN BVLPROPSAUX_CLEAN_TAC;;

(* the relation for the decremented clocks of the source sub-evaluations *)
let BVLPROPSAUX_IN_DEC_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = filter (fun th -> BVLPROPSAUX_is_in_rel (concl th)) asms in
  let src_of r = rand (rator (concl r)) in
  let sts = mapfilter (fun th -> let c = concl th in
              if BVLPROPSAUX_is_src_ev c then snd (dest_pair (snd (dest_pair (rand (lhs c)))))
              else failwith "") asms in
  let tac st =
    if exists (fun r -> src_of r = st) rels then failwith "have" else
    let f,args = strip_comb st in
    if not (is_const f && fst (dest_const f) = "bvl_dec_clock") then failwith "dec" else
    let n = hd args and s0 = hd (tl args) in
    let r = find (fun r -> src_of r = s0) rels in
    ASSUME_TAC (SPEC n (MATCH_MP BVLPROPSAUX_in_state_rel_dec_clock r)) in
  EVERY (mapfilter tac (setify sts)) g;;

(* the inlined find_code for the source find_code facts *)
let BVLPROPSAUX_IN_FC_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = filter (fun th -> BVLPROPSAUX_is_in_rel (concl th)) asms in
  let src_of r = rand (rator (concl r)) in
  let is_fc th = let c = concl th in is_eq c &&
    (try fst (dest_const (fst (strip_comb (lhs c)))) = "bvl_find_code" with Failure _ -> false) &&
    type_of (rand (rand (lhs c))) = BVLPROPSAUX_in_src_ty in
  let fcs = filter is_fc asms in
  let have_tgt fc = let _,args = strip_comb (lhs (concl fc)) in
    exists (fun th -> let c = concl th in is_eq c &&
      (try let f,args' = strip_comb (lhs c) in fst (dest_const f) = "bvl_find_code" &&
             el 0 args' = el 0 args && el 1 args' = el 1 args &&
             not (type_of (rand (el 2 args')) = BVLPROPSAUX_in_src_ty)
       with Failure _ -> false)) asms in
  let tac fc =
    if have_tgt fc then failwith "have" else
    let st = rand (rand (lhs (concl fc))) in
    let r = find (fun r -> src_of r = st) rels in
    BVLPROPSAUX_FRESH_STRIP_TAC (MATCH_MP BVLPROPSAUX_in_find_code (CONJ r fc)) in
  EVERY (mapfilter tac fcs) g;;

let BVLPROPSAUX_IN_IH1_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let ihs = filter (fun th -> let c = concl th in (is_forall c || is_imp c) &&
              BVLPROPSAUX_has_const "bvl_inlineProof_in_state_rel" c &&
              BVLPROPSAUX_has_const "bvl_evaluate" c) asms in
  let mains = flat (map (BVLPROPSAUX_in_discharge asms 4) ihs) in
  let rels = filter (fun th -> BVLPROPSAUX_is_in_rel (concl th)) asms in
  let src_of r = rand (rator (concl r)) in
  let processed st = exists (fun r -> src_of r = st) rels in
  let erels = filter (fun th -> BVLPROPSAUX_is_exp_rel (concl th)) asms in
  let evs = filter (fun th -> BVLPROPSAUX_is_src_ev (concl th)) asms in
  let monos = mapfilter (MATCH_MP bvl_evaluate_mono) evs in
  let try_main m =
    let _,b = strip_forall (concl m) in
    let cs = conjuncts (lhand b) in
    let rel_p = el 0 cs and erel_p = el 1 cs and ev_p = el 2 cs in
    let evl = lhs ev_p in
    let e = find (fun e -> lhs (concl e) = evl) evs in
    let r_tm,s'_tm = dest_pair (rhs (concl e)) in
    if processed s'_tm then failwith "processed" else
    let st = rand (rator rel_p) in
    let rel = find (fun r -> src_of r = st) rels in
    let t_tm = rand (concl rel) in
    let xs_tm = rand (rator erel_p) in
    let code_tm = rand (rator (rator erel_p)) in
    let er = find (fun er -> rand (rator (concl er)) = xs_tm) erels in
    let c_tm = rand (rator (rator (concl er))) in
    let ys_tm = rand (concl er) in
    let inst = SPECL [r_tm; t_tm; s'_tm; ys_tm] m in
    let erel_tac =
      if c_tm = code_tm then ACCEPT_TAC er else
      MATCH_MP_TAC subspt_exp_rel THEN EXISTS_TAC c_tm THEN CONJ_TAC THENL
       [MAP_EVERY MP_TAC monos THEN
        REWRITE_TAC[bvl_dec_clock_code; bvl_state_INFO.ri_accfupds; K_THM] THEN
        MESON_TAC[GEN_ALL subspt_trans; subspt_refl];
        ACCEPT_TAC er] in
    MP_TAC inst THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ACCEPT_TAC rel;
        erel_tac;
        ACCEPT_TAC e;
        REWRITE_TAC BVLPROPSAUX_eval_simps THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        ASM_REWRITE_TAC BVLPROPSAUX_eval_simps];
      DISCH_THEN BVLPROPSAUX_FRESH_STRIP_TAC] in
  let tacs = mapfilter try_main mains in
  if tacs = [] then failwith "BVLPROPSAUX_IN_IH1_TAC" else hd tacs g;;

(* the inlined do_app for the source do_app facts *)
let BVLPROPSAUX_IN_APP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = filter (fun th -> BVLPROPSAUX_is_in_rel (concl th)) asms in
  let src_of r = rand (rator (concl r)) in
  let is_app th = let c = concl th in is_eq c &&
    (try fst (dest_const (fst (strip_comb (lhs c)))) = "bvl_do_app" with Failure _ -> false) &&
    type_of (rand (lhs c)) = BVLPROPSAUX_in_src_ty in
  let apps = filter is_app asms in
  let have_tgt ap = let _,args = strip_comb (lhs (concl ap)) in
    exists (fun th -> let c = concl th in is_eq c &&
      (try let f,args' = strip_comb (lhs c) in fst (dest_const f) = "bvl_do_app" &&
             el 0 args' = el 0 args && el 1 args' = el 1 args &&
             not (type_of (el 2 args') = BVLPROPSAUX_in_src_ty)
       with Failure _ -> false)) asms in
  let tac ap =
    if have_tgt ap then failwith "have" else
    let f,args = strip_comb (lhs (concl ap)) in
    let st = el 2 args in
    let r = find (fun r -> src_of r = st) rels in
    let lim = rand (rator (rator (concl r))) in
    let th = MATCH_MP (SPECL [lim; el 0 args; el 1 args; st; rand (concl r)]
                         bvl_inlineProof_in_do_app_lemma) r in
    let th = CASE_REWRITE_RULE[] (REWRITE_RULE[ap] th) in
    if is_imp (concl th) then
      MP_TAC th THEN ANTS_TAC THENL
       [REWRITE_TAC BVLPROPSAUX_eval_simps THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        ASM_REWRITE_TAC BVLPROPSAUX_eval_simps;
        DISCH_TAC]
    else BVLPROPSAUX_FRESH_STRIP_TAC th in
  EVERY (mapfilter tac apps) g;;

let BVLPROPSAUX_IN_PREP_TAC : tactic =
  BVLPROPSAUX_IN_DEC_TAC THEN BVLPROPSAUX_IN_FC_TAC THEN BVLPROPSAUX_IN_APP_TAC;;

let BVLPROPSAUX_IN_IH_TAC : tactic =
  REPEAT (BVLPROPSAUX_IN_PREP_TAC THEN BVLPROPSAUX_IN_IH1_TAC) THEN
  BVLPROPSAUX_IN_PREP_TAC;;

(* compute the inlined evaluation with the facts about its sub-evaluations *)
let BVLPROPSAUX_IN_FIN_GEN_TAC (extra:thm list) : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let simple = filter (fun th -> not (is_imp (snd (strip_forall (concl th))))) asms in
  let rels = filter (fun th -> BVLPROPSAUX_is_in_rel (concl th)) asms in
  let is_st_eq c = let t = concl c in is_eq t &&
    (try mem (fst (dest_const (rator (lhs t))))
           ["bvl_state_clock"; "bvl_state_refs"; "bvl_state_globals"; "bvl_state_ffi"]
     with Failure _ -> false) in
  let st_eqs = flat (map (fun r -> filter is_st_eq
      (CONJUNCTS (REWRITE_RULE[bvl_inlineProof_in_state_rel_def] r))) rels) in
  let rws = extra @ st_eqs @ simple @ BVLPROPSAUX_eval_simps in
  (ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   BETA_TAC THEN
   REPEAT (CHANGED_TAC (REWRITE_TAC rws THEN CASE_REWRITE_TAC[])) THEN
   REWRITE_TAC[PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
   REWRITE_TAC rws THEN
   TRY (MATCH_MP_TAC BVLPROPSAUX_in_state_rel_clock0 THEN REWRITE_TAC rws)) g;;

let BVLPROPSAUX_IN_FIN_TAC : tactic = BVLPROPSAUX_IN_FIN_GEN_TAC [];;

(* the inlined call: the looked up body is the source of the inlined body *)
let BVLPROPSAUX_IN_INLINE_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let is_fc th = let c = concl th in is_eq c &&
    (try fst (dest_const (fst (strip_comb (lhs c)))) = "bvl_find_code" with Failure _ -> false) &&
    type_of (rand (rand (lhs c))) = BVLPROPSAUX_in_src_ty in
  let fc = find is_fc asms in
  let st = rand (rand (lhs (concl fc))) in
  let is_lk th = let c = concl th in is_eq c &&
    (try fst (dest_const (fst (strip_comb (lhs c)))) = "lookup" with Failure _ -> false) in
  let lk = find is_lk asms in
  let st0 = rand (rand (lhs (concl lk))) in
  let ev = find (fun th -> let c = concl th in BVLPROPSAUX_is_src_ev c &&
                   snd (dest_pair (snd (dest_pair (rand (lhs c))))) = st0 &&
                   snd (dest_pair (rhs c)) = st) asms in
  let mono = MATCH_MP bvl_evaluate_mono ev in
  let th = MATCH_MP BVLPROPSAUX_in_inline_find_code (CONJ mono (CONJ lk fc)) in
  let args_v,e_v = dest_pair (rand (rhs (concl fc))) in
  (STRIP_ASSUME_TAC th THEN
   BVLPROPSAUX_SUBST_VAR_TAC [fst (dest_var args_v); fst (dest_var e_v)]) g;;

(* the target evaluations with an extended environment *)
let BVLPROPSAUX_IN_EXPAND_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let simple = filter (fun th -> let c = concl th in not (is_forall c) && not (is_imp c))
                 asms in
  let is_tgt_ev th = let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
                     not (BVLPROPSAUX_is_src_ev c) in
  let tac f =
    let r = fst (dest_pair (rhs (concl f))) in
    let nte = mk_neg (mk_eq (r, `Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result`)) in
    let nth = EQT_ELIM (REWRITE_CONV (simple @ BVLPROPSAUX_eval_simps) nte) in
    ASSUME_TAC (MATCH_MP BVLPROPSAUX_bvl_expand_env_eq (CONJ f nth)) in
  EVERY (mapfilter tac (filter is_tgt_ev asms)) g;;

let BVLPROPSAUX_IN_INLINE_CASE_TAC : tactic =
  BVLPROPSAUX_IN_SPLIT_TAC THEN TRY BVLPROPSAUX_IN_INLINE_TAC THEN
  REPEAT (BVLPROPSAUX_IN_DEC_TAC THEN BVLPROPSAUX_IN_APP_TAC THEN BVLPROPSAUX_IN_IH1_TAC) THEN
  BVLPROPSAUX_IN_EXPAND_TAC THEN
  BVLPROPSAUX_IN_FIN_GEN_TAC [evaluate_mk_tick; ADD1];;

let BVLPROPSAUX_IN_CASE_TAC : tactic =
  REPEAT STRIP_TAC THEN BVLPROPSAUX_IN_INV_TAC THEN
  (fun (asl,w as g) ->
     let is_lk th = let c = concl th in is_eq c &&
       (try fst (dest_const (fst (strip_comb (lhs c)))) = "lookup" with Failure _ -> false) in
     if exists (fun (_,th) -> is_lk th) asl then BVLPROPSAUX_IN_INLINE_CASE_TAC g
     else (BVLPROPSAUX_IN_SPLIT_TAC THEN BVLPROPSAUX_IN_IH_TAC THEN
           BVLPROPSAUX_IN_FIN_TAC) g);;

(* HOL4 evaluate_inline (the free limit of HOL4 is quantified) *)
let bvl_inlineProof_evaluate_inline = prove
 (`!limit es env (s1:((num#bvl_exp)spt#C,FFI)bvl_state) res (t1:(C,FFI)bvl_state) s2 es2.
     bvl_inlineProof_in_state_rel limit s1 t1 /\
     bvl_inlineProof_exp_rel (bvl_state_code s1) es es2 /\
     bvl_evaluate (es,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     ?t2. bvl_evaluate (es2,env,t1) = (res,t2) /\
          bvl_inlineProof_in_state_rel limit s2 t2`,
  GEN_TAC THEN
  MATCH_MP_TAC (INST_TYPE [`:(num#bvl_exp)spt#C`,`:C`] BVLPROPSAUX_evaluate_ind) THEN
  REPEAT CONJ_TAC THEN BVLPROPSAUX_IN_CASE_TAC);;

let bvl_inlineProof_in_co_def = cake_def
  `bvl_inlineProof_in_co limit (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list) =
     (\n. let ((cs,cfg),progs) = co n in
          let (cs1,progs) = tick_compile_prog limit cs progs in
            (cfg,progs))`;;

let MAP_FST_tick_inline_all = prove
 (`!limit (cs:(num#bvl_exp)spt) prog.
     MAP FST (SND (tick_inline_all limit cs prog [])) = MAP FST prog`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`limit:num`; `cs:(num#bvl_exp)spt`; `prog:(num#num#bvl_exp)list`;
                 `[]:(num#num#bvl_exp)list`;
                 `FST (tick_inline_all limit (cs:(num#bvl_exp)spt) prog [])`;
                 `SND (tick_inline_all limit (cs:(num#bvl_exp)spt) prog [])`]
                tick_inline_all_names) THEN
  REWRITE_TAC[PAIR; REVERSE; MAP; APPEND] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* local helpers: HOL4 [local val] exp_rel_rw (the second one) *)
let BVLPROPSAUX_lookup_insert_swap = prove
 (`!x (y:A) (prog:(num#A)list) acc k.
     ~MEM x (MAP FST prog) ==>
     lookup k (union (insert x y (fromAList prog)) acc) =
     lookup k (union (fromAList prog) (insert x y acc))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALOOKUP (prog:(num#A)list) x = NONE` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ALOOKUP_NONE]; ALL_TAC] THEN
  REWRITE_TAC[lookup_union; lookup_insert; lookup_fromAList] THEN
  ASM_CASES_TAC `k:num = x` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

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
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP BVLPROPSAUX_exp_rel_tick_inline_sing) THEN
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
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BVLPROPSAUX_bvl_semantics_sim THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`limit:num`; `start:num`; `[]:bvl_v list`; `ffi:(FFI)ffi_state`;
                 `prog:(num#num#bvl_exp)list`;
                 `co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list`;
                 `cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option`;
                 `k:num`; `r:(bvl_v list,bvl_v)result`;
                 `s:((num#bvl_exp)spt#C,FFI)bvl_state`] BVLPROPSAUX_in_evaluate_Call) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;


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

(* HOL4 [local val] let_op_sing_thm *)
let BVLPROPSAUX_let_op_sing_thm = prove
 (`!x. bvl_inline_let_op_sing x = HD (bvl_inline_let_op [x])`,
  REWRITE_TAC[bvl_inline_let_op_sing_eq; let_op_one; HD]);;

(* HOL4 [local val] var_list_IMP_evaluate, the first (general) one; the   *)
(* free env of HOL4 is quantified                                           *)
let BVLPROPSAUX_var_list_IMP_evaluate_gen = prove
 (`!a2 a1 l (xs:bvl_exp list) env (s:(C,FFI)bvl_state).
     bvl_inline_var_list (LENGTH a1) l xs /\ LENGTH xs = LENGTH a2 ==>
     bvl_evaluate (l,APPEND (APPEND a1 a2) env,s) = (Rval a2,s)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `l:bvl_exp list` list_CASES) THEN
    REWRITE_TAC[bvl_inline_var_list_def; bvl_evaluate_def] THEN
    CASES_ON `h:bvl_exp` THEN REWRITE_TAC[bvl_inline_var_list_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `l:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[bvl_inline_var_list_def] THEN
  CASES_ON `h'':bvl_exp` THEN REWRITE_TAC[bvl_inline_var_list_def] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `a < (a + SUC b) + c`] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `EL (LENGTH (a1:bvl_v list)) (APPEND (APPEND a1 (CONS h t)) env) = h`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    SIMP_TAC[EL_LENGTH_APPEND; NULL; HD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND a1 [h:bvl_v]`; `t'':bvl_exp list`;
                                `t':bvl_exp list`; `env:bvl_v list`;
                                `s:(C,FFI)bvl_state`]) THEN
  SUBGOAL_THEN `LENGTH (APPEND a1 [h:bvl_v]) = LENGTH a1 + 1` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD]);;

(* HOL4 [local val] var_list_IMP_evaluate, the second one (env quantified) *)
let BVLPROPSAUX_var_list_IMP_evaluate = prove
 (`!l (xs:bvl_exp list) a env (s:(C,FFI)bvl_state).
     bvl_inline_var_list 0 l xs /\ LENGTH xs = LENGTH a ==>
     bvl_evaluate (l,APPEND a env,s) = (Rval a,s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:bvl_v list`; `[]:bvl_v list`; `l:bvl_exp list`; `xs:bvl_exp list`;
                 `env:bvl_v list`; `s:(C,FFI)bvl_state`]
                BVLPROPSAUX_var_list_IMP_evaluate_gen) THEN
  ASM_REWRITE_TAC[LENGTH; APPEND]);;

let bvl_inlineProof_LENGTH_let_op = prove
 (`!xs. LENGTH (bvl_inline_let_op xs) = LENGTH xs`,
  REWRITE_TAC[GSYM (CONJUNCT2 let_op_one)] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[let_op_one_def; LENGTH]);;


(* a local helper for the second do_app_lemma: Install *)
let BVLPROPSAUX_let_do_install = prove
 (CASE_TERM `!q l vs (s:(C,FFI)bvl_state) t. let_state_rel q l s t ==>
  (match (bvl_do_install vs s:(bvl_v#(C,FFI)bvl_state,bvl_v)result) with
     Rerr err -> bvl_do_install vs t = Rerr err
   | Rval (v,s2) -> ?t2. let_state_rel q l s2 t2 /\
                         bvl_do_install vs t = (Rval (v,t2):(bvl_v#(C,FFI)bvl_state,bvl_v)result))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVLPROPSAUX_let_state_rel_eq]) THEN
  MP_TAC(ISPEC `bvl_state_compile_oracle (s:(C,FFI)bvl_state) 0` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cfg:C` (X_CHOOSE_THEN `progs:(num#num#bvl_exp)list`
    ASSUME_TAC)) THEN
  REWRITE_TAC[bvl_do_install_def] THEN
  ASM_REWRITE_TAC[o_THM; domain_map; PAIR_MAP_THM; I_THM; LET_DEF; LET_END_DEF;
                  BVLPROPSAUX_MAP_FST_PAIR_MAP; shift_seq_def] THEN BETA_TAC THEN
  REWRITE_TAC[o_THM; FST_PAIR_MAP; I_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[BVLPROPSAUX_MAP_FST_PAIR_MAP] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `bvl_state_compile_oracle (s:(C,FFI)bvl_state) 0 = (cfg,progs)`)) THEN
  SPEC_TAC(`progs:(num#num#bvl_exp)list`,`progs:(num#num#bvl_exp)list`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `progs:(num#num#bvl_exp)list` list_CASES) THEN
  REWRITE_TAC[MAP] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `ae:num#bvl_exp` SUBST1_TAC)) THEN
    REWRITE_TAC[PAIR_MAP_THM; I_THM]] THEN
  CASE_REWRITE_TAC[] THEN REPEAT CASE_TAC THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
  REWRITE_TAC[BVLPROPSAUX_let_state_rel_eq; bvl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; map_union; map_fromAList; BVLPROPSAUX_PAIR_LAMBDA_MAP] THEN
  REWRITE_TAC[MAP; PAIR_MAP_THM; I_THM; ETA_AX]);;

(* HOL4 [local] do_app_lemma, the second one (for let_op) *)
let bvl_inlineProof_do_app_lemma = prove
 (CASE_TERM `!q4 l4 op a (s1:(C,FFI)bvl_state) t1.
    let_state_rel q4 l4 s1 t1 ==>
    match bvl_do_app op a s1 with
      Rerr err -> bvl_do_app op a t1 = Rerr err
    | Rval (v,s2) -> ?t2. let_state_rel q4 l4 s2 t2 /\
                          bvl_do_app op a t1 = Rval (v,t2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[BVLPROPSAUX_do_app_Install] THEN
    MATCH_MP_TAC BVLPROPSAUX_let_do_install THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BVLPROPSAUX_let_state_rel_eq] o
              check (fun th -> BVLPROPSAUX_has_const "let_state_rel" (concl th))) THEN
  SUBGOAL_THEN
   `bvl_state_code_fupd (K (bvl_state_code t1))
      (bvl_state_compile_fupd (K (bvl_state_compile t1))
        (bvl_state_compile_oracle_fupd (K (bvl_state_compile_oracle t1))
          (s1:(C,FFI)bvl_state))) = t1` ASSUME_TAC THENL
   [REWRITE_TAC[bvl_state_component_equality; bvl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvl_do_app op a (s1:(C,FFI)bvl_state)` (cases "result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `a':bvl_v#(C,FFI)bvl_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:bvl_v` (X_CHOOSE_THEN `s2:(C,FFI)bvl_state`
      SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:(C,FFI)bvl_state`;
                   `v:bvl_v`; `s2:(C,FFI)bvl_state`; `bvl_state_code (t1:(C,FFI)bvl_state)`;
                   `bvl_state_compile (t1:(C,FFI)bvl_state)`;
                   `bvl_state_compile_oracle (t1:(C,FFI)bvl_state)`]
                  bvl_do_app_with_code) THEN
    ASM_REWRITE_TAC[domain_map; SUBSET_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP bvl_do_app_const) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(op = clos_Install)`]) THEN
    REWRITE_TAC[BVLPROPSAUX_let_state_rel_eq; bvl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`op:clos_op`; `a:bvl_v list`; `s1:(C,FFI)bvl_state`;
                   `a':(bvl_v)error_result`; `bvl_state_code (t1:(C,FFI)bvl_state)`;
                   `bvl_state_compile (t1:(C,FFI)bvl_state)`;
                   `bvl_state_compile_oracle (t1:(C,FFI)bvl_state)`]
                  do_app_with_code_err_not_Install) THEN
    ASM_REWRITE_TAC[domain_map; SUBSET_REFL]]);;


(* local helpers for evaluate_let_op: clocks, find_code, compile_any *)
let BVLPROPSAUX_let_state_rel_dec_clock = prove
 (`!q l (s:(C,FFI)bvl_state) t n.
     let_state_rel q l s t ==>
     let_state_rel q l (bvl_dec_clock n s) (bvl_dec_clock n t)`,
  REWRITE_TAC[BVLPROPSAUX_let_state_rel_eq; bvl_dec_clock_def;
              bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_let_state_rel_clock0 = prove
 (`!q l (s:(C,FFI)bvl_state) t.
     let_state_rel q l s t ==>
     let_state_rel q l (bvl_state_clock_fupd (K 0) s) (bvl_state_clock_fupd (K 0) t)`,
  REWRITE_TAC[BVLPROPSAUX_let_state_rel_eq; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_let_find_code = prove
 (`!q l (s:(C,FFI)bvl_state) t dest vs args exp.
     let_state_rel q l s t /\ bvl_find_code dest vs (bvl_state_code s) = SOME (args,exp) ==>
     bvl_find_code dest vs (bvl_state_code t) =
       SOME (args,compile_any q l (LENGTH args) (bvl_inline_let_op_sing exp))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_let_state_rel_eq] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `bvl_find_code dest vs (bvl_state_code (s:(C,FFI)bvl_state)) = SOME (args,exp)` THEN
  CASES_ON `dest:num option` THEN REWRITE_TAC[bvl_find_code_def; lookup_map] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `LAST (vs:bvl_v list)` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `lookup a (bvl_state_code (s:(C,FFI)bvl_state))` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"];
    CASES_ON `lookup a (bvl_state_code (s:(C,FFI)bvl_state))` THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"]] THEN
  MP_TAC(ISPEC `a':num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[let_opt_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REWRITE_TAC[] THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[LENGTH_FRONT; ARITH_RULE `PRE (a + 1) = a`]);;

let BVLPROPSAUX_let_compile_any = prove
 (`!q l exp args (s:(C,FFI)bvl_state) res s2.
     bvl_evaluate (bvl_inline_let_op [exp],args,s) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate ([compile_any q l (LENGTH args) (bvl_inline_let_op_sing exp)],args,s) =
       (res,s2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BVLPROPSAUX_let_op_sing_thm] THEN
  MATCH_MP_TAC compile_any_correct THEN ASM_REWRITE_TAC[HD_let_op]);;


(* local tactics for evaluate_let_op, as for evaluate_inline; the source  *)
(* evaluations are those whose expressions are not let_op images          *)
let BVLPROPSAUX_dest_op_SOME = prove
 (`!e (args:A list) op.
     bvl_inline_dest_op e args = SOME op ==>
     ?ys. e = bvl_Op op ys /\ bvl_inline_var_list 0 ys args`,
  GEN_TAC THEN CASES_ON `e:bvl_exp` THEN
  REWRITE_TAC[bvl_inline_dest_op_def; distinctness "option"] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; injectivity "bvl_exp"] THEN
  DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `a1:bvl_exp list` THEN ASM_REWRITE_TAC[]);;

let BVLPROPSAUX_is_let_rel (t:term) =
  try fst (dest_const (fst (strip_comb t))) = "let_state_rel" with Failure _ -> false;;

let BVLPROPSAUX_is_lo_src_ev (t:term) =
  is_eq t && BVLPROPSAUX_is_ev (lhs t) &&
  (let xs = fst (dest_pair (rand (lhs t))) in
   not (BVLPROPSAUX_has_const "bvl_inline_let_op" xs) &&
   not (BVLPROPSAUX_has_const "compile_any" xs));;

let BVLPROPSAUX_lo_is_main (t:term) =
  let vs,b = strip_forall t in
  length vs >= 3 && is_imp b && is_conj (lhand b) &&
  BVLPROPSAUX_is_let_rel (lhand (lhand b));;

let rec BVLPROPSAUX_lo_discharge (asms:thm list) (depth:int) (th:thm) =
  if BVLPROPSAUX_lo_is_main (concl th) then [th]
  else if depth = 0 then []
  else
    let th' = try CONV_RULE (BVLPROPSAUX_UNDER_FORALL_CONV (REWR_CONV IMP_CONJ)) th
              with Failure _ -> th in
    let rs = mapfilter (fun a -> MATCH_MP th' a) asms in
    flat (map (BVLPROPSAUX_lo_discharge asms (depth - 1)) rs);;

let BVLPROPSAUX_LO_SPLIT_TAC : tactic =
  FIRST_X_ASSUM(BVLPROPSAUX_FRESH_STRIP_TAC o REWRITE_RULE BVLPROPSAUX_eval_case_eqs o
     BETA_RULE o REWRITE_RULE[LET_DEF; LET_END_DEF] o
     PURE_ONCE_REWRITE_RULE[bvl_evaluate_def] o
     check (fun th -> let c = concl th in BVLPROPSAUX_is_lo_src_ev c &&
            not (is_var (fst (dest_pair (rand (lhs c))))))) THEN
  TRY RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN BVLPROPSAUX_CLEAN_TAC;;

let BVLPROPSAUX_lo_rels (asl:(string*thm) list) =
  filter (fun th -> BVLPROPSAUX_is_let_rel (concl th)) (map snd asl);;

let BVLPROPSAUX_lo_src_of (r:thm) = rand (rator (concl r));;

let BVLPROPSAUX_LO_DEC_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = BVLPROPSAUX_lo_rels asl in
  let src_of = BVLPROPSAUX_lo_src_of in
  let sts = mapfilter (fun th -> let c = concl th in
              if BVLPROPSAUX_is_lo_src_ev c
              then snd (dest_pair (snd (dest_pair (rand (lhs c))))) else failwith "") asms in
  let tac st =
    if exists (fun r -> src_of r = st) rels then failwith "have" else
    let f,args = strip_comb st in
    if not (is_const f && fst (dest_const f) = "bvl_dec_clock") then failwith "dec" else
    let n = hd args and s0 = hd (tl args) in
    let r = find (fun r -> src_of r = s0) rels in
    ASSUME_TAC (SPEC n (MATCH_MP BVLPROPSAUX_let_state_rel_dec_clock r)) in
  EVERY (mapfilter tac (setify sts)) g;;

let BVLPROPSAUX_LO_FC_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = BVLPROPSAUX_lo_rels asl in
  let src_of = BVLPROPSAUX_lo_src_of in
  let fc_parts th = let c = concl th in
    if is_eq c && (try fst (dest_const (fst (strip_comb (lhs c)))) = "bvl_find_code"
                   with Failure _ -> false)
    then strip_comb (lhs c) else failwith "fc" in
  let fcs = filter (fun th -> can fc_parts th &&
              (let _,args = fc_parts th in exists (fun r -> src_of r = rand (el 2 args)) rels))
              asms in
  let tac fc =
    let _,args = fc_parts fc in
    let st = rand (el 2 args) in
    let r = find (fun r -> src_of r = st) rels in
    let tst = rand (concl r) in
    if exists (fun th -> can fc_parts th &&
                 (let _,args' = fc_parts th in el 0 args' = el 0 args &&
                    el 1 args' = el 1 args && rand (el 2 args') = tst)) asms
    then failwith "have" else
    ASSUME_TAC (MATCH_MP BVLPROPSAUX_let_find_code (CONJ r fc)) in
  EVERY (mapfilter tac fcs) g;;

let BVLPROPSAUX_LO_APP_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let rels = BVLPROPSAUX_lo_rels asl in
  let src_of = BVLPROPSAUX_lo_src_of in
  let app_parts th = let c = concl th in
    if is_eq c && (try fst (dest_const (fst (strip_comb (lhs c)))) = "bvl_do_app"
                   with Failure _ -> false)
    then strip_comb (lhs c) else failwith "app" in
  let apps = filter (fun th -> can app_parts th &&
               (let _,args = app_parts th in exists (fun r -> src_of r = el 2 args) rels))
               asms in
  let tac ap =
    let _,args = app_parts ap in
    let st = el 2 args in
    let r = find (fun r -> src_of r = st) rels in
    let tst = rand (concl r) in
    if exists (fun th -> can app_parts th &&
                 (let _,args' = app_parts th in el 0 args' = el 0 args &&
                    el 1 args' = el 1 args && el 2 args' = tst)) asms
    then failwith "have" else
    let _,rargs = strip_comb (concl r) in
    let th = MATCH_MP (SPECL [el 0 rargs; el 1 rargs; el 0 args; el 1 args; st; tst]
                         bvl_inlineProof_do_app_lemma) r in
    let th = CASE_REWRITE_RULE[] (REWRITE_RULE[ap] th) in
    BVLPROPSAUX_FRESH_STRIP_TAC th in
  EVERY (mapfilter tac apps) g;;

let BVLPROPSAUX_LO_IH1_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let ihs = filter (fun th -> let c = concl th in (is_forall c || is_imp c) &&
              BVLPROPSAUX_has_const "let_state_rel" c &&
              BVLPROPSAUX_has_const "bvl_evaluate" c) asms in
  let mains = flat (map (BVLPROPSAUX_lo_discharge asms 4) ihs) in
  let rels = BVLPROPSAUX_lo_rels asl in
  let src_of = BVLPROPSAUX_lo_src_of in
  let processed st = exists (fun r -> src_of r = st) rels in
  let evs = filter (fun th -> BVLPROPSAUX_is_lo_src_ev (concl th)) asms in
  let try_main m =
    let _,b = strip_forall (concl m) in
    let cs = conjuncts (lhand b) in
    let rel_p = el 0 cs and ev_p = el 1 cs in
    let evl = lhs ev_p in
    let e = find (fun e -> lhs (concl e) = evl) evs in
    let r_tm,s'_tm = dest_pair (rhs (concl e)) in
    if processed s'_tm then failwith "processed" else
    let st = rand (rator rel_p) in
    let rel = find (fun r -> src_of r = st) rels in
    let t_tm = rand (concl rel) in
    let inst = SPECL [r_tm; t_tm; s'_tm] m in
    MP_TAC inst THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ACCEPT_TAC rel;
        ACCEPT_TAC e;
        REWRITE_TAC BVLPROPSAUX_eval_simps THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
        ASM_REWRITE_TAC BVLPROPSAUX_eval_simps];
      DISCH_THEN BVLPROPSAUX_FRESH_STRIP_TAC] in
  let tacs = mapfilter try_main mains in
  if tacs = [] then failwith "BVLPROPSAUX_LO_IH1_TAC" else hd tacs g;;

(* the compile_any images of the target evaluations of let_op [e] *)
let BVLPROPSAUX_LO_CA_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let simple = filter (fun th -> not (is_imp (snd (strip_forall (concl th))))) asms in
  let rels = BVLPROPSAUX_lo_rels asl in
  if rels = [] then ALL_TAC g else
  let _,rargs = strip_comb (concl (hd rels)) in
  let q = el 0 rargs and l = el 1 rargs in
  let is_tgt th = let c = concl th in is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
    (let xs = fst (dest_pair (rand (lhs c))) in
     is_comb xs && is_const (rator xs) &&
     fst (dest_const (rator xs)) = "bvl_inline_let_op" &&
     (let a = rand xs in is_comb a && is_comb (rator a) &&
        (try fst (dest_const (rator (rator a))) = "CONS" with Failure _ -> false) &&
        (try fst (dest_const (rand a)) = "NIL" with Failure _ -> false))) in
  let tac f =
    let r = fst (dest_pair (rhs (concl f))) in
    let nte = mk_neg (mk_eq (r, `Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result`)) in
    let nth = EQT_ELIM (REWRITE_CONV (simple @ BVLPROPSAUX_eval_simps) nte) in
    ASSUME_TAC (MATCH_MP (SPECL [q; l] BVLPROPSAUX_let_compile_any) (CONJ f nth)) in
  EVERY (mapfilter tac (filter is_tgt asms)) g;;

let BVLPROPSAUX_LO_PREP_TAC : tactic =
  BVLPROPSAUX_LO_DEC_TAC THEN BVLPROPSAUX_LO_FC_TAC THEN BVLPROPSAUX_LO_APP_TAC;;

let BVLPROPSAUX_LO_IH_TAC : tactic =
  REPEAT (BVLPROPSAUX_LO_PREP_TAC THEN BVLPROPSAUX_LO_IH1_TAC) THEN
  BVLPROPSAUX_LO_PREP_TAC THEN BVLPROPSAUX_LO_CA_TAC;;

let BVLPROPSAUX_LO_FIN_REWR_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let simple = filter (fun th -> not (is_imp (snd (strip_forall (concl th))))) asms in
  let rels = BVLPROPSAUX_lo_rels asl in
  let is_st_eq c = let t = concl c in is_eq t &&
    (try mem (fst (dest_const (rator (lhs t))))
           ["bvl_state_clock"; "bvl_state_refs"; "bvl_state_globals"; "bvl_state_ffi"]
     with Failure _ -> false) in
  let st_eqs = flat (map (fun r -> filter is_st_eq
      (CONJUNCTS (REWRITE_RULE[BVLPROPSAUX_let_state_rel_eq] r))) rels) in
  let rws = HD_let_op :: st_eqs @ simple @ BVLPROPSAUX_eval_simps in
  (REPEAT (CHANGED_TAC (REWRITE_TAC rws THEN CASE_REWRITE_TAC[])) THEN
   REWRITE_TAC[PAIR_EQ] THEN CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN
   REWRITE_TAC rws THEN
   TRY (MATCH_MP_TAC BVLPROPSAUX_let_state_rel_clock0 THEN REWRITE_TAC rws)) g;;

let BVLPROPSAUX_LO_EV_UNFOLD_TAC : tactic =
  FIRST [CHANGED_TAC (ONCE_REWRITE_TAC[bvl_evaluate_def]);
         ONCE_REWRITE_TAC[bvl_evaluate_CONS]] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC;;

let BVLPROPSAUX_LO_FIN_TAC : tactic =
  ONCE_REWRITE_TAC[bvl_inline_let_op_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN BVLPROPSAUX_LO_EV_UNFOLD_TAC THEN BVLPROPSAUX_LO_FIN_REWR_TAC;;

(* the Let case: let_op turns Let xs (Op op ys) into Op op xs when ys are *)
(* the variables of xs                                                      *)
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

let BVLPROPSAUX_LO_LET_FIN_TAC : tactic =
  ONCE_REWRITE_TAC[bvl_inline_let_op_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  BETA_TAC THEN
  (fun (asl,w as g) ->
     let dt = find_term (fun t -> is_comb t && is_comb (rator t) &&
                (try fst (dest_const (rator (rator t))) = "bvl_inline_dest_op"
                 with Failure _ -> false)) w in
     (CASES_ON dt THEN CASE_REWRITE_TAC[]) g) THENL
   [BVLPROPSAUX_LO_EV_UNFOLD_TAC THEN BVLPROPSAUX_LO_FIN_REWR_TAC;
    FIRST_X_ASSUM(BVLPROPSAUX_FRESH_STRIP_TAC o MATCH_MP BVLPROPSAUX_dest_op_SOME o
      check (fun th -> BVLPROPSAUX_has_const "bvl_inline_dest_op" (concl th))) THEN
    (fun (asl,w as g) ->
       let eq = find (fun th -> let c = concl th in is_eq c &&
                  (try fst (dest_const (rator (lhs c))) = "HD" with Failure _ -> false) &&
                  BVLPROPSAUX_has_const "bvl_inline_let_op" (lhs c)) (map snd asl) in
       let lop = rand (lhs (concl eq)) in
       let tm = mk_eq(lop, mk_list([rhs (concl eq)], `:bvl_exp`)) in
       (SUBGOAL_THEN tm (fun lth -> RULE_ASSUM_TAC(REWRITE_RULE[lth])) THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM HD_let_op] THEN REWRITE_TAC[eq]; ALL_TAC]) g) THEN
    (fun (asl,w as g) ->
       let vl = find (fun th -> BVLPROPSAUX_has_const "bvl_inline_var_list" (concl th))
                  (map snd asl) in
       let ths = mapfilter (fun (_,th) -> MATCH_MP BVLPROPSAUX_let_op_Op_eq (CONJ vl th)) asl in
       (if ths = [] then BVLPROPSAUX_LO_EV_UNFOLD_TAC
        else REWRITE_TAC ths) g) THEN
    BVLPROPSAUX_LO_FIN_REWR_TAC];;

let BVLPROPSAUX_LO_CASE_TAC : tactic =
  REPEAT STRIP_TAC THEN BVLPROPSAUX_LO_SPLIT_TAC THEN BVLPROPSAUX_LO_IH_TAC THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> try fst (dest_const t) = "bvl_Let" with Failure _ -> false))
            (lhand (lhand (snd (dest_exists w))))
     then BVLPROPSAUX_LO_LET_FIN_TAC g else BVLPROPSAUX_LO_FIN_TAC g);;


(* HOL4 evaluate_let_op (the free q4 and l4 of HOL4 are quantified) *)
let bvl_inlineProof_evaluate_let_op = prove
 (`!q4 l4 es env (s1:(C,FFI)bvl_state) res t1 s2.
     let_state_rel q4 l4 s1 t1 /\
     bvl_evaluate (es,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
     ?t2. bvl_evaluate (bvl_inline_let_op es,env,t1) = (res,t2) /\
          let_state_rel q4 l4 s2 t2`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN
  REPEAT CONJ_TAC THEN BVLPROPSAUX_LO_CASE_TAC);;

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
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q4:bool`; `l4:num`; `[bvl_Call 0 (SOME start) []]`; `[]:bvl_v list`;
                 `bvl_initial_state (ffi0:(FFI)ffi_state) prog (co:num->C#(num#num#bvl_exp)list)
                    (let_op_cc q4 l4
                      (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option)) k`;
                 `r:(bvl_v list,bvl_v)result`;
                 `bvl_initial_state (ffi0:(FFI)ffi_state) (map (let_opt q4 l4) prog)
                    ((I ## MAP (I ## let_opt q4 l4)) o (co:num->C#(num#num#bvl_exp)list))
                    (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) k`;
                 `s:(C,FFI)bvl_state`] bvl_inlineProof_evaluate_let_op) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[BVLPROPSAUX_let_state_rel_eq; bvl_initial_state_simp; let_op_cc_def];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_inline_let_op_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)bvl_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t2:(C,FFI)bvl_state` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BVLPROPSAUX_let_state_rel_eq]) THEN
  MESON_TAC[]);;

(* HOL4 [local val] semantics_let_op *)
let BVLPROPSAUX_semantics_let_op = prove
 (`!q4 l4 (ffi:(FFI)ffi_state) prog (co:num->C#(num#num#bvl_exp)list)
     (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option) start.
     ~(bvl_semantics ffi prog co (let_op_cc q4 l4 cc) start = Fail) ==>
     bvl_semantics ffi (map (let_opt q4 l4) prog)
       ((I ## MAP (I ## let_opt q4 l4)) o co) cc start =
     bvl_semantics ffi prog co (let_op_cc q4 l4 cc) start`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BVLPROPSAUX_bvl_semantics_sim THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`q4:bool`; `l4:num`; `start:num`; `ffi:(FFI)ffi_state`;
                 `prog:(num#bvl_exp)spt`; `co:num->C#(num#num#bvl_exp)list`;
                 `cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option`;
                 `k:num`; `r:(bvl_v list,bvl_v)result`; `s:(C,FFI)bvl_state`]
                let_evaluate_Call) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;


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
  MP_TAC(ISPEC `h:num#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `ae:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ae:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[bvl_inline_optimise_def; PAIR_MAP_THM; I_THM; let_opt_def]);;


let bvl_inlineProof_state_cc_compile_inc_eq = prove
 (`!limit o1 o2 (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option).
     state_cc (bvl_inline_compile_inc limit o1 o2) cc =
     bvl_inlineProof_in_cc limit (bvl_inlineProof_remove_ticks_cc (let_op_cc o1 o2 cc))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`cs:(num#bvl_exp)spt`; `cfg:C`; `prog:(num#num#bvl_exp)list`] THEN
  REWRITE_TAC[state_cc_def; bvl_inlineProof_in_cc_def; bvl_inline_compile_inc_def;
              bvl_inlineProof_remove_ticks_cc_def; let_op_cc_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN BETA_TAC THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `tick_compile_prog limit (cs:(num#bvl_exp)spt) prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `prog1:(num#num#bvl_exp)list` SUBST1_TAC)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[BVLPROPSAUX_MAP_optimise]);;
let bvl_inlineProof_state_co_compile_inc_eq = prove
 (`!limit o1 o2 (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list).
     state_co (bvl_inline_compile_inc limit o1 o2) co =
     ((I ## MAP (I ## let_opt o1 o2)) o bvl_inlineProof_remove_ticks_co o
      bvl_inlineProof_in_co limit co)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[state_co_def; bvl_inlineProof_in_co_def; bvl_inline_compile_inc_def;
              bvl_inlineProof_remove_ticks_co_def] THEN
  MP_TAC(ISPEC `(co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list) n` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `csc:(num#bvl_exp)spt#C` (X_CHOOSE_THEN
    `progs:(num#num#bvl_exp)list` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `csc:(num#bvl_exp)spt#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(num#bvl_exp)spt` (X_CHOOSE_THEN `cfg:C` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `tick_compile_prog limit (cs:(num#bvl_exp)spt) progs` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `prog1:(num#num#bvl_exp)list` SUBST1_TAC)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_MAP_THM; I_THM; BVLPROPSAUX_MAP_optimise]);;

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
  REWRITE_TAC[bvl_inlineProof_state_cc_compile_inc_eq;
              bvl_inlineProof_state_co_compile_inc_eq] THEN
  REWRITE_TAC[bvl_inline_compile_prog_def; bvl_inline_compile_inc_def] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `tick_compile_prog limit LN (prog:(num#num#bvl_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `p1:(num#num#bvl_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
     is_var (rhs (concl th)) && fst (dest_var (rhs (concl th))) = "prog1")) THEN
  MP_TAC(ISPECL [`limit:num`; `ffi:(FFI)ffi_state`; `prog:(num#num#bvl_exp)list`;
                 `co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list`;
                 `let_op_cc o1 o2
                    (cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option)`;
                 `start:num`] BVLPROPSAUX_inline_ticks) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[BVLPROPSAUX_MAP_optimise] THEN
  MP_TAC(ISPECL [`o1:bool`; `o2:num`; `ffi:(FFI)ffi_state`;
                 `MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))) (p1:(num#num#bvl_exp)list)`;
                 `bvl_inlineProof_remove_ticks_co o bvl_inlineProof_in_co limit
                    (co:num->((num#bvl_exp)spt#C)#(num#num#bvl_exp)list)`;
                 `cc:C->(num#num#bvl_exp)list->(((8)word)list#((64)word)list#C)option`;
                 `start:num`] BVLPROPSAUX_lets) THEN
  ASM_REWRITE_TAC[]);;


let handle_ok_optimise = prove
 (`!b i (prog:(A#num#bvl_exp)list).
     handle_ok (MAP (SND o SND o bvl_inline_optimise b i) prog)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; handle_ok_def] THEN
  ONCE_REWRITE_TAC[handle_ok_CONS] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:A#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:A` (X_CHOOSE_THEN `ae:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ae:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[o_THM; bvl_inline_optimise_def; compile_any_handle_ok]);;

let compile_prog_handle_ok = prove
 (`!l b i prog inlines prog3.
     bvl_inline_compile_prog l b i prog = (inlines,prog3) ==>
     handle_ok (MAP (SND o SND) prog3)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_inline_compile_prog_def; bvl_inline_compile_inc_def] THEN
  MP_TAC(ISPEC `tick_compile_prog l LN (prog:(num#num#bvl_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `p1:(num#num#bvl_exp)list` SUBST1_TAC)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[GSYM MAP_o; GSYM o_ASSOC; handle_ok_optimise]);;

(* HOL4 [simp] *)
let MAP_FST_MAP_optimise = prove
 (`!x y (z:(A#num#bvl_exp)list).
     MAP FST (MAP (bvl_inline_optimise x y) z) = MAP FST z`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  MP_TAC(ISPEC `h:A#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:A` (X_CHOOSE_THEN `ae:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ae:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[bvl_inline_optimise_def; FST]);;

let compile_prog_names = prove
 (`!l b i prog inlines prog3.
     bvl_inline_compile_prog l b i prog = (inlines,prog3) ==>
     MAP FST prog3 = MAP FST prog`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_inline_compile_prog_def; bvl_inline_compile_inc_def] THEN
  MP_TAC(ISPEC `tick_compile_prog l LN (prog:(num#num#bvl_exp)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `p1:(num#num#bvl_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[MAP_FST_MAP_optimise] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP tick_inline_all_names o
                REWRITE_RULE[tick_compile_prog_def]) THEN
  REWRITE_TAC[REVERSE; MAP; APPEND] THEN DISCH_THEN(ACCEPT_TAC o SYM));;


(* code labels *)

let bvl_inlineProof_var_list_code_labels_imp = prove
 (`!n x (y:A list). bvl_inline_var_list n x y ==>
     UNIONS (set_of_list (MAP bvl_get_code_labels x)) = {}`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; set_of_list; UNIONS_0]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
  CASES_ON `h:bvl_exp` THEN REWRITE_TAC[bvl_inline_var_list_def] THEN
  STRIP_TAC THEN REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN ASM_MESON_TAC[]);;

(* a local helper: the code labels of let_op_one and let_op_list *)
let BVLPROPSAUX_let_op_one_code_labels = prove
 (`(!e. bvl_get_code_labels (let_op_one e) = bvl_get_code_labels e) /\
   (!es. UNIONS (set_of_list (MAP bvl_get_code_labels (bvl_inline_let_op_list es))) =
         UNIONS (set_of_list (MAP bvl_get_code_labels es)))`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN REWRITE_TAC[let_op_one_def] THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ASM_REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN
  CASES_ON `bvl_inline_dest_op (let_op_one a1) (bvl_inline_let_op_list a0)` THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BVLPROPSAUX_dest_op_SOME o
    check (fun th -> BVLPROPSAUX_has_const "bvl_inline_dest_op" (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_inlineProof_var_list_code_labels_imp) THEN
  UNDISCH_TAC `bvl_get_code_labels (let_op_one a1) = bvl_get_code_labels a1` THEN
  ASM_REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN SET_TAC[]);;

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
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `z:A#num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:A` (X_CHOOSE_THEN `ae:num#bvl_exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `ae:num#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `e:bvl_exp` SUBST1_TAC)) THEN
  REWRITE_TAC[optimise_eq; SND] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `bvl_get_code_labels (bvl_inline_let_op_sing (bvl_inline_remove_ticks_sing e))` THEN
  REWRITE_TAC[BVLPROPSAUX_compile_any_code_labels; let_op_sing_code_labels;
              BVLPROPSAUX_remove_ticks_sing_code_labels; SUBSET_REFL]);;


(* local helpers: the code labels of the values of a code table *)
let BVLPROPSAUX_toList_labels = prove
 (`!(cs:(A#bvl_exp)spt) k a c.
     lookup k cs = SOME (a,c) ==>
     bvl_get_code_labels c SUBSET
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; o_THM] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `bvl_get_code_labels c` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(a:A,c:bvl_exp)` THEN REWRITE_TAC[SND; MEM_toList] THEN ASM_MESON_TAC[]);;

let BVLPROPSAUX_toList_insert_labels = prove
 (`!(cs:(A#bvl_exp)spt) n a e.
     UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList (insert n (a,e) cs))))
     SUBSET bvl_get_code_labels e UNION
            UNIONS (set_of_list (MAP (bvl_get_code_labels o SND) (toList cs)))`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP; o_THM; IN_UNION;
              MEM_toList; lookup_insert] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `t:num->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A#bvl_exp` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  UNDISCH_TAC `(if k = n then SOME (a:A,e:bvl_exp) else lookup k cs) = SOME y` THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "option"] THEN DISCH_TAC THENL
   [DISJ1_TAC THEN UNDISCH_TAC `(x:num) IN t` THEN
    UNDISCH_TAC `t = bvl_get_code_labels (SND (y:A#bvl_exp))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(a:A,e:bvl_exp) = y`)) THEN
    REWRITE_TAC[SND] THEN MESON_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `t:num->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:A#bvl_exp` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

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
  MATCH_MP_TAC bvl_exp_INDUCT THEN REWRITE_TAC[tick_inline_sing_def] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN
  TRY (ASM SET_TAC[] THEN NO_TAC) THEN
  CASES_ON `a1:num option` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN TRY (ASM SET_TAC[] THEN NO_TAC) THEN
  CASES_ON `lookup a (cs:(A#bvl_exp)spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC BVLPROPSAUX_LABELS_RWS THEN TRY (ASM SET_TAC[] THEN NO_TAC) THEN
  MP_TAC(ISPEC `a':A#bvl_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ar:A` (X_CHOOSE_THEN `code:bvl_exp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC(mk_tick_code_labels :: BVLPROPSAUX_LABELS_RWS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BVLPROPSAUX_toList_labels) THEN ASM SET_TAC[]);;

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
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_inline_compile_prog_def; bvl_inline_compile_inc_def;
              tick_compile_prog_def] THEN
  MP_TAC(ISPEC `tick_inline_all x LN (p:(num#num#bvl_exp)list) []` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:(num#bvl_exp)spt` (X_CHOOSE_THEN
    `p1:(num#num#bvl_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND)
                                        (p1:(num#num#bvl_exp)list)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC BVLPROPSAUX_UNIONS_MAP_MONO THEN
    REWRITE_TAC[o_THM; optimise_get_code_labels];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP tick_inline_all_code_labels) THEN
    REWRITE_TAC[toList_def; toListA_def; MAP; set_of_list; UNIONS_0; UNION_EMPTY]]);;

(* the HOL4 [simp] theorems of this theory, registered for the files that  *)
(* load this one (the proofs above do not rely on them through the simpset) *)
let _ = cake_add_simps [HD_let_op; MAP_FST_MAP_optimise; let_op_sing_code_labels];;
