(* ========================================================================= *)
(* bviProps: port of HOL4 compiler/backend/semantics/bviPropsScript.sml     *)
(* (CakeML v3479).  Properties about BVI and its semantics.                 *)
(*                                                                           *)
(* Notes on the rendering: as in bvlProps (record updates as fupd chains,   *)
(* GENLIST is list_of_seq, BIGUNION is UNIONS, set is set_of_list).          *)
(* BVLPROPSAUX_ names are local helpers (not HOL4 names); some come from     *)
(* bvlProps.                                                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;

type_invention_error := true;;

(* HOL4 [simp] *)
let bvi_initial_state_simp = prove
 (`!(f:(FFI)ffi_state) c (co:num -> C # (num # num # bvi_exp) list) cc k.
     bvi_state_code (bvi_initial_state f c co cc k) = c /\
     bvi_state_ffi (bvi_initial_state f c co cc k) = f /\
     bvi_state_clock (bvi_initial_state f c co cc k) = k /\
     bvi_state_compile (bvi_initial_state f c co cc k) = cc /\
     bvi_state_compile_oracle (bvi_initial_state f c co cc k) = co /\
     bvi_state_refs (bvi_initial_state f c co cc k) = FEMPTY /\
     bvi_state_global (bvi_initial_state f c co cc k) = NONE`,
  REWRITE_TAC[bvi_initial_state_def; bvi_state_INFO.ri_accessors]);;
let _ = cake_add_simps [bvi_initial_state_simp];;

(* HOL4 [simp] *)
let bvi_initial_state_with_simp = prove
 (`!(f:(FFI)ffi_state) c (co:num -> C # (num # num # bvi_exp) list) cc k k1 c1.
     bvi_state_clock_fupd (K k1) (bvi_initial_state f c co cc k) =
     bvi_initial_state f c co cc k1 /\
     bvi_state_code_fupd (K c1) (bvi_initial_state f c co cc k) =
     bvi_initial_state f c1 co cc k`,
  REWRITE_TAC[bvi_initial_state_def; bvi_state_INFO.ri_fupds; K_THM]);;
let _ = cake_add_simps [bvi_initial_state_with_simp];;

let bvl_to_bvi_id = prove
 (`!s:(C,FFI)bvi_state. bvl_to_bvi (bvi_to_bvl s) s = s`,
  SIMP[bvl_to_bvi_def; bvi_to_bvl_def; bvi_state_component_equality]);;

let bvl_to_bvi_with_refs = prove
 (`!(x:(C,FFI)bvl_state) y (z:(C,FFI)bvi_state).
     bvl_to_bvi (bvl_state_refs_fupd (K y) x) z =
     bvi_state_refs_fupd (K y) (bvl_to_bvi x z)`,
  SIMP[bvl_to_bvi_def]);;

let bvl_to_bvi_with_clock = prove
 (`!(x:(C,FFI)bvl_state) y (z:(C,FFI)bvi_state).
     bvl_to_bvi (bvl_state_clock_fupd (K y) x) z =
     bvi_state_clock_fupd (K y) (bvl_to_bvi x z)`,
  SIMP[bvl_to_bvi_def]);;

let bvl_to_bvi_with_ffi = prove
 (`!(x:(C,FFI)bvl_state) y (z:(C,FFI)bvi_state).
     bvl_to_bvi (bvl_state_ffi_fupd (K y) x) z =
     bvi_state_ffi_fupd (K y) (bvl_to_bvi x z)`,
  SIMP[bvl_to_bvi_def]);;

(* HOL4 [simp] *)
let bvl_to_bvi_code = prove
 (`!(x:(C,FFI)bvl_state) (y:(C,FFI)bvi_state).
     bvi_state_code (bvl_to_bvi x y) = bvi_state_code y`,
  REWRITE_TAC[bvl_to_bvi_def; bvi_state_INFO.ri_accfupds]);;

(* HOL4 [simp] *)
let bvl_to_bvi_clock = prove
 (`!(x:(C,FFI)bvl_state) (y:(C,FFI)bvi_state).
     bvi_state_clock (bvl_to_bvi x y) = bvl_state_clock x`,
  REWRITE_TAC[bvl_to_bvi_def; bvi_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 [simp] *)
let bvi_bvi_to_bvl_refs = prove
 (`!x:(C,FFI)bvi_state. bvl_state_refs (bvi_to_bvl x) = bvi_state_refs x`,
  REWRITE_TAC[bvi_to_bvl_def; bvl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 [simp] *)
let bvi_to_bvl_code = prove
 (`!x:(C,FFI)bvi_state.
     bvl_state_code (bvi_to_bvl x) = sptree_map (K (ARB:num # bvl_exp)) (bvi_state_code x)`,
  REWRITE_TAC[bvi_to_bvl_def; bvl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 [simp] *)
let bvi_to_bvl_clock = prove
 (`!x:(C,FFI)bvi_state. bvl_state_clock (bvi_to_bvl x) = bvi_state_clock x`,
  REWRITE_TAC[bvi_to_bvl_def; bvl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 [simp] *)
let bvi_to_bvl_ffi = prove
 (`!x:(C,FFI)bvi_state. bvl_state_ffi (bvi_to_bvl x) = bvi_state_ffi x`,
  REWRITE_TAC[bvi_to_bvl_def; bvl_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [bvl_to_bvi_code; bvl_to_bvi_clock; bvi_bvi_to_bvl_refs;
                        bvi_to_bvl_code; bvi_to_bvl_clock; bvi_to_bvl_ffi];;

let bvi_to_bvl_to_bvi_with_ffi = prove
 (`!(x:(C,FFI)bvi_state) f.
     bvl_to_bvi (bvl_state_ffi_fupd (K f) (bvi_to_bvl x)) x = bvi_state_ffi_fupd (K f) x`,
  SIMP[bvl_to_bvi_def; bvi_to_bvl_def; bvi_state_component_equality]);;

(* HOL4 [simp] *)
let domain_bvi_to_bvl_code = prove
 (`!s:(C,FFI)bvi_state.
     domain (bvl_state_code (bvi_to_bvl s)) = domain (bvi_state_code s)`,
  REWRITE_TAC[bvi_to_bvl_code; domain_map]);;
let _ = cake_add_simps [domain_bvi_to_bvl_code];;

(* HOL4 [local] *)
let pair_case_elim = prove
 (CASE_TERM `!(p:A#B) f. (match p with (x,y) -> f x y) <=> ?x y. p = (x,y) /\ f x y`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4: prove_case_elim_thm makes  ty_CASE x f1 .. fn <=> (?a. x = C1 a /\ *)
(* f1 a) \/ ...  for a bool-valued case; here from the case equation        *)
let BVLPROPSAUX_case_elim (th:thm) : thm =
  let th1 = SPEC_ALL th in
  let v = rand (lhs (concl th1)) in
  let th2 = INST_TYPE [`:bool`,type_of v] th1 in
  let v' = rand (lhs (concl th2)) in
  GEN_ALL (REWRITE_RULE[EQ_CLAUSES] (INST [`T`,v'] th2));;

let case_elim_thms = end_itlist CONJ
  (pair_case_elim ::
   map BVLPROPSAUX_case_elim
     [list_case_eq; option_case_eq; case_eq "result"; case_eq "ffi_result"]);;

(* HOL4: case_eq_thms, the case equations of exp and exn_or_ret with        *)
(* bvlProps' case_eq_thms                                                    *)
let bvi_case_eq_thms = end_itlist CONJ
  [case_eq "bvi_exp"; case_eq "exn_or_ret"; bvlProps_case_eq_thms];;

(* ------------------------------------------------------------------------- *)
(* Local helpers for proofs by induction on bvi_evaluate (as in bvlProps).   *)
(* ------------------------------------------------------------------------- *)

let BVLPROPSAUX_bvi_evaluate_ind =
  let p = `P:bvi_exp list -> bvl_v list -> (C,FFI)bvi_state -> bool` in
  let th = ISPEC
    `\t:bvi_exp list # bvl_v list # (C,FFI)bvi_state.
        (P:bvi_exp list -> bvl_v list -> (C,FFI)bvi_state -> bool)
        (FST t) (FST (SND t)) (SND (SND t))` bvi_evaluate_ind in
  let th = PURE_REWRITE_RULE[FST; SND] (CONV_RULE (DEPTH_CONV BETA_CONV) th) in
  let hy = lhand (concl th) in
  let goal = mk_imp(hy,
    `!xs env s. (P:bvi_exp list -> bvl_v list -> (C,FFI)bvi_state -> bool) xs env s`) in
  GEN p (prove(goal,
    DISCH_TAC THEN MP_TAC(MP th (ASSUME hy)) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND]));;

let BVLPROPSAUX_bvi_eval_case_eqs =
  [pair_case_eq; COND_CASE_EQ; option_case_eq; list_case_eq; case_eq "result";
   case_eq "error_result"; case_eq "bvi_dest_thunk_ret"; case_eq "thunk_mode";
   case_eq "exn_or_ret";
   PAIR_EQ; injectivity "result"; distinctness "result"];;

let BVLPROPSAUX_bvi_eval_simps =
  flat (map (fun s -> BVLPROPSAUX_both (distinctness s))
          ["result"; "option"; "list"; "error_result"; "abort";
           "bvi_dest_thunk_ret"; "thunk_mode"; "exn_or_ret"]) @
  map injectivity ["result"; "option"; "list"; "error_result"; "abort";
                   "bvi_dest_thunk_ret"; "exn_or_ret"] @ [PAIR_EQ];;

let BVLPROPSAUX_bvi_CLEAN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE BVLPROPSAUX_bvi_eval_simps) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN TRY RVEQ_TAC;;

let BVLPROPSAUX_bvi_SPLIT_TAC : tactic =
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC BVLPROPSAUX_bvi_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN
  BVLPROPSAUX_bvi_CLEAN_TAC;;

(* a resolution tactic as BVLPROPSAUX_RES_TAC (bvlProps) with deeper       *)
(* chains (the Call and LetCall cases of BVI have long contexts) and the     *)
(* one-point rule for the context variables                                  *)
let BVLPROPSAUX_bvi_RES_TAC : tactic = fun (asl,w as gl) ->
  let asms = map (REWRITE_RULE[FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] o snd) asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let imps = filter is_impth asms in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let mp = MATCH_MP th in
    let rs = mapfilter (fun a -> curry (mp a)) asms in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let results =
    flat (map (fun th -> let mp = MATCH_MP (curry th) in
                 flat (map (resolve 8) (mapfilter (fun a -> curry (mp a)) asms)))
              imps) in
  let results = filter (fun th -> not (exists (fun a -> concl a = concl th) asms)) results in
  EVERY (map CAKE_ASSUME_TAC results) gl;;

(* HOL4 fs [evaluate_def] \\ gvs [AllCaseEqs()] on one hypothesis: the    *)
(* assumption bvi_evaluate .. = .. that the pattern matches (the newest),    *)
(* unfolded once and split into its cases                                    *)
let BVLPROPSAUX_bvi_EVAL_SPLIT_TAC (pat:string) : tactic =
  QPAT_X_ASSUM pat (CAKE_STRIP_ASSUME_TAC o REWRITE_RULE BVLPROPSAUX_bvi_eval_case_eqs o
                    BETA_RULE o REWRITE_RULE[LET_DEF; LET_END_DEF] o
                    ONCE_REWRITE_RULE[bvi_evaluate_def]) THEN
  RVEQ_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC;;

(* HOL4 proves evaluate_LENGTH (below) first, and this from it *)
let bvi_evaluate_IMP_LENGTH = prove
 (`!xs (s:bvl_v list) (env:(C,FFI)bvi_state) res s1.
     bvi_evaluate (xs,s,env) = (Rval res,s1) ==> LENGTH xs = LENGTH res`,
  REC_IND_TAC bvi_evaluate_ind THEN REPEAT STRIP_TAC THEN BVLPROPSAUX_bvi_SPLIT_TAC THEN
  BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ONE]);;

(* HOL4: evaluate_LENGTH (the variable names are HOL4's) *)
let bvi_evaluate_LENGTH = prove
 (CASE_TERM `!xs (s:bvl_v list) (env:(C,FFI)bvi_state).
     match bvi_evaluate (xs,s,env) with
       (Rval res,s1) -> LENGTH xs = LENGTH res
     | _ -> T`,
  REWRITE_TAC[BVLPROPSAUX_match_Rval] THEN MESON_TAC[bvi_evaluate_IMP_LENGTH]);;

let evaluate_SING_IMP = prove
 (`!x env (s1:(C,FFI)bvi_state) vs s2.
     bvi_evaluate ([x],env,s1) = (Rval vs,s2) ==> ?w. vs = [w]`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC bvi_evaluate_IMP_LENGTH THEN
  CASES_ON `vs:bvl_v list` THEN FS[LENGTH_EQ_NIL]);;

let bvi_evaluate_CONS = prove
 (CASE_TERM `!x xs env (s:(C,FFI)bvi_state).
     bvi_evaluate (CONS x xs,env,s) =
     match bvi_evaluate ([x],env,s) with
       (Rval v,s2) ->
         (match bvi_evaluate (xs,env,s2) with
            (Rval vs,s1) -> (Rval (CONS (HD v) vs),s1)
          | t -> t)
     | t -> t`,
  REPEAT GEN_TAC THEN CASES_ON `xs:bvi_exp list` THEN FS[bvi_evaluate_def] THEN
  REPEAT TOP_CASE_TAC THEN IMP_RES_TAC evaluate_SING_IMP THEN FS[]);;

(* HOL4 proves evaluate_SNOC before evaluate_APPEND (by induction); here it *)
(* follows from evaluate_APPEND                                              *)
let bvi_evaluate_APPEND = prove
 (CASE_TERM `!xs env (s:(C,FFI)bvi_state) ys.
     bvi_evaluate (APPEND xs ys,env,s) =
     match bvi_evaluate (xs,env,s) with
       (Rval vs,s2) ->
         (match bvi_evaluate (ys,env,s2) with
            (Rval ws,s1) -> (Rval (APPEND vs ws),s1)
          | res -> res)
     | res -> res`,
  LIST_INDUCT_TAC THEN FS[APPEND; bvi_evaluate_def] THEN REPEAT STRIP_TAC THENL
   [EVERY_CASE_TAC; ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN EVERY_CASE_TAC THEN FS[]]);;

let bvi_evaluate_SNOC = prove
 (CASE_TERM `!xs env (s:(C,FFI)bvi_state) x.
     bvi_evaluate (SNOC x xs,env,s) =
     match bvi_evaluate (xs,env,s) with
       (Rval vs,s2) ->
         (match bvi_evaluate ([x],env,s2) with
            (Rval v,s1) -> (Rval (APPEND vs v),s1)
          | t -> t)
     | t -> t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SNOC_APPEND; bvi_evaluate_APPEND]);;

let bvi_inc_clock_def = cake_def
  `bvi_inc_clock n (s:(C,FFI)bvi_state) =
     bvi_state_clock_fupd (K (bvi_state_clock s + n)) s`;;

let inc_clock_ZERO = prove
 (`!s:(C,FFI)bvi_state. bvi_inc_clock 0 s = s`,
  SIMP[bvi_inc_clock_def; bvi_state_component_equality]);;

let inc_clock_ADD = prove
 (`!n m (s:(C,FFI)bvi_state).
     bvi_inc_clock n (bvi_inc_clock m s) = bvi_inc_clock (n + m) s`,
  SIMP[bvi_inc_clock_def; bvi_state_component_equality; ADD_AC]);;

(* HOL4 [simp] *)
let bvi_inc_clock_refs = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_refs (bvi_inc_clock n s) = bvi_state_refs s`,
  SIMP[bvi_inc_clock_def]);;

(* HOL4 [simp] *)
let bvi_inc_clock_code = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_code (bvi_inc_clock n s) = bvi_state_code s`,
  SIMP[bvi_inc_clock_def]);;

(* HOL4 [simp] *)
let inc_clock_global = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_global (bvi_inc_clock n s) = bvi_state_global s`,
  SIMP[bvi_inc_clock_def]);;

(* HOL4 [simp] *)
let bvi_inc_clock_ffi = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_ffi (bvi_inc_clock n s) = bvi_state_ffi s`,
  SIMP[bvi_inc_clock_def]);;

(* HOL4 [simp] *)
let bvi_inc_clock_clock = prove
 (`!n (s:(C,FFI)bvi_state).
     bvi_state_clock (bvi_inc_clock n s) = bvi_state_clock s + n`,
  SIMP[bvi_inc_clock_def]);;
let _ = cake_add_simps [bvi_inc_clock_refs; bvi_inc_clock_code; inc_clock_global;
                        bvi_inc_clock_ffi; bvi_inc_clock_clock];;

(* HOL4 [simp] *)
let dec_clock_global = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_global (bvi_dec_clock n s) = bvi_state_global s`,
  SIMP[bvi_dec_clock_def]);;

(* HOL4 [simp] *)
let bvi_dec_clock_ffi = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_ffi (bvi_dec_clock n s) = bvi_state_ffi s`,
  SIMP[bvi_dec_clock_def]);;

(* HOL4 [simp] *)
let bvi_dec_clock_refs = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_refs (bvi_dec_clock n s) = bvi_state_refs s`,
  SIMP[bvi_dec_clock_def]);;

(* HOL4 [simp] *)
let bvi_dec_clock_with_code = prove
 (`!n c (s:(C,FFI)bvi_state).
     bvi_dec_clock n (bvi_state_code_fupd (K c) s) =
     bvi_state_code_fupd (K c) (bvi_dec_clock n s)`,
  SIMP[bvi_dec_clock_def; bvi_state_component_equality]);;

(* HOL4 [simp] *)
let bvi_dec_clock_code = prove
 (`!n (s:(C,FFI)bvi_state). bvi_state_code (bvi_dec_clock n s) = bvi_state_code s`,
  SIMP[bvi_dec_clock_def]);;
let _ = cake_add_simps [dec_clock_global; bvi_dec_clock_ffi; bvi_dec_clock_refs;
                        bvi_dec_clock_with_code; bvi_dec_clock_code];;

let dec_clock_inv_clock = prove
 (`!ticks c (t1:(C,FFI)bvi_state).
     ~(bvi_state_clock t1 < ticks + 1) ==>
     bvi_dec_clock (ticks + 1) (bvi_inc_clock c t1) =
     bvi_inc_clock c (bvi_dec_clock (ticks + 1) t1)`,
  RW[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_component_equality] THEN DECIDE_TAC);;

let dec_clock_inv_clock1 = prove
 (`!c (t1:(C,FFI)bvi_state).
     ~(bvi_state_clock t1 = 0) ==>
     bvi_dec_clock 1 (bvi_inc_clock c t1) = bvi_inc_clock c (bvi_dec_clock 1 t1)`,
  RW[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_component_equality] THEN DECIDE_TAC);;

(* HOL4 [simp] *)
let bvi_dec_clock0 = prove
 (`!(n:num) (s:(C,FFI)bvi_state). bvi_dec_clock 0 s = s`,
  SIMP[bvi_dec_clock_def; bvi_state_component_equality]);;
let _ = cake_add_simps [bvi_dec_clock0];;

(* ------------------------------------------------------------------------- *)
(* Local helpers: do_app copies the clock.  HOL4 proves do_app_inv_clock,   *)
(* do_app_change_clock and do_app_change_clock_err by case splits of         *)
(* do_app (and bvlProps' lemmas for the BVL operations).                     *)
(* ------------------------------------------------------------------------- *)

let BVLPROPSAUX_do_app_aux_clock = prove
 (CASE_TERM `!op vs (s:(C,FFI)bvi_state) f.
     bvi_do_app_aux op vs (bvi_state_clock_fupd f s) =
     OPTION_MAP (OPTION_MAP (\p. match p with (x,y) -> (x,bvi_state_clock_fupd f y)))
                (bvi_do_app_aux op vs s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_aux_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_state_INFO.ri_accfupds] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[OPTION_MAP_DEF; pair_CASE; bvi_state_INFO.ri_fupdcanon]);;

let BVLPROPSAUX_bvi_to_bvl_clock = prove
 (`!(s:(C,FFI)bvi_state) f.
     bvi_to_bvl (bvi_state_clock_fupd f s) = bvl_state_clock_fupd f (bvi_to_bvl s)`,
  REWRITE_TAC[bvi_to_bvl_def; bvi_state_INFO.ri_accfupds] THEN
  SIMP[bvl_state_component_equality]);;

let BVLPROPSAUX_bvl_to_bvi_clock = prove
 (`!(t:(C,FFI)bvl_state) (s:(C,FFI)bvi_state) f.
     bvl_to_bvi (bvl_state_clock_fupd f t) (bvi_state_clock_fupd f s) =
     bvi_state_clock_fupd f (bvl_to_bvi t s)`,
  REWRITE_TAC[bvl_to_bvi_def; bvl_state_INFO.ri_accfupds] THEN
  SIMP[bvi_state_component_equality]);;

let BVLPROPSAUX_bvi_do_install_clock = prove
 (CASE_TERM `!vs (s:(C,FFI)bvi_state) f.
     (bvi_do_install vs (bvi_state_clock_fupd f s):
        (bvl_v # (C,FFI)bvi_state,E)result) =
     map_result (\p. match p with (v,s1) -> (v,bvi_state_clock_fupd f s1)) I
                (bvi_do_install vs s)`,
  SIMP[bvi_do_install_def] THEN REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN SIMP[map_result_def; map_error_result_I] THEN
  SIMP[bvi_state_component_equality]);;

let BVLPROPSAUX_bvi_clock_rws = [OPTION_MAP_DEF; case_def "option"; map_result_def;
  map_error_result_I; I_THM; pair_CASE; case_def "result"; case_def "error_result";
  BVLPROPSAUX_bvl_to_bvi_clock; option_DISTINCT; option_INJ; injectivity "result";
  distinctness "result"];;

let BVLPROPSAUX_bvi_do_app_clock = prove
 (CASE_TERM `!op vs (s:(C,FFI)bvi_state) f.
     bvi_do_app op vs (bvi_state_clock_fupd f s) =
     map_result (\p. match p with (v,s1) -> (v,bvi_state_clock_fupd f s1)) I
                (bvi_do_app op vs s)`,
  REWRITE_TAC[bvi_do_app_def; BVLPROPSAUX_do_app_aux_clock; BVLPROPSAUX_bvi_to_bvl_clock;
              BVLPROPSAUX_do_app_clock; BVLPROPSAUX_bvi_do_install_clock] THEN
  REPEAT GEN_TAC THEN REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  FS[map_result_def; BVLPROPSAUX_bvl_to_bvi_clock; map_error_result_I]);;

(* a local helper: do_app keeps the clock, so inc_clock commutes with it *)
let BVLPROPSAUX_bvi_do_app_inc = prove
 (CASE_TERM `!op vs n (s:(C,FFI)bvi_state).
     bvi_do_app op vs (bvi_inc_clock n s) =
     map_result (\p. match p with (v,s1) -> (v,bvi_inc_clock n s1)) I
                (bvi_do_app op vs s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_inc_clock_def; BVLPROPSAUX_bvi_do_app_clock] THEN
  MP_TAC(ISPECL [`op:clos_op`; `vs:bvl_v list`; `s:(C,FFI)bvi_state`]
                bvi_do_app_const) THEN
  CASES_ON `bvi_do_app op vs (s:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[map_result_def] THEN
  CASES_ON `a:bvl_v#(C,FFI)bvi_state` THEN
  REWRITE_TAC[pair_CASE; injectivity "result"; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let do_app_inv_clock = prove
 (CASE_TERM `!op a (s:(C,FFI)bvi_state) n.
     match bvi_do_app op (REVERSE a) s with
       Rerr e -> bvi_do_app op (REVERSE a) (bvi_inc_clock n s) = Rerr e
     | Rval (v,s1) ->
         bvi_do_app op (REVERSE a) (bvi_inc_clock n s) = Rval (v,bvi_inc_clock n s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_bvi_do_app_inc] THEN
  CASES_ON `bvi_do_app op (REVERSE a) (s:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[case_def "result"; map_result_def; map_error_result_I; I_THM] THEN
  CASES_ON `a':bvl_v#(C,FFI)bvi_state` THEN REWRITE_TAC[pair_CASE]);;

(* HOL4 [local] *)
let do_app_inc_clock_IMP = prove
 (`!op vs (s:(C,FFI)bvi_state) v s1 n e.
     (bvi_do_app op vs s = Rval (v,s1) ==>
      bvi_do_app op vs (bvi_inc_clock n s) = Rval (v,bvi_inc_clock n s1)) /\
     (bvi_do_app op vs s = Rerr e ==> bvi_do_app op vs (bvi_inc_clock n s) = Rerr e)`,
  SIMP_TAC[BVLPROPSAUX_bvi_do_app_inc; map_result_def; map_error_result_I; I_THM;
           pair_CASE]);;

let evaluate_inv_clock = prove
 (`!xs env (t1:(C,FFI)bvi_state) res t2 n.
     bvi_evaluate (xs,env,t1) = (res,t2) /\ ~(res = Rerr (Rabort Rtimeout_error)) ==>
     bvi_evaluate (xs,env,bvi_inc_clock n t1) = (res,bvi_inc_clock n t2)`,
  REC_IND_TAC bvi_evaluate_ind THEN REPEAT STRIP_TAC THEN
  BVLPROPSAUX_bvi_EVAL_SPLIT_TAC "bvi_evaluate (_,_,(_:(C,FFI)bvi_state)) = _" THEN
  BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN IMP_RES_TAC do_app_inc_clock_IMP THEN
  SIMP[ARITH_ss; dec_clock_inv_clock; dec_clock_inv_clock1]);;

(* a local helper: the BVI-specific operations change only the global       *)
(* pointer and the references *)
let BVLPROPSAUX_do_app_aux_consts = prove
 (`!op vs (s:(C,FFI)bvi_state) v t.
     bvi_do_app_aux op vs s = SOME (SOME (v,t)) ==>
     bvi_state_code t = bvi_state_code s /\
     bvi_state_compile_oracle t = bvi_state_compile_oracle s /\
     bvi_state_compile t = bvi_state_compile s /\
     bvi_state_ffi t = bvi_state_ffi s /\
     bvi_state_clock t = bvi_state_clock s /\
     (IS_SOME (bvi_state_global s) ==> IS_SOME (bvi_state_global t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_aux_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; IS_SOME_DEF]);;

(* a local helper: do_app apart from Install keeps the code and the oracle *)
let BVLPROPSAUX_bvi_do_app_consts = prove
 (`!op a (s1:(C,FFI)bvi_state) x0 s2.
     bvi_do_app op a s1 = Rval (x0,s2) /\ ~(op = clos_Install) ==>
     bvi_state_code s2 = bvi_state_code s1 /\
     bvi_state_compile_oracle s2 = bvi_state_compile_oracle s1 /\
     bvi_state_compile s2 = bvi_state_compile s1 /\
     (IS_SOME (bvi_state_global s1) ==> IS_SOME (bvi_state_global s2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_def] THEN
  ASM_CASES_TAC `op = clos_Install` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[option_case_eq; case_eq "result"; case_eq "error_result"; pair_case_eq;
              PAIR_EQ; injectivity "result"; distinctness "result"; option_DISTINCT;
              option_INJ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  TRY (FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BVLPROPSAUX_do_app_aux_consts)) THEN
  ASM_REWRITE_TAC[bvl_to_bvi_def; bvi_state_INFO.ri_accfupds] THEN
  ASM_MESON_TAC[]);;

let do_app_code = prove
 (`!op a (s1:(C,FFI)bvi_state) x0 s2.
     bvi_do_app op a s1 = Rval (x0,s2) /\ ~(op = clos_Install) ==>
     bvi_state_code s2 = bvi_state_code s1`,
  MESON_TAC[BVLPROPSAUX_bvi_do_app_consts]);;

let do_app_oracle = prove
 (`!op a (s1:(C,FFI)bvi_state) x0 s2.
     bvi_do_app op a s1 = Rval (x0,s2) /\ ~(op = clos_Install) ==>
     bvi_state_compile_oracle s2 = bvi_state_compile_oracle s1 /\
     bvi_state_compile s2 = bvi_state_compile s1`,
  MESON_TAC[BVLPROPSAUX_bvi_do_app_consts]);;

(* HOL4 [local] *)
let GENLIST_add_split = prove
 (`!(f:num->A) a b.
     APPEND (list_of_seq f a) (list_of_seq (\i. f (a + i)) b) = list_of_seq f (a + b)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GENLIST_APPEND] THEN REWRITE_TAC[ADD_SYM]);;

(* HOL4 [local] *)
let FOLDL_union_GENLIST_split = prove
 (`!c (f:num -> C # (num # num # bvi_exp) list) a b.
     FOLDL sptree_union (FOLDL sptree_union c (MAP (fromAList o SND) (list_of_seq f a)))
       (MAP (fromAList o SND) (list_of_seq (\i. f (i + a)) b)) =
     FOLDL sptree_union c (MAP (fromAList o SND) (list_of_seq f (a + b)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\i. (f:num -> C # (num # num # bvi_exp) list) (i + a)) = (\i. f (a + i))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; ADD_SYM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM GENLIST_add_split; MAP_APPEND; FOLDL_APPEND]);;

(* a local helper for evaluate_code: the oracle and code of a later state   *)
(* come from those of an earlier one by installing n programs              *)
let BVLPROPSAUX_bvi_code_inv_def = new_definition
 `BVLPROPSAUX_bvi_code_inv (co:num -> C # (num # num # bvi_exp) list)
                           (code:(num # bvi_exp) spt) co1 code1 <=>
    ?n. co1 = shift_seq n co /\
        code1 = FOLDL sptree_union code (MAP (fromAList o SND) (list_of_seq co n))`;;

let BVLPROPSAUX_bvi_code_inv_refl = prove
 (`!(co:num -> C # (num # num # bvi_exp) list) code.
     BVLPROPSAUX_bvi_code_inv co code co code`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_bvi_code_inv_def] THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES; ETA_AX; list_of_seq; MAP; FOLDL]);;

let BVLPROPSAUX_bvi_code_inv_trans = prove
 (`!(co:num -> C # (num # num # bvi_exp) list) code co1 code1 co2 code2.
     BVLPROPSAUX_bvi_code_inv co code co1 code1 /\
     BVLPROPSAUX_bvi_code_inv co1 code1 co2 code2 ==>
     BVLPROPSAUX_bvi_code_inv co code co2 code2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_bvi_code_inv_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `n2 + n1:num` THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REWRITE_TAC[GENLIST_APPEND; MAP_APPEND; FOLDL_APPEND] THEN
  REWRITE_TAC[shift_seq_def; FUN_EQ_THM; ADD_ASSOC]);;

(* a local helper: Install changes the code and the oracle only *)
let BVLPROPSAUX_bvi_do_install_code = prove
 (`!vs (s:(C,FFI)bvi_state) v s'.
     bvi_do_install vs s = (Rval (v,s'):(bvl_v # (C,FFI)bvi_state,E)result) ==>
     BVLPROPSAUX_bvi_code_inv (bvi_state_compile_oracle s) (bvi_state_code s)
                              (bvi_state_compile_oracle s') (bvi_state_code s') /\
     bvi_state_global s' = bvi_state_global s /\
     bvi_state_refs s' = bvi_state_refs s /\
     bvi_state_ffi s' = bvi_state_ffi s /\
     bvi_state_clock s' = bvi_state_clock s /\
     bvi_state_compile s' = bvi_state_compile s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; BVLPROPSAUX_bvi_code_inv_def] THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC[ONE; list_of_seq; APPEND; MAP; FOLDL; o_THM]);;

let BVLPROPSAUX_bvi_do_app_code = prove
 (`!op vs (s:(C,FFI)bvi_state) v s'.
     bvi_do_app op vs s = Rval (v,s') ==>
     BVLPROPSAUX_bvi_code_inv (bvi_state_compile_oracle s) (bvi_state_code s)
                              (bvi_state_compile_oracle s') (bvi_state_code s') /\
     (IS_SOME (bvi_state_global s) ==> IS_SOME (bvi_state_global s'))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [ASM_REWRITE_TAC[bvi_do_app_def] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BVLPROPSAUX_bvi_do_install_code) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`op:clos_op`; `vs:bvl_v list`; `s:(C,FFI)bvi_state`;
                   `v:bvl_v`; `s':(C,FFI)bvi_state`] BVLPROPSAUX_bvi_do_app_consts) THEN
    ASM_SIMP_TAC[BVLPROPSAUX_bvi_code_inv_refl]]);;

let BVLPROPSAUX_bvi_evaluate_code_lemma = prove
 (`!xs env (s:(C,FFI)bvi_state) res s1.
      bvi_evaluate (xs,env,s) = (res,s1) ==>
      BVLPROPSAUX_bvi_code_inv (bvi_state_compile_oracle s) (bvi_state_code s)
                               (bvi_state_compile_oracle s1) (bvi_state_code s1)`,
  REC_IND_TAC bvi_evaluate_ind THEN REPEAT STRIP_TAC THEN BVLPROPSAUX_bvi_SPLIT_TAC THEN
  BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  IMP_RES_TAC BVLPROPSAUX_bvi_do_app_code THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM;
                  BVLPROPSAUX_bvi_code_inv_refl] THEN
  ASM_MESON_TAC[BVLPROPSAUX_bvi_code_inv_trans; BVLPROPSAUX_bvi_code_inv_refl]);;

(* a local helper: evaluate_global_mono_lemma in implication form *)
let BVLPROPSAUX_bvi_global_mono = prove
 (`!xs env (s:(C,FFI)bvi_state).
      IS_SOME (bvi_state_global s) ==>
      !res s1. bvi_evaluate (xs,env,s) = (res,s1) ==> IS_SOME (bvi_state_global s1)`,
  REC_IND_TAC bvi_evaluate_ind THEN REPEAT STRIP_TAC THEN BVLPROPSAUX_bvi_SPLIT_TAC THEN
  BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  IMP_RES_TAC BVLPROPSAUX_bvi_do_app_code THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dec_clock_global; bvi_state_INFO.ri_accfupds]) THEN
  ASM_REWRITE_TAC[dec_clock_global; bvi_state_INFO.ri_accfupds] THEN
  ASM_MESON_TAC[]);;

let bvi_evaluate_code = prove
 (`!xs env (s1:(C,FFI)bvi_state) vs s2.
     bvi_evaluate (xs,env,s1) = (vs,s2) ==>
     ?n. bvi_state_compile_oracle s2 = shift_seq n (bvi_state_compile_oracle s1) /\
         bvi_state_code s2 =
         FOLDL sptree_union (bvi_state_code s1)
               (MAP (fromAList o SND) (list_of_seq (bvi_state_compile_oracle s1) n))`,
  REWRITE_TAC[GSYM BVLPROPSAUX_bvi_code_inv_def] THEN
  MESON_TAC[BVLPROPSAUX_bvi_evaluate_code_lemma]);;

let evaluate_code_mono = prove
 (`!xs env (s1:(C,FFI)bvi_state) vs s2.
     bvi_evaluate (xs,env,s1) = (vs,s2) ==>
     subspt (bvi_state_code s1) (bvi_state_code s2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP bvi_evaluate_code) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[subspt_FOLDL_union]);;

(* HOL4 [local] *)
let evaluate_global_mono_lemma = prove
 (`!xs env (s:(C,FFI)bvi_state).
     IS_SOME (bvi_state_global s) ==>
     IS_SOME (bvi_state_global (SND (bvi_evaluate (xs,env,s))))`,
  MESON_TAC[BVLPROPSAUX_bvi_global_mono; PAIR; SND]);;

let evaluate_global_mono = prove
 (`!xs env (s:(C,FFI)bvi_state) res t.
     bvi_evaluate (xs,env,s) = (res,t) ==>
     IS_SOME (bvi_state_global s) ==> IS_SOME (bvi_state_global t)`,
  MESON_TAC[evaluate_global_mono_lemma; SND]);;

let bvi_do_app_err = prove
 (`!op vs (s:(C,FFI)bvi_state) e.
     bvi_do_app op vs s = Rerr e ==>
     e = Rabort Rtype_error \/
     (?i x. op = clos_FFI i /\ e = Rabort (Rffi_error x))`,
  REWRITE_TAC[bvi_do_app_def; bvi_do_install_def] THEN REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN RW[] THEN IMP_RES_TAC bvl_do_app_err THEN FS[]);;

let bvi_do_app_aux_const = prove
 (`!op vs (s:(C,FFI)bvi_state) y z.
     bvi_do_app_aux op vs s = SOME (SOME (y,z)) ==>
     bvi_state_clock z = bvi_state_clock s`,
  MESON_TAC[BVLPROPSAUX_do_app_aux_consts]);;

(* HOL4 proves do_app_cfg_swap later (with the adj_orac lemmas), after    *)
(* do_app_with_code and do_app_with_code_err; here these follow from it    *)

(* local helpers for do_app_cfg_swap: the BVI view of a state t with the    *)
(* refs, clock, global and ffi of s; do_app_aux on it                        *)
let BVLPROPSAUX_swap_def = new_definition
 `BVLPROPSAUX_swap (s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) =
    bvi_state_refs_fupd (K (bvi_state_refs s))
      (bvi_state_clock_fupd (K (bvi_state_clock s))
        (bvi_state_global_fupd (K (bvi_state_global s))
          (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))`;;

let BVLPROPSAUX_swap_acc = prove
 (`!(s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state).
     bvi_state_refs (BVLPROPSAUX_swap s t) = bvi_state_refs s /\
     bvi_state_clock (BVLPROPSAUX_swap s t) = bvi_state_clock s /\
     bvi_state_global (BVLPROPSAUX_swap s t) = bvi_state_global s /\
     bvi_state_ffi (BVLPROPSAUX_swap s t) = bvi_state_ffi s /\
     bvi_state_code (BVLPROPSAUX_swap s t) = bvi_state_code t /\
     bvi_state_compile (BVLPROPSAUX_swap s t) = bvi_state_compile t /\
     bvi_state_compile_oracle (BVLPROPSAUX_swap s t) = bvi_state_compile_oracle t`,
  REWRITE_TAC[BVLPROPSAUX_swap_def; bvi_state_INFO.ri_accfupds; K_THM]);;

let BVLPROPSAUX_swap_fupd = prove
 (`!(s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) r g.
     bvi_state_refs_fupd (K r) (BVLPROPSAUX_swap s t) =
     BVLPROPSAUX_swap (bvi_state_refs_fupd (K r) s) t /\
     bvi_state_global_fupd (K g) (BVLPROPSAUX_swap s t) =
     BVLPROPSAUX_swap (bvi_state_global_fupd (K g) s) t`,
  REWRITE_TAC[BVLPROPSAUX_swap_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  SIMP[bvi_state_component_equality]);;

(* the swap of a state with code c and the oracle of s1 *)
let BVLPROPSAUX_swap_code = prove
 (`!(s1:(A,FFI)bvi_state) (s:(A,FFI)bvi_state) c.
     bvi_state_compile s1 = bvi_state_compile s /\
     bvi_state_compile_oracle s1 = bvi_state_compile_oracle s ==>
     BVLPROPSAUX_swap s1 (bvi_state_code_fupd (K c) s) = bvi_state_code_fupd (K c) s1`,
  SIMP[BVLPROPSAUX_swap_def; bvi_state_component_equality]);;

let BVLPROPSAUX_do_app_aux_swap = prove
 (`!op vs (s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state).
     (!v s1. bvi_do_app_aux op vs s = SOME (SOME (v,s1)) /\
             domain (bvi_state_code s) SUBSET domain (bvi_state_code t) ==>
             bvi_do_app_aux op vs (BVLPROPSAUX_swap s t) =
             SOME (SOME (v,BVLPROPSAUX_swap s1 t))) /\
     (bvi_do_app_aux op vs s = SOME NONE ==>
      bvi_do_app_aux op vs (BVLPROPSAUX_swap s t) = SOME NONE) /\
     (bvi_do_app_aux op vs s = NONE /\
      domain (bvi_state_code t) SUBSET domain (bvi_state_code s) ==>
      bvi_do_app_aux op vs (BVLPROPSAUX_swap s t) = NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_aux_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[BVLPROPSAUX_swap_acc] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[BVLPROPSAUX_swap_fupd] THEN ASM SET_TAC[]);;

(* local helpers for do_app_cfg_swap: apart from Install and the global    *)
(* operations (which bviSem's do_app_aux handles), BVL's do_app reads the  *)
(* state only through refs, ffi and the domain of code, and changes only     *)
(* refs and ffi                                                              *)
let BVLPROPSAUX_is_glob_def = new_definition
 `BVLPROPSAUX_is_glob op <=>
    (match op with GlobOp (g:glob_op) -> T | _ -> F)`;;

let BVLPROPSAUX_is_glob = prove
 (CASE_TERM `!op. BVLPROPSAUX_is_glob op <=> (?g. op = GlobOp g)`,
  REWRITE_TAC[BVLPROPSAUX_is_glob_def] THEN MATCH_MP_TAC clos_op_INDUCT THEN
  REWRITE_TAC[case_def "clos_op"; distinctness "clos_op"; injectivity "clos_op"] THEN
  MESON_TAC[]);;

let BVLPROPSAUX_bvl_do_app_frame = prove
 (`!op vs (s:(A,FFI)bvl_state) g c (cmp:B -> (num # num # bvl_exp) list ->
        (byte list # int64 list # B) option) orc cd.
     ~(op = clos_Install) /\ ~BVLPROPSAUX_is_glob op ==>
     (!v s'. bvl_do_app op vs s = Rval (v,s') /\
             domain (bvl_state_code s) SUBSET domain cd ==>
             bvl_do_app op vs
               (bvl_state_REC g (bvl_state_refs s) c cmp orc cd (bvl_state_ffi s)) =
             Rval (v,bvl_state_REC g (bvl_state_refs s') c cmp orc cd (bvl_state_ffi s'))) /\
     (!e. bvl_do_app op vs s = Rerr e /\
          (domain cd SUBSET domain (bvl_state_code s) \/ ~(e = Rabort Rtype_error)) ==>
          bvl_do_app op vs
            (bvl_state_REC g (bvl_state_refs s) c cmp orc cd (bvl_state_ffi s)) = Rerr e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_is_glob] THEN
  REWRITE_TAC[bvl_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accessors; bvl_state_INFO.ri_fupds;
              K_THM] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ;
              distinctness "clos_op"; injectivity "clos_op"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_accessors; K_THM] THEN
  ASM_MESON_TAC[SUBSET]);;

let BVLPROPSAUX_do_app_aux_SOME_NONE = prove
 (`!op vs (s:(A,FFI)bvi_state).
     bvi_do_app_aux op vs s = SOME NONE ==> ~BVLPROPSAUX_is_glob op`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_is_glob; bvi_do_app_aux_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; distinctness "clos_op";
              injectivity "clos_op"] THEN
  MESON_TAC[]);;

let BVLPROPSAUX_bvi_to_bvl_swap = prove
 (`!(s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state).
     bvi_to_bvl (BVLPROPSAUX_swap s t) =
     bvl_state_REC (bvl_state_globals (ARB:(B,FFI)bvl_state))
       (bvl_state_refs (bvi_to_bvl s)) (bvi_state_clock s)
       (bvl_state_compile (ARB:(B,FFI)bvl_state))
       (bvl_state_compile_oracle (ARB:(B,FFI)bvl_state))
       (sptree_map (K (ARB:num # bvl_exp)) (bvi_state_code t)) (bvl_state_ffi (bvi_to_bvl s))`,
  REWRITE_TAC[bvi_to_bvl_def; BVLPROPSAUX_swap_acc; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[bvl_state_component_equality; bvl_state_INFO.ri_accessors;
              bvl_state_INFO.ri_accfupds; K_THM]);;

let BVLPROPSAUX_bvl_to_bvi_swap = prove
 (`!(s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) (r:(A,FFI)bvl_state) g cmp orc cd.
     bvl_to_bvi (bvl_state_REC g (bvl_state_refs r) (bvi_state_clock s) cmp orc cd
                   (bvl_state_ffi r)) (BVLPROPSAUX_swap s t) =
     BVLPROPSAUX_swap (bvl_to_bvi r s) t <=>
     bvl_state_clock r = bvi_state_clock s`,
  REWRITE_TAC[bvl_to_bvi_def; BVLPROPSAUX_swap_def; bvl_state_INFO.ri_accessors;
              bvi_state_INFO.ri_accfupds; K_THM; bvi_state_INFO.ri_fupdfupds; K_o_THM;
              bvi_state_INFO.ri_fupdcanon] THEN
  REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM] THEN
  MESON_TAC[]);;

(* instantiate a universally quantified variable v of an assumption       *)
(* !.. v ... . A1 /\ .. /\ t = v /\ .. ==> C  with t (no bound variables) *)
let BVLPROPSAUX_UNWIND_RULE (th:thm) : thm =
  let vs,bod = strip_forall (concl th) in
  if not (is_imp bod) then th else
  let cs = conjuncts (lhand bod) in
  let pick = mapfilter (fun c ->
      let l,r = dest_eq c in
      if mem r vs && not (exists (fun v -> vfree_in v l) vs) then (r,l)
      else if mem l vs && not (exists (fun v -> vfree_in v r) vs) then (l,r)
      else failwith "pick") cs in
  match pick with
    [] -> th
  | (v,t)::_ ->
      let th1 = SPECL (map (fun u -> if u = v then t else u) vs) th in
      let th2 = REWRITE_RULE[] th1 in
      GENL (filter (fun u -> u <> v) vs) th2;;
(* BVLPROPSAUX_UNWIND_RULE repeated until nothing changes, and as a tactic *)
let rec BVLPROPSAUX_UNWIND_RULE_REP (th:thm) : thm =
  let th' = try BVLPROPSAUX_UNWIND_RULE th with Failure _ -> th in
  if concl th' = concl th then th else BVLPROPSAUX_UNWIND_RULE_REP th';;
let BVLPROPSAUX_UNWIND_REP_ASM_TAC : tactic =
  RULE_ASSUM_TAC(fun th -> try BVLPROPSAUX_UNWIND_RULE_REP th with Failure _ -> th);;

let BVLPROPSAUX_bvi_do_app_swap = prove
 (`!op args (s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state).
     ~(op = clos_Install) ==>
     (!value s1. bvi_do_app op args s = Rval (value,s1) /\
                 domain (bvi_state_code s) SUBSET domain (bvi_state_code t) ==>
                 bvi_do_app op args (BVLPROPSAUX_swap s t) =
                 Rval (value,BVLPROPSAUX_swap s1 t)) /\
     (!error. bvi_do_app op args s = Rerr error /\
              (domain (bvi_state_code t) SUBSET domain (bvi_state_code s) \/
               ~(error = Rabort Rtype_error)) ==>
              bvi_do_app op args (BVLPROPSAUX_swap s t) = Rerr error)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[bvi_do_app_def] THEN
  MP_TAC(ISPECL [`op:clos_op`; `args:bvl_v list`; `s:(A,FFI)bvi_state`;
                 `t:(B,FFI)bvi_state`] BVLPROPSAUX_do_app_aux_swap) THEN
  MP_TAC(ISPECL [`op:clos_op`; `args:bvl_v list`; `s:(A,FFI)bvi_state`]
                BVLPROPSAUX_do_app_aux_SOME_NONE) THEN
  MP_TAC(ISPEC `bvi_do_app_aux op args (s:(A,FFI)bvi_state)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC BVLPROPSAUX_bvi_clock_rws THENL
   [DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY (FIRST_ASSUM CONTR_TAC) THEN
    RES_TAC THEN ASM_REWRITE_TAC[case_def "option"];
    ALL_TAC] THEN
  MP_TAC(ISPEC `a:(bvl_v # (A,FFI)bvi_state)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `p:bvl_v # (A,FFI)bvi_state` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[case_def "option"; option_INJ; option_DISTINCT] THENL
   [ALL_TAC;
    MP_TAC(ISPEC `p:bvl_v # (A,FFI)bvi_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v0:bvl_v` (X_CHOOSE_THEN `u0:(A,FFI)bvi_state`
      SUBST_ALL_TAC)) THEN
    REWRITE_TAC[pair_CASE; PAIR_EQ; injectivity "result"; distinctness "result"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN BVLPROPSAUX_UNWIND_REP_ASM_TAC THEN RES_TAC THEN
    ASM_REWRITE_TAC[case_def "option"; pair_CASE]] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[case_def "option"; BVLPROPSAUX_bvi_to_bvl_swap] THEN
  MP_TAC(ISPECL [`op:clos_op`; `args:bvl_v list`; `bvi_to_bvl (s:(A,FFI)bvi_state)`;
     `bvl_state_globals (ARB:(B,FFI)bvl_state)`; `bvi_state_clock (s:(A,FFI)bvi_state)`;
     `bvl_state_compile (ARB:(B,FFI)bvl_state)`;
     `bvl_state_compile_oracle (ARB:(B,FFI)bvl_state)`;
     `sptree_map (K (ARB:num # bvl_exp)) (bvi_state_code (t:(B,FFI)bvi_state))`]
     BVLPROPSAUX_bvl_do_app_frame) THEN
  ASM_REWRITE_TAC[bvi_to_bvl_code; domain_map] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPEC `bvl_do_app op args (bvi_to_bvl (s:(A,FFI)bvi_state))` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `p:bvl_v # (A,FFI)bvl_state` ASSUME_TAC)
    (X_CHOOSE_THEN `e:(bvl_v)error_result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[case_def "result"] THENL
   [MP_TAC(ISPEC `p:bvl_v # (A,FFI)bvl_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1:bvl_v` (X_CHOOSE_THEN `r1:(A,FFI)bvl_state`
      SUBST_ALL_TAC)) THEN
    REWRITE_TAC[pair_CASE; PAIR_EQ; injectivity "result"; distinctness "result"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN RES_TAC THEN
    ASM_REWRITE_TAC[case_def "result"; pair_CASE; injectivity "result"; PAIR_EQ] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP bvl_do_app_const o check (fun th ->
      is_eq (concl th) &&
      lhs (concl th) = `bvl_do_app op args (bvi_to_bvl (s:(A,FFI)bvi_state))`)) THEN
    REWRITE_TAC[bvi_to_bvl_clock] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[BVLPROPSAUX_bvl_to_bvi_swap];
    CASES_ON `e:(bvl_v)error_result` THEN
    REWRITE_TAC[case_def "error_result"; injectivity "result"; distinctness "result";
                injectivity "error_result"; distinctness "error_result"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(fun fr -> let fc = concl fr in
      if is_forall fc && type_of (fst (dest_forall fc)) = `:(bvl_v)error_result`
      then MP_TAC fr else NO_TAC) THEN
    ASM_REWRITE_TAC[bvi_to_bvl_code; domain_map; injectivity "error_result";
                    distinctness "error_result"; RIGHT_FORALL_IMP_THM;
                    LEFT_FORALL_IMP_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "error_result"]) THEN
    REWRITE_TAC[injectivity "result"; IMP_CONJ; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2;
                injectivity "error_result"; distinctness "error_result"] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[case_def "result"; case_def "error_result"]]);;

(* HOL4 [local] *)
let do_app_cfg_swap = prove
 (`!op args (s:(A,FFI)bvi_state) value (s1:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) error.
     ~(op = clos_Install) ==>
     ((bvi_do_app op args s = Rval (value,s1) /\
       domain (bvi_state_code s) SUBSET domain (bvi_state_code t) ==>
       bvi_do_app op args
         (bvi_state_refs_fupd (K (bvi_state_refs s))
           (bvi_state_clock_fupd (K (bvi_state_clock s))
             (bvi_state_global_fupd (K (bvi_state_global s))
               (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) =
       Rval (value,
             bvi_state_refs_fupd (K (bvi_state_refs s1))
               (bvi_state_clock_fupd (K (bvi_state_clock s1))
                 (bvi_state_global_fupd (K (bvi_state_global s1))
                   (bvi_state_ffi_fupd (K (bvi_state_ffi s1)) t))))) /\
      (bvi_do_app op args s = Rerr error /\
       (domain (bvi_state_code t) SUBSET domain (bvi_state_code s) \/
        ~(error = Rabort Rtype_error)) ==>
       bvi_do_app op args
         (bvi_state_refs_fupd (K (bvi_state_refs s))
           (bvi_state_clock_fupd (K (bvi_state_clock s))
             (bvi_state_global_fupd (K (bvi_state_global s))
               (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) =
       Rerr error))`,
  REWRITE_TAC[GSYM BVLPROPSAUX_swap_def] THEN MESON_TAC[BVLPROPSAUX_bvi_do_app_swap]);;

let bvi_do_app_with_code = prove
 (`!op vs (s:(C,FFI)bvi_state) r s' c.
     bvi_do_app op vs s = Rval (r,s') ==>
     domain (bvi_state_code s) SUBSET domain c /\ ~(op = clos_Install) ==>
     bvi_do_app op vs (bvi_state_code_fupd (K c) s) =
     Rval (r,bvi_state_code_fupd (K c) s')`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["op"; "vs"; "s"; "r"; "s'"; "bvi_state_code_fupd (K c) s"; "ARB"] MP_TAC
    do_app_cfg_swap THEN
  REWRITE_TAC[GSYM BVLPROPSAUX_swap_def] THEN IMP_RES_TAC do_app_oracle THEN
  SIMP[BVLPROPSAUX_swap_code]);;

let bvi_do_app_with_code_err = prove
 (`!op vs (s:(C,FFI)bvi_state) e c.
     bvi_do_app op vs s = Rerr e ==>
     (domain c SUBSET domain (bvi_state_code s) \/ ~(e = Rabort Rtype_error)) /\
     ~(op = clos_Install) ==>
     bvi_do_app op vs (bvi_state_code_fupd (K c) s) = Rerr e`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["op"; "vs"; "s"; "ARB"; "s"; "bvi_state_code_fupd (K c) s"; "e"] MP_TAC
    do_app_cfg_swap THEN
  REWRITE_TAC[GSYM BVLPROPSAUX_swap_def] THEN SIMP[BVLPROPSAUX_swap_code]);;

let do_app_aux_with_clock = prove
 (CASE_TERM `!op vs (s:(C,FFI)bvi_state) c.
     bvi_do_app_aux op vs (bvi_state_clock_fupd (K c) s) =
     OPTION_MAP (OPTION_MAP (\p. match p with (x,y) -> (x,bvi_state_clock_fupd (K c) y)))
                (bvi_do_app_aux op vs s)`,
  REWRITE_TAC[BVLPROPSAUX_do_app_aux_clock]);;

let bvi_do_app_change_clock = prove
 (`!op args (s1:(C,FFI)bvi_state) res s2 ck.
     bvi_do_app op args s1 = Rval (res,s2) ==>
     bvi_do_app op args (bvi_state_clock_fupd (K ck) s1) =
     Rval (res,bvi_state_clock_fupd (K ck) s2)`,
  SIMP_TAC[BVLPROPSAUX_bvi_do_app_clock; map_result_def; pair_CASE]);;

let bvi_do_app_change_clock_err = prove
 (`!op vs (s:(C,FFI)bvi_state) e c.
     bvi_do_app op vs s = Rerr e ==>
     bvi_do_app op vs (bvi_state_clock_fupd (K c) s) = Rerr e`,
  SIMP_TAC[BVLPROPSAUX_bvi_do_app_clock; map_result_def; map_error_result_I; I_THM]);;

let bvi_evaluate_add_clock = prove
 (`!exps env (s1:(C,FFI)bvi_state) res s2.
     bvi_evaluate (exps,env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !ck. bvi_evaluate (exps,env,bvi_inc_clock ck s1) = (res,bvi_inc_clock ck s2)`,
  MESON_TAC[evaluate_inv_clock]);;

let do_app_aux_io_events_mono = prove
 (`!op vs (s:(C,FFI)bvi_state) x y.
     bvi_do_app_aux op vs s = SOME (SOME (x,y)) ==>
     ffi_state_io_events (bvi_state_ffi s) <<= ffi_state_io_events (bvi_state_ffi y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BVLPROPSAUX_do_app_aux_consts) THEN
  SIMP_TAC[IS_PREFIX_REFL]);;

let bvi_do_app_io_events_mono = prove
 (`!op vs (s1:(C,FFI)bvi_state) x s2.
     bvi_do_app op vs s1 = Rval (x,s2) ==>
     ffi_state_io_events (bvi_state_ffi s1) <<= ffi_state_io_events (bvi_state_ffi s2)`,
  RW[bvi_do_app_def] THEN GVS(all_case_eqs()) THEN
  IMP_RES_TAC bvl_do_app_io_events_mono THEN IMP_RES_TAC do_app_aux_io_events_mono THEN
  IMP_RES_TAC BVLPROPSAUX_bvi_do_install_code THEN FS[bvl_to_bvi_def; IS_PREFIX_REFL]);;

let bvi_evaluate_io_events_mono = prove
 (`!exps env (s1:(C,FFI)bvi_state) res s2.
     bvi_evaluate (exps,env,s1) = (res,s2) ==>
     ffi_state_io_events (bvi_state_ffi s1) <<= ffi_state_io_events (bvi_state_ffi s2)`,
  REC_IND_TAC bvi_evaluate_ind THEN REPEAT STRIP_TAC THEN BVLPROPSAUX_bvi_SPLIT_TAC THEN
  BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  IMP_RES_TAC bvi_do_app_io_events_mono THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_dec_clock_ffi; bvi_state_INFO.ri_accfupds]) THEN
  REWRITE_TAC[bvi_dec_clock_ffi; bvi_state_INFO.ri_accfupds] THEN BVLPROPSAUX_PREFIX_CHAIN_TAC);;

(* HOL4 [local] *)
let bvi_do_app_inc_clock = prove
 (CASE_TERM `!op vs x (y:(C,FFI)bvi_state).
     bvi_do_app op vs (bvi_inc_clock x y) =
     map_result (\p. match p with
                       (v,s) -> (v,bvi_state_clock_fupd (K (x + bvi_state_clock y)) s))
                I (bvi_do_app op vs y)`,
  REWRITE_TAC[bvi_inc_clock_def; BVLPROPSAUX_bvi_do_app_clock] THEN
  REWRITE_TAC[ADD_AC]);;

(* HOL4 [local] *)
let bvi_dec_clock_1_inc_clock = prove
 (`!x (s:(C,FFI)bvi_state).
     ~(x = 0) ==> bvi_dec_clock 1 (bvi_inc_clock x s) = bvi_inc_clock (x - 1) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_INFO.ri_accfupds; K_THM;
              bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 [local] *)
let bvi_dec_clock_1_inc_clock2 = prove
 (`!x (s:(C,FFI)bvi_state).
     ~(bvi_state_clock s = 0) ==>
     bvi_dec_clock 1 (bvi_inc_clock x s) = bvi_inc_clock x (bvi_dec_clock 1 s)`,
  REWRITE_TAC[dec_clock_inv_clock1]);;

(* HOL4 [local] *)
let bvi_dec_clock_inc_clock = prove
 (`!n x (s:(C,FFI)bvi_state).
     ~(bvi_state_clock s < n) ==>
     bvi_dec_clock n (bvi_inc_clock x s) = bvi_inc_clock x (bvi_dec_clock n s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_INFO.ri_accfupds; K_THM;
              bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 [simp] *)
let inc_clock_eq_0 = prove
 (`!extra (s:(C,FFI)bvi_state).
     bvi_state_clock (bvi_inc_clock extra s) = 0 <=>
     bvi_state_clock s = 0 /\ extra = 0`,
  REWRITE_TAC[bvi_inc_clock_clock; ADD_EQ_0]);;
let _ = cake_add_simps [inc_clock_eq_0];;

(* a run that times out has a prefix of the io_events of the same run with  *)
(* more clock *)
let BVLPROPSAUX_bvi_atc_TO = prove
 (`!exps env (s:(C,FFI)bvi_state) s1.
     bvi_evaluate (exps,env,s) = (Rerr (Rabort Rtimeout_error),s1) ==>
     !extra r2 s2.
       bvi_evaluate (exps,env,bvi_inc_clock extra s) = (r2,s2) ==>
       ffi_state_io_events (bvi_state_ffi s1) <<= ffi_state_io_events (bvi_state_ffi s2)`,
  (* split the run that times out; its runs that do not time out are the  *)
  (* same with more clock (evaluate_add_clock), which simplifies the run   *)
  (* with more clock; split that too; chain the prefixes                    *)
  REC_IND_TAC bvi_evaluate_ind THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "bvi_evaluate (_,_,bvi_inc_clock _ (_:(C,FFI)bvi_state)) = _"
    (MP_TAC o ONCE_REWRITE_RULE[bvi_evaluate_def]) THEN
  BVLPROPSAUX_bvi_EVAL_SPLIT_TAC
    "bvi_evaluate (_,_,(_:(C,FFI)bvi_state)) = (Rerr (Rabort Rtimeout_error),_)" THEN
  IMP_RES_TAC bvi_evaluate_add_clock THEN
  RULE_ASSUM_TAC(REWRITE_RULE BVLPROPSAUX_bvi_eval_simps) THEN
  SIMP[ARITH_ss; bvi_dec_clock_1_inc_clock2; bvi_dec_clock_inc_clock] THEN
  REWRITE_TAC BVLPROPSAUX_bvi_eval_case_eqs THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  BVLPROPSAUX_bvi_CLEAN_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  IMP_RES_TAC bvi_evaluate_io_events_mono THEN IMP_RES_TAC bvi_do_app_io_events_mono THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_dec_clock_ffi; bvi_inc_clock_ffi;
                              bvi_state_INFO.ri_accfupds]) THEN
  REWRITE_TAC[bvi_inc_clock_ffi; bvi_dec_clock_ffi; bvi_state_INFO.ri_accfupds] THEN
  BVLPROPSAUX_PREFIX_CHAIN_TAC);;

(* HOL4 leaves extra free *)
let bvi_evaluate_add_to_clock_io_events_mono = prove
 (`!exps env (s:(C,FFI)bvi_state) extra.
     ffi_state_io_events (bvi_state_ffi (SND (bvi_evaluate (exps,env,s)))) <<=
     ffi_state_io_events
       (bvi_state_ffi (SND (bvi_evaluate (exps,env,bvi_inc_clock extra s))))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `FST (bvi_evaluate (exps,env,s:(C,FFI)bvi_state)) = Rerr (Rabort Rtimeout_error)`
  THENL [ASM_MESON_TAC[BVLPROPSAUX_bvi_atc_TO; PAIR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`exps:bvi_exp list`; `env:bvl_v list`; `s:(C,FFI)bvi_state`;
                 `FST (bvi_evaluate (exps,env,s:(C,FFI)bvi_state))`;
                 `SND (bvi_evaluate (exps,env,s:(C,FFI)bvi_state))`] bvi_evaluate_add_clock) THEN
  ASM_SIMP_TAC[PAIR; bvi_inc_clock_ffi; IS_PREFIX_REFL]);;

(* HOL4 [local]; HOL4 leaves n free *)
let bvi_take_drop_lem = prove
 (`!skip (env:A list) n.
     skip < LENGTH env /\ skip + SUC n <= LENGTH env /\ ~(DROP skip env = []) ==>
     CONS (EL skip env) (TAKE n (DROP (1 + skip) env)) = TAKE (n + 1) (DROP skip env)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [MATCH_MP DROP_EL_CONS th]) THEN
  REWRITE_TAC[GSYM ADD1; TAKE] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD1]);;

let bvi_evaluate_genlist_vars = prove
 (`!skip env n (st:(C,FFI)bvi_state).
     n + skip <= LENGTH env ==>
     bvi_evaluate (list_of_seq (\arg. bvi_Var (arg + skip)) n,env,st) =
     (Rval (TAKE n (DROP skip env)),st)`,
  SUBGOAL_THEN
   `!n skip env (st:(C,FFI)bvi_state).
      n + skip <= LENGTH env ==>
      bvi_evaluate (list_of_seq (\arg. bvi_Var (arg + skip)) n,env,st) =
      (Rval (TAKE n (DROP skip env)),st)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[list_of_seq; bvi_evaluate_def; TAKE]; ALL_TAC] THEN
  REWRITE_TAC[GENLIST_CONS; o_DEF] THEN
  SUBGOAL_THEN `(\x. bvi_Var (SUC x + skip)) = (\arg. bvi_Var (arg + (skip + 1)))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  REWRITE_TAC[bvi_evaluate_def; ADD_CLAUSES] THEN
  SUBGOAL_THEN `skip < LENGTH (env:bvl_v list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[pair_CASE; case_def "result"; HD]] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`skip + 1`; `env:bvl_v list`;
                                         `st:(C,FFI)bvi_state`] th)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pair_CASE; case_def "result"; HD] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [MATCH_MP DROP_EL_CONS th]) THEN
  REWRITE_TAC[TAKE]);;

(* HOL4: get_code_labels; Termination wf_rel_tac with measure exp_size;     *)
(* final get_code_labels_def is the definition with MAP get_code_labels      *)
(* (the d of LetCall is named dest: one quotation types a variable once)     *)
let bvi_get_code_labels_def = cake_def_wf
  `MEASURE bvi_exp_size`
  TERM_TAC
  `(bvi_get_code_labels (bvi_Var _) = {}:num->bool) /\
   (bvi_get_code_labels (bvi_If e1 e2 e3) =
      (bvi_get_code_labels e1 UNION bvi_get_code_labels e2) UNION
      bvi_get_code_labels e3) /\
   (bvi_get_code_labels (bvi_Let es e) =
      UNIONS (set_of_list (MAP bvi_get_code_labels es)) UNION bvi_get_code_labels e) /\
   (bvi_get_code_labels (bvi_Raise e) = bvi_get_code_labels e) /\
   (bvi_get_code_labels (bvi_Tick e) = bvi_get_code_labels e) /\
   (bvi_get_code_labels (bvi_Force loc v) = {loc}) /\
   (bvi_get_code_labels (bvi_Call _ d es h) =
      ((match d with NONE -> {} | SOME n -> {n}) UNION
       (match h with NONE -> {} | SOME e -> bvi_get_code_labels e)) UNION
      UNIONS (set_of_list (MAP bvi_get_code_labels es))) /\
   (bvi_get_code_labels (bvi_Op op es) =
      assign_get_code_label op UNION
      UNIONS (set_of_list (MAP bvi_get_code_labels es))) /\
   (bvi_get_code_labels (bvi_Return es) =
      UNIONS (set_of_list (MAP bvi_get_code_labels es))) /\
   (bvi_get_code_labels (LetCall _ _ dest es y) =
      ({dest} UNION bvi_get_code_labels y) UNION
      UNIONS (set_of_list (MAP bvi_get_code_labels es)))`;;
let _ = cake_add_simps [bvi_get_code_labels_def];;

let bvi_get_code_labels_ind = cake_ind "bvi_get_code_labels";;

let bvi_good_code_labels_def = cake_def
  `bvi_good_code_labels (p:(num # num # bvi_exp) list) elabs <=>
     UNIONS (set_of_list (MAP (bvi_get_code_labels o SND o SND) p)) SUBSET
     set_of_list (MAP FST p) UNION elabs`;;

let adj_orac_def = cake_def
  `adj_orac (cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option)
            (f:A -> B) (s:(A,FFI)bvi_state) =
     bvi_state_REC (bvi_state_refs s) (bvi_state_clock s) (bvi_state_global s) cc
       ((f ## I) o bvi_state_compile_oracle s) (bvi_state_code s) (bvi_state_ffi s)`;;

let adj_orac_ok_def = cake_def
  `adj_orac_ok (cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option)
               (f:A -> B) (s:(A,FFI)bvi_state) <=>
     !n x y. bvi_state_compile_oracle s n = (x,y) ==>
       OPTION_MAP (I ## (I ## f)) (bvi_state_compile s x y) = cc (f x) y`;;

(* HOL4 [local] *)
let adj_orac_simps = prove
 (`!(cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option)
     (f:A -> B) (s:(A,FFI)bvi_state) n k.
     bvi_state_clock (adj_orac cc f s) = bvi_state_clock s /\
     bvi_state_code (adj_orac cc f s) = bvi_state_code s /\
     bvi_state_refs (adj_orac cc f s) = bvi_state_refs s /\
     bvi_state_global (adj_orac cc f s) = bvi_state_global s /\
     bvi_state_ffi (adj_orac cc f s) = bvi_state_ffi s /\
     bvi_dec_clock n (adj_orac cc f s) = adj_orac cc f (bvi_dec_clock n s) /\
     bvi_state_clock_fupd (K k) (adj_orac cc f s) =
     adj_orac cc f (bvi_state_clock_fupd (K k) s) /\
     (adj_orac_ok cc f (bvi_dec_clock n s) <=> adj_orac_ok cc f s) /\
     (adj_orac_ok cc f (bvi_state_clock_fupd (K k) s) <=> adj_orac_ok cc f s)`,
  REWRITE_TAC[adj_orac_def; adj_orac_ok_def; bvi_dec_clock_def;
              bvi_state_INFO.ri_accessors; bvi_state_INFO.ri_accfupds;
              bvi_state_INFO.ri_fupds; K_THM]);;

let bvi_adj_orac_rel_def = cake_def
  `bvi_adj_orac_rel
     (cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option)
     (f:A -> B) (s1:(A,FFI)bvi_state) (s2:(B,FFI)bvi_state) <=>
     adj_orac_ok cc f s1 /\ s2 = adj_orac cc f s1`;;

(* HOL4 [local] *)
let do_app_cfg_swap_Rval = prove
 (`!op args (s:(A,FFI)bvi_state) (s1:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) value.
     ~(op = clos_Install) /\ domain (bvi_state_code s) = domain (bvi_state_code t) /\
     bvi_do_app op args s = Rval (value,s1) ==>
     bvi_do_app op args
       (bvi_state_refs_fupd (K (bvi_state_refs s))
         (bvi_state_clock_fupd (K (bvi_state_clock s))
           (bvi_state_global_fupd (K (bvi_state_global s))
             (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) =
     Rval (value,
           bvi_state_refs_fupd (K (bvi_state_refs s1))
             (bvi_state_clock_fupd (K (bvi_state_clock s1))
               (bvi_state_global_fupd (K (bvi_state_global s1))
                 (bvi_state_ffi_fupd (K (bvi_state_ffi s1)) t))))`,
  MESON_TAC[do_app_cfg_swap; SUBSET_REFL]);;

(* HOL4 [local] *)
let do_app_cfg_swap_Rerr = prove
 (`!op args (s:(A,FFI)bvi_state) (t:(B,FFI)bvi_state) error.
     ~(op = clos_Install) /\ domain (bvi_state_code s) = domain (bvi_state_code t) /\
     bvi_do_app op args s = Rerr error ==>
     bvi_do_app op args
       (bvi_state_refs_fupd (K (bvi_state_refs s))
         (bvi_state_clock_fupd (K (bvi_state_clock s))
           (bvi_state_global_fupd (K (bvi_state_global s))
             (bvi_state_ffi_fupd (K (bvi_state_ffi s)) t)))) = Rerr error`,
  MESON_TAC[do_app_cfg_swap; SUBSET_REFL]);;

(* HOL4 [local] *)
let bvi_do_install_Rerr_type = prove
 (`!args (s:(C,FFI)bvi_state) (e:(E)error_result).
     bvi_do_install args s = Rerr e ==> e = Rabort Rtype_error`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"] THEN MESON_TAC[]);;

(* a local helper: the oracle of adj_orac after an Install *)
let BVLPROPSAUX_shift_seq_PAIR_MAP = prove
 (`!(f:A -> B) (co:num -> A # (num # num # bvi_exp) list) n.
     shift_seq n ((f ## I) o co) = (f ## I) o shift_seq n co`,
  REWRITE_TAC[shift_seq_def; FUN_EQ_THM; o_THM]);;

(* HOL4 [local] *)
let bvi_do_install_adj_orac = prove
 (`!args (s:(A,FFI)bvi_state) v (t:(A,FFI)bvi_state)
     (cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option) (f:A -> B).
     adj_orac_ok cc f s /\
     (bvi_do_install args s:(bvl_v # (A,FFI)bvi_state,exn_or_ret)result) = Rval (v,t) ==>
     (bvi_do_install args (adj_orac cc f s):(bvl_v # (B,FFI)bvi_state,exn_or_ret)result) =
       Rval (v,adj_orac cc f t) /\
     adj_orac_ok cc f t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `bvi_state_compile_oracle (s:(A,FFI)bvi_state) 0` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cfg:A` (X_CHOOSE_THEN `progs:(num # num # bvi_exp) list`
    ASSUME_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [bvi_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[adj_orac_ok_def]) THEN
  REWRITE_TAC[adj_orac_ok_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[shift_seq_def] THEN ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(fun ok -> FIRST_ASSUM(MP_TAC o MATCH_MP ok)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; PAIR_MAP_THM; I_THM] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[shift_seq_def; ADD_CLAUSES]) THEN
  REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF; adj_orac_def;
              bvi_state_INFO.ri_accessors; o_THM] THEN
  ASM_REWRITE_TAC[PAIR_MAP_THM; pair_CASE; I_THM; case_def "list"; case_def "option"] THEN
  REWRITE_TAC[BVLPROPSAUX_shift_seq_PAIR_MAP] THEN
  REWRITE_TAC[shift_seq_def; o_THM; ADD_CLAUSES; PAIR_MAP; FST] THEN
  ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; bvi_state_INFO.ri_fupds; K_THM]);;

(* HOL4 [local] *)
let do_app_adj_orac = prove
 (`!(cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option)
     (f:A -> B) (s:(A,FFI)bvi_state) op args.
     adj_orac_ok cc f s ==>
     (!v t. bvi_do_app op args s = Rval (v,t) ==>
            bvi_do_app op args (adj_orac cc f s) = Rval (v,adj_orac cc f t) /\
            adj_orac_ok cc f t) /\
     (!e. bvi_do_app op args s = Rerr e /\ ~(e = Rabort Rtype_error) ==>
          bvi_do_app op args (adj_orac cc f s) = Rerr e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [ASM_REWRITE_TAC[bvi_do_app_def] THEN
    ASM_MESON_TAC[bvi_do_install_adj_orac; bvi_do_install_Rerr_type];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [QSPECL_THEN ["op"; "args"; "s"; "t"; "adj_orac cc f s"; "v"] MP_TAC do_app_cfg_swap_Rval THEN
    IMP_RES_TAC do_app_code THEN IMP_RES_TAC do_app_oracle THEN
    FS[adj_orac_def; adj_orac_ok_def; bvi_state_component_equality] THEN ASM_REWRITE_TAC[];
    QSPECL_THEN ["op"; "args"; "s"; "adj_orac cc f s"; "e"] MP_TAC do_app_cfg_swap_Rerr THEN
    FS[adj_orac_def; bvi_state_component_equality]]);;

(* local helpers for bvi_evaluate_adj_orac: do_app_adj_orac in the         *)
(* implication forms used by IMP_RES_TAC                                     *)
let BVLPROPSAUX_do_app_adj_Rval = prove
 (`!(cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option)
     (f:A -> B) (s:(A,FFI)bvi_state) op args v t.
     adj_orac_ok cc f s /\ bvi_do_app op args s = Rval (v,t) ==>
     bvi_do_app op args (adj_orac cc f s) = Rval (v,adj_orac cc f t) /\
     adj_orac_ok cc f t`,
  MESON_TAC[do_app_adj_orac]);;

let BVLPROPSAUX_do_app_adj_Rerr = prove
 (`!(cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option)
     (f:A -> B) (s:(A,FFI)bvi_state) op args e.
     adj_orac_ok cc f s /\ bvi_do_app op args s = Rerr e /\
     ~(e = Rabort Rtype_error) ==>
     bvi_do_app op args (adj_orac cc f s) = Rerr e`,
  MESON_TAC[do_app_adj_orac]);;

(* resolution as BVLPROPSAUX_bvi_RES_TAC, simplifying after each step and   *)
(* counting alpha-equivalent facts as known                                  *)
let BVLPROPSAUX_bvi_RES3_TAC (simps:thm list) : tactic = fun (asl,w as gl) ->
  let asms = map (fun (_,th) ->
      let th = REWRITE_RULE[FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] th in
      try BVLPROPSAUX_UNWIND_RULE_REP th with Failure _ -> th) asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let imps = filter is_impth asms in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let simp th = curry (REWRITE_RULE simps th) in
  (* MATCH_MP th prepares th once for all the assumptions *)
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let mp = MATCH_MP th in
    let rs = mapfilter (fun a -> simp (mp a)) asms in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let results = flat (map (fun th -> resolve 8 (curry th)) imps) in
  let known th l = forall (fun c -> exists (fun a -> aconv (concl a) c) l)
                          (conjuncts (concl th)) in
  let rec dedup acc l = match l with
      [] -> rev acc
    | th::t -> if known th (asms @ acc) then dedup acc t else dedup (th::acc) t in
  match dedup [] results with
    [] -> failwith "BVLPROPSAUX_bvi_RES3_TAC"
  | ths -> EVERY (map CAKE_ASSUME_TAC ths) gl;;

(* HOL4 proves evaluate_adj_orac_rel (below) first, and this from it *)
let bvi_evaluate_adj_orac = prove
 (`!xs env (s:(A,FFI)bvi_state) res t1
     (cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option) (f:A -> B).
     bvi_evaluate (xs,env,s) = (res,t1) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     adj_orac_ok cc f s ==>
     bvi_evaluate (xs,env,adj_orac cc f s) = (res,adj_orac cc f t1) /\
     adj_orac_ok cc f t1`,
  REC_IND_TAC bvi_evaluate_ind THEN REPEAT STRIP_TAC THEN
  BVLPROPSAUX_bvi_EVAL_SPLIT_TAC "bvi_evaluate (_,_,(_:(A,FFI)bvi_state)) = _" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[adj_orac_simps]) THEN
  BVLPROPSAUX_bvi_RES_TAC THEN BVLPROPSAUX_bvi_CLEAN_TAC THEN BVLPROPSAUX_bvi_RES_TAC THEN
  IMP_RES_TAC BVLPROPSAUX_do_app_adj_Rval THEN IMP_RES_TAC BVLPROPSAUX_do_app_adj_Rerr THEN
  ONCE_REWRITE_TAC[bvi_evaluate_def] THEN SIMP[adj_orac_simps]);;

(* HOL4 [local] *)
let evaluate_adj_orac_rel = prove
 (`!xs env (s:(A,FFI)bvi_state) res t1
     (cc:B -> (num # num # bvi_exp) list -> (byte list # int64 list # B) option) (f:A -> B)
     (s2:(B,FFI)bvi_state).
     bvi_evaluate (xs,env,s) = (res,t1) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     bvi_adj_orac_rel cc f s s2 ==>
     ?t2. bvi_evaluate (xs,env,s2) = (res,t2) /\ bvi_adj_orac_rel cc f t1 t2`,
  REWRITE_TAC[bvi_adj_orac_rel_def] THEN MESON_TAC[bvi_evaluate_adj_orac]);;

(* HOL4 [local] *)
let adj_orac_initial_state = prove
 (`!(cc:C -> (num # num # bvi_exp) list -> (byte list # int64 list # C) option)
     (ffi:(FFI)ffi_state) code (co:num -> (S # C) # (num # num # bvi_exp) list) k.
     adj_orac cc SND (bvi_initial_state ffi code co (state_cc (CURRY I) cc) k) =
     bvi_initial_state ffi code (state_co (CURRY I) co) cc k`,
  RW[adj_orac_def; bvi_initial_state_def; bvi_state_component_equality; state_co_def;
     FUN_EQ_THM] THEN
  REPEAT TOP_CASE_TAC THEN SIMP[]);;

(* HOL4 [local] *)
let adj_orac_ok_initial_state = prove
 (`!(cc:C -> (num # num # bvi_exp) list -> (byte list # int64 list # C) option)
     (ffi:(FFI)ffi_state) code (co:num -> (S # C) # (num # num # bvi_exp) list) k.
     adj_orac_ok cc SND (bvi_initial_state ffi code co (state_cc (CURRY I) cc) k)`,
  RW[adj_orac_ok_def; bvi_initial_state_def; state_cc_def] THEN REPEAT TOP_CASE_TAC THEN SIMP[]);;

(* HOL4 [local] *)
let evaluate_CURRY_I = prove
 (`!es env (ffi:(FFI)ffi_state) code (co:num -> (S # C) # (num # num # bvi_exp) list)
     (cc:C -> (num # num # bvi_exp) list -> (byte list # int64 list # C) option) k r s.
     bvi_evaluate (es,env,bvi_initial_state ffi code co (state_cc (CURRY I) cc) k) =
     (r,s) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     ?s2. bvi_evaluate (es,env,bvi_initial_state ffi code (state_co (CURRY I) co) cc k) =
          (r,s2) /\ bvi_state_ffi s2 = bvi_state_ffi s`,
  REPEAT STRIP_TAC THEN
  QSPECL_THEN ["es"; "env"; "bvi_initial_state ffi code co (state_cc (CURRY I) cc) k"; "r"; "s";
               "cc"; "SND:S#C->C"] MP_TAC bvi_evaluate_adj_orac THEN
  ASM_REWRITE_TAC[adj_orac_ok_initial_state; adj_orac_initial_state] THEN STRIP_TAC THEN
  ASM_EXISTS_TAC THEN REWRITE_TAC[adj_orac_simps]);;

(* a local helper: an equation with a pair on the right, componentwise *)
let BVLPROPSAUX_PAIR_EQ_FST_SND = prove
 (`!(p:A#B) r s. p = (r,s) <=> FST p = r /\ SND p = s`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND]);;

(* HOL4 proves this by comparing the two semantics through lprefix_lub; *)
(* here evaluate_adj_orac shows that, for every clock, the second run   *)
(* gives the result of the first one and a state with the same ffi, so  *)
(* the two definitions agree term by term                                *)
let bvi_semantics_CURRY_I = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> (S # C) # (num # num # bvi_exp) list)
     (cc:C -> (num # num # bvi_exp) list -> (byte list # int64 list # C) option) start.
     ~(bvi_semantics ffi code co (state_cc (CURRY I) cc) start = Fail) ==>
     bvi_semantics ffi code co (state_cc (CURRY I) cc) start =
     bvi_semantics ffi code (state_co (CURRY I) co) cc start`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. ~(FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
            bvi_initial_state (ffi:(FFI)ffi_state) code
              (co:num -> (S # C) # (num # num # bvi_exp) list)
              (state_cc (CURRY I) (cc:C -> (num # num # bvi_exp) list ->
                                      (byte list # int64 list # C) option)) k)) =
          Rerr (Rabort Rtype_error))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `Rabort Rtype_error:(exn_or_ret)error_result`]) THEN
    ASM_REWRITE_TAC[injectivity "error_result"; distinctness "abort"];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
          bvi_initial_state (ffi:(FFI)ffi_state) code
            (state_co (CURRY I) (co:num -> (S # C) # (num # num # bvi_exp) list))
            (cc:C -> (num # num # bvi_exp) list -> (byte list # int64 list # C) option) k) =
        (FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
               bvi_initial_state ffi code co (state_cc (CURRY I) cc) k)),
         adj_orac cc SND (SND (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
               bvi_initial_state ffi code co (state_cc (CURRY I) cc) k))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`[bvi_Call 0 (SOME start) [] NONE]`; `[]:bvl_v list`;
      `bvi_initial_state (ffi:(FFI)ffi_state) code
         (co:num -> (S # C) # (num # num # bvi_exp) list)
         (state_cc (CURRY I) (cc:C -> (num # num # bvi_exp) list ->
                                 (byte list # int64 list # C) option)) k`;
      `FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
              bvi_initial_state (ffi:(FFI)ffi_state) code
                (co:num -> (S # C) # (num # num # bvi_exp) list)
                (state_cc (CURRY I) (cc:C -> (num # num # bvi_exp) list ->
                                        (byte list # int64 list # C) option)) k))`;
      `SND (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
              bvi_initial_state (ffi:(FFI)ffi_state) code
                (co:num -> (S # C) # (num # num # bvi_exp) list)
                (state_cc (CURRY I) (cc:C -> (num # num # bvi_exp) list ->
                                        (byte list # int64 list # C) option)) k))`;
      `cc:C -> (num # num # bvi_exp) list -> (byte list # int64 list # C) option`;
      `SND:S # C -> C`] bvi_evaluate_adj_orac) THEN
    ASM_REWRITE_TAC[adj_orac_ok_initial_state; adj_orac_initial_state; PAIR] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  ASM_REWRITE_TAC[FST; SND; adj_orac_simps; BVLPROPSAUX_PAIR_EQ_FST_SND] THEN
  CONV_TAC(DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[adj_orac_simps]);;
