(* ========================================================================= *)
(* bvlProps: port of HOL4 compiler/backend/semantics/bvlPropsScript.sml     *)
(* (CakeML v3479).  Properties about BVL and its semantics.                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r).  *)
(*   A HOL4 record update that changes the type of the ffi field            *)
(*   (t1 with ffi := s1.ffi, t1 and s1 of different types) is written with  *)
(*   the record constructor bvl_state_REC (do_app_Rval_swap,                 *)
(*   do_app_Rerr_swap): the kit's updates keep the type.                     *)
(* - HOL4 GENLIST f n is list_of_seq f n, FUNPOW is ITER, x <<= y is        *)
(*   isPREFIX x y (HOL4 x <<= y), BIGUNION is UNIONS, set is set_of_list.    *)
(* - BVLPROPSAUX_ names are local helpers (not HOL4 names).                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/rich_list.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;

type_invention_error := true;;

(* HOL4 [simp] *)
let with_same_code = prove
 (`!s:(C,FFI)bvl_state. bvl_state_code_fupd (combin_K (bvl_state_code s)) s = s`,
  SIMP[bvl_state_component_equality]);;
let _ = cake_add_simps [with_same_code];;

(* HOL4 [simp] *)
let bvl_with_same_clock = prove
 (`!st:(A,B)bvl_state. bvl_state_clock_fupd (combin_K (bvl_state_clock st)) st = st`,
  SIMP[bvl_state_component_equality]);;
let _ = cake_add_simps [bvl_with_same_clock];;

(* HOL4 [simp] *)
let bvl_dec_clock_with_code = prove
 (`!n c (s:(C,FFI)bvl_state).
     bvl_dec_clock n (bvl_state_code_fupd (combin_K c) s) =
     bvl_state_code_fupd (combin_K c) (bvl_dec_clock n s)`,
  SIMP[bvl_dec_clock_def; bvl_state_component_equality]);;
let _ = cake_add_simps [bvl_dec_clock_with_code];;

(* HOL4: case_eq_thms, the conjunction of bool_case_eq, pair_case_eq and   *)
(* the case equations of eq_result, const_part, word_size, result,        *)
(* error_result, v, ref, option, list, sum, op, mem_op, int_op, word_op,   *)
(* block_op, glob_op and ffi_result                                         *)
let bvlProps_case_eq_thms = end_itlist CONJ
  ([COND_CASE_EQ; pair_case_eq] @
   map case_eq ["eq_result"; "const_part"; "word_size"; "result"; "error_result";
                "bvl_v"; "bvl_ref"] @
   [option_case_eq; list_case_eq; sum_case_eq] @
   map case_eq ["clos_op"; "mem_op"; "int_op"; "word_op"; "block_op"; "glob_op";
                "ffi_result"]);;

(* HOL4 [local] *)
let bvl_do_app_split_list = prove
 (`!op vs (s:(C,FFI)bvl_state) res.
     bvl_do_app op vs s = res <=>
     vs = [] /\ bvl_do_app op [] s = res \/
     (?v vs1. vs = CONS v vs1 /\ bvl_do_app op (CONS v vs1) s = res)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `vs:bvl_v list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* HOL4 [local] *)
let bvl_pair_lam_lem = prove
 (CASE_TERM `!(f:A->B->C) v z. (let (x,y) = z in f x y) = v <=>
             ?x1 x2. z = (x1,x2) /\ f x1 x2 = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pair_case_eq] THEN MESON_TAC[]);;

(* HOL4: do_app_cases_val and do_app_cases_err are not ported: they are     *)
(* the results of an ML conversion (do_app_split_list, then SIMP_CONV with   *)
(* do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem and PULL_EXISTS),    *)
(* used nowhere in CakeML, and computing them with the kit's simplifier      *)
(* takes about 150 s.  BVLPROPSAUX_do_app_cases_CONV below computes the      *)
(* corresponding theorems on demand, applied to the terms                   *)
(* bvl_do_app op vs s = Rval (v,s') and bvl_do_app op vs s = Rerr err.       *)

let BVLPROPSAUX_do_app_cases_CONV =
  ONCE_REWRITE_CONV[bvl_do_app_split_list] THENC
  CAKE_SIMP_CONV ([bvl_do_app_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                   bvl_pair_lam_lem; LET_DEF; LET_END_DEF] @
                  CONJUNCTS bvlProps_case_eq_thms @
                  [case_eq "thunk_op"; case_eq "thunk_mode"]);;

(* The proofs of the do_app lemmas: one case split of do_app each, as in    *)
(* HOL4 (Cases_on op \\ gvs [do_app_def, AllCaseEqs()]).                     *)

(* HOL4: t1 with <| globals := s1.globals; refs := s1.refs;                  *)
(* clock := s1.clock; ffi := s1.ffi |> changes the ffi type of t1            *)
let do_app_Rval_swap = prove
 (`!op a (s1:(A,B)bvl_state) x0 x1 (t1:(C,D)bvl_state).
     bvl_do_app op a s1 = Rval (x0,x1) /\ ~(op = clos_Install) /\
     domain (bvl_state_code s1) SUBSET domain (bvl_state_code t1) ==>
     bvl_do_app op a
       (bvl_state_REC (bvl_state_globals s1) (bvl_state_refs s1) (bvl_state_clock s1)
          (bvl_state_compile t1) (bvl_state_compile_oracle t1) (bvl_state_code t1)
          (bvl_state_ffi s1)) =
     Rval (x0,bvl_state_REC (bvl_state_globals x1) (bvl_state_refs x1)
                (bvl_state_clock x1) (bvl_state_compile t1)
                (bvl_state_compile_oracle t1) (bvl_state_code t1) (bvl_state_ffi x1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accessors; bvl_state_INFO.ri_fupds;
              K_THM] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REWRITE_TAC[distinctness "clos_op"] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_accessors; K_THM] THEN
  ASM SET_TAC[]);;

let bvl_do_app_with_code = prove
 (`!op vs (s:(C,FFI)bvl_state) r s' c cc co.
     bvl_do_app op vs s = Rval (r,s') /\ ~(op = clos_Install) ==>
     domain (bvl_state_code s) SUBSET domain c ==>
     bvl_do_app op vs (bvl_state_code_fupd (combin_K c) (bvl_state_compile_fupd (combin_K cc)
                        (bvl_state_compile_oracle_fupd (combin_K co) s))) =
     Rval (r,bvl_state_code_fupd (combin_K c) (bvl_state_compile_fupd (combin_K cc)
               (bvl_state_compile_oracle_fupd (combin_K co) s')))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REWRITE_TAC[distinctness "clos_op"] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bvl_state_INFO.ri_fupdcanon; bvl_state_INFO.ri_fupdfupds; o_DEF; K_THM] THEN
  ASM SET_TAC[]);;

(* HOL4: the ffi type of t1 changes, as in do_app_Rval_swap *)
let do_app_Rerr_swap = prove
 (`!op a (s1:(A,B)bvl_state) e (t1:(C,D)bvl_state).
     bvl_do_app op a s1 = Rerr e /\ ~(op = clos_Install) /\
     domain (bvl_state_code t1) SUBSET domain (bvl_state_code s1) ==>
     bvl_do_app op a
       (bvl_state_REC (bvl_state_globals s1) (bvl_state_refs s1) (bvl_state_clock s1)
          (bvl_state_compile t1) (bvl_state_compile_oracle t1) (bvl_state_code t1)
          (bvl_state_ffi s1)) = Rerr e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accessors; bvl_state_INFO.ri_fupds;
              K_THM] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REWRITE_TAC[distinctness "clos_op"] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM SET_TAC[]);;

let do_app_with_code_err_not_Install = prove
 (`!op vs (s:(C,FFI)bvl_state) e c cc co.
     bvl_do_app op vs s = Rerr e /\ ~(op = clos_Install) ==>
     (domain c SUBSET domain (bvl_state_code s) \/ ~(e = Rabort Rtype_error)) ==>
     bvl_do_app op vs (bvl_state_code_fupd (combin_K c) (bvl_state_compile_fupd (combin_K cc)
                        (bvl_state_compile_oracle_fupd (combin_K co) s))) = Rerr e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REWRITE_TAC[distinctness "clos_op"] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM SET_TAC[]);;

let bvl_do_app_with_code_err = prove
 (`!op vs (s:(C,FFI)bvl_state) e c.
     bvl_do_app op vs s = Rerr e ==>
     (domain c = domain (bvl_state_code s) \/ ~(e = Rabort Rtype_error)) ==>
     bvl_do_app op vs (bvl_state_code_fupd (combin_K c) s) = Rerr e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_app_def; bvl_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 [simp] *)
let bvl_initial_state_simp = prove
 (`!(f:(FFI)ffi_state) c (co:num -> C # (num # num # bvl_exp) list) cc k.
     bvl_state_code (bvl_initial_state f c co cc k) = c /\
     bvl_state_ffi (bvl_initial_state f c co cc k) = f /\
     bvl_state_clock (bvl_initial_state f c co cc k) = k /\
     bvl_state_compile (bvl_initial_state f c co cc k) = cc /\
     bvl_state_compile_oracle (bvl_initial_state f c co cc k) = co /\
     bvl_state_refs (bvl_initial_state f c co cc k) = FEMPTY /\
     bvl_state_globals (bvl_initial_state f c co cc k) = []`,
  REWRITE_TAC[bvl_initial_state_def; bvl_state_INFO.ri_accessors]);;
let _ = cake_add_simps [bvl_initial_state_simp];;

(* HOL4 [simp] *)
let bvl_initial_state_with_simp = prove
 (`!(f:(FFI)ffi_state) c (co:num -> C # (num # num # bvl_exp) list) cc k k1 c1.
     bvl_state_clock_fupd (combin_K k1) (bvl_initial_state f c co cc k) =
     bvl_initial_state f c co cc k1 /\
     bvl_state_code_fupd (combin_K c1) (bvl_initial_state f c co cc k) =
     bvl_initial_state f c1 co cc k`,
  REWRITE_TAC[bvl_initial_state_def; bvl_state_INFO.ri_fupds; K_THM]);;
let _ = cake_add_simps [bvl_initial_state_with_simp];;

(* HOL4 [simp] *)
let bool_to_tag_11 = prove
 (`!b1 b2. bool_to_tag b1 = bool_to_tag b2 <=> b1 = b2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bool_to_tag_def; true_tag_def; false_tag_def] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN CONV_TAC NUM_REDUCE_CONV);;
let _ = cake_add_simps [bool_to_tag_11];;

(* HOL4 [simp] *)
let bvl_Boolv_11 = prove
 (`!b1 b2. bvl_Boolv b1 = bvl_Boolv b2 <=> b1 = b2`,
  REWRITE_TAC[bvl_Boolv_def; injectivity "bvl_v"; bool_to_tag_11]);;
let _ = cake_add_simps [bvl_Boolv_11];;

let find_code_EVERY_IMP = prove
 (`!dest a (r:(C,FFI)bvl_state) q t P.
     bvl_find_code dest a (bvl_state_code r) = SOME (q,t) ==>
     ALL P a ==> ALL P q`,
  REPEAT GEN_TAC THEN CASES_ON `dest:num option` THEN
  REWRITE_TAC[bvl_find_code_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[MEM_FRONT_NOT_NIL]);;

let bvl_do_app_err = prove
 (`!op vs (s:(C,FFI)bvl_state) e.
     bvl_do_app op vs s = Rerr e ==>
     e = Rabort Rtype_error \/
     (?i x. op = clos_FFI i /\ e = Rabort (Rffi_error x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def; bvl_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ;
              distinctness "clos_op"; injectivity "clos_op"] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers for proofs by induction on bvl_evaluate.                    *)
(* ------------------------------------------------------------------------- *)

(* bvl_evaluate_ind with the tuple split: MATCH_MP_TAC applies it to goals  *)
(* !xs env s. P xs env s                                                     *)
let BVLPROPSAUX_evaluate_ind =
  let p = `P:bvl_exp list -> bvl_v list -> (C,FFI)bvl_state -> bool` in
  let th = ISPEC
    `\t:bvl_exp list # bvl_v list # (C,FFI)bvl_state.
        (P:bvl_exp list -> bvl_v list -> (C,FFI)bvl_state -> bool)
        (FST t) (FST (SND t)) (SND (SND t))` bvl_evaluate_ind in
  let th = PURE_REWRITE_RULE[FST; SND] (CONV_RULE (DEPTH_CONV BETA_CONV) th) in
  let hy = lhand (concl th) in
  let goal = mk_imp(hy,
    `!xs env s. (P:bvl_exp list -> bvl_v list -> (C,FFI)bvl_state -> bool) xs env s`) in
  GEN p (prove(goal,
    DISCH_TAC THEN MP_TAC(MP th (ASSUME hy)) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND]));;

(* Local tactics: unfold the evaluate call of the last assumption once,     *)
(* split it with the case equations into the facts about the                 *)
(* sub-evaluations, and resolve the induction hypotheses with them.         *)

let BVLPROPSAUX_eval_case_eqs =
  [pair_case_eq; COND_CASE_EQ; option_case_eq; list_case_eq; case_eq "result";
   case_eq "error_result"; case_eq "bvl_dest_thunk_ret"; case_eq "thunk_mode";
   PAIR_EQ; injectivity "result"; distinctness "result"];;

let BVLPROPSAUX_both th = [th; ONCE_REWRITE_RULE[EQ_SYM_EQ] th];;

let BVLPROPSAUX_eval_simps =
  flat (map (fun s -> BVLPROPSAUX_both (distinctness s))
          ["result"; "option"; "list"; "error_result"; "abort";
           "bvl_dest_thunk_ret"; "thunk_mode"]) @
  map injectivity ["result"; "option"; "list"; "error_result"; "abort";
                   "bvl_dest_thunk_ret"] @ [PAIR_EQ];;

let BVLPROPSAUX_CLEAN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE BVLPROPSAUX_eval_simps) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN TRY RVEQ_TAC;;

let BVLPROPSAUX_SPLIT_TAC : tactic =
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REWRITE_TAC BVLPROPSAUX_eval_case_eqs THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN BVLPROPSAUX_CLEAN_TAC THEN
  BVLPROPSAUX_CLEAN_TAC;;

(* a local resolution tactic (HOL4 res_tac): every implicational assumption, *)
(* curried, is resolved with the other assumptions by MATCH_MP, as far as    *)
(* it goes                                                                    *)
let BVLPROPSAUX_RES_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let imps = filter is_impth asms in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let results =
    flat (map (fun th -> let th' = curry th in
                 flat (map (resolve 4) (mapfilter (fun a -> MATCH_MP th' a) asms)))
              imps) in
  let results = filter (fun th -> not (exists (fun a -> concl a = concl th) asms)) results in
  EVERY (map CAKE_ASSUME_TAC results) gl;;

let BVLPROPSAUX_evaluate_LENGTH_imp = prove
 (`!xs env (s:(C,FFI)bvl_state) res s1.
      bvl_evaluate (xs,env,s) = (Rval res,s1) ==> LENGTH xs = LENGTH res`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN BVLPROPSAUX_SPLIT_TAC THEN
  REWRITE_TAC[LENGTH] THEN BVLPROPSAUX_RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ONE]);;

(* a local helper: a match on (Rval res,s) with a T default *)
let BVLPROPSAUX_match_Rval = prove
 (CASE_TERM `!(p:(A,B)result # C) (P:A->bool).
     (match p with (Rval res,s1) -> P res | _ -> T) <=>
     (!res s1. p = (Rval res,s1) ==> P res)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  CASES_ON `p1:(A,B)result` THEN
  REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; injectivity "result";
              distinctness "result"] THEN MESON_TAC[]);;

(* HOL4: evaluate_LENGTH (the variable names are HOL4's) *)
let bvl_evaluate_LENGTH = prove
 (CASE_TERM `!xs (s:bvl_v list) (env:(C,FFI)bvl_state).
     match bvl_evaluate (xs,s,env) with
       (Rval res,s1) -> LENGTH xs = LENGTH res
     | _ -> T`,
  REWRITE_TAC[BVLPROPSAUX_match_Rval] THEN
  MESON_TAC[BVLPROPSAUX_evaluate_LENGTH_imp]);;

let bvl_evaluate_IMP_LENGTH = prove
 (`!xs (s:bvl_v list) (env:(C,FFI)bvl_state) res s1.
     bvl_evaluate (xs,s,env) = (Rval res,s1) ==> LENGTH xs = LENGTH res`,
  MESON_TAC[BVLPROPSAUX_evaluate_LENGTH_imp]);;

let bvl_evaluate_CONS = prove
 (CASE_TERM `!x xs env (s:(C,FFI)bvl_state).
     bvl_evaluate (CONS x xs,env,s) =
     match bvl_evaluate ([x],env,s) with
       (Rval v,s2) ->
         (match bvl_evaluate (xs,env,s2) with
            (Rval vs,s1) -> (Rval (CONS (HD v) vs),s1)
          | t -> t)
     | t -> t`,
  REPEAT GEN_TAC THEN CASES_ON `xs:bvl_exp list` THEN
  REWRITE_TAC[bvl_evaluate_def] THEN
  MP_TAC(ISPEC `bvl_evaluate ([x],env,s:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)bvl_state` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  REWRITE_TAC[pair_CASE] THEN
  CASES_ON `r:(bvl_v list,bvl_v)result` THEN REWRITE_TAC[case_def "result"] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HD]);;

(* a local helper: case-split a term of type result # state *)
let BVLPROPSAUX_PAIR_RESULT_TAC (tm:term) (rn:string) (sn:string) : tactic =
  fun (asl,w as gl) ->
    let rty,sty = (match dest_type (type_of tm) with
                     (_,[a;b]) -> a,b | _ -> failwith "PAIR_RESULT_TAC") in
    let r = mk_var(rn,rty) and s = mk_var(sn,sty) in
    (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s SUBST1_TAC)) THEN
     CASES_ON r THEN REWRITE_TAC[pair_CASE; case_def "result"]) gl;;

(* HOL4 proves evaluate_SNOC before evaluate_APPEND (by induction); here it *)
(* follows from evaluate_APPEND                                              *)
let bvl_evaluate_APPEND = prove
 (CASE_TERM `!xs env (s:(C,FFI)bvl_state) ys.
     bvl_evaluate (APPEND xs ys,env,s) =
     match bvl_evaluate (xs,env,s) with
       (Rval vs,s2) ->
         (match bvl_evaluate (ys,env,s2) with
            (Rval ws,s1) -> (Rval (APPEND vs ws),s1)
          | res -> res)
     | res -> res`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[APPEND; bvl_evaluate_def; pair_CASE; case_def "result"] THEN
    BVLPROPSAUX_PAIR_RESULT_TAC `bvl_evaluate (ys,env,s:(C,FFI)bvl_state)` "r" "s1" THEN
    REWRITE_TAC[APPEND];
    REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
    ASM_REWRITE_TAC[] THEN
    BVLPROPSAUX_PAIR_RESULT_TAC `bvl_evaluate ([h],env,s:(C,FFI)bvl_state)` "r" "s1" THEN
    BVLPROPSAUX_PAIR_RESULT_TAC `bvl_evaluate (t,env,s1:(C,FFI)bvl_state)` "r2" "s2" THEN
    BVLPROPSAUX_PAIR_RESULT_TAC `bvl_evaluate (ys,env,s2:(C,FFI)bvl_state)` "r3" "s3" THEN
    REWRITE_TAC[APPEND]]);;

let bvl_evaluate_SNOC = prove
 (CASE_TERM `!xs env (s:(C,FFI)bvl_state) x.
     bvl_evaluate (SNOC x xs,env,s) =
     match bvl_evaluate (xs,env,s) with
       (Rval vs,s2) ->
         (match bvl_evaluate ([x],env,s2) with
            (Rval v,s1) -> (Rval (APPEND vs v),s1)
          | t -> t)
     | t -> t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SNOC_APPEND; bvl_evaluate_APPEND]);;

let bvl_evaluate_SING = prove
 (`!x env (s:(C,FFI)bvl_state) a p1.
     bvl_evaluate ([x],env,s) = (Rval a,p1) ==> ?d1. a = [d1]`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP bvl_evaluate_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH] THEN DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL; ONE] THEN STRIP_TAC THEN
  EXISTS_TAC `h:bvl_v` THEN ASM_REWRITE_TAC[]);;

(* a local helper for evaluate_code: the oracle and code of a later state   *)
(* come from those of an earlier one by installing n programs              *)
let BVLPROPSAUX_code_inv_def = new_definition
 `BVLPROPSAUX_code_inv (co:num -> C # (num # num # bvl_exp) list)
                       (code:(num # bvl_exp) spt) co1 code1 <=>
    ?n. co1 = shift_seq n co /\
        code1 = FOLDL sptree_union code (MAP (fromAList o SND) (list_of_seq co n))`;;

let BVLPROPSAUX_code_inv_refl = prove
 (`!(co:num -> C # (num # num # bvl_exp) list) code.
     BVLPROPSAUX_code_inv co code co code`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_code_inv_def] THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[shift_seq_def; ADD_CLAUSES; ETA_AX; list_of_seq; MAP; FOLDL]);;

let BVLPROPSAUX_code_inv_trans = prove
 (`!(co:num -> C # (num # num # bvl_exp) list) code co1 code1 co2 code2.
     BVLPROPSAUX_code_inv co code co1 code1 /\
     BVLPROPSAUX_code_inv co1 code1 co2 code2 ==>
     BVLPROPSAUX_code_inv co code co2 code2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BVLPROPSAUX_code_inv_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `n2 + n1:num` THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REWRITE_TAC[GENLIST_APPEND; MAP_APPEND; FOLDL_APPEND] THEN
  REWRITE_TAC[shift_seq_def; FUN_EQ_THM; ADD_ASSOC]);;

(* a local helper: do_app with clos_Install is do_install *)
let BVLPROPSAUX_do_app_Install = prove
 (`!vs (s:(C,FFI)bvl_state).
     bvl_do_app clos_Install vs s = bvl_do_install vs s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[]);;

let BVLPROPSAUX_do_install_code = prove
 (`!vs (s:(C,FFI)bvl_state) v s'.
     bvl_do_install vs s = (Rval (v,s'):(bvl_v # (C,FFI)bvl_state,E)result) ==>
     BVLPROPSAUX_code_inv (bvl_state_compile_oracle s) (bvl_state_code s)
                          (bvl_state_compile_oracle s') (bvl_state_code s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_install_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; BVLPROPSAUX_code_inv_def] THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC[ONE; list_of_seq; APPEND; MAP; FOLDL; o_THM]);;

let BVLPROPSAUX_do_app_code = prove
 (`!op vs (s:(C,FFI)bvl_state) v s'.
     bvl_do_app op vs s = Rval (v,s') ==>
     BVLPROPSAUX_code_inv (bvl_state_compile_oracle s) (bvl_state_code s)
                          (bvl_state_compile_oracle s') (bvl_state_code s')`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `op = clos_Install` THENL
   [ASM_REWRITE_TAC[BVLPROPSAUX_do_app_Install; BVLPROPSAUX_do_install_code];
    DISCH_THEN(MP_TAC o MATCH_MP bvl_do_app_const) THEN
    ASM_SIMP_TAC[BVLPROPSAUX_code_inv_refl]]);;

let BVLPROPSAUX_evaluate_code_lemma = prove
 (`!xs env (s:(C,FFI)bvl_state) res s1.
      bvl_evaluate (xs,env,s) = (res,s1) ==>
      BVLPROPSAUX_code_inv (bvl_state_compile_oracle s) (bvl_state_code s)
                           (bvl_state_compile_oracle s1) (bvl_state_code s1)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN BVLPROPSAUX_SPLIT_TAC THEN
  BVLPROPSAUX_RES_TAC THEN
  IMP_RES_TAC BVLPROPSAUX_do_app_code THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
                  BVLPROPSAUX_code_inv_refl] THEN
  ASM_MESON_TAC[BVLPROPSAUX_code_inv_trans; BVLPROPSAUX_code_inv_refl]);;

let bvl_evaluate_code = prove
 (`!xs env (s1:(C,FFI)bvl_state) vs s2.
     bvl_evaluate (xs,env,s1) = (vs,s2) ==>
     ?n. bvl_state_compile_oracle s2 = shift_seq n (bvl_state_compile_oracle s1) /\
         bvl_state_code s2 =
         FOLDL sptree_union (bvl_state_code s1)
               (MAP (fromAList o SND) (list_of_seq (bvl_state_compile_oracle s1) n))`,
  REWRITE_TAC[GSYM BVLPROPSAUX_code_inv_def] THEN
  MESON_TAC[BVLPROPSAUX_evaluate_code_lemma]);;

let bvl_evaluate_mono = prove
 (`!xs env (s1:(C,FFI)bvl_state) vs s2.
     bvl_evaluate (xs,env,s1) = (vs,s2) ==>
     subspt (bvl_state_code s1) (bvl_state_code s2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP bvl_evaluate_code) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[subspt_FOLDL_union]);;

let evaluate_mk_tick = prove
 (`!exp env (s:(C,FFI)bvl_state) n.
     bvl_evaluate ([mk_tick n exp],env,s) =
     if bvl_state_clock s < n then
       (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (combin_K 0) s)
     else bvl_evaluate ([exp],env,bvl_dec_clock n s)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[mk_tick_def] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[ITER; LT; bvl_dec_clock_def; SUB_0] THEN
    SIMP[bvl_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ITER] THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
              bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  ASM_CASES_TAC `bvl_state_clock (s:(C,FFI)bvl_state) = 0` THEN
  ASM_REWRITE_TAC[LT_0; ARITH_RULE `0 < SUC n`] THENL
   [SIMP[bvl_state_component_equality]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(c = 0) ==> (c - 1 < n <=> c < SUC n)`;
               ARITH_RULE `c - 1 - n = c - SUC n`]);;

let evaluate_MAP_Const = prove
 (`!i env (t1:(C,FFI)bvl_state) (exps:A list).
     bvl_evaluate (MAP (combin_K (bvl_Op (IntOp (clos_Const i)) [])) exps,env,t1) =
     (Rval (MAP (combin_K (bvl_Number i)) exps),t1)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; bvl_evaluate_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN ASM_REWRITE_TAC[K_THM] THEN
  REWRITE_TAC[bvl_evaluate_def; bvl_do_app_def] THEN
  CAKE_REWRITE_TAC[REVERSE; bvl_do_int_app_def; HD] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[HD]);;

(* HOL4 [simp] *)
let bvl_evaluate_Bool = prove
 (`!b env (s:(C,FFI)bvl_state).
     bvl_evaluate ([bvl_Bool b],env,s) = (Rval [bvl_Boolv b],s)`,
  REWRITE_TAC[bvl_Bool_def; bvl_Boolv_def; bvl_evaluate_def; REVERSE;
              bvl_do_app_Cons] THEN
  CAKE_REWRITE_TAC[REVERSE]);;
let _ = cake_add_simps [bvl_evaluate_Bool];;

(* a local tactic for evaluate_expand_env: split the first evaluation of  *)
(* the original environment, condition or case variable, then simplify    *)
(* with the induction hypotheses (HOL4 split_tac)                         *)
let BVLPROPSAUX_EE_STEP_TAC : tactic = fun (asl,w as g) ->
  let env = mk_var("env",`:bvl_v list`) in
  let fw = frees w in
  let ok t = not (vfree_in env t) && subset (frees t) fw in
  let is_ev t = is_comb t && is_const (rator t) &&
                fst(dest_const(rator t)) = "bvl_evaluate" in
  match find_terms (fun t -> is_ev t && ok t) w with
    t::_ ->
      (CASES_ON t THEN
       (fun (asl,w as g) ->
          let eq = find (fun (_,th) -> let c = concl th in is_eq c && lhs c = t) asl in
          let r = lhand (rand (concl (snd eq))) in
          (CASES_ON r THEN FS[]) g)) g
  | [] ->
  match find_terms (fun t -> is_cond t && ok (fst(dest_cond t))) w with
    t::_ -> (ASM_CASES_TAC (fst(dest_cond t)) THEN FS[]) g
  | [] ->
  match find_terms (fun t -> is_case_app t &&
                       (let _,x,_ = dest_case_app t in is_var x && ok x)) w with
    t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN FS[]) g
  | [] -> failwith "BVLPROPSAUX_EE_STEP_TAC";;
let bvl_evaluate_expand_env = prove
 (`!xs a (s:(C,FFI)bvl_state) env.
     ~(FST (bvl_evaluate (xs,a,s)) = Rerr (Rabort Rtype_error)) ==>
     bvl_evaluate (xs,APPEND a env,s) = bvl_evaluate (xs,a,s)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (CHANGED_TAC BVLPROPSAUX_EE_STEP_TAC) THEN
  ASM_SIMP_TAC[EL_APPEND1; LENGTH_APPEND; ARITH_RULE `n < a ==> n < a + b:num`]);;

let bvl_inc_clock_def = cake_def
  `bvl_inc_clock ck (s:(C,FFI)bvl_state) =
     bvl_state_clock_fupd (combin_K (bvl_state_clock s + ck)) s`;;

(* HOL4 [simp] *)
let bvl_inc_clock_code = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_code (bvl_inc_clock n s) = bvl_state_code s`,
  REWRITE_TAC[bvl_inc_clock_def; bvl_state_INFO.ri_accfupds]);;

(* HOL4 [simp] *)
let bvl_inc_clock_refs = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_refs (bvl_inc_clock n s) = bvl_state_refs s`,
  REWRITE_TAC[bvl_inc_clock_def; bvl_state_INFO.ri_accfupds]);;

(* HOL4 [simp] *)
let bvl_inc_clock_ffi = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_ffi (bvl_inc_clock n s) = bvl_state_ffi s`,
  REWRITE_TAC[bvl_inc_clock_def; bvl_state_INFO.ri_accfupds]);;

(* HOL4 [simp] *)
let bvl_inc_clock_clock = prove
 (`!n (s:(C,FFI)bvl_state).
     bvl_state_clock (bvl_inc_clock n s) = bvl_state_clock s + n`,
  REWRITE_TAC[bvl_inc_clock_def; bvl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 [simp] *)
let inc_clock0 = prove
 (`!(n:num) (s:(C,FFI)bvl_state). bvl_inc_clock 0 s = s`,
  REWRITE_TAC[bvl_inc_clock_def; ADD_CLAUSES] THEN SIMP[bvl_state_component_equality]);;
let _ = cake_add_simps [bvl_inc_clock_code; bvl_inc_clock_refs; bvl_inc_clock_ffi;
                        bvl_inc_clock_clock; inc_clock0];;

let inc_clock_add = prove
 (`!k1 k2 (s:(C,FFI)bvl_state).
     bvl_inc_clock k1 (bvl_inc_clock k2 s) = bvl_inc_clock (k1 + k2) s`,
  REWRITE_TAC[bvl_inc_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
              bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  REWRITE_TAC[ADD_AC]);;

(* HOL4 [simp] *)
let bvl_dec_clock_code = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_code (bvl_dec_clock n s) = bvl_state_code s`,
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds]);;

(* HOL4 [simp] *)
let bvl_dec_clock_refs = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_refs (bvl_dec_clock n s) = bvl_state_refs s`,
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds]);;

(* HOL4 [simp] *)
let bvl_dec_clock_ffi = prove
 (`!n (s:(C,FFI)bvl_state). bvl_state_ffi (bvl_dec_clock n s) = bvl_state_ffi s`,
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds]);;

(* HOL4 [simp] *)
let bvl_dec_clock0 = prove
 (`!(n:num) (s:(C,FFI)bvl_state). bvl_dec_clock 0 s = s`,
  REWRITE_TAC[bvl_dec_clock_def; SUB_0] THEN SIMP[bvl_state_component_equality]);;
let _ = cake_add_simps [bvl_dec_clock_code; bvl_dec_clock_refs; bvl_dec_clock_ffi;
                        bvl_dec_clock0];;

(* a local helper: do_app copies the clock (HOL4 proves do_app_change_clock *)
(* and do_app_change_clock_err by case splits of do_app)                    *)
let BVLPROPSAUX_do_app_clock = prove
 (CASE_TERM `!op vs (s:(C,FFI)bvl_state) f.
     bvl_do_app op vs (bvl_state_clock_fupd f s) =
     map_result (\p. match p with (v,s1) -> (v,bvl_state_clock_fupd f s1)) I
                (bvl_do_app op vs s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def; bvl_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvl_state_INFO.ri_accfupds] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[map_result_def; map_error_result_I; I_THM; pair_CASE;
              bvl_state_INFO.ri_fupdcanon]);;

let bvl_do_app_change_clock = prove
 (`!op args (s1:(C,FFI)bvl_state) res s2 ck.
     bvl_do_app op args s1 = Rval (res,s2) ==>
     bvl_do_app op args (bvl_state_clock_fupd (combin_K ck) s1) =
     Rval (res,bvl_state_clock_fupd (combin_K ck) s2)`,
  SIMP_TAC[BVLPROPSAUX_do_app_clock; map_result_def; pair_CASE]);;

let bvl_do_app_change_clock_err = prove
 (`!op args (s1:(C,FFI)bvl_state) e ck.
     bvl_do_app op args s1 = Rerr e ==>
     bvl_do_app op args (bvl_state_clock_fupd (combin_K ck) s1) = Rerr e`,
  SIMP_TAC[BVLPROPSAUX_do_app_clock; map_result_def; map_error_result_I; I_THM]);;

(* ------------------------------------------------------------------------- *)
(* Local tactics for the inductions on evaluate that compare two runs.       *)
(* ------------------------------------------------------------------------- *)

let BVLPROPSAUX_is_ev t = is_comb t && is_const (rator t) &&
                fst(dest_const(rator t)) = "bvl_evaluate";;
let BVLPROPSAUX_has_const s t =
  can (find_term (fun u -> is_const u && fst(dest_const u) = s)) t;;

(* the subterms satisfying p that are not under a binder of one of their    *)
(* free variables, in left-to-right order                                    *)
let BVLPROPSAUX_free_terms p tm =
  let rec go bound t acc =
    let acc = if p t && not (exists (fun v -> mem v bound) (frees t))
              then t::acc else acc in
    match t with
      Comb(f,x) -> go bound x (go bound f acc)
    | Abs(v,b) -> go (v::bound) b acc
    | _ -> acc in
  rev (go [] tm []);;

(* a local tactic for the inductions on evaluate that compare two runs: it  *)
(* discharges a flat antecedent, or splits the first evaluate/do_app of the  *)
(* original run (no inc_clock), condition or case scrutinee, then simplifies *)
(* with the induction hypotheses and thl (HOL4 Cases_on ... \\ fs [])       *)
let BVLPROPSAUX_AC_STEP_TAC (thl:thm list) : tactic = fun (asl,w as g) ->
  let ok t = not (BVLPROPSAUX_has_const "bvl_inc_clock" t) in
  let is_do_app t = is_comb t && (let f,args = strip_comb t in
                     is_const f && fst(dest_const f) = "bvl_do_app" && length args = 3) in
  let flat t = not (can (find_term (fun u -> BVLPROPSAUX_is_ev u || is_do_app u ||
                                             is_cond u || is_case_app u)) t) in
  if is_imp w && flat (lhand w) then
    (DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ]) THEN RVEQ_TAC THEN FS thl) g
  else
  match BVLPROPSAUX_free_terms (fun t -> (BVLPROPSAUX_is_ev t || is_do_app t) && ok t) w with
    t::_ ->
      (CASES_ON t THEN
       (fun (asl,w as g) ->
          try let eq = find (fun (_,th) -> let c = concl th in is_eq c && lhs c = t) asl in
              let r = rand (concl (snd eq)) in
              let r = if is_pair r then fst(dest_pair r) else r in
              if is_var r then (CASES_ON r THEN FS thl) g else FS thl g
          with Failure _ -> FS thl g)) g
  | [] ->
  match BVLPROPSAUX_free_terms (fun t -> is_cond t && ok (fst(dest_cond t))) w with
    t::_ -> (ASM_CASES_TAC (fst(dest_cond t)) THEN FS thl) g
  | [] ->
  match BVLPROPSAUX_free_terms (fun t -> is_case_app t &&
                       (let _,x,_ = dest_case_app t in ok x)) w with
    t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN FS thl) g
  | [] -> failwith "BVLPROPSAUX_AC_STEP_TAC";;

let rec BVLPROPSAUX_UPTO_TAC n (tac:tactic) : tactic =
  if n = 0 then ALL_TAC else TRY (CHANGED_TAC tac THEN BVLPROPSAUX_UPTO_TAC (n-1) tac);;

(* a local resolution tactic: every implicational assumption, curried, is    *)
(* resolved with the other assumptions by MATCH_MP; an antecedent that no    *)
(* assumption matches is discharged when rewriting with thl and the          *)
(* assumptions proves it                                                     *)
let BVLPROPSAUX_RES2_TAC (thl:thm list) : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let discharge th =
    let th' = SPEC_ALL th in
    let ant = lhand (concl th') in
    let pth = EQT_ELIM (REWRITE_CONV (thl @ asms) ant) in
    MP th' pth in
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let rs = mapfilter (fun a -> curry (MATCH_MP th a)) asms in
    let rs = if rs <> [] then rs else
             (try [curry (discharge th)] with Failure _ -> []) in
    if rs = [] then [] else flat (map (resolve (depth-1)) rs) in
  let results =
    flat (map (fun th -> resolve 8 (curry th)) (filter is_impth asms)) in
  let results = filter (fun th -> not (is_impth th) &&
                          not (exists (fun a -> concl a = concl th) asms)) results in
  if results = [] then failwith "BVLPROPSAUX_RES2_TAC"
  else EVERY (map ASSUME_TAC results) g;;

(* a local closing tactic: the goal follows from the numeric comparisons    *)
(* among the assumptions                                                     *)
let BVLPROPSAUX_ARITH_CLOSE_TAC : tactic = fun (asl,w as g) ->
  let is_num_rel t =
    let t = if is_neg t then dest_neg t else t in
    (is_comb t && is_comb (rator t) &&
     (let f = rator (rator t) in
      is_const f && mem (fst(dest_const f)) ["<"; "<="] &&
      type_of (rand t) = `:num`)) ||
    (is_eq t && type_of (lhs t) = `:num`) in
  (REPEAT (FIRST_X_ASSUM (MP_TAC o check (is_num_rel o concl))) THEN ARITH_TAC) g;;

(* HOL4 [local]: do_app_inc_clock, dec_clock_1_inc_clock,                    *)
(* dec_clock_1_inc_clock2 and dec_clock_inc_clock come after                 *)
(* evaluate_io_events_mono in HOL4; here before evaluate_add_clock, whose    *)
(* proof uses them                                                           *)
let bvl_do_app_inc_clock = prove
 (CASE_TERM `!op vs x (y:(C,FFI)bvl_state).
     bvl_do_app op vs (bvl_inc_clock x y) =
     map_result (\p. match p with
                       (v,s) -> (v,bvl_state_clock_fupd (combin_K (x + bvl_state_clock y)) s))
                I (bvl_do_app op vs y)`,
  REWRITE_TAC[bvl_inc_clock_def; BVLPROPSAUX_do_app_clock] THEN
  REWRITE_TAC[ADD_AC]);;

let bvl_dec_clock_1_inc_clock = prove
 (`!x (s:(C,FFI)bvl_state).
     ~(x = 0) ==> bvl_dec_clock 1 (bvl_inc_clock x s) = bvl_inc_clock (x - 1) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_dec_clock_def; bvl_inc_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
              bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let bvl_dec_clock_1_inc_clock2 = prove
 (`!x (s:(C,FFI)bvl_state).
     ~(bvl_state_clock s = 0) ==>
     bvl_dec_clock 1 (bvl_inc_clock x s) = bvl_inc_clock x (bvl_dec_clock 1 s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_dec_clock_def; bvl_inc_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
              bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let bvl_dec_clock_inc_clock = prove
 (`!n x (s:(C,FFI)bvl_state).
     ~(bvl_state_clock s < n) ==>
     bvl_dec_clock n (bvl_inc_clock x s) = bvl_inc_clock x (bvl_dec_clock n s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_dec_clock_def; bvl_inc_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
              bvl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* a local helper: do_app keeps the clock, so inc_clock commutes with it *)
let BVLPROPSAUX_do_app_inc = prove
 (CASE_TERM `!op vs ck (s:(C,FFI)bvl_state).
     bvl_do_app op vs (bvl_inc_clock ck s) =
     map_result (\p. match p with (v,s1) -> (v,bvl_inc_clock ck s1)) I
                (bvl_do_app op vs s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_inc_clock] THEN
  MP_TAC(ISPECL [`op:clos_op`; `vs:bvl_v list`; `s:(C,FFI)bvl_state`]
                bvl_do_app_const) THEN
  CASES_ON `bvl_do_app op vs (s:(C,FFI)bvl_state)` THEN
  REWRITE_TAC[map_result_def] THEN
  CASES_ON `a:bvl_v#(C,FFI)bvl_state` THEN
  REWRITE_TAC[pair_CASE; injectivity "result"; PAIR_EQ; bvl_inc_clock_def] THEN
  MESON_TAC[ADD_SYM]);;

let BVLPROPSAUX_AC_thl =
  [BVLPROPSAUX_do_app_inc; bvl_dec_clock_1_inc_clock2; bvl_dec_clock_inc_clock;
   map_result_def; map_error_result_I; I_THM];;

(* the start of the proofs by induction on evaluate that compare a run with *)
(* another: the hypothesis on the first run, unfolded, becomes the          *)
(* antecedent of the goal                                                    *)
let BVLPROPSAUX_AC_START : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
     is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
     not (BVLPROPSAUX_has_const "bvl_inc_clock" c))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF];;

let bvl_evaluate_add_clock = prove
 (`!exps env (s1:(C,FFI)bvl_state) res s2.
     bvl_evaluate (exps,env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !ck. bvl_evaluate (exps,env,bvl_inc_clock ck s1) = (res,bvl_inc_clock ck s2)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  BVLPROPSAUX_AC_START THEN
  BVLPROPSAUX_UPTO_TAC 12 (BVLPROPSAUX_AC_STEP_TAC BVLPROPSAUX_AC_thl) THEN
  TRY (BVLPROPSAUX_RES2_TAC BVLPROPSAUX_eval_simps THEN FS BVLPROPSAUX_AC_thl) THEN
  TRY BVLPROPSAUX_ARITH_CLOSE_TAC);;

let bvl_evaluate_add_clock_initial_state = prove
 (`!es env (ffi:(FFI)ffi_state) code (co:num -> C # (num # num # bvl_exp) list)
      cc k r s'.
     bvl_evaluate (es,env,bvl_initial_state ffi code co cc k) = (r,s') /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !extra.
       bvl_evaluate (es,env,bvl_initial_state ffi code co cc (k + extra)) =
       (r,bvl_state_clock_fupd (combin_K (bvl_state_clock s' + extra)) s')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP bvl_evaluate_add_clock) THEN
  REWRITE_TAC[bvl_initial_state_def; bvl_inc_clock_def; bvl_state_INFO.ri_accessors;
              bvl_state_INFO.ri_fupds; K_THM]);;

let bvl_do_app_io_events_mono = prove
 (`!op vs (s1:(C,FFI)bvl_state) x s2.
     bvl_do_app op vs s1 = Rval (x,s2) ==>
     ffi_state_io_events (bvl_state_ffi s1) <<= ffi_state_io_events (bvl_state_ffi s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def; bvl_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[SEM2AUX_call_FFI_io_events]);;

let bvl_evaluate_io_events_mono = prove
 (`!exps env (s1:(C,FFI)bvl_state) res s2.
     bvl_evaluate (exps,env,s1) = (res,s2) ==>
     ffi_state_io_events (bvl_state_ffi s1) <<= ffi_state_io_events (bvl_state_ffi s2)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN BVLPROPSAUX_SPLIT_TAC THEN
  BVLPROPSAUX_RES_TAC THEN
  IMP_RES_TAC bvl_do_app_io_events_mono THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_dec_clock_ffi; bvl_state_INFO.ri_accfupds]) THEN
  ASM_REWRITE_TAC[IS_PREFIX_REFL; bvl_dec_clock_ffi; bvl_state_INFO.ri_accfupds] THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL]);;

(* local helpers for evaluate_add_to_clock_io_events_mono *)

let BVLPROPSAUX_add_clock_imp = prove
 (`!exps env (s1:(C,FFI)bvl_state) res s2.
     bvl_evaluate (exps,env,s1) = (res,s2) ==>
     ~(res = Rerr (Rabort Rtimeout_error)) ==>
     !ck. bvl_evaluate (exps,env,bvl_inc_clock ck s1) = (res,bvl_inc_clock ck s2)`,
  MESON_TAC[bvl_evaluate_add_clock]);;

(* split the first evaluate or do_app of the original run (no inc_clock)   *)
(* by its result, an error into timeout or not; for an evaluate that does  *)
(* not time out, add the run with more clock (evaluate_add_clock); split    *)
(* the runs with more clock by their result only; split conditions and     *)
(* case scrutinees; simplify with the induction hypotheses and thl         *)
let BVLPROPSAUX_TO_STEP_TAC (thl:thm list) : tactic = fun (asl,w as g) ->
  let inc t = BVLPROPSAUX_has_const "bvl_inc_clock" t in
  let is_do_app t = is_comb t && (let f,args = strip_comb t in
                     is_const f && fst(dest_const f) = "bvl_do_app" && length args = 3) in
  let flat t = not (can (find_term (fun u -> BVLPROPSAUX_is_ev u || is_do_app u ||
                                             is_cond u || is_case_app u)) t) in
  let eq_of t asl =
    snd (find (fun (_,th) -> let c = concl th in is_eq c && lhs c = t) asl) in
  let res_of th = let r = rand (concl th) in
                  if is_pair r then fst(dest_pair r) else r in
  let split base t : tactic =
    CASES_ON t THEN
    (fun (asl,w as g) ->
       let r = res_of (eq_of t asl) in
       if not (is_var r) then ALL_TAC g else
       (CASES_ON r THEN
        (if not base then ALL_TAC else
         TRY (fun (asl,w as g) ->
           let r = res_of (eq_of t asl) in
           let c,args = strip_comb r in
           if fst(dest_const c) <> "Rerr" then failwith "no err" else
           let e = hd args in
           let tm0 = `Rabort Rtimeout_error:(A)error_result` in
           let tm0 = inst (type_match (type_of tm0) (type_of e) []) tm0 in
           ASM_CASES_TAC (mk_eq(e,tm0)) g))) g) THEN
    (fun (asl,w as g) ->
       if not (base && BVLPROPSAUX_is_ev t) then ALL_TAC g else
       try let th1 = MATCH_MP BVLPROPSAUX_add_clock_imp (eq_of t asl) in
           let ant = lhand (concl th1) in
           let negs = filter (fun th -> is_neg (concl th)) (map snd asl) in
           let th2 = MP th1 (EQT_ELIM (REWRITE_CONV (BVLPROPSAUX_eval_simps @
                                                    negs) ant)) in
           ASSUME_TAC th2 g
       with Failure _ -> ALL_TAC g) THEN
    FS thl in
  if is_imp w && flat (lhand w) then
    (DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ]) THEN RVEQ_TAC THEN FS thl) g
  else
  match BVLPROPSAUX_free_terms (fun t -> is_cond t && not (inc (fst(dest_cond t)))) w with
    t::_ -> (ASM_CASES_TAC (fst(dest_cond t)) THEN FS thl) g
  | [] ->
  match BVLPROPSAUX_free_terms (fun t -> (BVLPROPSAUX_is_ev t || is_do_app t) &&
                                         not (inc t)) w with
    t::_ -> split true t g
  | [] ->
  match BVLPROPSAUX_free_terms (fun t -> is_case_app t &&
                       (let _,x,_ = dest_case_app t in not (inc x))) w with
    t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN FS thl) g
  | [] ->
  match BVLPROPSAUX_free_terms (fun t -> BVLPROPSAUX_is_ev t || is_do_app t) w with
    t::_ -> split false t g
  | [] ->
  match BVLPROPSAUX_free_terms is_cond w with
    t::_ -> (ASM_CASES_TAC (fst(dest_cond t)) THEN FS thl) g
  | [] ->
  match BVLPROPSAUX_free_terms is_case_app w with
    t::_ -> let _,x,_ = dest_case_app t in (CASES_ON x THEN FS thl) g
  | [] -> failwith "BVLPROPSAUX_TO_STEP_TAC";;

(* a local helper tactic: prove l <<= r from the isPREFIX assumptions by a  *)
(* chain of isPREFIX_TRANS steps (breadth-first search)                     *)
let BVLPROPSAUX_PREFIX_CHAIN_TAC : tactic = fun (asl,w as g) ->
  let is_pre t = try let f,args = strip_comb t in
                     is_const f && fst(dest_const f) = "isPREFIX" && length args = 2
                 with Failure _ -> false in
  if not (is_pre w) then failwith "BVLPROPSAUX_PREFIX_CHAIN_TAC" else
  let l,r = match snd(strip_comb w) with [a;b] -> a,b | _ -> failwith "chain" in
  if aconv l r then ACCEPT_TAC (ISPEC l IS_PREFIX_REFL) g else
  let facts = filter (fun th -> is_pre (concl th)) (map snd asl) in
  let edges = map (fun th -> match snd(strip_comb(concl th)) with
                               [a;b] -> a,(b,th) | _ -> failwith "chain") facts in
  let rec bfs frontier visited =
    match frontier with
      [] -> failwith "BVLPROPSAUX_PREFIX_CHAIN_TAC: no chain"
    | (t,th)::rest ->
        if aconv t r then th else
        let nexts = filter (fun (a,(b,_)) -> aconv a t &&
                                not (exists (aconv b) visited)) edges in
        let new_items = map (fun (_,(b,th2)) ->
                               b, MATCH_MP isPREFIX_TRANS (CONJ th th2)) nexts in
        bfs (rest @ new_items) (map fst new_items @ visited) in
  let start = filter (fun (a,_) -> aconv a l) edges in
  let init = map (fun (_,(b,th)) -> b,th) start in
  ACCEPT_TAC (bfs init (l :: map fst init)) g;;

let BVLPROPSAUX_ATC_thl =
  [BVLPROPSAUX_do_app_inc; bvl_dec_clock_1_inc_clock2; bvl_dec_clock_inc_clock;
   map_result_def; map_error_result_I; I_THM; bvl_inc_clock_ffi; bvl_dec_clock_ffi;
   bvl_state_INFO.ri_accfupds; K_THM];;

let BVLPROPSAUX_io_mono_imp = prove
 (`!exps env (s1:(C,FFI)bvl_state) res s2.
     bvl_evaluate (exps,env,s1) = (res,s2) ==>
     ffi_state_io_events (bvl_state_ffi s1) <<= ffi_state_io_events (bvl_state_ffi s2)`,
  REWRITE_TAC[bvl_evaluate_io_events_mono]);;

(* close a leaf: instantiate the induction hypotheses (antecedents matched *)
(* by assumptions, as far as they go) and the io_events_mono facts of       *)
(* evaluate and do_app with the facts of the runs, then chain the prefixes  *)
let BVLPROPSAUX_TO_CLOSE_TAC : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let is_pre t = try let f,args = strip_comb t in
                     is_const f && fst(dest_const f) = "isPREFIX" && length args = 2
                 with Failure _ -> false in
  let is_do_app t = is_comb t && (let f,args = strip_comb t in
                     is_const f && fst(dest_const f) = "bvl_do_app" && length args = 3) in
  let facts = filter (fun th -> let c = concl th in
                        is_eq c && (BVLPROPSAUX_is_ev (lhs c) || is_do_app (lhs c))) asms in
  let monos = mapfilter (fun th -> MATCH_MP BVLPROPSAUX_io_mono_imp th) facts @
              mapfilter (fun th -> MATCH_MP bvl_do_app_io_events_mono th) facts in
  let is_impth th = is_imp (snd (strip_forall (concl th))) in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let rec resolve depth th =
    if not (is_impth th) then [th] else
    if depth = 0 then [] else
    let rs = mapfilter (fun a -> curry (MATCH_MP th a)) asms in
    flat (map (resolve (depth-1)) rs) in
  let inst = flat (map (fun ih -> resolve 8 (curry ih)) (filter is_impth asms)) in
  let pre = filter (fun th -> is_pre (concl th)) (monos @ inst) in
  let rw = [bvl_inc_clock_ffi; bvl_dec_clock_ffi; bvl_state_INFO.ri_accfupds] in
  (MAP_EVERY (ASSUME_TAC o REWRITE_RULE rw) pre THEN
   REWRITE_TAC rw THEN BVLPROPSAUX_PREFIX_CHAIN_TAC) g;;

(* a local closing tactic: the numeric comparisons among the assumptions    *)
(* are contradictory                                                         *)
let BVLPROPSAUX_ARITH_CONTR_TAC : tactic =
  SUBGOAL_THEN `F` CONTR_TAC THEN BVLPROPSAUX_ARITH_CLOSE_TAC;;

(* the start of the induction: both runs, unfolded once, become the         *)
(* antecedents of the goal                                                   *)
let BVLPROPSAUX_TO_START : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
     is_eq c && BVLPROPSAUX_is_ev (lhs c) && BVLPROPSAUX_has_const "bvl_inc_clock" c)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
     is_eq c && BVLPROPSAUX_is_ev (lhs c) &&
     not (BVLPROPSAUX_has_const "bvl_inc_clock" c))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF];;

(* a run that times out has a prefix of the io_events of the same run with  *)
(* more clock                                                                *)
let BVLPROPSAUX_atc_TO = prove
 (`!exps env (s:(C,FFI)bvl_state) s1.
     bvl_evaluate (exps,env,s) = (Rerr (Rabort Rtimeout_error),s1) ==>
     !extra r2 s2.
       bvl_evaluate (exps,env,bvl_inc_clock extra s) = (r2,s2) ==>
       ffi_state_io_events (bvl_state_ffi s1) <<= ffi_state_io_events (bvl_state_ffi s2)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  BVLPROPSAUX_TO_START THEN
  BVLPROPSAUX_UPTO_TAC 16 (BVLPROPSAUX_TO_STEP_TAC BVLPROPSAUX_ATC_thl) THEN
  TRY BVLPROPSAUX_TO_CLOSE_TAC THEN TRY BVLPROPSAUX_ARITH_CONTR_TAC);;

(* HOL4 leaves extra free *)
let bvl_evaluate_add_to_clock_io_events_mono = prove
 (`!exps env (s:(C,FFI)bvl_state) extra.
     ffi_state_io_events (bvl_state_ffi (SND (bvl_evaluate (exps,env,s)))) <<=
     ffi_state_io_events
       (bvl_state_ffi (SND (bvl_evaluate (exps,env,bvl_inc_clock extra s))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `bvl_evaluate (exps,env,s:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `bvl_evaluate (exps,env,bvl_inc_clock extra (s:(C,FFI)bvl_state))`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SND] THEN
  ASM_CASES_TAC `r1 = Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[BVLPROPSAUX_atc_TO];
    MP_TAC(ISPECL [`exps:bvl_exp list`; `env:bvl_v list`; `s:(C,FFI)bvl_state`;
                   `r1:(bvl_v list,bvl_v)result`; `s1:(C,FFI)bvl_state`]
                  bvl_evaluate_add_clock) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `extra:num`) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[bvl_inc_clock_ffi; IS_PREFIX_REFL]]);;

(* HOL4 [local]; HOL4 leaves n free *)
let bvl_take_drop_lem = prove
 (`!skip (env:A list) n.
     skip < LENGTH env /\ skip + SUC n <= LENGTH env /\ ~(DROP skip env = []) ==>
     CONS (EL skip env) (TAKE n (DROP (1 + skip) env)) = TAKE (n + 1) (DROP skip env)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [MATCH_MP DROP_EL_CONS th]) THEN
  REWRITE_TAC[GSYM ADD1; TAKE] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD1]);;

let bvl_evaluate_genlist_vars = prove
 (`!skip env n (st:(C,FFI)bvl_state).
     n + skip <= LENGTH env ==>
     bvl_evaluate (list_of_seq (\arg. bvl_Var (arg + skip)) n,env,st) =
     (Rval (TAKE n (DROP skip env)),st)`,
  SUBGOAL_THEN
   `!n skip env (st:(C,FFI)bvl_state).
      n + skip <= LENGTH env ==>
      bvl_evaluate (list_of_seq (\arg. bvl_Var (arg + skip)) n,env,st) =
      (Rval (TAKE n (DROP skip env)),st)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[list_of_seq; bvl_evaluate_def; TAKE]; ALL_TAC] THEN
  REWRITE_TAC[GENLIST_CONS; o_DEF] THEN
  SUBGOAL_THEN `(\x. bvl_Var (SUC x + skip)) = (\arg. bvl_Var (arg + (skip + 1)))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  REWRITE_TAC[bvl_evaluate_def; ADD_CLAUSES] THEN
  SUBGOAL_THEN `skip < LENGTH (env:bvl_v list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[pair_CASE; case_def "result"; HD]] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`skip + 1`; `env:bvl_v list`;
                                         `st:(C,FFI)bvl_state`] th)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pair_CASE; case_def "result"; HD] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [MATCH_MP DROP_EL_CONS th]) THEN
  REWRITE_TAC[TAKE]);;

let evaluate_var_reverse = prove
 (`!xs env ys (st:(C,FFI)bvl_state).
     bvl_evaluate (MAP bvl_Var xs,env,st) = (Rval ys,st) ==>
     bvl_evaluate (REVERSE (MAP bvl_Var xs),env,st) = (Rval (REVERSE ys),st)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; REVERSE; bvl_evaluate_def; PAIR_EQ; injectivity "result"] THENL
   [MESON_TAC[REVERSE]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN REWRITE_TAC[bvl_evaluate_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; distinctness "result"] THEN
  MP_TAC(ISPEC `bvl_evaluate (MAP bvl_Var t,env,st:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvl_state` MP_TAC)) THEN
  STRUCT_CASES_TAC(ISPEC `r:(bvl_v list,bvl_v)result` (cases "result")) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[pair_CASE; case_def "result"; PAIR_EQ; injectivity "result";
              distinctness "result"; HD] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`env:bvl_v list`; `a:bvl_v list`;
                                `st:(C,FFI)bvl_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[bvl_evaluate_APPEND; pair_CASE; case_def "result"] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def; pair_CASE; case_def "result"; REVERSE]);;

let evaluate_genlist_vars_rev = prove
 (`!skip env n (st:(C,FFI)bvl_state).
     n + skip <= LENGTH env ==>
     bvl_evaluate (REVERSE (list_of_seq (\arg. bvl_Var (arg + skip)) n),env,st) =
     (Rval (REVERSE (TAKE n (DROP skip env))),st)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `st:(C,FFI)bvl_state` o MATCH_MP bvl_evaluate_genlist_vars) THEN
  SUBGOAL_THEN `list_of_seq (\arg. bvl_Var (arg + skip)) n =
                MAP bvl_Var (list_of_seq (\arg. arg + skip) n)` SUBST1_TAC THENL
   [REWRITE_TAC[MAP_GENLIST; o_DEF]; ALL_TAC] THEN
  MATCH_ACCEPT_TAC evaluate_var_reverse);;

(* a local helper: do_part only adds references *)
let BVLPROPSAUX_do_part_SUBSET = prove
 (`!m p (refs:(num,(bvl_v)bvl_ref)fmap) x refs1.
     bvl_do_part m p refs = (x,refs1) ==> FDOM refs SUBSET FDOM refs1`,
  GEN_TAC THEN MATCH_MP_TAC const_part_INDUCT THEN
  REWRITE_TAC[bvl_do_part_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SUBSET_REFL; FDOM_FUPDATE] THEN SET_TAC[]);;

(* HOL4 [local] *)
let do_build_SUBSET = prove
 (`!m n parts (refs:(num,(bvl_v)bvl_ref)fmap) q rs.
     bvl_do_build m n parts refs = (q,rs) ==> FDOM refs SUBSET FDOM rs`,
  SUBGOAL_THEN
   `!parts m n (refs:(num,(bvl_v)bvl_ref)fmap) q rs.
      bvl_do_build m n parts refs = (q,rs) ==> FDOM refs SUBSET FDOM rs`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_build_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPEC `bvl_do_part m h (refs:(num,(bvl_v)bvl_ref)fmap)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:bvl_v` (X_CHOOSE_THEN `refs1:(num,(bvl_v)bvl_ref)fmap`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BVLPROPSAUX_do_part_SUBSET) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  DISCH_THEN(fun ih -> FIRST_X_ASSUM(MP_TAC o MATCH_MP ih)) THEN
  ASM SET_TAC[]);;

let bvl_do_app_refs_SUBSET = prove
 (`!op a (r:(C,FFI)bvl_state) q t.
     bvl_do_app op a r = Rval (q,t) ==>
     FDOM (bvl_state_refs r) SUBSET FDOM (bvl_state_refs t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def; bvl_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM; SUBSET_REFL; FDOM_FUPDATE] THEN
  TRY (SET_TAC[]) THEN
  ASM_MESON_TAC[do_build_SUBSET; bvl_do_build_const_def]);;

(* a local helper: evaluate_refs_SUBSET_lemma in implication form *)
let BVLPROPSAUX_refs_SUBSET = prove
 (`!xs env (s:(C,FFI)bvl_state) res t.
     bvl_evaluate (xs,env,s) = (res,t) ==>
     FDOM (bvl_state_refs s) SUBSET FDOM (bvl_state_refs t)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN BVLPROPSAUX_SPLIT_TAC THEN
  BVLPROPSAUX_RES_TAC THEN
  IMP_RES_TAC bvl_do_app_refs_SUBSET THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_dec_clock_refs; bvl_state_INFO.ri_accfupds]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; bvl_dec_clock_refs; bvl_state_INFO.ri_accfupds] THEN
  ASM_MESON_TAC[SUBSET_TRANS; SUBSET_REFL]);;

(* HOL4 [local] *)
let evaluate_refs_SUBSET_lemma = prove
 (`!xs env (s:(C,FFI)bvl_state).
     FDOM (bvl_state_refs s) SUBSET
     FDOM (bvl_state_refs (SND (bvl_evaluate (xs,env,s))))`,
  MESON_TAC[BVLPROPSAUX_refs_SUBSET; PAIR; SND]);;

let bvl_evaluate_refs_SUBSET = prove
 (`!xs env (s:(C,FFI)bvl_state) res t.
     bvl_evaluate (xs,env,s) = (res,t) ==>
     FDOM (bvl_state_refs s) SUBSET FDOM (bvl_state_refs t)`,
  MESON_TAC[evaluate_refs_SUBSET_lemma; SND]);;

let bvl_get_vars_def = cake_def
  `(bvl_get_vars [] (env:A list) = SOME []) /\
   (bvl_get_vars (CONS n ns) env =
      if n < LENGTH env then
        (match bvl_get_vars ns env with
           NONE -> NONE
         | SOME vs -> SOME (CONS (EL n env) vs))
      else NONE)`;;

let isVar_def = cake_def
  `(isVar (bvl_Var n) <=> T) /\ (isVar _ <=> F)`;;

let destVar_def = cake_def
  `destVar (bvl_Var n) = n`;;

let evaluate_Var_list = prove
 (`!l env (s:(C,FFI)bvl_state).
     ALL isVar l ==>
     bvl_evaluate (l,env,s) = (Rerr (Rabort Rtype_error),s) \/
     ?vs. bvl_evaluate (l,env,s) = (Rval vs,s) /\
          bvl_get_vars (MAP destVar l) env = SOME vs /\
          LENGTH vs = LENGTH l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; MAP; bvl_evaluate_def; bvl_get_vars_def; LENGTH] THENL
   [GEN_TAC THEN DISJ2_TAC THEN EXISTS_TAC `[]:bvl_v list` THEN REWRITE_TAC[LENGTH];
    ALL_TAC] THEN
  CASES_ON `h:bvl_exp` THEN REWRITE_TAC[isVar_def; destVar_def] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  REWRITE_TAC[bvl_evaluate_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`env:bvl_v list`; `s:(C,FFI)bvl_state`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; case_def "result"; case_def "option"; HD; LENGTH;
                  PAIR_EQ; injectivity "result"; distinctness "result";
                  injectivity "option"] THEN
  ASM_MESON_TAC[LENGTH]);;

(* HOL4 [simp]; Termination WF_REL_TAC `measure (exp1_size o SND)` *)
let bVarBound_def = cake_def_wf
  `MEASURE (list_size bvl_exp_size o (SND:num # bvl_exp list -> bvl_exp list))`
  (REWRITE_TAC[measure_THM; o_THM] THEN TERM_TAC)
  `(bVarBound n [] <=> T) /\
   (bVarBound n (CONS (x:bvl_exp) (CONS y xs)) <=>
      bVarBound n [x] /\ bVarBound n (CONS y xs)) /\
   (bVarBound n [bvl_Var v] <=> v < n) /\
   (bVarBound n [bvl_If x1 x2 x3] <=>
      bVarBound n [x1] /\ bVarBound n [x2] /\ bVarBound n [x3]) /\
   (bVarBound n [bvl_Let xs x2] <=>
      bVarBound n xs /\ bVarBound (n + LENGTH xs) [x2]) /\
   (bVarBound n [bvl_Raise x1] <=> bVarBound n [x1]) /\
   (bVarBound n [bvl_Tick x1] <=> bVarBound n [x1]) /\
   (bVarBound n [bvl_Op op xs] <=> bVarBound n xs) /\
   (bVarBound n [bvl_Force loc v] <=> v < n) /\
   (bVarBound n [bvl_Handle x1 x2] <=>
      bVarBound n [x1] /\ bVarBound (n + 1) [x2]) /\
   (bVarBound n [bvl_Call ticks dest xs] <=> bVarBound n xs)`;;
let _ = cake_add_simps [bVarBound_def];;

let bVarBound_ind = cake_ind "bVarBound";;

(* HOL4 [simp]; Termination WF_REL_TAC `measure (exp1_size o SND)` *)
let bEvery_def = cake_def_wf
  `MEASURE (list_size bvl_exp_size o
            (SND:(bvl_exp->bool) # bvl_exp list -> bvl_exp list))`
  (REWRITE_TAC[measure_THM; o_THM] THEN TERM_TAC)
  `(bEvery P [] <=> T) /\
   (bEvery P (CONS (x:bvl_exp) (CONS y xs)) <=>
      bEvery P [x] /\ bEvery P (CONS y xs)) /\
   (bEvery P [bvl_Var v] <=> P (bvl_Var v)) /\
   (bEvery P [bvl_If x1 x2 x3] <=> P (bvl_If x1 x2 x3) /\
      bEvery P [x1] /\ bEvery P [x2] /\ bEvery P [x3]) /\
   (bEvery P [bvl_Let xs x2] <=> P (bvl_Let xs x2) /\
      bEvery P xs /\ bEvery P [x2]) /\
   (bEvery P [bvl_Raise x1] <=> P (bvl_Raise x1) /\ bEvery P [x1]) /\
   (bEvery P [bvl_Tick x1] <=> P (bvl_Tick x1) /\ bEvery P [x1]) /\
   (bEvery P [bvl_Force m n] <=> P (bvl_Force m n)) /\
   (bEvery P [bvl_Op op xs] <=> P (bvl_Op op xs) /\ bEvery P xs) /\
   (bEvery P [bvl_Handle x1 x2] <=> P (bvl_Handle x1 x2) /\
      bEvery P [x1] /\ bEvery P [x2]) /\
   (bEvery P [bvl_Call ticks dest xs] <=> P (bvl_Call ticks dest xs) /\ bEvery P xs)`;;
let _ = cake_add_simps [bEvery_def];;

let bEvery_ind = cake_ind "bEvery";;

let bVarBound_EVERY = prove
 (`!ls (P:num). bVarBound P ls <=> ALL (\e. bVarBound P [e]) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bVarBound_def; ALL] THEN
  GEN_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[bVarBound_def; ALL] THEN SIMP_TAC[]);;

let bEvery_EVERY = prove
 (`!ls (P:bvl_exp->bool). bEvery P ls <=> ALL (\e. bEvery P [e]) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[bEvery_def; ALL] THEN
  GEN_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `t:bvl_exp list` list_CASES) THEN
  REWRITE_TAC[bEvery_def; ALL] THEN SIMP_TAC[]);;

(* HOL4: get_code_labels; Termination wf_rel_tac `measure exp_size`; HOL4's  *)
(* final get_code_labels_def is the definition with MAP get_code_labels      *)
let bvl_get_code_labels_def = cake_def_wf
  `MEASURE bvl_exp_size`
  TERM_TAC
  `(bvl_get_code_labels (bvl_Var _) = {}:num->bool) /\
   (bvl_get_code_labels (bvl_If e1 e2 e3) =
      (bvl_get_code_labels e1 UNION bvl_get_code_labels e2) UNION
      bvl_get_code_labels e3) /\
   (bvl_get_code_labels (bvl_Let es e) =
      UNIONS (set_of_list (MAP bvl_get_code_labels es)) UNION bvl_get_code_labels e) /\
   (bvl_get_code_labels (bvl_Raise e) = bvl_get_code_labels e) /\
   (bvl_get_code_labels (bvl_Handle e1 e2) =
      bvl_get_code_labels e1 UNION bvl_get_code_labels e2) /\
   (bvl_get_code_labels (bvl_Tick e) = bvl_get_code_labels e) /\
   (bvl_get_code_labels (bvl_Force loc v) = {loc}) /\
   (bvl_get_code_labels (bvl_Call _ d es) =
      (match d with NONE -> {} | SOME n -> {n}) UNION
      UNIONS (set_of_list (MAP bvl_get_code_labels es))) /\
   (bvl_get_code_labels (bvl_Op op es) =
      assign_get_code_label op UNION
      UNIONS (set_of_list (MAP bvl_get_code_labels es)))`;;
let _ = cake_add_simps [bvl_get_code_labels_def];;

let bvl_get_code_labels_ind = cake_ind "bvl_get_code_labels";;

(* HOL4 [simp] *)
let mk_tick_code_labels = prove
 (`!n x. bvl_get_code_labels (mk_tick n x) = bvl_get_code_labels x`,
  REWRITE_TAC[mk_tick_def] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITER; bvl_get_code_labels_def]);;
let _ = cake_add_simps [mk_tick_code_labels];;
