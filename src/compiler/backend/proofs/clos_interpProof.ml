(* ========================================================================= *)
(* clos_interpProof: port of HOL4 compiler/backend/proofs/                   *)
(* clos_interpProofScript.sml (CakeML v3479).                                *)
(* Correctness proof for the closLang interpreter used by the REPL, i.e.    *)
(* Install, to avoid spending time compiling simple run-once code in        *)
(* declarations.                                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;

type_invention_error := true;;

(* CLOSP2AUX_ names are local helpers. *)

(* ------------------------------------------------------------------------- *)
(* correctness of interpreter                                                *)
(* ------------------------------------------------------------------------- *)

(* HOL4: state_rel_def *)
let clos_interpProof_state_rel_def = cake_def
  `clos_interpProof_state_rel (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_max_app t = clos_state_max_app s /\ 1 <= clos_state_max_app s /\
     clos_state_clock t = clos_state_clock s /\
     clos_state_ffi t = clos_state_ffi s /\
     clos_state_globals s = clos_state_globals t /\
     clos_state_refs s = clos_state_refs t /\
     clos_state_compile s = pure_cc (insert_interp ## I) (clos_state_compile t) /\
     clos_state_compile_oracle t =
       pure_co (insert_interp ## I) o clos_state_compile_oracle s /\
     oHD (clos_state_globals s) = SOME (SOME (clos_Closure NONE [] [] 1 clos_interpreter))`;;

(* HOL4: state_rel_1_def *)
let state_rel_1_def = cake_def
  `state_rel_1 (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_max_app t = clos_state_max_app s /\ 1 <= clos_state_max_app s /\
     clos_state_clock t = clos_state_clock s /\
     clos_state_ffi t = clos_state_ffi s /\
     clos_state_globals s = clos_state_globals t /\
     clos_state_refs s = clos_state_refs t /\
     clos_state_compile s = pure_cc (insert_interp ## I) (clos_state_compile t) /\
     clos_state_compile_oracle t =
       pure_co (insert_interp ## I) o clos_state_compile_oracle s`;;

(* HOL4: LIST_REL_eq' [local] *)
let LIST_REL_eq' = prove
 (`!(xs:A list) (ys:A list). ALL2 (\(v1:A) v2. v1 = v2) = (\xs ys. xs = ys)`,
  REWRITE_TAC[ETA_AX; LIST_REL_eq]);;

(* HOL4: OPTREL_eq' [local] *)
let OPTREL_eq' = prove
 (`OPTREL (\(v1:A) v2. v1 = v2) = (\x y. x = y)`,
  REWRITE_TAC[ETA_AX; OPTREL_eq]);;

(* local helpers for do_app_oHD_globals: the updates of the globals *)
let CLOSP2AUX_ip_oHD_LUPDATE = prove
 (`!(l:(clos_v option)list) n w x.
     oHD l = SOME (SOME x) /\ get_global n l = SOME NONE ==>
     oHD (LUPDATE (SOME w) n l) = SOME (SOME x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[oHD_DEF; distinctness "option"] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[get_global_def; LUPDATE_DEF; oHD_DEF; LENGTH; EL; HD; LT_0; NOT_SUC;
              injectivity "option"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[oHD_DEF]);;

let CLOSP2AUX_ip_oHD_APPEND = prove
 (`!(l:(clos_v option)list) m x. oHD l = SOME (SOME x) ==> oHD (APPEND l m) = SOME (SOME x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[oHD_DEF; APPEND; distinctness "option"]);;

(* HOL4: do_app_oHD_globals *)
let do_app_oHD_globals = prove
 (`clos_do_app p vs (s1:(C,FFI)clos_state) = Rval (v,s2) ==>
   oHD (clos_state_globals s1) = SOME (SOME x) ==>
   oHD (clos_state_globals s2) = SOME (SOME x)`,
  REWRITE_TAC[clos_do_app_def] THEN REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; LET_DEF; LET_END_DEF; injectivity "result";
              distinctness "result"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  TRY(MATCH_MP_TAC CLOSP2AUX_ip_oHD_LUPDATE THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MATCH_MP_TAC CLOSP2AUX_ip_oHD_APPEND THEN ASM_REWRITE_TAC[]);;

(* HOL4: interp_assum_def; interp_assum (:'c) (:'ffi) takes the types as    *)
(* arguments: here the arguments are universes (:C) and (:FFI), as in       *)
(* bvl_constProof; the definition is interp_assum_DEF and the HOL4          *)
(* statement interp_assum_def                                               *)
let interp_assum_DEF = cake_def
  `interp_assum (cc:C->bool) (ff:FFI->bool) c <=>
     (!xs s1 env (t1:(C,FFI)clos_state) res s2.
        clos_state_clock s1 <= c /\
        clos_evaluate (xs,env,s1) = (res,s2) /\
        ~(res = Rerr (Rabort Rtype_error)) ==>
        clos_interpProof_state_rel s1 t1 ==>
        ?ck t2.
          clos_evaluate (xs,env,clos_state_clock_fupd (K (ck + clos_state_clock t1)) t1) =
          (res,t2) /\
          clos_interpProof_state_rel s2 t2) /\
     (!args s1 loc f (t1:(C,FFI)clos_state) res s2.
        clos_state_clock s1 <= c /\
        evaluate_app loc f args s1 = (res,s2) /\
        ~(res = Rerr (Rabort Rtype_error)) ==>
        clos_interpProof_state_rel s1 t1 ==>
        ?ck t2.
          evaluate_app loc f args (clos_state_clock_fupd (K (ck + clos_state_clock t1)) t1) =
          (res,t2) /\
          clos_interpProof_state_rel s2 t2)`;;

let interp_assum_def = prove
 (`!c. interp_assum (:C) (:FFI) c <=>
     (!xs s1 env (t1:(C,FFI)clos_state) res s2.
        clos_state_clock s1 <= c /\
        clos_evaluate (xs,env,s1) = (res,s2) /\
        ~(res = Rerr (Rabort Rtype_error)) ==>
        clos_interpProof_state_rel s1 t1 ==>
        ?ck t2.
          clos_evaluate (xs,env,clos_state_clock_fupd (K (ck + clos_state_clock t1)) t1) =
          (res,t2) /\
          clos_interpProof_state_rel s2 t2) /\
     (!args s1 loc f (t1:(C,FFI)clos_state) res s2.
        clos_state_clock s1 <= c /\
        evaluate_app loc f args s1 = (res,s2) /\
        ~(res = Rerr (Rabort Rtype_error)) ==>
        clos_interpProof_state_rel s1 t1 ==>
        ?ck t2.
          evaluate_app loc f args (clos_state_clock_fupd (K (ck + clos_state_clock t1)) t1) =
          (res,t2) /\
          clos_interpProof_state_rel s2 t2)`,
  REWRITE_TAC[interp_assum_DEF]);;

(* HOL4: interp_assum_leq *)
let interp_assum_leq = prove
 (`interp_assum (:C) (:FFI) c /\ d <= c ==> interp_assum (:C) (:FFI) d`,
  REWRITE_TAC[interp_assum_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] th)) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS]);;

(* HOL4: evaluate_Constant [simp,local] *)
let evaluate_Constant = prove
 (`clos_evaluate ([clos_Op t (BlockOp (Constant c)) []],env,s) =
   (Rval [make_const c],s:(C,FFI)clos_state)`,
  REWRITE_TAC[clos_evaluate_def; distinctness "clos_op"; REVERSE] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4: evaluate_Cons_nil *)
let evaluate_Cons_nil = prove
 (`clos_evaluate ([clos_Op t (BlockOp (clos_Cons n)) []],env,s) =
   (Rval [clos_Block n []],s:(C,FFI)clos_state)`,
  REWRITE_TAC[clos_evaluate_def; distinctness "clos_op"; REVERSE] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4: evaluate_Global_0 *)
let evaluate_Global_0 = prove
 (`clos_interpProof_state_rel s t ==>
   clos_evaluate ([clos_Op tr (GlobOp (clos_Global 0)) []],env,
                  clos_state_clock_fupd (K k) t) =
   (Rval [clos_Closure NONE [] [] 1 clos_interpreter],
    clos_state_clock_fupd (K k) (t:(C,FFI)clos_state))`,
  REWRITE_TAC[clos_interpProof_state_rel_def] THEN STRIP_TAC THEN
  REWRITE_TAC[clos_evaluate_def; distinctness "clos_op"; REVERSE] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; get_global_def] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `clos_state_globals (s:(C,FFI)clos_state)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "oHD" with Failure _ -> false))
      (lhs (concl th)))) THEN
  SPEC_TAC(`clos_state_globals (t:(C,FFI)clos_state)`, `g:(clos_v option)list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[oHD_DEF; distinctness "option"; injectivity "option"; LENGTH; LT_0; EL; HD] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

(* HOL4: v_to_list_list_to_v *)
let v_to_list_list_to_v = prove
 (`!a. clos_v_to_list (clos_list_to_v a) = SOME a`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_list_to_v_def; clos_v_to_list_def] THEN
  CASE_REWRITE_TAC[]);;

(* local helpers: the symbolic evaluation of the interpreter (HOL4: ntac k  *)
(* simp [Once evaluate_def, do_app_def, dest_closure_def, check_loc_def,    *)
(* dec_clock_def, ...])                                                     *)
let CLOSP2AUX_ip_do_app = prove
 (CASE_TERM `(!(s:(C,FFI)clos_state) n tag xs.
      clos_do_app (BlockOp (ElemAt n)) [clos_Block tag xs] s =
      if n < LENGTH xs then Rval (EL n xs, s) else Rerr (Rabort Rtype_error)) /\
   (!(s:(C,FFI)clos_state) n l tag xs.
      clos_do_app (BlockOp (clos_TagLenEq n l)) [clos_Block tag xs] s =
      Rval (clos_Boolv (tag = n /\ LENGTH xs = l), s)) /\
   (!(s:(C,FFI)clos_state) l tag xs.
      clos_do_app (BlockOp (clos_LenEq l)) [clos_Block tag xs] s =
      Rval (clos_Boolv (LENGTH xs = l), s)) /\
   (!(s:(C,FFI)clos_state) tag xs.
      clos_do_app (BlockOp (clos_Cons tag)) xs s = Rval (clos_Block tag xs, s)) /\
   (!(s:(C,FFI)clos_state) c.
      clos_do_app (BlockOp (Constant c)) [] s = Rval (make_const c, s)) /\
   (!(s:(C,FFI)clos_state) i j.
      clos_do_app (BlockOp (EqualConst (clos_Int i))) [clos_Number j] s =
      Rval (clos_Boolv (i = j), s)) /\
   (!(s:(C,FFI)clos_state) i.
      clos_do_app (IntOp (clos_Const i)) [] s = Rval (clos_Number i, s)) /\
   (!(s:(C,FFI)clos_state) i j.
      clos_do_app (IntOp clos_Sub) [clos_Number i; clos_Number j] s =
      Rval (clos_Number (i - j), s)) /\
   (!(s:(C,FFI)clos_state) x1 x2.
      clos_do_app (BlockOp clos_ListAppend) [x1; x2] s =
      (match (clos_v_to_list x1, clos_v_to_list x2) with
         (SOME xs, SOME ys) -> Rval (clos_list_to_v (APPEND xs ys), s)
       | _ -> Rerr (Rabort Rtype_error))) /\
   (!(s:(C,FFI)clos_state) n lv.
      clos_do_app (BlockOp (FromList n)) [lv] s =
      (match clos_v_to_list lv with
         SOME vs -> Rval (clos_Block n vs, s)
       | _ -> Rerr (Rabort Rtype_error)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CASE_REWRITE_TAC[]);;

(* decide the comparisons of numbers that the clock checks produce (the   *)
(* evaluator below retries the same comparisons at each pass: the results   *)
(* of ARITH_RULE, also failures, are remembered)                            *)
let CLOSP2AUX_IP_ARITH_CONV : conv =
  let num_ty = `:num` in
  let memo = Hashtbl.create 997 in
  fun tm ->
  let isnum t = (try type_of t = num_ty with Failure _ -> false) in
  let ok = (is_binary "<" tm || is_binary "<=" tm || (is_eq tm && isnum (lhand tm))) &&
           isnum (rand tm) in
  if not ok then failwith "CLOSP2AUX_IP_ARITH_CONV" else
  if frees tm = [] then CHANGED_CONV NUM_REDUCE_CONV tm else
  let r = try Hashtbl.find memo tm with Not_found ->
            let r = try Some (EQT_INTRO (ARITH_RULE tm)) with Failure _ ->
                    try Some (EQF_INTRO (ARITH_RULE (mk_neg tm))) with Failure _ -> None in
            Hashtbl.add memo tm r; r in
  match r with Some th -> th | None -> failwith "CLOSP2AUX_IP_ARITH_CONV";;

(* a lazy evaluator: rewrite only the active positions of a term (not the  *)
(* branches of conditionals and case expressions, not under binders)       *)
let CLOSP2AUX_is_case (tm:term) : bool =
  let h,args = strip_comb tm in
  is_const h && args <> [] &&
  (let n = fst(dest_const h) in
   let l = String.length n in l > 5 && String.sub n (l - 5) 5 = "_CASE");;

let rec CLOSP2AUX_LAZY_CONV (step:conv) : conv = fun tm ->
  try step tm with Failure _ ->
  if is_cond tm then RATOR_CONV(RATOR_CONV(RAND_CONV (CLOSP2AUX_LAZY_CONV step))) tm
  else if CLOSP2AUX_is_case tm then
    let h,args = strip_comb tm in
    (funpow (length args - 1) RATOR_CONV (RAND_CONV (CLOSP2AUX_LAZY_CONV step))) tm
  else match tm with
    Comb(f,x) ->
      (try let th1 = CLOSP2AUX_LAZY_CONV step f in
           (try MK_COMB(th1, CLOSP2AUX_LAZY_CONV step x) with Failure _ -> AP_THM th1 x)
       with Failure _ -> AP_TERM f (CLOSP2AUX_LAZY_CONV step x))
  | _ -> failwith "CLOSP2AUX_LAZY_CONV";;

let CLOSP2AUX_ip_case_defs =
  map case_def ["result"; "option"; "list"; "prod"; "error_result"; "app_kind";
                "clos_v"; "eq_result"];;

(* the step rules; extra are added per use (assumptions, IHs) *)
let CLOSP2AUX_ip_step_rules =
  CONJUNCTS clos_evaluate_def @
  [CLOSP2AUX_ip_do_app; dest_closure_def; check_loc_def; clos_dec_clock_def;
   clos_state_INFO.ri_accfupds; clos_state_INFO.ri_fupdfupds; K_o_THM; K_THM;
   LENGTH; REVERSE; APPEND; APPEND_NIL; HD; TL; EL_CONS; TAKE_DEF; DROP_DEF;
   LISTAUX_list_of_seq_1; LET_DEF; LET_END_DEF; clos_interpreter_def; ALL;
   clos_Boolv_def; true_tag_def; false_tag_def; COND_CLAUSES; REFL_CLAUSE;
   injectivity "clos_v"; distinctness "clos_v"; injectivity "clos_op";
   distinctness "clos_op"; distinctness "block_op"; distinctness "int_op";
   injectivity "result"; distinctness "result"; PAIR_EQ; CONS_11; NOT_CONS_NIL;
   NOT_NIL_CONS; SUC_SUB1; NOT_SUC; AND_CLAUSES; OR_CLAUSES; NOT_CLAUSES; IMP_CLAUSES;
   clos_with_same_clock; I_THM; o_THM] @ CLOSP2AUX_ip_case_defs;;

let CLOSP2AUX_IP_STEP_CONV (extra:thm list) : conv =
  let rw = GEN_REWRITE_CONV I (extra @ CLOSP2AUX_ip_step_rules) in
  CHANGED_CONV (FIRST_CONV [rw; BETA_CONV; NUM_RED_CONV; CLOSP2AUX_IP_ARITH_CONV]);;

let CLOSP2AUX_IP_LAZY_TAC (extra:thm list) : tactic =
  CONV_TAC(REPEATC (CLOSP2AUX_LAZY_CONV (CLOSP2AUX_IP_STEP_CONV extra)));;

let CLOSP2AUX_ip_int_suc_sub1 = prove
 (`!n. &(SUC n) - &1:int = &n`,
  REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC);;

let CLOSP2AUX_IP_ASM_LAZY_TAC (extra:thm list) : tactic = fun (asl,w as g) ->
  CLOSP2AUX_IP_LAZY_TAC (extra @ map snd asl) g;;

(* HOL4: clos_interp_el_thm *)
let clos_interp_el_thm = prove
 (`!n env rest cl_env.
     n < LENGTH env /\ 1 <= clos_state_max_app t4 ==>
     ?c. clos_evaluate
           ([clos_interp_el],
            CONS (clos_list_to_v env) (CONS (clos_Number (&n))
              (CONS (clos_Recclosure NONE [] cl_env
                       [(1,Fn (implode "") NONE NONE 1 clos_interp_el)] 0) rest)),
            clos_state_clock_fupd (K (c + clos_state_clock t4)) t4) =
         (Rval [EL n env],(t4:(C,FFI)clos_state))`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `env:clos_v list` list_CASES) THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; LT_SUC; LT_0] THEN STRIP_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; clos_list_to_v_def];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:clos_v list`; `cl_env:clos_v list`;
                                  `cl_env:clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c1:num` ASSUME_TAC) THEN
    EXISTS_TAC `c1 + 2` THEN
    REWRITE_TAC[ARITH_RULE `(c1 + 2) + k = SUC (SUC (c1 + k))`; clos_list_to_v_def]] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV) [clos_interp_el_def] THEN
  CLOSP2AUX_IP_ASM_LAZY_TAC[CLOSP2AUX_ip_int_suc_sub1; INT_OF_NUM_EQ; OPTION_MAP_DEF; EL]);;

(* HOL4: clos_interp_rev_thm *)
let clos_interp_rev_thm = prove
 (`!a env rest cl_env.
     1 <= clos_state_max_app t4 ==>
     clos_evaluate
       ([clos_interp_rev],
        CONS (clos_list_to_v env) (CONS (clos_list_to_v a)
          (CONS (clos_Recclosure NONE [] cl_env
                   [(1,Fn (implode "") NONE NONE 1 clos_interp_rev)] 0) rest)),
        clos_state_clock_fupd (K (2 * LENGTH a + clos_state_clock t4)) t4) =
     (Rval [clos_list_to_v (APPEND (REVERSE a) env)],(t4:(C,FFI)clos_state))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[LENGTH; MULT_CLAUSES; ADD_CLAUSES; REVERSE; APPEND; clos_list_to_v_def];
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:clos_v) env`; `cl_env:clos_v list`;
                                  `cl_env:clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[clos_list_to_v_def; cons_tag_def]) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `2 * SUC n + k = SUC (SUC (2 * n + k))`;
                clos_list_to_v_def; REVERSE; GSYM APPEND_ASSOC; APPEND]] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV) [clos_interp_rev_def] THEN
  CLOSP2AUX_IP_ASM_LAZY_TAC[OPTION_MAP_DEF; nil_tag_def; cons_tag_def]);;

(* HOL4: evaluate_SING_intro [local] *)
let evaluate_SING_intro = prove
 (`x = (Rval [v:clos_v]:(clos_v list,clos_v)result,s) /\ vs = [v] ==>
   x = (Rval vs,s:(C,FFI)clos_state)`,
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* clocks in the canonical form SUC^k r (r a normalised sum): the clock    *)
(* decrements of the evaluation are then SUC_SUB1 steps                     *)
(* (the quotations are parsed once: a parse costs milliseconds here, and the *)
(* conversion is tried thousands of times by the evaluator below)           *)
let CLOSP2AUX_SUCN_NORM_CONV : conv =
  let num_ty = `:num` and plus_tm = `(+):num->num->num` and suc_tm = `SUC` in
  let rec conv e =
    if not (type_of e = num_ty) then failwith "CLOSP2AUX_SUCN_NORM_CONV" else
    if is_binary "-" e then LAND_CONV conv e else
    let th1 = (REWRITE_CONV[ADD1] THENC NUM_NORMALIZE_CONV) e in
    let p = rand (concl th1) in
    let rec summands t = (try let l,r = dest_binop plus_tm t in
                                summands l @ summands r with Failure _ -> [t]) in
    let ss = summands p in
    let nums,rest = partition is_numeral ss in
    let k = itlist (fun t a -> dest_small_numeral t + a) nums 0 in
    if rest = [] then failwith "CLOSP2AUX_SUCN_NORM_CONV" else
    let r = end_itlist (fun a b -> mk_binop plus_tm a b) rest in
    let target = funpow k (fun t -> mk_comb(suc_tm,t)) r in
    if target = e then failwith "CLOSP2AUX_SUCN_NORM_CONV" else
    ARITH_RULE (mk_eq(e,target)) in
  conv;;

let CLOSP2AUX_CLOCK_NORM_CONV : conv = fun tm ->
  match tm with
    Comb(Comb(Const("clos_state_clock_fupd",_),Comb(Const("K",_),e)),s) ->
      RATOR_CONV(RAND_CONV(RAND_CONV CLOSP2AUX_SUCN_NORM_CONV)) tm
  | _ -> failwith "CLOSP2AUX_CLOCK_NORM_CONV";;

let CLOSP2AUX_CLOCK_NORM_RULE : thm -> thm =
  CONV_RULE (TOP_DEPTH_CONV CLOSP2AUX_CLOCK_NORM_CONV);;

(* the extra rules (assumptions) are tried first; an application of a     *)
(* function value that is not a constructor term (a variable, HD [v], ...)  *)
(* to arguments is left to the extra rules                                  *)
let CLOSP2AUX_IP_STEP2_CONV (extra:thm list) : conv =
  let rw0 = GEN_REWRITE_CONV I extra in
  let rw = GEN_REWRITE_CONV I CLOSP2AUX_ip_step_rules in
  let cons_names = ["clos_Number"; "clos_Word64"; "clos_Block"; "ByteVector"; "clos_RefPtr";
                    "clos_Closure"; "clos_Recclosure"] in
  let rw1 tm =
    let h,args = strip_comb tm in
    if is_const h && fst(dest_const h) = "evaluate_app" && length args = 4 &&
       is_cons (el 2 args) &&
       not (let fh = fst(strip_comb(el 1 args)) in
            is_const fh && mem (fst(dest_const fh)) cons_names)
    then failwith "CLOSP2AUX_IP_STEP2_CONV"
    else rw tm in
  CHANGED_CONV (FIRST_CONV [rw0; rw1; BETA_CONV; NUM_RED_CONV; CLOSP2AUX_IP_ARITH_CONV;
                            CLOSP2AUX_CLOCK_NORM_CONV]);;

(* local helpers for clos_interpreter_correct: its two statements as      *)
(* predicates of e and es, and one lemma per case of to_constant_ind        *)
let CLOSP2AUX_ip_P0 =
 `!env (s4:(C,FFI)clos_state) (t4:(C,FFI)clos_state) r s5.
     clos_evaluate ([e],env,s4) = (r,s5) /\ can_interpret e /\
     interp_assum (:C) (:FFI) (clos_state_clock s4) /\
     clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     ?c t5. clos_evaluate ([clos_interpreter_body],
                           [make_const (to_constant e); clos_Block 0 []; clos_list_to_v env],
                           clos_state_clock_fupd (K (c + clos_state_clock t4)) t4) = (r,t5) /\
            clos_interpProof_state_rel s5 t5`;;

let CLOSP2AUX_ip_P1 = CASE_TERM
 `!env (s4:(C,FFI)clos_state) (t4:(C,FFI)clos_state) r s5.
     clos_evaluate (es,env,s4) = (r,s5) /\ can_interpret_list es /\
     interp_assum (:C) (:FFI) (clos_state_clock s4) /\
     clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     ?c t5 r5. clos_evaluate ([clos_interpreter_body],
                              [make_const (to_constant_list es); clos_Block 1 [];
                               clos_list_to_v env],
                              clos_state_clock_fupd (K (c + clos_state_clock t4)) t4) =
               (r5,t5) /\
               clos_interpProof_state_rel s5 t5 /\
               (match r with Rval vs -> r5 = Rval [clos_list_to_v vs] | _ -> r = r5)`;;

let CLOSP2AUX_ip_p0 (e:term) = vsubst [e,`e:clos_exp`] CLOSP2AUX_ip_P0;;
let CLOSP2AUX_ip_p1 (es:term) = vsubst [es,`es:clos_exp list`] CLOSP2AUX_ip_P1;;

(* split the evaluation tm: Rval a at state s, or Rerr e *)
let CLOSP2AUX_IP_SPLIT_TAC (tm:term) (a:term) (s:term) (e:term) : tactic =
  let pc = prove
   (`!p:(clos_v list,clos_v)result # (C,FFI)clos_state.
       (?a s. p = (Rval a,s)) \/ (?e s. p = (Rerr e,s))`,
    GEN_TAC THEN MP_TAC(ISPEC `p:(clos_v list,clos_v)result # (C,FFI)clos_state`
      PAIR_SURJECTIVE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    CASES_ON `x:(clos_v list,clos_v)result` THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN MESON_TAC[]) in
  DISJ_CASES_THEN2
   (X_CHOOSE_THEN a (X_CHOOSE_THEN s ASSUME_TAC))
   (X_CHOOSE_THEN e (X_CHOOSE_THEN s ASSUME_TAC))
   (ISPEC tm pc) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = tm then REWRITE_TAC[th]
                        else NO_TAC) THEN TRY(CASE_REWRITE_TAC[]);;

(* use the induction hypothesis lab on the assumptions, naming the         *)
(* witnesses of its conclusion                                              *)
let CLOSP2AUX_IP_IH_TAC (lab:string) (names:term list) : tactic = fun (asl,w as g) ->
  let ih = assoc lab asl in
  let nrm = REWRITE_RULE[distinctness "result"; injectivity "result";
                         distinctness "error_result"] in
  let asms0 = map snd asl in
  let asms = asms0 @ mapfilter (fun th -> let th' = nrm th in
                                  if concl th' = concl th then failwith "same" else th') asms0 in
  let rec resolve depth th =
    let c = snd (strip_forall (concl th)) in
    if not (is_imp c) then [th] else if depth = 0 then [] else
    let rs = mapfilter (fun a -> nrm (MATCH_MP th a)) asms in
    flat (map (resolve (depth-1)) rs) in
  match resolve 7 (REWRITE_RULE[IMP_CONJ] ih) with
    th::_ -> (itlist (fun v ttac -> X_CHOOSE_THEN v ttac) names STRIP_ASSUME_TAC) th g
  | [] -> failwith ("CLOSP2AUX_IP_IH_TAC "^lab);;

(* interp_assum after an evaluation from s4 to s6 *)
let CLOSP2AUX_IP_LEQ_TAC (ev:term) : tactic =
  FIRST_ASSUM(fun th ->
    if concl th <> ev then NO_TAC else
    let le = MATCH_MP (CONJUNCT1 clos_evaluate_clock) th in
    FIRST_ASSUM(fun ia -> if can (find_term (fun t ->
                                try fst(dest_const t) = "interp_assum" with Failure _ -> false))
                                (concl ia) && not (is_forall (concl ia))
                          then ASSUME_TAC (MATCH_MP interp_assum_leq (CONJ ia le))
                          else NO_TAC));;

(* lift the evaluation ev (an assumption) by extra clock ticks *)
let CLOSP2AUX_IP_LIFT_TAC (ev:term) (extra:term) : tactic =
  FIRST_ASSUM(fun th ->
    if concl th <> ev then NO_TAC else
    let nt = prove(mk_neg(mk_eq(fst(dest_pair(rhs ev)), `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result`)),
                   REWRITE_TAC[distinctness "result"; injectivity "result";
                               distinctness "error_result"; injectivity "error_result";
                               distinctness "abort"]) in
    ASSUME_TAC(REWRITE_RULE[clos_state_INFO.ri_accfupds; clos_state_INFO.ri_fupdfupds;
                            K_o_THM; K_THM]
                 (SPEC extra (MATCH_MP clos_evaluate_add_clock (CONJ th nt)))));;

(* the facts of the relation that the evaluation of the interpreter uses *)
let CLOSP2AUX_ip_state_rel_facts = prove
 (`!(s:(C,FFI)clos_state) t.
     clos_interpProof_state_rel s t ==>
     1 <= clos_state_max_app t /\
     (!k. clos_do_app (GlobOp (clos_Global 0)) [] (clos_state_clock_fupd (K k) t) =
          Rval (clos_Closure NONE [] [] 1 clos_interpreter, clos_state_clock_fupd (K k) t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_interpProof_state_rel_def] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN GEN_TAC THEN
  REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; get_global_def] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `clos_state_globals (s:(C,FFI)clos_state)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "oHD" with Failure _ -> false))
      (lhs (concl th)))) THEN
  SPEC_TAC(`clos_state_globals (t:(C,FFI)clos_state)`, `g:(clos_v option)list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[oHD_DEF; distinctness "option"; injectivity "option"; LENGTH; LT_0; EL; HD] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

(* the evaluation with the assumptions (clock-normalised) and the facts of *)
(* the relations as extra rules *)
let CLOSP2AUX_IP_EVAL_TAC (extra:thm list) : tactic = fun (asl,w as g) ->
  let asms = map snd asl in
  let facts = flat (mapfilter (fun th -> CONJUNCTS (MATCH_MP CLOSP2AUX_ip_state_rel_facts th))
                       asms) in
  let ths = map CLOSP2AUX_CLOCK_NORM_RULE (extra @ facts @ asms) in
  CONV_TAC(REPEATC (CLOSP2AUX_LAZY_CONV (CLOSP2AUX_IP_STEP2_CONV ths))) g;;

(* finishing the residual goal of a symbolic evaluation *)
let CLOSP2AUX_IP_FIN_TAC : tactic =
  REPEAT(CHANGED_TAC(REWRITE_TAC[DROP_DEF; TAKE_DEF; APPEND; REVERSE; evaluate_app_NIL] THEN
                     CONV_TAC NUM_REDUCE_CONV)) THEN
  REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[]);;

(* unfolding the top interpreter body of the goal *)
let CLOSP2AUX_IP_BODY_TAC : tactic =
  REWRITE_TAC[to_constant_def; to_constant_op_def; LENGTH; NOT_SUC; make_const_def; MAP] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV) [clos_interpreter_body_def];;

(* the [] case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_nil = prove
 (CLOSP2AUX_ip_p1 `[]:clos_exp list`,
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `t4:(C,FFI)clos_state`;
                        `Rval [clos_list_to_v []]:(clos_v list,clos_v)result`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[to_constant_def; make_const_def; MAP; clos_list_to_v_def; nil_tag_def;
              clos_interpreter_body_def] THEN
  CLOSP2AUX_IP_EVAL_TAC[]);;

(* the If case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_If = prove
 (mk_imp(list_mk_conj [CLOSP2AUX_ip_p0 `e1:clos_exp`; CLOSP2AUX_ip_p0 `e2:clos_exp`;
                       CLOSP2AUX_ip_p0 `e3:clos_exp`],
         CLOSP2AUX_ip_p0 `clos_If t e1 e2 e3`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1")
    (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH3"))) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([e1],env,s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
      check (fun th -> is_eq (concl th) &&
                       lhs (concl th) = `clos_evaluate ([e1],env,s4:(C,FFI)clos_state)`)) THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IP_LEQ_TAC `clos_evaluate ([e1],env,s4:(C,FFI)clos_state) = (Rval [v1],s6)` THEN
    REWRITE_TAC[HD] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `clos_Boolv T = v1`)) THEN
      DISCH_TAC THEN
      CLOSP2AUX_IP_IH_TAC "IH2" [`c2:num`; `t7:(C,FFI)clos_state`] THEN
      CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
          [make_const (to_constant e1); clos_Block 0 []; clos_list_to_v env],
          clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
          (Rval [clos_Boolv T],t6:(C,FFI)clos_state)` `c2 + 3` THEN
      MAP_EVERY EXISTS_TAC [`c1 + c2 + 6`; `t7:(C,FFI)clos_state`] THEN
      ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
      CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `clos_Boolv F = v1`)) THEN
      DISCH_TAC THEN
      CLOSP2AUX_IP_IH_TAC "IH3" [`c2:num`; `t7:(C,FFI)clos_state`] THEN
      CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
          [make_const (to_constant e1); clos_Block 0 []; clos_list_to_v env],
          clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
          (Rval [clos_Boolv F],t6:(C,FFI)clos_state)` `c2 + 3` THEN
      MAP_EVERY EXISTS_TAC [`c1 + c2 + 6`; `t7:(C,FFI)clos_state`] THEN
      ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
      CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC;
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC]);;

(* the clock of related states, and clock updates of related states *)
let CLOSP2AUX_ip_state_rel_clock = prove
 (`!(s:(C,FFI)clos_state) t.
     clos_interpProof_state_rel s t ==>
     clos_state_clock t = clos_state_clock s /\
     !k. clos_interpProof_state_rel (clos_state_clock_fupd (K k) s)
                                    (clos_state_clock_fupd (K k) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_interpProof_state_rel_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSP2AUX_ip_nonzero_SUC = prove
 (`!m. (?n. m = SUC n) <=> ~(m = 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
  REWRITE_TAC[NOT_SUC; SUC_INJ] THEN MESON_TAC[]);;

(* the Tick case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_Tick = prove
 (mk_imp(CLOSP2AUX_ip_p0 `e:clos_exp`, CLOSP2AUX_ip_p0 `clos_Tick t e`),
  DISCH_THEN(LABEL_TAC "IH1") THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_ip_state_rel_clock) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `clos_state_clock_fupd (K 0) (t4:(C,FFI)clos_state)`] THEN
    CONJ_TAC THENL
     [CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
      FIRST_X_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) = `0`
                              then REWRITE_TAC[SYM th; clos_with_same_clock] else NO_TAC)];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` ASSUME_TAC o
    REWRITE_RULE[GSYM CLOSP2AUX_ip_nonzero_SUC] o check (is_neg o concl)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `interp_assum (:C) (:FFI)
                  (clos_state_clock (clos_dec_clock 1 (s4:(C,FFI)clos_state)))` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST [`clos_state_clock (s4:(C,FFI)clos_state)`,`c:num`] interp_assum_leq) THEN
    ASM_REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `clos_interpProof_state_rel (clos_dec_clock 1 (s4:(C,FFI)clos_state))
                  (clos_dec_clock 1 (t4:(C,FFI)clos_state))` ASSUME_TAC THENL
   [REWRITE_TAC[clos_dec_clock_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds;
                              clos_state_INFO.ri_fupdfupds; K_o_THM; K_THM]) THEN
  MAP_EVERY EXISTS_TAC [`c1 + 2`; `t6:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, t6:(C,FFI)clos_state)`)) THEN
  ASM_REWRITE_TAC[SUC_SUB1] THEN DISCH_TAC THEN
  CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC);;

(* the Raise case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_Raise = prove
 (mk_imp(CLOSP2AUX_ip_p0 `e:clos_exp`, CLOSP2AUX_ip_p0 `clos_Raise t e`),
  DISCH_THEN(LABEL_TAC "IH1") THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([e],env,s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
      check (fun th -> is_eq (concl th) &&
                       lhs (concl th) = `clos_evaluate ([e],env,s4:(C,FFI)clos_state)`)) THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`];
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`]] THEN
  MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
  CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC);;

(* the Let case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_Let = prove
 (mk_imp(mk_conj(CLOSP2AUX_ip_p0 `e:clos_exp`, CLOSP2AUX_ip_p1 `es:clos_exp list`),
         CLOSP2AUX_ip_p0 `clos_Let t es e`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (es,env,s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [DISCH_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH2" [`c1:num`; `t6:(C,FFI)clos_state`;
                               `r6:(clos_v list,clos_v)result`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[case_def "result"]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `r6:(clos_v list,clos_v)result`)) THEN
    CLOSP2AUX_IP_LEQ_TAC `clos_evaluate (es,env,s4:(C,FFI)clos_state) = (Rval a1,s6)` THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c2:num`; `t7:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
        [make_const (to_constant_list es); clos_Block 1 []; clos_list_to_v env],
        clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
        (Rval [clos_list_to_v a1],t6:(C,FFI)clos_state)` `c2 + 3` THEN
    MAP_EVERY EXISTS_TAC [`c1 + c2 + 6`; `t7:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    CLOSP2AUX_IP_EVAL_TAC[v_to_list_list_to_v] THEN CLOSP2AUX_IP_FIN_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH2" [`c1:num`; `t6:(C,FFI)clos_state`;
                               `r6:(clos_v list,clos_v)result`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[case_def "result"]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `r6:(clos_v list,clos_v)result`)) THEN
    MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC]);;

(* the Handle case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_Handle = prove
 (mk_imp(mk_conj(CLOSP2AUX_ip_p0 `e1:clos_exp`, CLOSP2AUX_ip_p0 `e2:clos_exp`),
         CLOSP2AUX_ip_p0 `clos_Handle t e1 e2`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([e1],env,s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
      check (fun th -> is_eq (concl th) &&
                       lhs (concl th) = `clos_evaluate ([e1],env,s4:(C,FFI)clos_state)`)) THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)
    (ISPEC `err:(clos_v)error_result` (cases "error_result")) THEN
  CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IP_LEQ_TAC
      `clos_evaluate ([e1],env,s4:(C,FFI)clos_state) = (Rerr (Rraise v1),s6)` THEN
    CLOSP2AUX_IP_IH_TAC "IH2" [`c2:num`; `t7:(C,FFI)clos_state`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_list_to_v_def; cons_tag_def]) THEN
    CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
        [make_const (to_constant e1); clos_Block 0 []; clos_list_to_v env],
        clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
        (Rerr (Rraise v1),t6:(C,FFI)clos_state)` `c2 + 3` THEN
    MAP_EVERY EXISTS_TAC [`c1 + c2 + 6`; `t7:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC;
    STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC]);;

(* the Var case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_Var = prove
 (CLOSP2AUX_ip_p0 `clos_Var t n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [ALL_TAC; RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_ip_state_rel_facts) THEN
  MP_TAC(SPECL [`n:num`; `env:clos_v list`;
    `[clos_Block 0 [clos_Number (&n)]; clos_Block 0 []; clos_list_to_v env]`;
    `[clos_Block 0 [clos_Number (&n)]; clos_Block 0 []; clos_list_to_v env]`]
    clos_interp_el_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c1:num` ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`c1 + 2`; `t4:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
  CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC);;

(* the App case of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_App = prove
 (mk_imp(mk_conj(CLOSP2AUX_ip_p0 `e:clos_exp`,
                 list_mk_forall([`a1:clos_exp list`; `e1:clos_exp`],
                   mk_imp(`es = CONS (e1:clos_exp) a1`, CLOSP2AUX_ip_p0 `e1:clos_exp`))),
         CLOSP2AUX_ip_p0 `clos_App x x' e es`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def; LISTAUX_LENGTH_EQ_1] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[can_interpret_def; IS_NONE_EQ_NONE]) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "IH2" o REWRITE_RULE[] o SPECL [`[]:clos_exp list`; `a:clos_exp`] o
    check (is_forall o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def; LENGTH; GT; LT_0] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([a],env,s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `va:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
      check (fun th -> is_eq (concl th) &&
                       lhs (concl th) = `clos_evaluate ([a],env,s4:(C,FFI)clos_state)`)) THEN
    CLOSP2AUX_IP_IH_TAC "IH2" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IP_LEQ_TAC `clos_evaluate ([a],env,s4:(C,FFI)clos_state) = (Rval [va],s6)` THEN
    CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([e],env,s6:(C,FFI)clos_state)`
      `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
     [FIRST_ASSUM(X_CHOOSE_THEN `vf:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
        check (fun th -> is_eq (concl th) &&
                         lhs (concl th) = `clos_evaluate ([e],env,s6:(C,FFI)clos_state)`)) THEN
      CLOSP2AUX_IP_IH_TAC "IH1" [`c2:num`; `t7:(C,FFI)clos_state`] THEN
      CLOSP2AUX_IP_LEQ_TAC `clos_evaluate ([e],env,s6:(C,FFI)clos_state) = (Rval [vf],s7)` THEN
      REWRITE_TAC[HD] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[interp_assum_def] o check (fun th ->
        concl th = `interp_assum (:C) (:FFI) (clos_state_clock (s7:(C,FFI)clos_state))`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`[va]:clos_v list`; `s7:(C,FFI)clos_state`; `NONE:num option`;
        `vf:clos_v`; `t7:(C,FFI)clos_state`; `r:(clos_v list,clos_v)result`;
        `s5:(C,FFI)clos_state`]) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t8:(C,FFI)clos_state`
        STRIP_ASSUME_TAC)) THEN
      CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
          [make_const (to_constant a); clos_Block 0 []; clos_list_to_v env],
          clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
          (Rval [va],t6:(C,FFI)clos_state)` `c2 + ck + 3` THEN
      CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
          [make_const (to_constant e); clos_Block 0 []; clos_list_to_v env],
          clos_state_clock_fupd (K (c2 + clos_state_clock t6)) t6) =
          (Rval [vf],t7:(C,FFI)clos_state)` `ck:num` THEN
      MAP_EVERY EXISTS_TAC [`c1 + c2 + ck + 6`; `t8:(C,FFI)clos_state`] THEN
      ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[] THEN
      CLOSP2AUX_IP_FIN_TAC;
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      CLOSP2AUX_IP_IH_TAC "IH1" [`c2:num`; `t7:(C,FFI)clos_state`] THEN
      CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
          [make_const (to_constant a); clos_Block 0 []; clos_list_to_v env],
          clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
          (Rval [va],t6:(C,FFI)clos_state)` `c2 + 3` THEN
      MAP_EVERY EXISTS_TAC [`c1 + c2 + 6`; `t7:(C,FFI)clos_state`] THEN
      ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[] THEN
      CLOSP2AUX_IP_FIN_TAC];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH2" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[] THEN
    CLOSP2AUX_IP_FIN_TAC]);;

(* the Op cases of clos_interpreter_correct *)
let CLOSP2AUX_ip_do_app_Global = prove
 (CASE_TERM `(!n (s:(C,FFI)clos_state).
     clos_do_app (GlobOp (clos_Global n)) [] s =
     (match get_global n (clos_state_globals s) with
        SOME (SOME v) -> Rval (v,s)
      | _ -> Rerr (Rabort Rtype_error))) /\
   (!n (s:(C,FFI)clos_state).
     clos_do_app (GlobOp (clos_Global 0)) [clos_Number (&n)] s =
     (match get_global n (clos_state_globals s) with
        SOME (SOME v) -> Rval (v,s)
      | _ -> Rerr (Rabort Rtype_error)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT; NUM_OF_INT_OF_NUM]);;

let CLOSP2AUX_ip_state_rel_globals = prove
 (`!(s:(C,FFI)clos_state) t.
     clos_interpProof_state_rel s t ==> clos_state_globals t = clos_state_globals s`,
  SIMP_TAC[clos_interpProof_state_rel_def]);;

let CLOSP2AUX_ip_option2_cases = prove
 (`!x:(A option)option. x = NONE \/ x = SOME NONE \/ ?v. x = SOME (SOME v)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `x:(A option)option` (cases "option")) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[cases "option"]);;

let CLOSP2AUX_ip_correct_Op_Global = prove
 (CLOSP2AUX_ip_p0 `clos_Op t (GlobOp (clos_Global n)) []`,
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def; distinctness "clos_op"] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; CLOSP2AUX_ip_do_app_Global] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSP2AUX_ip_state_rel_globals) THEN
  REPEAT_TCL DISJ_CASES_THEN
    (fun th -> try (X_CHOOSE_THEN `v:clos_v` ASSUME_TAC th) with Failure _ -> ASSUME_TAC th)
    (ISPEC `get_global n (clos_state_globals (s4:(C,FFI)clos_state))`
       CLOSP2AUX_ip_option2_cases) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  TRY(RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC THEN NO_TAC) THEN
  MAP_EVERY EXISTS_TAC [`0`; `t4:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
  CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[CLOSP2AUX_ip_do_app_Global]);;

let CLOSP2AUX_IP_OP_NIL_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def; distinctness "clos_op"] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; CLOSP2AUX_ip_do_app] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `t4:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
  CLOSP2AUX_IP_BODY_TAC THEN CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC;;

let CLOSP2AUX_ip_correct_Op_Cons_nil = prove
 (CLOSP2AUX_ip_p0 `clos_Op t (BlockOp (clos_Cons tag)) []`, CLOSP2AUX_IP_OP_NIL_TAC);;

let CLOSP2AUX_ip_correct_Op_Const = prove
 (CLOSP2AUX_ip_p0 `clos_Op t (IntOp (clos_Const i)) []`, CLOSP2AUX_IP_OP_NIL_TAC);;

let CLOSP2AUX_ip_correct_Op_Constant = prove
 (CLOSP2AUX_ip_p0 `clos_Op t (BlockOp (Constant c)) []`, CLOSP2AUX_IP_OP_NIL_TAC);;

let CLOSP2AUX_ip_correct_Op_Cons = prove
 (mk_imp(list_mk_conj [CLOSP2AUX_ip_p1 `CONS (e0:clos_exp) es0`; `tag < 3`],
         CLOSP2AUX_ip_p0 `clos_Op t (BlockOp (clos_Cons tag)) (CONS (e0:clos_exp) es0)`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") MP_TAC) THEN
  DISCH_THEN(fun th -> REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC
    (MATCH_MP (ARITH_RULE `tag < 3 ==> tag = 0 \/ tag = 1 \/ tag = 2`) th)) THEN
  (REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `can_interpret_list (CONS (e0:clos_exp) es0)` ASSUME_TAC THEN
  TRY(ASM_REWRITE_TAC[can_interpret_def] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def; distinctness "clos_op"] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (CONS e0 es0,env,s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [REWRITE_TAC[CLOSP2AUX_ip_do_app] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`;
                               `r6:(clos_v list,clos_v)result`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[case_def "result"]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `r6:(clos_v list,clos_v)result`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_ip_state_rel_facts o
      check (fun th -> concl th = `clos_interpProof_state_rel s5 (t6:(C,FFI)clos_state)`)) THEN
    CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
        [make_const (to_constant_list (CONS e0 es0)); clos_Block 1 [];
         clos_list_to_v env],
        clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
        (Rval [clos_list_to_v a1],t6:(C,FFI)clos_state)`
      `2 * LENGTH (a1:clos_v list) + 2` THEN
    MP_TAC(REWRITE_RULE[clos_list_to_v_def; nil_tag_def; APPEND_NIL]
      (SPECL [`a1:clos_v list`; `[]:clos_v list`]
        (INST [`t6:(C,FFI)clos_state`,`t4:(C,FFI)clos_state`] clos_interp_rev_thm))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`c1 + 2 * LENGTH (a1:clos_v list) + 5`; `t6:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[to_constant_def; make_const_def; MAP]) THEN
    CLOSP2AUX_IP_EVAL_TAC[v_to_list_list_to_v] THEN CLOSP2AUX_IP_FIN_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`;
                               `r6:(clos_v list,clos_v)result`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[case_def "result"]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `r6:(clos_v list,clos_v)result`)) THEN
    MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_BODY_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[to_constant_def; make_const_def; MAP]) THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC]));;
let CLOSP2AUX_ip_can_interpret_op = prove
 (`!p l. can_interpret_op p l <=>
     (?tag. p = BlockOp (clos_Cons tag) /\ (l = 0 \/ tag < 3)) \/
     (?i. p = IntOp (clos_Const i) /\ l = 0) \/
     (?n. p = GlobOp (clos_Global n) /\ l = 0) \/
     (?c. p = BlockOp (Constant c) /\ l = 0)`,
  let ths = [can_interpret_op_def; distinctness "clos_op"; injectivity "clos_op";
             distinctness "block_op"; injectivity "block_op"; distinctness "int_op";
             injectivity "int_op"; distinctness "glob_op"; injectivity "glob_op";
             UNWIND_THM1; EXISTS_SIMP] in
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `p:clos_op` (cases "clos_op")) THEN REWRITE_TAC ths THEN
  (fun (asl,w as g) ->
     match filter (fun v -> mem (type_of v) [`:block_op`; `:int_op`; `:glob_op`]) (frees w) with
       v::_ -> (STRUCT_CASES_TAC (ISPEC v (cases (fst(dest_type(type_of v))))) THEN
                REWRITE_TAC ths) g
     | [] -> ALL_TAC g) THEN
  MESON_TAC[]);;

let CLOSP2AUX_ip_correct_Op = prove
 (mk_imp(CLOSP2AUX_ip_p1 `es:clos_exp list`, CLOSP2AUX_ip_p0 `clos_Op t p es`),
  DISCH_TAC THEN
  ASM_CASES_TAC `can_interpret_op p (LENGTH (es:clos_exp list))` THENL
   [ALL_TAC; REPEAT GEN_TAC THEN ASM_REWRITE_TAC[can_interpret_def]] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[CLOSP2AUX_ip_can_interpret_op; LENGTH_EQ_NIL] o
    check (fun th -> not (is_forall (concl th)))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  TRY(FIRST (map MATCH_ACCEPT_TAC
    [CLOSP2AUX_ip_correct_Op_Cons_nil; CLOSP2AUX_ip_correct_Op_Const;
     CLOSP2AUX_ip_correct_Op_Global; CLOSP2AUX_ip_correct_Op_Constant]) THEN NO_TAC) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `e0:clos_exp` (X_CHOOSE_THEN `es0:clos_exp list` SUBST_ALL_TAC))
    (ISPEC `es:clos_exp list` list_CASES) THEN
  TRY(MATCH_ACCEPT_TAC CLOSP2AUX_ip_correct_Op_Cons_nil THEN NO_TAC) THEN
  MATCH_MP_TAC CLOSP2AUX_ip_correct_Op_Cons THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* the CONS case (list mode) of clos_interpreter_correct *)
let CLOSP2AUX_ip_correct_CONS = prove
 (mk_imp(mk_conj(CLOSP2AUX_ip_p0 `x:clos_exp`, CLOSP2AUX_ip_p1 `xs:clos_exp list`),
         CLOSP2AUX_ip_p1 `CONS (x:clos_exp) xs`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_CONS] o
    check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x],env,s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
      check (fun th -> is_eq (concl th) &&
                       lhs (concl th) = `clos_evaluate ([x],env,s4:(C,FFI)clos_state)`)) THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IP_LEQ_TAC `clos_evaluate ([x],env,s4:(C,FFI)clos_state) = (Rval [v1],s6)` THEN
    CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,env,s6:(C,FFI)clos_state)`
      `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THEN
    REWRITE_TAC[PAIR_EQ; HD] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH2" [`c2:num`; `t7:(C,FFI)clos_state`;
                               `r7:(clos_v list,clos_v)result`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[case_def "result"]) THEN
    CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([clos_interpreter_body],
        [make_const (to_constant x); clos_Block 0 []; clos_list_to_v env],
        clos_state_clock_fupd (K (c1 + clos_state_clock t4)) t4) =
        (Rval [v1],t6:(C,FFI)clos_state)` `c2 + 3` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `r7:(clos_v list,clos_v)result`)) THEN
      MAP_EVERY EXISTS_TAC [`c1 + c2 + 6`; `t7:(C,FFI)clos_state`;
        `Rval [clos_list_to_v (CONS v1 a2)]:(clos_v list,clos_v)result`];
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `r7:(clos_v list,clos_v)result`)) THEN
      MAP_EVERY EXISTS_TAC [`c1 + c2 + 6`; `t7:(C,FFI)clos_state`;
        `Rerr err:(clos_v list,clos_v)result`]] THEN
    ASM_REWRITE_TAC[case_def "result"] THEN
    REWRITE_TAC[to_constant_def; make_const_def; MAP] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
      [clos_interpreter_body_def] THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC THEN
    REWRITE_TAC[clos_list_to_v_def; cons_tag_def];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH1" [`c1:num`; `t6:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`;
      `Rerr err:(clos_v list,clos_v)result`] THEN
    ASM_REWRITE_TAC[case_def "result"] THEN
    REWRITE_TAC[to_constant_def; make_const_def; MAP] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
      [clos_interpreter_body_def] THEN
    CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC]);;

(* HOL4: clos_interpreter_correct *)
let clos_interpreter_correct = prove
 (CASE_TERM `(!e env (s4:(C,FFI)clos_state) (t4:(C,FFI)clos_state) r s5.
     clos_evaluate ([e],env,s4) = (r,s5) /\
     can_interpret e /\
     interp_assum (:C) (:FFI) (clos_state_clock s4) /\
     clos_interpProof_state_rel s4 t4 /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?c t5.
       clos_evaluate ([clos_interpreter_body],
                      [make_const (to_constant e); clos_Block 0 []; clos_list_to_v env],
                      clos_state_clock_fupd (K (c + clos_state_clock t4)) t4) = (r,t5) /\
       clos_interpProof_state_rel s5 t5) /\
   (!es env (s4:(C,FFI)clos_state) (t4:(C,FFI)clos_state) r s5.
     clos_evaluate (es,env,s4) = (r,s5) /\
     can_interpret_list es /\
     interp_assum (:C) (:FFI) (clos_state_clock s4) /\
     clos_interpProof_state_rel s4 t4 /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?c t5 r5.
       clos_evaluate ([clos_interpreter_body],
                      [make_const (to_constant_list es); clos_Block 1 [];
                       clos_list_to_v env],
                      clos_state_clock_fupd (K (c + clos_state_clock t4)) t4) = (r5,t5) /\
       clos_interpProof_state_rel s5 t5 /\
       (match r with Rval vs -> r5 = Rval [clos_list_to_v vs] | _ -> r = r5))`,
  MATCH_MP_TAC to_constant_ind THEN CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THEN
  TRY(REPEAT GEN_TAC THEN REWRITE_TAC[can_interpret_def] THEN NO_TAC) THEN
  REPEAT GEN_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
    [CLOSP2AUX_ip_correct_Var; CLOSP2AUX_ip_correct_App; CLOSP2AUX_ip_correct_If;
     CLOSP2AUX_ip_correct_Let; CLOSP2AUX_ip_correct_Op; CLOSP2AUX_ip_correct_Raise;
     CLOSP2AUX_ip_correct_Tick; CLOSP2AUX_ip_correct_Handle; CLOSP2AUX_ip_correct_nil;
     CLOSP2AUX_ip_correct_CONS]));;

(* HOL4: opt_interp_thm *)
let opt_interp_thm = prove
 (`opt_interp e = SOME x /\
   interp_assum (:C) (:FFI) (clos_state_clock s4) /\
   clos_evaluate ([e],[],s4:(C,FFI)clos_state) = (r,s5) /\
   clos_interpProof_state_rel s4 t4 /\ ~(r = Rerr (Rabort Rtype_error)) ==>
   ?ck t5.
     clos_evaluate ([x],[],clos_state_clock_fupd (K (ck + clos_state_clock t4)) t4) = (r,t5) /\
     clos_interpProof_state_rel s5 (t5:(C,FFI)clos_state)`,
  REWRITE_TAC[opt_interp_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `x:clos_exp`)) THEN
  MP_TAC(SPECL [`e:clos_exp`; `[]:clos_v list`; `s4:(C,FFI)clos_state`;
                `t4:(C,FFI)clos_state`; `r:(clos_v list,clos_v)result`;
                `s5:(C,FFI)clos_state`] (CONJUNCT1 clos_interpreter_correct)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:num` (X_CHOOSE_THEN `t6:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_list_to_v_def; nil_tag_def]) THEN
  MAP_EVERY EXISTS_TAC [`c1 + 3`; `t6:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
  CLOSP2AUX_IP_EVAL_TAC[] THEN CLOSP2AUX_IP_FIN_TAC);;

(* HOL4: opt_interp1_thm' *)
let opt_interp1_thm' = prove
 (`!l s4 t4 s5 r.
     interp_assum (:C) (:FFI) (clos_state_clock s4) /\
     clos_evaluate ([l],[],s4) = (r,s5) /\
     clos_interpProof_state_rel s4 t4 /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?ck (t5:(C,FFI)clos_state).
       clos_evaluate ([opt_interp1 l],[],
                      clos_state_clock_fupd (K (clos_state_clock t4 + ck)) t4) = (r,t5) /\
       clos_interpProof_state_rel s5 t5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[opt_interp1_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `x:clos_exp` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC `opt_interp l` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[interp_assum_def] o check (fun th ->
      concl th = `interp_assum (:C) (:FFI) (clos_state_clock (s4:(C,FFI)clos_state))`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`[l:clos_exp]`; `s4:(C,FFI)clos_state`; `[]:clos_v list`;
      `t4:(C,FFI)clos_state`; `r:(clos_v list,clos_v)result`; `s5:(C,FFI)clos_state`]) THEN
    ASM_REWRITE_TAC[LE_REFL];
    MP_TAC(INST [`l:clos_exp`,`e:clos_exp`] opt_interp_thm) THEN ASM_REWRITE_TAC[]]);;

(* HOL4: opt_interp1_thm *)
let opt_interp1_thm = prove
 (`!l s4 t4 s5 r.
     interp_assum (:C) (:FFI) (clos_state_clock s4) /\
     clos_evaluate (l,[],s4) = (r,s5) /\
     clos_interpProof_state_rel s4 t4 /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?ck (t5:(C,FFI)clos_state).
       clos_evaluate (MAP opt_interp1 l,[],
                      clos_state_clock_fupd (K (clos_state_clock t4 + ck)) t4) = (r,t5) /\
       clos_interpProof_state_rel s5 t5`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; clos_evaluate_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t4:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MAP] THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_CONS] o check (fun th ->
    is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([h],[],s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
      check (fun th -> is_eq (concl th) &&
                       lhs (concl th) = `clos_evaluate ([h],[],s4:(C,FFI)clos_state)`)) THEN
    MP_TAC(SPECL [`h:clos_exp`; `s4:(C,FFI)clos_state`; `t4:(C,FFI)clos_state`;
                  `s6:(C,FFI)clos_state`; `Rval [v1]:(clos_v list,clos_v)result`]
                 opt_interp1_thm') THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t6:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    CLOSP2AUX_IP_LEQ_TAC `clos_evaluate ([h],[],s4:(C,FFI)clos_state) = (Rval [v1],s6)` THEN
    CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (t,[],s6:(C,FFI)clos_state)`
      `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THEN
    REWRITE_TAC[PAIR_EQ; HD] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`ck1 + ck2`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
    CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([opt_interp1 h],[],
        clos_state_clock_fupd (K (clos_state_clock t4 + ck1)) t4) =
        (Rval [v1],t6:(C,FFI)clos_state)` `ck2:num` THEN
    REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(SPECL [`h:clos_exp`; `s4:(C,FFI)clos_state`; `t4:(C,FFI)clos_state`;
                  `s5:(C,FFI)clos_state`; `Rerr err:(clos_v list,clos_v)result`]
                 opt_interp1_thm') THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t6:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1:num`; `t6:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[]]);;

(* local helpers: the evaluation clause of interp_assum at the clock of    *)
(* the state; the three shapes of insert_interp1                           *)
let CLOSP2AUX_IP_ADD_SYM_TAC : tactic =
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(C,FFI)clos_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(C,FFI)clos_state`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];;

let CLOSP2AUX_ip_interp_assum_eval = prove
 (`!xs env (s1:(C,FFI)clos_state) t1 res s2.
     interp_assum (:C) (:FFI) (clos_state_clock s1) /\
     clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     clos_interpProof_state_rel s1 t1 ==>
     ?ck t2. clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t1 + ck)) t1) =
             (res,t2) /\ clos_interpProof_state_rel s2 t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[interp_assum_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs:clos_exp list`; `s1:(C,FFI)clos_state`;
    `env:clos_v list`; `t1:(C,FFI)clos_state`; `res:(clos_v list,clos_v)result`;
    `s2:(C,FFI)clos_state`]) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN CLOSP2AUX_IP_ADD_SYM_TAC);;

let CLOSP2AUX_ip_insert_interp1_cases = prove
 (`!e. insert_interp1 e = e \/
       (?x. opt_interp e = SOME x /\ insert_interp1 e = x) \/
       (?t ys y. opt_interp e = NONE /\ e = clos_Let t ys y /\
                 insert_interp1 e = clos_Let backend_common_None (MAP opt_interp1 ys) y)`,
  GEN_TAC THEN REWRITE_TAC[insert_interp1_def] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `x:clos_exp` SUBST1_TAC)
    (ISPEC `opt_interp e` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `e:clos_exp` (CONJUNCT1 (cases "clos_exp"))) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "clos_exp"; injectivity "clos_exp"] THEN MESON_TAC[]);;

(* HOL4: evaluate_insert_interp1 *)
let evaluate_insert_interp1 = prove
 (`interp_assum (:C) (:FFI) (clos_state_clock s4) /\
   clos_evaluate ([e],[],s4) = (r,s5) /\ clos_interpProof_state_rel s4 t4 /\
   ~(r = Rerr (Rabort Rtype_error)) ==>
   ?ck (t5:(C,FFI)clos_state).
     clos_evaluate ([insert_interp1 e],[],
                    clos_state_clock_fupd (K (clos_state_clock t4 + ck)) t4) = (r,t5) /\
     clos_interpProof_state_rel s5 t5`,
  STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC
    (SPEC `e:clos_exp` CLOSP2AUX_ip_insert_interp1_cases) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC CLOSP2AUX_ip_interp_assum_eval THEN EXISTS_TAC `s4:(C,FFI)clos_state` THEN
    ASM_REWRITE_TAC[];
    MP_TAC opt_interp_thm THEN ASM_REWRITE_TAC[] THEN CLOSP2AUX_IP_ADD_SYM_TAC;
    ALL_TAC] THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (ys,[],s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`ys:clos_exp list`; `s4:(C,FFI)clos_state`; `t4:(C,FFI)clos_state`;
                  `s6:(C,FFI)clos_state`; `Rval a1:(clos_v list,clos_v)result`]
                 opt_interp1_thm) THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t6:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    CLOSP2AUX_IP_LEQ_TAC `clos_evaluate (ys,[],s4:(C,FFI)clos_state) = (Rval a1,s6)` THEN
    MP_TAC(SPECL [`[y:clos_exp]`; `APPEND a1 []:clos_v list`; `s6:(C,FFI)clos_state`;
                  `t6:(C,FFI)clos_state`; `r:(clos_v list,clos_v)result`;
                  `s5:(C,FFI)clos_state`] CLOSP2AUX_ip_interp_assum_eval) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `t7:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1 + ck2`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
    CLOSP2AUX_IP_LIFT_TAC `clos_evaluate (MAP opt_interp1 ys,[],
        clos_state_clock_fupd (K (clos_state_clock t4 + ck1)) t4) =
        (Rval a1,t6:(C,FFI)clos_state)` `ck2:num` THEN
    REWRITE_TAC[clos_evaluate_def; ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(SPECL [`ys:clos_exp list`; `s4:(C,FFI)clos_state`; `t4:(C,FFI)clos_state`;
                  `s5:(C,FFI)clos_state`; `Rerr err:(clos_v list,clos_v)result`]
                 opt_interp1_thm) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t6:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1:num`; `t6:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]]);;

(* HOL4: evaluate_insert_interp *)
let evaluate_insert_interp = prove
 (`!exps s4 s5 r t4.
     interp_assum (:C) (:FFI) (clos_state_clock s4) /\
     clos_evaluate (exps,[],s4) = (r,s5) /\ clos_interpProof_state_rel s4 t4 /\
     ~(r = Rerr (Rabort Rtype_error)) ==>
     ?ck (t5:(C,FFI)clos_state).
       clos_evaluate (insert_interp exps,[],
                      clos_state_clock_fupd (K (clos_state_clock t4 + ck)) t4) = (r,t5) /\
       clos_interpProof_state_rel s5 t5`,
  REWRITE_TAC[insert_interp_def] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; clos_evaluate_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t4:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MAP] THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[clos_evaluate_CONS] o check (fun th ->
    is_eq (concl th) &&
    rhs (concl th) = `(r:(clos_v list,clos_v)result, s5:(C,FFI)clos_state)`)) THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([h],[],s4:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
      check (fun th -> is_eq (concl th) &&
                       lhs (concl th) = `clos_evaluate ([h],[],s4:(C,FFI)clos_state)`)) THEN
    MP_TAC(INST [`h:clos_exp`,`e:clos_exp`; `s6:(C,FFI)clos_state`,`s5:(C,FFI)clos_state`;
                 `Rval [v1]:(clos_v list,clos_v)result`,`r:(clos_v list,clos_v)result`]
                evaluate_insert_interp1) THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t6:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    CLOSP2AUX_IP_LEQ_TAC `clos_evaluate ([h],[],s4:(C,FFI)clos_state) = (Rval [v1],s6)` THEN
    CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (t,[],s6:(C,FFI)clos_state)`
      `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THEN
    REWRITE_TAC[PAIR_EQ; HD] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IP_IH_TAC "IH" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`ck1 + ck2`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
    CLOSP2AUX_IP_LIFT_TAC `clos_evaluate ([insert_interp1 h],[],
        clos_state_clock_fupd (K (clos_state_clock t4 + ck1)) t4) =
        (Rval [v1],t6:(C,FFI)clos_state)` `ck2:num` THEN
    REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MP_TAC(INST [`h:clos_exp`,`e:clos_exp`;
                 `Rerr err:(clos_v list,clos_v)result`,`r:(clos_v list,clos_v)result`]
                evaluate_insert_interp1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `t6:(C,FFI)clos_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1:num`; `t6:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[]]);;

(* HOL4: state_rel_refs_clocks_eqs [local] *)
let state_rel_refs_clocks_eqs = prove
 (`clos_interpProof_state_rel (s1:(C,FFI)clos_state) s2 ==>
   clos_state_refs s1 = clos_state_refs s2 /\ clos_state_clock s1 = clos_state_clock s2`,
  SIMP_TAC[clos_interpProof_state_rel_def]);;

(* HOL4: state_rel_update_thunk [local] *)
let clos_interpProof_state_rel_update_thunk = prove
 (`clos_interpProof_state_rel (s1:(C,FFI)clos_state) s2 ==>
   clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 ==>
   ?refs2. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) vs = SOME refs2 /\
           clos_interpProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                      (clos_state_refs_fupd (K refs2) s2)`,
  DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP state_rel_refs_clocks_eqs) THEN
  DISCH_TAC THEN EXISTS_TAC `refs1:(num,(clos_v)clos_ref)fmap` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[clos_interpProof_state_rel_def] o check (fun th ->
    concl th = `clos_interpProof_state_rel (s1:(C,FFI)clos_state) s2`)) THEN
  REWRITE_TAC[clos_interpProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* local helpers for evaluate_interp_lemma.  interp_assum holds for every  *)
(* clock (CLOSP2AUX_il_interp_assum), by complete induction on the clock    *)
(* bound n; for a fixed n the simulation of the evaluations from states    *)
(* with clock at most n is proved by the induction of closProps on the     *)
(* source evaluation (CLOSP2AUX_il_ind), one lemma per case; the Install   *)
(* case uses evaluate_insert_interp with interp_assum of a smaller clock.  *)
(* The target is evaluated with an extra clock ck; a sub-evaluation is     *)
(* stepped over by splitting ck (CLOSP2AUX_il_shift, CLOSP2AUX_il_add)     *)

let CLOSP2AUX_il_P = `\xs env (s1:(C,FFI)clos_state).
   !t1 res s2.
     clos_state_clock s1 <= n /\ clos_evaluate (xs,env,s1) = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\ clos_interpProof_state_rel s1 t1 ==>
     ?ck t2. clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t1 + ck)) t1) =
             (res,t2) /\ clos_interpProof_state_rel s2 t2`;;

let CLOSP2AUX_il_Q = `\loc_opt f args (s1:(C,FFI)clos_state).
   !t1 res s2.
     clos_state_clock s1 <= n /\ evaluate_app loc_opt f args s1 = (res,s2) /\
     ~(res = Rerr (Rabort Rtype_error)) /\ clos_interpProof_state_rel s1 t1 ==>
     ?ck t2. evaluate_app loc_opt f args
               (clos_state_clock_fupd (K (clos_state_clock t1 + ck)) t1) = (res,t2) /\
             clos_interpProof_state_rel s2 t2`;;

let CLOSP2AUX_il_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [CLOSP2AUX_il_P; CLOSP2AUX_il_Q] CLOSPROPSAUX_evaluate_ind);;

let CLOSP2AUX_il_cases = conjuncts (lhand (concl CLOSP2AUX_il_ind));;

let CLOSP2AUX_il_add = prove
 (`!xs env (t:(C,FFI)clos_state) ck1 r u.
     clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t + ck1)) t) = (r,u) /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !ck2. clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t + ck1 + ck2)) t) =
           (r,clos_state_clock_fupd (K (clos_state_clock u + ck2)) u)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP clos_evaluate_add_clock) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; clos_state_INFO.ri_fupdfupds; K_o_THM; K_THM;
              ADD_ASSOC]);;

let CLOSP2AUX_il_add_app = prove
 (`!lo f args (t:(C,FFI)clos_state) ck1 r u.
     evaluate_app lo f args (clos_state_clock_fupd (K (clos_state_clock t + ck1)) t) = (r,u) /\
     ~(r = Rerr (Rabort Rtimeout_error)) ==>
     !ck2. evaluate_app lo f args
             (clos_state_clock_fupd (K (clos_state_clock t + ck1 + ck2)) t) =
           (r,clos_state_clock_fupd (K (clos_state_clock u + ck2)) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC(SPECL [`lo:num option`; `f:clos_v`; `args:clos_v list`;
    `clos_state_clock_fupd (K (clos_state_clock (t:(C,FFI)clos_state) + ck1)) t`;
    `r:(clos_v list,clos_v)result`; `u:(C,FFI)clos_state`; `ck2:num`]
    (CONJUNCT2 CLOSPROPSAUX_evaluate_add_to_clock)) THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; clos_state_INFO.ri_fupdfupds; K_o_THM; K_THM;
                  ADD_ASSOC]);;

let CLOSP2AUX_il_shift = prove
 (`!ck1 (P:num->bool). (?ck. P (ck1 + ck)) ==> (?ck. P ck)`,
  MESON_TAC[]);;

let CLOSP2AUX_il_disch_shift = prove
 (`!ck1 A (P:num->bool). (A ==> ?ck. P (ck1 + ck)) ==> (A ==> ?ck. P ck)`,
  MESON_TAC[]);;

(* the tactics of the case lemmas                                           *)
(*   IL_CLOCK_TAC ev   the clock bound n for the result state of ev          *)
(*   IL_IH_TAC lab vs  resolve the labelled induction hypothesis with the    *)
(*                     assumptions; vs name the target clock and state       *)
(*   IL_SHIFT_TAC ev   step the target of the goal past the target           *)
(*                     evaluation ev (an assumption) that does not time out  *)
(*   IL_FIN_TAC t      finish with no extra clock and the target state t     *)
let CLOSP2AUX_IL_CLOCK_TAC (ev:term) : tactic = fun (asl,w as g) ->
  let th = find (fun th -> concl th = ev) (map snd asl) in
  let le = MATCH_MP (if is_comb (lhs ev) &&
                        (try fst(dest_const(fst(strip_comb(lhs ev)))) = "evaluate_app"
                         with Failure _ -> false)
                     then CONJUNCT2 clos_evaluate_clock else CONJUNCT1 clos_evaluate_clock) th in
  let s1 = rand (rand (concl le)) in
  let bnd = find (fun th -> let c = concl th in is_binary "<=" c &&
                    lhand c = mk_comb(`clos_state_clock:(C,FFI)clos_state->num`, s1))
                 (map snd asl) in
  ASSUME_TAC (MATCH_MP LE_TRANS (CONJ le bnd)) g;;

let CLOSP2AUX_IL_IH_TAC (lab:string) (names:term list) : tactic = fun (asl,w as g) ->
  let ih = assoc lab asl in
  let nrm = REWRITE_RULE[distinctness "result"; injectivity "result";
                         distinctness "error_result"] in
  let asms0 = map snd asl in
  let asms = asms0 @ mapfilter (fun th -> let th' = nrm th in
                                  if concl th' = concl th then failwith "same" else th') asms0 in
  let rec resolve depth th =
    let c = snd (strip_forall (concl th)) in
    if not (is_imp c) then [th] else if depth = 0 then [] else
    let rs = mapfilter (fun a -> nrm (MATCH_MP th a)) asms in
    flat (map (resolve (depth-1)) rs) in
  match resolve 9 (REWRITE_RULE[IMP_CONJ] ih) with
    th::_ -> (itlist (fun v ttac -> X_CHOOSE_THEN v ttac) names STRIP_ASSUME_TAC) th g
  | [] -> failwith ("CLOSP2AUX_IL_IH_TAC "^lab);;

let CLOSP2AUX_IL_SHIFT_TAC (ev:term) : tactic = fun (asl,w as g) ->
  let th = find (fun th -> concl th = ev) (map snd asl) in
  let st = (try rand (rand (rand (lhs ev))) with Failure _ -> lhs ev) in
  let isapp = (try fst(dest_const(fst(strip_comb(lhs ev)))) = "evaluate_app"
               with Failure _ -> false) in
  let st = if isapp then rand (lhs ev) else st in
  let k = rand (rand (rand (rator st))) in
  let r = fst (dest_pair (rhs ev)) in
  let nt = EQT_ELIM (REWRITE_CONV[distinctness "result"; injectivity "result";
                                  distinctness "error_result"; injectivity "error_result";
                                  distinctness "abort"]
             (mk_neg (mk_eq (r, `Rerr (Rabort Rtimeout_error):(clos_v list,clos_v)result`)))) in
  let add = MATCH_MP (if isapp then CLOSP2AUX_il_add_app else CLOSP2AUX_il_add) (CONJ th nt) in
  let sh = if is_imp w then CLOSP2AUX_il_disch_shift else CLOSP2AUX_il_shift in
  (MATCH_MP_TAC (SPEC k sh) THEN REWRITE_TAC[add] THEN
   TRY(CASE_REWRITE_TAC[])) g;;

let CLOSP2AUX_IL_FIN_TAC (t:term) : tactic =
  MAP_EVERY EXISTS_TAC [`0`; t] THEN
  REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN ASM_REWRITE_TAC[] THEN
  TRY(CASE_REWRITE_TAC[]);;

let CLOSP2AUX_il_state_rel_eqs = prove
 (`!(s:(C,FFI)clos_state) t. clos_interpProof_state_rel s t ==>
     clos_state_max_app t = clos_state_max_app s /\ clos_state_clock t = clos_state_clock s /\
     clos_state_globals t = clos_state_globals s /\ clos_state_refs t = clos_state_refs s /\
     clos_state_ffi t = clos_state_ffi s /\ clos_state_code t = clos_state_code s`,
  SIMP_TAC[clos_interpProof_state_rel_def]);;

(* the source evaluation equation of a case, moved to the goal *)
let CLOSP2AUX_IL_SRC_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res:(clos_v list,clos_v)result, s2:(C,FFI)clos_state)`));;

(* the cases without sub-evaluations: the target state is t1 *)
let CLOSP2AUX_IL_LEAF_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_il_state_rel_eqs) THEN
  CLOSP2AUX_IL_FIN_TAC `t1:(C,FFI)clos_state` THEN
  CLOSP2AUX_IL_SRC_TAC THEN
  REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ]) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[];;

let CLOSP2AUX_il_nil = prove
 (el 0 CLOSP2AUX_il_cases,
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  CLOSP2AUX_IL_FIN_TAC `t1:(C,FFI)clos_state` THEN REWRITE_TAC[clos_evaluate_def]);;

let CLOSP2AUX_il_Var = prove (el 2 CLOSP2AUX_il_cases, CLOSP2AUX_IL_LEAF_TAC);;

let CLOSP2AUX_il_Fn = prove (el 8 CLOSP2AUX_il_cases, CLOSP2AUX_IL_LEAF_TAC);;

(* an error result of a sub-evaluation that is the result of the case *)
let CLOSP2AUX_IL_ERR_TAC (lab:string) : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CLOSP2AUX_IL_IH_TAC lab [`cke:num`; `te:(C,FFI)clos_state`] THEN
  MAP_EVERY EXISTS_TAC [`cke:num`; `te:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
  TRY(CASE_REWRITE_TAC[]);;

let CLOSP2AUX_il_Raise = prove
 (el 5 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THEN
  CLOSP2AUX_IL_ERR_TAC "IH1");;

let CLOSP2AUX_il_CONS = prove
 (el 1 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x],env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IL_CLOCK_TAC `clos_evaluate ([x],env,s:(C,FFI)clos_state) = (Rval a1,s6)` THEN
    CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate ([x],env,
        clos_state_clock_fupd (K (clos_state_clock t1 + ck1)) t1) =
        (Rval a1,t6:(C,FFI)clos_state)` THEN
    CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (CONS y xs,env,s6:(C,FFI)clos_state)`
      `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
     [CLOSP2AUX_IL_IH_TAC "IH2" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
      CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate (CONS y xs,env,
          clos_state_clock_fupd (K (clos_state_clock t6 + ck2)) t6) =
          (Rval a2,t7:(C,FFI)clos_state)` THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      CLOSP2AUX_IL_FIN_TAC `t7:(C,FFI)clos_state`;
      CLOSP2AUX_IL_ERR_TAC "IH2"];
    CLOSP2AUX_IL_ERR_TAC "IH1"]);;

let CLOSP2AUX_il_If = prove
 (el 3 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1")
    (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH3"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IL_CLOCK_TAC `clos_evaluate ([x1],env,s:(C,FFI)clos_state) = (Rval a1,s6)` THEN
    CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate ([x1],env,
        clos_state_clock_fupd (K (clos_state_clock t1 + ck1)) t1) =
        (Rval a1,t6:(C,FFI)clos_state)` THEN
    COND_CASES_TAC THENL
     [DISCH_TAC THEN CLOSP2AUX_IL_IH_TAC "IH2" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
      MAP_EVERY EXISTS_TAC [`ck2:num`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[];
      COND_CASES_TAC THENL
       [DISCH_TAC THEN CLOSP2AUX_IL_IH_TAC "IH3" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
        MAP_EVERY EXISTS_TAC [`ck2:num`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC]];
    CLOSP2AUX_IL_ERR_TAC "IH1"]);;

let CLOSP2AUX_il_Let = prove
 (el 4 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IL_CLOCK_TAC `clos_evaluate (xs,env,s:(C,FFI)clos_state) = (Rval a1,s6)` THEN
    CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate (xs,env,
        clos_state_clock_fupd (K (clos_state_clock t1 + ck1)) t1) =
        (Rval a1,t6:(C,FFI)clos_state)` THEN
    DISCH_TAC THEN CLOSP2AUX_IL_IH_TAC "IH2" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`ck2:num`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[];
    CLOSP2AUX_IL_ERR_TAC "IH1"]);;

let CLOSP2AUX_il_Handle = prove
 (el 6 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s1:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_IL_ERR_TAC "IH1"; ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)
    (ISPEC `err:(clos_v)error_result` (cases "error_result")) THEN
  CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IL_CLOCK_TAC
      `clos_evaluate ([x1],env,s1:(C,FFI)clos_state) = (Rerr (Rraise v1),s6)` THEN
    CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate ([x1],env,
        clos_state_clock_fupd (K (clos_state_clock t1 + ck1)) t1) =
        (Rerr (Rraise v1),t6:(C,FFI)clos_state)` THEN
    DISCH_TAC THEN CLOSP2AUX_IL_IH_TAC "IH2" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`ck2:num`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[];
    CLOSP2AUX_IL_ERR_TAC "IH1"]);;

let CLOSP2AUX_il_Letrec = prove
 (el 9 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP CLOSP2AUX_il_state_rel_eqs) THEN
  CLOSP2AUX_IL_SRC_TAC THEN
  REWRITE_TAC[clos_evaluate_def; clos_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC THEN NO_TAC) THEN
  DISCH_TAC THEN CLOSP2AUX_IL_IH_TAC "IH1" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
  MAP_EVERY EXISTS_TAC [`ck2:num`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_il_Tick = prove
 (el 11 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_ip_state_rel_clock) THEN
  CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) = 0` THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t1:(C,FFI)clos_state`] THEN
    REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `m:num` ASSUME_TAC o
    REWRITE_RULE[GSYM CLOSP2AUX_ip_nonzero_SUC] o check (is_neg o concl)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `clos_state_clock (clos_dec_clock 1 (s:(C,FFI)clos_state)) <= n` ASSUME_TAC THENL
   [REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `clos_interpProof_state_rel (clos_dec_clock 1 (s:(C,FFI)clos_state))
                  (clos_dec_clock 1 (t1:(C,FFI)clos_state))` ASSUME_TAC THENL
   [REWRITE_TAC[clos_dec_clock_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
  MAP_EVERY EXISTS_TAC [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
  SUBGOAL_THEN `clos_state_clock (t1:(C,FFI)clos_state) = SUC m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res:(clos_v list,clos_v)result, t6:(C,FFI)clos_state)`)) THEN
  ASM_REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds;
                  clos_state_INFO.ri_fupdfupds; K_o_THM; K_THM; NOT_SUC; ADD_EQ_0; SUC_SUB1;
                  ARITH_RULE `(SUC m + ck1) - 1 = m + ck1`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_il_Call = prove
 (el 12 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,env,s1:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = `clos_interpProof_state_rel s6 (t6:(C,FFI)clos_state)`)) THEN
    REWRITE_TAC[clos_interpProof_state_rel_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_find_code_def; FLOOKUP_EMPTY] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    CLOSP2AUX_IL_ERR_TAC "IH1"]);;

let CLOSP2AUX_il_App = prove
 (el 10 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH3")
    (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  ASM_CASES_TAC `LENGTH (args:clos_exp list) > 0` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (args,env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IL_CLOCK_TAC `clos_evaluate (args,env,s:(C,FFI)clos_state) = (Rval a1,s6)` THEN
    CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate (args,env,
        clos_state_clock_fupd (K (clos_state_clock t1 + ck1)) t1) =
        (Rval a1,t6:(C,FFI)clos_state)` THEN
    CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s6:(C,FFI)clos_state)`
      `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
     [CLOSP2AUX_IL_IH_TAC "IH2" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
      CLOSP2AUX_IL_CLOCK_TAC `clos_evaluate ([x1],env,s6:(C,FFI)clos_state) = (Rval a2,s7)` THEN
      CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate ([x1],env,
          clos_state_clock_fupd (K (clos_state_clock t6 + ck2)) t6) =
          (Rval a2,t7:(C,FFI)clos_state)` THEN
      DISCH_TAC THEN CLOSP2AUX_IL_IH_TAC "IH3" [`ck3:num`; `t8:(C,FFI)clos_state`] THEN
      MAP_EVERY EXISTS_TAC [`ck3:num`; `t8:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[];
      CLOSP2AUX_IL_ERR_TAC "IH2"];
    CLOSP2AUX_IL_ERR_TAC "IH1"]);;

let CLOSP2AUX_il_app_nil = prove (el 13 CLOSP2AUX_il_cases, CLOSP2AUX_IL_LEAF_TAC);;

let CLOSP2AUX_il_dec_shift = prove
 (`!(t:(C,FFI)clos_state) m ck. m <= clos_state_clock t ==>
     clos_dec_clock m (clos_state_clock_fupd (K (clos_state_clock t + ck)) t) =
     clos_state_clock_fupd (K (clos_state_clock (clos_dec_clock m t) + ck)) (clos_dec_clock m t)`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; clos_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* the timeout and clock decrement results of evaluate_app: no extra clock *)
let CLOSP2AUX_IL_APP_LEAF_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
  ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1;
                  clos_dec_clock_def; clos_state_INFO.ri_fupdfupds; K_o_THM];;

let CLOSP2AUX_il_app_cons = prove
 (el 14 CLOSP2AUX_il_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP CLOSP2AUX_il_state_rel_eqs) THEN
  CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `clos_state_max_app (t1:(C,FFI)clos_state)`) th]) THEN
  DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
    (X_CHOOSE_THEN `ak:app_kind` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))
    (ISPEC `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) loc_opt f (CONS v4 v5)`
       (cases "option")) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `pv:clos_v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `fe:clos_exp` (X_CHOOSE_THEN `fenv:clos_v list`
      (X_CHOOSE_THEN `rest:clos_v list` SUBST_ALL_TAC)))
    (ISPEC `ak:app_kind` (cases "app_kind")) THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLOSP2AUX_ip_state_rel_clock) THENL
   [COND_CASES_TAC THEN CLOSP2AUX_IL_APP_LEAF_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [CLOSP2AUX_IL_APP_LEAF_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!ck. ~(clos_state_clock (t1:(C,FFI)clos_state) + ck <
                      LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list))`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list) <=
                clos_state_clock (t1:(C,FFI)clos_state)`
    (fun th -> REWRITE_TAC[MATCH_MP CLOSP2AUX_il_dec_shift th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `clos_state_clock (clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) -
                  LENGTH (rest:clos_v list)) (s:(C,FFI)clos_state)) <= n` ASSUME_TAC THENL
   [REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `clos_interpProof_state_rel
     (clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list))
        (s:(C,FFI)clos_state))
     (clos_dec_clock (LENGTH (CONS v4 v5) - LENGTH rest) (t1:(C,FFI)clos_state))`
    ASSUME_TAC THENL
   [REWRITE_TAC[clos_dec_clock_def] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_state_clock (t1:(C,FFI)clos_state)`) th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([fe:clos_exp],fenv:clos_v list,
      clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list))
      (s:(C,FFI)clos_state))`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_IL_ERR_TAC "IH2"] THEN
  CLOSP2AUX_IL_IH_TAC "IH2" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
  CLOSP2AUX_IL_CLOCK_TAC `clos_evaluate ([fe:clos_exp],fenv:clos_v list,
      clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list))
      (s:(C,FFI)clos_state)) = (Rval a1,s6)` THEN
  CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate ([fe:clos_exp],fenv:clos_v list,
      clos_state_clock_fupd (K (clos_state_clock (clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) -
        LENGTH (rest:clos_v list)) (t1:(C,FFI)clos_state)) + ck1))
      (clos_dec_clock (LENGTH (CONS v4 v5) - LENGTH rest) t1)) = (Rval a1,t6)` THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `v:clos_v` (X_CHOOSE_THEN `a2:clos_v list` SUBST_ALL_TAC))
    (ISPEC `a1:clos_v list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IL_FIN_TAC `t6:(C,FFI)clos_state`;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `v':clos_v` (X_CHOOSE_THEN `a3:clos_v list` SUBST_ALL_TAC))
    (ISPEC `a2:clos_v list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN CLOSP2AUX_IL_IH_TAC "IH1" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`ck2:num`; `t7:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IL_FIN_TAC `t6:(C,FFI)clos_state`]);;
let CLOSP2AUX_il_simple_val_rel = prove
 (`clos_simple_val_rel (\v1 v2:clos_v. v1 = v2)`,
  REWRITE_TAC[clos_simple_val_rel_def; LIST_REL_eq'] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY EQ_TAC THEN
  SIMP_TAC[clos_isClos_def] THEN MESON_TAC[]);;
let CLOSP2AUX_il_simple_state_rel = prove
 (`clos_simple_state_rel (\v1 v2:clos_v. v1 = v2) (state_rel_1:(C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  REWRITE_TAC[clos_simple_state_rel_def; state_rel_1_def; LIST_REL_eq'; OPTREL_eq'] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;
let CLOSP2AUX_il_exc_rel_eq = prove
 (`!e1 e2:(clos_v)error_result. exc_rel (\v1 v2:clos_v. v1 = v2) e1 e2 <=> e1 = e2`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `e1:(clos_v)error_result` (cases "error_result")) THEN
  STRUCT_CASES_TAC (ISPEC `e2:(clos_v)error_result` (cases "error_result")) THEN
  REWRITE_TAC[exc_rel_def; injectivity "error_result"; distinctness "error_result"]);;
let CLOSP2AUX_il_do_app = prove
 (`!op vs (s:(C,FFI)clos_state) t.
     clos_interpProof_state_rel s t ==>
     (!v s'. clos_do_app op vs s = Rval (v,s') ==>
             ?t'. clos_do_app op vs t = Rval (v,t') /\ clos_interpProof_state_rel s' t') /\
     (!e. clos_do_app op vs s = Rerr e ==> clos_do_app op vs t = Rerr e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `state_rel_1 (s:(C,FFI)clos_state) t` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[clos_interpProof_state_rel_def; state_rel_1_def] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v1 v2:clos_v. v1 = v2`;
                 `state_rel_1:(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `vs:clos_v list`;
                 `vs:clos_v list`; `op:clos_op`] simple_val_rel_do_app) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_il_simple_val_rel; CLOSP2AUX_il_simple_state_rel; LIST_REL_eq'] THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `p:clos_v#(C,FFI)clos_state` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (X_CHOOSE_THEN `e0:(clos_v)error_result` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC `clos_do_app op vs (s:(C,FFI)clos_state)` (cases "result")) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; CLOSP2AUX_il_exc_rel_eq] THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MP_TAC(ISPEC `p:clos_v#(C,FFI)clos_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:clos_v` (X_CHOOSE_THEN `s0:(C,FFI)clos_state` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:clos_v` (X_CHOOSE_THEN `t0:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `t0:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `oHD (clos_state_globals (s':(C,FFI)clos_state)) =
                SOME (SOME (clos_Closure NONE [] [] 1 clos_interpreter))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP do_app_oHD_globals o check (fun th ->
      concl th = `clos_do_app op vs s = Rval (y,s':(C,FFI)clos_state)`)) THEN
    UNDISCH_TAC `clos_interpProof_state_rel (s:(C,FFI)clos_state) t` THEN
    SIMP_TAC[clos_interpProof_state_rel_def];
    ALL_TAC] THEN
  UNDISCH_TAC `state_rel_1 (s':(C,FFI)clos_state) t0` THEN
  REWRITE_TAC[clos_interpProof_state_rel_def; state_rel_1_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
(* the Install case: the target installs the code of the source with the  *)
(* interpreter inserted                                                     *)
let CLOSP2AUX_il_install_state = prove
 (`!(s:(C,FFI)clos_state) t.
     clos_interpProof_state_rel s t ==>
     clos_interpProof_state_rel
       (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s)))
          (clos_state_clock_fupd (K (clos_state_clock s - 1)) s))
       (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t)))
          (clos_state_clock_fupd (K (clos_state_clock t - 1)) t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_interpProof_state_rel_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; shift_seq_def] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let CLOSP2AUX_il_oracle0 = prove
 (`!(s:(C,FFI)clos_state) t k.
     clos_interpProof_state_rel s t ==>
     clos_state_compile_oracle (clos_state_clock_fupd (K k) t) 0 =
       (FST (clos_state_compile_oracle s 0),
        insert_interp (FST (SND (clos_state_compile_oracle s 0))), []) /\
     clos_state_compile_oracle s 0 =
       (FST (clos_state_compile_oracle s 0), FST (SND (clos_state_compile_oracle s 0)), []) /\
     FST (clos_state_compile_oracle (clos_state_clock_fupd (K k) t) 1) =
       FST (clos_state_compile_oracle s 1) /\
     (!cfg p. clos_state_compile (clos_state_clock_fupd (K k) t) cfg (insert_interp p,[]) =
              clos_state_compile s cfg (p,[]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_interpProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; o_THM; pure_co_def; pure_cc_def; PAIR_MAP;
                  I_THM; LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
  SPEC_TAC(`clos_state_compile_oracle (s:(C,FFI)clos_state) 0`,`q:C # clos_exp list # (num # num # clos_exp) list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND; PAIR_MAP; I_THM] THEN SIMP_TAC[]);;

let CLOSP2AUX_il_insert_interp_nil = prove
 (`!p. insert_interp p = [] <=> p = []`,
  REWRITE_TAC[insert_interp_def; MAP_EQ_NIL]);;

(* do_install on the target with the clock k, from do_install on the source *)
let CLOSP2AUX_il_do_install = prove
 (CASE_TERM `!vs (s:(C,FFI)clos_state) t k.
     clos_interpProof_state_rel s t ==>
     clos_do_install vs (clos_state_clock_fupd (K k) t) =
     (match clos_do_install vs (clos_state_clock_fupd (K k) s) with
        (Rval es,s1) ->
          (Rval (insert_interp es),
           clos_state_compile_oracle_fupd
             (K (shift_seq 1 (clos_state_compile_oracle t)))
             (clos_state_clock_fupd (K (k - 1)) t))
      | (Rerr e,s1) ->
          (Rerr e,
           if e = Rabort Rtype_error then clos_state_clock_fupd (K k) t
           else clos_state_compile_oracle_fupd
                  (K (shift_seq 1 (clos_state_compile_oracle t)))
                  (clos_state_clock_fupd (K (k - 1)) t)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `?v1 v2:clos_v. vs = [v1; v2]` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_SIMP_TAC[CLOSPROPSAUX_do_install_not2] THEN CASE_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v1:clos_v` (X_CHOOSE_THEN `v2:clos_v` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o MATCH_MP CLOSP2AUX_il_oracle0) THEN
  MP_TAC(SPECL [`v1:clos_v`; `v2:clos_v`; `clos_state_clock_fupd (K k) (s:(C,FFI)clos_state)`;
                `FST (clos_state_compile_oracle (s:(C,FFI)clos_state) 0)`;
                `FST (SND (clos_state_compile_oracle (s:(C,FFI)clos_state) 0))`]
    CLOSPROPSAUX_do_install_char) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`v1:clos_v`; `v2:clos_v`; `clos_state_clock_fupd (K k) (t:(C,FFI)clos_state)`;
                `FST (clos_state_compile_oracle (s:(C,FFI)clos_state) 0)`;
                `insert_interp (FST (SND (clos_state_compile_oracle (s:(C,FFI)clos_state) 0)))`]
    CLOSPROPSAUX_do_install_char) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) then REWRITE_TAC[th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "FST" with Failure _ -> false)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; clos_state_INFO.ri_fupdfupds; K_o_THM;
              CLOSP2AUX_il_insert_interp_nil] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "error_result"; distinctness "error_result"; distinctness "abort"] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "error_result"; distinctness "error_result"; distinctness "abort";
              PAIR_EQ; clos_state_INFO.ri_fupdfupds; K_o_THM]);;

let CLOSP2AUX_il_do_install_state = prove
 (`!vs (s:(C,FFI)clos_state) r s'.
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     clos_do_install vs s = (r,s') /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     s' = clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s)))
            (clos_state_clock_fupd (K (clos_state_clock s - 1)) s) /\
     (r = Rerr (Rabort Rtimeout_error) <=> clos_state_clock s = 0) /\
     (!e. r = Rerr e ==> e = Rabort Rtimeout_error)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?v1 v2:clos_v. vs = [v1; v2]` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC `clos_do_install vs (s:(C,FFI)clos_state) = (r,s')` THEN
    ASM_SIMP_TAC[CLOSPROPSAUX_do_install_not2; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v1:clos_v` (X_CHOOSE_THEN `v2:clos_v` SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `clos_state_compile_oracle (s:(C,FFI)clos_state) 0 =
     (FST (clos_state_compile_oracle s 0), FST (SND (clos_state_compile_oracle s 0)), [])`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
    SPEC_TAC(`clos_state_compile_oracle (s:(C,FFI)clos_state) 0`,
             `q:C # clos_exp list # (num # num # clos_exp) list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `clos_do_install [v1; v2] (s:(C,FFI)clos_state) = (r,s')` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSPROPSAUX_do_install_char th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [ALL_TAC; RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; injectivity "error_result"] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let CLOSP2AUX_il_install_clock = prove
 (`!(t:(C,FFI)clos_state) o1 ck.
     1 <= clos_state_clock t ==>
     clos_state_compile_oracle_fupd (K o1)
       (clos_state_clock_fupd (K ((clos_state_clock t + ck) - 1)) t) =
     clos_state_clock_fupd
       (K (clos_state_clock (clos_state_compile_oracle_fupd (K o1)
             (clos_state_clock_fupd (K (clos_state_clock t - 1)) t)) + ck))
       (clos_state_compile_oracle_fupd (K o1)
          (clos_state_clock_fupd (K (clos_state_clock t - 1)) t))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[clos_state_component_equality; clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

let CLOSP2AUX_il_state_rel_refs = prove
 (`!(s:(C,FFI)clos_state) t r.
     clos_interpProof_state_rel s t ==>
     clos_interpProof_state_rel (clos_state_refs_fupd (K r) s) (clos_state_refs_fupd (K r) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_interpProof_state_rel_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM]);;

let CLOSP2AUX_IL_REFS_TAC (s:term) (t:term) : tactic =
  FIRST_ASSUM(fun th -> REWRITE_TAC[SYM(CONJUNCT1(MATCH_MP state_rel_refs_clocks_eqs
    (check (fun th -> concl th =
      mk_comb(mk_comb(`clos_interpProof_state_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`,
                      s),t)) th)))]);;

let CLOSP2AUX_IL_S6T6 =
  check (fun th -> concl th = `clos_interpProof_state_rel s6 (t6:(C,FFI)clos_state)`);;

(* the Op case: an operation other than Install and ForceThunk *)
let CLOSP2AUX_IL_OP_APP_TAC : tactic =
  REWRITE_TAC[ASSUME `~(op = clos_Install)`; ASSUME `~(op = clos_ThunkOp ForceThunk)`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPECL [`op:clos_op`; `REVERSE a1:clos_v list`] o
    MATCH_MP CLOSP2AUX_il_do_app o CLOSP2AUX_IL_S6T6) THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `p:clos_v#(C,FFI)clos_state` ASSUME_TAC)
    (X_CHOOSE_THEN `e0:(clos_v)error_result` ASSUME_TAC)
    (ISPEC `clos_do_app op (REVERSE a1) (s6:(C,FFI)clos_state)` (cases "result")) THENL
   [MP_TAC(ISPEC `p:clos_v#(C,FFI)clos_state` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v0:clos_v` (X_CHOOSE_THEN `s7:(C,FFI)clos_state` SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 2
      then MP_TAC (MATCH_MP th
        (ASSUME `clos_do_app op (REVERSE a1) (s6:(C,FFI)clos_state) = Rval (v0,s7)`))
      else NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t7:(C,FFI)clos_state` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IL_FIN_TAC `t7:(C,FFI)clos_state`;
    FIRST_X_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 1
      then ASSUME_TAC (MATCH_MP th
        (ASSUME `clos_do_app op (REVERSE a1) (s6:(C,FFI)clos_state) = Rerr e0`))
      else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    CLOSP2AUX_IL_FIN_TAC `t6:(C,FFI)clos_state`];;

(* the Op case: ForceThunk *)
let CLOSP2AUX_IL_OP_FORCE_TAC : tactic =
  REWRITE_TAC[ASSUME `~(op = clos_Install)`; ASSUME `op = clos_ThunkOp ForceThunk`] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
  CLOSP2AUX_IL_REFS_TAC `s6:(C,FFI)clos_state` `t6:(C,FFI)clos_state` THEN
  DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
    (DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
      (X_CHOOSE_THEN `tm:thunk_mode` (X_CHOOSE_THEN `v:clos_v`
         (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))))
    (ISPEC `clos_dest_thunk a1 (clos_state_refs (s6:(C,FFI)clos_state))`
       (cases "clos_dest_thunk_ret")) THEN
  CASE_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_ASSUM CONTR_TAC;
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC (ISPEC `tm:thunk_mode` (cases "thunk_mode")) THEN
  CASE_REWRITE_TAC[] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN CLOSP2AUX_IL_FIN_TAC `t6:(C,FFI)clos_state`; ALL_TAC] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[v],
      s6:(C,FFI)clos_state)` `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_IL_IH_TAC "IHF" [`ck2:num`; `t7:(C,FFI)clos_state`] THEN
    CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[v],
      clos_state_clock_fupd (K (clos_state_clock t6 + ck2)) t6) =
      (Rval a2,t7:(C,FFI)clos_state)` THEN
    REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN
    CLOSP2AUX_IL_REFS_TAC `s7:(C,FFI)clos_state` `t7:(C,FFI)clos_state` THEN
    DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
      (X_CHOOSE_THEN `rf:(num,(clos_v)clos_ref)fmap` (fun th -> REWRITE_TAC[th]))
      (ISPEC `clos_update_thunk a1 (clos_state_refs (s7:(C,FFI)clos_state)) a2`
         (cases "option")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
    EXISTS_TAC `clos_state_refs_fupd (K rf) (t7:(C,FFI)clos_state)` THEN
    ASM_SIMP_TAC[CLOSP2AUX_il_state_rel_refs];
    CLOSP2AUX_IL_ERR_TAC "IHF"];;

(* the Op case: Install *)
let CLOSP2AUX_IL_OP_INSTALL_TAC : tactic =
  REWRITE_TAC[ASSUME `op = clos_Install`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSP2AUX_il_do_install (CLOSP2AUX_IL_S6T6 th)]) THEN
  SUBGOAL_THEN `!ck. clos_state_clock_fupd (K (clos_state_clock (t6:(C,FFI)clos_state) + ck))
                       (s6:(C,FFI)clos_state) =
                     clos_state_clock_fupd (K (clos_state_clock s6 + ck)) s6`
    (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1 (MATCH_MP CLOSP2AUX_ip_state_rel_clock
      (CLOSP2AUX_IL_S6T6 th))]);
    ALL_TAC] THEN
  MP_TAC(ISPEC `clos_do_install (REVERSE a1) (s6:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r7:(clos_exp list,clos_v)result`
    (X_CHOOSE_THEN `s7:(C,FFI)clos_state` ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. SND (SND (clos_state_compile_oracle (s6:(C,FFI)clos_state) n)) = []`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CLOSP2AUX_IL_S6T6) THEN SIMP_TAC[clos_interpProof_state_rel_def];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `es:clos_exp list` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `e7:(clos_v)error_result` SUBST_ALL_TAC)
    (ISPEC `r7:(clos_exp list,clos_v)result` (cases "result")) THEN
  CASE_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`REVERSE a1:clos_v list`; `s6:(C,FFI)clos_state`;
                  `Rval es:(clos_exp list,clos_v)result`; `s7:(C,FFI)clos_state`]
      CLOSP2AUX_il_do_install_state);
    MP_TAC(SPECL [`REVERSE a1:clos_v list`; `s6:(C,FFI)clos_state`;
                  `Rerr e7:(clos_exp list,clos_v)result`; `s7:(C,FFI)clos_state`]
      CLOSP2AUX_il_do_install_state)] THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP do_install_add_to_clock (check (fun th ->
      concl th = `clos_do_install (REVERSE a1) s6 = (Rval es,s7:(C,FFI)clos_state)`) th)]) THEN
    CASE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= clos_state_clock (t6:(C,FFI)clos_state)` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1 (MATCH_MP CLOSP2AUX_ip_state_rel_clock
        (CLOSP2AUX_IL_S6T6 th))]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSP2AUX_il_install_clock (check (fun th ->
      concl th = `1 <= clos_state_clock (t6:(C,FFI)clos_state)`) th)]) THEN
    SUBGOAL_THEN `interp_assum (:C) (:FFI) (clos_state_clock (s7:(C,FFI)clos_state))`
      ASSUME_TAC THENL
     [USE_THEN "OUT" MATCH_MP_TAC THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `s7:(C,FFI)clos_state`) th]) THEN
      REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `clos_interpProof_state_rel (s7:(C,FFI)clos_state)
       (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle t6)))
          (clos_state_clock_fupd (K (clos_state_clock t6 - 1)) (t6:(C,FFI)clos_state)))`
      ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `s7:(C,FFI)clos_state`) th]) THEN
      MATCH_MP_TAC CLOSP2AUX_il_install_state THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (es,[],s7:(C,FFI)clos_state)`
      `a3:clos_v list` `s8:(C,FFI)clos_state` `e8:(clos_v)error_result` THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    LABEL_TAC "EII" evaluate_insert_interp THEN
    CLOSP2AUX_IL_IH_TAC "EII" [`ck2:num`; `t8:(C,FFI)clos_state`] THEN
    MAP_EVERY EXISTS_TAC [`ck2:num`; `t8:(C,FFI)clos_state`] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[];
    ASM_CASES_TAC `e7 = Rabort Rtype_error:(clos_v)error_result` THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `e7:(clos_v)error_result`))) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `clos_do_install (REVERSE a1) (s6:(C,FFI)clos_state)`) th]) THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "abort"; injectivity "error_result"; PAIR_EQ] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    MATCH_MP_TAC CLOSP2AUX_il_install_state THEN FIRST_ASSUM ACCEPT_TAC];;

let CLOSP2AUX_il_Op = prove
 (mk_imp(`!m. m < n ==> interp_assum (:C) (:FFI) m`, el 7 CLOSP2AUX_il_cases),
  DISCH_THEN(LABEL_TAC "OUT") THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHI")
    (CONJUNCTS_THEN2 (LABEL_TAC "IHF") (LABEL_TAC "IH1"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_IL_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_IL_ERR_TAC "IH1"] THEN
  CLOSP2AUX_IL_IH_TAC "IH1" [`ck1:num`; `t6:(C,FFI)clos_state`] THEN
  CLOSP2AUX_IL_CLOCK_TAC `clos_evaluate (xs,env,s:(C,FFI)clos_state) = (Rval a1,s6)` THEN
  CLOSP2AUX_IL_SHIFT_TAC `clos_evaluate (xs,env,
      clos_state_clock_fupd (K (clos_state_clock t1 + ck1)) t1) =
      (Rval a1,t6:(C,FFI)clos_state)` THEN
  ASM_CASES_TAC `op = clos_Install` THENL
   [CLOSP2AUX_IL_OP_INSTALL_TAC;
    ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THENL
     [CLOSP2AUX_IL_OP_FORCE_TAC; CLOSP2AUX_IL_OP_APP_TAC]]);;

(* interp_assum holds for every clock *)
let CLOSP2AUX_il_interp_assum = prove
 (`!n. interp_assum (:C) (:FFI) n`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(MP CLOSP2AUX_il_ind (end_itlist CONJ
    [CLOSP2AUX_il_nil; CLOSP2AUX_il_CONS; CLOSP2AUX_il_Var; CLOSP2AUX_il_If;
     CLOSP2AUX_il_Let; CLOSP2AUX_il_Raise; CLOSP2AUX_il_Handle;
     MP CLOSP2AUX_il_Op (ASSUME `!m. m < n ==> interp_assum (:C) (:FFI) m`);
     CLOSP2AUX_il_Fn; CLOSP2AUX_il_Letrec; CLOSP2AUX_il_App; CLOSP2AUX_il_Tick;
     CLOSP2AUX_il_Call; CLOSP2AUX_il_app_nil; CLOSP2AUX_il_app_cons])) THEN
  STRIP_TAC THEN REWRITE_TAC[interp_assum_def] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `s1:(C,FFI)clos_state` THEN
                          ASM_REWRITE_TAC[]));;

(* HOL4: evaluate_interp_lemma *)
let evaluate_interp_lemma = prove
 (`(!xs (s1:(C,FFI)clos_state) env t1 res s2.
      clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      clos_interpProof_state_rel s1 t1 ==>
      ?ck t2.
        clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t1 + ck)) t1) =
        (res,t2) /\
        clos_interpProof_state_rel s2 t2) /\
   (!args (s1:(C,FFI)clos_state) loc f t1 res s2.
      evaluate_app loc f args s1 = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      clos_interpProof_state_rel s1 t1 ==>
      ?ck t2.
        evaluate_app loc f args (clos_state_clock_fupd (K (clos_state_clock t1 + ck)) t1) =
        (res,t2) /\
        clos_interpProof_state_rel s2 t2)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ONCE_REWRITE_RULE[ADD_SYM] (REWRITE_RULE[interp_assum_def; IMP_IMP]
    (SPEC `clos_state_clock (s1:(C,FFI)clos_state)` CLOSP2AUX_il_interp_assum))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `s1:(C,FFI)clos_state` THEN
                          ASM_REWRITE_TAC[LE_REFL]));;

(* HOL4: evaluate_interp_thm *)
let evaluate_interp_thm = prove
 (`!xs env (s1:(C,FFI)clos_state) t1 res s2.
     clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     clos_interpProof_state_rel s1 t1 ==>
     ?ck t2.
       clos_evaluate (xs,env,clos_state_clock_fupd (K (clos_state_clock t1 + ck)) t1) =
       (res,t2) /\
       clos_interpProof_state_rel s2 t2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (CONJUNCT1 evaluate_interp_lemma)) THEN
  EXISTS_TAC `s1:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* not has_install ignores compiler oracle                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4: v_ok_def [simp] *)
let v_ok_def = sem1aux_def_wf
  `MEASURE clos_v_size`
  (SEM1AUX_TC_TAC ORELSE
   (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    RVEQ_TAC THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP clos_v_size_lemma)) THEN
    REWRITE_TAC(WF_REL_THMS @ [type_size_def "clos_v"] @ size_aux_eqs "clos_v") THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC))
  `(v_ok (clos_Number x) <=> T) /\
   (v_ok (clos_Word64 w) <=> T) /\
   (v_ok (clos_Block n vs) <=> ALL v_ok vs) /\
   (v_ok (ByteVector ws) <=> T) /\
   (v_ok (clos_RefPtr b n) <=> T) /\
   (v_ok (clos_Closure loco vs1 env1 n bod1) <=>
      ~has_install bod1 /\ ALL v_ok env1 /\ ALL v_ok vs1) /\
   (v_ok (clos_Recclosure loco vs1 env1 fns1 i) <=>
      ALL v_ok env1 /\ ALL v_ok vs1 /\ i < LENGTH fns1 /\
      ALL ((~) o has_install o SND) fns1)`;;
let _ = cake_add_simps [v_ok_def];;

let v_ok_ind = cake_ind "v_ok";;

(* HOL4: res_ok_def [simp] *)
let res_ok_def = sem1aux_def
  `(res_ok (Rerr (Rabort _):(clos_v list,clos_v)result) <=> T) /\
   (res_ok (Rerr (Rraise v)) <=> v_ok v) /\
   (res_ok (Rval vs) <=> ALL v_ok vs)`;;
let _ = cake_add_simps [res_ok_def];;

(* HOL4: state_rel'_def *)
let state_rel'_def = cake_def
  `state_rel' (s:(C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     (!n. SND (SND (clos_state_compile_oracle s n)) = []) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY /\
     clos_state_max_app t = clos_state_max_app s /\ 1 <= clos_state_max_app s /\
     clos_state_clock t = clos_state_clock s /\
     clos_state_ffi t = clos_state_ffi s /\
     clos_state_globals s = clos_state_globals t /\
     ALL (OPTION_ALL v_ok) (clos_state_globals t) /\
     clos_state_refs s = clos_state_refs t /\
     FEVERY (\p. match p with
                   (k,v) -> !vs. v = clos_ValueArray vs ==> ALL v_ok vs)
            (clos_state_refs t) /\
     FEVERY (\p. match p with
                   (k,v) -> !m w. v = clos_Thunk m w ==> v_ok w)
            (clos_state_refs t) /\
     clos_state_compile s = pure_cc (insert_interp ## I) (clos_state_compile t) /\
     clos_state_compile_oracle t =
       pure_co (insert_interp ## I) o clos_state_compile_oracle s`;;

(* HOL4: lookup_vars_ok *)
let lookup_vars_ok = prove
 (`!vs (env:clos_v list) env'. lookup_vars vs env = SOME env' /\ ALL v_ok env ==> ALL v_ok env'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def; injectivity "option"] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) (X_CHOOSE_THEN `xs:clos_v list`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC `lookup_vars t (env:clos_v list)` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_EL]) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4: state_rel'_clock [local] *)
let state_rel'_clock = prove
 (`state_rel' (s:(C,FFI)clos_state) t ==> clos_state_clock t = clos_state_clock s`,
  SIMP_TAC[state_rel'_def]);;

(* HOL4: state_rel'_refs [local] *)
let state_rel'_refs = prove
 (`state_rel' (s:(C,FFI)clos_state) t ==> clos_state_refs t = clos_state_refs s`,
  SIMP_TAC[state_rel'_def]);;

(* HOL4: state_rel'_dec_clock [local] *)
let state_rel'_dec_clock = prove
 (`state_rel' (s:(C,FFI)clos_state) t ==>
   state_rel' (clos_dec_clock 1 s) (clos_dec_clock 1 t)`,
  REWRITE_TAC[state_rel'_def; clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: has_install_list_eq [local] *)
let has_install_list_eq = prove
 (`!xs. has_install_list xs <=> EX has_install xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[has_install_def; EX]);;

(* local helpers for evaluate_change_oracle *)
let CLOSP2AUX_co_dest_closure_ok = prove
 (`!max_app loc_opt f args.
     v_ok f /\ ALL v_ok args ==>
     (!v. dest_closure max_app loc_opt f args = SOME (Partial_app v) ==> v_ok v) /\
     (!exp env rest.
        dest_closure max_app loc_opt f args = SOME (Full_app exp env rest) ==>
        ~has_install exp /\ ALL v_ok env /\ ALL v_ok rest)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `f:clos_v` (CONJUNCT1 (cases "clos_v"))) THEN
  REWRITE_TAC[dest_closure_def; v_ok_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THENL
   [STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[injectivity "option"; distinctness "option"; injectivity "app_kind";
                distinctness "app_kind"] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
    ASM_SIMP_TAC[v_ok_def; ALL_APPEND; EVERY_REVERSE; EVERY_TAKE; EVERY_DROP];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `EL a4 (a3:(num # clos_exp) list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `na:num` (X_CHOOSE_THEN `ex:clos_exp` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"; injectivity "app_kind";
              distinctness "app_kind"] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[v_ok_def; ALL_APPEND; EVERY_REVERSE; EVERY_TAKE; EVERY_DROP; EVERY_GENLIST;
               ALL] THEN
  UNDISCH_TAC `ALL ((~) o has_install o SND) (a3:(num # clos_exp) list)` THEN
  REWRITE_TAC[GSYM ALL_EL; o_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `a4:num`) THEN ASM_REWRITE_TAC[SND] THEN ASM_ARITH_TAC);;

let CLOSP2AUX_co_ALL2_vr = prove
 (`!xs ys. ALL2 (\v1 v2:clos_v. v1 = v2 /\ v_ok v1) xs ys <=> xs = ys /\ ALL v_ok xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11] THEN MESON_TAC[]);;

let CLOSP2AUX_co_ALL2_OPTREL_vr = prove
 (`!xs ys. ALL2 (OPTREL (\v1 v2:clos_v. v1 = v2 /\ v_ok v1)) xs ys <=>
           xs = ys /\ ALL (OPTION_ALL v_ok) xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL; NOT_CONS_NIL; NOT_NIL_CONS; CONS_11] THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "option")))
    [`h:clos_v option`; `h':clos_v option`] THEN
  REWRITE_TAC[OPTREL_THM; OPTION_ALL_def; distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let CLOSP2AUX_co_simple_val_rel = prove
 (`clos_simple_val_rel (\v1 v2:clos_v. v1 = v2 /\ v_ok v1)`,
  REWRITE_TAC[clos_simple_val_rel_def; CLOSP2AUX_co_ALL2_vr] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY EQ_TAC THEN
  SIMP_TAC[clos_isClos_def; v_ok_def] THEN MESON_TAC[v_ok_def]);;

let CLOSP2AUX_has_const (c:string) (tm:term) =
  can (find_term (fun t -> is_const t && fst(dest_const t) = c)) tm;;

let CLOSP2AUX_co_refs_ok = prove
 (`!(s:(C,FFI)clos_state) t ptr.
     state_rel' s t ==>
     (!w. FLOOKUP (clos_state_refs t) ptr = SOME (clos_ValueArray w) ==> ALL v_ok w) /\
     (!m w. FLOOKUP (clos_state_refs t) ptr = SOME (clos_Thunk m w) ==> v_ok w)`,
  REWRITE_TAC[state_rel'_def] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP FEVERY_FLOOKUP o C CONJ
      (ASSUME `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) ptr = SOME (clos_ValueArray w)`) o
      check (fun th -> CLOSP2AUX_has_const "FEVERY" (concl th) &&
                       CLOSP2AUX_has_const "clos_ValueArray" (concl th)));
    FIRST_X_ASSUM(MP_TAC o MATCH_MP FEVERY_FLOOKUP o C CONJ
      (ASSUME `FLOOKUP (clos_state_refs (t:(C,FFI)clos_state)) ptr = SOME (clos_Thunk m w)`) o
      check (fun th -> CLOSP2AUX_has_const "FEVERY" (concl th) &&
                       CLOSP2AUX_has_const "clos_Thunk" (concl th)))] THEN
  REWRITE_TAC[case_def "prod"] THEN MESON_TAC[]);;

let CLOSP2AUX_co_state_rel_refs_upd = prove
 (`!(s:(C,FFI)clos_state) t p x.
     state_rel' s t /\ (!vs. x = clos_ValueArray vs ==> ALL v_ok vs) /\
     (!m w. x = clos_Thunk m w ==> v_ok w) ==>
     state_rel' (clos_state_refs_fupd (K (clos_state_refs s |+ (p,x))) s)
                (clos_state_refs_fupd (K (clos_state_refs t |+ (p,x))) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[state_rel'_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC (CONJUNCT2 (SPEC_ALL FEVERY_STRENGTHEN_THM)) THEN
  ASM_REWRITE_TAC[case_def "prod"]);;
let CLOSP2AUX_CO_FLOOKUP_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSP2AUX_has_const "FLOOKUP" (concl th))) THEN
  ASM_REWRITE_TAC[];;

let CLOSP2AUX_co_simple_state_rel = prove
 (`clos_simple_state_rel (\v1 v2:clos_v. v1 = v2 /\ v_ok v1)
     (state_rel':(C,FFI)clos_state->(C,FFI)clos_state->bool)`,
  REWRITE_TAC[clos_simple_state_rel_def; CLOSP2AUX_co_ALL2_vr; CLOSP2AUX_co_ALL2_OPTREL_vr] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel'_refs o
    check (fun th -> CLOSP2AUX_has_const "state_rel'" (concl th))) THEN
  RVEQ_TAC THENL
   [CLOSP2AUX_CO_FLOOKUP_TAC;
    CLOSP2AUX_CO_FLOOKUP_TAC;
    EXISTS_TAC `w:clos_v list` THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `w:clos_v list` (CONJUNCT1 (SPEC `ptr:num`
      (MATCH_MP CLOSP2AUX_co_refs_ok (check (fun th -> CLOSP2AUX_has_const "state_rel'" (concl th))
         th)))))) THEN
    CLOSP2AUX_CO_FLOOKUP_TAC THEN SIMP_TAC[];
    EXISTS_TAC `v:clos_v` THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPECL [`m:thunk_mode`; `v:clos_v`] (CONJUNCT2 (SPEC `ptr:num`
      (MATCH_MP CLOSP2AUX_co_refs_ok (check (fun th -> CLOSP2AUX_has_const "state_rel'" (concl th))
         th)))))) THEN
    CLOSP2AUX_CO_FLOOKUP_TAC THEN SIMP_TAC[];
    UNDISCH_TAC `state_rel' (s:(C,FFI)clos_state) t` THEN SIMP_TAC[state_rel'_def];
    UNDISCH_TAC `state_rel' (s:(C,FFI)clos_state) t` THEN
    SIMP_TAC[state_rel'_def; clos_state_INFO.ri_accfupds; K_THM];
    MATCH_MP_TAC CLOSP2AUX_co_state_rel_refs_upd THEN
    ASM_REWRITE_TAC[distinctness "clos_ref"];
    MATCH_MP_TAC CLOSP2AUX_co_state_rel_refs_upd THEN
    ASM_REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSP2AUX_co_state_rel_refs_upd THEN
    ASM_REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `state_rel' (s:(C,FFI)clos_state) t` THEN
    ASM_SIMP_TAC[state_rel'_def; clos_state_INFO.ri_accfupds; K_THM]]);;

let CLOSP2AUX_co_exc_rel = prove
 (`!e1 e2:(clos_v)error_result.
     exc_rel (\v1 v2:clos_v. v1 = v2 /\ v_ok v1) e1 e2 <=>
     e1 = e2 /\ res_ok (Rerr e1:(clos_v list,clos_v)result)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `e1:(clos_v)error_result` (cases "error_result")) THEN
  STRUCT_CASES_TAC (ISPEC `e2:(clos_v)error_result` (cases "error_result")) THEN
  REWRITE_TAC[exc_rel_def; res_ok_def; injectivity "error_result";
              distinctness "error_result"] THEN MESON_TAC[]);;

let CLOSP2AUX_co_do_app = prove
 (`!op vs (s:(C,FFI)clos_state) t.
     state_rel' s t /\ ALL v_ok vs ==>
     (!v s'. clos_do_app op vs s = Rval (v,s') ==>
             ?t'. clos_do_app op vs t = Rval (v,t') /\ state_rel' s' t' /\ v_ok v) /\
     (!e. clos_do_app op vs s = Rerr e ==>
          clos_do_app op vs t = Rerr e /\ res_ok (Rerr e:(clos_v list,clos_v)result))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\v1 v2:clos_v. v1 = v2 /\ v_ok v1`;
                 `state_rel':(C,FFI)clos_state->(C,FFI)clos_state->bool`;
                 `s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `vs:clos_v list`;
                 `vs:clos_v list`; `op:clos_op`] simple_val_rel_do_app) THEN
  ASM_REWRITE_TAC[CLOSP2AUX_co_simple_val_rel; CLOSP2AUX_co_simple_state_rel;
                  CLOSP2AUX_co_ALL2_vr] THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `p:clos_v#(C,FFI)clos_state` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (X_CHOOSE_THEN `e0:(clos_v)error_result` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC `clos_do_app op vs (s:(C,FFI)clos_state)` (cases "result")) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; CLOSP2AUX_co_exc_rel] THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MP_TAC(ISPEC `p:clos_v#(C,FFI)clos_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:clos_v` (X_CHOOSE_THEN `s0:(C,FFI)clos_state` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:clos_v` (X_CHOOSE_THEN `t0:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `t0:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[]);;

(* evaluate_change_oracle is proved by the induction of closProps on the  *)
(* source evaluation, one lemma per case (CLOSP2AUX_co_ind)                 *)
let CLOSP2AUX_co_P = `\xs env (s1:(C,FFI)clos_state).
   !t1 res s2.
     clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     state_rel' s1 t1 /\ ~has_install_list xs /\ ALL v_ok env ==>
     ?t2. clos_evaluate (xs,env,t1) = (res,t2) /\ state_rel' s2 t2 /\ res_ok res`;;

let CLOSP2AUX_co_Q = `\loc_opt f args (s1:(C,FFI)clos_state).
   !t1 res s2.
     evaluate_app loc_opt f args s1 = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
     state_rel' s1 t1 /\ ALL v_ok args /\ v_ok f ==>
     ?t2. evaluate_app loc_opt f args t1 = (res,t2) /\ state_rel' s2 t2 /\ res_ok res`;;

let CLOSP2AUX_co_ind =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (ISPECL [CLOSP2AUX_co_P; CLOSP2AUX_co_Q] CLOSPROPSAUX_evaluate_ind);;

let CLOSP2AUX_co_cases = conjuncts (lhand (concl CLOSP2AUX_co_ind));;

(* the normal form of the side conditions *)
let CLOSP2AUX_co_has_install_AppUnit = prove
 (`!x. has_install (clos_AppUnit x) <=> has_install x`,
  REWRITE_TAC[clos_AppUnit_def; has_install_def; distinctness "clos_op"]);;

let CLOSP2AUX_co_nrm_thms =
  [has_install_def; ALL; ALL_APPEND; DE_MORGAN_THM; res_ok_def;
   CLOSP2AUX_co_has_install_AppUnit; HD;
   distinctness "result"; injectivity "result"; distinctness "error_result";
   distinctness "clos_op"];;

let CLOSP2AUX_CO_NRM_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE CLOSP2AUX_co_nrm_thms) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* the source evaluation equation of a case, moved to the goal *)
let CLOSP2AUX_CO_SRC_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res:(clos_v list,clos_v)result, s2:(C,FFI)clos_state)`));;

(* resolve the labelled induction hypothesis; t names the target state *)
let CLOSP2AUX_CO_IH_TAC (lab:string) (t:term) : tactic = fun (asl,w as g) ->
  let ih = assoc lab asl in
  let nrm th = REWRITE_RULE[IMP_CONJ] (REWRITE_RULE CLOSP2AUX_co_nrm_thms th) in
  let asms = map snd asl in
  let rec resolve depth th =
    let c = snd (strip_forall (concl th)) in
    if not (is_imp c) then [th] else if depth = 0 then [] else
    let rs = mapfilter (fun a -> nrm (MATCH_MP th a)) asms in
    flat (map (resolve (depth-1)) rs) in
  match resolve 12 (nrm ih) with
    th::_ -> (X_CHOOSE_THEN t STRIP_ASSUME_TAC th THEN CLOSP2AUX_CO_NRM_TAC) g
  | [] -> failwith ("CLOSP2AUX_CO_IH_TAC "^lab);;

(* an error result of a sub-evaluation that is the result of the case *)
let CLOSP2AUX_CO_ERR_TAC (lab:string) : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_IH_TAC lab `te:(C,FFI)clos_state` THEN
  EXISTS_TAC `te:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[] THEN
  TRY(CASE_REWRITE_TAC[]) THEN ASM_REWRITE_TAC[res_ok_def; HD; ALL];;

let CLOSP2AUX_co_nil = prove
 (el 0 CLOSP2AUX_co_cases,
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `t1:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL]);;

let CLOSP2AUX_co_Var = prove
 (el 2 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  EXISTS_TAC `t1:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM ALL_EL] o check (fun th ->
    concl th = `ALL v_ok (env:clos_v list)`)) THEN ASM_SIMP_TAC[]);;

(* the singleton value of a singleton evaluation *)
let CLOSP2AUX_CO_SING_TAC (tm:term) (v:term) : tactic =
  FIRST_ASSUM(X_CHOOSE_THEN v SUBST_ALL_TAC o MATCH_MP clos_evaluate_SING o
    check (fun th -> is_eq (concl th) && lhs (concl th) = tm));;

let CLOSP2AUX_co_Raise = prove
 (el 5 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP2AUX_CO_NRM_TAC THEN CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_CO_SING_TAC `clos_evaluate ([x1],env,s:(C,FFI)clos_state)` `v1:clos_v`;
    ALL_TAC] THEN
  CLOSP2AUX_CO_ERR_TAC "IH1");;

let CLOSP2AUX_co_If = prove
 (el 3 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1")
    (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH3"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IH1"] THEN
  CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `clos_evaluate ([x1],env,t1:(C,FFI)clos_state)`) th]) THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN CLOSP2AUX_CO_IH_TAC "IH2" `t7:(C,FFI)clos_state` THEN
    EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THENL
     [DISCH_TAC THEN CLOSP2AUX_CO_IH_TAC "IH3" `t7:(C,FFI)clos_state` THEN
      EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC]]);;

(* rewrite the target sub-evaluation of the goal with its equation *)
let CLOSP2AUX_CO_TGT_TAC (tm:term) : tactic =
  FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) && lhs (concl th) = tm) th]) THEN
  TRY(CASE_REWRITE_TAC[]);;

let CLOSP2AUX_co_Let = prove
 (el 4 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IH1"] THEN
  CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
  CLOSP2AUX_CO_TGT_TAC `clos_evaluate (xs,env,t1:(C,FFI)clos_state)` THEN
  DISCH_TAC THEN CLOSP2AUX_CO_IH_TAC "IH2" `t7:(C,FFI)clos_state` THEN
  EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_co_Handle = prove
 (el 6 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s1:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_CO_ERR_TAC "IH1"; ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `v1:clos_v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `ab:abort` SUBST_ALL_TAC)
    (ISPEC `err:(clos_v)error_result` (cases "error_result")) THEN
  CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
    CLOSP2AUX_CO_TGT_TAC `clos_evaluate ([x1],env,t1:(C,FFI)clos_state)` THEN
    DISCH_TAC THEN CLOSP2AUX_CO_IH_TAC "IH2" `t7:(C,FFI)clos_state` THEN
    EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[];
    CLOSP2AUX_CO_ERR_TAC "IH1"]);;

let CLOSP2AUX_co_CONS = prove
 (el 1 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x],env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IH1"] THEN
  CLOSP2AUX_CO_SING_TAC `clos_evaluate ([x],env,s:(C,FFI)clos_state)` `v1:clos_v` THEN
  CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
  CLOSP2AUX_CO_TGT_TAC `clos_evaluate ([x],env,t1:(C,FFI)clos_state)` THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (CONS y xs,env,s6:(C,FFI)clos_state)`
    `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_CO_IH_TAC "IH2" `t7:(C,FFI)clos_state` THEN
    CLOSP2AUX_CO_TGT_TAC `clos_evaluate (CONS y xs,env,t6:(C,FFI)clos_state)` THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL; HD];
    CLOSP2AUX_CO_ERR_TAC "IH2"]);;

let CLOSP2AUX_co_Tick = prove
 (el 11 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP2AUX_CO_NRM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel'_clock) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel'_dec_clock) THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  ASM_CASES_TAC `clos_state_clock (s:(C,FFI)clos_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `t1:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def];
    DISCH_TAC THEN CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
    EXISTS_TAC `t6:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[]]);;

let CLOSP2AUX_co_Call = prove
 (el 12 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,env,s1:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = `state_rel' s6 (t6:(C,FFI)clos_state)`)) THEN
    REWRITE_TAC[state_rel'_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_find_code_def; FLOOKUP_EMPTY] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    CLOSP2AUX_CO_ERR_TAC "IH1"]);;

let CLOSP2AUX_co_Fn = prove
 (el 8 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  SUBGOAL_THEN `clos_state_max_app (t1:(C,FFI)clos_state) = clos_state_max_app (s:(C,FFI)clos_state)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `state_rel' (s:(C,FFI)clos_state) t1` THEN SIMP_TAC[state_rel'_def]; ALL_TAC] THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(TOP_CASE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ]) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  EXISTS_TAC `t1:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; v_ok_def; ALL] THEN
  MATCH_MP_TAC lookup_vars_ok THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_co_rc_ok = prove
 (`!loc e fns. ALL v_ok e /\ ~has_install_list (MAP SND fns) ==>
               ALL v_ok (list_of_seq (clos_Recclosure loc [] e fns) (LENGTH fns))`,
  REWRITE_TAC[has_install_list_eq; NOT_EX; ALL_MAP; EVERY_GENLIST; v_ok_def; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSP2AUX_has_const "has_install" (concl th))) THEN
  REWRITE_TAC[o_DEF] THEN SIMP_TAC[]);;

let CLOSP2AUX_co_Letrec = prove
 (el 9 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH1") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP2AUX_CO_NRM_TAC THEN
  SUBGOAL_THEN `clos_state_max_app (t1:(C,FFI)clos_state) = clos_state_max_app (s:(C,FFI)clos_state)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `state_rel' (s:(C,FFI)clos_state) t1` THEN SIMP_TAC[state_rel'_def]; ALL_TAC] THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `clos_state_max_app (t1:(C,FFI)clos_state)`) th]) THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `names:num list` SUBST_ALL_TAC)
    (ISPEC `namesopt:(num list)option` (cases "option")) THEN
  CASE_REWRITE_TAC[] THENL
   [ALL_TAC;
    DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
      (X_CHOOSE_THEN `env1:clos_v list` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
      (ISPEC `lookup_vars names (env:clos_v list)` (cases "option")) THEN
    REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `ALL v_ok (env1:clos_v list)` ASSUME_TAC THENL
     [MATCH_MP_TAC lookup_vars_ok THEN ASM_MESON_TAC[]; ALL_TAC]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `loc:num option` o MATCH_MP CLOSP2AUX_co_rc_ok o C CONJ
    (ASSUME `~has_install_list (MAP SND (fns:(num # clos_exp) list))`) o
    check (fun th -> concl th = `ALL v_ok (env:clos_v list)` ||
                     concl th = `ALL v_ok (env1:clos_v list)`)) THEN
  CLOSP2AUX_CO_IH_TAC "IH1" `t7:(C,FFI)clos_state` THEN
  EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_co_App = prove
 (el 10 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH3")
    (CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH1"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  ASM_CASES_TAC `LENGTH (args:clos_exp list) > 0` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (args,env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IH1"] THEN
  CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
  CLOSP2AUX_CO_TGT_TAC `clos_evaluate (args,env,t1:(C,FFI)clos_state)` THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([x1],env,s6:(C,FFI)clos_state)`
    `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IH2"] THEN
  CLOSP2AUX_CO_SING_TAC `clos_evaluate ([x1],env,s6:(C,FFI)clos_state)` `vf:clos_v` THEN
  CLOSP2AUX_CO_IH_TAC "IH2" `t7:(C,FFI)clos_state` THEN
  CLOSP2AUX_CO_TGT_TAC `clos_evaluate ([x1],env,t6:(C,FFI)clos_state)` THEN
  REWRITE_TAC[HD] THEN DISCH_TAC THEN
  CLOSP2AUX_CO_IH_TAC "IH3" `t8:(C,FFI)clos_state` THEN
  EXISTS_TAC `t8:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[]);;

let CLOSP2AUX_co_app_nil = prove
 (el 13 CLOSP2AUX_co_cases,
  REWRITE_TAC[clos_evaluate_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  EXISTS_TAC `t1:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL]);;

let CLOSP2AUX_co_state_rel_clock = prove
 (`!(s:(C,FFI)clos_state) t k.
     state_rel' s t ==>
     state_rel' (clos_state_clock_fupd (K k) s) (clos_state_clock_fupd (K k) t)`,
  REWRITE_TAC[state_rel'_def; clos_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[]);;

let CLOSP2AUX_co_app_cons = prove
 (el 14 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  SUBGOAL_THEN `clos_state_max_app (t1:(C,FFI)clos_state) = clos_state_max_app (s:(C,FFI)clos_state) /\
                clos_state_clock t1 = clos_state_clock s`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `state_rel' (s:(C,FFI)clos_state) t1` THEN SIMP_TAC[state_rel'_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`clos_state_max_app (s:(C,FFI)clos_state)`; `loc_opt:num option`; `f:clos_v`;
                `CONS (v4:clos_v) v5`] CLOSP2AUX_co_dest_closure_ok) THEN
  ASM_REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
    (X_CHOOSE_THEN `ak:app_kind` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))
    (ISPEC `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) loc_opt f (CONS v4 v5)`
       (cases "option")) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `pv:clos_v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `fe:clos_exp` (X_CHOOSE_THEN `fenv:clos_v list`
      (X_CHOOSE_THEN `rest:clos_v list` SUBST_ALL_TAC)))
    (ISPEC `ak:app_kind` (cases "app_kind")) THEN
  CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `clos_state_clock_fupd (K 0) (t1:(C,FFI)clos_state)` THEN
    ASM_SIMP_TAC[res_ok_def; CLOSP2AUX_co_state_rel_clock];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `clos_dec_clock (LENGTH (CONS (v4:clos_v) v5)) (t1:(C,FFI)clos_state)` THEN
    REWRITE_TAC[clos_dec_clock_def] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[res_ok_def; ALL; CLOSP2AUX_co_state_rel_clock];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `clos_state_clock_fupd (K 0) (t1:(C,FFI)clos_state)` THEN
    ASM_SIMP_TAC[res_ok_def; CLOSP2AUX_co_state_rel_clock];
    ALL_TAC] THEN
  SUBGOAL_THEN `state_rel'
     (clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list)) (s:(C,FFI)clos_state))
     (clos_dec_clock (LENGTH (CONS v4 v5) - LENGTH rest) (t1:(C,FFI)clos_state))` ASSUME_TAC THENL
   [REWRITE_TAC[clos_dec_clock_def] THEN ASM_SIMP_TAC[CLOSP2AUX_co_state_rel_clock]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
    then STRIP_ASSUME_TAC (MATCH_MP th (ASSUME
      `dest_closure (clos_state_max_app (s:(C,FFI)clos_state)) loc_opt f (CONS v4 v5) =
       SOME (Full_app fe fenv rest)`))
    else NO_TAC) THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([fe:clos_exp],fenv:clos_v list,
      clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list))
      (s:(C,FFI)clos_state))`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IH2"] THEN
  CLOSP2AUX_CO_IH_TAC "IH2" `t6:(C,FFI)clos_state` THEN
  CLOSP2AUX_CO_TGT_TAC `clos_evaluate ([fe:clos_exp],fenv:clos_v list,
      clos_dec_clock (LENGTH (CONS (v4:clos_v) v5) - LENGTH (rest:clos_v list))
      (t1:(C,FFI)clos_state))` THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `v:clos_v` (X_CHOOSE_THEN `a2:clos_v list` SUBST_ALL_TAC))
    (ISPEC `a1:clos_v list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `t6:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `v':clos_v` (X_CHOOSE_THEN `a3:clos_v list` SUBST_ALL_TAC))
    (ISPEC `a2:clos_v list` list_CASES) THEN CASE_REWRITE_TAC[] THENL
   [CLOSP2AUX_CO_NRM_TAC THEN DISCH_TAC THEN
    CLOSP2AUX_CO_IH_TAC "IH1" `t7:(C,FFI)clos_state` THEN
    EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
    EXISTS_TAC `t6:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL]]);;
let CLOSP2AUX_co_dest_thunk = prove
 (`!vs refs m v. clos_dest_thunk vs refs = clos_IsThunk m v ==>
                 ?ptr. FLOOKUP refs ptr = SOME (clos_Thunk m v)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_dest_thunk_def; distinctness "clos_dest_thunk_ret"] THEN
  STRUCT_CASES_TAC (ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_dest_thunk_def; distinctness "clos_dest_thunk_ret"] THEN
  STRUCT_CASES_TAC (ISPEC `h:clos_v` (CONJUNCT1 (cases "clos_v"))) THEN
  REWRITE_TAC[clos_dest_thunk_def; distinctness "clos_dest_thunk_ret"] THEN
  REPEAT GEN_TAC THEN REPEAT(TOP_CASE_TAC THEN
    REWRITE_TAC[distinctness "clos_dest_thunk_ret"; injectivity "clos_dest_thunk_ret"]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

let CLOSP2AUX_co_update_thunk = prove
 (`!vs refs vs2 refs'.
     clos_update_thunk vs refs vs2 = SOME refs' ==>
     ?p v. vs2 = [v] /\ refs' = refs |+ (p,clos_Thunk Evaluated v)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `vs:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `h:clos_v` (CONJUNCT1 (cases "clos_v"))) THEN
  REWRITE_TAC[clos_update_thunk_def; distinctness "option"] THEN
  GEN_TAC THEN X_GEN_TAC `vs2:clos_v list` THEN
  STRUCT_CASES_TAC (ISPEC `vs2:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; distinctness "option"] THEN
  STRUCT_CASES_TAC (ISPEC `t:clos_v list` list_CASES) THEN
  REWRITE_TAC[clos_update_thunk_def; distinctness "option"; CONS_11] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[store_thunk_def] THEN
  REPEAT(TOP_CASE_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"]) THEN
  MESON_TAC[]);;
let CLOSP2AUX_co_state_rel_refs_upd2 = prove
 (`!(s:(C,FFI)clos_state) t p x.
     state_rel' s t /\ (!vs. x = clos_ValueArray vs ==> ALL v_ok vs) /\
     (!m w. x = clos_Thunk m w ==> v_ok w) ==>
     state_rel' (clos_state_refs_fupd (K (clos_state_refs s |+ (p,x))) s)
                (clos_state_refs_fupd (K (clos_state_refs s |+ (p,x))) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:(C,FFI)clos_state`; `t:(C,FFI)clos_state`; `p:num`; `x:(clos_v)clos_ref`]
    CLOSP2AUX_co_state_rel_refs_upd) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel'_refs th]));;

let CLOSP2AUX_co_Op = prove
 (el 7 CLOSP2AUX_co_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHI")
    (CONJUNCTS_THEN2 (LABEL_TAC "IHF") (LABEL_TAC "IH1"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  CLOSP2AUX_CO_SRC_TAC THEN REWRITE_TAC[clos_evaluate_def] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,env,s:(C,FFI)clos_state)`
    `a1:clos_v list` `s6:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IH1"] THEN
  CLOSP2AUX_CO_IH_TAC "IH1" `t6:(C,FFI)clos_state` THEN
  CLOSP2AUX_CO_TGT_TAC `clos_evaluate (xs,env,t1:(C,FFI)clos_state)` THEN
  REWRITE_TAC[ASSUME `~(op = clos_Install)`] THEN
  ASM_CASES_TAC `op = clos_ThunkOp ForceThunk` THENL
   [ALL_TAC;
    REWRITE_TAC[ASSUME `~(op = clos_ThunkOp ForceThunk)`] THEN
    MP_TAC(SPECL [`op:clos_op`; `REVERSE a1:clos_v list`; `s6:(C,FFI)clos_state`;
                  `t6:(C,FFI)clos_state`] CLOSP2AUX_co_do_app) THEN
    ASM_REWRITE_TAC[EVERY_REVERSE] THEN STRIP_TAC THEN
    DISJ_CASES_THEN2
      (X_CHOOSE_THEN `p:clos_v#(C,FFI)clos_state` ASSUME_TAC)
      (X_CHOOSE_THEN `e0:(clos_v)error_result` ASSUME_TAC)
      (ISPEC `clos_do_app op (REVERSE a1) (s6:(C,FFI)clos_state)` (cases "result")) THENL
     [MP_TAC(ISPEC `p:clos_v#(C,FFI)clos_state` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `v0:clos_v` (X_CHOOSE_THEN `s7:(C,FFI)clos_state`
        SUBST_ALL_TAC)) THEN
      FIRST_X_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 2
        then MP_TAC (MATCH_MP th
          (ASSUME `clos_do_app op (REVERSE a1) (s6:(C,FFI)clos_state) = Rval (v0,s7)`))
        else NO_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `t7:(C,FFI)clos_state` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      EXISTS_TAC `t7:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL];
      FIRST_X_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 1
        then STRIP_ASSUME_TAC (MATCH_MP th
          (ASSUME `clos_do_app op (REVERSE a1) (s6:(C,FFI)clos_state) = Rerr e0`))
        else NO_TAC) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
      EXISTS_TAC `t6:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[]]] THEN
  REWRITE_TAC[ASSUME `op = clos_ThunkOp ForceThunk`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel'_refs (check (fun th ->
    concl th = `state_rel' s6 (t6:(C,FFI)clos_state)`) th)]) THEN
  DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
    (DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
      (X_CHOOSE_THEN `tm:thunk_mode` (X_CHOOSE_THEN `v:clos_v`
         (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))))
    (ISPEC `clos_dest_thunk a1 (clos_state_refs (s6:(C,FFI)clos_state))`
       (cases "clos_dest_thunk_ret")) THEN
  CASE_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_ASSUM CONTR_TAC;
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v_ok v` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `ptr:num` o MATCH_MP CLOSP2AUX_co_dest_thunk o check (fun th ->
      CLOSP2AUX_has_const "clos_IsThunk" (concl th))) THEN
    MP_TAC(SPEC `ptr:num` (MATCH_MP CLOSP2AUX_co_refs_ok (ASSUME
      `state_rel' s6 (t6:(C,FFI)clos_state)`))) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel'_refs (check (fun th ->
      concl th = `state_rel' s6 (t6:(C,FFI)clos_state)`) th)]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC (ISPEC `tm:thunk_mode` (cases "thunk_mode")) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `t6:(C,FFI)clos_state` THEN ASM_REWRITE_TAC[res_ok_def; ALL];
    ALL_TAC] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[v],
      s6:(C,FFI)clos_state)` `a2:clos_v list` `s7:(C,FFI)clos_state` `err:(clos_v)error_result` THENL
   [ALL_TAC; CLOSP2AUX_CO_ERR_TAC "IHF"] THEN
  CLOSP2AUX_CO_IH_TAC "IHF" `t7:(C,FFI)clos_state` THEN
  CLOSP2AUX_CO_TGT_TAC `clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],[v],
      t6:(C,FFI)clos_state)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel'_refs (check (fun th ->
    concl th = `state_rel' s7 (t7:(C,FFI)clos_state)`) th)]) THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
    (X_CHOOSE_THEN `rf:(num,(clos_v)clos_ref)fmap` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (ISPEC `clos_update_thunk a1 (clos_state_refs (s7:(C,FFI)clos_state)) a2` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `v2:clos_v` STRIP_ASSUME_TAC) o
    MATCH_MP CLOSP2AUX_co_update_thunk) THEN
  RVEQ_TAC THEN CLOSP2AUX_CO_NRM_TAC THEN
  EXISTS_TAC `clos_state_refs_fupd (K (clos_state_refs (s7:(C,FFI)clos_state) |+ (p,clos_Thunk Evaluated v2)))
                (t7:(C,FFI)clos_state)` THEN
  ASM_REWRITE_TAC[res_ok_def; ALL] THEN
  MATCH_MP_TAC CLOSP2AUX_co_state_rel_refs_upd2 THEN
  ASM_REWRITE_TAC[distinctness "clos_ref"; injectivity "clos_ref"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: evaluate_change_oracle; the variable n of the HOL4 statement does *)
(* not occur in it (its type is free there; :num here)                     *)
let evaluate_change_oracle = prove
 (`(!tmp xs env (s1:(C,FFI)clos_state) t1 res s2 (n:num).
      tmp = (xs,env,s1) /\
      clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      state_rel' s1 t1 /\ ~has_install_list xs /\ ALL v_ok env ==>
      ?t2. clos_evaluate (xs,env,t1) = (res,t2) /\ state_rel' s2 t2 /\ res_ok res) /\
   (!loc f args (s:(C,FFI)clos_state) res s2 t1.
      evaluate_app loc f args s = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      state_rel' s t1 /\ ALL v_ok args /\ v_ok f ==>
      ?t2. evaluate_app loc f args t1 = (res,t2) /\ state_rel' s2 t2 /\ res_ok res)`,
  MP_TAC(MP CLOSP2AUX_co_ind (end_itlist CONJ
    [CLOSP2AUX_co_nil; CLOSP2AUX_co_CONS; CLOSP2AUX_co_Var; CLOSP2AUX_co_If;
     CLOSP2AUX_co_Let; CLOSP2AUX_co_Raise; CLOSP2AUX_co_Handle; CLOSP2AUX_co_Op;
     CLOSP2AUX_co_Fn; CLOSP2AUX_co_Letrec; CLOSP2AUX_co_App; CLOSP2AUX_co_Tick;
     CLOSP2AUX_co_Call; CLOSP2AUX_co_app_nil; CLOSP2AUX_co_app_cons])) THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `s1:(C,FFI)clos_state` THEN
                            ASM_REWRITE_TAC[]);
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC `s:(C,FFI)clos_state` THEN
                            ASM_REWRITE_TAC[])]);;

let CLOSP2AUX_ip_do_app_globals = prove
 (CASE_TERM `(!(s:(C,FFI)clos_state).
     clos_do_app (GlobOp AllocGlobal) [clos_Number (&1)] s =
     Rval (clos_Unit, clos_state_globals_fupd
             (K (APPEND (clos_state_globals s) (REPLICATE 1 NONE))) s)) /\
   (!(s:(C,FFI)clos_state) v.
     clos_do_app (GlobOp (SetGlobal 0)) [v] s =
     (match get_global 0 (clos_state_globals s) with
        SOME NONE -> Rval (clos_Unit, clos_state_globals_fupd
                             (K (LUPDATE (SOME v) 0 (clos_state_globals s))) s)
      | _ -> Rerr (Rabort Rtype_error)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT; NUM_OF_INT_OF_NUM]);;

let CLOSP2AUX_ip_REPLICATE_1 = prove
 (`!x:A. REPLICATE 1 x = [x]`,
  REWRITE_TAC[ONE; REPLICATE]);;

let CLOSP2AUX_ip_compile_init = prove
 (`!(ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k b.
     1 <= ma ==>
     clos_evaluate ([compile_init b],[],clos_initial_state ffi ma code co cc k) =
     (Rval [clos_Unit],
      clos_state_globals_fupd
        (K [SOME (if b then clos_Closure NONE [] [] 1 clos_interpreter
                  else clos_Block 0 [])])
        (clos_initial_state ffi ma code co cc k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[compile_init_def] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
  CLOSP2AUX_IP_EVAL_TAC[CLOSP2AUX_ip_do_app_globals; CLOSP2AUX_ip_REPLICATE_1; get_global_def;
                        LUPDATE_def; clos_initial_state_def; clos_state_INFO.ri_accessors;
                        LT_0; ARITH_RULE `0 < 1`] THEN
  REWRITE_TAC[clos_initial_state_def; clos_state_component_equality;
              clos_state_INFO.ri_accessors; clos_state_INFO.ri_accfupds; K_THM; APPEND;
              LUPDATE_def; CLOSP2AUX_ip_REPLICATE_1]);;

(* ------------------------------------------------------------------------- *)
(* preservation of observable semantics                                      *)
(* ------------------------------------------------------------------------- *)

(* HOL4: init_globals [local] *)
let init_globals = prove
 (`clos_state_globals (clos_initial_state (ffi:(FFI)ffi_state) max_app f
                         (co:num -> C # clos_prog) cc ck) = []`,
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors]);;

let CLOSP2AUX_ip_init_clock = prove
 (`!(ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k ck g.
     clos_state_clock_fupd
       (K (clos_state_clock (clos_state_globals_fupd (K g)
             (clos_initial_state ffi ma code co cc k)) + ck))
       (clos_state_globals_fupd (K g) (clos_initial_state ffi ma code co cc k)) =
     clos_state_globals_fupd (K g) (clos_initial_state ffi ma code co cc (k + ck))`,
  REWRITE_TAC[clos_initial_state_def; clos_state_component_equality;
              clos_state_INFO.ri_accessors; clos_state_INFO.ri_accfupds; K_THM]);;

(* the interpreted program after compile_init T *)
let CLOSP2AUX_IP_SEM_TAC (r:term) : tactic =
  MP_TAC(SPECL [`xs:clos_exp list`; `[]:clos_v list`;
    `clos_state_globals_fupd (K [SOME (clos_Closure NONE [] [] 1 clos_interpreter)])
       (clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY (co:num -> C # clos_prog)
          (pure_cc (insert_interp ## I) cc) k)`;
    `clos_state_globals_fupd (K [SOME (clos_Closure NONE [] [] 1 clos_interpreter)])
       (clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
          (pure_co (insert_interp ## I) o (co:num -> C # clos_prog)) cc k)`;
    r; `s2:(C,FFI)clos_state`] evaluate_interp_thm) THEN
  ASM_REWRITE_TAC[distinctness "result"; injectivity "result"] THEN ANTS_TAC THENL
   [REWRITE_TAC[clos_interpProof_state_rel_def; clos_initial_state_def;
                clos_state_INFO.ri_accessors; clos_state_INFO.ri_accfupds; K_THM; oHD_DEF] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSP2AUX_ip_init_clock] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(C,FFI)clos_state` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1; LEFT_EXISTS_AND_THM;
              EXISTS_REFL; CLOSPROPSAUX_result_rel_T_refl] THEN
  UNDISCH_TAC `clos_interpProof_state_rel (s2:(C,FFI)clos_state) t2` THEN
  SIMP_TAC[clos_interpProof_state_rel_def];;

(* HOL4: semantics_attach_interpreter *)
let semantics_attach_interpreter = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num -> C # clos_prog)
       (pure_cc (insert_interp ## I) cc) (attach_interpreter xs) = Fail) ==>
   (!n. SND (SND (co n)) = []) /\ 0 < max_app ==>
   clos_semantics ffi max_app FEMPTY (pure_co (insert_interp ## I) o co) cc
     (attach_interpreter xs) =
   clos_semantics ffi max_app FEMPTY co (pure_cc (insert_interp ## I) cc)
     (attach_interpreter xs)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] clos_IMP_semantics_eq) THEN
  (fun (asl,w as g) ->
     let rv,_ = dest_exists w in
     let tys,_ = splitlist dest_fun_ty (type_of rv) in
     let vs = map (fun (i,ty) -> mk_var("x" ^ string_of_int i,ty))
                (zip (1--length tys) tys) in
     EXISTS_TAC (list_mk_abs(vs,`T`)) g) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[clos_eval_sim_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= max_app` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `has_install_list (xs:clos_exp list)` THENL
   [ALL_TAC;
    MP_TAC(SPECL [`(attach_interpreter xs,[]:clos_v list,
                    clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY (co:num -> C # clos_prog)
                      (pure_cc (insert_interp ## I) cc) k)`;
                  `attach_interpreter xs`; `[]:clos_v list`;
                  `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY (co:num -> C # clos_prog)
                     (pure_cc (insert_interp ## I) cc) k`;
                  `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                     (pure_co (insert_interp ## I) o (co:num -> C # clos_prog)) cc k`;
                  `res1:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`; `0`]
       (CONJUNCT1 evaluate_change_oracle)) THEN
    ASM_REWRITE_TAC[ALL] THEN ANTS_TAC THENL
     [REWRITE_TAC[state_rel'_def; clos_initial_state_def; clos_state_INFO.ri_accessors;
                  FEVERY_FEMPTY; ALL; o_THM; pure_co_def; PAIR_MAP; I_THM] THEN
      ASM_REWRITE_TAC[attach_interpreter_def; compile_init_def; has_install_def;
                      distinctness "clos_op"] THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; pure_co_def];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:(C,FFI)clos_state` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`0`; `res1:(clos_v list,clos_v)result`; `t2:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; CLOSPROPSAUX_result_rel_T_refl] THEN
    UNDISCH_TAC `state_rel' (s2:(C,FFI)clos_state) t2` THEN SIMP_TAC[state_rel'_def]] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(res1:(clos_v list,clos_v)result, s2:(C,FFI)clos_state)`)) THEN
  ASM_REWRITE_TAC[attach_interpreter_def] THEN ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  ASM_SIMP_TAC[CLOSP2AUX_ip_compile_init] THEN CASE_REWRITE_TAC[] THEN
  CLOSP2AUX_IP_SPLIT_TAC `clos_evaluate (xs,[],clos_state_globals_fupd
      (K [SOME (clos_Closure NONE [] [] 1 clos_interpreter)])
      (clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY (co:num -> C # clos_prog)
         (pure_cc (insert_interp ## I) cc) k))`
    `a:clos_v list` `s3:(C,FFI)clos_state` `err:(clos_v)error_result` THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [CLOSP2AUX_IP_SEM_TAC `Rval a:(clos_v list,clos_v)result`;
    CLOSP2AUX_IP_SEM_TAC `Rerr err:(clos_v list,clos_v)result`]);;

(* ------------------------------------------------------------------------- *)
(* syntactic lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

(* a local helper: interpretable expressions set no globals *)
let CLOSP2AUX_ip_can_interpret_globals = prove
 (`(!x. can_interpret x ==> clos_set_globals x = EMPTY_BAG /\ clos_esgc_free x) /\
   (!xs. can_interpret_list xs ==>
         clos_elist_globals xs = EMPTY_BAG /\ ALL clos_esgc_free xs)`,
  MATCH_MP_TAC can_interpret_ind THEN
  REWRITE_TAC[can_interpret_def; clos_set_globals_def; clos_esgc_free_def; ALL;
              BAG_UNION_EMPTY] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[BAG_UNION_EMPTY] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[CLOSP2AUX_ip_can_interpret_op] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "can_interpret_op"
                                              with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[clos_op_gbag_def]);;

(* HOL4: opt_interp_lemma [local] *)
let opt_interp_lemma = prove
 (`opt_interp x = SOME x' ==>
   clos_set_globals x' = EMPTY_BAG /\
   clos_set_globals x = EMPTY_BAG /\
   (1 <= max_app ==> ~contains_App_SOME max_app [x']) /\
   every_Fn_vs_NONE [x'] /\
   no_mti x' /\
   clos_esgc_free x /\
   clos_esgc_free x'`,
  REWRITE_TAC[opt_interp_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (CONJUNCT1 CLOSP2AUX_ip_can_interpret_globals) o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "can_interpret"
                                              with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY;
                  contains_App_SOME_def; every_Fn_vs_NONE_def; no_mti_def;
                  clos_esgc_free_def; ALL; LENGTH; IS_SOME_DEF; IS_NONE_DEF] THEN
  ARITH_TAC);;

(* a local helper: the two shapes of opt_interp1 *)
let CLOSP2AUX_ip_opt_interp1_cases = prove
 (`!e. opt_interp1 e = e \/ (?x. opt_interp e = SOME x /\ opt_interp1 e = x)`,
  GEN_TAC THEN REWRITE_TAC[opt_interp1_def] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `x:clos_exp` SUBST1_TAC)
    (ISPEC `opt_interp e` (cases "option")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"] THEN MESON_TAC[]);;

(* HOL4: elist_globals_insert_interp *)
let elist_globals_insert_interp = prove
 (`clos_elist_globals (insert_interp xs) = clos_elist_globals xs`,
  REWRITE_TAC[insert_interp_def] THEN SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; clos_set_globals_def] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC
    (SPEC `h:clos_exp` CLOSP2AUX_ip_insert_interp1_cases) THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[clos_set_globals_def] THEN AP_TERM_TAC THEN
  SPEC_TAC(`ys:clos_exp list`,`ys:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; clos_set_globals_def] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC (SPEC `h':clos_exp` CLOSP2AUX_ip_opt_interp1_cases) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_REWRITE_TAC[]);;

(* HOL4: contains_App_SOME_insert_interp *)
let contains_App_SOME_insert_interp = prove
 (`~contains_App_SOME max_app xs /\ 1 <= max_app ==>
   ~contains_App_SOME max_app (insert_interp xs)`,
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[insert_interp_def] THEN ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] THEN
  REWRITE_TAC[NOT_EX; ALL_MAP; o_DEF] THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x. ~contains_App_SOME max_app [x]` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:clos_exp` THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC
    (SPEC `h:clos_exp` CLOSP2AUX_ip_insert_interp1_cases) THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[contains_App_SOME_def; DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[contains_App_SOME_def; DE_MORGAN_THM] THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `~contains_App_SOME max_app ys`)) THEN
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] THEN
  REWRITE_TAC[NOT_EX; ALL_MAP; o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x. ~contains_App_SOME max_app [x]` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h':clos_exp` THEN STRIP_TAC THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC (SPEC `h':clos_exp` CLOSP2AUX_ip_opt_interp1_cases) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[]);;

(* HOL4: every_Fn_vs_NONE_insert_interp *)
let every_Fn_vs_NONE_insert_interp = prove
 (`every_Fn_vs_NONE xs ==> every_Fn_vs_NONE (insert_interp xs)`,
  REWRITE_TAC[insert_interp_def] THEN ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x. every_Fn_vs_NONE [x]` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:clos_exp` THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC
    (SPEC `h:clos_exp` CLOSP2AUX_ip_insert_interp1_cases) THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[every_Fn_vs_NONE_def]) THEN
  ASM_REWRITE_TAC[every_Fn_vs_NONE_def] THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `every_Fn_vs_NONE ys`)) THEN
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `\x. every_Fn_vs_NONE [x]` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h':clos_exp` THEN STRIP_TAC THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC (SPEC `h':clos_exp` CLOSP2AUX_ip_opt_interp1_cases) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[]);;

(* HOL4: insert_interp_no_mti *)
let insert_interp_no_mti = prove
 (`MEM e (insert_interp xs) ==> ALL no_mti xs ==> no_mti e`,
  SUBGOAL_THEN `ALL no_mti xs ==> ALL no_mti (insert_interp xs)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]] THEN
  REWRITE_TAC[insert_interp_def; ALL_MAP; o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `no_mti` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:clos_exp` THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC
    (SPEC `h:clos_exp` CLOSP2AUX_ip_insert_interp1_cases) THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[no_mti_def]) THEN
  ASM_REWRITE_TAC[no_mti_def; ALL_MAP; o_DEF] THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `no_mti` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h':clos_exp` THEN STRIP_TAC THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC (SPEC `h':clos_exp` CLOSP2AUX_ip_opt_interp1_cases) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[]);;

(* HOL4: insert_interp_esgc_free *)
let insert_interp_esgc_free = prove
 (`ALL clos_esgc_free (insert_interp xs) <=> ALL clos_esgc_free xs`,
  REWRITE_TAC[insert_interp_def] THEN SPEC_TAC(`xs:clos_exp list`,`xs:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC
    (SPEC `h:clos_exp` CLOSP2AUX_ip_insert_interp1_cases) THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  RVEQ_TAC THEN REWRITE_TAC[clos_esgc_free_def] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`ys:clos_exp list`,`ys:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC (SPEC `h':clos_exp` CLOSP2AUX_ip_opt_interp1_cases) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP opt_interp_lemma) THEN ASM_SIMP_TAC[]);;
