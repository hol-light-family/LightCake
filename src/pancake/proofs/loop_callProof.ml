(* ========================================================================= *)
(* loop_callProof: port of HOL4 pancake/proofs/loop_callProofScript.sml      *)
(* (CakeML v3479).                                                           *)
(* loop_call proof.                                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: compile_correct is                *)
(*   loop_callProof_compile_correct; comp is loop_call_comp.                 *)
(* - FRONT is BUTLAST.                                                       *)
(* - The proof of compile_correct is by induction on the semantics, with the *)
(*   tools of loopProps (PLOOPAUX_EVAL_CASES_TAC, ...); the induction        *)
(*   hypotheses are instantiated by PLOOPAUX_IHS2_TAC, which also matches   *)
(*   the other antecedents (the comp equation) to fix their variables.       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/backend_common.ml";;
needs "pancake/semantics/loopSem.ml";;
needs "pancake/semantics/loopProps.ml";;
needs "pancake/loop_call.ml";;

prioritize_num();;
type_invention_error := true;;

let labels_in_def = cake_def
  `labels_in (l:num spt) (locals:((A)word_loc)spt) <=>
     !n x. lookup n l = SOME x ==> lookup n locals = SOME (wl_Loc x 0)`;;

let PLOOPAUX_get_vars_length = prove
 (`!xs ys (s:(A,FFI)loop_state). get_vars xs s = SOME ys ==> LENGTH ys = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[get_vars_def; option_INJ] THEN REPEAT GEN_TAC THENL
  [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

let get_vars_front = prove
 (`!xs ys (s:(A,FFI)loop_state).
     get_vars xs s = SOME ys /\ ~(xs = []) ==>
     get_vars (BUTLAST xs) s = SOME (BUTLAST ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[get_vars_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `t:num list = []` THENL
  [RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[get_vars_def; option_INJ]) THEN RVEQ_TAC THEN
   REWRITE_TAC[BUTLAST; get_vars_def];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(a':((A)word_loc)list = [])` ASSUME_TAC THENL
  [ASM_MESON_TAC[PLOOPAUX_get_vars_length; LENGTH_EQ_NIL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[BUTLAST; get_vars_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a':((A)word_loc)list`; `s:(A,FFI)loop_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE]);;

let get_vars_last = prove
 (`!xs ys (s:(A,FFI)loop_state).
     get_vars xs s = SOME ys /\ ~(xs = []) ==>
     lookup (LAST xs) (loop_state_locals s) = SOME (LAST ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[get_vars_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_CASES_TAC `t:num list = []` THENL
  [RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[get_vars_def; option_INJ]) THEN RVEQ_TAC THEN
   ASM_REWRITE_TAC[LAST];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(a':((A)word_loc)list = [])` ASSUME_TAC THENL
  [ASM_MESON_TAC[PLOOPAUX_get_vars_length; LENGTH_EQ_NIL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LAST] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let evaluate_ShMem_neq_locals = prove
 (`loop_evaluate (loop_ShMem op v ad, (s:(A,FFI)loop_state)) = (res, s') /\ ~(v = n) /\
   ~(?x. res = SOME (loop_FinalFFI x)) /\ lookup n (loop_state_locals s) = x ==>
   lookup n (loop_state_locals s') = x`,
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[loop_evaluate_def; loop_sh_mem_op_def; loop_sh_mem_load_def;
              loop_sh_mem_store_def; loop_set_var_def; call_env_def] THEN
  REWRITE_TAC[is_load_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  FS[lookup_insert] THEN ASM_MESON_TAC[]);;

let evaluate_ShMem_not_load_locals = prove
 (`loop_evaluate (loop_ShMem op v ad, (s:(A,FFI)loop_state)) = (res, s') /\
   ~loop_call_is_load op /\ ~(?x. res = SOME (loop_FinalFFI x)) ==>
   loop_state_locals s = loop_state_locals s'`,
  STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  REWRITE_TAC[loop_call_is_load_def; is_load_def] THEN
  REWRITE_TAC[loop_evaluate_def; loop_sh_mem_op_def; loop_sh_mem_load_def;
              loop_sh_mem_store_def; loop_set_var_def; call_env_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  FS[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* compile_correct, by induction on the semantics                            *)
(* ------------------------------------------------------------------------- *)

let PLOOPAUX_IHS2_TAC (fin:tactic) : tactic = fun (asl,w as g) ->
  let facts = map (concl o snd) asl in
  let evs = filter (fun th -> PLOOPAUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists PLOOPAUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  let avoid = freesl (w :: facts @ flat (map (hyp o snd) asl)) in
  let inst_of ih0 e cj0 =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = GENL vs1 (SPECL vs1 ih0) in
    let vs,bod = strip_forall (concl ih) in
    let ant,_ = dest_imp bod in
    let cj = vsubst (zip vs1 vs0) cj0 in
    let (_,tmi,tyi) = term_match [] cj (concl e) in
    if exists (fun (a,b) -> not (a = b)) tyi ||
       exists (fun (t,v) -> not (mem v vs) && not (t = v)) tmi then failwith "" else
    let tmi = filter (fun (t,v) -> mem v vs) tmi in
    let extend tmi k =
      let k' = vsubst tmi k in
      let unb = filter (fun v -> mem v vs) (frees k') in
      if unb = [] then tmi else
      try let ext = tryfind (fun f ->
              let (_,tmi2,tyi2) = term_match [] k' f in
              if exists (fun (a,b) -> not (a = b)) tyi2 ||
                 exists (fun (t,v) -> not (mem v unb) && not (t = v)) tmi2
              then failwith ""
              else filter (fun (t,v) -> mem v unb) tmi2) facts in
          tmi @ ext
      with Failure _ -> tmi in
    let tmi = itlist (fun k acc -> extend acc k) (rev (conjuncts ant)) tmi in
    let ihi = INST tmi (SPEC_ALL ih) in
    let a,c = dest_imp (concl ihi) in
    if exists (fun v -> mem v vs) (frees c) then failwith "" else
    let rest = filter (fun v -> mem v vs) (subtract (frees a) (frees c)) in
    c, GENL rest ihi in
  let insts = flat (map (fun e ->
      flat (map (fun ih ->
          let _,bod = strip_forall (concl ih) in
          let cjs = filter PLOOPAUX_is_eval_eq (conjuncts(fst(dest_imp bod))) in
          mapfilter (fun cj -> inst_of ih e cj) cjs) ihs)) evs) in
  MAP_EVERY (fun (c,th) ->
      TRY (SUBGOAL_THEN c (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
            [MATCH_MP_TAC th THEN IL2AUX_EXISTS_ASM_TAC THEN fin THEN NO_TAC;
             ALL_TAC]))
    insts g;;

let PLOOPAUX_is_comp_eq tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "loop_call_comp"
   with Failure _ -> false);;

(* the comp assumption of a constructor: unfold it once and split (the     *)
(* assumption is kept)                                                     *)

let PLOOPAUX_COMP_CASES_TAC : tactic =
  FIRST_ASSUM(MP_TAC o check (fun th -> PLOOPAUX_is_comp_eq (concl th) &&
                not (is_var (rand(lhs(concl th)))))) THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[loop_call_comp_def] THENC
           REWRITE_CONV(PLOOPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN RVEQ_TAC;;

(* comp of loop_Assign n e: split e (comp has a clause for loop_Var) *)

let PLOOPAUX_ASSIGN_EXP_TAC : tactic = fun (asl,w as g) ->
  try let th = find (fun th -> PLOOPAUX_is_comp_eq (concl th) &&
                       (let p = rand(lhs(concl th)) in
                        let f,args = strip_comb p in
                        fst(dest_const f) = "loop_Assign" && is_var (el 1 args)))
                    (map snd asl) in
      let e = el 1 (snd(strip_comb(rand(lhs(concl th))))) in
      CASES_ON e g
  with Failure _ -> ALL_TAC g;;

(* for a conditional program if b then c1 else c2 in an assumption and      *)
(* assumptions f c1 = r1 and f c2 = r2, add f (if b then c1 else c2) =      *)
(* (if b then r1 else r2) (pairs componentwise)                            *)

let PLOOPAUX_COND_EQ_FACT_TAC : tactic = fun (asl,w as g) ->
  let is_prog_cond t =
    is_cond t && (try fst(dest_type(type_of t)) = "loop_prog" with Failure _ -> false) in
  let conds = setify (flat (map (fun (_,th) ->
                  if is_forall (concl th) then [] else find_terms is_prog_cond (concl th)) asl)) in
  let facts = filter is_eq (map (concl o snd) asl) in
  let mk c =
    let b,(x,y) = dest_cond c in
    mapfilter (fun f ->
        let l1,r1 = dest_eq f in
        if free_in x l1 && not (free_in y l1) && not (free_in c l1) then
          let l2 = subst [y,x] l1 in
          let f2 = find (fun f' -> lhs f' = l2) facts in
          let r2 = rhs f2 in
          let r = if is_pair r1 && is_pair r2 then
                    let a1,b1 = dest_pair r1 and a2,b2 = dest_pair r2 in
                    mk_pair(mk_cond(b,a1,a2), mk_cond(b,b1,b2))
                  else mk_cond(b,r1,r2) in
          mk_eq(subst [c,x] l1, r)
        else failwith "") facts in
  let tms = setify (flat (map mk conds)) in
  MAP_EVERY (fun tm -> SUBGOAL_THEN tm ASSUME_TAC THENL
                         [COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) tms g;;

let PLOOPAUX_cut_res_not_error = prove
 (`!live r (s:(A,FFI)loop_state) res t.
     cut_res (live:(B)spt) (r:((W)loop_result)option,s) = (res,t)
     ==> ~(res = SOME loop_Error) ==> ~(r = SOME loop_Error)`,
  REWRITE_TAC[cut_res_def] THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_MESON_TAC[]);;

let PLOOPAUX_exit_loop_not_error = prove
 (`!r:((W)loop_result)option.
     ~(loop_exit_loop r = SOME loop_Error) ==> ~(r = SOME loop_Error)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((W)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[loop_exit_loop_def] THEN
  STRUCT_CASES_TAC (ISPEC `a:(W)loop_result` (cases "loop_result")) THEN
  REWRITE_TAC(loop_exit_loop_def :: PLOOPAUX_result_rws));;

let PLOOPAUX_labels_in_LN = prove
 (`!locals:((A)word_loc)spt. labels_in LN locals`,
  REWRITE_TAC[labels_in_def; lookup_def; option_DISTINCT]);;

let PLOOPAUX_labels_ins = prove
 (`!L (locs:((A)word_loc)spt) v x.
     labels_in L locs /\ lookup v L = NONE ==> labels_in L (insert v x locs)`,
  REWRITE_TAC[labels_in_def; lookup_insert] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT]);;

let PLOOPAUX_labels_del = prove
 (`!L (locs:((A)word_loc)spt) v. labels_in L locs ==> labels_in (delete v L) locs`,
  REWRITE_TAC[labels_in_def; lookup_delete] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT]);;

let PLOOPAUX_labels_ins_ins = prove
 (`!L (locs:((A)word_loc)spt) v y.
     labels_in L locs ==> labels_in (insert v y L) (insert v (wl_Loc y 0) locs)`,
  REWRITE_TAC[labels_in_def; lookup_insert] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  ASM_MESON_TAC[]);;

let PLOOPAUX_labels_ld_ai = prove
 (`!L (locs:((A)word_loc)spt) vs xs.
     labels_in L locs ==> labels_in (list_delete vs L) (alist_insert vs xs locs)`,
  REWRITE_TAC[labels_in_def; lookup_list_delete] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_SIMP_TAC[PLOOPAUX_lookup_alist_insert_not_MEM]);;

let PLOOPAUX_is_labels_in tm =
  try fst(dest_const(fst(strip_comb tm))) = "labels_in" with Failure _ -> false;;

(* a goal labels_in L locs from labels_in l s.locals: the label map and the *)
(* locals are taken apart (insert, delete, list_delete, alist_insert)       *)

let PLOOPAUX_LABELS_STEP_TAC : tactic =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC PLOOPAUX_labels_ins THEN CONJ_TAC THENL
          [ALL_TAC; REWRITE_TAC[lookup_delete; lookup_def; lookup_list_delete; COND_ID] THEN
                    ASM_REWRITE_TAC[COND_ID] THEN
                    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC];
         MATCH_MP_TAC PLOOPAUX_labels_ins_ins;
         MATCH_MP_TAC PLOOPAUX_labels_ld_ai;
         MATCH_MP_TAC PLOOPAUX_labels_del];;

let PLOOPAUX_LABELS_TAC : tactic = fun (asl,w as g) ->
  if not (PLOOPAUX_is_labels_in w) then failwith "PLOOPAUX_LABELS_TAC" else
  (FIRST_ASSUM(fun th ->
     if not (PLOOPAUX_is_labels_in (concl th)) then NO_TAC else
     IMP_RES_TAC (REWRITE_RULE[labels_in_def] th)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[loop_eval_def]) THEN
   REPEAT(FIRST_X_ASSUM(fun th1 ->
     FIRST_X_ASSUM(fun th2 ->
       let l1,r1 = dest_eq(concl th1) and l2,r2 = dest_eq(concl th2) in
       if l1 = l2 && not (r1 = r2) then
         ASSUME_TAC th1 THEN ASSUME_TAC (TRANS (SYM th1) th2)
       else NO_TAC))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
   REPEAT PLOOPAUX_LABELS_STEP_TAC) g;;

let PLOOPAUX_comp_loop_LN = prove
 (`!l ns (p:(A)loop_prog) ms.
     loop_call_comp l (loop_Loop ns p ms) = loop_call_comp LN (loop_Loop ns p ms)`,
  REWRITE_TAC[loop_call_comp_def]);;

let PLOOPAUX_CC_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  PLOOPAUX_ASSIGN_EXP_TAC THEN
  PLOOPAUX_COMP_CASES_TAC THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[PLOOPAUX_comp_loop_LN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN PLOOPAUX_COND_EQ_FACT_TAC THEN
  IMP_RES_TAC PLOOPAUX_cut_res_not_error THEN
  IMP_RES_TAC PLOOPAUX_exit_loop_not_error THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_IHS2_TAC (REPEAT COND_CASES_TAC THEN
                     ASM_REWRITE_TAC (PLOOPAUX_labels_in_LN :: PLOOPAUX_result_rws)) THEN
  PLOOPAUX_IHS2_TAC (REPEAT COND_CASES_TAC THEN
                     ASM_REWRITE_TAC (PLOOPAUX_labels_in_LN :: PLOOPAUX_result_rws));;

let PLOOPAUX_CC_FIN_TAC : tactic =
  IMP_RES_TAC PLOOPAUX_mem_store_locals THEN
  PLOOPAUX_DROP_IHS_TAC THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  FS[PLOOPAUX_labels_in_LN; loop_set_var_def; set_vars_def; loop_set_globals_def;
     call_env_def; loop_dec_clock_def; loop_eval_def; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN TRY PLOOPAUX_LABELS_TAC;;

let PLOOPAUX_CC_ARITH_TAC : tactic =
  GEN_TAC THEN QCASES_ON "arith" THEN
  PLOOPAUX_EVAL_CASES_TAC THEN PLOOPAUX_COMP_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN ASM_REWRITE_TAC[option_CASE] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "loop_arith" with Failure _ -> false)) THEN
  REWRITE_TAC[loop_arith_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[loop_set_var_def] THEN SIMP[] THEN
  PLOOPAUX_LABELS_TAC;;

let PLOOPAUX_find_code_front = prove
 (`!vs n (code:(num list#(A)loop_prog)spt).
     ~(vs = []) /\ LAST vs = wl_Loc n 0 ==>
     find_code (SOME n) (BUTLAST vs) code = find_code NONE (vs:((A)word_loc)list) code`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[find_code_def] THEN
  REWRITE_TAC[case_def "word_loc"] THEN
  SUBGOAL_THEN `LENGTH (vs:((A)word_loc)list) = LENGTH (BUTLAST vs) + 1` SUBST1_TAC THENL
  [UNDISCH_TAC `~(vs:((A)word_loc)list = [])` THEN
   SPEC_TAC(`vs:((A)word_loc)list`,`vs:((A)word_loc)list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; BUTLAST; LENGTH] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ASM_SIMP_TAC[] THEN ARITH_TAC;
   REWRITE_TAC[EQ_ADD_RCANCEL]]);;

let PLOOPAUX_call_clause = PLOOPAUX_eval_clause "loop_Call";;

let PLOOPAUX_call_front_eval = prove
 (`!ret n args handler (s:(A,FFI)loop_state) vs.
     get_vars args s = SOME vs /\ ~(args = []) /\
     lookup (LAST args) (loop_state_locals s) = SOME (wl_Loc n 0) ==>
     loop_evaluate (loop_Call ret (SOME n) (BUTLAST args) handler, s) =
     loop_evaluate (loop_Call ret NONE args handler, s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`args:num list`; `vs:((A)word_loc)list`; `s:(A,FFI)loop_state`]
         get_vars_front) THEN
  MP_TAC(ISPECL [`args:num list`; `vs:((A)word_loc)list`; `s:(A,FFI)loop_state`]
         get_vars_last) THEN
  ASM_REWRITE_TAC[option_INJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(vs:((A)word_loc)list = [])` ASSUME_TAC THENL
  [ASM_MESON_TAC[PLOOPAUX_get_vars_length; LENGTH_EQ_NIL]; ALL_TAC] THEN
  REWRITE_TAC[PLOOPAUX_call_clause] THEN ASM_REWRITE_TAC[option_CASE] THEN
  MP_TAC(ISPECL [`vs:((A)word_loc)list`; `n:num`; `loop_state_code (s:(A,FFI)loop_state)`]
         PLOOPAUX_find_code_front) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[]);;

(* the Call case: comp only resolves the target of a call with no target  *)
(* whose last argument holds a known label                                *)

let PLOOPAUX_CC_CALL_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (PLOOPAUX_is_comp_eq o concl)) THEN
  REWRITE_TAC[loop_call_comp_def] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)
    (ISPEC `dest:num option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; PAIR_EQ] THENL
  [ALL_TAC; STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[PLOOPAUX_labels_in_LN]] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `h:num` (X_CHOOSE_THEN `t:num list` SUBST_ALL_TAC))
    (ISPEC `argvars:num list` list_CASES) THEN
  REWRITE_TAC[list_CASE] THENL
  [STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (PLOOPAUX_is_eval_eq o concl)) THEN
   REWRITE_TAC[PLOOPAUX_call_clause; get_vars_def; find_code_def; option_CASE; PAIR_EQ] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; option_CASE] THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `n:num` (fun th -> REWRITE_TAC[th; option_CASE] THEN ASSUME_TAC th))
    (ISPEC `lookup (LAST (CONS h t)) (l:num spt)` (cases "option")) THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[PLOOPAUX_labels_in_LN] THEN
  DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `vs:((A)word_loc)list`)
    (ISPEC `get_vars (CONS h t) (s:(A,FFI)loop_state)` (cases "option")) THENL
  [FIRST_X_ASSUM(MP_TAC o check (PLOOPAUX_is_eval_eq o concl)) THEN
   ASM_REWRITE_TAC[PLOOPAUX_call_clause; option_CASE; PAIR_EQ] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`ret:(num list#num_set)option`; `n:num`; `CONS h t:num list`;
       `handler:(num#(A)loop_prog#(A)loop_prog#num_set)option`; `s:(A,FFI)loop_state`;
       `vs:((A)word_loc)list`] PLOOPAUX_call_front_eval) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
   FIRST_X_ASSUM(MP_TAC o check (PLOOPAUX_is_labels_in o concl)) THEN
   REWRITE_TAC[labels_in_def] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];;

(* HOL4: compile_correct *)

let loop_callProof_compile_correct = prove
 (`!v (v1:(A,FFI)loop_state) res s1 l p nl.
     loop_evaluate (v,v1) = (res,s1) /\ ~(res = SOME loop_Error) /\
     loop_call_comp l v = (p,nl) /\ labels_in l (loop_state_locals v1) ==>
     loop_evaluate (p,v1) = (res,s1) /\ labels_in nl (loop_state_locals s1)`,
  REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN
  (fun (asl,w as g) ->
     let has c = can (find_term (fun t -> try fst(dest_const t) = c
                                          with Failure _ -> false)) w in
     if has "loop_Arith" then PLOOPAUX_CC_ARITH_TAC g
     else if has "loop_Call" then PLOOPAUX_CC_CALL_TAC g
     else (PLOOPAUX_CC_TAC THEN PLOOPAUX_CC_FIN_TAC) g));;
