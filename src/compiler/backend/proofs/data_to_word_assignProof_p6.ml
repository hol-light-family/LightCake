(* ========================================================================= *)
(* data_to_word_assignProof_p6: part 6 of 6 (HOL4 lines 14006-16966) of the  *)
(* port of HOL4 compiler/backend/proofs/data_to_word_assignProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p6 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_assignProof.ml needs the last.                *)
(* ASP6AUX_ names are local helpers of this part.                           *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_assignProof_p5.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 6: HOL4 lines 14006-16966 ===== *)

(* ------------------------------------------------------------------------- *)
(* Helpers of this part (ASP6AUX_ names, asp6_ functions).                   *)
(* ------------------------------------------------------------------------- *)

(* is tm an application of the constant named nm *)
let asp6_is_app nm tm =
  try let f,_ = strip_comb tm in is_const f && fst (dest_const f) = nm
  with Failure _ -> false;;

(* the assumption whose conclusion is an application of nm *)
let asp6_asm_app nm = fun th -> asp6_is_app nm (concl th);;

let ASP6AUX_state_rel_facts = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     good_dimindex (:A) /\ shift_length c < dimindex (:A) /\
     wl_state_ffi t = data_state_ffi s /\
     Globals IN FDOM (wl_state_store t) /\
     IS_SOME (data_state_tstamps s) /\
     option_le (wl_state_stack_max t) (data_state_stack_max s)`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; ALL] THEN MESON_TAC[]);;

(* the introduction of an assign proof: op (by intro), names_opt = NONE,     *)
(* x = s; leaves the hypotheses of assign_thm_goal as assumptions           *)

let ASP6AUX_INTRO_TAC (intro:tactic) : tactic =
  REPEAT GEN_TAC THEN intro THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def;
     distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op";
     distinctness "mem_op"; distinctness "glob_op"; distinctness "int_op";
     distinctness "word_op"]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    try let l,r = dest_eq (concl th) in
        fst (dest_var l) = "names_opt" && r = `NONE:(1 spt)option`
    with Failure _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "data_cut_state_opt" (lhs (concl th)) with Failure _ -> false)) THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM);;

let ASP6AUX_DO_STACK_FIELDS = prove
 (`!op vs (s:(C,FFI)data_state).
     data_state_global (do_stack op vs (do_lim_safe s op vs)) = data_state_global s /\
     data_state_refs (do_stack op vs (do_lim_safe s op vs)) = data_state_refs s /\
     data_state_code (do_stack op vs (do_lim_safe s op vs)) = data_state_code s /\
     data_state_tstamps (do_stack op vs (do_lim_safe s op vs)) = data_state_tstamps s /\
     data_state_space (do_stack op vs (do_lim_safe s op vs)) = data_state_space s /\
     data_state_ffi (do_stack op vs (do_lim_safe s op vs)) = data_state_ffi s /\
     data_state_limits (do_stack op vs (do_lim_safe s op vs)) = data_state_limits s /\
     data_state_locals (do_stack op vs (do_lim_safe s op vs)) = data_state_locals s /\
     data_state_clock (do_stack op vs (do_lim_safe s op vs)) = data_state_clock s /\
     data_state_handler (do_stack op vs (do_lim_safe s op vs)) = data_state_handler s /\
     data_state_compile (do_stack op vs (do_lim_safe s op vs)) = data_state_compile s /\
     data_state_compile_oracle (do_stack op vs (do_lim_safe s op vs)) =
       data_state_compile_oracle s /\
     data_state_stack (do_stack op vs (do_lim_safe s op vs)) = data_state_stack s /\
     data_state_stack_frame_sizes (do_stack op vs (do_lim_safe s op vs)) =
       data_state_stack_frame_sizes s /\
     data_state_locals_size (do_stack op vs (do_lim_safe s op vs)) =
       data_state_locals_size s /\
     data_state_peak_heap_length (do_stack op vs (do_lim_safe s op vs)) =
       data_state_peak_heap_length s /\
     option_le (data_state_stack_max s)
       (data_state_stack_max (do_stack op vs (do_lim_safe s op vs)))`,
  REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; option_le_max_right; option_le_refl]);;

(* proves  data_do_app op vs s = Rval (v,s2) <=> ...  for an operator op    *)
(* with no space reset and no space requirement (do_app_aux unfolded)       *)
let ASP6AUX_DO_APP_TAC op_tm : tactic =
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [op_tm; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "int_op"; distinctness "block_op";
              distinctness "word_op"; distinctness "mem_op"; distinctness "glob_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS] THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; case_eq "option"; case_eq "bvl_ref";
              COND_CASE_EQ; distinctness "result"; injectivity "result"; PAIR_EQ;
              RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Symbolic evaluation of wordLang code (the work of HOL4's eval_tac and of *)
(* fs/simp with wordSemTheory.evaluate_def).                                *)
(* asp6_ev_conv thl evaluates a term wl_evaluate (p,s) with p a concrete     *)
(* program: it unfolds the clause of the head constructor, simplifies with  *)
(* the project simpset and thl, and goes on with the parts of the result    *)
(* that are again such evaluations; wl_Seq c1 c2 with c1 evaluating to      *)
(* (NONE,s1) becomes wl_evaluate (c2,s1).  The constructors listed in       *)
(* asp6_ev_stop are not unfolded.                                           *)
(* ------------------------------------------------------------------------- *)

let asp6_ev_table =
  map (fun th -> let l = lhs (concl (SPEC_ALL th)) in
                 fst (dest_const (fst (strip_comb (fst (dest_pair (rand l)))))), th)
      (CONJUNCTS wl_evaluate_def);;

let ASP6AUX_ev_Seq = assoc "wl_Seq" asp6_ev_table;;

let asp6_ev_stop = ref ["wl_Call"; "MustTerminate"];;

let asp6_is_ev tm =
  match tm with
    Comb(Const("wl_evaluate",_),arg) ->
      (try let p,_ = dest_pair arg in
           let h = fst (strip_comb p) in
           is_const h && (let n = fst (dest_const h) in
                          exists (fun (m,_) -> m = n) asp6_ev_table &&
                          not (mem n !asp6_ev_stop))
       with Failure _ -> false)
  | _ -> false;;

(* apply c to the closed subterms of tm (no variable bound in tm free in    *)
(* them), outermost first, once at each place                               *)
let rec asp6_closed_conv bvs c tm =
  try (if exists (fun v -> vfree_in v tm) bvs then failwith "" else c tm)
  with Failure _ ->
  match tm with
    Comb(f,x) ->
      (match (try Some (asp6_closed_conv bvs c f) with Failure _ -> None),
             (try Some (asp6_closed_conv bvs c x) with Failure _ -> None) with
         None, None -> failwith "asp6_closed_conv"
       | Some a, None -> AP_THM a x
       | None, Some b -> AP_TERM f b
       | Some a, Some b -> MK_COMB(a,b))
  | Abs(v,_) -> ABS_CONV (asp6_closed_conv (v::bvs) c) tm
  | _ -> failwith "asp6_closed_conv";;

let asp6_is_none tm = is_const tm && fst (dest_const tm) = "NONE";;

let rec asp6_ev_conv thl tm =
  if not (asp6_is_ev tm) then failwith "asp6_ev_conv" else
  let p,s = dest_pair (rand tm) in
  let hd,args = strip_comb p in
  let name = fst (dest_const hd) in
  if name = "wl_Seq" then
    let c1 = el 0 args and c2 = el 1 args in
    let tm1 = mk_comb(rator tm, mk_pair(c1,s)) in
    let th1 = try asp6_ev_conv thl tm1 with Failure _ -> REFL tm1 in
    let r1 = rhs (concl th1) in
    if is_pair r1 && asp6_is_none (fst (dest_pair r1)) then
      let s1 = snd (dest_pair r1) in
      let th2 = MATCH_MP (ISPECL [c1; c2; s; s1] IL2AUX_evaluate_Seq_NONE) th1 in
      TRANS th2 (asp6_ev_rest thl (rhs (concl th2)))
    else
      let th2 = REWR_CONV ASP6AUX_ev_Seq tm in
      let th3 = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV
                  (fun t -> if t = tm1 then th1 else failwith ""))) th2 in
      let th4 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV thl)) th3 in
      TRANS th4 (asp6_ev_rest thl (rhs (concl th4)))
  else
    let cls = map snd (filter (fun (m,_) -> m = name) asp6_ev_table) in
    let th1 = tryfind (fun cl -> REWR_CONV cl tm) cls in
    let th2 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV thl)) th1 in
    TRANS th2 (asp6_ev_rest thl (rhs (concl th2)))
and asp6_ev_rest thl tm =
  try let th = asp6_closed_conv [] (asp6_ev_conv thl) tm in
      TRANS th (asp6_ev_rest thl (rhs (concl th)))
  with Failure _ -> REFL tm;;

(* evaluate the closed evaluations of the goal, with the assumptions *)
let ASP6AUX_EV_TAC thl : tactic = fun (asl,w as g) ->
  CONV_TAC (asp6_closed_conv [] (asp6_ev_conv (thl @ map snd asl))) g;;

(* the goal ?q r. (q0,r0) = (q,r) /\ P q r of an evaluation (or with the    *)
(* pair equation split into q0 = q /\ r0 = r): q, r := q0, r0               *)
let ASP6AUX_QR_TAC : tactic = fun (asl,w as g) ->
  let q,b = dest_exists w in
  let r,b2 = dest_exists b in
  let c1 = fst (dest_conj b2) in
  let q0,r0 =
    if is_eq c1 && is_pair (lhs c1) then dest_pair (lhs c1)
    else let e1,e2 = dest_conj c1 in lhs e1, lhs e2 in
  (EXISTS_TAC q0 THEN EXISTS_TAC r0 THEN REWRITE_TAC[option_DISTINCT; PAIR_EQ]) g;;


let ASP6AUX_get_vars_1 = prove
 (`!args (s:A spt) x1.
     data_get_vars args s = SOME [x1] <=> ?a1. args = [a1] /\ lookup a1 s = SOME x1`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `args:num list` list_CASES) THEN
  REWRITE_TAC[get_vars_SOME_IFF_data_eq; NOT_CONS_NIL; CONS_11; data_get_var_def] THEN
  STRUCT_CASES_TAC(ISPEC `t:num list` list_CASES) THEN
  REWRITE_TAC[get_vars_SOME_IFF_data_eq; NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[NOT_CONS_NIL]);;

let ASP6AUX_state_rel_get_var1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs a1 v1.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     lookup a1 (data_state_locals s) = SOME v1 ==>
     ?w1. lookup (adjust_var a1) (wl_state_locals t) = SOME w1 /\
          memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
            (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
            (CONS (v1,w1) (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `[a1:num]`; `[v1:data_v]`]
    ASP4AUX_state_rel_get_vars) THEN
  ASM_REWRITE_TAC[ASP6AUX_get_vars_1] THEN ANTS_TAC THENL
   [EXISTS_TAC `a1:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `ws:(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC 0)`; SUC_INJ; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `h:A word_loc` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; wl_get_var_def; ZIP; APPEND]) THEN
  ASM_REWRITE_TAC[APPEND]);;

let ASP6AUX_state_rel_final = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w
    (s2:(C,FFI)data_state) (t1:(A,C,FFI)wl_state) L.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     wl_state_locals t1 = insert (adjust_var dest) w L /\
     sptree_inter L (adjust_set (data_state_locals s)) =
       sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)) /\
     lookup 0 L = lookup 0 (wl_state_locals t) /\
     (!n. IS_SOME (lookup (adjust_var n) (wl_state_locals t)) ==>
          IS_SOME (lookup (adjust_var n) L)) /\
     wl_state_ffi t1 = wl_state_ffi t /\
     wl_state_clock t1 = wl_state_clock t /\
     wl_state_handler t1 = wl_state_handler t /\
     wl_state_gc_fun t1 = wl_state_gc_fun t /\
     wl_state_code t1 = wl_state_code t /\
     wl_state_compile t1 = wl_state_compile t /\
     wl_state_compile_oracle t1 = wl_state_compile_oracle t /\
     wl_state_code_buffer t1 = wl_state_code_buffer t /\
     wl_state_data_buffer t1 = wl_state_data_buffer t /\
     wl_state_stack t1 = wl_state_stack t /\
     wl_state_stack_size t1 = wl_state_stack_size t /\
     wl_state_locals_size t1 = wl_state_locals_size t /\
     wl_state_stack_limit t1 = wl_state_stack_limit t /\
     wl_state_stack_max t1 = wl_state_stack_max t /\
     wl_state_be t1 = wl_state_be t /\
     wl_state_mdomain t1 = wl_state_mdomain t /\
     (!k. MEM k [CodeBuffer; CodeBufferEnd; BitmapBuffer; BitmapBufferEnd; HeapLength] ==>
          FLOOKUP (wl_state_store t1) k = FLOOKUP (wl_state_store t) k) /\
     Globals IN FDOM (wl_state_store t1) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s2) (wl_state_store t1) (wl_state_memory t1) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s2),FAPPLY (wl_state_store t1) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2) t1 NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  REWRITE_TAC[lookup_insert; adjust_var_NEQ; adjust_var_11] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [UNDISCH_TAC `code_oracle_rel c (data_state_compile (s:(C,FFI)data_state))
       (data_state_compile_oracle s) (wl_state_store (t:(A,C,FFI)wl_state))
       (wl_state_compile t) (wl_state_compile_oracle t) (wl_state_code_buffer t)
       (wl_state_data_buffer t)` THEN
    REWRITE_TAC[code_oracle_rel_def] THEN ASM_SIMP_TAC[MEM] THEN NO_TAC;
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    (fun (asl,w as g) -> if asp6_is_app "option_le" w then MP5AUX_HEAD_MESON_TAC[option_le_trans] g
                         else failwith "not option_le");
    UNDISCH_TAC `limits_inv (data_state_limits (s:(C,FFI)data_state))
       (FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength) (wl_state_stack_limit t)
       (data_to_word_config_len_size c) (data_to_word_config_has_fp_ops c)
       (data_to_word_config_has_fp_tern c)` THEN
    ASM_SIMP_TAC[MEM] THEN NO_TAC;
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC memory_rel_insert THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

let ASP6AUX_get_vars_2 = prove
 (`!args (s:A spt) x1 x2.
     data_get_vars args s = SOME [x1; x2] <=>
     ?a1 a2. args = [a1; a2] /\ lookup a1 s = SOME x1 /\ lookup a2 s = SOME x2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC 0) = 2`; LENGTH_EQ_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `a2:num` SUBST_ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a1:num`; `a2:num`] THEN POP_ASSUM MP_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[data_get_vars_def; data_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup a1 (s:A spt)` THEN CASES_ON `lookup a2 (s:A spt)` THEN
  TRY(CASES_ON `lookup a3 (s:A spt)`) THEN
  CASE_REWRITE_TAC[option_INJ; option_DISTINCT; CONS_11]);;

let ASP6AUX_get_vars_3 = prove
 (`!args (s:A spt) x1 x2 x3.
     data_get_vars args s = SOME [x1; x2; x3] <=>
     ?a1 a2 a3. args = [a1; a2; a3] /\ lookup a1 s = SOME x1 /\ lookup a2 s = SOME x2 /\
                lookup a3 s = SOME x3`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `SUC (SUC (SUC 0)) = 3`; LENGTH_EQ_3] THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `a3:num`
      SUBST_ALL_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`a1:num`; `a2:num`; `a3:num`] THEN POP_ASSUM MP_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[data_get_vars_def; data_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `lookup a1 (s:A spt)` THEN CASES_ON `lookup a2 (s:A spt)` THEN
  TRY(CASES_ON `lookup a3 (s:A spt)`) THEN
  CASE_REWRITE_TAC[option_INJ; option_DISTINCT; CONS_11]);;

let ASP6AUX_state_rel_get_var2 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs a1 a2 v1 v2.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     lookup a1 (data_state_locals s) = SOME v1 /\
     lookup a2 (data_state_locals s) = SOME v2 ==>
     ?w1 w2. lookup (adjust_var a1) (wl_state_locals t) = SOME w1 /\
          lookup (adjust_var a2) (wl_state_locals t) = SOME w2 /\
          memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
            (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
            (CONS (v1,w1) (CONS (v2,w2) (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `[a1:num; a2]`;
                 `[v1:data_v; v2]`] ASP4AUX_state_rel_get_vars) THEN
  ASM_REWRITE_TAC[ASP6AUX_get_vars_2] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a1:num`; `a2:num`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `ws:(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `t':(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n) /\ ~(SUC n = 0)`; SUC_INJ; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`h:A word_loc`; `h':A word_loc`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; wl_get_var_def; ZIP; APPEND]) THEN
  ASM_REWRITE_TAC[APPEND]);;

let ASP6AUX_state_rel_get_var3 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs a1 a2 a3 v1 v2 v3.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     lookup a1 (data_state_locals s) = SOME v1 /\
     lookup a2 (data_state_locals s) = SOME v2 /\
     lookup a3 (data_state_locals s) = SOME v3 ==>
     ?w1 w2 w3. lookup (adjust_var a1) (wl_state_locals t) = SOME w1 /\
          lookup (adjust_var a2) (wl_state_locals t) = SOME w2 /\
          lookup (adjust_var a3) (wl_state_locals t) = SOME w3 /\
          memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
            (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
            (CONS (v1,w1) (CONS (v2,w2) (CONS (v3,w3) (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `[a1:num; a2; a3]`;
                 `[v1:data_v; v2; v3]`] ASP4AUX_state_rel_get_vars) THEN
  ASM_REWRITE_TAC[ASP6AUX_get_vars_3] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a1:num`; `a2:num`; `a3:num`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `ws:(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `t':(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n) /\ ~(SUC n = 0)`; SUC_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `t'':(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n) /\ ~(SUC n = 0)`; SUC_INJ; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`h:A word_loc`; `h':A word_loc`; `h'':A word_loc`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; wl_get_var_def; ZIP; APPEND]) THEN
  ASM_REWRITE_TAC[APPEND]);;

(* the word values of the arguments: for args a1 .. ak (k = 1, 2, 3) with   *)
(* assumptions lookup ai (data_state_locals s) = SOME vi, the assumptions    *)
(* lookup (adjust_var ai) (wl_state_locals t) = SOME wi and the memory_rel   *)
(* with (v1,w1) ... (vk,wk) in front (wi named by the second list)           *)
let ASP6AUX_GET_VARS_TAC (avs:term list) (wvs:term list) : tactic = fun (asl,w as g) ->
  let find_lookup a =
    snd (find (fun (_,th) ->
      try let l = lhs (concl th) in
          asp6_is_app "lookup" l && rand (rator l) = a &&
          asp6_is_app "data_state_locals" (rand l)
      with Failure _ -> false) asl) in
  let srel = snd (find (fun (_,th) ->
      asp6_is_app "data_to_word_gcProof_state_rel" (concl th)) asl) in
  let lem = match length avs with
      1 -> ASP6AUX_state_rel_get_var1 | 2 -> ASP6AUX_state_rel_get_var2
    | 3 -> ASP6AUX_state_rel_get_var3 | _ -> failwith "ASP6AUX_GET_VARS_TAC" in
  let th = MATCH_MP lem (end_itlist CONJ (srel :: map find_lookup avs)) in
  let rec chooses vs = match vs with
      [] -> STRIP_ASSUME_TAC
    | v::rest -> X_CHOOSE_THEN v (chooses rest) in
  chooses wvs th g;;

(* the end of an assign proof whose word state is wl_set_var (adjust_var    *)
(* dest) w t and whose data state differs from s only in stack_max and       *)
(* safety: the memory_rel for the new value comes from the memory_rel        *)
(* assumption that contains the term tm, by memory_rel_rearrange             *)
let ASP6AUX_FINISH_SIMPLE_TAC (tm:term) : tactic =
  ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP1AUX_state_rel_set_var THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN ASM_REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
    can (find_term (fun u -> u = tm)) (concl th))) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];;

(* memory_rel_rearrange with the memory_rel assumption first *)
let ASP6AUX_memory_rel_rearrange = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm xs ys.
     memory_rel c be ts refs sp st m dm xs ==>
     (!x. MEM x ys ==> MEM x xs) ==>
     memory_rel c be ts refs sp st m dm ys`,
  MESON_TAC[memory_rel_rearrange]);;

(* the end of an assign proof with ASP6AUX_state_rel_final: the word value  *)
(* w and the locals L under it; leaves the memory_rel goal (and what the     *)
(* rewriting does not solve)                                                 *)
let ASP6AUX_FINISH_FINAL_TAC (w:term) (lc:term) : tactic =
  ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final THEN
  MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; w; lc] THEN
  ASM_REWRITE_TAC[wl_set_var_def; wl_set_store_def; wl_state_INFO.ri_accfupds;
                  data_state_INFO.ri_accfupds; K_THM; ASP6AUX_DO_STACK_FIELDS;
                  FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"; MEM;
                  FAPPLY_FUPDATE_THM];;

let ASP6AUX_inst_Load8 =
  CAKE_SIMP_CONV [wl_inst_def] `wl_inst (Mem Load8 r (Addr a w)) (s:(A,C,FFI)wl_state)`;;

let ASP6AUX_inst_Store8 =
  CAKE_SIMP_CONV [wl_inst_def] `wl_inst (Mem Store8 r (Addr a w)) (s:(A,C,FFI)wl_state)`;;

let ASP6AUX_shl_zx_byte = prove
 (`!b:byte. good_dimindex (:A) ==> word_shl (word_zx b:A word) 2 = word (4 * val b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  REWRITE_TAC[GSYM dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val (b:byte) < 2 EXP 8` ASSUME_TAC THENL
   [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP 10 <= dimword (:A)` ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def; LE_EXP] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (b:byte) MOD dimword (:A) = val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `2 EXP 10 <= dimword (:A)` THEN
    UNDISCH_TAC `val (b:byte) < 2 EXP 8` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    REWRITE_TAC[]]);;

(* the fields of wl_set_var v w s and wl_set_store k w s *)
let ASP6AUX_set_var_fields =
  let names = map (fun (f,_,_) -> f) wl_state_INFO.ri_fields in
  let cl f = if f = "locals" then
               "wl_state_locals (wl_set_var v w s) = insert v w (wl_state_locals s)"
             else "wl_state_" ^ f ^ " (wl_set_var v w s) = wl_state_" ^ f ^ " s" in
  let tm = parse_term ("!v (w:A word_loc) (s:(A,C,FFI)wl_state). " ^
                       String.concat " /\\ " (map cl names)) in
  prove(tm, REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM]);;

let ASP6AUX_set_store_fields =
  let names = map (fun (f,_,_) -> f) wl_state_INFO.ri_fields in
  let cl f = if f = "store" then
               "wl_state_store (wl_set_store k w s) = wl_state_store s |+ (k,w)"
             else "wl_state_" ^ f ^ " (wl_set_store k w s) = wl_state_" ^ f ^ " s" in
  let tm = parse_term ("!k (w:A word_loc) (s:(A,C,FFI)wl_state). " ^
                       String.concat " /\\ " (map cl names)) in
  prove(tm, REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM]);;

(* small shift amounts on a good word size *)
let ASP6AUX_good_dimindex_small = prove
 (`good_dimindex (:A) ==>
   (!k. k < 32 ==> val (word k:A word) = k) /\
   (!k. k < 32 ==> ~(k >= dimindex (:A)))`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD] THEN REPEAT STRIP_TAC THEN
  TRY(MATCH_MP_TAC MOD_LT) THEN
  TRY(MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `32` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 5` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_ARITH_TAC);;

let ASP6AUX_state_rel_final2 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w
    (s2:(C,FFI)data_state) (t1:(A,C,FFI)wl_state).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     sptree_inter (wl_state_locals t1) (adjust_set (data_state_locals s)) =
       sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)) /\
     lookup 0 (wl_state_locals t1) = lookup 0 (wl_state_locals t) /\
     (!n. IS_SOME (lookup (adjust_var n) (wl_state_locals t)) ==>
          IS_SOME (lookup (adjust_var n) (wl_state_locals t1))) /\
     wl_state_ffi t1 = wl_state_ffi t /\
     wl_state_clock t1 = wl_state_clock t /\
     wl_state_handler t1 = wl_state_handler t /\
     wl_state_gc_fun t1 = wl_state_gc_fun t /\
     wl_state_code t1 = wl_state_code t /\
     wl_state_compile t1 = wl_state_compile t /\
     wl_state_compile_oracle t1 = wl_state_compile_oracle t /\
     wl_state_code_buffer t1 = wl_state_code_buffer t /\
     wl_state_data_buffer t1 = wl_state_data_buffer t /\
     wl_state_stack t1 = wl_state_stack t /\
     wl_state_stack_size t1 = wl_state_stack_size t /\
     wl_state_locals_size t1 = wl_state_locals_size t /\
     wl_state_stack_limit t1 = wl_state_stack_limit t /\
     wl_state_stack_max t1 = wl_state_stack_max t /\
     wl_state_be t1 = wl_state_be t /\
     wl_state_mdomain t1 = wl_state_mdomain t /\
     FLOOKUP (wl_state_store t1) CodeBuffer = FLOOKUP (wl_state_store t) CodeBuffer /\
     FLOOKUP (wl_state_store t1) CodeBufferEnd = FLOOKUP (wl_state_store t) CodeBufferEnd /\
     FLOOKUP (wl_state_store t1) BitmapBuffer = FLOOKUP (wl_state_store t) BitmapBuffer /\
     FLOOKUP (wl_state_store t1) BitmapBufferEnd =
       FLOOKUP (wl_state_store t) BitmapBufferEnd /\
     FLOOKUP (wl_state_store t1) HeapLength = FLOOKUP (wl_state_store t) HeapLength /\
     Globals IN FDOM (wl_state_store t1) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s2) (wl_state_store t1) (wl_state_memory t1) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s2),FAPPLY (wl_state_store t1) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_set_var (adjust_var dest) w t1) NONE locs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final THEN
  MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `w:A word_loc`;
                        `wl_state_locals (t1:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[ASP6AUX_set_var_fields; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* a memory or store update over a wl_set_var (the simplifier puts it there) *)
let ASP6AUX_fupd_set_var = prove
 (`!f f' v (w:A word_loc) (s:(A,C,FFI)wl_state) k u.
     wl_state_memory_fupd f (wl_set_var v w s) = wl_set_var v w (wl_state_memory_fupd f s) /\
     wl_state_store_fupd f' (wl_set_var v w s) = wl_set_var v w (wl_state_store_fupd f' s) /\
     wl_set_store k u (wl_set_var v w s) = wl_set_var v w (wl_set_store k u s)`,
  REWRITE_TAC[wl_set_var_def; wl_set_store_def; wl_state_INFO.ri_fupdcanon;
              wl_state_INFO.ri_accfupds]);;

let ASP6AUX_do_stack_stack_max = prove
 (`!op vs (s:(C,FFI)data_state) (s1:(C,FFI)data_state).
     data_state_stack_max s1 = data_state_stack_max s ==>
     option_le (data_state_stack_max s)
       (data_state_stack_max (do_stack op vs (do_lim_safe s1 op vs)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`op:clos_op`; `vs:data_v list`; `s1:(C,FFI)data_state`]
    ASP6AUX_DO_STACK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* the end of an assign proof with the word state wl_set_var (adjust_var     *)
(* dest) w t1: applies ASP6AUX_state_rel_final2 and rewrites the side       *)
(* conditions (temporaries at odd variables, store updates); leaves the      *)
(* memory_rel goal                                                           *)
let ASP6AUX_FINISH_TAC : tactic =
  ASP6AUX_QR_TAC THEN REWRITE_TAC[ASP6AUX_fupd_set_var] THEN
  MATCH_MP_TAC ASP6AUX_state_rel_final2 THEN
  MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`] THEN
  ASM_SIMP_TAC[ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; wl_state_INFO.ri_accfupds;
               data_state_INFO.ri_accfupds; K_THM; ASP6AUX_DO_STACK_FIELDS;
               ASP6AUX_do_stack_stack_max; check_lim_def;
               FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"; MEM;
               FAPPLY_FUPDATE_THM; inter_insert_ODD_adjust_set_alt; lookup_insert;
               adjust_var_NEQ; ARITH; ARITH_RULE `~(0 = 1) /\ ~(0 = 3) /\ ~(0 = 5) /\
                 ~(0 = 7) /\ ~(0 = 9) /\ ~(0 = 11) /\ ~(0 = 13) /\ ~(0 = 15)`];;

let ASP6AUX_byte_zx_word_val = prove
 (`!b:byte. good_dimindex (:A) ==> (word_zx (word (val b):A word):byte) = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ZX_WORD] THEN
  SUBGOAL_THEN `val (b:byte) MOD 2 EXP dimindex (:A) = val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN MATCH_MP_TAC(ARITH_RULE `b <= c ==> a < b ==> a < c`) THEN
    REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    REWRITE_TAC[WORD_VAL]]);;

let ASP6AUX_small_index = prove
 (`!index. good_dimindex (:A) /\ index < 2 EXP (dimindex (:A) - 3) ==>
           small_int (:A) (&index) /\ 4 * index < dimword (:A)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (dimindex (:A) - 3) * 8 = dimword (:A)` ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def] THEN
    SUBGOAL_THEN `dimindex (:A) = (dimindex (:A) - 3) + 3`
      (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
     [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
      REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  REWRITE_TAC[small_int_def] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SIMP_TAC[DIV_MULT; ARITH_RULE `~(8 = 0)`] THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_ARITH `-- &a <= &b:int`] THEN ASM_ARITH_TAC);;

let ASP6AUX_byte_array_len = prove
 (`!(ws:byte list) P Q.
     (if dimindex (:A) = 32 then LENGTH ws + 4 < 2 EXP (dimindex (:A) - 3) /\ P
      else LENGTH ws + 8 < 2 EXP (dimindex (:A) - 3) /\ Q) ==>
     LENGTH ws < 2 EXP (dimindex (:A) - 3)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ARITH_TAC);;

(* the GiveUp branch of an assign proof: the goal ?q r. wl_evaluate         *)
(* (GiveUp,t) = (q,r) /\ ...; sm_tac proves option_le (data_state_stack_max *)
(* s) (data_state_stack_max s2), safe_tac the safety part                   *)
let ASP6AUX_GIVEUP_TAC (sm_tac:tactic) (safe_tac:tactic) : tactic =
  FIRST_ASSUM(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC o
    MATCH_MP evaluate_GiveUp2 o check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
    check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
  MAP_EVERY EXISTS_TAC [`SOME (NotEnoughSpace:(A)wl_result)`; `r:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w as g) ->
     if asp6_is_app "option_le" w then
       (SUBGOAL_THEN (mk_comb(mk_comb(`option_le:num option->num option->bool`,
                        `data_state_stack_max (s:(C,FFI)data_state)`), rand w))
          ASSUME_TAC THENL [sm_tac; MP5AUX_HEAD_MESON_TAC[option_le_trans]]) g
     else safe_tac g);;

let ASP6AUX_state_rel_conf = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex (:A) /\
     backend_common_word_shift (:A) <= shift_length c /\
     limits_length_limit (data_state_limits s) = data_to_word_config_len_size c /\
     (limits_arch_64_bit (data_state_limits s) <=> dimindex (:A) = 64) /\
     arch_size (data_state_limits s) = dimindex (:A)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP3AUX_memory_rel_conf o
    MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
    check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
  REWRITE_TAC[limits_inv_def] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[arch_size_def] THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let ASP6AUX_encode_header_lim = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs tag len.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\ tag < 64 /\
     len < 2 EXP limits_length_limit (data_state_limits s) /\
     len < 2 EXP arch_size (data_state_limits s) DIV 16 ==>
     ?h. encode_header c tag len = SOME (h:A word)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  REWRITE_TAC[encode_header_def] THEN
  SUBGOAL_THEN `tag < 2 EXP (dimindex (:A) - data_to_word_config_len_size c - 2) /\
                tag < dimword (:A) DIV 16 /\ len < 2 EXP (dimindex (:A) - 4) /\
                len < 2 EXP data_to_word_config_len_size c`
    (fun th -> REWRITE_TAC[th; option_INJ] THEN MESON_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `arch_size (data_state_limits (s:(C,FFI)data_state)) =
                                      dimindex (:A)`;
                              ASSUME `limits_length_limit (data_state_limits (s:(C,FFI)data_state)) =
                                      data_to_word_config_len_size c`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 6` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 6` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    UNDISCH_TAC `len < 2 EXP dimindex (:A) DIV 16` THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let ASP6AUX_do_stack_safe = prove
 (`!op vs (s:(C,FFI)data_state).
     data_state_safe_for_space (do_stack op vs (do_lim_safe s op vs)) ==>
     lim_safe (data_state_limits s) op vs /\ data_state_safe_for_space s`,
  REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

let ASP6AUX_get_vars_adjust_var_eq = prove
 (`!args (s1:(A,C,FFI)wl_state) (s0:(A,C,FFI)wl_state).
     (!n. lookup (adjust_var n) (wl_state_locals s1) =
          lookup (adjust_var n) (wl_state_locals s0)) ==>
     wl_get_vars (MAP adjust_var args) s1 = wl_get_vars (MAP adjust_var args) s0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; wl_get_vars_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[wl_get_var_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,C,FFI)wl_state`; `s0:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let ASP6AUX_shift_amount = prove
 (`!c. shift_length c < dimindex (:A) ==>
       val (word (shift_length c - backend_common_word_shift (:A)):A word) =
       shift_length c - backend_common_word_shift (:A) /\
       ~(shift_length c - backend_common_word_shift (:A) >= dimindex (:A))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD; GSYM dimword_def] THEN
  MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`shift_length c`,`a:num`) THEN
  SPEC_TAC(`backend_common_word_shift (:A)`,`b:num`) THEN
  SPEC_TAC(`dimindex (:A)`,`d:num`) THEN SPEC_TAC(`dimword (:A)`,`e:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a - b < e` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Separation-logic helpers (the work of HOL4 helperLib's SEP_R_TAC,         *)
(* SEP_W_TAC and of fs [AC STAR_ASSOC STAR_COMM]), after the versions in     *)
(* data_to_word_memoryProof_p4.  An assertion is a left-associated STAR      *)
(* tree; its leaves are compared up to alpha-conversion.                     *)
(* ------------------------------------------------------------------------- *)

let asp6_is_star tm =
  try let f,_ = dest_comb tm in
      let s,_ = dest_comb f in
      is_const s && fst(dest_const s) = "STAR"
  with Failure _ -> false;;

let rec asp6_star_leaves tm =
  if asp6_is_star tm then asp6_star_leaves (rand(rator tm)) @ asp6_star_leaves (rand tm)
  else [tm];;

let asp6_mk_star p q =
  let x = fst(dest_fun_ty(fst(dest_fun_ty(type_of p)))) in
  mk_comb(mk_comb(mk_const("STAR",[x,`:A`]),p),q);;

let asp6_list_mk_star l =
  match l with
    [] -> failwith "asp6_list_mk_star"
  | h::t -> rev_itlist (fun x acc -> asp6_mk_star acc x) t h;;

let asp6_is_one tm =
  try let f,_ = dest_comb tm in is_const f && fst(dest_const f) = "set_sep_one"
  with Failure _ -> false;;

let rec asp6_remove_first p l =
  match l with
    [] -> failwith "asp6_remove_first"
  | h::t -> if p h then t else h :: asp6_remove_first p t;;

(* th : |- p s; puts the first leaf satisfying pr in front:                 *)
(*   |- (leaf STAR rest) s   (rest a left-associated STAR of the others)     *)
let ASP6AUX_STAR_FOCUS pr th =
  let p,s = dest_comb(concl th) in
  let leaves = asp6_star_leaves p in
  let leaf = find pr leaves in
  let rest = asp6_remove_first (fun l -> l == leaf) leaves in
  MP4AUX_STAR_AC_RULE (asp6_mk_star leaf (asp6_list_mk_star rest)) th;;

(* the same, the leaves selected (in this order) put in front *)
let ASP6AUX_STAR_FOCUS_LIST prs th =
  let p,s = dest_comb(concl th) in
  let leaves = asp6_star_leaves p in
  let rec pick prs ls =
    match prs with
      [] -> [],ls
    | pr::prs' -> let l = find pr ls in
                  let ls' = asp6_remove_first (fun x -> x == l) ls in
                  let a,b = pick prs' ls' in l::a,b in
  let front,rest = pick prs leaves in
  let q = if rest = [] then asp6_list_mk_star front
          else asp6_mk_star (asp6_list_mk_star front) (asp6_list_mk_star rest) in
  MP4AUX_STAR_AC_RULE q th;;

(* reading: th : |- p (fun2set (m,dm)) gives |- m a = x /\ a IN dm for     *)
(* every leaf set_sep_one (a,x) of p                                        *)
let ASP6AUX_SEP_READS th =
  let p,s = dest_comb(concl th) in
  let leaves = asp6_star_leaves p in
  let ones = filter asp6_is_one leaves in
  if length leaves = 1 then
    (if ones = [] then [] else [MATCH_MP one_fun2set_IMP th])
  else
    map (fun leaf ->
           let rest = asp6_remove_first (fun l -> l == leaf) leaves in
           let th1 = MP4AUX_STAR_AC_RULE
                       (asp6_mk_star leaf (asp6_list_mk_star rest)) th in
           MATCH_MP read_fun2set th1) ones;;

let asp6_is_fun2set_asm tm =
  try let _,s = dest_comb tm in
      let f,_ = dest_comb s in
      is_const f && fst(dest_const f) = "fun2set"
  with Failure _ -> false;;

(* HOL4 SEP_R_TAC: the reads of every fun2set assumption as assumptions   *)
let ASP6AUX_SEP_R_TAC : tactic = fun (asl,w as g) ->
  let ths = flat (map (fun (_,th) ->
                   if asp6_is_fun2set_asm (concl th)
                   then (try ASP6AUX_SEP_READS th with Failure _ -> [])
                   else []) asl) in
  let ths = flat (map CONJUNCTS ths) in
  let ths = filter (fun th -> not (exists (fun (_,a) -> aconv (concl a) (concl th)) asl))
                   ths in
  MAP_EVERY ASSUME_TAC ths g;;

(* writing: th : |- p (fun2set (m,dm)) with a leaf set_sep_one (a,x) gives *)
(* |- p' (fun2set ((a =+ y) m,dm)), p' = p with that leaf set_sep_one (a,y) *)
let ASP6AUX_SEP_WRITE a y th =
  let p,s = dest_comb(concl th) in
  let leaves = asp6_star_leaves p in
  let leaf = find (fun l -> asp6_is_one l && aconv (fst(dest_pair(rand l))) a) leaves in
  let newleaf = mk_comb(rator leaf,mk_pair(a,y)) in
  let leaves' = map (fun l -> if l == leaf then newleaf else l) leaves in
  if length leaves = 1 then
    SPEC y (MATCH_MP MP4AUX_write_fun2set_one th)
  else
    let rest = asp6_remove_first (fun l -> l == leaf) leaves in
    let th1 = MP4AUX_STAR_AC_RULE (asp6_mk_star leaf (asp6_list_mk_star rest)) th in
    let th2 = SPEC y (MATCH_MP write_fun2set th1) in
    MP4AUX_STAR_AC_RULE (asp6_list_mk_star leaves') th2;;

(* the updates of an update chain (a1 =+ y1) ((a2 =+ y2) ... m), outermost *)
(* first, and m                                                              *)
let rec asp6_dest_updates tm =
  try let f,m = dest_comb tm in
      let g,y = dest_comb f in
      let u,a = dest_comb g in
      if is_const u && fst(dest_const u) = "=+" then
        let l,m0 = asp6_dest_updates m in (a,y)::l,m0
      else [],tm
  with Failure _ -> [],tm;;

(* th : |- p (fun2set (m,dm)); upd an update chain over m: the assertion    *)
(* with the written leaves, on fun2set (upd,dm)                             *)
let ASP6AUX_SEP_WRITES upd th =
  let ups,_ = asp6_dest_updates upd in
  rev_itlist (fun (a,y) th -> ASP6AUX_SEP_WRITE a y th) (rev ups) th;;

(* HOL4 SEP_W_TAC: for a fun2set assumption over m and the biggest update  *)
(* chain over m in the goal, the written assertion as a new assumption     *)
let ASP6AUX_SEP_W_TAC : tactic = fun (asl,w as g) ->
  let cands = filter (fun (_,th) -> asp6_is_fun2set_asm (concl th)) asl in
  let try_one (_,th) =
    let _,s = dest_comb(concl th) in
    let m = lhand(rand s) in
    let ups = find_terms (fun t -> let l,m0 = asp6_dest_updates t in
                                   l <> [] && aconv m0 m) w in
    let ups = sort (fun x y -> length(fst(asp6_dest_updates x)) >
                               length(fst(asp6_dest_updates y))) ups in
    let up = hd ups in
    ASP6AUX_SEP_WRITES up th in
  ASSUME_TAC (tryfind try_one cands) g;;

(* closes a goal  q s  with an assumption  p s,  p and q equal up to AC    *)
let ASP6AUX_SEP_AC_TAC : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let ql = asp6_star_leaves q in
  let ok (_,th) =
    let c = concl th in
    is_comb c && aconv (rand c) s &&
    let pl = asp6_star_leaves (rator c) in
    length pl = length ql in
  tryfind (fun (_,th as a) ->
             if ok a then ACCEPT_TAC (MP4AUX_STAR_AC_RULE q th) g
             else failwith "") asl;;

let ASP6AUX_ev_Call_tail =
  CAKE_SIMP_CONV [assoc "wl_Call" asp6_ev_table]
    `wl_evaluate (wl_Call NONE (SOME d) args NONE, s:(A,C,FFI)wl_state)`;;

let ASP6AUX_get_real_offset_Smallnum = prove
 (`!n. good_dimindex (:A) ==>
       get_real_offset (Smallnum (&n):A word) =
       SOME (word_add bytes_in_word (word_mul (word n) bytes_in_word))`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[get_real_offset_def; MP6AUX_SMALLNUM_NUM; bytes_in_word_def; option_INJ;
                  WORD_SHL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_MUL; option_INJ] THEN
  CONV_TAC WORD_RULE);;

let ASP6AUX_encode_header_NONE = prove
 (`!c tag len.
     encode_header c tag len = (NONE:(A word)option) <=>
     ~(tag < 2 EXP (dimindex (:A) - data_to_word_config_len_size c - 2) /\
       tag < dimword (:A) DIV 16 /\ len < 2 EXP (dimindex (:A) - 4) /\
       len < 2 EXP data_to_word_config_len_size c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let ASP6AUX_state_rel_final3 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w
    (s2:(C,FFI)data_state) (t1:(A,C,FFI)wl_state).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_ffi s2 = data_state_ffi s /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     sptree_inter (wl_state_locals t1) (adjust_set (insert dest v (data_state_locals s))) =
       sptree_inter (insert (adjust_var dest) w (wl_state_locals t))
         (adjust_set (insert dest v (data_state_locals s))) /\
     lookup 0 (wl_state_locals t1) = lookup 0 (wl_state_locals t) /\
     lookup (adjust_var dest) (wl_state_locals t1) = SOME w /\
     (!n. ~(n = dest) /\ IS_SOME (lookup (adjust_var n) (wl_state_locals t)) ==>
          IS_SOME (lookup (adjust_var n) (wl_state_locals t1))) /\
     wl_state_ffi t1 = wl_state_ffi t /\
     wl_state_clock t1 = wl_state_clock t /\
     wl_state_handler t1 = wl_state_handler t /\
     wl_state_gc_fun t1 = wl_state_gc_fun t /\
     wl_state_code t1 = wl_state_code t /\
     wl_state_compile t1 = wl_state_compile t /\
     wl_state_compile_oracle t1 = wl_state_compile_oracle t /\
     wl_state_code_buffer t1 = wl_state_code_buffer t /\
     wl_state_data_buffer t1 = wl_state_data_buffer t /\
     wl_state_stack t1 = wl_state_stack t /\
     wl_state_stack_size t1 = wl_state_stack_size t /\
     wl_state_locals_size t1 = wl_state_locals_size t /\
     wl_state_stack_limit t1 = wl_state_stack_limit t /\
     wl_state_stack_max t1 = wl_state_stack_max t /\
     wl_state_be t1 = wl_state_be t /\
     wl_state_mdomain t1 = wl_state_mdomain t /\
     (!k. MEM k [CodeBuffer; CodeBufferEnd; BitmapBuffer; BitmapBufferEnd; HeapLength] ==>
          FLOOKUP (wl_state_store t1) k = FLOOKUP (wl_state_store t) k) /\
     Globals IN FDOM (wl_state_store t1) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s2) (wl_state_store t1) (wl_state_memory t1) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s2),FAPPLY (wl_state_store t1) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2) t1 NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  REWRITE_TAC[lookup_insert; adjust_var_NEQ; adjust_var_11] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [UNDISCH_TAC `code_oracle_rel c (data_state_compile (s:(C,FFI)data_state))
       (data_state_compile_oracle s) (wl_state_store (t:(A,C,FFI)wl_state))
       (wl_state_compile t) (wl_state_compile_oracle t) (wl_state_code_buffer t)
       (wl_state_data_buffer t)` THEN
    REWRITE_TAC[code_oracle_rel_def] THEN ASM_SIMP_TAC[MEM] THEN NO_TAC;
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    (fun (asl,w as g) -> if asp6_is_app "option_le" w then MP5AUX_HEAD_MESON_TAC[option_le_trans] g
                         else failwith "not option_le");
    UNDISCH_TAC `limits_inv (data_state_limits (s:(C,FFI)data_state))
       (FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength) (wl_state_stack_limit t)
       (data_to_word_config_len_size c) (data_to_word_config_has_fp_ops c)
       (data_to_word_config_has_fp_tern c)` THEN
    ASM_SIMP_TAC[MEM] THEN NO_TAC;
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && asp6_is_app "sptree_inter" (lhs (concl th))
                          then REWRITE_TAC[th] else NO_TAC) THEN
    MATCH_MP_TAC memory_rel_insert THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

(* ------------------------------------------------------------------------- *)
(* End of the general helpers.                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 line 14006 *)
let w2w_select_id = prove
 (`!w:int64. dimindex (:A) = 64 ==>
             ((word_zx:A word -> int64) (word_extract 63 0 w)) = w`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_EXTRACT; DIMINDEX_64; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> i <= 63`]);;

(* HOL4 line 14014 *)
let extract_append_id = prove
 (`!w:int64. dimindex (:A) = 32 ==>
             word_join (word_extract 63 32 w:A word) (word_extract 31 0 w:A word) = w`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_EXTRACT; DIMINDEX_64; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[ARITH_RULE `i < 32 ==> i <= 31`];
    ASM_SIMP_TAC[ARITH_RULE `~(i < 32) /\ i < 64 ==> i - 32 < 32 /\ (i - 32) + 32 <= 63 /\
                                                     (i - 32) + 32 = i`]]);;

(* HOL4 line 14027 *)
let word1_cases = prove
 (`!w:1 word. w = word 0 \/ w = word 1`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_1] THEN
  MP_TAC(ISPEC `w:1 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* HOL4 line 14033 *)
let w2w_w2w_64 = prove
 (`!w:int64. dimindex (:A) = 64 ==> word_zx ((word_zx w):A word) = w`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; DIMINDEX_64] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 14039 (local) *)
let fp_greater = prove
 (`!a b. (fp64_greaterThan a b <=> fp64_lessThan b a) /\
         (fp64_greaterEqual a b <=> fp64_lessEqual b a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fp64_greaterThan_def; fp64_lessThan_def; fp64_greaterEqual_def;
              fp64_lessEqual_def; float_greater_than_def; float_less_than_def;
              float_greater_equal_def; float_less_equal_def] THEN
  SPEC_TAC(`fp64_to_float b`,`y:double`) THEN SPEC_TAC(`fp64_to_float a`,`x:double`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[float_compare_def] THEN
  CASES_ON `float_value (x:double)` THEN CASES_ON `float_value (y:double)` THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `float_Sign (x:double)` word1_cases) THEN
  MP_TAC(ISPEC `float_Sign (y:double)` word1_cases) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_REAL_ARITH_TAC);;

(* real_addr reads only the store and one even variable *)
let ASP6AUX_real_addr_set_var = prove
 (`!k v (s:(A,C,FFI)wl_state) c e.
     ODD k ==>
     wl_word_exp (wl_set_var k v s) (real_addr c (adjust_var e)) =
     wl_word_exp s (real_addr c (adjust_var e))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(adjust_var e = k)` ASSUME_TAC THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `ODD (adjust_var e)` THEN REWRITE_TAC[GSYM NOT_EVEN; EVEN_adjust_var];
    ALL_TAC] THEN
  REWRITE_TAC[real_addr_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[word_exp_rw; MAP; ASP6AUX_set_var_fields; lookup_insert]);;

(* the data_do_app clause of the floating point comparisons *)
let ASP6AUX_do_app_FP_cmp = prove
 (`!fpc vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (FP_cmp fpc)) vs s = Rval (v,s2) ==>
     ?w1 w2:int64. vs = [data_Word64 w1; data_Word64 w2] /\
       v = data_Boolv (fp_cmp_comp fpc w1 w2) /\
       s2 = do_stack (WordOp (FP_cmp fpc)) vs (do_lim_safe s (WordOp (FP_cmp fpc)) vs)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`WordOp (FP_cmp fpc)`; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "word_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[data_do_word_app_def] THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; case_eq "option"; distinctness "result";
              injectivity "result"; PAIR_EQ; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

let ASP6AUX_state_rel_fp = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     (limits_has_fp_ops (data_state_limits s) <=> data_to_word_config_has_fp_ops c) /\
     (limits_has_fp_tops (data_state_limits s) <=> data_to_word_config_has_fp_tern c)`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; limits_inv_def] THEN MESON_TAC[]);;

(* the floating point instructions of the assign_FP code; the moves between *)
(* registers depend on the word size (ASP6AUX_inst_FPMov64 and _32)         *)
let ASP6AUX_inst_FP = end_itlist CONJ (map (CAKE_SIMP_CONV [wl_inst_def])
  [`wl_inst (FP (FPLess r d1 d2)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPLessEqual r d1 d2)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPEqual r d1 d2)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPAbs d1 d2)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPNeg d1 d2)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPSqrt d1 d2)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPAdd d1 d2 d3)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPSub d1 d2 d3)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPMul d1 d2 d3)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPDiv d1 d2 d3)) (s:(A,C,FFI)wl_state)`;
   `wl_inst (FP (FPFma d1 d2 d3)) (s:(A,C,FFI)wl_state)`]);;

let ASP6AUX_inst_FPMov64 =
  let h = `dimindex (:A) = 64` in
  DISCH h (end_itlist CONJ (map (CAKE_SIMP_CONV [wl_inst_def; ASSUME h])
    [`wl_inst (FP (FPMovFromReg d r1 r2)) (s:(A,C,FFI)wl_state)`;
     `wl_inst (FP (FPMovToReg r1 r2 d)) (s:(A,C,FFI)wl_state)`]));;

let ASP6AUX_inst_FPMov32 =
  let h = `~(dimindex (:A) = 64)` in
  DISCH h (end_itlist CONJ (map (CAKE_SIMP_CONV [wl_inst_def; ASSUME h])
    [`wl_inst (FP (FPMovFromReg d r1 r2)) (s:(A,C,FFI)wl_state)`;
     `wl_inst (FP (FPMovToReg r1 r2 d)) (s:(A,C,FFI)wl_state)`]));;

(* the fields of wl_set_fp_var v x s *)
let ASP6AUX_set_fp_var_fields =
  let names = map (fun (f,_,_) -> f) wl_state_INFO.ri_fields in
  let cl f = if f = "fp_regs" then
               "wl_state_fp_regs (wl_set_fp_var v x s) = wl_state_fp_regs s |+ (v,x)"
             else "wl_state_" ^ f ^ " (wl_set_fp_var v x s) = wl_state_" ^ f ^ " s" in
  let tm = parse_term ("!v (x:int64) (s:(A,C,FFI)wl_state). " ^
                       String.concat " /\\ " (map cl names)) in
  prove(tm, REWRITE_TAC[wl_set_fp_var_def; wl_state_INFO.ri_accfupds; K_THM]);;

let ASP6AUX_bool_word = prove
 (`!b. word_add (word_shl (if b then word 1 else word 0) 4) (word 2):A word =
       if b then word 18 else word 2`,
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_SHL_0; WORD_ADD_0; WORD_SHL_WORD; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ASP6AUX_FINISH_TAC with extra rewrites for the fields of the final state *)
let ASP6AUX_FINISH_WITH_TAC (extra:thm list) : tactic =
  ASP6AUX_QR_TAC THEN REWRITE_TAC[ASP6AUX_fupd_set_var] THEN
  MATCH_MP_TAC ASP6AUX_state_rel_final2 THEN
  MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`] THEN
  ASM_SIMP_TAC(extra @
              [ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; wl_state_INFO.ri_accfupds;
               data_state_INFO.ri_accfupds; K_THM; ASP6AUX_DO_STACK_FIELDS;
               ASP6AUX_do_stack_stack_max; check_lim_def;
               FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"; MEM;
               FAPPLY_FUPDATE_THM; inter_insert_ODD_adjust_set_alt; lookup_insert;
               adjust_var_NEQ; ARITH; ARITH_RULE `~(0 = 1) /\ ~(0 = 3) /\ ~(0 = 5) /\
                 ~(0 = 7) /\ ~(0 = 9) /\ ~(0 = 11) /\ ~(0 = 13) /\ ~(0 = 15) /\
                 ~(0 = 17) /\ ~(0 = 19) /\ ~(0 = 21) /\ ~(0 = 23) /\ ~(0 = 31) /\
                 ~(0 = 33)`]);;

(* memory_rel for a boolean result: split on the boolean of the data_Boolv  *)
(* of the goal and use the memory_rel of the state_rel of s and t          *)
let ASP6AUX_BOOLV_TAC : tactic = fun (asl,w as g) ->
  let bv = find_term (fun u -> is_comb u && is_const (rator u) &&
                               fst (dest_const (rator u)) = "data_Boolv") w in
  (ASM_CASES_TAC (rand bv) THEN ASM_REWRITE_TAC[] THEN
   (MATCH_MP_TAC memory_rel_Boolv_T ORELSE MATCH_MP_TAC memory_rel_Boolv_F) THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(ACCEPT_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                                   (t:(A,C,FFI)wl_state) NONE locs` o concl))) g;;

(* HOL4 line 14057 *)
let assign_FP_cmp = prove
 (assign_thm_stmt `(?fpc. op = WordOp (FP_cmp fpc))`,
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `fpc:fp_cmp` SUBST_ALL_TAC)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_FP_cmp o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   DISCH_THEN(X_CHOOSE_THEN `u1:int64` (X_CHOOSE_THEN `u2:int64` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `e1:num` (X_CHOOSE_THEN `e2:num` STRIP_ASSUME_TAC) o
     REWRITE_RULE[ASP6AUX_get_vars_2] o
     check (fun th -> try asp6_is_app "data_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
     check (asp6_asm_app "data_to_word_gcProof_state_rel"))) THEN (MP_TAC(MATCH_MP ASP6AUX_state_rel_get_var2 (end_itlist CONJ
     [ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`;
      ASSUME `lookup e1 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u1)`;
      ASSUME `lookup e2 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u2)`])) THEN
   DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` (X_CHOOSE_THEN `ww2:A word_loc` STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP
       (CONJ (MATCH_MP memory_rel_tl th) (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr2:num` (X_CHOOSE_THEN `x2:A word` (X_CHOOSE_THEN `h2:A word`
     STRIP_ASSUME_TAC))) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP (CONJ th (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr1:num` (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `h1:A word`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC) THEN (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_FP_cmp_def]) THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_fp o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   ASM_CASES_TAC `data_to_word_config_has_fp_ops c` THEN ASM_REWRITE_TAC[FST]) THENL [(SUBGOAL_THEN `dimindex(:A) = 64 \/ dimindex(:A) = 32` MP_TAC THENL
    [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
   DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASP5AUX_WORD64_CONDS_TAC) THENL [(SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word x2)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THENL
      [EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr2 (wl_Word (word 0)):A word`] THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   SUBGOAL_THEN `val (word 4:A word) = 4 /\ ~(4 >= dimindex (:A))` STRIP_ASSUME_TAC THENL
    [MP_TAC(MATCH_MP ASP6AUX_good_dimindex_small (ASSUME `good_dimindex (:A)`)) THEN
     DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `4`)) THEN REWRITE_TAC[ARITH] THEN
     MESON_TAC[]; ALL_TAC]) THEN (SUBGOAL_THEN `ShiftVar Lsl 3 4 = wl_Shift Lsl (wl_Var 3) (wl_Const (word 4)):(A)wl_exp`
     SUBST1_TAC THENL
    [REWRITE_TAC[ShiftVar_def; distinctness "shift"] THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC]) THEN (CASES_ON `fpc:fp_cmp` THEN REWRITE_TAC[fp_cmp_inst_def; fp_cmp_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[fp_greater] THEN
   REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov64; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE;
     w2w_select_id] THEN
   REWRITE_TAC[ASP6AUX_bool_word] THEN ASP6AUX_FINISH_WITH_TAC [ASP6AUX_set_fp_var_fields; adjust_var_eq_numeral] THEN
   ASP6AUX_BOOLV_TAC); (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word x2)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THENL
      [EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr2 (wl_Word (word 0)):A word`] THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   SUBGOAL_THEN `word_shl bytes_in_word 1 = word_mul (word 2) bytes_in_word:A word`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   SUBGOAL_THEN `ShiftVar Lsl 3 4 = wl_Shift Lsl (wl_Var 3) (wl_Const (word 4)):(A)wl_exp`
     SUBST1_TAC THENL
    [REWRITE_TAC[ShiftVar_def; distinctness "shift"] THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   SUBGOAL_THEN `val (word 4:A word) = 4 /\ ~(4 >= dimindex (:A))` STRIP_ASSUME_TAC THENL
    [MP_TAC(MATCH_MP ASP6AUX_good_dimindex_small (ASSUME `good_dimindex (:A)`)) THEN
     DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `4`)) THEN REWRITE_TAC[ARITH] THEN
     MESON_TAC[]; ALL_TAC]) THEN (SUBGOAL_THEN `~(dimindex (:A) = 64)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   ASSUME_TAC(GEN `w:int64` (MP (SPEC `w:int64` extract_append_id)
                                (ASSUME `dimindex (:A) = 32`))) THEN
   CASES_ON `fpc:fp_cmp` THEN REWRITE_TAC[fp_cmp_inst_def; fp_cmp_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[fp_greater] THEN
   REWRITE_TAC[data_to_word_list_Seq_def] THEN
   UNDISCH_TAC `dimindex (:A) = 32` THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov32; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE] THEN
   DISCH_TAC THEN
   REWRITE_TAC[ASP6AUX_bool_word] THEN ASP6AUX_FINISH_WITH_TAC [ASP6AUX_set_fp_var_fields; adjust_var_eq_numeral] THEN
   ASP6AUX_BOOLV_TAC)]; (ASP6AUX_GIVEUP_TAC (REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS])
    (DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe) THEN
     ASM_REWRITE_TAC[lim_safe_def]))]);;

(* the floating point registers are not part of state_rel *)
let ASP6AUX_state_rel_fp_regs = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs f.
     data_to_word_gcProof_state_rel c l1 l2 s (wl_state_fp_regs_fupd f t) v locs <=>
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; wl_state_INFO.ri_accfupds]);;

(* the same from a state st that differs from t in its locals and floating  *)
(* point registers only                                                      *)
let ASP6AUX_WriteWord64_W64 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs (st:(A,C,FFI)wl_state)
    header dest w vs op.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     3 <= data_state_space s /\ dimindex (:A) = 64 /\ encode_header c 3 1 = SOME header /\
     st = wl_state_locals_fupd (K (wl_state_locals st))
            (wl_state_fp_regs_fupd (K (wl_state_fp_regs st)) t) /\
     lookup 3 (wl_state_locals st) = SOME (wl_Word w) /\
     (!k. EVEN k ==> lookup k (wl_state_locals st) = lookup k (wl_state_locals t)) ==>
     ?r. wl_evaluate (WriteWord64 c header dest 3,st) = (NONE,r) /\
         data_to_word_gcProof_state_rel c l1 l2
           (data_set_var dest (data_Word64 (word_zx w))
              (do_stack op vs (do_lim_safe
                 (data_state_space_fupd (K (data_state_space s - 3)) s) op vs)))
           r NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)))) THEN
  MATCH_MP_TAC ASP4AUX_WordFromInt_W64 THEN
  ASM_REWRITE_TAC[ASP6AUX_state_rel_fp_regs; wl_state_INFO.ri_accfupds; K_THM]);;

let ASP6AUX_WriteWord64_W32 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs (st:(A,C,FFI)wl_state)
    header dest src1 src2 (w:int64) vs op.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     3 <= data_state_space s /\ dimindex (:A) = 32 /\ encode_header c 3 2 = SOME header /\
     ~(src1 = 1) /\ ~(src2 = 1) /\
     st = wl_state_locals_fupd (K (wl_state_locals st))
            (wl_state_fp_regs_fupd (K (wl_state_fp_regs st)) t) /\
     lookup src1 (wl_state_locals st) = SOME (wl_Word (word_extract 31 0 w)) /\
     lookup src2 (wl_state_locals st) = SOME (wl_Word (word_extract 63 32 w)) /\
     (!k. EVEN k ==> lookup k (wl_state_locals st) = lookup k (wl_state_locals t)) ==>
     ?r. wl_evaluate (WriteWord64_on_32 c header dest src1 src2,st) = (NONE,r) /\
         data_to_word_gcProof_state_rel c l1 l2
           (data_set_var dest (data_Word64 w)
              (do_stack op vs (do_lim_safe
                 (data_state_space_fupd (K (data_state_space s - 3)) s) op vs)))
           r NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)))) THEN
  MATCH_MP_TAC ASP4AUX_WordFromInt_W32 THEN
  ASM_REWRITE_TAC[ASP6AUX_state_rel_fp_regs; wl_state_INFO.ri_accfupds; K_THM]);;

(* proves the data_do_app lemma of a floating point operator with space 3 *)
let ASP6AUX_DO_APP_FP3_TAC (op_tm:term) : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [op_tm; `vs:data_v list`; `s:(C,FFI)data_state`; `v:data_v`;
                 `s2:(C,FFI)data_state`] ASP5AUX_DO_APP_SPACE3) THEN
  ASM_REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
                  injectivity "clos_op"; distinctness "word_op"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "data_do_app_aux" (lhs (concl th))
                                          with Failure _ -> false)) THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[data_do_word_app_def] THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; case_eq "option"; distinctness "result";
              injectivity "result"; PAIR_EQ; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[];;

let ASP6AUX_do_app_FP_bop = prove
 (`!fpb vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (FP_bop fpb)) vs s = Rval (v,s2) ==>
     ?u1 u2:int64. vs = [data_Word64 u1; data_Word64 u2] /\
       v = data_Word64 (fp_bop_comp fpb u1 u2) /\ 3 <= data_state_space s /\
       s2 = do_stack (WordOp (FP_bop fpb)) vs
              (do_lim_safe (data_state_space_fupd (K (data_state_space s - 3)) s)
                 (WordOp (FP_bop fpb)) vs)`,
  ASP6AUX_DO_APP_FP3_TAC `WordOp (FP_bop fpb)`);;

let ASP6AUX_do_app_FP_uop = prove
 (`!fpu vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (FP_uop fpu)) vs s = Rval (v,s2) ==>
     ?u1:int64. vs = [data_Word64 u1] /\
       v = data_Word64 (fp_uop_comp fpu u1) /\ 3 <= data_state_space s /\
       s2 = do_stack (WordOp (FP_uop fpu)) vs
              (do_lim_safe (data_state_space_fupd (K (data_state_space s - 3)) s)
                 (WordOp (FP_uop fpu)) vs)`,
  ASP6AUX_DO_APP_FP3_TAC `WordOp (FP_uop fpu)`);;

let ASP6AUX_do_app_FP_top = prove
 (`!fpt vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (FP_top fpt)) vs s = Rval (v,s2) ==>
     ?u1 u2 u3:int64. vs = [data_Word64 u1; data_Word64 u2; data_Word64 u3] /\
       v = data_Word64 (fp_top_comp fpt u1 u2 u3) /\ 3 <= data_state_space s /\
       s2 = do_stack (WordOp (FP_top fpt)) vs
              (do_lim_safe (data_state_space_fupd (K (data_state_space s - 3)) s)
                 (WordOp (FP_top fpt)) vs)`,
  ASP6AUX_DO_APP_FP3_TAC `WordOp (FP_top fpt)`);;

(* the headers of the Word64 results (after part 4's ASP4AUX_encode_header_3) *)
let ASP6AUX_encode_header_3 = prove
 (`!c len. good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
           len < 2 EXP data_to_word_config_len_size c /\ len <= 2 ==>
           ?h. encode_header c 3 len = SOME (h:A word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THENL [MESON_TAC[]; REWRITE_TAC[option_DISTINCT]] THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP 6 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2)`
    MP_TAC THENL
   [REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dimword (:A) DIV 16 = 2 EXP (dimindex (:A) - 4) /\ 16 <= dimword (:A) DIV 16`
    MP_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* the state st of the goal's wl_evaluate (CNAME ..., st), and the operator *)
(* and arguments of its do_stack                                            *)
let asp6_callee_state (cname:string) (w:term) =
  let ev = find_term (fun u ->
      try let f,a = dest_comb u in
          is_const f && fst (dest_const f) = "wl_evaluate" &&
          (let h = fst (strip_comb (fst (dest_pair a))) in
           is_const h && fst (dest_const h) = cname)
      with Failure _ -> false) w in
  snd (dest_pair (rand ev));;

let asp6_goal_op_vs (w:term) =
  let ds = find_term (fun u -> try fst (dest_const (fst (strip_comb u))) = "do_stack" &&
                                   length (snd (strip_comb u)) = 3
                               with Failure _ -> false) w in
  match snd (strip_comb ds) with [op; vs; _] -> op, vs | _ -> failwith "asp6_goal_op_vs";;

(* the side conditions on the final state st of the Word64 lemmas *)
let ASP6AUX_W64_ST_TAC : tactic =
  REWRITE_TAC[wl_state_INFO.ri_component_equality; ASP6AUX_set_var_fields;
              ASP6AUX_set_fp_var_fields; wl_state_INFO.ri_accfupds; K_THM] THEN
  TRY(X_GEN_TAC `kk:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[ASP4AUX_lookup_insert_ODD; ARITH] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[lookup_insert; ARITH];;

(* the end of a Word64 result on a 64-bit architecture: the goal is        *)
(* ?q r. wl_evaluate (WriteWord64 c a dest 3,st) = (q,r) /\ ...            *)
let ASP6AUX_WW64_FINISH_TAC (extra:thm list) : tactic =
  W(fun (_,w) ->
    let st = asp6_callee_state "WriteWord64" w in
    let wv = rand (rand (rator st)) in
    let op, vs = asp6_goal_op_vs w in
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; st; `a:A word`; `dest:num`; wv;
      vs; op] ASP6AUX_WriteWord64_W64)) THEN
  (ANTS_TAC THENL [REPEAT CONJ_TAC THEN ASP6AUX_W64_ST_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "data_to_word_gcProof_state_rel" (concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "word_zx" with Failure _ -> false))
      (concl th))) THEN
  ASM_SIMP_TAC extra;;

(* the end of a Word64 result on a 32-bit architecture: the goal is        *)
(* ?q r. wl_evaluate (WriteWord64_on_32 c a dest 5 3,st) = (q,r) /\ ...     *)
(* with the high half of the result in local 3 of st                        *)
let ASP6AUX_WW32_FINISH_TAC : tactic =
  W(fun (_,w) ->
    let st = asp6_callee_state "WriteWord64_on_32" w in
    let wv = rand (rand (rand (rator st))) in
    let op, vs = asp6_goal_op_vs w in
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; st; `a:A word`; `dest:num`; `5`; `3`;
      wv; vs; op] ASP6AUX_WriteWord64_W32)) THEN
  (ANTS_TAC THENL [REPEAT CONJ_TAC THEN ASP6AUX_W64_ST_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT];;

(* the option_le of stack_max of the GiveUp of a space 3 operator *)
let ASP6AUX_SM3_TAC : tactic =
  W(fun (_,w) -> let op, vs = asp6_goal_op_vs w in
    MP_TAC(ISPECL [op; vs;
      `data_state_space_fupd (K (data_state_space s - 3)) (s:(C,FFI)data_state)`]
      ASP6AUX_DO_STACK_FIELDS)) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[];;

(* the GiveUp of a space 3 floating point operator without fp ops *)
let ASP6AUX_NOFP3_GIVEUP_TAC : tactic =
  ASP6AUX_GIVEUP_TAC ASP6AUX_SM3_TAC
   (DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN ASM_REWRITE_TAC[]);;

(* the GiveUp of a missing Word64 header on a 32-bit architecture: the     *)
(* operator is not lim_safe (it needs 1 < len_size, after part 5's         *)
(* ASP5AUX_W64_GIVEUP_TAC)                                                  *)
let ASP6AUX_W32_GIVEUP_TAC : tactic =
  ASP6AUX_GIVEUP_TAC ASP6AUX_SM3_TAC
   (DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN
    ASM_REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `2`]
      (INST_TYPE [`:A`,`:A`] ASP6AUX_encode_header_3)) THEN
    ASM_REWRITE_TAC[option_DISTINCT; NOT_EXISTS_THM; ARITH] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 2` THEN REWRITE_TAC[LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;


(* HOL4 line 14159 *)
let assign_FP_top = prove
 (assign_thm_stmt `(?fpt. op = WordOp (FP_top fpt))`,
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `fpt:fp_top` SUBST_ALL_TAC)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_FP_top o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   DISCH_THEN(X_CHOOSE_THEN `u1:int64` (X_CHOOSE_THEN `u2:int64` (X_CHOOSE_THEN `u3:int64`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `e1:num` (X_CHOOSE_THEN `e2:num` (X_CHOOSE_THEN `e3:num`
     STRIP_ASSUME_TAC)) o
     REWRITE_RULE[ASP6AUX_get_vars_3] o
     check (fun th -> try asp6_is_app "data_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
     check (asp6_asm_app "data_to_word_gcProof_state_rel"))) THEN (MP_TAC(MATCH_MP ASP6AUX_state_rel_get_var3 (end_itlist CONJ
     [ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`;
      ASSUME `lookup e1 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u1)`;
      ASSUME `lookup e2 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u2)`;
      ASSUME `lookup e3 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u3)`])) THEN
   DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` (X_CHOOSE_THEN `ww2:A word_loc`
     (X_CHOOSE_THEN `ww3:A word_loc` STRIP_ASSUME_TAC))) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP
       (CONJ (MATCH_MP memory_rel_tl (MATCH_MP memory_rel_tl th)) (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr3:num` (X_CHOOSE_THEN `x3:A word` (X_CHOOSE_THEN `h3:A word`
     STRIP_ASSUME_TAC))) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP
       (CONJ (MATCH_MP memory_rel_tl th) (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr2:num` (X_CHOOSE_THEN `x2:A word` (X_CHOOSE_THEN `h2:A word`
     STRIP_ASSUME_TAC))) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP (CONJ th (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr1:num` (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `h1:A word`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC) THEN (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[arg3_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_FP_top_def]) THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_fp o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   ASM_CASES_TAC `~data_to_word_config_has_fp_ops c \/ ~data_to_word_config_has_fp_tern c` THEN
   ASM_REWRITE_TAC[FST]) THENL [(ASP6AUX_GIVEUP_TAC ASP6AUX_SM3_TAC
    (DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe) THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN ASM_MESON_TAC[])); (POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
   SUBGOAL_THEN `dimindex(:A) = 64 \/ dimindex(:A) = 32` MP_TAC THENL
    [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
   DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASP5AUX_WORD64_CONDS_TAC) THENL [(CASES_ON `encode_header c 3 1:(A word)option` THEN CASE_REWRITE_TAC[FST]) THENL [(SUBGOAL_THEN `1 < 2 EXP data_to_word_config_len_size c` ASSUME_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 1` THEN REWRITE_TAC[LE_EXP] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `1`] (INST_TYPE [`:A`,`:A`] ASP6AUX_encode_header_3)) THEN
   ASM_REWRITE_TAC[option_DISTINCT; ARITH; NOT_EXISTS_THM]); (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word x2) /\
                 wl_word_exp t (real_addr c (adjust_var e3)) = SOME (wl_Word x3)`
     STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THENL
      [EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr2 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr3 (wl_Word (word 0)):A word`] THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   CASES_ON `fpt:fp_top` THEN REWRITE_TAC[fp_top_inst_def; fp_top_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov64; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE;
     w2w_select_id] THEN
   ASP6AUX_WW64_FINISH_TAC [w2w_w2w_64])]; (CASES_ON `encode_header c 3 2:(A word)option` THEN CASE_REWRITE_TAC[FST]) THENL [(ASP6AUX_W32_GIVEUP_TAC); (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word x2) /\
                 wl_word_exp t (real_addr c (adjust_var e3)) = SOME (wl_Word x3)`
     STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THENL
      [EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr2 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr3 (wl_Word (word 0)):A word`] THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   SUBGOAL_THEN `word_shl bytes_in_word 1 = word_mul (word 2) bytes_in_word:A word`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   SUBGOAL_THEN `~(dimindex (:A) = 64)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   ASSUME_TAC(GEN `w:int64` (MP (SPEC `w:int64` extract_append_id)
                                (ASSUME `dimindex (:A) = 32`))) THEN
   CASES_ON `fpt:fp_top` THEN REWRITE_TAC[fp_top_inst_def; fp_top_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   UNDISCH_TAC `dimindex (:A) = 32` THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov32; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE] THEN
   DISCH_TAC THEN ASP6AUX_WW32_FINISH_TAC)]]]);;

(* HOL4 line 14321 *)
let assign_FP_bop = prove
 (assign_thm_stmt `(?fpb. op = WordOp (FP_bop fpb))`,
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `fpb:fp_bop` SUBST_ALL_TAC)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_FP_bop o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   DISCH_THEN(X_CHOOSE_THEN `u1:int64` (X_CHOOSE_THEN `u2:int64` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `e1:num` (X_CHOOSE_THEN `e2:num` STRIP_ASSUME_TAC) o
     REWRITE_RULE[ASP6AUX_get_vars_2] o
     check (fun th -> try asp6_is_app "data_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
     check (asp6_asm_app "data_to_word_gcProof_state_rel"))) THEN (MP_TAC(MATCH_MP ASP6AUX_state_rel_get_var2 (end_itlist CONJ
     [ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`;
      ASSUME `lookup e1 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u1)`;
      ASSUME `lookup e2 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u2)`])) THEN
   DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` (X_CHOOSE_THEN `ww2:A word_loc` STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP
       (CONJ (MATCH_MP memory_rel_tl th) (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr2:num` (X_CHOOSE_THEN `x2:A word` (X_CHOOSE_THEN `h2:A word`
     STRIP_ASSUME_TAC))) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP (CONJ th (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr1:num` (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `h1:A word`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC) THEN (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_FP_bop_def]) THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_fp o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   ASM_CASES_TAC `data_to_word_config_has_fp_ops c` THEN ASM_REWRITE_TAC[FST]) THENL [(SUBGOAL_THEN `dimindex(:A) = 64 \/ dimindex(:A) = 32` MP_TAC THENL
    [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
   DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASP5AUX_WORD64_CONDS_TAC) THENL [(CASES_ON `encode_header c 3 1:(A word)option` THEN CASE_REWRITE_TAC[FST]) THENL [(SUBGOAL_THEN `1 < 2 EXP data_to_word_config_len_size c` ASSUME_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 1` THEN REWRITE_TAC[LE_EXP] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `1`] (INST_TYPE [`:A`,`:A`] ASP6AUX_encode_header_3)) THEN
   ASM_REWRITE_TAC[option_DISTINCT; ARITH; NOT_EXISTS_THM]); (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word x2)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THENL
      [EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr2 (wl_Word (word 0)):A word`] THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   CASES_ON `fpb:fp_bop` THEN REWRITE_TAC[fp_bop_inst_def; fp_bop_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov64; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE;
     w2w_select_id] THEN
   ASP6AUX_WW64_FINISH_TAC [w2w_w2w_64])]; (CASES_ON `encode_header c 3 2:(A word)option` THEN CASE_REWRITE_TAC[FST]) THENL [(ASP6AUX_W32_GIVEUP_TAC); (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word x2)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THENL
      [EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word`;
       EXISTS_TAC `get_addr c ptr2 (wl_Word (word 0)):A word`] THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   SUBGOAL_THEN `word_shl bytes_in_word 1 = word_mul (word 2) bytes_in_word:A word`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   SUBGOAL_THEN `~(dimindex (:A) = 64)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   ASSUME_TAC(GEN `w:int64` (MP (SPEC `w:int64` extract_append_id)
                                (ASSUME `dimindex (:A) = 32`))) THEN
   CASES_ON `fpb:fp_bop` THEN REWRITE_TAC[fp_bop_inst_def; fp_bop_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   UNDISCH_TAC `dimindex (:A) = 32` THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov32; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE] THEN
   DISCH_TAC THEN ASP6AUX_WW32_FINISH_TAC)]]; (ASP6AUX_NOFP3_GIVEUP_TAC)]);;

(* HOL4 line 14467 *)
let assign_FP_uop = prove
 (assign_thm_stmt `(?fpu. op = WordOp (FP_uop fpu))`,
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `fpu:fp_uop` SUBST_ALL_TAC)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_FP_uop o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   DISCH_THEN(X_CHOOSE_THEN `u1:int64` STRIP_ASSUME_TAC) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `e1:num` STRIP_ASSUME_TAC o
     REWRITE_RULE[ASP6AUX_get_vars_1] o
     check (fun th -> try asp6_is_app "data_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
     check (asp6_asm_app "data_to_word_gcProof_state_rel"))) THEN (MP_TAC(MATCH_MP ASP6AUX_state_rel_get_var1 (end_itlist CONJ
     [ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`;
      ASSUME `lookup e1 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_Word64 u1)`])) THEN
   DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Word64_IMP (CONJ th (ASSUME `good_dimindex (:A)`)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ptr1:num` (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `h1:A word`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC) THEN (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_FP_uop_def]) THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_fp o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   ASM_CASES_TAC `data_to_word_config_has_fp_ops c` THEN ASM_REWRITE_TAC[FST]) THENL [(SUBGOAL_THEN `dimindex(:A) = 64 \/ dimindex(:A) = 32` MP_TAC THENL
    [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
   DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASP5AUX_WORD64_CONDS_TAC) THENL [(CASES_ON `encode_header c 3 1:(A word)option` THEN CASE_REWRITE_TAC[FST]) THENL [(SUBGOAL_THEN `1 < 2 EXP data_to_word_config_len_size c` ASSUME_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 1` THEN REWRITE_TAC[LE_EXP] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `1`] (INST_TYPE [`:A`,`:A`] ASP6AUX_encode_header_3)) THEN
   ASM_REWRITE_TAC[option_DISTINCT; ARITH; NOT_EXISTS_THM]); (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC get_var_get_real_addr_lemma THEN
     EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word` THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   CASES_ON `fpu:fp_uop` THEN REWRITE_TAC[fp_uop_inst_def; fp_uop_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov64; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE;
     w2w_select_id] THEN
   ASP6AUX_WW64_FINISH_TAC [w2w_w2w_64])]; (CASES_ON `encode_header c 3 2:(A word)option` THEN CASE_REWRITE_TAC[FST]) THENL [(ASP6AUX_W32_GIVEUP_TAC); (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word x1)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC get_var_get_real_addr_lemma THEN
     EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word` THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC] THEN
   SUBGOAL_THEN `word_shl bytes_in_word 1 = word_mul (word 2) bytes_in_word:A word`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   SUBGOAL_THEN `~(dimindex (:A) = 64)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   ASSUME_TAC(GEN `w:int64` (MP (SPEC `w:int64` extract_append_id)
                                (ASSUME `dimindex (:A) = 32`))) THEN
   CASES_ON `fpu:fp_uop` THEN REWRITE_TAC[fp_uop_inst_def; fp_uop_comp_def] THEN
   CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   UNDISCH_TAC `dimindex (:A) = 32` THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
     ASP6AUX_set_var_fields; ASP6AUX_real_addr_set_var; ARITH; ASP6AUX_inst_FP;
     ASP6AUX_inst_FPMov32; ASP6AUX_set_fp_var_fields; wl_get_fp_var_def; FLOOKUP_UPDATE] THEN
   DISCH_TAC THEN ASP6AUX_WW32_FINISH_TAC)]]; (ASP6AUX_NOFP3_GIVEUP_TAC)]);;

let ASP6AUX_do_app_Label = prove
 (`!lab vs (s:(C,FFI)data_state) v s2.
     data_do_app (clos_Label lab) vs s = Rval (v,s2) <=>
     vs = [] /\ lab IN domain (data_state_code s) /\ v = data_CodePtr lab /\
     s2 = do_stack (clos_Label lab) vs (do_lim_safe s (clos_Label lab) vs)`,
  ASP6AUX_DO_APP_TAC `clos_Label lab`);;

let ASP6AUX_state_rel_code_domain = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs lab.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs /\
     lab IN domain (data_state_code s) ==>
     lab IN domain (wl_state_code t)`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_to_word_gcProof_code_rel_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNION]);;

(* HOL4 line 14592 *)
let assign_Label = prove
 (assign_thm_stmt `(?lab. op = clos_Label lab)`,
  ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `lab:num` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_Label] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  SUBGOAL_THEN `lab IN domain (wl_state_code (t:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ASP6AUX_state_rel_code_domain]; ALL_TAC] THEN
  ASP6AUX_EV_TAC [] THEN
  ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP1AUX_state_rel_set_var THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN ASM_REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS] THEN
  MATCH_MP_TAC memory_rel_CodePtr THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN REWRITE_TAC[]);;

(* HOL4 line 14617 *)
let data_to_word_assignProof_do_app_Ref = prove
 ((CASE_TERM
  `!vals (x:(C,FFI)data_state).
     data_do_app (MemOp clos_Ref) vals x =
     match consume_space (LENGTH vals + 1) x with
       NONE -> Rerr (Rabort Rtype_error)
     | SOME s1 ->
         Rval
          (data_RefPtr T (minimal ptr. ~(ptr IN domain (data_state_refs s1))),
           data_state_refs_fupd
             (K (insert (minimal ptr. ~(ptr IN domain (data_state_refs s1)))
                   (bvl_ValueArray vals) (data_state_refs s1)))
             (data_state_safe_for_space_fupd
                (K (data_state_safe_for_space
                      (do_stack (MemOp clos_Ref) vals
                         (do_lim_safe s1 (MemOp clos_Ref) vals))))
                (data_state_stack_max_fupd
                   (K (data_state_stack_max
                         (do_stack (MemOp clos_Ref) vals
                            (do_lim_safe s1 (MemOp clos_Ref) vals))))
                   s1)))`),
  (REPEAT GEN_TAC THEN
   REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; op_space_req_def; MEM;
     distinctness "clos_op"; injectivity "clos_op"; distinctness "mem_op";
     ARITH_RULE `~(n + 1 = 0)`] THEN
   CASES_ON `consume_space (LENGTH (vals:data_v list) + 1) (x:(C,FFI)data_state)` THEN
   CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS; injectivity "result"; PAIR_EQ] THEN
   REWRITE_TAC[do_stack_def; do_lim_safe] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; data_state_INFO.ri_fupdfupds;
               data_state_INFO.ri_fupdcanon; K_THM; K_o_THM]));;

(* HOL4 line 14634 *)
let assign_Ref = prove
 ((assign_thm_stmt `op = MemOp clos_Ref`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_assignProof_do_app_Ref] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  CASES_ON `consume_space (LENGTH (vals:data_v list) + 1) (s:(C,FFI)data_state)` THEN
  CASE_REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[consume_space_def] o
    check (fun th -> try asp6_is_app "consume_space" (lhs (concl th))
                     with Failure _ -> false)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`;
                 `vals:data_v list`] ASP4AUX_state_rel_get_vars) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Ref_def] THEN
  CASES_ON `encode_header c 2 (LENGTH (args:num list)):(A word)option` THEN
  CASE_REWRITE_TAC[]) THENL
   [(ASP6AUX_GIVEUP_TAC
    (MP_TAC(ISPECL [`MemOp clos_Ref`; `vals:data_v list`;
       `data_state_space_fupd (K (data_state_space s - (LENGTH (vals:data_v list) + 1)))
          (s:(C,FFI)data_state)`] ASP6AUX_DO_STACK_FIELDS) THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[])
    (REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN(K ALL_TAC) THEN
     DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe) THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN STRIP_TAC THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
       `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `2`; `LENGTH (args:num list)`]
       ASP6AUX_encode_header_lim) THEN
     ASM_REWRITE_TAC[option_DISTINCT] THEN CONV_TAC NUM_REDUCE_CONV));
    (REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   MP_TAC(ISPEC `data_state_refs (s:(C,FFI)data_state)` LEAST_NOTIN_spt_DOMAIN) THEN
   ABBREV_TAC `new = minimal ptr. ~(ptr IN domain (data_state_refs (s:(C,FFI)data_state)))` THEN
   DISCH_TAC) THEN
    (FIRST_ASSUM(MP_TAC o SPECL [`a:A word`; `new:num`] o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Ref) o check (asp6_asm_app "memory_rel")) THEN
   ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL
    [UNDISCH_TAC `encode_header c 2 (LENGTH (args:num list)) = SOME (a:A word)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DISCH_THEN(X_CHOOSE_THEN `eoh:A word` (X_CHOOSE_THEN `curr:A word`
     (X_CHOOSE_THEN `trig:A word` (X_CHOOSE_THEN `m1:A word->A word_loc`
       STRIP_ASSUME_TAC))))) THEN
    (REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                   ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; FLOOKUP_UPDATE]) THEN
    (BIGPAUX_MATCH_ABBREV_TAC `wl_evaluate (StoreEach 1 (CONS 3 (MAP adjust_var args)) (word 0),
      t5:(A,C,FFI)wl_state)` `t5:(A,C,FFI)wl_state` THEN
   SUBGOAL_THEN `wl_get_vars (MAP adjust_var args) (t5:(A,C,FFI)wl_state) = SOME ws`
     ASSUME_TAC THENL
    [EXPAND_TAC "t5" THEN
     W(fun (asl,w) -> MP_TAC (ISPECL [`args:num list`; rand(lhs w); `t:(A,C,FFI)wl_state`]
        ASP6AUX_get_vars_adjust_var_eq)) THEN
     REWRITE_TAC[ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; lookup_insert;
                 adjust_var_NEQ] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `wl_evaluate (StoreEach 1 (CONS 3 (MAP adjust_var args)) (word 0),
                   t5:(A,C,FFI)wl_state) = (NONE,wl_state_memory_fupd (K m1) t5)`
     SUBST1_TAC THENL
    [MATCH_MP_TAC evaluate_StoreEach THEN
     MAP_EVERY EXISTS_TAC [`CONS (wl_Word a) (ws:(A word_loc)list)`;
       `word_sub eoh (word_mul bytes_in_word (word (LENGTH (vals:data_v list) + 1))):A word`] THEN
     ASM_REWRITE_TAC[wl_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
     EXPAND_TAC "t5" THEN
     REWRITE_TAC[ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; wl_get_var_def;
                 lookup_insert; ARITH_RULE `~(3 = 1)`] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC]) THEN
    (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_shift_amount o
     check ((=) `shift_length c < dimindex (:A)` o concl)) THEN
   CASE_REWRITE_TAC[] THEN
   ASP3AUX_UNABBREV_TAC `t5:(A,C,FFI)wl_state` THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                   WORD_OR_0; ASP6AUX_set_var_fields; ASP6AUX_set_store_fields;
                   FLOOKUP_UPDATE]) THEN
    (ASP6AUX_FINISH_TAC) THEN
    (SUBGOAL_THEN `!(st:(store_name,A word_loc)fmap) v1 v2.
      st |+ (TriggerGC,v1) |+ (EndOfHeap,v2) = st |+ (EndOfHeap,v2) |+ (TriggerGC,v1)`
     (fun th -> REWRITE_TAC[th]) THENL
    [REPEAT GEN_TAC THEN MATCH_MP_TAC FUPDATE_COMMUTES THEN
     REWRITE_TAC[distinctness "store_name"];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `bvl_ValueArray (vals:data_v list)`)) (concl th))) THEN
   REWRITE_TAC[make_ptr_def; WORD_SUB_0] THEN
   MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[])]);;

let ASP6AUX_do_app_Update = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp Update) vs s = Rval (v,s2) <=>
     ?b ptr i x xs. vs = [data_RefPtr b ptr; data_Number i; x] /\
       lookup ptr (data_state_refs s) = SOME (bvl_ValueArray xs) /\
       &0 <= i /\ i < &(LENGTH xs) /\ v = data_Unit /\
       s2 = data_state_refs_fupd
              (K (insert ptr (bvl_ValueArray (LUPDATE x (num_of_int i) xs))
                    (data_state_refs s)))
              (do_stack (MemOp Update) vs (do_lim_safe s (MemOp Update) vs))`,
  ASP6AUX_DO_APP_TAC `MemOp Update`);;

(* HOL4 line 14696 *)
let assign_Update = prove
 ((assign_thm_stmt `op = MemOp Update`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_Update] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `a3:num`
    STRIP_ASSUME_TAC)) o REWRITE_RULE[ASP6AUX_get_vars_3]) THEN
  RVEQ_TAC) THEN
  (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[arg3_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Update_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  ASP6AUX_GET_VARS_TAC [`a1:num`; `a2:num`; `a3:num`]
    [`w1:A word_loc`; `w2:A word_loc`; `w3:A word_loc`]) THEN
  (ABBREV_TAC `index = num_of_int i` THEN
  (SUBGOAL_THEN `i = &index:int` SUBST_ALL_TAC THENL
   [EXPAND_TAC "index" THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LT]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_memory_rel_rearrange o
    check (asp6_asm_app "memory_rel")) THEN
  DISCH_THEN(MP_TAC o SPEC
    `CONS (x:data_v,w3:A word_loc) (CONS (data_RefPtr b ptr,w1)
       (CONS (data_Number (&index),w2)
         (APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
                   (toAList (sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
                      (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))))`) THEN
  ANTS_TAC THENL [REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP memory_rel_Update o
    (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ValueArray xs)`)
                       (CONJ (ASSUME `good_dimindex (:A)`)
                         (ASSUME `index < LENGTH (xs:data_v list)`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `i_w:A word`
    (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `y1:A word` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC) THEN
  ((SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word x1) /\
                wl_word_exp t (real_offset c (adjust_var a2)) = SOME (wl_Word y1)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `ptr_w:A word`;
      MATCH_MP_TAC get_real_offset_lemma THEN EXISTS_TAC `i_w:A word`] THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC])) THEN
  (ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; wl_mem_store_def; ITLIST; OPTION_MAP_DEF;
                  WORD_ADD_0; data_to_word_Unit_def]) THEN
  (ASP6AUX_FINISH_FINAL_TAC `wl_Word (word 2):A word_loc` `wl_state_locals (t:(A,C,FFI)wl_state)` THEN
   MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `LUPDATE (x:data_v) index xs`)) (concl th))) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]));;

let ASP6AUX_do_app_El = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp clos_El) vs s = Rval (v,s2) <=>
     ((?ts tag xs i. vs = [data_Block ts tag xs; data_Number i] /\ &0 <= i /\
                     num_of_int i < LENGTH xs /\ v = EL (num_of_int i) xs) \/
      (?b ptr xs i. vs = [data_RefPtr b ptr; data_Number i] /\
                    lookup ptr (data_state_refs s) = SOME (bvl_ValueArray xs) /\
                    &0 <= i /\ i < &(LENGTH xs) /\ v = EL (num_of_int i) xs)) /\
     s2 = do_stack (MemOp clos_El) vs (do_lim_safe s (MemOp clos_El) vs)`,
  ASP6AUX_DO_APP_TAC `MemOp clos_El`);;

(* HOL4 line 14740 *)
let assign_El = prove
 (assign_thm_stmt `op = MemOp clos_El`,
  (ASP6AUX_INTRO_TAC (DISCH_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_El] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `a2:num` STRIP_ASSUME_TAC) o
    REWRITE_RULE[ASP6AUX_get_vars_2]) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_El_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  ASP6AUX_GET_VARS_TAC [`a1:num`; `a2:num`] [`w1:A word_loc`; `w2:A word_loc`] THEN
  ABBREV_TAC `index = num_of_int i` THEN
  (SUBGOAL_THEN `i = &index:int` SUBST_ALL_TAC THENL
   [EXPAND_TAC "index" THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC])) THENL
   [(FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_El o
    (fun th -> CONJ th (CONJ (ASSUME `good_dimindex (:A)`)
                         (ASSUME `index < LENGTH (xs:data_v list)`))) o
    check (asp6_asm_app "memory_rel")) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `i_w:A word`
    (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `y1:A word` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word x1) /\
                wl_word_exp t (real_offset c (adjust_var a2)) = SOME (wl_Word y1)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `ptr_w:A word`;
      MATCH_MP_TAC get_real_offset_lemma THEN EXISTS_TAC `i_w:A word`] THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC] THEN
  ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0]) THEN
    (ASP6AUX_FINISH_SIMPLE_TAC `EL index (xs:data_v list)`);
    (RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LT]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Deref o
    (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ValueArray xs)`)
                       (CONJ (ASSUME `good_dimindex (:A)`)
                         (ASSUME `index < LENGTH (xs:data_v list)`)))) o
    check (asp6_asm_app "memory_rel")) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `i_w:A word`
    (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `y1:A word` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word x1) /\
                wl_word_exp t (real_offset c (adjust_var a2)) = SOME (wl_Word y1)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `ptr_w:A word`;
      MATCH_MP_TAC get_real_offset_lemma THEN EXISTS_TAC `i_w:A word`] THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC] THEN
  ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0] THEN
  ASP6AUX_FINISH_SIMPLE_TAC `EL index (xs:data_v list)`)]);;

let ASP6AUX_do_app_ElemAt = prove
 (`!k vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (ElemAt k)) vs s = Rval (v,s2) <=>
     ((?ts tag xs. vs = [data_Block ts tag xs] /\ k < LENGTH xs /\ v = EL k xs) \/
      (?b ptr xs. vs = [data_RefPtr b ptr] /\
                  lookup ptr (data_state_refs s) = SOME (bvl_ValueArray xs) /\
                  k < LENGTH xs /\ v = EL k xs)) /\
     s2 = do_stack (BlockOp (ElemAt k)) vs (do_lim_safe s (BlockOp (ElemAt k)) vs)`,
  ASP6AUX_DO_APP_TAC `BlockOp (ElemAt k)`);;

(* HOL4 line 14809 *)
let assign_ElemAt = prove
 (assign_thm_stmt `(?n. op = BlockOp (ElemAt n))`,
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)) THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_ElemAt] o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                      with Failure _ -> false)) THEN
   RVEQ_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `a1:num` STRIP_ASSUME_TAC o
     REWRITE_RULE[ASP6AUX_get_vars_1]) THEN
   RVEQ_TAC THEN
   REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_ElemAt_def] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
   ASP6AUX_GET_VARS_TAC [`a1:num`] [`w1:A word_loc`]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_El' o
      (fun th -> CONJ th (CONJ (ASSUME `good_dimindex (:A)`)
                           (ASSUME `k < LENGTH (xs:data_v list)`))) o
      check (asp6_asm_app "memory_rel"));
    FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Deref' o
      (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                         SOME (bvl_ValueArray xs)`)
                         (CONJ (ASSUME `good_dimindex (:A)`)
                           (ASSUME `k < LENGTH (xs:data_v list)`)))) o
      check (asp6_asm_app "memory_rel"))] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ptr_w:A word`; `x1:A word`] THEN TRY(X_GEN_TAC `i_w:A word`) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                 SOME (wl_Word x1)` ASSUME_TAC THENL
    [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `ptr_w:A word` THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC]) THEN
  ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                  WORD_ADD_ASSOC] THEN
  ASP6AUX_FINISH_SIMPLE_TAC `EL k (xs:data_v list)`);;

let ASP6AUX_do_app_UpdateByte = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp UpdateByte) vs s = Rval (v,s2) <=>
     ?b ptr i bb fl ws. vs = [data_RefPtr b ptr; data_Number i; data_Number bb] /\
       lookup ptr (data_state_refs s) = SOME (bvl_ByteArray fl ws) /\
       &0 <= i /\ i < &(LENGTH ws) /\ (?w:byte. bb = &(val w)) /\ v = data_Unit /\
       s2 = data_state_refs_fupd
              (K (insert ptr (bvl_ByteArray fl (LUPDATE (iword bb) (num_of_int i) ws))
                    (data_state_refs s)))
              (do_stack (MemOp UpdateByte) vs (do_lim_safe s (MemOp UpdateByte) vs))`,
  ASP6AUX_DO_APP_TAC `MemOp UpdateByte`);;

(* HOL4 line 14874 *)
let assign_UpdateByte = prove
 ((assign_thm_stmt `op = MemOp UpdateByte`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_UpdateByte] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `a3:num`
    STRIP_ASSUME_TAC)) o REWRITE_RULE[ASP6AUX_get_vars_3]) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[arg3_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_UpdateByte_def; data_to_word_list_Seq_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  ASP6AUX_GET_VARS_TAC [`a1:num`; `a2:num`; `a3:num`]
    [`w1:A word_loc`; `w2:A word_loc`; `w3:A word_loc`] THEN
  ABBREV_TAC `index = num_of_int i` THEN
  (SUBGOAL_THEN `i = &index:int` SUBST_ALL_TAC THENL
   [EXPAND_TAC "index" THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LT]) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_IWORD; WORD_VAL]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_ByteArray_IMP o
    (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ByteArray fl ws)`)
                         (ASSUME `good_dimindex (:A)`))) o
    check (asp6_asm_app "memory_rel")) THEN
  DISCH_THEN(X_CHOOSE_THEN `pw:A word` (X_CHOOSE_THEN `pa:A word` (X_CHOOSE_THEN `hdr:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP6AUX_byte_array_len o check (is_cond o concl)) THEN
  MP_TAC(SPEC `index:num` ASP6AUX_small_index) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LT_TRANS]; STRIP_TAC] THEN
  MP_TAC(SPEC `val (w:byte)` ASP6AUX_small_index) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
    REWRITE_TAC[GSYM DIMINDEX_8; VAL_BOUND; LE_EXP] THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; DIMINDEX_8] THEN
    ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `w2 = wl_Word (word (4 * index):A word) /\
                w3 = wl_Word (word (4 * val (w:byte)):A word)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MP6AUX_SMALLNUM_NUM] THEN CONJ_TAC THEN
    MATCH_MP_TAC memory_rel_Number_IMP THEN
    MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
      `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
      `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
      `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
      `[]:(data_v # A word_loc) list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `data_RefPtr b ptr`)) (concl th) &&
      not (can (find_term ((=) `LUPDATE:byte->num->byte list->byte list`)) (concl th)))) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word pa) /\
                wl_word_exp t (real_byte_offset (adjust_var a2)) =
                SOME (wl_Word (word_add bytes_in_word (word index)))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC get_var_get_real_addr_lemma THEN EXISTS_TAC `pw:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def];
      ASM_SIMP_TAC[GSYM BIGPAUX_USHR_4] THEN MATCH_MP_TAC get_real_byte_offset_lemma THEN
      ASM_REWRITE_TAC[wl_get_var_def]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MP (ASSUME `index < LENGTH (ws:byte list)`) o SPEC `index:num` o
    check (fun th -> can (find_term ((=) `mem_load_byte_aux:(A word->A word_loc)->(A word->bool)->bool->A word->byte option`)) (concl th))) THEN
  REWRITE_TAC[mem_load_byte_aux_def]) THEN
  (CASES_ON `wl_state_memory (t:(A,C,FFI)wl_state)
              (byte_align (word_add (word_add pa bytes_in_word) (word index)))` THEN
  CASE_REWRITE_TAC[option_DISTINCT]) THEN
  (COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val (word 2:A word) = 2 /\ ~(2 >= dimindex (:A))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ASP6AUX_good_dimindex_small; ARITH_RULE `2 < 32`]; ALL_TAC] THEN
  ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                  ASP6AUX_inst_Store8; WORD_ADD_ASSOC; ASP6AUX_set_var_fields;
                  BIGPAUX_USHR_4; ASP6AUX_byte_zx_word_val; mem_store_byte_aux_def;
                  data_to_word_Unit_def]) THEN
  (ASP6AUX_FINISH_TAC) THEN
  (REWRITE_TAC[GSYM WORD_IWORD; WORD_VAL] THEN
   MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `index < LENGTH (ws:byte list)`) o
     SPECL [`index:num`; `w:byte`] o check (fun th ->
     can (find_term ((=) `LUPDATE:byte->num->byte list->byte list`)) (concl th))) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[theWord_def] THEN
   MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]));;

let ASP6AUX_do_app_DerefByte = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp DerefByte) vs s = Rval (v,s2) <=>
     ?b ptr i fl ws. vs = [data_RefPtr b ptr; data_Number i] /\
       lookup ptr (data_state_refs s) = SOME (bvl_ByteArray fl ws) /\
       &0 <= i /\ i < &(LENGTH ws) /\ v = data_Number (&(val (EL (num_of_int i) ws))) /\
       s2 = do_stack (MemOp DerefByte) vs (do_lim_safe s (MemOp DerefByte) vs)`,
  ASP6AUX_DO_APP_TAC `MemOp DerefByte`);;

(* HOL4 line 14984 *)
let assign_DerefByte = prove
 ((assign_thm_stmt `op = MemOp DerefByte`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_DerefByte] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `a2:num` STRIP_ASSUME_TAC) o
    REWRITE_RULE[ASP6AUX_get_vars_2]) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_DerefByte_def; data_to_word_list_Seq_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  ASP6AUX_GET_VARS_TAC [`a1:num`; `a2:num`] [`w1:A word_loc`; `w2:A word_loc`] THEN
  ABBREV_TAC `index = num_of_int i` THEN
  (SUBGOAL_THEN `i = &index:int` SUBST_ALL_TAC THENL
   [EXPAND_TAC "index" THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LT]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_ByteArray_IMP o
    (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ByteArray fl ws)`)
                         (ASSUME `good_dimindex (:A)`))) o
    check (asp6_asm_app "memory_rel")) THEN
  DISCH_THEN(X_CHOOSE_THEN `pw:A word` (X_CHOOSE_THEN `pa:A word` (X_CHOOSE_THEN `hdr:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC) THEN
  (SUBGOAL_THEN `LENGTH (ws:byte list) < 2 EXP (dimindex (:A) - 3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (dimindex (:A) - 3) * 8 = dimword (:A)` ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def] THEN
    SUBGOAL_THEN `dimindex (:A) = (dimindex (:A) - 3) + 3`
      (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
     [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
      REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `small_int (:A) (&index)` ASSUME_TAC THENL
   [REWRITE_TAC[small_int_def] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SIMP_TAC[DIV_MULT; ARITH_RULE `~(8 = 0)`] THEN
    REWRITE_TAC[INT_OF_NUM_LT; INT_ARITH `-- &a <= &b:int`] THEN ASM_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `w2 = wl_Word (word (4 * index):A word)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM MP6AUX_SMALLNUM_NUM] THEN MATCH_MP_TAC memory_rel_Number_IMP THEN
    MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
      `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
      `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
      `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
      `[]:(data_v # A word_loc) list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `data_RefPtr b ptr`)) (concl th) &&
      not (can (find_term ((=) `LUPDATE:byte->num->byte list->byte list`)) (concl th)))) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * index < dimword (:A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try rand (concl th) = `dimword (:A)` with Failure _ -> false)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word pa) /\
                wl_word_exp t (real_byte_offset (adjust_var a2)) =
                SOME (wl_Word (word_add bytes_in_word (word index)))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC get_var_get_real_addr_lemma THEN EXISTS_TAC `pw:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def];
      ASM_SIMP_TAC[GSYM BIGPAUX_USHR_4] THEN MATCH_MP_TAC get_real_byte_offset_lemma THEN
      ASM_REWRITE_TAC[wl_get_var_def]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `index:num` o check (fun th ->
    can (find_term ((=) `mem_load_byte_aux:(A word->A word_loc)->(A word->bool)->bool->A word->byte option`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word 2:A word) = 2 /\ ~(2 >= dimindex (:A))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ASP6AUX_good_dimindex_small; ARITH_RULE `2 < 32`]; ALL_TAC] THEN
  ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                  ASP6AUX_inst_Load8; WORD_ADD_ASSOC; ASP6AUX_set_var_fields]) THEN
  (ASP6AUX_FINISH_TAC) THEN
  (ASM_SIMP_TAC[ASP6AUX_shl_zx_byte; GSYM MP6AUX_SMALLNUM_NUM] THEN
   MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_SIMP_TAC[small_int_w2n] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN REWRITE_TAC[]));;

let ASP6AUX_do_app_Const = prove
 (`!i vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp (clos_Const i)) vs s = Rval (v,s2) <=>
     vs = [] /\ small_enough_int i /\ v = data_Number i /\
     s2 = do_stack (IntOp (clos_Const i)) vs (do_lim_safe s (IntOp (clos_Const i)) vs)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`IntOp (clos_Const i)`; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "int_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  STRUCT_CASES_TAC(ISPEC `vs:data_v list` list_CASES) THEN
  REWRITE_TAC[data_do_int_app_def; NOT_CONS_NIL] THEN
  TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[injectivity "result"; distinctness "result";
                                       PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 15075 *)
let assign_Const = prove
 (assign_thm_stmt `(?i. op = IntOp (clos_Const i))`,
  ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `i:int` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_Const] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST (assign_Const i l dest) =
                (wl_Assign (adjust_var dest) (wl_Const (Smallnum i)):(A)wl_prog)`
    SUBST1_TAC THENL
   [REWRITE_TAC[assign_Const_def; data_to_word_Smallnum_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  ASP6AUX_EV_TAC [word_exp_rw] THEN
  ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP1AUX_state_rel_set_var THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN ASM_REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN
  ASM_SIMP_TAC[MP3AUX_small_enough_int] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN REWRITE_TAC[]);;

let ASP6AUX_do_app_GlobalsPtr = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (GlobOp GlobalsPtr) vs s = Rval (v,s2) <=>
     ?p. vs = [] /\ data_state_global s = SOME p /\ v = data_RefPtr T p /\
         s2 = do_stack (GlobOp GlobalsPtr) vs (do_lim_safe s (GlobOp GlobalsPtr) vs)`,
  ASP6AUX_DO_APP_TAC `GlobOp GlobalsPtr`);;

(* HOL4 line 15097 *)
let assign_GlobalsPtr = prove
 (assign_thm_stmt `op = GlobOp GlobalsPtr`,
  ASP6AUX_INTRO_TAC (DISCH_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_GlobalsPtr] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  ASP6AUX_EV_TAC [word_exp_rw] THEN
  ASM_REWRITE_TAC[FLOOKUP_DEF] THEN CASE_REWRITE_TAC[] THEN
  ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP1AUX_state_rel_set_var THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN ASM_REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  ASM_REWRITE_TAC[MEM; MEM_APPEND; the_global_def; OPTION_MAP_DEF; misc_the_def] THEN
  MESON_TAC[]);;

let ASP6AUX_do_app_Global = prove
 (`!k vs (s:(C,FFI)data_state) v s2.
     data_do_app (GlobOp (clos_Global k)) vs s = Rval (v,s2) <=>
     ?ptr xs. vs = [] /\ data_state_global s = SOME ptr /\
         lookup ptr (data_state_refs s) = SOME (bvl_ValueArray xs) /\
         k < LENGTH xs /\ v = EL k xs /\
         s2 = do_stack (GlobOp (clos_Global k)) vs
                (do_lim_safe s (GlobOp (clos_Global k)) vs)`,
  ASP6AUX_DO_APP_TAC `GlobOp (clos_Global k)`);;

let ASP6AUX_memory_rel_GlobReal = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars w.
     memory_rel c be ts refs sp st m dm vars /\
     FLOOKUP st Globals = SOME (wl_Word w) ==>
     ?a. get_real_simple_addr c st w = SOME a /\ FLOOKUP st GlobReal = SOME (wl_Word a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `glob_real_inv c curr (FLOOKUP (st:(store_name,A word_loc)fmap) Globals)
                 (FLOOKUP st GlobReal)` THEN
  ASM_REWRITE_TAC[glob_real_inv_def; get_real_simple_addr_def; option_INJ;
                  injectivity "word_loc"] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let ASP6AUX_state_rel_memory_rel_global = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs ptr.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_global s = SOME ptr ==>
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (data_RefPtr T ptr,FAPPLY (wl_state_store t) Globals)
          (APPEND (join_env (data_state_locals s)
                    (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  ASM_REWRITE_TAC[MEM; MEM_APPEND; the_global_def; OPTION_MAP_DEF; misc_the_def] THEN
  MESON_TAC[]);;

(* HOL4 line 15119 *)
let assign_Global = prove
 ((assign_thm_stmt `(?n. op = GlobOp (clos_Global n))`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_Global] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Global_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  DRULE_ALL ASP6AUX_state_rel_memory_rel_global THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Deref' o
    (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ValueArray xs)`)
                       (CONJ (ASSUME `good_dimindex (:A)`) (ASSUME `k < LENGTH (xs:data_v list)`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_RefPtr_T_IMP o
    (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
    check (fun th -> asp6_is_app "memory_rel" (concl th) &&
                     can (find_term ((=) `data_RefPtr T ptr`)) (rand (concl th)) &&
                     not (can (find_term ((=) `EL k (xs:data_v list)`)) (concl th)))) THEN
  STRIP_TAC) THEN
  (SUBGOAL_THEN `ptr_w:A word = w /\ x1:A word = a` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals = wl_Word w` THEN
    ASM_REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) w = SOME a` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) Globals = SOME (wl_Word w)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP6AUX_memory_rel_GlobReal o
    (fun th -> CONJ th (ASSUME `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) Globals =
                                SOME (wl_Word w)`)) o
    check (asp6_asm_app "memory_rel")) THEN
  ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(X_CHOOSE_THEN `a2:A word` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN
  ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0]) THEN
  (SUBGOAL_THEN `word_add a2 (word_mul bytes_in_word (word (k + 1))) =
                 word_add (word_add a2 bytes_in_word) (word_mul bytes_in_word (word k)):A word`
     SUBST1_TAC THENL [REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP1AUX_state_rel_set_var THEN
   EXISTS_TAC `s:(C,FFI)data_state` THEN ASM_REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `EL k (xs:data_v list)`)) (concl th))) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN
   ASM_REWRITE_TAC[MEM; MEM_APPEND; the_global_def; OPTION_MAP_DEF; misc_the_def] THEN
   MESON_TAC[]));;

let ASP6AUX_do_app_SetGlobal = prove
 (`!k vs (s:(C,FFI)data_state) v s2.
     data_do_app (GlobOp (SetGlobal k)) vs s = Rval (v,s2) <=>
     ?x ptr xs. vs = [x] /\ data_state_global s = SOME ptr /\
         lookup ptr (data_state_refs s) = SOME (bvl_ValueArray xs) /\
         k < LENGTH xs /\ v = data_Unit /\
         s2 = data_state_refs_fupd
                (K (insert ptr (bvl_ValueArray (LUPDATE x k xs)) (data_state_refs s)))
                (do_stack (GlobOp (SetGlobal k)) vs
                  (do_lim_safe s (GlobOp (SetGlobal k)) vs))`,
  ASP6AUX_DO_APP_TAC `GlobOp (SetGlobal k)`);;

(* HOL4 line 15154 *)
let assign_SetGlobal = prove
 ((assign_thm_stmt `(?n. op = GlobOp (SetGlobal n))`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_SetGlobal] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a1:num` STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_get_vars_1]) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_SetGlobal_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  DRULE_ALL ASP6AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  DRULE_ALL ASP6AUX_state_rel_memory_rel_global THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_RefPtr_T_IMP o
    (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
    check (fun th -> asp6_is_app "memory_rel" (concl th) &&
                     (try rand(rator(rand(concl th))) = `data_RefPtr T ptr` with Failure _ -> false) ||
                     (try fst(dest_pair(rand(rator(rand(concl th))))) = `data_RefPtr T ptr` with Failure _ -> false))) THEN
  STRIP_TAC) THEN
  (SUBGOAL_THEN `memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
      (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
      (CONS (x':data_v,w1:A word_loc)
        (CONS (data_RefPtr T ptr,FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)
          (APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
                    (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))))`
     MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
      can (find_term ((=) `CONS (x':data_v,w1:A word_loc)`)) (concl th))) THEN
    MATCH_MP_TAC memory_rel_rearrange THEN
    ASM_REWRITE_TAC[MEM; MEM_APPEND; the_global_def; OPTION_MAP_DEF; misc_the_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP memory_rel_Update' o
    (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ValueArray xs)`)
                       (CONJ (ASSUME `good_dimindex (:A)`) (ASSUME `k < LENGTH (xs:data_v list)`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr_w:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `ptr_w:A word = w /\ x1:A word = a` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals = wl_Word w` THEN
    ASM_REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) w = SOME a` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) Globals = SOME (wl_Word w)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP6AUX_memory_rel_GlobReal o
    (fun th -> CONJ th (ASSUME `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) Globals =
                                SOME (wl_Word w)`)) o
    check (asp6_asm_app "memory_rel")) THEN
  ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(X_CHOOSE_THEN `a2:A word` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `word_add a2 (word_mul bytes_in_word (word (k + 1))) =
                 word_add (word_add a2 bytes_in_word) (word_mul bytes_in_word (word k)):A word`
     ASSUME_TAC THENL [REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; wl_mem_store_def; ITLIST; OPTION_MAP_DEF;
                  WORD_ADD_0; data_to_word_Unit_def]) THEN
  (ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final THEN
   MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
                         `wl_Word (word 2):A word_loc`;
                         `wl_state_locals (t:(A,C,FFI)wl_state)`] THEN
   ASM_REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds;
                   K_THM; ASP6AUX_DO_STACK_FIELDS]) THEN
  (MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `LUPDATE (x':data_v) k xs`)) (concl th))) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN
   ASM_REWRITE_TAC[MEM; MEM_APPEND; the_global_def; OPTION_MAP_DEF; misc_the_def] THEN
   MESON_TAC[]));;

let ASP6AUX_memory_rel_set_globals = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars www ra.
     memory_rel c be ts refs sp st m dm vars /\
     get_real_simple_addr c st www = SOME ra ==>
     memory_rel c be ts refs sp (st |+ (Globals,wl_Word www) |+ (GlobReal,wl_Word ra))
       m dm vars`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                                heap_element)list`; `limit:num`; `a:num`; `sp':num`;
                        `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"] THEN
  MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `get_real_simple_addr c (st:(store_name,A word_loc)fmap) www = SOME ra` THEN
  ASM_REWRITE_TAC[get_real_simple_addr_def; glob_real_inv_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[]);;

let ASP6AUX_do_app_SetGlobalsPtr = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (GlobOp SetGlobalsPtr) vs s = Rval (v,s2) <=>
     ?p. vs = [data_RefPtr T p] /\ v = data_Unit /\
         s2 = data_state_global_fupd (K (SOME p))
                (do_stack (GlobOp SetGlobalsPtr) vs
                  (do_lim_safe s (GlobOp SetGlobalsPtr) vs))`,
  ASP6AUX_DO_APP_TAC `GlobOp SetGlobalsPtr`);;

(* HOL4 line 15204 *)
let assign_SetGlobalsPtr = prove
 ((assign_thm_stmt `op = GlobOp SetGlobalsPtr`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_SetGlobalsPtr] o
    check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                     with Failure _ -> false)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a1:num` STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_get_vars_1]) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_SetGlobalsPtr_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
  DRULE_ALL ASP6AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_RefPtr_T_IMP o
    (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o
    check (asp6_asm_app "memory_rel")) THEN
  DISCH_THEN(X_CHOOSE_THEN `www:A word` (X_CHOOSE_THEN `ra:A word` (X_CHOOSE_THEN `hd:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `wl_word_exp (wl_set_store Globals (wl_Word www) (t:(A,C,FFI)wl_state))
                  (real_addr c (adjust_var a1)) = SOME (wl_Word ra)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `www:A word` THEN
    ASM_REWRITE_TAC[wl_set_store_def; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    UNDISCH_TAC `get_real_addr c (wl_state_store (t:(A,C,FFI)wl_state)) www = SOME ra` THEN
    REWRITE_TAC[get_real_addr_def; FLOOKUP_UPDATE; distinctness "store_name"];
    ALL_TAC]) THEN
  (ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; data_to_word_Unit_def]) THEN
  (ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final THEN
   MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`;
                         `wl_Word (word 2):A word_loc`;
                         `wl_state_locals (t:(A,C,FFI)wl_state)`] THEN
   ASM_REWRITE_TAC[wl_set_var_def; wl_set_store_def; wl_state_INFO.ri_accfupds;
                   data_state_INFO.ri_accfupds; K_THM; ASP6AUX_DO_STACK_FIELDS;
                   FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"; MEM;
                   FAPPLY_FUPDATE_THM] THEN
   CONJ_TAC THENL [MESON_TAC[distinctness "store_name"]; ALL_TAC] THEN
   MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC ASP6AUX_memory_rel_set_globals THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `CONS (data_RefPtr T p,wl_Word (www:A word))`)) (concl th))) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN
   ASM_REWRITE_TAC[MEM; MEM_APPEND; the_global_def; OPTION_MAP_DEF; misc_the_def] THEN
   MESON_TAC[]));;

(* HOL4 line 15265 *)
let IMP = prove
 (`!b1 b2. b1 \/ b2 <=> ~b1 ==> b2`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b1:bool` THEN BOOL_CASES_TAC `b2:bool` THEN
  REWRITE_TAC[]);;

(* HOL4 line 15271 *)
let memcopy_def = cake_def
  `memcopy k (a1:A word) (a2:A word) (m:A word->B) dm =
     if k = 0 then SOME m else
       if a1 IN dm /\ a2 IN dm then
         memcopy (k - 1) (word_add a1 bytes_in_word) (word_add a2 bytes_in_word)
           ((a2 =+ m a1) m) dm
       else NONE`;;

(* HOL4 memcopy_ind (made by Definition) *)
let memcopy_ind = cake_ind "memcopy";;

(* HOL4 line 15279 *)
let MemCopy_thm = prove
 (`!ret_val l1 l2 k a1 a2 (s:(A,C,FFI)wl_state) m dm m1.
     memcopy k a1 a2 m dm = SOME m1 /\
     wl_state_memory s = m /\ wl_state_mdomain s = dm /\
     lookup MemCopy_location (wl_state_code s) = SOME (5,MemCopy_code) /\
     k <= wl_state_clock s /\ 4 * k < dimword (:A) /\
     wl_get_var 0 s = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 s = SOME (wl_Word (word (4 * k))) /\
     wl_get_var 4 s = SOME (wl_Word (a1:A word)) /\
     wl_get_var 6 s = SOME (wl_Word a2) /\
     wl_get_var 8 s = SOME ret_val ==>
     ?smx.
       wl_evaluate (MemCopy_code,s) =
         (SOME (wl_Result (wl_Loc l1 l2) [ret_val]),
          wl_state_clock_fupd (K (wl_state_clock s - k))
            (wl_state_memory_fupd (K m1) (wl_state_locals_fupd (K LN)
               (wl_state_locals_size_fupd (K (SOME 0)) (wl_state_stack_max_fupd (K smx) s))))) /\
       option_le smx
         (OPTION_MAP2 MAX (wl_state_stack_max s)
            (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack s))
               (lookup MemCopy_location (wl_state_stack_size s))))`,
  (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
    [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[memcopy_def] THEN REWRITE_TAC[option_INJ] THEN
     STRIP_TAC THEN EXISTS_TAC `wl_state_stack_max (s:(A,C,FFI)wl_state)` THEN
     REWRITE_TAC[option_le_max_right; option_le_refl] THEN
     REWRITE_TAC[MemCopy_code_def] THEN
     ASP6AUX_EV_TAC [word_exp_rw; asm_word_cmp_def; WORD_AND_0; MULT_CLAUSES; SUB_0;
                     wl_get_vars_def; wl_flush_state_def] THEN
     REWRITE_TAC[PAIR_EQ; wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                 SUB_0] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[memcopy_def] THEN
   REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
   SUBGOAL_THEN `~(word (4 * SUC k) = word 0:A word)` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD; GSYM dimword_def] THEN
     ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `word_sub (word (4 * SUC k)) (word 4) = word (4 * k):A word` ASSUME_TAC THENL
    [REWRITE_TAC[MULT_CLAUSES; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
   REWRITE_TAC[MemCopy_code_def; data_to_word_list_Seq_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   FIRST_X_ASSUM(ASSUME_TAC o CAKE_SIMP_RULE [] o
     check ((=) `~(word (4 * SUC k) = word 0:A word)` o concl)) THEN
   ASP6AUX_EV_TAC [word_exp_rw; asm_word_cmp_def; WORD_AND_REFL; wl_get_vars_def;
                   wl_mem_load_def; wl_mem_store_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                   ASP6AUX_set_var_fields; word_op_def]) THEN
  (REWRITE_TAC[ASP6AUX_ev_Call_tail] THEN
   SIMP (wl_get_vars_def :: wl_get_var_def :: bad_dest_args_def :: add_ret_loc_def ::
         wl_find_code_def :: LENGTH :: lookup_insert :: wl_state_INFO.ri_accfupds :: K_THM ::
         [ASP6AUX_set_var_fields]) THEN
   COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `word_sub (word (4 + 4 * k)) (word 4) = word (4 * k):A word` SUBST1_TAC THENL
    [REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
   ABBREV_TAC `s6 = wl_call_env
            [wl_Loc l1 l2; wl_Word (word (4 * k):A word);
             wl_Word (word_add a1 bytes_in_word);
             wl_Word (word_add a2 bytes_in_word); ret_val]
            (lookup MemCopy_location (wl_state_stack_size (s:(A,C,FFI)wl_state)))
            (wl_dec_clock
            (wl_state_memory_fupd (K ((a2 =+ m a1) m))
            (wl_set_var 6 (wl_Word (word_add a2 bytes_in_word))
            (wl_set_var 4 (wl_Word (word_add a1 bytes_in_word))
            (wl_set_var 2 (wl_Word (word (4 * k)))
            (wl_set_var 1 (m a1) s))))))` THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a1:A word) bytes_in_word`;
     `word_add (a2:A word) bytes_in_word`; `s6:(A,C,FFI)wl_state`;
     `((a2:A word) =+ (m:A word->A word_loc) a1) m`; `dm:A word->bool`;
     `m1:A word->A word_loc`] o check (is_forall o concl)) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "s6" THEN
     REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM;
                 ASP6AUX_set_var_fields; wl_get_var_def; fromList2_def; FOLDL] THEN
     CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[lookup_insert; SND] THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
   EXISTS_TAC `smx:num option` THEN
   EXPAND_TAC "s6" THEN
   REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM;
               ASP6AUX_set_var_fields; PAIR_EQ] THEN
   CONJ_TAC THENL
    [REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM;
                 ASP6AUX_set_var_fields] THEN ASM_ARITH_TAC;
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "option_le" (concl th) &&
     can (find_term ((=) `s6:(A,C,FFI)wl_state`)) (concl th))) THEN
   EXPAND_TAC "s6" THEN
   REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM;
               ASP6AUX_set_var_fields] THEN
   SPEC_TAC(`OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (s:(A,C,FFI)wl_state)))
               (lookup MemCopy_location (wl_state_stack_size s))`,`y:num option`) THEN
   SPEC_TAC(`wl_state_stack_max (s:(A,C,FFI)wl_state)`,`x:num option`) THEN
   REPEAT GEN_TAC THEN
   MAP_EVERY (fun v -> STRUCT_CASES_TAC(ISPEC v option_CASES))
     [`x:num option`; `y:num option`; `smx:num option`] THEN
   REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC));;

(* HOL4 line 15317: Theorem assign_ConsExtend_expand (SIMP_CONV (srw_ss())  *)
(* [assign_def] on assign c n l dest (BlockOp (ConsExtend tag)) args        *)
(* names_opt): the unfolding of data_to_word_assign at ConsExtend; a        *)
(* conversion result, here by the kit's simplifier                          *)
let assign_ConsExtend_expand =
  CAKE_SIMP_CONV [data_to_word_assign_def]
    `data_to_word_assign c n l dest (BlockOp (ConsExtend tag)) args names_opt:
       (A)wl_prog#num`;;

(* HOL4 line 15321 *)
let data_to_word_assignProof_get_vars_IMP_domain = prove
 (`!xs (s:A spt) y. data_get_vars xs s = SOME y ==> ALL (\x. x IN domain s) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[get_vars_SOME_IFF_data_eq; ALL; data_get_var_def;
                                   domain_lookup] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `y':A` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:A spt`; `ys:A list`]) THEN
    ASM_REWRITE_TAC[domain_lookup]]);;

(* HOL4 line 15330 *)
let memory_rel_IMP_free_space = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     ?nfree curr other.
       FLOOKUP st NextFree = SOME (wl_Word nfree) /\
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       (word_list_exists nfree sp STAR other) (fun2set (m,dm))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN
   STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`word_add curr (word_mul bytes_in_word (word a)):A word`;
                         `curr:A word`] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (asp6_is_app "word_ml_inv" o concl)) THEN
   REWRITE_TAC[word_ml_inv_def; abs_ml_inv_def; unused_space_inv_def] THEN STRIP_TAC THEN
   ASM_CASES_TAC `sp = 0` THENL
    [EXISTS_TAC `word_heap curr heap c STAR word_heap (other:A word) (heap_expand limit) c` THEN
     ASM_REWRITE_TAC[data_to_word_memoryProof_word_list_exists_thm; SEP_CLAUSES];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `~(sp' + sp1 = 0)` (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th)) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
   DISCH_THEN(X_CHOOSE_THEN `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list` (X_CHOOSE_THEN `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
       heap_element)list` STRIP_ASSUME_TAC)) THEN
   UNDISCH_TAC `(word_heap curr heap c STAR word_heap (other:A word) (heap_expand limit) c)
      (fun2set ((m:A word->A word_loc),dm))` THEN
   ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def; word_el_def] THEN
   SUBGOAL_THEN `((sp' + sp1) - 1) + 1 = sp + ((sp' + sp1) - sp)` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[data_to_word_memoryProof_word_list_exists_ADD] THEN
   DISCH_THEN(MP_TAC o ASP6AUX_STAR_FOCUS (fun l ->
     try asp6_is_app "word_list_exists" l && rand l = `sp:num` with Failure _ -> false)) THEN
   MESON_TAC[]));;

(* HOL4 line 15356 *)
let IMP_store_list_SOME = prove
 (`!ws (a:A word) n (m:A word->A word_loc) dm other.
     (word_list_exists a n STAR other) (fun2set (m,dm)) /\ LENGTH ws <= n ==>
     ?m1. data_to_word_memoryProof_store_list a ws m dm = SOME m1 /\
          (misc_word_list a ws STAR
           word_list_exists (word_add a (word_mul bytes_in_word (word (LENGTH ws))))
             (n - LENGTH ws) STAR
           other) (fun2set (m1,dm))`,
  (LIST_INDUCT_TAC THENL
    [REWRITE_TAC[data_to_word_memoryProof_store_list_def; misc_word_list_def; LENGTH;
                 WORD_MUL_0; WORD_ADD_0; SUB_0; SEP_CLAUSES; option_INJ] THEN
     MESON_TAC[];
     ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
   REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
   REWRITE_TAC[data_to_word_memoryProof_word_list_exists_thm; SEP_CLAUSES; SEP_EXISTS_THM] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `w0:A word_loc`) ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP read_fun2set o
     MP4AUX_STAR_AC_RULE `set_sep_one (a:A word,w0:A word_loc) STAR
        (word_list_exists (word_add a bytes_in_word) n' STAR other)`) THEN
   STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `h:A word_loc` o MATCH_MP write_fun2set o
     MP4AUX_STAR_AC_RULE `set_sep_one (a:A word,w0:A word_loc) STAR
        (word_list_exists (word_add a bytes_in_word) n' STAR other)`) THEN
   DISCH_THEN(MP_TAC o MP4AUX_STAR_AC_RULE
     `word_list_exists (word_add (a:A word) bytes_in_word) n' STAR
        (other STAR set_sep_one (a,h:A word_loc))`) THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:A word) bytes_in_word`; `n':num`;
     `(a =+ h) (m:A word->A word_loc)`; `dm:A word->bool`;
     `other STAR set_sep_one (a:A word,h:A word_loc)`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `m1:A word->A word_loc` THEN
   ASM_REWRITE_TAC[data_to_word_memoryProof_store_list_def; misc_word_list_def; SUB_SUC]) THEN
  (SUBGOAL_THEN `word_add (word_add a bytes_in_word) (word_mul bytes_in_word (word (LENGTH (t:(A word_loc)list)))) =
                 word_add a (word_mul bytes_in_word (word (SUC (LENGTH t)))):A word`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
   ASP6AUX_SEP_AC_TAC));;

(* HOL4 line 15373 *)
let get_vars_cut_env = prove
 (`!vs bs nms (x1:A spt) x2.
     data_cut_env nms x1 = SOME x2 /\
     data_get_vars vs x1 = SOME bs /\
     ALL (\v. v IN domain nms) vs ==>
     data_get_vars vs x2 = SOME bs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[get_vars_SOME_IFF_data_eq; ALL] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`y:A`; `ys:A list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `data_cut_env nms (x1:A spt) = SOME x2` THEN
    REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[data_get_var_def; lookup_mk_wf; lookup_inter_alt] THEN
    ASM_MESON_TAC[data_get_var_def];
    ASM_MESON_TAC[]]);;

(* HOL4 line 15387 *)
let word_exp_real_addr_some_value = prove
 (`!(s3:(A,C,FFI)wl_state) curr a ww c.
     FLOOKUP (wl_state_store s3) CurrHeap = SOME (wl_Word curr) /\
     wl_get_var a s3 = SOME (wl_Word ww) /\
     good_dimindex (:A) /\ shift_length c < dimindex (:A) ==>
     ?wx. wl_word_exp s3 (real_addr c a) = SOME (wl_Word wx)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `!k. k < dimindex (:A) ==> val (word k:A word) = k /\ ~(k >= dimindex (:A))`
     ASSUME_TAC THENL
    [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
      [ALL_TAC; UNDISCH_TAC `k < dimindex (:A)` THEN ARITH_TAC] THEN
     REWRITE_TAC[VAL_WORD] THEN
     MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `dimindex (:A)` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[dimword_def; LT_POW2_REFL];
     ALL_TAC] THEN
   SUBGOAL_THEN `backend_common_word_shift (:A) < dimindex (:A) /\
                 shift_length c - backend_common_word_shift (:A) < dimindex (:A)`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `good_dimindex (:A)` THEN UNDISCH_TAC `shift_length c < dimindex (:A)` THEN
     REWRITE_TAC[backend_common_word_shift_def; good_dimindex_def] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun th ->
     if is_forall (concl th) then
       MAP_EVERY (fun k -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME k)))
         [`backend_common_word_shift (:A) < dimindex (:A)`;
          `shift_length c - backend_common_word_shift (:A) < dimindex (:A)`;
          `shift_length c < dimindex (:A)`]
     else NO_TAC)) THEN
  (REWRITE_TAC[real_addr_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   REPEAT COND_CASES_TAC THEN
   REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; MAP;
                                     word_op_def; word_sh_def] THEN CASE_REWRITE_TAC[])) THEN
   REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[]));;

(* HOL4 line 15398 *)
let store_list_APPEND = prove
 (CASE_TERM
  `!xs ys (a:A word) (m:A word->A word_loc) dm.
     data_to_word_memoryProof_store_list a (APPEND xs ys) m dm =
     match data_to_word_memoryProof_store_list a xs m dm with
       NONE -> NONE
     | SOME m1 ->
         data_to_word_memoryProof_store_list
           (word_add a (word_mul bytes_in_word (word (LENGTH xs)))) ys m1 dm`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; data_to_word_memoryProof_store_list_def; LENGTH] THEN
  CASE_REWRITE_TAC[WORD_MUL_0; WORD_ADD_0] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_add (word_add (a:A word) bytes_in_word)
                  (word_mul bytes_in_word (word (LENGTH (t:(A word_loc)list)))) =
                word_add a (word_mul bytes_in_word (word (SUC (LENGTH t))))`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 15410 *)
let memory_rel_store_list_to_unused = prove
 (`!ws2 (m:A word->A word_loc) dm m1 c be ts refs n st vars nfree.
     memory_rel c be ts refs n st m dm vars /\
     data_to_word_memoryProof_store_list nfree ws2 m dm = SOME m1 /\
     FLOOKUP st NextFree = SOME (wl_Word nfree) /\ LENGTH ws2 <= n ==>
     memory_rel c be ts refs n st m1 dm vars`,
  (MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
    [REWRITE_TAC[data_to_word_memoryProof_store_list_def; option_INJ] THEN MESON_TAC[];
     ALL_TAC] THEN
   X_GEN_TAC `l:(A word_loc)list` THEN DISCH_TAC THEN X_GEN_TAC `x:A word_loc` THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC[SNOC_APPEND; store_list_APPEND; LENGTH_APPEND; LENGTH] THEN
   CASES_ON `data_to_word_memoryProof_store_list nfree (l:(A word_loc)list) (m:A word->A word_loc) dm` THEN
   CASE_REWRITE_TAC[option_DISTINCT] THEN
   REWRITE_TAC[data_to_word_memoryProof_store_list_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`m:A word->A word_loc`; `dm:A word->bool`; `a:A word->A word_loc`;
     `c:data_to_word_config`; `be:bool`; `ts:num`; `refs:((data_v)bvl_ref)spt`; `n:num`;
     `st:(store_name,A word_loc)fmap`; `vars:(data_v#A word_loc)list`; `nfree:A word`]) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:A word_loc` o MATCH_MP memory_rel_write) THEN
   ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
   DISCH_THEN(X_CHOOSE_THEN `fr:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
   DISCH_THEN(MP_TAC o SPEC `LENGTH (l:(A word_loc)list)`) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   EXPAND_TAC "m1" THEN MESON_TAC[]));;

(* HOL4 line 15424 *)
let get_vars_delete_lemma = prove
 (`!t7 (s1:(A,C,FFI)wl_state) x9 x7 x5 x1.
     wl_get_vars (MAP adjust_var t7)
       (wl_state_locals_fupd
          (K (insert 9 x9 (insert 7 x7 (insert 5 x5 (insert 1 x1 (wl_state_locals s1))))))
          s1) =
     wl_get_vars (MAP adjust_var t7) s1`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; wl_get_vars_def] THEN
  REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
              adjust_var_NEQ]);;

(* HOL4 line 15437 *)
let INTRO_IS_SOME = prove
 (`!x:A option. (?v. x = SOME v) <=> IS_SOME x`,
  GEN_TAC THEN CASES_ON `x:A option` THEN
  REWRITE_TAC[IS_SOME_DEF; option_INJ; option_DISTINCT] THEN MESON_TAC[]);;

(* HOL4 line 15443 *)
let STAR_fun2set_IMP_SEP_T = prove
 (`!p q (m:A->B) dm.
     (p STAR q) (fun2set (m,dm)) ==> (p STAR SEP_T) (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`fun2set ((m:A->B),dm)`,`s:A#B->bool`) THEN
  REWRITE_TAC[STAR_def; SEP_T_def] THEN MESON_TAC[]);;

(* HOL4 line 15452 *)
let IMP_memcopy_lemma = prove
 (`!c (s1:(A,C,FFI)wl_state) ts (x:(C,FFI)data_state) sp m1 ts' n' l' w_ptr ys7 ws1 vars
    startptr a1 wx.
     memory_rel c (wl_state_be s1) ts (data_state_refs x) sp (wl_state_store s1) m1
       (wl_state_mdomain s1)
       (CONS (data_Block ts' n' l',wl_Word w_ptr) (APPEND (ZIP ys7 ws1) vars)) /\
     startptr < LENGTH l' /\ LENGTH ys7 = LENGTH ws1 /\ good_dimindex (:A) /\
     lookup (adjust_var a1) (wl_state_locals s1) = SOME (wl_Word (w_ptr:A word)) /\
     wl_word_exp s1 (real_addr c (adjust_var a1)) = SOME (wl_Word wx) ==>
     memory_rel c (wl_state_be s1) ts (data_state_refs x) sp (wl_state_store s1) m1
       (wl_state_mdomain s1)
       (CONS (data_Block ts' n' l',wl_Word w_ptr)
          (APPEND (ZIP (APPEND ys7 [EL startptr l'])
                       (APPEND ws1 [m1 (word_add (word_add wx bytes_in_word)
                                          (word_mul bytes_in_word (word startptr)))]))
             vars)) /\
     (word_add (word_add wx bytes_in_word) (word_mul bytes_in_word (word startptr)))
       IN wl_state_mdomain s1`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
     (fun th -> CONJ th (ASSUME `good_dimindex (:A)`)) o check (asp6_asm_app "memory_rel")) THEN
   SUBGOAL_THEN `~(l':data_v list = [])` (fun th -> REWRITE_TAC[th]) THENL
    [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `startptr < LENGTH ([]:data_v list)` THEN
     REWRITE_TAC[LENGTH; LT];
     ALL_TAC] THEN
   REWRITE_TAC[injectivity "word_loc"] THEN
   DISCH_THEN(X_CHOOSE_THEN `w0:A word` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `hx:A word` STRIP_ASSUME_TAC)))) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `w_ptr:A word = w0` o concl)) THEN
   SUBGOAL_THEN `wx:A word = a` SUBST_ALL_TAC THENL
    [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP3AUX_memory_rel_conf o
       check (asp6_asm_app "memory_rel")) THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `adjust_var a1`; `s1:(A,C,FFI)wl_state`;
                    `w_ptr:A word`; `a:A word`] get_real_addr_lemma) THEN
     ASM_REWRITE_TAC[wl_get_var_def; option_INJ; injectivity "word_loc"];
     ALL_TAC] THEN
   SUBGOAL_THEN `small_int (:A) (&startptr)` ASSUME_TAC THENL
    [MP_TAC(SPEC `startptr:num` ASP6AUX_small_index) THEN ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL
      [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `LENGTH (l':data_v list)` THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN
       MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (dimindex (:A) - 4)` THEN
       ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
       SIMP_TAC[]];
     ALL_TAC]) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_swap o MATCH_MP IMP_memory_rel_Number o
     (fun th -> CONJ (ASSUME `good_dimindex (:A)`)
                  (CONJ (ASSUME `small_int (:A) (&startptr)`) th)) o
     check (asp6_asm_app "memory_rel")) THEN
   DISCH_THEN(MP_TAC o MATCH_MP memory_rel_El o
     (fun th -> CONJ th (CONJ (ASSUME `good_dimindex (:A)`)
                          (ASSUME `startptr < LENGTH (l':data_v list)`)))) THEN
   REWRITE_TAC[injectivity "word_loc"] THEN
   DISCH_THEN(X_CHOOSE_THEN `pw:A word` (X_CHOOSE_THEN `iw:A word`
     (X_CHOOSE_THEN `xa:A word` (X_CHOOSE_THEN `ya:A word` STRIP_ASSUME_TAC)))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `w_ptr:A word = pw`);
                               GSYM(ASSUME `Smallnum (&startptr):A word = iw`)]) THEN
   ALL_TAC) THEN
  (SUBGOAL_THEN `xa:A word = a /\
                 ya = word_add bytes_in_word (word_mul (word startptr) bytes_in_word):A word`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `get_real_addr c (wl_state_store (s1:(A,C,FFI)wl_state)) w_ptr = SOME xa` THEN
     UNDISCH_TAC `get_real_offset (Smallnum (&startptr):A word) = SOME ya` THEN
     ASM_SIMP_TAC[ASP6AUX_get_real_offset_Smallnum; option_INJ] THEN MESON_TAC[];
     ALL_TAC] THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
     try let l = lhs (concl th) in l = `xa:A word` || l = `ya:A word` with Failure _ -> false))) THEN
   SUBGOAL_THEN `word_add (word_add a bytes_in_word) (word_mul bytes_in_word (word startptr)) =
                 word_add a (word_add bytes_in_word (word_mul (word startptr) bytes_in_word)):A word`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `EL startptr (l':data_v list)`)) (concl th))) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN
   SIMP_TAC[GSYM ZIP_APPEND; LENGTH; ASSUME `LENGTH (ys7:data_v list) = LENGTH (ws1:(A word_loc)list)`] THEN
   REWRITE_TAC[MEM; MEM_APPEND; ZIP; HD; TL] THEN MESON_TAC[]));;

let ASP6AUX_word_list_SNOC = prove
 (`!(a:A word) h t (x:A word_loc).
     misc_word_list a (CONS h (APPEND t [x])) =
     misc_word_list a (CONS h t) STAR
     set_sep_one (word_add a (word_mul bytes_in_word (word (SUC (LENGTH t)))),x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN
  REWRITE_TAC[data_to_word_memoryProof_word_list_APPEND; LENGTH] THEN
  REWRITE_TAC[misc_word_list_def; SEP_CLAUSES] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 15487 (HOL4: Q.prove ... |> SPEC_ALL |> GEN_ALL; the unused   *)
(* bound variables m2 ts are dropped by SPEC_ALL/GEN_ALL)                   *)
let IMP_memcopy = prove
 (`!len startptr m1 ws1 ys7 k c (s1:(A,C,FFI)wl_state) ts (x:(C,FFI)data_state) sp ts' n'
    l' w_ptr vars nfree full_header other a1 wx.
     memory_rel c (wl_state_be s1) ts (data_state_refs x) sp (wl_state_store s1) m1
       (wl_state_mdomain s1)
       (CONS (data_Block ts' n' l',wl_Word w_ptr) (APPEND (ZIP ys7 ws1) vars)) /\
     (misc_word_list nfree (CONS (wl_Word full_header) ws1) STAR
      word_list_exists
        (word_add nfree (word_mul bytes_in_word (word (SUC (LENGTH ws1))))) k STAR other)
       (fun2set (m1,wl_state_mdomain s1)) /\ len <= k /\ good_dimindex (:A) /\
     lookup (adjust_var a1) (wl_state_locals s1) = SOME (wl_Word (w_ptr:A word)) /\
     wl_word_exp s1 (real_addr c (adjust_var a1)) = SOME (wl_Word wx) /\
     FLOOKUP (wl_state_store s1) NextFree = SOME (wl_Word nfree) /\
     startptr + len <= LENGTH l' /\
     LENGTH ws1 + len < sp /\
     LENGTH ys7 = LENGTH ws1 ==>
     ?m2 ws2.
       memcopy len (word_add (word_add wx bytes_in_word)
                      (word_mul bytes_in_word (word startptr)))
         (word_add nfree (word_mul bytes_in_word (word (LENGTH ws1 + 1)))) m1
         (wl_state_mdomain s1) = SOME m2 /\
       (misc_word_list nfree (CONS (wl_Word full_header) (APPEND ws1 ws2)) STAR SEP_T)
         (fun2set (m2,wl_state_mdomain s1)) /\
       LENGTH ws2 = len /\
       memory_rel c (wl_state_be s1) ts (data_state_refs x) sp (wl_state_store s1) m2
         (wl_state_mdomain s1)
         (APPEND (ZIP (APPEND ys7 (TAKE len (DROP startptr l'))) (APPEND ws1 ws2)) vars)`,
  (INDUCT_TAC THENL
    [REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[memcopy_def] THEN
     MAP_EVERY EXISTS_TAC [`m1:A word->A word_loc`; `[]:(A word_loc)list`] THEN
     REWRITE_TAC[APPEND_NIL; TAKE_0; LENGTH] THEN CONJ_TAC THENL
      [MATCH_MP_TAC STAR_fun2set_IMP_SEP_T THEN
       EXISTS_TAC `word_list_exists (word_add nfree (word_mul bytes_in_word
          (word (SUC (LENGTH (ws1:(A word_loc)list)))))) k STAR other:(A word#A word_loc->bool)->bool` THEN
       ASP6AUX_SEP_AC_TAC;
       FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (asp6_asm_app "memory_rel")) THEN
       REWRITE_TAC[]];
     ALL_TAC]) THEN
  (REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
   REWRITE_TAC[ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
   REWRITE_TAC[data_to_word_memoryProof_word_list_exists_thm; SEP_CLAUSES; SEP_EXISTS_THM] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w0:A word_loc`)
     STRIP_ASSUME_TAC)) THEN
   ABBREV_TAC `dst = word_add nfree (word_mul bytes_in_word
                       (word (SUC (LENGTH (ws1:(A word_loc)list))))):A word` THEN
   SUBGOAL_THEN `word_add nfree (word_mul bytes_in_word (word (LENGTH (ws1:(A word_loc)list) + 1))) =
                 dst:A word` SUBST1_TAC THENL [EXPAND_TAC "dst" THEN REWRITE_TAC[ADD1]; ALL_TAC] THEN
   ABBREV_TAC `src = word_add (word_add wx bytes_in_word)
                       (word_mul bytes_in_word (word startptr)):A word` THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `s1:(A,C,FFI)wl_state`; `ts:num`;
     `x:(C,FFI)data_state`; `sp:num`; `m1:A word->A word_loc`; `ts':num`; `n':num`;
     `l':data_v list`; `w_ptr:A word`; `ys7:data_v list`; `ws1:(A word_loc)list`;
     `vars:(data_v#A word_loc)list`; `startptr:num`; `a1:num`; `wx:A word`]
     IMP_memcopy_lemma) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC]) THEN
  (ASP6AUX_SEP_R_TAC THEN
   ONCE_REWRITE_TAC[memcopy_def] THEN ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
   ABBREV_TAC `xx = (m1:A word->A word_loc) src` THEN
   ABBREV_TAC `m4 = ((dst:A word) =+ (xx:A word_loc)) m1` THEN
   SUBGOAL_THEN `memory_rel c (wl_state_be (s1:(A,C,FFI)wl_state)) ts
      (data_state_refs (x:(C,FFI)data_state)) sp (wl_state_store s1) m4
      (wl_state_mdomain s1)
      (CONS (data_Block ts' n' l',wl_Word w_ptr)
         (APPEND (ZIP (APPEND ys7 [EL startptr l']) (APPEND ws1 [xx:A word_loc])) vars))`
     ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `xx:A word_loc` o MATCH_MP memory_rel_write o
       check (fun th -> asp6_is_app "memory_rel" (concl th) &&
         can (find_term ((=) `EL startptr (l':data_v list)`)) (concl th))) THEN
     ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
     DISCH_THEN(X_CHOOSE_THEN `fr:A word` (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPEC `LENGTH (ws1:(A word_loc)list) + 1`))) THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `nfree:A word = fr` o concl)) THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     EXPAND_TAC "m4" THEN EXPAND_TAC "dst" THEN EXPAND_TAC "xx" THEN
     REWRITE_TAC[ADD1] THEN MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `xx:A word_loc` o MATCH_MP write_fun2set o
     ASP6AUX_STAR_FOCUS (fun l -> try asp6_is_one l && fst(dest_pair(rand l)) = `dst:A word`
                                  with Failure _ -> false) o
     check (fun th -> asp6_is_fun2set_asm (concl th) &&
       can (find_term ((=) `misc_word_list:A word->(A word_loc)list->(A word#A word_loc->bool)->bool`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`startptr + 1`; `m4:A word->A word_loc`;
     `APPEND ws1 [xx:A word_loc]`; `APPEND ys7 [EL startptr (l':data_v list)]`; `n:num`;
     `c:data_to_word_config`; `s1:(A,C,FFI)wl_state`; `ts:num`; `x:(C,FFI)data_state`;
     `sp:num`; `ts':num`; `n':num`; `l':data_v list`; `w_ptr:A word`;
     `vars:(data_v#A word_loc)list`; `nfree:A word`; `full_header:A word`;
     `other:(A word#A word_loc->bool)->bool`; `a1:num`; `wx:A word`] o
     check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
   SUBGOAL_THEN `word_add (word_add (wx:A word) bytes_in_word)
                   (word_mul bytes_in_word (word (startptr + 1))) =
                 word_add src bytes_in_word /\
                 word_add nfree (word_mul bytes_in_word (word ((LENGTH (ws1:(A word_loc)list) + SUC 0) + 1))) =
                 word_add dst bytes_in_word:A word /\
                 word_add nfree (word_mul bytes_in_word (word (SUC (LENGTH ws1 + SUC 0)))) =
                 word_add dst bytes_in_word`
     (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "src" THEN EXPAND_TAC "dst" THEN
     REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE;
     ALL_TAC]) THEN
  (ANTS_TAC THENL
    [CONJ_TAC THENL
      [REWRITE_TAC[ASP6AUX_word_list_SNOC] THEN ASM_REWRITE_TAC[] THEN
       ASP6AUX_SEP_AC_TAC;
       ASM_ARITH_TAC];
     ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `m2:A word->A word_loc` (X_CHOOSE_THEN `ws2:(A word_loc)list`
     STRIP_ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`m2:A word->A word_loc`; `CONS (xx:A word_loc) ws2`] THEN
   ASM_REWRITE_TAC[LENGTH] THEN
   SUBGOAL_THEN `startptr < LENGTH (l':data_v list)` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[DROP_EL_CONS; TAKE] THEN
   REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_fun2set_asm (concl th) &&
     can (find_term ((=) `m2:A word->A word_loc`)) (concl th))) THEN
   REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `m2:A word->A word_loc`)) (concl th))) THEN
   REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN SIMP_TAC[]));;

(* HOL4 line 15547 *)
let data_to_word_assignProof_cut_envs_adjust_sets_insert_ODD = prove
 (`!n (names:B spt) (w:A) t.
     ODD n ==>
     cut_envs (adjust_sets names) (insert n w t) = cut_envs (adjust_sets names) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[adjust_sets_def; cut_envs_def] THEN
  ASM_SIMP_TAC[cut_names_adjust_set_insert_ODD] THEN
  SUBGOAL_THEN `cut_names (LS one) (insert n (w:A) t) = cut_names (LS one) t`
    (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[ODD]; ALL_TAC] THEN
  REWRITE_TAC[cut_names_def; inter_insert; domain_insert] THEN
  SUBGOAL_THEN `domain (LS (one:1)) = {0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; domain_lookup; lookup_def; IN_SING] THEN MESON_TAC[option_DISTINCT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_SING] THEN
  SUBGOAL_THEN `{0} SUBSET n INSERT domain (t:A spt) <=> {0} SUBSET domain t`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SUBSET; IN_SING; IN_INSERT] THEN ASM_MESON_TAC[]);;

(* HOL4 line 15563 *)
let IN_domain_adjust_set_IMP = prove
 (`!x the_names:A spt.
     x IN domain (adjust_set the_names) ==>
     ?xa. x = adjust_var xa /\ xa IN domain the_names`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[adjust_set_def; domain_fromAList; IN_SET_OF_LIST; MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[MEM_toAList; domain_lookup; PAIR_EQ] THEN
  MESON_TAC[]);;

(* ConsExtend call machinery: local copies of part 2's tools for stub calls *)
(* (ASP6AUX_C2_ and asp6c2_ of data_to_word_assignProof_p2.ml, renamed)          *)
let asp6c2_head_is name tm =
  try let f,_ = strip_comb tm in is_const f && fst(dest_const f) = name
  with Failure _ -> false;;


let asp6c2_eval_rws =
  [wl_evaluate_def; wl_word_exp_def; wl_get_var_def; wl_set_var_def;
   wl_get_var_imm_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
   K_o_THM; K_THM; lookup_insert; ARITH_EQ; wl_word_cmp_def; insert_shadow];;

let asp6c2_eval_rws2 =
  [data_to_word_list_Seq_def; wl_inst_def; the_words_def; word_op_def; MAP; ITLIST;
   WORD_ADD_0; OPTION_MAP_DEF; wl_get_vars_def; wl_flush_state_def];;

let asp6c2_call_rws =
  [bad_dest_args_def; wl_find_code_def; add_ret_loc_def; wl_call_env_def;
   wl_dec_clock_def; LENGTH; ARITH_SUC; option_DISTINCT; NOT_CONS_NIL];;

(* the state st of the first wl_evaluate (code,st) in tm *)
let asp6c2_eval_arg code tm =
  let t = find_term (fun t ->
      try let f,a = dest_comb t in
          (match f with Const("wl_evaluate",_) -> fst(dest_pair a) = code
                      | _ -> false)
      with Failure _ -> false) tm in
  snd(dest_pair(rand t));;


let rec asp6c2_drule_n asl n th =
  if n = 0 then th else
  let mp = MATCH_MP_CURRIED th in
  tryfind (fun a -> asp6c2_drule_n asl (n-1) (mp a)) asl;;

(* MP_TAC th with its first n (curried) antecedents discharged by matching *)
(* assumptions                                                              *)
let ASP6AUX_C2_DRULE_N n th : tactic = fun (asl,w as g) ->
  MP_TAC (asp6c2_drule_n (map snd asl) n (IMP_CURRY_RULE (GEN_ALL th))) g;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of the byte copying loops.                                     *)
(* ------------------------------------------------------------------------- *)

let asp6c2_crw_conv asl thl = CASE_REWRITE_CONV (map snd asl @ thl);;

(* the first subterm wl_word_exp st (real_addr c v) of the goal: add its   *)
(* value SOME (wl_Word x) (get_var_get_real_addr_lemma) as an assumption;    *)
(* wl_get_var v st is computed by rewriting with thl and the assumptions,   *)
(* x comes from an assumption get_real_addr c _ ptr = SOME x                 *)
let ASP6AUX_C2_REAL_ADDR_TAC thl : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t ->
      try let f,args = strip_comb t in
          fst(dest_const f) = "wl_word_exp" && length args = 2 &&
          asp6c2_head_is "real_addr" (el 1 args)
      with Failure _ -> false) w in
  let st = rand(rator tm) and e = rand tm in
  let c = rand(rator e) and v = rand e in
  let gv = list_mk_icomb "wl_get_var" [v; st] in
  let th1 = asp6c2_crw_conv asl thl gv in
  let ptr = rand(rand(rhs(concl th1))) in
  let x = rand(rhs(snd(find (fun (_,th) ->
            try let l = lhs(concl th) in
                asp6c2_head_is "get_real_addr" l && rand l = ptr && rand(rator(rator l)) = c
            with Failure _ -> false) asl) |> concl)) in
  (MP_TAC (ISPECL [c; v; st; ptr; x] get_var_get_real_addr_lemma) THEN
   ANTS_TAC THENL [ASP2AUX_CRW_TAC thl; DISCH_TAC]) g;;

(* symbolic evaluation: rewriting, with the real_addr expressions resolved *)
let ASP6AUX_C2_EVAL_TAC thl : tactic =
  ASP2AUX_CRW_TAC thl THEN
  REPEAT(ASP6AUX_C2_REAL_ADDR_TAC thl THEN ASP2AUX_CRW_TAC thl);;


(* lookup loc (wl_state_code t) = SOME (k,code) for a stub, from the code_rel *)
(* assumption                                                               *)
let ASP6AUX_C2_STUB_TAC tm : tactic =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MATCH_MP_TAC ASP2AUX_code_rel_stub THEN
    FIRST_ASSUM(fun th -> if asp6c2_head_is "data_to_word_gcProof_code_rel" (concl th)
                          then MAP_EVERY EXISTS_TAC [rand(rator(rator(concl th)));
                                                     rand(rator(concl th))] THEN
                               ASM_REWRITE_TAC[]
                          else failwith "") THEN
    REWRITE_TAC[data_to_word_stubs_def; MEM; MEM_APPEND];
    ALL_TAC];;

(* MP_TAC (mk st) where st is the state of the first wl_evaluate (code,st)  *)
(* of the goal                                                               *)
let ASP6AUX_C2_EVAL_LEMMA_TAC code (mk:term->thm) : tactic = fun (asl,w as g) ->
  MP_TAC (mk (asp6c2_eval_arg code w)) g;;


(* for the memory_rel assumption th (vars = CONS x1 (CONS x2 ... rest)),    *)
(* add memory_rel ... (CONS xi1 (CONS xi2 ... rest)) for the indices is     *)

(* the data_do_app clause of ConsExtend *)
let ASP6AUX_do_app_ConsExtend = prove
 (`!tag vs (x:(C,FFI)data_state) v s2 ts.
     data_do_app (BlockOp (ConsExtend tag)) vs x = Rval (v,s2) /\
     data_state_tstamps x = SOME ts ==>
     ?bts btag xs' lower len xs.
       vs = CONS (data_Block bts btag xs') (CONS (data_Number lower)
              (CONS (data_Number len) (CONS (data_Number (&(LENGTH xs) + len)) xs))) /\
       &0 <= lower /\ &0 <= len /\ lower + len <= &(LENGTH xs') /\
       ~(&(LENGTH xs) + len = &0) /\
       v = data_Block ts tag (APPEND xs (TAKE (num_of_int len) (DROP (num_of_int lower) xs'))) /\
       s2 = check_lim (data_state_tstamps_fupd (K (SOME (ts + 1)))
              (do_stack (BlockOp (ConsExtend tag)) vs (do_lim_safe
                (data_state_space_fupd (K 0)
                  (data_state_safe_for_space_fupd
                    (K (data_state_safe_for_space x /\ no_thunks_in_refs (data_state_refs x) /\
                        size_of_heap_args vs x + space_consumed x (BlockOp (ConsExtend tag)) vs <=
                        limits_heap_limit (data_state_limits x)))
                    (data_state_peak_heap_length_fupd
                      (K (MAX (data_state_peak_heap_length x)
                              (size_of_heap_args vs x +
                               space_consumed x (BlockOp (ConsExtend tag)) vs)))
                      x))) (BlockOp (ConsExtend tag)) vs)))
            (LENGTH (APPEND xs (TAKE (num_of_int len) (DROP (num_of_int lower) xs'))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; MEM;
     distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op"] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; COND_CASE_EQ; distinctness "result"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "with_fresh_ts" (lhs (concl th))
                                          with Failure _ -> false)) THEN
  REWRITE_TAC[with_fresh_ts_def; ASP6AUX_DO_STACK_FIELDS; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; INT_NOT_LT; INT_GT; INT_NOT_LT]) THEN
  ASM_MESON_TAC[]);;

let ASP6AUX_get_vars_CONS = prove
 (`!args (s:A spt) x1 xs.
     data_get_vars args s = SOME (CONS x1 xs) <=>
     ?a1 rest. args = CONS a1 rest /\ lookup a1 s = SOME x1 /\ data_get_vars rest s = SOME xs`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `args:num list` list_CASES) THEN
  REWRITE_TAC[get_vars_SOME_IFF_data_eq; NOT_CONS_NIL; CONS_11; data_get_var_def] THEN
  MESON_TAC[]);;

(* peel the first argument off a data_get_vars assumption with a CONS value *)
let ASP6AUX_GV_PEEL_TAC (a:term) (r:term) : tactic =
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[ASP6AUX_get_vars_CONS] o
    check (fun th -> try asp6_is_app "data_get_vars" (lhs (concl th)) &&
                         is_cons (rand (rhs (concl th)))
                     with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN r STRIP_ASSUME_TAC));;

(* ASP6AUX_GIVEUP_TAC for goals with several state_rel assumptions: uses   *)
(* the one of s and t                                                       *)
let ASP6AUX_GIVEUP_BASE_TAC (sm_tac:tactic) (safe_tac:tactic) : tactic =
  let base = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                (t:(A,C,FFI)wl_state) NONE locs` in
  FIRST_ASSUM(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC o
    MATCH_MP evaluate_GiveUp2 o check (fun th -> concl th = base)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
    check (fun th -> concl th = base)) THEN
  MAP_EVERY EXISTS_TAC [`SOME (NotEnoughSpace:(A)wl_result)`; `r:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w as g) ->
     if asp6_is_app "option_le" w then
       (MATCH_MP_TAC option_le_trans THEN
        EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC option_le_trans THEN
        EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; sm_tac]) g
     else safe_tac g);;

(* the cut of the arguments and the live variables of a call is defined *)
let ASP6AUX_cut_env_list_insert_SOME = prove
 (`!args kept (env:A spt) vals x.
     data_get_vars args env = SOME vals /\ data_cut_env kept env = SOME x ==>
     ?xa. data_cut_env (list_insert args kept) env = SOME xa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_assignProof_get_vars_IMP_domain) THEN
  UNDISCH_TAC `data_cut_env kept (env:A spt) = SOME x` THEN
  REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
  COND_CASES_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[SUBSET; domain_list_insert] THEN
  ASM_MESON_TAC[SUBSET]);;

let ASP6AUX_exp_dimindex_4 = prove
 (`good_dimindex (:A) ==> 2 EXP (dimindex (:A) - 4) <= dimword (:A) DIV 8`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;
(* peel the first value off a wl_get_vars assumption with a CONS argument list *)
let ASP6AUX_WGV_PEEL_TAC (w:term) (r:term) : tactic =
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[CONJUNCT2 (SPEC_ALL get_vars_SOME_IFF_eq)] o
    check (fun th -> try asp6_is_app "wl_get_vars" (lhs (concl th)) &&
                         is_cons (rand (rator (lhs (concl th))))
                     with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN w (X_CHOOSE_THEN r STRIP_ASSUME_TAC));;

let ASP6AUX_ConsExtend_s1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (s1:(A,C,FFI)wl_state) locs xa sp a1 a2 a3 a4 t7 bts btag
    xs' startptr len ys7.
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K xa) (data_state_space_fupd (K sp) s)) s1 NONE locs /\
     data_get_vars (CONS a1 (CONS a2 (CONS a3 (CONS a4 t7)))) xa =
       SOME (CONS (data_Block bts btag xs') (CONS (data_Number (&startptr))
         (CONS (data_Number (&len)) (CONS (data_Number (&(LENGTH ys7 + len))) ys7)))) /\
     startptr + len <= LENGTH xs' /\ small_int (:A) (&(LENGTH ys7 + len)) ==>
     lookup (adjust_var a2) (wl_state_locals s1) = SOME (wl_Word (word (4 * startptr))) /\
     lookup (adjust_var a3) (wl_state_locals s1) = SOME (wl_Word (word (4 * len))) /\
     lookup (adjust_var a4) (wl_state_locals s1) =
       SOME (wl_Word (word (4 * (LENGTH ys7 + len)))) /\
     ?ws1 w_ptr.
       wl_get_vars (MAP adjust_var t7) s1 = SOME ws1 /\ LENGTH ws1 = LENGTH ys7 /\
       lookup (adjust_var a1) (wl_state_locals s1) = SOME (wl_Word w_ptr) /\
       (~(xs' = []) ==> ?a_ptr. get_real_addr c (wl_state_store s1) w_ptr = SOME a_ptr) /\
       memory_rel c (wl_state_be s1) (THE (data_state_tstamps s)) (data_state_refs s) sp
         (wl_state_store s1) (wl_state_memory s1) (wl_state_mdomain s1)
         (CONS (data_Block bts btag xs',wl_Word w_ptr)
           (APPEND (ZIP ys7 ws1)
             (APPEND (join_env xa (toAList (sptree_inter (wl_state_locals s1) (adjust_set xa))))
               (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store s1) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack s1))))))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `data_get_vars (CONS a1 (CONS a2 (CONS a3 (CONS a4 t7))))
     (data_state_locals (data_state_locals_fupd (K (xa:data_v spt))
       (data_state_space_fupd (K sp) (s:(C,FFI)data_state)))) =
     SOME (CONS (data_Block bts btag xs') (CONS (data_Number (&startptr))
       (CONS (data_Number (&len)) (CONS (data_Number (&(LENGTH (ys7:data_v list) + len))) ys7))))`
     ASSUME_TAC THENL
    [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_state_rel_get_vars o
     (fun th -> CONJ th (ASSUME `data_get_vars (CONS a1 (CONS a2 (CONS a3 (CONS a4 t7))))
     (data_state_locals (data_state_locals_fupd (K (xa:data_v spt))
       (data_state_space_fupd (K sp) (s:(C,FFI)data_state)))) =
     SOME (CONS (data_Block bts btag xs') (CONS (data_Number (&startptr))
       (CONS (data_Number (&len)) (CONS (data_Number (&(LENGTH (ys7:data_v list) + len))) ys7))))`)) o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC)) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[MAP]) THEN
   ASP6AUX_WGV_PEEL_TAC `w1:A word_loc` `r1:(A word_loc)list` THEN
   ASP6AUX_WGV_PEEL_TAC `w2:A word_loc` `r2:(A word_loc)list` THEN
   ASP6AUX_WGV_PEEL_TAC `w3:A word_loc` `r3:(A word_loc)list` THEN
   ASP6AUX_WGV_PEEL_TAC `w4:A word_loc` `ws1:(A word_loc)list` THEN
   RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ZIP; LENGTH; SUC_INJ; APPEND; wl_get_var_def]) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Block_IMP o
     C CONJ (ASSUME `good_dimindex (:A)`) o check (asp6_asm_app "memory_rel")) THEN
   DISCH_THEN(X_CHOOSE_THEN `w_ptr:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
   SUBGOAL_THEN `small_int (:A) (&startptr) /\ small_int (:A) (&len)` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[MP6AUX_SMALL_INT_NUM] THEN
     FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP6AUX_exp_dimindex_4 o
       check ((=) `good_dimindex (:A)` o concl)) THEN
     ASM_CASES_TAC `xs':data_v list = []` THENL
      [UNDISCH_TAC `startptr + len <= LENGTH (xs':data_v list)` THEN
       ASM_REWRITE_TAC[LENGTH] THEN
       SUBGOAL_THEN `0 < dimword (:A) DIV 8` MP_TAC THENL
        [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
         STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
         ARITH_TAC];
       FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
       STRIP_TAC THEN ASM_ARITH_TAC];
     ALL_TAC]) THEN
  (FIRST_ASSUM(fun th0 -> let th = check (asp6_asm_app "memory_rel") th0 in
     MP_TAC(MATCH_MP memory_rel_Number_IMP (end_itlist CONJ
       [ASSUME `good_dimindex (:A)`; ASSUME `small_int (:A) (&startptr)`;
        MATCH_MP memory_rel_tl th])) THEN
     MP_TAC(MATCH_MP memory_rel_Number_IMP (end_itlist CONJ
       [ASSUME `good_dimindex (:A)`; ASSUME `small_int (:A) (&len)`;
        MATCH_MP memory_rel_tl (MATCH_MP memory_rel_tl th)])) THEN
     MP_TAC(MATCH_MP memory_rel_Number_IMP (end_itlist CONJ
       [ASSUME `good_dimindex (:A)`;
        ASSUME `small_int (:A) (&(LENGTH (ys7:data_v list) + len))`;
        MATCH_MP memory_rel_tl (MATCH_MP memory_rel_tl (MATCH_MP memory_rel_tl th))]))) THEN
   REWRITE_TAC[MP6AUX_SMALLNUM_NUM] THEN
   REPEAT(DISCH_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC [`ws1:(A word_loc)list`; `w_ptr:A word`] THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
    [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
     ASM_REWRITE_TAC[] THEN MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (asp6_asm_app "memory_rel")) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]));;

(* the variables of the data program are not changed by odd temporaries *)
let ASP6AUX_get_vars_adjust_set_var_ODD = prove
 (`!xs k v (s:(A,C,FFI)wl_state).
     ODD k ==>
     wl_get_vars (MAP adjust_var xs) (wl_set_var k v s) = wl_get_vars (MAP adjust_var xs) s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; wl_get_vars_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `ODD k`)]) THEN
  REWRITE_TAC[wl_get_var_def; ASP6AUX_set_var_fields; lookup_insert] THEN
  SUBGOAL_THEN `~(adjust_var h = k)` (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN UNDISCH_TAC `ODD (adjust_var h)` THEN
  REWRITE_TAC[GSYM NOT_EVEN; EVEN_adjust_var]);;

(* the StoreEach of ConsExtend: header and copied elements stored at NextFree *)
let ASP6AUX_StoreEach_ConsExtend = prove
 (`!(s1:(A,C,FFI)wl_state) t7 ws1 nfree hdr x9 x7 sp other.
     wl_get_vars (MAP adjust_var t7) s1 = SOME ws1 /\
     (word_list_exists nfree sp STAR other) (fun2set (wl_state_memory s1,wl_state_mdomain s1)) /\
     LENGTH ws1 + 1 <= sp ==>
     ?m1. wl_evaluate (StoreEach 1 (CONS 5 (MAP adjust_var t7)) (word 0),
            wl_set_var 9 x9 (wl_set_var 7 x7 (wl_set_var 5 (wl_Word hdr)
              (wl_set_var 1 (wl_Word nfree) s1)))) =
          (NONE,wl_state_memory_fupd (K m1) (wl_set_var 9 x9 (wl_set_var 7 x7
             (wl_set_var 5 (wl_Word hdr) (wl_set_var 1 (wl_Word nfree) s1))))) /\
          data_to_word_memoryProof_store_list nfree (CONS (wl_Word hdr) ws1)
            (wl_state_memory s1) (wl_state_mdomain s1) = SOME m1 /\
          (misc_word_list nfree (CONS (wl_Word hdr) ws1) STAR
           word_list_exists
             (word_add nfree (word_mul bytes_in_word (word (LENGTH ws1 + 1))))
             (sp - (LENGTH ws1 + 1)) STAR other) (fun2set (m1,wl_state_mdomain s1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`CONS (wl_Word hdr) (ws1:(A word_loc)list)`; `nfree:A word`; `sp:num`;
    `wl_state_memory (s1:(A,C,FFI)wl_state)`; `wl_state_mdomain (s1:(A,C,FFI)wl_state)`;
    `other:(A word#A word_loc->bool)->bool`] IMP_store_list_SOME) THEN
  ASM_REWRITE_TAC[LENGTH; ARITH_RULE `SUC n = n + 1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m1:A word->A word_loc` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC evaluate_StoreEach THEN
  MAP_EVERY EXISTS_TAC [`CONS (wl_Word hdr) (ws1:(A word_loc)list)`; `nfree:A word`] THEN
  ASM_REWRITE_TAC[ASP6AUX_set_var_fields; wl_get_vars_def; wl_get_var_def; lookup_insert;
                  ARITH] THEN
  ASM_SIMP_TAC[ASP6AUX_get_vars_adjust_set_var_ODD; ARITH] THEN CASE_REWRITE_TAC[]);;

(* the Make_ptr_bits_code of ConsExtend (tag in 9, length in 7, result in 3) *)
let ASP6AUX_Make_ptr_ConsExtend = prove
 (`!c (st:(A,C,FFI)wl_state) tag n nfree curr.
     shift_length c < dimindex (:A) /\ tag < dimword (:A) /\ n < dimword (:A) /\
     FLOOKUP (wl_state_store st) NextFree = SOME (wl_Word nfree) /\
     FLOOKUP (wl_state_store st) CurrHeap = SOME (wl_Word curr) /\
     lookup 9 (wl_state_locals st) = SOME (wl_Word (word tag)) /\
     lookup 7 (wl_state_locals st) = SOME (wl_Word (word n)) ==>
     wl_evaluate (Make_ptr_bits_code c 9 7 3,st) =
       (NONE,wl_set_var 3 (make_cons_ptr c (word_sub nfree curr) tag n) st)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC data_to_word_assignProof_Make_ptr_bits_thm THEN
  ASM_REWRITE_TAC[ARITH] THEN
  UNDISCH_TAC `shift_length c < dimindex (:A)` THEN REWRITE_TAC[shift_length_def] THEN
  ARITH_TAC);;

(* rewrite the goal with the assumption wl_evaluate (CNAME ...,_) = ...     *)
let ASP6AUX_USE_EV_TAC (cname:string) : tactic =
  FIRST_ASSUM(fun th ->
    let l = lhs (concl th) in
    if asp6_is_app "wl_evaluate" l &&
       (let h = fst (strip_comb (fst (dest_pair (rand l)))) in
        is_const h && fst (dest_const h) = cname)
    then REWRITE_TAC[th] THEN CASE_REWRITE_TAC[] else NO_TAC);;

(* real_addr reads only the CurrHeap entry of the store and one variable *)
let ASP6AUX_real_addr_eq = prove
 (`!c v (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state).
     FLOOKUP (wl_state_store s') CurrHeap = FLOOKUP (wl_state_store s) CurrHeap /\
     lookup v (wl_state_locals s') = lookup v (wl_state_locals s) ==>
     wl_word_exp s' (real_addr c v) = wl_word_exp s (real_addr c v)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_addr_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[word_exp_rw; MAP]);;

let ASP6AUX_word_exp_ShiftVar_Lsl = prove
 (`!(t:(A,C,FFI)wl_state) v n w.
     lookup v (wl_state_locals t) = SOME (wl_Word w) ==>
     wl_word_exp t (ShiftVar Lsl v n) = SOME (wl_Word (word_shl w n))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[word_exp_set_var_ShiftVar_lemma] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[OPTION_MAP_DEF]);;

(* the header of the block made by ConsExtend *)
let ASP6AUX_full_header = prove
 (`!c tag n (a:A word).
     encode_header c (4 * tag) 0 = SOME a /\
     data_to_word_config_len_size c + 7 < dimindex (:A) /\
     n < 2 EXP data_to_word_config_len_size c /\ n < 2 EXP (dimindex (:A) - 4) ==>
     encode_header c (4 * tag) n =
       SOME (word_or (word_shl (word (4 * n))
                       (dimindex (:A) - data_to_word_config_len_size c - 2)) a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[make_header_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_SHL_0; WORD_OR_0] THEN
  SUBGOAL_THEN `word (4 * n):A word = word_shl (word n) 2` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[WORD_SHL_COMPOSE] THEN
  SUBGOAL_THEN `2 + (dimindex (:A) - data_to_word_config_len_size c - 2) =
                dimindex (:A) - data_to_word_config_len_size c` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_OR_0; WORD_ZX_0]);;
let ASP6AUX_biw_mul_succ = prove
 (`!n. good_dimindex (:A) ==>
       word_mul bytes_in_word (word (n + 1)):A word =
       word_add bytes_in_word (word_shl (word n) (backend_common_word_shift (:A)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP bytes_in_word_mul_eq_shift th)]) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE);;
let ASP6AUX_startptr_addr = prove
 (`!k. good_dimindex (:A) ==>
       word_shl (word (4 * k)) (backend_common_word_shift (:A) - 2) =
       word_mul bytes_in_word (word k):A word`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP bytes_in_word_mul_eq_shift th]) THEN
  REWRITE_TAC[WORD_SHL_WORD; backend_common_word_shift_def] THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(* HOL4 line 15573 *)
let assign_ConsExtend = prove
 (assign_thm_stmt `(?tag. op = BlockOp (ConsExtend tag))`,
  (REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `tag:num` SUBST_ALL_TAC) THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def]) THEN
   MP_TAC(ISPEC `names_opt:(1 spt)option` option_CASES) THEN
   FIRST_X_ASSUM(fun th -> if is_neg (concl th) && can (find_term ((=) `names_opt:(1 spt)option`)) (concl th)
                           then REWRITE_TAC[th] else NO_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `kept:1 spt` SUBST_ALL_TAC)) THEN (FIRST_ASSUM(MP_TAC o MATCH_MP state_rel_cut_state_opt_SOME o
     (fun th -> end_itlist CONJ [th; ASSUME `data_get_vars args (data_state_locals (s:(C,FFI)data_state)) = SOME vals`;
        ASSUME `data_cut_state_opt (SOME kept) (s:(C,FFI)data_state) = SOME x`]) o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
     STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP do_app_stack_max o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
   FIRST_X_ASSUM(X_CHOOSE_TAC `ts:num` o REWRITE_RULE[IS_SOME_EXISTS] o
     check ((=) `IS_SOME (data_state_tstamps (s:(C,FFI)data_state))` o concl))) THEN (SUBGOAL_THEN `data_state_tstamps (x:(C,FFI)data_state) = SOME ts` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_ConsExtend o
     (fun th -> CONJ th (ASSUME `data_state_tstamps (x:(C,FFI)data_state) = SOME ts`)) o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`bts:num`; `btag:num`; `xs':data_v list`; `lw:int`; `ln:int`;
                        `ys7:data_v list`] THEN
   STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM])) THEN (FIRST_X_ASSUM(X_CHOOSE_THEN `startptr:num` SUBST_ALL_TAC o REWRITE_RULE[GSYM INT_OF_NUM_EXISTS] o
     check ((=) `&0 <= (lw:int)` o concl)) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `len:num` SUBST_ALL_TAC o REWRITE_RULE[GSYM INT_OF_NUM_EXISTS] o
     check ((=) `&0 <= (ln:int)` o concl)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NUM_OF_INT_OF_NUM; INT_OF_NUM_ADD; INT_OF_NUM_LE; INT_OF_NUM_EQ]) THEN
   REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_ADD] THEN
   ASP6AUX_GV_PEEL_TAC `a1:num` `r1:num list` THEN
   ASP6AUX_GV_PEEL_TAC `a2:num` `r2:num list` THEN
   ASP6AUX_GV_PEEL_TAC `a3:num` `r3:num list` THEN
   ASP6AUX_GV_PEEL_TAC `a4:num` `t7:num list` THEN
   RVEQ_TAC) THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
   REWRITE_TAC[assign_ConsExtend_expand; assign_ConsExtend_def] THEN CASE_REWRITE_TAC[] THEN
   CASES_ON `encode_header c (4 * tag) 0:(A word)option` THEN CASE_REWRITE_TAC[FST]) THENL [(REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   ASP6AUX_GIVEUP_BASE_TAC (FIRST_ASSUM ACCEPT_TAC)
    (DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[check_lim_def; data_state_INFO.ri_accfupds; K_THM] THEN
     DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe o CONJUNCT2) THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN
     REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LT; INT_GT; INT_OF_NUM_EQ; INT_OF_NUM_LE;
                 NUM_OF_INT_OF_NUM] THEN
     ASM_REWRITE_TAC[ARITH_RULE `~(a < 0)`; GSYM NOT_LE] THEN
     UNDISCH_TAC `encode_header c (4 * tag) 0:(A word)option = NONE` THEN
     REWRITE_TAC[encode_header_def; dimword_def; EXP_LT_0; ARITH; GSYM NOT_LE] THEN
     COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
     POP_ASSUM MP_TAC THEN CONV_TAC TAUT)); (MP_TAC(MATCH_MP ASP6AUX_state_rel_get_var1 (end_itlist CONJ
     [ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`;
      ASSUME `lookup a4 (data_state_locals (s:(C,FFI)data_state)) =
              SOME (data_Number (&(LENGTH (ys7:data_v list) + len)))`])) THEN
   DISCH_THEN(X_CHOOSE_THEN `w4:A word_loc` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
     CONJ (ASSUME `good_dimindex (:A)`) o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `w4:A word_loc`)) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `ww4:A word` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; data_to_word_list_Seq_def] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `adjust_var a4`; `ww4:A word`]
     evaluate_BignumHalt2) THEN
   ASM_REWRITE_TAC[wl_get_var_def] THEN
   DISCH_THEN(X_CHOOSE_THEN `rh:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
   ASM_CASES_TAC `~small_int (:A) (&(LENGTH (ys7:data_v list) + len))` THEN
   POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
   ASP6AUX_EV_TAC [word_exp_rw]) THENL [(ASP6AUX_QR_TAC THEN REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC option_le_trans THEN
     EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC option_le_trans THEN
     EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[check_lim_def; data_state_INFO.ri_accfupds; K_THM] THEN
   DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe o CONJUNCT2) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN
   REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LT; INT_GT; INT_OF_NUM_EQ; INT_OF_NUM_LE;
               NUM_OF_INT_OF_NUM] THEN
   ASM_REWRITE_TAC[ARITH_RULE `~(a < 0)`; GSYM NOT_LE] THEN
   SUBGOAL_THEN `LENGTH (APPEND ys7 (TAKE len (DROP startptr (xs':data_v list)))) =
                 LENGTH (ys7:data_v list) + len` SUBST1_TAC THENL
    [ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TAKE; LENGTH_DROP;
                  ARITH_RULE `a + b <= c ==> b <= c - a`];
     ALL_TAC] THEN
   SUBGOAL_THEN `dimword (:A) DIV 8 <= LENGTH (ys7:data_v list) + len` ASSUME_TAC THENL
    [UNDISCH_TAC `~small_int (:A) (&(LENGTH (ys7:data_v list) + len))` THEN
     REWRITE_TAC[small_int_def; INT_OF_NUM_LT; GSYM NOT_LE] THEN
     MATCH_MP_TAC(TAUT `b ==> ~(b /\ ~c) ==> c`) THEN INT_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `2 EXP dimindex (:A) DIV 16 <= LENGTH (ys7:data_v list) + len`
     (fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `dimword (:A) DIV 8` THEN
   ASM_REWRITE_TAC[dimword_def] THEN MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC); (FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[] o
     check ((=) `~ ~small_int (:A) (&(LENGTH (ys7:data_v list) + len))` o concl)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_Number_IMP o
     (fun th -> end_itlist CONJ [ASSUME `good_dimindex (:A)`;
                  ASSUME `small_int (:A) (&(LENGTH (ys7:data_v list) + len))`; th]) o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `ww4:A word`)) (concl th))) THEN
   REWRITE_TAC[injectivity "word_loc"; MP6AUX_SMALLNUM_NUM] THEN DISCH_THEN SUBST_ALL_TAC THEN
   PAIRARG_TAC) THEN (SUBGOAL_THEN `data_get_vars (CONS a1 (CONS a2 (CONS a3 (CONS a4 t7))))
                   (data_state_locals (s:(C,FFI)data_state)) =
                 SOME (CONS (data_Block bts btag xs') (CONS (data_Number (&startptr))
                   (CONS (data_Number (&len))
                   (CONS (data_Number (&(LENGTH (ys7:data_v list) + len))) ys7))))`
     ASSUME_TAC THENL
    [ASM_REWRITE_TAC[data_get_vars_def; data_get_var_def] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP2AUX_cut_state_opt_cut_env o
     check (fun th -> try asp6_is_app "data_cut_state_opt" (lhs (concl th)) with Failure _ -> false)) THEN
   FIRST_ASSUM(fun cth -> if asp6_is_app "data_cut_env" (lhs (concl cth)) then
     FIRST_ASSUM(fun gth -> if asp6_is_app "data_get_vars" (lhs (concl gth)) &&
                               is_cons (rand (rator (lhs (concl gth))))
       then MP_TAC(MATCH_MP ASP6AUX_cut_env_list_insert_SOME (CONJ gth cth)) else NO_TAC)
     else NO_TAC) THEN
   DISCH_THEN(X_CHOOSE_TAC `xa:data_v spt`) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[data_to_word_get_names_def]) THEN
   REWRITE_TAC[data_to_word_get_names_def]) THEN (SUBGOAL_THEN `4 * (LENGTH (ys7:data_v list) + len) < dimword (:A) /\
                 MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16) <
                 dimword (:A) DIV 8 /\
                 (LENGTH (ys7:data_v list) + len) < dimword (:A) DIV 8`
     STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `dimword (:A) = 2 EXP 32 \/ dimword (:A) = 2 EXP 64` MP_TAC THENL
      [REWRITE_TAC[dimword_def] THEN ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
     UNDISCH_TAC `small_int (:A) (&(LENGTH (ys7:data_v list) + len))` THEN
     REWRITE_TAC[small_int_def; INT_OF_NUM_LT] THEN
     STRIP_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
     RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     MP5AUX_ARITH_TAC;
     ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `wl_set_var 1 (wl_Word (word (4 * (LENGTH (ys7:data_v list) + len)))) (t:(A,C,FFI)wl_state)`;
     `locs:(num#num)list`; `CONS (a1:num) (CONS a2 (CONS a3 (CONS a4 (t7:num list))))`;
     `kept:1 spt`; `xa:data_v spt`;
     `CONS (data_Block bts btag xs') (CONS (data_Number (&startptr)) (CONS (data_Number (&len))
        (CONS (data_Number (&(LENGTH (ys7:data_v list) + len))) ys7)))`;
     `LENGTH (ys7:data_v list) + len`;
     `MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)`;
     `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] AllocVar_thm_nary) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[wl_set_var_def; state_rel_insert_1; wl_get_var_def;
                     wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
     FIRST_X_ASSUM(fun th -> if asp6_is_app "wl_evaluate" (lhs (concl th)) then
       MP_TAC th THEN REWRITE_TAC[wl_set_var_def] else NO_TAC) THEN
     SIMP_TAC[];
     ALL_TAC] THEN
   ASM_CASES_TAC `res = SOME (NotEnoughSpace:(A)wl_result)` THEN ASM_REWRITE_TAC[]) THENL [(REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`SOME (NotEnoughSpace:(A)wl_result)`; `s1:(A,C,FFI)wl_state`] THEN
   REWRITE_TAC[option_DISTINCT] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `cut_locals kept (s:(C,FFI)data_state) =
                 data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals s) kept))) s`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [REWRITE_TAC[cut_locals_def] THEN ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
     CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC option_le_trans THEN
     EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   DISCH_TAC THEN REWRITE_TAC[check_lim_def; data_state_INFO.ri_accfupds; K_THM] THEN
   DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe o CONJUNCT2) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lim_safe_def] THEN
   REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LT; INT_GT; INT_OF_NUM_EQ; INT_OF_NUM_LE;
               NUM_OF_INT_OF_NUM] THEN
   ASM_REWRITE_TAC[ARITH_RULE `~(a < 0)`; GSYM NOT_LE] THEN
   SUBGOAL_THEN `LENGTH (APPEND ys7 (TAKE len (DROP startptr (xs':data_v list)))) =
                 LENGTH (ys7:data_v list) + len` SUBST1_TAC THENL
    [ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TAKE; LENGTH_DROP;
                  ARITH_RULE `a + b <= c ==> b <= c - a`];
     ALL_TAC] THEN
   REWRITE_TAC[space_consumed_def; NUM_OF_INT_OF_NUM] THEN
   SUBGOAL_THEN `LENGTH (APPEND ys7 (TAKE len (DROP startptr (xs':data_v list)))) =
                 LENGTH (ys7:data_v list) + len` SUBST1_TAC THENL
    [ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TAKE; LENGTH_DROP;
                  ARITH_RULE `a + b <= c ==> b <= c - a`];
     ALL_TAC] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `LENGTH (ys7:data_v list) + len <
                 MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)`
     ASSUME_TAC THENL
    [REWRITE_TAC[dimword_def; MIN] THEN COND_CASES_TAC THEN MP5AUX_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
     can (find_term ((=) `limits_heap_limit (data_state_limits (s:(C,FFI)data_state))`))
       (concl th))) THEN
   ASM_REWRITE_TAC[] THEN MP5AUX_ARITH_TAC); (STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `data_get_vars (CONS a1 (CONS a2 (CONS a3 (CONS a4 t7)))) (xa:data_v spt) =
                 SOME (CONS (data_Block bts btag xs') (CONS (data_Number (&startptr))
                   (CONS (data_Number (&len))
                   (CONS (data_Number (&(LENGTH (ys7:data_v list) + len))) ys7))))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC get_vars_cut_env THEN
     EXISTS_TAC `list_insert (CONS a1 (CONS a2 (CONS a3 (CONS a4 t7)))) (kept:1 spt)` THEN
     EXISTS_TAC `data_state_locals (s:(C,FFI)data_state)` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[GSYM ALL_MEM; domain_list_insert] THEN MESON_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
     `s1:(A,C,FFI)wl_state`; `locs:(num#num)list`; `xa:data_v spt`;
     `(LENGTH (ys7:data_v list) + len) + 1`; `a1:num`; `a2:num`; `a3:num`; `a4:num`;
     `t7:num list`; `bts:num`; `btag:num`; `xs':data_v list`; `startptr:num`; `len:num`;
     `ys7:data_v list`] ASP6AUX_ConsExtend_s1) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ws1:(A word_loc)list`
       (X_CHOOSE_THEN `w_ptr:A word` STRIP_ASSUME_TAC)))))) THEN (FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_IMP_free_space o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `w_ptr:A word`)) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `nfree:A word` (X_CHOOSE_THEN `curr:A word`
     (X_CHOOSE_THEN `other:(A word#A word_loc->bool)->bool` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `val (word (dimindex (:A) - data_to_word_config_len_size c - 2):A word) =
                   dimindex (:A) - data_to_word_config_len_size c - 2 /\
                 ~(dimindex (:A) - data_to_word_config_len_size c - 2 >= dimindex (:A)) /\
                 val (word 2:A word) = 2 /\ ~(2 >= dimindex (:A))`
     STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[VAL_WORD; GE; NOT_LE] THEN
     SUBGOAL_THEN `dimindex (:A) < 2 EXP dimindex (:A) /\ 2 < dimindex (:A)` STRIP_ASSUME_TAC THENL
      [REWRITE_TAC[LT_POW2_REFL] THEN
       UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
       ALL_TAC] THEN
     REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MOD_LT) THEN
     MP5AUX_ARITH_TAC;
     ALL_TAC] THEN
   ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; ASP6AUX_set_var_fields;
                   ARITH; adjust_var_NEQ_1; BIGPAUX_USHR_4; WORD_OR_0]) THEN (W(fun (_,w) ->
     let st = asp6_callee_state "StoreEach" w in
     let hdr = rand (rand (rator (rand (rand st)))) in
     MP_TAC(ISPECL [`s1:(A,C,FFI)wl_state`; `t7:num list`; `ws1:(A word_loc)list`;
       `nfree:A word`; hdr; `wl_Word (word tag):A word_loc`;
       `wl_Word (word (LENGTH (ys7:data_v list) + len)):A word_loc`;
       `(LENGTH (ys7:data_v list) + len) + 1`;
       `other:(A word#A word_loc->bool)->bool`] ASP6AUX_StoreEach_ConsExtend)) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC)) THEN (SUBGOAL_THEN `backend_common_word_shift (:A) MOD dimword (:A) = backend_common_word_shift (:A) /\
                 val (word (backend_common_word_shift (:A)):A word) = backend_common_word_shift (:A) /\
                 ~(backend_common_word_shift (:A) >= dimindex (:A))`
     STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `backend_common_word_shift (:A) < dimindex (:A) /\
                   dimindex (:A) < dimword (:A)` STRIP_ASSUME_TAC THENL
      [REWRITE_TAC[dimword_def; LT_POW2_REFL] THEN MP5AUX_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `backend_common_word_shift (:A) MOD dimword (:A) = backend_common_word_shift (:A)`
       ASSUME_TAC THENL [MATCH_MP_TAC MOD_LT THEN MP5AUX_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[VAL_WORD; GE; NOT_LE; GSYM dimword_def];
     ALL_TAC]) THEN (SUBGOAL_THEN `tag < dimword (:A) /\ LENGTH (ys7:data_v list) + len < dimword (:A)`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(SPECL [`dimword (:A)`; `16`] DIV_LE) THEN MP_TAC(SPECL [`dimword (:A)`; `8`] DIV_LE) THEN
     UNDISCH_TAC `encode_header c (4 * tag) 0 = SOME (a:A word)` THEN
     REWRITE_TAC[encode_header_def] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
     POP_ASSUM MP_TAC THEN UNDISCH_TAC `LENGTH (ys7:data_v list) + len < dimword (:A) DIV 8` THEN
     ARITH_TAC;
     ALL_TAC]) THEN (W(fun (_,w) ->
     let st = asp6_callee_state "StoreEach" w in
     let st' = vsubst [st,`st0:(A,C,FFI)wl_state`]
                 `wl_state_memory_fupd (K (m1:A word->A word_loc)) (st0:(A,C,FFI)wl_state)` in
     MP_TAC(ISPECL [`c:data_to_word_config`; st'; `tag:num`; `LENGTH (ys7:data_v list) + len`;
                    `nfree:A word`; `curr:A word`] ASP6AUX_Make_ptr_ConsExtend)) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; ASP6AUX_set_var_fields; lookup_insert; ARITH] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   DISCH_TAC THEN ASP6AUX_USE_EV_TAC "StoreEach" THEN ASP6AUX_USE_EV_TAC "Make_ptr_bits_code" THEN
   MP_TAC(ISPECL [`s1:(A,C,FFI)wl_state`; `curr:A word`; `adjust_var a1`; `w_ptr:A word`;
                  `c:data_to_word_config`] word_exp_real_addr_some_value) THEN
   ASM_REWRITE_TAC[wl_get_var_def] THEN
   DISCH_THEN(X_CHOOSE_TAC `wx:A word`) THEN
   SUBGOAL_THEN `!st:(A,C,FFI)wl_state.
       FLOOKUP (wl_state_store st) CurrHeap =
         FLOOKUP (wl_state_store (s1:(A,C,FFI)wl_state)) CurrHeap /\
       lookup (adjust_var a1) (wl_state_locals st) = lookup (adjust_var a1) (wl_state_locals s1) ==>
       wl_word_exp st (real_addr c (adjust_var a1)) = SOME (wl_Word wx)`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
       try asp6_is_app "wl_word_exp" (lhs (concl th)) with Failure _ -> false)) THEN
     MATCH_MP_TAC ASP6AUX_real_addr_eq THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; ASP6AUX_set_var_fields;
                   ARITH; adjust_var_NEQ_1; BIGPAUX_USHR_4; WORD_OR_0;
                   wl_state_INFO.ri_accfupds; K_THM; ASP6AUX_set_store_fields;
                   FLOOKUP_UPDATE; distinctness "store_name"; adjust_var_eq_numeral;
                   GEN_ALL(ISPECL [`tt:(A,C,FFI)wl_state`; `adjust_var a2`; `nn:num`;
                     `word (4 * startptr):A word`] ASP6AUX_word_exp_ShiftVar_Lsl)]) THEN (ASM_CASES_TAC `len = 0` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC[MULT_CLAUSES; asm_word_cmp_def; WORD_AND_0] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; TAKE_0; APPEND_NIL; MULT_CLAUSES]) THEN
     REWRITE_TAC[ADD_CLAUSES; TAKE_0; APPEND_NIL] THEN ALL_TAC;
     ALL_TAC]) THENL [(SUBGOAL_THEN `data_cut_env kept (xa:data_v spt) =
                 SOME (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) kept))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC cut_env_cut_env_list_insert THEN
     MAP_EVERY EXISTS_TAC [`CONS (a1:num) (CONS a2 (CONS a3 (CONS a4 (t7:num list))))`;
                           `data_state_locals (s:(C,FFI)data_state)`] THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "data_cut_env" (lhs (concl th)) &&
       rand (rator (lhs (concl th))) = `kept:1 spt` with Failure _ -> false)) THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state))
          (kept:1 spt))))
          (data_state_space_fupd (K (LENGTH (ys7:data_v list) + 1)) s)) (s1:(A,C,FFI)wl_state)
       NONE locs`
     ASSUME_TAC THENL
    [MATCH_MP_TAC state_rel_cut_IMP THEN
     EXISTS_TAC `data_state_locals_fupd (K (xa:data_v spt))
                   (data_state_space_fupd (K (LENGTH (ys7:data_v list) + 1)) (s:(C,FFI)data_state))` THEN
     EXISTS_TAC `SOME (kept:1 spt)` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_state_INFO.ri_accfupds; K_THM] THEN
     CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
     REWRITE_TAC[data_state_INFO.ri_fupdfupds; K_o_THM];
     ALL_TAC]) THEN (ASP6AUX_QR_TAC THEN REWRITE_TAC[ASP6AUX_fupd_set_var] THEN
   MATCH_MP_TAC ASP6AUX_state_rel_final2 THEN
   MAP_EVERY EXISTS_TAC
    [`data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state))
        (kept:1 spt)))) (data_state_space_fupd (K (LENGTH (ys7:data_v list) + 1)) s)`;
     `s1:(A,C,FFI)wl_state`] THEN
   ASM_SIMP_TAC[ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; wl_state_INFO.ri_accfupds;
               data_state_INFO.ri_accfupds; K_THM; ASP6AUX_DO_STACK_FIELDS;
               ASP6AUX_do_stack_stack_max; check_lim_def;
               FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"; MEM;
               FAPPLY_FUPDATE_THM; inter_insert_ODD_adjust_set_alt; lookup_insert;
               adjust_var_NEQ; adjust_var_eq_numeral; ARITH; IS_SOME_DEF; THE_DEF]) THEN (CONJ_TAC THENL
    [FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP ASP6AUX_state_rel_facts (check (fun th ->
       asp6_is_app "data_to_word_gcProof_state_rel" (concl th) &&
       can (find_term ((=) `s1:(A,C,FFI)wl_state`)) (concl th)) th))) THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!k (v:data_v). lookup k (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state))
                   (kept:1 spt))) = SOME v ==> lookup k (xa:data_v spt) = SOME v`
     ASSUME_TAC THENL
    [UNDISCH_TAC `data_cut_env kept (xa:data_v spt) =
                  SOME (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) kept))` THEN
     REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
     REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN MESON_TAC[option_DISTINCT];
     ALL_TAC] THEN
   SUBGOAL_THEN `memory_rel c (wl_state_be s1) ts (data_state_refs s) (LENGTH (ys7:data_v list) + 1)
       (wl_state_store s1) m1 (wl_state_mdomain (s1:(A,C,FFI)wl_state))
       (APPEND (ZIP ys7 ws1)
         (APPEND (join_env (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (kept:1 spt)))
           (toAList (sptree_inter (wl_state_locals s1)
             (adjust_set (mk_wf (sptree_inter (data_state_locals s) kept))))))
         (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store s1) Globals)]
           (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack s1)))))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC memory_rel_store_list_to_unused THEN
     MAP_EVERY EXISTS_TAC [
       `CONS (wl_Word (word_or (word_shl (word (4 * LENGTH (ys7:data_v list)))
          (dimindex (:A) - data_to_word_config_len_size c - 2)) a)) (ws1:(A word_loc)list)`;
       `wl_state_memory (s1:(A,C,FFI)wl_state)`; `nfree:A word`] THEN
     ASM_REWRITE_TAC[LENGTH; ADD1; LE_REFL] THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o check (fun th ->
       asp6_is_app "memory_rel" (concl th) && can (find_term ((=) `w_ptr:A word`)) (concl th))) THEN
     REWRITE_TAC[THE_DEF] THEN
     MATCH_MP_TAC memory_rel_rearrange THEN REWRITE_TAC[MEM_APPEND] THEN
     X_GEN_TAC `p:data_v#A word_loc` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     DISJ2_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC join_env_submap_MEM THEN
     MAP_EVERY EXISTS_TAC [`mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (kept:1 spt))`;
                           `wl_state_locals (s1:(A,C,FFI)wl_state)`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN (MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (s1:(A,C,FFI)wl_state)`; `ts:num`;
     `data_state_refs (s:(C,FFI)data_state)`; `LENGTH (ys7:data_v list) + 1`;
     `wl_state_store (s1:(A,C,FFI)wl_state)`; `m1:A word->A word_loc`;
     `wl_state_mdomain (s1:(A,C,FFI)wl_state)`; `ys7:data_v list`; `ws1:(A word_loc)list`;
     `APPEND (join_env (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (kept:1 spt)))
           (toAList (sptree_inter (wl_state_locals (s1:(A,C,FFI)wl_state))
             (adjust_set (mk_wf (sptree_inter (data_state_locals s) kept))))))
         (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store s1) Globals)]
           (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack s1)))`;
     `tag:num`;
     `word_or (word_shl (word (4 * LENGTH (ys7:data_v list)))
          (dimindex (:A) - data_to_word_config_len_size c - 2)) (a:A word)`]
     memory_rel_Cons_alt) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`; GSYM LENGTH_EQ_NIL] THEN
     MATCH_MP_TAC ASP6AUX_full_header THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `LENGTH (ys7:data_v list) < MIN (2 EXP data_to_word_config_len_size c)
                    (dimword (:A) DIV 16)` THEN
     REWRITE_TAC[MIN; dimword_def] THEN
     SUBGOAL_THEN `2 EXP dimindex (:A) DIV 16 = 2 EXP (dimindex (:A) - 4)` SUBST1_TAC THENL
      [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
       ALL_TAC] THEN
     COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr':A word` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `free:A word = nfree /\ curr':A word = curr` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
    [CONJ_TAC THENL
      [UNDISCH_TAC `FLOOKUP (wl_state_store (s1:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word free)`;
       UNDISCH_TAC `FLOOKUP (wl_state_store (s1:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr')`] THEN
     ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
     asp6_is_app "memory_rel" (rand (concl th)))) THEN
   ANTS_TAC THENL
    [MATCH_MP_TAC STAR_fun2set_IMP_SEP_T THEN
     FIRST_ASSUM(fun th0 -> if asp6_is_app "STAR" (rator (concl th0)) then
       let th = REWRITE_RULE[GSYM STAR_ASSOC] th0 in
       EXISTS_TAC (rand (rator (concl th))) THEN ACCEPT_TAC th else NO_TAC);
     ALL_TAC] THEN
   ASM_SIMP_TAC[SUB_REFL; ASP6AUX_biw_mul_succ]); (SUBGOAL_THEN `~(word_and (word (4 * len)) (word (4 * len)) = word 0:A word)`
     (fun th -> REWRITE_TAC[asm_word_cmp_def; th]) THENL
    [REWRITE_TAC[WORD_AND_REFL] THEN DISCH_THEN(MP_TAC o AP_TERM `val:A word->num`) THEN
     SUBGOAL_THEN `4 * len < dimword (:A)` ASSUME_TAC THENL
      [UNDISCH_TAC `4 * (LENGTH (ys7:data_v list) + len) < dimword (:A)` THEN ARITH_TAC;
       ALL_TAC] THEN
     ASM_SIMP_TAC[VAL_WORD_EQ; VAL_WORD_0; GSYM dimword_def] THEN
     UNDISCH_TAC `~(len = 0)` THEN ARITH_TAC;
     ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                                   (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
   ASP6AUX_C2_STUB_TAC `lookup MemCopy_location (wl_state_code (t:(A,C,FFI)wl_state)) =
                        SOME (5,MemCopy_code)` THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_evaluate_clock o
     check (fun th -> try asp6_is_app "wl_evaluate" (lhs (concl th)) &&
                          rand (lhs (concl th)) = `wl_state_code (s1:(A,C,FFI)wl_state)` = false
                      with Failure _ -> false) o
     check (fun th -> try let p = fst (dest_pair (rand (lhs (concl th)))) in
                          asp6_is_app "AllocVar" p with Failure _ -> false)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASP6AUX_set_var_fields]) THEN
   ALL_TAC) THEN (SUBGOAL_THEN `data_cut_env kept (xa:data_v spt) =
                 SOME (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) kept))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC cut_env_cut_env_list_insert THEN
     MAP_EVERY EXISTS_TAC [`CONS (a1:num) (CONS a2 (CONS a3 (CONS a4 (t7:num list))))`;
                           `data_state_locals (s:(C,FFI)data_state)`] THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "data_cut_env" (lhs (concl th)) &&
       rand (rator (lhs (concl th))) = `kept:1 spt` with Failure _ -> false)) THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC]) THEN (W(fun (asl,w) ->
     let srth = snd (find (fun (_,th) -> let tm = concl th in
        asp6_is_app "data_to_word_gcProof_state_rel" tm &&
        rand (rator (rator tm)) = `s1:(A,C,FFI)wl_state` &&
        can (find_term ((=) `xa:data_v spt`)) tm) asl) in
     let sx = rand (rator (rator (rator (concl srth)))) in
     let ctm = vsubst [sx,`sx0:(C,FFI)data_state`]
       `data_cut_state_opt (SOME (kept:1 spt)) (sx0:(C,FFI)data_state) =
        SOME (data_state_locals_fupd
          (K (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) kept))) sx0)` in
     let gtm = vsubst [sx,`sx0:(C,FFI)data_state`]
       `data_get_vars (CONS a1 (CONS a2 (CONS a3 (CONS a4 t7))))
          (data_state_locals (sx0:(C,FFI)data_state)) =
        SOME (CONS (data_Block bts btag xs') (CONS (data_Number (&startptr))
          (CONS (data_Number (&len))
          (CONS (data_Number (&(LENGTH (ys7:data_v list) + len))) ys7))))` in
     SUBGOAL_THEN ctm ASSUME_TAC THENL
      [REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_state_INFO.ri_accfupds;
                   K_THM] THEN
       CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
       ALL_TAC] THEN
     SUBGOAL_THEN gtm ASSUME_TAC THENL
      [REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MP_TAC(MATCH_MP state_rel_cut_state_opt_SOME
       (end_itlist CONJ [srth; ASSUME gtm; ASSUME ctm]))) THEN
   DISCH_THEN(X_CHOOSE_THEN `yy:(A word_loc)spt` (X_CHOOSE_THEN `wss:(A word_loc)list`
     STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
     STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs o
     check (fun th -> try asp6_is_app "wl_cut_env" (lhs (concl th)) &&
       rand (lhs (concl th)) = `wl_state_locals (s1:(A,C,FFI)wl_state)` with Failure _ -> false)) THEN
   MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (s1:(A,C,FFI)wl_state))`
     PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `q:(num#A word_loc)list` (X_CHOOSE_THEN `perm:num->num->num`
     ASSUME_TAC))) THEN (SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!k (v:data_v). lookup k (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state))
                   (kept:1 spt))) = SOME v ==> lookup k (xa:data_v spt) = SOME v`
     ASSUME_TAC THENL
    [UNDISCH_TAC `data_cut_env kept (xa:data_v spt) =
                  SOME (mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) kept))` THEN
     REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
     REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN MESON_TAC[option_DISTINCT];
     ALL_TAC] THEN
   SUBGOAL_THEN `memory_rel c (wl_state_be s1) ts (data_state_refs s)
       ((LENGTH (ys7:data_v list) + len) + 1)
       (wl_state_store s1) m1 (wl_state_mdomain (s1:(A,C,FFI)wl_state))
       (CONS (data_Block bts btag xs',wl_Word w_ptr)
       (APPEND (ZIP ys7 ws1)
         (APPEND (join_env (xa:data_v spt)
           (toAList (sptree_inter (wl_state_locals s1) (adjust_set xa))))
         (APPEND [(the_global (data_state_global (s:(C,FFI)data_state)),
                   FAPPLY (wl_state_store s1) Globals)]
           (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack s1))))))`
     ASSUME_TAC THENL
    [MATCH_MP_TAC memory_rel_store_list_to_unused THEN
     MAP_EVERY EXISTS_TAC [
       `CONS (wl_Word (word_or (word_shl (word (4 * (LENGTH (ys7:data_v list) + len)))
          (dimindex (:A) - data_to_word_config_len_size c - 2)) a)) (ws1:(A word_loc)list)`;
       `wl_state_memory (s1:(A,C,FFI)wl_state)`; `nfree:A word`] THEN
     ASM_REWRITE_TAC[LENGTH; ADD1] THEN
     CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
     FIRST_ASSUM(MP_TAC o check (fun th ->
       asp6_is_app "memory_rel" (concl th) && can (find_term ((=) `w_ptr:A word`)) (concl th))) THEN
     REWRITE_TAC[THE_DEF];
     ALL_TAC]) THEN (MP_TAC(ISPECL [`len:num`; `startptr:num`; `m1:A word->A word_loc`; `ws1:(A word_loc)list`;
     `ys7:data_v list`; `len:num`; `c:data_to_word_config`; `s1:(A,C,FFI)wl_state`; `ts:num`;
     `s:(C,FFI)data_state`; `(LENGTH (ys7:data_v list) + len) + 1`; `bts:num`; `btag:num`;
     `xs':data_v list`; `w_ptr:A word`;
     `APPEND (join_env (xa:data_v spt)
           (toAList (sptree_inter (wl_state_locals (s1:(A,C,FFI)wl_state)) (adjust_set xa))))
         (APPEND [(the_global (data_state_global (s:(C,FFI)data_state)),
                   FAPPLY (wl_state_store s1) Globals)]
           (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack s1)))`;
     `nfree:A word`;
     `word_or (word_shl (word (4 * (LENGTH (ys7:data_v list) + len)))
          (dimindex (:A) - data_to_word_config_len_size c - 2)) (a:A word)`;
     `other:(A word#A word_loc->bool)->bool`; `a1:num`; `wx:A word`] IMP_memcopy) THEN
   SUBGOAL_THEN `((LENGTH (ys7:data_v list) + len) + 1) - (LENGTH ys7 + 1) = len`
     ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   ANTS_TAC THENL
    [FIRST_ASSUM(let qtm = `LENGTH (ws1:(A word_loc)list) = LENGTH (ys7:data_v list)` in fun eqth -> if concl eqth = qtm
       then RULE_ASSUM_TAC(fun th -> if th == eqth then th else REWRITE_RULE[eqth] th) THEN
            REWRITE_TAC[eqth] else NO_TAC) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ADD1;
       ASSUME `((LENGTH (ys7:data_v list) + len) + 1) - (LENGTH ys7 + 1) = len`]) THEN
     ASM_REWRITE_TAC[ADD1; LE_REFL] THEN ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `m2:A word->A word_loc` (X_CHOOSE_THEN `ws2:(A word_loc)list`
     STRIP_ASSUME_TAC))) THEN (ASP6AUX_C2_EVAL_TAC (asp6c2_eval_rws @ asp6c2_eval_rws2 @ asp6c2_call_rws @
    [domain_adjust_sets; ALL_DISTINCT; MEM; adjust_var_NEQ; adjust_var_11;
     MustTerminate_limit_NOT_0; wl_push_env_def; LET_DEF; LET_END_DEF;
     ASP6AUX_set_var_fields; ASP6AUX_set_store_fields] @
    map ASP2AUX_cut_envs_ins [1;3;5;7;9;11;13;15])) THEN (SUBGOAL_THEN `LENGTH (t7:num list) = LENGTH (ws1:(A word_loc)list) /\ 4 * len < dimword (:A) /\
                 len < MustTerminate_limit (:A) - 1`
     STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THENL
      [FIRST_ASSUM(MP_TAC o MATCH_MP get_vars_IMP_LENGTH_word o check (fun th ->
         try asp6_is_app "wl_get_vars" (lhs (concl th)) &&
             rand (lhs (concl th)) = `s1:(A,C,FFI)wl_state` &&
             rand (rator (lhs (concl th))) = `MAP adjust_var (t7:num list)`
         with Failure _ -> false)) THEN REWRITE_TAC[LENGTH_MAP];
       UNDISCH_TAC `4 * (LENGTH (ys7:data_v list) + len) < dimword (:A)` THEN ARITH_TAC;
       MP_TAC(ISPEC `word len:A word` ASP2AUX_val_lt_MustTerminate_limit) THEN
       SUBGOAL_THEN `len < 2 EXP dimindex (:A)` (fun th -> SIMP_TAC[th; VAL_WORD_EQ]) THEN
       REWRITE_TAC[GSYM dimword_def] THEN
       UNDISCH_TAC `4 * (LENGTH (ys7:data_v list) + len) < dimword (:A)` THEN ARITH_TAC];
     ALL_TAC] THEN
   SUBGOAL_THEN `memcopy len
       (word_add wx (word_add bytes_in_word (word_shl (word (4 * startptr))
          (backend_common_word_shift (:A) - 2))))
       (word_add nfree (word_mul bytes_in_word (word (LENGTH (t7:num list) + 1)))) m1
       (wl_state_mdomain (s1:(A,C,FFI)wl_state)) = SOME (m2:A word->A word_loc)`
     ASSUME_TAC THENL
    [REWRITE_TAC[MATCH_MP ASP6AUX_startptr_addr (ASSUME `good_dimindex (:A)`)] THEN
     REWRITE_TAC[WORD_ADD_ASSOC] THEN
     FIRST_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "memcopy" (lhs (concl th))
                                          with Failure _ -> false)) THEN
     REWRITE_TAC[ASSUME `LENGTH (t7:num list) = LENGTH (ws1:(A word_loc)list)`];
     ALL_TAC] THEN
   ASP6AUX_C2_EVAL_LEMMA_TAC `MemCopy_code:(A)wl_prog` (fun st ->
     ISPECL [`make_cons_ptr c (word_sub nfree curr) tag (LENGTH (ys7:data_v list) + len):A word_loc`;
       `n:num`; `l:num`; `len:num`;
       `word_add wx (word_add bytes_in_word (word_shl (word (4 * startptr))
          (backend_common_word_shift (:A) - 2))):A word`;
       `word_add nfree (word_mul bytes_in_word (word (LENGTH (t7:num list) + 1))):A word`;
       st; `m1:A word->A word_loc`; `wl_state_mdomain (s1:(A,C,FFI)wl_state)`;
       `m2:A word->A word_loc`] MemCopy_thm) THEN
   ANTS_TAC THENL
    [ASP2AUX_CRW_TAC (asp6c2_eval_rws @ asp6c2_eval_rws2 @ asp6c2_call_rws @
       [ASP6AUX_set_var_fields; ASP6AUX_set_store_fields]) THEN
     CONV_TAC(DEPTH_CONV ASP2AUX_LOOKUP_FROMLIST2_CONV) THEN ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[LT_IMP_LE];
     ALL_TAC]) THEN (DISCH_THEN(X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC) THEN
   ASP2AUX_CRW_TAC (asp6c2_eval_rws @ asp6c2_eval_rws2 @ asp6c2_call_rws @
      [push_env_store; wl_push_env_def; wl_pop_env_def; wl_fix_clock_def;
       wl_set_vars_def; alist_insert_def; LET_DEF; LET_END_DEF; LENGTH;
       wl_bad_fun_return_def; ASP6AUX_set_var_fields; ASP6AUX_set_store_fields]) THEN
   SUBGOAL_THEN `domain (sptree_union (fromAList (q:(num#A word_loc)list))
                  (fromAList (toAList (y1:(A word_loc)spt)))) =
                domain y1 UNION domain (y2:(A word_loc)spt)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[domain_union; domain_fromAList_toAList] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP env_to_list_domain) THEN SET_TAC[];
    ALL_TAC] THEN
   ASP2AUX_CRW_TAC [option_DISTINCT; injectivity "wl_result"]) THEN (ASP2AUX_EXISTS_PAIR_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
   REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
   REWRITE_TAC[data_set_var_def; check_lim_def; data_state_INFO.ri_accfupds; K_THM;
               ASP6AUX_DO_STACK_FIELDS; wl_state_INFO.ri_accfupds; ASP6AUX_set_var_fields;
               ASP6AUX_set_store_fields; THE_DEF; IS_SOME_DEF] THEN
   CASE_REWRITE_TAC[APPEND] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm;
       data_state_INFO.ri_accfupds; K_THM; ALL] o
     check (fun th -> asp6_is_app "data_to_word_gcProof_state_rel" (concl th) &&
       rand (rator (rator (concl th))) = `s1:(A,C,FFI)wl_state` &&
       can (find_term ((=) `xa:data_v spt`)) (concl th))) THEN
   ASM_REWRITE_TAC[code_oracle_rel_NextFree; FDOM_FUPDATE; IN_INSERT; ALL; FLOOKUP_UPDATE;
                   distinctness "store_name"] THEN
   REPEAT CONJ_TAC THENL
    [ASP6AUX_C2_DRULE_N 3 ASP2AUX_cut_ret_lookup_0 THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
     ASP6AUX_C2_DRULE_N 3 ASP2AUX_cut_ret_IS_SOME THEN DISCH_THEN MATCH_ACCEPT_TAC;
     FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_stack_max_le o check (fun th ->
       try fst (dest_pair (rand (lhs (concl th)))) = `MemCopy_code:(A)wl_prog`
       with Failure _ -> false)) THEN
     REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; stack_size_eq] THEN
     FIRST_ASSUM(MP_TAC o check (fun th -> asp6_is_app "option_le" (concl th) &&
       rand (concl th) = `wl_state_stack_max (s1:(A,C,FFI)wl_state)`)) THEN
     REWRITE_TAC[ASSUME `wl_state_locals_size (s1:(A,C,FFI)wl_state) =
                         data_state_locals_size (s:(C,FFI)data_state)`;
                 ASSUME `wl_state_stack_size (s1:(A,C,FFI)wl_state) =
                         data_state_stack_frame_sizes (s:(C,FFI)data_state)`] THEN
     ASP2AUX_OPTION_ARITH_TAC;
     FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_rel_IMP_size_of_stack o check (fun th ->
       asp6_is_app "ALL2" (concl th) &&
       rand (concl th) = `wl_state_stack (s1:(A,C,FFI)wl_state)`)) THEN
     REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "option_le" (concl th) &&
       free_in `smx:num option` (concl th)))) THEN
     UNDISCH_TAC `option_le (wl_state_stack_max (s1:(A,C,FFI)wl_state))
                    (data_state_stack_max (s:(C,FFI)data_state))` THEN
     REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds; K_THM;
                     stack_size_eq; stack_consumed_def; ASP6AUX_set_store_fields] THEN
     ASP2AUX_OPTION_ARITH_TAC;
     ALL_TAC]) THEN (REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
   SUBGOAL_THEN `LENGTH (APPEND (ws1:(A word_loc)list) ws2) = LENGTH (ys7:data_v list) + len /\
                 LENGTH (APPEND ys7 (TAKE len (DROP startptr (xs':data_v list)))) =
                   LENGTH ys7 + len`
     STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TAKE; LENGTH_DROP;
                  ARITH_RULE `a + b <= c ==> b <= c - a`];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (s1:(A,C,FFI)wl_state)`; `ts:num`;
     `data_state_refs (s:(C,FFI)data_state)`; `(LENGTH (ys7:data_v list) + len) + 1`;
     `wl_state_store (s1:(A,C,FFI)wl_state)`; `m2:A word->A word_loc`;
     `wl_state_mdomain (s1:(A,C,FFI)wl_state)`;
     `APPEND ys7 (TAKE len (DROP startptr (xs':data_v list)))`;
     `APPEND (ws1:(A word_loc)list) ws2`;
     `APPEND (join_env (xa:data_v spt)
           (toAList (sptree_inter (wl_state_locals (s1:(A,C,FFI)wl_state)) (adjust_set xa))))
         (APPEND [(the_global (data_state_global (s:(C,FFI)data_state)),
                   FAPPLY (wl_state_store s1) Globals)]
           (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack s1)))`;
     `tag:num`;
     `word_or (word_shl (word (4 * (LENGTH (ys7:data_v list) + len)))
          (dimindex (:A) - data_to_word_config_len_size c - 2)) (a:A word)`]
     memory_rel_Cons_alt) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`; GSYM LENGTH_EQ_NIL] THEN
     MATCH_MP_TAC ASP6AUX_full_header THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `LENGTH (ys7:data_v list) + len < MIN (2 EXP data_to_word_config_len_size c)
                    (dimword (:A) DIV 16)` THEN
     REWRITE_TAC[MIN; dimword_def] THEN
     SUBGOAL_THEN `2 EXP dimindex (:A) DIV 16 = 2 EXP (dimindex (:A) - 4)` SUBST1_TAC THENL
      [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
       ALL_TAC] THEN
     COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr':A word` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `free:A word = nfree /\ curr':A word = curr` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
    [CONJ_TAC THENL
      [UNDISCH_TAC `FLOOKUP (wl_state_store (s1:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word free)`;
       UNDISCH_TAC `FLOOKUP (wl_state_store (s1:(A,C,FFI)wl_state)) CurrHeap = SOME (wl_Word curr')`] THEN
     ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
     asp6_is_app "memory_rel" (rand (concl th)))) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[SUB_REFL; MATCH_MP ASP6AUX_biw_mul_succ (ASSUME `good_dimindex (:A)`)] THEN
   DISCH_TAC THEN MATCH_MP_TAC ASP2AUX_memory_rel_cut_ret THEN
   MAP_EVERY EXISTS_TAC
    [`APPEND (join_env (xa:data_v spt)
           (toAList (sptree_inter (wl_state_locals (s1:(A,C,FFI)wl_state)) (adjust_set xa))))
         (APPEND [(the_global (data_state_global (s:(C,FFI)data_state)),
                   FAPPLY (wl_state_store s1) Globals)]
           (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack s1)))`;
     `kept:1 spt`; `xa:data_v spt`; `wl_state_locals (s1:(A,C,FFI)wl_state)`;
     `y2:(A word_loc)spt`; `wl_state_permute (s1:(A,C,FFI)wl_state)`; `perm:num->num->num`] THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[])]]]]);;

let ASP6AUX_do_app_Cons_nil = prove
 (`!tag (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (clos_Cons tag)) [] s = Rval (v,s2) <=>
     v = data_Block 0 tag [] /\
     s2 = do_stack (BlockOp (clos_Cons tag)) [] (do_lim_safe s (BlockOp (clos_Cons tag)) [])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; op_space_req_def; MEM;
     LENGTH; distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op"] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN MESON_TAC[]);;

let ASP6AUX_do_app_Cons = prove
 (`!tag vs (s:(C,FFI)data_state) v s2 ts.
     data_do_app (BlockOp (clos_Cons tag)) vs s = Rval (v,s2) /\ ~(vs = []) /\
     data_state_tstamps s = SOME ts ==>
     LENGTH vs + 1 <= data_state_space s /\ v = data_Block ts tag vs /\
     s2 = check_lim (data_state_tstamps_fupd (K (SOME (ts + 1)))
            (do_stack (BlockOp (clos_Cons tag)) vs
              (do_lim_safe (data_state_space_fupd
                              (K (data_state_space s - (LENGTH vs + 1))) s)
                 (BlockOp (clos_Cons tag)) vs))) (LENGTH vs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `data_do_app (BlockOp (clos_Cons tag)) vs (s:(C,FFI)data_state) = Rval (v,s2)` THEN
  ASM_REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; op_space_req_def; MEM;
     LENGTH_EQ_NIL; distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op";
     ARITH_RULE `~(n + 1 = 0)`] THEN
  REWRITE_TAC[consume_space_def] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[distinctness "result"] THEN
  REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[with_fresh_ts_def; ASP6AUX_DO_STACK_FIELDS; data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 16150 *)
let assign_Cons = prove
 ((assign_thm_stmt `(?tag. op = BlockOp (clos_Cons tag))`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `tag:num` SUBST_ALL_TAC)) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
   REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_Cons_def] THEN
   ASM_CASES_TAC `args:num list = []` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[get_vars_SOME_IFF_data_eq]) THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `vals:data_v list = []` o concl)) THEN
     FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ASP6AUX_do_app_Cons_nil] o
       check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                        with Failure _ -> false)) THEN
     RVEQ_TAC THEN REWRITE_TAC[LENGTH] THEN COND_CASES_TAC THENL
      [REWRITE_TAC[FST] THEN ASP6AUX_EV_TAC [word_exp_rw] THEN ASP6AUX_FINISH_TAC THEN
       REWRITE_TAC[ARITH_RULE `16 * tag + 2 = 2 + 16 * tag`] THEN
       SUBGOAL_THEN `word (2 + 16 * tag):A word = BlockNil tag` SUBST1_TAC THENL
        [REWRITE_TAC[BlockNil_def; WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
         REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE;
         ALL_TAC] THEN
       MATCH_MP_TAC memory_rel_Cons_empty THEN ASM_REWRITE_TAC[] THEN
       FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN REWRITE_TAC[];
       ALL_TAC];
     ALL_TAC]) THENL
   [(REWRITE_TAC[FST] THEN
   ASP6AUX_GIVEUP_TAC (REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS])
    (DISCH_THEN(K ALL_TAC) THEN
     DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe) THEN
     REWRITE_TAC[lim_safe_def] THEN
     FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
       check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
     ASM_REWRITE_TAC[GSYM dimword_def]));
    (SUBGOAL_THEN `~(vals:data_v list = [])` ASSUME_TAC THENL
    [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(args:num list = [])` THEN
     ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH];
     ALL_TAC] THEN
   FIRST_ASSUM(X_CHOOSE_TAC `ts:num` o REWRITE_RULE[IS_SOME_EXISTS] o
     check ((=) `IS_SOME (data_state_tstamps (s:(C,FFI)data_state))` o concl)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_Cons o
     (fun th -> CONJ th (CONJ (ASSUME `~(vals:data_v list = [])`)
        (ASSUME `data_state_tstamps (s:(C,FFI)data_state) = SOME ts`))) o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                      with Failure _ -> false)) THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                  `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `args:num list`;
                  `vals:data_v list`] ASP4AUX_state_rel_get_vars) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
   CASES_ON `encode_header c (4 * tag) (LENGTH (vals:data_v list)):(A word)option` THEN
   CASE_REWRITE_TAC[]) THENL
     [(REWRITE_TAC[FST] THEN
   ASP6AUX_GIVEUP_TAC
    (REWRITE_TAC[check_lim_def; data_state_INFO.ri_accfupds; K_THM] THEN
     MATCH_MP_TAC ASP6AUX_do_stack_stack_max THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM])
    (DISCH_THEN(K ALL_TAC) THEN
     REWRITE_TAC[check_lim_def; data_state_INFO.ri_accfupds; K_THM] THEN
     DISCH_THEN(MP_TAC o MATCH_MP ASP6AUX_do_stack_safe o CONJUNCT2) THEN
     ASM_REWRITE_TAC[lim_safe_def; data_state_INFO.ri_accfupds; K_THM] THEN
     FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
       check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
     ASM_REWRITE_TAC[GSYM dimword_def] THEN
     UNDISCH_TAC `encode_header c (4 * tag) (LENGTH (vals:data_v list)) = (NONE:(A word)option)` THEN
     REWRITE_TAC[ASP6AUX_encode_header_NONE] THEN
     REPEAT(POP_ASSUM(K ALL_TAC)) THEN ARITH_TAC));
      (FIRST_ASSUM(MP_TAC o SPECL [`tag:num`; `a:A word`] o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Cons1) o check (asp6_asm_app "memory_rel")) THEN
   ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr:A word`
     (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
   REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                   ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; FLOOKUP_UPDATE]) THEN
      (BIGPAUX_MATCH_ABBREV_TAC `wl_evaluate (StoreEach 1 (CONS 3 (MAP adjust_var args)) (word 0),
      t5:(A,C,FFI)wl_state)` `t5:(A,C,FFI)wl_state` THEN
   SUBGOAL_THEN `wl_get_vars (MAP adjust_var args) (t5:(A,C,FFI)wl_state) = SOME ws`
     ASSUME_TAC THENL
    [EXPAND_TAC "t5" THEN
     W(fun (asl,w) -> MP_TAC (ISPECL [`args:num list`; rand(lhs w); `t:(A,C,FFI)wl_state`]
        ASP6AUX_get_vars_adjust_var_eq)) THEN
     REWRITE_TAC[ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; lookup_insert;
                 adjust_var_NEQ] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `wl_evaluate (StoreEach 1 (CONS 3 (MAP adjust_var args)) (word 0),
                   t5:(A,C,FFI)wl_state) = (NONE,wl_state_memory_fupd (K m1) t5)`
     SUBST1_TAC THENL
    [MATCH_MP_TAC evaluate_StoreEach THEN
     MAP_EVERY EXISTS_TAC [`CONS (wl_Word a) (ws:(A word_loc)list)`; `free:A word`] THEN
     ASM_REWRITE_TAC[wl_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
     EXPAND_TAC "t5" THEN
     REWRITE_TAC[ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; wl_get_var_def;
                 lookup_insert; ARITH_RULE `~(3 = 1)`] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_shift_amount o
     check ((=) `shift_length c < dimindex (:A)` o concl)) THEN
   CASE_REWRITE_TAC[] THEN
   ASP3AUX_UNABBREV_TAC `t5:(A,C,FFI)wl_state` THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_mem_load_def; ITLIST; OPTION_MAP_DEF; WORD_ADD_0;
                   WORD_OR_0; ASP6AUX_set_var_fields; ASP6AUX_set_store_fields;
                   FLOOKUP_UPDATE]) THEN
      (ASP6AUX_FINISH_TAC) THEN
      (REWRITE_TAC[IS_SOME_DEF; THE_DEF] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "memory_rel" (concl th) &&
     can (find_term ((=) `make_cons_ptr:data_to_word_config->A word->num->num->A word_loc`))
       (concl th))) THEN
   ASM_REWRITE_TAC[make_cons_ptr_def; get_lowerbits_def] THEN
   SUBGOAL_THEN `!b:A word. word_or (word 1) (word_or b (word 1)) = word_or (word 1) b`
     (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
   REWRITE_TAC[THE_DEF])]]);;

let ASP6AUX_do_app_FFI = prove
 (`!n vs (x:(C,FFI)data_state) v s2.
     data_do_app (clos_FFI n) vs x = Rval (v,s2) ==>
     ?b1 cptr b2 ptr cws ws ffi' ws'.
       vs = [data_RefPtr b1 cptr; data_RefPtr b2 ptr] /\
       lookup cptr (data_state_refs x) = SOME (bvl_ByteArray T cws) /\
       lookup ptr (data_state_refs x) = SOME (bvl_ByteArray F ws) /\
       call_FFI (data_state_ffi x) (ExtCall n) cws ws = FFI_return ffi' ws' /\
       v = data_Unit /\
       s2 = data_state_refs_fupd (K (insert ptr (bvl_ByteArray F ws') (data_state_refs x)))
              (data_state_ffi_fupd (K ffi')
                (do_stack (clos_FFI n) vs (do_lim_safe
                  (data_state_space_fupd (K 0)
                    (data_state_safe_for_space_fupd
                      (K (data_state_safe_for_space x /\ no_thunks_in_refs (data_state_refs x) /\
                          size_of_heap_args vs x + space_consumed x (clos_FFI n) vs <=
                          limits_heap_limit (data_state_limits x)))
                      (data_state_peak_heap_length_fupd
                        (K (MAX (data_state_peak_heap_length x)
                                (size_of_heap_args vs x + space_consumed x (clos_FFI n) vs)))
                        x))) (clos_FFI n) vs)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; MEM;
     distinctness "clos_op"; injectivity "clos_op"] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS; data_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; case_eq "option"; case_eq "bvl_ref";
              case_eq "ffi_result"; COND_CASE_EQ; distinctness "result"; injectivity "result";
              PAIR_EQ; pair_case_eq] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;


let ASP6AUX_byte_header_len = prove
 (`!c (h:A word) L.
     good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
     (if dimindex (:A) = 32
      then L + 4 < 2 EXP (dimindex (:A) - 3) /\
           word_ushr h (dimindex (:A) - data_to_word_config_len_size c - 2) = word (L + 4)
      else L + 8 < 2 EXP (dimindex (:A) - 3) /\
           word_ushr h (dimindex (:A) - data_to_word_config_len_size c - 3) = word (L + 8)) ==>
     word_sub (word_ushr h ((dimindex (:A) - backend_common_word_shift (:A)) -
                            data_to_word_config_len_size c)) bytes_in_word = word L /\
     val (word L:A word) = L /\
     val (word ((dimindex (:A) - backend_common_word_shift (:A)) -
                data_to_word_config_len_size c):A word) =
       (dimindex (:A) - backend_common_word_shift (:A)) - data_to_word_config_len_size c /\
     ~((dimindex (:A) - backend_common_word_shift (:A)) - data_to_word_config_len_size c >=
       dimindex (:A))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[backend_common_word_shift_def; bytes_in_word_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THENL
   [SUBGOAL_THEN `30 - data_to_word_config_len_size c = (32 - data_to_word_config_len_size c) - 2`
      SUBST1_TAC THENL [ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `61 - data_to_word_config_len_size c = (64 - data_to_word_config_len_size c) - 3`
      SUBST1_TAC THENL [ARITH_TAC; ALL_TAC]] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
  (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MOD_LT) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let ASP6AUX_state_rel_ffi_upd = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs f.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_ffi_fupd (K f) s)
       (wl_state_ffi_fupd (K f) t) v locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* the end of an assign proof that changes the ffi state on both sides     *)
let ASP6AUX_state_rel_final_ffi = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w
    (s2:(C,FFI)data_state) (t1:(A,C,FFI)wl_state).
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_state_clock s2 = data_state_clock s /\
     data_state_handler s2 = data_state_handler s /\
     data_state_code s2 = data_state_code s /\
     data_state_compile s2 = data_state_compile s /\
     data_state_compile_oracle s2 = data_state_compile_oracle s /\
     data_state_locals s2 = data_state_locals s /\
     data_state_stack s2 = data_state_stack s /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes s /\
     data_state_locals_size s2 = data_state_locals_size s /\
     data_state_limits s2 = data_state_limits s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     sptree_inter (wl_state_locals t1) (adjust_set (data_state_locals s)) =
       sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)) /\
     lookup 0 (wl_state_locals t1) = lookup 0 (wl_state_locals t) /\
     (!n. IS_SOME (lookup (adjust_var n) (wl_state_locals t)) ==>
          IS_SOME (lookup (adjust_var n) (wl_state_locals t1))) /\
     wl_state_ffi t1 = data_state_ffi s2 /\
     wl_state_clock t1 = wl_state_clock t /\
     wl_state_handler t1 = wl_state_handler t /\
     wl_state_gc_fun t1 = wl_state_gc_fun t /\
     wl_state_code t1 = wl_state_code t /\
     wl_state_compile t1 = wl_state_compile t /\
     wl_state_compile_oracle t1 = wl_state_compile_oracle t /\
     wl_state_code_buffer t1 = wl_state_code_buffer t /\
     wl_state_data_buffer t1 = wl_state_data_buffer t /\
     wl_state_stack t1 = wl_state_stack t /\
     wl_state_stack_size t1 = wl_state_stack_size t /\
     wl_state_locals_size t1 = wl_state_locals_size t /\
     wl_state_stack_limit t1 = wl_state_stack_limit t /\
     wl_state_stack_max t1 = wl_state_stack_max t /\
     wl_state_be t1 = wl_state_be t /\
     wl_state_mdomain t1 = wl_state_mdomain t /\
     FLOOKUP (wl_state_store t1) CodeBuffer = FLOOKUP (wl_state_store t) CodeBuffer /\
     FLOOKUP (wl_state_store t1) CodeBufferEnd = FLOOKUP (wl_state_store t) CodeBufferEnd /\
     FLOOKUP (wl_state_store t1) BitmapBuffer = FLOOKUP (wl_state_store t) BitmapBuffer /\
     FLOOKUP (wl_state_store t1) BitmapBufferEnd =
       FLOOKUP (wl_state_store t) BitmapBufferEnd /\
     FLOOKUP (wl_state_store t1) HeapLength = FLOOKUP (wl_state_store t) HeapLength /\
     Globals IN FDOM (wl_state_store t1) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s2) (wl_state_store t1) (wl_state_memory t1) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s2),FAPPLY (wl_state_store t1) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_set_var (adjust_var dest) w t1) NONE locs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final2 THEN
  MAP_EVERY EXISTS_TAC
   [`data_state_ffi_fupd (K (data_state_ffi (s2:(C,FFI)data_state))) (s:(C,FFI)data_state)`;
    `wl_state_ffi_fupd (K (data_state_ffi (s2:(C,FFI)data_state))) (t:(A,C,FFI)wl_state)`] THEN
  ASM_SIMP_TAC[ASP6AUX_state_rel_ffi_upd; data_state_INFO.ri_accfupds;
               wl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 16246 *)
let assign_FFI = prove
 (assign_thm_stmt `(?n. op = clos_FFI n)`,
  (REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `fn:mlstring` SUBST_ALL_TAC) THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def]) THEN
   MP_TAC(ISPEC `names_opt:(1 spt)option` option_CASES) THEN
   FIRST_X_ASSUM(fun th -> if is_neg (concl th) && can (find_term ((=) `names_opt:(1 spt)option`)) (concl th)
                           then REWRITE_TAC[th] else NO_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `kept:1 spt` SUBST_ALL_TAC)) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP state_rel_cut_state_opt_SOME o
     (fun th -> end_itlist CONJ [th; ASSUME `data_get_vars args (data_state_locals (s:(C,FFI)data_state)) = SOME vals`;
        ASSUME `data_cut_state_opt (SOME kept) (s:(C,FFI)data_state) = SOME x`]) o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
     STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_FFI o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`b1:bool`; `cptr:num`; `b2:bool`; `ptr:num`; `cws:byte list`;
     `dws:byte list`; `nffi:(FFI)ffi_state`; `nbs:byte list`] THEN
   STRIP_TAC) THEN
  (RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `e1:num` (X_CHOOSE_THEN `e2:num` STRIP_ASSUME_TAC) o
     REWRITE_RULE[ASP6AUX_get_vars_2] o
     check (fun th -> try asp6_is_app "data_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
   ALL_TAC) THEN
  (MP_TAC(MATCH_MP ASP6AUX_state_rel_get_var2 (end_itlist CONJ
     [ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`;
      ASSUME `lookup e1 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_RefPtr b1 cptr)`;
      ASSUME `lookup e2 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_RefPtr b2 ptr)`])) THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_ByteArray_IMP o
     (fun th -> CONJ th (CONJ (ASSUME `lookup cptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ByteArray T cws)`)
                         (ASSUME `good_dimindex (:A)`))) o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `CONS (data_RefPtr b1 cptr,(w1:A word_loc))`)) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `pw1:A word` (X_CHOOSE_THEN `pa1:A word` (X_CHOOSE_THEN `hd1:A word`
     STRIP_ASSUME_TAC))) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `CONS (data_RefPtr b1 cptr,(w1:A word_loc))`)) (concl th))) THEN
   RVEQ_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_ByteArray_IMP o
     (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ByteArray F dws)`)
                         (ASSUME `good_dimindex (:A)`))) o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `CONS (data_RefPtr b2 ptr,(w2:A word_loc))`)) (concl th) &&
       not (can (find_term ((=) `data_RefPtr b1 cptr`)) (concl th)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `pw2:A word` (X_CHOOSE_THEN `pa2:A word` (X_CHOOSE_THEN `hd2:A word`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC) THEN
  (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_FFI_def] THEN
   ASM_CASES_TAC `~data_to_word_config_call_empty_ffi c /\ fn = implode ""` THEN
   ASM_REWRITE_TAC[]) THENL
  [(FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
   UNDISCH_TAC `call_FFI (data_state_ffi (s:(C,FFI)data_state)) (ExtCall (implode "")) cws dws =
                FFI_return nffi nbs` THEN
   REWRITE_TAC[call_FFI_def; injectivity "ffi_result"] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   ASP6AUX_EV_TAC [word_exp_rw; data_to_word_Unit_def] THEN
   ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final2 THEN
   MAP_EVERY EXISTS_TAC [`data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals s) (kept:1 spt))))
                            (s:(C,FFI)data_state)`; `t:(A,C,FFI)wl_state`] THEN
   ASM_SIMP_TAC[ASP6AUX_set_var_fields; wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds;
                K_THM; ASP6AUX_DO_STACK_FIELDS; ASP6AUX_do_stack_stack_max; insert_unchanged] THEN
   ALL_TAC) THEN
   (MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC memory_rel_zero_space THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel o
     check (fun th -> asp6_is_app "data_to_word_gcProof_state_rel" (concl th) &&
       can (find_term ((=) `mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (kept:1 spt))`)) (concl th) &&
       not (can (find_term ((=) `y:(A word_loc)spt`)) (concl th)))) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);
   (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word pa1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word pa2)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THEN
     ASM_REWRITE_TAC[wl_get_var_def] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
   ALL_TAC) THEN
   (MP_TAC(ISPECL [`c:data_to_word_config`; `make_byte_header c T (LENGTH (cws:byte list)):A word`;
     `LENGTH (cws:byte list)`] ASP6AUX_byte_header_len) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `make_byte_header c F (LENGTH (dws:byte list)):A word`;
     `LENGTH (dws:byte list)`] ASP6AUX_byte_header_len) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
   SUBGOAL_THEN `read_bytearray (word_add pa1 bytes_in_word) (LENGTH (cws:byte list))
                   (mem_load_byte_aux (wl_state_memory (t:(A,C,FFI)wl_state)) (wl_state_mdomain t)
                      (wl_state_be t)) = SOME cws /\
                 read_bytearray (word_add pa2 bytes_in_word) (LENGTH (dws:byte list))
                   (mem_load_byte_aux (wl_state_memory t) (wl_state_mdomain t)
                      (wl_state_be t)) = SOME dws` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC IMP_read_bytearray_GENLIST THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   ASM_CASES_TAC `fn = implode ""`) THENL
   [(CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; data_to_word_list_Seq_def] THEN
   ASM_REWRITE_TAC[] THEN
   ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; ASP6AUX_set_var_fields;
                   wl_mem_load_def; ASP6AUX_real_addr_set_var; cut_env_adjust_sets_ODD;
                   word_op_def; word_sh_def; ARITH; wl_get_var_def; lookup_insert; VAL_WORD_0;
                   read_bytearray_def; call_FFI_def; write_bytearray_def; LET_DEF; LET_END_DEF;
                   data_to_word_Unit_def]) THEN
    (UNDISCH_TAC `call_FFI (data_state_ffi (s:(C,FFI)data_state)) (ExtCall fn) cws dws =
                FFI_return nffi nbs` THEN
   ASM_REWRITE_TAC[call_FFI_def; injectivity "ffi_result"] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
   ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final_ffi THEN
   MAP_EVERY EXISTS_TAC [`data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals s) (kept:1 spt))))
                            (s:(C,FFI)data_state)`;
                         `wl_state_locals_fupd (K y) (t:(A,C,FFI)wl_state)`] THEN
   ASM_SIMP_TAC[ASP6AUX_set_var_fields; wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds;
                K_THM; ASP6AUX_DO_STACK_FIELDS; ASP6AUX_do_stack_stack_max; insert_unchanged] THEN
   MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC memory_rel_zero_space THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel o
     check (fun th -> asp6_is_app "data_to_word_gcProof_state_rel" (concl th) &&
       can (find_term ((=) `y:(A word_loc)spt`)) (concl th))) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
   MESON_TAC[]);
    (CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; data_to_word_list_Seq_def] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `LENGTH (nbs:byte list) = LENGTH (dws:byte list) /\
                 ~(ExtCall fn = ExtCall (implode ""))` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `call_FFI (data_state_ffi (s:(C,FFI)data_state)) (ExtCall fn) cws dws =
                  FFI_return nffi nbs` THEN
     ASM_REWRITE_TAC[call_FFI_def; injectivity "ffiname"] THEN
     (MP_TAC(ISPEC `ffi_state_oracle (data_state_ffi (s:(C,FFI)data_state)) (ExtCall fn)
       (ffi_state_ffi_state (data_state_ffi s)) cws dws` (cases "oracle_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[distinctness "ffi_result"] THEN
   COND_CASES_TAC THEN REWRITE_TAC[distinctness "ffi_result"; injectivity "ffi_result"] THEN
   STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);
     (ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; ASP6AUX_set_var_fields;
                   wl_mem_load_def; ASP6AUX_real_addr_set_var; cut_env_adjust_sets_ODD;
                   word_op_def; word_sh_def; ARITH; wl_get_var_def; lookup_insert;
                   LET_DEF; LET_END_DEF; data_to_word_Unit_def]) THEN
     (ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final_ffi THEN
   MAP_EVERY EXISTS_TAC [`data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals s) (kept:1 spt))))
                            (s:(C,FFI)data_state)`;
                         `wl_state_locals_fupd (K y) (t:(A,C,FFI)wl_state)`] THEN
   ASM_SIMP_TAC[ASP6AUX_set_var_fields; wl_state_INFO.ri_accfupds; data_state_INFO.ri_accfupds;
                K_THM; ASP6AUX_DO_STACK_FIELDS; ASP6AUX_do_stack_stack_max; insert_unchanged] THEN
   MATCH_MP_TAC memory_rel_Unit THEN ASM_REWRITE_TAC[] THEN ALL_TAC) THEN
     (FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_zero_space o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `CONS (data_RefPtr b2 ptr,wl_Word (pw2:A word))`)) (concl th))) THEN
   DISCH_THEN(MP_TAC o MATCH_MP memory_rel_write_bytearray o
     C CONJ (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) = SOME (bvl_ByteArray F dws)`)
              (CONJ (ASSUME `LENGTH (nbs:byte list) = LENGTH (dws:byte list)`)
                (CONJ (ASSUME `get_real_simple_addr c (wl_state_store (t:(A,C,FFI)wl_state)) pw2 = SOME pa2`)
                      (ASSUME `good_dimindex (:A)`))))) THEN
   DISCH_THEN(MP_TAC o MATCH_MP memory_rel_tl) THEN
   MATCH_MP_TAC memory_rel_rearrange THEN
   REWRITE_TAC[MEM_APPEND; MEM] THEN X_GEN_TAC `p:data_v#A word_loc` THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
   MATCH_MP_TAC join_env_submap_MEM THEN
   MAP_EVERY EXISTS_TAC [`mk_wf (sptree_inter (data_state_locals (s:(C,FFI)data_state)) (kept:1 spt))`;
                         `y:(A word_loc)spt`] THEN
   ASM_REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN CONJ_TAC THENL
    [MESON_TAC[option_DISTINCT];
     REPEAT STRIP_TAC THEN MATCH_MP_TAC cut_env_lookup THEN
     EXISTS_TAC `adjust_sets (kept:1 spt)` THEN EXISTS_TAC `y:(A word_loc)spt` THEN
     ASM_REWRITE_TAC[]])])]]);;

(* the data_do_app clause of an FFI call that ends the program *)
let ASP6AUX_do_app_FFI_final = prove
 (`!n vs (x:(C,FFI)data_state) f.
     data_do_app (clos_FFI n) vs x = Rerr (Rabort (Rffi_error f)) ==>
     ?b1 cptr b2 ptr cws ws.
       vs = [data_RefPtr b1 cptr; data_RefPtr b2 ptr] /\
       lookup cptr (data_state_refs x) = SOME (bvl_ByteArray T cws) /\
       lookup ptr (data_state_refs x) = SOME (bvl_ByteArray F ws) /\
       call_FFI (data_state_ffi x) (ExtCall n) cws ws = FFI_final f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; MEM;
     distinctness "clos_op"; injectivity "clos_op"] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS; data_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; case_eq "option"; case_eq "bvl_ref";
              case_eq "ffi_result"; COND_CASE_EQ; distinctness "result"; injectivity "result";
              PAIR_EQ; pair_case_eq; injectivity "error_result"; distinctness "abort";
              injectivity "abort"; distinctness "error_result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 16482 *)
let assign_FFI_final = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs i names_opt x args vals f
    n l dest.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     ~(op_requires_names (clos_FFI i) <=> (names_opt = NONE)) /\
     data_cut_state_opt names_opt s = SOME x /\
     data_get_vars args (data_state_locals s) = SOME vals /\
     wl_state_termdep t > 1 /\
     data_do_app (clos_FFI i) vals x = Rerr (Rabort (Rffi_error f)) ==>
     ?q r.
       wl_evaluate (FST (data_to_word_assign c n l dest (clos_FFI i) args names_opt),t) =
         (q,r) /\
       option_le (wl_state_stack_max r) (data_state_stack_max s) /\
       ~(q = SOME NotEnoughSpace) /\ wl_state_ffi r = wl_state_ffi t /\
       q = SOME (wl_FinalFFI f)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def]) THEN
   MP_TAC(ISPEC `names_opt:(1 spt)option` option_CASES) THEN
   FIRST_X_ASSUM(fun th -> if is_neg (concl th) && can (find_term ((=) `names_opt:(1 spt)option`)) (concl th)
                           then REWRITE_TAC[th] else NO_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `kept:1 spt` SUBST_ALL_TAC)) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP state_rel_cut_state_opt_SOME o
     (fun th -> end_itlist CONJ [th; ASSUME `data_get_vars args (data_state_locals (s:(C,FFI)data_state)) = SOME vals`;
        ASSUME `data_cut_state_opt (SOME kept) (s:(C,FFI)data_state) = SOME x`]) o
     check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
   DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
     STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_FFI_final o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th)) with Failure _ -> false)) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`b1:bool`; `cptr:num`; `b2:bool`; `ptr:num`; `cws:byte list`;
     `dws:byte list`] THEN
   STRIP_TAC) THEN
  (RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `e1:num` (X_CHOOSE_THEN `e2:num` STRIP_ASSUME_TAC) o
     REWRITE_RULE[ASP6AUX_get_vars_2] o
     check (fun th -> try asp6_is_app "data_get_vars" (lhs (concl th)) with Failure _ -> false)) THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
   ALL_TAC) THEN
  (MP_TAC(MATCH_MP ASP6AUX_state_rel_get_var2 (end_itlist CONJ
     [ASSUME `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs`;
      ASSUME `lookup e1 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_RefPtr b1 cptr)`;
      ASSUME `lookup e2 (data_state_locals (s:(C,FFI)data_state)) = SOME (data_RefPtr b2 ptr)`])) THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_ByteArray_IMP o
     (fun th -> CONJ th (CONJ (ASSUME `lookup cptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ByteArray T cws)`)
                         (ASSUME `good_dimindex (:A)`))) o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `CONS (data_RefPtr b1 cptr,(w1:A word_loc))`)) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `pw1:A word` (X_CHOOSE_THEN `pa1:A word` (X_CHOOSE_THEN `hd1:A word`
     STRIP_ASSUME_TAC))) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `CONS (data_RefPtr b1 cptr,(w1:A word_loc))`)) (concl th))) THEN
   RVEQ_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_ByteArray_IMP o
     (fun th -> CONJ th (CONJ (ASSUME `lookup ptr (data_state_refs (s:(C,FFI)data_state)) =
                                       SOME (bvl_ByteArray F dws)`)
                         (ASSUME `good_dimindex (:A)`))) o
     check (fun th -> asp6_is_app "memory_rel" (concl th) &&
       can (find_term ((=) `CONS (data_RefPtr b2 ptr,(w2:A word_loc))`)) (concl th) &&
       not (can (find_term ((=) `data_RefPtr b1 cptr`)) (concl th)))) THEN
   DISCH_THEN(X_CHOOSE_THEN `pw2:A word` (X_CHOOSE_THEN `pa2:A word` (X_CHOOSE_THEN `hd2:A word`
     STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC) THEN
  (REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_FFI_def] THEN
   ASM_CASES_TAC `~data_to_word_config_call_empty_ffi c /\ i = implode ""` THEN
   ASM_REWRITE_TAC[]) THENL
  [(FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
   UNDISCH_TAC `call_FFI (data_state_ffi (s:(C,FFI)data_state)) (ExtCall (implode "")) cws dws =
                FFI_final f` THEN
   REWRITE_TAC[call_FFI_def; distinctness "ffi_result"]);
   (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var e1)) = SOME (wl_Word pa1) /\
                 wl_word_exp t (real_addr c (adjust_var e2)) = SOME (wl_Word pa2)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THEN
     ASM_REWRITE_TAC[wl_get_var_def] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_conf o
     check ((=) `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` o concl)) THEN
   ALL_TAC) THEN
   (MP_TAC(ISPECL [`c:data_to_word_config`; `make_byte_header c T (LENGTH (cws:byte list)):A word`;
     `LENGTH (cws:byte list)`] ASP6AUX_byte_header_len) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `make_byte_header c F (LENGTH (dws:byte list)):A word`;
     `LENGTH (dws:byte list)`] ASP6AUX_byte_header_len) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
   SUBGOAL_THEN `read_bytearray (word_add pa1 bytes_in_word) (LENGTH (cws:byte list))
                   (mem_load_byte_aux (wl_state_memory (t:(A,C,FFI)wl_state)) (wl_state_mdomain t)
                      (wl_state_be t)) = SOME cws /\
                 read_bytearray (word_add pa2 bytes_in_word) (LENGTH (dws:byte list))
                   (mem_load_byte_aux (wl_state_memory t) (wl_state_mdomain t)
                      (wl_state_be t)) = SOME dws` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC IMP_read_bytearray_GENLIST THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   ASM_CASES_TAC `i = implode ""`) THENL
   [(FIRST_X_ASSUM SUBST_ALL_TAC THEN
   UNDISCH_TAC `call_FFI (data_state_ffi (s:(C,FFI)data_state)) (ExtCall (implode "")) cws dws =
                FFI_final f` THEN
   REWRITE_TAC[call_FFI_def; distinctness "ffi_result"]);
    (CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; data_to_word_list_Seq_def] THEN
   ASM_REWRITE_TAC[] THEN
   ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; ASP6AUX_set_var_fields;
                   wl_mem_load_def; ASP6AUX_real_addr_set_var; cut_env_adjust_sets_ODD;
                   word_op_def; word_sh_def; ARITH; wl_get_var_def; lookup_insert;
                   LET_DEF; LET_END_DEF; data_to_word_Unit_def]) THEN
    (ASP6AUX_QR_TAC THEN
   REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM; ASP6AUX_set_var_fields;
               option_INJ; distinctness "wl_result"] THEN
   ASM_REWRITE_TAC[])]]);;

(* HOL4 line 16620 *)
let getWords_acc = prove
 (CASE_TERM
  `!ws (acc:(bool#A word)list).
     getWords ws acc =
     let (cs,c) = getWords ws [] in (APPEND (REVERSE acc) cs,c)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[getWords_def; REVERSE; APPEND_NIL] THEN CASE_REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  X_GEN_TAC `acc:(bool#A word)list` THEN
  SUBST1_TAC(ISPEC `h:bool#A word_loc` (GSYM PAIR)) THEN
  SPEC_TAC(`FST (h:bool#A word_loc)`,`b:bool`) THEN
  SPEC_TAC(`SND (h:bool#A word_loc)`,`y:A word_loc`) THEN
  REPEAT GEN_TAC THEN CASES_ON `y:A word_loc` THEN
  REWRITE_TAC[getWords_def] THEN CASE_REWRITE_TAC[] THENL
   [ONCE_ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `getWords t ([]:(bool#A word)list)` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[REVERSE; APPEND; GSYM APPEND_ASSOC];
    REWRITE_TAC[REVERSE; APPEND_NIL] THEN CASE_REWRITE_TAC[APPEND_NIL]]);;

(* HOL4 line 16632 *)
let getWords_thm = prove
 (`!ws (cs:(bool#A word)list) rest.
     getWords ws [] = (cs,rest) ==>
     ws = APPEND (MAP (\(b,c). (b,wl_Word c)) cs) rest`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[getWords_def; REVERSE; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    EXPAND_TAC "cs" THEN EXPAND_TAC "rest" THEN REWRITE_TAC[MAP; APPEND];
    ALL_TAC] THEN
  SUBST1_TAC(ISPEC `h:bool#A word_loc` (GSYM PAIR)) THEN
  SPEC_TAC(`FST (h:bool#A word_loc)`,`b:bool`) THEN
  SPEC_TAC(`SND (h:bool#A word_loc)`,`y:A word_loc`) THEN
  REPEAT GEN_TAC THEN CASES_ON `y:A word_loc` THEN
  REWRITE_TAC[getWords_def] THEN CASE_REWRITE_TAC[] THENL
   [ONCE_REWRITE_TAC[getWords_acc] THEN
    MP_TAC(ISPEC `getWords t ([]:(bool#A word)list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:(bool#A word)list` (X_CHOOSE_THEN `p2:(bool#A word_loc)list`
      ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[REVERSE; APPEND; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p1:(bool#A word)list`; `p2:(bool#A word_loc)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "cs" THEN EXPAND_TAC "rest" THEN REWRITE_TAC[MAP; APPEND] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[REVERSE; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "cs" THEN EXPAND_TAC "rest" THEN
    REWRITE_TAC[MAP; APPEND]]);;

(* HOL4 line 16645 *)
let store_list_word_cond_add_IMP = prove
 (`!y2 (m:A word->A word_loc) (a:A word) m1 free c dm.
     data_to_word_memoryProof_store_list free
       (MAP (word_cond_add c a) (MAP (\(b,c). (b,wl_Word c)) y2)) m dm = SOME m1 ==>
     const_addresses free y2 dm /\
     const_writes free (word_shl a (shift_length c - backend_common_word_shift (:A))) y2 m =
       m1`,
  (LIST_INDUCT_TAC THEN
   REWRITE_TAC[MAP; data_to_word_memoryProof_store_list_def; const_addresses_def;
               const_writes_def; option_INJ] THEN
   REPEAT GEN_TAC THEN
   SUBST1_TAC(ISPEC `h:bool#A word` (GSYM PAIR)) THEN
   SPEC_TAC(`FST (h:bool#A word)`,`b:bool`) THEN SPEC_TAC(`SND (h:bool#A word)`,`w:A word`) THEN
   REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[const_writes_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`((free:A word) =+ word_cond_add c (a:A word) (b,wl_Word w))
      (m:A word->A word_loc)`; `a:A word`; `m1:A word->A word_loc`;
      `word_add (free:A word) bytes_in_word`; `c:data_to_word_config`; `dm:A word->bool`]) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   DISJ_CASES_THEN SUBST_ALL_TAC (SPEC `b:bool` BOOL_CASES_AX) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[word_cond_add_def]) THEN
   ASM_REWRITE_TAC[]));;

(* HOL4 line 16662 *)
let evaluate_StoreAnyConsts = prove
 (`!r1 r2 r3 vs w (s:(A,C,FFI)wl_state) free m dm m1 c (a:A word).
     data_to_word_memoryProof_store_list free (MAP (word_cond_add c a) vs) m dm = SOME m1 /\
     m = wl_state_memory s /\ dm = wl_state_mdomain s /\ ALL_DISTINCT [r1;r2;r3] /\
     ALL (good_loc (domain (wl_state_code s)) o SND) (CONS w vs) /\
     lookup r2 (wl_state_locals s) = SOME (wl_Word free) /\
     lookup r3 (wl_state_locals s) =
       SOME (wl_Word (word_shl a (shift_length c - backend_common_word_shift (:A)))) ==>
     ?ll.
       wl_evaluate (StoreAnyConsts r1 r2 r3 vs w,s) =
         (NONE,wl_state_memory_fupd (K m1) (wl_state_locals_fupd (K ll)
                 (wl_state_store_fupd
                    (K (wl_state_store s |+
                          (NextFree,wl_Word (word_add free
                             (word_mul bytes_in_word (word (LENGTH vs)))))))
                    s))) /\
       lookup r1 ll = SOME (word_cond_add c a w) /\
       !n. ~MEM n [r1;r2;r3] ==> lookup n ll = lookup n (wl_state_locals s)`,
  (MATCH_MP_TAC StoreAnyConsts_ind THEN CONJ_TAC THENL
    [REPEAT GEN_TAC THEN
     REWRITE_TAC[MAP; data_to_word_memoryProof_store_list_def; option_INJ; ALL; o_THM;
                 ALL_DISTINCT; MEM; DE_MORGAN_THM; LENGTH; WORD_MUL_0; WORD_ADD_0] THEN
     STRIP_TAC THEN RVEQ_TAC THEN
     REWRITE_TAC[StoreAnyConsts_def] THEN
     FIRST_X_ASSUM(MP_TAC o check (asp6_is_app "good_loc" o concl)) THEN
     SUBST1_TAC(ISPEC `v:bool#A word_loc` (GSYM PAIR)) THEN
     SPEC_TAC(`FST (v:bool#A word_loc)`,`b:bool`) THEN
     SPEC_TAC(`SND (v:bool#A word_loc)`,`y:A word_loc`) THEN
     REPEAT GEN_TAC THEN REWRITE_TAC[FST; SND] THEN
     CASES_ON `y:A word_loc` THEN CASE_REWRITE_TAC[good_loc_def] THEN REPEAT STRIP_TAC THEN
     ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; ASP6AUX_set_store_fields;
                     ASP6AUX_set_var_fields] THEN
     TRY(BOOL_CASES_TAC `b:bool`) THEN
     REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; MAP;
       word_op_def; ASP6AUX_set_store_fields; ASP6AUX_set_var_fields] THEN CASE_REWRITE_TAC[])) THEN
     REWRITE_TAC[word_cond_add_def] THEN
     REWRITE_TAC[PAIR_EQ; wl_state_component_equality; ASP6AUX_set_var_fields;
                 ASP6AUX_set_store_fields; wl_state_INFO.ri_accfupds; K_THM; RIGHT_EXISTS_AND_THM;
                 UNWIND_THM1; lookup_insert] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   RVEQ_TAC THEN
   REWRITE_TAC[StoreAnyConsts_def] THEN
   CASES_ON `SND (v:bool#A word_loc)` THEN CASE_REWRITE_TAC[]) THENL
   [(MP_TAC(ISPEC `getWords (CONS (v:bool#A word_loc) vs) []` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `ws:(bool#A word)list` (X_CHOOSE_THEN `vs1:(bool#A word_loc)list`
     ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP getWords_thm) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a':A word`; `ws:(bool#A word)list`;
     `vs1:(bool#A word_loc)list`] o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `getWords:(bool#A word_loc)list->(bool#A word)list->(bool#A word)list#(bool#A word_loc)list`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "data_to_word_memoryProof_store_list" (lhs (concl th)) with Failure _ -> false)) THEN
   ASM_REWRITE_TAC[MAP_APPEND; store_list_APPEND] THEN
   CASES_ON `data_to_word_memoryProof_store_list free
      (MAP (word_cond_add c a) (MAP (\(b,c). b,wl_Word c) (ws:(bool#A word)list)))
      (wl_state_memory (s:(A,C,FFI)wl_state)) (wl_state_mdomain s)` THEN
   CASE_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP store_list_word_cond_add_IMP) THEN STRIP_TAC) THEN
    (ASP6AUX_EV_TAC [wl_get_var_def; ASP6AUX_set_var_fields; wl_unset_var_def;
                   wl_state_INFO.ri_accfupds; K_THM; LET_DEF; LET_END_DEF] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   ABBREV_TAC `s5 = wl_set_var r2 (wl_Word (word_add free (word_mul bytes_in_word
       (word (LENGTH (ws:(bool#A word)list))))))
       (wl_set_var r3 (wl_Word (word_shl a (shift_length c - backend_common_word_shift (:A))))
       (wl_state_locals_fupd (K (delete r2 (delete r3 (wl_state_locals (s:(A,C,FFI)wl_state)))))
       (wl_state_memory_fupd (K a'') s)))` THEN
   ALL_TAC) THEN
    (SUBGOAL_THEN `ALL (good_loc (domain (wl_state_code (s:(A,C,FFI)wl_state))) o SND)
                   (CONS (w:bool#A word_loc) vs1)` ASSUME_TAC THENL
    [UNDISCH_TAC `ALL (good_loc (domain (wl_state_code (s:(A,C,FFI)wl_state))) o SND)
                    (CONS (w:bool#A word_loc) (CONS v vs))` THEN
     FIRST_ASSUM(fun th -> if is_eq (concl th) && is_cons (lhs (concl th)) &&
                              asp6_is_app "APPEND" (rhs (concl th))
                           then SUBST1_TAC th else NO_TAC) THEN
     REWRITE_TAC[ALL; ALL_APPEND] THEN SIMP_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`s5:(A,C,FFI)wl_state`;
     `word_add free (word_mul bytes_in_word (word (LENGTH (ws:(bool#A word)list)))):A word`;
     `a'':A word->A word_loc`; `wl_state_mdomain (s:(A,C,FFI)wl_state)`;
     `m1:A word->A word_loc`; `c:data_to_word_config`; `a:A word`] o
     check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `vs1:(bool#A word_loc)list`)) (concl th))) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "s5" THEN
     REWRITE_TAC[ASP6AUX_set_var_fields; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
     ASM_REWRITE_TAC[] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP; ALL; ALL_DISTINCT; MEM; DE_MORGAN_THM;
                                 ALL_APPEND; ALL_MAP]) THEN
     ASM_REWRITE_TAC[ALL; ALL_DISTINCT; MEM; DE_MORGAN_THM];
     ALL_TAC]) THEN
    (DISCH_THEN(X_CHOOSE_THEN `ll:(A word_loc)spt` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `ll:(A word_loc)spt` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [EXPAND_TAC "s5" THEN
     REWRITE_TAC[PAIR_EQ; wl_state_component_equality; ASP6AUX_set_var_fields;
                 wl_state_INFO.ri_accfupds; K_THM; LENGTH_APPEND; LENGTH_MAP] THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
     X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `ll:(A word_loc)spt`)) (concl th))) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "s5" THEN
     RULE_ASSUM_TAC(REWRITE_RULE[MEM; DE_MORGAN_THM]) THEN
     ASM_REWRITE_TAC[ASP6AUX_set_var_fields; wl_state_INFO.ri_accfupds; K_THM;
                     lookup_insert; lookup_delete]]);
    (SUBGOAL_THEN `a1 = 0 /\ a0 IN domain (wl_state_code (s:(A,C,FFI)wl_state)) /\
                 ALL (good_loc (domain (wl_state_code s)) o SND) (CONS (w:bool#A word_loc) vs)`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `ALL (good_loc (domain (wl_state_code (s:(A,C,FFI)wl_state))) o SND)
                    (CONS (w:bool#A word_loc) (CONS v vs))` THEN
     ASM_REWRITE_TAC[ALL; o_THM; good_loc_def] THEN SIMP_TAC[];
     ALL_TAC] THEN
   RVEQ_TAC THEN
   SUBGOAL_THEN `word_cond_add c (a:A word) v = wl_Loc a0 0` ASSUME_TAC THENL
    [SUBST1_TAC(ISPEC `v:bool#A word_loc` (GSYM PAIR)) THEN
     FIRST_ASSUM(let qtm = `SND (v:bool#A word_loc) = wl_Loc a0 0` in fun th -> if concl th = qtm
                           then SUBST1_TAC th else NO_TAC) THEN
     BOOL_CASES_TAC `FST (v:bool#A word_loc)` THEN REWRITE_TAC[word_cond_add_def];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "data_to_word_memoryProof_store_list" (lhs (concl th)) with Failure _ -> false)) THEN
   ASM_REWRITE_TAC[MAP; data_to_word_memoryProof_store_list_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
   REWRITE_TAC[data_to_word_list_Seq_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM]) THEN
   SUBGOAL_THEN `~(r2:num = r1) /\ ~(r3:num = r1) /\ ~(r3:num = r2)` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASP6AUX_EV_TAC [word_exp_rw; wl_get_var_def; ASP6AUX_set_var_fields; wl_mem_store_def;
                   ITLIST; OPTION_MAP_DEF; WORD_ADD_0; lookup_insert;
                   wl_state_INFO.ri_accfupds; K_THM]) THEN
    (ABBREV_TAC `s5 = wl_state_memory_fupd (K ((free =+ wl_Loc a0 0) (wl_state_memory s)))
      (wl_set_var r2 (wl_Word (word_add free bytes_in_word))
      (wl_set_var r1 (wl_Loc a0 0) (s:(A,C,FFI)wl_state)))` THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`s5:(A,C,FFI)wl_state`;
     `word_add free bytes_in_word:A word`;
     `(free =+ wl_Loc a0 0) (wl_state_memory (s:(A,C,FFI)wl_state))`;
     `wl_state_mdomain (s:(A,C,FFI)wl_state)`;
     `m1:A word->A word_loc`; `c:data_to_word_config`; `a:A word`] o
     REWRITE_RULE[] o
     SPECL [`a0:num`; `0`] o
     check (fun th -> is_forall (concl th) &&
       can (find_term (fun u -> is_const u && fst(dest_const u) = "wl_Loc")) (concl th) &&
       can (find_term ((=) `vs:(bool#A word_loc)list`)) (concl th))) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "s5" THEN
     ASM_REWRITE_TAC[ASP6AUX_set_var_fields; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
                     ALL_DISTINCT; MEM; DE_MORGAN_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `ll:(A word_loc)spt` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `ll:(A word_loc)spt` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [EXPAND_TAC "s5" THEN
     REWRITE_TAC[PAIR_EQ; wl_state_component_equality; ASP6AUX_set_var_fields;
                 wl_state_INFO.ri_accfupds; K_THM; LENGTH] THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE;
     X_GEN_TAC `k:num` THEN REWRITE_TAC[MEM; DE_MORGAN_THM] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
         can (find_term ((=) `ll:(A word_loc)spt`)) (concl th)
       then MP_TAC (SPEC `k:num` th) else NO_TAC) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "s5" THEN
     ASM_REWRITE_TAC[ASP6AUX_set_var_fields; wl_state_INFO.ri_accfupds; K_THM;
                     lookup_insert]])]);;

let ASP6AUX_do_build_SOME = prove
 (`!parts m k (x:((data_v)bvl_ref)spt) ts v vs ts1.
     data_do_build m k parts x (SOME ts) = (v,vs,ts1) ==> ?ts2. ts1 = SOME ts2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_do_build_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?a b c. data_do_part m h (x:((data_v)bvl_ref)spt) (SOME ts) = (a,b,SOME c)`
    STRIP_ASSUME_TAC THENL
   [STRUCT_CASES_TAC(ISPEC `h:const_part` (cases "const_part")) THEN
    REWRITE_TAC[data_do_part_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 16738 *)
let do_build_const_IMP_SOME = prove
 (`!parts (x:((data_v)bvl_ref)spt) ts v vs ts1.
     data_do_build_const parts x (SOME ts) = (v,vs,ts1) ==> ?ts2. ts1 = SOME ts2`,
  REWRITE_TAC[data_do_build_const_def] THEN MESON_TAC[ASP6AUX_do_build_SOME]);;

(* HOL4 line 16752 (local) *)
let TWO_POW_LEMMA = prove
 (`!n. (2 EXP n <= 3 ==> n < 2) /\ (2 EXP n <= 2 ==> n < 2) /\ (2 EXP n <= 1 ==> n < 1)`,
  GEN_TAC THEN ASM_CASES_TAC `n < 2` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `n = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    SUBGOAL_THEN `2 EXP 2 <= 2 EXP n` MP_TAC THENL
     [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]]);;

(* HOL4 line 16764 *)
let bignum_size = prove
 (`!i. good_dimindex (:A) ==>
       bignum_size (dimindex (:A) = 64) i =
       LENGTH (n2mw (num_of_int (abs i)):(A word)list) + 1`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[bignum_size_def; ARITH_RULE `1 + a = b + 1 <=> a = b`] THEN
  SPEC_TAC(`num_of_int (abs i)`,`n:num`) THEN
  MATCH_MP_TAC (INST_TYPE [`:A`,`:N`] n2mw_ind) THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[bignum_digits_def] THEN
  ONCE_REWRITE_TAC[INST_TYPE [`:A`,`:N`] n2mw_def] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LENGTH] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ADD1; ARITH_RULE `1 + a = b + 1 <=> a = b`] THEN
  REPEAT AP_TERM_TAC THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let ASP6AUX_part_NONE_Int = prove
 (`!c m i (off:A word) lims.
     good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
     limits_length_limit lims = data_to_word_config_len_size c /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     part_to_words c m (clos_Int i) off = NONE ==> ~lim_safe_part lims (clos_Int i)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `2 EXP data_to_word_config_len_size c <= 2 EXP (dimindex (:A) - 4) /\
                 2 EXP 6 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2) /\
                 2 EXP 32 <= dimword (:A)` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[LE_EXP; dimword_def] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
     REWRITE_TAC[good_dimindex_def] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `2 EXP 28 <= dimword (:A) DIV 16` ASSUME_TAC THENL
    [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN UNDISCH_TAC `2 EXP 32 <= dimword (:A)` THEN
     CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
     ALL_TAC] THEN
   UNDISCH_TAC `part_to_words c m (clos_Int i) (off:A word) = NONE` THEN
   ASM_SIMP_TAC[part_to_words_def; lim_safe_part_def; small_num_small_int] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; i2mw_def] THEN CASE_REWRITE_TAC[] THEN
   CASES_ON `encode_header c (if i < &0 then 7 else 3)
               (LENGTH (n2mw (num_of_int (abs i)):(A word)list)):(A word)option` THEN
   CASE_REWRITE_TAC[option_DISTINCT] THEN
   ASM_SIMP_TAC[bignum_size] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ASP6AUX_encode_header_NONE] o
     check (fun th -> try asp6_is_app "encode_header" (lhs (concl th)) with Failure _ -> false)) THEN
   MAP_EVERY (fun t -> UNDISCH_TAC t)
     [`2 EXP data_to_word_config_len_size c <= 2 EXP (dimindex (:A) - 4)`;
      `2 EXP 6 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2)`;
      `2 EXP 28 <= dimword (:A) DIV 16`] THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   COND_CASES_TAC THEN ARITH_TAC));;

let ASP6AUX_part_NONE_Con = prove
 (`!c m t ns (off:A word) lims.
     good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
     limits_length_limit lims = data_to_word_config_len_size c /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     part_to_words c m (clos_Con t ns) off = NONE ==> ~lim_safe_part lims (clos_Con t ns)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `arch_size lims = dimindex (:A)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[arch_size_def] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
     REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   UNDISCH_TAC `part_to_words c m (clos_Con t ns) (off:A word) = NONE` THEN
   ASM_REWRITE_TAC[part_to_words_def; lim_safe_part_def; GSYM dimword_def] THEN
   STRUCT_CASES_TAC(ISPEC `ns:num list` list_CASES) THEN
   REWRITE_TAC[NULL; NOT_CONS_NIL] THENL
    [COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT];
     ALL_TAC] THEN
   CASES_ON `encode_header c (4 * t) (LENGTH (CONS (h:num) t')):(A word)option` THEN
   CASE_REWRITE_TAC[option_DISTINCT] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ASP6AUX_encode_header_NONE] o
     check (fun th -> try asp6_is_app "encode_header" (lhs (concl th)) with Failure _ -> false)) THEN
   REWRITE_TAC[DE_MORGAN_THM] THEN ARITH_TAC));;

let ASP6AUX_part_NONE_W64 = prove
 (`!c m w (off:A word) lims.
     good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
     limits_length_limit lims = data_to_word_config_len_size c /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     part_to_words c m (clos_W64 w) off = NONE ==> ~lim_safe_part lims (clos_W64 w)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `part_to_words c m (clos_W64 w) (off:A word) = NONE` THEN
   ASM_REWRITE_TAC[part_to_words_def; lim_safe_part_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   SUBGOAL_THEN `LENGTH (if dimindex (:A) < 64 then [word_extract 63 32 w; word_extract 31 0 w]
                         else [word_extract 63 0 (w:int64):A word]) <= 2`
     ASSUME_TAC THENL
    [COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
   ABBREV_TAC `ws = if dimindex (:A) < 64 then [word_extract 63 32 w; word_extract 31 0 w]
                         else [word_extract 63 0 (w:int64):A word]` THEN
   CASES_ON `encode_header c 3 (LENGTH (ws:(A word)list)):(A word)option` THEN
   CASE_REWRITE_TAC[option_DISTINCT] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ASP6AUX_encode_header_NONE] o
     check (fun th -> try asp6_is_app "encode_header" (lhs (concl th)) with Failure _ -> false)) THEN
   SUBGOAL_THEN `2 EXP 6 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2) /\
                 2 EXP 28 <= 2 EXP (dimindex (:A) - 4) /\ 2 EXP 28 <= dimword (:A) DIV 16`
     MP_TAC THENL
    [REWRITE_TAC[LE_EXP] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
     REWRITE_TAC[dimword_def] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
     REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `1 < data_to_word_config_len_size c ==> 2 EXP 2 <= 2 EXP data_to_word_config_len_size c`
     MP_TAC THENL [REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `LENGTH (ws:(A word)list) <= 2` THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC));;

let ASP6AUX_part_NONE_Str = prove
 (`!c m s (off:A word) lims.
     good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
     limits_length_limit lims = data_to_word_config_len_size c /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     part_to_words c m (clos_Str s) off = NONE ==> ~lim_safe_part lims (clos_Str s)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `arch_size lims = dimindex (:A)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[arch_size_def] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
     REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   UNDISCH_TAC `part_to_words c m (clos_Str s) (off:A word) = NONE` THEN
   ASM_REWRITE_TAC[part_to_words_def; lim_safe_part_def] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[LENGTH_MAP; LENGTH_explode; byte_len_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
   POP_ASSUM MP_TAC THEN UNDISCH_TAC `good_dimindex (:A)` THEN
   REWRITE_TAC[good_dimindex_def] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC));;

(* HOL4 line 16779 (local; the variable free of HOL4 is hidden there: no     *)
(* change here) *)
let parts_to_words_NONE = prove
 (`!parts (off:A word) m aa (t:(A,C,FFI)wl_state) (s:(C,FFI)data_state) c heap a sp sp1
    gens limit.
     parts_to_words c m aa parts off = NONE /\ good_dimindex (:A) /\
     heap_in_memory_store heap a sp sp1 gens c (wl_state_store t) (wl_state_memory t)
       (wl_state_mdomain t) limit ==>
     limits_inv (data_state_limits s) (FLOOKUP (wl_state_store t) HeapLength)
       (wl_state_stack_limit t) (data_to_word_config_len_size c)
       (data_to_word_config_has_fp_ops c) (data_to_word_config_has_fp_tern c) ==>
     EX ((~) o lim_safe_part (data_state_limits s)) parts`,
  (LIST_INDUCT_TAC THENL
    [REWRITE_TAC[parts_to_words_def; option_DISTINCT]; ALL_TAC] THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[parts_to_words_def; EX; o_THM] THEN
   CASES_ON `part_to_words c m (h:const_part) (off:A word)` THEN CASE_REWRITE_TAC[] THENL
    [REWRITE_TAC[heap_in_memory_store_def; limits_inv_def] THEN REPEAT STRIP_TAC THEN
     DISJ1_TAC THEN
     UNDISCH_TAC `part_to_words c m (h:const_part) (off:A word) = NONE` THEN
     STRUCT_CASES_TAC(ISPEC `h:const_part` (cases "const_part")) THEN DISCH_TAC THENL
      [MATCH_MP_TAC ASP6AUX_part_NONE_Con; MATCH_MP_TAC ASP6AUX_part_NONE_Int;
       MATCH_MP_TAC ASP6AUX_part_NONE_Str; MATCH_MP_TAC ASP6AUX_part_NONE_W64] THEN
     MAP_EVERY EXISTS_TAC [`c:data_to_word_config`;
       `m:(bool#A word_loc)spt`; `off:A word`] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPEC `a':(bool#A word_loc)#(bool#A word_loc)list` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:bool#A word_loc` (X_CHOOSE_THEN `xs:(bool#A word_loc)list`
     SUBST1_TAC)) THEN CASE_REWRITE_TAC[] THEN
   CASES_ON `parts_to_words c (insert aa (w1:bool#A word_loc) m) (aa + 1) t
      (word_add (off:A word) (word_mul bytes_in_word (word (LENGTH (xs:(bool#A word_loc)list)))))` THEN
   CASE_REWRITE_TAC[option_DISTINCT] THENL
    [REPEAT STRIP_TAC THEN DISJ2_TAC THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
   MAP_EVERY EXISTS_TAC [`word_add (off:A word) (word_mul bytes_in_word
        (word (LENGTH (xs:(bool#A word_loc)list))))`;
     `insert aa (w1:bool#A word_loc) m`; `aa + 1`; `t':(A,C,FFI)wl_state`; `c:data_to_word_config`;
     `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`; `limit:num`] THEN
   ASM_REWRITE_TAC[];
     MP_TAC(ISPEC `a'':(bool#A word_loc)#(bool#A word_loc)list` PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN `r1:bool#A word_loc` (X_CHOOSE_THEN `ys1:(bool#A word_loc)list`
       SUBST1_TAC)) THEN CASE_REWRITE_TAC[option_DISTINCT]]));;

let ASP6AUX_do_app_Build = prove
 (`!parts vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (Build parts)) vs s = Rval (v,s2) ==>
     vs = [] /\ SUM (MAP part_space_req parts) <= data_state_space s /\
     ?refs1 ts1.
       data_do_build_const parts (data_state_refs s) (data_state_tstamps s) =
         (v,refs1,ts1) /\
       s2 = data_state_refs_fupd (K refs1) (data_state_tstamps_fupd (K ts1)
              (do_stack (BlockOp (Build parts)) []
                (do_lim_safe (data_state_space_fupd
                   (K (data_state_space s - SUM (MAP part_space_req parts))) s)
                   (BlockOp (Build parts)) [])))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; do_space_def; op_space_reset_def; op_space_req_def; MEM;
     distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op"] THEN
  REWRITE_TAC[consume_space_def] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[SUB_0; LE_0] THEN
    SUBGOAL_THEN `data_state_space_fupd (K (data_state_space s)) (s:(C,FFI)data_state) = s`
      SUBST1_TAC THENL
     [REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
      ALL_TAC];
    COND_CASES_TAC THEN CASE_REWRITE_TAC[distinctness "result"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[data_do_app_aux_def] THEN
  STRUCT_CASES_TAC(ISPEC `vs:data_v list` list_CASES) THEN CASE_REWRITE_TAC[distinctness "result"] THEN
  REWRITE_TAC[ASP6AUX_DO_STACK_FIELDS; data_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC(ISPEC `data_do_build_const parts (data_state_refs (s:(C,FFI)data_state))
                  (data_state_tstamps s)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:data_v` (X_CHOOSE_THEN `rt:((data_v)bvl_ref)spt#num option`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `rt:((data_v)bvl_ref)spt#num option` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `t1:num option`
    SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[injectivity "result"; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 16826 *)
let assign_Build = prove
 ((assign_thm_stmt `(?parts. op = BlockOp (Build parts))`),
  (ASP6AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `parts:const_part list` SUBST_ALL_TAC)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP6AUX_do_app_Build o
     check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                      with Failure _ -> false)) THEN
   DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `refs1:((data_v)bvl_ref)spt` (X_CHOOSE_THEN `ts1:num option`
       STRIP_ASSUME_TAC)))) THEN
   RVEQ_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_state_rel_facts) THEN
   REWRITE_TAC[data_to_word_assign_def] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[assign_Build_def] THEN
   CASES_ON `const_parts_to_words c parts:((bool#A word_loc)#(bool#A word_loc)list)option` THEN
   CASE_REWRITE_TAC[]) THENL
   [(REWRITE_TAC[FST] THEN
   ASP6AUX_GIVEUP_TAC
    (REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
     MATCH_MP_TAC ASP6AUX_do_stack_stack_max THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM])
    (DISCH_THEN(K ALL_TAC) THEN
     REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
     DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP ASP6AUX_do_stack_safe) THEN
     REWRITE_TAC[lim_safe_def; data_state_INFO.ri_accfupds; K_THM] THEN
     SUBGOAL_THEN `EX ((~) o lim_safe_part (data_state_limits (s:(C,FFI)data_state))) parts`
       MP_TAC THENL
      [FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm; memory_rel_def] o
         check (asp6_asm_app "data_to_word_gcProof_state_rel")) THEN
       STRIP_TAC THEN
       MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] parts_to_words_NONE) THEN
       MAP_EVERY EXISTS_TAC [`word 0:A word`; `LN:(bool#A word_loc)spt`; `0`;
         `t:(A,C,FFI)wl_state`; `c:data_to_word_config`] THEN
       ASM_REWRITE_TAC[GSYM const_parts_to_words_def] THEN ASM_MESON_TAC[];
       REWRITE_TAC[NOT_ALL; o_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC[]]));
    (MP_TAC(ISPEC `a:(bool#A word_loc)#(bool#A word_loc)list` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `w0:bool#A word_loc` (X_CHOOSE_THEN `ws:(bool#A word_loc)list`
     SUBST_ALL_TAC)) THEN CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(X_CHOOSE_TAC `ts:num` o REWRITE_RULE[IS_SOME_EXISTS] o
     check ((=) `IS_SOME (data_state_tstamps (s:(C,FFI)data_state))` o concl)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP do_build_const_IMP_SOME o
     REWRITE_RULE[ASSUME `data_state_tstamps (s:(C,FFI)data_state) = SOME ts`] o
     check (fun th -> try asp6_is_app "data_do_build_const" (lhs (concl th)) with Failure _ -> false)) THEN
   DISCH_THEN(X_CHOOSE_THEN `ts2:num` SUBST_ALL_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_IMP_free_space o check (asp6_asm_app "memory_rel")) THEN
   DISCH_THEN(X_CHOOSE_THEN `free:A word` (X_CHOOSE_THEN `curr:A word`
     (X_CHOOSE_THEN `other:(A word#A word_loc->bool)->bool` STRIP_ASSUME_TAC))) THEN
   MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
     `ts:num`; `data_state_refs (s:(C,FFI)data_state)`; `data_state_space (s:(C,FFI)data_state)`;
     `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
     `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
     `APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
          (toAList (sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
             (adjust_set (data_state_locals s)))))
        (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
           (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))`;
     `parts:const_part list`; `v:data_v`; `refs1:((data_v)bvl_ref)spt`; `ts2:num`;
     `w0:bool#A word_loc`; `ws:(bool#A word_loc)list`; `free:A word`; `curr:A word`]
     memory_rel_do_build_const) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `data_state_tstamps (s:(C,FFI)data_state) = SOME ts`;
                               THE_DEF]) THEN
   ASM_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC)) THEN
    (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP6AUX_shift_amount o
     check ((=) `shift_length c < dimindex (:A)` o concl)) THEN
   REWRITE_TAC[data_to_word_list_Seq_def] THEN
   ASP6AUX_EV_TAC [word_exp_rw; ITLIST; OPTION_MAP_DEF; WORD_ADD_0; ASP6AUX_set_var_fields;
                   word_op_def; word_sh_def; wl_get_var_def; lookup_insert; WORD_SUB_0]) THEN
    (ABBREV_TAC `s1 = wl_set_var 3 (wl_Word (word_shl (word_sub free curr)
      (shift_length c - backend_common_word_shift (:A))))
      (wl_set_var 1 (wl_Word free) (t:(A,C,FFI)wl_state))` THEN
   MP_TAC(ISPECL [`adjust_var dest`; `1`; `3`; `ws:(bool#A word_loc)list`; `w0:bool#A word_loc`;
     `s1:(A,C,FFI)wl_state`; `free:A word`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
     `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `m1:A word->A word_loc`; `c:data_to_word_config`;
     `word_sub free curr:A word`] evaluate_StoreAnyConsts) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "s1" THEN
     ASM_REWRITE_TAC[ASP6AUX_set_var_fields; lookup_insert; ALL_DISTINCT; MEM; adjust_var_NEQ;
                     ARITH_RULE `~(1 = 3) /\ ~(3 = 1)`] THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `parts:const_part list`; `FST (w0:bool#A word_loc)`;
       `SND (w0:bool#A word_loc)`; `ws:(bool#A word_loc)list`;
       `domain (wl_state_code (t:(A,C,FFI)wl_state))`] const_parts_to_words_good_loc) THEN
     ASM_REWRITE_TAC[PAIR; ALL; o_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `ll:(A word_loc)spt` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[]) THEN
    (ASP6AUX_QR_TAC THEN MATCH_MP_TAC ASP6AUX_state_rel_final3 THEN
   MAP_EVERY EXISTS_TAC [`s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`] THEN
   EXPAND_TAC "s1" THEN
   ASM_SIMP_TAC[ASP6AUX_set_var_fields; ASP6AUX_set_store_fields; wl_state_INFO.ri_accfupds;
                data_state_INFO.ri_accfupds; K_THM; ASP6AUX_DO_STACK_FIELDS;
                ASP6AUX_do_stack_stack_max; FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT;
                distinctness "store_name"; FAPPLY_FUPDATE_THM; IS_SOME_DEF; THE_DEF] THEN
   ALL_TAC) THEN
    (EXISTS_TAC `word_cond_add c (word_sub free curr) (w0:bool#A word_loc)` THEN
   SUBGOAL_THEN `!k. ~(k = adjust_var dest) /\ ~(k = 1) /\ ~(k = 3) ==>
                     lookup k ll = lookup k (wl_state_locals (t:(A,C,FFI)wl_state))`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th) &&
       can (find_term ((=) `ll:(A word_loc)spt`)) (concl th))) THEN
     ASM_REWRITE_TAC[MEM] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "s1" THEN
     ASM_REWRITE_TAC[ASP6AUX_set_var_fields; lookup_insert];
     ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC(MESON[spt_eq_thm; wf_inter]
       `!(x1:(A word_loc)spt) (y1:1 spt) (x2:(A word_loc)spt) (y2:1 spt).
          (!n. lookup n (sptree_inter x1 y1) = lookup n (sptree_inter x2 y2)) ==> sptree_inter x1 y1 = sptree_inter x2 y2`) THEN
     X_GEN_TAC `k:num` THEN REWRITE_TAC[lookup_inter_alt] THEN COND_CASES_TAC THEN
     REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(ASSUME_TAC o MATCH_MP domain_adjust_set_EVEN) THEN
     CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> asp6_is_app "EVEN" (concl th))) THEN
     CONV_TAC NUM_REDUCE_CONV;
     FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[adjust_var_NEQ; ARITH_EQ] THEN
     MESON_TAC[adjust_var_NEQ];
     REWRITE_TAC[];
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `lookup (adjust_var n) ll = lookup (adjust_var n) (wl_state_locals (t:(A,C,FFI)wl_state))`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[adjust_var_NEQ; adjust_var_11];
     REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[distinctness "store_name"];
     MATCH_MP_TAC memory_rel_less_space THEN
     EXISTS_TAC `data_state_space (s:(C,FFI)data_state) - LENGTH (ws:(bool#A word_loc)list)` THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`c:data_to_word_config`; `parts:const_part list`; `w0:bool#A word_loc`;
       `ws:(bool#A word_loc)list`] (INST_TYPE [`:A`,`:A`] const_parts_to_words_LENGTH)) THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC])]);;

(* HOL4 line 16926: fun foldr1 (ML) *)

(* HOL4 line 16928 (local) *)
let join_lemma = prove
 (`!b1 b2 x. (b1 ==> x) /\ (b2 ==> x) ==> (b1 \/ b2 ==> x)`,
  MESON_TAC[]);;

(* HOL4 line 16931 (local): the disjunction of the hypotheses of all        *)
(* assign_X theorems (HOL4: DB.match on _ ==> ^assign_thm_goal, folded with  *)
(* join_lemma)                                                              *)
let imp_assign =
  end_itlist (fun x y -> MATCH_MP join_lemma (CONJ x y))
   (map SPEC_ALL
     [assign_Install; assign_MutCons; assign_UpdateCons; assign_FinaliseCons;
      assign_WordFromWord; assign_CopyByte; assign_StringCmp; assign_XorByte;
      assign_ListAppend; assign_AllocThunk; assign_UpdateThunk; assign_ConfigGC;
      assign_WordToInt; assign_FromList; assign_RefByte; assign_RefArray;
      assign_WordFromInt; assign_TagEq; assign_TagLenEq; assign_LenEq; assign_Add;
      assign_Sub; assign_Mult; assign_Div; assign_Mod; assign_LengthByte; assign_Length;
      assign_LengthBlock; assign_BoundsCheckBlock; assign_BoundsCheckArray;
      assign_BoundsCheckByte; assign_LessSmallConst; assign_BoolNot; assign_BoolTest;
      assign_WordTest; assign_Less; assign_LessEq; assign_EqualConst; assign_Equal;
      assign_WordOpW8; assign_WordOpW64; assign_WordShiftW8; assign_WordShiftW64;
      assign_FP_cmp; assign_FP_top; assign_FP_bop; assign_FP_uop; assign_Label;
      assign_Ref; assign_Update; assign_El; assign_ElemAt; assign_UpdateByte;
      assign_DerefByte; assign_Const; assign_GlobalsPtr; assign_Global; assign_SetGlobal;
      assign_SetGlobalsPtr; assign_ConsExtend; assign_Cons; assign_FFI; assign_Build]);;

(* split the operator of the data_do_app assumption down to its leaves *)
let ASP6AUX_OP_CASES_TAC : tactic =
  let tys = [`:clos_op`; `:int_op`; `:word_op`; `:block_op`; `:glob_op`; `:mem_op`; `:thunk_op`;
             `:word_size`; `:bool`] in
  let rec split (asl,w as g) =
    let th = find (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                             with Failure _ -> false) (map snd asl) in
    let opt = rand(rator(rator(lhs(concl th)))) in
    let vs = filter (fun v -> mem (type_of v) tys) (frees opt) in
    if vs = [] then ALL_TAC g else
    let v = hd vs in
    if type_of v = bool_ty then
      (DISJ_CASES_THEN SUBST_ALL_TAC (SPEC v BOOL_CASES_AX) THEN split) g
    else (CASES_ON v THEN split) g in
  split;;

let ASP6AUX_NO_APP_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try asp6_is_app "data_do_app" (lhs (concl th))
                                          with Failure _ -> false)) THEN
  REWRITE_TAC[data_do_app_def; MEM; distinctness "clos_op"; injectivity "clos_op";
              distinctness "int_op"; distinctness "glob_op"; distinctness "mem_op";
              distinctness "block_op"; injectivity "mem_op"; injectivity "block_op"] THEN
  REWRITE_TAC[case_eq "option"; distinctness "result"] THEN
  REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "result"];;

(* HOL4 line 16935 *)
let assign_thm = prove
 (list_mk_forall(frees assign_thm_goal,assign_thm_goal),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] imp_assign) THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  ASP6AUX_OP_CASES_TAC THEN
  REWRITE_TAC[distinctness "clos_op"; injectivity "clos_op"; distinctness "int_op";
              injectivity "int_op"; distinctness "word_op"; injectivity "word_op";
              distinctness "block_op"; injectivity "block_op"; distinctness "glob_op";
              injectivity "glob_op"; distinctness "mem_op"; injectivity "mem_op";
              distinctness "thunk_op"; injectivity "thunk_op"; distinctness "word_size"] THEN
  (fun (asl,w as g) -> if w = `F` then ASP6AUX_NO_APP_TAC g
                       else (MESON_TAC[] ORELSE ASP6AUX_NO_APP_TAC) g));;
