(* ========================================================================= *)
(* data_to_word_assignProof_p4: part 4 of 6 (HOL4 lines 8194-11023) of the   *)
(* port of HOL4 compiler/backend/proofs/data_to_word_assignProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p6 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_assignProof.ml needs the last.                *)
(* ASP4AUX_ names are local helpers of this part.                           *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_assignProof_p3.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 4: HOL4 lines 8194-11023 ===== *)

(* ------------------------------------------------------------------------- *)
(* Helpers of this part (ASP4AUX_ theorems and tactics, asp4_ functions):    *)
(* the shared steps of the assign proofs below (HOL4: gvs with              *)
(* op_requires_names_def, cut_state_opt_def, do_app; imp_res_tac            *)
(* state_rel_get_vars_IMP and memory_rel_get_vars_IMP; eval_tac; fs with   *)
(* state_rel_thm and memory_rel_insert).                                    *)
(* ------------------------------------------------------------------------- *)

let ASP4AUX_DO_APP_NOSPACE = prove
 (`!op vs (s:(C,FFI)data_state).
     ~op_space_reset op /\ op_space_req op (LENGTH vs) = 0 /\ ~(op = clos_Install) /\
     ~(MEM op [IntOp Greater; IntOp GreaterEq]) ==>
     data_do_app op vs s = data_do_app_aux op vs (do_stack op vs (do_lim_safe s op vs))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[data_do_app_def; do_space_def] THEN
  CASE_REWRITE_TAC[]);;

(* proves  data_do_app op vs s = Rval (v,s2) <=> ...  for an operator op    *)
(* with no space reset and no space requirement (do_app_aux unfolded)       *)
let ASP4AUX_DO_APP_TAC op_tm : tactic =
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [op_tm; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "int_op"; distinctness "block_op";
              distinctness "word_op"; distinctness "mem_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; distinctness "result";
              injectivity "result"; PAIR_EQ; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

let ASP4AUX_state_rel_facts = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     good_dimindex (:A) /\ shift_length c < dimindex (:A) /\
     wl_state_ffi t = data_state_ffi s /\
     option_le (wl_state_stack_max t) (data_state_stack_max s)`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]);;

let ASP4AUX_state_rel_get_vars = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs args vals.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars args (data_state_locals s) = SOME vals ==>
     ?ws. wl_get_vars (MAP adjust_var args) t = SOME ws /\ LENGTH ws = LENGTH vals /\
          memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
            (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
            (APPEND (ZIP vals ws) (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))))`,
  REPEAT STRIP_TAC THEN
  DRULE state_rel_get_vars_IMP THEN DISCH_THEN(DRULE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ws:(A word_loc)list` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  DRULE_ALL memory_rel_get_vars_IMP THEN REWRITE_TAC[GSYM APPEND_ASSOC]);;

let ASP4AUX_state_rel_get_var1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs a1 v1.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars [a1] (data_state_locals s) = SOME [v1] ==>
     ?w1. wl_get_var (adjust_var a1) t = SOME w1 /\
          memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
            (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
            (CONS (v1,w1) (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))))`,
  REPEAT STRIP_TAC THEN DRULE_ALL ASP4AUX_state_rel_get_vars THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `ws:(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC `h:A word_loc` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; ZIP; APPEND]) THEN
  ASM_REWRITE_TAC[APPEND]);;

let ASP4AUX_state_rel_get_var2 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs a1 a2 v1 v2.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_vars [a1; a2] (data_state_locals s) = SOME [v1; v2] ==>
     ?w1 w2. wl_get_var (adjust_var a1) t = SOME w1 /\
          wl_get_var (adjust_var a2) t = SOME w2 /\
          memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
            (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
            (CONS (v1,w1) (CONS (v2,w2) (APPEND (join_env (data_state_locals s)
                 (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))))`,
  REPEAT STRIP_TAC THEN DRULE_ALL ASP4AUX_state_rel_get_vars THEN
  DISCH_THEN(X_CHOOSE_THEN `ws:(A word_loc)list` MP_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `ws:(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ARITH_RULE `~(SUC n = 0)`] THEN
  STRUCT_CASES_TAC(ISPEC `t':(A word_loc)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL; ARITH_RULE `~(0 = SUC n)`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`h:A word_loc`; `h':A word_loc`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; get_vars_SOME_IFF; ZIP; APPEND]) THEN
  ASM_REWRITE_TAC[APPEND]);;

let ASP4AUX_state_rel_do_stack_set_var = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w op vs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest v (do_stack op vs (do_lim_safe s op vs)))
       (wl_set_var (adjust_var dest) w t) NONE locs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ASP1AUX_state_rel_set_var THEN
  EXISTS_TAC `s:(C,FFI)data_state` THEN
  ASM_REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                  data_state_INFO.ri_accfupds; K_THM; option_le_max_right; option_le_refl] THEN
  ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]);;

let ASP4AUX_state_rel_do_stack_set_var_1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w x op vs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest v (do_stack op vs (do_lim_safe s op vs)))
       (wl_state_locals_fupd (K (insert (adjust_var dest) w (insert 1 x (wl_state_locals t))))
          t) NONE locs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `wl_state_locals_fupd (K (insert 1 x (wl_state_locals t)))
                    (t:(A,C,FFI)wl_state)`;
                 `locs:(num#num)list`; `dest:num`; `v:data_v`; `w:A word_loc`;
                 `op:clos_op`; `vs:data_v list`] ASP4AUX_state_rel_do_stack_set_var) THEN
  ASM_REWRITE_TAC[state_rel_insert_1; wl_set_var_def; wl_state_INFO.ri_accfupds;
                  wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[inter_insert_ODD_adjust_set_alt; ARITH_ODD]);;

let ASP4AUX_memory_rel_Boolv = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars b.
     memory_rel c be ts refs sp st m dm vars /\ good_dimindex (:A)
     ==> memory_rel c be ts refs sp st m dm
           (CONS (data_Boolv b,wl_Word (if b then word 18 else word 2:A word)) vars)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[memory_rel_Boolv_T; memory_rel_Boolv_F]);;

(* the goal ?q r. (NONE,r0) = (q,r) /\ P q r of an evaluation: q, r := NONE, r0 *)
let ASP4AUX_NONE_TAC : tactic = fun (asl,w as g) ->
  let q,b = dest_exists w in
  let r,b2 = dest_exists b in
  let eqn = fst (dest_conj b2) in
  let l = lhs eqn in
  let q0,r0 = dest_pair l in
  (EXISTS_TAC q0 THEN EXISTS_TAC r0 THEN REWRITE_TAC[option_DISTINCT]) g;;

let ASP4AUX_word_16 = prove
 (`!n. word_add (word_mul (word n) (word 16)) (word 2):A word = word (16 * n + 2)`,
  REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD; MULT_SYM]);;

let ASP4AUX_word_16_eq = prove
 (`!m n. m < dimword(:A) DIV 16 /\ n < dimword(:A) DIV 16 ==>
         (word (16 * m + 2):A word = word (16 * n + 2) <=> m = n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[n2w_11] THEN
  ASM_SIMP_TAC[MOD_LT; data_to_word_assignProof_LESS_DIV_16_IMP] THEN ARITH_TAC);;

let asp4_ev_clause c = find (fun th -> let l = lhs (concl (SPEC_ALL th)) in
                  fst (dest_const (fst (strip_comb (fst (dest_pair (rand l)))))) = c)
       (CONJUNCTS wl_evaluate_def);;

let ASP4AUX_ev_Seq = asp4_ev_clause "wl_Seq";;

(* ------------------------------------------------------------------------- *)
(* Symbolic evaluation of wordLang code (the work of HOL4's eval_tac and of *)
(* fs/simp with wordSemTheory.evaluate_def in the proofs below).            *)
(* asp4_ev_conv thl evaluates a term wl_evaluate (p,s) with p a concrete     *)
(* program: it unfolds the clause of the head constructor, simplifies with  *)
(* the project simpset and thl, and goes on with the parts of the result    *)
(* that are again such closed evaluations; wl_Seq c1 c2 with c1 evaluating  *)
(* to (NONE,s1) becomes wl_evaluate (c2,s1).  The constructors listed in    *)
(* asp4_ev_stop are not unfolded.                                          *)
(* ------------------------------------------------------------------------- *)

let asp4_ev_table =
  map (fun th -> let l = lhs (concl (SPEC_ALL th)) in
                 fst (dest_const (fst (strip_comb (fst (dest_pair (rand l)))))), th)
      (CONJUNCTS wl_evaluate_def);;

(* constructors that are not unfolded (calls are proved by their own      *)
(* lemmas, eval_Call_Arith and the like)                                    *)
let asp4_ev_stop = ref ["wl_Call"; "MustTerminate"];;

let asp4_is_ev tm =
  match tm with
    Comb(Const("wl_evaluate",_),arg) ->
      (try let p,_ = dest_pair arg in
           let h = fst (strip_comb p) in
           is_const h && (let n = fst (dest_const h) in
                          exists (fun (m,_) -> m = n) asp4_ev_table &&
                          not (mem n !asp4_ev_stop))
       with Failure _ -> false)
  | _ -> false;;

(* apply c to the closed subterms of tm (no variable bound in tm free in    *)
(* them), outermost first, once at each place                               *)
let rec asp4_closed_conv bvs c tm =
  try (if exists (fun v -> vfree_in v tm) bvs then failwith "" else c tm)
  with Failure _ ->
  match tm with
    Comb(f,x) ->
      (match (try Some (asp4_closed_conv bvs c f) with Failure _ -> None),
             (try Some (asp4_closed_conv bvs c x) with Failure _ -> None) with
         None, None -> failwith "asp4_closed_conv"
       | Some a, None -> AP_THM a x
       | None, Some b -> AP_TERM f b
       | Some a, Some b -> MK_COMB(a,b))
  | Abs(v,_) -> ABS_CONV (asp4_closed_conv (v::bvs) c) tm
  | _ -> failwith "asp4_closed_conv";;

let asp4_is_none tm = is_const tm && fst (dest_const tm) = "NONE";;

let rec asp4_ev_conv thl tm =
  if not (asp4_is_ev tm) then failwith "asp4_ev_conv" else
  let p,s = dest_pair (rand tm) in
  let hd,args = strip_comb p in
  let name = fst (dest_const hd) in
  if name = "wl_Seq" then
    let c1 = el 0 args and c2 = el 1 args in
    let tm1 = mk_comb(rator tm, mk_pair(c1,s)) in
    let th1 = try asp4_ev_conv thl tm1 with Failure _ -> REFL tm1 in
    let r1 = rhs (concl th1) in
    if is_pair r1 && asp4_is_none (fst (dest_pair r1)) then
      let s1 = snd (dest_pair r1) in
      let th2 = MATCH_MP (ISPECL [c1; c2; s; s1] IL2AUX_evaluate_Seq_NONE) th1 in
      TRANS th2 (asp4_ev_rest thl (rhs (concl th2)))
    else
      let th2 = REWR_CONV ASP4AUX_ev_Seq tm in
      let th3 = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV
                  (fun t -> if t = tm1 then th1 else failwith ""))) th2 in
      let th4 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV thl)) th3 in
      TRANS th4 (asp4_ev_rest thl (rhs (concl th4)))
  else
    let cls = map snd (filter (fun (m,_) -> m = name) asp4_ev_table) in
    let th1 = tryfind (fun cl -> REWR_CONV cl tm) cls in
    let th2 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV thl)) th1 in
    TRANS th2 (asp4_ev_rest thl (rhs (concl th2)))
and asp4_ev_rest thl tm =
  try let th = asp4_closed_conv [] (asp4_ev_conv thl) tm in
      TRANS th (asp4_ev_rest thl (rhs (concl th)))
  with Failure _ -> REFL tm;;

(* evaluate the closed evaluations of the goal, with the assumptions *)
let ASP4AUX_EV_TAC thl : tactic = fun (asl,w as g) ->
  CONV_TAC (asp4_closed_conv [] (asp4_ev_conv (thl @ map snd asl))) g;;

let ASP4AUX_EV_RWS =
  [word_exp_rw; wl_set_var_def; adjust_var_NEQ; word_cmp_Word_Word; asm_word_cmp_def;
   data_to_word_gcProof_word_and_one_eq_0_iff; wl_mem_load_def; WORD_AND_NOT0;
   insert_shadow];;

(* HOL4: the do_app equations of TagEq, LenEq, TagLenEq (gvs [do_app,     *)
(* AllCaseEqs()])                                                          *)
let ASP4AUX_do_app_TagEq = prove
 (`!tag vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (TagEq tag)) vs s = Rval (v,s2) <=>
     ?ts tg xs. vs = [data_Block ts tg xs] /\ v = data_Boolv (tg = tag) /\
                s2 = do_stack (BlockOp (TagEq tag)) vs
                       (do_lim_safe s (BlockOp (TagEq tag)) vs)`,
  ASP4AUX_DO_APP_TAC `BlockOp (TagEq tag)`);;

let ASP4AUX_memory_rel_conf = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars.
     memory_rel c be ts refs sp st m dm vars ==>
     data_to_word_config_len_size c + 7 < dimindex (:A) /\
     shift_length c < dimindex (:A) /\ ~(data_to_word_config_len_size c = 0) /\
     backend_common_word_shift (:A) <= shift_length c`,
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN MESON_TAC[]);;

let ASP4AUX_do_app_TagLenEq = prove
 (`!tag len vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (clos_TagLenEq tag len)) vs s = Rval (v,s2) <=>
     ?ts tg xs. vs = [data_Block ts tg xs] /\ v = data_Boolv (tg = tag /\ LENGTH xs = len) /\
                s2 = do_stack (BlockOp (clos_TagLenEq tag len)) vs
                       (do_lim_safe s (BlockOp (clos_TagLenEq tag len)) vs)`,
  ASP4AUX_DO_APP_TAC `BlockOp (clos_TagLenEq tag len)`);;

let ASP4AUX_do_app_LenEq = prove
 (`!len vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (clos_LenEq len)) vs s = Rval (v,s2) <=>
     ?ts tg xs. vs = [data_Block ts tg xs] /\ v = data_Boolv (LENGTH xs = len) /\
                s2 = do_stack (BlockOp (clos_LenEq len)) vs
                       (do_lim_safe s (BlockOp (clos_LenEq len)) vs)`,
  ASP4AUX_DO_APP_TAC `BlockOp (clos_LenEq len)`);;

(* the common start of the proofs for TagEq, TagLenEq, LenEq: after the     *)
(* introduction of op by intro, names_opt = NONE, x = s, the do_app        *)
(* equation do_th, args = [a1], the assignment unfolded with assign_th,    *)
(* lookup (adjust_var a1) (locals t) = SOME w1 and memory_rel with          *)
(* (Block ts5 t5 l5,w1) in front                                            *)
let ASP4AUX_BLOCK_OP_INTRO_TAC (intro:tactic) do_th assign_th : tactic =
  REPEAT GEN_TAC THEN intro THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def;
     distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op"]) THEN
  UNDISCH_TAC `names_opt:(1 spt)option = NONE` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    is_const t && fst(dest_const t) = "data_do_app")) (concl th))) THEN
  REWRITE_TAC[do_th] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts5:num` (X_CHOOSE_THEN `t5:num` (X_CHOOSE_THEN `l5:data_v list`
    STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_th] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf);;

(* the end of a Boolv result: (NONE,r) with r the word state with dest set  *)
(* to 18 or 2 (and maybe 1 set), the data state with dest set              *)
let ASP4AUX_BOOLV_TAC : tactic =
  ASP4AUX_NONE_TAC THEN
  (MATCH_MP_TAC ASP4AUX_state_rel_do_stack_set_var_1 ORELSE
   (REWRITE_TAC[GSYM wl_set_var_def] THEN MATCH_MP_TAC ASP4AUX_state_rel_do_stack_set_var)) THEN
  ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
  (MATCH_MP_TAC memory_rel_Boolv_T ORELSE MATCH_MP_TAC memory_rel_Boolv_F) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl) THEN REWRITE_TAC[];;

let ASP4AUX_cut_state_opt_SOME = prove
 (`!names_opt (s:(C,FFI)data_state) x.
     data_cut_state_opt names_opt s = SOME x <=>
     (names_opt = NONE /\ x = s) \/
     (?names. names_opt = SOME names /\
              domain names SUBSET domain (data_state_locals s) /\
              x = data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals s) names))) s)`,
  GEN_TAC THEN CASES_ON `names_opt:(1 spt)option` THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def; data_cut_env_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; UNWIND_THM1] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_INJ; option_DISTINCT] THEN ASM_MESON_TAC[]);;

let ASP4AUX_DO_APP_RESET = prove
 (`!op vs (s:(C,FFI)data_state).
     op_space_reset op /\ ~(op = clos_Install) /\
     ~(MEM op [IntOp Greater; IntOp GreaterEq]) ==>
     data_do_app op vs s =
     data_do_app_aux op vs (do_stack op vs (do_lim_safe (THE (do_space op vs s)) op vs))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[data_do_app_def] THEN
  SUBGOAL_THEN `?s1. do_space op vs (s:(C,FFI)data_state) = SOME s1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[do_space_def] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[THE_DEF] THEN CASE_REWRITE_TAC[]);;

let ASP4AUX_memory_rel_Number_small = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 v1 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm (CONS (data_Number n1,wl_Word v1) vars) /\
     ~bit 0 v1 ==>
     small_int (:A) n1 /\ v1 = Smallnum n1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n1:int`; `wl_Word (v1:A word)`;
                 `vars:(data_v#A word_loc)list`] memory_rel_any_Number_IMP) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n1:int`; `wl_Word (v1:A word)`;
                 `vars:(data_v#A word_loc)list`] memory_rel_Number_IMP) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"]);;

(* state_rel does not look at safe_for_space and peak_heap_length         *)
let ASP4AUX_state_rel_same_fields = prove
 (`!c l1 l2 (s:(C,FFI)data_state) s' (t:(A,C,FFI)wl_state) v locs.
     data_state_locals s' = data_state_locals s /\
     data_state_locals_size s' = data_state_locals_size s /\
     data_state_stack s' = data_state_stack s /\
     data_state_stack_max s' = data_state_stack_max s /\
     data_state_stack_frame_sizes s' = data_state_stack_frame_sizes s /\
     data_state_global s' = data_state_global s /\
     data_state_handler s' = data_state_handler s /\
     data_state_refs s' = data_state_refs s /\
     data_state_compile s' = data_state_compile s /\
     data_state_clock s' = data_state_clock s /\
     data_state_code s' = data_state_code s /\
     data_state_ffi s' = data_state_ffi s /\
     data_state_space s' = data_state_space s /\
     data_state_tstamps s' = data_state_tstamps s /\
     data_state_limits s' = data_state_limits s /\
     data_state_compile_oracle s' = data_state_compile_oracle s ==>
     (data_to_word_gcProof_state_rel c l1 l2 s' t v locs <=>
      data_to_word_gcProof_state_rel c l1 l2 s t v locs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[data_to_word_gcProof_state_rel_thm]);;

let ASP4AUX_option_stack_bound = prove
 (`!tsm xsm ls st d d1.
     option_le (OPTION_MAP2 (+) st ls) tsm /\ option_le tsm xsm ==>
     option_le (OPTION_MAP2 MAX (OPTION_MAP2 MAX (OPTION_MAP2 MAX tsm (OPTION_MAP2 (+) ls st))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls st) d))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls st) d1))
       (OPTION_MAP2 MAX xsm (OPTION_MAP2 (+) (OPTION_MAP2 MAX d d1) (OPTION_MAP2 (+) st ls)))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v option_nchotomy))
    [`tsm:num option`; `xsm:num option`; `ls:num option`; `st:num option`;
     `d:num option`; `d1:num option`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

(* ASP4AUX_EV_TAC with calls and MustTerminate unfolded too                *)
let ASP4AUX_EV_ALL_TAC thl : tactic = fun g ->
  let old = !asp4_ev_stop in
  asp4_ev_stop := [];
  try let r = ASP4AUX_EV_TAC thl g in asp4_ev_stop := old; r
  with e -> (asp4_ev_stop := old; raise e);;

(* the state of the first wl_evaluate (code,st) of the goal               *)
let asp4_callee_state code (w:term) =
  let t = find_term (fun t ->
      try let f,a = dest_comb t in
          (match f with
             Const("wl_evaluate",_) -> fst (dest_pair a) = code
           | _ -> false)
      with Failure _ -> false) w in
  snd (dest_pair (rand t));;

let ASP4AUX_refs_S1 = prove
 (`!op vs (s:(C,FFI)data_state).
     op_space_reset op ==>
     data_state_refs (do_stack op vs (do_lim_safe (THE (do_space op vs s)) op vs)) =
     data_state_refs s`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[do_stack_def; do_lim_safe; do_space_def; THE_DEF; LET_DEF; LET_END_DEF;
                  data_state_INFO.ri_accfupds; K_THM]);;

let ASP4AUX_do_app_RefArray = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp RefArray) vs s = Rval (v,s2) <=>
     ?i w. vs = [data_Number i; w] /\ &0 <= i /\
           v = data_RefPtr T (minimal ptr. ~(ptr IN domain (data_state_refs s))) /\
           s2 = data_state_refs_fupd (K (insert
                  (minimal ptr. ~(ptr IN domain (data_state_refs s)))
                  (bvl_ValueArray (REPLICATE (num_of_int i) w)) (data_state_refs s)))
                (do_stack (MemOp RefArray) vs
                  (do_lim_safe (THE (do_space (MemOp RefArray) vs s)) (MemOp RefArray) vs))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`MemOp RefArray`; `vs:data_v list`; `s:(C,FFI)data_state`] ASP4AUX_DO_APP_RESET) THEN
  REWRITE_TAC[op_space_reset_def; MEM; distinctness "clos_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  SIMP_TAC[ASP4AUX_refs_S1; op_space_reset_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[case_eq "list"; case_eq "data_v"; distinctness "result";
              injectivity "result"; PAIR_EQ; COND_RAND; COND_RATOR; COND_EXPAND] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ASP4AUX_state_rel_len_size = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) xs locs.
     data_to_word_gcProof_state_rel c l1 l2 s t xs locs ==>
     limits_length_limit (data_state_limits s) = data_to_word_config_len_size c`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; limits_inv_def] THEN MESON_TAC[]);;

let ASP4AUX_RefArray_len_word = prove
 (`!k. 4 * k < dimword (:A) /\ good_dimindex (:A) ==>
       word_shl (word_add (word_ushr (word (4 * k)) 2) (word 1))
         (backend_common_word_shift (:A)) =
       word_mul bytes_in_word (word (k + 1)):A word`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (4 * k)) 2 = word k:A word` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; GSYM dimword_def] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `4 * k < d ==> k < d`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC DIV_MULT THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_ADD; shift_lsl] THEN MATCH_ACCEPT_TAC WORD_MUL_SYM);;

let ASP4AUX_RefArray_header = prove
 (`!c k. data_to_word_config_len_size c + 2 <= dimindex (:A) ==>
         word_or (word_shl (word (4 * k))
                    ((dimindex (:A) - data_to_word_config_len_size c) - 2))
                 (make_header c (word 2) 0) =
         make_header c (word 2) k:A word`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[make_header_def; LET_DEF; LET_END_DEF; FOUR_MUL_LSL; WORD_OR_0; WORD_SHL_0] THEN
  SUBGOAL_THEN `((dimindex (:A) - data_to_word_config_len_size c) - 2) + 2 =
                dimindex (:A) - data_to_word_config_len_size c` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]);;

let ASP4AUX_RefArray_code_thm = prove
 (`!c (r:(A,C,FFI)wl_state) k w trig eoh curr m1 l1 l2.
     lookup 0 (wl_state_locals r) = SOME (wl_Loc l1 l2) /\
     lookup 2 (wl_state_locals r) = SOME (wl_Word (word (4 * k))) /\
     lookup 4 (wl_state_locals r) = SOME w /\
     FLOOKUP (wl_state_store r) TriggerGC = SOME (wl_Word trig) /\
     FLOOKUP (wl_state_store r) EndOfHeap = SOME (wl_Word eoh) /\
     FLOOKUP (wl_state_store r) CurrHeap = SOME (wl_Word curr) /\
     data_to_word_memoryProof_store_list
       (word_sub eoh (word_mul bytes_in_word (word (k + 1))))
       (CONS (wl_Word (make_header c (word 2) k)) (REPLICATE k w))
       (wl_state_memory r) (wl_state_mdomain r) = SOME m1 /\
     lookup Replicate_location (wl_state_code r) = SOME (5,Replicate_code) /\
     4 * k < dimword (:A) /\ k < wl_state_clock r /\
     good_dimindex (:A) /\ shift_length c < dimindex (:A) /\
     data_to_word_config_len_size c + 2 <= dimindex (:A)
     ==>
     ?mx. wl_evaluate (RefArray_code c,r) =
          (SOME (wl_Result (wl_Loc l1 l2)
             [make_ptr c (word_sub (word_sub eoh (word_mul bytes_in_word (word (k + 1)))) curr)
                (word 0:A word) k]),
           wl_state_memory_fupd (K m1)
            (wl_state_clock_fupd (K ((wl_state_clock r - k) - 1))
              (wl_state_locals_fupd (K LN)
                (wl_state_locals_size_fupd (K (SOME 0))
                  (wl_state_stack_max_fupd (K mx)
                    (wl_state_store_fupd (K (wl_state_store r
                       |+ (EndOfHeap,wl_Word (word_sub eoh
                             (word_mul bytes_in_word (word (k + 1)))))
                       |+ (TriggerGC,wl_Word (word_sub trig
                             (word_mul bytes_in_word (word (k + 1)))))))
                    r)))))) /\
          option_le mx (OPTION_MAP2 MAX (wl_state_stack_max r)
             (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack r))
                (lookup Replicate_location (wl_state_stack_size r))))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word 2:A word) = 2 /\ val (word 1:A word) = 1 /\
                val (word (backend_common_word_shift (:A)):A word) =
                  backend_common_word_shift (:A) /\
                val (word (shift_length c - backend_common_word_shift (:A)):A word) =
                  shift_length c - backend_common_word_shift (:A) /\
                val (word ((dimindex (:A) - data_to_word_config_len_size c) - 2):A word) =
                  (dimindex (:A) - data_to_word_config_len_size c) - 2 /\
                ~(2 >= dimindex (:A)) /\ ~(backend_common_word_shift (:A) >= dimindex (:A)) /\
                ~(shift_length c - backend_common_word_shift (:A) >= dimindex (:A)) /\
                ~((dimindex (:A) - data_to_word_config_len_size c) - 2 >= dimindex (:A))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[w2n_n2w] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN UNDISCH_TAC `shift_length c < dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MOD_LT) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` ASP4AUX_RefArray_len_word) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:data_to_word_config`; `k:num`] ASP4AUX_RefArray_header) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `data_to_word_memoryProof_store_list
       (word_sub eoh (word_mul bytes_in_word (word (k + 1))))
       (CONS (wl_Word (make_header c (word 2) k)) (REPLICATE k (w:A word_loc)))
       (wl_state_memory (r:(A,C,FFI)wl_state)) (wl_state_mdomain r) = SOME m1` THEN
  REWRITE_TAC[data_to_word_memoryProof_store_list_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  REWRITE_TAC[RefArray_code_def; data_to_word_list_Seq_def] THEN
  ASP4AUX_EV_TAC (wl_set_store_def :: wl_mem_store_def :: FLOOKUP_UPDATE ::
                  wl_get_store_def :: WORD_ADD_0 :: WORD_OR_0 :: ASP4AUX_EV_RWS)) THEN
  (W(fun (_,w) -> let st = asp4_callee_state
      `wl_Call NONE (SOME Replicate_location) [0; 1; 4; 2; 3] NONE:(A)wl_prog` w in
    MP_TAC(ISPECL [`k:num`; `word_sub eoh (word_mul bytes_in_word (word (k + 1))):A word`;
      st; `m1:A word->A word_loc`; `0`; `1`; `4`; `2`; `3`; `w:A word_loc`; `l1:num`;
      `l2:num`; `make_ptr c (word_sub (word_sub eoh (word_mul bytes_in_word (word (k + 1))))
          curr) (word 0:A word) k:A word_loc`] data_to_word_bignumProof_Replicate_code_thm)) THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
                  wl_get_var_def; lookup_insert; ARITH; make_ptr_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `mx:num option` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mx:num option` THEN ASM_REWRITE_TAC[]) THEN
  (REWRITE_TAC[PAIR_EQ; wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM]) THEN
  (MATCH_MP_TAC FUPDATE_COMMUTES THEN REWRITE_TAC[distinctness "store_name"]));;

let ASP4AUX_lookup_pop_locals = prove
 (`!(y1:(A word_loc)spt) y2 p q1 p1.
     env_to_list y2 p = (q1,p1) ==>
     !kk. lookup kk (sptree_union (fromAList q1) (fromAList (toAList y1))) = lookup kk (sptree_union y2 y1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP env_to_list_lookup_equiv) THEN
  ASM_REWRITE_TAC[lookup_union; lookup_fromAList; lookup_fromAList_toAList]);;

let ASP4AUX_RefArray_mr0 = prove
 (`!c l1 l2 (s1:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x1 a2 vv w2 L.
     data_to_word_gcProof_state_rel c l1 l2 s1 t NONE locs /\
     data_cut_state_opt (SOME names) s1 = SOME x1 /\
     lookup a2 (data_state_locals s1) = SOME vv /\
     lookup (adjust_var a2) (wl_state_locals t) = SOME w2 /\
     (!kk vx. lookup kk L = SOME vx ==> lookup kk (wl_state_locals t) = SOME vx) ==>
     memory_rel c (wl_state_be t) (THE (data_state_tstamps x1)) (data_state_refs x1)
       (data_state_space x1) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (vv,w2)
         (APPEND (join_env (data_state_locals x1)
                   (toAList (sptree_inter L (adjust_set (data_state_locals x1)))))
            (APPEND [(the_global (data_state_global x1),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack x1) (wl_state_stack t)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_lookup)) THEN
  DISCH_THEN(MP_TAC o SPECL [`a2:num`; `vv:data_v`; `w2:A word_loc`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM; MEM_APPEND] THEN X_GEN_TAC `p:data_v#A word_loc` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ1_TAC THEN
  MATCH_MP_TAC join_env_submap_MEM THEN
  MAP_EVERY EXISTS_TAC [`mk_wf (sptree_inter (data_state_locals (s1:(C,FFI)data_state)) (names:1 spt))`;
                        `L:(A word_loc)spt`] THEN
  ASM_REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN
  MESON_TAC[option_DISTINCT]);;

let ASP4AUX_encode_header_RefArray = prove
 (`!c k. good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
         k < 2 EXP data_to_word_config_len_size c /\ k < dimword (:A) DIV 16 ==>
         encode_header c 2 k = SOME (make_header c (word 2) k:A word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[encode_header_def] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dimword (:A) DIV 16 = 2 EXP (dimindex (:A) - 4) /\ 2 < dimword (:A) DIV 16`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP 2 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2)`
    MP_TAC THENL
   [REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `k < dimword (:A) DIV 16` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ARITH_TAC);;

let ASP4AUX_RefArray_call = prove
 (`!c l1 l2 (s1:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x1 a1 a2 k vv dest n l.
     data_to_word_gcProof_state_rel c l1 l2 s1 t NONE locs /\
     data_cut_state_opt (SOME names) s1 = SOME x1 /\
     lookup a1 (data_state_locals s1) = SOME (data_Number (&k)) /\
     lookup a2 (data_state_locals s1) = SOME vv /\
     data_state_space s1 = k + 1 /\ small_int (:A) (&k) /\
     4 * k < dimword (:A) /\ k < 2 EXP data_to_word_config_len_size c /\
     k < dimword (:A) DIV 16 /\ ~(wl_state_termdep t = 0)
     ==>
     ?r. wl_evaluate (MustTerminate (wl_Call (SOME ([adjust_var dest],adjust_sets names,wl_Skip,n,l))
            (SOME RefArray_location) [adjust_var a1; adjust_var a2] NONE),t) = (NONE,r) /\
         data_to_word_gcProof_state_rel c l1 l2
           (data_set_var dest (data_RefPtr T (minimal ptr. ~(ptr IN domain (data_state_refs x1))))
             (data_state_refs_fupd (K (insert (minimal ptr. ~(ptr IN domain (data_state_refs x1)))
                    (bvl_ValueArray (REPLICATE k vv)) (data_state_refs x1)))
               (data_state_space_fupd (K 0)
                 (data_state_stack_max_fupd (K (OPTION_MAP2 MAX (data_state_stack_max x1)
                    (OPTION_MAP2 (+)
                       (OPTION_MAP2 MAX (lookup RefArray_location (data_state_stack_frame_sizes x1))
                          (lookup Replicate_location (data_state_stack_frame_sizes x1)))
                       (OPTION_MAP2 (+) (size_of_stack (data_state_stack x1))
                          (data_state_locals_size x1))))) x1))))
           r NONE locs`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP lookup_RefByte_location) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s1:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `[]:num list`; `[]:data_v list`;
                 `names:1 spt`; `x1:(C,FFI)data_state`] state_rel_cut_state_opt_SOME) THEN
  ASM_REWRITE_TAC[data_get_vars_def; MAP; LENGTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    vfree_in `ws:(A word_loc)list` (concl th)))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s1:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`;
                 `locs:(num#num)list`; `a1:num`; `k:num`] state_rel_get_var_Number_IMP) THEN
  ASM_REWRITE_TAC[data_get_var_def; MP6AUX_SMALLNUM_NUM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s1:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`;
                 `locs:(num#num)list`; `a2:num`; `vv:data_v`] state_rel_get_var_IMP) THEN
  ASM_REWRITE_TAC[data_get_var_def] THEN DISCH_THEN(X_CHOOSE_TAC `w2:A word_loc`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def])) THEN
  (ASP4AUX_EV_ALL_TAC (data_to_word_get_names_def :: wl_find_code_def :: bad_dest_args_def ::
     add_ret_loc_def :: wl_dec_clock_def :: wl_call_env_def :: wl_get_vars_def ::
     LENGTH :: ARITH :: TWO_LESS_MustTerminate_limit :: ASP4AUX_EV_RWS)) THEN
  (MP_TAC(ISPEC `env_to_list (y2:((A)word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(num#(A)word_loc)list` (X_CHOOSE_THEN `p1:num->num->num`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF; adjust_sets_def; FST; domain_def;
                  NOT_INSERT_EMPTY] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM]) THEN
  (MP_TAC(ISPECL [`y1:(A word_loc)spt`; `y2:(A word_loc)spt`;
                 `wl_state_permute (t:(A,C,FFI)wl_state)`; `q1:(num#(A)word_loc)list`;
                 `p1:num->num->num`] ASP4AUX_lookup_pop_locals) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!kk vx. lookup kk (sptree_union (fromAList (q1:(num#(A)word_loc)list))
                   (fromAList (toAList (y1:(A word_loc)spt)))) = SOME vx ==>
                 lookup kk (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME vx` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC cut_env_lookup THEN
    MAP_EVERY EXISTS_TAC [`adjust_sets (names:1 spt)`; `sptree_union (y2:(A word_loc)spt) y1`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s1:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:1 spt`;
                 `x1:(C,FFI)data_state`; `a2:num`; `vv:data_v`; `w2:A word_loc`;
                 `sptree_union (fromAList (q1:(num#(A)word_loc)list))
                    (fromAList (toAList (y1:(A word_loc)spt)))`] ASP4AUX_RefArray_mr0) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_MEMREL_LEN_SIZE7 o check (fun th ->
    can (find_term ((=) `vv:data_v`)) (concl th) && is_comb (concl th) &&
    (let h,_ = strip_comb (concl th) in is_const h && fst(dest_const h) = "memory_rel"))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_RefArray) o check (fun th ->
    can (find_term ((=) `vv:data_v`)) (concl th) && is_comb (concl th) &&
    (let h,_ = strip_comb (concl th) in is_const h && fst(dest_const h) = "memory_rel"))) THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `make_header c (word 2) k:A word`;
    `minimal ptr. ~(ptr IN domain (data_state_refs (x1:(C,FFI)data_state)))`]) THEN
  SUBGOAL_THEN `data_state_space (x1:(C,FFI)data_state) = k + 1` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
    ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ASP4AUX_encode_header_RefArray; LEAST_NOTIN_spt_DOMAIN;
               ARITH_RULE `k < k + 1`; ARITH_RULE `(k + 1) - (k + 1) = 0`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `eoh:A word` (X_CHOOSE_THEN `curr:A word`
    (X_CHOOSE_THEN `trig:A word` (X_CHOOSE_THEN `m1:A word->A word_loc`
      STRIP_ASSUME_TAC))))) THEN
  (SUBGOAL_THEN `k < dimword (:A) /\ data_to_word_config_len_size c + 2 <= dimindex (:A)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `k < MustTerminate_limit (:A) - 1` ASSUME_TAC THENL
   [MP_TAC(UNDISCH MustTerminate_limit_SUB_2) THEN MP_TAC TWO_LESS_MustTerminate_limit THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [`c:data_to_word_config`;
    asp4_callee_state `RefArray_code c:(A)wl_prog` w; `k:num`; `w2:A word_loc`;
    `trig:A word`; `eoh:A word`; `curr:A word`; `m1:A word->A word_loc`; `n:num`; `l:num`]
    ASP4AUX_RefArray_code_thm)) THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
                  lookup_fromList2; lookup_fromList; LENGTH; ARITH; EL; HD; TL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mx:num option` (CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC (MATCH_MP evaluate_stack_max_le th) THEN SUBST1_TAC th)
    ASSUME_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH; ARITH] THEN
  REWRITE_TAC[wl_pop_env_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP env_to_list_domain o check (fun th ->
    try fst(strip_comb(lhs(concl th))) = `env_to_list:((A)word_loc)spt->(num->num->num)->((num#(A)word_loc)list#(num->num->num))` with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; domain_union; domain_fromAList_toAList] THEN
  REWRITE_TAC[UNION_COMM] THEN
  ASP4AUX_EV_TAC (wl_set_vars_def :: alist_insert_def :: ASP4AUX_EV_RWS) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM]) THEN
  (UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (x1:(C,FFI)data_state)
                 (t:(A,C,FFI)wl_state) NONE locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def;
              wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
              data_state_INFO.ri_accfupds; data_state_INFO.ri_fupdfupds] THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; distinctness "store_name"; FDOM_FUPDATE; IN_INSERT; ALL]) THEN
  (CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
      is_const h && fst(dest_const h) = "code_oracle_rel")) THEN
    REWRITE_TAC[code_oracle_rel_def; FLOOKUP_UPDATE; distinctness "store_name"];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
      is_const h && fst(dest_const h) = "ALL")) THEN REWRITE_TAC[ALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`names:1 spt`; `wl_state_locals (t:(A,C,FFI)wl_state)`;
                   `y1:(A word_loc)spt`; `y2:(A word_loc)spt`;
                   `wl_state_permute (t:(A,C,FFI)wl_state)`; `q1:(num#(A)word_loc)list`;
                   `p1:num->num->num`; `l1:num`; `l2:num`] cut_envs_lookup_0) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[lookup_insert; ONCE_REWRITE_RULE[EQ_SYM_EQ] adjust_var_NOT_0;
                lookup_union; lookup_fromAList; lookup_fromAList_toAList] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [X_GEN_TAC `nn:num` THEN REWRITE_TAC[lookup_insert; adjust_var_11] THEN
    COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[lookup_union] THEN
    MP_TAC(ISPECL [`names:1 spt`; `wl_state_locals (t:(A,C,FFI)wl_state)`;
                   `(y1:(A word_loc)spt,y2:(A word_loc)spt)`; `nn:num`]
      adjust_var_cut_env_IMP_MEM) THEN
    ASM_REWRITE_TAC[SND] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IS_SOME (lookup nn (names:1 spt))` ASSUME_TAC THENL
     [UNDISCH_TAC `IS_SOME (lookup nn (data_state_locals (x1:(C,FFI)data_state)))` THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
      REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lookup_mk_wf; lookup_inter_alt] THEN
      REWRITE_TAC[domain_lookup; IS_SOME_EXISTS] THEN MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    UNDISCH_TAC `IS_SOME (lookup (adjust_var nn) (y2:(A word_loc)spt)) <=>
                 IS_SOME (lookup nn (names:1 spt))` THEN
    ASM_REWRITE_TAC[] THEN
    CASES_ON `lookup (adjust_var nn) (y2:(A word_loc)spt)` THEN
    REWRITE_TAC[IS_SOME_DEF] THEN CASE_REWRITE_TAC[IS_SOME_DEF];
    ALL_TAC]) THEN
  (FIRST_X_ASSUM(fun th -> if can (find_term ((=) `wl_state_stack_max_fupd (K (mx:num option))
       :(A,C,FFI)wl_state->(A,C,FFI)wl_state`)) (concl th) then ASSUME_TAC (REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM] th)
     else failwith "") THEN
  SUBGOAL_THEN `option_le (wl_state_stack_max (t:(A,C,FFI)wl_state)) mx` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> let c = concl th in
      if is_comb c && rand c = `mx:num option` &&
         can (find_term (fun u -> try fst(dest_const u) = "RefArray_location"
                                  with Failure _ -> false)) c &&
         not (can (find_term (fun u -> try fst(dest_const u) = "Replicate_location"
                                       with Failure _ -> false)) c)
      then MATCH_MP_TAC option_le_trans THEN EXISTS_TAC (lhand c) THEN
           ASM_REWRITE_TAC[option_le_max_right; option_le_refl]
      else failwith "");
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)))
                   (wl_state_locals_size t)) (wl_state_stack_max t)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> let c = concl th in
      if is_comb c && is_comb (rator c) && lhand c = `mx:num option` &&
         can (find_term (fun u -> try fst(dest_const u) = "Replicate_location"
                                  with Failure _ -> false)) c
      then MATCH_MP_TAC option_le_trans THEN EXISTS_TAC (rand c) THEN ASM_REWRITE_TAC[]
      else failwith "") THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP stack_rel_IMP_size_of_stack o check (fun th ->
      can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "data_to_word_gcProof_stack_rel")) (concl th))) THEN
    REWRITE_TAC[stack_size_eq2; stack_size_frame_def] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ASP4AUX_option_stack_bound THEN ASM_MESON_TAC[];
    ALL_TAC]) THEN
  (CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND; GSYM APPEND_ASSOC; FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
  MATCH_MP_TAC (REWRITE_RULE[APPEND] memory_rel_insert) THEN
  FIRST_ASSUM(fun th -> ACCEPT_TAC (REWRITE_RULE[APPEND] th))));;

let ASP4AUX_cut_env_list_insert_lookup = prove
 (`!vs names (env:A spt) xa v.
     data_cut_env (list_insert vs names) env = SOME xa /\ MEM v vs ==>
     lookup v xa = lookup v env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_list_insert]);;

let ASP4AUX_cut_state_opt_list_insert = prove
 (`!names (s:(C,FFI)data_state) x vs xa sp.
     data_cut_state_opt (SOME names) s = SOME x /\
     data_cut_env (list_insert vs names) (data_state_locals s) = SOME xa ==>
     data_cut_state_opt (SOME names)
       (data_state_locals_fupd (K xa) (data_state_space_fupd (K sp) s)) =
     SOME (data_state_space_fupd (K sp) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `data_cut_env names (data_state_locals (s:(C,FFI)data_state))` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vs:num list`; `names:1 spt`; `data_state_locals (s:(C,FFI)data_state)`;
                 `xa:data_v spt`; `a:data_v spt`] cut_env_cut_env_list_insert) THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[option_INJ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs (concl th) = `x:(C,FFI)data_state`)) THEN
  REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 8194 *)
let assign_RefArray = prove
 (assign_thm_stmt `op = MemOp RefArray`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?names. names_opt = SOME (names:1 spt)`
    (X_CHOOSE_THEN `names:1 spt` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (MemOp RefArray) <=> names_opt:(1 spt)option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:(1 spt)option` THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DRULE_ALL state_rel_cut_state_opt_SOME THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (MemOp RefArray) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_RefArray] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `vv:data_v` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `LENGTH (args:num list) = LENGTH [data_Number i; vv]` THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS] o check (fun th ->
      concl th = `&0 <= (i:int)`)) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_RefArray_def; FST; LET_DEF; LET_END_DEF] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
  DRULE_ALL memory_rel_any_Number_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `adjust_var a1`; `v1:A word`]
    evaluate_BignumHalt2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rh:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `limits_arch_64_bit (data_state_limits (x:(C,FFI)data_state)) <=>
                dimindex (:A) = 64` ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm; limits_inv_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `option_le (wl_state_stack_max (t:(A,C,FFI)wl_state))
                  (data_state_stack_max (x:(C,FFI)data_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ASP4AUX_state_rel_facts]; ALL_TAC] THEN
  ASM_CASES_TAC `bit 0 (v1:A word)`) THENL
  [((SUBGOAL_THEN `~small_int (:A) (&k)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN
  MAP_EVERY EXISTS_TAC [`SOME NotEnoughSpace:((A)wl_result)option`; `rh:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[do_space_def; THE_DEF; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                  op_space_reset_def; data_state_INFO.ri_accfupds; K_THM; lim_safe_def;
                  arch_size_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `data_state_stack_max (x:(C,FFI)data_state)` THEN
    ASM_REWRITE_TAC[option_le_max_right; option_le_refl];
    ALL_TAC]) THEN
   (DISCH_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  SUBGOAL_THEN `~(k < 2 EXP (if dimindex (:A) = 64 then 64 else 32) DIV 16)`
    (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `~small_int (:A) (&k)` THEN REWRITE_TAC[MP6AUX_SMALL_INT_NUM; dimword_def] THEN
  UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC));
   ((SUBGOAL_THEN `small_int (:A) (&k)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `v1 = word (4 * k):A word` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
                   `THE (data_state_tstamps (s:(C,FFI)data_state))`;
                   `data_state_refs (s:(C,FFI)data_state)`; `data_state_space (s:(C,FFI)data_state)`;
                   `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
                   `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `&k:int`; `v1:A word`]
      ASP4AUX_memory_rel_Number_small) THEN
    ASM_REWRITE_TAC[MP6AUX_SMALLNUM_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `CONS (vv,w2:A word_loc) (APPEND
       (join_env (data_state_locals (s:(C,FFI)data_state))
       (toAList (sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
          (adjust_set (data_state_locals s)))))
      (APPEND [the_global (data_state_global s),FAPPLY (wl_state_store t) Globals]
      (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * k < dimword (:A) /\ k < dimword (:A) DIV 8` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `small_int (:A) (&k)` THEN REWRITE_TAC[MP6AUX_SMALL_INT_NUM] THEN
    MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP4AUX_EV_TAC (wl_get_vars_def :: wl_set_vars_def :: alist_insert_def :: MAP ::
                  ASP4AUX_EV_RWS)) THEN
   (REWRITE_TAC[data_to_word_get_names_def] THEN
  SUBGOAL_THEN `?xa. data_cut_env (list_insert [a1; a2] names)
                       (data_state_locals (s:(C,FFI)data_state)) = SOME xa` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_state_opt (SOME names) (s:(C,FFI)data_state) = SOME x` THEN
    UNDISCH_TAC `data_get_vars [a1; a2] (data_state_locals (s:(C,FFI)data_state)) =
                 SOME [data_Number (&k); vv]` THEN
    REWRITE_TAC[get_vars_SOME_IFF_data; ASP4AUX_cut_state_opt_SOME; option_DISTINCT;
                option_INJ; UNWIND_THM1; data_cut_env_def; data_get_var_def] THEN
    REWRITE_TAC[list_insert_def; domain_insert; SUBSET; IN_INSERT] THEN
    REWRITE_TAC[domain_lookup] THEN MESON_TAC[option_DISTINCT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (AllocVar c (MIN (2 EXP data_to_word_config_len_size c)
            (dimword (:A) DIV 16)) (list_insert [a1; a2] names),
            wl_state_locals_fupd (K (insert 1 (wl_Word (word (4 * k))) (wl_state_locals t)))
            (t:(A,C,FFI)wl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `qa:((A)wl_result)option` (X_CHOOSE_THEN `ra:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `wl_state_locals_fupd (K (insert 1 (wl_Word (word (4 * k))) (wl_state_locals t)))
       (t:(A,C,FFI)wl_state)`;
    `locs:(num#num)list`; `a1:num`; `a2:num`; `names:1 spt`; `xa:data_v spt`; `k:num`;
    `vv:data_v`; `MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)`;
    `qa:((A)wl_result)option`; `ra:(A,C,FFI)wl_state`] AllocVar_thm_binary) THEN
  ASM_REWRITE_TAC[state_rel_insert_1; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM;
                  lookup_insert] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `dimword (:A) DIV 16` THEN
    REWRITE_TAC[ARITH_RULE `MIN a b <= b`] THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `qa = SOME NotEnoughSpace:((A)wl_result)option`) THENL
   [((ASM_REWRITE_TAC[option_DISTINCT] THEN
  MAP_EVERY EXISTS_TAC [`SOME NotEnoughSpace:((A)wl_result)option`; `ra:(A,C,FFI)wl_state`] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    lhand (concl th) = `qa = SOME NotEnoughSpace:((A)wl_result)option`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
    (FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP cut_state_opt_IMP_cut_locals) THEN
  SUBGOAL_THEN `data_state_stack_max (x:(C,FFI)data_state) =
                  data_state_stack_max (s:(C,FFI)data_state) /\
                data_state_refs x = data_state_refs s /\
                data_state_limits x = data_state_limits s` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC]) THEN
    (ASM_REWRITE_TAC[do_space_def; THE_DEF; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                  op_space_reset_def; data_state_INFO.ri_accfupds; K_THM; lim_safe_def;
                  arch_size_def; space_consumed_def; NUM_OF_INT_OF_NUM]) THEN
    (CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN
    ASM_REWRITE_TAC[option_le_max_right; option_le_refl];
    ALL_TAC] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_len_size o check (fun th ->
    concl th = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                  (t:(A,C,FFI)wl_state) NONE locs`)) THEN
  SUBGOAL_THEN `k < MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)`
    ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k < MIN a b <=> k < a /\ k < b`] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `k < 2 EXP (if limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state))
                            then 64 else 32) DIV 16` THEN
    SUBGOAL_THEN `limits_arch_64_bit (data_state_limits (s:(C,FFI)data_state)) <=>
                  dimindex (:A) = 64` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[dimword_def] THEN UNDISCH_TAC `good_dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "limits_heap_limit"))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `size_of_heap_args [data_Number (&k); vv] (x:(C,FFI)data_state) + k + 1 <=
               limits_heap_limit (data_state_limits (s:(C,FFI)data_state))` THEN
  ARITH_TAC));
    ((FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    lhand (concl th) = `~(qa = SOME NotEnoughSpace:((A)wl_result)option)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o check (fun th -> is_eq (concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "AllocVar" with Failure _ -> false))
      (lhs (concl th)))) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_state_locals_fupd (K xa) (data_state_space_fupd (K (k + 1)) (s:(C,FFI)data_state))`;
    `ra:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:1 spt`;
    `data_state_space_fupd (K (k + 1)) (x:(C,FFI)data_state)`; `a1:num`; `a2:num`; `k:num`;
    `vv:data_v`; `dest:num`; `n:num`; `l:num`] ASP4AUX_RefArray_call) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    SUBGOAL_THEN `data_get_var a1 (data_state_locals (s:(C,FFI)data_state)) =
                    SOME (data_Number (&k)) /\
                  data_get_var a2 (data_state_locals s) = SOME vv` MP_TAC THENL
     [ASM_MESON_TAC[get_vars_SOME_IFF_data]; ALL_TAC] THEN
    REWRITE_TAC[data_get_var_def] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ASP4AUX_cut_state_opt_list_insert THEN EXISTS_TAC `[a1; a2]:num list` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`[a1; a2]:num list`; `names:1 spt`;
                     `data_state_locals (s:(C,FFI)data_state)`; `xa:data_v spt`; `a1:num`]
        ASP4AUX_cut_env_list_insert_lookup) THEN ASM_REWRITE_TAC[MEM];
      MP_TAC(ISPECL [`[a1; a2]:num list`; `names:1 spt`;
                     `data_state_locals (s:(C,FFI)data_state)`; `xa:data_v spt`; `a2:num`]
        ASP4AUX_cut_env_list_insert_lookup) THEN ASM_REWRITE_TAC[MEM];
      UNDISCH_TAC `k < MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)` THEN
      ARITH_TAC;
      UNDISCH_TAC `k < MIN (2 EXP data_to_word_config_len_size c) (dimword (:A) DIV 16)` THEN
      ARITH_TAC;
      UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC];
    ALL_TAC]) THEN
    (REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `rr:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,args = strip_comb (concl th) in
    is_const h && fst(dest_const h) = "data_to_word_gcProof_state_rel" &&
    length args = 7 && el 4 args = `rr:(A,C,FFI)wl_state`)) THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> b ==> a`) THEN
  MATCH_MP_TAC ASP4AUX_state_rel_same_fields THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; data_state_INFO.ri_fupdfupds;
              K_THM; K_o_THM; do_stack_def; do_lim_safe; do_space_def; op_space_reset_def;
              MEM; THE_DEF; LET_DEF; LET_END_DEF; stack_consumed_def]))])]);;

(* HOL4 line 8683 (local) *)
let LENGTH_n2mw_1 = prove
 (`!n. LENGTH ((n2mw n):(A word)list) = 1 <=> ~(n = 0) /\ n < dimword (:A)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[n2mw_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = 1)`; ARITH_RULE `SUC k = 1 <=> k = 0`;
                  LENGTH_EQ_NIL; n2mw_NIL] THEN
  SIMP_TAC[DIV_EQ_0; LBIGAUX_DIMWORD_NZ]);;

(* HOL4 line 8691 (local) *)
let WordFromInt_DIV_LEMMA = prove
 (`!kk B. kk < B * B /\ 0 < B ==> B * (kk DIV B) <= B * B - B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `kk DIV B < B` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIV_LT_X]; ALL_TAC] THEN
  TRANS_TAC LE_TRANS `B * (B - 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES; LE_REFL]]);;

(* HOL4 line 8700 (local) *)
let explode_less_32 = prove
 (`!P. (!n. n < 32 ==> P (n:num)) <=>
       P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\
       P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17 /\ P 18 /\ P 19 /\
       P 20 /\ P 21 /\ P 22 /\ P 23 /\ P 24 /\ P 25 /\ P 26 /\ P 27 /\ P 28 /\ P 29 /\
       P 30 /\ P 31`,
  GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 8711 (local) *)
let LESS_IMP_NOT_BIT = prove
 (`!k n. n < 2 EXP k ==> ~numbit k n`,
  SIMP_TAC[numbit; DIV_LT; ODD]);;

(* HOL4 line 8717 *)
let data_to_word_assignProof_Smallnum_alt = prove
 (`!i. Smallnum i =
       if i < &0 then word_shl (word_sub (word 0) (word (num_of_int (--i)))) 2
       else word_shl (word (num_of_int i)) 2:A word`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_Smallnum_def; WORD_MUL_LSL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `num_of_int (&4 * (&0 - i)) = 4 * num_of_int (--i)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL] THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `(i:int) < &0 ==> &0 <= &4 * (&0 - i)`;
                   INT_ARITH `(i:int) < &0 ==> &0 <= --i`] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_MUL] THEN CONV_TAC WORD_RULE;
    SUBGOAL_THEN `num_of_int (&4 * i) = 4 * num_of_int i` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL] THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `~((i:int) < &0) ==> &0 <= &4 * i`;
                   INT_ARITH `~((i:int) < &0) ==> &0 <= i`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_MUL] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 8726 (local) *)
let ASP4AUX_NUMBIT_MOD_EQ = prove
 (`!n a b. a MOD 2 EXP (n + 1) = b MOD 2 EXP (n + 1) ==> (numbit n a <=> numbit n b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `n + 1`; `a:num`] NUMBIT_MOD_2EXP) THEN
  MP_TAC(SPECL [`n:num`; `n + 1`; `b:num`] NUMBIT_MOD_2EXP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN MESON_TAC[]);;

let ASP4AUX_SUB_CONG = prove
 (`!a b i p u v. a + i = p * u /\ b + i = p * v ==> (a == b) (mod p)`,
  NUMBER_TAC);;

let BIT_lemma = prove
 (`!n k i.
     numbit n (2 EXP k - i) <=>
     if n < k /\ i < 2 EXP k /\ ~(i = 0)
     then numbit n (2 EXP (MAX n i + 1) - i)
     else numbit n (2 EXP k - i)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `i < 2 EXP (MAX n i + 1)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP i` THEN REWRITE_TAC[LT_POW2_REFL; LE_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ASP4AUX_NUMBIT_MOD_EQ THEN REWRITE_TAC[GSYM CONG] THEN
  MATCH_MP_TAC ASP4AUX_SUB_CONG THEN EXISTS_TAC `i:num` THEN
  EXISTS_TAC `2 EXP (k - (n + 1))` THEN EXISTS_TAC `2 EXP ((MAX n i + 1) - (n + 1))` THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[SUB_ADD; LT_IMP_LE; ARITH_RULE `n < k ==> (n + 1) + k - (n + 1) = k`;
               ARITH_RULE `(n + 1) + (MAX n i + 1) - (n + 1) = MAX n i + 1`]);;

(* HOL4 line 8749 (local) *)
let BIT_Lemma2 = prove
 (`!m k n.
     numbit m (2 EXP k - n) =
     if ~(n = 0) /\ n <= 2 EXP m /\ m < k then T else numbit m (2 EXP k - n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `numbit m (2 EXP k - n) <=> numbit m (2 EXP (m + 1) - n)` SUBST1_TAC THENL
   [MATCH_MP_TAC ASP4AUX_NUMBIT_MOD_EQ THEN REWRITE_TAC[GSYM CONG] THEN
    MATCH_MP_TAC ASP4AUX_SUB_CONG THEN EXISTS_TAC `n:num` THEN
    EXISTS_TAC `2 EXP (k - (m + 1))` THEN EXISTS_TAC `1` THEN
    REWRITE_TAC[GSYM EXP_ADD; MULT_CLAUSES] THEN
    SUBGOAL_THEN `n <= 2 EXP k /\ n <= 2 EXP (m + 1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN TRANS_TAC LE_TRANS `2 EXP m` THEN ASM_REWRITE_TAC[LE_EXP] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `m < k ==> (m + 1) + k - (m + 1) = k`];
    ALL_TAC] THEN
  REWRITE_TAC[numbit] THEN
  SUBGOAL_THEN `(2 EXP (m + 1) - n) DIV 2 EXP m = 1` (fun th -> REWRITE_TAC[th; ARITH]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `2 EXP m - n` THEN
  REWRITE_TAC[EXP_ADD; EXP_1] THEN
  MP_TAC(SPEC `m:num` LT_POW2_REFL) THEN ASM_ARITH_TAC);;

(* HOL4: word_exp_set_var_ShiftVar_lemma, in a form for the evaluation    *)
let ASP4AUX_word_exp_ShiftVar = prove
 (CASE_TERM
  `!sh (t:(A,C,FFI)wl_state) v n.
     ~(sh = Ror) /\ ~(n = 0) /\ n < dimindex (:A) ==>
     wl_word_exp t (ShiftVar sh v n) =
     match lookup v (wl_state_locals t) with
       SOME (wl_Word w) -> OPTION_MAP wl_Word (word_sh sh w n)
     | _ -> NONE`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ShiftVar_def; GSYM NOT_LT] THEN
  REWRITE_TAC[wl_word_exp_def; wl_get_var_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word n:A word) = n` SUBST1_TAC THENL
   [REWRITE_TAC[w2n_n2w] THEN MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LT_TRANS `dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dimindex_lt_dimword];
    REWRITE_TAC[]]);;

let ASP4AUX_do_word_app_WordFromInt = prove
 (`!vs r. data_do_word_app WordFromInt vs = SOME r <=>
          ?i. vs = [data_Number i] /\ r = data_Word64 (iword i)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_do_word_app_def; option_DISTINCT; NOT_CONS_NIL] THEN
  CASES_ON `h:data_v` THEN REWRITE_TAC[data_do_word_app_def; option_DISTINCT; CONS_11;
    distinctness "data_v"; injectivity "data_v"] THEN
  CASES_ON `t:data_v list` THEN
  REWRITE_TAC[data_do_word_app_def; option_DISTINCT; option_INJ; NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let ASP4AUX_do_app_WordFromInt = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp WordFromInt) vs s = Rval (v,s2) <=>
     ?i. vs = [data_Number i] /\ 3 <= data_state_space s /\ v = data_Word64 (iword i) /\
         s2 = do_stack (WordOp WordFromInt) vs
                (do_lim_safe (data_state_space_fupd (K (data_state_space s - 3)) s)
                   (WordOp WordFromInt) vs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_do_app_def; distinctness "clos_op"; MEM; do_space_def;
              op_space_reset_def; op_space_req_def; consume_space_def; ARITH_EQ] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN
  ASM_CASES_TAC `data_state_space (s:(C,FFI)data_state) < 3` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[distinctness "result"] THEN
  REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `data_do_word_app WordFromInt vs` THEN
  CASE_REWRITE_TAC[distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASP4AUX_do_word_app_WordFromInt]) THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `data_do_word_app WordFromInt vs = NONE` THEN
    ASM_REWRITE_TAC[data_do_word_app_def; option_DISTINCT];
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[CONS_11; injectivity "data_v"] THEN MESON_TAC[]]);;

let ASP4AUX_join_env_locals_EVEN = prove
 (`!(sl:A spt) (L1:B spt) L2.
     (!k. EVEN k ==> lookup k L1 = lookup k L2) ==>
     join_env_locals sl L1 = join_env_locals sl L2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[join_env_locals_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[inter_eq; lookup_inter_alt] THEN
  X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[domain_adjust_set_EVEN]);;

let ASP4AUX_state_rel_W64_end = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest wv sp1 nf m' locals'
    vs op sp2.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s) sp1
       (wl_state_store t |+ (NextFree,nf)) m' (wl_state_mdomain t)
       (APPEND (join_env_locals (insert dest wv (data_state_locals s)) locals')
          (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
             (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t)))) /\
     (!n. IS_SOME (lookup n (data_state_locals s)) ==>
          IS_SOME (lookup (adjust_var n) locals')) /\
     IS_SOME (lookup (adjust_var dest) locals') /\
     lookup 0 locals' = lookup 0 (wl_state_locals t) /\ sp2 <= sp1 ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest wv
          (do_stack op vs (do_lim_safe (data_state_space_fupd (K sp2) s) op vs)))
       (wl_state_store_fupd (K (wl_state_store t |+ (NextFree,nf)))
          (wl_state_memory_fupd (K m') (wl_state_locals_fupd (K locals') t))) NONE locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN
  REWRITE_TAC[data_set_var_def; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
              data_state_INFO.ri_accfupds; data_state_INFO.ri_fupdfupds; K_THM; K_o_THM;
              wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds] THEN
  ASM_REWRITE_TAC[code_oracle_rel_NextFree; FLOOKUP_UPDATE; distinctness "store_name";
                  FDOM_FUPDATE; IN_INSERT; ALL; option_le_max_right] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `nn:num` THEN REWRITE_TAC[lookup_insert] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND; GSYM APPEND_ASSOC; FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
  MATCH_MP_TAC memory_rel_less_space THEN EXISTS_TAC `sp1:num` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `nf:A word_loc`)) (concl th) &&
    (let h,_ = strip_comb (concl th) in is_const h && fst(dest_const h) = "memory_rel"))) THEN
  REWRITE_TAC[join_env_locals_def; APPEND]);;

let ASP4AUX_WordFromInt_W64 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs L1 header dest w vs op.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     3 <= data_state_space s /\ dimindex (:A) = 64 /\ encode_header c 3 1 = SOME header /\
     lookup 3 L1 = SOME (wl_Word w) /\
     (!k. EVEN k ==> lookup k L1 = lookup k (wl_state_locals t)) ==>
     ?r. wl_evaluate (WriteWord64 c header dest 3,wl_state_locals_fupd (K L1) t) = (NONE,r) /\
         data_to_word_gcProof_state_rel c l1 l2
           (data_set_var dest (data_Word64 (word_zx w))
              (do_stack op vs (do_lim_safe
                 (data_state_space_fupd (K (data_state_space s - 3)) s) op vs)))
           r NONE locs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`;
    `wl_state_locals_fupd (K L1) (t:(A,C,FFI)wl_state)`;
    `data_state_locals (s:(C,FFI)data_state)`;
    `APPEND [(the_global (data_state_global (s:(C,FFI)data_state)),
              FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)]
       (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))`;
    `3`; `w:A word`; `header:A word`; `dest:num`] evaluate_WriteWord64) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def] THEN
  SUBGOAL_THEN `join_env_locals (data_state_locals (s:(C,FFI)data_state)) (L1:(A word_loc)spt) =
                join_env_locals (data_state_locals s) (wl_state_locals (t:(A,C,FFI)wl_state))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ASP4AUX_join_env_locals_EVEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[join_env_locals_def] THEN
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel);
      ASM_ARITH_TAC;
      X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `lookup (adjust_var nn) (L1:(A word_loc)spt) =
                    lookup (adjust_var nn) (wl_state_locals (t:(A,C,FFI)wl_state))`
        SUBST1_TAC THENL [ASM_MESON_TAC[EVEN_adjust_var]; ALL_TAC] THEN
      ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nf:A word_loc` (X_CHOOSE_THEN `m1:A word->A word_loc`
    (X_CHOOSE_THEN `lc:(A word_loc)spt` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1; wl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  MATCH_MP_TAC ASP4AUX_state_rel_W64_end THEN
  EXISTS_TAC `data_state_space (s:(C,FFI)data_state) - 2` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `lookup 0 (lc:(A word_loc)spt) = lookup 0 (L1:(A word_loc)spt)` THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ARITH];
    ARITH_TAC]);;

let ASP4AUX_WordFromInt_W32 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs L1 header dest src1 src2
    (w:int64) vs op.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     3 <= data_state_space s /\ dimindex (:A) = 32 /\ encode_header c 3 2 = SOME header /\
     ~(src1 = 1) /\ ~(src2 = 1) /\
     lookup src1 L1 = SOME (wl_Word (word_extract 31 0 w)) /\
     lookup src2 L1 = SOME (wl_Word (word_extract 63 32 w)) /\
     (!k. EVEN k ==> lookup k L1 = lookup k (wl_state_locals t)) ==>
     ?r. wl_evaluate (WriteWord64_on_32 c header dest src1 src2,
                      wl_state_locals_fupd (K L1) t) = (NONE,r) /\
         data_to_word_gcProof_state_rel c l1 l2
           (data_set_var dest (data_Word64 w)
              (do_stack op vs (do_lim_safe
                 (data_state_space_fupd (K (data_state_space s - 3)) s) op vs)))
           r NONE locs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`;
    `wl_state_locals_fupd (K L1) (t:(A,C,FFI)wl_state)`;
    `data_state_locals (s:(C,FFI)data_state)`;
    `APPEND [(the_global (data_state_global (s:(C,FFI)data_state)),
              FAPPLY (wl_state_store (t:(A,C,FFI)wl_state)) Globals)]
       (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))`;
    `src1:num`; `src2:num`; `w:int64`; `header:A word`; `dest:num`]
    evaluate_WriteWord64_on_32) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def] THEN
  SUBGOAL_THEN `join_env_locals (data_state_locals (s:(C,FFI)data_state)) (L1:(A word_loc)spt) =
                join_env_locals (data_state_locals s) (wl_state_locals (t:(A,C,FFI)wl_state))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ASP4AUX_join_env_locals_EVEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[join_env_locals_def] THEN
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel);
      ASM_ARITH_TAC;
      X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `lookup (adjust_var nn) (L1:(A word_loc)spt) =
                    lookup (adjust_var nn) (wl_state_locals (t:(A,C,FFI)wl_state))`
        SUBST1_TAC THENL [ASM_MESON_TAC[EVEN_adjust_var]; ALL_TAC] THEN
      ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nf:A word_loc` (X_CHOOSE_THEN `m1:A word->A word_loc`
    (X_CHOOSE_THEN `lc:(A word_loc)spt` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1; wl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  MATCH_MP_TAC ASP4AUX_state_rel_W64_end THEN
  EXISTS_TAC `data_state_space (s:(C,FFI)data_state) - 3` THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  UNDISCH_TAC `lookup 0 (lc:(A word_loc)spt) = lookup 0 (L1:(A word_loc)spt)` THEN
  DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ARITH]);;

let ASP4AUX_encode_header_3 = prove
 (`!c len. good_dimindex (:A) /\ data_to_word_config_len_size c + 7 < dimindex (:A) /\
           1 < data_to_word_config_len_size c /\ len <= 2 ==>
           ?h. encode_header c 3 len = SOME (h:A word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[encode_header_def] THEN
  COND_CASES_TAC THENL [MESON_TAC[]; REWRITE_TAC[option_DISTINCT]] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP 6 <= 2 EXP ((dimindex (:A) - data_to_word_config_len_size c) - 2) /\
                2 EXP 2 <= 2 EXP data_to_word_config_len_size c`
    MP_TAC THENL
   [REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dimword (:A) DIV 16 = 2 EXP (dimindex (:A) - 4) /\ 16 <= dimword (:A) DIV 16`
    MP_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let ASP4AUX_W64_small = prove
 (`!i. dimindex(:A) = 64 /\ small_int (:A) i ==>
       (word_zx (word_ishr (Smallnum i:A word) 2):int64) = iword i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w] THEN
  SUBGOAL_THEN `!x:A word. (word_zx x:int64) = word_sx x` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_SX_ZX THEN
    ASM_REWRITE_TAC[DIMINDEX_64; LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[word_sx] THEN AP_TERM_TAC THEN REWRITE_TAC[IVAL_WORD_ISHR] THEN
  SUBGOAL_THEN `ival (iword (&4 * i):A word) = &4 * i` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN
    UNDISCH_TAC `small_int (:A) i` THEN
    ASM_REWRITE_TAC[small_int_def; dimword_def] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC INT_REDUCE_CONV THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  MATCH_MP_TAC(CONJUNCT2 INT_DIV_MUL) THEN INT_ARITH_TAC);;

let ASP4AUX_W64_pos = prove
 (`!i. dimindex(:A) = 64 /\ &0 <= i ==>
       (word_zx (word (num_of_int (abs i)):A word):int64) = iword i`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` SUBST1_TAC o GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS]) THEN
  REWRITE_TAC[INT_ABS_NUM; NUM_OF_INT_OF_NUM; GSYM WORD_IWORD] THEN
  MATCH_MP_TAC WORD_ZX_WORD_SIMPLE THEN ASM_REWRITE_TAC[DIMINDEX_64; LE_REFL]);;

let ASP4AUX_W64_neg = prove
 (`!i. dimindex(:A) = 64 /\ i < &0 ==>
       (word_zx (word_sub (word 0) (word (num_of_int (abs i))):A word):int64) = iword i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. (i:int) = --(&n)` (X_CHOOSE_THEN `n:num` SUBST1_TAC) THENL
   [EXISTS_TAC `num_of_int (--i)` THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `i:int < &0 ==> &0 <= --i`; INT_NEG_NEG];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM; IWORD_INT_NEG; GSYM WORD_IWORD] THEN
  REWRITE_TAC[WORD_SUB_LZERO] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64] THEN
  SUBGOAL_THEN `!x:A word. val x MOD 2 EXP 64 = val x` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `x:A word` VAL_BOUND) THEN ASM_REWRITE_TAC[dimword_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_NEG; VAL_WORD; dimword_def; DIMINDEX_64]);;

let ASP4AUX_lookup_insert_ODD = prove
 (`!k n (v:A) t. EVEN k /\ ODD n ==> lookup k (insert n v t) = lookup k t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[NOT_EVEN]);;

(* the general (M word result) form of the library WORD_SUBWORD_IWORD, whose *)
(* name is rebound to the N word form in Library/words.ml                   *)
let ASP4AUX_WORD_SUBWORD_IWORD = prove
 (`!x pos len.
        pos + len <= dimindex(:N)
        ==> word_subword (iword x:N word) (pos,len):M word =
            iword((x div &2 pow pos) rem &2 pow len)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUBWORD_AS_IWORD] THEN
  SIMP_TAC[INT_DIV_REM; INT_POW_LE; INT_POS; GSYM INT_POW_ADD] THEN
  ASM_SIMP_TAC[INT_REM_IVAL_IWORD]);;

let ASP4AUX_extract_lo_iword = prove
 (`!i. dimindex(:A) = 32 ==> (word_extract 31 0 (iword i:int64):A word) = iword i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_extract_subword] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SIMP_TAC[ASP4AUX_WORD_SUBWORD_IWORD; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[INT_POW; INT_DIV_1] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IWORD_REM_SIZE]);;

let ASP4AUX_extract_hi_iword = prove
 (`!i. dimindex(:A) = 32 ==>
       (word_extract 63 32 (iword i:int64):A word) = iword (i div &2 pow 32)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_extract_subword] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SIMP_TAC[ASP4AUX_WORD_SUBWORD_IWORD; DIMINDEX_64; ARITH] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IWORD_REM_SIZE]);;

let ASP4AUX_div_small = prove
 (`!x d. &0 < d /\ --d <= x /\ x < d ==> x div d = if x < &0 then -- &1 else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC INT_DIV_UNIQ THEN EXISTS_TAC `x + d:int` THEN ASM_INT_ARITH_TAC;
    REWRITE_TAC[INT_DIV_EQ_0] THEN ASM_INT_ARITH_TAC]);;

let ASP4AUX_W32_small = prove
 (`!i. dimindex(:A) = 32 /\ small_int (:A) i ==>
       word_ishr (Smallnum i:A word) 2 = iword i /\
       word_ishr (Smallnum i:A word) 31 = iword (i div &2 pow 32)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; word_ishr] THEN
  SUBGOAL_THEN `ival (iword (&4 * i):A word) = &4 * i` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN
    UNDISCH_TAC `small_int (:A) i` THEN
    ASM_REWRITE_TAC[small_int_def; dimword_def] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC INT_REDUCE_CONV THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `small_int (:A) i` THEN
  ASM_REWRITE_TAC[small_int_def; dimword_def] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC(CONJUNCT2 INT_DIV_MUL) THEN INT_ARITH_TAC;
    AP_TERM_TAC THEN
    W(fun (_,w) -> let l,r = dest_eq w in
      MP_TAC(SPECL [lhand l; rand l] ASP4AUX_div_small) THEN
      MP_TAC(SPECL [lhand r; rand r] ASP4AUX_div_small)) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[INT_ARITH `&4 * i < &0 <=> i:int < &0`]]);;

let ASP4AUX_word_list_read2 = prove
 (`!(a:N word) (x0:B) x1 xs ff m dm.
     (misc_word_list a (CONS x0 (CONS x1 xs)) STAR ff) (fun2set (m,dm)) ==>
     m (word_add a bytes_in_word) = x1 /\ word_add a bytes_in_word IN dm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[misc_word_list_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC read_fun2set THEN
  EXISTS_TAC `set_sep_one (a:N word,x0:B) STAR
    misc_word_list (word_add (word_add a bytes_in_word) bytes_in_word) xs STAR ff` THEN
  FIRST_X_ASSUM(MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  REWRITE_TAC[STAR_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [STAR_COMM] THEN REFL_TAC);;

let ASP4AUX_memory_rel_len_size_nz = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm vs.
     memory_rel c be ts refs sp st m dm vs ==> ~(data_to_word_config_len_size c = 0)`,
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN MESON_TAC[]);;

let ASP4AUX_n2mw_2 = prove
 (`!n. dimword(:A) <= n ==>
       ?rest. n2mw n:(A word)list = CONS (word n) (CONS (word (n DIV dimword(:A))) rest)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0) /\ ~(n DIV dimword(:A) = 0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; LBIGAUX_DIMWORD_NZ; NOT_LT] THEN
    MP_TAC(INST_TYPE [`:A`,`:N`] ONE_LT_dimword) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN ASM_REWRITE_TAC[CONS_11] THEN
  REWRITE_TAC[dimword_def; WORD_MOD_SIZE] THEN MESON_TAC[]);;

let ASP4AUX_iword_abs = prove
 (`!i. (&0 <= i ==> iword i:N word = word (num_of_int (abs i))) /\
       (i < &0 ==> iword i:N word = word_sub (word 0) (word (num_of_int (abs i))))`,
  GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_SUB_LZERO] THEN REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_NEG] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN AP_TERM_TAC THEN ASM_INT_ARITH_TAC);;

let ASP4AUX_iword_div32 = prove
 (`!i. dimindex(:A) = 32 ==>
       (&0 <= i ==>
        iword (i div &2 pow 32):A word = word (num_of_int (abs i) DIV dimword (:A))) /\
       (i < &0 /\ ~(num_of_int (abs i) = 0) /\ num_of_int (abs i) < dimword (:A) ==>
        iword (i div &2 pow 32):A word = word_not (word 0))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `dimword (:A) = 2 EXP 32` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[dimword_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[WORD_IWORD; GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_POW] THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN ASM_INT_ARITH_TAC;
    SUBGOAL_THEN `i div &2 pow 32 = -- &1` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_DIV_UNIQ THEN EXISTS_TAC `&2 pow 32 + i:int` THEN
      UNDISCH_TAC `num_of_int (abs i) < 2 EXP 32` THEN
      UNDISCH_TAC `~(num_of_int (abs i) = 0)` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_POW] THEN
      SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
      CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[IWORD_INT_NEG; GSYM WORD_IWORD; WORD_NEG_1]]]);;

let ASP4AUX_word_not_plus1 = prove
 (`!x:N word. word (val (word_not x) + 1) = word_neg x`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_NEG; VAL_WORD_NOT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN REWRITE_TAC[dimword_def] THEN ARITH_TAC);;

let ASP4AUX_neg_div = prove
 (`!n d. 0 < d ==>
         --(&n) div &d = if n MOD d = 0 then --(&(n DIV d)) else --(&(n DIV d)) - &1:int`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  MP_TAC(SPECL [`n:num`; `d:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = n DIV d` THEN ABBREV_TAC `r = n MOD d` THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [EXISTS_TAC `&0:int` THEN ASM_REWRITE_TAC[INT_ABS_NUM] THEN
    UNDISCH_TAC `n = q * d + r` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_SIMP_TAC[] THEN INT_ARITH_TAC;
    EXISTS_TAC `&d - &r:int` THEN REWRITE_TAC[INT_ABS_NUM] THEN
    UNDISCH_TAC `n = q * d + r` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
    UNDISCH_TAC `r < d` THEN UNDISCH_TAC `~(r = 0)` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC]);;

let ASP4AUX_neg_hi = prove
 (`!n. dimindex(:A) = 32 ==>
       word (val (word_not (word (n DIV dimword(:A)):A word)) +
             (if (if dimword(:A) <= val (word_not (word n:A word)) + 1
                  then word 1 else word 0:A word) = word 0 then 0 else 1)) =
       iword (--(&n) div &2 pow 32):A word`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 pow 32 = &(dimword(:A)):int` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_POW; dimword_def]; ALL_TAC] THEN
  SIMP_TAC[ASP4AUX_neg_div; ZERO_LT_dimword] THEN
  SUBGOAL_THEN `(dimword(:A) <= val (word_not (word n:A word)) + 1 <=>
                 n MOD dimword(:A) = 0)` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_NOT; VAL_WORD; GSYM dimword_def] THEN
    MP_TAC(SPECL [`n:num`; `dimword(:A)`] MOD_LT_EQ) THEN
    REWRITE_TAC[LBIGAUX_DIMWORD_NZ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(word 1:A word = word 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD; GSYM dimword_def] THEN
    SIMP_TAC[MOD_LT; ONE_LT_dimword] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n MOD dimword(:A) = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; WORD_VAL] THENL
   [REWRITE_TAC[ASP4AUX_word_not_plus1; IWORD_INT_NEG; GSYM WORD_IWORD];
    REWRITE_TAC[IWORD_INT_SUB; IWORD_INT_NEG; GSYM WORD_IWORD] THEN
    REWRITE_TAC[WORD_NOT_AS_SUB]]);;

let asp4_ww32_finish_ext (extra:thm list) (src1:int) (src2:int) : tactic =
  let prog = subst [mk_small_numeral src1,`x1:num`; mk_small_numeral src2,`x2:num`]
               `WriteWord64_on_32 c a dest x1 x2:(A)wl_prog` in
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NOT_LE]) THEN
  W(fun (_,w) -> let st = asp4_callee_state prog w in
    let l1 = rand (rand (rator st)) in
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; l1; `a:A word`; `dest:num`;
      mk_small_numeral src1; mk_small_numeral src2;
      `iword i:int64`; `[data_Number i]`; `WordOp WordFromInt`] ASP4AUX_WordFromInt_W32)) THEN
  ASM_SIMP_TAC[ASP4AUX_extract_lo_iword; ASP4AUX_extract_hi_iword; ARITH] THEN
  (ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[lookup_insert; ARITH] THEN
      ASM_SIMP_TAC(ASP4AUX_iword_abs :: ASP4AUX_iword_div32 :: DIV_LT :: extra);
      REWRITE_TAC[lookup_insert; ARITH] THEN
      ASM_SIMP_TAC(ASP4AUX_iword_abs :: ASP4AUX_iword_div32 :: DIV_LT :: extra);
      X_GEN_TAC `kk:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[ASP4AUX_lookup_insert_ODD; ARITH]];
    ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT];;

let asp4_ww32_finish = asp4_ww32_finish_ext [];;

let asp4_digit2_tac : tactic =
  SUBGOAL_THEN `dimword (:A) <= num_of_int (abs i)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_n2mw_1; NOT_LT]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `rest:(A word)list` o MATCH_MP ASP4AUX_n2mw_2) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_word_list_read2 o
    REWRITE_RULE[ASSUME `n2mw (num_of_int (abs i)):(A word)list =
      CONS (word (num_of_int (abs i))) (CONS (word (num_of_int (abs i) DIV dimword (:A))) rest)`;
      MAP] o check (fun th -> can (find_term (fun u ->
        try fst(dest_const u) = "misc_word_list" with Failure _ -> false)) (concl th))) THEN
  SUBGOAL_THEN `word_add (word_add ad bytes_in_word) bytes_in_word =
                word_add ad (word_mul (word 2) bytes_in_word):A word` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];;

(* HOL4 line 8766 *)
let assign_WordFromInt = prove
 (assign_thm_stmt `op = WordOp WordFromInt`,
  (REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def;
     distinctness "clos_op"; injectivity "clos_op"]) THEN
  UNDISCH_TAC `names_opt:(1 spt)option = NONE` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `data_do_app (WordOp WordFromInt) vals (s:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_WordFromInt] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_WordFromInt_def; LET_DEF; LET_END_DEF] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def])) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP6AUX_MEMREL_LEN_SIZE7) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o CONJ (ASSUME `good_dimindex(:A)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_len_size) THEN
  CASES_ON `encode_header c 3 (if dimindex (:A) < 64 then 2 else 1):(A word)option` THEN
  CASE_REWRITE_TAC[FST]) THENL
  [(MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `t:(A,C,FFI)wl_state`; `locs:(num#num)list`] evaluate_GiveUp2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`SOME NotEnoughSpace:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC[do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds;
              K_THM; lim_safe_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC option_le_trans THEN EXISTS_TAC `wl_state_stack_max (t:(A,C,FFI)wl_state)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC option_le_trans THEN
    EXISTS_TAC `data_state_stack_max (s:(C,FFI)data_state)` THEN
    ASM_REWRITE_TAC[option_le_max_right; option_le_refl];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(1 < data_to_word_config_len_size c)` (fun th -> REWRITE_TAC[th]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `if dimindex (:A) < 64 then 2 else 1`]
    (INST_TYPE [`:A`,`:A`] ASP4AUX_encode_header_3)) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN ARITH_TAC);
   (SUBGOAL_THEN `dimindex(:A) = 64 \/ dimindex(:A) = 32` MP_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun u ->
    try fst(dest_const u) = "encode_header" with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[]) THENL
   [(SUBGOAL_THEN `val (word 2:A word) = 2 /\ ~(2 >= dimindex (:A)) /\ ~(2 = 0)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; dimword_def] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_CASES_TAC `small_int (:A) i`) THENL
    [((FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_IMP
    (CONJ (ASSUME `good_dimindex (:A)`) (CONJ (ASSUME `small_int (:A) i`) th)))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASP4AUX_EV_TAC ASP4AUX_EV_RWS) THEN (MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`;
    `insert 3 (wl_Word (word_ishr (Smallnum i) 2)) (wl_state_locals (t:(A,C,FFI)wl_state))`;
    `a:A word`; `dest:num`; `word_ishr (Smallnum i:A word) 2`; `[data_Number i]`;
    `WordOp WordFromInt`] ASP4AUX_WordFromInt_W64) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  ANTS_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
    is_const h && fst(dest_const h) = "data_to_word_gcProof_state_rel" &&
    can (find_term (fun u -> try fst(dest_const u) = "word_zx" with Failure _ -> false))
      (concl th))) THEN
  ASM_SIMP_TAC[ASP4AUX_W64_small]));
     ((FIRST_ASSUM(MP_TAC o SPECL [`adjust_var a1`; `1`; `3`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] evaluate_LoadBignum)) THEN
  ASM_REWRITE_TAC[wl_get_var_def; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A word` (X_CHOOSE_THEN `junk:A word_loc` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `bit 0 (w:A word)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASP4AUX_EV_TAC (wl_set_vars_def :: alist_insert_def :: ASP4AUX_EV_RWS)) THEN (SUBGOAL_THEN `word_and h (word 16) = word 0:A word <=> &0 <= (i:int)` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[WORD_AND_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (i:int)` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN (W(fun (_,w) -> let st = asp4_callee_state `WriteWord64 c a dest 3:(A)wl_prog` w in
    let l1t = rand (rator st) in let l1 = rand l1t in
    let wv = rand (rand (rator l1)) in
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; l1; `a:A word`; `dest:num`; wv;
      `[data_Number i]`; `WordOp WordFromInt`] ASP4AUX_WordFromInt_W64)) THEN
  (ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[lookup_insert];
      X_GEN_TAC `kk:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[ASP4AUX_lookup_insert_ODD; ARITH]];
    ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
    is_const h && fst(dest_const h) = "data_to_word_gcProof_state_rel" &&
    can (find_term (fun u -> try fst(dest_const u) = "word_zx" with Failure _ -> false))
      (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NOT_LE]) THEN
  ASM_SIMP_TAC[ASP4AUX_W64_pos; ASP4AUX_W64_neg]))];
    (SUBGOAL_THEN `val (word 2:A word) = 2 /\ ~(2 >= dimindex (:A)) /\ ~(2 = 0) /\
                val (word 31:A word) = 31 /\ ~(31 >= dimindex (:A)) /\ ~(31 = 0)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; dimword_def] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_CASES_TAC `small_int (:A) i`) THENL
    [((FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_IMP
    (CONJ (ASSUME `good_dimindex (:A)`) (CONJ (ASSUME `small_int (:A) i`) th)))) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP4AUX_EV_TAC ASP4AUX_EV_RWS) THEN (W(fun (_,w) -> let st = asp4_callee_state `WriteWord64_on_32 c a dest 3 5:(A)wl_prog` w in
    let l1 = rand (rand (rator st)) in
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; l1; `a:A word`; `dest:num`; `3`; `5`;
      `iword i:int64`; `[data_Number i]`; `WordOp WordFromInt`] ASP4AUX_WordFromInt_W32)) THEN
  ASM_SIMP_TAC[ASP4AUX_extract_lo_iword; ASP4AUX_extract_hi_iword; ASP4AUX_W32_small; ARITH]) THEN (ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[lookup_insert; ARITH];
      REWRITE_TAC[lookup_insert; ARITH];
      X_GEN_TAC `kk:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[ASP4AUX_lookup_insert_ODD; ARITH]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT]));
     ((FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP memory_rel_Number_bignum_IMP_ALT
    (CONJ th (CONJ (ASSUME `~small_int (:A) i`) (ASSUME `good_dimindex (:A)`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:((A word#A word_loc)->bool)->bool` (X_CHOOSE_THEN `w2:A word`
    (X_CHOOSE_THEN `xh:A word` (X_CHOOSE_THEN `ad:A word` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o REWRITE_RULE[injectivity "word_loc"] o check (fun th ->
    concl th = `wl_Word (w:A word) = wl_Word w2`)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `adjust_var a1`; `t:(A,C,FFI)wl_state`; `w:A word`;
                 `ad:A word`] get_var_get_real_addr_lemma) THEN
  ASM_REWRITE_TAC[wl_get_var_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(32 - data_to_word_config_len_size c = 0) /\
                32 - data_to_word_config_len_size c < 32 /\
                ~(32 - data_to_word_config_len_size c >= 32) /\
                32 - data_to_word_config_len_size c < dimindex (:A)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_memory_rel_len_size_nz) THEN
    UNDISCH_TAC `data_to_word_config_len_size c + 7 < dimindex (:A)` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (xh:A word) (32 - data_to_word_config_len_size c) =
                word (LENGTH (n2mw (num_of_int (abs i)):(A word)list))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun u ->
      try fst(dest_const u) = "decode_length" with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[decode_length_def];
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP4AUX_EV_TAC (ASP4AUX_word_exp_ShiftVar :: WORD_ADD_0 :: ASP4AUX_EV_RWS)) THEN (SUBGOAL_THEN `LENGTH (n2mw (num_of_int (abs i)):(A word)list) MOD dimword (:A) =
                LENGTH (n2mw (num_of_int (abs i)):(A word)list)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(num_of_int (abs i) = 0) /\ &(num_of_int (abs i)) = abs (i:int)`
    STRIP_ASSUME_TAC THENL
   [SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    UNDISCH_TAC `~small_int (:A) i` THEN ASM_REWRITE_TAC[small_int_def; dimword_def] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH (n2mw (num_of_int (abs i)):(A word)list) = 1` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `&0 <= (i:int)` THEN ASM_REWRITE_TAC[]) THENL
      [(SUBGOAL_THEN `num_of_int (abs i) < dimword (:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_n2mw_1]; ALL_TAC] THEN
  asp4_ww32_finish 5 9);
       (SUBGOAL_THEN `num_of_int (abs i) < dimword (:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_n2mw_1]; ALL_TAC] THEN
  asp4_ww32_finish 5 9);
       ((asp4_digit2_tac) THEN (asp4_ww32_finish 5 9));
       ((asp4_digit2_tac) THEN (ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: word_add_carry_def :: LET_DEF ::
     LET_END_DEF :: WORD_XOR_0 :: WORD_XOR_NOT0 :: ASP4AUX_EV_RWS)) THEN (SUBGOAL_THEN `--(&(num_of_int (abs i))) = i:int` ASSUME_TAC THENL
   [UNDISCH_TAC `&(num_of_int (abs i)) = abs (i:int)` THEN
    UNDISCH_TAC `~(&0 <= (i:int))` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `num_of_int (abs i)` (MATCH_MP ASP4AUX_neg_hi (ASSUME `dimindex(:A) = 32`))) THEN
  REWRITE_TAC[ASSUME `--(&(num_of_int (abs i))) = i:int`] THEN DISCH_TAC THEN
  asp4_ww32_finish_ext [ASP4AUX_word_not_plus1; WORD_SUB_LZERO] 15 19))])]]]);;

(* HOL4 line 9238 *)
let assign_TagEq = prove
 (assign_thm_stmt `(?tag. op = BlockOp (TagEq tag))`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `tag:num` SUBST1_TAC) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def;
     distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op"]) THEN
  UNDISCH_TAC `names_opt:(1 spt)option = NONE` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `data_do_app (BlockOp (TagEq tag)) vals (s:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_TagEq] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts5:num` (X_CHOOSE_THEN `t5:num` (X_CHOOSE_THEN `l5:data_v list`
    STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_TagEq_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  DRULE_ALL memory_rel_Block_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `t5 < dimword(:A) DIV 16` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN
    STRIP_TAC THEN ASM_MESON_TAC[encode_header_tag_mask];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[FST] THENL
   [ALL_TAC;
    (* HOL4: reverse IF_CASES_TAC THEN1 (eval_tac ...) *)
    SUBGOAL_THEN `~(t5:num = tag)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN ASP4AUX_NONE_TAC THEN
    REWRITE_TAC[GSYM wl_set_var_def] THEN
    MATCH_MP_TAC ASP4AUX_state_rel_do_stack_set_var THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC memory_rel_Boolv_F THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl) THEN REWRITE_TAC[]] THEN
  REWRITE_TAC[data_to_word_list_Seq_def; LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC `w = word_add (word_mul (word t5) (word 16)) (word 2):A word` THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_SIMP_TAC[ASP4AUX_word_16; ASP4AUX_word_16_eq];
    SUBGOAL_THEN `!z. wl_word_exp (wl_state_locals_fupd (K (insert 1 z (wl_state_locals t)))
                                    (t:(A,C,FFI)wl_state)) (real_addr c (adjust_var a1)) =
                      SOME (wl_Word a)` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
                      adjust_var_NEQ];
      ALL_TAC] THEN
    DRULE_ALL encode_header_tag_mask THEN STRIP_TAC THEN
    ASP4AUX_EV_TAC (ASP4AUX_word_16_eq :: ASP4AUX_EV_RWS)] THEN
  COND_CASES_TAC THEN ASP4AUX_NONE_TAC THEN
  MATCH_MP_TAC ASP4AUX_state_rel_do_stack_set_var_1 THEN ASM_REWRITE_TAC[] THEN
  (MATCH_MP_TAC memory_rel_Boolv_T ORELSE MATCH_MP_TAC memory_rel_Boolv_F) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP memory_rel_tl) THEN REWRITE_TAC[]);;

(* HOL4 line 9306 *)
let ASP4AUX_ptr_bits_bit = prove
 (`!c tag len i.
     i < dimindex(:A) /\ bit i (ptr_bits c tag len:A word) ==>
     1 <= i /\ i < data_to_word_config_len_bits c + data_to_word_config_tag_bits c + 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ptr_bits_def; BIT_WORD_OR] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] maxout_bits_bit)) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let all_ones_get_addr = prove
 (`!c ptr tag2 len2.
     word_and (all_ones (data_to_word_config_len_bits c +
                         (data_to_word_config_tag_bits c + 1)) 0)
       (get_addr c ptr (wl_Word (ptr_bits c tag2 len2))) =
     word_or (ptr_bits c tag2 len2) (word 1):A word`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[get_addr_def; get_lowerbits_def; small_shift_length_def; shift_length_def] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIT_WORD_AND; BIT_WORD_OR; all_ones_bit; BIT_WORD_SHL; BIT_WORD_BITS;
               BIT_WORD_1; ADD_CLAUSES] THEN
  ASM_CASES_TAC `bit i (ptr_bits c tag2 len2:A word)` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `tag2:num`; `len2:num`; `i:num`]
      ASP4AUX_ptr_bits_bit) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ARITH_TAC]);;

(* HOL4 line 9341 *)
let MULT_TWO_EXP_LESS_dimword = prove
 (`!b l n. b + l <= dimindex (:A) /\ n < 2 EXP b ==> n * 2 EXP l < dimword (:A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dimword_def] THEN
  TRANS_TAC LTE_TRANS `2 EXP b * 2 EXP l` THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD; LE_EXP] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 9354 *)
let ASP4AUX_word_shl_eq = prove
 (`!b l m n. b + l <= dimindex(:A) /\ m < 2 EXP b /\ n < 2 EXP b ==>
             (word_shl (word m) l = (word_shl (word n) l:A word) <=> m = n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SHL_WORD; n2w_11] THEN
  SUBGOAL_THEN `2 EXP l * m < dimword(:A) /\ 2 EXP l * n < dimword(:A)` STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN CONJ_TAC THEN MATCH_MP_TAC MULT_TWO_EXP_LESS_dimword THEN
    EXISTS_TAC `b:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]);;

let maxout_bits_eq = prove
 (`!b l n n'.
     b + l <= dimindex (:A) /\ n' < 2 EXP b - 1 ==>
     (maxout_bits n b l = (maxout_bits n' b l:A word) <=> n = n')`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n:num = n'` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[maxout_bits_def] THEN
  SUBGOAL_THEN `all_ones (l + b) l = word_shl (word (2 EXP b - 1)) l:A word` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[all_ones_n2w]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`b:num`; `l:num`; `n:num`; `n':num`] ASP4AUX_word_shl_eq);
    MP_TAC(ISPECL [`b:num`; `l:num`; `2 EXP b - 1`; `n':num`] ASP4AUX_word_shl_eq)] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THEN TRY ASM_ARITH_TAC THEN
  DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 9373 *)
let word_or_eq_word_or_split = prove
 (`!w1 w2 v1 v2:A word.
     word_and w1 w2 = word 0 /\ word_and v1 v2 = word 0 /\
     word_and w1 v2 = word 0 /\ word_and v1 w2 = word 0 ==>
     ((word_or w1 w2 = word_or v1 v2) <=> (w1 = v1 /\ w2 = v2))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_0] THEN
  MESON_TAC[]);;

(* HOL4 line 9382 *)
let ptr_bits_eq_ptr_bits = prove
 (`!tag c len tag2 len2.
     tag < 2 EXP data_to_word_config_tag_bits c - 1 /\
     len < 2 EXP data_to_word_config_len_bits c - 1 /\
     data_to_word_config_len_bits c + data_to_word_config_tag_bits c < dimindex (:A) ==>
     ((word_or (ptr_bits c tag2 len2) (word 1) =
       word_or (ptr_bits c tag len) (word 1:A word)) <=>
      (tag2 = tag /\ len2 = len))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ptr_bits_or_1_add_1; WORD_EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[ptr_bits_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `maxout_bits tag2 (data_to_word_config_tag_bits c) (1 + data_to_word_config_len_bits c) =
    (maxout_bits tag (data_to_word_config_tag_bits c) (1 + data_to_word_config_len_bits c)
      :A word) /\
    maxout_bits len2 (data_to_word_config_len_bits c) 1 =
    (maxout_bits len (data_to_word_config_len_bits c) 1:A word)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC word_or_eq_word_or_split THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] maxout_bits_bit))) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    BINOP_TAC THEN MATCH_MP_TAC maxout_bits_eq THEN ASM_ARITH_TAC]);;

(* HOL4 line 9408 *)
let maxout_bits_0 = prove
 (`!b e. maxout_bits 0 b e = word 0:A word`,
  REPEAT GEN_TAC THEN REWRITE_TAC[maxout_bits_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_SHL_0] THEN
  SUBGOAL_THEN `b = 0` SUBST_ALL_TAC THENL
   [MP_TAC(SPEC `b:num` LT_POW2_REFL) THEN ASM_ARITH_TAC;
    REWRITE_TAC[all_ones_def; ADD_CLAUSES; LE_REFL]]);;

(* HOL4 line 9417 *)
let ptr_bits_eq_ptr_bits_len_only = prove
 (`!len c len2.
     len < 2 EXP data_to_word_config_len_bits c - 1 /\
     data_to_word_config_len_bits c < dimindex (:A) ==>
     ((word_or (ptr_bits c 0 len2) (word 1) =
       word_or (ptr_bits c 0 len) (word 1:A word)) <=>
      (len2 = len))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ptr_bits_or_1_add_1; WORD_EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[ptr_bits_def; maxout_bits_0; WORD_OR_0] THEN
  MATCH_MP_TAC maxout_bits_eq THEN ASM_ARITH_TAC);;

(* HOL4 line 9429 *)
let ASP4AUX_memory_rel_Block_ptr = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag l w rest.
     memory_rel c be ts refs sp st m dm (CONS (data_Block ts' tag l, w) rest) /\
     ~(l = []) ==>
     ?ptr. w = wl_Word (get_addr c ptr (wl_Word (ptr_bits c tag (LENGTH l))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def; MAP] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    is_const t && fst(dest_const t) = "v_inv")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    is_const t && fst(dest_const t) = "word_addr")) (concl th))) THEN
  DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC `hs:(((A)word_loc)heap_address)list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN ASM_REWRITE_TAC[v_inv_def] THEN STRIP_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `ptr:num` THEN
  UNDISCH_TAC `word_addr c (h:((A)word_loc)heap_address) = w` THEN
  ASM_REWRITE_TAC[word_addr_def] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[injectivity "word_loc"] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LIST_REL_LENGTH o check (fun th ->
    try rand(rator(concl th)) = `l:data_v list` with Failure _ -> false)) THEN
  SIMP_TAC[]);;

let assign_TagLenEq = prove
 (assign_thm_stmt `(?tag len. op = BlockOp (clos_TagLenEq tag len))`,
  ASP4AUX_BLOCK_OP_INTRO_TAC
    (DISCH_THEN(X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `len:num` SUBST1_TAC)))
    ASP4AUX_do_app_TagLenEq assign_TagLenEq_def THEN
  DRULE_ALL memory_rel_tag_limit THEN DISCH_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [(* HOL4: len = 0 case *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[FST] THENL
     [DRULE_ALL memory_rel_test_nil_eq THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      ASP4AUX_EV_TAC ASP4AUX_EV_RWS;
      SUBGOAL_THEN `~(t5:num = tag /\ LENGTH (l5:data_v list) = 0)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASP4AUX_EV_TAC ASP4AUX_EV_RWS] THEN
    TRY COND_CASES_TAC THEN ASP4AUX_BOOLV_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[FST] THENL
   [(* HOL4: tag < 2 ** tag_bits - 1 /\ len < 2 ** len_bits - 1 *)
    DRULE_ALL memory_rel_Block_IMP THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `(word_and w (all_ones ((data_to_word_config_len_bits c +
                              data_to_word_config_tag_bits c) + 1) 0) =
       word_or (ptr_bits c tag len) (word 1):A word) <=>
      (t5:num = tag /\ LENGTH (l5:data_v list) = len)` ASSUME_TAC THENL
     [ASM_CASES_TAC `l5:data_v list = []` THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[LENGTH] THEN
        STRIP_TAC THEN UNDISCH_TAC `~bit 0 (w:A word)` THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `bit 0:A word->bool`) THEN
        ASM_REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_1; DIMINDEX_GT_0];
        ALL_TAC] THEN
      DRULE_ALL ASP4AUX_memory_rel_Block_ptr THEN
      DISCH_THEN(X_CHOOSE_THEN `ptr:num` MP_TAC) THEN
      ASM_REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[GSYM ADD_ASSOC; all_ones_get_addr] THEN
      MATCH_MP_TAC ptr_bits_eq_ptr_bits THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `shift_length c < dimindex(:A)` THEN REWRITE_TAC[shift_length_def] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN COND_CASES_TAC THEN ASP4AUX_BOOLV_TAC;
    ALL_TAC] THEN
  (* HOL4: CASE_TAC on encode_header *)
  CASES_ON `encode_header c (4 * tag) len:(A word)option` THEN CASE_REWRITE_TAC[] THENL
   [DRULE_ALL memory_rel_test_none_eq THEN DISCH_TAC THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN ASP4AUX_BOOLV_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  DRULE_ALL memory_rel_Block_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(word 0 = a:A word) /\ ~(t5:num = tag /\ LENGTH (l5:data_v list) = len)`
      STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH] THEN ASM_MESON_TAC[encode_header_NEQ_0]; ALL_TAC] THEN
    UNDISCH_TAC `w = word_add (word_mul (word t5) (word 16)) (word 2):A word` THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN DISCH_TAC;
    SUBGOAL_THEN `!z. wl_word_exp (wl_state_locals_fupd (K (insert 1 z (wl_state_locals t)))
                                    (t:(A,C,FFI)wl_state)) (real_addr c (adjust_var a1)) =
                      SOME (wl_Word a')` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
                      adjust_var_NEQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:A word = a) <=> (t5:num = tag /\ LENGTH (l5:data_v list) = len)`
      ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:data_to_word_config`; `4 * t5`; `LENGTH (l5:data_v list)`;
                     `4 * tag`; `len:num`; `x:A word`; `a:A word`] encode_header_EQ) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS] THEN
  TRY COND_CASES_TAC THEN ASP4AUX_BOOLV_TAC);;

(* HOL4 line 9540 *)
let all_ones_and_1 = prove
 (`!k. ~(k = 0) ==> word_and (all_ones k 0) (word 1) = word 1:A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_1] THEN
  ASM_SIMP_TAC[all_ones_bit] THEN ASM_ARITH_TAC);;

(* HOL4 line 9546 *)
let all_ones_and_ptr_bits_tag_0 = prove
 (`!c tag len.
     word_and (all_ones (data_to_word_config_len_bits c + 1) 0) (ptr_bits c tag len) =
     ptr_bits c 0 len:A word`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; ptr_bits_def; maxout_bits_0; WORD_OR_0;
              BIT_WORD_AND; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[all_ones_bit] THEN
  ASM_CASES_TAC `bit i (maxout_bits len (data_to_word_config_len_bits c) 1:A word)` THEN
  ASM_CASES_TAC `bit i (maxout_bits tag (data_to_word_config_tag_bits c)
                          (1 + data_to_word_config_len_bits c):A word)` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] maxout_bits_bit))) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 9555 *)
let ASP4AUX_all_ones_get_addr_len = prove
 (`!c ptr tag2 len2.
     word_and (get_addr c ptr (wl_Word (ptr_bits c tag2 len2)))
       (all_ones (data_to_word_config_len_bits c + 1) 0) =
     word_or (ptr_bits c 0 len2) (word 1):A word`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `ptr:num`; `tag2:num`; `len2:num`]
    (INST_TYPE [`:A`,`:A`] all_ones_get_addr)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `tag2:num`; `len2:num`]
    (INST_TYPE [`:A`,`:A`] all_ones_and_ptr_bits_tag_0)) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_1] THEN
  DISCH_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_SIMP_TAC[all_ones_bit; LE_0] THEN
  ASM_CASES_TAC `i < data_to_word_config_len_bits c + 1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i < data_to_word_config_len_bits c + data_to_word_config_tag_bits c + 1`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONV_TAC TAUT;
    SUBGOAL_THEN `~(i = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC TAUT]);;

let assign_LenEq = prove
 (assign_thm_stmt `(?len. op = BlockOp (clos_LenEq len))`,
  ASP4AUX_BLOCK_OP_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `len:num` SUBST1_TAC))
    ASP4AUX_do_app_LenEq assign_LenEq_def THEN
  DRULE_ALL memory_rel_Block_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(~bit 0 (w:A word)) <=> (l5:data_v list = [])` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (l5:data_v list) < dimword(:A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LENGTH; ZERO_LT_dimword] THEN
    TRANS_TAC LTE_TRANS `2 EXP (dimindex(:A) - 4)` THEN ASM_REWRITE_TAC[dimword_def; LE_EXP] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [(* HOL4: len = 0 case *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FST] THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN COND_CASES_TAC THEN ASP4AUX_BOOLV_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[FST] THENL
   [(* HOL4: len < 2 ** len_bits - 1 *)
    SUBGOAL_THEN `(word_and w (all_ones (data_to_word_config_len_bits c + 1) 0) =
                   word_or (ptr_bits c 0 len) (word 1):A word) <=>
                  LENGTH (l5:data_v list) = len` ASSUME_TAC THENL
     [ASM_CASES_TAC `l5:data_v list = []` THENL
       [SUBGOAL_THEN `~(LENGTH (l5:data_v list) = len) /\ ~bit 0 (w:A word)`
          (fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THENL
         [ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `bit 0:A word->bool`) THEN
        ASM_REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_1; DIMINDEX_GT_0];
        ALL_TAC] THEN
      DRULE_ALL ASP4AUX_memory_rel_Block_ptr THEN
      DISCH_THEN(X_CHOOSE_THEN `ptr:num` MP_TAC) THEN
      ASM_REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ASP4AUX_all_ones_get_addr_len] THEN
      MATCH_MP_TAC ptr_bits_eq_ptr_bits_len_only THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `shift_length c < dimindex(:A)` THEN REWRITE_TAC[shift_length_def] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN COND_CASES_TAC THEN ASP4AUX_BOOLV_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[FST] THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(LENGTH (l5:data_v list) = len)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN ASP4AUX_BOOLV_TAC] THEN
  (* HOL4: len < dimword: compare the decoded length of the header *)
  REWRITE_TAC[data_to_word_list_Seq_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `(word 0 = word len:A word) <=> F` ASSUME_TAC THENL
   [REWRITE_TAC[n2w_11] THEN ASM_SIMP_TAC[MOD_LT; ZERO_LT_dimword] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(word (LENGTH (l5:data_v list)) = word len:A word) <=> LENGTH l5 = len`
    ASSUME_TAC THENL
   [REWRITE_TAC[n2w_11] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(LENGTH (l5:data_v list) = len)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `w:A word`)) THEN
    ASP4AUX_EV_TAC ASP4AUX_EV_RWS THEN ASP4AUX_BOOLV_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `t:(A,C,FFI)wl_state`; `w:A word`; `a:A word`;
                 `a1:num`] word_exp_real_addr) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (word (dimindex (:A) - data_to_word_config_len_size c):A word) =
                dimindex (:A) - data_to_word_config_len_size c /\
                ~(dimindex (:A) - data_to_word_config_len_size c >= dimindex (:A))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[w2n_n2w] THEN MATCH_MP_TAC MOD_LT THEN
      MP_TAC(INST_TYPE [`:A`,`:N`] dimindex_lt_dimword) THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr x (dimindex(:A) - data_to_word_config_len_size c) =
                word (LENGTH (l5:data_v list)):A word` ASSUME_TAC THENL
   [ASM_MESON_TAC[decode_length_def]; ALL_TAC] THEN
  ASP4AUX_EV_TAC (word_sh_def :: ASP4AUX_EV_RWS) THEN
  COND_CASES_TAC THEN ASP4AUX_BOOLV_TAC);;

(* HOL4 line 9679 *)
let state_rel_upd_safe_pkheap = prove
 (`!c l1 l2 (s:(C,FFI)data_state) lcl hpk (r:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K lcl) (data_state_space_fupd (K 0)
          (data_state_stack_max_fupd (K NONE) s))) r NONE locs <=>
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K lcl) (data_state_stack_max_fupd (K NONE)
          (data_state_space_fupd (K 0) (data_state_safe_for_space_fupd (K F)
             (data_state_peak_heap_length_fupd (K hpk) s))))) r NONE locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 lines 9692-9704: vals eval_Call_Add .. eval_Call_Mod (HOL4:         *)
(* Q.SPEC k eval_Call_Arith |> SIMP_RULE std_ss [int_op_def,               *)
(* Arith_location_def]); here the same derivation with the kit's simplifier *)
let eval_Call_Add = CAKE_SIMP_RULE
  [data_to_word_bignumProof_int_op_def; data_to_word_bignumProof_Arith_location_def]
  (SPEC `0` eval_Call_Arith);;

let eval_Call_Sub = CAKE_SIMP_RULE
  [data_to_word_bignumProof_int_op_def; data_to_word_bignumProof_Arith_location_def]
  (SPEC `1` eval_Call_Arith);;

let eval_Call_Mul = CAKE_SIMP_RULE
  [data_to_word_bignumProof_int_op_def; data_to_word_bignumProof_Arith_location_def]
  (SPEC `4` eval_Call_Arith);;

let eval_Call_Div = CAKE_SIMP_RULE
  [data_to_word_bignumProof_int_op_def; data_to_word_bignumProof_Arith_location_def]
  (SPEC `5` eval_Call_Arith);;

let eval_Call_Mod = CAKE_SIMP_RULE
  [data_to_word_bignumProof_int_op_def; data_to_word_bignumProof_Arith_location_def]
  (SPEC `6` eval_Call_Arith);;

(* HOL4 line 9707 *)
let state_rel_ignore_safe_for_space = prove
 (`!c l1 l2 (x:(C,FFI)data_state) l s m (r:(A,C,FFI)wl_state) t locs.
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K l) (data_state_space_fupd (K s)
          (data_state_safe_for_space_fupd (K m) x))) r t locs <=>
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K l) (data_state_space_fupd (K s) x)) r t locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds; K_THM]);;

let _ = cake_add_simps [state_rel_ignore_safe_for_space];;

(* HOL4 line 9715 *)
let state_rel_peak_heap_length = prove
 (`!c l1 l2 (x:(C,FFI)data_state) l s m (r:(A,C,FFI)wl_state) t locs.
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K l) (data_state_space_fupd (K s)
          (data_state_peak_heap_length_fupd (K m) x))) r t locs <=>
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_locals_fupd (K l) (data_state_space_fupd (K s) x)) r t locs`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds; K_THM]);;

let _ = cake_add_simps [state_rel_peak_heap_length];;

(* HOL4 line 9723 (simp; the same statement as the local theorem of line   *)
(* 5392, rebinds the name)                                                   *)
let opt_map_plus_zero_id = prove
 (`!n. OPTION_MAP2 (+) (SOME 0) n = (n:num option)`,
  GEN_TAC THEN CASES_ON `n:num option` THEN REWRITE_TAC[OPTION_MAP2_THM; ADD_CLAUSES]);;

let _ = cake_add_simps [opt_map_plus_zero_id];;

(* HOL4 line 9729 *)
let small_num_small_int = prove
 (`good_dimindex (:A) ==> small_num (dimindex (:A) = 64) = small_int (:A)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; small_num_def; small_int_def; dimword_def] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[]);;

let _ = cake_add_simps [small_num_small_int];;

(* HOL4 line 9737 *)
let memory_rel_small_int = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm i (w:A word) vars.
     memory_rel c be ts refs sp st m dm (CONS (data_Number i,wl_Word w) vars) /\
     bit 0 w /\ good_dimindex (:A) ==>
     ~small_int (:A) i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `i:int`; `wl_Word (w:A word)`;
                 `vars:(data_v#A word_loc)list`] memory_rel_Number_IMP) THEN
  ASM_REWRITE_TAC[injectivity "word_loc"] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `bit 0 (Smallnum i:A word)` THEN
  REWRITE_TAC[word_bit_test; EXP] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[data_to_word_memoryProof_Smallnum_bits]);;

(* HOL4 line 9748 *)
let small_int_Smallnum_add = prove
 (`!i1 i2. good_dimindex(:A) /\ small_int(:A) (i1 + i2) ==>
           word_add (Smallnum i1) (Smallnum i2):A word = Smallnum (i1 + i2)`,
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; word_i2w_add; INT_ADD_LDISTRIB]);;

(* HOL4 line 9756 *)
let small_int_INT_MIN_MAX = prove
 (`!i. good_dimindex(:A) /\ small_int (:A) i ==>
       (integer_word_INT_MIN (:A) <= &4 * i /\ &4 * i <= integer_word_INT_MAX (:A))`,
  GEN_TAC THEN
  REWRITE_TAC[small_int_def; good_dimindex_def; integer_word_INT_MIN_def;
              integer_word_INT_MAX_def; INT_MIN_def; dimword_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC);;

(* HOL4 line 9765 *)
let small_int_w2i_Smallnum_add = prove
 (`!i1 i2.
     good_dimindex(:A) /\
     small_int (:A) (i1 + i2) /\
     small_int (:A) i1 /\
     small_int (:A) i2 ==>
     ival (word_add (Smallnum i1) (Smallnum i2):A word) =
     ival (Smallnum i1:A word) + ival (Smallnum i2:A word)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[small_int_Smallnum_add] THEN
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w] THEN
  ASM_SIMP_TAC[w2i_i2w; small_int_INT_MIN_MAX] THEN INT_ARITH_TAC);;

(* HOL4 line 9779 *)
let data_to_word_assignProof_OPTION_MAP2_NONE = prove
 (`!(f:A->B->C) n m. (OPTION_MAP2 f NONE n = NONE) /\ (OPTION_MAP2 f m NONE = NONE)`,
  REWRITE_TAC[OPTION_MAP2_DEF; IS_SOME_DEF]);;

let _ = cake_add_simps [data_to_word_assignProof_OPTION_MAP2_NONE];;

(* HOL4 line 9785 *)
let state_rel_IMP_arch_64_bit = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) xs locs.
     data_to_word_gcProof_state_rel c l1 l2 s t xs locs ==>
     (limits_arch_64_bit (data_state_limits s) = (dimindex (:A) = 64))`,
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; limits_inv_def] THEN MESON_TAC[]);;

(* HOL4 line 9792 *)
let cut_state_opt_twice = prove
 (`!names_opt (s:(C,FFI)data_state) x.
     data_cut_state_opt names_opt s = SOME x ==> data_cut_state_opt names_opt x = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ASP4AUX_cut_state_opt_SOME] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; UNWIND_THM1] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; data_state_INFO.ri_fupdfupds; K_THM;
              domain_mk_wf; domain_inter] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM] THEN
  SIMP_TAC[spt_eq_thm; wf_mk_wf] THEN
  REWRITE_TAC[lookup_mk_wf; lookup_inter_alt] THEN MESON_TAC[]);;

(* HOL4 line 9802 *)
let cut_state_opt_extra_const = prove
 (`!names_opt (s:(C,FFI)data_state) x.
     data_cut_state_opt names_opt s = SOME x ==>
     data_state_stack_frame_sizes s = data_state_stack_frame_sizes x /\
     data_state_locals_size s = data_state_locals_size x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ASP4AUX_cut_state_opt_SOME] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds]);;

(* ------------------------------------------------------------------------- *)
(* Helpers of the proofs for Add, Sub, Mult, Div and Mod: do_app with a     *)
(* space reset, the fast path (small numbers) and the call of the bignum    *)
(* code (HOL4: eval_Call_Add .. eval_Call_Mod and the reasoning after it).  *)
(* ------------------------------------------------------------------------- *)
let ASP4AUX_DV_CASES_TAC (v:term) : tactic =
  REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (ISPEC v (case_info_of_tyname "data_v").ci_nchotomy);;

let ASP4AUX_LIST_CASES_TAC (v:term) (h:term) (t:term) : tactic =
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN h (X_CHOOSE_THEN t SUBST1_TAC))
    (ISPEC v list_CASES);;

(* proves  data_do_int_app iop vs = SOME r <=> ?n1 n2. vs = [..] /\ ...      *)
let ASP4AUX_INT_APP_TAC : tactic =
  REPEAT GEN_TAC THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [REWRITE_TAC[data_do_int_app_def; option_DISTINCT; NOT_CONS_NIL]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
    REWRITE_TAC[data_do_int_app_def; option_DISTINCT; CONS_11; NOT_CONS_NIL];
    ALL_TAC] THEN
  ASP4AUX_DV_CASES_TAC `x1:data_v` THEN ASP4AUX_DV_CASES_TAC `x2:data_v` THEN
  REWRITE_TAC[data_do_int_app_def; option_DISTINCT; CONS_11; NOT_CONS_NIL;
              distinctness "data_v"; injectivity "data_v"] THEN
  TRY(ASP4AUX_LIST_CASES_TAC `t2:data_v list` `x3:data_v` `t3:data_v list` THEN
      REWRITE_TAC[data_do_int_app_def; option_DISTINCT; CONS_11; NOT_CONS_NIL;
                  distinctness "data_v"; injectivity "data_v"; option_INJ]) THEN
  MESON_TAC[];;

let ASP4AUX_int_app_Add = prove
 (`!vs r. data_do_int_app clos_Add vs = SOME r <=>
          ?n1 n2. vs = [data_Number n1; data_Number n2] /\ r = data_Number (n1 + n2)`,
  ASP4AUX_INT_APP_TAC);;

(* proves the do_app equation of an operator with a space reset          *)
let ASP4AUX_DO_APP_ARITH_TAC op_tm int_th : tactic =
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [op_tm; `vs:data_v list`; `s:(C,FFI)data_state`] ASP4AUX_DO_APP_RESET) THEN
  REWRITE_TAC[op_space_reset_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "int_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[case_eq "option"; distinctness "result"; injectivity "result"; PAIR_EQ;
              int_th] THEN
  MESON_TAC[];;

let ASP4AUX_do_app_Add = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp clos_Add) vs s = Rval (v,s2) <=>
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\ v = data_Number (n1 + n2) /\
             s2 = do_stack (IntOp clos_Add) vs
                    (do_lim_safe (THE (do_space (IntOp clos_Add) vs s)) (IntOp clos_Add) vs)`,
  ASP4AUX_DO_APP_ARITH_TAC `IntOp clos_Add` ASP4AUX_int_app_Add);;

(* ASP1AUX_state_rel_set_var with the space of s2 in memory_rel           *)
let ASP4AUX_state_rel_set_var_sp = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w
    (s2:(C,FFI)data_state).
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
     data_state_global s2 = data_state_global s /\
     IS_SOME (data_state_tstamps s2) /\
     option_le (data_state_stack_max s) (data_state_stack_max s2) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s2)) (data_state_refs s2)
       (data_state_space s2) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_set_var (adjust_var dest) w t) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_set_var_def; wl_set_var_def] THEN SIMP[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_insert; adjust_var_NEQ; adjust_var_11] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[option_le_trans];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC memory_rel_insert THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

(* the end of the fast path of Add, Sub, ...: dest := a small number, the  *)
(* word variables 3 and 1 overwritten                                       *)
let ASP4AUX_state_rel_arith_fast = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest i op vs y3 y1.
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\ op_space_reset op /\
     small_int (:A) i ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest (data_Number i)
          (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs)))
       (wl_state_locals_fupd (K (insert (adjust_var dest) (wl_Word (Smallnum i))
          (insert 3 y3 (insert 1 y1 (wl_state_locals t))))) t) NONE locs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `x:(C,FFI)data_state`;
                 `wl_state_locals_fupd (K (insert 3 y3 (insert 1 y1 (wl_state_locals t))))
                    (t:(A,C,FFI)wl_state)`;
                 `locs:(num#num)list`; `dest:num`; `data_Number i`;
                 `wl_Word (Smallnum i:A word)`;
                 `do_stack op vs (do_lim_safe (THE (do_space op vs (x:(C,FFI)data_state)))
                    op vs)`] ASP4AUX_state_rel_set_var_sp) THEN
  ASM_REWRITE_TAC[state_rel_insert_3_1; wl_set_var_def; wl_state_INFO.ri_accfupds;
                  wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[do_space_def; THE_DEF; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                  data_state_INFO.ri_accfupds; K_THM; option_le_max_right; option_le_refl] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  ASM_SIMP_TAC[inter_insert_ODD_adjust_set_alt; ARITH_ODD] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC memory_rel_zero_space THEN EXISTS_TAC `data_state_space (x:(C,FFI)data_state)` THEN
  ASM_MESON_TAC[ASP1AUX_state_rel_memory_rel]);;

let ASP4AUX_memory_rel_Number2_small = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 n2 v1 v2 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number n1,wl_Word v1) (CONS (data_Number n2,wl_Word v2) vars)) /\
     ~bit 0 v1 /\ ~bit 0 v2 ==>
     small_int (:A) n1 /\ small_int (:A) n2 /\ v1 = Smallnum n1 /\ v2 = Smallnum n2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n1:int`; `v1:A word`;
                 `CONS (data_Number n2,wl_Word (v2:A word)) vars`]
    ASP4AUX_memory_rel_Number_small) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n2:int`; `v2:A word`;
                 `CONS (data_Number n1,wl_Word (v1:A word)) vars`]
    ASP4AUX_memory_rel_Number_small) THEN
  ASM_SIMP_TAC[memory_rel_swap]);;

(* pair_CASE e (\a b. t)  -->  (\(a,b). t) e  (the form of eval_Call_Arith) *)
let ASP4AUX_PAIR_CASE_GABS_CONV : conv = fun tm ->
  let f,args = strip_comb tm in
  if not (is_const f && fst (dest_const f) = "pair_CASE") || length args <> 2
  then failwith "ASP4AUX_PAIR_CASE_GABS_CONV" else
  let e = el 0 args and lam = el 1 args in
  let a,b1 = dest_abs lam in
  let b,t = dest_abs b1 in
  let rhs = mk_comb (mk_gabs (mk_pair (a,b),t),e) in
  let p = genvar (type_of e) in
  let th = prove (mk_forall (p, mk_eq (subst [p,e] tm, subst [p,e] rhs)),
                  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
                  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]) in
  SPEC e th;;

let ASP4AUX_option_add_rot = prove
 (`!a b c. OPTION_MAP2 (+) (a:num option) (OPTION_MAP2 (+) b c) =
           OPTION_MAP2 (+) c (OPTION_MAP2 (+) a b)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a:num option` option_nchotomy) THEN
  STRUCT_CASES_TAC(ISPEC `b:num option` option_nchotomy) THEN
  STRUCT_CASES_TAC(ISPEC `c:num option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_INJ] THEN ARITH_TAC);;

(* the call of the bignum code (HOL4: the part of assign_Add .. assign_Mod *)
(* after drule eval_Call_Add .. eval_Call_Mod)                              *)
let ASP4AUX_arith_slow = prove
 (`!index iop c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names a1 a2
    i1 i2 x r dest n l.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\ 1 < wl_state_termdep t /\
     data_get_vars [a1; a2] (data_state_locals s) = SOME [data_Number i1; data_Number i2] /\
     data_cut_state_opt (SOME names) s = SOME x /\
     data_to_word_bignumProof_int_op index i1 i2 = SOME r /\
     op_space_reset (IntOp iop) /\
     stack_consumed (data_state_stack_frame_sizes x) (data_state_limits x) (IntOp iop)
        [data_Number i1; data_Number i2] =
       OPTION_MAP2 MAX (lookup (Arith_location index) (data_state_stack_frame_sizes x))
         (max_depth (data_state_stack_frame_sizes x) AnyArith_call_tree) /\
     space_consumed x (IntOp iop) [data_Number i1; data_Number i2] =
       2 * bignum_size (limits_arch_64_bit (data_state_limits x)) i1 +
       2 * bignum_size (limits_arch_64_bit (data_state_limits x)) i2 /\
     (lim_safe (data_state_limits x) (IntOp iop) [data_Number i1; data_Number i2] ==>
      bignum_size (limits_arch_64_bit (data_state_limits x)) i1 +
      bignum_size (limits_arch_64_bit (data_state_limits x)) i2 <=
      2 EXP limits_length_limit (data_state_limits x)) ==>
     ?q r'.
       (\(res,s1). if res = NONE then wl_evaluate (wl_Move 2 [adjust_var dest,1],s1)
                   else (res,s1))
         (wl_evaluate
           (MustTerminate
             (wl_Call (SOME ([1],adjust_sets (data_to_word_get_names (SOME names)),wl_Skip,n,l))
               (SOME (Arith_location index))
               [adjust_var a1; adjust_var a2] NONE),t)) = (q,r') /\
       (q = SOME NotEnoughSpace ==>
        wl_state_ffi r' = wl_state_ffi t /\
        option_le (wl_state_stack_max r')
          (data_state_stack_max
             (do_stack (IntOp iop) [data_Number i1; data_Number i2]
                (do_lim_safe (THE (do_space (IntOp iop) [data_Number i1; data_Number i2] x))
                   (IntOp iop) [data_Number i1; data_Number i2]))) /\
        (~(data_to_word_config_gc_kind c = data_to_word_None) ==>
         ~data_state_safe_for_space
             (do_stack (IntOp iop) [data_Number i1; data_Number i2]
                (do_lim_safe (THE (do_space (IntOp iop) [data_Number i1; data_Number i2] x))
                   (IntOp iop) [data_Number i1; data_Number i2])))) /\
       (~(q = SOME NotEnoughSpace) ==>
        data_to_word_gcProof_state_rel c l1 l2
          (data_set_var dest (data_Number r)
             (do_stack (IntOp iop) [data_Number i1; data_Number i2]
                (do_lim_safe (THE (do_space (IntOp iop) [data_Number i1; data_Number i2] x))
                   (IntOp iop) [data_Number i1; data_Number i2]))) r' NONE locs /\
        q = NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`index:num`; `r:int`; `c:data_to_word_config`; `l1:num`; `l2:num`;
                 `s:(C,FFI)data_state`; `t:(A,C,FFI)wl_state`; `locs:(num#num)list`;
                 `SOME (names:1 spt)`; `a1:num`; `a2:num`; `i1:int`; `i2:int`;
                 `x:(C,FFI)data_state`; `dest:num`; `n:num`; `l:num`] eval_Call_Arith) THEN
  ASM_REWRITE_TAC[option_DISTINCT; data_to_word_list_Seq_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `r':(A,C,FFI)wl_state`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`q:((A)wl_result)option`; `r':(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:(C,FFI)data_state) = data_state_locals_fupd (K (mk_wf (sptree_inter (data_state_locals s) (names:1 spt))))
                      (s:(C,FFI)data_state)` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[cut_state_opt_SOME_eq]; ALL_TAC] THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) NONE locs` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[data_to_word_gcProof_state_rel_thm] th)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP stack_rel_IMP_size_of_stack o check (fun th ->
    can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "data_to_word_gcProof_stack_rel")) (concl th))) THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_state_INFO.ri_accfupds; K_THM]) THEN
  ASM_REWRITE_TAC[do_stack_def; do_lim_safe; do_space_def; THE_DEF; LET_DEF; LET_END_DEF;
                  data_state_INFO.ri_accfupds; K_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `wl_state_stack_size (t:(A,C,FFI)wl_state) =
                                        data_state_stack_frame_sizes (s:(C,FFI)data_state)`;
                              ASSUME `wl_state_locals_size (t:(A,C,FFI)wl_state) =
                                        data_state_locals_size (s:(C,FFI)data_state)`;
                              ASSUME `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)) =
                                        size_of_stack (data_state_stack (s:(C,FFI)data_state))`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ISPECL
    [`size_of_stack (data_state_stack (s:(C,FFI)data_state))`;
     `data_state_locals_size (s:(C,FFI)data_state)`;
     `OPTION_MAP2 MAX (lookup (Arith_location index) (data_state_stack_frame_sizes
         (s:(C,FFI)data_state)))
        (max_depth (data_state_stack_frame_sizes s) AnyArith_call_tree)`]
    ASP4AUX_option_add_rot]) THEN
  SUBGOAL_THEN `limits_length_limit (data_state_limits (s:(C,FFI)data_state)) =
                data_to_word_config_len_size c` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "limits_inv")) (concl th))) THEN
    REWRITE_TAC[limits_inv_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `q = SOME NotEnoughSpace:((A)wl_result)option`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "limits_heap_limit")) (concl th) && is_imp (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "lim_safe")) (concl th) && is_imp (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    lhand(concl th) = `~(q = SOME NotEnoughSpace:((A)wl_result)option)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "data_to_word_gcProof_state_rel")) (concl th) &&
      can (find_term ((=) `r':(A,C,FFI)wl_state`)) (concl th)
    then MP_TAC th else failwith "") THEN
  MATCH_MP_TAC(TAUT `(q <=> p) ==> p ==> q`) THEN
  MATCH_MP_TAC ASP4AUX_state_rel_same_fields THEN
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM]]);;

let ASP4AUX_memory_rel_Number2_bits = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 n2 v1 v2 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number n1,wl_Word v1) (CONS (data_Number n2,wl_Word v2) vars)) ==>
     (bit 0 v1 <=> ~small_int (:A) n1) /\ (bit 0 v2 <=> ~small_int (:A) n2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                   `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                   `dm:A word->bool`; `n1:int`; `wl_Word (v1:A word)`;
                   `CONS (data_Number n2,wl_Word (v2:A word)) vars`]
      memory_rel_any_Number_IMP);
    MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                   `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                   `dm:A word->bool`; `n2:int`; `wl_Word (v2:A word)`;
                   `CONS (data_Number n1,wl_Word (v1:A word)) vars`]
      memory_rel_any_Number_IMP)] THEN
  ASM_SIMP_TAC[memory_rel_swap; injectivity "word_loc"; UNWIND_THM1]);;

let ASP4AUX_not_all_small_add = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 n2 v1 v2 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number n1,wl_Word v1) (CONS (data_Number n2,wl_Word v2) vars)) /\
     ~(ival (word_add v1 v2) = ival v1 + ival v2 /\ ~bit 0 v1 /\ ~bit 0 v2) ==>
     ~(small_int (:A) n1 /\ small_int (:A) n2 /\ small_int (:A) (n1 + n2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_memory_rel_Number2_bits o
    CONJ (ASSUME `good_dimindex(:A)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n1:int`; `n2:int`; `v1:A word`; `v2:A word`;
                 `vars:(data_v#A word_loc)list`] ASP4AUX_memory_rel_Number2_small) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(ival (word_add v1 v2) = ival v1 + ival (v2:A word) /\ ~bit 0 v1 /\
                 ~bit 0 v2)` THEN
  ASM_SIMP_TAC[small_int_w2i_Smallnum_add]);;

(* the state of the first wl_evaluate (MustTerminate _,st) of the goal     *)
let asp4_must_state (w:term) =
  let t = find_term (fun t ->
      try let f,a = dest_comb t in
          (match f with
             Const("wl_evaluate",_) ->
               let p = fst (dest_pair a) in
               is_comb p && (match rator p with Const("MustTerminate",_) -> true
                                               | _ -> false)
           | _ -> false)
      with Failure _ -> false) w in
  snd (dest_pair (rand t));;

(* HOL4 line 9812 *)
let assign_Add = prove
 (assign_thm_stmt `op = IntOp clos_Add`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?names. names_opt = SOME (names:1 spt)`
    (X_CHOOSE_THEN `names:1 spt` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (IntOp clos_Add) <=> names_opt:(1 spt)option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:(1 spt)option` THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DRULE_ALL state_rel_cut_state_opt_SOME THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (IntOp clos_Add) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_Add] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `n2:int` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `LENGTH (args:num list) = LENGTH [data_Number n1; data_Number n2]` THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Add_def; FST] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
  DRULE memory_rel_Number_IMP_Word_2 THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF :: ASP4AUX_EV_RWS) THEN
  ASM_CASES_TAC `ival (word_add v1 v2) = ival v1 + ival (v2:A word) /\ ~bit 0 (v1:A word) /\
                 ~bit 0 (v2:A word)` THEN
  REWRITE_TAC[BIT_WORD_OR; word_bit_if_1_0; BIT_WORD_0; DE_MORGAN_THM; DIMINDEX_GT_0] THEN
  ASM_REWRITE_TAC[] THENL
   [(* HOL4: IF_CASES_TAC THEN1: the fast path *)
    CASE_REWRITE_TAC[] THEN
  ASP4AUX_EV_TAC (wl_get_vars_def :: wl_set_vars_def :: alist_insert_def :: MAP :: ASP4AUX_EV_RWS) THEN
    ASP4AUX_NONE_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    SUBGOAL_THEN `~bit 0 (word_add v1 v2:A word)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CONJUNCT1 BIT_WORD_ADD_CLAUSES]; ALL_TAC] THEN
    DRULE_ALL memory_rel_Add THEN
    DISCH_THEN(fun mr -> MP_TAC(MATCH_MP ASP4AUX_memory_rel_Number_small
       (end_itlist CONJ [ASSUME `good_dimindex(:A)`; mr;
                   ASSUME `~bit 0 (word_add v1 v2:A word)`]))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ASP4AUX_state_rel_arith_fast THEN ASM_REWRITE_TAC[op_space_reset_def];
    (* the call of the bignum code *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_arch_64_bit o check (fun th ->
      can (find_term ((=) `x:(C,FFI)data_state`)) (concl th) &&
      can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "data_to_word_gcProof_state_rel")) (concl th))) THEN
    SUBGOAL_THEN `~(small_int (:A) n1 /\ small_int (:A) n2 /\ small_int (:A) (n1 + n2))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC ASP4AUX_not_all_small_add THEN
      MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV ASP4AUX_PAIR_CASE_GABS_CONV) THEN
    W(fun (_,w) -> MP_TAC(ISPECL [`0`; `clos_Add`; `c:data_to_word_config`; `l1:num`; `l2:num`;
      `s:(C,FFI)data_state`; asp4_must_state w; `locs:(num#num)list`; `names:1 spt`;
      `a1:num`; `a2:num`; `n1:int`; `n2:int`; `x:(C,FFI)data_state`; `n1 + n2:int`;
      `dest:num`; `n:num`; `l:num`] ASP4AUX_arith_slow)) THEN
    REWRITE_TAC[data_to_word_bignumProof_Arith_location_def; data_to_word_bignumProof_int_op_def;
                ARITH_EQ; wl_state_INFO.ri_accfupds; K_THM; state_rel_insert_3_1;
                op_space_reset_def] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < n <=> n > 1`] THEN
      REWRITE_TAC[stack_consumed_def; space_consumed_def; lim_safe_def; LET_DEF; LET_END_DEF] THEN
      ASM_SIMP_TAC[small_num_small_int];
      ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC]);;

(* HOL4 line 9966 *)
let small_int_Smallnum_sub = prove
 (`!i1 i2. good_dimindex(:A) /\ small_int(:A) (i1 - i2) ==>
           word_sub (Smallnum i1) (Smallnum i2):A word = Smallnum (i1 - i2)`,
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w; word_i2w_sub; INT_SUB_LDISTRIB]);;

(* HOL4 line 9975 *)
let small_int_w2i_Smallnum_sub = prove
 (`!i1 i2.
     good_dimindex(:A) /\ small_int(:A) (i1 - i2) /\ small_int(:A) i1 /\
     small_int(:A) i2 ==>
     ival (word_sub (Smallnum i1) (Smallnum i2):A word) =
     ival (Smallnum i1:A word) - ival (Smallnum i2:A word)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[small_int_Smallnum_sub] THEN
  REWRITE_TAC[data_to_word_memoryProof_Smallnum_i2w] THEN
  ASM_SIMP_TAC[w2i_i2w; small_int_INT_MIN_MAX] THEN INT_ARITH_TAC);;

(* HOL4 line 9992 (local) *)
let word_bit_0_sub_lemma = prove
 (`!w1 w2:A word.
     ~bit 0 w1 /\ ~bit 0 w2 ==> ~bit 0 (word_add w1 (word_mul (word_neg (word 1)) w2))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_mul (word_neg (word 1)) w2 = word_neg w2:A word` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT1 BIT_WORD_ADD_CLAUSES; CONJUNCT1 BIT_WORD_NEG_CLAUSES] THEN
  MESON_TAC[]);;

let ASP4AUX_int_app_Sub = prove
 (`!vs r. data_do_int_app clos_Sub vs = SOME r <=>
          ?n1 n2. vs = [data_Number n1; data_Number n2] /\ r = data_Number (n1 - n2)`,
  ASP4AUX_INT_APP_TAC);;

let ASP4AUX_do_app_Sub = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp clos_Sub) vs s = Rval (v,s2) <=>
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\ v = data_Number (n1 - n2) /\
             s2 = do_stack (IntOp clos_Sub) vs
                    (do_lim_safe (THE (do_space (IntOp clos_Sub) vs s)) (IntOp clos_Sub) vs)`,
  ASP4AUX_DO_APP_ARITH_TAC `IntOp clos_Sub` ASP4AUX_int_app_Sub);;

let ASP4AUX_not_all_small_sub = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 n2 v1 v2 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number n1,wl_Word v1) (CONS (data_Number n2,wl_Word v2) vars)) /\
     ~(ival (word_sub v1 v2) = ival v1 - ival v2 /\ ~bit 0 v1 /\ ~bit 0 v2) ==>
     ~(small_int (:A) n1 /\ small_int (:A) n2 /\ small_int (:A) (n1 - n2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_memory_rel_Number2_bits o
    CONJ (ASSUME `good_dimindex(:A)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n1:int`; `n2:int`; `v1:A word`; `v2:A word`;
                 `vars:(data_v#A word_loc)list`] ASP4AUX_memory_rel_Number2_small) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(ival (word_sub v1 v2) = ival v1 - ival (v2:A word) /\ ~bit 0 v1 /\
                 ~bit 0 v2)` THEN
  ASM_SIMP_TAC[small_int_w2i_Smallnum_sub]);;

(* HOL4 line 10003 *)
let assign_Sub = prove
 (assign_thm_stmt `op = IntOp clos_Sub`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?names. names_opt = SOME (names:1 spt)`
    (X_CHOOSE_THEN `names:1 spt` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (IntOp clos_Sub) <=> names_opt:(1 spt)option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:(1 spt)option` THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DRULE_ALL state_rel_cut_state_opt_SOME THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (IntOp clos_Sub) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_Sub] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `n2:int` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `LENGTH (args:num list) = LENGTH [data_Number n1; data_Number n2]` THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Sub_def; FST] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
  DRULE memory_rel_Number_IMP_Word_2 THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF :: ASP4AUX_EV_RWS) THEN
  ASM_CASES_TAC `ival (word_sub v1 v2) = ival v1 - ival (v2:A word) /\ ~bit 0 (v1:A word) /\
                 ~bit 0 (v2:A word)` THEN
  REWRITE_TAC[BIT_WORD_OR; word_bit_if_1_0; BIT_WORD_0; DE_MORGAN_THM; DIMINDEX_GT_0] THEN
  ASM_REWRITE_TAC[] THENL
   [(* HOL4: IF_CASES_TAC THEN1: the fast path *)
    CASE_REWRITE_TAC[] THEN
  ASP4AUX_EV_TAC (wl_get_vars_def :: wl_set_vars_def :: alist_insert_def :: MAP :: ASP4AUX_EV_RWS) THEN
    ASP4AUX_NONE_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    SUBGOAL_THEN `~bit 0 (word_sub v1 v2:A word)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CONJUNCT1 BIT_WORD_SUB_CLAUSES]; ALL_TAC] THEN
    DRULE_ALL memory_rel_Sub THEN
    DISCH_THEN(fun mr -> MP_TAC(MATCH_MP ASP4AUX_memory_rel_Number_small
       (end_itlist CONJ [ASSUME `good_dimindex(:A)`; mr;
                   ASSUME `~bit 0 (word_sub v1 v2:A word)`]))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ASP4AUX_state_rel_arith_fast THEN ASM_REWRITE_TAC[op_space_reset_def];
    (* the call of the bignum code *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_arch_64_bit o check (fun th ->
      can (find_term ((=) `x:(C,FFI)data_state`)) (concl th) &&
      can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "data_to_word_gcProof_state_rel")) (concl th))) THEN
    SUBGOAL_THEN `~(small_int (:A) n1 /\ small_int (:A) n2 /\ small_int (:A) (n1 - n2))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC ASP4AUX_not_all_small_sub THEN
      MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV ASP4AUX_PAIR_CASE_GABS_CONV) THEN
    W(fun (_,w) -> MP_TAC(ISPECL [`1`; `clos_Sub`; `c:data_to_word_config`; `l1:num`; `l2:num`;
      `s:(C,FFI)data_state`; asp4_must_state w; `locs:(num#num)list`; `names:1 spt`;
      `a1:num`; `a2:num`; `n1:int`; `n2:int`; `x:(C,FFI)data_state`; `n1 - n2:int`;
      `dest:num`; `n:num`; `l:num`] ASP4AUX_arith_slow)) THEN
    REWRITE_TAC[data_to_word_bignumProof_Arith_location_def; data_to_word_bignumProof_int_op_def;
                ARITH_EQ; wl_state_INFO.ri_accfupds; K_THM; state_rel_insert_3_1;
                op_space_reset_def] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < n <=> n > 1`] THEN
      REWRITE_TAC[stack_consumed_def; space_consumed_def; lim_safe_def; LET_DEF; LET_END_DEF] THEN
      ASM_SIMP_TAC[small_num_small_int];
      ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC]);;

(* HOL4 line 10160 *)
let cut_state_opt_IMP_ffi = prove
 (`!names_opt (s:(C,FFI)data_state) x.
     data_cut_state_opt names_opt s = SOME x ==> data_state_ffi x = data_state_ffi s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ASP4AUX_cut_state_opt_SOME] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[data_state_INFO.ri_accfupds]);;

(* HOL4 line 10167 *)
let quad_times_div_half_double = prove
 (`!j. (4 * j) DIV 2 = 2 * (j:num)`,
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC);;

(* HOL4 line 10176 *)
let w2n_mul_less = prove
 (`!(w:A word) (w':A word). (val w * val w') < dimword (:A) EXP 2`,
  REWRITE_TAC[EXP_2] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC LT_MULT2 THEN
  REWRITE_TAC[w2n_lt]);;

(* the word variables at odd keys do not matter for state_rel            *)
let ASP4AUX_state_rel_odd = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs L.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs /\
     (!k. EVEN k ==> lookup k L = lookup k (wl_state_locals t)) ==>
     data_to_word_gcProof_state_rel c l1 l2 s (wl_state_locals_fupd (K L) t) v locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sptree_inter L (adjust_set (data_state_locals (s:(C,FFI)data_state))) =
                sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
                  (adjust_set (data_state_locals s))` SUBST1_TAC THENL
   [SIMP_TAC[spt_eq_thm; wf_inter] THEN REWRITE_TAC[lookup_inter_alt] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[domain_adjust_set_EVEN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[EVEN];
    ASM_MESON_TAC[EVEN_adjust_var]]);;

(* ASP4AUX_state_rel_arith_fast with the number's memory_rel given        *)
let ASP4AUX_state_rel_arith_fast2 = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest i w L op vs.
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\ op_space_reset op /\
     (!k. EVEN k ==> lookup k L = lookup k (wl_state_locals t)) /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps x)) (data_state_refs x) 0
       (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (data_Number i,wl_Word w)
         (APPEND (join_env (data_state_locals x)
                   (toAList (sptree_inter (wl_state_locals t) (adjust_set (data_state_locals x)))))
            (APPEND [(the_global (data_state_global x),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack x) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest (data_Number i)
          (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs)))
       (wl_state_locals_fupd (K (insert (adjust_var dest) (wl_Word w) L)) t) NONE locs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `x:(C,FFI)data_state`;
                 `wl_state_locals_fupd (K L) (t:(A,C,FFI)wl_state)`;
                 `locs:(num#num)list`; `dest:num`; `data_Number i`; `wl_Word (w:A word)`;
                 `do_stack op vs (do_lim_safe (THE (do_space op vs (x:(C,FFI)data_state)))
                    op vs)`] ASP4AUX_state_rel_set_var_sp) THEN
  ASM_SIMP_TAC[ASP4AUX_state_rel_odd; wl_set_var_def; wl_state_INFO.ri_accfupds;
               wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[do_space_def; THE_DEF; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                  data_state_INFO.ri_accfupds; K_THM; option_le_max_right; option_le_refl] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  SUBGOAL_THEN `sptree_inter L (adjust_set (data_state_locals (x:(C,FFI)data_state))) =
                sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
                  (adjust_set (data_state_locals x))` SUBST1_TAC THENL
   [SIMP_TAC[spt_eq_thm; wf_inter] THEN REWRITE_TAC[lookup_inter_alt] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[domain_adjust_set_EVEN];
    ASM_REWRITE_TAC[]]);;

let ASP4AUX_mult_fast_cond = prove
 (`!n1 n2. good_dimindex (:A) /\ small_int (:A) n1 /\ small_int (:A) n2 /\
           &0 <= n1 /\ &0 <= n2 /\ small_int (:A) (n1 * n2) ==>
           word ((val (word_ushr (Smallnum n1:A word) 1) * val (Smallnum n2:A word)) DIV
                 dimword (:A)) = word 0:A word`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_MUL; MP6AUX_SMALL_INT_NUM]) THEN
  REWRITE_TAC[MP6AUX_SMALLNUM_NUM; VAL_WORD_USHR; w2n_n2w] THEN
  SUBGOAL_THEN `8 * (dimword (:A) DIV 8) <= dimword (:A)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `a < d DIV 8 /\ 8 * (d DIV 8) <= d ==> 4 * a < d`] THEN
  REWRITE_TAC[EXP_1; quad_times_div_half_double] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DIV_LT THEN
  UNDISCH_TAC `a * b < dimword (:A) DIV 8` THEN UNDISCH_TAC `8 * (dimword (:A) DIV 8) <= dimword (:A)` THEN
  ARITH_TAC);;

(* HOL4: memory_rel_Number_single_mul after memory_rel_swap               *)
let ASP4AUX_memory_rel_mult = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 n2 v1 v2 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number n1,wl_Word v1) (CONS (data_Number n2,wl_Word v2) vars)) /\
     word_or (word ((val (word_ushr v1 1) * val v2) DIV dimword (:A)))
       (word_and (word 1) (word_or v1 v2)) = word 0 ==>
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (n1 * n2),
              wl_Word (word_ushr (word (val (word_ushr v1 1) * val v2)) 1)) vars)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_swap) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n2:int`; `v2:A word`; `n1:int`; `v1:A word`;
                 `vars:(data_v#A word_loc)list`] memory_rel_Number_single_mul) THEN
  ASM_REWRITE_TAC[single_mul_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; ADD_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_MUL_SYM; MULT_SYM; WORD_OR_SYM; WORD_AND_SYM]) THEN
  REWRITE_TAC[INT_MUL_SYM; MULT_SYM; WORD_OR_SYM; WORD_AND_SYM] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_MUL; WORD_VAL; WORD_MUL_SYM]);;

(* from the memory relation of s to that of the cut state x              *)
let ASP4AUX_memory_rel_cut = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm (s:(C,FFI)data_state) names x
    (L:(A word_loc)spt) hd rest.
     data_cut_state_opt (SOME names) s = SOME x /\
     memory_rel c be ts refs sp st m dm
       (CONS hd (APPEND (join_env (data_state_locals s)
          (toAList (sptree_inter L (adjust_set (data_state_locals s))))) rest)) ==>
     memory_rel c be ts refs 0 st m dm
       (CONS hd (APPEND (join_env (data_state_locals x)
          (toAList (sptree_inter L (adjust_set (data_state_locals x))))) rest))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC memory_rel_zero_space THEN
  EXISTS_TAC `sp:num` THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] memory_rel_rearrange) THEN
  FIRST_ASSUM(fun th -> if is_comb (concl th) && can (find_term (fun t -> is_const t &&
       fst(dest_const t) = "memory_rel")) (concl th) && not (is_imp (concl th))
     then EXISTS_TAC (rand (concl th)) else failwith "") THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MEM; MEM_APPEND] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  MATCH_MP_TAC join_env_submap_MEM THEN
  MAP_EVERY EXISTS_TAC [`data_state_locals (x:(C,FFI)data_state)`; `L:(A word_loc)spt`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; lookup_mk_wf; lookup_inter_alt] THEN
  MESON_TAC[option_DISTINCT]);;

let ASP4AUX_EVEN_NOT_1_3 = prove
 (`!k. EVEN k ==> ~(k = 1) /\ ~(k = 3)`,
  GEN_TAC THEN ASM_CASES_TAC `k = 1` THEN ASM_CASES_TAC `k = 3` THEN
  ASM_REWRITE_TAC[ARITH]);;

let ASP4AUX_not_all_small_mult = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 n2 v1 v2 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number n1,wl_Word v1) (CONS (data_Number n2,wl_Word v2) vars)) /\
     ~(word_or (word ((val (word_ushr v1 1) * val v2) DIV dimword (:A)))
         (word_and (word 1) (word_or v1 v2)) = word 0) ==>
     ~(small_int (:A) n1 /\ &0 <= n1 /\ small_int (:A) n2 /\ &0 <= n2 /\
       small_int (:A) (n1 * n2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_memory_rel_Number2_bits o
    CONJ (ASSUME `good_dimindex(:A)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n1:int`; `n2:int`; `v1:A word`; `v2:A word`;
                 `vars:(data_v#A word_loc)list`] ASP4AUX_memory_rel_Number2_small) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(word_or (word ((val (word_ushr v1 1) * val v2) DIV dimword (:A)))
         (word_and (word 1) (word_or v1 v2)) = word 0:A word)` THEN
  ASM_SIMP_TAC[ASP4AUX_mult_fast_cond; WORD_OR_0] THEN
  REWRITE_TAC[WORD_BITWISE_RULE
    `word_and (word 1) (word_or a b) = word_or (word_and (word 1) a) (word_and (word 1) b):A word`;
    data_to_word_memoryProof_Smallnum_bits; WORD_OR_0]);;

let ASP4AUX_int_app_Mult = prove
 (`!vs r. data_do_int_app Mult vs = SOME r <=>
          ?n1 n2. vs = [data_Number n1; data_Number n2] /\ r = data_Number (n1 * n2)`,
  ASP4AUX_INT_APP_TAC);;

let ASP4AUX_do_app_Mult = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp Mult) vs s = Rval (v,s2) <=>
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\ v = data_Number (n1 * n2) /\
             s2 = do_stack (IntOp Mult) vs
                    (do_lim_safe (THE (do_space (IntOp Mult) vs s)) (IntOp Mult) vs)`,
  ASP4AUX_DO_APP_ARITH_TAC `IntOp Mult` ASP4AUX_int_app_Mult);;

(* HOL4 line 10186 *)
let assign_Mult = prove
 (assign_thm_stmt `op = IntOp Mult`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?names. names_opt = SOME (names:1 spt)`
    (X_CHOOSE_THEN `names:1 spt` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (IntOp Mult) <=> names_opt:(1 spt)option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:(1 spt)option` THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DRULE_ALL state_rel_cut_state_opt_SOME THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (IntOp Mult) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_Mult] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `n2:int` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `LENGTH (args:num list) = LENGTH [data_Number n1; data_Number n2]` THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Mult_def; FST] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
  DRULE memory_rel_Number_IMP_Word_2 THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `1 < dimindex(:A) /\ ~(1 >= dimindex(:A))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
                  ASP4AUX_word_exp_ShiftVar :: word_sh_def :: ASP4AUX_EV_RWS) THEN
  REWRITE_TAC[WORD_OR_0] THEN
  ASM_CASES_TAC `word_or (word ((val (word_ushr v1 1) * val v2) DIV dimword (:A)))
                   (word_and (word 1) (word_or v1 v2)) = word 0:A word` THEN
  ASM_REWRITE_TAC[] THENL
   [(* HOL4: IF_CASES_TAC: the fast path *)
    CASE_REWRITE_TAC[] THEN
    ASP4AUX_EV_TAC (wl_get_vars_def :: wl_set_vars_def :: alist_insert_def :: MAP ::
                    ASP4AUX_EV_RWS) THEN
    ASP4AUX_NONE_TAC THEN
    MATCH_MP_TAC ASP4AUX_state_rel_arith_fast2 THEN
    ASM_REWRITE_TAC[op_space_reset_def; lookup_insert] THEN
    CONJ_TAC THENL [MESON_TAC[ASP4AUX_EVEN_NOT_1_3]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_memory_rel_cut o CONJ
      (ASSUME `data_cut_state_opt (SOME names) (s:(C,FFI)data_state) = SOME x`) o
      MATCH_MP ASP4AUX_memory_rel_mult o CONJ (ASSUME `good_dimindex(:A)`) o
      (fun th -> CONJ th (ASSUME `word_or (word ((val (word_ushr v1 1) * val v2) DIV dimword (:A)))
                     (word_and (word 1) (word_or v1 v2)) = word 0:A word`)) o
      check (fun th -> can (find_term ((=) `data_Number n1`)) (concl th) &&
                       can (find_term ((=) `data_Number n2`)) (concl th))) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM];
    (* the call of the bignum code *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_arch_64_bit o check (fun th ->
      can (find_term ((=) `x:(C,FFI)data_state`)) (concl th) &&
      can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "data_to_word_gcProof_state_rel")) (concl th))) THEN
    SUBGOAL_THEN `~(small_int (:A) n1 /\ &0 <= n1 /\ small_int (:A) n2 /\ &0 <= n2 /\
                    small_int (:A) (n1 * n2))` ASSUME_TAC THENL
     [MATCH_MP_TAC ASP4AUX_not_all_small_mult THEN
      MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV ASP4AUX_PAIR_CASE_GABS_CONV) THEN
    W(fun (_,w) -> MP_TAC(ISPECL [`4`; `Mult`; `c:data_to_word_config`; `l1:num`; `l2:num`;
      `s:(C,FFI)data_state`; asp4_must_state w; `locs:(num#num)list`; `names:1 spt`;
      `a1:num`; `a2:num`; `n1:int`; `n2:int`; `x:(C,FFI)data_state`; `n1 * n2:int`;
      `dest:num`; `n:num`; `l:num`] ASP4AUX_arith_slow)) THEN
    REWRITE_TAC[data_to_word_bignumProof_Arith_location_def; data_to_word_bignumProof_int_op_def;
                ARITH_EQ; wl_state_INFO.ri_accfupds; K_THM; op_space_reset_def] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < n <=> n > 1`] THEN
      REWRITE_TAC[stack_consumed_def; space_consumed_def; lim_safe_def; LET_DEF; LET_END_DEF] THEN
      ASM_SIMP_TAC[small_num_small_int] THEN
      MATCH_MP_TAC ASP4AUX_state_rel_odd THEN ASM_REWRITE_TAC[lookup_insert] THEN
      MESON_TAC[ASP4AUX_EVEN_NOT_1_3];
      ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC]);;

(* HOL4 line 10360 *)
let word_bit_lsr_dimindex_1 = prove
 (`!w1:A word. bit 0 (word_ushr w1 (dimindex (:A) - 1)) <=> word_msb w1`,
  REWRITE_TAC[BIT_WORD_USHR; word_msb_def; ADD_CLAUSES]);;

(* HOL4 line 10366 *)
let state_rel_Number_IMP = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs a1 i1 v1.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_get_var a1 (data_state_locals s) = SOME (data_Number i1) /\
     lookup (adjust_var a1) (wl_state_locals t) = SOME v1 ==>
     ?w1. (v1 = wl_Word w1) /\
          (~(bit 0 w1) <=> small_int (:A) i1) /\
          (~(word_msb w1) /\ ~(bit 0 w1) ==>
           &0 <= i1 /\ w1 = word (4 * num_of_int i1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN STRIP_TAC THEN
  DRULE memory_rel_get_var_IMP THEN
  DISCH_THEN(MP_TAC o SPECL [`a1:num`; `data_Number i1`; `v1:A word_loc`]) THEN
  ASM_REWRITE_TAC[wl_get_var_def] THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_any_Number_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `w:A word` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `small_int (:A) i1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DRULE_ALL memory_rel_Number_word_msb THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_Number_IMP THEN REWRITE_TAC[injectivity "word_loc"] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[data_to_word_Smallnum_def] THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `~((i:int) < &0) ==> &0 <= &4 * i`;
               INT_ARITH `~((i:int) < &0) ==> &0 <= i`]);;

(* HOL4 line 10386 *)
let option_le_add_comm = prove
 (`!a b c. option_le (OPTION_MAP2 (+) a b) c ==> option_le (OPTION_MAP2 (+) b a) c`,
  REPEAT GEN_TAC THEN CASES_ON `a:num option` THEN CASES_ON `b:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM] THEN REWRITE_TAC[ADD_SYM]);;

(* HOL4 line 10393 *)
let IN_adjust_set_IN = prove
 (`!y x:A spt. y IN domain (adjust_set x) ==> (y - 2) DIV 2 IN domain x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [domain_lookup] THEN
  REWRITE_TAC[lookup_adjust_set] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* ASP4AUX_INT_APP_TAC for an operator whose result is guarded by        *)
(* ~(n2 = &0)                                                               *)
let ASP4AUX_INT_APP_COND_TAC : tactic =
  REPEAT GEN_TAC THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [REWRITE_TAC[data_do_int_app_def; option_DISTINCT; NOT_CONS_NIL]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
    REWRITE_TAC[data_do_int_app_def; option_DISTINCT; CONS_11; NOT_CONS_NIL];
    ALL_TAC] THEN
  ASP4AUX_DV_CASES_TAC `x1:data_v` THEN ASP4AUX_DV_CASES_TAC `x2:data_v` THEN
  REWRITE_TAC[data_do_int_app_def; option_DISTINCT; CONS_11; NOT_CONS_NIL;
              distinctness "data_v"; injectivity "data_v"] THEN
  TRY(ASP4AUX_LIST_CASES_TAC `t2:data_v list` `x3:data_v` `t3:data_v list` THEN
      REWRITE_TAC[data_do_int_app_def; option_DISTINCT; CONS_11; NOT_CONS_NIL;
                  distinctness "data_v"; injectivity "data_v"; option_INJ]) THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
  ASM_MESON_TAC[];;

let ASP4AUX_int_app_Div = prove
 (`!vs r. data_do_int_app clos_Div vs = SOME r <=>
          ?n1 n2. vs = [data_Number n1; data_Number n2] /\ ~(n2 = &0) /\
                  r = data_Number (int_div n1 n2)`,
  ASP4AUX_INT_APP_COND_TAC);;

let ASP4AUX_int_app_Mod = prove
 (`!vs r. data_do_int_app clos_Mod vs = SOME r <=>
          ?n1 n2. vs = [data_Number n1; data_Number n2] /\ ~(n2 = &0) /\
                  r = data_Number (integer_int_mod n1 n2)`,
  ASP4AUX_INT_APP_COND_TAC);;

let ASP4AUX_do_app_Div = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp clos_Div) vs s = Rval (v,s2) <=>
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\ ~(n2 = &0) /\
             v = data_Number (int_div n1 n2) /\
             s2 = do_stack (IntOp clos_Div) vs
                    (do_lim_safe (THE (do_space (IntOp clos_Div) vs s)) (IntOp clos_Div) vs)`,
  ASP4AUX_DO_APP_ARITH_TAC `IntOp clos_Div` ASP4AUX_int_app_Div);;

let ASP4AUX_do_app_Mod = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp clos_Mod) vs s = Rval (v,s2) <=>
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\ ~(n2 = &0) /\
             v = data_Number (integer_int_mod n1 n2) /\
             s2 = do_stack (IntOp clos_Mod) vs
                    (do_lim_safe (THE (do_space (IntOp clos_Mod) vs s)) (IntOp clos_Mod) vs)`,
  ASP4AUX_DO_APP_ARITH_TAC `IntOp clos_Mod` ASP4AUX_int_app_Mod);;

let ASP4AUX_msb_or = prove
 (`!a b:A word. word_msb (word_or a b) <=> word_msb a \/ word_msb b`,
  REWRITE_TAC[word_msb_def; BIT_WORD_OR; HB_LT_DIMINDEX]);;

(* the test of assign_Div and assign_Mod: both numbers small and >= 0     *)
let ASP4AUX_div_test = prove
 (`!v1 v2:A word.
     ~bit 0 (word_or (word_or v1 (word_or v2 (word 0)))
               (word_or (word_ushr (word_or v1 (word_or v2 (word 0))) (dimindex (:A) - 1))
                  (word 0))) <=>
     ~bit 0 v1 /\ ~bit 0 v2 /\ ~word_msb v1 /\ ~word_msb v2`,
  REWRITE_TAC[WORD_OR_0] THEN
  REWRITE_TAC[BIT_WORD_OR; DIMINDEX_GT_0; word_bit_lsr_dimindex_1; ASP4AUX_msb_or] THEN
  CONV_TAC TAUT);;

(* ASP4AUX_state_rel_arith_fast with any word variables at odd keys        *)
let ASP4AUX_state_rel_arith_fast3 = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest i L op vs.
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\ op_space_reset op /\
     small_int (:A) i /\
     (!k. EVEN k ==> lookup k L = lookup k (wl_state_locals t)) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest (data_Number i)
          (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs)))
       (wl_state_locals_fupd (K (insert (adjust_var dest) (wl_Word (Smallnum i)) L)) t)
       NONE locs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ASP4AUX_state_rel_arith_fast2 THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC memory_rel_zero_space THEN
  EXISTS_TAC `data_state_space (x:(C,FFI)data_state)` THEN
  ASM_MESON_TAC[ASP1AUX_state_rel_memory_rel]);;

let ASP4AUX_word_div_4 = prove
 (`!k1 k2. 4 * k1 < dimword (:A) /\ 4 * k2 < dimword (:A) /\ ~(k2 = 0) /\
           ~word_msb (word (4 * k1):A word) /\ ~word_msb (word (4 * k2):A word) ==>
           word_jdiv (word (4 * k1):A word) (word (4 * k2)) = word (k1 DIV k2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[word_quot_def] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UDIV; w2n_n2w] THEN
  ASM_SIMP_TAC[MOD_LT; DIV_MULT2; ARITH_EQ] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN TRANS_TAC LET_TRANS `k1:num` THEN
  REWRITE_TAC[DIV_LE] THEN ASM_ARITH_TAC);;

let ASP4AUX_Smallnum_msb = prove
 (`!i. good_dimindex (:A) /\ small_int (:A) i /\ &0 <= i ==> ~word_msb (Smallnum i:A word)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP6AUX_SMALL_INT_NUM]) THEN
  REWRITE_TAC[MP6AUX_SMALLNUM_NUM; word_msb_def; MSB_VAL; NOT_LE; w2n_n2w] THEN
  UNDISCH_TAC `k < dimword (:A) DIV 8` THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN TRANS_TAC LET_TRANS `4 * k` THEN REWRITE_TAC[MOD_LE] THEN
  ASM_ARITH_TAC);;

let ASP4AUX_not_all_small_div = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm n1 n2 v1 v2 vars.
     good_dimindex (:A) /\
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number n1,wl_Word v1) (CONS (data_Number n2,wl_Word v2) vars)) /\
     ~(~bit 0 v1 /\ ~bit 0 v2 /\ ~word_msb v1 /\ ~word_msb v2) ==>
     ~(small_int (:A) n1 /\ &0 <= n1 /\ small_int (:A) n2 /\ &0 <= n2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP4AUX_memory_rel_Number2_bits o
    CONJ (ASSUME `good_dimindex(:A)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
                 `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`;
                 `dm:A word->bool`; `n1:int`; `n2:int`; `v1:A word`; `v2:A word`;
                 `vars:(data_v#A word_loc)list`] ASP4AUX_memory_rel_Number2_small) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(~bit 0 (v1:A word) /\ ~bit 0 (v2:A word) /\ ~word_msb v1 /\ ~word_msb v2)` THEN
  ASM_SIMP_TAC[ASP4AUX_Smallnum_msb]);;

(* state_rel survives a change of the word state that keeps the even     *)
(* keys of the cut locals, the stack and the store (HOL4: the state_rel_thm *)
(* reasoning after a call returns)                                          *)
let ASP4AUX_state_rel_frame = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) t' locs SM.
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\
     wl_state_ffi t' = wl_state_ffi t /\ wl_state_clock t' = wl_state_clock t /\
     wl_state_handler t' = wl_state_handler t /\ wl_state_gc_fun t' = wl_state_gc_fun t /\
     wl_state_code t' = wl_state_code t /\ wl_state_store t' = wl_state_store t /\
     wl_state_compile t' = wl_state_compile t /\
     wl_state_compile_oracle t' = wl_state_compile_oracle t /\
     wl_state_code_buffer t' = wl_state_code_buffer t /\
     wl_state_data_buffer t' = wl_state_data_buffer t /\
     wl_state_stack t' = wl_state_stack t /\ wl_state_stack_size t' = wl_state_stack_size t /\
     wl_state_locals_size t' = wl_state_locals_size t /\
     wl_state_stack_limit t' = wl_state_stack_limit t /\
     wl_state_be t' = wl_state_be t /\ wl_state_memory t' = wl_state_memory t /\
     wl_state_mdomain t' = wl_state_mdomain t /\
     lookup 0 (wl_state_locals t') = lookup 0 (wl_state_locals t) /\
     (!k. k IN domain (adjust_set (data_state_locals x)) ==>
          lookup k (wl_state_locals t') = lookup k (wl_state_locals t)) /\
     option_le (wl_state_stack_max t) (wl_state_stack_max t') /\
     option_le (wl_state_stack_max t') SM /\ option_le (data_state_stack_max x) SM ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_stack_max_fupd (K SM) x) t' NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sptree_inter (wl_state_locals (t':(A,C,FFI)wl_state))
                  (adjust_set (data_state_locals (x:(C,FFI)data_state))) =
                sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state)) (adjust_set (data_state_locals x))`
    ASSUME_TAC THENL
   [SIMP_TAC[spt_eq_thm; wf_inter] THEN REWRITE_TAC[lookup_inter_alt] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `adjust_var n IN domain (adjust_set (data_state_locals (x:(C,FFI)data_state)))`
      ASSUME_TAC THENL
     [REWRITE_TAC[GCP1AUX_adjust_var_IN_adjust_set] THEN
      ASM_MESON_TAC[IS_SOME_lookup];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ASM_MESON_TAC[option_le_trans]]);;

let ASP4AUX_option_stack_bound2 = prove
 (`!tsm xsm ls st d d1.
     option_le (OPTION_MAP2 (+) st ls) tsm /\ option_le tsm xsm ==>
     option_le (OPTION_MAP2 MAX (OPTION_MAP2 MAX tsm (OPTION_MAP2 (+) ls st))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls st) d))
       (OPTION_MAP2 MAX xsm (OPTION_MAP2 (+) (OPTION_MAP2 MAX d d1) (OPTION_MAP2 (+) st ls)))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v option_nchotomy))
    [`tsm:num option`; `xsm:num option`; `ls:num option`; `st:num option`;
     `d:num option`; `d1:num option`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

let ASP4AUX_lookup_LongDiv = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs ==>
     lookup LongDiv_location (wl_state_code t) = SOME (4,LongDiv_code c) /\
     lookup LongDiv1_location (wl_state_code t) = SOME (7,LongDiv1_code c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN
  REWRITE_TAC[data_to_word_gcProof_code_rel_def; data_to_word_stubs_def] THEN
  REWRITE_TAC[ALL; APPEND] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  MESON_TAC[]);;

(* the call of LongDiv_code in assign_Div and assign_Mod (HOL4: the part   *)
(* after qmatch_goalsub_abbrev_tac `evaluate (LongDiv_code c,t2)`)         *)
let ASP4AUX_LongDiv_call = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x a1 a2 w1 w2 n l.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_state_opt (SOME names) s = SOME x /\
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs /\
     wl_state_termdep t > 1 /\
     lookup (adjust_var a1) (wl_state_locals t) = SOME (wl_Word w1) /\
     lookup (adjust_var a2) (wl_state_locals t) = SOME (wl_Word w2) /\
     single_div_pre (word 0) w1 w2 ==>
     ?t'. wl_evaluate (MustTerminate (wl_Call (SOME ([1],adjust_sets
                         (data_to_word_get_names (SOME names)),wl_Skip,n,l + 1))
                         (SOME LongDiv_location) [1; adjust_var a1; adjust_var a2] NONE),
              wl_state_locals_fupd (K (insert 1 (wl_Word (word 0)) (wl_state_locals t))) t) =
            (NONE,t') /\
          lookup 1 (wl_state_locals t') = SOME (wl_Word (FST (single_div (word 0) w1 w2))) /\
          wl_state_store t' =
            wl_state_store t |+ (Temp (word 28),wl_Word (SND (single_div (word 0) w1 w2))) /\
          data_to_word_gcProof_state_rel c l1 l2
            (data_state_stack_max_fupd (K (OPTION_MAP2 MAX (data_state_stack_max x)
               (OPTION_MAP2 (+)
                  (OPTION_MAP2 MAX (lookup LongDiv_location (data_state_stack_frame_sizes x))
                     (lookup LongDiv1_location (data_state_stack_frame_sizes x)))
                  (OPTION_MAP2 (+) (size_of_stack (data_state_stack x))
                     (data_state_locals_size x))))) x)
            (wl_state_store_fupd (K (wl_state_store t)) t') NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_lookup_LongDiv) THEN
  SUBGOAL_THEN `?y. wl_cut_env (adjust_sets (names:1 spt)) (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME y`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC cut_env_IMP_cut_env THEN
    MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                          `locs:(num#num)list`; `data_state_locals (x:(C,FFI)data_state)`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `data_cut_state_opt (SOME names) (s:(C,FFI)data_state) = SOME x` THEN
    REWRITE_TAC[ASP4AUX_cut_state_opt_SOME; option_DISTINCT; option_INJ; UNWIND_THM1] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[data_cut_env_def; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC) o MATCH_MP cut_env_IMP_cut_envs) THEN
  ASP4AUX_EV_ALL_TAC (data_to_word_get_names_def :: wl_find_code_def :: bad_dest_args_def ::
     add_ret_loc_def :: wl_dec_clock_def :: wl_call_env_def :: wl_get_vars_def ::
     LENGTH :: ARITH :: TWO_LESS_MustTerminate_limit ::
     MATCH_MP data_to_word_gcProof_cut_envs_adjust_sets_insert_ODD (ARITH_RULE `ODD 1`) ::
     ASP4AUX_EV_RWS) THEN
  SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `env_to_list (y2:((A)word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(num#(A)word_loc)list` (X_CHOOSE_THEN `p1:num->num->num`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF; adjust_sets_def; FST; domain_def;
                  NOT_INSERT_EMPTY] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [asp4_callee_state `LongDiv_code c:(A)wl_prog` w; `n:num`;
    `l + 1`; `c:data_to_word_config`; `word 0:A word`; `w1:A word`; `w2:A word`;
    `FST (single_div (word 0) (w1:A word) w2)`; `SND (single_div (word 0) (w1:A word) w2)`]
    evaluate_LongDiv_code')) THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_fromList2; lookup_fromList;
                  LENGTH; ARITH; EL; HD; TL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[MustTerminate_limit_SUB_2; TWO_LESS_MustTerminate_limit;
               ARITH_RULE `d <= m - 2 /\ 2 < m ==> d < m - 1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `mx:num option`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH; ARITH] THEN
  REWRITE_TAC[wl_pop_env_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
              K_o_THM; K_THM] THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP env_to_list_domain o check (fun th ->
    try fst(strip_comb(lhs(concl th))) = `env_to_list:((A)word_loc)spt->(num->num->num)->((num#(A)word_loc)list#(num->num->num))` with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; domain_union; domain_fromAList_toAList] THEN
  REWRITE_TAC[UNION_COMM] THEN
  ASP4AUX_EV_TAC (wl_set_vars_def :: alist_insert_def :: ASP4AUX_EV_RWS) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM;
              lookup_insert; FLOOKUP_UPDATE] THEN
  SUBGOAL_THEN `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) = SOME (wl_Loc l1 l2)`
    ASSUME_TAC THENL [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`names:1 spt`; `wl_state_locals (t:(A,C,FFI)wl_state)`; `y1:((A)word_loc)spt`;
                 `y2:((A)word_loc)spt`; `wl_state_permute (t:(A,C,FFI)wl_state)`;
                 `q1:(num#(A)word_loc)list`; `p1:num->num->num`; `l1:num`; `l2:num`]
    cut_envs_lookup_0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP env_to_list_lookup_equiv o check (fun th ->
    try fst(strip_comb(lhs(concl th))) = `env_to_list:((A)word_loc)spt->(num->num->num)->((num#(A)word_loc)list#(num->num->num))` with Failure _ -> false)) THEN
  MATCH_MP_TAC ASP4AUX_state_rel_frame THEN EXISTS_TAC `t:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  REWRITE_TAC[lookup_insert; lookup_union; lookup_fromAList; lookup_fromAList_toAList; ARITH] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `y1 = sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state)) (LS one) /\
                y2 = sptree_inter (wl_state_locals t) (adjust_set (names:1 spt))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `cut_envs (adjust_sets (names:1 spt)) (wl_state_locals (t:(A,C,FFI)wl_state)) =
                 SOME (y1,y2)` THEN
    REWRITE_TAC[cut_envs_def; cut_names_def; adjust_sets_def; FST; SND] THEN
    REPEAT COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(k = 1) /\ ~(k = 0) /\ k IN domain (adjust_set (names:1 spt))`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `k IN domain (adjust_set (data_state_locals (x:(C,FFI)data_state)))` THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP cut_state_opt_SOME_eq) THEN
      REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; mk_wf_inter;
                  IN_domain_adjust_set_inter] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP domain_adjust_set_EVEN) THEN
      UNDISCH_TAC `k IN domain (adjust_set (data_state_locals (s:(C,FFI)data_state)))` THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [domain_lookup] THEN
      REWRITE_TAC[lookup_adjust_set] THEN
      ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
      ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[ARITH];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_inter_alt; domain_def; IN_SING] THEN
    CASES_ON `lookup k (wl_state_locals (t:(A,C,FFI)wl_state))` THEN CASE_REWRITE_TAC[];
    UNDISCH_TAC `mx = OPTION_MAP2 MAX (OPTION_MAP2 MAX (wl_state_stack_max (t:(A,C,FFI)wl_state))
      (wl_stack_size (CONS (StackFrame (wl_state_locals_size t) (toAList y1) q1 NONE)
         (wl_state_stack t)))) (OPTION_MAP2 (+) (wl_stack_size
         (CONS (StackFrame (wl_state_locals_size t) (toAList y1) q1 NONE) (wl_state_stack t)))
         (lookup LongDiv_location (wl_state_stack_size t))) \/
     mx = OPTION_MAP2 MAX (OPTION_MAP2 MAX (OPTION_MAP2 MAX (wl_state_stack_max t)
      (wl_stack_size (CONS (StackFrame (wl_state_locals_size t) (toAList y1) q1 NONE)
         (wl_state_stack t)))) (OPTION_MAP2 (+) (wl_stack_size
         (CONS (StackFrame (wl_state_locals_size t) (toAList y1) q1 NONE) (wl_state_stack t)))
         (lookup LongDiv_location (wl_state_stack_size t))))
       (OPTION_MAP2 (+) (wl_stack_size (CONS (StackFrame (wl_state_locals_size t)
          (toAList y1) q1 NONE) (wl_state_stack t)))
          (lookup LongDiv1_location (wl_state_stack_size t)))` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_le_max_right; option_le_refl];
    ALL_TAC;
    REWRITE_TAC[option_le_max_right; option_le_refl]] THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) NONE locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP stack_rel_IMP_size_of_stack o check (fun th ->
    can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "data_to_word_gcProof_stack_rel")) (concl th))) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj (concl th) &&
    can (find_term ((=) `mx:num option`)) (concl th))) THEN
  REWRITE_TAC[stack_size_eq2; stack_size_frame_def] THEN
  ASM_REWRITE_TAC[] THEN
  (MATCH_MP_TAC ASP4AUX_option_stack_bound ORELSE
   MATCH_MP_TAC ASP4AUX_option_stack_bound2) THEN ASM_MESON_TAC[]);;

(* the end of a fast path after a call: dest := a small number            *)
let ASP4AUX_state_rel_after_call = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest i op vs SM.
     data_to_word_gcProof_state_rel c l1 l2 (data_state_stack_max_fupd (K SM) x) t NONE locs /\
     op_space_reset op /\ small_int (:A) i /\
     data_state_stack_max (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs)) = SM ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest (data_Number i)
          (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs)))
       (wl_set_var (adjust_var dest) (wl_Word (Smallnum i)) t) NONE locs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ASP4AUX_state_rel_set_var_sp THEN
  EXISTS_TAC `data_state_stack_max_fupd (K SM) (x:(C,FFI)data_state)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `data_state_stack_max (do_stack op vs (do_lim_safe (THE (do_space op vs
                 (x:(C,FFI)data_state))) op vs)) = (SM:num option)` THEN
  ASM_REWRITE_TAC[do_space_def; THE_DEF; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                  data_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[option_le_refl] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[data_to_word_gcProof_state_rel_thm; data_state_INFO.ri_accfupds;
                                K_THM]; ALL_TAC] THEN
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC memory_rel_zero_space THEN
  EXISTS_TAC `data_state_space (x:(C,FFI)data_state)` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP1AUX_state_rel_memory_rel) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 10403 *)
let assign_Div = prove
 (assign_thm_stmt `op = IntOp clos_Div`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?names. names_opt = SOME (names:1 spt)`
    (X_CHOOSE_THEN `names:1 spt` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (IntOp clos_Div) <=> names_opt:(1 spt)option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:(1 spt)option` THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DRULE_ALL state_rel_cut_state_opt_SOME THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (IntOp clos_Div) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_Div] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `n2:int` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `LENGTH (args:num list) = LENGTH [data_Number n1; data_Number n2]` THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Div_def; FST] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
  DRULE memory_rel_Number_IMP_Word_2 THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `~(dimindex(:A) - 1 = 0) /\ dimindex(:A) - 1 < dimindex(:A) /\
                1 < dimindex(:A) /\ ~(1 >= dimindex(:A)) /\
                ~(2 >= dimindex(:A)) /\ 2 < dimindex(:A) /\
                ~(dimindex(:A) - 1 >= dimindex(:A))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `data_get_var a1 (data_state_locals (s:(C,FFI)data_state)) =
                  SOME (data_Number n1) /\
                data_get_var a2 (data_state_locals s) = SOME (data_Number n2)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[get_vars_SOME_IFF_data]; ALL_TAC] THEN
  ASM_CASES_TAC `~bit 0 (v1:A word) /\ ~bit 0 (v2:A word) /\ ~word_msb (v1:A word) /\
                 ~word_msb (v2:A word)` THENL
   [FIRST_ASSUM STRIP_ASSUME_TAC THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `a1:num`; `n1:int`;
                     `wl_Word (v1:A word)`] state_rel_Number_IMP) THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `a2:num`; `n2:int`;
                     `wl_Word (v2:A word)`] state_rel_Number_IMP) THEN
      ASM_REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `k1:num` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS] o check (fun th ->
          concl th = `&0 <= (n1:int)`)) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `k2:num` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS] o check (fun th ->
          concl th = `&0 <= (n2:int)`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ]) THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
        (let l = lhs(concl th) in is_var l && mem (fst(dest_var l)) ["v1";"v2"])))) THEN
      REWRITE_TAC[data_to_word_list_Seq_def] THEN
      ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
                      ASP4AUX_word_exp_ShiftVar :: word_sh_def :: ASP4AUX_EV_RWS) THEN
      REWRITE_TAC[ASP4AUX_div_test] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `k1 < dimword (:A) DIV 8 /\ k2 < dimword (:A) DIV 8 /\ ~(k2 = 0)`
        STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
          can (find_term ((=) `&k2:int`)) (concl th) && is_eq (dest_neg (concl th)))) ORELSE ALL_TAC THEN
        ASM_MESON_TAC[MP6AUX_SMALL_INT_NUM; INT_OF_NUM_EQ];
        ALL_TAC] THEN
      SUBGOAL_THEN `8 * (dimword (:A) DIV 8) <= dimword (:A)` ASSUME_TAC THENL
       [MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `4 * k1 < dimword (:A) /\ 4 * k2 < dimword (:A) /\
                    k1 DIV k2 < dimword (:A) DIV 8` STRIP_ASSUME_TAC THENL
       [MP_TAC(SPECL [`k1:num`; `k2:num`] DIV_LE) THEN
        UNDISCH_TAC `k1 < dimword (:A) DIV 8` THEN UNDISCH_TAC `k2 < dimword (:A) DIV 8` THEN
        UNDISCH_TAC `8 * (dimword (:A) DIV 8) <= dimword (:A)` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `small_int (:A) (&(k1 DIV k2)) /\ ~(word (4 * k2) = word 0:A word) /\
                    int_div (&k1) (&k2) = &(k1 DIV k2)` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[INT_DIV; MP6AUX_SMALL_INT_NUM; n2w_11; MOD_LT; ZERO_LT_dimword] THEN
        UNDISCH_TAC `~(k2 = 0)` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `data_to_word_config_has_div c` THEN ASM_REWRITE_TAC[] THENL
     [(* has_div *)
      ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
           ASP4AUX_word_exp_ShiftVar :: word_sh_def :: ASP4AUX_word_div_4 :: ASP4AUX_EV_RWS) THEN
      ASP4AUX_NONE_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[WORD_SHL_WORD; ARITH_RULE `2 EXP 2 * q = 4 * q`; GSYM MP6AUX_SMALLNUM_NUM] THEN
        MATCH_MP_TAC ASP4AUX_state_rel_arith_fast3 THEN
        ASM_REWRITE_TAC[op_space_reset_def; lookup_insert] THEN
        MESON_TAC[ASP4AUX_EVEN_NOT_1_3];
      ASM_CASES_TAC `data_to_word_config_has_longdiv c` THEN ASM_REWRITE_TAC[] THENL
       [(* has_longdiv *)
        SUBGOAL_THEN `val (word (4 * k1):A word) = 4 * k1 /\ val (word (4 * k2):A word) = 4 * k2 /\
                        (4 * k1) DIV (4 * k2) = k1 DIV k2 /\ k1 DIV k2 < dimword (:A) /\
                        ~(4 * k2 = 0)` STRIP_ASSUME_TAC THENL
           [ASM_SIMP_TAC[w2n_n2w; MOD_LT; DIV_MULT2; ARITH_EQ] THEN
            UNDISCH_TAC `k1 DIV k2 < dimword (:A) DIV 8` THEN UNDISCH_TAC `~(k2 = 0)` THEN
            MP_TAC(SPECL [`dimword(:A)`; `8`] DIV_LE) THEN ARITH_TAC;
            ALL_TAC] THEN
          ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
             ASP4AUX_word_exp_ShiftVar :: word_sh_def :: VAL_WORD_0 :: ASP4AUX_EV_RWS) THEN
        ASP4AUX_NONE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[WORD_SHL_WORD; ARITH_RULE `2 EXP 2 * q = 4 * q`; GSYM MP6AUX_SMALLNUM_NUM] THEN
          MATCH_MP_TAC ASP4AUX_state_rel_arith_fast3 THEN
          ASM_REWRITE_TAC[op_space_reset_def; lookup_insert] THEN
          MESON_TAC[ASP4AUX_EVEN_NOT_1_3];
        (* the call of LongDiv_code *)
        MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                         `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:1 spt`;
                         `x:(C,FFI)data_state`; `a1:num`; `a2:num`; `word (4 * k1):A word`;
                         `word (4 * k2):A word`; `n:num`; `l:num`] ASP4AUX_LongDiv_call) THEN
          SUBGOAL_THEN `val (word (4 * k1):A word) = 4 * k1 /\ val (word (4 * k2):A word) = 4 * k2 /\
                        (4 * k1) DIV (4 * k2) = k1 DIV k2 /\ k1 DIV k2 < dimword (:A)`
            STRIP_ASSUME_TAC THENL
           [ASM_SIMP_TAC[w2n_n2w; MOD_LT; DIV_MULT2; ARITH_EQ] THEN
            UNDISCH_TAC `k1 DIV k2 < dimword (:A) DIV 8` THEN
            MP_TAC(SPECL [`dimword(:A)`; `8`] DIV_LE) THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[single_div_pre_def; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
          DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
          ASP4AUX_EV_TAC (ASP4AUX_word_exp_ShiftVar :: word_sh_def :: insert_shadow :: ASP4AUX_EV_RWS) THEN
        ASP4AUX_NONE_TAC THEN
          SUBGOAL_THEN `word_shl (FST (single_div (word 0) (word (4 * k1)) (word (4 * k2)))) 2 =
                        Smallnum (&(k1 DIV k2)):A word` SUBST1_TAC THENL
           [REWRITE_TAC[single_div_def; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
            ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_SHL_WORD; MP6AUX_SMALLNUM_NUM] THEN
            AP_TERM_TAC THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM wl_set_var_def] THEN
          MATCH_MP_TAC ASP4AUX_state_rel_after_call THEN
          EXISTS_TAC `OPTION_MAP2 MAX (data_state_stack_max (x:(C,FFI)data_state))
            (OPTION_MAP2 (+)
               (OPTION_MAP2 MAX (lookup LongDiv_location (data_state_stack_frame_sizes x))
                  (lookup LongDiv1_location (data_state_stack_frame_sizes x)))
               (OPTION_MAP2 (+) (size_of_stack (data_state_stack x)) (data_state_locals_size x)))` THEN
          ASM_REWRITE_TAC[op_space_reset_def] THEN CONJ_TAC THENL
           [SUBGOAL_THEN `t3 = wl_set_store (Temp (word 28))
               (wl_Word (SND (single_div (word 0) (word (4 * k1)) (word (4 * k2)))))
               (wl_state_store_fupd (K (wl_state_store (t:(A,C,FFI)wl_state))) (t3:(A,C,FFI)wl_state))`
               SUBST1_TAC THENL
             [ASM_REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
                              K_o_THM; K_THM] THEN
              REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
              ASM_REWRITE_TAC[];
              ASM_REWRITE_TAC[state_rel_set_store_Temp]];
            ALL_TAC] THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_arch_64_bit o check (fun th ->
            concl th = `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
                          (t:(A,C,FFI)wl_state) NONE locs`)) THEN
          REWRITE_TAC[do_space_def; THE_DEF; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                      op_space_reset_def; data_state_INFO.ri_accfupds; K_THM; stack_consumed_def] THEN
          ASM_SIMP_TAC[small_num_small_int; INT_POS]]];
    (* the call of the bignum code *)
    REWRITE_TAC[data_to_word_list_Seq_def] THEN
      ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
                      ASP4AUX_word_exp_ShiftVar :: word_sh_def :: ASP4AUX_EV_RWS) THEN
      REWRITE_TAC[ASP4AUX_div_test] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_arch_64_bit o check (fun th ->
        can (find_term ((=) `x:(C,FFI)data_state`)) (concl th) &&
        can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "data_to_word_gcProof_state_rel")) (concl th))) THEN
      SUBGOAL_THEN `~(small_int (:A) n1 /\ &0 <= n1 /\ small_int (:A) n2 /\ &0 <= n2 /\
                      small_int (:A) (int_div n1 n2))` ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `~(a /\ b /\ c /\ d) ==> ~(a /\ b /\ c /\ d /\ e)`) THEN
        MATCH_MP_TAC ASP4AUX_not_all_small_div THEN
        MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`] THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      CONV_TAC(ONCE_DEPTH_CONV ASP4AUX_PAIR_CASE_GABS_CONV) THEN
      W(fun (_,w) -> MP_TAC(ISPECL [`5`; `clos_Div`; `c:data_to_word_config`; `l1:num`; `l2:num`;
        `s:(C,FFI)data_state`; asp4_must_state w; `locs:(num#num)list`; `names:1 spt`;
        `a1:num`; `a2:num`; `n1:int`; `n2:int`; `x:(C,FFI)data_state`; `int_div n1 n2`;
        `dest:num`; `n:num`; `l:num`] ASP4AUX_arith_slow)) THEN
      REWRITE_TAC[data_to_word_bignumProof_Arith_location_def; data_to_word_bignumProof_int_op_def;
                  ARITH_EQ; wl_state_INFO.ri_accfupds; K_THM; op_space_reset_def] THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `1 < n <=> n > 1`] THEN
        REWRITE_TAC[stack_consumed_def; space_consumed_def; lim_safe_def; LET_DEF; LET_END_DEF] THEN
        ASM_SIMP_TAC[small_num_small_int] THEN
        MATCH_MP_TAC ASP4AUX_state_rel_odd THEN ASM_REWRITE_TAC[lookup_insert] THEN
        MESON_TAC[ASP4AUX_EVEN_NOT_1_3];
        ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC]);;

(* HOL4 line 10711 *)
let assign_Mod = prove
 (assign_thm_stmt `op = (IntOp clos_Mod)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?names. names_opt = SOME (names:1 spt)`
    (X_CHOOSE_THEN `names:1 spt` SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `~(op_requires_names (IntOp clos_Mod) <=> names_opt:(1 spt)option = NONE)` THEN
    REWRITE_TAC[op_requires_names_def; op_space_reset_def] THEN
    CASES_ON `names_opt:(1 spt)option` THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DRULE_ALL state_rel_cut_state_opt_SOME THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `data_do_app (IntOp clos_Mod) vals (x:(C,FFI)data_state) = Rval (v,s2)` THEN
  REWRITE_TAC[ASP4AUX_do_app_Mod] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `n2:int` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  UNDISCH_TAC `LENGTH (args:num list) = LENGTH [data_Number n1; data_Number n2]` THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_Mod_def; FST] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc` STRIP_ASSUME_TAC)) THEN
  DRULE memory_rel_Number_IMP_Word_2 THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
    (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `~(dimindex(:A) - 1 = 0) /\ dimindex(:A) - 1 < dimindex(:A) /\
                1 < dimindex(:A) /\ ~(1 >= dimindex(:A)) /\
                ~(2 >= dimindex(:A)) /\ 2 < dimindex(:A) /\
                ~(dimindex(:A) - 1 >= dimindex(:A))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `data_get_var a1 (data_state_locals (s:(C,FFI)data_state)) =
                  SOME (data_Number n1) /\
                data_get_var a2 (data_state_locals s) = SOME (data_Number n2)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[get_vars_SOME_IFF_data]; ALL_TAC] THEN
  ASM_CASES_TAC `~bit 0 (v1:A word) /\ ~bit 0 (v2:A word) /\ ~word_msb (v1:A word) /\
                 ~word_msb (v2:A word)` THENL
   [FIRST_ASSUM STRIP_ASSUME_TAC THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `a1:num`; `n1:int`;
                     `wl_Word (v1:A word)`] state_rel_Number_IMP) THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                     `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `a2:num`; `n2:int`;
                     `wl_Word (v2:A word)`] state_rel_Number_IMP) THEN
      ASM_REWRITE_TAC[injectivity "word_loc"; UNWIND_THM1] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `k1:num` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS] o check (fun th ->
          concl th = `&0 <= (n1:int)`)) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `k2:num` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [GSYM INT_OF_NUM_EXISTS] o check (fun th ->
          concl th = `&0 <= (n2:int)`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ]) THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
        (let l = lhs(concl th) in is_var l && mem (fst(dest_var l)) ["v1";"v2"])))) THEN
      REWRITE_TAC[data_to_word_list_Seq_def] THEN
      ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
                      ASP4AUX_word_exp_ShiftVar :: word_sh_def :: ASP4AUX_EV_RWS) THEN
      REWRITE_TAC[ASP4AUX_div_test] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `k1 < dimword (:A) DIV 8 /\ k2 < dimword (:A) DIV 8 /\ ~(k2 = 0)`
        STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
          can (find_term ((=) `&k2:int`)) (concl th) && is_eq (dest_neg (concl th)))) ORELSE ALL_TAC THEN
        ASM_MESON_TAC[MP6AUX_SMALL_INT_NUM; INT_OF_NUM_EQ];
        ALL_TAC] THEN
      SUBGOAL_THEN `8 * (dimword (:A) DIV 8) <= dimword (:A)` ASSUME_TAC THENL
       [MP_TAC(SPECL [`dimword(:A)`; `8`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `4 * k1 < dimword (:A) /\ 4 * k2 < dimword (:A) /\
                    k1 DIV k2 < dimword (:A) DIV 8` STRIP_ASSUME_TAC THENL
       [MP_TAC(SPECL [`k1:num`; `k2:num`] DIV_LE) THEN
        UNDISCH_TAC `k1 < dimword (:A) DIV 8` THEN UNDISCH_TAC `k2 < dimword (:A) DIV 8` THEN
        UNDISCH_TAC `8 * (dimword (:A) DIV 8) <= dimword (:A)` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `small_int (:A) (&(k1 MOD k2)) /\ ~(word (4 * k2) = word 0:A word) /\
                    integer_int_mod (&k1) (&k2) = &(k1 MOD k2)` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `k1 MOD k2 < k2` MP_TAC THENL [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
        ASM_SIMP_TAC[INT_MOD; MP6AUX_SMALL_INT_NUM; n2w_11; MOD_LT; ZERO_LT_dimword] THEN
        UNDISCH_TAC `~(k2 = 0)` THEN UNDISCH_TAC `k2 < dimword (:A) DIV 8` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `data_to_word_config_has_div c` THEN ASM_REWRITE_TAC[] THENL
     [(* has_div *)
      ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
           ASP4AUX_word_exp_ShiftVar :: word_sh_def :: ASP4AUX_word_div_4 :: ASP4AUX_EV_RWS) THEN
      ASP4AUX_NONE_TAC THEN
        SUBGOAL_THEN `k1 DIV k2 < dimword (:A)` ASSUME_TAC THENL
         [UNDISCH_TAC `k1 DIV k2 < dimword (:A) DIV 8` THEN
          MP_TAC(SPECL [`dimword(:A)`; `8`] DIV_LE) THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_LT] THEN
        SUBGOAL_THEN `word_sub (word (4 * k1)) (word ((k1 DIV k2) * (4 * k2))) =
                      Smallnum (&(k1 MOD k2)):A word` SUBST1_TAC THENL
         [MP_TAC(SPECL [`k1:num`; `k2:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          SUBGOAL_THEN `(k1 DIV k2) * (4 * k2) <= 4 * k1` ASSUME_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[MP6AUX_SMALLNUM_NUM] THEN
          SUBGOAL_THEN `4 * (k1 MOD k2) = 4 * k1 - (k1 DIV k2) * (4 * k2)` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[WORD_SUB];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC ASP4AUX_state_rel_arith_fast3 THEN
        ASM_REWRITE_TAC[op_space_reset_def; lookup_insert] THEN
        MESON_TAC[ASP4AUX_EVEN_NOT_1_3];
      ASM_CASES_TAC `data_to_word_config_has_longdiv c` THEN ASM_REWRITE_TAC[] THENL
       [(* has_longdiv *)
        SUBGOAL_THEN `val (word (4 * k1):A word) = 4 * k1 /\ val (word (4 * k2):A word) = 4 * k2 /\
                        (4 * k1) DIV (4 * k2) = k1 DIV k2 /\ k1 DIV k2 < dimword (:A) /\
                        ~(4 * k2 = 0) /\ (4 * k1) MOD (4 * k2) = 4 * (k1 MOD k2)` STRIP_ASSUME_TAC THENL
           [ASM_SIMP_TAC[w2n_n2w; MOD_LT; DIV_MULT2; MOD_MULT2; ARITH_EQ] THEN
            UNDISCH_TAC `k1 DIV k2 < dimword (:A) DIV 8` THEN UNDISCH_TAC `~(k2 = 0)` THEN
            MP_TAC(SPECL [`dimword(:A)`; `8`] DIV_LE) THEN ARITH_TAC;
            ALL_TAC] THEN
          ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
             ASP4AUX_word_exp_ShiftVar :: word_sh_def :: VAL_WORD_0 :: wl_set_vars_def ::
             alist_insert_def :: MAP :: ASP4AUX_EV_RWS) THEN
        ASP4AUX_NONE_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM MP6AUX_SMALLNUM_NUM] THEN
          MATCH_MP_TAC ASP4AUX_state_rel_arith_fast3 THEN
          ASM_REWRITE_TAC[op_space_reset_def; lookup_insert] THEN
          MESON_TAC[ASP4AUX_EVEN_NOT_1_3];
        (* the call of LongDiv_code *)
        MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                         `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:1 spt`;
                         `x:(C,FFI)data_state`; `a1:num`; `a2:num`; `word (4 * k1):A word`;
                         `word (4 * k2):A word`; `n:num`; `l:num`] ASP4AUX_LongDiv_call) THEN
          SUBGOAL_THEN `val (word (4 * k1):A word) = 4 * k1 /\ val (word (4 * k2):A word) = 4 * k2 /\
                        (4 * k1) DIV (4 * k2) = k1 DIV k2 /\ k1 DIV k2 < dimword (:A)`
            STRIP_ASSUME_TAC THENL
           [ASM_SIMP_TAC[w2n_n2w; MOD_LT; DIV_MULT2; ARITH_EQ] THEN
            UNDISCH_TAC `k1 DIV k2 < dimword (:A) DIV 8` THEN
            MP_TAC(SPECL [`dimword(:A)`; `8`] DIV_LE) THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[single_div_pre_def; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
          DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
          ASP4AUX_EV_TAC (wl_get_store_def :: FLOOKUP_UPDATE :: insert_shadow :: ASP4AUX_EV_RWS) THEN
        ASP4AUX_NONE_TAC THEN
          SUBGOAL_THEN `SND (single_div (word 0) (word (4 * k1)) (word (4 * k2))) =
                        Smallnum (&(k1 MOD k2)):A word` SUBST1_TAC THENL
           [REWRITE_TAC[single_div_def; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
            ASM_REWRITE_TAC[] THEN REWRITE_TAC[MP6AUX_SMALLNUM_NUM] THEN
            ASM_SIMP_TAC[MOD_MULT2; ARITH_EQ];
            ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM wl_set_var_def] THEN
          MATCH_MP_TAC ASP4AUX_state_rel_after_call THEN
          EXISTS_TAC `OPTION_MAP2 MAX (data_state_stack_max (x:(C,FFI)data_state))
            (OPTION_MAP2 (+)
               (OPTION_MAP2 MAX (lookup LongDiv_location (data_state_stack_frame_sizes x))
                  (lookup LongDiv1_location (data_state_stack_frame_sizes x)))
               (OPTION_MAP2 (+) (size_of_stack (data_state_stack x)) (data_state_locals_size x)))` THEN
          ASM_REWRITE_TAC[op_space_reset_def] THEN CONJ_TAC THENL
           [SUBGOAL_THEN `t3 = wl_set_store (Temp (word 28))
               (wl_Word (SND (single_div (word 0) (word (4 * k1)) (word (4 * k2)))))
               (wl_state_store_fupd (K (wl_state_store (t:(A,C,FFI)wl_state))) (t3:(A,C,FFI)wl_state))`
               SUBST1_TAC THENL
             [ASM_REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
                              K_o_THM; K_THM] THEN
              REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM] THEN
              ASM_REWRITE_TAC[];
              ASM_REWRITE_TAC[state_rel_set_store_Temp]];
            ALL_TAC] THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_arch_64_bit o check (fun th ->
            concl th = `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
                          (t:(A,C,FFI)wl_state) NONE locs`)) THEN
          REWRITE_TAC[do_space_def; THE_DEF; do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF;
                      op_space_reset_def; data_state_INFO.ri_accfupds; K_THM; stack_consumed_def] THEN
          ASM_SIMP_TAC[small_num_small_int; INT_POS]]];
    (* the call of the bignum code *)
    REWRITE_TAC[data_to_word_list_Seq_def] THEN
      ASP4AUX_EV_TAC (wl_inst_def :: wl_get_vars_def :: LET_DEF :: LET_END_DEF ::
                      ASP4AUX_word_exp_ShiftVar :: word_sh_def :: ASP4AUX_EV_RWS) THEN
      REWRITE_TAC[ASP4AUX_div_test] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP state_rel_IMP_arch_64_bit o check (fun th ->
        can (find_term ((=) `x:(C,FFI)data_state`)) (concl th) &&
        can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "data_to_word_gcProof_state_rel")) (concl th))) THEN
      SUBGOAL_THEN `~(small_int (:A) n1 /\ &0 <= n1 /\ small_int (:A) n2 /\ &0 <= n2 /\
                      small_int (:A) (integer_int_mod n1 n2))` ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `~(a /\ b /\ c /\ d) ==> ~(a /\ b /\ c /\ d /\ e)`) THEN
        MATCH_MP_TAC ASP4AUX_not_all_small_div THEN
        MAP_EVERY EXISTS_TAC [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`] THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      CONV_TAC(ONCE_DEPTH_CONV ASP4AUX_PAIR_CASE_GABS_CONV) THEN
      W(fun (_,w) -> MP_TAC(ISPECL [`6`; `clos_Mod`; `c:data_to_word_config`; `l1:num`; `l2:num`;
        `s:(C,FFI)data_state`; asp4_must_state w; `locs:(num#num)list`; `names:1 spt`;
        `a1:num`; `a2:num`; `n1:int`; `n2:int`; `x:(C,FFI)data_state`; `integer_int_mod n1 n2`;
        `dest:num`; `n:num`; `l:num`] ASP4AUX_arith_slow)) THEN
      REWRITE_TAC[data_to_word_bignumProof_Arith_location_def; data_to_word_bignumProof_int_op_def;
                  ARITH_EQ; wl_state_INFO.ri_accfupds; K_THM; op_space_reset_def] THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `1 < n <=> n > 1`] THEN
        REWRITE_TAC[stack_consumed_def; space_consumed_def; lim_safe_def; LET_DEF; LET_END_DEF] THEN
        ASM_SIMP_TAC[small_num_small_int] THEN
        MATCH_MP_TAC ASP4AUX_state_rel_odd THEN ASM_REWRITE_TAC[lookup_insert] THEN
        MESON_TAC[ASP4AUX_EVEN_NOT_1_3];
        ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC]);;
