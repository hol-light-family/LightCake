(* ========================================================================= *)
(* data_to_word_assignProof_p5: part 5 of 6 (HOL4 lines 11024-14005) of the  *)
(* port of HOL4 compiler/backend/proofs/data_to_word_assignProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p6 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_assignProof.ml needs the last.                *)
(* ASP5AUX_ names are local helpers of this part.                           *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_assignProof_p4.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 5: HOL4 lines 11024-14005 ===== *)

(* ------------------------------------------------------------------------- *)
(* Helpers of this part (ASP5AUX_ theorems and tactics, asp5_ functions):    *)
(* the shared steps of the assign proofs below (HOL4: gvs with              *)
(* op_requires_names_def, cut_state_opt_def, do_app; imp_res_tac            *)
(* state_rel_get_vars_IMP and memory_rel_get_vars_IMP; eval_tac; fs with   *)
(* state_rel_thm and memory_rel_insert).  After the helpers of part 4.     *)
(* ------------------------------------------------------------------------- *)

(* proves  data_do_app op vs s = Rval (v,s2) <=> ...  for an operator op    *)
(* with no space reset and no space requirement (do_app_aux unfolded)       *)
let ASP5AUX_DO_APP_TAC op_tm (extra:thm list) : tactic =
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [op_tm; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "int_op"; distinctness "block_op";
              distinctness "word_op"; distinctness "mem_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC([case_eq "list"; case_eq "data_v"; case_eq "option"; case_eq "bvl_ref";
               case_eq "prod"; COND_CASE_EQ; distinctness "result";
               injectivity "result"; PAIR_EQ; RIGHT_AND_EXISTS_THM;
               LEFT_AND_EXISTS_THM] @ extra) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];;

(* inserting into an odd local (a temporary: never adjust_var n, never 0)   *)
(* does not change state_rel                                                *)
let ASP5AUX_ODD_adjust_var = prove
 (`!k n. ODD k ==> ~(adjust_var n = k) /\ ~(k = 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
    REWRITE_TAC[adjust_var_def; ODD_ADD; ODD_MULT; ARITH];
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC) THEN REWRITE_TAC[ARITH]]);;

let ASP5AUX_locals_fupd_id = prove
 (`!(t:(A,C,FFI)wl_state). wl_state_locals_fupd (K (wl_state_locals t)) t = t`,
  REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

(* the final state_rel of a Boolv/Number result: the word state is t with  *)
(* locals insert (adjust_var dest) w L, L the locals of t with temporaries *)
(* (odd locals) set                                                        *)
let ASP5AUX_state_rel_finish = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w op vs L.
     data_to_word_gcProof_state_rel c l1 l2 s (wl_state_locals_fupd (K L) t) NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps s)) (data_state_refs s)
       (data_state_space s) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals s)
                   (toAList (sptree_inter L (adjust_set (data_state_locals s)))))
            (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest v (do_stack op vs (do_lim_safe s op vs)))
       (wl_state_locals_fupd (K (insert (adjust_var dest) w L)) t) NONE locs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
                 `wl_state_locals_fupd (K L) (t:(A,C,FFI)wl_state)`;
                 `locs:(num#num)list`; `dest:num`; `v:data_v`; `w:A word_loc`;
                 `op:clos_op`; `vs:data_v list`] ASP4AUX_state_rel_do_stack_set_var) THEN
  ASM_REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds;
                  wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM]);;

(* ------------------------------------------------------------------------- *)
(* Symbolic evaluation of wordLang code (the work of HOL4's eval_tac and of *)
(* fs/simp with wordSemTheory.evaluate_def in the proofs below), as in part *)
(* 4: asp5_ev_conv thl evaluates a term wl_evaluate (p,s) with p a concrete *)
(* program: it unfolds the clause of the head constructor, simplifies with  *)
(* the project simpset and thl, and goes on with the parts of the result    *)
(* that are again such closed evaluations; wl_Seq c1 c2 with c1 evaluating  *)
(* to (NONE,s1) becomes wl_evaluate (c2,s1).  The constructors listed in    *)
(* asp5_ev_stop are not unfolded.                                          *)
(* ------------------------------------------------------------------------- *)

let asp5_ev_table =
  map (fun th -> let l = lhs (concl (SPEC_ALL th)) in
                 fst (dest_const (fst (strip_comb (fst (dest_pair (rand l)))))), th)
      (CONJUNCTS wl_evaluate_def);;

let asp5_ev_clause c = assoc c asp5_ev_table;;

let asp5_ev_stop = ref ["wl_Call"; "MustTerminate"];;

let asp5_is_ev tm =
  match tm with
    Comb(Const("wl_evaluate",_),arg) ->
      (try let p,_ = dest_pair arg in
           let h = fst (strip_comb p) in
           is_const h && (let n = fst (dest_const h) in
                          exists (fun (m,_) -> m = n) asp5_ev_table &&
                          not (mem n !asp5_ev_stop))
       with Failure _ -> false)
  | _ -> false;;

(* apply c to the closed subterms of tm (no variable bound in tm free in    *)
(* them), outermost first, once at each place                               *)
let rec asp5_closed_conv bvs c tm =
  try (if exists (fun v -> vfree_in v tm) bvs then failwith "" else c tm)
  with Failure _ ->
  match tm with
    Comb(f,x) ->
      (match (try Some (asp5_closed_conv bvs c f) with Failure _ -> None),
             (try Some (asp5_closed_conv bvs c x) with Failure _ -> None) with
         None, None -> failwith "asp5_closed_conv"
       | Some a, None -> AP_THM a x
       | None, Some b -> AP_TERM f b
       | Some a, Some b -> MK_COMB(a,b))
  | Abs(v,_) -> ABS_CONV (asp5_closed_conv (v::bvs) c) tm
  | _ -> failwith "asp5_closed_conv";;

let asp5_is_none tm = is_const tm && fst (dest_const tm) = "NONE";;

let rec asp5_ev_conv thl tm =
  if not (asp5_is_ev tm) then failwith "asp5_ev_conv" else
  let p,s = dest_pair (rand tm) in
  let hd,args = strip_comb p in
  let name = fst (dest_const hd) in
  if name = "wl_Seq" then
    let c1 = el 0 args and c2 = el 1 args in
    let tm1 = mk_comb(rator tm, mk_pair(c1,s)) in
    let th1 = try asp5_ev_conv thl tm1 with Failure _ -> REFL tm1 in
    let r1 = rhs (concl th1) in
    if is_pair r1 && asp5_is_none (fst (dest_pair r1)) then
      let s1 = snd (dest_pair r1) in
      let th2 = MATCH_MP (ISPECL [c1; c2; s; s1] IL2AUX_evaluate_Seq_NONE) th1 in
      TRANS th2 (asp5_ev_rest thl (rhs (concl th2)))
    else
      let th2 = REWR_CONV (asp5_ev_clause "wl_Seq") tm in
      let th3 = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV
                  (fun t -> if t = tm1 then th1 else failwith ""))) th2 in
      let th4 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV thl)) th3 in
      TRANS th4 (asp5_ev_rest thl (rhs (concl th4)))
  else
    let th1 = REWR_CONV (asp5_ev_clause name) tm in
    let th2 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV thl)) th1 in
    TRANS th2 (asp5_ev_rest thl (rhs (concl th2)))
and asp5_ev_rest thl tm =
  try let th = asp5_closed_conv [] (asp5_ev_conv thl) tm in
      TRANS th (asp5_ev_rest thl (rhs (concl th)))
  with Failure _ -> REFL tm;;

(* evaluate the closed evaluations of the goal, with the assumptions *)
let ASP5AUX_EV_TAC thl : tactic = fun (asl,w as g) ->
  CONV_TAC (asp5_closed_conv [] (asp5_ev_conv (thl @ map snd asl))) g;;

(* the common start of the assign proofs of operators with names_opt = NONE *)
(* (HOL4: rpt strip_tac \\ gvs [op_requires_names_def, op_space_reset_def,  *)
(* cut_state_opt_def]): after intro (which introduces op), names_opt is    *)
(* NONE and x is s                                                          *)
let ASP5AUX_INTRO_TAC (intro:tactic) : tactic =
  REPEAT GEN_TAC THEN intro THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def;
     distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op";
     distinctness "mem_op"; distinctness "int_op"; distinctness "word_op";
     injectivity "block_op"; injectivity "mem_op"; injectivity "int_op";
     injectivity "word_op"]) THEN
  UNDISCH_TAC `names_opt:(1 spt)option = NONE` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `data_cut_state_opt NONE (s:(C,FFI)data_state) = SOME x` THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts);;

(* unfold the assignment: assign_th is the equation of the operator *)
let ASP5AUX_UNFOLD_ASSIGN_TAC assign_th : tactic =
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[assign_th];;

(* the do_app assumption, rewritten with th *)
let ASP5AUX_DO_APP_ASM_TAC th : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    is_const t && fst(dest_const t) = "data_do_app")) (concl th))) THEN
  REWRITE_TAC[th];;

(* a Boolv argument: its value and its word *)
let ASP5AUX_memory_rel_dest_Boolv = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm v w vars b.
     memory_rel c be ts refs sp st m dm (CONS (v,w) vars) /\ good_dimindex (:A) /\
     dest_Boolv v = SOME b ==>
     v = data_Boolv b /\ w = wl_Word (if b then word 18 else word 2)`,
  REPEAT GEN_TAC THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[dest_Boolv_def; option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  DRULE_ALL memory_rel_Block_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A word` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[data_Boolv_def; bool_to_tag_def; true_tag_def; false_tag_def;
                  injectivity "data_v"; injectivity "word_loc"] THEN
  UNDISCH_TAC `a1 < 2` THEN SPEC_TAC(`a1:num`,`k:num`) THEN
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

let ASP5AUX_DIV_SMALL = prove
 (`!n i. n < 32 /\ ~(i < 5) ==> n DIV 2 EXP i = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 5` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* bitwise operations on small numerals (HOL4: EVAL of n2w ?? n2w) *)
let ASP5AUX_SMALL_BITWISE_TAC : tactic =
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 5` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
      `i < 5 ==> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[ASP5AUX_DIV_SMALL; ARITH]];;

let ASP5AUX_xor_16 = prove
 (`word_xor (word 18) (word 16):A word = word 2 /\
   word_xor (word 2) (word 16):A word = word 18`,
  CONJ_TAC THEN ASP5AUX_SMALL_BITWISE_TAC);;

(* the state_rel part of the end of an assign proof: after the evaluation,  *)
(* the goal ?q r. (NONE,r0) = (q,r) /\ ... with r0 the word state with the *)
(* result in adjust_var dest (and maybe temporaries in odd locals); leaves  *)
(* the memory_rel goal of the result                                        *)
let ASP5AUX_FINISH_TAC : tactic =
  ASP4AUX_NONE_TAC THEN
  MATCH_MP_TAC ASP5AUX_state_rel_finish THEN CONJ_TAC THENL
   [REPEAT (GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 1`))] ORELSE
            GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 3`))] ORELSE
            GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 5`))] ORELSE
            GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 7`))]) THEN
    ASM_REWRITE_TAC[ASP5AUX_locals_fupd_id];
    REWRITE_TAC[MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 1`));
                MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 3`));
                MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 5`));
                MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 7`))]];;

(* the memory_rel goal of a Boolv result *)
(* the memory_rel goal of the rest: an assumption with one or two values   *)
(* (the arguments) in front                                                 *)
let ASP5AUX_MEM_TL_TAC : tactic =
  FIRST_ASSUM(fun th g ->
    try ACCEPT_TAC(MATCH_MP memory_rel_tl th) g with Failure _ ->
    ACCEPT_TAC(MATCH_MP memory_rel_tl (MATCH_MP memory_rel_tl th)) g);;

let ASP5AUX_BOOLV_MEM_TAC : tactic =
  (MATCH_MP_TAC memory_rel_Boolv_T ORELSE MATCH_MP_TAC memory_rel_Boolv_F) THEN
  ASM_REWRITE_TAC[] THEN ASP5AUX_MEM_TL_TAC;;

(* the memory_rel goal of a small Number result (the word is Smallnum i)    *)
let ASP5AUX_NUMBER_MEM_TAC : tactic =
  MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASP5AUX_MEM_TL_TAC;;

(* the same for a result word_shl (word n) 2 (IMP_memory_rel_Number_num)    *)
let ASP5AUX_NUM_MEM_TAC : tactic =
  MATCH_MP_TAC IMP_memory_rel_Number_num THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASP5AUX_MEM_TL_TAC;;

(* the equations assign c secn l dest op args names = match args with ... *)
let ASP5AUX_ASSIGN_EQ_TAC def : tactic =
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(REWR_CONV data_to_word_assign_def)) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_arg1_def; data_to_word_arg2_def; def] THEN
  STRUCT_CASES_TAC(ISPEC `args:num list` list_CASES) THEN CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `t:num list` list_CASES) THEN CASE_REWRITE_TAC[] THEN
  TRY(STRUCT_CASES_TAC(ISPEC `t':num list` list_CASES) THEN CASE_REWRITE_TAC[]);;

let ASP5AUX_do_app_BoolNot = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp BoolNot) vs s = Rval (v,s2) <=>
     ?v1 b. vs = [v1] /\ dest_Boolv v1 = SOME b /\ v = data_Boolv (~b) /\
            s2 = do_stack (BlockOp BoolNot) vs (do_lim_safe s (BlockOp BoolNot) vs)`,
  ASP5AUX_DO_APP_TAC `BlockOp BoolNot` []);;

let ASP5AUX_ival_small = prove
 (`!n. good_dimindex (:A) /\ n < 2 EXP 31 ==> ival (word n:A word) = &n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_IWORD] THEN MATCH_MP_TAC IVAL_IWORD THEN
  SUBGOAL_THEN `2 EXP 31 <= 2 EXP (dimindex(:A) - 1)` MP_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl) o REWRITE_RULE[good_dimindex_def]) THEN
    ARITH_TAC;
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT; INT_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_disj (concl th)) &&
      can (find_term ((=) `n:num`)) (concl th))) THEN
    ARITH_TAC]);;

let ASP5AUX_word_18_2 = prove
 (`good_dimindex (:A) ==> ~(word 18 = (word 2:A word)) /\ ~(word 2 = (word 18:A word))`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV);;

let ASP5AUX_do_app_BoolTest = prove
 (`!test vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (BoolTest test)) vs s = Rval (v,s2) <=>
     ?v1 v2 b1 b2. vs = [v1;v2] /\ dest_Boolv v1 = SOME b1 /\ dest_Boolv v2 = SOME b2 /\
            v = data_Boolv (b1 = b2) /\
            s2 = do_stack (BlockOp (BoolTest test)) vs
                   (do_lim_safe s (BlockOp (BoolTest test)) vs)`,
  ASP5AUX_DO_APP_TAC `BlockOp (BoolTest test)` []);;

(* proves  f op vs = SOME r <=> ?.. vs = [..] /\ ...  for f = data_do_int_app *)
(* or data_do_word_app (def its definition), vs of length 1 or 2            *)
let ASP5AUX_APP_TAC (def:thm) (extra:thm list) : tactic =
  let rws = [def; option_DISTINCT; option_INJ; CONS_11; NOT_CONS_NIL;
             distinctness "data_v"; injectivity "data_v"; COND_CASE_EQ] @ extra in
  REPEAT GEN_TAC THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [CASE_REWRITE_TAC rws; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [ASP4AUX_DV_CASES_TAC `x1:data_v` THEN CASE_REWRITE_TAC rws THEN MESON_TAC[]; ALL_TAC] THEN
  ASP4AUX_DV_CASES_TAC `x1:data_v` THEN ASP4AUX_DV_CASES_TAC `x2:data_v` THEN
  CASE_REWRITE_TAC rws THEN
  TRY(ASP4AUX_LIST_CASES_TAC `t2:data_v list` `x3:data_v` `t3:data_v list` THEN
      CASE_REWRITE_TAC rws) THEN
  MESON_TAC[];;

let ASP5AUX_int_app_LessConstSmall = prove
 (`!i vs r. data_do_int_app (LessConstSmall i) vs = SOME r <=>
            ?j. vs = [data_Number j] /\ &0 <= j /\ j <= &1000000 /\ i < 1000000 /\
                r = data_Boolv (j < &i)`,
  ASP5AUX_APP_TAC data_do_int_app_def []);;

let ASP5AUX_do_app_LessConstSmall = prove
 (`!i vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp (LessConstSmall i)) vs s = Rval (v,s2) <=>
     ?j. vs = [data_Number j] /\ &0 <= j /\ j <= &1000000 /\ i < 1000000 /\
         v = data_Boolv (j < &i) /\
         s2 = do_stack (IntOp (LessConstSmall i)) vs
                (do_lim_safe s (IntOp (LessConstSmall i)) vs)`,
  ASP5AUX_DO_APP_TAC `IntOp (LessConstSmall i)` [ASP5AUX_int_app_LessConstSmall]);;

let ASP5AUX_dimword_DIV_8 = prove
 (`good_dimindex (:A) ==> 2 EXP 29 <= dimword (:A) DIV 8`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASP5AUX_small_int_num = prove
 (`!a. good_dimindex (:A) /\ a < 2 EXP 29 ==> small_int (:A) (&a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[small_int_def] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP5AUX_dimword_DIV_8) THEN
  UNDISCH_TAC `a < 2 EXP 29` THEN REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;

let ASP5AUX_word_small_cmp = prove
 (`!a b. good_dimindex (:A) /\ a < 2 EXP 32 /\ b < 2 EXP 32 ==>
         ((word a:A word = word b) <=> a = b) /\
         (word_ult (word a:A word) (word b) <=> a < b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; WORD_ULT] THEN
  ASM_SIMP_TAC[ASP2AUX_VAL_WORD_SMALL]);;

let ASP5AUX_word_app_WordTest = prove
 (`!ws test vs r. data_do_word_app (WordTest ws test) vs = SOME r <=>
     ws = W8 /\
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\
             &0 <= n1 /\ n1 < &256 /\ &0 <= n2 /\ n2 < &256 /\
             ((test = Equal /\ r = data_Boolv (n1 = n2)) \/
              (test = Compare Lt /\ r = data_Boolv (n1 < n2)) \/
              (test = Compare Leq /\ r = data_Boolv (n1 <= n2)))`,
  REPEAT GEN_TAC THEN CASES_ON `ws:word_size` THEN
  REWRITE_TAC[distinctness "word_size"] THEN
  CASES_ON `test:test` THEN TRY(CASES_ON `a:opb`) THEN
  REWRITE_TAC[distinctness "test"; injectivity "test"; distinctness "opb"] THEN
  SPEC_TAC(`r:data_v`,`r:data_v`) THEN SPEC_TAC(`vs:data_v list`,`vs:data_v list`) THEN
  ASP5AUX_APP_TAC data_do_word_app_def []);;

let ASP5AUX_do_app_WordTest = prove
 (`!ws test vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (WordTest ws test)) vs s = Rval (v,s2) <=>
     ws = W8 /\
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\
             &0 <= n1 /\ n1 < &256 /\ &0 <= n2 /\ n2 < &256 /\
             ((test = Equal /\ v = data_Boolv (n1 = n2)) \/
              (test = Compare Lt /\ v = data_Boolv (n1 < n2)) \/
              (test = Compare Leq /\ v = data_Boolv (n1 <= n2))) /\
             s2 = do_stack (WordOp (WordTest ws test)) vs
                    (do_lim_safe s (WordOp (WordTest ws test)) vs)`,
  ASP5AUX_DO_APP_TAC `WordOp (WordTest ws test)` [ASP5AUX_word_app_WordTest]);;

(* two small natural-number arguments: their words (HOL4: memory_rel_Number_IMP *)
(* twice)                                                                     *)
let ASP5AUX_memory_rel_Number2_num = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm k1 k2 w1 w2 vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number (&k1),w1) (CONS (data_Number (&k2),w2) vars)) ==>
     good_dimindex (:A) /\ k1 < 2 EXP 29 /\ k2 < 2 EXP 29 ==>
     w1 = wl_Word (word (4 * k1)) /\ w2 = wl_Word (word (4 * k2))`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tl) THEN
  REWRITE_TAC[GSYM MP6AUX_SMALLNUM_NUM] THEN
  MATCH_MP_TAC memory_rel_Number_IMP THEN ASM_SIMP_TAC[ASP5AUX_small_int_num] THEN
  ASM_MESON_TAC[]);;

let ASP5AUX_do_app_LengthBlock = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp LengthBlock) vs s = Rval (v,s2) <=>
     ?ts tag xs. vs = [data_Block ts tag xs] /\ v = data_Number (&(LENGTH xs)) /\
            s2 = do_stack (BlockOp LengthBlock) vs (do_lim_safe s (BlockOp LengthBlock) vs)`,
  ASP5AUX_DO_APP_TAC `BlockOp LengthBlock` []);;

let ASP5AUX_val_word_lt = prove
 (`!k. k < dimindex (:A) ==> val (word k:A word) = k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `dimindex (:A)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL]);;

(* args = [a1] (resp. [a1;a2]) from the get_vars assumption *)
let ASP5AUX_args1_TAC : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC;;

let ASP5AUX_args2_TAC : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list`
    STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC;;

(* the shift amounts of the length computations are in range *)
let ASP5AUX_SHIFT_FACTS_TAC : tactic =
  SUBGOAL_THEN `dimindex (:A) - data_to_word_config_len_size c < dimindex (:A) /\
                ~(dimindex (:A) - data_to_word_config_len_size c >= dimindex (:A)) /\
                2 < dimindex (:A) /\ ~(2 >= dimindex (:A))` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def] o check (fun th ->
      can (find_term ((=) `good_dimindex (:A)`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `data_to_word_config_len_size c`)) (concl th) &&
      is_neg (concl th))) THEN
    ARITH_TAC;
    ALL_TAC];;

let ASP5AUX_DO_APP_STATE_RWS =
  [do_stack_def; do_lim_safe; LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM];;

let ASP5AUX_do_app_Length = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp Length) vs s = Rval (v,s2) <=>
     ?bl ptr xs. vs = [data_RefPtr bl ptr] /\
            lookup ptr (data_state_refs s) = SOME (bvl_ValueArray xs) /\
            v = data_Number (&(LENGTH xs)) /\
            s2 = do_stack (MemOp Length) vs (do_lim_safe s (MemOp Length) vs)`,
  ASP5AUX_DO_APP_TAC `MemOp Length` ASP5AUX_DO_APP_STATE_RWS);;

let ASP5AUX_do_app_LengthByte = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp LengthByte) vs s = Rval (v,s2) <=>
     ?bl ptr fl xs. vs = [data_RefPtr bl ptr] /\
            lookup ptr (data_state_refs s) = SOME (bvl_ByteArray fl xs) /\
            v = data_Number (&(LENGTH xs)) /\
            s2 = do_stack (MemOp LengthByte) vs (do_lim_safe s (MemOp LengthByte) vs)`,
  ASP5AUX_DO_APP_TAC `MemOp LengthByte` ASP5AUX_DO_APP_STATE_RWS);;

let ASP5AUX_word_add_sub = prove
 (`!n k. word_sub (word (n + k)) (word k):A word = word n`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_SUB]);;

(* HOL4 line 11024 *)
(* the case dimindex (:A) = D of assign_LengthByte: the shift amount is   *)
(* (D - S) - len_size, the header is shifted back to LENGTH xs + B         *)
let ASP5AUX_LENGTHBYTE_CASE_TAC (d:int) (b:int) : tactic =
  let dn = mk_small_numeral d and bn = mk_small_numeral b in
  let sh = if d = 32 then 2 else 3 in
  let k = mk_small_numeral (d - sh) in
  let dimeq = mk_eq(`dimindex (:A)`, dn) in
  let sub_eq = ARITH_RULE (mk_eq(`(dd - l) - ss:num`,`kk - l:num`) |>
     subst [dn,`dd:num`; mk_small_numeral sh,`ss:num`; k,`kk:num`]) in
  let kl = mk_comb(mk_comb(`(-):num->num->num`,k),`data_to_word_config_len_size c`) in
  let facts = list_mk_conj
    [mk_eq(mk_comb(`val:A word->num`,mk_comb(`word:num->A word`,kl)),kl);
     mk_neg(mk_comb(mk_comb(`(>=):num->num->bool`,kl),dn));
     `val (word 2:A word) = 2`] in
  RULE_ASSUM_TAC(fun th -> if is_eq (concl th) && lhs (concl th) = `dimindex (:A)` then th
    else REWRITE_RULE[ASSUME dimeq; sub_eq] th) THEN
  REWRITE_TAC[backend_common_word_shift_def; bytes_in_word_def] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN facts STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      mk_comb(mk_comb(`(<):num->num->bool`,`data_to_word_config_len_size c + 7`),dn))) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE (mk_comb(mk_comb(`(<):num->num->bool`,kl),
                                  `18446744073709551616`));
             ARITH_RULE (mk_comb(mk_comb(`(<):num->num->bool`,kl),`4294967296`))] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASP5AUX_EV_TAC ASP4AUX_EV_RWS THEN
  REWRITE_TAC[ASP5AUX_word_add_sub] THEN ASP5AUX_FINISH_TAC THEN
  MATCH_MP_TAC IMP_memory_rel_Number_num3 THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASP5AUX_MEM_TL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) bn)) (concl th) &&
    can (find_term ((=) `LENGTH (xs:byte list)`)) (concl th) &&
    is_comb (concl th) && fst (strip_comb (concl th)) = `(<):num->num->bool`)) THEN
  ARITH_TAC;;

let ASP5AUX_do_app_BoundsCheckBlock = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp BoundsCheckBlock) vs s = Rval (v,s2) <=>
     ?ts tag ys i. vs = [data_Block ts tag ys; data_Number i] /\
            v = data_Boolv (&0 <= i /\ i < &(LENGTH ys)) /\
            s2 = do_stack (BlockOp BoundsCheckBlock) vs
                   (do_lim_safe s (BlockOp BoundsCheckBlock) vs)`,
  ASP5AUX_DO_APP_TAC `BlockOp BoundsCheckBlock` []);;

(* the second argument of a bounds check is a Number: its word is a Word  *)
let ASP5AUX_memory_rel_snd_Number = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x1 w1 i w2 vars.
     memory_rel c be ts refs sp st m dm (CONS (x1,w1) (CONS (data_Number i,w2) vars)) /\
     good_dimindex (:A) ==> ?wi. w2 = wl_Word wi`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tl) THEN
  DRULE_ALL memory_rel_any_Number_IMP THEN MESON_TAC[]);;

(* the bounds check of Number i against a length n (a word n), both ways   *)
let ASP5AUX_bounds_check = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x1 w1 i wi vars n.
     memory_rel c be ts refs sp st m dm
       (CONS (x1,w1) (CONS (data_Number i,wl_Word wi) vars)) /\
     good_dimindex (:A) /\ n < 2 EXP (dimindex (:A) - 4) ==>
     (word_ult (word_ror wi 2) (word n) <=> &0 <= i /\ i < &n) /\
     (~word_ult (word n) (word_ror wi 2) <=> &0 <= i /\ i <= &n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tl) THEN
  MP_TAC(ISPECL [`n:num`] MP4AUX_small_int_LT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_bounds_check THEN
  REWRITE_TAC[WORD_ULT; WORD_ULE; NOT_LT] THEN SIMP_TAC[]);;

(* rewrite the bounds comparison word_ult (word_ror wi 2) (word n) of the  *)
(* code with the data comparison (n the length n_tm)                       *)
let ASP5AUX_BOUNDS_TAC (n_tm:term) : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] ASP5AUX_bounds_check) o
    check (fun th -> is_comb (concl th) && is_const (fst (strip_comb (concl th))) &&
                     fst (dest_const (fst (strip_comb (concl th)))) = "memory_rel")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC n_tm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);;

let ASP5AUX_do_app_BoundsCheckArray = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp BoundsCheckArray) vs s = Rval (v,s2) <=>
     ?bl ptr ws i. vs = [data_RefPtr bl ptr; data_Number i] /\
            lookup ptr (data_state_refs s) = SOME (bvl_ValueArray ws) /\
            v = data_Boolv (&0 <= i /\ i < &(LENGTH ws)) /\
            s2 = do_stack (MemOp BoundsCheckArray) vs
                   (do_lim_safe s (MemOp BoundsCheckArray) vs)`,
  ASP5AUX_DO_APP_TAC `MemOp BoundsCheckArray` ASP5AUX_DO_APP_STATE_RWS);;

let ASP5AUX_do_app_BoundsCheckByte = prove
 (`!leq vs (s:(C,FFI)data_state) v s2.
     data_do_app (MemOp (BoundsCheckByte leq)) vs s = Rval (v,s2) <=>
     ?bl ptr fl ws i. vs = [data_RefPtr bl ptr; data_Number i] /\
            lookup ptr (data_state_refs s) = SOME (bvl_ByteArray fl ws) /\
            v = data_Boolv (&0 <= i /\ (if leq then (<=) else (<)) i (&(LENGTH ws))) /\
            s2 = do_stack (MemOp (BoundsCheckByte leq)) vs
                   (do_lim_safe s (MemOp (BoundsCheckByte leq)) vs)`,
  ASP5AUX_DO_APP_TAC `MemOp (BoundsCheckByte leq)` ASP5AUX_DO_APP_STATE_RWS);;

let ASP5AUX_small_int_len3 = prove
 (`!n. good_dimindex (:A) /\ n < 2 EXP (dimindex (:A) - 3) ==> small_int (:A) (&n)`,
  REWRITE_TAC[good_dimindex_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[small_int_def; dimword_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `n:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ASP5AUX_bounds_check3 = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x1 w1 i wi vars n.
     memory_rel c be ts refs sp st m dm
       (CONS (x1,w1) (CONS (data_Number i,wl_Word wi) vars)) /\
     good_dimindex (:A) /\ n < 2 EXP (dimindex (:A) - 3) ==>
     (word_ult (word_ror wi 2) (word n) <=> &0 <= i /\ i < &n) /\
     (~word_ult (word n) (word_ror wi 2) <=> &0 <= i /\ i <= &n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tl) THEN
  MP_TAC(ISPECL [`n:num`] ASP5AUX_small_int_len3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DRULE_ALL memory_rel_bounds_check THEN
  REWRITE_TAC[WORD_ULT; WORD_ULE; NOT_LT] THEN SIMP_TAC[]);;

let ASP5AUX_BOUNDS3_TAC (n_tm:term) : tactic =
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] ASP5AUX_bounds_check3) o
    check (fun th -> is_comb (concl th) && is_const (fst (strip_comb (concl th))) &&
                     fst (dest_const (fst (strip_comb (concl th)))) = "memory_rel")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC n_tm) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]);;

(* one dimension case of assign_BoundsCheckByte *)
let ASP5AUX_BOUNDSBYTE_CASE_TAC (d:int) : tactic =
  let dn = mk_small_numeral d in
  let ex = mk_small_numeral (if d = 32 then 2 else 3) in
  let dimeq = mk_eq(`dimindex (:A)`, dn) in
  let kl = mk_comb(mk_comb(`(-):num->num->num`,
             mk_comb(mk_comb(`(-):num->num->num`,dn),`data_to_word_config_len_size c`)),ex) in
  let facts = list_mk_conj
    [mk_eq(mk_comb(`val:A word->num`,mk_comb(`word:num->A word`,kl)),kl);
     mk_neg(mk_comb(mk_comb(`(>=):num->num->bool`,kl),dn));
     `val (word 2:A word) = 2`;
     `LENGTH (ws:byte list) < 2 EXP (dimindex (:A) - 3)`;
     mk_comb(mk_comb(`(<):num->num->bool`,`LENGTH (ws:byte list)`),
             rhs (concl (NUM_REDUCE_CONV (mk_comb(mk_comb(`(EXP):num->num->num`,`2`),
                                                  mk_small_numeral (d - 3))))))] in
  RULE_ASSUM_TAC(fun th -> if is_eq (concl th) && lhs (concl th) = `dimindex (:A)` then th
    else REWRITE_RULE[ASSUME dimeq] th) THEN
  REWRITE_TAC[bytes_in_word_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN facts STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      mk_comb(mk_comb(`(<):num->num->bool`,`data_to_word_config_len_size c + 7`),dn))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `LENGTH (ws:byte list)`)) (concl th) &&
      is_comb (concl th) && fst (strip_comb (concl th)) = `(<):num->num->bool`)) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE (mk_comb(mk_comb(`(<):num->num->bool`,kl),
                                  `18446744073709551616`));
             ARITH_RULE (mk_comb(mk_comb(`(<):num->num->bool`,kl),`4294967296`))] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  BOOL_CASES_TAC `leq:bool` THEN REWRITE_TAC[] THEN
  ASP5AUX_EV_TAC (wl_get_var_imm_def::ShiftVar_def::ASP4AUX_EV_RWS) THEN
  REWRITE_TAC[ASP5AUX_word_add_sub] THEN
  ASP5AUX_BOUNDS3_TAC `LENGTH (ws:byte list)` THEN
  COND_CASES_TAC THEN ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC;;

(* more rewrites for symbolic evaluation: calls, returns, list_Seq *)
let ASP5AUX_EV_RWS2 =
  [data_to_word_list_Seq_def; wl_get_vars_def; wl_get_var_imm_def; wl_flush_state_def;
   bad_dest_args_def; add_ret_loc_def; wl_find_code_def; wl_call_env_def; wl_dec_clock_def;
   wl_bad_fun_return_def] @ ASP4AUX_EV_RWS;;

(* abbreviate as v the state s of the first wl_evaluate (code,s) of the goal *)
let ASP5AUX_ABBREV_EV_TAC (code:term) (v:term) : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t -> match t with
      Comb(Const("wl_evaluate",_),arg) -> (try fst (dest_pair arg) = code with Failure _ -> false)
    | _ -> false) w in
  let x = snd (dest_pair (rand tm)) in
  ABBREV_TAC (mk_eq(v,x)) g;;

let ASP5AUX_val_sub1 = prove
 (`!l:A word. ~(l = word 0) ==> val (word_sub l (word 1)) = val l - 1`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* the end of a code proof that returns from t: the clock and the stack     *)
(* maximum of t                                                             *)
let ASP5AUX_RET_TAC : tactic =
  MAP_EVERY EXISTS_TAC [`wl_state_clock (t:(A,C,FFI)wl_state)`;
                        `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
  REWRITE_TAC[option_le_max_right; option_le_refl; PAIR_EQ; ARITH_RULE `a <= b + a:num`] THEN
  REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];;

let ASP5AUX_IS_MEMREL th = is_comb (concl th) && is_const (fst (strip_comb (concl th))) &&
                           fst (dest_const (fst (strip_comb (concl th)))) = "memory_rel";;

let ASP5AUX_word_2_0 = prove
 (`good_dimindex (:A) ==> ~(word 2 = word 0:A word)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV);;

let ASP5AUX_word_cmp_res_swap = prove
 (`!i1 i2. ~(i2 = i1) /\ good_dimindex (:A) ==>
           (word_cmp_res i1 i2:A word) =
           (if (word_cmp_res i2 i1:A word) = word 0 then word 2 else word 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP5AUX_word_2_0) THEN
  SUBGOAL_THEN `~((i1:int) = i2)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[word_cmp_res_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(i1:int) < i2` THENL
   [SUBGOAL_THEN `~((i2:int) < i1)` ASSUME_TAC THENL [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(i2:int) < i1` ASSUME_TAC THENL [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let ASP5AUX_int_app_Less = prove
 (`!vs r. data_do_int_app clos_Less vs = SOME r <=>
          ?n1 n2. vs = [data_Number n1; data_Number n2] /\ r = data_Boolv (n1 < n2)`,
  ASP5AUX_APP_TAC data_do_int_app_def []);;

let ASP5AUX_int_app_LessEq = prove
 (`!vs r. data_do_int_app LessEq vs = SOME r <=>
          ?n1 n2. vs = [data_Number n1; data_Number n2] /\ r = data_Boolv (n1 <= n2)`,
  ASP5AUX_APP_TAC data_do_int_app_def []);;

(* the do_app equation of an operator with a space reset *)
let ASP5AUX_DO_APP_RESET_TAC op_tm int_th : tactic =
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [op_tm; `vs:data_v list`; `s:(C,FFI)data_state`] ASP4AUX_DO_APP_RESET) THEN
  REWRITE_TAC[op_space_reset_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "int_op"; distinctness "block_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[case_eq "option"; distinctness "result"; injectivity "result"; PAIR_EQ;
              int_th] THEN
  MESON_TAC[];;

let ASP5AUX_do_app_Less = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp clos_Less) vs s = Rval (v,s2) <=>
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\ v = data_Boolv (n1 < n2) /\
             s2 = do_stack (IntOp clos_Less) vs
                    (do_lim_safe (THE (do_space (IntOp clos_Less) vs s)) (IntOp clos_Less) vs)`,
  ASP5AUX_DO_APP_RESET_TAC `IntOp clos_Less` ASP5AUX_int_app_Less);;

let ASP5AUX_do_app_LessEq = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (IntOp LessEq) vs s = Rval (v,s2) <=>
     ?n1 n2. vs = [data_Number n1; data_Number n2] /\ v = data_Boolv (n1 <= n2) /\
             s2 = do_stack (IntOp LessEq) vs
                    (do_lim_safe (THE (do_space (IntOp LessEq) vs s)) (IntOp LessEq) vs)`,
  ASP5AUX_DO_APP_RESET_TAC `IntOp LessEq` ASP5AUX_int_app_LessEq);;

let ASP5AUX_code_rel_stubs = prove
 (`!c s_code (t_code:(num#(A)wl_prog)spt).
     data_to_word_gcProof_code_rel c s_code t_code ==>
     lookup Compare_location t_code = SOME (3,Compare_code c) /\
     lookup Compare1_location t_code = SOME (4,Compare1_code) /\
     lookup Equal_location t_code = SOME (3,Equal_code c) /\
     lookup Equal1_location t_code = SOME (4,Equal1_code)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_code_rel_def; data_to_word_stubs_def; ALL_APPEND; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* the final state_rel of an operator with a space reset (Less, LessEq,    *)
(* Equal): the data state is x after do_space, do_lim_safe, do_stack with  *)
(* dest set, the word state t with locals insert (adjust_var dest) w L and *)
(* a new stack_max sm and permute p                                         *)
let ASP5AUX_state_rel_finish_reset = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w L op vs sm p.
     op_space_reset op /\
     data_to_word_gcProof_state_rel c l1 l2 x (wl_state_locals_fupd (K L) t) NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps x)) (data_state_refs x) 0
       (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals x)
                   (toAList (sptree_inter L (adjust_set (data_state_locals x)))))
            (APPEND [(the_global (data_state_global x),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack x) (wl_state_stack t))))) /\
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t)) sm /\
     option_le sm (data_state_stack_max
       (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs))) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest v (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs)))
       (wl_state_stack_max_fupd (K sm) (wl_state_permute_fupd (K p)
          (wl_state_locals_fupd (K (insert (adjust_var dest) w L)) t))) NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `option_le sm (data_state_stack_max
      (do_stack op vs (do_lim_safe (THE (do_space op vs (x:(C,FFI)data_state))) op vs)))` THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
      (wl_state_locals_fupd (K L) (t:(A,C,FFI)wl_state)) NONE locs` THEN
  ASM_REWRITE_TAC[data_to_word_gcProof_state_rel_thm; do_space_def; THE_DEF; do_stack_def;
    do_lim_safe; LET_DEF; LET_END_DEF; data_set_var_def; data_state_INFO.ri_accfupds;
    wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[lookup_insert; adjust_var_NEQ];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `dest:num`)) (concl th) &&
      can (find_term ((=) `IS_SOME:(data_v)option->bool`)) (concl th))) THEN
    REWRITE_TAC[lookup_insert; adjust_var_11] THEN COND_CASES_TAC THEN
    REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC memory_rel_insert THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

let ASP5AUX_state_rel_finish_reset0 = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w L op vs.
     op_space_reset op /\
     data_to_word_gcProof_state_rel c l1 l2 x (wl_state_locals_fupd (K L) t) NONE locs /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps x)) (data_state_refs x) 0
       (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals x)
                   (toAList (sptree_inter L (adjust_set (data_state_locals x)))))
            (APPEND [(the_global (data_state_global x),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack x) (wl_state_stack t))))) /\
     option_le (data_state_stack_max x)
       (data_state_stack_max (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs))) ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_set_var dest v (do_stack op vs (do_lim_safe (THE (do_space op vs x)) op vs)))
       (wl_state_locals_fupd (K (insert (adjust_var dest) w L)) t) NONE locs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `x:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `dest:num`; `v:data_v`; `w:A word_loc`;
    `L:(A word_loc)spt`; `op:clos_op`; `vs:data_v list`;
    `wl_state_stack_max (t:(A,C,FFI)wl_state)`; `wl_state_permute (t:(A,C,FFI)wl_state)`]
    ASP5AUX_state_rel_finish_reset) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wl_state_stack_max_fupd (K (wl_state_stack_max (t:(A,C,FFI)wl_state)))
     (wl_state_permute_fupd (K (wl_state_permute t))
       (wl_state_locals_fupd (K (insert (adjust_var dest) (w:A word_loc) L)) t)) =
     wl_state_locals_fupd (K (insert (adjust_var dest) w L)) t` SUBST1_TAC THENL
   [REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o check (fun th ->
    can (find_term (fun u -> is_const u && fst (dest_const u) = "data_to_word_gcProof_state_rel"))
      (concl th))) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[option_le_trans]);;

(* the final state_rel when the data state s2 differs from x only in the    *)
(* space, the safety flags, the peak heap length and stack_max, and the     *)
(* word state is t with locals insert (adjust_var dest) w L, a new          *)
(* stack_max sm and permute p                                               *)
let ASP5AUX_state_rel_finish_sp = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs dest v w L sm p
    (s2:(C,FFI)data_state).
     data_to_word_gcProof_state_rel c l1 l2 x (wl_state_locals_fupd (K L) t) NONE locs /\
     data_state_ffi s2 = data_state_ffi x /\
     data_state_clock s2 = data_state_clock x /\
     data_state_handler s2 = data_state_handler x /\
     data_state_code s2 = data_state_code x /\
     data_state_compile s2 = data_state_compile x /\
     data_state_compile_oracle s2 = data_state_compile_oracle x /\
     data_state_locals s2 = data_state_locals x /\
     data_state_stack s2 = data_state_stack x /\
     data_state_stack_frame_sizes s2 = data_state_stack_frame_sizes x /\
     data_state_locals_size s2 = data_state_locals_size x /\
     data_state_limits s2 = data_state_limits x /\
     data_state_global s2 = data_state_global x /\
     data_state_refs s2 = data_state_refs x /\
     data_state_tstamps s2 = data_state_tstamps x /\
     memory_rel c (wl_state_be t) (THE (data_state_tstamps x)) (data_state_refs x)
       (data_state_space s2) (wl_state_store t) (wl_state_memory t) (wl_state_mdomain t)
       (CONS (v,w)
         (APPEND (join_env (data_state_locals x)
                   (toAList (sptree_inter L (adjust_set (data_state_locals x)))))
            (APPEND [(the_global (data_state_global x),FAPPLY (wl_state_store t) Globals)]
               (data_to_word_gcProof_flat (data_state_stack x) (wl_state_stack t))))) /\
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t)) sm /\
     option_le sm (data_state_stack_max s2) ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_set_var dest v s2)
       (wl_state_stack_max_fupd (K sm) (wl_state_permute_fupd (K p)
          (wl_state_locals_fupd (K (insert (adjust_var dest) w L)) t))) NONE locs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
      (wl_state_locals_fupd (K L) (t:(A,C,FFI)wl_state)) NONE locs` THEN
  ASM_REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_set_var_def;
    data_state_INFO.ri_accfupds; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[lookup_insert; adjust_var_NEQ];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `dest:num`)) (concl th) &&
      can (find_term ((=) `IS_SOME:(data_v)option->bool`)) (concl th))) THEN
    REWRITE_TAC[lookup_insert; adjust_var_11] THEN COND_CASES_TAC THEN
    REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC memory_rel_insert THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `CONS ((v:data_v),(w:A word_loc))`)) (concl th))) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]]);;

(* the stack bounds of a call of a comparison stub (Less, LessEq, Equal)   *)
let ASP5AUX_OPTION_CASES_TAC : tactic =
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC (ISPEC v (cases "option")))
    [`smt:num option`; `smx:num option`; `sz:num option`; `ls:num option`;
     `cm:num option`; `cm1:num option`; `m:num option`] THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def; option_DISTINCT] THEN ARITH_TAC;;

let ASP5AUX_call_stack_bounds = prove
 (`!smt smx sz ls cm cm1 m.
     option_le smt smx /\
     option_le (OPTION_MAP2 (+) sz ls) smt /\
     option_le (OPTION_MAP2 MAX (OPTION_MAP2 MAX smt (OPTION_MAP2 (+) ls sz))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls sz) cm)) m /\
     option_le m (OPTION_MAP2 MAX (OPTION_MAP2 MAX (OPTION_MAP2 MAX smt (OPTION_MAP2 (+) ls sz))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls sz) cm))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls sz) cm1)) ==>
     option_le (OPTION_MAP2 (+) sz ls) m /\
     option_le m (OPTION_MAP2 MAX smx (OPTION_MAP2 (+) (OPTION_MAP2 MAX cm cm1)
                                        (OPTION_MAP2 (+) sz ls)))`,
  ASP5AUX_OPTION_CASES_TAC);;

let ASP5AUX_state_rel_stack_facts = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 x t v locs ==>
     option_le (wl_state_stack_max t) (data_state_stack_max x) /\
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t)) (wl_state_locals_size t))
       (wl_state_stack_max t) /\
     wl_state_stack_size t = data_state_stack_frame_sizes x /\
     wl_state_locals_size t = data_state_locals_size x /\
     size_of_stack (data_state_stack x) = wl_stack_size (wl_state_stack t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC stack_rel_IMP_size_of_stack THEN ASM_REWRITE_TAC[]);;

(* the common start of the assign proofs of operators that need the names: *)
(* names_opt = SOME kept, the cut state x, the cut word locals y           *)
let ASP5AUX_INTRO_NAMES_TAC (intro:tactic) : tactic =
  REPEAT GEN_TAC THEN intro THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def; op_space_reset_def;
    distinctness "clos_op"; injectivity "clos_op"; distinctness "block_op";
    distinctness "int_op"]) THEN
  SUBGOAL_THEN `?kept. names_opt = SOME (kept:1 spt)` (X_CHOOSE_THEN `kept:1 spt` SUBST_ALL_TAC)
  THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term ((=) `names_opt:(1 spt)option`)) (concl th))) THEN
    REWRITE_TAC[] THEN STRUCT_CASES_TAC(ISPEC `names_opt:(1 spt)option` (cases "option")) THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_state_rel_facts) THEN
  DRULE_ALL state_rel_cut_state_opt_SOME THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(A word_loc)spt` (X_CHOOSE_THEN `ws:(A word_loc)list`
    STRIP_ASSUME_TAC));;

(* the state_rel/memory_rel of the end of an operator with a space reset    *)
let ASP5AUX_RESET0_TAC : tactic =
  ASP4AUX_NONE_TAC THEN MATCH_MP_TAC ASP5AUX_state_rel_finish_reset0 THEN
  REWRITE_TAC[op_space_reset_def] THEN REPEAT CONJ_TAC THENL
   [REPEAT (GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 1`))] ORELSE
            GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 3`))] ORELSE
            GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 5`))]) THEN
    ASM_REWRITE_TAC[ASP5AUX_locals_fupd_id];
    REWRITE_TAC[MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 1`));
                MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 3`));
                MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 5`))] THEN
    (MATCH_MP_TAC memory_rel_Boolv_T ORELSE MATCH_MP_TAC memory_rel_Boolv_F) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC memory_rel_zero_space THEN
    EXISTS_TAC `data_state_space (x:(C,FFI)data_state)` THEN
    MATCH_MP_TAC ASP1AUX_state_rel_memory_rel THEN ASM_MESON_TAC[];
    REWRITE_TAC[do_stack_def; do_lim_safe; do_space_def; op_space_reset_def; THE_DEF;
                LET_DEF; LET_END_DEF; data_state_INFO.ri_accfupds; K_THM;
                option_le_max_right; option_le_refl]];;

let ASP5AUX_CALL_FINISH_TAC : tactic =
  CONJ_TAC THENL
   [REPEAT (GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 1`))] ORELSE
            GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 3`))] ORELSE
            GEN_REWRITE_TAC I [MATCH_MP ASP1AUX_state_rel_insert_odd
                                (EQT_ELIM (NUM_REDUCE_CONV `ODD 5`))]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 1`));
                MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 3`));
                MATCH_MP inter_insert_ODD_adjust_set_alt (EQT_ELIM (NUM_REDUCE_CONV `ODD 5`))] THEN
    (MATCH_MP_TAC memory_rel_Boolv_T ORELSE MATCH_MP_TAC memory_rel_Boolv_F) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC memory_rel_zero_space THEN
    EXISTS_TAC `data_state_space (x:(C,FFI)data_state)` THEN
    FIRST_ASSUM(fun th ->
      let th' = MATCH_MP ASP1AUX_state_rel_memory_rel th in
      MP_TAC th' THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
      DISCH_THEN ACCEPT_TAC)];;

(* the end of the call case of Less and LessEq *)
let ASP5AUX_CMP_END_TAC : tactic =
  (SUBGOAL_THEN `!X. wl_state_locals_fupd (K X)
     (wl_state_locals_size_fupd (K (wl_state_locals_size t))
     (wl_state_stack_fupd (K (wl_state_stack t))
     (wl_state_stack_max_fupd (K smx)
     (wl_state_permute_fupd (K perm)
     (wl_state_clock_fupd (K (wl_state_clock t))
     (wl_state_termdep_fupd (K (wl_state_termdep t)) (t:(A,C,FFI)wl_state))))))) =
     wl_state_stack_max_fupd (K smx) (wl_state_permute_fupd (K perm)
       (wl_state_locals_fupd (K X) t))` (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   COND_CASES_TAC THEN ASP4AUX_NONE_TAC THEN
   MATCH_MP_TAC ASP5AUX_state_rel_finish_sp THEN
   EXISTS_TAC `x:(C,FFI)data_state` THEN
   REWRITE_TAC[do_stack_def; do_space_def; op_space_reset_def; THE_DEF; LET_DEF; LET_END_DEF;
               data_state_INFO.ri_accfupds; K_THM]) THEN
  (UNDISCH_TAC `y = sptree_union y2 (y1:(A word_loc)spt)` THEN DISCH_THEN SUBST_ALL_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_stack_max_le o check (fun th -> is_eq (concl th) &&
     can (find_term ((=) `Compare_code c:(A)wl_prog`)) (lhs (concl th)))) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_state_rel_stack_facts o check (fun th ->
     concl th = `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
                   (t:(A,C,FFI)wl_state) NONE locs`)) THEN
   UNDISCH_TAC `option_le smx (OPTION_MAP2 MAX (wl_state_stack_max (t1:(A,C,FFI)wl_state))
     (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1))
        (lookup Compare1_location (wl_state_stack_size t1))))` THEN
   EXPAND_TAC "t1" THEN
   REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; stack_size_eq2; stack_size_frame_def] THEN
   REPEAT DISCH_TAC THEN
   MP_TAC(ISPECL [`wl_state_stack_max (t:(A,C,FFI)wl_state)`;
                  `data_state_stack_max (x:(C,FFI)data_state)`;
                  `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state))`;
                  `wl_state_locals_size (t:(A,C,FFI)wl_state)`;
                  `lookup Compare_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`;
                  `lookup Compare1_location (wl_state_stack_size (t:(A,C,FFI)wl_state))`;
                  `smx:num option`] ASP5AUX_call_stack_bounds) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[stack_consumed_def] THEN
   REWRITE_TAC[GSYM(ASSUME `wl_state_stack_size (t:(A,C,FFI)wl_state) =
                            data_state_stack_frame_sizes (x:(C,FFI)data_state)`);
               GSYM(ASSUME `wl_state_locals_size (t:(A,C,FFI)wl_state) =
                            data_state_locals_size (x:(C,FFI)data_state)`)] THEN
   ASM_REWRITE_TAC[]) THEN
  ASP5AUX_CALL_FINISH_TAC;;

let ASP5AUX_not_ilt = prove
 (`!v1 v2:A word. ~word_ilt v2 v1 <=> word_ilt v1 v2 \/ v1 = v2`,
  REWRITE_TAC[WORD_ILT; GSYM IVAL_EQ] THEN INT_ARITH_TAC);;

let ASP5AUX_do_app_EqualConst_Int0 = prove
 (`!i vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (EqualConst (clos_Int i))) vs s = Rval (v,s2) <=>
     ?j. vs = [data_Number j] /\ v = data_Boolv (i = j) /\
         s2 = do_stack (BlockOp (EqualConst (clos_Int i))) vs
                (do_lim_safe s (BlockOp (EqualConst (clos_Int i))) vs)`,
  ASP5AUX_DO_APP_TAC `BlockOp (EqualConst (clos_Int i))` []);;

let ASP5AUX_do_app_EqualConst_W640 = prove
 (`!i vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (EqualConst (clos_W64 i))) vs s = Rval (v,s2) <=>
     ?j. vs = [data_Word64 j] /\ v = data_Boolv (i = j) /\
         s2 = do_stack (BlockOp (EqualConst (clos_W64 i))) vs
                (do_lim_safe s (BlockOp (EqualConst (clos_W64 i))) vs)`,
  ASP5AUX_DO_APP_TAC `BlockOp (EqualConst (clos_W64 i))` []);;

(* the same with the data comparison j = i (the order of the code)          *)
let ASP5AUX_do_app_EqualConst_Int = prove
 (`!i vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (EqualConst (clos_Int i))) vs s = Rval (v,s2) <=>
     ?j. vs = [data_Number j] /\ v = data_Boolv (j = i) /\
         s2 = do_stack (BlockOp (EqualConst (clos_Int i))) vs
                (do_lim_safe s (BlockOp (EqualConst (clos_Int i))) vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ASP5AUX_do_app_EqualConst_Int0] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  SUBGOAL_THEN `((i:int) = j) <=> (j = i)` SUBST1_TAC THENL
   [MESON_TAC[]; REWRITE_TAC[]]);;

let ASP5AUX_do_app_EqualConst_W64 = prove
 (`!i vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (EqualConst (clos_W64 i))) vs s = Rval (v,s2) <=>
     ?j. vs = [data_Word64 j] /\ v = data_Boolv (j = i) /\
         s2 = do_stack (BlockOp (EqualConst (clos_W64 i))) vs
                (do_lim_safe s (BlockOp (EqualConst (clos_W64 i))) vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ASP5AUX_do_app_EqualConst_W640] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  SUBGOAL_THEN `((i:int64) = j) <=> (j = i)` SUBST1_TAC THENL
   [MESON_TAC[]; REWRITE_TAC[]]);;

let ASP5AUX_do_app_EqualConst_Str = prove
 (`!i vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp (EqualConst (clos_Str i))) vs s = Rval (v,s2) <=>
     ?bl ptr j. vs = [data_RefPtr bl ptr] /\
         lookup ptr (data_state_refs s) = SOME (bvl_ByteArray T j) /\
         v = data_Boolv (j = MAP (word o ORD) (explode i)) /\
         s2 = do_stack (BlockOp (EqualConst (clos_Str i))) vs
                (do_lim_safe s (BlockOp (EqualConst (clos_Str i))) vs)`,
  ASP5AUX_DO_APP_TAC `BlockOp (EqualConst (clos_Str i))` ASP5AUX_DO_APP_STATE_RWS);;

let ASP5AUX_do_app_EqualConst_Con = prove
 (`!t ns vs (s:(C,FFI)data_state) v s2.
     ~(data_do_app (BlockOp (EqualConst (clos_Con t ns))) vs s = Rval (v,s2))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`BlockOp (EqualConst (clos_Con t ns))`; `vs:data_v list`;
                 `s:(C,FFI)data_state`] ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "block_op"] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[data_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
  CASE_REWRITE_TAC[distinctness "result"]);;

let ASP5AUX_val_word_ORD = prove
 (`!x. val (word (ORD x):byte) = ORD x`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[ORD_BOUND]);;

let ASP5AUX_some_pair = prove
 (CASE_TERM
  `!(P:A->B->bool) (f:A->B->C option) r.
     (match (some (x,y). P x y) with NONE -> NONE | SOME (x,y) -> f x y) = SOME r ==>
     ?x y. P x y /\ f x y = SOME r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  SPEC_TAC(`@p. (\(x,y). (P:A->B->bool) x y) p`,`pr:A#B`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `pr:A#B` PAIR_SURJECTIVE) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let ASP5AUX_word_app_WordOpW8 = prove
 (`!opw vs r. data_do_word_app (WordOpw W8 opw) vs = SOME r ==>
     ?w1 w2:byte. vs = [data_Number (&(val w1)); data_Number (&(val w2))] /\
                  r = data_Number (&(val (opw_lookup opw w1 w2)))`,
  REPEAT GEN_TAC THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
    CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t2:data_v list` `x3:data_v` `t3:data_v list` THENL
   [ALL_TAC;
    ASP4AUX_DV_CASES_TAC `x1:data_v` THEN ASP4AUX_DV_CASES_TAC `x2:data_v` THEN
    CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]] THEN
  ASP4AUX_DV_CASES_TAC `x1:data_v` THEN ASP4AUX_DV_CASES_TAC `x2:data_v` THEN
  CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ASP5AUX_some_pair) THEN
  REWRITE_TAC[option_INJ; CONS_11; injectivity "data_v"] THEN MESON_TAC[]);;

let ASP5AUX_do_app_WordOpW8 = prove
 (`!opw vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (WordOpw W8 opw)) vs s = Rval (v,s2) ==>
     ?w1 w2:byte. vs = [data_Number (&(val w1)); data_Number (&(val w2))] /\
            v = data_Number (&(val (opw_lookup opw w1 w2))) /\
            s2 = do_stack (WordOp (WordOpw W8 opw)) vs
                   (do_lim_safe s (WordOp (WordOpw W8 opw)) vs)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`WordOp (WordOpw W8 opw)`; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "word_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[case_eq "option"; distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:data_v` (CONJUNCTS_THEN2
    (MP_TAC o MATCH_MP ASP5AUX_word_app_WordOpW8) STRIP_ASSUME_TAC)) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`w1:byte`; `w2:byte`] THEN ASM_MESON_TAC[]);;

let ASP5AUX_dimindex_10 = prove
 (`good_dimindex (:A) ==> dimindex (:A) = (dimindex (:A) - 10) + 10 /\
                          2 EXP dimindex (:A) = 2 EXP (dimindex (:A) - 10) * 1024 /\
                          1024 <= 2 EXP dimindex (:A)`,
  REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASP5AUX_val_ushr_shl_10 = prove
 (`!x:A word. good_dimindex (:A) ==>
     val (word_ushr (word_shl x (dimindex (:A) - 10)) (dimindex (:A) - 10)) = val x MOD 1024`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_dimindex_10) THEN
  ASM_REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_SHL; MOD_MULT2] THEN
  MATCH_MP_TAC DIV_MULT THEN REWRITE_TAC[EXP_EQ_0; ARITH]);;

let ASP5AUX_val_small = prove
 (`!n. good_dimindex (:A) /\ n < 1024 ==> val (word n:A word) = n`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_dimindex_10) THEN
  REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let ASP5AUX_MOD_MOD_1024 = prove
 (`!m p. (m MOD (p * 1024)) MOD 1024 = m MOD 1024`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MOD]);;

let ASP5AUX_carried_add = prove
 (`!w1 w2:byte. good_dimindex (:A) ==>
     word_ushr (word_shl (word_add (word (4 * val w1)) (word (4 * val w2)))
                 (dimindex (:A) - 10)) (dimindex (:A) - 10) =
     (word (4 * val (word_add w1 w2)):A word)`,
  (REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_dimindex_10) THEN
  MP_TAC(ISPEC `w1:byte` VAL_BOUND) THEN MP_TAC(ISPEC `w2:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[ASP5AUX_val_ushr_shl_10] THEN
  REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV) THEN
  (SUBGOAL_THEN `4 * (val (w1:byte) + val (w2:byte)) MOD 256 < 1024` ASSUME_TAC THENL
    [MP_TAC(SPECL [`val (w1:byte) + val (w2:byte)`; `256`] MOD_LT_EQ) THEN ARITH_TAC;
     ALL_TAC] THEN
   ASM_SIMP_TAC[ASP5AUX_val_small; ARITH_RULE `a < 256 ==> 4 * a < 1024`] THEN
   REWRITE_TAC[ASP5AUX_MOD_MOD_1024] THEN
   REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; ARITH_RULE `1024 = 4 * 256`; MOD_MULT2]));;

let ASP5AUX_carried_sub = prove
 (`!w1 w2:byte. good_dimindex (:A) ==>
     word_ushr (word_shl (word_sub (word (4 * val w1)) (word (4 * val w2)))
                 (dimindex (:A) - 10)) (dimindex (:A) - 10) =
     (word (4 * val (word_sub w1 w2)):A word)`,
  (REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_dimindex_10) THEN
  MP_TAC(ISPEC `w1:byte` VAL_BOUND) THEN MP_TAC(ISPEC `w2:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[ASP5AUX_val_ushr_shl_10] THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `4 * (val (w1:byte) + (256 - val (w2:byte))) MOD 256 < 1024` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val (w1:byte) + (256 - val (w2:byte))`; `256`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ASP5AUX_val_small; ARITH_RULE `a < 256 ==> 4 * a < 1024`] THEN
  REWRITE_TAC[ASP5AUX_MOD_MOD_1024] THEN
  SUBGOAL_THEN `4 * val (w1:byte) + (2 EXP (dimindex (:A) - 10) * 1024 - 4 * val (w2:byte)) =
                (2 EXP (dimindex (:A) - 10) - 1) * 1024 + 4 * (val w1 + (256 - val w2))`
    SUBST1_TAC THENL
   [MP_TAC(SPECL [`2`; `dimindex (:A) - 10`] EXP_EQ_0) THEN
    UNDISCH_TAC `val (w2:byte) < 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `1024 = 4 * 256`; MOD_MULT2]));;

let ASP5AUX_extract_vals = prove
 (`!x:int64. dimindex (:A) = 32 ==>
     val (word_extract 31 0 x:A word) = val x MOD 4294967296 /\
     val (word_extract 63 32 x:A word) = val x DIV 4294967296 /\
     val x DIV 4294967296 < 4294967296`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. word_extract 31 0 (word n:int64):A word = word (n MOD 4294967296) /\
                    word_extract 63 32 (word n:int64):A word =
                    word ((n DIV 4294967296) MOD 4294967296)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[word_extract_n2w; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITS_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (x:int64) DIV 4294967296 < 4294967296` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `x:int64` WORD_VAL)] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL]);;

let ASP5AUX_DIV_SMALL2 = prove
 (`!x n. x < 2 * n ==> x DIV n = if n <= x then 1 else 0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `x - n` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC]);;

let ASP5AUX_ADD_DIV_N = prove
 (`!a b n. ~(n = 0) ==>
     (a + b) DIV n = a DIV n + b DIV n + (a MOD n + b MOD n) DIV n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `n:num`] DIVISION) THEN MP_TAC(SPECL [`b:num`; `n:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a + b = (a DIV n + b DIV n) * n + (a MOD n + b MOD n)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[DIV_MULT_ADD] THEN ARITH_TAC]);;

let ASP5AUX_add64_on_32 = prove
 (`!c' c'':int64. dimindex (:A) = 32 ==>
  word (val (word_extract 31 0 c':A word) + val (word_extract 31 0 c'':A word)) =
  (word_extract 31 0 (word_add c' c''):A word) /\
  word ((val (word_extract 63 32 c':A word) + val (word_extract 63 32 c'':A word)) +
        (if dimword (:A) <= val (word_extract 31 0 c':A word) + val (word_extract 31 0 c'':A word)
         then 1 else 0)) =
  (word_extract 63 32 (word_add c' c''):A word)`,
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[ASP5AUX_extract_vals]) THEN
  (ASM_REWRITE_TAC[VAL_WORD; VAL_WORD_ADD; DIMINDEX_64; dimword_def]) THEN
  (CONV_TAC NUM_REDUCE_CONV THEN
   SUBGOAL_THEN `18446744073709551616 = 4294967296 * 4294967296` SUBST1_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   REWRITE_TAC[MOD_ADD_MOD; MOD_MOD]) THEN
  (REWRITE_TAC[GSYM DIV_MOD]) THEN
  (MP_TAC(SPECL [`val (c':int64)`; `val (c'':int64)`; `4294967296`] ASP5AUX_ADD_DIV_N) THEN
   REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC ASP5AUX_DIV_SMALL2 THEN
   MP_TAC(SPECL [`val (c':int64)`; `4294967296`] MOD_LT_EQ) THEN
   MP_TAC(SPECL [`val (c'':int64)`; `4294967296`] MOD_LT_EQ) THEN ARITH_TAC));;

let ASP5AUX_sub_arith = prove
 (`!a1 a2 b1 b2. a1 < 4294967296 /\ a2 < 4294967296 /\ b1 < 4294967296 /\ b2 < 4294967296 ==>
     ((a1 + (4294967295 - b1)) + 1) MOD 4294967296 =
     ((a2 * 4294967296 + a1) + (4294967296 * 4294967296 - (b2 * 4294967296 + b1))) MOD
     4294967296 /\
     ((a2 + (4294967295 - b2)) +
      (if 4294967296 <= (a1 + (4294967295 - b1)) + 1 then 1 else 0)) MOD 4294967296 =
     (((a2 * 4294967296 + a1) + (4294967296 * 4294967296 - (b2 * 4294967296 + b1))) DIV
      4294967296) MOD 4294967296`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a2 * 4294967296 + a1) + (4294967296 * 4294967296 - (b2 * 4294967296 + b1)) =
                (a2 + (4294967295 - b2)) * 4294967296 + ((a1 + (4294967295 - b1)) + 1)`
    SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC ASP5AUX_DIV_SMALL2 THEN ASM_ARITH_TAC);;

let ASP5AUX_sub64_on_32 = prove
 (`!c' c'':int64. dimindex (:A) = 32 ==>
  word ((val (word_extract 31 0 c':A word) + val (word_not (word_extract 31 0 c'':A word))) + 1) =
  (word_extract 31 0 (word_sub c' c''):A word) /\
  word ((val (word_extract 63 32 c':A word) + val (word_not (word_extract 63 32 c'':A word))) +
        (if dimword (:A) <= (val (word_extract 31 0 c':A word) +
                             val (word_not (word_extract 31 0 c'':A word))) + 1
         then 1 else 0)) =
  (word_extract 63 32 (word_sub c' c''):A word)`,
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NOT] THEN ASM_SIMP_TAC[ASP5AUX_extract_vals] THEN
   ASM_REWRITE_TAC[VAL_WORD; VAL_WORD_SUB; DIMINDEX_64; dimword_def] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   SUBGOAL_THEN `18446744073709551616 = 4294967296 * 4294967296` SUBST1_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
   REWRITE_TAC[MOD_MOD; GSYM DIV_MOD] THEN
   MP_TAC(SPECL [`val (c':int64) MOD 4294967296`; `val (c':int64) DIV 4294967296`;
                 `val (c'':int64) MOD 4294967296`; `val (c'':int64) DIV 4294967296`]
     ASP5AUX_sub_arith) THEN
   MP_TAC(SPECL [`val (c':int64)`; `4294967296`] DIVISION) THEN
   MP_TAC(SPECL [`val (c'':int64)`; `4294967296`] DIVISION) THEN
   ASM_SIMP_TAC[ASP5AUX_extract_vals; ARITH_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
   ASM_REWRITE_TAC[]));;

let ASP5AUX_inst_AddCarry = prove
 (CASE_TERM
  `!r1 r2 r3 r4 (s:(A,C,FFI)wl_state).
     wl_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) s =
     match wl_get_vars [r2;r3;r4] s with
       SOME [wl_Word l; wl_Word r; wl_Word c] ->
         SOME (wl_set_var r4 (wl_Word (if dimword (:A) <= (val l + val r) +
                                             (if c = word 0 then 0 else 1)
                                       then word 1 else word 0))
                 (wl_set_var r1 (wl_Word (word ((val l + val r) +
                                             (if c = word 0 then 0 else 1)))) s))
     | _ -> NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_add_carry_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[]);;

let ASP5AUX_bool_word_0 = prove
 (`!b. ((if b then word 1 else word 0:A word) = word 0) <=> ~b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1; VAL_WORD_0] THEN ARITH_TAC);;

let ASP5AUX_insert_29_31 = prove
 (`!(a:A) b t. insert 29 a (insert 31 b t) = insert 31 b (insert 29 a t) /\
               insert 29 a (insert 33 b t) = insert 33 b (insert 29 a t) /\
               insert 29 a (insert 27 b t) = insert 27 b (insert 29 a t) /\
               insert 27 a (insert 33 b t) = insert 33 b (insert 27 a t)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [insert_insert] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ?x1 .. xn. L = R x1 .. xn: the witnesses by matching R against L *)
let ASP5AUX_EXISTS_MATCH_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let l,r = dest_eq body in
  let (_,tmi,tyi) = term_match [] r l in
  (MAP_EVERY (fun v -> EXISTS_TAC (try rev_assoc v tmi with Failure _ -> v)) vs THEN
   REWRITE_TAC[]) g;;

let ASP5AUX_header_pair = prove
 (CASE_TERM
  `!(x:(A#B)option) (y:(A#B)option) (f:A->B->A->B->C option) r.
     (match (x,y) with (SOME (a1,h1),SOME (a2,h2)) -> f a1 h1 a2 h2 | _ -> NONE) = SOME r ==>
     ?a1 h1 a2 h2. x = SOME (a1,h1) /\ y = SOME (a2,h2) /\ f a1 h1 a2 h2 = SOME r`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

let ASP5AUX_word_header_SOME = prove
 (`!c st (w:A word) dm m a h.
     word_header c st w dm m = SOME (a,h) <=>
     get_real_addr c st w = SOME a /\ a IN dm /\ m a = wl_Word h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_header_def] THEN
  STRUCT_CASES_TAC(ISPEC `get_real_addr c st (w:A word)` option_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `(m:A word->A word_loc) x` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; distinctness "word_loc";
                   injectivity "word_loc"] THEN
  ASM_MESON_TAC[injectivity "word_loc"; distinctness "word_loc"]);;

let ASP5AUX_and_pow2 = prove
 (`!h:A word. (word_and h (word 4) = word 0 <=> ~bit 2 h) /\
              (word_and h (word 16) = word 0 <=> ~bit 4 h)`,
  REWRITE_TAC[word_bit_test] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let ASP5AUX_and24 = prove
 (`!h:A word. good_dimindex (:A) ==>
     (word_and h (word 24) = word 16 <=> ~bit 3 h /\ bit 4 h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 < dimindex (:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD] THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th)) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 < n ==> 3 < n`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MESON_TAC[];
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i < 5` THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
        `i < 5 ==> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[ASP5AUX_DIV_SMALL; ARITH]]]);;

let ASP5AUX_RET3_TAC : tactic =
  MAP_EVERY EXISTS_TAC [`wl_state_clock (t:(A,C,FFI)wl_state)`;
                        `wl_state_permute (t:(A,C,FFI)wl_state)`;
                        `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
  ASM_REWRITE_TAC[option_le_max_right; option_le_refl; PAIR_EQ] THEN
  REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];;

(* split on tm, rewriting the goal and the assumptions with the case *)
let ASP5AUX_SPLIT_TAC (tm:term) : tactic =
  ASM_CASES_TAC tm THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[];;

(* a word_eq result SOME (r,l,ck) = SOME (res,l',wck') in the assumptions:  *)
(* the code returns r from t                                               *)
let ASP5AUX_EQ_RET_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
    is_eq c && is_comb (lhs c) &&
    (try fst (dest_const (rator (lhs c))) = "SOME" with Failure _ -> false) &&
    can (find_term (fun u -> try fst (dest_var u) = "res" with Failure _ -> false)) c)) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN ASP5AUX_RET3_TAC;;

(* the stack bounds of the calls in Equal_code and Equal1_code (HOL4:      *)
(* option_le_trans, option_le_max_right, eq_code_stack_max_sub1, ...)     *)
let ASP5AUX_opt_cases_tac (vs:term list) : tactic =
  MAP_EVERY (fun v -> STRUCT_CASES_TAC(ISPEC v option_CASES)) vs THEN
  REWRITE_TAC[OPTION_MAP2_THM; OPTION_MAP_DEF; option_le_def];;

let ASP5AUX_le_mult_suc = prove
 (`!k m. m <= (k + 1) * m`,
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

(* ARITH_TAC with m <= (k + 1) times m for the products (k + 1) times m of  *)
(* the goal                                                                 *)
let ASP5AUX_MULT_ARITH_TAC : tactic = fun (asl,w as g) ->
  let ps = setify (find_terms (fun t -> try
      let f,m = dest_comb t in let g1,km = dest_comb f in
      fst (dest_const g1) = "*" && is_comb km &&
      (let h,one = dest_comb km in rand h <> one && one = `1`)
    with Failure _ -> false) w) in
  (MAP_EVERY (fun p -> let km = rand (rator p) in
      MP_TAC(SPECL [lhand km; rand p] ASP5AUX_le_mult_suc)) ps THEN
   MAP_EVERY (fun p -> SPEC_TAC(p, genvar `:num`)) ps THEN ARITH_TAC) g;;

let ASP5AUX_eq_bound_tail = prove
 (`!smx sm ss k (tsz:num spt) x.
     (x = lookup Equal_location tsz \/ x = lookup Equal1_location tsz \/
      x = lookup Compare1_location tsz) /\
     option_le smx (OPTION_MAP2 MAX (OPTION_MAP2 MAX sm (OPTION_MAP2 (+) ss x))
                      (OPTION_MAP2 (+) ss (eq_code_stack_max (k + 1) tsz))) ==>
     option_le smx (OPTION_MAP2 MAX sm (OPTION_MAP2 (+) ss (eq_code_stack_max (k + 1) tsz)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_code_stack_max_def] THEN
  SPEC_TAC(`lookup Equal_location (tsz:num spt)`,`a:num option`) THEN
  SPEC_TAC(`lookup Equal1_location (tsz:num spt)`,`b:num option`) THEN
  SPEC_TAC(`lookup Compare1_location (tsz:num spt)`,`d:num option`) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  ASP5AUX_opt_cases_tac [`smx:num option`; `sm:num option`; `ss:num option`;
                         `a:num option`; `b:num option`; `d:num option`] THEN
  ASP5AUX_MULT_ARITH_TAC);;

let ASP5AUX_eq_bound_cmp = prove
 (`!smx sm ss k (tsz:num spt).
     option_le smx (OPTION_MAP2 MAX (OPTION_MAP2 MAX sm
                      (OPTION_MAP2 (+) ss (lookup Compare1_location tsz)))
                      (OPTION_MAP2 (+) ss (lookup Compare1_location tsz))) ==>
     option_le smx (OPTION_MAP2 MAX sm (OPTION_MAP2 (+) ss (eq_code_stack_max (k + 1) tsz)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_code_stack_max_def] THEN
  SPEC_TAC(`lookup Equal_location (tsz:num spt)`,`a:num option`) THEN
  SPEC_TAC(`lookup Equal1_location (tsz:num spt)`,`b:num option`) THEN
  SPEC_TAC(`lookup Compare1_location (tsz:num spt)`,`d:num option`) THEN
  REPEAT GEN_TAC THEN
  ASP5AUX_opt_cases_tac [`smx:num option`; `sm:num option`; `ss:num option`;
                         `a:num option`; `b:num option`; `d:num option`] THEN
  ASP5AUX_MULT_ARITH_TAC);;

let ASP5AUX_shift_lsl_mul = prove
 (`!w:A word. good_dimindex (:A) ==>
              word_shl w (backend_common_word_shift (:A)) = word_mul bytes_in_word w`,
  SIMP_TAC[shift_lsl] THEN REWRITE_TAC[WORD_MUL_SYM]);;

let ASP5AUX_cut_envs_0246 = prove
 (`!L:(A)spt. IS_SOME (lookup 0 L) /\ IS_SOME (lookup 2 L) /\ IS_SOME (lookup 4 L) /\
              IS_SOME (lookup 6 L) ==>
     cut_envs (insert 6 one (insert 4 one (insert 2 one (insert 0 one LN))),(LN:1 spt)) L =
     SOME (sptree_inter L (insert 6 one (insert 4 one (insert 2 one (insert 0 one (LN:1 spt))))),
           LN)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def; inter_LN] THEN
  REWRITE_TAC[domain_insert; domain_def; EMPTY_SUBSET] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; domain_lookup] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_EXISTS]) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let ASP5AUX_le_mult_pos = prove
 (`!k m. ~(k = 0) ==> m <= k * m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k = (k - 1) + 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

(* the bounds of the return from the call of Equal_code in Equal1_code    *)
let ASP5AUX_EQB_TAC (vs:term list) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_code_stack_max_def] THEN
  SPEC_TAC(`lookup Equal_location (tsz:num spt)`,`a:num option`) THEN
  SPEC_TAC(`lookup Equal1_location (tsz:num spt)`,`b:num option`) THEN
  SPEC_TAC(`lookup Compare1_location (tsz:num spt)`,`d:num option`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
     fst (dest_var (lhs (concl th))) = "ls" then SUBST_ALL_TAC th else NO_TAC) THEN
  (SUBGOAL_THEN `k - 1 + 1 = k` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM MP_TAC) THEN
  ASP5AUX_opt_cases_tac (vs @ [`sm:num option`;
    `ss:num option`; `a:num option`; `b:num option`; `d:num option`]) THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  W(fun (_,w) -> let ps = setify (find_terms (fun t -> try
        let f,m = dest_comb t in let g1,kk = dest_comb f in
        fst (dest_const g1) = "*" && kk = `k:num` with Failure _ -> false) w) in
     MAP_EVERY (fun p -> MP_TAC(SPECL [`k:num`; rand p] ASP5AUX_le_mult_pos)) ps THEN
     MAP_EVERY (fun p -> SPEC_TAC(p, genvar `:num`)) ps) THEN
  ARITH_TAC;;

let ASP5AUX_eq_bound_ret = prove
 (`!smx1 sm ss ls k (tsz:num spt).
     ~(k = 0) /\ (ls = lookup Equal_location tsz \/ ls = lookup Equal1_location tsz) /\
     option_le smx1
       (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX (OPTION_MAP2 MAX sm (OPTION_MAP2 (+) ls ss))
             (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls ss) (lookup Equal_location tsz)))
          (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls ss) (eq_code_stack_max (k - 1 + 1) tsz))) ==>
     option_le smx1 (OPTION_MAP2 MAX sm (OPTION_MAP2 (+) ss (eq_code_stack_max (k + 1) tsz)))`,
  ASP5AUX_EQB_TAC [`smx1:num option`]);;

let ASP5AUX_eq_bound_ret2 = prove
 (`!smx1 smx2 sm ss ls k (tsz:num spt).
     ~(k = 0) /\ (ls = lookup Equal_location tsz \/ ls = lookup Equal1_location tsz) /\
     option_le smx1
       (OPTION_MAP2 MAX
          (OPTION_MAP2 MAX (OPTION_MAP2 MAX sm (OPTION_MAP2 (+) ls ss))
             (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls ss) (lookup Equal_location tsz)))
          (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls ss) (eq_code_stack_max (k - 1 + 1) tsz))) /\
     option_le smx2
       (OPTION_MAP2 MAX (OPTION_MAP2 MAX smx1 (OPTION_MAP2 (+) ss (lookup Equal1_location tsz)))
          (OPTION_MAP2 (+) ss (eq_code_stack_max (k + 1) tsz))) ==>
     option_le smx2 (OPTION_MAP2 MAX sm (OPTION_MAP2 (+) ss (eq_code_stack_max (k + 1) tsz)))`,
  ASP5AUX_EQB_TAC [`smx1:num option`; `smx2:num option`]);;

let ASP5AUX_do_app_Equal = prove
 (`!vs (s:(C,FFI)data_state) v s2.
     data_do_app (BlockOp clos_Equal) vs s = Rval (v,s2) <=>
     ?x1 x2 b. vs = [x1; x2] /\ data_do_eq (data_state_refs s) x1 x2 = Eq_val b /\
               v = data_Boolv b /\
               s2 = do_stack (BlockOp clos_Equal) vs
                      (do_lim_safe (THE (do_space (BlockOp clos_Equal) vs s))
                         (BlockOp clos_Equal) vs)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`BlockOp clos_Equal`; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_RESET) THEN
  REWRITE_TAC[op_space_reset_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "int_op"; distinctness "block_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[ASP4AUX_refs_S1; op_space_reset_def] THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [CASE_REWRITE_TAC[data_do_app_aux_def; distinctness "result"; NOT_CONS_NIL]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [CASE_REWRITE_TAC[data_do_app_aux_def; distinctness "result"; NOT_CONS_NIL; CONS_11];
    ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t2:data_v list` `x3:data_v` `t3:data_v list` THENL
   [ALL_TAC;
    CASE_REWRITE_TAC[data_do_app_aux_def; distinctness "result"; NOT_CONS_NIL; CONS_11]] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  SIMP_TAC[ASP4AUX_refs_S1; op_space_reset_def] THEN
  REWRITE_TAC[case_eq "eq_result"; distinctness "result"; injectivity "result"; PAIR_EQ;
              CONS_11] THEN
  MESON_TAC[]);;

let ASP5AUX_cut_state_refs = prove
 (`!kept (s:(C,FFI)data_state) x.
     data_cut_state_opt (SOME kept) s = SOME x ==>
     data_state_refs x = data_state_refs s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  CASE_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `data_cut_env kept (data_state_locals (s:(C,FFI)data_state))`
    option_CASES) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

let ASP5AUX_equal_stack_bounds = prove
 (`!smt smx sz ls m k (tsz:num spt).
     option_le smt smx /\
     option_le (OPTION_MAP2 (+) sz ls) smt /\
     option_le (OPTION_MAP2 MAX (OPTION_MAP2 MAX smt (OPTION_MAP2 (+) ls sz))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls sz) (lookup Equal_location tsz))) m /\
     option_le m (OPTION_MAP2 MAX (OPTION_MAP2 MAX (OPTION_MAP2 MAX smt (OPTION_MAP2 (+) ls sz))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls sz) (lookup Equal_location tsz)))
                  (OPTION_MAP2 (+) (OPTION_MAP2 (+) ls sz) (eq_code_stack_max (k + 1) tsz))) ==>
     option_le (OPTION_MAP2 (+) sz ls) m /\
     option_le m (OPTION_MAP2 MAX smx (OPTION_MAP2 (+) (eq_code_stack_max (k + 1) tsz)
                                        (OPTION_MAP2 (+) sz ls)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_code_stack_max_def] THEN
  SPEC_TAC(`lookup Equal_location (tsz:num spt)`,`a:num option`) THEN
  SPEC_TAC(`lookup Equal1_location (tsz:num spt)`,`b:num option`) THEN
  SPEC_TAC(`lookup Compare1_location (tsz:num spt)`,`d:num option`) THEN
  REPEAT GEN_TAC THEN
  ASP5AUX_opt_cases_tac [`smt:num option`; `smx:num option`; `sz:num option`;
                         `ls:num option`; `m:num option`;
                         `a:num option`; `b:num option`; `d:num option`] THEN
  ASP5AUX_MULT_ARITH_TAC);;

let ASP5AUX_MIN_SUC = prove
 (`!a b. MIN (a + 1) (b + 1) = MIN a b + 1`,
  REWRITE_TAC[MIN] THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let ASP5AUX_DO_APP_SPACE3 = prove
 (`!op vs (s:(C,FFI)data_state) v s2.
     ~op_space_reset op /\ op_space_req op (LENGTH vs) = 3 /\ ~(op = clos_Install) /\
     ~(MEM op [IntOp Greater; IntOp GreaterEq]) /\
     data_do_app op vs s = Rval (v,s2) ==>
     3 <= data_state_space s /\
     data_do_app_aux op vs (do_stack op vs (do_lim_safe
        (data_state_space_fupd (K (data_state_space s - 3)) s) op vs)) = Rval (v,s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `data_do_app op vs (s:(C,FFI)data_state) = Rval (v,s2)` THEN
  ASM_REWRITE_TAC[data_do_app_def; do_space_def; consume_space_def; ARITH_EQ] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[distinctness "result"] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let ASP5AUX_word_app_WordOpW64 = prove
 (`!opw vs r. data_do_word_app (WordOpw W64 opw) vs = SOME r ==>
     ?w1 w2:int64. vs = [data_Word64 w1; data_Word64 w2] /\
                  r = data_Word64 (opw_lookup opw w1 w2)`,
  REPEAT GEN_TAC THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
    CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t2:data_v list` `x3:data_v` `t3:data_v list` THENL
   [ALL_TAC;
    ASP4AUX_DV_CASES_TAC `x1:data_v` THEN ASP4AUX_DV_CASES_TAC `x2:data_v` THEN
    CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]] THEN
  ASP4AUX_DV_CASES_TAC `x1:data_v` THEN ASP4AUX_DV_CASES_TAC `x2:data_v` THEN
  CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  REWRITE_TAC[option_INJ; CONS_11; injectivity "data_v"] THEN MESON_TAC[]);;

let ASP5AUX_do_app_WordOpW64 = prove
 (`!opw vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (WordOpw W64 opw)) vs s = Rval (v,s2) ==>
     ?w1 w2:int64. vs = [data_Word64 w1; data_Word64 w2] /\
            v = data_Word64 (opw_lookup opw w1 w2) /\ 3 <= data_state_space s /\
            s2 = do_stack (WordOp (WordOpw W64 opw)) vs
                   (do_lim_safe (data_state_space_fupd (K (data_state_space s - 3)) s)
                      (WordOp (WordOpw W64 opw)) vs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`WordOp (WordOpw W64 opw)`; `vs:data_v list`; `s:(C,FFI)data_state`;
                 `v:data_v`; `s2:(C,FFI)data_state`] ASP5AUX_DO_APP_SPACE3) THEN
  ASM_REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
                  injectivity "clos_op"; distinctness "word_op"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `data_do_app_aux (WordOp (WordOpw W64 opw)) vs
     (do_stack (WordOp (WordOpw W64 opw)) vs (do_lim_safe
        (data_state_space_fupd (K (data_state_space s - 3)) (s:(C,FFI)data_state))
        (WordOp (WordOpw W64 opw)) vs)) = Rval (v,s2)` THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[case_eq "option"; distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:data_v` (CONJUNCTS_THEN2
    (MP_TAC o MATCH_MP ASP5AUX_word_app_WordOpW64) STRIP_ASSUME_TAC)) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`w1:int64`; `w2:int64`] THEN ASM_MESON_TAC[]);;

(* the GiveUp case of the Word64 results (HOL4: conj_tac >- metis_tac      *)
(* [option_le_trans, consume_space_stack_max] and the contradiction of     *)
(* encode_header c 3 len = NONE with lim_safe): len is 1 or 2              *)
let ASP5AUX_W64_GIVEUP_TAC (len:term) : tactic =
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
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
  DISCH_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ASP4AUX_state_rel_len_size th]) THEN
  SUBGOAL_THEN `~(1 < data_to_word_config_len_size c)` (fun th -> REWRITE_TAC[th]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; len] (INST_TYPE [`:A`,`:A`] ASP4AUX_encode_header_3)) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN ARITH_TAC;;

(* the 64-bit word operations on a 64-bit architecture (HOL4: sw = SOME    *)
(* (w2w w64) and w2w (w2w w64) = w64)                                      *)
let ASP5AUX_zx_opw = prove
 (`!w1 w2:int64. dimindex (:A) = 64 ==>
     (word_zx:A word->int64) (word_and (word_extract 63 0 w1) (word_extract 63 0 w2)) =
       word_and w1 w2 /\
     (word_zx:A word->int64) (word_or (word_extract 63 0 w1) (word_extract 63 0 w2)) =
       word_or w1 w2 /\
     (word_zx:A word->int64) (word_xor (word_extract 63 0 w1) (word_extract 63 0 w2)) =
       word_xor w1 w2 /\
     (word_zx:A word->int64) (word_add (word_extract 63 0 w1) (word_extract 63 0 w2)) =
       word_add w1 w2 /\
     (word_zx:A word->int64) (word_sub (word_extract 63 0 w1) (word_extract 63 0 w2)) =
       word_sub w1 w2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!w:int64. word_extract 63 0 w:A word = word_zx w` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC WORD_EXTRACT_ZX THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex (:A) <= dimindex (:64) /\ dimindex (:64) <= dimindex (:A)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[DIMINDEX_64; LE_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WORD_ZX_AND; GSYM WORD_ZX_OR; GSYM WORD_ZX_XOR; GSYM WORD_ZX_ADD;
               GSYM WORD_ZX_SUB; WORD_ZX_ZX]);;

(* the state of the first wl_evaluate (code,st) of the goal (after part 4's *)
(* asp4_callee_state)                                                        *)
let asp5_callee_state code (w:term) =
  let t = find_term (fun t ->
      try let f,a = dest_comb t in
          (match f with
             Const("wl_evaluate",_) -> fst (dest_pair a) = code
           | _ -> false)
      with Failure _ -> false) w in
  snd (dest_pair (rand t));;

(* the do_stack op vs _ of the goal: op and vs *)
let asp5_goal_op_vs (w:term) =
  let ds = find_term (fun t -> try fst (dest_const (fst (strip_comb t))) = "do_stack" &&
                                   length (snd (strip_comb t)) = 3
                               with Failure _ -> false) w in
  match snd (strip_comb ds) with [op; vs; _] -> op, vs | _ -> failwith "asp5_goal_op_vs";;

(* the end of a Word64 result on a 64-bit architecture: the goal is        *)
(* ?q r. wl_evaluate (WriteWord64 c a dest 3,st) = (q,r) /\ ... with the   *)
(* result word in local 3 of st; extra rewrites the result of the data     *)
(* state                                                                   *)
let ASP5AUX_WW64_FINISH_TAC (extra:thm list) : tactic =
  W(fun (_,w) ->
    let st = asp5_callee_state `WriteWord64 c a dest 3:(A)wl_prog` w in
    let l1t = rand (rand (rator st)) in
    let wv = rand (rand (rator l1t)) in
    let op, vs = asp5_goal_op_vs w in
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; l1t; `a:A word`; `dest:num`; wv;
      vs; op] ASP4AUX_WordFromInt_W64)) THEN
  (ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `kk:num` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[ASP4AUX_lookup_insert_ODD; ARITH] THEN NO_TAC) THEN
    ASM_REWRITE_TAC[lookup_insert];
    ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
    is_const h && fst(dest_const h) = "data_to_word_gcProof_state_rel" &&
    can (find_term (fun u -> try fst(dest_const u) = "word_zx" with Failure _ -> false))
      (concl th))) THEN
  ASM_SIMP_TAC extra;;

(* the end of a Word64 result w on a 32-bit architecture: the goal is      *)
(* ?q r. wl_evaluate (WriteWord64_on_32 c a dest 33 31,st) = (q,r) /\ ...  *)
(* with the halves of w in locals 33 (low) and 31 (high) of st              *)
let ASP5AUX_WW32_FINISH_TAC (wv:term) : tactic =
  W(fun (_,w) ->
    let st = asp5_callee_state `WriteWord64_on_32 c a dest 33 31:(A)wl_prog` w in
    let l1t = rand (rand (rator st)) in
    let op, vs = asp5_goal_op_vs w in
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; l1t; `a:A word`; `dest:num`;
      `33`; `31`; wv; vs; op] ASP4AUX_WordFromInt_W32)) THEN
  (ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `kk:num` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[ASP4AUX_lookup_insert_ODD; ARITH] THEN NO_TAC) THEN
    ASM_REWRITE_TAC[lookup_insert; ARITH];
    ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[option_DISTINCT];;

(* the Word64 arguments of a two-argument Word64 operation: their pointers, *)
(* addresses and headers (HOL4: drule0 memory_rel_Word64_IMP \\ imp_res_tac *)
(* memory_rel_tl \\ drule0 memory_rel_Word64_IMP)                          *)
let ASP5AUX_WORD64_ARGS_TAC : tactic =
  FIRST_ASSUM(fun th0 -> let th = check ASP5AUX_IS_MEMREL th0 in
    MP_TAC(MATCH_MP memory_rel_Word64_IMP
      (CONJ (MATCH_MP memory_rel_tl th) (ASSUME `good_dimindex (:A)`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr2:num` (X_CHOOSE_THEN `x2:A word` (X_CHOOSE_THEN `h2:A word`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(fun th0 -> let th = check ASP5AUX_IS_MEMREL th0 in
    MP_TAC(MATCH_MP memory_rel_Word64_IMP (CONJ th (ASSUME `good_dimindex (:A)`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr1:num` (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `h1:A word`
    STRIP_ASSUME_TAC)));;

(* the conditional facts dimindex (:A) < 64 of memory_rel_Word64_IMP, after *)
(* the case split on the word size                                          *)
let ASP5AUX_WORD64_CONDS_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
         CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[];;

(* the real addresses of the pointers ptr1 and ptr2 (HOL4: rpt_drule0       *)
(* get_var_get_real_addr_lemma)                                             *)
let ASP5AUX_REAL_ADDR2_TAC : tactic =
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word x1) /\
                wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a2)) =
                SOME (wl_Word x2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC get_var_get_real_addr_lemma THENL
     [EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word`;
      EXISTS_TAC `get_addr c ptr2 (wl_Word (word 0)):A word`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* A small decision procedure for the bit identities of the shifts below     *)
(* (HOL4: fs [fcpTheory.CART_EQ, word_lsl_def, word_lsr_def, ...] and the    *)
(* arithmetic case splits): after WORD_EQ_BITS_ALT and the BIT_WORD_ rules,  *)
(* the goal is a boolean combination of linear arithmetic atoms and atoms    *)
(* bit e w; ASP5AUX_ARITH_SPLIT_TAC splits on (or decides) the arithmetic    *)
(* atoms, ASP5AUX_BIT_UNIFY_TAC identifies the bit atoms with provably equal *)
(* indices (and removes those with indices out of range), then TAUT.         *)
(* ------------------------------------------------------------------------- *)
let asp5_num_rel tm =
  (is_comb tm && is_comb (rator tm) &&
   (let f = rator (rator tm) in
    is_const f && mem (fst (dest_const f)) ["<"; "<="; ">"; ">="] &&
    type_of (rand tm) = `:num`)) ||
  (is_eq tm && type_of (lhs tm) = `:num`);;

let asp5_is_bit tm =
  is_comb tm && is_comb (rator tm) &&
  (let f = rator (rator tm) in is_const f && fst (dest_const f) = "bit");;

let asp5_arith_hyps asl =
  filter (fun t -> asp5_num_rel t || (is_neg t && asp5_num_rel (rand t)))
    (map (concl o snd) asl);;

let asp5_arith_prove hyps tm =
  try Some (ARITH_RULE (if hyps = [] then tm else mk_imp (list_mk_conj hyps, tm)))
  with Failure _ -> None;;

let rec ASP5AUX_ARITH_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let hyps = asp5_arith_hyps asl in
  let atoms = setify (find_terms (fun t -> asp5_num_rel t &&
                                   not (exists (fun h -> h = t || h = mk_neg t) hyps)) w) in
  if atoms = [] then ALL_TAC g else
  let rec decide l =
    match l with
      [] -> None
    | a::rest ->
        (match asp5_arith_prove hyps a with
           Some th -> Some (if hyps = [] then th else
                              MP th (end_itlist CONJ (map ASSUME hyps)))
         | None ->
           (match asp5_arith_prove hyps (mk_neg a) with
              Some th -> Some (if hyps = [] then th else
                                 MP th (end_itlist CONJ (map ASSUME hyps)))
            | None -> decide rest)) in
  let use th = RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th THEN
                TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
                ASM_REWRITE_TAC[] in
  match decide atoms with
    Some th -> (use th THEN ASP5AUX_ARITH_SPLIT_TAC) g
  | None -> (ASM_CASES_TAC (hd atoms) THEN POP_ASSUM use THEN ASP5AUX_ARITH_SPLIT_TAC) g;;

let ASP5AUX_BIT_UNIFY_TAC : tactic = fun (asl,w as g) ->
  let hyps = asp5_arith_hyps asl in
  let hth = if hyps = [] then TRUTH else end_itlist CONJ (map ASSUME hyps) in
  let prove tm = match asp5_arith_prove hyps tm with
      Some th -> Some (if hyps = [] then th else MP th hth)
    | None -> None in
  let bits = setify (find_terms asp5_is_bit w) in
  let rec classes l acc =
    match l with
      [] -> acc
    | b::rest ->
        let e = rand (rator b) and x = rand b in
        let same, other = partition (fun b2 -> rand b2 = x &&
          prove (mk_eq(rand (rator b2), e)) <> None) rest in
        classes other ((b, same)::acc) in
  let cls = classes bits [] in
  let ths = flat (map (fun (b, same) ->
      map (fun b2 -> let e = rand (rator b) and e2 = rand (rator b2) in
             match prove (mk_eq(e2, e)) with
               Some th -> AP_THM (AP_TERM (rator (rator b)) th) (rand b)
             | None -> failwith "ASP5AUX_BIT_UNIFY_TAC") same) cls) in
  (if ths = [] then ALL_TAC else PURE_REWRITE_TAC ths) g;;

(* the whole procedure for an equation of words; dims rewrites the        *)
(* dimindex terms to numerals                                              *)
let ASP5AUX_WORD_BITS_TAC (dims:thm list) : tactic =
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR; BIT_WORD_ISHR; BIT_WORD_ROR;
              BIT_WORD_EXTRACT; BIT_WORD_ZX; BIT_WORD_0; ADD_CLAUSES] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [BIT_GUARD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE dims) THEN REWRITE_TAC dims THEN
  ASP5AUX_ARITH_SPLIT_TAC THEN ASP5AUX_BIT_UNIFY_TAC THEN CONV_TAC TAUT;;

let ASP5AUX_some_single = prove
 (CASE_TERM
  `!(P:A->bool) (f:A->B option) r.
     (match (some x. P x) with NONE -> NONE | SOME x -> f x) = SOME r ==>
     ?x. P x /\ f x = SOME r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN MESON_TAC[]);;

let ASP5AUX_word_app_WordShiftW8 = prove
 (`!sh n vs r. data_do_word_app (WordShift W8 sh n) vs = SOME r ==>
     ?w:byte. vs = [data_Number (&(val w))] /\ r = data_Number (&(val (shift_lookup sh w n)))`,
  REPEAT GEN_TAC THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [ALL_TAC;
    ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
    CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]] THEN
  ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
  CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ASP5AUX_some_single) THEN
  REWRITE_TAC[option_INJ; CONS_11; injectivity "data_v"] THEN MESON_TAC[]);;

let ASP5AUX_do_app_WordShiftW8 = prove
 (`!sh n vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (WordShift W8 sh n)) vs s = Rval (v,s2) ==>
     ?w:byte. vs = [data_Number (&(val w))] /\
            v = data_Number (&(val (shift_lookup sh w n))) /\
            s2 = do_stack (WordOp (WordShift W8 sh n)) vs
                   (do_lim_safe s (WordOp (WordShift W8 sh n)) vs)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`WordOp (WordShift W8 sh n)`; `vs:data_v list`; `s:(C,FFI)data_state`]
    ASP4AUX_DO_APP_NOSPACE) THEN
  REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
              injectivity "clos_op"; distinctness "word_op"] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[case_eq "option"; distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:data_v` (CONJUNCTS_THEN2
    (MP_TAC o MATCH_MP ASP5AUX_word_app_WordShiftW8) STRIP_ASSUME_TAC)) THEN
  STRIP_TAC THEN EXISTS_TAC `w:byte` THEN ASM_MESON_TAC[]);;

let ASP5AUX_shift8_amounts = prove
 (`good_dimindex (:A) ==>
   dimindex(:A) - 10 < dimindex(:A) /\ ~(dimindex(:A) - 10 >= dimindex(:A)) /\
   (!n. dimindex(:A) - 10 + MIN n 8 < dimindex(:A)) /\
   (!n. ~(dimindex(:A) - 10 + MIN n 8 >= dimindex(:A))) /\
   (!n. MIN n 8 + 2 < dimindex(:A)) /\ (!n. ~(MIN n 8 + 2 >= dimindex(:A))) /\
   (!n. MIN n 8 < dimindex(:A)) /\ (!n. ~(MIN n 8 >= dimindex(:A))) /\
   dimindex(:A) - 8 < dimindex(:A) /\ ~(dimindex(:A) - 8 >= dimindex(:A)) /\
   2 < dimindex(:A) /\ ~(2 >= dimindex(:A))`,
  REWRITE_TAC[good_dimindex_def; MIN] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN TRY COND_CASES_TAC THEN ASM_ARITH_TAC);;

let ASP5AUX_word_4val = prove
 (`!w:byte. word (4 * val w):A word = word_shl (word_zx w) 2`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD_ZX_GEN] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_AC]);;

(* the four W8 shifts on the Smallnum representation word (4 times val w) *)
let ASP5AUX_SHIFT8_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN
  REWRITE_TAC[ASP5AUX_word_4val; MIN] THEN
  SUBGOAL_THEN `n MOD 8 < 8` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (fun th -> ASSUME_TAC th THEN
    ASP5AUX_WORD_BITS_TAC [DIMINDEX_8; DIMINDEX_64; th]));;

let ASP5AUX_shift8_Lsl = prove
 (`!(w:byte) n. good_dimindex (:A) ==>
     word_ushr (word_shl (word (4 * val w)) (dimindex (:A) - 10 + MIN n 8))
       (dimindex (:A) - 10) = word (4 * val (word_shl w n)):A word`,
  ASP5AUX_SHIFT8_TAC);;

let ASP5AUX_shift8_Lsr = prove
 (`!(w:byte) n. good_dimindex (:A) ==>
     word_shl (word_ushr (word (4 * val w)) (MIN n 8 + 2)) 2 =
     word (4 * val (word_ushr w n)):A word`,
  ASP5AUX_SHIFT8_TAC);;

let ASP5AUX_shift8_Asr = prove
 (`!(w:byte) n. good_dimindex (:A) ==>
     word_shl (word_ushr (word_ishr (word_shl (word (4 * val w)) (dimindex (:A) - 10))
       (MIN n 8)) (dimindex (:A) - 8)) 2 =
     word (4 * val (word_ishr w n)):A word`,
  ASP5AUX_SHIFT8_TAC);;

let ASP5AUX_shift8_Ror = prove
 (`!(w:byte) n. good_dimindex (:A) ==>
     word_or (word_shl (word_ushr (word (4 * val w)) (n MOD 8 + 2)) 2)
       (word_ushr (word_shl (word (4 * val w)) (dimindex (:A) - 2 - n MOD 8))
          (dimindex (:A) - 10)) =
     word (4 * val (word_ror w n)):A word`,
  ASP5AUX_SHIFT8_TAC);;

(* ShiftVar on the locals of a word state built by inserts (HOL4: once     *)
(* rewrite word_exp_set_var_ShiftVar_lemma \\ fs [lookup_insert]), in a     *)
(* form for the evaluator                                                   *)
let ASP5AUX_word_exp_ShiftVar_ins = prove
 (`(!sh (t:(A,C,FFI)wl_state) v n w L.
      wl_word_exp (wl_state_locals_fupd (K (insert v (wl_Word w) L)) t) (ShiftVar sh v n) =
      SOME (wl_Word (shift_lookup sh w n))) /\
   (!sh (t:(A,C,FFI)wl_state) v n k x L.
      ~(v = k) ==>
      wl_word_exp (wl_state_locals_fupd (K (insert k x L)) t) (ShiftVar sh v n) =
      wl_word_exp (wl_state_locals_fupd (K L) t) (ShiftVar sh v n))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[word_exp_set_var_ShiftVar_lemma] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
    CASES_ON `sh:shift` THEN CASE_REWRITE_TAC[shift_lookup_def; OPTION_MAP_DEF];
    DISCH_TAC THEN REWRITE_TAC[ShiftVar_def; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[wl_word_exp_def; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM;
                    lookup_insert; MAP]]);;

(* the goal (NONE,s1) = (NONE,s2) with s1, s2 the word state with the      *)
(* locals insert 31 (Word x) (insert 33 (Word y) L): x and y are equal by  *)
(* ASP5AUX_WORD_BITS_TAC                                                   *)
let ASP5AUX_LOCALS_EQ_TAC (dims:thm list) : tactic = fun (asl,w as g) ->
  let l, r = dest_eq w in
  let getws tm =
    let st = snd (dest_pair tm) in
    let lt = rand (rand (rator st)) in
    let x = rand (rand (rator lt)) in
    let y = rand (rand (rator (rand lt))) in x, y in
  let x1, y1 = getws l and x2, y2 = getws r in
  (SUBGOAL_THEN (mk_conj (mk_eq (x1, x2), mk_eq (y1, y2))) ASSUME_TAC THENL
    [CONJ_TAC THEN ASP5AUX_WORD_BITS_TAC dims; ASM_REWRITE_TAC[]]) g;;

let ASP5AUX_word_app_WordShiftW64 = prove
 (`!sh n vs r. data_do_word_app (WordShift W64 sh n) vs = SOME r ==>
     ?w:int64. vs = [data_Word64 w] /\ r = data_Word64 (shift_lookup sh w n)`,
  REPEAT GEN_TAC THEN
  ASP4AUX_LIST_CASES_TAC `vs:data_v list` `x1:data_v` `t1:data_v list` THENL
   [CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]; ALL_TAC] THEN
  ASP4AUX_LIST_CASES_TAC `t1:data_v list` `x2:data_v` `t2:data_v list` THENL
   [ALL_TAC;
    ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
    CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT]] THEN
  ASP4AUX_DV_CASES_TAC `x1:data_v` THEN
  CASE_REWRITE_TAC[data_do_word_app_def; option_DISTINCT] THEN
  REWRITE_TAC[option_INJ; CONS_11; injectivity "data_v"] THEN MESON_TAC[]);;

let ASP5AUX_do_app_WordShiftW64 = prove
 (`!sh n vs (s:(C,FFI)data_state) v s2.
     data_do_app (WordOp (WordShift W64 sh n)) vs s = Rval (v,s2) ==>
     ?w:int64. vs = [data_Word64 w] /\
            v = data_Word64 (shift_lookup sh w n) /\ 3 <= data_state_space s /\
            s2 = do_stack (WordOp (WordShift W64 sh n)) vs
                   (do_lim_safe (data_state_space_fupd (K (data_state_space s - 3)) s)
                      (WordOp (WordShift W64 sh n)) vs)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`WordOp (WordShift W64 sh n)`; `vs:data_v list`; `s:(C,FFI)data_state`;
                 `v:data_v`; `s2:(C,FFI)data_state`] ASP5AUX_DO_APP_SPACE3) THEN
  ASM_REWRITE_TAC[op_space_reset_def; op_space_req_def; MEM; distinctness "clos_op";
                  injectivity "clos_op"; distinctness "word_op"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `data_do_app_aux (WordOp (WordShift W64 sh n)) vs
     (do_stack (WordOp (WordShift W64 sh n)) vs (do_lim_safe
        (data_state_space_fupd (K (data_state_space s - 3)) (s:(C,FFI)data_state))
        (WordOp (WordShift W64 sh n)) vs)) = Rval (v,s2)` THEN
  CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[data_do_app_aux_def] THENC
                               CASE_REWRITE_CONV[]))) THEN
  REWRITE_TAC[case_eq "option"; distinctness "result"; injectivity "result"; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:data_v` (CONJUNCTS_THEN2
    (MP_TAC o MATCH_MP ASP5AUX_word_app_WordShiftW64) STRIP_ASSUME_TAC)) THEN
  STRIP_TAC THEN EXISTS_TAC `w:int64` THEN ASM_MESON_TAC[]);;

(* the 64-bit shifts on a 64-bit architecture (HOL4: WORD_w2w_EXTRACT and  *)
(* the bit equalities)                                                     *)
let ASP5AUX_zx_shift = prove
 (`!sh (w:int64) n. dimindex (:A) = 64 ==>
     (word_zx:A word->int64) (shift_lookup sh (word_extract 63 0 w) n) =
     shift_lookup sh w n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n MOD 64 < 64` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  CASES_ON `sh:shift` THEN REWRITE_TAC[shift_lookup_def] THEN
  ASP5AUX_WORD_BITS_TAC [DIMINDEX_64; ASSUME `dimindex(:A) = 64`]);;

(* HOL4 line 11024 *)
let assign_LengthByte = prove
 (assign_thm_stmt `op = MemOp LengthByte`,
  ASP5AUX_INTRO_TAC (DISCH_THEN SUBST1_TAC) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_LengthByte THEN
  DISCH_THEN(X_CHOOSE_THEN `bl:bool` (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `fl:bool`
    (X_CHOOSE_THEN `xs:byte list` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC THEN ASP5AUX_args1_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_LengthByte_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf) THEN
  DRULE_ALL memory_rel_ByteArray_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word a)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o check (fun th ->
    concl th = `good_dimindex (:A)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THENL
   [ASP5AUX_LENGTHBYTE_CASE_TAC 32 4; ASP5AUX_LENGTHBYTE_CASE_TAC 64 8]);;

(* HOL4 line 11083 *)
let assign_Length = prove
 (assign_thm_stmt `op = MemOp Length`,
  ASP5AUX_INTRO_TAC (DISCH_THEN SUBST1_TAC) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_Length THEN
  DISCH_THEN(X_CHOOSE_THEN `bl:bool` (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `xs:data_v list`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN ASP5AUX_args1_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_Length_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf) THEN
  DRULE_ALL memory_rel_ValueArray_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word a)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC] THEN
  ASP5AUX_SHIFT_FACTS_TAC THEN
  ASP5AUX_EV_TAC (ASP5AUX_val_word_lt::ASP4AUX_EV_RWS) THEN
  REWRITE_TAC[GSYM decode_length_def] THEN ASM_REWRITE_TAC[] THEN
  ASP5AUX_FINISH_TAC THEN ASP5AUX_NUM_MEM_TAC);;

(* HOL4 line 11134 *)
let assign_LengthBlock = prove
 (assign_thm_stmt `op = BlockOp LengthBlock`,
  ASP5AUX_INTRO_TAC (DISCH_THEN SUBST1_TAC) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_LengthBlock THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:num` (X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `xs:data_v list`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN ASP5AUX_args1_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_LengthBlock_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf) THEN
  DRULE_ALL memory_rel_Block_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASM_CASES_TAC `xs:data_v list = []` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RVEQ_TAC THENL
   [ASP5AUX_EV_TAC (wl_get_var_imm_def::data_to_word_gcProof_word_and_one_eq_0_iff::
                    ASP4AUX_EV_RWS) THEN
    ASP5AUX_FINISH_TAC THEN REWRITE_TAC[LENGTH] THEN
    SUBGOAL_THEN `word 0:A word = Smallnum (&0)` SUBST1_TAC THENL
     [REWRITE_TAC[MP6AUX_SMALLNUM_NUM; MULT_CLAUSES]; ALL_TAC] THEN
    ASP5AUX_NUMBER_MEM_TAC THEN MATCH_MP_TAC ASP5AUX_small_int_num THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                  SOME (wl_Word a)` ASSUME_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def];
      ALL_TAC] THEN
    ASP5AUX_SHIFT_FACTS_TAC THEN
    ASP5AUX_EV_TAC (wl_get_var_imm_def::data_to_word_gcProof_word_and_one_eq_0_iff::
                    ASP5AUX_val_word_lt::ASP4AUX_EV_RWS) THEN
    REWRITE_TAC[GSYM decode_length_def] THEN ASM_REWRITE_TAC[] THEN
    ASP5AUX_FINISH_TAC THEN ASP5AUX_NUM_MEM_TAC]);;

(* HOL4 line 11195 (the theorem of line 11214 rebinds the name; HOL4's      *)
(* overloads TRUE_CONST, FALSE_CONST and ShiftN are written out)            *)
let assign_BoundsCheckBlock = prove
 (CASE_TERM
  `!c secn l dest args names.
     data_to_word_assign c secn l dest (BlockOp BoundsCheckBlock) args names =
     match args with
       [v1;v2] ->
         (data_to_word_list_Seq
            [wl_If asm_Test (adjust_var v1) (Imm (word 1))
               (wl_Assign 1 (wl_Const (word 0)))
               (wl_Assign 1
                  (let addr = real_addr c (adjust_var v1) in
                   let header = wl_Load addr in
                   let k = dimindex (:A) - data_to_word_config_len_size c in
                     wl_Shift Lsr header (wl_Const (word k))));
             wl_Assign 3 (ShiftVar Ror (adjust_var v2) 2);
             wl_If Lower 3 (Reg 1)
               (wl_Assign (adjust_var dest) (wl_Const (word 18)))
               (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l)
     | _ -> (wl_Skip:(A)wl_prog,l)`,
  ASP5AUX_ASSIGN_EQ_TAC assign_BoundsCheckBlock_def);;

(* HOL4 line 11214 (allow_rebind) *)
let assign_BoundsCheckBlock = prove
 (assign_thm_stmt `op = BlockOp BoundsCheckBlock`,
  ASP5AUX_INTRO_TAC (DISCH_THEN SUBST1_TAC) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_BoundsCheckBlock THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:num` (X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `ys:data_v list`
    (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC THEN ASP5AUX_args2_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_BoundsCheckBlock_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf) THEN
  DRULE_ALL ASP5AUX_memory_rel_snd_Number THEN
  DISCH_THEN(X_CHOOSE_THEN `wi:A word` SUBST_ALL_TAC) THEN
  DRULE_ALL memory_rel_Block_IMP THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASP5AUX_SHIFT_FACTS_TAC THEN
  ASM_CASES_TAC `ys:data_v list = []` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RVEQ_TAC THENL
   [REWRITE_TAC[data_to_word_list_Seq_def] THEN
    ASP5AUX_EV_TAC (wl_get_var_imm_def::data_to_word_gcProof_word_and_one_eq_0_iff::
                    ShiftVar_def::ASP5AUX_val_word_lt::ASP4AUX_EV_RWS) THEN
    REWRITE_TAC[LENGTH; INT_ARITH `!i:int. (&0 <= i /\ i < &0) <=> F`] THEN
    ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC;
    SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                  SOME (wl_Word a)` ASSUME_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def];
      ALL_TAC] THEN
    REWRITE_TAC[data_to_word_list_Seq_def] THEN
    ASP5AUX_EV_TAC (wl_get_var_imm_def::data_to_word_gcProof_word_and_one_eq_0_iff::
                    ShiftVar_def::ASP5AUX_val_word_lt::ASP4AUX_EV_RWS) THEN
    REWRITE_TAC[GSYM decode_length_def] THEN ASM_REWRITE_TAC[] THEN
    ASP5AUX_BOUNDS_TAC `LENGTH (ys:data_v list)` THEN
    COND_CASES_TAC THEN ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC]);;

(* HOL4 line 11289 (the theorem of line 11306 rebinds the name) *)
let assign_BoundsCheckArray = prove
 (CASE_TERM
  `!c secn l dest args names.
     data_to_word_assign c secn l dest (MemOp BoundsCheckArray) args names =
     match args with
       [v1;v2] ->
         (data_to_word_list_Seq
            [wl_Assign 1
               (let addr = real_addr c (adjust_var v1) in
                let header = wl_Load addr in
                let k = dimindex (:A) - data_to_word_config_len_size c in
                  wl_Shift Lsr header (wl_Const (word k)));
             wl_Assign 3 (ShiftVar Ror (adjust_var v2) 2);
             wl_If Lower 3 (Reg 1)
               (wl_Assign (adjust_var dest) (wl_Const (word 18)))
               (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l)
     | _ -> (wl_Skip:(A)wl_prog,l)`,
  ASP5AUX_ASSIGN_EQ_TAC assign_BoundsCheckArray_def);;

(* HOL4 line 11306 (allow_rebind) *)
let assign_BoundsCheckArray = prove
 (assign_thm_stmt `op = MemOp BoundsCheckArray`,
  ASP5AUX_INTRO_TAC (DISCH_THEN SUBST1_TAC) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_BoundsCheckArray THEN
  DISCH_THEN(X_CHOOSE_THEN `bl:bool` (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `ws:data_v list`
    (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC THEN ASP5AUX_args2_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_BoundsCheckArray_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf) THEN
  DRULE_ALL ASP5AUX_memory_rel_snd_Number THEN
  DISCH_THEN(X_CHOOSE_THEN `wi:A word` SUBST_ALL_TAC) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
    `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `bl:bool`; `ptr:num`; `w1:A word_loc`] memory_rel_ValueArray_IMP) THEN
  DISCH_THEN(MP_TAC o SPECL [`CONS (data_Number i,wl_Word (wi:A word))
     (APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
                 (toAList (sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
                            (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))`;
     `ws:data_v list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASP5AUX_SHIFT_FACTS_TAC THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word a)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP5AUX_EV_TAC (wl_get_var_imm_def::ShiftVar_def::ASP5AUX_val_word_lt::ASP4AUX_EV_RWS) THEN
  REWRITE_TAC[GSYM decode_length_def] THEN ASM_REWRITE_TAC[] THEN
  ASP5AUX_BOUNDS_TAC `LENGTH (ws:data_v list)` THEN
  COND_CASES_TAC THEN ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC);;

(* HOL4 line 11369 (the theorem of line 11388 rebinds the name) *)
let assign_BoundsCheckByte = prove
 (CASE_TERM
  `!c secn l dest leq args names.
     data_to_word_assign c secn l dest (MemOp (BoundsCheckByte leq)) args names =
     match args with
       [v1;v2] ->
         (data_to_word_list_Seq
            [wl_Assign 1
               (let addr = real_addr c (adjust_var v1) in
                let header = wl_Load addr in
                let extra = (if dimindex (:A) = 32 then 2 else 3) in
                let k = (dimindex (:A) - data_to_word_config_len_size c) - extra in
                  wl_Op asm_Sub [wl_Shift Lsr header (wl_Const (word k));
                                 wl_Const bytes_in_word]);
             wl_Assign 3 (ShiftVar Ror (adjust_var v2) 2);
             (if leq then wl_If NotLower 1 (Reg 3) else wl_If Lower 3 (Reg 1))
               (wl_Assign (adjust_var dest) (wl_Const (word 18)))
               (wl_Assign (adjust_var dest) (wl_Const (word 2)))],l)
     | _ -> (wl_Skip:(A)wl_prog,l)`,
  ASP5AUX_ASSIGN_EQ_TAC assign_BoundsCheckByte_def);;

(* HOL4 line 11388 (allow_rebind) *)
let assign_BoundsCheckByte = prove
 (assign_thm_stmt `(?leq. op = MemOp (BoundsCheckByte leq))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `leq:bool` SUBST1_TAC)) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_BoundsCheckByte THEN
  DISCH_THEN(X_CHOOSE_THEN `bl:bool` (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `fl:bool`
    (X_CHOOSE_THEN `ws:byte list` (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC))))) THEN
  RVEQ_TAC THEN ASP5AUX_args2_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_BoundsCheckByte_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf) THEN
  DRULE_ALL ASP5AUX_memory_rel_snd_Number THEN
  DISCH_THEN(X_CHOOSE_THEN `wi:A word` SUBST_ALL_TAC) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `data_state_space (s:(C,FFI)data_state)`; `wl_state_store (t:(A,C,FFI)wl_state)`;
    `wl_state_memory (t:(A,C,FFI)wl_state)`; `wl_state_mdomain (t:(A,C,FFI)wl_state)`;
    `bl:bool`; `ptr:num`; `w1:A word_loc`] memory_rel_ByteArray_IMP) THEN
  DISCH_THEN(MP_TAC o SPECL [`CONS (data_Number i,wl_Word (wi:A word))
     (APPEND (join_env (data_state_locals (s:(C,FFI)data_state))
                 (toAList (sptree_inter (wl_state_locals (t:(A,C,FFI)wl_state))
                            (adjust_set (data_state_locals s)))))
              (APPEND [(the_global (data_state_global s),FAPPLY (wl_state_store t) Globals)]
                 (data_to_word_gcProof_flat (data_state_stack s) (wl_state_stack t))))`;
     `fl:bool`; `ws:byte list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `a:A word` (X_CHOOSE_THEN `x:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                SOME (wl_Word a)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
    ASM_REWRITE_TAC[wl_get_var_def];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o check (fun th ->
    concl th = `good_dimindex (:A)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THENL
   [ASP5AUX_BOUNDSBYTE_CASE_TAC 32; ASP5AUX_BOUNDSBYTE_CASE_TAC 64]);;

(* HOL4 line 11453 *)
let assign_LessConstSmall = prove
 (CASE_TERM
  `!c secn l dest i args names.
     data_to_word_assign c secn l dest (IntOp (LessConstSmall i)) args names =
     match args with
       [v1] -> (wl_If asm_Less (adjust_var v1) (Imm (word (4 * i)))
                  (wl_Assign (adjust_var dest) (wl_Const (word 18)))
                  (wl_Assign (adjust_var dest) (wl_Const (word 2))),l)
     | _ -> (wl_Skip:(A)wl_prog,l)`,
  ASP5AUX_ASSIGN_EQ_TAC assign_LessConstSmall_def);;

(* HOL4 line 11464 (allow_rebind) *)
let assign_LessSmallConst = prove
 (assign_thm_stmt `(?i. op = IntOp (LessConstSmall i))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST1_TAC)) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_LessConstSmall THEN
  DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_LessConstSmall_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k. (j:int) = &k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `num_of_int j` THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN
  SUBGOAL_THEN `4 * k < 2 EXP 31 /\ 4 * i < 2 EXP 31 /\ k < 2 EXP 29`
    STRIP_ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `k <= 1000000` THEN UNDISCH_TAC `i < 1000000` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `small_int (:A) (&k)` ASSUME_TAC THENL
   [MATCH_MP_TAC ASP5AUX_small_int_num THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DRULE_ALL memory_rel_Number_IMP THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def; MP6AUX_SMALLNUM_NUM]) THEN
  ASP5AUX_EV_TAC (wl_get_var_imm_def::ASP4AUX_EV_RWS) THEN
  SUBGOAL_THEN `word_ilt (word (4 * k)) (word (4 * i):A word) <=> k < i`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_ILT; ASP5AUX_ival_small; INT_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LT] THEN
  COND_CASES_TAC THEN ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC);;

(* HOL4 line 11505 (allow_rebind) *)
let assign_BoolNot = prove
 (assign_thm_stmt `op = BlockOp BoolNot`,
  ASP5AUX_INTRO_TAC (DISCH_THEN SUBST1_TAC) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_BoolNot THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:data_v` (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_BoolNot_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
  DRULE_ALL ASP5AUX_memory_rel_dest_Boolv THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASP5AUX_EV_TAC ASP4AUX_EV_RWS THEN
  REWRITE_TAC[WORD_XOR_0] THEN COND_CASES_TAC THEN REWRITE_TAC[ASP5AUX_xor_16] THEN
  ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC);;

(* HOL4 line 11546 (allow_rebind) *)
let assign_BoolTest = prove
 (assign_thm_stmt `(?test. op = BlockOp (BoolTest test))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `test:test` SUBST1_TAC)) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_BoolTest THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:data_v` (X_CHOOSE_THEN `v2:data_v`
    (X_CHOOSE_THEN `b1:bool` (X_CHOOSE_THEN `b2:bool` STRIP_ASSUME_TAC)))) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list`
    STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_BoolTest_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
    STRIP_ASSUME_TAC)) THEN
  DRULE_ALL ASP5AUX_memory_rel_dest_Boolv THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_tl) THEN DISCH_TAC THEN
  DRULE_ALL ASP5AUX_memory_rel_dest_Boolv THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASP5AUX_EV_TAC (wl_get_var_imm_def::ASP4AUX_EV_RWS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_word_18_2) THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN ASM_REWRITE_TAC[] THEN
  ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC);;

(* HOL4 line 11592 (allow_rebind) *)
let assign_WordTest = prove
 (assign_thm_stmt `(?ws test. op = WordOp (WordTest ws test))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `ws:word_size`
    (X_CHOOSE_THEN `test:test` SUBST1_TAC))) THEN
  ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_WordTest THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n1:int`
    (X_CHOOSE_THEN `n2:int` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP data_to_word_gcProof_get_vars_IMP_LENGTH) THEN
  REWRITE_TAC[LENGTH; ONE; TWO; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `tl:num list` (CONJUNCTS_THEN2
    SUBST_ALL_TAC (X_CHOOSE_THEN `a2:num` (X_CHOOSE_THEN `tl2:num list`
    STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_WordTest_def THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?k1 k2. (n1:int) = &k1 /\ (n2:int) = &k2 /\ k1 < 256 /\ k2 < 256`
    (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`num_of_int n1`; `num_of_int n2`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT];
    ALL_TAC] THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ASP5AUX_memory_rel_Number2_num) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `k1 < 256` THEN UNDISCH_TAC `k2 < 256` THEN ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  SUBGOAL_THEN `4 * k1 < dimword (:A) /\ 4 * k2 < dimword (:A)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
    UNDISCH_TAC `k1 < 256` THEN UNDISCH_TAC `k2 < 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) o
    check (is_disj o concl)) THEN
  CASE_REWRITE_TAC[] THEN ASP5AUX_EV_TAC (wl_get_var_imm_def::ASP4AUX_EV_RWS) THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; WORD_ULT; VAL_WORD; GSYM dimword_def; MOD_LT;
               INT_OF_NUM_EQ; INT_OF_NUM_LT; INT_OF_NUM_LE] THEN
  REWRITE_TAC[ARITH_RULE `4 * a = 4 * b <=> a = b`; ARITH_RULE `4 * a < 4 * b <=> a < b`;
              ARITH_RULE `4 * a <= 4 * b <=> a <= b`;
              NOT_LT] THEN
  COND_CASES_TAC THEN ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC);;

(* HOL4 line 11642 *)
let data_to_word_assignProof_Compare1_code_thm = prove
 (`!l a1 a2 dm m res (t:(A,C,FFI)wl_state) l1 l2.
     word_cmp_loop l a1 a2 dm m = SOME res /\
     dm = wl_state_mdomain t /\
     m = wl_state_memory t /\
     lookup Compare1_location (wl_state_code t) = SOME (4,Compare1_code) /\
     lookup Compare1_location (wl_state_stack_size t) = wl_state_locals_size t /\
     wl_get_var 0 t = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 t = SOME (wl_Word l) /\
     wl_get_var 4 t = SOME (wl_Word a1) /\
     wl_get_var 6 t = SOME (wl_Word a2) /\
     val l <= wl_state_clock t ==>
     ?ck smx.
       wl_evaluate (Compare1_code,t) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word res]),
          wl_state_clock_fupd (K ck) (wl_state_locals_fupd (K LN)
            (wl_state_locals_size_fupd (K (SOME 0)) (wl_state_stack_max_fupd (K smx) t)))) /\
       option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                        (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                           (wl_state_locals_size t))) /\
       wl_state_clock t <= val l + ck`,
  MATCH_MP_TAC word_cmp_loop_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  UNDISCH_TAC `word_cmp_loop l a1 a2 (wl_state_mdomain (t:(A,C,FFI)wl_state))
                 (wl_state_memory t) = SOME res` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [word_cmp_loop_def] THEN
  REWRITE_TAC[data_to_word_Compare1_code_def] THEN
  ASM_CASES_TAC `l:A word = word 0` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [(* l = 0: the result 1 *)
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
    ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN
    MAP_EVERY EXISTS_TAC [`wl_state_clock (t:(A,C,FFI)wl_state)`;
                          `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
    REWRITE_TAC[option_le_max_right; option_le_refl; VAL_WORD_0; ADD_CLAUSES; LE_REFL;
                PAIR_EQ] THEN
    REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  CASES_ON `wl_state_memory (t:(A,C,FFI)wl_state) a1` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `wl_state_memory (t:(A,C,FFI)wl_state) a2` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASP5AUX_EV_TAC (wl_mem_load_def::ASP5AUX_EV_RWS2) THEN
  ASM_CASES_TAC `a:A word = a'` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    (* different words: the result 0 or 2 *)
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`wl_state_clock (t:(A,C,FFI)wl_state)`;
                          `wl_state_stack_max (t:(A,C,FFI)wl_state)`] THEN
    REWRITE_TAC[option_le_max_right; option_le_refl; PAIR_EQ;
                ARITH_RULE `a <= b + a:num`] THEN
    REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM]] THEN
  (* equal words: the tail call *)
  DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
  SIMP ASP5AUX_EV_RWS2 THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `val (l:A word) <= wl_state_clock (t:(A,C,FFI)wl_state)` THEN
    UNDISCH_TAC `~(l:A word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASP5AUX_ABBREV_EV_TAC `Compare1_code:(A)wl_prog` `t1:(A,C,FFI)wl_state` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a':A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:A word`; `t1:(A,C,FFI)wl_state`; `l1:num`; `l2:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t1" THEN BIGPAUX_FROMLIST2_TAC THEN
    ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH; ASP5AUX_val_sub1] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `smx:num option`] THEN
  UNDISCH_TAC `option_le smx (OPTION_MAP2 MAX (wl_state_stack_max (t1:(A,C,FFI)wl_state))
    (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1)) (wl_state_locals_size t1)))` THEN
  UNDISCH_TAC `wl_state_clock (t1:(A,C,FFI)wl_state) <= val (word_sub (l:A word) (word 1)) + ck` THEN
  EXPAND_TAC "t1" THEN
  ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; ASP5AUX_val_sub1; OPTION_MAP2_MAX_CANCEL] THEN
  REPEAT STRIP_TAC THENL
   [EXPAND_TAC "t1" THEN
    REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ck:num`)) (concl th))) THEN
    UNDISCH_TAC `val (l:A word) <= wl_state_clock (t:(A,C,FFI)wl_state)` THEN
    UNDISCH_TAC `~(l:A word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN ARITH_TAC]);;

(* HOL4 line 11704 *)
let word_exp_insert = prove
 (`!m n (t:(A,C,FFI)wl_state) w c n1 w1.
     (~(m = n) ==>
      (wl_word_exp (wl_state_locals_fupd (K (insert n w (wl_state_locals t))) t)
         (real_addr c m) =
       wl_word_exp t (real_addr c m))) /\
     (~(m IN {n,n1}) ==>
      (wl_word_exp (wl_state_locals_fupd (K (insert n w (insert n1 w1 (wl_state_locals t))))
                      t) (real_addr c m) =
       wl_word_exp t (real_addr c m)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  CONJ_TAC THEN STRIP_TAC THEN REWRITE_TAC[real_addr_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[wl_word_exp_def; wl_get_var_def; wl_get_store_def;
                  wl_state_INFO.ri_accfupds; K_THM; lookup_insert; MAP]);;

(* a tail call of Compare1_code from t (after the code of Compare_code)     *)
let ASP5AUX_COMPARE1_CALL_TAC : tactic =
  CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
  SIMP ASP5AUX_EV_RWS2 THEN
  SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `dimword (:A) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASP5AUX_ABBREV_EV_TAC `Compare1_code:(A)wl_prog` `t1:(A,C,FFI)wl_state` THEN
  FIRST_X_ASSUM(fun th ->
    let l = lhs (concl th) in
    let f,args = strip_comb l in
    if is_const f && fst (dest_const f) = "word_cmp_loop" then
      MP_TAC(ISPECL (args @ [rand (rhs (concl th)); `t1:(A,C,FFI)wl_state`; `l1:num`; `l2:num`])
               data_to_word_assignProof_Compare1_code_thm) THEN
      REWRITE_TAC[th]
    else NO_TAC) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t1" THEN BIGPAUX_FROMLIST2_TAC THEN
    ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH; wl_get_var_def] THEN
    MP_TAC(ISPEC `decode_length c (x2:A word)` VAL_BOUND) THEN
    REWRITE_TAC[GSYM dimword_def] THEN
    UNDISCH_TAC `dimword (:A) < wl_state_clock (t:(A,C,FFI)wl_state)` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def] THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `smx:num option`] THEN
  UNDISCH_TAC `option_le smx (OPTION_MAP2 MAX (wl_state_stack_max (t1:(A,C,FFI)wl_state))
    (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1)) (wl_state_locals_size t1)))` THEN
  EXPAND_TAC "t1" THEN
  ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; OPTION_MAP2_MAX_CANCEL] THEN
  DISCH_TAC THEN EXPAND_TAC "t1" THEN
  REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];;

(* HOL4 line 11719 *)
let data_to_word_assignProof_Compare_code_thm = prove
 (`!c be ts refs sp st m dm i1 v1 i2 v2 vars (t:(A,C,FFI)wl_state) l1 l2.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Number i1,wl_Word v1) (CONS (data_Number i2,wl_Word v2) vars)) /\
     dm = wl_state_mdomain t /\
     m = wl_state_memory t /\
     st = wl_state_store t /\
     (~bit 0 v1 ==> bit 0 v2) /\
     shift_length c < dimindex (:A) /\
     lookup Compare1_location (wl_state_code t) = SOME (4,Compare1_code) /\
     wl_get_var 0 t = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 t = SOME (wl_Word (v1:A word)) /\
     wl_get_var 4 t = SOME (wl_Word (v2:A word)) /\
     dimword (:A) < wl_state_clock t /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c < dimindex (:A) /\
     good_dimindex (:A) ==>
     ?ck smx.
       wl_evaluate (Compare_code c,t) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word (word_cmp_res i1 i2)]),
          wl_state_clock_fupd (K ck) (wl_state_locals_fupd (K LN)
            (wl_state_locals_size_fupd (K (SOME 0)) (wl_state_stack_max_fupd (K smx) t)))) /\
       option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                        (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                           (lookup Compare1_location (wl_state_stack_size t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Number_cmp)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
              UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[data_to_word_Compare_code_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASM_CASES_TAC `bit 0 (v1:A word)` THEN ASM_CASES_TAC `bit 0 (v2:A word)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [(* two bignums *)
    SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c 2) = SOME (wl_Word a1)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `v1:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x y. wl_word_exp (wl_state_locals_fupd (K (insert 1 x (insert 11 y
                    (wl_state_locals t)))) (t:(A,C,FFI)wl_state)) (real_addr c 4) =
                    SOME (wl_Word a2)` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `v2:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN `dimindex (:A) - data_to_word_config_len_size c < dimindex (:A) /\
                  ~(dimindex (:A) - data_to_word_config_len_size c >= dimindex (:A)) /\
                  backend_common_word_shift (:A) < dimindex (:A) /\
                  ~(backend_common_word_shift (:A) >= dimindex (:A))` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[backend_common_word_shift_def] THEN
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def] o check (fun th ->
        concl th = `good_dimindex (:A)`)) THEN
      UNDISCH_TAC `~(data_to_word_config_len_size c = 0)` THEN
      UNDISCH_TAC `data_to_word_config_len_size c < dimindex (:A)` THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASP5AUX_EV_TAC (wl_mem_load_def::data_to_word_gcProof_word_and_one_eq_0_iff::
                    ASP5AUX_val_word_lt::ASP5AUX_EV_RWS2) THEN
    REWRITE_TAC[GSYM decode_length_def] THEN
    ASM_CASES_TAC `x1:A word = x2` THEN ASM_REWRITE_TAC[] THENL
     [(* equal headers: a call of Compare1_code *)
      FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[shift_lsl; WORD_ADD_0] THEN
      COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
      DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[WORD_MUL_SYM]) THEN
      ASP5AUX_COMPARE1_CALL_TAC;
      (* different headers *)
      FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      REPEAT COND_CASES_TAC THEN
      (FIRST_ASSUM(CONTR_TAC o REWRITE_RULE[]) ORELSE ASP5AUX_RET_TAC)];
    (* a bignum and a small number: the reverse comparison *)
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Number_cmp) o
      MATCH_MP memory_rel_swap o check ASP5AUX_IS_MEMREL) THEN
    ASM_REWRITE_TAC[injectivity "word_loc"; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
                    UNWIND_THM1; UNWIND_THM2] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`i1:int`; `i2:int`] ASP5AUX_word_cmp_res_swap) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c 2) = SOME (wl_Word a)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `v1:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def];
      ALL_TAC] THEN
    ASP5AUX_EV_TAC (wl_mem_load_def::data_to_word_gcProof_word_and_one_eq_0_iff::
                    ASP5AUX_EV_RWS2) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[ASP5AUX_word_2_0] THEN ASP5AUX_RET_TAC;
    (* a small number and a bignum *)
    SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c 4) = SOME (wl_Word a)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `v2:A word` THEN
      ASM_REWRITE_TAC[wl_get_var_def];
      ALL_TAC] THEN
    ASP5AUX_EV_TAC (wl_mem_load_def::data_to_word_gcProof_word_and_one_eq_0_iff::
                    ASP5AUX_EV_RWS2) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASP5AUX_RET_TAC;
    (* two small numbers: excluded *)
    ASM_MESON_TAC[]]);;

(* HOL4 line 11831 *)
let word_cmp_Less_word_cmp_res = prove
 (`!i i'. good_dimindex (:A) ==>
          (asm_word_cmp asm_Less (word_cmp_res i i') (word 1:A word) <=> i < i')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cmp_res_def; asm_word_cmp_def; WORD_ILT] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[ASP5AUX_ival_small; ARITH] THEN
  REWRITE_TAC[INT_LT_REFL; INT_OF_NUM_LT; ARITH] THEN ASM_INT_ARITH_TAC);;

(* HOL4 line 11840 *)
let word_cmp_NotLess_word_cmp_res = prove
 (`!i i'. good_dimindex (:A) ==>
          (asm_word_cmp NotLess (word 1:A word) (word_cmp_res i i') <=> (i <= i'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cmp_res_def; asm_word_cmp_def; WORD_ILT] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[ASP5AUX_ival_small; ARITH] THEN
  REWRITE_TAC[INT_LT_REFL; INT_OF_NUM_LT; ARITH] THEN ASM_INT_ARITH_TAC);;

(* HOL4 line 11850 *)
let word_cmp_not_NotLess_word_cmp_res = prove
 (`!i i'. good_dimindex (:A) ==>
          (~asm_word_cmp NotLess (word 1:A word) (word_cmp_res i i') <=> (i' < i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cmp_res_def; asm_word_cmp_def; WORD_ILT] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[ASP5AUX_ival_small; ARITH] THEN
  REWRITE_TAC[INT_LT_REFL; INT_OF_NUM_LT; ARITH] THEN ASM_INT_ARITH_TAC);;

(* HOL4 line 11860 *)
let not_word_cmp_Less_word_cmp_res = prove
 (`!i i'. good_dimindex (:A) ==>
          (~asm_word_cmp asm_Less (word_cmp_res i i') (word 1:A word) <=> (i' <= i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_cmp_res_def; asm_word_cmp_def; WORD_ILT] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[ASP5AUX_ival_small; ARITH] THEN
  REWRITE_TAC[INT_LT_REFL; INT_OF_NUM_LT; ARITH] THEN ASM_INT_ARITH_TAC);;

(* HOL4 line 11870 *)
let IMP_spt_eq = prove
 (`!t1 t2:A spt. sptree_wf t1 /\ sptree_wf t2 /\ (!n. lookup n t1 = lookup n t2) ==> (t1 = t2)`,
  MESON_TAC[spt_eq_thm]);;

(* HOL4 line 11876 *)
let env_to_list_cut_env_IMP = prove
 (`!(x:(A word_loc)spt) (t:(A,C,FFI)wl_state) l permute y s.
     env_to_list x (wl_state_permute t) = (l,permute) /\ wl_cut_env y s = SOME x ==>
     (fromAList l = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC IMP_spt_eq THEN
  REWRITE_TAC[wf_fromAList; lookup_fromAList] THEN CONJ_TAC THENL
   [UNDISCH_TAC `wl_cut_env y (s:(A word_loc)spt) = SOME x` THEN
    REWRITE_TAC[wl_cut_env_def; cut_envs_def; cut_names_def] THEN
    REPEAT(COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT]) THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC wf_union THEN REWRITE_TAC[wf_inter];
    DRULE env_to_list_lookup_equiv THEN SIMP_TAC[]]);;

(* HOL4 line 11889 *)
let dimword_LESS_MustTerminate_limit = prove
 (`good_dimindex (:A) ==> dimword (:A) < MustTerminate_limit (:A) - 1`,
  DISCH_TAC THEN REWRITE_TAC[MustTerminate_limit_def] THEN
  MATCH_MP_TAC(ARITH_RULE `1 < n ==> n < (2 * n + k) - 1`) THEN
  REWRITE_TAC[dimword_def] THEN
  MATCH_MP_TAC(ARITH_RULE `2 EXP 1 < x ==> 1 < x`) THEN REWRITE_TAC[LT_EXP] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def]) THEN ARITH_TAC);;

(* the call of Compare_code in Less and LessEq: from the MustTerminate     *)
(* call to the final If of the code                                         *)
let ASP5AUX_CMP_CALL_TAC : tactic =
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_code_rel_stubs o CONJUNCT1 o CONJUNCT2 o
     CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
     check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
                                    (t:(A,C,FFI)wl_state) NONE locs`))) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP cut_env_IMP_cut_envs o check (fun th ->
     can (find_term (fun u -> is_const u && fst (dest_const u) = "wl_cut_env")) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
     STRIP_ASSUME_TAC)) THEN
   CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "MustTerminate"))) THEN
   SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `dimword (:A) < MustTerminate_limit (:A) - 1` ASSUME_TAC THENL
    [ASM_SIMP_TAC[dimword_LESS_MustTerminate_limit]; ALL_TAC] THEN
   SUBGOAL_THEN `~(MustTerminate_limit (:A) = 0)` ASSUME_TAC THENL
    [UNDISCH_TAC `dimword (:A) < MustTerminate_limit (:A) - 1` THEN ARITH_TAC; ALL_TAC] THEN
   CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
   SIMP (data_to_word_get_names_def::cut_envs_adjust_sets_ODD::domain_adjust_sets::
         ALL_DISTINCT::MEM::ASP5AUX_EV_RWS2)) THEN
  (MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
     PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `lst:(num#A word_loc)list` (X_CHOOSE_THEN `perm:num->num->num`
     ASSUME_TAC)) THEN
   REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN SIMP[stack_size_eq2; stack_size_frame_def]) THEN
  (ASP5AUX_ABBREV_EV_TAC `Compare_code c:(A)wl_prog` `t1:(A,C,FFI)wl_state` THEN
   FIRST_ASSUM(fun th -> if ASP5AUX_IS_MEMREL th &&
       can (find_term ((=) `data_Number i1`)) (concl th) then
     MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] data_to_word_assignProof_Compare_code_thm) th)
     else NO_TAC) THEN
   DISCH_THEN(MP_TAC o REWRITE_RULE[IMP_IMP] o SPECL [`t1:(A,C,FFI)wl_state`; `n:num`; `l:num`]) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "t1" THEN BIGPAUX_FROMLIST2_TAC THEN
     ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH; wl_get_var_def] THEN
     FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf o check ASP5AUX_IS_MEMREL) THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [ASM_MESON_TAC[];
       UNDISCH_TAC `data_to_word_config_len_size c + 7 < dimindex (:A)` THEN ARITH_TAC];
     ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LENGTH] THEN
   EXPAND_TAC "t1" THEN SIMP[wl_pop_env_def; wl_set_vars_def; alist_insert_def;
                             asp5_ev_clause "wl_Skip"]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_envs_wf) THEN
   SUBGOAL_THEN `fromAList (lst:(num#A word_loc)list) = y2` ASSUME_TAC THENL
    [MATCH_MP_TAC IMP_spt_eq THEN ASM_REWRITE_TAC[wf_fromAList; lookup_fromAList] THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP env_to_list_lookup_equiv o
       check (fun th -> is_eq (concl th) &&
         can (find_term (fun u -> is_const u && fst (dest_const u) = "env_to_list")) (concl th))) THEN
     SIMP_TAC[];
     ALL_TAC] THEN
   ASM_SIMP_TAC[fromAList_toAList] THEN
   REWRITE_TAC[domain_union; UNION_ACI] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
   SIMP ASP5AUX_EV_RWS2) THEN
  (ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN CASE_REWRITE_TAC[] THEN
   ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 );;

(* HOL4 line 11897 *)
let assign_Less = prove
 (assign_thm_stmt `op = IntOp clos_Less`,
  (ASP5AUX_INTRO_NAMES_TAC (DISCH_THEN SUBST1_TAC) THEN
   ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_Less THEN
   DISCH_THEN(X_CHOOSE_THEN `i1:int` (X_CHOOSE_THEN `i2:int` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN ASP5AUX_args2_TAC) THEN
  (DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
     STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Number_cmp) o
     check (fun th -> is_comb (concl th) && is_const (fst (strip_comb (concl th))) &&
                      fst (dest_const (fst (strip_comb (concl th)))) = "memory_rel" &&
                      can (find_term ((=) `w1:A word_loc`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
   ASP5AUX_UNFOLD_ASSIGN_TAC assign_Less_def THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP5AUX_EV_TAC (data_to_word_gcProof_word_and_one_eq_0_iff::WORD_OR_0::BIT_WORD_OR::
                   ASP5AUX_EV_RWS2)) THEN
  ASM_CASES_TAC `bit 0 (v1:A word) \/ bit 0 (v2:A word)` THEN ASM_REWRITE_TAC[] THENL
   [ASP5AUX_CMP_CALL_TAC THEN
    REWRITE_TAC[GSYM asm_word_cmp_def] THEN ASM_SIMP_TAC[word_cmp_Less_word_cmp_res] THEN
    ASP5AUX_CMP_END_TAC;
    (FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DE_MORGAN_THM] o check (fun th ->
      is_neg (concl th) && is_disj (rand (concl th)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CASE_REWRITE_TAC[] THEN
    ASP5AUX_EV_TAC (ASP5AUX_EV_RWS2)) THEN
    (FIRST_ASSUM(fun th -> if is_iff (concl th) &&
     can (find_term (fun u -> is_const u && fst (dest_const u) = "word_ilt")) (concl th)
     then REWRITE_TAC[GSYM th] else NO_TAC) THEN
   COND_CASES_TAC THEN ASP5AUX_RESET0_TAC)]);;

(* HOL4 line 12032 *)
let assign_LessEq = prove
 (assign_thm_stmt `op = IntOp LessEq`,
  (ASP5AUX_INTRO_NAMES_TAC (DISCH_THEN SUBST1_TAC) THEN
   ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_LessEq THEN
   DISCH_THEN(X_CHOOSE_THEN `i1:int` (X_CHOOSE_THEN `i2:int` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN ASP5AUX_args2_TAC) THEN
  (DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` (X_CHOOSE_THEN `w2:A word_loc`
     STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Number_cmp) o
     check (fun th -> is_comb (concl th) && is_const (fst (strip_comb (concl th))) &&
                      fst (dest_const (fst (strip_comb (concl th)))) = "memory_rel" &&
                      can (find_term ((=) `w1:A word_loc`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `v1:A word` (X_CHOOSE_THEN `v2:A word`
     (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
   ASP5AUX_UNFOLD_ASSIGN_TAC assign_LessEq_def THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP5AUX_EV_TAC (data_to_word_gcProof_word_and_one_eq_0_iff::WORD_OR_0::BIT_WORD_OR::
                   ASP5AUX_EV_RWS2)) THEN
  ASM_CASES_TAC `bit 0 (v1:A word) \/ bit 0 (v2:A word)` THEN ASM_REWRITE_TAC[] THENL
   [ASP5AUX_CMP_CALL_TAC THEN
    REWRITE_TAC[GSYM asm_word_cmp_def] THEN ASM_SIMP_TAC[word_cmp_NotLess_word_cmp_res] THEN
    ASP5AUX_CMP_END_TAC;
    (FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DE_MORGAN_THM] o check (fun th ->
      is_neg (concl th) && is_disj (rand (concl th)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CASE_REWRITE_TAC[] THEN
    ASP5AUX_EV_TAC (ASP5AUX_EV_RWS2)) THEN
    (REWRITE_TAC[ASP5AUX_not_ilt] THEN
     FIRST_ASSUM(fun th -> if is_iff (concl th) &&
       can (find_term (fun u -> is_const u && fst (dest_const u) = "word_ilt")) (concl th)
       then REWRITE_TAC[GSYM th] else NO_TAC) THEN
     FIRST_ASSUM(fun th -> if is_iff (concl th) &&
       can (find_term ((=) `(v1:A word) = v2`)) (concl th)
       then REWRITE_TAC[GSYM th] else NO_TAC) THEN
     REWRITE_TAC[GSYM INT_LE_LT] THEN
     COND_CASES_TAC THEN ASP5AUX_RESET0_TAC)]);;

(* HOL4 line 12168 *)
let word_exp_set_var_ShiftVar = prove
 (CASE_TERM
  `!v (w:A word) (t:(A,C,FFI)wl_state) sow n.
     wl_word_exp (wl_set_var v (wl_Word w) t) (ShiftVar sow v n) =
     OPTION_MAP wl_Word (match sow with
                           Lsl -> SOME (word_shl w n)
                         | Lsr -> SOME (word_ushr w n)
                         | Asr -> SOME (word_ishr w n)
                         | Ror -> SOME (word_ror w n))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_exp_set_var_ShiftVar_lemma] THEN
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 12179 (local; the theorem of line 12206 rebinds the name) *)
let MemEqList_thm = prove
 (`!offset (t:(A,C,FFI)wl_state) xs dm m b a.
     word_mem_eq (word_add a offset) xs dm m = SOME b /\
     wl_get_var 3 t = SOME (wl_Word a) /\ dm = wl_state_mdomain t /\
     m = wl_state_memory t ==>
     ?x. wl_evaluate (MemEqList offset xs,t) =
           (NONE,wl_state_locals_fupd
                   (K (((if b then insert 1 (wl_Word (word 18)) else I) o
                        (if ~(xs = []) then insert 5 x else I)) (wl_state_locals t))) t)`,
  SUBGOAL_THEN
   `!xs offset (t:(A,C,FFI)wl_state) dm m b a.
     word_mem_eq (word_add a offset) xs dm m = SOME b /\
     wl_get_var 3 t = SOME (wl_Word a) /\ dm = wl_state_mdomain t /\
     m = wl_state_memory t ==>
     ?x. wl_evaluate (MemEqList offset xs,t) =
           (NONE,wl_state_locals_fupd
                   (K (((if b then insert 1 (wl_Word (word 18)) else I) o
                        (if ~(xs = []) then insert 5 x else I)) (wl_state_locals t))) t)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[word_mem_eq_def; option_INJ; MemEqList_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[o_THM; I_THM] THEN ASP5AUX_EV_TAC ASP4AUX_EV_RWS THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:A word` THEN X_GEN_TAC `ws:(A word)list` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[word_mem_eq_def] THEN
  ASM_CASES_TAC `word_add a offset IN (dm:A word->bool)` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  SUBGOAL_THEN `isWord ((m:A word -> A word_loc) (word_add a offset)) <=>
                ?y. m (word_add a offset) = wl_Word y` SUBST1_TAC THENL
   [SPEC_TAC(`(m:A word -> A word_loc) (word_add a offset)`,`z:A word_loc`) THEN
    GEN_TAC THEN CASES_ON `z:A word_loc` THEN
    REWRITE_TAC[isWord_def; injectivity "word_loc"; distinctness "word_loc"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?y. (m:A word -> A word_loc) (word_add a offset) = wl_Word y` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:A word`) THEN ASM_REWRITE_TAC[injectivity "word_loc"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MemEqList_def; NOT_CONS_NIL] THEN
  ASP5AUX_EV_TAC (WORD_ADD_0::ASP4AUX_EV_RWS) THEN
  ASM_CASES_TAC `y:A word = h` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl) o check (fun th ->
    can (find_term ((=) `SOME (b:bool)`)) (concl th))) THEN
  ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`word_add offset bytes_in_word:A word`;
      `wl_state_locals_fupd (K (insert 5 (wl_Word h) (wl_state_locals t)))
         (t:(A,C,FFI)wl_state)`;
      `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
      `b:bool`; `a:A word`]) THEN
    REWRITE_TAC[WORD_ADD_ASSOC; wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM;
                lookup_insert; ARITH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A word_loc` SUBST1_TAC) THEN
    REWRITE_TAC[wl_state_INFO.ri_fupdfupds; K_o_THM; o_THM; injectivity "prod"] THEN
    ASM_CASES_TAC `ws:(A word)list = []` THEN ASM_REWRITE_TAC[I_THM] THENL
     [EXISTS_TAC `wl_Word h:A word_loc` THEN REWRITE_TAC[];
      EXISTS_TAC `x:A word_loc` THEN REWRITE_TAC[insert_shadow]];
    DISCH_TAC THEN ASM_REWRITE_TAC[o_THM; I_THM] THEN
    EXISTS_TAC `wl_Word y:A word_loc` THEN REWRITE_TAC[]]);;

(* HOL4 line 12206 (HOL4: MemEqList_thm |> Q.SPEC 0w |> SIMP_RULE std_ss  *)
(* [WORD_ADD_0]; rebinds the name)                                          *)
let MemEqList_thm = prove
 (`!(t:(A,C,FFI)wl_state) xs dm m b a.
     word_mem_eq a xs dm m = SOME b /\
     wl_get_var 3 t = SOME (wl_Word a) /\ dm = wl_state_mdomain t /\
     m = wl_state_memory t ==>
     ?x. wl_evaluate (MemEqList (word 0) xs,t) =
           (NONE,wl_state_locals_fupd
                   (K (((if b then insert 1 (wl_Word (word 18)) else I) o
                        (if ~(xs = []) then insert 5 x else I)) (wl_state_locals t))) t)`,
  MP_TAC(ISPEC `word 0:A word` MemEqList_thm) THEN REWRITE_TAC[WORD_ADD_0]);;

(* apply MemEqList_thm to the first evaluation of MemEqList in the goal *)
let ASP5AUX_MEMEQ_TAC : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t -> match t with
      Comb(Const("wl_evaluate",_),arg) ->
        (try let p = fst (dest_pair arg) in
             let h = fst (strip_comb p) in
             is_const h && fst (dest_const h) = "MemEqList" with Failure _ -> false)
    | _ -> false) w in
  let p,st = dest_pair (rand tm) in
  let xs = rand p in
  let mth = snd (find (fun (_,th) -> is_eq (concl th) &&
     (let l = lhs (concl th) in
      is_comb l && (let f,args = strip_comb l in
                    is_const f && fst (dest_const f) = "word_mem_eq" &&
                    length args = 4 && el 1 args = xs))) asl) in
  let _,args = strip_comb (lhs (concl mth)) in
  let a = el 0 args and dm = el 2 args and m = el 3 args in
  let b = rand (rhs (concl mth)) in
  (MP_TAC(ISPECL [st; xs; dm; m; b; a] MemEqList_thm) THEN
   ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH] THEN
   DISCH_THEN(X_CHOOSE_THEN `xm:A word_loc` SUBST1_TAC)) g;;

(* HOL4 line 12209 *)
let assign_EqualConst = prove
 (assign_thm_stmt `(?p. op = BlockOp (EqualConst p))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `p:const_part` SUBST1_TAC)) THEN CASES_ON `p:const_part` THENL
   [ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_EqualConst_Con;
    (ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_EqualConst_Int THEN
   DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
   ASP5AUX_args1_TAC THEN
   DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP memory_rel_any_Number_IMP o
     CONJ (ASSUME `good_dimindex (:A)`)) THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A word` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o SPEC `a:int` o MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Number_const_test) o
     check ASP5AUX_IS_MEMREL) THEN
   ASM_REWRITE_TAC[] THEN
   ASP5AUX_UNFOLD_ASSIGN_TAC assign_EqualConst_def THEN
   REWRITE_TAC[part_to_words_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def])) THEN
    ASM_CASES_TAC `small_int (:A) (a:int)` THEN ASM_REWRITE_TAC[] THENL
     [(DISCH_TAC THEN CASE_REWRITE_TAC[] THEN
     ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN
     REWRITE_TAC[ISPECL [`w:A word`; `Smallnum a:A word`] EQ_SYM_EQ] THEN
     ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THEN ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC);
      REWRITE_TAC[bignum_words_def] THEN
   MP_TAC(ISPEC `i2mw (a:int):bool#(A word)list` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `sign:bool` (X_CHOOSE_THEN `ws:(A word)list` SUBST1_TAC)) THEN
   CASE_REWRITE_TAC[] THEN
   CASES_ON `encode_header c (if sign then 7 else 3) (LENGTH (ws:(A word)list)):(A word)option` THEN CASE_REWRITE_TAC[] THENL
       [DISCH_TAC THEN ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN ASM_REWRITE_TAC[] THEN
     ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC;
        REWRITE_TAC[MP6AUX_MAP_GET_WORD] THEN
   ASM_CASES_TAC `small_int (:A) (j:int)` THEN ASM_REWRITE_TAC[] THENL
         [DISCH_TAC THEN
     ASP5AUX_EV_TAC (data_to_word_gcProof_word_and_one_eq_0_iff::ASP5AUX_EV_RWS2) THEN
     ASM_REWRITE_TAC[] THEN ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC;
          (DISCH_THEN(X_CHOOSE_THEN `ra:A word` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `!z. wl_word_exp (wl_state_locals_fupd (K (insert 1 z (wl_state_locals t)))
                   (t:(A,C,FFI)wl_state)) (real_addr c (adjust_var a1)) = SOME (wl_Word ra)`
     ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
     ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
                     adjust_var_NEQ];
     ALL_TAC] THEN
   ASP5AUX_EV_TAC (data_to_word_gcProof_word_and_one_eq_0_iff::ASP5AUX_EV_RWS2)) THEN
       (ASP5AUX_MEMEQ_TAC THEN CASE_REWRITE_TAC[] THEN
   ASP5AUX_EV_TAC (NOT_CONS_NIL::o_THM::I_THM::ASP5AUX_EV_RWS2)) THEN
       (COND_CASES_TAC THEN ASM_REWRITE_TAC[I_THM; lookup_insert; ARITH; case_def "option"] THEN
   ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC)]]];
    ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_EqualConst_Str THEN
   DISCH_THEN(X_CHOOSE_THEN `bl:bool` (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `jj:byte list`
     STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN ASP5AUX_args1_TAC THEN
   DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o SPECL [`jj:byte list`; `a:mlstring`] o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_String_const_test) o
     check ASP5AUX_IS_MEMREL) THEN
   ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   REWRITE_TAC[MP6AUX_BYTES_STR] THEN
   ASP5AUX_UNFOLD_ASSIGN_TAC assign_EqualConst_def THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   CASES_ON `part_to_words c LN (clos_Str a) (word 0:A word)` THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN ASM_REWRITE_TAC[] THEN
     ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC;
      (MP_TAC(ISPEC `a':(bool#A word_loc)#((bool#A word_loc)list)` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `xw:bool#A word_loc` (X_CHOOSE_THEN `res:(bool#A word_loc)list`
     SUBST_ALL_TAC)) THEN
   MP_TAC(ISPEC `xw:bool#A word_loc` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `xb:bool` (X_CHOOSE_THEN `xv:A word_loc` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN
   SUBGOAL_THEN `xb:bool` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       can (find_term (fun u -> is_const u && fst (dest_const u) = "part_to_words")) (lhs (concl th)))) THEN
     REWRITE_TAC[part_to_words_def; LET_DEF; LET_END_DEF] THEN
     COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN MESON_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`(xb:bool,xv:A word_loc)`; `res:(bool#A word_loc)list`] o
     check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `ra:A word` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN
   SUBGOAL_THEN `!z. wl_word_exp (wl_state_locals_fupd (K (insert 1 z (wl_state_locals t)))
                   (t:(A,C,FFI)wl_state)) (real_addr c (adjust_var a1)) = SOME (wl_Word ra)`
     ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
     ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
                     adjust_var_NEQ];
     ALL_TAC] THEN
   REWRITE_TAC[FST; data_to_word_list_Seq_def] THEN
   ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN
   ASP5AUX_MEMEQ_TAC THEN CASE_REWRITE_TAC[] THEN
   ASP5AUX_EV_TAC (NOT_CONS_NIL::o_THM::I_THM::ASP5AUX_EV_RWS2)) THEN
      (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[I_THM; lookup_insert; ARITH; case_def "option"] THEN
   ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC)];
    ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_EqualConst_W64 THEN
   DISCH_THEN(X_CHOOSE_THEN `j:int64` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
   ASP5AUX_args1_TAC THEN
   DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word_loc` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o SPEC `a:int64` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] memory_rel_Word64_const_test) o
     check ASP5AUX_IS_MEMREL) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A word` (X_CHOOSE_THEN `ra:A word` (X_CHOOSE_THEN
     `words:(A word)list` (X_CHOOSE_THEN `h:A word` STRIP_ASSUME_TAC)))) THEN
   RVEQ_TAC THEN
   ASP5AUX_UNFOLD_ASSIGN_TAC assign_EqualConst_def THEN
   REWRITE_TAC[part_to_words_def; LET_DEF; LET_END_DEF] THEN
   SUBGOAL_THEN `(if dimindex (:A) < 64 then [word_extract 63 32 a; word_extract 31 0 a]
                  else [word_extract 63 0 (a:int64)]) = (words:(A word)list)` SUBST1_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN COND_CASES_TAC THEN
     SIMP_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[MAP; TL; MP6AUX_MAP_GET_WORD] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   SUBGOAL_THEN `!z. wl_word_exp (wl_state_locals_fupd (K (insert 1 z (wl_state_locals t)))
                   (t:(A,C,FFI)wl_state)) (real_addr c (adjust_var a1)) = SOME (wl_Word ra)`
     ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC get_real_addr_lemma THEN EXISTS_TAC `w:A word` THEN
     ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
                     adjust_var_NEQ];
     ALL_TAC] THEN
   REWRITE_TAC[FST; data_to_word_list_Seq_def] THEN
   ASP5AUX_EV_TAC (WORD_ADD_0::ASP5AUX_EV_RWS2) THEN
   ASP5AUX_MEMEQ_TAC THEN CASE_REWRITE_TAC[] THEN
   ASP5AUX_EV_TAC (NOT_CONS_NIL::o_THM::I_THM::ASP5AUX_EV_RWS2) THEN
   REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[I_THM; lookup_insert; ARITH; case_def "option"] THEN
   ASP5AUX_FINISH_TAC THEN ASP5AUX_BOOLV_MEM_TAC]);;

(* HOL4 line 12388 *)
let option_map_mult_suc = prove
 (`!n m. OPTION_MAP (( * ) (SUC n)) m = OPTION_MAP2 (+) m (OPTION_MAP (( * ) n) m)`,
  REPEAT GEN_TAC THEN CASES_ON `m:num option` THEN
  REWRITE_TAC[OPTION_MAP_DEF; OPTION_MAP2_THM; option_INJ] THEN ARITH_TAC);;

(* HOL4 line 12395 *)
let eq_code_stack_max_sub1 = prove
 (`!l tsz.
     ~(l = 0) ==>
     eq_code_stack_max l tsz =
     OPTION_MAP2 (+)
       (OPTION_MAP2 MAX (lookup Equal_location tsz)
          (OPTION_MAP2 MAX (lookup Equal1_location tsz) (lookup Compare1_location tsz)))
       (eq_code_stack_max (l - 1) tsz)`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN GEN_TAC THEN
  REWRITE_TAC[eq_code_stack_max_def; option_map_mult_suc]);;

(* HOL4 line 12409 *)
let eq_code_stack_max_le_mono = prove
 (`!a b tsz. a <= b ==> option_le (eq_code_stack_max a tsz) (eq_code_stack_max b tsz)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eq_code_stack_max_def] THEN
  SPEC_TAC(`OPTION_MAP2 MAX (lookup Equal_location (tsz:num spt))
              (OPTION_MAP2 MAX (lookup Equal1_location tsz) (lookup Compare1_location tsz))`,
           `x:num option`) THEN
  GEN_TAC THEN CASES_ON `x:num option` THEN REWRITE_TAC[OPTION_MAP_DEF; option_le_def] THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL]);;

(* HOL4 line 12416 *)
let sane_locals_size_def = cake_def
  `sane_locals_size (t:(A,C,FFI)wl_state) <=>
     (wl_state_locals_size t = lookup Equal_location (wl_state_stack_size t) \/
      wl_state_locals_size t = lookup Equal1_location (wl_state_stack_size t))`;;

(* HOL4 line 12421 *)
let data_to_word_assignProof_Equal_code_lemma = prove
 (`(!c st dm m l wck v1 v2 (t:(A,C,FFI)wl_state) l1 l2 res l' wck'.
      word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
      dm = wl_state_mdomain t /\
      m = wl_state_memory t /\
      st = wl_state_store t /\
      l <= wl_state_clock t /\
      shift_length c < dimindex (:A) /\
      lookup Equal_location (wl_state_code t) = SOME (3,Equal_code c) /\
      lookup Equal1_location (wl_state_code t) = SOME (4,Equal1_code) /\
      lookup Compare1_location (wl_state_code t) = SOME (4,Compare1_code) /\
      wl_get_var 0 t = SOME (wl_Loc l1 l2) /\
      wl_get_var 2 t = SOME (wl_Word (v1:A word)) /\
      wl_get_var 4 t = SOME (wl_Word (v2:A word)) /\
      ~(data_to_word_config_len_size c = 0) /\
      data_to_word_config_len_size c < dimindex (:A) /\
      sane_locals_size t /\
      good_dimindex (:A) ==>
      ?ck new_p smx.
        wl_evaluate (Equal_code c,t) =
          (SOME (wl_Result (wl_Loc l1 l2) [wl_Word res]),
           wl_state_clock_fupd (K ck) (wl_state_locals_fupd (K LN)
             (wl_state_locals_size_fupd (K (SOME 0)) (wl_state_permute_fupd (K new_p)
                (wl_state_stack_max_fupd (K smx) t))))) /\
        option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                         (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                            (eq_code_stack_max (wck + 1) (wl_state_stack_size t)))) /\
        l' <= ck) /\
   (!c st dm m l wck w a1 a2 (t:(A,C,FFI)wl_state) l1 l2 res l' wck'.
      word_eq_list c st dm m l wck w a1 a2 = SOME (res,l',wck') /\
      dm = wl_state_mdomain t /\
      m = wl_state_memory t /\
      st = wl_state_store t /\
      l <= wl_state_clock t /\
      shift_length c < dimindex (:A) /\
      lookup Equal_location (wl_state_code t) = SOME (3,Equal_code c) /\
      lookup Equal1_location (wl_state_code t) = SOME (4,Equal1_code) /\
      lookup Compare1_location (wl_state_code t) = SOME (4,Compare1_code) /\
      wl_get_var 0 t = SOME (wl_Loc l1 l2) /\
      wl_get_var 2 t = SOME (wl_Word (w:A word)) /\
      wl_get_var 4 t = SOME (wl_Word (a1:A word)) /\
      wl_get_var 6 t = SOME (wl_Word (a2:A word)) /\
      sane_locals_size t /\
      ~(data_to_word_config_len_size c = 0) /\
      data_to_word_config_len_size c < dimindex (:A) /\
      good_dimindex (:A) ==>
      ?ck new_p smx.
        wl_evaluate (Equal1_code,t) =
          (SOME (wl_Result (wl_Loc l1 l2) [wl_Word res]),
           wl_state_clock_fupd (K ck) (wl_state_locals_fupd (K LN)
             (wl_state_locals_size_fupd (K (SOME 0)) (wl_state_permute_fupd (K new_p)
                (wl_state_stack_max_fupd (K smx) t))))) /\
        option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                         (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                            (eq_code_stack_max (wck + 1) (wl_state_stack_size t)))) /\
        l' <= ck)`,
  MATCH_MP_TAC word_eq_ind THEN CONJ_TAC THENL
  [(REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [CONJUNCT1 word_eq_def] o
   check (fun th -> can (find_term (fun u -> is_const u && fst(dest_const u) = "word_eq"))
   (lhand (concl th)) && is_eq (concl th) &&
   fst(dest_const(fst(strip_comb(lhand(concl th))))) = "word_eq")) THEN
   REWRITE_TAC[data_to_word_Equal_code_def; data_to_word_list_Seq_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def])) THEN
  (ASM_CASES_TAC `w1:A word = w2` THEN ASM_REWRITE_TAC[]) THENL
  [(REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASP5AUX_EV_TAC ASP5AUX_EV_RWS2) THEN
   (ASP5AUX_RET3_TAC);
   (ASM_CASES_TAC `bit 0 (w1:A word) /\ bit 0 (w2:A word)` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
     REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
     ASP5AUX_EV_TAC (BIT_WORD_AND::ASP5AUX_EV_RWS2) THEN ASP5AUX_RET3_TAC]) THEN
    (DISCH_THEN(MP_TAC o MATCH_MP ASP5AUX_header_pair) THEN
     REWRITE_TAC[ASP5AUX_word_header_SOME] THEN
     DISCH_THEN(X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `h1:A word` (X_CHOOSE_THEN `x2:A word`
     (X_CHOOSE_THEN `h2:A word` STRIP_ASSUME_TAC))))) THEN
    (SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c 2) = SOME (wl_Word x1) /\
     wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c 4) = SOME (wl_Word x2)`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC get_real_addr_lemma THENL
     [EXISTS_TAC `w1:A word`; EXISTS_TAC `w2:A word`] THEN
     ASM_REWRITE_TAC[wl_get_var_def];
     ALL_TAC]) THEN
    (ASP5AUX_EV_TAC (BIT_WORD_AND::word_exp_insert::IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
     ASP5AUX_EV_RWS2)) THEN
    (ASP5AUX_SPLIT_TAC `word_and (h1:A word) (word 12) = word 0`) THENL
    [(RULE_ASSUM_TAC(REWRITE_RULE[word_is_clos_def]) THEN
       ASP5AUX_SPLIT_TAC `word_and (h1:A word) (word_or (tag_mask c) (word 2)) =
       word (16 * closure_tag + 2)`) THENL
      [(ASP5AUX_EQ_RET_TAC);
       (CASE_REWRITE_TAC[] THEN
         ASP5AUX_EV_TAC (BIT_WORD_AND::word_exp_insert::IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
         ASP5AUX_EV_RWS2)) THEN
        (ASP5AUX_SPLIT_TAC `word_and (h1:A word) (word_or (tag_mask c) (word 2)) =
         word (16 * partial_app_tag + 2)`) THENL
        [(ASP5AUX_EQ_RET_TAC);
         (CASE_REWRITE_TAC[] THEN
           ASP5AUX_EV_TAC (BIT_WORD_AND::word_exp_insert::IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
           ASP5AUX_EV_RWS2)) THEN
          (ASP5AUX_SPLIT_TAC `h1:A word = h2`) THENL
          [(ASM_CASES_TAC `l = 0` THENL
             [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
             ASM_REWRITE_TAC[option_DISTINCT];
             ALL_TAC] THEN
             FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
             ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
            (CASE_REWRITE_TAC[] THEN
             ASP5AUX_EV_TAC (BIT_WORD_AND::word_exp_insert::IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
             ASP5AUX_word_exp_ShiftVar_ins::ASP5AUX_EV_RWS2)) THEN
            (REWRITE_TAC[WORD_ADD_0; GSYM decode_length_def] THEN
             CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
             SIMP ASP5AUX_EV_RWS2) THEN
            (SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
             [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]) THEN
            (ASP5AUX_ABBREV_EV_TAC `Equal1_code:(A)wl_prog` `t1:(A,C,FFI)wl_state`) THEN
            (FIRST_X_ASSUM(MP_TAC o SPECL [`h2:A word`; `h2:A word`; `x1:A word`; `x2:A word`] o
             check (fun th -> is_forall (concl th) && can (find_term (fun u -> try
             fst(dest_const u) = "word_eq_list" with Failure _ -> false)) (concl th))) THEN
             ASM_REWRITE_TAC[ASP5AUX_word_header_SOME; word_is_clos_def] THEN
             DISCH_THEN(MP_TAC o SPECL [`t1:(A,C,FFI)wl_state`; `l1:num`; `l2:num`; `res:A word`;
             `l':num`; `wck':num`]) THEN
             ASM_REWRITE_TAC[]) THEN
            (ANTS_TAC THENL
             [EXPAND_TAC "t1" THEN BIGPAUX_FROMLIST2_TAC THEN
             ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH;
             sane_locals_size_def] THEN
             ASM_ARITH_TAC;
             ALL_TAC]) THEN
            (DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `p2:num->num->num`
             (X_CHOOSE_THEN `smx2:num option` STRIP_ASSUME_TAC))) THEN
             ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def; option_DISTINCT] THEN
             MAP_EVERY EXISTS_TAC [`ck2:num`; `p2:num->num->num`; `smx2:num option`] THEN
             ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
             [EXPAND_TAC "t1" THEN
             REWRITE_TAC[PAIR_EQ; wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds;
             K_THM];
             MATCH_MP_TAC ASP5AUX_eq_bound_tail THEN
             EXISTS_TAC `lookup Equal1_location (wl_state_stack_size (t:(A,C,FFI)wl_state))` THEN
             REWRITE_TAC[] THEN
             FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `smx2:num option`)) (concl th))) THEN
             EXPAND_TAC "t1" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]]);
           (ASP5AUX_EQ_RET_TAC)]]];
     (CASE_REWRITE_TAC[] THEN
       ASP5AUX_EV_TAC (BIT_WORD_AND::word_exp_insert::IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
       ASP5AUX_word_exp_ShiftVar_ins::WORD_ADD_0::ASP5AUX_EV_RWS2)) THEN
      (ASP5AUX_SPLIT_TAC `h1:A word = h2`) THENL
      [(CASE_REWRITE_TAC[] THEN
         ASP5AUX_EV_TAC (ASP5AUX_and_pow2::ASP5AUX_and24::BIT_WORD_AND::word_exp_insert::
         IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
         ASP5AUX_word_exp_ShiftVar_ins::WORD_ADD_0::ASP5AUX_EV_RWS2)) THEN
        (ASP5AUX_SPLIT_TAC `bit 2 (h2:A word)` THENL [ALL_TAC; ASP5AUX_EQ_RET_TAC]) THEN
        (CASE_REWRITE_TAC[] THEN
         ASP5AUX_EV_TAC (ASP5AUX_and_pow2::ASP5AUX_and24::BIT_WORD_AND::word_exp_insert::
         IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
         ASP5AUX_word_exp_ShiftVar_ins::WORD_ADD_0::ASP5AUX_EV_RWS2)) THEN
        (ASP5AUX_SPLIT_TAC `~bit 3 (h2:A word) /\ bit 4 h2` THENL [ASP5AUX_EQ_RET_TAC; ALL_TAC]) THEN
        (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
         COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
         REWRITE_TAC[case_eq "option"; option_DISTINCT; option_INJ; PAIR_EQ] THEN
         DISCH_THEN(X_CHOOSE_THEN `r:A word` STRIP_ASSUME_TAC) THEN RVEQ_TAC) THEN
        (CASE_REWRITE_TAC[] THEN
         ASP5AUX_EV_TAC (ASP5AUX_shift_lsl_mul::ASP5AUX_and_pow2::ASP5AUX_and24::BIT_WORD_AND::
         word_exp_insert::IN_INSERT::NOT_IN_EMPTY::wl_mem_load_def::
         ASP5AUX_word_exp_ShiftVar_ins::WORD_ADD_0::ASP5AUX_EV_RWS2)) THEN
        (REWRITE_TAC[GSYM decode_length_def] THEN
         CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
         SIMP ASP5AUX_EV_RWS2) THEN
        (SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]) THEN
        (ASP5AUX_ABBREV_EV_TAC `Compare1_code:(A)wl_prog` `t1:(A,C,FFI)wl_state`) THEN
        (FIRST_X_ASSUM(fun th ->
         let l = lhs (concl th) in
         let f,args = strip_comb l in
         if is_const f && fst (dest_const f) = "word_cmp_loop" then
         MP_TAC(ISPECL (args @ [rand (rhs (concl th)); `t1:(A,C,FFI)wl_state`; `l1:num`; `l2:num`])
         data_to_word_assignProof_Compare1_code_thm) THEN
         REWRITE_TAC[th]
         else NO_TAC)) THEN
        (ANTS_TAC THENL
         [EXPAND_TAC "t1" THEN BIGPAUX_FROMLIST2_TAC THEN
         ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH; wl_get_var_def] THEN
         ASM_ARITH_TAC;
         ALL_TAC]) THEN
        (DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `smx2:num option` STRIP_ASSUME_TAC)) THEN
         ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def; option_DISTINCT] THEN
         MAP_EVERY EXISTS_TAC [`ck2:num`; `wl_state_permute (t:(A,C,FFI)wl_state)`;
         `smx2:num option`] THEN
         REPEAT CONJ_TAC THENL
         [EXPAND_TAC "t1" THEN
         REWRITE_TAC[PAIR_EQ; wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds;
         K_THM];
         MATCH_MP_TAC ASP5AUX_eq_bound_cmp THEN
         FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `smx2:num option`)) (concl th))) THEN
         EXPAND_TAC "t1" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
         FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ck2:num`)) (concl th))) THEN
         EXPAND_TAC "t1" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
         ASM_ARITH_TAC]);
       (ASP5AUX_EQ_RET_TAC)]]];
   (REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN REPEAT GEN_TAC THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [CONJUNCT2 word_eq_def] o
   check (fun th -> is_eq (concl th) && is_comb (lhand (concl th)) &&
   (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "word_eq_list"
   with Failure _ -> false))) THEN
   REWRITE_TAC[data_to_word_Equal1_code_def; data_to_word_list_Seq_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def])) THEN
  (ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN ASP5AUX_RET3_TAC;
   ALL_TAC]) THEN
  (COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
   CASES_ON `wl_state_memory (t:(A,C,FFI)wl_state) a1` THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
   CASES_ON `wl_state_memory (t:(A,C,FFI)wl_state) a2` THEN CASE_REWRITE_TAC[option_DISTINCT]) THEN
  (REWRITE_TAC[case_eq "option"; option_DISTINCT; EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `xr:A word` (X_CHOOSE_THEN `lr:num` (X_CHOOSE_THEN `ckr:num`
   STRIP_ASSUME_TAC)))) THEN
  (ASP5AUX_EV_TAC (wl_mem_load_def::ASP5AUX_EV_RWS2)) THEN
  (CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
   SIMP (ASP5AUX_cut_envs_0246::list_insert_def::domain_insert::domain_def::NOT_INSERT_EMPTY::
   ALL_DISTINCT::MEM::IS_SOME_DEF::lookup_insert::ASP5AUX_EV_RWS2)) THEN
  (SUBGOAL_THEN `~(wl_state_clock (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]) THEN
  (MP_TAC(ISPEC `env_to_list (LN:(A word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
   PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `lst:(num#A word_loc)list` (X_CHOOSE_THEN `perm:num->num->num`
   ASSUME_TAC)) THEN
   REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN SIMP[stack_size_eq2; stack_size_frame_def]) THEN
  (ASP5AUX_ABBREV_EV_TAC `Equal_code c:(A)wl_prog` `t1:(A,C,FFI)wl_state`) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`a:A word`; `a':A word`] o
   check (fun th -> is_forall (concl th) && length (fst (strip_forall (concl th))) = 2)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`t1:(A,C,FFI)wl_state`; `Equal1_location`; `2`; `xr:A word`;
   `lr:num`; `ckr:num`]) THEN
   ASM_REWRITE_TAC[]) THEN
  (ANTS_TAC THENL
   [EXPAND_TAC "t1" THEN BIGPAUX_FROMLIST2_TAC THEN
   ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH;
   sane_locals_size_def] THEN
   ASM_ARITH_TAC;
   ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `p1:num->num->num`
   (X_CHOOSE_THEN `smx1:num option` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LENGTH] THEN
   EXPAND_TAC "t1" THEN SIMP[wl_pop_env_def; wl_set_vars_def; alist_insert_def;
   asp5_ev_clause "wl_Skip"]) THEN
  (SUBGOAL_THEN `fromAList (lst:(num#A word_loc)list) = LN` ASSUME_TAC THENL
   [MATCH_MP_TAC IMP_spt_eq THEN REWRITE_TAC[wf_fromAList; sptree_wf_def; lookup_fromAList] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP env_to_list_lookup_equiv o
   check (fun th -> is_eq (concl th) &&
   can (find_term (fun u -> is_const u && fst (dest_const u) = "env_to_list")) (concl th))) THEN
   SIMP_TAC[lookup_def];
   ALL_TAC] THEN
   ASM_SIMP_TAC[fromAList_toAList; wf_inter; union_LN; domain_inter; domain_insert; domain_def] THEN
   CASE_REWRITE_TAC[]) THEN
  (REWRITE_TAC[UNION_EMPTY] THEN CASE_REWRITE_TAC[] THEN
   ASP5AUX_EV_TAC (lookup_inter_alt::domain_insert::domain_def::IN_INSERT::NOT_IN_EMPTY::
   ASP5AUX_EV_RWS2)) THEN
  (ASP5AUX_SPLIT_TAC `xr:A word = word 1` THENL
   [ALL_TAC;
   FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
   is_eq c && is_comb (lhs c) &&
   (try fst (dest_const (rator (lhs c))) = "SOME" with Failure _ -> false) &&
   can (find_term (fun u -> try fst (dest_var u) = "res" with Failure _ -> false)) c)) THEN
   REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
   CASE_REWRITE_TAC[option_DISTINCT] THEN
   MAP_EVERY EXISTS_TAC [`ck1:num`; `p1:num->num->num`; `smx1:num option`] THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[PAIR_EQ; wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds;
   K_THM];
   MATCH_MP_TAC ASP5AUX_eq_bound_ret THEN
   EXISTS_TAC `wl_state_locals_size (t:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[sane_locals_size_def];
   FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `smx1:num option`)) (concl th))) THEN
   TRY(EXPAND_TAC "t1") THEN
   SIMP[wl_state_INFO.ri_accfupds; K_THM; stack_size_eq2; stack_size_frame_def]];
   ASM_REWRITE_TAC[]]]) THEN
  (ASM_CASES_TAC `lr = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
   ASM_REWRITE_TAC[option_DISTINCT];
   ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (CASE_REWRITE_TAC[] THEN
   ASP5AUX_EV_TAC (lookup_inter_alt::domain_insert::domain_def::IN_INSERT::NOT_IN_EMPTY::
   WORD_ADD_0::ASP5AUX_EV_RWS2)) THEN
  (CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
   SIMP (lookup_inter_alt::domain_insert::domain_def::IN_INSERT::NOT_IN_EMPTY::ASP5AUX_EV_RWS2)) THEN
  (SUBGOAL_THEN `~(ck1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]) THEN
  (ASP5AUX_ABBREV_EV_TAC `Equal1_code:(A)wl_prog` `t5:(A,C,FFI)wl_state`) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`a:A word`; `a':A word`; `ckr:num`; `word 1:A word`; `lr:num`] o
   check (fun th -> is_forall (concl th) && length (fst (strip_forall (concl th))) = 5)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`t5:(A,C,FFI)wl_state`; `l1:num`; `l2:num`; `res:A word`;
   `l':num`; `wck':num`]) THEN
   ASM_REWRITE_TAC[]) THEN
  (ANTS_TAC THENL
   [EXPAND_TAC "t5" THEN BIGPAUX_FROMLIST2_TAC THEN
   ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH;
   sane_locals_size_def] THEN
   ASM_ARITH_TAC;
   ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `p2:num->num->num`
   (X_CHOOSE_THEN `smx2:num option` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wl_bad_fun_return_def; option_DISTINCT] THEN
   MAP_EVERY EXISTS_TAC [`ck2:num`; `p2:num->num->num`; `smx2:num option`] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "t5" THEN
   REWRITE_TAC[PAIR_EQ; wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds;
   K_THM];
   MATCH_MP_TAC ASP5AUX_eq_bound_ret2 THEN
   MAP_EVERY EXISTS_TAC [`smx1:num option`; `wl_state_locals_size (t:(A,C,FFI)wl_state)`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[sane_locals_size_def];
   FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
   is_comb c && is_comb (rator c) && rand (rator c) = `smx1:num option` &&
   (try fst (dest_const (rator (rator c))) = "option_le" with Failure _ -> false))) THEN
   EXPAND_TAC "t1" THEN
   SIMP[wl_state_INFO.ri_accfupds; K_THM; stack_size_eq2; stack_size_frame_def];
   FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
   is_comb c && is_comb (rator c) && rand (rator c) = `smx2:num option` &&
   (try fst (dest_const (rator (rator c))) = "option_le" with Failure _ -> false))) THEN
   EXPAND_TAC "t5" THEN
   SIMP[wl_state_INFO.ri_accfupds; K_THM]]])]);;

(* HOL4 line 12766 *)
let data_to_word_assignProof_Equal_code_thm = prove
 (`!c st dm m l wck v1 v2 res l' wck' (t:(A,C,FFI)wl_state) l1 l2.
     word_eq c st dm m l wck v1 v2 = SOME (res,l',wck') /\
     dm = wl_state_mdomain t /\
     m = wl_state_memory t /\
     st = wl_state_store t /\
     l <= wl_state_clock t /\
     shift_length c < dimindex (:A) /\
     wl_state_locals_size t = lookup Equal_location (wl_state_stack_size t) /\
     lookup Equal_location (wl_state_code t) = SOME (3,Equal_code c) /\
     lookup Equal1_location (wl_state_code t) = SOME (4,Equal1_code) /\
     lookup Compare1_location (wl_state_code t) = SOME (4,Compare1_code) /\
     wl_get_var 0 t = SOME (wl_Loc l1 l2) /\
     wl_get_var 2 t = SOME (wl_Word (v1:A word)) /\
     wl_get_var 4 t = SOME (wl_Word (v2:A word)) /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c < dimindex (:A) /\
     good_dimindex (:A) ==>
     ?ck new_p smx.
       wl_evaluate (Equal_code c,t) =
         (SOME (wl_Result (wl_Loc l1 l2) [wl_Word res]),
          wl_state_clock_fupd (K ck) (wl_state_locals_fupd (K LN)
            (wl_state_locals_size_fupd (K (SOME 0)) (wl_state_permute_fupd (K new_p)
               (wl_state_stack_max_fupd (K smx) t))))) /\
       option_le smx (OPTION_MAP2 MAX (wl_state_stack_max t)
                        (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t))
                           (eq_code_stack_max (wck + 1) (wl_state_stack_size t)))) /\
       l' <= ck`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT1 data_to_word_assignProof_Equal_code_lemma) THEN
  MAP_EVERY EXISTS_TAC [`st:(store_name,A word_loc)fmap`; `dm:A word->bool`;
                        `m:A word->A word_loc`; `l:num`; `v1:A word`; `v2:A word`;
                        `wck':num`] THEN
  ASM_REWRITE_TAC[sane_locals_size_def]);;

(* HOL4 line 12799 (local) *)
let data_to_word_assignProof_MIN_SUB = prove
 (`!a b c. MIN a b - c = MIN (a - c) (b - c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MIN] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 12805 *)
let assign_Equal = prove
 (assign_thm_stmt `op = BlockOp clos_Equal`,
  (ASP5AUX_INTRO_NAMES_TAC (DISCH_THEN SUBST1_TAC) THEN
   ASP5AUX_DO_APP_ASM_TAC ASP5AUX_do_app_Equal THEN
   DISCH_THEN(X_CHOOSE_THEN `xv1:data_v` (X_CHOOSE_THEN `xv2:data_v` (X_CHOOSE_THEN `b:bool`
   STRIP_ASSUME_TAC))) THEN
   RVEQ_TAC THEN ASP5AUX_args2_TAC) THEN
  (DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
   DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` (X_CHOOSE_THEN `ww2:A word_loc`
   STRIP_ASSUME_TAC))) THEN
  (FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASP5AUX_cut_state_refs) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `data_state_refs (x:(C,FFI)data_state) =
   data_state_refs (s:(C,FFI)data_state)`]) THEN
   FIRST_ASSUM(fun th0 -> let th = check ASP5AUX_IS_MEMREL th0 in
   MP_TAC(MATCH_MP memory_rel_simple_eq (CONJ th (CONJ (ASSUME
   `data_do_eq (data_state_refs (s:(C,FFI)data_state)) xv1 xv2 = Eq_val b`)
   (ASSUME `good_dimindex (:A)`))))) THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2:A word`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))))) THEN
  (ASP5AUX_UNFOLD_ASSIGN_TAC assign_Equal_def THEN REWRITE_TAC[data_to_word_list_Seq_def] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   ASP5AUX_EV_TAC (data_to_word_gcProof_word_and_one_eq_0_iff::WORD_OR_0::BIT_WORD_AND::
   ASP5AUX_EV_RWS2)) THEN
  (FIRST_ASSUM(fun th0 -> let th = check ASP5AUX_IS_MEMREL th0 in
   MP_TAC(MATCH_MP word_eq_thm (CONJ th (CONJ (ASSUME
   `data_do_eq (data_state_refs (s:(C,FFI)data_state)) xv1 xv2 = Eq_val b`)
   (ASSUME `good_dimindex (:A)`))))) THEN
   DISCH_THEN(X_CHOOSE_THEN `res:A word` (X_CHOOSE_THEN `lr:num` (X_CHOOSE_THEN `ckr:num`
   STRIP_ASSUME_TAC)))) THEN
  (ASM_CASES_TAC `bit 0 (w1:A word) /\ bit 0 (w2:A word)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
   SUBGOAL_THEN `(w1:A word = w2) <=> b` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   CASE_REWRITE_TAC[] THEN ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN
   ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASP5AUX_RESET0_TAC]) THEN
  (ASM_CASES_TAC `w1:A word = w2` THENL
   [SUBGOAL_THEN `b /\ res = word 1:A word` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [CONJUNCT1 word_eq_def] o
   check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
   (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_eq"
   with Failure _ -> false))) THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN
   ASP5AUX_RESET0_TAC;
   ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_code_rel_stubs o CONJUNCT1 o CONJUNCT2 o
   CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[data_to_word_gcProof_state_rel_thm] o
   check (fun th -> concl th = `data_to_word_gcProof_state_rel c l1 l2 (s:(C,FFI)data_state)
   (t:(A,C,FFI)wl_state) NONE locs`))) THEN
  (FIRST_ASSUM(MP_TAC o MATCH_MP cut_env_IMP_cut_envs o check (fun th ->
   can (find_term (fun u -> is_const u && fst (dest_const u) = "wl_cut_env")) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
   STRIP_ASSUME_TAC)) THEN
   CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "MustTerminate"))) THEN
   SUBGOAL_THEN `~(wl_state_termdep (t:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `wl_state_termdep (t:(A,C,FFI)wl_state) > 1` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `dimword (:A) < MustTerminate_limit (:A) - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[dimword_LESS_MustTerminate_limit]; ALL_TAC] THEN
   SUBGOAL_THEN `~(MustTerminate_limit (:A) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `dimword (:A) < MustTerminate_limit (:A) - 1` THEN ARITH_TAC; ALL_TAC] THEN
   CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV (asp5_ev_clause "wl_Call"))) THEN
   SIMP (data_to_word_get_names_def::cut_envs_adjust_sets_ODD::domain_adjust_sets::
   ALL_DISTINCT::MEM::ASP5AUX_EV_RWS2)) THEN
  (MP_TAC(ISPEC `env_to_list (y2:(A word_loc)spt) (wl_state_permute (t:(A,C,FFI)wl_state))`
   PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `lst:(num#A word_loc)list` (X_CHOOSE_THEN `perm:num->num->num`
   ASSUME_TAC)) THEN
   REWRITE_TAC[wl_push_env_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN SIMP[stack_size_eq2; stack_size_frame_def]) THEN
  (ASP5AUX_ABBREV_EV_TAC `Equal_code c:(A)wl_prog` `t1:(A,C,FFI)wl_state`) THEN
  (FIRST_ASSUM(fun th ->
   let l = lhs (concl th) in
   let f,args = strip_comb l in
   if is_const f && fst (dest_const f) = "word_eq" then
   let r = rand (rhs (concl th)) in
   let r1,r23 = dest_pair r in let r2,r3 = dest_pair r23 in
   MP_TAC(ISPECL (args @ [r1; r2; r3; `t1:(A,C,FFI)wl_state`; `n:num`; `l:num`])
   data_to_word_assignProof_Equal_code_thm) THEN REWRITE_TAC[th]
   else NO_TAC)) THEN
  (ANTS_TAC THENL
   [EXPAND_TAC "t1" THEN BIGPAUX_FROMLIST2_TAC THEN
   ASM_SIMP_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH; wl_get_var_def;
   LE_REFL] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf o check ASP5AUX_IS_MEMREL) THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
   ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `new_p:num->num->num`
   (X_CHOOSE_THEN `smx:num option` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LENGTH] THEN
   EXPAND_TAC "t1" THEN SIMP[wl_pop_env_def; wl_set_vars_def; alist_insert_def;
   asp5_ev_clause "wl_Skip"]) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_envs_wf) THEN
   SUBGOAL_THEN `fromAList (lst:(num#A word_loc)list) = y2` ASSUME_TAC THENL
   [MATCH_MP_TAC IMP_spt_eq THEN ASM_REWRITE_TAC[wf_fromAList; lookup_fromAList] THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP env_to_list_lookup_equiv o
   check (fun th -> is_eq (concl th) &&
   can (find_term (fun u -> is_const u && fst (dest_const u) = "env_to_list")) (concl th))) THEN
   SIMP_TAC[];
   ALL_TAC] THEN
   ASM_SIMP_TAC[fromAList_toAList] THEN
   REWRITE_TAC[domain_union; UNION_ACI] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
   SIMP ASP5AUX_EV_RWS2) THEN
  (ASP5AUX_EV_TAC ASP5AUX_EV_RWS2 THEN CASE_REWRITE_TAC[] THEN
   ASP5AUX_EV_TAC ASP5AUX_EV_RWS2) THEN
  ((SUBGOAL_THEN `!X. wl_state_locals_fupd (K X)
   (wl_state_locals_size_fupd (K (wl_state_locals_size t))
   (wl_state_stack_fupd (K (wl_state_stack t))
   (wl_state_stack_max_fupd (K smx)
   (wl_state_permute_fupd (K new_p)
   (wl_state_clock_fupd (K (wl_state_clock t))
   (wl_state_termdep_fupd (K (wl_state_termdep t)) (t:(A,C,FFI)wl_state))))))) =
   wl_state_stack_max_fupd (K smx) (wl_state_permute_fupd (K new_p)
   (wl_state_locals_fupd (K X) t))` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
   REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM];
   ALL_TAC]) THEN
   COND_CASES_TAC THEN ASP4AUX_NONE_TAC THEN
   MATCH_MP_TAC ASP5AUX_state_rel_finish_sp THEN
   EXISTS_TAC `x:(C,FFI)data_state` THEN
   REWRITE_TAC[do_stack_def; do_space_def; op_space_reset_def; THE_DEF; LET_DEF; LET_END_DEF;
   data_state_INFO.ri_accfupds; K_THM]) THEN
  (UNDISCH_TAC `y = sptree_union y2 (y1:(A word_loc)spt)` THEN DISCH_THEN SUBST_ALL_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP evaluate_stack_max_le o check (fun th -> is_eq (concl th) &&
   can (find_term ((=) `Equal_code c:(A)wl_prog`)) (lhs (concl th)))) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_state_rel_stack_facts o check (fun th ->
   concl th = `data_to_word_gcProof_state_rel c l1 l2 (x:(C,FFI)data_state)
   (t:(A,C,FFI)wl_state) NONE locs`)) THEN
   UNDISCH_TAC `option_le smx (OPTION_MAP2 MAX (wl_state_stack_max (t1:(A,C,FFI)wl_state))
   (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t1))
   (eq_code_stack_max (MIN (vs_depth xv1) (vs_depth xv2) + 1) (wl_state_stack_size t1))))` THEN
   EXPAND_TAC "t1" THEN
   REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; stack_size_eq2; stack_size_frame_def] THEN
   REPEAT DISCH_TAC THEN
   MP_TAC(ISPECL [`wl_state_stack_max (t:(A,C,FFI)wl_state)`;
   `data_state_stack_max (x:(C,FFI)data_state)`;
   `wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state))`;
   `wl_state_locals_size (t:(A,C,FFI)wl_state)`;
   `smx:num option`; `MIN (vs_depth xv1) (vs_depth xv2)`;
   `wl_state_stack_size (t:(A,C,FFI)wl_state)`] ASP5AUX_equal_stack_bounds) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[stack_consumed_def; ASP5AUX_MIN_SUC] THEN
   REWRITE_TAC[GSYM(ASSUME `wl_state_stack_size (t:(A,C,FFI)wl_state) =
   data_state_stack_frame_sizes (x:(C,FFI)data_state)`);
   GSYM(ASSUME `wl_state_locals_size (t:(A,C,FFI)wl_state) =
   data_state_locals_size (x:(C,FFI)data_state)`)] THEN
   ASM_REWRITE_TAC[]) THEN
  (ASP5AUX_CALL_FINISH_TAC));;

(* HOL4 line 12959 *)
let assign_WordOpW8 = prove
 (assign_thm_stmt `(?opw. op = WordOp (WordOpw W8 opw))`,
  (ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `opw:opw` SUBST1_TAC)) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP5AUX_do_app_WordOpW8 o check (fun th ->
     can (find_term (fun u -> is_const u && fst (dest_const u) = "data_do_app")) (concl th))) THEN
   DISCH_THEN(X_CHOOSE_THEN `w1:byte` (X_CHOOSE_THEN `w2:byte` STRIP_ASSUME_TAC)) THEN
   RVEQ_TAC THEN ASP5AUX_args2_TAC THEN
   DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
   DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` (X_CHOOSE_THEN `ww2:A word_loc`
     STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP ASP5AUX_memory_rel_Number2_num o check ASP5AUX_IS_MEMREL) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
     MP_TAC(ISPEC `w1:byte` VAL_BOUND) THEN MP_TAC(ISPEC `w2:byte` VAL_BOUND) THEN
     REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
     DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC)] THEN
   ASP5AUX_UNFOLD_ASSIGN_TAC assign_WordOpW8_def THEN
   RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
   SUBGOAL_THEN `dimindex (:A) - 10 < dimindex (:A) /\
                 ~(dimindex (:A) - 10 >= dimindex (:A))` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o REWRITE_RULE[good_dimindex_def] o check (fun th ->
       concl th = `good_dimindex (:A)`)) THEN ARITH_TAC;
     ALL_TAC] THEN
   CASES_ON `opw:opw` THEN CASE_REWRITE_TAC[lookup_word_op_def] THEN
   ASP5AUX_EV_TAC (WORD_AND_NOT0::WORD_OR_0::WORD_XOR_0::WORD_ADD_0::ASP5AUX_val_word_lt::
                   ASP5AUX_EV_RWS2) THEN
   ASM_SIMP_TAC[ASP5AUX_carried_add; ASP5AUX_carried_sub] THEN
   ASP5AUX_FINISH_TAC THEN REWRITE_TAC[opw_lookup_def] THEN
   TRY(MATCH_MP_TAC memory_rel_And THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   TRY(MATCH_MP_TAC memory_rel_Or THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   TRY(MATCH_MP_TAC memory_rel_Xor THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   REWRITE_TAC[GSYM MP6AUX_SMALLNUM_NUM] THEN ASP5AUX_NUMBER_MEM_TAC THEN
   MATCH_MP_TAC ASP5AUX_small_int_num THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `256` THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[w2n_lt_256]));;

(* HOL4 line 13152: val assign_WordOp64 (SIMP_CONV of assign_def on        *)
(* assign c n l dest (WordOp (WordOpw W64 opw)) [e1; e2] names_opt): a      *)
(* proof tool, not stated                                                    *)

(* HOL4 line 13156 *)
let mw2n_2_IMP = prove
 (`!w1 w2:A word n.
     mw2n [w1;w2] = n ==> w2 = word (n DIV dimword (:A)) /\ w1 = word n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw2n_def; MULT_CLAUSES; ADD_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `w1:A word` VAL_BOUND) THEN REWRITE_TAC[GSYM dimword_def] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(val (w1:A word) + dimword (:A) * val (w2:A word)) DIV dimword (:A) =
                  val w2` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `val (w1:A word)` THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      REWRITE_TAC[WORD_VAL]];
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; GSYM dimword_def] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN ASM_SIMP_TAC[MOD_LT]]);;

(* HOL4 line 13167 (HOL4 Abbrev (x = e) is the plain equation) *)
let IMP_mw2n_2 = prove
 (`!x1 x2:A word n.
     (x2 = word_extract 63 32 (word n:int64)) /\
     (x1 = word_extract 31 0 (word n:int64)) /\
     n < dimword (:64) /\ dimindex (:A) = 32 ==>
     mw2n [x1;x2] = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[mw2n_def; word_extract_n2w] THEN
  ASM_REWRITE_TAC[DIMINDEX_64; dimword_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITS_THM; MULT_CLAUSES; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `n < dimword (:64)` THEN REWRITE_TAC[dimword_def; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[DIV_1; MOD_MOD_REFL] THEN
  SUBGOAL_THEN `(n DIV 4294967296) MOD 4294967296 = n DIV 4294967296` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`n:num`; `4294967296`] DIVISION) THEN ARITH_TAC]);;

(* HOL4 line 13182 *)
let evaluate_WordOp64_on_32 = prove
 (`!l opw (t:(A,C,FFI)wl_state) (c':int64) (c'':int64).
     dimindex (:A) = 32 ==>
     ?w27 w29.
       wl_evaluate
         (WordOp64_on_32 opw,
          wl_state_locals_fupd
            (K (insert 23 (wl_Word (word_extract 31 0 c''))
                 (insert 21 (wl_Word (word_extract 63 32 c''))
                    (insert 13 (wl_Word (word_extract 31 0 c'))
                       (insert 11 (wl_Word (word_extract 63 32 c')) l))))) t) =
       (NONE,wl_state_locals_fupd
          (K (insert 31 (wl_Word (word_extract 63 32 (opw_lookup opw c' c'')))
               (insert 33 (wl_Word (word_extract 31 0 (opw_lookup opw c' c'')))
                  (insert 27 w27
                     (insert 29 w29
                        (insert 23 (wl_Word (word_extract 31 0 c''))
                           (insert 21 (wl_Word (word_extract 63 32 c''))
                              (insert 13 (wl_Word (word_extract 31 0 c'))
                                 (insert 11 (wl_Word (word_extract 63 32 c')) l))))))))) t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CASES_ON `opw:opw` THEN
  REWRITE_TAC[WordOp64_on_32_def] THEN CASE_REWRITE_TAC[opw_lookup_def] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP5AUX_EV_TAC (ASP5AUX_inst_AddCarry::WORD_NEG_1::WORD_XOR_NOT0::WORD_AND_NOT0::WORD_OR_0::
                  WORD_XOR_0::ASP5AUX_bool_word_0::ASP5AUX_EV_RWS2) THEN
  REWRITE_TAC[WORD_EXTRACT_OVER_BITWISE] THEN
  REWRITE_TAC[COND_SWAP] THEN ASM_SIMP_TAC[ASP5AUX_add64_on_32; ASP5AUX_sub64_on_32] THEN
  REWRITE_TAC[ASP5AUX_insert_29_31; insert_shadow] THEN
  ASP5AUX_EXISTS_MATCH_TAC);;

(* HOL4 line 13317 *)
let IMP_encode_header_NOT_NONE = prove
 (`!c. dimindex (:A) = 32 /\ 1 < data_to_word_config_len_size c /\
       1 < 30 - data_to_word_config_len_size c ==>
       ~(encode_header c 3 2 = (NONE:(A word)option))`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[encode_header_def; dimword_def] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `!k. 2 <= k ==> 3 < 2 EXP k /\ 2 < 2 EXP k` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    (MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 2` THEN
     ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV);
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= data_to_word_config_len_size c /\
                2 <= (32 - data_to_word_config_len_size c) - 2` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[option_DISTINCT]);;

(* HOL4 line 13324 *)
let assign_WordOpW64 = prove
 (assign_thm_stmt `(?opw. op = WordOp (WordOpw W64 opw))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `opw:opw` SUBST1_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP5AUX_do_app_WordOpW64 o check (fun th ->
     can (find_term (fun u -> is_const u && fst (dest_const u) = "data_do_app")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:int64` (X_CHOOSE_THEN `w2:int64` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN ASP5AUX_args2_TAC THEN
  DRULE_ALL ASP4AUX_state_rel_get_var2 THEN
  DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` (X_CHOOSE_THEN `ww2:A word_loc`
     STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf o check ASP5AUX_IS_MEMREL) THEN
  ASP5AUX_WORD64_ARGS_TAC THEN RVEQ_TAC THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_WordOpW64_def THEN
  SUBGOAL_THEN `dimindex(:A) = 64 \/ dimindex(:A) = 32` MP_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASP5AUX_WORD64_CONDS_TAC THENL
   [(* dimindex (:A) = 64 *)
    CASES_ON `encode_header c 3 1:(A word)option` THEN CASE_REWRITE_TAC[FST] THENL
     [ASP5AUX_W64_GIVEUP_TAC `1`; ALL_TAC] THEN
    ASP5AUX_REAL_ADDR2_TAC THEN
    CASES_ON `opw:opw` THEN CASE_REWRITE_TAC[opw_lookup_def] THEN
    ASP5AUX_EV_TAC (WORD_ADD_0::WORD_OR_0::WORD_XOR_0::ASP5AUX_EV_RWS2) THEN
    ASP5AUX_WW64_FINISH_TAC [ASP5AUX_zx_opw];
    (* dimindex (:A) = 32 *)
    CASES_ON `encode_header c 3 2:(A word)option` THEN CASE_REWRITE_TAC[FST] THENL
     [ASP5AUX_W64_GIVEUP_TAC `2`; ALL_TAC] THEN
    ASP5AUX_REAL_ADDR2_TAC THEN
    SUBGOAL_THEN `!w. wl_word_exp (wl_state_locals_fupd (K (insert 15 w (wl_state_locals t)))
                     (t:(A,C,FFI)wl_state)) (real_addr c (adjust_var a2)) = SOME (wl_Word x2)`
      ASSUME_TAC THENL
     [GEN_TAC THEN ASM_SIMP_TAC[word_exp_insert; ASP5AUX_ODD_adjust_var; ARITH]; ALL_TAC] THEN
    SUBGOAL_THEN `word_shl bytes_in_word 1 = word_mul (word 2) bytes_in_word:A word`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[data_to_word_list_Seq_def] THEN
    ASP5AUX_EV_TAC (WORD_ADD_0::ASP5AUX_EV_RWS2) THEN
    MP_TAC(ISPECL [`insert 17 (wl_Word x2) (insert 15 (wl_Word x1)
                       (wl_state_locals (t:(A,C,FFI)wl_state)))`; `opw:opw`;
                   `t:(A,C,FFI)wl_state`; `w1:int64`; `w2:int64`] evaluate_WordOp64_on_32) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w27:A word_loc` (X_CHOOSE_THEN `w29:A word_loc` SUBST1_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    ASP5AUX_WW32_FINISH_TAC `opw_lookup opw (w1:int64) w2`]);;

(* HOL4 line 13465 *)
let assign_WordShiftW8 = prove
 (assign_thm_stmt `(?sh n. op = WordOp (WordShift W8 sh n))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `sh:shift` (X_CHOOSE_THEN `k:num`
    SUBST1_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP5AUX_do_app_WordShiftW8 o check (fun th ->
     can (find_term (fun u -> is_const u && fst (dest_const u) = "data_do_app")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:byte` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN ASP5AUX_args1_TAC THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `small_int (:A) (&(val (w1:byte)))` ASSUME_TAC THENL
   [MATCH_MP_TAC ASP5AUX_small_int_num THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `w1:byte` w2n_lt_256) THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th0 -> let th = check ASP5AUX_IS_MEMREL th0 in
    MP_TAC(MATCH_MP memory_rel_Number_IMP (CONJ (ASSUME `good_dimindex (:A)`)
      (CONJ (ASSUME `small_int (:A) (&(val (w1:byte)))`) th)))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MP6AUX_SMALLNUM_NUM]) THEN
  ASP5AUX_UNFOLD_ASSIGN_TAC assign_WordShiftW8_def THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP5AUX_shift8_amounts o check (fun th ->
    concl th = `good_dimindex (:A)`)) THEN
  SUBGOAL_THEN `!sh m. wl_word_exp (t:(A,C,FFI)wl_state) (ShiftVar sh (adjust_var a1) m) =
      SOME (wl_Word (shift_lookup sh (word (4 * val (w1:byte))) m))` ASSUME_TAC THENL
   [X_GEN_TAC `sh0:shift` THEN X_GEN_TAC `m:num` THEN
    ONCE_REWRITE_TAC[word_exp_set_var_ShiftVar_lemma] THEN
    ASM_REWRITE_TAC[] THEN CASES_ON `sh0:shift` THEN
    CASE_REWRITE_TAC[shift_lookup_def; OPTION_MAP_DEF];
    ALL_TAC] THEN
  CASES_ON `sh:shift` THEN CASE_REWRITE_TAC[shift_lookup_def] THEN
  ASP5AUX_EV_TAC (ASP5AUX_val_word_lt::WORD_OR_0::ASP5AUX_EV_RWS2) THEN
  ASP5AUX_FINISH_TAC THEN
  ASM_SIMP_TAC[ASP5AUX_shift8_Lsl; ASP5AUX_shift8_Lsr; ASP5AUX_shift8_Asr;
               ASP5AUX_shift8_Ror] THEN
  REWRITE_TAC[GSYM MP6AUX_SMALLNUM_NUM] THEN ASP5AUX_NUMBER_MEM_TAC THEN
  MATCH_MP_TAC ASP5AUX_small_int_num THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `256` THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[w2n_lt_256]);;

(* HOL4 line 13734: val assign_WordShift64 (SIMP_CONV of assign_def): a     *)
(* proof tool, not stated                                                    *)

(* HOL4 line 13738 *)
let evaluate_WordShift64_on_32 = prove
 (`!l sh n (t:(A,C,FFI)wl_state) (c':int64).
     dimindex (:A) = 32 ==>
     wl_evaluate
       (WordShift64_on_32 sh n,
        wl_state_locals_fupd
          (K (insert 13 (wl_Word (word_extract 31 0 c'))
               (insert 11 (wl_Word (word_extract 63 32 c')) l))) t) =
     (NONE,wl_state_locals_fupd
        (K (insert 31 (wl_Word (word_extract 63 32 (shift_lookup sh c' n)))
             (insert 33 (wl_Word (word_extract 31 0 (shift_lookup sh c' n)))
                (insert 13 (wl_Word (word_extract 31 0 c'))
                   (insert 11 (wl_Word (word_extract 63 32 c')) l))))) t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n MOD 64 < 64` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  CASES_ON `sh:shift` THEN
  REWRITE_TAC[WordShift64_on_32_def; distinctness "shift"; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[shift_lookup_def] THEN
  ASM_CASES_TAC `n < 32` THEN ASM_CASES_TAC `n MOD 64 < 32` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[data_to_word_list_Seq_def] THEN
  ASP5AUX_EV_TAC (ASP5AUX_word_exp_ShiftVar_ins::WORD_OR_0::ASP5AUX_EV_RWS2) THEN
  ASP5AUX_LOCALS_EQ_TAC [DIMINDEX_64; ASSUME `dimindex(:A) = 32`]);;

(* HOL4 line 13832 *)
let assign_WordShiftW64 = prove
 (assign_thm_stmt `(?sh n. op = WordOp (WordShift W64 sh n))`,
  ASP5AUX_INTRO_TAC (DISCH_THEN(X_CHOOSE_THEN `sh:shift` (X_CHOOSE_THEN `k:num`
    SUBST1_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ASP5AUX_do_app_WordShiftW64 o check (fun th ->
     can (find_term (fun u -> is_const u && fst (dest_const u) = "data_do_app")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:int64` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN ASP5AUX_args1_TAC THEN
  DRULE_ALL ASP4AUX_state_rel_get_var1 THEN
  DISCH_THEN(X_CHOOSE_THEN `ww1:A word_loc` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASP4AUX_memory_rel_conf o check ASP5AUX_IS_MEMREL) THEN
  FIRST_ASSUM(fun th0 -> let th = check ASP5AUX_IS_MEMREL th0 in
    MP_TAC(MATCH_MP memory_rel_Word64_IMP (CONJ th (ASSUME `good_dimindex (:A)`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr1:num` (X_CHOOSE_THEN `x1:A word` (X_CHOOSE_THEN `h1:A word`
    STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN ASP5AUX_UNFOLD_ASSIGN_TAC assign_WordShiftW64_def THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `dimindex(:A) = 64 \/ dimindex(:A) = 32` MP_TAC THENL
   [ASM_MESON_TAC[good_dimindex_def]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASP5AUX_WORD64_CONDS_TAC THENL
   [(* dimindex (:A) = 64 *)
    CASES_ON `encode_header c 3 1:(A word)option` THEN CASE_REWRITE_TAC[FST] THENL
     [ASP5AUX_W64_GIVEUP_TAC `1`; ALL_TAC] THEN
    SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                  SOME (wl_Word x1)` ASSUME_TAC THENL
     [MATCH_MP_TAC get_var_get_real_addr_lemma THEN
      EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[data_to_word_list_Seq_def; LoadWord64_def] THEN
    ASP5AUX_EV_TAC (WORD_ADD_0::ASP5AUX_word_exp_ShiftVar_ins::ASP5AUX_EV_RWS2) THEN
    ASP5AUX_WW64_FINISH_TAC [ASP5AUX_zx_shift];
    (* dimindex (:A) = 32 *)
    CASES_ON `encode_header c 3 2:(A word)option` THEN CASE_REWRITE_TAC[FST] THENL
     [ASP5AUX_W64_GIVEUP_TAC `2`; ALL_TAC] THEN
    SUBGOAL_THEN `wl_word_exp (t:(A,C,FFI)wl_state) (real_addr c (adjust_var a1)) =
                  SOME (wl_Word x1)` ASSUME_TAC THENL
     [MATCH_MP_TAC get_var_get_real_addr_lemma THEN
      EXISTS_TAC `get_addr c ptr1 (wl_Word (word 0)):A word` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `word_shl bytes_in_word 1 = word_mul (word 2) bytes_in_word:A word`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[data_to_word_list_Seq_def] THEN
    ASP5AUX_EV_TAC (WORD_ADD_0::ASP5AUX_EV_RWS2) THEN
    MP_TAC(ISPECL [`insert 15 (wl_Word x1) (wl_state_locals (t:(A,C,FFI)wl_state))`;
                   `sh:shift`; `k:num`; `t:(A,C,FFI)wl_state`; `w1:int64`]
                  evaluate_WordShift64_on_32) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    ASP5AUX_WW32_FINISH_TAC `shift_lookup sh (w1:int64) k`]);;

(* HOL4 lines 13990-14002: vals assign_FP_cmp, assign_FP_top, assign_FP_bop, *)
(* assign_FP_uop (SIMP_CONV of assign_def): proof tools, not stated          *)
