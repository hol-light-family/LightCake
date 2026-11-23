(* ========================================================================= *)
(* word_allocProof_p2: part 2 (HOL4 lines 5708-11484) of the port of HOL4    *)
(* compiler/backend/proofs/word_allocProofScript.sml (CakeML v3479).         *)
(* Correctness of the SSA pass (ssa_cc_trans, full_ssa_cc_trans), the        *)
(* syntactic conventions it establishes, and word_alloc's pre/post           *)
(* conventions.  Part 1 is word_allocProof_p1.ml; word_allocProof.ml loads   *)
(* both.  The notes on the rendering in word_allocProof_p1.ml apply here.    *)
(* - WALLOCPAUX_ names are local helpers (not HOL4 names).                   *)
(* ========================================================================= *)

needs "compiler/backend/proofs/word_allocProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 line 5708 *)
let is_alloc_var_add = prove
 (`!na. is_alloc_var na ==> is_alloc_var (na + 4)`,
  REWRITE_TAC[WALLOCPAUX_is_alloc_var_add4]);;

(* HOL4 line 5717 *)
let is_stack_var_add = prove
 (`!na. is_stack_var na ==> is_stack_var (na + 4)`,
  GEN_TAC THEN REWRITE_TAC[is_stack_var_def] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `na + 4 = 1 * 4 + na`] THEN REWRITE_TAC[MOD_MULT_ADD]);;

(* HOL4 line 5726 *)
let is_alloc_var_flip = prove
 (`!na. is_alloc_var na ==> is_stack_var (na + 2)`,
  REWRITE_TAC[is_alloc_var_def; is_stack_var_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 5737 *)
let is_stack_var_flip = prove
 (`!na. is_stack_var na ==> is_alloc_var (na + 2)`,
  REWRITE_TAC[is_alloc_var_def; is_stack_var_def] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 5749 *)
let list_next_var_rename_props = prove
 (`!ls (ssa:num spt) na ls' ssa' na'.
     list_next_var_rename ls ssa na = (ls',ssa',na')
     ==> (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa
     ==> na <= na' /\
         (is_alloc_var na ==> is_alloc_var na') /\
         (is_stack_var na ==> is_stack_var na') /\
         ssa_map_ok na' ssa'`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_next_var_rename_def; next_var_rename_def; LET_DEF; LET_END_DEF;
              PAIR_EQ; pair_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    SIMP_TAC[LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename t (insert h na ssa) (na + 4)`
    [`ys:num list`; `s2:num spt`; `n2:num`] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`insert h na (ssa:num spt)`; `na + 4`; `ys:num list`;
                                `s2:num spt`; `n2:num`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[is_alloc_var_add; is_stack_var_add];
      MATCH_MP_TAC ssa_map_ok_extend THEN ASM_MESON_TAC[convention_partitions]];
    ALL_TAC] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_MESON_TAC[is_alloc_var_add];
    ASM_MESON_TAC[is_stack_var_add];
    FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 line 5780 *)
let list_next_var_rename_move_props = prove
 (`!ls (ssa:num spt) na (ls':(A)wl_prog) ssa' na'.
     list_next_var_rename_move ssa na ls = (ls',ssa',na')
     ==> (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa
     ==> na <= na' /\
         (is_alloc_var na ==> is_alloc_var na') /\
         (is_stack_var na ==> is_stack_var na') /\
         ssa_map_ok na' ssa'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename ls (ssa:num spt) na`
    [`l2:num list`; `s2:num spt`; `n2:num`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["ssa'"; "na'"]))) THEN
  MATCH_MP_TAC list_next_var_rename_props THEN
  MAP_EVERY EXISTS_TAC [`ls:num list`; `l2:num list`] THEN FIRST_ASSUM ACCEPT_TAC);;

(* HOL4 line 5796 *)
let next_var_rename_props = prove
 (`!ls (ssa:num spt) na ls' ssa' na'.
     next_var_rename ls ssa na = (ls',ssa',na')
     ==> (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa
     ==> na <= na' /\
         (is_alloc_var na ==> is_alloc_var na') /\
         (is_stack_var na ==> is_stack_var na') /\
         ssa_map_ok na' ssa'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC list_next_var_rename_props THEN
  MAP_EVERY EXISTS_TAC [`[ls:num]`; `[ls':num]`] THEN
  UNDISCH_TAC `next_var_rename ls (ssa:num spt) na = ls',ssa',na'` THEN
  REWRITE_TAC[list_next_var_rename_def; next_var_rename_def; LET_DEF; LET_END_DEF;
              PAIR_EQ; pair_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  SIMP_TAC[]);;

(* HOL4 line 5817 *)
let ssa_cc_trans_inst_props = prove
 (`!(i:(A)inst) (ssa:num spt) na (i':(A)wl_prog) ssa' na'.
     ssa_cc_trans_inst i ssa na = (i',ssa',na')
     ==> ssa_map_ok na ssa /\ is_alloc_var na
     ==> na <= na' /\ is_alloc_var na' /\ ssa_map_ok na' ssa'`,
  MATCH_MP_TAC ssa_cc_trans_inst_ind THEN
  REWRITE_TAC[ssa_cc_trans_inst_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN
  ASM_MESON_TAC[is_alloc_var_add; ssa_map_ok_extend; convention_partitions]);;

(* HOL4 line 5834: val exp_tac (ML tactic) is not needed *)

(* HOL4 line 5838 *)
let fix_inconsistencies_props = prove
 (`!prio ssaL ssaR na (a:(A)wl_prog) (b:(A)wl_prog) na' ssaU.
     fix_inconsistencies prio ssaL ssaR na = (a,b,na',ssaU)
     ==> is_alloc_var na /\ ssa_map_ok na ssaL /\ ssa_map_ok na ssaR
     ==> na <= na' /\ is_alloc_var na' /\ ssa_map_ok na' ssaU`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fix_inconsistencies_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPECL [`MAP FST (toAList (sptree_union ssaL ssaR:num spt))`; `na:num`; `ssaL:num spt`;
                 `ssaR:num spt`] merge_moves_frame) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves (MAP FST (toAList (sptree_union ssaL ssaR:num spt)))
                          ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPECL [`prio:((1,1)sum)option`; `MAP FST (toAList (sptree_union ssaL ssaR:num spt))`;
                 `n1:num`; `sL:num spt`; `sR:num spt`]
                (INST_TYPE [`:A`,`:A`] fake_moves_frame)) THEN
  WALLOCPAUX_TUPLE_TAC `fake_moves prio (MAP FST (toAList (sptree_union ssaL ssaR:num spt))) sL sR n1:
                          (A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`fL:(A)wl_prog`; `fR:(A)wl_prog`; `n2:num`; `sL2:num spt`; `sR2:num spt`] THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["na'"; "ssaU"]))) THEN
  ASM_MESON_TAC[LE_TRANS]);;

(* HOL4 line 5857: val th (ML) is folded into the proofs that use it *)

(* HOL4 line 5862 *)
let flip_rw = prove
 (`!na. (is_stack_var (na + 2) <=> is_alloc_var na) /\
        (is_alloc_var (na + 2) <=> is_stack_var na)`,
  GEN_TAC THEN REWRITE_TAC[is_alloc_var_def; is_stack_var_def] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  SUBGOAL_THEN `na MOD 4 < 4` MP_TAC THENL [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`na MOD 4`,`m:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 lines 5876-5892: val swap_imp and val list_next_var_rename_props_2 (ML) *)
(* are not needed                                                           *)

(* HOL4 line 5894 *)
let ssa_map_ok_lem = prove
 (`!na (ssa:num spt). ssa_map_ok na ssa ==> ssa_map_ok (na + 2) ssa`,
  MESON_TAC[ssa_map_ok_more; ARITH_RULE `na <= na + 2`]);;

(* HOL4 line 5901 *)
let list_next_var_rename_move_props_2 = prove
 (`!ls (ssa:num spt) na (ls':(A)wl_prog) ssa' na'.
     list_next_var_rename_move ssa (na + 2) ls = (ls',ssa',na')
     ==> (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa
     ==> na + 2 <= na' /\
         (is_alloc_var na ==> is_stack_var na') /\
         (is_stack_var na ==> is_alloc_var na') /\
         ssa_map_ok na' ssa'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP list_next_var_rename_move_props) THEN
  REWRITE_TAC[flip_rw] THEN MESON_TAC[ssa_map_ok_lem]);;

(* HOL4 line 5916 *)
let ssa_map_ok_inter = prove
 (`!na (ssa:num spt) (ssa':B spt). ssa_map_ok na ssa ==> ssa_map_ok na (sptree_inter ssa ssa')`,
  REWRITE_TAC[ssa_map_ok_def; lookup_inter] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
  CASES_ON `lookup x (ssa:num spt)` THEN CASES_ON `lookup x (ssa':B spt)` THEN
  ASM_REWRITE_TAC[option_CASE; option_DISTINCT] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5925 *)
let ssa_map_ok_insert = prove
 (`!na (ssa:num spt) x y.
     ssa_map_ok na ssa /\ y < na /\ ~is_phy_var y ==> ssa_map_ok na (insert x y ssa)`,
  REWRITE_TAC[ssa_map_ok_def; lookup_insert] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x':num`; `y':num`] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5935 *)
let ssa_map_ok_force_rename = prove
 (`!na ls (ssa:num spt).
     ssa_map_ok na ssa /\ ALL (\x. SND x < na /\ ~is_phy_var (SND x)) ls
     ==> ssa_map_ok na (force_rename ls ssa)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [SIMP_TAC[force_rename_def]; ALL_TAC] THEN
  SUBGOAL_THEN `?x y. h = (x:num,y:num)` (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[force_rename_def; ALL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ssa_map_ok_insert THEN ASM_REWRITE_TAC[]);;

(* helpers for ssa_cc_trans_props (local to this file) *)

let WALLOCPAUX_PROPS_PRE_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a = lhand w in
     if is_forall a || is_conj a then (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) g
     else ALL_TAC g) THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC;;

let WALLOCPAUX_PROPS_EQ_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  STRIP_TAC;;

let WALLOCPAUX_PROPS_FIN_TAC : tactic =
  REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[next_var_rename_props; list_next_var_rename_props; ssa_cc_trans_inst_props;
                LE_TRANS; LE_REFL];;

let WALLOCPAUX_PROPS_LNVRM_TAC (n:term) : tactic =
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try rand(rator(lhs(concl th))) = mk_binop `(+):num->num->num` n `2` with Failure _ -> false)
    then MP_TAC(MATCH_MP list_next_var_rename_move_props_2 th) else NO_TAC);;

let WALLOCPAUX_PROPS_ALLOC_TAC : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
  WALLOCPAUX_PROPS_LNVRM_TAC `na:num` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  WALLOCPAUX_PROPS_LNVRM_TAC `na'':num` THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_inter THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[];;

let WALLOCPAUX_PROPS_CALL_TAC : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  WALLOCPAUX_PROPS_LNVRM_TAC `na:num` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  WALLOCPAUX_PROPS_LNVRM_TAC `na'':num` THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_inter THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_props o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename"
     with Failure _ -> false))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`stack_mov:(A)wl_prog`; `ssa'':num spt`;
      `sptree_inter ssa'' (sptree_union (FST (numset:num_set#num_set)) (SND numset)):num spt`; `na'':num`;
      `MAP FST (toAList (sptree_union (FST (numset:num_set#num_set)) (SND numset)))`;
      `ret_mov:(A)wl_prog`; `ssa''':num spt`; `na''':num`; `ret':num list`; `ssa_2_p:num spt`;
      `na_2_p:num`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 11)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`ren_ret_handler:(A)wl_prog`; `ssa_2:num spt`; `na_2:num`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `prog':(A)wl_prog,ssa':num spt,na':num`)) THEN
  MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC[option_CASE; PAIR_EQ] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n0 hp k1 k2. hq = (n0:num,hp:(A)wl_prog,k1:num,k2:num)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[option_CASE; pair_CASE] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP next_var_rename_props o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "next_var_rename"
     with Failure _ -> false))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na''':num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `is_alloc_var na_3_p` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`stack_mov:(A)wl_prog`; `ssa'':num spt`;
      `sptree_inter ssa'' (sptree_union (FST (numset:num_set#num_set)) (SND numset)):num spt`; `na'':num`;
      `MAP FST (toAList (sptree_union (FST (numset:num_set#num_set)) (SND numset)))`;
      `ret_mov:(A)wl_prog`; `na''':num`; `ret':num list`; `ssa_2_p:num spt`; `na_2_p:num`;
      `ren_ret_handler:(A)wl_prog`; `ssa_2:num spt`; `k1:num`; `k2:num`; `n0:num`;
      `ssa''':num spt`; `na_2:num`; `n':num`; `hp:(A)wl_prog`; `ssa_3_p:num spt`;
      `na_3_p:num`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 21)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`ren_exc_handler:(A)wl_prog`; `ssa_3:num spt`; `na_3:num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP fix_inconsistencies_props) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na_2:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;;

let WALLOCPAUX_loop_setup_props = prove
 (`!(names:1 spt) (exit_names:1 spt) (ssa:num spt) na (setup_prog:(A)wl_prog)
    ssa_refreshed na_refreshed.
     loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) /\
     ssa_map_ok na ssa /\ is_alloc_var na
     ==> is_alloc_var na_refreshed /\ ssa_map_ok na_refreshed ssa_refreshed /\
         na <= na_refreshed`,
  REPEAT GEN_TAC THEN REWRITE_TAC[loop_setup_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && is_var(rhs(concl th))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_props o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename"
     with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_move_props o check (fun th ->
    is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename_move"
     with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WALLOCPAUX_PROPS_LOOP_TAC : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] WALLOCPAUX_loop_setup_props) o
    check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "loop_setup" with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sptree_inter (ssa_refreshed:num spt) (names:1 spt)`; `body':(A)wl_prog`;
                                `ssa'':num spt`; `na'':num`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC ssa_map_ok_inter THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_ARITH_TAC THEN
  MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
  EXISTS_TAC `na_refreshed:num` THEN ASM_REWRITE_TAC[];;

(* HOL4 line 5951 *)
let ssa_cc_trans_props = prove
 (`!(prog:(A)wl_prog) (ssa:num spt) na lt (prog':(A)wl_prog) ssa' na'.
     ssa_cc_trans prog ssa na lt = (prog',ssa',na')
     ==> ssa_map_ok na ssa /\ is_alloc_var na
     ==> na <= na' /\ is_alloc_var na' /\ ssa_map_ok na' ssa'`,
  MATCH_MP_TAC ssa_cc_trans_ind THEN REPEAT CONJ_TAC THENL
   [(* Skip *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* Move *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
      MP_TAC(ISPECL [`MAP FST (ls:(num#num)list)`; `ssa:num spt`; `na:num`; `ren_ls1:num list`;
                     `ssa'':num spt`; `na'':num`] list_next_var_rename_props) THEN
      MP_TAC(ISPECL [`MAP FST (ls:(num#num)list)`; `ssa:num spt`; `na:num`; `ren_ls1:num list`;
                     `ssa'':num spt`; `na'':num`] list_next_var_rename_lemma_1) THEN
      ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      STRIP_TAC THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC ssa_map_ok_force_rename THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EVERY_FILTER_IMP THEN
      MP_TAC(ISPECL [`MAP SND (ls:(num#num)list)`; `ren_ls1:num list`;
                     `\y:num. y < na'' /\ ~is_phy_var y`] every_zip_snd) THEN
      BETA_TAC THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_COUNT_LIST] THEN
      X_GEN_TAC `x:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_ARITH_TAC;
        SUBGOAL_THEN `is_alloc_var (4 * x + na)` MP_TAC THENL
         [UNDISCH_TAC `is_alloc_var na` THEN REWRITE_TAC[is_alloc_var_def] THEN
          ONCE_REWRITE_TAC[ARITH_RULE `4 * x + na = x * 4 + na`] THEN REWRITE_TAC[MOD_MULT_ADD];
          MESON_TAC[convention_partitions]]];
    (* StoreConsts *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Inst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Assign *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Get *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Store *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Seq *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* MustTerminate *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* If *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1]) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && not(is_forall(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`e3':(A)wl_prog`; `ssa3:num spt`; `na3:num`] o
                    check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP fix_inconsistencies_props) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na2:num` THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;
    (* Alloc *)
    WALLOCPAUX_PROPS_ALLOC_TAC;
    (* Raise *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* OpCurrHeap *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Return *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* Tick *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* Set *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* LocValue *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Install *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
      WALLOCPAUX_PROPS_LNVRM_TAC `na:num` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP next_var_rename_props o check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "next_var_rename"
         with Failure _ -> false))) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [DISJ1_TAC THEN MATCH_MP_TAC is_stack_var_flip THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_lem THEN ASM_REWRITE_TAC[]];
        STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_move_props o check (fun th ->
        is_eq(concl th) && (try rand(rator(lhs(concl th))) = `na''':num` with Failure _ -> false))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[is_stack_var_flip]; STRIP_TAC] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_ARITH_TAC THEN
      ASM_MESON_TAC[is_stack_var_flip];
    (* CodeBufferWrite *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* DataBufferWrite *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* FFI *)
    WALLOCPAUX_PROPS_ALLOC_TAC;
    (* Call NONE *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* Call SOME *)
    WALLOCPAUX_PROPS_CALL_TAC;
    (* ShareInst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN COND_CASES_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
      TRY(ASM_REWRITE_TAC[LE_REFL] THEN NO_TAC) THEN WALLOCPAUX_PROPS_FIN_TAC;
    (* Loop *)
    WALLOCPAUX_PROPS_LOOP_TAC;
    (* Break *)
    WALLOCPAUX_PROPS_PRE_TAC THEN TOP_CASE_TAC THEN REWRITE_TAC[] THEN REPEAT PAIRARG_TAC THEN
      WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL];
    (* Continue *)
    WALLOCPAUX_PROPS_PRE_TAC THEN TOP_CASE_TAC THEN REWRITE_TAC[] THEN REPEAT PAIRARG_TAC THEN
      WALLOCPAUX_PROPS_EQ_TAC THEN ASM_REWRITE_TAC[LE_REFL]]);;

(* HOL4 line 6212 *)
let PAIR_ZIP_MEM = prove
 (`!(a:A) (b:B) c d. LENGTH c = LENGTH d /\ MEM (a,b) (ZIP c d) ==> MEM a c /\ MEM b d`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[MEM_ZIP; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6222 *)
let ALOOKUP_ZIP_MEM = prove
 (`!(a:A list) (b:B list) x y.
     LENGTH a = LENGTH b /\ ALOOKUP (ZIP a b) x = SOME y ==> MEM x a /\ MEM y b`,
  MESON_TAC[ALOOKUP_MEM; PAIR_ZIP_MEM]);;

(* HOL4 line 6232 *)
let ALOOKUP_ALL_DISTINCT_REMAP = prove
 (`!(ls:A list) (x:B list) (f:A->C) y n.
     LENGTH ls = LENGTH x /\ ALL_DISTINCT (MAP f ls) /\ n < LENGTH ls /\
     ALOOKUP (ZIP ls x) (EL n ls) = SOME y
     ==> ALOOKUP (ZIP (MAP f ls) x) (f (EL n ls)) = SOME y`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; NOT_SUC]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ; MAP; ALL_DISTINCT; ZIP; ALOOKUP_def] THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0] THENL
   [MESON_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `~((f:A->C) (EL n' t) = f h)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~MEM ((f:A->C) h) (MAP f t)` THEN
      REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `EL n' (t:A list)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(h:A = EL n' t)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((f:A->C) (EL n' t) = f h)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(h:A = EL n' t)`]) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 6256 *)
let ssa_cc_trans_exp_correct = prove
 (`!(st:(A,C,FFI)wl_state) w cst ssa na res.
     wl_word_exp st w = SOME res /\ word_state_eq_rel st cst /\
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst)
     ==> wl_word_exp cst (ssa_cc_trans_exp ssa w) = SOME res`,
  MATCH_MP_TAC wl_word_exp_ind THEN
  REWRITE_TAC[wl_word_exp_def; ssa_cc_trans_exp_def] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REWRITE_TAC[wl_get_var_def; ssa_locals_rel_def; option_lookup_def; domain_lookup] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th0 -> FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th th0))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      try fst(dest_const t) = "THE" with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[THE_DEF];
    REWRITE_TAC[wl_get_store_def; word_state_eq_rel_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; case_eq "word_loc"; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[WALLOCPAUX_mem_load_eq];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; option_DISTINCT] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `MAP (wl_word_exp (cst:(A,C,FFI)wl_state)) (MAP (ssa_cc_trans_exp ssa) wexps) =
      MAP (wl_word_exp (s:(A,C,FFI)wl_state)) (wexps:((A)wl_exp)list)`
      SUBST1_TAC THENL
     [REWRITE_TAC[MAP_MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
      REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
      X_GEN_TAC `e:(A)wl_exp` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP the_words_EVERY_IS_SOME) THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
      DISCH_THEN(MP_TAC o SPEC `wl_word_exp (s:(A,C,FFI)wl_state) e`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IS_SOME_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_TAC `r:(A)word_loc`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:(A)wl_exp`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; case_eq "word_loc"; option_DISTINCT] THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 lines 6294-6308: val exp_tac2 and val setup_tac (ML) are not needed *)

(* HOL4 line 6310 *)
let get_var_set_vars_notin = prove
 (`!v ls vs (st:(A,C,FFI)wl_state).
     ~MEM v ls /\ LENGTH ls = LENGTH vs
     ==> wl_get_var v (wl_set_vars ls vs st) = wl_get_var v st`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[wl_get_var_def; wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM;
               lookup_alist_insert] THEN
  MP_TAC(ISPEC `ALOOKUP (ZIP (ls:num list) (vs:((A)word_loc)list)) v` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[ALOOKUP_ZIP_MEM]);;

(* HOL4 line 6321 *)
let ssa_locals_rel_delete_left = prove
 (`!na (ssa:num spt) (stl:A spt) cstl n.
     ssa_locals_rel na ssa stl cstl ==> ssa_locals_rel na ssa (delete n stl) cstl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; lookup_delete] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 6331 *)
let ssa_locals_rel_delete_right = prove
 (`!na (ssa:num spt) (stl:A spt) cstl n.
     ssa_map_ok na ssa /\ ssa_locals_rel na ssa stl cstl /\ is_phy_var n
     ==> ssa_locals_rel na ssa stl (delete n cstl)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def; domain_delete; IN_DELETE; lookup_delete] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:A`] o check (fun th ->
      can (find_term (fun t -> t = `stl:A spt`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(THE (lookup x (ssa:num spt)) = n)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `x IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 6347 *)
let lookup_force_rename_aux = prove
 (CASE_TERM
  `!x ls (ssa:num spt).
     lookup x (force_rename (REVERSE ls) ssa) =
     match ALOOKUP ls x with NONE -> lookup x ssa | SOME y -> SOME y`,
  GEN_TAC THEN MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[REVERSE; force_rename_def; ALOOKUP_def; option_CASE];
    X_GEN_TAC `l:(num#num)list` THEN DISCH_TAC THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `ssa:num spt`] THEN
    ASM_REWRITE_TAC[REVERSE_SNOC; force_rename_def; ALOOKUP_SNOC; FST; SND] THEN
    MP_TAC(ISPEC `ALOOKUP (l:(num#num)list) x` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; lookup_insert] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE]]);;

(* HOL4 line 6364 *)
let lookup_force_rename = prove
 (CASE_TERM
  `!x ls (ssa:num spt).
     lookup x (force_rename ls ssa) =
     match ALOOKUP (REVERSE ls) x with NONE -> lookup x ssa | SOME y -> SOME y`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:num`; `REVERSE (ls:(num#num)list)`; `ssa:num spt`]
                lookup_force_rename_aux) THEN
  REWRITE_TAC[REVERSE_REVERSE]);;

(* HOL4 line 6373 *)
let domain_force_rename = prove
 (`!ls (ssa:num spt).
     domain (force_rename ls ssa) = domain ssa UNION set_of_list (MAP FST ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[force_rename_def; MAP; set_of_list; UNION_EMPTY] THEN
  SUBGOAL_THEN `?a b. h = (a:num,b:num)` (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[force_rename_def; domain_insert; FST] THEN SET_TAC[]);;

(* HOL4 line 6383 *)
let ssa_locals_rel_force_rename = prove
 (`!na (ssa:num spt) (st1:A spt) st2 ls.
     ssa_locals_rel na ssa st1 st2 /\
     ALL (\x. lookup (FST x) st1 = lookup (SND x) st2) ls /\
     set_of_list (MAP SND ls) SUBSET domain st2
     ==> ssa_locals_rel na (force_rename ls ssa) st1 st2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; lookup_force_rename; domain_force_rename] THEN
  REWRITE_TAC[GSYM ALL_MEM; SUBSET; IN_SET_OF_LIST; IN_UNION] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    MP_TAC(ISPEC `ALOOKUP (REVERSE (ls:(num#num)list)) x` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[option_CASE; option_INJ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN REWRITE_TAC[MEM_REVERSE] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM_MAP] THEN
    EXISTS_TAC `(x:num,z:num)` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:num`; `y:A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:A`] o check (fun th ->
      can (find_term (fun t -> t = `st1:A spt`)) (concl th) && is_forall(concl th) &&
      not (can (find_term (fun t -> t = `ls:(num#num)list`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `ALOOKUP (REVERSE (ls:(num#num)list)) x` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:num` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[option_CASE; THE_DEF] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN REWRITE_TAC[MEM_REVERSE] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(x:num,z:num)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]);;

(* helper: a map that is ALL_DISTINCT on a list is injective on its elements *)

(* HOL4 line 6405 *)
let list_next_var_rename_move_distinct = prove
 (`!(ssa:num spt) na ls (mov:(A)wl_prog) ssa' na' x y.
     list_next_var_rename_move ssa na ls = (mov,ssa',na') /\ ALL_DISTINCT ls /\
     MEM x ls /\ MEM y ls /\ option_lookup ssa' x = option_lookup ssa' y
     ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && is_var(rhs(concl th))))) THEN
  MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nl")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "some")))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1 o check (fun th ->
    is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename"
     with Failure _ -> false))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dist") (K ALL_TAC)) THEN
  SUBGOAL_THEN `!z. MEM z ls ==> option_lookup (ssa':num spt) z = THE (lookup z ssa')`
    (LABEL_TAC "ol") THENL
   [X_GEN_TAC `z:num` THEN DISCH_TAC THEN
    USE_THEN "some" (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_lookup_def; option_CASE; THE_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `\z. THE (lookup z (ssa':num spt))` LSCANPAUX_INJ_MAP) THEN
  EXISTS_TAC `ls:num list` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "nl" (SUBST1_TAC o SYM) THEN USE_THEN "dist" ACCEPT_TAC;
    BETA_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 6425 *)
let get_vars_NOT_MEM = prove
 (`!h xs (cs:(A,C,FFI)wl_state) h' ys.
     ~MEM h xs
     ==> wl_get_vars xs (wl_state_locals_fupd (K (insert h h' ys)) cs) =
         wl_get_vars xs (wl_state_locals_fupd (K ys) cs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[wl_get_vars_def; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 6432 *)
let get_vars_eq_alist_insert = prove
 (`!(st:(A,C,FFI)wl_state) rest regs l.
     ALL_DISTINCT regs /\ LENGTH regs = LENGTH l /\
     (!x. MEM x regs
          ==> lookup x (wl_state_locals st) = lookup x (alist_insert regs l rest))
     ==> wl_get_vars regs st = SOME l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; wl_get_vars_def] THEN MESON_TAC[LENGTH_EQ_NIL];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[ALL_DISTINCT; MEM; alist_insert_def; wl_get_vars_def; wl_get_var_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lookup h (wl_state_locals (st:(A,C,FFI)wl_state)) = SOME h'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[lookup_insert]; ALL_TAC] THEN
  REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN `wl_get_vars t (st:(A,C,FFI)wl_state) = SOME t'` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[lookup_insert] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[option_CASE]]);;

(* HOL4 line 6451 *)
let cut_envs_domain_SUBSET = prove
 (`!(x1:num_set) (x2:num_set) (locs:A spt) x.
     cut_envs (x1,x2) locs = SOME x
     ==> domain x1 SUBSET domain locs /\ domain x2 SUBSET domain locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE; option_DISTINCT]);;

(* HOL4 line 6459 *)
let ssa_reconcile_distinct_lemma = prove
 (CASE_TERM
  `!(f:num->B) (g:num->B) (ns:A spt).
     INJ f (domain ns) UNIV
     ==> ALL_DISTINCT (MAP FST
           (FILTER (\ab. match ab with (a,b) -> ~(a = b))
              (MAP (\v. (f v,g v)) (MAP FST (toAList ns)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM
   `!L. MAP FST (FILTER (\ab. match ab with (a,b) -> ~(a = b)) (MAP (\v. (f v,g v)) L)) =
        MAP (f:num->B) (FILTER (\v. ~(f v = (g:num->B) v)) L)`)
    (fun th -> REWRITE_TAC[th]) THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FILTER; pair_CASE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; FST];
    ALL_TAC] THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[MEM_FILTER; MEM_MAP; EXISTS_PAIR_THM; MEM_toAList] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[INJ; IN_UNIV]) THEN
    ASM_REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC FILTER_ALL_DISTINCT THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]]);;

(* HOL4 line 6485 *)
let ssa_reconcile_moves_eq = prove
 (CASE_TERM
  `!(m:B spt) (f:num->B) L.
     FILTER (\ab. match ab with (a,b) -> ~(a = b))
       (FLAT (MAP (\v. match lookup v m with NONE -> [] | SOME cv -> [(f v,cv)]) L)) =
     MAP (\v. (f v,THE (lookup v m)))
       (FILTER (\v. match lookup v m with NONE -> F | SOME cv -> ~(f v = cv)) L)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FLAT; FILTER] THEN
  MP_TAC(ISPEC `lookup h (m:B spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `cv:B` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; APPEND; FILTER; pair_CASE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; THE_DEF]);;

(* HOL4 line 6500 *)
let ssa_reconcile_filtered_all_distinct = prove
 (CASE_TERM
  `!(cur_ssa:num spt) (tgt_ssa:num spt) (ns:A spt).
     ALL_DISTINCT (FILTER (\v. match lookup v cur_ssa with
                                 NONE -> F
                               | SOME cv -> ~(option_lookup tgt_ssa v = cv))
                     (MAP FST (toAList ns)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FILTER_ALL_DISTINCT THEN
  REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]);;

(* HOL4 line 6510 *)
let ssa_reconcile_filtered_in_dom = prove
 (CASE_TERM
  `!(cur_ssa:num spt) (tgt_ssa:num spt) (ns:A spt) v.
     MEM v (FILTER (\v. match lookup v cur_ssa with
                          NONE -> F
                        | SOME cv -> ~(option_lookup tgt_ssa v = cv))
              (MAP FST (toAList ns)))
     ==> v IN domain ns /\
         ?cv. lookup v cur_ssa = SOME cv /\ ~(option_lookup tgt_ssa v = cv) /\
              THE (lookup v cur_ssa) = cv`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM_FILTER; MEM_MAP; EXISTS_PAIR_THM; MEM_toAList] THEN
  MP_TAC(ISPEC `lookup v (cur_ssa:num spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `cv:num` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE; option_INJ; THE_DEF] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]);;

(* HOL4 line 6524; the HOL4 variable val is vv here (val is a constant)    *)
let ssa_reconcile_get_vars_lemma = prove
 (`!ls (cur_ssa:num spt) (cst:(A,C,FFI)wl_state).
     ALL_DISTINCT ls /\
     (!v. MEM v ls ==> ?vv. lookup (THE (lookup v cur_ssa)) (wl_state_locals cst) = SOME vv)
     ==> ?vs. wl_get_vars (MAP (\v. THE (lookup v cur_ssa)) ls) cst = SOME vs /\
              LENGTH vs = LENGTH ls /\
              !i. i < LENGTH ls
                  ==> lookup (THE (lookup (EL i ls) cur_ssa)) (wl_state_locals cst) =
                      SOME (EL i vs)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; wl_get_vars_def; option_INJ; LENGTH; LT] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `[]:((A)word_loc)list` THEN REWRITE_TAC[LENGTH];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_DISTINCT; MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cur_ssa:num spt`; `cst:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:((A)word_loc)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:num` o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "MEM" with Failure _ -> false)) (concl th))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `vv:(A)word_loc`) THEN
  EXISTS_TAC `CONS (vv:(A)word_loc) vs` THEN
  ASM_REWRITE_TAC[MAP; wl_get_vars_def; wl_get_var_def; option_CASE; LENGTH] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THEN ASM_MESON_TAC[]);;

(* HOL4 line 6550 *)
let alookup_zip_map_some = prove
 (`!ls (vs:B list) i (f:A->C).
     ALL_DISTINCT (MAP f ls) /\ i < LENGTH ls /\ LENGTH vs = LENGTH ls
     ==> ALOOKUP (ZIP (MAP f ls) vs) (f (EL i ls)) = SOME (EL i vs)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
  SUBGOAL_THEN `LENGTH (MAP (f:A->C) ls) = LENGTH (vs:B list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[MAP_ZIP; MEM_ZIP] THEN EXISTS_TAC `i:num` THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_MAP]);;

(* HOL4 line 6567 *)
let alookup_zip_map_option_lookup_none = prove
 (`!ls (vs:B list) n (ns:A spt) (f:num->C).
     INJ f (domain ns) UNIV /\ n IN domain ns /\ ~MEM n ls /\
     (!v. MEM v ls ==> v IN domain ns) /\ LENGTH vs = LENGTH ls
     ==> ALOOKUP (ZIP (MAP f ls) vs) (f n) = NONE`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `ALOOKUP (ZIP (MAP (f:num->C) ls) (vs:B list)) (f n)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (X_CHOOSE_THEN `y:B` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:num->C) n`; `y:B`; `MAP (f:num->C) ls`; `vs:B list`] PAIR_ZIP_MEM) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; MEM_MAP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) (K ALL_TAC)) THEN
  SUBGOAL_THEN `n:num = v` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[INJ; IN_UNIV]) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 6593 *)
let evaluate_ssa_reconcile = prove
 (`!na (cur_ssa:num spt) (st_locs:((A)word_loc)spt) (cst:(A,C,FFI)wl_state) tgt_ssa
    (ns:B spt).
     ssa_locals_rel na cur_ssa st_locs (wl_state_locals cst) /\
     INJ (option_lookup tgt_ssa) (domain ns) UNIV
     ==> ?cst'. wl_evaluate (ssa_reconcile cur_ssa tgt_ssa ns:(A)wl_prog,cst) = (NONE,cst') /\
                word_state_eq_rel cst cst' /\
                strong_locals_rel (option_lookup tgt_ssa) (domain ns) st_locs
                  (wl_state_locals cst')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ssa_reconcile_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ssa_reconcile_moves_eq; MAP_EQ_NIL] THEN
  (fun (asl,w as g) ->
     let fl = find_term (fun t -> is_comb t &&
       (try fst(dest_const(fst(strip_comb t))) = "FILTER" with Failure _ -> false)) w in
     ABBREV_TAC (mk_eq(`vfl:num list`, fl)) g) THEN
  SUBGOAL_THEN `!n. MEM n vfl <=> n IN domain (ns:B spt) /\
                    ?cv. lookup n (cur_ssa:num spt) = SOME cv /\ ~(option_lookup tgt_ssa n = cv)`
    (LABEL_TAC "memfv") THENL
   [EXPAND_TAC "vfl" THEN REWRITE_TAC[MEM_FILTER; MEM_MAP; EXISTS_PAIR_THM; MEM_toAList;
                                     domain_lookup; RIGHT_AND_EXISTS_THM] THEN
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `lookup n (cur_ssa:num spt)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `c:num` SUBST1_TAC)) THEN
    REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (vfl:num list)` (LABEL_TAC "dfv") THENL
   [EXPAND_TAC "vfl" THEN REWRITE_TAC[ssa_reconcile_filtered_all_distinct]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP (option_lookup (tgt_ssa:num spt)) vfl)` (LABEL_TAC "dmfv") THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[INJ; IN_UNIV] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "INJ" with Failure _ -> false)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n v. n IN domain (ns:B spt) /\ lookup n st_locs = SOME (v:(A)word_loc)
                      ==> ?cv. lookup n (cur_ssa:num spt) = SOME cv /\
                               lookup cv (wl_state_locals (cst:(A,C,FFI)wl_state)) = SOME v`
    (LABEL_TAC "rel") THENL
   [UNDISCH_TAC `ssa_locals_rel na (cur_ssa:num spt) st_locs
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def; domain_lookup] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `cv0:num`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `cv0:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      try fst(dest_const t) = "THE" with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[THE_DEF];
    ALL_TAC] THEN
  ASM_CASES_TAC `vfl:num list = []` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `cst:(A,C,FFI)wl_state` THEN
    REWRITE_TAC[wl_evaluate_def; WALLOCPAUX_wser_refl; strong_locals_rel_def] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN STRIP_TAC THEN
    USE_THEN "rel" (MP_TAC o SPECL [`n:num`; `v:(A)word_loc`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cv:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `option_lookup tgt_ssa n = cv` (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "memfv" (MP_TAC o SPEC `n:num`) THEN
    UNDISCH_TAC `vfl:num list = []` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[wl_evaluate_def] THEN
  SUBGOAL_THEN
   `MAP FST (MAP (\v. option_lookup tgt_ssa v,THE (lookup v (cur_ssa:num spt))) vfl) =
    MAP (option_lookup tgt_ssa) vfl /\
    MAP SND (MAP (\v. option_lookup tgt_ssa v,THE (lookup v (cur_ssa:num spt))) vfl) =
    MAP (\v. THE (lookup v cur_ssa)) vfl` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[MAP_MAP_o; o_DEF; FST; SND; ETA_AX]; ALL_TAC] THEN
  USE_THEN "dmfv" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`vfl:num list`; `cur_ssa:num spt`; `cst:(A,C,FFI)wl_state`]
                ssa_reconcile_get_vars_lemma) THEN
  ANTS_TAC THENL
   [USE_THEN "dfv" (fun th -> REWRITE_TAC[th]) THEN X_GEN_TAC `v:num` THEN
    USE_THEN "memfv" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
    UNDISCH_TAC `ssa_locals_rel na (cur_ssa:num spt) st_locs
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def; domain_lookup] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:((A)word_loc)list` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[option_CASE] THEN
  EXISTS_TAC `wl_set_vars (MAP (option_lookup tgt_ssa) vfl) vs (cst:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[word_state_eq_rel_def; wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  REWRITE_TAC[strong_locals_rel_def; wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN STRIP_TAC THEN
  USE_THEN "rel" (MP_TAC o SPECL [`n:num`; `v:(A)word_loc`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cv:num` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[lookup_alist_insert; LENGTH_MAP] THEN
  ASM_CASES_TAC `option_lookup tgt_ssa n = (cv:num)` THENL
   [SUBGOAL_THEN `~MEM n (vfl:num list)` ASSUME_TAC THENL
     [USE_THEN "memfv" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
    MP_TAC(ISPECL [`vfl:num list`; `vs:((A)word_loc)list`; `n:num`; `ns:B spt`;
                   `option_lookup (tgt_ssa:num spt)`] alookup_zip_map_option_lookup_none) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      USE_THEN "memfv" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[option_CASE]];
    SUBGOAL_THEN `MEM n (vfl:num list)` MP_TAC THENL
     [USE_THEN "memfv" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n = EL i (vfl:num list)`)) THEN
    MP_TAC(ISPECL [`vfl:num list`; `vs:((A)word_loc)list`; `i:num`;
                   `option_lookup (tgt_ssa:num spt)`] alookup_zip_map_some) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `vs:((A)word_loc)list`)) (concl th))) THEN
    ASM_REWRITE_TAC[THE_DEF] THEN REWRITE_TAC[option_INJ] THEN MESON_TAC[]]);;

(* HOL4 line 6708 *)
let lt_ok_def = cake_def
  `lt_ok (lt:(num spt#A spt#B spt)list) <=>
     ALL (\x. match x with
                (tgt_ssa,names,exit_names) ->
                  INJ (option_lookup tgt_ssa) (domain names) UNIV /\
                  INJ (option_lookup tgt_ssa) (domain exit_names) UNIV) lt`;;

(* HOL4 line 6715 *)
let foldr_insert_const_swap = prove
 (`!rs h (v:(A)word_loc) m.
     ITLIST (\r loc. insert r v loc) rs (insert h v m) =
     insert h v (ITLIST (\r loc. insert r v loc) rs m)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `h:num = h'` THEN ASM_SIMP_TAC[insert_swap]);;

(* HOL4 line 6727 *)
let evaluate_fake_const_chain = prove
 (`!rs (cst:(A,C,FFI)wl_state).
     wl_evaluate (ITLIST wl_Seq (MAP (\r. fake_move r:(A)wl_prog) rs) wl_Skip,cst) =
     (NONE,wl_state_locals_fupd
             (K (ITLIST (\r loc. insert r (wl_Word (word 0)) loc) rs (wl_state_locals cst)))
             cst)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MAP] THENL
   [REWRITE_TAC[wl_evaluate_def; word_allocProof_with_same_locals]; ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC(ISPECL [`fake_move h:(A)wl_prog`;
                 `ITLIST wl_Seq (MAP (\r. fake_move r:(A)wl_prog) t) wl_Skip`;
                 `cst:(A,C,FFI)wl_state`; `wl_set_var h (wl_Word (word 0)) (cst:(A,C,FFI)wl_state)`]
                IL2AUX_evaluate_Seq_NONE) THEN
  REWRITE_TAC[WALLOCPAUX_evaluate_fake_move] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
                  K_THM; K_o_THM; foldr_insert_const_swap]);;

(* HOL4 line 6743 *)
let evaluate_fake_const_chain_locals = prove
 (`!rs (cst:(A,C,FFI)wl_state).
     let rcst = SND (wl_evaluate (ITLIST wl_Seq (MAP (\r. fake_move r:(A)wl_prog) rs) wl_Skip,
                                  cst)) in
     word_state_eq_rel cst rcst /\
     domain (wl_state_locals rcst) = domain (wl_state_locals cst) UNION set_of_list rs /\
     (!r. ~MEM r rs ==> lookup r (wl_state_locals rcst) = lookup r (wl_state_locals cst)) /\
     (!r. MEM r rs ==> lookup r (wl_state_locals rcst) = SOME (wl_Word (word 0)))`,
  REWRITE_TAC[evaluate_fake_const_chain; LET_DEF; LET_END_DEF; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ITLIST; MEM; set_of_list; UNION_EMPTY; word_allocProof_with_same_locals;
                WALLOCPAUX_wser_refl];
    ALL_TAC] THEN
  GEN_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `cst:(A,C,FFI)wl_state`) THEN
  REWRITE_TAC[ITLIST; MEM; set_of_list; domain_insert; lookup_insert] THEN
  REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* helper: word_state_eq_rel is transitive *)

(* HOL4 line 6766 *)
let loop_setup_correct = prove
 (`!(st:(A,C,FFI)wl_state) cst ssa na (names:1 spt) (exit_names:1 spt) (setup_prog:(A)wl_prog)
    ssa_refreshed na_refreshed.
     word_state_eq_rel st cst /\
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     ssa_map_ok na ssa /\ is_alloc_var na /\
     loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed)
     ==> ?rcst.
           wl_evaluate (setup_prog,cst) = (NONE,rcst) /\
           word_state_eq_rel st rcst /\
           ssa_locals_rel na_refreshed ssa_refreshed (wl_state_locals st) (wl_state_locals rcst) /\
           na <= na_refreshed /\ is_alloc_var na_refreshed /\
           ssa_map_ok na_refreshed ssa_refreshed /\
           domain ssa_refreshed = domain ssa UNION domain (sptree_union names exit_names) /\
           INJ (option_lookup ssa_refreshed) (domain names) UNIV /\
           INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV /\
           (!v. v IN domain ssa_refreshed
                ==> option_lookup ssa_refreshed v IN domain (wl_state_locals rcst))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[loop_setup_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `ex = FILTER (\v. lookup v (ssa:num spt) = NONE)
                     (MAP FST (toAList (sptree_union (names:1 spt) exit_names)))` THEN
  ABBREV_TAC `rf = FILTER (\v. IS_SOME (lookup v (ssa:num spt)))
                     (MAP FST (toAList (sptree_union (names:1 spt) exit_names)))` THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && is_var(rhs(concl th))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `setup_prog:(A)wl_prog`)) THEN
  SUBGOAL_THEN `ALL_DISTINCT (ex:num list) /\ ALL_DISTINCT (rf:num list)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ex"; "rf"] THEN CONJ_TAC THEN MATCH_MP_TAC FILTER_ALL_DISTINCT THEN
    REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!v. MEM v ex <=> v IN domain (sptree_union (names:1 spt) exit_names) /\
                                lookup v (ssa:num spt) = NONE) /\
                (!v. MEM v rf <=> v IN domain (sptree_union (names:1 spt) exit_names) /\
                                v IN domain (ssa:num spt))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ex"; "rf"] THEN
    REWRITE_TAC[MEM_FILTER; MEM_MAP; EXISTS_PAIR_THM; MEM_toAList; domain_lookup] THEN
    CONJ_TAC THEN X_GEN_TAC `v:num` THEN
    MP_TAC(ISPEC `lookup v (ssa:num spt)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `c:num` SUBST1_TAC)) THEN
    REWRITE_TAC[IS_SOME_DEF; option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_props o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename"
     with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1 o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename"
     with Failure _ -> false))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`ex:num list`; `ssa:num spt`; `na:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`fresh_pos_ls:num list`; `cst:(A,C,FFI)wl_state`]
                evaluate_fake_const_chain_locals) THEN
  REWRITE_TAC[evaluate_fake_const_chain; LET_DEF; LET_END_DEF; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `fcst = wl_state_locals_fupd
                (K (ITLIST (\r loc. insert r (wl_Word (word 0)) loc) fresh_pos_ls
                     (wl_state_locals cst))) (cst:(A,C,FFI)wl_state)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`ITLIST wl_Seq (MAP (\r. fake_move r:(A)wl_prog) fresh_pos_ls) wl_Skip`;
                 `refresh_mov:(A)wl_prog`; `cst:(A,C,FFI)wl_state`; `fcst:(A,C,FFI)wl_state`]
                IL2AUX_evaluate_Seq_NONE) THEN
  ASM_REWRITE_TAC[evaluate_fake_const_chain] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `ssa_locals_rel na_ext ssa_ext (wl_state_locals (st:(A,C,FFI)wl_state))
                  (wl_state_locals (fcst:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [UNDISCH_TAC `ssa_locals_rel na (ssa:num spt) (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[IN_UNION; IN_SET_OF_LIST] THEN
      ASM_CASES_TAC `MEM x (ex:num list)` THENL
       [DISJ2_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `MAP (\x. THE (lookup x (ssa_ext:num spt))) ex = fresh_pos_ls`)) THEN
        REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[THE_DEF];
        DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:num` THEN
        FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
            can (find_term (fun t -> t = `ssa_ext:num spt`)) (concl th) &&
            not (can (find_term (fun t -> try fst(dest_const t) = "?" with Failure _ -> false)) (concl th))
          then MP_TAC(SPEC `x:num` th) else NO_TAC) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC];
      MAP_EVERY X_GEN_TAC [`x:num`; `y:(A)word_loc`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:(A)word_loc`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `wl_state_locals (st:(A,C,FFI)wl_state)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `x IN domain (ssa:num spt)` THEN REWRITE_TAC[domain_lookup] THEN
      DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
      SUBGOAL_THEN `lookup x (ssa_ext:num spt) = SOME z` ASSUME_TAC THENL
       [ASM_MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
      SUBGOAL_THEN `z < na` ASSUME_TAC THENL [ASM_MESON_TAC[ssa_map_ok_def]; ALL_TAC] THEN
      SUBGOAL_THEN `~MEM z (fresh_pos_ls:num list)` ASSUME_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `MAP (\x. 4 * x + na) (COUNT_LIST (LENGTH (ex:num list))) = fresh_pos_ls`)) THEN
        REWRITE_TAC[MEM_MAP] THEN STRIP_TAC THEN UNDISCH_TAC `z < na` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_UNION; domain_lookup] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[THE_DEF] THEN ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `lookup (THE (lookup x (ssa:num spt)))
                       (wl_state_locals (cst:(A,C,FFI)wl_state)) = SOME y` THEN
        ASM_REWRITE_TAC[THE_DEF];
        ASM_MESON_TAC[LTE_TRANS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `set_of_list rf SUBSET domain (ssa_ext:num spt)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_UNION] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `ssa_ext:num spt`; `na_ext:num`; `rf:num list`;
                 `fcst:(A,C,FFI)wl_state`] list_next_var_rename_move_preserve_weak) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WALLOCPAUX_word_state_eq_rel_trans THEN
    EXISTS_TAC `cst:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (refresh_mov:(A)wl_prog,fcst:(A,C,FFI)wl_state)`
    [`res0:((A)wl_result)option`; `rcst:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  EXISTS_TAC `rcst:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_move_props o check (fun th ->
    is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename_move"
     with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename_move"
     with Failure _ -> false))) THEN
  REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename rf (ssa_ext:num spt) na_ext`
    [`nls:num list`; `s2:num spt`; `n2:num`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s2:num spt = ssa_refreshed`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `n2:num = na_refreshed`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1 o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `list_next_var_rename rf (ssa_ext:num spt) na_ext`)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`rf:num list`; `ssa_ext:num spt`; `na_ext:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `set_of_list ex UNION set_of_list rf = domain (sptree_union (names:1 spt) exit_names)`
    ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[domain_lookup] THEN
    X_GEN_TAC `v:num` THEN MP_TAC(ISPEC `lookup v (ssa:num spt)` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. MEM x ex ==> ~MEM x (rf:num list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  SUBGOAL_THEN `MAP (option_lookup (ssa_refreshed:num spt)) ex = fresh_pos_ls /\
                MAP (option_lookup (ssa_refreshed:num spt)) rf = nls` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `MAP (\x. THE (lookup x (ssa_ext:num spt))) ex = fresh_pos_ls`));
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `MAP (\x. THE (lookup x (ssa_refreshed:num spt))) rf = nls`))] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `x:num` THEN
    DISCH_TAC THEN REWRITE_TAC[option_lookup_def] THENL
     [SUBGOAL_THEN `lookup x (ssa_refreshed:num spt) = lookup x ssa_ext` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          (let b = snd(dest_forall(concl th)) in
           is_imp b && is_eq(rand b) && free_in `ssa_ext:num spt` (rand b) &&
           free_in `ssa_refreshed:num spt` (rand b)))) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?y. lookup x (ssa_ext:num spt) = SOME y` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[option_CASE; THE_DEF]];
      SUBGOAL_THEN `?y. lookup x (ssa_refreshed:num spt) = SOME y` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[option_CASE; THE_DEF]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. MEM e fresh_pos_ls ==> ~MEM e (nls:num list)` ASSUME_TAC THENL
   [X_GEN_TAC `e:num` THEN
    FIRST_ASSUM(fun th -> if concl th =
        `MAP (\x. 4 * x + na) (COUNT_LIST (LENGTH (ex:num list))) = fresh_pos_ls`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if concl th =
        `MAP (\x. 4 * x + na_ext) (COUNT_LIST (LENGTH (rf:num list))) = nls`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[MEM_MAP; MEM_COUNT_LIST] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `j:num` THEN
    UNDISCH_TAC `na + 4 * LENGTH (ex:num list) = na_ext` THEN
    UNDISCH_TAC `x < LENGTH (ex:num list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `INJ (option_lookup (ssa_refreshed:num spt))
                  (domain (sptree_union (names:1 spt) exit_names)) (:num)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `set_of_list ex UNION set_of_list rf = domain (sptree_union (names:1 spt) exit_names)`)) THEN
    REWRITE_TAC[INJ; IN_UNIV; IN_UNION; IN_SET_OF_LIST] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `option_lookup (ssa_refreshed:num spt)` LSCANPAUX_INJ_MAP) THEN
    EXISTS_TAC `APPEND ex rf:num list` THEN
    ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND; ALL_DISTINCT_APPEND];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `na_ext:num` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `set_of_list ex UNION set_of_list rf = domain (sptree_union (names:1 spt) exit_names)`)) THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `domain (ssa_refreshed:num spt)`
                          then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[UNION_ASSOC];
    MATCH_MP_TAC word_allocProof_INJ_less THEN
    EXISTS_TAC `domain (sptree_union (names:1 spt) exit_names)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[domain_union] THEN SET_TAC[]];
    MATCH_MP_TAC word_allocProof_INJ_less THEN
    EXISTS_TAC `domain (sptree_union (names:1 spt) exit_names)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[domain_union] THEN SET_TAC[]];
    X_GEN_TAC `v:num` THEN DISCH_THEN(MP_TAC o REWRITE_RULE[domain_lookup]) THEN
    DISCH_THEN(X_CHOOSE_TAC `w:num`) THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
    UNDISCH_TAC `ssa_locals_rel na_refreshed ssa_refreshed (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (rcst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 7018 *)
let evaluate_seq_collapse = prove
 (`!(P:(A)wl_prog) Q (s:(A,C,FFI)wl_state) t.
     wl_evaluate (P,s) = (NONE,t) ==> wl_evaluate (wl_Seq P Q,s) = wl_evaluate (Q,t)`,
  REWRITE_TAC[IL2AUX_evaluate_Seq_NONE]);;

(* HOL4 line 7026 *)
let cut_env_fromAList_LN = prove
 (`!(a:1 spt) (g:num#1->num#1) (v:A spt).
     wl_cut_env (a,fromAList (MAP g (toAList (LN:1 spt)))) v = wl_cut_env (a,LN) v`,
  REWRITE_TAC[toAList_def; foldi_def; MAP; fromAList_def]);;

(* helpers for ssa_cc_trans_Loop_helper (local to this file) *)

let WALLOCPAUX_ssa_locals_rel_cut = prove
 (`!(ssa:num spt) (ns:1 spt) (env:A spt) y na.
     domain env = domain ns /\ domain ns SUBSET domain ssa /\
     strong_locals_rel (option_lookup ssa) (domain ns) env y /\
     domain y = IMAGE (option_lookup ssa) (domain env) /\
     ALL (\x. x < na) (MAP FST (toAList ns))
     ==> ssa_locals_rel na (sptree_inter ssa ns) env y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ssa_locals_rel_def; lookup_inter_alt] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `z:num`] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[option_lookup_def; option_CASE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `v:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN domain (ns:1 spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `domain (env:A spt) = domain (ns:1 spt)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z. lookup x (ssa:num spt) = SOME z` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM domain_lookup] THEN
    UNDISCH_TAC `domain (ns:1 spt) SUBSET domain (ssa:num spt)` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[domain_inter; IN_INTER; THE_DEF] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `strong_locals_rel (option_lookup (ssa:num spt)) (domain (ns:1 spt)) (env:A spt) y` THEN
    REWRITE_TAC[strong_locals_rel_def] THEN DISCH_THEN(MP_TAC o SPECL [`x:num`; `v:A`]) THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE];
    DISCH_TAC THEN UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (ns:1 spt)))` THEN
    REWRITE_TAC[GSYM ALL_MEM; toAList_domain] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let WALLOCPAUX_lt_ok_CONS = prove
 (`!(t:num spt) (n:A spt) (e:B spt) lt.
     lt_ok (CONS (t,n,e) lt) <=>
     INJ (option_lookup t) (domain n) UNIV /\ INJ (option_lookup t) (domain e) UNIV /\
     lt_ok lt`,
  REWRITE_TAC[lt_ok_def; ALL; pair_CASE; CONJ_ASSOC]);;

let WALLOCPAUX_body_final_eval = prove
 (`!(body':(A)wl_prog) bm (s:(A,C,FFI)wl_state) r2 s2.
     wl_evaluate (body',s) = (r2,s2)
     ==> wl_evaluate ((if bm = wl_Skip then body' else wl_Seq body' bm),s) =
         (if r2 = NONE then wl_evaluate (bm,s2) else (r2,s2))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; pair_CASE]]);;

let WALLOCPAUX_SLOOP_UNFOLD_TAC : tactic =
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_cut_state_def; option_CASE; wl_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN
  ASM_REWRITE_TAC([pair_CASE; wl_cont_loop_def; wl_exit_loop_def; option_INJ; option_DISTINCT;
                   wl_STOP_def; wl_state_INFO.ri_accfupds; K_THM] @
                  WALLOCPAUX_wl_result_distinct) THEN
  BETA_TAC THEN REWRITE_TAC[pair_CASE];;

let WALLOCPAUX_wl_result_inject = (case_info_of_tyname "wl_result").ci_inject;;

let WALLOCPAUX_LH_EXIT_TAC : tactic =
  EXISTS_TAC `perm1:num->num->num` THEN
  REMOVE_THEN "tgt" (MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
  ASM_REWRITE_TAC[option_CASE; WALLOCPAUX_wl_result_CASE];;

let WALLOCPAUX_cut_env_domain = prove
 (`!(n1:1 spt) (n2:1 spt) (l:A spt) e.
     wl_cut_env (n1,n2) l = SOME e ==> domain n1 SUBSET domain l /\ domain n2 SUBSET domain l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_cut_env_def] THEN
  MP_TAC(ISPEC `cut_envs (n1:1 spt,n2:1 spt) (l:A spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `p:A spt#A spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; option_DISTINCT] THEN DISCH_TAC THEN
  MATCH_MP_TAC cut_envs_domain_SUBSET THEN EXISTS_TAC `p:A spt#A spt` THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* the cases NONE and Continue 0 of the loop helper, once the target state  *)
(* c after body_final is known: word_state_eq_rel s1 c, strong_locals_rel   *)
(* on the loop names, wl_state_clock c <= wl_state_clock cst and the        *)
(* target run (tgt) reduced to the continue branch                          *)

let WALLOCPAUX_LH_CONT_TAC (c:term) : tactic =
  let ck = mk_comb(`wl_state_clock:(A,C,FFI)wl_state->num`, c) in
  let wser_tac = FIRST_ASSUM(fun th -> if is_comb(concl th) &&
      (try fst(dest_const(fst(strip_comb(concl th)))) = "word_state_eq_rel" &&
           rand(concl th) = c && rand(rator(concl th)) = `s1:(A,C,FFI)wl_state`
       with Failure _ -> false)
    then MP_TAC(REWRITE_RULE[word_state_eq_rel_def] th) else NO_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] in
  ASM_CASES_TAC `wl_state_clock (s1:(A,C,FFI)wl_state) = 0` THENL
   [SUBGOAL_THEN (mk_eq(ck,`0`)) ASSUME_TAC THENL [wser_tac; ALL_TAC] THEN
    REMOVE_THEN "tgt" MP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
    ASM_REWRITE_TAC[option_CASE; WALLOCPAUX_wl_result_CASE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_wser_flush THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_neg(mk_eq(ck,`0`))) ASSUME_TAC THENL [wser_tac; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_cut_env (names,LN) (wl_state_locals (s1:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `env3:((A)word_loc)spt` ASSUME_TAC)) THENL
   [EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
    REWRITE_TAC[wl_dec_clock_def] THEN WALLOCPAUX_SLOOP_UNFOLD_TAC;
    ALL_TAC] THEN
  let sub t = subst [c, `cc:(A,C,FFI)wl_state`] t in
  SUBGOAL_THEN `domain (names:1 spt) SUBSET domain (wl_state_locals (s1:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP WALLOCPAUX_cut_env_domain) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (sub `!v. v IN domain (names:1 spt)
                         ==> option_lookup (ssa_refreshed:num spt) v IN
                             domain (wl_state_locals (cc:(A,C,FFI)wl_state))`)
    ASSUME_TAC THENL
   [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `v IN domain (wl_state_locals (s1:(A,C,FFI)wl_state))` MP_TAC THENL
     [UNDISCH_TAC `domain (names:1 spt) SUBSET domain (wl_state_locals (s1:(A,C,FFI)wl_state))` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[domain_lookup] THEN DISCH_THEN(X_CHOOSE_TAC `w:(A)word_loc`) THEN
    EXISTS_TAC `w:(A)word_loc` THEN
    FIRST_ASSUM(fun th -> if concl th = sub `strong_locals_rel (option_lookup (ssa_refreshed:num spt))
        (domain (names:1 spt)) (wl_state_locals (s1:(A,C,FFI)wl_state))
        (wl_state_locals (cc:(A,C,FFI)wl_state))`
      then MP_TAC(REWRITE_RULE[strong_locals_rel_def] th) else NO_TAC) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "cih" (MP_TAC o SPEC (mk_comb(`wl_dec_clock:(A,C,FFI)wl_state->(A,C,FFI)wl_state`, c))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    FIRST_ASSUM(fun th -> if is_neg(concl th) && lhs(rand(concl th)) = ck then
      MP_TAC th else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_binary "<=" (concl th) && lhand(concl th) = ck then
      MP_TAC th else NO_TAC) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`wl_dec_clock (s1:(A,C,FFI)wl_state)`; `ssa_refreshed:num spt`;
    `na_refreshed:num`; `names:1 spt`; `body:(A)wl_prog`; `exit_names:1 spt`;
    `lt:(num spt#1 spt#1 spt)list`; `body':(A)wl_prog`; `ssa':num spt`; `na':num`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[GSYM wl_dec_clock_def] THEN MATCH_MP_TAC WALLOCPAUX_wser_dec_clock THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(MP_TAC o SPECL [`res':((A)wl_result)option`; `rcst:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL
   [REMOVE_THEN "tgt" MP_TAC THEN ASM_REWRITE_TAC[wl_STOP_def]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` (LABEL_TAC "p2")) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) &&
       (try fst(dest_pair(rand(lhs(concl th)))) = `body:(A)wl_prog` with Failure _ -> false) then
      MP_TAC(ISPECL [`body:(A)wl_prog`; snd(dest_pair(rand(lhs(concl th))));
                     `perm2:num->num->num`] permute_swap_lemma)
    else NO_TAC) THEN
  ASM_REWRITE_TAC([pair_CASE; option_INJ; option_DISTINCT] @ WALLOCPAUX_wl_result_distinct) THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon; wl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm3:num->num->num`) THEN
  EXISTS_TAC `perm3:num->num->num` THEN WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
  REMOVE_THEN "p2" MP_TAC THEN
  REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN DISCH_THEN ACCEPT_TAC;;

(* HOL4 line 7039 *)
let ssa_cc_trans_Loop_helper = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) cst ssa_refreshed na_refreshed (names:1 spt) (body:(A)wl_prog)
    (exit_names:1 spt) (lt:(num spt#1 spt#1 spt)list) body' ssa' na'.
     word_state_eq_rel st cst /\
     strong_locals_rel (option_lookup ssa_refreshed) (domain names)
       (wl_state_locals st) (wl_state_locals cst) /\
     (!v. v IN domain names
          ==> option_lookup ssa_refreshed v IN domain (wl_state_locals cst)) /\
     ssa_map_ok na_refreshed ssa_refreshed /\
     is_alloc_var na_refreshed /\
     wl_every_var (\x. x < na_refreshed) body /\
     INJ (option_lookup ssa_refreshed) (domain names) UNIV /\
     INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV /\
     domain names SUBSET domain ssa_refreshed /\
     domain exit_names SUBSET domain ssa_refreshed /\
     ALL (\x. x < na_refreshed) (MAP FST (toAList names)) /\
     ALL (\x. x < na_refreshed) (MAP FST (toAList exit_names)) /\
     lt_ok lt /\
     ssa_cc_trans body (sptree_inter ssa_refreshed names) na_refreshed
       (CONS (ssa_refreshed,names,exit_names) lt) = (body',ssa',na') /\
     (!(st':(A,C,FFI)wl_state) cst' ssa'' na'' lt'.
        word_state_eq_rel st' cst' /\
        ssa_locals_rel na'' ssa'' (wl_state_locals st') (wl_state_locals cst') /\
        is_alloc_var na'' /\
        wl_every_var (\x. x < na'') body /\
        ssa_map_ok na'' ssa'' /\
        lt_ok lt'
        ==> ?perm'.
              (let (res,rst) = wl_evaluate (body,wl_state_permute_fupd (K perm') st') in
                 res = SOME wl_Error \/
                 (let (prog',ssaB,naB) = ssa_cc_trans body ssa'' na'' lt' in
                  let (res',rcst) = wl_evaluate (prog',cst') in
                    res = res' /\ word_state_eq_rel rst rcst /\
                    (match res with
                       NONE -> ssa_locals_rel naB ssaB (wl_state_locals rst) (wl_state_locals rcst)
                     | SOME (wordSem_Break n) ->
                         (match oEL n lt' with
                            NONE -> T
                          | SOME (tgt_ssa,_,exit_names) ->
                              strong_locals_rel (option_lookup tgt_ssa) (domain exit_names)
                                (wl_state_locals rst) (wl_state_locals rcst))
                     | SOME (wordSem_Continue n') ->
                         (match oEL n' lt' with
                            NONE -> T
                          | SOME (tgt_ssa,names,_) ->
                              strong_locals_rel (option_lookup tgt_ssa) (domain names)
                                (wl_state_locals rst) (wl_state_locals rcst))
                     | SOME _ -> wl_state_locals rst = wl_state_locals rcst))))
     ==> let back_moves = (ssa_reconcile ssa' ssa_refreshed names:(A)wl_prog) in
         let body_final = (if back_moves = wl_Skip then body' else wl_Seq body' back_moves) in
         let ssa_names = apply_nummap_key (option_lookup ssa_refreshed) names in
         let ssa_exit = apply_nummap_key (option_lookup ssa_refreshed) exit_names in
         !res' rcst.
           wl_evaluate (wl_Loop ssa_names body_final ssa_exit,cst) = (res',rcst)
           ==> ?perm'.
                 (\xy. match xy with
                         (res,rst) ->
                           res = SOME wl_Error \/
                           res = res' /\ word_state_eq_rel rst rcst /\
                           (match res with
                              NONE -> ssa_locals_rel na' (sptree_inter ssa_refreshed exit_names)
                                        (wl_state_locals rst) (wl_state_locals rcst)
                            | SOME (wordSem_Break n) ->
                                (match oEL n lt with
                                   NONE -> T
                                 | SOME (tgt_ssa,_,exit_names) ->
                                     strong_locals_rel (option_lookup tgt_ssa)
                                       (domain exit_names) (wl_state_locals rst)
                                       (wl_state_locals rcst))
                            | SOME (wordSem_Continue n') ->
                                (match oEL n' lt with
                                   NONE -> T
                                 | SOME (tgt_ssa,names,_) ->
                                     strong_locals_rel (option_lookup tgt_ssa)
                                       (domain names) (wl_state_locals rst)
                                       (wl_state_locals rcst))
                            | SOME _ -> wl_state_locals rst = wl_state_locals rcst))
                 (wl_evaluate (wl_Loop names body exit_names,
                               wl_state_permute_fupd (K perm') st))`,
  GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`st:(A,C,FFI)wl_state`,`st:(A,C,FFI)wl_state`) THEN
  SPEC_TAC(`cst:(A,C,FFI)wl_state`,`cst:(A,C,FFI)wl_state`) THEN
  MATCH_MP_TAC WALLOCPAUX_clock_induct THEN
  X_GEN_TAC `cst:(A,C,FFI)wl_state` THEN DISCH_THEN(LABEL_TAC "cih") THEN
  X_GEN_TAC `st:(A,C,FFI)wl_state` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM(LABEL_TAC "bih") THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`res':((A)wl_result)option`; `rcst:(A,C,FFI)wl_state`] THEN
  DISCH_THEN(LABEL_TAC "tgt") THEN
  MP_TAC(ISPEC `wl_cut_env (names,LN) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `env:((A)word_loc)spt` ASSUME_TAC)) THENL
   [EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_permute_same] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[wl_cut_state_def; option_CASE] THEN BETA_TAC THEN REWRITE_TAC[pair_CASE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`option_lookup (ssa_refreshed:num spt)`; `(names:1 spt,LN:1 spt)`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`; `env:((A)word_loc)spt`;
                 `wl_state_locals (cst:(A,C,FFI)wl_state)`] cut_env_lemma) THEN
  ASM_REWRITE_TAC[domain_def; UNION_EMPTY; FST; SND; WALLOCPAUX_apply_nummaps_key_pair;
                  WALLOCPAUX_apply_nummap_key_LN] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  USE_THEN "bih" (MP_TAC o SPECL [`wl_state_locals_fupd (K env) (st:(A,C,FFI)wl_state)`;
    `wl_state_locals_fupd (K y) (cst:(A,C,FFI)wl_state)`; `sptree_inter (ssa_refreshed:num spt) (names:1 spt)`;
    `na_refreshed:num`; `CONS (ssa_refreshed:num spt,names:1 spt,exit_names:1 spt) lt`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; WALLOCPAUX_lt_ok_CONS] THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           MATCH_MP_TAC WALLOCPAUX_wser_locals THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC;
           MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_cut THEN ASM_REWRITE_TAC[] THEN NO_TAC;
           MATCH_MP_TAC ssa_map_ok_inter THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm1:num->num->num` MP_TAC) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ssa_cc_trans" with Failure _ -> false)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE; wl_state_INFO.ri_fupdcanon] THEN
  WALLOCPAUX_NAME_EVAL_TAC `body:(A)wl_prog` [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_NAME_EVAL_TAC `body':(A)wl_prog` [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  DISCH_THEN(LABEL_TAC "rel") THEN
  REMOVE_THEN "tgt" (MP_TAC o ONCE_REWRITE_RULE[wl_evaluate_def]) THEN
  ASM_REWRITE_TAC[wl_cut_state_def; option_CASE] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_pair(rand(lhs(concl th)))) = `body':(A)wl_prog` with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP WALLOCPAUX_body_final_eval th] else NO_TAC) THEN
  DISCH_THEN(LABEL_TAC "tgt") THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THENL
   [EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_SLOOP_UNFOLD_TAC; ALL_TAC] THEN
  REMOVE_THEN "rel" MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rel"))) THEN
  WALLOCPAUX_RESULT_CASES_TAC `r1:((A)wl_result)option` THEN
  RULE_ASSUM_TAC(REWRITE_RULE([option_CASE; WALLOCPAUX_wl_result_CASE; option_INJ; option_DISTINCT;
                               pair_CASE; wl_cont_loop_def; wl_exit_loop_def] @
                              WALLOCPAUX_wl_result_distinct)) THENL
   [(* NONE *)
    (SUBGOAL_THEN `wl_state_clock (s2:(A,C,FFI)wl_state) <= wl_state_clock (cst:(A,C,FFI)wl_state)` ASSUME_TAC THENL
        [FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o check (fun th -> is_eq(concl th) &&
           (try fst(dest_pair(rand(lhs(concl th)))) = `body':(A)wl_prog` with Failure _ -> false))) THEN
         REWRITE_TAC[wl_state_INFO.ri_accfupds] THEN SIMP_TAC[];
         ALL_TAC] THEN
       MP_TAC(ISPECL [`na':num`; `ssa':num spt`; `wl_state_locals (s1:(A,C,FFI)wl_state)`;
                      `s2:(A,C,FFI)wl_state`; `ssa_refreshed:num spt`; `names:1 spt`]
                     evaluate_ssa_reconcile) THEN
       ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN `c2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
       SUBGOAL_THEN `word_state_eq_rel (s1:(A,C,FFI)wl_state) c2` ASSUME_TAC THENL
        [MATCH_MP_TAC WALLOCPAUX_word_state_eq_rel_trans THEN EXISTS_TAC `s2:(A,C,FFI)wl_state` THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       SUBGOAL_THEN `wl_state_clock (c2:(A,C,FFI)wl_state) <= wl_state_clock (cst:(A,C,FFI)wl_state)`
         ASSUME_TAC THENL
        [UNDISCH_TAC `word_state_eq_rel (s2:(A,C,FFI)wl_state) c2` THEN
         REWRITE_TAC[word_state_eq_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       REMOVE_THEN "tgt" MP_TAC THEN ASM_REWRITE_TAC[pair_CASE; wl_cont_loop_def] THEN
       DISCH_THEN(LABEL_TAC "tgt") THEN
       WALLOCPAUX_LH_CONT_TAC `c2:(A,C,FFI)wl_state`);
    (* Result *) WALLOCPAUX_LH_EXIT_TAC;
    (* Exception *) WALLOCPAUX_LH_EXIT_TAC;
    (* Break *)
    (MP_TAC(SPEC `a:num` num_CASES) THEN
       DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE(WALLOCPAUX_wl_result_inject @
         [NOT_SUC; SUC_SUB1; oEL_DEF; option_CASE; pair_CASE])) THENL
        [(MP_TAC(ISPEC `wl_cut_env (exit_names,LN) (wl_state_locals (s1:(A,C,FFI)wl_state))`
              (cases "option")) THEN
            DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `env2:((A)word_loc)spt` ASSUME_TAC)) THENL
             [EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
              ASM_REWRITE_TAC[wl_cut_state_def; option_CASE; pair_CASE];
              ALL_TAC] THEN
            MP_TAC(ISPECL [`option_lookup (ssa_refreshed:num spt)`; `(exit_names:1 spt,LN:1 spt)`;
                           `wl_state_locals (s1:(A,C,FFI)wl_state)`; `env2:((A)word_loc)spt`;
                           `wl_state_locals (s2:(A,C,FFI)wl_state)`] cut_env_lemma) THEN
            ASM_REWRITE_TAC[domain_def; UNION_EMPTY; FST; SND; WALLOCPAUX_apply_nummaps_key_pair;
                            WALLOCPAUX_apply_nummap_key_LN] THEN
            DISCH_THEN(X_CHOOSE_THEN `y2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
            REMOVE_THEN "tgt" MP_TAC THEN ASM_REWRITE_TAC[option_CASE; PAIR_EQ] THEN
            DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
            SUBGOAL_THEN `na_refreshed <= na'` ASSUME_TAC THENL
             [FIRST_ASSUM(MP_TAC o MATCH_MP ssa_cc_trans_props o check (fun th -> is_eq(concl th) &&
                (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ssa_cc_trans"
                 with Failure _ -> false))) THEN
              ANTS_TAC THENL
               [CONJ_TAC THENL [MATCH_MP_TAC ssa_map_ok_inter THEN FIRST_ASSUM ACCEPT_TAC;
                                FIRST_ASSUM ACCEPT_TAC];
                SIMP_TAC[]];
              ALL_TAC] THEN
            EXISTS_TAC `perm1:num->num->num` THEN WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
            ASM_REWRITE_TAC[wl_cut_state_def; option_CASE; pair_CASE] THEN
            REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; option_CASE; option_DISTINCT] THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC WALLOCPAUX_wser_locals THEN FIRST_ASSUM ACCEPT_TAC;
              MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_cut THEN ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `ALL (\x. x < na_refreshed) (MAP FST (toAList (exit_names:1 spt)))` THEN
              MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN BETA_TAC THEN
              UNDISCH_TAC `na_refreshed <= na'` THEN ARITH_TAC]);
         EXISTS_TAC `perm1:num->num->num` THEN
         REMOVE_THEN "tgt" (MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
         DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
         WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
         REWRITE_TAC(WALLOCPAUX_wl_result_inject @ [NOT_SUC; SUC_SUB1; pair_CASE]) THEN
         ASM_REWRITE_TAC(WALLOCPAUX_wl_result_inject @
           [option_CASE; WALLOCPAUX_wl_result_CASE; NOT_SUC; SUC_SUB1])]);
    (* Continue *)
    (MP_TAC(SPEC `a:num` num_CASES) THEN
       DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)) THEN
       RULE_ASSUM_TAC(REWRITE_RULE(WALLOCPAUX_wl_result_inject @
         [NOT_SUC; SUC_SUB1; oEL_DEF; option_CASE; pair_CASE; wl_cont_loop_def])) THENL
        [(SUBGOAL_THEN `wl_state_clock (s2:(A,C,FFI)wl_state) <= wl_state_clock (cst:(A,C,FFI)wl_state)` ASSUME_TAC THENL
             [FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o check (fun th -> is_eq(concl th) &&
                (try fst(dest_pair(rand(lhs(concl th)))) = `body':(A)wl_prog` with Failure _ -> false))) THEN
              REWRITE_TAC[wl_state_INFO.ri_accfupds] THEN SIMP_TAC[];
              ALL_TAC] THEN
            WALLOCPAUX_LH_CONT_TAC `s2:(A,C,FFI)wl_state`);
         EXISTS_TAC `perm1:num->num->num` THEN
         REMOVE_THEN "tgt" (MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
         DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
         WALLOCPAUX_SLOOP_UNFOLD_TAC THEN
         REWRITE_TAC(WALLOCPAUX_wl_result_inject @ [NOT_SUC; SUC_SUB1; pair_CASE]) THEN
         ASM_REWRITE_TAC(WALLOCPAUX_wl_result_inject @
           [option_CASE; WALLOCPAUX_wl_result_CASE; NOT_SUC; SUC_SUB1])]);
    (* TimeOut *) WALLOCPAUX_LH_EXIT_TAC;
    (* NotEnoughSpace *) WALLOCPAUX_LH_EXIT_TAC;
    (* FinalFFI *) WALLOCPAUX_LH_EXIT_TAC;
    (* Error *) FIRST_X_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))]);;

(* HOL4 line 7657 *)
let ssa_cut_inter_lemma = prove
 (`!(ssa':A spt) (x1:B spt) (x2:B spt) xx.
     domain ssa' INTER domain (sptree_union x1 x2) = domain x1 UNION domain x2
     ==> xx IN domain (sptree_union x1 x2)
     ==> xx IN domain ssa'`,
  REWRITE_TAC[domain_union] THEN SET_TAC[]);;

(* ssa_cc_trans_correct is proved by induction on the program size with one *)
(* lemma per constructor; WALLOCPAUX_sct_Q st prog is its statement for a   *)
(* fixed source state st                                                    *)

let WALLOCPAUX_sct_Q_def = new_definition (CASE_TERM
 `WALLOCPAUX_sct_Q (st:(A,C,FFI)wl_state) (prog:(A)wl_prog) <=>
   !cst ssa na lt.
     word_state_eq_rel st cst /\
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     is_alloc_var na /\
     wl_every_var (\x. x < na) prog /\
     ssa_map_ok na ssa /\
     lt_ok lt
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
           let (res',rcst) = wl_evaluate (prog',cst) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE -> ssa_locals_rel na' ssa' (wl_state_locals rst) (wl_state_locals rcst)
              | SOME (wordSem_Break n) ->
                  (match oEL n lt with
                     SOME (tgt_ssa,_,exit_names) ->
                       strong_locals_rel (option_lookup tgt_ssa) (domain exit_names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME (wordSem_Continue n) ->
                  (match oEL n lt with
                     SOME (tgt_ssa,names,_) ->
                       strong_locals_rel (option_lookup tgt_ssa) (domain names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`);;

(* opening of a case lemma: the source runs with the permutation of the     *)
(* target                                                                   *)

let WALLOCPAUX_SCT_OPEN_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[ssa_cc_trans_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE];;

let WALLOCPAUX_sct_Skip = prove
 (`(!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Skip:(A)wl_prog)
        ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
   ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Skip:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[pair_CASE; option_DISTINCT] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[pair_CASE; option_CASE; wl_state_INFO.ri_accfupds] THEN
  CONJ_TAC THENL [MATCH_MP_TAC WALLOCPAUX_wser_permute THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

(* expand word_state_eq_rel st cst into the field equations, keeping it     *)

let WALLOCPAUX_SCT_EXPAND_TAC : tactic =
  FIRST_ASSUM(fun th -> if is_comb(concl th) &&
      (try fst(dest_const(fst(strip_comb(concl th)))) = "word_state_eq_rel" with Failure _ -> false)
    then STRIP_ASSUME_TAC(REWRITE_RULE[word_state_eq_rel_def] th) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_var_exp_def; LET_DEF; LET_END_DEF]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* the closing conjuncts: equal results, related states, related locals     *)

let WALLOCPAUX_SCT_FINISH_TAC : tactic =
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[word_state_eq_rel_def] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(SIMP[] THEN MATCH_MP_TAC ssa_locals_rel_set_var THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(SIMP[] THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

(* for every wl_get_var r st = SOME v (or wl_get_vars) among the            *)
(* assumptions, add the corresponding fact of the target state              *)

let WALLOCPAUX_SCT_GETVAR_TAC : tactic =
  fun (asl,w as g) ->
    let hd th = try fst(dest_const(fst(strip_comb(concl th)))) with Failure _ -> "" in
    let lhd th = try fst(dest_const(fst(strip_comb(lhs(concl th))))) with Failure _ -> "" in
    let rel = snd(find (fun (_,th) -> hd th = "ssa_locals_rel") asl) in
    let gv = filter (fun (_,th) -> lhd th = "wl_get_var") asl
    and gvs = filter (fun (_,th) -> lhd th = "wl_get_vars") asl in
    (MAP_EVERY (fun (_,th) -> try ASSUME_TAC(MATCH_MP ssa_locals_rel_get_var (CONJ rel th))
                              with Failure _ -> ALL_TAC) gv THEN
     MAP_EVERY (fun (_,th) -> try ASSUME_TAC(MATCH_MP ssa_locals_rel_get_vars (CONJ rel th))
                              with Failure _ -> ALL_TAC) gvs) g;;

let WALLOCPAUX_sct_Assign = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Assign a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Assign a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def] THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (ssa_cc_trans_exp ssa a1) = SOME a`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_cc_trans_exp_correct THEN
    MAP_EVERY EXISTS_TAC [`st:(A,C,FFI)wl_state`; `na:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_set_var_def] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_Get = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Get a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Get a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def; wl_get_store_def] THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_get_store_def; option_CASE; pair_CASE; wl_set_var_def] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_Set = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Set a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Set a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_store_def; COND_CASE_EQ] THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (ssa_cc_trans_exp ssa a1) = SOME a`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_cc_trans_exp_correct THEN
    MAP_EVERY EXISTS_TAC [`st:(A,C,FFI)wl_state`; `na:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_set_store_def] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_Store = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Store a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Store a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; wl_mem_store_def; COND_CASE_EQ] THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (ssa_cc_trans_exp ssa a0) = SOME (wl_Word a)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_cc_trans_exp_correct THEN
    MAP_EVERY EXISTS_TAC [`st:(A,C,FFI)wl_state`; `na:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_mem_store_def; WALLOCPAUX_word_loc_CASE] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_Tick = prove
 (`(!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Tick:(A)wl_prog)
        ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
   ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Tick:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[COND_CASE_EQ; wl_flush_state_def; wl_dec_clock_def] THEN WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_flush_state_def; wl_dec_clock_def] THEN
  SIMP[WALLOCPAUX_wl_result_CASE] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_LocValue = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_LocValue a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_LocValue a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def; COND_CASE_EQ] THEN WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_set_var_def] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_CodeBufferWrite = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_CodeBufferWrite a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_CodeBufferWrite a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"] THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_DataBufferWrite = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_DataBufferWrite a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_DataBufferWrite a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"] THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_sct_OpCurrHeap = prove
 (`!a0 a1 a2.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_OpCurrHeap a0 a1 a2:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_OpCurrHeap a0 a1 a2:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; wl_set_var_def] THEN
  SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state)
                  (ssa_cc_trans_exp ssa (wl_Op a0 [wl_Var a2; Lookup CurrHeap])) = SOME a`
    (ASSUME_TAC o REWRITE_RULE[ssa_cc_trans_exp_def; MAP]) THENL
   [MATCH_MP_TAC ssa_cc_trans_exp_correct THEN
    MAP_EVERY EXISTS_TAC [`st:(A,C,FFI)wl_state`; `na:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_set_var_def] THEN
  WALLOCPAUX_SCT_FINISH_TAC);;

let WALLOCPAUX_lt_ok_oEL = prove
 (`!(lt:(num spt#A spt#B spt)list) n t a b.
     lt_ok lt /\ oEL n lt = SOME (t,a,b)
     ==> INJ (option_lookup t) (domain a) UNIV /\ INJ (option_lookup t) (domain b) UNIV`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lt_ok_def; GSYM ALL_MEM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(t:num spt,a:A spt,b:B spt)`) THEN REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `oEL n (lt:(num spt#A spt#B spt)list) = SOME (t,a,b)` THEN
  REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[]);;

let WALLOCPAUX_sct_Break = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Break a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Break a0:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC([pair_CASE; option_DISTINCT; option_INJ] @ WALLOCPAUX_wl_result_distinct) THEN
  MP_TAC(ISPEC `oEL a0 (lt:(num spt#1 spt#1 spt)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `p:num spt#1 spt#1 spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    MATCH_MP_TAC WALLOCPAUX_wser_permute THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `p:num spt#1 spt#1 spt` [`t0:num spt`; `nm:1 spt`; `en:1 spt`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pair_CASE]) THEN REWRITE_TAC[pair_CASE] THEN
  SUBGOAL_THEN `INJ (option_lookup (t0:num spt)) (domain (en:1 spt)) UNIV` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt:(num spt#1 spt#1 spt)list`; `a0:num`; `t0:num spt`; `nm:1 spt`;
                   `en:1 spt`] WALLOCPAUX_lt_ok_oEL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`na:num`; `ssa:num spt`; `wl_state_locals (st:(A,C,FFI)wl_state)`;
                 `cst:(A,C,FFI)wl_state`; `t0:num spt`; `en:1 spt`] evaluate_ssa_reconcile) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `wl_evaluate ((ssa_reconcile (ssa:num spt) t0 (en:1 spt)):(A)wl_prog,cst:(A,C,FFI)wl_state) = NONE,c2` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE; wl_state_INFO.ri_accfupds] THEN
    MATCH_MP_TAC WALLOCPAUX_wser_permute THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(ssa_reconcile (ssa:num spt) t0 (en:1 spt)):(A)wl_prog`; `wl_Break a0:(A)wl_prog`;
                 `cst:(A,C,FFI)wl_state`; `c2:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE; wl_state_INFO.ri_accfupds] THEN
  MATCH_MP_TAC WALLOCPAUX_wser_permute THEN
  MATCH_MP_TAC WALLOCPAUX_word_state_eq_rel_trans THEN EXISTS_TAC `cst:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_sct_Continue = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Continue a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Continue a0:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC([pair_CASE; option_DISTINCT; option_INJ] @ WALLOCPAUX_wl_result_distinct) THEN
  MP_TAC(ISPEC `oEL a0 (lt:(num spt#1 spt#1 spt)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `p:num spt#1 spt#1 spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    MATCH_MP_TAC WALLOCPAUX_wser_permute THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `p:num spt#1 spt#1 spt` [`t0:num spt`; `nm:1 spt`; `en:1 spt`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pair_CASE]) THEN REWRITE_TAC[pair_CASE] THEN
  SUBGOAL_THEN `INJ (option_lookup (t0:num spt)) (domain (nm:1 spt)) UNIV` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt:(num spt#1 spt#1 spt)list`; `a0:num`; `t0:num spt`; `nm:1 spt`;
                   `en:1 spt`] WALLOCPAUX_lt_ok_oEL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`na:num`; `ssa:num spt`; `wl_state_locals (st:(A,C,FFI)wl_state)`;
                 `cst:(A,C,FFI)wl_state`; `t0:num spt`; `nm:1 spt`] evaluate_ssa_reconcile) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `wl_evaluate ((ssa_reconcile (ssa:num spt) t0 (nm:1 spt)):(A)wl_prog,cst:(A,C,FFI)wl_state) = NONE,c2` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE; wl_state_INFO.ri_accfupds] THEN
    MATCH_MP_TAC WALLOCPAUX_wser_permute THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(ssa_reconcile (ssa:num spt) t0 (nm:1 spt)):(A)wl_prog`; `wl_Continue a0:(A)wl_prog`;
                 `cst:(A,C,FFI)wl_state`; `c2:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE; wl_state_INFO.ri_accfupds] THEN
  MATCH_MP_TAC WALLOCPAUX_wser_permute THEN
  MATCH_MP_TAC WALLOCPAUX_word_state_eq_rel_trans THEN EXISTS_TAC `cst:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_sct_MustTerminate = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (MustTerminate a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (MustTerminate a0:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a0:(A)wl_prog`) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
    `wl_state_clock_fupd (K (MustTerminate_limit (:A)))
       (wl_state_termdep_fupd (K (wl_state_termdep st - 1)) (st:(A,C,FFI)wl_state))`) THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`wl_state_clock_fupd (K (MustTerminate_limit (:A)))
       (wl_state_termdep_fupd (K (wl_state_termdep (st:(A,C,FFI)wl_state) - 1))
          (cst:(A,C,FFI)wl_state))`;
     `ssa:num spt`; `na:num`; `lt:(num spt#1 spt#1 spt)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` (fun th ->
    EXISTS_TAC `perm:num->num->num` THEN MP_TAC th)) THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (a0:(A)wl_prog) ssa na lt`
    [`p1:(A)wl_prog`; `sa1:num spt`; `n1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdcanon] THEN
  WALLOCPAUX_NAME_EVAL_TAC `a0:(A)wl_prog`
    [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_NAME_EVAL_TAC `p1:(A)wl_prog`
    [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  ASM_CASES_TAC `wl_state_termdep (st:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THEN
  ASM_REWRITE_TAC([pair_CASE; option_INJ] @ WALLOCPAUX_wl_result_distinct) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `r1 = SOME (wl_TimeOut:(A)wl_result)` THEN ASM_REWRITE_TAC[pair_CASE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_state_eq_rel_def]) THEN
  REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_sct_Seq = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Seq a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Seq a0 a1:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (a0:(A)wl_prog) ssa na lt`
    [`p0:(A)wl_prog`; `sa1:num spt`; `n1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (a1:(A)wl_prog) sa1 n1 lt`
    [`p1:(A)wl_prog`; `sa2:num spt`; `n2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  USE_THEN "ih" (MP_TAC o SPEC `a0:(A)wl_prog`) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `st:(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`cst:(A,C,FFI)wl_state`; `ssa:num spt`; `na:num`;
                             `lt:(num spt#1 spt#1 spt)list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm1:num->num->num` MP_TAC) THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_NAME_EVAL_TAC `a0:(A)wl_prog`
    [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_NAME_EVAL_TAC `p0:(A)wl_prog`
    [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THENL
   [DISCH_TAC THEN EXISTS_TAC `perm1:num->num->num` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `r1:((A)wl_result)option`)) THEN
    ASSUM_LIST(fun ths -> REWRITE_TAC (mapfilter (MATCH_MP WALLOCPAUX_seq_SOME) ths)) THEN
    REWRITE_TAC[pair_CASE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `r1:((A)wl_result)option = NONE` THENL
   [ALL_TAC;
    SUBGOAL_THEN `?x:(A)wl_result. r1 = SOME x` (X_CHOOSE_THEN `x:(A)wl_result` SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[cases "option"]; ALL_TAC] THEN
    EXISTS_TAC `perm1:num->num->num` THEN
    ASSUM_LIST(fun ths -> REWRITE_TAC (mapfilter (MATCH_MP WALLOCPAUX_seq_SOME) ths)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; option_INJ]) THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; option_INJ]] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `r1:((A)wl_result)option`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ssa_cc_trans_props o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `ssa_cc_trans (a0:(A)wl_prog) ssa na lt`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a1:(A)wl_prog`) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s1:(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`s2:(A,C,FFI)wl_state`; `sa1:num spt`; `n1:num`;
                             `lt:(num spt#1 spt#1 spt)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC every_var_mono THEN
    EXISTS_TAC `\x:num. x < na` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm2:num->num->num` (LABEL_TAC "ih2")) THEN
  MP_TAC(ISPECL [`a0:(A)wl_prog`; `wl_state_permute_fupd (K perm1) (st:(A,C,FFI)wl_state)`;
                 `perm2:num->num->num`] permute_swap_lemma) THEN
  ASM_REWRITE_TAC[pair_CASE; option_DISTINCT; wl_state_INFO.ri_fupdfupds; K_o_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm3:num->num->num`) THEN
  EXISTS_TAC `perm3:num->num->num` THEN
  ASSUM_LIST(fun ths -> REWRITE_TAC (mapfilter (MATCH_MP IL2AUX_evaluate_Seq_NONE) ths)) THEN
  REMOVE_THEN "ih2" MP_TAC THEN ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE]);;

(* the guard of an If in the source and in the target                      *)

let WALLOCPAUX_SCT_IFG_TAC : tactic =
  fun (asl,w as g) ->
    let iff = find_term (fun t ->
        try fst(dest_const(fst(strip_comb t))) = "wl_If" with Failure _ -> false) w in
    let args = snd(strip_comb iff) in
    let cmp = el 0 args and r1 = el 1 args and ri = el 2 args in
    let stt = `st:(A,C,FFI)wl_state` in
    let gv = list_mk_icomb "wl_get_var" [r1; stt]
    and gvi = list_mk_icomb "wl_get_var_imm" [ri; stt]
    and wc = list_mk_icomb "wl_word_cmp" [cmp; `x:(A)word_loc`; `y:(A)word_loc`] in
    (MP_TAC(ISPEC gv (cases "option")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:(A)word_loc` ASSUME_TAC)) THENL
      [WALLOCPAUX_EAC_SRCERR_TAC; ALL_TAC] THEN
     MP_TAC(ISPEC gvi (cases "option")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:(A)word_loc` ASSUME_TAC)) THENL
      [WALLOCPAUX_EAC_SRCERR_TAC; ALL_TAC] THEN
     MP_TAC(ISPEC wc (cases "option")) THEN
     DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `b:bool` ASSUME_TAC)) THENL
      [WALLOCPAUX_EAC_SRCERR_TAC; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_imm_def; option_INJ]) THEN
     REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
       is_eq(concl th) && rhs(concl th) = `y:(A)word_loc`))) THEN
     WALLOCPAUX_SCT_GETVAR_TAC) g;;

(* a branch of the If case: p the source branch, q its translation, cn the  *)
(* consistency moves, (sa,nb) the ssa map and counter given to p, (sb,nc)    *)
(* its results, fixth the matching fix_inconsistencies lemma instance        *)

let WALLOCPAUX_SCT_IFBR_TAC (p:term) (q:term) (cn:term) (sa:term) (nb:term)
                            (sb:term) (nc:term) (fixth:thm) : tactic =
  REMOVE_THEN "ih" (MP_TAC o SPEC p) THEN
  ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `st:(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`cst:(A,C,FFI)wl_state`; sa; nb; `lt:(num spt#1 spt#1 spt)list`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na:num` THEN
           ASM_REWRITE_TAC[] THEN NO_TAC;
           MATCH_MP_TAC every_var_mono THEN EXISTS_TAC `\x:num. x < na` THEN
           ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
           MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN
           ASM_REWRITE_TAC[] THEN NO_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` (fun th ->
    EXISTS_TAC `perm:num->num->num` THEN MP_TAC th)) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[WALLOCPAUX_get_var_permute; wl_get_var_imm_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_reg_imm_CASE; wl_get_var_imm_def] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ssa_cc_trans" &&
           el 0 (snd(strip_comb(lhs(concl th)))) = p with Failure _ -> false)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_NAME_EVAL_TAC p [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_NAME_EVAL_TAC q [`r2:((A)wl_result)option`; `s2:(A,C,FFI)wl_state`] THEN
  ASM_CASES_TAC `r1 = SOME (wl_Error:(A)wl_result)` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `r1:((A)wl_result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rx:(A)wl_result` SUBST_ALL_TAC)) THENL
   [(RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_pair(rand(lhs(concl th)))) = q with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP (ISPECL [q; cn] IL2AUX_evaluate_Seq_NONE) th] else NO_TAC) THEN
  MP_TAC fixth THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN TRY(MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na2:num` THEN
    ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(MP_TAC o SPECL [`s1:(A,C,FFI)wl_state`; `s2:(A,C,FFI)wl_state`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC nc THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  WALLOCPAUX_NAME_EVAL_TAC cn [`r3:((A)wl_result)option`; `s3:(A,C,FFI)wl_state`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE] THEN
  MATCH_MP_TAC WALLOCPAUX_word_state_eq_rel_trans THEN EXISTS_TAC `s2:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[]);
    FIRST_ASSUM(fun th -> if is_eq(concl th) &&
        (try fst(dest_pair(rand(lhs(concl th)))) = q with Failure _ -> false)
      then REWRITE_TAC[MATCH_MP (ISPECL [q; cn] WALLOCPAUX_seq_SOME) th] else NO_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; option_INJ]) THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; option_INJ]];;

let WALLOCPAUX_sct_If = prove
 (`!a0 a1 a2 a3 a4.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_If a0 a1 a2 a3 a4:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_If a0 a1 a2 a3 a4:(A)wl_prog)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a2:(A)reg_imm` (cases "reg_imm")) THEN
  (DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_var_imm_def; WALLOCPAUX_reg_imm_CASE]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF; WALLOCPAUX_reg_imm_CASE] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (a3:(A)wl_prog) ssa na lt`
    [`e2':(A)wl_prog`; `ssa2:num spt`; `na2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (a4:(A)wl_prog) ssa na2 lt`
    [`e3':(A)wl_prog`; `ssa3:num spt`; `na3:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `fix_inconsistencies (mk_prio (e2':(A)wl_prog) e3') ssa2 ssa3 na3:
                          (A)wl_prog#(A)wl_prog#num#num spt`
    [`c2:(A)wl_prog`; `c3:(A)wl_prog`; `nf:num`; `sf:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ssa_cc_trans_props o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `ssa_cc_trans (a3:(A)wl_prog) ssa na lt`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ssa_cc_trans_props o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `ssa_cc_trans (a4:(A)wl_prog) ssa na2 lt`)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  WALLOCPAUX_SCT_IFG_TAC THEN
  ASM_CASES_TAC `b:bool` THENL
   [WALLOCPAUX_SCT_IFBR_TAC `a3:(A)wl_prog` `e2':(A)wl_prog` `c2:(A)wl_prog`
      `ssa:num spt` `na:num` `ssa2:num spt` `na2:num`
      (INST_TYPE [`:C`,`:B`; `:FFI`,`:C`]
        (ISPECL [`mk_prio (e2':(A)wl_prog) e3'`; `na3:num`; `ssa2:num spt`; `ssa3:num spt`]
           fix_inconsistencies_correctL));
    WALLOCPAUX_SCT_IFBR_TAC `a4:(A)wl_prog` `e3':(A)wl_prog` `c3:(A)wl_prog`
      `ssa:num spt` `na2:num` `ssa3:num spt` `na3:num`
      (INST_TYPE [`:C`,`:B`; `:FFI`,`:C`]
        (ISPECL [`na3:num`; `ssa2:num spt`; `ssa3:num spt`; `mk_prio (e2':(A)wl_prog) e3'`]
           fix_inconsistencies_correctR))]));;

let WALLOCPAUX_sct_Loop = prove
 (`!a0 a1 a2.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Loop a0 a1 a2:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Loop a0 a1 a2:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `loop_setup a0 a2 ssa na:(A)wl_prog#num spt#num`
    [`sp:(A)wl_prog`; `sr:num spt`; `nr:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (a1:(A)wl_prog) (sptree_inter sr a0) nr (CONS (sr,a0,a2) lt)`
    [`b':(A)wl_prog`; `s':num spt`; `n':num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `cst:(A,C,FFI)wl_state`; `ssa:num spt`; `na:num`;
                 `a0:1 spt`; `a2:1 spt`; `sp:(A)wl_prog`; `sr:num spt`; `nr:num`]
                loop_setup_correct) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `domain (a0:1 spt) SUBSET domain (sr:num spt) /\
                domain (a2:1 spt) SUBSET domain sr` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[domain_union] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `strong_locals_rel (option_lookup (sr:num spt)) (domain (a0:1 spt))
                  (wl_state_locals (st:(A,C,FFI)wl_state)) (wl_state_locals (c1:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [REWRITE_TAC[strong_locals_rel_def] THEN MAP_EVERY X_GEN_TAC [`n:num`; `v:(A)word_loc`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?z. lookup n (sr:num spt) = SOME z` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM domain_lookup] THEN
      UNDISCH_TAC `domain (a0:1 spt) SUBSET domain (sr:num spt)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `ssa_locals_rel nr (sr:num spt) (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (c1:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[THE_DEF] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `c1:(A,C,FFI)wl_state`; `sr:num spt`; `nr:num`;
                 `a0:1 spt`; `a1:(A)wl_prog`; `a2:1 spt`; `lt:(num spt#1 spt#1 spt)list`;
                 `b':(A)wl_prog`; `s':num spt`; `n':num`] ssa_cc_trans_Loop_helper) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `wl_state_locals (c1:(A,C,FFI)wl_state)`)) (concl th))) THEN
      UNDISCH_TAC `domain (a0:1 spt) SUBSET domain (sr:num spt)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC every_var_mono THEN EXISTS_TAC `\x:num. x < na` THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN UNDISCH_TAC `na <= nr` THEN ARITH_TAC;
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (a0:1 spt)))` THEN
      MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN BETA_TAC THEN UNDISCH_TAC `na <= nr` THEN ARITH_TAC;
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (a2:1 spt)))` THEN
      MATCH_MP_TAC MONO_ALL THEN GEN_TAC THEN BETA_TAC THEN UNDISCH_TAC `na <= nr` THEN ARITH_TAC;
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "ih" (MP_TAC o SPEC `a1:(A)wl_prog`) THEN
      ANTS_TAC THENL [WALLOCPAUX_SIZE_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `st':(A,C,FFI)wl_state`) THEN REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
      DISCH_THEN(MP_TAC o SPECL [`cst':(A,C,FFI)wl_state`; `ssa'':num spt`; `na'':num`;
                                 `lt':(num spt#1 spt#1 spt)list`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[TAUT `(if b then T else q) <=> b \/ q`]];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_pair(rand(lhs(concl th)))) = `sp:(A)wl_prog` with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th] else NO_TAC) THEN
  DISCH_TAC THEN
  (fun (asl,w as g) ->
     let tm = find_term (fun t -> is_comb t &&
         (try fst(dest_const(rator t)) = "wl_evaluate" with Failure _ -> false) &&
         (try snd(dest_pair(rand t)) = `c1:(A,C,FFI)wl_state` with Failure _ -> false)) w in
     WALLOCPAUX_TUPLE_TAC tm [`res0:((A)wl_result)option`; `rc0:(A,C,FFI)wl_state`] g) THEN
  REWRITE_TAC[pair_CASE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`res0:((A)wl_result)option`; `rc0:(A,C,FFI)wl_state`] o
    check (fun th -> is_forall(concl th) &&
      (try fst(dest_var(fst(dest_forall(concl th)))) = "res'" with Failure _ -> false))) THEN
  REWRITE_TAC[TAUT `(if b then T else q) <=> b \/ q`] THEN DISCH_THEN ACCEPT_TAC);;

(* the move into register 2 that precedes Raise and Install in the SSA form *)

let WALLOCPAUX_eval_move_var = prove
 (`!p x y (s:(A,C,FFI)wl_state) w.
     wl_get_var y s = SOME w
     ==> wl_evaluate (wl_Move p [(x,y)]:(A)wl_prog,s) =
         (NONE,wl_state_locals_fupd (K (insert x w (wl_state_locals s))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_var_def] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:num`; `x:num`; `y:num`; `s:(A,C,FFI)wl_state`]
                (INST_TYPE [`:A`,`:A`] WALLOCPAUX_evaluate_Move1)) THEN
  ASM_REWRITE_TAC[domain_lookup; THE_DEF] THEN ANTS_TAC THENL [MESON_TAC[]; SIMP_TAC[]]);;

let WALLOCPAUX_sct_Raise = prove
 (`!a0.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Raise a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Raise a0:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; wl_jump_exc_def; COND_CASE_EQ; list_case_eq;
      case_eq "stack_frame"] THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_get_var" &&
           rand(lhs(concl th)) = `cst:(A,C,FFI)wl_state` with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP WALLOCPAUX_eval_move_var th] else NO_TAC) THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert;
                  option_CASE; pair_CASE; wl_jump_exc_def] THEN
  SIMP_NOASM[] THEN WALLOCPAUX_SCT_FINISH_TAC);;

(* the parallel move of the SSA form into fresh distinct registers *)

let WALLOCPAUX_eval_move_list = prove
 (`!p xs ys (s:(A,C,FFI)wl_state) vs.
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys /\ wl_get_vars ys s = SOME vs
     ==> wl_evaluate (wl_Move p (ZIP xs ys):(A)wl_prog,s) = (NONE,wl_set_vars xs vs s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_SIMP_TAC[MAP_ZIP] THEN ASM_REWRITE_TAC[option_CASE]);;

(* the registers 2 * (x + 1) used for arguments and results *)

let WALLOCPAUX_even_regs = prove
 (`!n. ALL_DISTINCT (list_of_seq (\x. 2 * (x + 1)) n) /\
       (!r. MEM r (list_of_seq (\x. 2 * (x + 1)) n) ==> is_phy_var r)`,
  GEN_TAC THEN REWRITE_TAC[ALL_DISTINCT_GENLIST; MEM_GENLIST; is_phy_var_def] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 * (m + 1) = (m + 1) * 2 + 0`] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* the SSA name of a variable of the source state is not a physical register *)

let WALLOCPAUX_option_lookup_not_phy = prove
 (`!na ssa (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) n v.
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     ssa_map_ok na ssa /\ wl_get_var n st = SOME v
     ==> ~is_phy_var (option_lookup ssa n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def; wl_get_var_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o check (fun th ->
    can (find_term (fun t -> t = `wl_state_locals (st:(A,C,FFI)wl_state)`)) (concl th))) THEN
  ASM_REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_sct_Return = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Return a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Return a0 a1:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `rets = list_of_seq (\x. 2 * (x + 1)) (LENGTH (a1:num list))` THEN
  WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"] THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN
  MP_TAC(SPEC `LENGTH (a1:num list)` WALLOCPAUX_even_regs) THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (a:((A)word_loc)list) = LENGTH (a1:num list)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_vars_length_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `list_of_seq (\x. 2 * (x + 1)) (LENGTH (a1:num list))`;
                 `MAP (option_lookup ssa) (a1:num list)`; `cst:(A,C,FFI)wl_state`;
                 `a:((A)word_loc)list`] WALLOCPAUX_eval_move_list) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pair_CASE] THEN
  SUBGOAL_THEN `~MEM (option_lookup ssa (a0:num)) (list_of_seq (\x. 2 * (x + 1)) (LENGTH (a1:num list)))`
    ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`na:num`; `ssa:num spt`; `st:(A,C,FFI)wl_state`; `cst:(A,C,FFI)wl_state`;
                   `a0:num`] WALLOCPAUX_option_lookup_not_phy) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  MP_TAC(ISPECL [`option_lookup ssa (a0:num)`; `list_of_seq (\x. 2 * (x + 1)) (LENGTH (a1:num list))`;
                 `a:((A)word_loc)list`; `cst:(A,C,FFI)wl_state`] get_var_set_vars_notin) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`cst:(A,C,FFI)wl_state`; `list_of_seq (\x. 2 * (x + 1)) (LENGTH (a1:num list))`;
                 `a:((A)word_loc)list`] get_vars_set_vars_eq) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  REWRITE_TAC[wl_flush_state_def; wl_set_vars_def; word_state_eq_rel_def;
              wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]);;

let WALLOCPAUX_sct_Call_tail = prove
 (`!(dest:num option) (args:num list) (h:(num#(A)wl_prog#num#num)option)
    (st:(A,C,FFI)wl_state).
     WALLOCPAUX_sct_Q st (wl_Call NONE dest args h:(A)wl_prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE; LENGTH_MAP] THEN
  MP_TAC(ISPEC `wl_get_vars args (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:((A)word_loc)list` ASSUME_TAC)) THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE; wl_get_vars_with_const];
    ALL_TAC] THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN
  SUBGOAL_THEN `LENGTH (x:((A)word_loc)list) = LENGTH (args:num list)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_vars_length_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (list_of_seq (\x. 2 * x) (LENGTH (args:num list)))` ASSUME_TAC THENL
   [REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `list_of_seq (\x. 2 * x) (LENGTH (args:num list))`;
                 `MAP (option_lookup ssa) (args:num list)`; `cst:(A,C,FFI)wl_state`;
                 `x:((A)word_loc)list`] WALLOCPAUX_eval_move_list) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(fst(dest_pair(rand(lhs(concl th)))))))) = "wl_Move"
       with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th] else NO_TAC) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_get_vars_with_const] THEN ASM_REWRITE_TAC[option_CASE] THEN
  MP_TAC(ISPECL [`cst:(A,C,FFI)wl_state`; `list_of_seq (\x. 2 * x) (LENGTH (args:num list))`;
                 `x:((A)word_loc)list`] get_vars_set_vars_eq) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_CASE] THEN
  SUBGOAL_THEN `bad_dest_args (dest:num option) (list_of_seq (\x. 2 * x) (LENGTH (args:num list))) <=>
                bad_dest_args dest args` SUBST1_TAC THENL
   [REWRITE_TAC[bad_dest_args_def; GSYM LENGTH_EQ_NIL; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THEN
  ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
  REWRITE_TAC[add_ret_loc_def; wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `wl_find_code (dest:num option) (x:((A)word_loc)list)
                  (wl_state_code (st:(A,C,FFI)wl_state)) (wl_state_stack_size st)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `fc:((A)word_loc)list#(A)wl_prog#(num)option` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE] THEN
  SUBGOAL_THEN `?args1 prog ss. fc = (args1:((A)word_loc)list,prog:(A)wl_prog,ss:(num)option)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[pair_CASE] THEN
  STRUCT_CASES_TAC (ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; pair_CASE; WALLOCPAUX_wl_result_CASE] THEN
  ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE] THENL
   [REWRITE_TAC(WALLOCPAUX_wl_result_distinct @ [option_INJ]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_wser_flush THEN
      REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_call_env args1 ss (wl_dec_clock (wl_state_permute_fupd
                  (K (wl_state_permute cst)) (st:(A,C,FFI)wl_state))) =
                wl_call_env args1 ss (wl_dec_clock (wl_state_locals_fupd
                  (K (alist_insert (list_of_seq (\x. 2 * x) (LENGTH (args:num list))) x
                       (wl_state_locals cst))) (cst:(A,C,FFI)wl_state)))` SUBST1_TAC THENL
   [REWRITE_TAC[wl_state_component_equality; wl_call_env_def; wl_dec_clock_def] THEN
    SIMP[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  WALLOCPAUX_NAME_EVAL_TAC `prog:(A)wl_prog` [`r:((A)wl_result)option`; `t:(A,C,FFI)wl_state`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[pair_CASE; WALLOCPAUX_wser_refl] THEN
  UNDISCH_TAC `~wl_bad_fun_return (r:((A)wl_result)option)` THEN
  SPEC_TAC(`r:((A)wl_result)option`, `r:((A)wl_result)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; wl_bad_fun_return_def; option_CASE] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a:(A)wl_result` (cases "wl_result")) THEN
  REWRITE_TAC[wl_bad_fun_return_def; WALLOCPAUX_wl_result_CASE; COND_ID]);;

let WALLOCPAUX_sct_ShareInst = prove
 (`!a0 a1 a2.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (ShareInst a0 a1 a2:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (ShareInst a0 a1 a2:(A)wl_prog)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `a0:memop` (cases "memop")) THEN
  WALLOCPAUX_SCT_OPEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE WALLOCPAUX_memop_distinct) THEN
  REWRITE_TAC(WALLOCPAUX_memop_distinct @ [pair_CASE]) THEN
  WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; case_eq "ffi_result";
      share_inst_def; WALLOCPAUX_sh_mem_set_var_cases;
      wl_sh_mem_store_def; wl_sh_mem_load_def; wl_sh_mem_store_byte_def;
      wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_sh_mem_load_byte_def;
      wl_sh_mem_load16_def; wl_sh_mem_load32_def; COND_CASE_EQ; wl_set_var_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE WALLOCPAUX_memop_distinct) THEN WALLOCPAUX_SCT_GETVAR_TAC THEN
  (SUBGOAL_THEN `wl_word_exp (cst:(A,C,FFI)wl_state) (ssa_cc_trans_exp ssa a2) = SOME (wl_Word a)`
     ASSUME_TAC THENL
    [MATCH_MP_TAC ssa_cc_trans_exp_correct THEN
     MAP_EVERY EXISTS_TAC [`st:(A,C,FFI)wl_state`; `na:num`] THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; share_inst_def;
                  WALLOCPAUX_sh_mem_set_var_cases;
                  wl_sh_mem_store_def; wl_sh_mem_load_def; wl_sh_mem_store_byte_def;
                  wl_sh_mem_store16_def; wl_sh_mem_store32_def; wl_sh_mem_load_byte_def;
                  wl_sh_mem_load16_def; wl_sh_mem_load32_def; wl_set_var_def] THEN
  SIMP[WALLOCPAUX_wl_result_CASE] THEN
  REWRITE_TAC[wl_flush_state_def] THEN WALLOCPAUX_SCT_FINISH_TAC);;

(* the target locals after a chain of inserts and deletes of physical registers *)
let WALLOCPAUX_PEEL_TAC : tactic =
  REPEAT((MATCH_MP_TAC ssa_locals_rel_ignore_insert ORELSE
          MATCH_MP_TAC ssa_locals_rel_delete_right ORELSE
          MATCH_MP_TAC ssa_locals_rel_delete_left) THEN
         REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
         TRY(REWRITE_TAC[is_phy_var_def] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC));;

let WALLOCPAUX_sct_StoreConsts = prove
 (`!a0 a1 a2 a3 a4.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_StoreConsts a0 a1 a2 a3 a4:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_StoreConsts a0 a1 a2 a3 a4:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; COND_CASE_EQ; wl_set_var_def;
      wl_unset_var_def] THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  ASM_REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; option_CASE; pair_CASE;
    ARITH_EQ] THEN
  REWRITE_TAC[wl_set_vars_def; alist_insert_def] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert; ARITH_EQ;
              option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[wl_set_var_def; wl_unset_var_def; wl_state_INFO.ri_accfupds; K_THM; pair_CASE;
              MAP; ALL_DISTINCT; MEM; ARITH_RULE `~(na + 4 = na)`; wl_get_vars_def;
              wl_get_var_def; lookup_insert; lookup_delete; ARITH_EQ; option_CASE;
              wl_set_vars_def; alist_insert_def] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC ssa_locals_rel_insert THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC ssa_map_ok_extend THEN ASM_MESON_TAC[convention_partitions];
    ASM_ARITH_TAC] THEN
  MATCH_MP_TAC ssa_locals_rel_insert THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_PEEL_TAC);;

(* the values read by wl_get_vars, element by element *)
let WALLOCPAUX_get_vars_EL = prove
 (`!ls (st:(A,C,FFI)wl_state) vs i.
     wl_get_vars ls st = SOME vs /\ i < LENGTH ls
     ==> lookup (EL i ls) (wl_state_locals st) = SOME (EL i vs)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN REWRITE_TAC[EL; HD; TL; LENGTH; LT_SUC] THEN
  DISCH_TAC THENL
   [ASM_MESON_TAC[wl_get_var_def];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* the locals after a parallel move, for the renamed and forced ssa map *)
let WALLOCPAUX_move_locals = prove
 (`!P ls1 ls2 vs (ssa:num spt) na (stl:A spt) cstl ren ssa' na'.
     (!x y. P (x,y) ==> ~MEM x ls1) /\
     list_next_var_rename ls1 ssa na = (ren,ssa',na') /\
     ssa_locals_rel na ssa stl cstl /\ ssa_map_ok na ssa /\ ~is_phy_var na /\
     LENGTH ls1 = LENGTH vs /\ LENGTH ls2 = LENGTH ls1 /\
     ALL (\x. x < na) ls1 /\ ALL_DISTINCT ls1 /\
     (!i. i < LENGTH ls2 ==> lookup (EL i ls2) stl = SOME (EL i vs))
     ==> ssa_locals_rel na' (force_rename (FILTER P (ZIP ls2 ren)) ssa')
           (alist_insert ls1 vs stl) (alist_insert ren vs cstl)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (ren:num list) /\ LENGTH ren = LENGTH (ls1:num list)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ls2:num list) = LENGTH (ren:num list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ssa_locals_rel_force_rename THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`ls1:num list`; `ssa:num spt`; `na:num`; `stl:A spt`; `cstl:A spt`;
                   `ren:num list`; `ssa':num spt`; `na':num`; `vs:A list`]
           ssa_locals_rel_list_next_var_rename) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN X_GEN_TAC `p:num#num` THEN
    SIMP_TAC[MEM_ZIP; ASSUME `LENGTH (ls2:num list) = LENGTH (ren:num list)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN
    SUBGOAL_THEN `~MEM (EL n ls2:num) ls1` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `EL n ren:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[WALLOCPAUX_lookup_alist_insert_notin] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `SOME (EL n vs:A)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `n < LENGTH (ren:num list)` THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MISC3AUX_lookup_alist_insert_EL THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_MAP; MEM_FILTER] THEN
    SIMP_TAC[MEM_ZIP; ASSUME `LENGTH (ls2:num list) = LENGTH (ren:num list)`] THEN
    SUBGOAL_THEN `LENGTH (ren:num list) = LENGTH (vs:A list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[domain_alist_insert; IN_UNION; IN_SET_OF_LIST] THEN
    REPEAT STRIP_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[SND] THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `n:num` THEN ASM_MESON_TAC[]]);;

let WALLOCPAUX_sct_Move = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Move a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Move a0 a1:(A)wl_prog)`,
  WALLOCPAUX_SCT_OPEN_TAC THEN WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; COND_CASE_EQ; wl_set_vars_def] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename (MAP FST (a1:(num#num)list)) ssa na`
    [`ren:num list`; `ssa1:num spt`; `na1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  SUBGOAL_THEN `ALL_DISTINCT (ren:num list) /\ LENGTH ren = LENGTH (a1:(num#num)list)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (a:((A)word_loc)list) = LENGTH (a1:(num#num)list)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP get_vars_length_lemma) THEN REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_vars (MAP (option_lookup ssa) (MAP SND (a1:(num#num)list)))
                  (cst:(A,C,FFI)wl_state) = SOME a` ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_locals_rel_get_vars THEN
    EXISTS_TAC `na:num` THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SUBGOAL_THEN `LENGTH (ren:num list) =
                LENGTH (MAP (option_lookup ssa) (MAP SND (a1:(num#num)list)))`
    (LABEL_TAC "lz") THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  USE_THEN "lz" (fun th -> REWRITE_TAC[MATCH_MP MAP_FST_ZIP th; MATCH_MP MAP_SND_ZIP th]) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC WALLOCPAUX_move_locals THEN
  MAP_EVERY EXISTS_TAC [`ssa:num spt`; `na:num`] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE];
    ASM_MESON_TAC[convention_partitions];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WALLOCPAUX_get_vars_EL THEN
    ASM_REWRITE_TAC[LENGTH_MAP]]);;

(* ------------------------------------------------------------------------- *)
(* ssa_cc_trans_correct, case Inst (HOL4 line 7860): one lemma per group of  *)
(* instructions, all following the same pattern: run the source, transfer   *)
(* the register reads to the target, run the target, relate the results     *)
(* ------------------------------------------------------------------------- *)

let WALLOCPAUX_SCT_IOPEN_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[ssa_cc_trans_def; ssa_cc_trans_inst_def; next_var_rename_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_EAC_SRC_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_var_inst_def; every_var_imm_def]);;

let WALLOCPAUX_SCT_EXPS_TAC : tactic =
  fun (asl,w as g) ->
    let hd th = try fst(dest_const(fst(strip_comb(concl th)))) with Failure _ -> "" in
    let lhd th = try fst(dest_const(fst(strip_comb(lhs(concl th))))) with Failure _ -> "" in
    let rel = snd(find (fun (_,th) -> hd th = "ssa_locals_rel") asl) in
    let eqr = snd(find (fun (_,th) -> hd th = "word_state_eq_rel") asl) in
    let ex = filter (fun (_,th) -> lhd th = "wl_word_exp") asl in
    MAP_EVERY (fun (_,th) ->
       try ASSUME_TAC(REWRITE_RULE[ssa_cc_trans_exp_def; MAP]
             (MATCH_MP ssa_cc_trans_exp_correct (CONJ th (CONJ eqr rel))))
       with Failure _ -> ALL_TAC) ex g;;

let WALLOCPAUX_SCT_NOTPHY_TAC : tactic =
  fun (asl,w as g) ->
    let hd th = try fst(dest_const(fst(strip_comb(concl th)))) with Failure _ -> "" in
    let lhd th = try fst(dest_const(fst(strip_comb(lhs(concl th))))) with Failure _ -> "" in
    let rel = snd(find (fun (_,th) -> hd th = "ssa_locals_rel") asl) in
    let mok = snd(find (fun (_,th) -> hd th = "ssa_map_ok") asl) in
    let gv = filter (fun (_,th) -> lhd th = "wl_get_var") asl in
    MAP_EVERY (fun (_,th) ->
       try ASSUME_TAC(MATCH_MP WALLOCPAUX_option_lookup_not_phy (CONJ rel (CONJ mok th)))
       with Failure _ -> ALL_TAC) gv g;;

let WALLOCPAUX_INST_CASES =
  map (fun n -> (case_info_of_tyname n).ci_def)
      ["inst"; "asm_arith"; "memop"; "addr"; "fp"; "reg_imm"; "list"; "word_loc"];;

let WALLOCPAUX_SCT_INST_TAC : tactic =
  WALLOCPAUX_SCT_IOPEN_TAC THEN
  GVS[wl_inst_def; wl_assign_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; case_eq "list"; COND_CASE_EQ; wl_set_var_def; wl_set_fp_var_def;
      wl_get_fp_var_def; wl_get_vars_def; WALLOCPAUX_reg_imm_CASE; wl_mem_load_def;
      wl_mem_store_def] THEN
  WALLOCPAUX_SCT_EXPS_TAC THEN WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_NOTPHY_TAC THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC([wl_inst_def; wl_assign_def] @ WALLOCPAUX_INST_CASES) THEN
  ASM_REWRITE_TAC([option_CASE; pair_CASE; wl_set_var_def; wl_get_fp_var_def;
                   wl_set_fp_var_def; wl_get_vars_def; wl_mem_load_def; wl_mem_store_def] @
                  WALLOCPAUX_INST_CASES) THEN
  WALLOCPAUX_SCT_FINISH_TAC;;

(* infrastructure for the Inst cases of ssa_cc_trans_correct                 *)

let WALLOCPAUX_PHY_REGS = prove
 (`is_phy_var 0 /\ is_phy_var 2 /\ is_phy_var 4 /\ is_phy_var 6 /\ is_phy_var 8`,
  REWRITE_TAC[is_phy_var_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let WALLOCPAUX_phy_neq = prove
 (`!x y. ~is_phy_var x /\ is_phy_var y ==> ~(x = y) /\ ~(y = x)`,
  MESON_TAC[]);;

let WALLOCPAUX_lt_neq = prove
 (`!x na. x < na ==> ~(x = na) /\ ~(na = x) /\ ~(x = na + 4) /\ ~(na + 4 = x)`,
  ARITH_TAC);;

let WALLOCPAUX_na_notphy = prove
 (`!na. is_alloc_var na ==>
        ~is_phy_var na /\ ~is_phy_var (na + 4) /\ ~(na = na + 4) /\ ~(na + 4 = na)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `~(na = na + 4) /\ ~(na + 4 = na)`] THEN
  ASM_MESON_TAC[convention_partitions; WALLOCPAUX_is_alloc_var_add4]);;

(* the SSA name of a variable of the source state is a renamed variable *)

let WALLOCPAUX_option_lookup_ok = prove
 (`!na ssa (st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) n v.
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     ssa_map_ok na ssa /\ wl_get_var n st = SOME v
     ==> ~is_phy_var (option_lookup ssa n) /\ option_lookup ssa n < na`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def; wl_get_var_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `v:(A)word_loc`] o check (fun th ->
    can (find_term (fun t -> t = `wl_state_locals (st:(A,C,FFI)wl_state)`)) (concl th))) THEN
  ASM_REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN ASM_MESON_TAC[]);;

(* for the fresh name na and every renamed source variable among the        *)
(* wl_get_var assumptions: disequalities with the small physical registers  *)
(* and with na and na + 4 (to decide lookup_insert conditions)               *)

let WALLOCPAUX_SCT_NEQ_TAC : tactic =
  fun (asl,w as g) ->
    let hd th = try fst(dest_const(fst(strip_comb(concl th)))) with Failure _ -> "" in
    let lhd th = try fst(dest_const(fst(strip_comb(lhs(concl th))))) with Failure _ -> "" in
    let rel = snd(find (fun (_,th) -> hd th = "ssa_locals_rel") asl) in
    let mok = snd(find (fun (_,th) -> hd th = "ssa_map_ok") asl) in
    let alv = snd(find (fun (_,th) -> hd th = "is_alloc_var") asl) in
    let gv = filter (fun (_,th) -> lhd th = "wl_get_var" &&
                       (try fst(dest_const(fst(strip_comb(rand(lhs(concl th)))))) <> ""
                        with Failure _ -> true)) asl in
    let phys = CONJUNCTS WALLOCPAUX_PHY_REGS in
    let naf = CONJUNCTS(MATCH_MP WALLOCPAUX_na_notphy alv) in
    let nonphy x = flat (map (fun k -> CONJUNCTS(MATCH_MP WALLOCPAUX_phy_neq (CONJ x k))) phys) in
    let srcf = flat (map (fun (_,th) ->
        try let c = MATCH_MP WALLOCPAUX_option_lookup_ok (CONJ rel (CONJ mok th)) in
            let c1,c2 = CONJ_PAIR c in
            c1 :: nonphy c1 @ CONJUNCTS(MATCH_MP WALLOCPAUX_lt_neq c2)
        with Failure _ -> []) gv) in
    let thms = naf @ nonphy (el 0 naf) @ nonphy (el 1 naf) @ srcf in
    MAP_EVERY ASSUME_TAC thms g;;

(* the relation for a chain of target inserts: fresh names (set_var) or     *)
(* physical registers (ignore_insert)                                        *)

let WALLOCPAUX_REL_TAC : tactic =
  REPEAT((MATCH_MP_TAC ssa_locals_rel_set_var ORELSE
          MATCH_MP_TAC ssa_locals_rel_ignore_insert) THEN
         REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
         TRY(REWRITE_TAC[WALLOCPAUX_PHY_REGS] THEN NO_TAC) THEN
         TRY(MATCH_MP_TAC ssa_map_ok_extend THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
         TRY(MATCH_MP_TAC (ARITH_RULE `r < na ==> r < na + 4`) THEN
             FIRST_ASSUM ACCEPT_TAC));;

let WALLOCPAUX_TGT_RWS =
  [option_CASE; pair_CASE; wl_set_var_def; wl_get_fp_var_def; wl_set_fp_var_def;
   wl_get_vars_def; wl_get_var_def; wl_mem_load_def; wl_mem_store_def; wl_set_vars_def;
   alist_insert_def; MAP; ALL_DISTINCT; MEM; wl_state_INFO.ri_accfupds; K_THM;
   lookup_insert; ARITH_EQ; wl_inst_def; wl_assign_def; wl_word_exp_def; LET_DEF;
   LET_END_DEF; OPTION_MAP_DEF; VAL_EQ_0] @ WALLOCPAUX_INST_CASES;;

(* evaluate a target of at most three nested Seq/Move/Inst steps *)

let WALLOCPAUX_SCT_TGT_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC WALLOCPAUX_TGT_RWS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC WALLOCPAUX_TGT_RWS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC WALLOCPAUX_TGT_RWS THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC WALLOCPAUX_TGT_RWS;;

let WALLOCPAUX_SCT_IFIN_TAC : tactic =
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  WALLOCPAUX_REL_TAC;;

let WALLOCPAUX_SCT_INST2_TAC : tactic =
  WALLOCPAUX_SCT_IOPEN_TAC THEN
  GVS[wl_inst_def; wl_assign_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; case_eq "list"; COND_CASE_EQ; wl_set_var_def; wl_set_fp_var_def;
      wl_get_fp_var_def; wl_get_vars_def; WALLOCPAUX_reg_imm_CASE; wl_mem_load_def;
      wl_mem_store_def] THEN
  WALLOCPAUX_SCT_EXPS_TAC THEN WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_NEQ_TAC THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN WALLOCPAUX_SCT_TGT_TAC THEN WALLOCPAUX_SCT_IFIN_TAC;;

let WALLOCPAUX_SCT_INST3_TAC : tactic =
  WALLOCPAUX_SCT_IOPEN_TAC THEN
  GVS[wl_inst_def; wl_assign_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; case_eq "list"; COND_CASE_EQ; wl_set_var_def; wl_set_fp_var_def;
      wl_get_fp_var_def; wl_get_vars_def; WALLOCPAUX_reg_imm_CASE; wl_mem_load_def;
      wl_mem_store_def; wl_word_exp_def] THEN
  WALLOCPAUX_SCT_EXPS_TAC THEN WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_NEQ_TAC THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN WALLOCPAUX_SCT_TGT_TAC THEN WALLOCPAUX_SCT_IFIN_TAC;;


let WALLOCPAUX_RI_SPLIT_TAC (tac:tactic) : tactic =
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[cases "reg_imm"]
    `(!r. P (Reg r)) /\ (!w. P (Imm w)) ==> !ri:(A)reg_imm. P ri`) THEN
  CONJ_TAC THEN tac;;

let WALLOCPAUX_sct_Inst_basic = prove
 (`(!st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Inst asm_Skip:(A)wl_prog)) /\
   (!reg w st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (asm_Const reg w):(A)wl_prog)) /\
   (!r1 r2 r3 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (asm_Div r1 r2 r3)):(A)wl_prog)) /\
   (!r a w st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem asm_Load r (Addr a w)):(A)wl_prog)) /\
   (!r a w st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem asm_Store r (Addr a w)):(A)wl_prog)) /\
   (!r a w st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem asm_Load32 r (Addr a w)):(A)wl_prog)) /\
   (!r a w st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem asm_Store32 r (Addr a w)):(A)wl_prog)) /\
   (!r a w st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem Load8 r (Addr a w)):(A)wl_prog)) /\
   (!r a w st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem Store8 r (Addr a w)):(A)wl_prog)) /\
   (!r f1 f2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPLess r f1 f2)):(A)wl_prog)) /\
   (!r f1 f2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPLessEqual r f1 f2)):(A)wl_prog)) /\
   (!r f1 f2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPEqual r f1 f2)):(A)wl_prog)) /\
   (!v7 v8 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem Load16 v7 v8):(A)wl_prog)) /\
   (!v7 v8 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (Mem Store16 v7 v8):(A)wl_prog)) /\
   (!d1 d2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPAbs d1 d2)):(A)wl_prog)) /\
   (!d1 d2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPNeg d1 d2)):(A)wl_prog)) /\
   (!d1 d2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPSqrt d1 d2)):(A)wl_prog)) /\
   (!d1 d2 d3 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPAdd d1 d2 d3)):(A)wl_prog)) /\
   (!d1 d2 d3 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPSub d1 d2 d3)):(A)wl_prog)) /\
   (!d1 d2 d3 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPMul d1 d2 d3)):(A)wl_prog)) /\
   (!d1 d2 d3 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPDiv d1 d2 d3)):(A)wl_prog)) /\
   (!d1 d2 d3 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPFma d1 d2 d3)):(A)wl_prog)) /\
   (!d1 d2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPMov d1 d2)):(A)wl_prog)) /\
   (!d1 d2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPToInt d1 d2)):(A)wl_prog)) /\
   (!d1 d2 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPFromInt d1 d2)):(A)wl_prog))`,
  REPEAT CONJ_TAC THEN WALLOCPAUX_SCT_INST_TAC);;

let WALLOCPAUX_sct_Inst_Binop = prove
 (`!bop r1 r2 (ri:(A)reg_imm) (st:(A,C,FFI)wl_state).
     WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (Binop bop r1 r2 ri)):(A)wl_prog)`,
  WALLOCPAUX_RI_SPLIT_TAC WALLOCPAUX_SCT_INST_TAC);;

let WALLOCPAUX_sct_Inst_Shift = prove
 (`!sh r1 r2 (ri:(A)reg_imm) (st:(A,C,FFI)wl_state).
     WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (asm_Shift sh r1 r2 ri)):(A)wl_prog)`,
  WALLOCPAUX_RI_SPLIT_TAC WALLOCPAUX_SCT_INST3_TAC);;

let WALLOCPAUX_sct_Inst_moves = prove
 (`(!r1 r2 r3 r4 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)):(A)wl_prog)) /\
   (!r1 r2 r3 r4 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (AddOverflow r1 r2 r3 r4)):(A)wl_prog)) /\
   (!r1 r2 r3 r4 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (SubOverflow r1 r2 r3 r4)):(A)wl_prog)) /\
   (!r1 r2 r3 r4 st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (LongMul r1 r2 r3 r4)):(A)wl_prog)) /\
   (!r1 r2 d st:(A,C,FFI)wl_state.
      WALLOCPAUX_sct_Q st (wl_Inst (FP (FPMovToReg r1 r2 d)):(A)wl_prog))`,
  REPEAT CONJ_TAC THEN WALLOCPAUX_SCT_INST2_TAC);;

let WALLOCPAUX_sct_Inst_LongDiv = prove
 (`!r1 r2 r3 r4 r5 (st:(A,C,FFI)wl_state).
     WALLOCPAUX_sct_Q st (wl_Inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)):(A)wl_prog)`,
  WALLOCPAUX_SCT_IOPEN_TAC THEN
  GVS[wl_inst_def; wl_assign_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; case_eq "list"; COND_CASE_EQ; wl_set_var_def; wl_set_fp_var_def;
      wl_get_fp_var_def; wl_get_vars_def; WALLOCPAUX_reg_imm_CASE; wl_mem_load_def;
      wl_mem_store_def] THEN
  WALLOCPAUX_SCT_EXPS_TAC THEN WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_NEQ_TAC THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN WALLOCPAUX_SCT_TGT_TAC THEN
  REWRITE_TAC[MATCH_MP insert_swap (ARITH_RULE `~(na = na + 4)`)] THEN
  WALLOCPAUX_SCT_IFIN_TAC);;

(* renaming a variable of the source to a fresh name holding the same value *)

let WALLOCPAUX_ssa_locals_rel_rename = prove
 (`!na ssa (stl:A spt) cstl n w.
     ssa_locals_rel na ssa stl cstl /\ ssa_map_ok na ssa /\ n < na /\
     lookup n stl = SOME w
     ==> ssa_locals_rel (na + 4) (insert n na ssa) stl (insert na w cstl)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`na:num`; `ssa:num spt`; `stl:A spt`; `cstl:A spt`; `n:num`; `w:A`]
         ssa_locals_rel_set_var) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. lookup x (insert n (w:A) stl) = lookup x stl` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ssa_locals_rel_def]);;

(* two renamed source registers are equal: so are their values *)

let WALLOCPAUX_SAME_REG_TAC : tactic =
  fun (asl,w as g) ->
    let isol t = try fst(dest_const(fst(strip_comb t))) = "option_lookup"
                 with Failure _ -> false in
    let eqth = snd(find (fun (_,th) -> is_eq(concl th) && isol(lhs(concl th)) &&
                                       isol(rhs(concl th))) asl) in
    let l = lhs(concl eqth) and r = rhs(concl eqth) in
    let isgv x th = is_eq(concl th) &&
      (try let f,args = strip_comb(lhs(concl th)) in
           fst(dest_const f) = "wl_get_var" && hd args = x with Failure _ -> false) in
    let th1 = snd(find (fun (_,th) -> isgv l th) asl)
    and th2 = snd(find (fun (_,th) -> isgv r th) asl) in
    let e = TRANS (SYM (REWRITE_RULE[eqth] th1)) th2 in
    let e' = REWRITE_RULE([option_INJ] @ (case_info_of_tyname "word_loc").ci_inject) e in
    SUBST_ALL_TAC e' g;;

let WALLOCPAUX_sct_FPMovFromReg = prove
 (`!d r1 r2 (st:(A,C,FFI)wl_state).
     WALLOCPAUX_sct_Q st (wl_Inst (FP (FPMovFromReg d r1 r2)):(A)wl_prog)`,
  WALLOCPAUX_SCT_IOPEN_TAC THEN
  GVS[wl_inst_def; wl_assign_def; option_case_eq; pair_case_eq;
      case_eq "word_loc"; case_eq "list"; COND_CASE_EQ; wl_set_var_def; wl_set_fp_var_def;
      wl_get_fp_var_def; wl_get_vars_def; WALLOCPAUX_reg_imm_CASE; wl_mem_load_def;
      wl_mem_store_def] THEN
  WALLOCPAUX_SCT_EXPS_TAC THEN WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_NEQ_TAC THEN
  WALLOCPAUX_SCT_EXPAND_TAC THENL
   [WALLOCPAUX_SCT_TGT_TAC THEN WALLOCPAUX_SCT_IFIN_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[pair_CASE] THENL
   [WALLOCPAUX_SAME_REG_TAC THEN WALLOCPAUX_SCT_TGT_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_rename THEN ASM_REWRITE_TAC[]];
    WALLOCPAUX_SCT_TGT_TAC THEN WALLOCPAUX_SCT_IFIN_TAC]);;

let WALLOCPAUX_sct_Inst = prove
 (`!(i:(A)inst) (st:(A,C,FFI)wl_state). WALLOCPAUX_sct_Q st (wl_Inst i:(A)wl_prog)`,
  MP_TAC(ISPEC `\(i:(A)inst) (ssa:num spt) (na:num).
                  !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Inst i:(A)wl_prog)`
         ssa_cc_trans_inst_ind) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WALLOCPAUX_sct_Inst_basic; WALLOCPAUX_sct_Inst_Binop; WALLOCPAUX_sct_Inst_Shift;
              WALLOCPAUX_sct_Inst_moves; WALLOCPAUX_sct_Inst_LongDiv;
              WALLOCPAUX_sct_FPMovFromReg] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* ssa_cc_trans_correct, case Alloc (HOL4 line 9333): the Alloc itself is    *)
(* the Alloc case of evaluate_apply_colour for the colouring option_lookup  *)
(* of the renamed map; around it the two renaming moves                      *)
(* ------------------------------------------------------------------------- *)

(* the locals after popping the frame pushed for an Alloc *)

let WALLOCPAUX_pop_push_domain = prove
 (`!(e1:((A)word_loc)spt) e2 (s:(A,C,FFI)wl_state) (s2:(A,C,FFI)wl_state)
    (s3:(A,C,FFI)wl_state).
     s_key_eq (wl_state_stack (wl_push_env (e1,e2) NONE s)) (wl_state_stack s2) /\
     wl_pop_env s2 = SOME s3
     ==> domain (wl_state_locals s3) = domain e1 UNION domain e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_push_env_NONE_stack; wl_pop_env_def] THEN
  MP_TAC(ISPEC `wl_state_stack (s2:(A,C,FFI)wl_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `hd:(A)stack_frame`
    (X_CHOOSE_THEN `tl:((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[s_key_eq_def] THEN
  STRUCT_CASES_TAC (ISPEC `hd:(A)stack_frame` (cases "stack_frame")) THEN
  REWRITE_TAC[s_frame_key_eq_def2; list_CASE; WALLOCPAUX_stack_frame_CASE] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "a3")) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "a1")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; option_INJ]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `s3:(A,C,FFI)wl_state`)) THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; domain_union; domain_fromAList;
              set_MAP_FST_toAList_domain] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      rhs(concl th) = `MAP FST (a2:(num#(A)word_loc)list)`
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  REWRITE_TAC[IL2AUX_env_to_list_domain] THEN
  SET_TAC[]);;

let WALLOCPAUX_cut_names_domain = prove
 (`!(n:B spt) (env:A spt) e. cut_names n env = SOME e ==> domain e = domain n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[domain_inter] THEN ASM SET_TAC[]);;

let WALLOCPAUX_alloc_NONE_domain = prove
 (`!w n1 n2 (s:(A,C,FFI)wl_state) (s':(A,C,FFI)wl_state).
     wl_alloc w (n1,n2) s = (NONE,s')
     ==> domain (wl_state_locals s') = domain n1 UNION domain n2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  GVS[option_case_eq; pair_case_eq; COND_CASE_EQ; PAIR_EQ; option_DISTINCT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e1:((A)word_loc)spt`; `e2:((A)word_loc)spt`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s3:(A,C,FFI)wl_state`
      (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `s':(A,C,FFI)wl_state`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "cut_envs"
     with Failure _ -> false))) THEN
  REWRITE_TAC[WALLOCPAUX_cut_envs_SOME] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM o MATCH_MP WALLOCPAUX_cut_names_domain)) THEN
  MATCH_MP_TAC WALLOCPAUX_pop_push_domain THEN
  EXISTS_TAC `wl_set_store AllocSize (wl_Word w) (s:(A,C,FFI)wl_state)` THEN
  EXISTS_TAC `s2:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC gc_s_key_eq THEN FIRST_ASSUM ACCEPT_TAC);;

let WALLOCPAUX_alloc_SOME = prove
 (`!w names (s:(A,C,FFI)wl_state) r (s':(A,C,FFI)wl_state).
     wl_alloc w names s = (SOME r,s') ==> r = wl_Error \/ r = NotEnoughSpace`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  REPEAT TOP_CASE_TAC THEN SIMP[PAIR_EQ; option_INJ; option_DISTINCT] THEN MESON_TAC[]);;

(* the names given by the renaming move: fresh for the moved variables, the *)
(* old ones otherwise                                                        *)

let WALLOCPAUX_lnvrm_names = prove
 (`!(ssa:num spt) na ls (mov:(A)wl_prog) ssa' na'.
     list_next_var_rename_move ssa na ls = (mov,ssa',na') /\ ALL_DISTINCT ls
     ==> (!y. MEM y ls ==> na <= option_lookup ssa' y) /\
         (!x. ~MEM x ls ==> option_lookup ssa' x = option_lookup ssa x) /\
         domain ssa' = domain ssa UNION set_of_list ls`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename ls (ssa:num spt) na`
    [`new:num list`; `s1:num spt`; `n1:num`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && is_var(rhs(concl th))))) THEN
  MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun t -> t = `?y. lookup x (ssa':num spt) = SOME y`)) (concl th)
      then MP_TAC(SPEC `y:num` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
    SUBGOAL_THEN `MEM (z:num) new` MP_TAC THENL
     [UNDISCH_TAC `new = MAP (\x. THE (lookup x (ssa':num spt))) ls` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `y:num` THEN
      ASM_REWRITE_TAC[THE_DEF];
      ALL_TAC] THEN
    UNDISCH_TAC `new = MAP (\x. 4 * x + na) (COUNT_LIST (LENGTH (ls:num list)))` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM_MAP] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[option_lookup_def] THEN
    ASM_SIMP_TAC[]]);;

let WALLOCPAUX_lnvrm_INJ = prove
 (`!(ssa:num spt) na ls (mov:(A)wl_prog) ssa' na' n.
     list_next_var_rename_move ssa (na + 2) ls = (mov,ssa',na') /\ ALL_DISTINCT ls /\
     ssa_map_ok na ssa /\ n IN domain ssa
     ==> INJ (option_lookup ssa') (n INSERT set_of_list ls) UNIV`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WALLOCPAUX_lnvrm_names o
    CONJ (ASSUME `list_next_var_rename_move (ssa:num spt) (na + 2) ls =
                  (mov:(A)wl_prog,ssa',na')`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN domain (ssa:num spt) ==> option_lookup ssa x < na` ASSUME_TAC THENL
   [REWRITE_TAC[domain_lookup] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
    UNDISCH_TAC `ssa_map_ok na (ssa:num spt)` THEN REWRITE_TAC[ssa_map_ok_def] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INJ; IN_UNIV; IN_INSERT; IN_SET_OF_LIST] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
  ASM_CASES_TAC `MEM (x:num) ls` THEN ASM_CASES_TAC `MEM (y:num) ls` THEN
  ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN MATCH_MP_TAC list_next_var_rename_move_distinct THEN
    MAP_EVERY EXISTS_TAC [`ssa:num spt`; `na + 2`; `ls:num list`; `mov:(A)wl_prog`;
                          `ssa':num spt`; `na':num`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    MATCH_MP_TAC(ARITH_RULE `a < na /\ na + 2 <= b ==> ~(b:num = a)`) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    MATCH_MP_TAC(ARITH_RULE `a < na /\ na + 2 <= b ==> ~(a:num = b)`) THEN
    ASM_SIMP_TAC[];
    MESON_TAC[]]);;

(* the relation for the cut-down map after a call or an Alloc *)

let WALLOCPAUX_ssa_locals_rel_cut2 = prove
 (`!(ssa:num spt) (ns:1 spt) (env:A spt) y na.
     domain env = domain ns /\ domain ns SUBSET domain ssa /\
     strong_locals_rel (option_lookup ssa) (domain ns) env y /\
     ALL (\x. x < na) (MAP FST (toAList ns))
     ==> ssa_locals_rel na (sptree_inter ssa ns) env y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ssa_locals_rel_def; lookup_inter_alt] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `z:num`] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?v:A. lookup x (env:A spt) = SOME v` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM domain_lookup] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `strong_locals_rel (option_lookup (ssa:num spt)) (domain (ns:1 spt))
                   (env:A spt) y` THEN
    REWRITE_TAC[strong_locals_rel_def] THEN DISCH_THEN(MP_TAC o SPECL [`x:num`; `v:A`]) THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE; domain_lookup] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `v:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN domain (ns:1 spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `domain (env:A spt) = domain (ns:1 spt)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z. lookup x (ssa:num spt) = SOME z` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM domain_lookup] THEN
    UNDISCH_TAC `domain (ns:1 spt) SUBSET domain (ssa:num spt)` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[domain_inter; IN_INTER; THE_DEF] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[domain_lookup] THEN EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `strong_locals_rel (option_lookup (ssa:num spt)) (domain (ns:1 spt))
                   (env:A spt) y` THEN
    REWRITE_TAC[strong_locals_rel_def] THEN DISCH_THEN(MP_TAC o SPECL [`x:num`; `v:A`]) THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE];
    DISCH_TAC THEN UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (ns:1 spt)))` THEN
    REWRITE_TAC[GSYM ALL_MEM; toAList_domain] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* an ssa relation gives a strong relation under option_lookup, also after a *)
(* write to a physical register of the target                               *)

let WALLOCPAUX_ssa_locals_rel_strong_phy = prove
 (`!na ssa (stl:A spt) cstl s k v.
     ssa_locals_rel na ssa stl cstl /\ ssa_map_ok na ssa /\ is_phy_var k
     ==> strong_locals_rel (option_lookup ssa) s stl (insert k v cstl)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def; strong_locals_rel_def] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `u:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `u:A`] o check (fun th ->
    can (find_term (fun t -> t = `stl:A spt`)) (concl th))) THEN
  ASM_REWRITE_TAC[domain_lookup] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `z:num`) MP_TAC) THEN
  ASM_REWRITE_TAC[THE_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_lookup_def; option_CASE; lookup_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_sct_Alloc = prove
 (`!a0 a1.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Alloc a0 a1:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Alloc a0 a1:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  SUBGOAL_THEN `?p0 p1. a1 = (p0:num_set,p1:num_set)`
    (X_CHOOSE_THEN `p0:num_set` (X_CHOOSE_THEN `p1:num_set` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_name_def; FST; SND]) THEN
  MP_TAC(ISPEC `wl_get_var a0 (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:(A)word_loc` ASSUME_TAC)) THENL
   [EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[WALLOCPAUX_get_var_permute; option_CASE; pair_CASE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v:(A)word_loc` (cases "word_loc")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:(A)word` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `l1:num` (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC))) THENL
   [ALL_TAC;
    EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[WALLOCPAUX_get_var_permute; option_CASE; pair_CASE;
                    WALLOCPAUX_word_loc_CASE]] THEN
  MP_TAC(ISPEC `cut_envs (p0:num_set,p1:num_set) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `xx:((A)word_loc)spt#((A)word_loc)spt` ASSUME_TAC)) THENL
   [EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[WALLOCPAUX_get_var_permute; option_CASE; WALLOCPAUX_word_loc_CASE] THEN
    REWRITE_TAC[wl_alloc_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[option_CASE; pair_CASE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. xx = (x1:((A)word_loc)spt,x2:((A)word_loc)spt)`
    (X_CHOOSE_THEN `x1:((A)word_loc)spt` (X_CHOOSE_THEN `x2:((A)word_loc)spt`
      SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_envs_domain_SUBSET) THEN
  ABBREV_TAC `ls = MAP FST (toAList (sptree_union p0 p1:num_set))` THEN
  SUBGOAL_THEN `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[set_MAP_FST_toAList_domain; domain_union];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (ls:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (ssa:num spt) (na + 2) ls:(A)wl_prog#num spt#num`
    [`mov1:(A)wl_prog`; `ssa1:num spt`; `na1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))
                          (na1 + 2) ls:(A)wl_prog#num spt#num`
    [`mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `ssa:num spt`; `na + 2`; `ls:num list`;
                 `cst:(A,C,FFI)wl_state`] list_next_var_rename_move_preserve) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[UNION_SUBSET];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov1:(A)wl_prog,cst:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `rcst1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `na + 2 <= na1 /\ ssa_map_ok na1 (ssa1:num spt)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`; `mov1:(A)wl_prog`;
                   `ssa1:num spt`; `na1:num`] list_next_var_rename_move_props_2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ssa:num spt`; `na + 2`; `ls:num list`; `mov1:(A)wl_prog`;
                 `ssa1:num spt`; `na1:num`] WALLOCPAUX_lnvrm_names) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wl_get_var (option_lookup ssa1 a0) (rcst1:(A,C,FFI)wl_state) =
                SOME (wl_Word (w:A word))` ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_locals_rel_get_var THEN
    MAP_EVERY EXISTS_TAC [`na1:num`; `st:(A,C,FFI)wl_state`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(option_lookup ssa1 a0 = 2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`na1:num`; `ssa1:num spt`; `st:(A,C,FFI)wl_state`;
                   `rcst1:(A,C,FFI)wl_state`; `a0:num`; `wl_Word (w:A word)`]
           WALLOCPAUX_option_lookup_not_phy) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[WALLOCPAUX_PHY_REGS];
    ALL_TAC] THEN
  ABBREV_TAC `rcst2 = wl_state_locals_fupd
     (K (insert 2 (wl_Word (w:A word)) (wl_state_locals rcst1))) (rcst1:(A,C,FFI)wl_state)` THEN
  SUBGOAL_THEN `!X. wl_evaluate (wl_Seq mov1 (wl_Seq (wl_Move 1 [2,option_lookup ssa1 a0]) X),
                    cst) = wl_evaluate (X,rcst2:(A,C,FFI)wl_state)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`mov1:(A)wl_prog`; `wl_Seq (wl_Move 1 [2,option_lookup ssa1 a0]) X:(A)wl_prog`;
                   `cst:(A,C,FFI)wl_state`; `rcst1:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def] THEN
    ASM_REWRITE_TAC[option_CASE; wl_set_vars_def; alist_insert_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a0:num) IN domain (ssa:num spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `ssa_locals_rel na ssa (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def] THEN
    UNDISCH_TAC `wl_get_var a0 (st:(A,C,FFI)wl_state) = SOME (wl_Word w)` THEN
    REWRITE_TAC[wl_get_var_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wl_Alloc a0 (p0,p1):(A)wl_prog`; `st:(A,C,FFI)wl_state`;
                 `rcst2:(A,C,FFI)wl_state`; `option_lookup (ssa1:num spt)`;
                 `sptree_union p0 p1:num_set`; `[]:(num_set#num_set)list`] evaluate_apply_colour) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[colouring_ok_def; get_live_def; get_writes_def; LET_DEF; LET_END_DEF] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND; union_LN] THEN
      SUBGOAL_THEN `INJ (option_lookup ssa1) (a0 INSERT set_of_list (ls:num list)) (:num)`
        ASSUME_TAC THENL
       [MATCH_MP_TAC WALLOCPAUX_lnvrm_INJ THEN
        MAP_EVERY EXISTS_TAC [`ssa:num spt`; `na:num`; `mov1:(A)wl_prog`; `na1:num`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC INJ_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`a0 INSERT set_of_list (ls:num list)`; `(:num)`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL; domain_insert; domain_union] THEN SET_TAC[];
      EXPAND_TAC "rcst2" THEN UNDISCH_TAC `word_state_eq_rel st (rcst1:(A,C,FFI)wl_state)` THEN
      REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM];
      EXPAND_TAC "rcst2" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
      MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_strong_phy THEN EXISTS_TAC `na1:num` THEN
      ASM_REWRITE_TAC[WALLOCPAUX_PHY_REGS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_var 2 (rcst2:(A,C,FFI)wl_state) = SOME (wl_Word (w:A word)) /\
                wl_get_var (option_lookup ssa1 a0) rcst2 = SOME (wl_Word w)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wl_get_var (option_lookup ssa1 a0) (rcst1:(A,C,FFI)wl_state) =
                 SOME (wl_Word (w:A word))` THEN
    EXPAND_TAC "rcst2" THEN
    REWRITE_TAC[wl_get_var_def; wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `perm:num->num->num`) THEN EXISTS_TAC `perm:num->num->num` THEN
  POP_ASSUM MP_TAC THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (wl_Alloc a0 (p0,p1):(A)wl_prog,
                          wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state))`
    [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `res = SOME (wl_Error:(A)wl_result)` THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (apply_colour (option_lookup ssa1)
                          (wl_Alloc a0 (p0,p1):(A)wl_prog), rcst2:(A,C,FFI)wl_state)`
    [`res3:((A)wl_result)option`; `rcst3:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wl_evaluate (wl_Alloc 2 (apply_nummaps_key (option_lookup ssa1) (p0,p1)):(A)wl_prog,
                  rcst2:(A,C,FFI)wl_state) = (res,rcst3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) =
        `(res:((A)wl_result)option,rcst3:(A,C,FFI)wl_state)` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[apply_colour_def] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[option_CASE; WALLOCPAUX_word_loc_CASE];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_alloc (w:A word) (p0,p1) (wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state)) =
                (res,rst)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) =
        `(res:((A)wl_result)option,rst:(A,C,FFI)wl_state)` &&
        can (find_term (fun t -> t = `perm:num->num->num`)) (concl th)
      then MP_TAC th else NO_TAC) THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[WALLOCPAUX_get_var_permute; option_CASE; WALLOCPAUX_word_loc_CASE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `res:((A)wl_result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r:(A)wl_result` SUBST_ALL_TAC)) THENL
   [(MP_TAC(ISPECL [`wl_Alloc 2 (apply_nummaps_key (option_lookup ssa1) (p0,p1)):(A)wl_prog`;
                   `mov2:(A)wl_prog`; `rcst2:(A,C,FFI)wl_state`; `rcst3:(A,C,FFI)wl_state`]
           IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_alloc"
         with Failure _ -> false)
      then ASSUME_TAC(MATCH_MP WALLOCPAUX_alloc_NONE_domain th) else NO_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
    MP_TAC(ISPECL [`rst:(A,C,FFI)wl_state`; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`;
                   `na1 + 2`; `ls:num list`; `rcst3:(A,C,FFI)wl_state`]
           list_next_var_rename_move_preserve) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [(MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_cut2 THEN
        ASM_REWRITE_TAC[domain_union] THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `a0 < na /\ ALL (\x. x < na) (MAP FST (toAList (p0:num_set))) /\
               ALL (\x. x < na) (MAP FST (toAList (p1:num_set)))` THEN
  UNDISCH_TAC `na + 2 <= na1` THEN
  REWRITE_TAC[GSYM ALL_MEM; toAList_domain; IN_UNION] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);
        ASM_REWRITE_TAC[SUBSET_REFL];
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
        EXISTS_TAC `na1:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov2:(A)wl_prog,rcst3:(A,C,FFI)wl_state)`
      [`r4:((A)wl_result)option`; `rcst4:(A,C,FFI)wl_state`] THEN
    REWRITE_TAC[pair_CASE; option_CASE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);
    (FIRST_ASSUM(fun th -> if is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_alloc"
         with Failure _ -> false)
      then MP_TAC(MATCH_MP WALLOCPAUX_alloc_SOME th) else NO_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`wl_Alloc 2 (apply_nummaps_key (option_lookup ssa1) (p0,p1)):(A)wl_prog`;
                   `mov2:(A)wl_prog`; `rcst2:(A,C,FFI)wl_state`; `NotEnoughSpace:(A)wl_result`;
                   `rcst3:(A,C,FFI)wl_state`] WALLOCPAUX_seq_SOME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; WALLOCPAUX_wl_result_CASE]) THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE])]);;

(* ------------------------------------------------------------------------- *)
(* ssa_cc_trans_correct, case Install (HOL4 line 9710)                       *)
(* ------------------------------------------------------------------------- *)

(* an ssa relation gives a strong relation under option_lookup, also after  *)
(* writes to physical registers of the target                                *)

let WALLOCPAUX_ssa_locals_rel_strong_gen = prove
 (`!na ssa (stl:A spt) cstl cstl' s.
     ssa_locals_rel na ssa stl cstl /\ ssa_map_ok na ssa /\
     (!x. ~is_phy_var x ==> lookup x cstl' = lookup x cstl)
     ==> strong_locals_rel (option_lookup ssa) s stl cstl'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_locals_rel_def; ssa_map_ok_def; strong_locals_rel_def] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `u:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `u:A`] o check (fun th ->
    can (find_term (fun t -> t = `stl:A spt`)) (concl th))) THEN
  ASM_REWRITE_TAC[domain_lookup] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `z:num`) MP_TAC) THEN
  ASM_REWRITE_TAC[THE_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
  SUBGOAL_THEN `~is_phy_var z` (fun th -> ASM_SIMP_TAC[th]) THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_lookup_insert_phy = prove
 (`!x k (v:A) t. ~is_phy_var x /\ is_phy_var k ==> lookup x (insert k v t) = lookup x t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[]);;

let WALLOCPAUX_sct_Install = prove
 (`!a0 a1 a2 a3 a4.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Install a0 a1 a2 a3 a4:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Install a0 a1 a2 a3 a4:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  SUBGOAL_THEN `?p0 p1. a4 = (p0:num_set,p1:num_set)`
    (X_CHOOSE_THEN `p0:num_set` (X_CHOOSE_THEN `p1:num_set` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_name_def; FST; SND]) THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; COND_CASE_EQ; case_eq "list"] THEN
  SUBGOAL_THEN `?env. (a:((A)word_loc)spt) = env`
    (X_CHOOSE_THEN `env:((A)word_loc)spt` SUBST_ALL_TAC) THENL [MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `ls = MAP FST (toAList (sptree_union p0 p1:num_set))` THEN
  SUBGOAL_THEN `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[set_MAP_FST_toAList_domain; domain_union];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (ls:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  REWRITE_TAC[ssa_cc_trans_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (ssa:num spt) (na + 2) ls:(A)wl_prog#num spt#num`
    [`mov1:(A)wl_prog`; `ssa1:num spt`; `na1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (insert a0 (na1 + 2)
                          (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))) ((na1 + 2) + 4) ls:(A)wl_prog#num spt#num`
    [`mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  SUBGOAL_THEN `domain (p0:num_set) SUBSET domain (wl_state_locals (st:(A,C,FFI)wl_state)) /\
                domain (p1:num_set) SUBSET domain (wl_state_locals st)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wl_cut_env (p0,p1) (wl_state_locals (st:(A,C,FFI)wl_state)) =
                 SOME (env:((A)word_loc)spt)` THEN
    REWRITE_TAC[WALLOCPAUX_cut_env_SOME] THEN STRIP_TAC THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP cut_envs_domain_SUBSET);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `ssa:num spt`; `na + 2`; `ls:num list`;
                 `cst:(A,C,FFI)wl_state`] list_next_var_rename_move_preserve) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[UNION_SUBSET];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov1:(A)wl_prog,cst:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `rcst1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `na + 2 <= na1 /\ is_stack_var na1 /\ ssa_map_ok na1 (ssa1:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`; `mov1:(A)wl_prog`;
                   `ssa1:num spt`; `na1:num`] list_next_var_rename_move_props_2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ssa:num spt`; `na + 2`; `ls:num list`; `mov1:(A)wl_prog`;
                 `ssa1:num spt`; `na1:num`] WALLOCPAUX_lnvrm_names) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_NEQ_TAC THEN
  SUBGOAL_THEN `!X. wl_evaluate (wl_Seq mov1 (wl_Seq (wl_Move 1 [2,option_lookup ssa1 a0;
                        4,option_lookup ssa1 a1]) X), cst) =
                    wl_evaluate (X:(A)wl_prog, wl_state_locals_fupd (K (insert 2 (wl_Word (a:A word))
                       (insert 4 (wl_Word (a':A word)) (wl_state_locals rcst1)))) (rcst1:(A,C,FFI)wl_state))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`mov1:(A)wl_prog`;
                   `wl_Seq (wl_Move 1 [2,option_lookup ssa1 a0; 4,option_lookup ssa1 a1]) X:(A)wl_prog`;
                   `cst:(A,C,FFI)wl_state`; `rcst1:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; ARITH_EQ] THEN
    ASM_REWRITE_TAC[option_CASE; wl_set_vars_def; alist_insert_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a0:num) IN domain (ssa:num spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `ssa_locals_rel na ssa (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def] THEN
    UNDISCH_TAC `wl_get_var a0 (st:(A,C,FFI)wl_state) = SOME (wl_Word (a:A word))` THEN
    REWRITE_TAC[wl_get_var_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`option_lookup (ssa1:num spt)`; `(p0:num_set,p1:num_set)`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`; `env:((A)word_loc)spt`;
                 `insert 2 (wl_Word (a:A word)) (insert 4 (wl_Word (a':A word))
                    (wl_state_locals (rcst1:(A,C,FFI)wl_state)))`] cut_env_lemma) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INJ_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`a0 INSERT set_of_list (ls:num list)`; `(:num)`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC WALLOCPAUX_lnvrm_INJ THEN
        MAP_EVERY EXISTS_TAC [`ssa:num spt`; `na:num`; `mov1:(A)wl_prog`; `na1:num`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[ASSUME `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`] THEN
        SET_TAC[]];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_strong_gen THEN
      MAP_EVERY EXISTS_TAC [`na1:num`; `wl_state_locals (rcst1:(A,C,FFI)wl_state)`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[WALLOCPAUX_lookup_insert_phy; WALLOCPAUX_PHY_REGS]];
    ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `env2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (wl_Install 2 4 (option_lookup ssa1 a2) (option_lookup ssa1 a3)
       (apply_nummaps_key (option_lookup ssa1) (p0,p1)):(A)wl_prog,
       wl_state_locals_fupd (K (insert 2 (wl_Word (a:A word)) (insert 4 (wl_Word (a':A word))
         (wl_state_locals rcst1)))) (rcst1:(A,C,FFI)wl_state))`
    [`r3:((A)wl_result)option`; `rcst3:(A,C,FFI)wl_state`] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      rhs(concl th) = `(r3:((A)wl_result)option,rcst3:(A,C,FFI)wl_state)`
    then MP_TAC(ONCE_REWRITE_RULE[wl_evaluate_def] th) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASM_REWRITE_TAC([wl_state_INFO.ri_accfupds; K_THM; option_CASE; pair_CASE; wl_get_var_def;
                   lookup_insert; ARITH_EQ; LET_DEF; LET_END_DEF] @ WALLOCPAUX_INST_CASES) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC([wl_state_INFO.ri_accfupds; K_THM; option_CASE; pair_CASE; wl_get_var_def;
                   lookup_insert; ARITH_EQ; LET_DEF; LET_END_DEF] @ WALLOCPAUX_INST_CASES) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" &&
           can (find_term (fun t -> try fst(dest_const t) = "wl_Install" with Failure _ -> false))
             (lhs(concl th)) with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th] else NO_TAC) THEN
  (fun (asl,w as g) ->
     let tm = find_term (fun t -> try fst(dest_const(rator t)) = "wl_evaluate" &&
                 fst(dest_const(fst(strip_comb(fst(dest_pair(rand t)))))) = "wl_Seq"
               with Failure _ -> false) w in
     ABBREV_TAC (mk_eq(`ts3:(A,C,FFI)wl_state`, snd(dest_pair(rand tm)))) g) THEN
  SUBGOAL_THEN `wl_state_locals (ts3:(A,C,FFI)wl_state) = insert 2 (wl_Loc x 0) env2`
    ASSUME_TAC THENL
   [EXPAND_TAC "ts3" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Move 1 [na1 + 2,2]:(A)wl_prog, ts3:(A,C,FFI)wl_state) =
                (NONE, wl_set_vars [na1 + 2] [wl_Loc x 0] ts3)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; wl_get_var_def; lookup_insert;
                    option_CASE];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" &&
           can (find_term (fun t -> try fst(dest_const t) = "wl_Move" with Failure _ -> false))
             (lhs(concl th)) with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th] else NO_TAC) THEN
  (fun (asl,w as g) ->
     let wser = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "word_state_eq_rel"
                                    with Failure _ -> false) w in
     let src = rand(rator wser) in
     MP_TAC(ISPECL [src; `insert a0 (na1 + 2) (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))`;
                    `(na1 + 2) + 4`; `ls:num list`;
                    `wl_set_vars [na1 + 2] [wl_Loc x 0] (ts3:(A,C,FFI)wl_state)`]
            list_next_var_rename_move_preserve) g) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_set_vars_def; alist_insert_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    SUBGOAL_THEN `ssa_map_ok (na1 + 2) (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
      EXISTS_TAC `na1:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ssa_locals_rel_set_var THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ssa_locals_rel_ignore_insert THEN
        ASM_REWRITE_TAC[WALLOCPAUX_PHY_REGS] THEN
        MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_cut2 THEN
        ASM_REWRITE_TAC[domain_union] THEN CONJ_TAC THENL
         [SET_TAC[];
          UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p0:num_set)))` THEN
          UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p1:num_set)))` THEN
          UNDISCH_TAC `na + 2 <= na1` THEN
          REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_union; IN_UNION] THEN
          REWRITE_TAC[GSYM IN_SET_OF_LIST; ASSUME `set_of_list (ls:num list) =
            domain (p0:num_set) UNION domain (p1:num_set)`; IN_UNION] THEN
          DISCH_THEN(LABEL_TAC "le") THEN DISCH_THEN(LABEL_TAC "h1") THEN
          DISCH_THEN(LABEL_TAC "h0") THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
          MATCH_MP_TAC(ARITH_RULE `z < na /\ na + 2 <= na1 ==> z < na1 + 2`) THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
             [REMOVE_THEN "h0" MATCH_MP_TAC; REMOVE_THEN "h1" MATCH_MP_TAC] THEN
            FIRST_ASSUM ACCEPT_TAC;
            REMOVE_THEN "le" ACCEPT_TAC]];
        UNDISCH_TAC `a0 < na` THEN UNDISCH_TAC `na + 2 <= na1` THEN ARITH_TAC];
      REWRITE_TAC[domain_insert; ASSUME `set_of_list (ls:num list) = domain (p0:num_set) UNION
                                           domain (p1:num_set)`;
                  ASSUME `domain (env:((A)word_loc)spt) = domain (p0:num_set) UNION
                                           domain (p1:num_set)`] THEN SET_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_extend THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `na1:num` is_stack_var_flip) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[convention_partitions];
      EXPAND_TAC "ts3" THEN
      REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM; fromAList_def] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov2:(A)wl_prog,
     wl_set_vars [na1 + 2] [wl_Loc x 0] (ts3:(A,C,FFI)wl_state))`
    [`r5:((A)wl_result)option`; `rcst5:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM]) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* ssa_cc_trans_correct, case FFI (HOL4 line 9868)                           *)
(* ------------------------------------------------------------------------- *)

(* rename the variables of the right-hand side of the assumption whose      *)
(* left-hand side satisfies pred (left to right) to the given names         *)

let WALLOCPAUX_RENAME_TAC (pred:term->bool) (names:string list) : tactic =
  fun (asl,w as g) ->
    let th = snd(find (fun (_,th) -> is_eq(concl th) && pred(lhs(concl th))) asl) in
    let rec vlr t = if is_var t then [t] else if is_comb t then vlr(rator t) @ vlr(rand t)
                    else [] in
    let rec uniq l = match l with [] -> [] | h::t -> h :: uniq (filter ((<>) h) t) in
    let vs = uniq (vlr (rhs(concl th))) in
    let k = min (length names) (length vs) in
    let pairs = zip (fst(chop_list k vs)) (fst(chop_list k names)) in
    MAP_EVERY (fun (v,n) ->
      let v' = mk_var(n,type_of v) in
      SUBGOAL_THEN (mk_exists(v',mk_eq(v,v'))) (X_CHOOSE_THEN v' SUBST_ALL_TAC) THENL
       [MESON_TAC[]; ALL_TAC]) pairs g;;

let WALLOCPAUX_LHS_IS (c:string) (args:term list) (t:term) : bool =
  try let f,xs = strip_comb t in
      fst(dest_const f) = c &&
      (args = [] || (length xs >= length args && fst(chop_list (length args) xs) = args))
  with Failure _ -> false;;

let WALLOCPAUX_sct_FFI = prove
 (`!a0 a1 a2 a3 a4 a5.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_FFI a0 a1 a2 a3 a4 a5:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_FFI a0 a1 a2 a3 a4 a5:(A)wl_prog)`,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN
  SUBGOAL_THEN `?p0 p1. a5 = (p0:num_set,p1:num_set)`
    (X_CHOOSE_THEN `p0:num_set` (X_CHOOSE_THEN `p1:num_set` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_name_def; FST; SND]) THEN
  EXISTS_TAC `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
  WALLOCPAUX_EAC_SRC_TAC THEN
  GVS[option_case_eq; pair_case_eq; case_eq "word_loc"; COND_CASE_EQ; case_eq "list";
      case_eq "ffi_result"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "wl_get_var" [`a2:num`]) ["w"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "wl_get_var" [`a1:num`]) ["w2"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "wl_get_var" [`a4:num`]) ["w3"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "wl_get_var" [`a3:num`]) ["w4"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "wl_cut_env" []) ["env"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "read_bytearray" [`w2:A word`]) ["bytes"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "read_bytearray" [`w4:A word`]) ["bytes2"] THEN
  WALLOCPAUX_RENAME_TAC (WALLOCPAUX_LHS_IS "call_FFI" []) ["ffi_r1"; "ffi_r2"] THEN
  (ABBREV_TAC `ls = MAP FST (toAList (sptree_union p0 p1:num_set))` THEN
  SUBGOAL_THEN `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[set_MAP_FST_toAList_domain; domain_union];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (ls:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (ssa:num spt) (na + 2) ls:(A)wl_prog#num spt#num`
    [`mov1:(A)wl_prog`; `ssa1:num spt`; `na1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))
                          (na1 + 2) ls:(A)wl_prog#num spt#num`
    [`mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  SUBGOAL_THEN `domain (p0:num_set) SUBSET domain (wl_state_locals (st:(A,C,FFI)wl_state)) /\
                domain (p1:num_set) SUBSET domain (wl_state_locals st)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wl_cut_env (p0,p1) (wl_state_locals (st:(A,C,FFI)wl_state)) =
                 SOME (env:((A)word_loc)spt)` THEN
    REWRITE_TAC[WALLOCPAUX_cut_env_SOME] THEN STRIP_TAC THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP cut_envs_domain_SUBSET);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `ssa:num spt`; `na + 2`; `ls:num list`;
                 `cst:(A,C,FFI)wl_state`] list_next_var_rename_move_preserve) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[UNION_SUBSET];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov1:(A)wl_prog,cst:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `rcst1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `na + 2 <= na1 /\ is_stack_var na1 /\ ssa_map_ok na1 (ssa1:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`; `mov1:(A)wl_prog`;
                   `ssa1:num spt`; `na1:num`] list_next_var_rename_move_props_2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ssa:num spt`; `na + 2`; `ls:num list`; `mov1:(A)wl_prog`;
                 `ssa1:num spt`; `na1:num`] WALLOCPAUX_lnvrm_names) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  WALLOCPAUX_SCT_GETVAR_TAC THEN WALLOCPAUX_SCT_NEQ_TAC) THEN
  (SUBGOAL_THEN `!X. wl_evaluate (wl_Seq mov1 (wl_Seq (wl_Move 1 [2,option_lookup ssa1 a1;
                        4,option_lookup ssa1 a2; 6,option_lookup ssa1 a3; 8,option_lookup ssa1 a4]) X),
                        cst) =
                    wl_evaluate (X:(A)wl_prog, wl_state_locals_fupd (K (insert 2 (wl_Word (w2:A word))
                       (insert 4 (wl_Word (w:A word)) (insert 6 (wl_Word (w4:A word))
                       (insert 8 (wl_Word (w3:A word)) (wl_state_locals rcst1)))))) (rcst1:(A,C,FFI)wl_state))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`mov1:(A)wl_prog`;
                   `wl_Seq (wl_Move 1 [2,option_lookup ssa1 a1; 4,option_lookup ssa1 a2;
                      6,option_lookup ssa1 a3; 8,option_lookup ssa1 a4]) X:(A)wl_prog`;
                   `cst:(A,C,FFI)wl_state`; `rcst1:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; ARITH_EQ] THEN
    ASM_REWRITE_TAC[option_CASE; wl_set_vars_def; alist_insert_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a1:num) IN domain (ssa:num spt)` ASSUME_TAC THENL
   [UNDISCH_TAC `ssa_locals_rel na ssa (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def] THEN
    UNDISCH_TAC `wl_get_var a1 (st:(A,C,FFI)wl_state) = SOME (wl_Word (w2:A word))` THEN
    REWRITE_TAC[wl_get_var_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`option_lookup (ssa1:num spt)`; `(p0:num_set,p1:num_set)`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`; `env:((A)word_loc)spt`;
                 `insert 2 (wl_Word (w2:A word)) (insert 4 (wl_Word (w:A word))
                    (insert 6 (wl_Word (w4:A word)) (insert 8 (wl_Word (w3:A word))
                    (wl_state_locals (rcst1:(A,C,FFI)wl_state)))))`] cut_env_lemma) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INJ_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`a1 INSERT set_of_list (ls:num list)`; `(:num)`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC WALLOCPAUX_lnvrm_INJ THEN
        MAP_EVERY EXISTS_TAC [`ssa:num spt`; `na:num`; `mov1:(A)wl_prog`; `na1:num`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[ASSUME `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`] THEN
        SET_TAC[]];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_strong_gen THEN
      MAP_EVERY EXISTS_TAC [`na1:num`; `wl_state_locals (rcst1:(A,C,FFI)wl_state)`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[WALLOCPAUX_lookup_insert_phy; WALLOCPAUX_PHY_REGS]];
    ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `env2:((A)word_loc)spt` STRIP_ASSUME_TAC) THEN
  WALLOCPAUX_SCT_EXPAND_TAC THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (wl_FFI a0 2 4 6 8
       (apply_nummaps_key (option_lookup ssa1) (p0,p1)):(A)wl_prog,
       wl_state_locals_fupd (K (insert 2 (wl_Word (w2:A word)) (insert 4 (wl_Word (w:A word))
         (insert 6 (wl_Word (w4:A word)) (insert 8 (wl_Word (w3:A word))
         (wl_state_locals rcst1)))))) (rcst1:(A,C,FFI)wl_state))`
    [`r3:((A)wl_result)option`; `rcst3:(A,C,FFI)wl_state`] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      rhs(concl th) = `(r3:((A)wl_result)option,rcst3:(A,C,FFI)wl_state)`
    then MP_TAC(ONCE_REWRITE_RULE[wl_evaluate_def] th) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  ASM_REWRITE_TAC([wl_state_INFO.ri_accfupds; K_THM; option_CASE; pair_CASE; wl_get_var_def;
                   lookup_insert; ARITH_EQ; LET_DEF; LET_END_DEF] @ WALLOCPAUX_INST_CASES) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC([wl_state_INFO.ri_accfupds; K_THM; option_CASE; pair_CASE; wl_get_var_def;
                   lookup_insert; ARITH_EQ; LET_DEF; LET_END_DEF] @ WALLOCPAUX_INST_CASES @
                  [(case_info_of_tyname "ffi_result").ci_def]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THENL
  [(FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" &&
           can (find_term (fun t -> try fst(dest_const t) = "wl_FFI" with Failure _ -> false))
             (lhs(concl th)) with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP IL2AUX_evaluate_Seq_NONE th] else NO_TAC)) THEN
   ((fun (asl,w as g) ->
     let wser = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "word_state_eq_rel"
                                    with Failure _ -> false) w in
     let src = rand(rator wser) in
     let ev = find_term (fun t -> try fst(dest_const(rator t)) = "wl_evaluate" &&
                                      fst(dest_pair(rand t)) = `mov2:(A)wl_prog`
                                  with Failure _ -> false) w in
     let tgt = snd(dest_pair(rand ev)) in
     MP_TAC(ISPECL [src; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`;
                    `na1 + 2`; `ls:num list`; tgt]
            list_next_var_rename_move_preserve) g) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_cut2 THEN
      ASM_REWRITE_TAC[domain_union] THEN CONJ_TAC THENL
       [SET_TAC[];
        UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p0:num_set)))` THEN
        UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p1:num_set)))` THEN
        UNDISCH_TAC `na + 2 <= na1` THEN
        REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_union; IN_UNION] THEN
        REWRITE_TAC[GSYM IN_SET_OF_LIST; ASSUME `set_of_list (ls:num list) =
          domain (p0:num_set) UNION domain (p1:num_set)`; IN_UNION] THEN
        DISCH_THEN(LABEL_TAC "le") THEN DISCH_THEN(LABEL_TAC "h1") THEN
        DISCH_THEN(LABEL_TAC "h0") THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
        MATCH_MP_TAC(ARITH_RULE `z < na /\ na + 2 <= na1 ==> z < na1 + 2`) THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
           [REMOVE_THEN "h0" MATCH_MP_TAC; REMOVE_THEN "h1" MATCH_MP_TAC] THEN
          FIRST_ASSUM ACCEPT_TAC;
          REMOVE_THEN "le" ACCEPT_TAC]];
      REWRITE_TAC[ASSUME `set_of_list (ls:num list) = domain (p0:num_set) UNION
                                           domain (p1:num_set)`;
                  ASSUME `domain (env:((A)word_loc)spt) = domain (p0:num_set) UNION
                                           domain (p1:num_set)`] THEN SET_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
      EXISTS_TAC `na1:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  (fun (asl,w as g) ->
     let ev = find_term (fun t -> try fst(dest_const(rator t)) = "wl_evaluate" &&
                                      fst(dest_pair(rand t)) = `mov2:(A)wl_prog`
                                  with Failure _ -> false) w in
     WALLOCPAUX_TUPLE_TAC ev [`r5:((A)wl_result)option`; `rcst5:(A,C,FFI)wl_state`] g) THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_state_INFO.ri_accfupds; K_THM]) THEN ASM_REWRITE_TAC[]);
   FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" &&
           can (find_term (fun t -> try fst(dest_const t) = "wl_FFI" with Failure _ -> false))
             (lhs(concl th)) with Failure _ -> false)
    then REWRITE_TAC[MATCH_MP WALLOCPAUX_seq_SOME th] else NO_TAC) THEN
  REWRITE_TAC[pair_CASE] THEN
  REWRITE_TAC[word_state_eq_rel_def; wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[]]);;

(* case analysis of the handler pair h, hh from their correspondence *)

let WALLOCPAUX_HMATCH_TAC : tactic =
  FIRST_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "option_CASE" &&
        free_in `hh:(num#(A)wl_prog#num#num)option` (concl th) &&
        free_in `h:(num#(A)wl_prog#num#num)option` (concl th) &&
        not (free_in `Q:((A)wl_result)option->(A,C,FFI)wl_state->((A)wl_result)option->(A,C,FFI)wl_state->bool` (concl th))
    with Failure _ -> false)) THEN
  SPEC_TAC(`hh:(num#(A)wl_prog#num#num)option`, `hh:(num#(A)wl_prog#num#num)option`) THEN
  SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE; option_DISTINCT;
              option_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];;

(* a returning call simulated by a call with renamed arguments, results,  *)
(* cut sets (under f) and continuations; Q is the relation of the results   *)
(* (generalises the Call case of evaluate_apply_colour)                      *)

let WALLOCPAUX_call_sim = prove
 (CASE_TERM
  `!(st:(A,C,FFI)wl_state) (cst:(A,C,FFI)wl_state) (f:num->num)
    (n:num list) (n':num list) (p0:num_set) (p1:num_set) (rh:(A)wl_prog) (rh':(A)wl_prog)
    (l1:num) (l2:num) (dest:num option) (args:num list) (args':num list)
    (h:(num#(A)wl_prog#num#num)option) (hh:(num#(A)wl_prog#num#num)option)
    (Q:((A)wl_result)option->(A,C,FFI)wl_state->((A)wl_result)option->(A,C,FFI)wl_state->bool).
     word_state_eq_rel st cst /\
     (!xs. wl_get_vars args st = SOME xs ==> wl_get_vars args' cst = SOME xs) /\
     LENGTH args' = LENGTH args /\
     ALL_DISTINCT n' /\ LENGTH n' = LENGTH n /\
     INJ f (domain p0 UNION domain p1) (:num) /\
     strong_locals_rel f (domain p0 UNION domain p1) (wl_state_locals st) (wl_state_locals cst) /\
     (match h with
        NONE -> hh = NONE
      | SOME (w,hp,k1,k2) ->
          (match hh with NONE -> F | SOME (w',hp',k1',k2') -> k1' = k1 /\ k2' = k2)) /\
     (!r s t. word_state_eq_rel s t /\ wl_state_locals s = wl_state_locals t /\
              ((?x y. r = wl_Exception x y) \/ r = wl_TimeOut \/ r = NotEnoughSpace \/
               (?e. r = wl_FinalFFI e))
              ==> Q (SOME r) s (SOME r) t) /\
     (!s1 t1 ys.
        word_state_eq_rel s1 t1 /\
        strong_locals_rel f (:num) (wl_state_locals s1) (wl_state_locals t1) /\
        domain (wl_state_locals s1) = domain p0 UNION domain p1 /\
        domain (wl_state_locals t1) = IMAGE f (domain p0) UNION IMAGE f (domain p1) /\
        LENGTH ys = LENGTH n
        ==> ?perm. let (r,s) = wl_evaluate (rh, wl_state_permute_fupd (K perm) (wl_set_vars n ys s1)) in
                   if r = SOME wl_Error then T else
                   let (r',t) = wl_evaluate (rh', wl_set_vars n' ys t1) in Q r s r' t) /\
     (match h with
        NONE -> T
      | SOME (w,hp,k1,k2) ->
          (match hh with
             NONE -> T
           | SOME (w',hp',k1',k2') ->
               !s1 t1 y.
                 word_state_eq_rel s1 t1 /\
                 strong_locals_rel f (:num) (wl_state_locals s1) (wl_state_locals t1) /\
                 domain (wl_state_locals s1) = domain p0 UNION domain p1 /\
                 domain (wl_state_locals t1) = IMAGE f (domain p0) UNION IMAGE f (domain p1)
                 ==> ?perm. let (r,s) = wl_evaluate (hp, wl_state_permute_fupd (K perm) (wl_set_var w y s1)) in
                            if r = SOME wl_Error then T else
                            let (r',t) = wl_evaluate (hp', wl_set_var w' y t1) in Q r s r' t))
     ==> ?perm. let (r,s) = wl_evaluate (wl_Call (SOME (n,(p0,p1),rh,l1,l2)) dest args h,
                                          wl_state_permute_fupd (K perm) st) in
                if r = SOME wl_Error then T else
                let (r',t) = wl_evaluate (wl_Call (SOME (n',apply_nummaps_key f (p0,p1),rh',l1,l2))
                                            dest args' hh, cst) in
                  Q r s r' t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in let k = length cs in
    MAP_EVERY ASSUME_TAC (fst(chop_list (k - 3) cs)) THEN
    LABEL_TAC "cp" (el (k - 3) cs) THEN LABEL_TAC "ihr" (el (k - 2) cs) THEN
    LABEL_TAC "ihh" (el (k - 1) cs)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[word_state_eq_rel_def] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "word_state_eq_rel" with Failure _ -> false)) THEN
  SUBGOAL_THEN `(args':num list) = [] <=> (args:num list) = []` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  let srcerr thl =
    EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_permute_same] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC([option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; add_ret_loc_def;
                     WALLOCPAUX_wl_result_CASE] @ thl) in
  MP_TAC(ISPEC `wl_get_vars args (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xs:((A)word_loc)list` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THENL [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_find_code (dest:num option) (CONS (wl_Loc l1 l2) (xs:((A)word_loc)list))
                  (wl_state_code (st:(A,C,FFI)wl_state)) (wl_state_stack_size st)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `fc:((A)word_loc)list#(A)wl_prog#(num)option` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?args1 prog ss. fc = (args1:((A)word_loc)list,prog:(A)wl_prog,ss:(num)option)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_CASES_TAC `domain (p0:num_set) = {} \/ ~ALL_DISTINCT (n:num list)` THENL
   [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `cut_envs (p0:num_set,p1:num_set) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `xx:((A)word_loc)spt#((A)word_loc)spt` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. xx = (x1:((A)word_loc)spt,x2:((A)word_loc)spt)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun t -> t = `args':num list`)) (concl th)
    then ASSUME_TAC(MATCH_MP th (ASSUME `wl_get_vars args (st:(A,C,FFI)wl_state) =
                                         SOME (xs:((A)word_loc)list)`)) else NO_TAC) THEN
  MP_TAC(ISPECL [`f:num->num`; `p0:num_set`; `p1:num_set`;
                 `wl_state_locals (st:(A,C,FFI)wl_state)`; `x1:((A)word_loc)spt`;
                 `x2:((A)word_loc)spt`; `wl_state_locals (cst:(A,C,FFI)wl_state)`]
                cut_envs_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    ((MATCH_MP_TAC word_allocProof_INJ_less THEN
      EXISTS_TAC `domain (p0:num_set) UNION domain (p1:num_set)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]) ORELSE
     (MATCH_MP_TAC strong_locals_rel_subset THEN
      EXISTS_TAC `domain (p0:num_set) UNION domain (p1:num_set)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]));
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:((A)word_loc)spt` (X_CHOOSE_THEN `y2:((A)word_loc)spt`
    STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `~(domain (apply_nummap_key (f:num->num) (p0:num_set)) = {})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[apply_nummap_key_domain; IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN SIMP[] THEN
  ASM_REWRITE_TAC[add_ret_loc_def; option_CASE; pair_CASE; bad_dest_args_def;
                  nummaps_to_nummap] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bad_dest_args_def]) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  let push_tac s0 c0 tp =
    MP_TAC(ISPECL [s0; c0; `x2:((A)word_loc)spt`; `y2:((A)word_loc)spt`;
                   `x1:((A)word_loc)spt`; `y1:((A)word_loc)spt`; `f:num->num`;
                   `h:(num#(A)wl_prog#num#num)option`; `hh:(num#(A)wl_prog#num#num)option`;
                   tp] push_env_s_val_eq) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] in
  ASM_CASES_TAC `wl_state_clock (st:(A,C,FFI)wl_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [push_tac `st:(A,C,FFI)wl_state` `cst:(A,C,FFI)wl_state` `wl_state_permute (cst:(A,C,FFI)wl_state)` THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num->num->num` (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `P:num->num->num` THEN
    REWRITE_TAC([pair_CASE; option_INJ; option_CASE; WALLOCPAUX_wl_result_CASE] @
                WALLOCPAUX_wl_result_distinct) THEN
    USE_THEN "cp" MATCH_MP_TAC THEN REWRITE_TAC WALLOCPAUX_wl_result_distinct THEN
    CONJ_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def; wl_flush_state_def; wl_state_INFO.ri_accfupds;
                  K_THM] THEN
      ASM_REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                      push_env_stack_max_eq] THEN
      FIRST_ASSUM(fun th -> if (try fst(dest_const(fst(strip_comb(concl th)))) = "s_val_eq"
                                with Failure _ -> false)
                            then REWRITE_TAC[MATCH_MP s_val_eq_stack_size th] else NO_TAC);
      REWRITE_TAC[wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM]];
    ALL_TAC] THEN
  push_tac `wl_dec_clock (st:(A,C,FFI)wl_state)` `wl_dec_clock (cst:(A,C,FFI)wl_state)`
    `\n. wl_state_permute (cst:(A,C,FFI)wl_state) (n + 1)` THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num->num->num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  WALLOCPAUX_TUPLE_TAC
    `env_to_list (y2:((A)word_loc)spt) (wl_state_permute (wl_dec_clock (cst:(A,C,FFI)wl_state)))`
    [`lsA:(num#(A)word_loc)list`; `pA:num->num->num`] THEN
  WALLOCPAUX_TUPLE_TAC `env_to_list (x2:((A)word_loc)spt) P`
    [`lsB:(num#(A)word_loc)list`; `pB:num->num->num`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\n. (P:num->num->num) (n + 1)) =
                (\n. wl_state_permute (cst:(A,C,FFI)wl_state) (n + 1))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "env_to_list" &&
           rand(lhs(concl th)) = `P:num->num->num` with Failure _ -> false))) THEN
    REWRITE_TAC[env_to_list_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[WALLOCPAUX_call_env_permute] THEN
  WALLOCPAUX_EX_REFINE_TAC `\n. if n = 0 then (P:num->num->num) 0 else perm2 (n - 1)`
    `perm2:num->num->num` THEN
  REWRITE_TAC[WALLOCPAUX_push_env_perm; WALLOCPAUX_call_env_permute] THEN
  MP_TAC(ISPECL [`wl_dec_clock (st:(A,C,FFI)wl_state)`; `wl_dec_clock (cst:(A,C,FFI)wl_state)`;
                 `x1:((A)word_loc)spt`; `x2:((A)word_loc)spt`; `y1:((A)word_loc)spt`;
                 `y2:((A)word_loc)spt`; `h:(num#(A)wl_prog#num#num)option`;
                 `hh:(num#(A)wl_prog#num#num)option`; `P:num->num->num`;
                 `args1:((A)word_loc)list`; `ss:num option`] WALLOCPAUX_call_states) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    REWRITE_TAC[word_state_eq_rel_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `sc0 = wl_call_env args1 ss (wl_push_env (x1,x2) h
                     (wl_state_permute_fupd (K P) (wl_dec_clock (st:(A,C,FFI)wl_state))))` THEN
  ABBREV_TAC `tc0 = wl_call_env args1 ss (wl_push_env (y1,y2) hh
                     (wl_dec_clock (cst:(A,C,FFI)wl_state)))` THEN
  WALLOCPAUX_PERM_SWAP4_TAC `prog:(A)wl_prog` `sc0:(A,C,FFI)wl_state` THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE];
    ALL_TAC] THEN
  SUBGOAL_THEN `s_val_eq (wl_state_stack (sc0:(A,C,FFI)wl_state))
                  (wl_state_stack (tc0:(A,C,FFI)wl_state))`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sc0"; "tc0"] THEN
    REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `sc0:(A,C,FFI)wl_state`] wl_evaluate_stack_swap) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (prog:(A)wl_prog,sc0:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE; PAIR_MAP_THM; I_THM] THEN
  WALLOCPAUX_RESULT_CASES_TAC `r1:((A)wl_result)option` THEN
  let stop =
    STRIP_TAC THEN EXISTS_TAC `wl_state_permute (s1:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_permute_same] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_stack (tc0:(A,C,FFI)wl_state)` o
                  check (is_forall o concl)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC([pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE; option_INJ;
                 WALLOCPAUX_wser_refl] @ WALLOCPAUX_wl_result_distinct) THEN
    USE_THEN "cp" MATCH_MP_TAC THEN
    REWRITE_TAC([WALLOCPAUX_wser_refl; option_INJ] @ WALLOCPAUX_wl_result_distinct) THEN
    MESON_TAC[] in
  let result =
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `wl_state_stack (tc0:(A,C,FFI)wl_state)`))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `st3:((A)stack_frame)list` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    ASM_CASES_TAC `~((a0:(A)word_loc) = wl_Loc l1 l2) \/
                   ~(LENGTH (a1:((A)word_loc)list) = LENGTH (n:num list))` THEN
    ASM_REWRITE_TAC[pair_CASE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
    REWRITE_TAC[wl_pop_env_with_const] THEN
    MP_TAC(ISPEC `wl_pop_env (s1:(A,C,FFI)wl_state)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s1p:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; option_CASE; pair_CASE; WALLOCPAUX_wl_result_CASE] THEN
    let hoptS = CASE_TERM `match (h:(num#(A)wl_prog#num#num)option) with
                             NONE -> NONE
                           | SOME (w,hp,k1,k2) -> SOME (wl_state_handler (st:(A,C,FFI)wl_state),k1,k2)`
    and hoptT = CASE_TERM `match (hh:(num#(A)wl_prog#num#num)option) with
                             NONE -> NONE
                           | SOME (w,hp,k1,k2) -> SOME (wl_state_handler (cst:(A,C,FFI)wl_state),k1,k2)` in
    SUBGOAL_THEN (mk_eq(hoptT,hoptS)) ASSUME_TAC THENL
     [WALLOCPAUX_HMATCH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
    SUBGOAL_THEN (mk_eq(`wl_state_stack (sc0:(A,C,FFI)wl_state)`,
       list_mk_icomb "CONS" [list_mk_icomb "StackFrame"
         [`wl_state_locals_size (st:(A,C,FFI)wl_state)`; `toAList (x1:((A)word_loc)spt)`;
          `lsB:(num#(A)word_loc)list`; hoptS]; `wl_state_stack (st:(A,C,FFI)wl_state)`]))
      ASSUME_TAC THENL
     [EXPAND_TAC "sc0" THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; wl_dec_clock_def] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(`wl_state_stack (tc0:(A,C,FFI)wl_state)`,
       list_mk_icomb "CONS" [list_mk_icomb "StackFrame"
         [`wl_state_locals_size (st:(A,C,FFI)wl_state)`; `toAList (y1:((A)word_loc)spt)`;
          `lsA:(num#(A)word_loc)list`; hoptS]; `wl_state_stack (st:(A,C,FFI)wl_state)`]))
      ASSUME_TAC THENL
     [EXPAND_TAC "tc0" THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; wl_dec_clock_def] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    (fun (asl,w as g) ->
       let abbr v = concl(snd(find (fun (_,th) -> is_eq(concl th) && rhs(concl th) = v) asl)) in
       let push_s = rand(lhs(abbr `sc0:(A,C,FFI)wl_state`))
       and push_t = rand(lhs(abbr `tc0:(A,C,FFI)wl_state`)) in
       let ins t = rand t and bs t = rand(rator t) in
       (MP_TAC(ISPECL [`(x1:((A)word_loc)spt,x2:((A)word_loc)spt)`; bs push_s; ins push_s;
                       `s1:(A,C,FFI)wl_state`] push_env_pop_env_s_key_eq) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `s_key_eq (wl_state_stack (sc0:(A,C,FFI)wl_state))
                         (wl_state_stack (s1:(A,C,FFI)wl_state))` THEN
          EXPAND_TAC "sc0" THEN REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `n0:num option` (X_CHOOSE_THEN `l0:(num#(A)word_loc)list`
          (X_CHOOSE_THEN `ls0:((A)stack_frame)list` (X_CHOOSE_THEN `o0:(num#num#num)option`
          (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `y0:(A,C,FFI)wl_state` STRIP_ASSUME_TAC)))))) THEN
        MP_TAC(ISPECL [`(y1:((A)word_loc)spt,y2:((A)word_loc)spt)`; bs push_t; ins push_t;
                       `wl_state_stack_fupd (K st3) (s1:(A,C,FFI)wl_state)`]
                      push_env_pop_env_s_key_eq) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `s_key_eq (wl_state_stack (tc0:(A,C,FFI)wl_state)) st3` THEN
          EXPAND_TAC "tc0" THEN REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `n1:num option` (X_CHOOSE_THEN `l1':(num#(A)word_loc)list`
          (X_CHOOSE_THEN `ls1:((A)stack_frame)list` (X_CHOOSE_THEN `o1:(num#num#num)option`
          (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `t1p:(A,C,FFI)wl_state` STRIP_ASSUME_TAC))))))) g) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `wl_pop_env (s1:(A,C,FFI)wl_state) = SOME y0`)) THEN
    ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    MP_TAC(ISPECL [`f:num->num`; `x1:((A)word_loc)spt`; `y1:((A)word_loc)spt`;
                   `lsB:(num#(A)word_loc)list`; `lsA:(num#(A)word_loc)list`;
                   `s1:(A,C,FFI)wl_state`; `wl_state_stack_fupd (K st3) (s1:(A,C,FFI)wl_state)`;
                   `s1p:(A,C,FFI)wl_state`; `t1p:(A,C,FFI)wl_state`;
                   `wl_state_locals_size (st:(A,C,FFI)wl_state)`; hoptS;
                   `wl_state_stack (st:(A,C,FFI)wl_state)`;
                   `wl_state_stack (st:(A,C,FFI)wl_state)`] WALLOCPAUX_pop_env_rel) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC key_map_implies THEN FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPECL [`x2:((A)word_loc)spt`; `P:num->num->num`] env_to_list_keys) THEN
        ASM_REWRITE_TAC[pair_CASE] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        (MATCH_MP_TAC word_allocProof_INJ_less THEN
         EXISTS_TAC `domain (p0:num_set) UNION domain (p1:num_set)` THEN
         ASM_REWRITE_TAC[] THEN SET_TAC[]);
        ONCE_REWRITE_TAC[s_key_eq_sym] THEN
        UNDISCH_TAC `s_key_eq (wl_state_stack (sc0:(A,C,FFI)wl_state))
                       (wl_state_stack (s1:(A,C,FFI)wl_state))` THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[s_key_eq_sym] THEN
        UNDISCH_TAC `s_key_eq (wl_state_stack (tc0:(A,C,FFI)wl_state)) st3` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `domain (wl_state_locals (s1p:(A,C,FFI)wl_state)) =
                  domain (p0:num_set) UNION domain (p1:num_set) /\
                  domain (wl_state_locals (t1p:(A,C,FFI)wl_state)) =
                  IMAGE (f:num->num) (domain p0) UNION IMAGE f (domain p1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `domain (x2:((A)word_loc)spt) UNION domain (x1:((A)word_loc)spt) =
                     domain (wl_state_locals (s1p:(A,C,FFI)wl_state))`;
        UNDISCH_TAC `domain (y2:((A)word_loc)spt) UNION domain (y1:((A)word_loc)spt) =
                     domain (wl_state_locals (t1p:(A,C,FFI)wl_state))`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_stack (t1p:(A,C,FFI)wl_state) = wl_state_stack (s1p:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC s_val_and_key_eq THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[s_val_eq_sym] THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC s_key_eq_trans THEN
        EXISTS_TAC `wl_state_stack (st:(A,C,FFI)wl_state)` THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; ONCE_REWRITE_TAC[s_key_eq_sym] THEN FIRST_ASSUM ACCEPT_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_handler (t1p:(A,C,FFI)wl_state) =
                  wl_state_handler (s1p:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(concl th)))) = "option_CASE" &&
            free_in `t1p:(A,C,FFI)wl_state` (concl th) with Failure _ -> false)) THEN
      SPEC_TAC(`h:(num#(A)wl_prog#num#num)option`, `h:(num#(A)wl_prog#num#num)option`) THEN
      REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; option_CASE; pair_CASE;
                  wl_state_INFO.ri_accfupds; K_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY (fun t ->
      FIRST_ASSUM(fun th -> if concl th = t then STRIP_ASSUME_TAC(MATCH_MP wl_pop_env_const th)
                            else NO_TAC))
      [`wl_pop_env (s1:(A,C,FFI)wl_state) = SOME s1p`;
       `wl_pop_env (wl_state_stack_fupd (K st3) (s1:(A,C,FFI)wl_state)) = SOME t1p`] THEN
    SUBGOAL_THEN `word_state_eq_rel (s1p:(A,C,FFI)wl_state) (t1p:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def] THEN
      ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
      ALL_TAC] THEN
    REMOVE_THEN "ihr" (MP_TAC o SPECL [`s1p:(A,C,FFI)wl_state`; `t1p:(A,C,FFI)wl_state`;
                                       `a1:((A)word_loc)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `perm3:num->num->num` ASSUME_TAC) THEN
    EXISTS_TAC `perm3:num->num->num` THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_set_vars_with_const; option_CASE] THEN
    ASM_REWRITE_TAC[] in
  let exc_none =
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `hh:(num#(A)wl_prog#num#num)option`)) THEN
    REWRITE_TAC[option_CASE; pair_CASE] THEN
    SUBGOAL_THEN
     `wl_state_handler (sc0:(A,C,FFI)wl_state) = wl_state_handler (st:(A,C,FFI)wl_state) /\
      wl_state_stack sc0 = CONS (StackFrame (wl_state_locals_size st) (toAList x1) lsB NONE)
                             (wl_state_stack st) /\
      wl_state_stack (tc0:(A,C,FFI)wl_state) =
        CONS (StackFrame (wl_state_locals_size st) (toAList y1) lsA NONE) (wl_state_stack st)`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["sc0"; "tc0"] THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; WALLOCPAUX_push_env_permute_handler;
                  wl_dec_clock_def; option_CASE] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    SUBGOAL_THEN `wl_state_handler (st:(A,C,FFI)wl_state) < LENGTH (wl_state_stack st)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a < b + 1 /\ ~(a = b) ==> a < b`) THEN CONJ_TAC THENL
       [UNDISCH_TAC `wl_state_handler (sc0:(A,C,FFI)wl_state) < LENGTH (wl_state_stack sc0)` THEN
        ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        DISCH_TAC THEN
        UNDISCH_TAC `LASTN (wl_state_handler (sc0:(A,C,FFI)wl_state) + 1) (wl_state_stack sc0) =
                     CONS (StackFrame m e0 e (SOME nh)) ls` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `LENGTH (wl_state_stack (st:(A,C,FFI)wl_state)) + 1 =
                      LENGTH (CONS (StackFrame (wl_state_locals_size st) (toAList x1) lsB NONE)
                                   (wl_state_stack st))` SUBST1_TAC THENL
         [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC([LASTN_LENGTH_ID; CONS_11; option_DISTINCT] @ WALLOCPAUX_stack_frame_inject)];
      ALL_TAC] THEN
    SUBGOAL_THEN `LASTN (wl_state_handler (st:(A,C,FFI)wl_state) + 1) (wl_state_stack st) =
                  CONS (StackFrame m e0 e (SOME nh)) ls` ASSUME_TAC THENL
     [UNDISCH_TAC `LASTN (wl_state_handler (sc0:(A,C,FFI)wl_state) + 1) (wl_state_stack sc0) =
                   CONS (StackFrame m e0 e (SOME nh)) ls` THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[LASTN_TL; ASSUME `wl_state_handler (st:(A,C,FFI)wl_state) < LENGTH (wl_state_stack st)`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`wl_state_stack (tc0:(A,C,FFI)wl_state)`;
      `e0:(num#(A)word_loc)list`; `e:(num#(A)word_loc)list`; `ls:((A)stack_frame)list`] o
      check (fun th -> is_forall(concl th) && free_in `e0:(num#(A)word_loc)list` (concl th) = false &&
                       length(fst(strip_forall(concl th))) = 4)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        SIMP_TAC[LASTN_TL; ASSUME `wl_state_handler (st:(A,C,FFI)wl_state) < LENGTH (wl_state_stack st)`] THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `st4:((A)stack_frame)list` (X_CHOOSE_THEN `locs:((A)word_loc)spt`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `lss2:(num#(A)word_loc)list` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `lss2 = (lss:(num#(A)word_loc)list)` SUBST_ALL_TAC THENL
     [ONCE_REWRITE_TAC[GSYM ZIP_MAP_FST_SND_EQ] THEN
      UNDISCH_TAC `MAP SND (lss:(num#(A)word_loc)list) = MAP SND (lss2:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `MAP FST (e:(num#(A)word_loc)list) = MAP FST (lss2:(num#(A)word_loc)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `st4 = wl_state_stack (s1:(A,C,FFI)wl_state)` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC s_val_and_key_eq THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC s_key_eq_trans THEN EXISTS_TAC `ls:((A)stack_frame)list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `wl_state_permute (s1:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_permute_same] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" with Failure _ -> false) &&
        free_in `tc0:(A,C,FFI)wl_state` (lhs(concl th))
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    SUBGOAL_THEN `wl_state_stack_fupd (K (wl_state_stack s1))
                    (wl_state_handler_fupd (K (wl_state_handler s1))
                       (wl_state_locals_fupd (K (wl_state_locals s1)) s1)) = (s1:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [REWRITE_TAC[wl_state_component_equality] THEN SIMP[]; ALL_TAC] THEN
    ASM_REWRITE_TAC([option_INJ] @ WALLOCPAUX_wl_result_distinct) THEN
    USE_THEN "cp" MATCH_MP_TAC THEN
    REWRITE_TAC WALLOCPAUX_wl_result_distinct THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[];
      MESON_TAC[]] in
  let exc_some =
    SUBGOAL_THEN `?hv hp k1 k2. hq = (hv:num,hp:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN
    MP_TAC(ISPEC `hh:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `hq':num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
      FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)); ALL_TAC] THEN
    SUBGOAL_THEN `?hv' hp' k1' k2'. hq' = (hv':num,hp':(A)wl_prog,k1':num,k2':num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE; pair_CASE]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (fun th ->
      concl th = `k1':num = k1 /\ k2':num = k2`)) THEN
    REWRITE_TAC[option_CASE; pair_CASE] THEN
    SUBGOAL_THEN
     `wl_state_handler (sc0:(A,C,FFI)wl_state) = LENGTH (wl_state_stack (st:(A,C,FFI)wl_state)) /\
      wl_state_stack sc0 =
        CONS (StackFrame (wl_state_locals_size st) (toAList x1) lsB
                (SOME (wl_state_handler st,k1,k2))) (wl_state_stack st) /\
      wl_state_stack (tc0:(A,C,FFI)wl_state) =
        CONS (StackFrame (wl_state_locals_size st) (toAList y1) lsA
                (SOME (wl_state_handler st,k1,k2))) (wl_state_stack st)`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["sc0"; "tc0"] THEN
      REWRITE_TAC[wl_call_env_def; wl_state_INFO.ri_accfupds; K_THM;
                  WALLOCPAUX_push_env_stack_gen; WALLOCPAUX_push_env_permute_handler;
                  wl_dec_clock_def; option_CASE; pair_CASE] THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    let lastn_whole fr =
      SUBGOAL_THEN (mk_eq(`LENGTH (wl_state_stack (st:(A,C,FFI)wl_state)) + 1`,
                          mk_comb(`LENGTH:((A)stack_frame)list->num`,
                                  list_mk_icomb "CONS" [fr; `wl_state_stack (st:(A,C,FFI)wl_state)`])))
        SUBST1_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LASTN_LENGTH_ID] in
    UNDISCH_TAC `LASTN (wl_state_handler (sc0:(A,C,FFI)wl_state) + 1) (wl_state_stack sc0) =
                 CONS (StackFrame m e0 e (SOME nh)) ls` THEN
    ASM_REWRITE_TAC[] THEN
    lastn_whole `StackFrame (wl_state_locals_size (st:(A,C,FFI)wl_state)) (toAList (x1:((A)word_loc)spt)) lsB
                   (SOME (wl_state_handler st,k1,k2))` THEN
    REWRITE_TAC([CONS_11; option_INJ] @ WALLOCPAUX_stack_frame_inject) THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      is_var(rhs(concl th)) &&
      mem (fst(dest_var(rhs(concl th)))) ["m"; "e0"; "e"; "nh"; "ls"]))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `m:num option`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pair_CASE]) THEN REWRITE_TAC[pair_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`wl_state_stack (tc0:(A,C,FFI)wl_state)`;
      `toAList (y1:((A)word_loc)spt)`; `lsA:(num#(A)word_loc)list`;
      `wl_state_stack (st:(A,C,FFI)wl_state)`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        lastn_whole `StackFrame (wl_state_locals_size (s1:(A,C,FFI)wl_state))
                       (toAList (y1:((A)word_loc)spt)) lsA
                       (SOME (wl_state_handler (st:(A,C,FFI)wl_state),k1,k2))`;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `st4:((A)stack_frame)list` (X_CHOOSE_THEN `locs:((A)word_loc)spt`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `lss2:(num#(A)word_loc)list` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `st4 = wl_state_stack (s1:(A,C,FFI)wl_state)` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC s_val_and_key_eq THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC s_key_eq_trans THEN EXISTS_TAC `wl_state_stack (st:(A,C,FFI)wl_state)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `locs:((A)word_loc)spt`)) THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate" with Failure _ -> false) &&
        free_in `tc0:(A,C,FFI)wl_state` (lhs(concl th))
      then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[pair_CASE; option_CASE; WALLOCPAUX_wl_result_CASE] THEN
    ASM_CASES_TAC `(a0:(A)word_loc) = wl_Loc k1 k2` THEN ASM_REWRITE_TAC[pair_CASE] THEN
    SUBGOAL_THEN `domain (sptree_union (fromAList lss) (fromAList (toAList (x1:((A)word_loc)spt)))) =
                  domain (p0:num_set) UNION domain (p1:num_set) /\
                  domain (sptree_union (fromAList lss2) (fromAList (toAList (y1:((A)word_loc)spt)))) =
                  IMAGE (f:num->num) (domain p0) UNION IMAGE f (domain p1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      ASM_REWRITE_TAC[domain_union; domain_fromAList; set_MAP_FST_toAList_domain] THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `MAP FST (lsB:(num#(A)word_loc)list) = MAP FST (lss:(num#(A)word_loc)list)`)) THEN
        MP_TAC(ISPECL [`x2:((A)word_loc)spt`; `P:num->num->num`] env_to_list_keys);
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `MAP FST (lsA:(num#(A)word_loc)list) = MAP FST (lss2:(num#(A)word_loc)list)`)) THEN
        MP_TAC(ISPECL [`y2:((A)word_loc)spt`; `wl_state_permute (cst:(A,C,FFI)wl_state)`]
                      env_to_list_keys)] THEN
      ASM_REWRITE_TAC[pair_CASE] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `strong_locals_rel (f:num->num) (:num) (wl_state_locals (s1:(A,C,FFI)wl_state))
                    (sptree_union (fromAList lss2) (fromAList (toAList (y1:((A)word_loc)spt))))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `wl_state_locals (s1:(A,C,FFI)wl_state) =
                   sptree_union (fromAList lss) (fromAList (toAList (x1:((A)word_loc)spt)))` THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC WALLOCPAUX_union_alist_slr THEN
      EXISTS_TAC `lsB:(num#(A)word_loc)list` THEN EXISTS_TAC `lsA:(num#(A)word_loc)list` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC key_map_implies THEN FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPECL [`x2:((A)word_loc)spt`; `P:num->num->num`] env_to_list_keys) THEN
        ASM_REWRITE_TAC[pair_CASE] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        (MATCH_MP_TAC word_allocProof_INJ_less THEN
         EXISTS_TAC `domain (p0:num_set) UNION domain (p1:num_set)` THEN
         ASM_REWRITE_TAC[] THEN SET_TAC[]);
        UNDISCH_TAC `domain (x1:((A)word_loc)spt) = domain (p0:num_set)` THEN
        DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
        CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM] THEN
    SUBGOAL_THEN `!p. wl_set_var hv (a1:(A)word_loc) (wl_state_permute_fupd (K p) (s1:(A,C,FFI)wl_state)) =
                      wl_state_permute_fupd (K p) (wl_set_var hv a1 s1)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[wl_set_var_with_const]; ALL_TAC] THEN
    (fun (asl,w as g) ->
       let tm = find_term (fun t -> is_comb t &&
                  (try fst(dest_const(rator t)) = "wl_evaluate" with Failure _ -> false) &&
                  (try fst(dest_pair(rand t)) = `hp':(A)wl_prog` with Failure _ -> false)) w in
       let cstT = snd(dest_pair(rand tm)) in
       (REMOVE_THEN "ihh" (MP_TAC o SPECL [`s1:(A,C,FFI)wl_state`; rand cstT;
                                            `a1:(A)word_loc`])) g) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `perm3:num->num->num` MP_TAC) THEN
    DISCH_THEN(fun th -> EXISTS_TAC `perm3:num->num->num` THEN MP_TAC th) THEN
    REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC in
  let exc =
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e0:(num#(A)word_loc)list` (X_CHOOSE_THEN `e:(num#(A)word_loc)list`
       (X_CHOOSE_THEN `nh:num#num#num` (X_CHOOSE_THEN `ls:((A)stack_frame)list`
        (X_CHOOSE_THEN `m:num option` (X_CHOOSE_THEN `lss:(num#(A)word_loc)list`
          STRIP_ASSUME_TAC))))))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
    MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [exc_none; exc_some] in
  (fun (asl,w as g) ->
     let a = fst(dest_imp w) in
     let c = if is_conj a then fst(dest_conj a) else a in
     let hd = try fst(dest_const(fst(strip_comb c))) with Failure _ -> "" in
     (if hd = "s_key_eq" then result else if hd = "<" then exc else stop) g));;

(* ------------------------------------------------------------------------- *)
(* ssa_cc_trans_correct, case Call with a return handler (HOL4 line 8298)    *)
(* ------------------------------------------------------------------------- *)

(* after the return of a call: the renaming moves of the return handler *)

let WALLOCPAUX_ret_moves = prove
 (`!(s1:(A,C,FFI)wl_state) (t1:(A,C,FFI)wl_state) (ssa1:num spt) na1 (p0:num_set) (p1:num_set)
    ls (mov2:(A)wl_prog) ssa2 na2 (n:num list) (ys:((A)word_loc)list) ret' ssa_2_p na_2_p
    (X:(A)wl_prog).
     word_state_eq_rel s1 t1 /\
     strong_locals_rel (option_lookup ssa1) (:num) (wl_state_locals s1) (wl_state_locals t1) /\
     domain (wl_state_locals s1) = domain p0 UNION domain p1 /\
     set_of_list ls = domain p0 UNION domain p1 /\ ALL_DISTINCT ls /\
     domain p0 UNION domain p1 SUBSET domain ssa1 /\
     ALL (\x. x < na1 + 2) ls /\
     ssa_map_ok na1 ssa1 /\ is_stack_var na1 /\
     list_next_var_rename_move (sptree_inter ssa1 (sptree_union p0 p1)) (na1 + 2) ls = (mov2,ssa2,na2) /\
     list_next_var_rename n ssa2 na2 = (ret',ssa_2_p,na_2_p) /\
     ALL_DISTINCT n /\ ALL (\x. x < na2) n /\ LENGTH ys = LENGTH n
     ==> ?t3. wl_evaluate (wl_Seq mov2 (wl_Seq (wl_Move 1
                (ZIP ret' (list_of_seq (\x. 2 * (x + 1)) (LENGTH n)))) X),
                wl_set_vars (list_of_seq (\x. 2 * (x + 1)) (LENGTH n)) ys t1) =
              wl_evaluate (X,t3) /\
              word_state_eq_rel (wl_set_vars n ys s1) t3 /\
              ssa_locals_rel na_2_p ssa_2_p (wl_state_locals (wl_set_vars n ys s1))
                (wl_state_locals t3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `regs = list_of_seq (\x. 2 * (x + 1)) (LENGTH (n:num list))` THEN
  SUBGOAL_THEN `ALL_DISTINCT (regs:num list) /\ ALL is_phy_var regs /\ LENGTH regs = LENGTH (n:num list)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "regs" THEN REWRITE_TAC[WALLOCPAUX_even_regs; LENGTH_LIST_OF_SEQ; GSYM ALL_MEM] THEN
    REWRITE_TAC[WALLOCPAUX_even_regs];
    ALL_TAC] THEN
  SUBGOAL_THEN `ssa_map_ok (na1 + 2) (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))` ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
    EXISTS_TAC `na1:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ssa_locals_rel (na1 + 2) (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))
                  (wl_state_locals (s1:(A,C,FFI)wl_state))
                  (wl_state_locals (wl_set_vars regs (ys:((A)word_loc)list) (t1:(A,C,FFI)wl_state)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC ssa_locals_rel_ignore_list_insert THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_cut2 THEN
    ASM_REWRITE_TAC[domain_union] THEN CONJ_TAC THENL
     [MATCH_MP_TAC strong_locals_rel_subset THEN EXISTS_TAC `(:num)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      UNDISCH_TAC `ALL (\x. x < na1 + 2) (ls:num list)` THEN
      REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_union; GSYM IN_SET_OF_LIST] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:(A,C,FFI)wl_state`; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`;
                 `na1 + 2`; `ls:num list`;
                 `wl_set_vars regs (ys:((A)word_loc)list) (t1:(A,C,FFI)wl_state)`]
         list_next_var_rename_move_preserve) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `word_state_eq_rel (s1:(A,C,FFI)wl_state) t1` THEN
    REWRITE_TAC[wl_set_vars_def; word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov2:(A)wl_prog,
      wl_set_vars regs (ys:((A)word_loc)list) (t1:(A,C,FFI)wl_state))`
    [`r2:((A)wl_result)option`; `t2:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~is_phy_var (na1 + 2)` ASSUME_TAC THENL
   [MP_TAC(SPEC `na1:num` is_stack_var_flip) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[convention_partitions];
    ALL_TAC] THEN
  SUBGOAL_THEN `na1 + 2 <= na2 /\ is_alloc_var na2 /\ ssa_map_ok na2 (ssa2:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`; `na1 + 2`;
                   `mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] list_next_var_rename_move_props) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `na1:num` is_stack_var_flip) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (ret':num list) /\ LENGTH ret' = LENGTH (n:num list)`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1 o check (fun th ->
      is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
                              "list_next_var_rename" with Failure _ -> false))) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_COUNT_LIST];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_vars regs (t2:(A,C,FFI)wl_state) = SOME (ys:((A)word_loc)list)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC get_vars_eq_alist_insert THEN
    EXISTS_TAC `wl_state_locals (t1:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ALL is_phy_var (regs:num list)` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Move 1 (ZIP ret' regs):(A)wl_prog, t2:(A,C,FFI)wl_state) =
                (NONE, wl_set_vars ret' ys t2)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    SUBGOAL_THEN `LENGTH (ret':num list) = LENGTH (regs:num list)` (LABEL_TAC "lz") THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "lz" (fun th -> REWRITE_TAC[MATCH_MP MAP_FST_ZIP th; MATCH_MP MAP_SND_ZIP th]) THEN
    ASM_REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  EXISTS_TAC `wl_set_vars ret' (ys:((A)word_loc)list) (t2:(A,C,FFI)wl_state)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`mov2:(A)wl_prog`; `wl_Seq (wl_Move 1 (ZIP ret' regs)) X:(A)wl_prog`;
                   `wl_set_vars regs (ys:((A)word_loc)list) (t1:(A,C,FFI)wl_state)`;
                   `t2:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[wl_set_vars_def] THEN MATCH_MP_TAC WALLOCPAUX_wser_locals THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC ssa_locals_rel_list_next_var_rename THEN
    MAP_EVERY EXISTS_TAC [`ssa2:num spt`; `na2:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[convention_partitions]]);;

(* after an exception caught by the handler: the renaming moves of the     *)
(* exception handler                                                         *)

let WALLOCPAUX_exc_moves = prove
 (`!(s1:(A,C,FFI)wl_state) (t1:(A,C,FFI)wl_state) (ssa1:num spt) na1 (p0:num_set) (p1:num_set)
    ls (mov2:(A)wl_prog) ssa2 na2 hv (y:(A)word_loc) na3 (X:(A)wl_prog).
     word_state_eq_rel s1 t1 /\
     strong_locals_rel (option_lookup ssa1) (:num) (wl_state_locals s1) (wl_state_locals t1) /\
     domain (wl_state_locals s1) = domain p0 UNION domain p1 /\
     set_of_list ls = domain p0 UNION domain p1 /\ ALL_DISTINCT ls /\
     domain p0 UNION domain p1 SUBSET domain ssa1 /\
     ALL (\x. x < na1 + 2) ls /\
     ssa_map_ok na1 ssa1 /\ is_stack_var na1 /\
     list_next_var_rename_move (sptree_inter ssa1 (sptree_union p0 p1)) (na1 + 2) ls = (mov2,ssa2,na2) /\
     na2 <= na3 /\ hv < na3
     ==> ?t3. wl_evaluate (wl_Seq mov2 (wl_Seq (wl_Move 1 [na3,2]) X), wl_set_var 2 y t1) =
              wl_evaluate (X,t3) /\
              word_state_eq_rel (wl_set_var hv y s1) t3 /\
              ssa_locals_rel (na3 + 4) (insert hv na3 ssa2)
                (wl_state_locals (wl_set_var hv y s1)) (wl_state_locals t3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ssa_map_ok (na1 + 2) (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))` ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
    EXISTS_TAC `na1:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ssa_locals_rel (na1 + 2) (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))
                  (wl_state_locals (s1:(A,C,FFI)wl_state))
                  (wl_state_locals (wl_set_var 2 (y:(A)word_loc) (t1:(A,C,FFI)wl_state)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    MATCH_MP_TAC ssa_locals_rel_ignore_insert THEN ASM_REWRITE_TAC[WALLOCPAUX_PHY_REGS] THEN
    MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_cut2 THEN
    ASM_REWRITE_TAC[domain_union] THEN CONJ_TAC THENL
     [MATCH_MP_TAC strong_locals_rel_subset THEN EXISTS_TAC `(:num)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      UNDISCH_TAC `ALL (\x. x < na1 + 2) (ls:num list)` THEN
      REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_union; GSYM IN_SET_OF_LIST] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:(A,C,FFI)wl_state`; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`;
                 `na1 + 2`; `ls:num list`;
                 `wl_set_var 2 (y:(A)word_loc) (t1:(A,C,FFI)wl_state)`]
         list_next_var_rename_move_preserve) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `word_state_eq_rel (s1:(A,C,FFI)wl_state) t1` THEN
    REWRITE_TAC[wl_set_var_def; word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov2:(A)wl_prog,
      wl_set_var 2 (y:(A)word_loc) (t1:(A,C,FFI)wl_state))`
    [`r2:((A)wl_result)option`; `t2:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~is_phy_var (na1 + 2)` ASSUME_TAC THENL
   [MP_TAC(SPEC `na1:num` is_stack_var_flip) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[convention_partitions];
    ALL_TAC] THEN
  SUBGOAL_THEN `na1 + 2 <= na2 /\ ssa_map_ok na2 (ssa2:num spt)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`; `na1 + 2`;
                   `mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] list_next_var_rename_move_props) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `na1:num` is_stack_var_flip) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Move 1 [na3,2]:(A)wl_prog, t2:(A,C,FFI)wl_state) =
                (NONE, wl_set_vars [na3] [y] t2)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def; wl_get_var_def] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2`) THEN
    REWRITE_TAC[WALLOCPAUX_PHY_REGS; wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM;
                lookup_insert] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  EXISTS_TAC `wl_set_vars [na3] [y:(A)word_loc] (t2:(A,C,FFI)wl_state)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`mov2:(A)wl_prog`; `wl_Seq (wl_Move 1 [na3,2]) X:(A)wl_prog`;
                   `wl_set_var 2 (y:(A)word_loc) (t1:(A,C,FFI)wl_state)`;
                   `t2:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[wl_set_vars_def; wl_set_var_def] THEN MATCH_MP_TAC WALLOCPAUX_wser_locals THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[wl_set_vars_def; wl_set_var_def; alist_insert_def; wl_state_INFO.ri_accfupds;
                K_THM] THEN
    MATCH_MP_TAC ssa_locals_rel_set_var THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na2:num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na2:num` THEN ASM_REWRITE_TAC[]]]);;

(* the relation of the results in WALLOCPAUX_sct_Q *)

let WALLOCPAUX_sct_R_def = new_definition (CASE_TERM
 `WALLOCPAUX_sct_R (na':num) (ssa':num spt) (lt:(num spt#1 spt#1 spt)list)
    (res:((A)wl_result)option) (rst:(A,C,FFI)wl_state) (res':((A)wl_result)option)
    (rcst:(A,C,FFI)wl_state) <=>
      res = res' /\
      word_state_eq_rel rst rcst /\
      (match res with
         NONE -> ssa_locals_rel na' ssa' (wl_state_locals rst) (wl_state_locals rcst)
       | SOME (wordSem_Break n) ->
           (match oEL n lt with
              SOME (tgt_ssa,_,exit_names) ->
                strong_locals_rel (option_lookup tgt_ssa) (domain exit_names)
                  (wl_state_locals rst) (wl_state_locals rcst)
            | NONE -> T)
       | SOME (wordSem_Continue n) ->
           (match oEL n lt with
              SOME (tgt_ssa,names,_) ->
                strong_locals_rel (option_lookup tgt_ssa) (domain names)
                  (wl_state_locals rst) (wl_state_locals rcst)
            | NONE -> T)
       | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`);;

(* the passthrough results satisfy the relation *)

let WALLOCPAUX_sct_R_pass = prove
 (`!na (ssa:num spt) lt r (s:(A,C,FFI)wl_state) t.
     word_state_eq_rel s t /\ wl_state_locals s = wl_state_locals t /\
     ((?x y. r = wl_Exception x y) \/ r = wl_TimeOut \/ r = NotEnoughSpace \/
      (?e. r = wl_FinalFFI e))
     ==> WALLOCPAUX_sct_R na ssa lt (SOME r) s (SOME r) t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)))) THEN
  ASM_REWRITE_TAC[WALLOCPAUX_sct_R_def; option_CASE; WALLOCPAUX_wl_result_CASE]);;

(* a continuation followed by consistency moves *)

let WALLOCPAUX_sct_R_seq_cons = prove
 (CASE_TERM
  `!na (ssa:num spt) lt r (s:(A,C,FFI)wl_state) r' t (cons:(A)wl_prog) naF ssaF
    (P:(A)wl_prog) t0.
     wl_evaluate (P,t0) = (r',t) /\
     WALLOCPAUX_sct_R na ssa lt r s r' t /\
     (!(stL:(A,C,FFI)wl_state) (cstL:(A,C,FFI)wl_state).
        ssa_locals_rel na ssa (wl_state_locals stL) (wl_state_locals cstL)
        ==> let (resL,rcstL) = wl_evaluate (cons,cstL) in
              resL = NONE /\
              ssa_locals_rel naF ssaF (wl_state_locals stL) (wl_state_locals rcstL) /\
              word_state_eq_rel cstL rcstL)
     ==> let (r2,t2) = wl_evaluate (wl_Seq P cons,t0) in
           WALLOCPAUX_sct_R naF ssaF lt r s r2 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `r':((A)wl_result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC)) THENL
   [MP_TAC(ISPECL [`P:(A)wl_prog`; `cons:(A)wl_prog`; `t0:(A,C,FFI)wl_state`;
                   `t:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `WALLOCPAUX_sct_R na ssa lt r (s:(A,C,FFI)wl_state) NONE (t:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_sct_R_def] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `r:((A)wl_result)option`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:(A,C,FFI)wl_state`; `t:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    WALLOCPAUX_TUPLE_TAC `wl_evaluate (cons:(A)wl_prog,t:(A,C,FFI)wl_state)`
      [`r3:((A)wl_result)option`; `t3:(A,C,FFI)wl_state`] THEN
    REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
    MATCH_MP_TAC WALLOCPAUX_word_state_eq_rel_trans THEN EXISTS_TAC `t:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`P:(A)wl_prog`; `cons:(A)wl_prog`; `t0:(A,C,FFI)wl_state`; `rr:(A)wl_result`;
                   `t:(A,C,FFI)wl_state`] WALLOCPAUX_seq_SOME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE] THEN
    UNDISCH_TAC `WALLOCPAUX_sct_R na ssa lt r (s:(A,C,FFI)wl_state) (SOME rr) (t:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_sct_R_def] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `r:((A)wl_result)option`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN ASM_REWRITE_TAC[option_CASE]]);;

(* the returning call without an exception handler *)

let WALLOCPAUX_sct_Call_ret_none = prove
 (CASE_TERM
  `!(n:num list) (names:num_set#num_set) (ret_handler:(A)wl_prog) (l1:num) (l2:num)
    (dest:num option) (args:num list).
     (!st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st ret_handler)
     ==> !st:(A,C,FFI)wl_state.
           WALLOCPAUX_sct_Q st (wl_Call (SOME (n,names,ret_handler,l1,l2)) dest args NONE)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ihr") THEN
  GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p0 p1. names = (p0:num_set,p1:num_set)`
    (X_CHOOSE_THEN `p0:num_set` (X_CHOOSE_THEN `p1:num_set` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_name_def; FST; SND; option_CASE;
                              pair_CASE]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  let srcerr thl =
    EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_permute_same] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC([option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; add_ret_loc_def;
                     WALLOCPAUX_wl_result_CASE] @ thl) in
  MP_TAC(ISPEC `wl_get_vars args (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xs:((A)word_loc)list` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THENL [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_find_code (dest:num option) (CONS (wl_Loc l1 l2) (xs:((A)word_loc)list))
                  (wl_state_code (st:(A,C,FFI)wl_state)) (wl_state_stack_size st)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `fc:((A)word_loc)list#(A)wl_prog#(num)option` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?args1 prog ss. fc = (args1:((A)word_loc)list,prog:(A)wl_prog,ss:(num)option)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_CASES_TAC `domain (p0:num_set) = {} \/ ~ALL_DISTINCT (n:num list)` THENL
   [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `cut_envs (p0:num_set,p1:num_set) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `xx:((A)word_loc)spt#((A)word_loc)spt` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. xx = (x1:((A)word_loc)spt,x2:((A)word_loc)spt)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_envs_domain_SUBSET) THEN
  ABBREV_TAC `ls = MAP FST (toAList (sptree_union p0 p1:num_set))` THEN
  SUBGOAL_THEN `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[set_MAP_FST_toAList_domain; domain_union];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (ls:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; FST; SND; option_CASE] THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (ssa:num spt) (na + 2) ls:(A)wl_prog#num spt#num`
    [`mov1:(A)wl_prog`; `ssa1:num spt`; `na1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))
                          (na1 + 2) ls:(A)wl_prog#num spt#num`
    [`mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename (n:num list) (ssa2:num spt) na2`
    [`ret':num list`; `ssa_2_p:num spt`; `na_2_p:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (ret_handler:(A)wl_prog) ssa_2_p na_2_p lt`
    [`ren_ret_handler:(A)wl_prog`; `ssa_2:num spt`; `na_2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `ssa:num spt`; `na + 2`; `ls:num list`;
                 `cst:(A,C,FFI)wl_state`] list_next_var_rename_move_preserve) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[UNION_SUBSET];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov1:(A)wl_prog,cst:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `rcst1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `na + 2 <= na1 /\ is_stack_var na1 /\ ssa_map_ok na1 (ssa1:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`; `mov1:(A)wl_prog`;
                   `ssa1:num spt`; `na1:num`] list_next_var_rename_move_props_2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ssa:num spt`; `na + 2`; `ls:num list`; `mov1:(A)wl_prog`;
                 `ssa1:num spt`; `na1:num`] WALLOCPAUX_lnvrm_names) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `strong_locals_rel (option_lookup ssa) (:num) (wl_state_locals (st:(A,C,FFI)wl_state))
                  (wl_state_locals (rcst1:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [REWRITE_TAC[strong_locals_rel_def; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `v:(A)word_loc`] THEN DISCH_TAC THEN
    UNDISCH_TAC `ssa_locals_rel na ssa (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def; domain_lookup] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:num`; `v:(A)word_loc`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CHOOSE_THEN ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `v:(A)word_loc`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "THE")) (concl th) &&
      can (find_term (fun t -> t = `ssa:num spt`)) (concl th))) THEN
    ASM_REWRITE_TAC[THE_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_vars (MAP (option_lookup ssa) args) (rcst1:(A,C,FFI)wl_state) =
                SOME (xs:((A)word_loc)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC strong_locals_rel_get_vars THEN
    MAP_EVERY EXISTS_TAC [`(:num)`; `st:(A,C,FFI)wl_state`] THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `na1 + 2 <= na2 /\ is_alloc_var na2 /\ ssa_map_ok na2 (ssa2:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`; `na1 + 2`;
                   `mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] list_next_var_rename_move_props) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `na1:num` is_stack_var_flip) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
      EXISTS_TAC `na1:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `na2 <= na_2_p /\ is_alloc_var na_2_p /\ ssa_map_ok na_2_p (ssa_2_p:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num list`; `ssa2:num spt`; `na2:num`; `ret':num list`;
                   `ssa_2_p:num spt`; `na_2_p:num`] list_next_var_rename_props) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `na_2_p <= na_2 /\ is_alloc_var na_2 /\ ssa_map_ok na_2 (ssa_2:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ret_handler:(A)wl_prog`; `ssa_2_p:num spt`; `na_2_p:num`;
                   `lt:(num spt#1 spt#1 spt)list`; `ren_ret_handler:(A)wl_prog`;
                   `ssa_2:num spt`; `na_2:num`] ssa_cc_trans_props) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cargs = list_of_seq (\x. 2 * (x + 1)) (LENGTH (MAP (option_lookup ssa) (args:num list)))` THEN
  SUBGOAL_THEN `ALL_DISTINCT (cargs:num list) /\ ALL is_phy_var cargs /\
                LENGTH cargs = LENGTH (args:num list)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cargs" THEN REWRITE_TAC[WALLOCPAUX_even_regs; LENGTH_LIST_OF_SEQ; LENGTH_MAP;
                                       GSYM ALL_MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (xs:((A)word_loc)list) = LENGTH (args:num list)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_vars_length_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X. wl_evaluate (wl_Seq mov1 (wl_Seq (wl_Move 1 (ZIP cargs
                      (MAP (option_lookup ssa) args))) X), cst) =
                    wl_evaluate (X:(A)wl_prog, wl_set_vars cargs xs (rcst1:(A,C,FFI)wl_state))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`mov1:(A)wl_prog`;
                   `wl_Seq (wl_Move 1 (ZIP cargs (MAP (option_lookup ssa) args))) X:(A)wl_prog`;
                   `cst:(A,C,FFI)wl_state`; `rcst1:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    SUBGOAL_THEN `LENGTH (cargs:num list) = LENGTH (MAP (option_lookup ssa) (args:num list))`
      (LABEL_TAC "lz") THENL [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
    USE_THEN "lz" (fun th -> REWRITE_TAC[MATCH_MP MAP_FST_ZIP th; MATCH_MP MAP_SND_ZIP th]) THEN
    ASM_REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `wl_set_vars cargs xs (rcst1:(A,C,FFI)wl_state)`;
                 `option_lookup (ssa1:num spt)`; `n:num list`;
                 `list_of_seq (\x. 2 * (x + 1)) (LENGTH (n:num list))`;
                 `p0:num_set`; `p1:num_set`; `ret_handler:(A)wl_prog`;
                 `wl_Seq mov2 (wl_Seq (wl_Move 1 (ZIP ret' (list_of_seq (\x. 2 * (x + 1))
                    (LENGTH (n:num list))))) ren_ret_handler):(A)wl_prog`;
                 `l1:num`; `l2:num`; `dest:num option`; `args:num list`; `cargs:num list`;
                 `NONE:(num#(A)wl_prog#num#num)option`; `NONE:(num#(A)wl_prog#num#num)option`;
                 `WALLOCPAUX_sct_R na_2 (ssa_2:num spt) lt:((A)wl_result)option->
                    (A,C,FFI)wl_state->((A)wl_result)option->(A,C,FFI)wl_state->bool`]
         WALLOCPAUX_call_sim) THEN
  ANTS_TAC THENL
   [ALL_TAC; REWRITE_TAC[WALLOCPAUX_sct_R_def] THEN DISCH_THEN ACCEPT_TAC] THEN
  REWRITE_TAC[option_CASE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wl_set_vars_def] THEN
    UNDISCH_TAC `word_state_eq_rel (st:(A,C,FFI)wl_state) rcst1` THEN
    REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM];
    GEN_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC get_vars_set_vars_eq THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[WALLOCPAUX_even_regs];
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    REWRITE_TAC[INJ; IN_UNIV] THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    REWRITE_TAC[GSYM(ASSUME `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`);
                IN_SET_OF_LIST] THEN STRIP_TAC THEN
    MATCH_MP_TAC list_next_var_rename_move_distinct THEN
    MAP_EVERY EXISTS_TAC [`ssa:num spt`; `na + 2`; `ls:num list`; `mov1:(A)wl_prog`;
                          `ssa1:num spt`; `na1:num`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_strong_gen THEN
    MAP_EVERY EXISTS_TAC [`na1:num`; `wl_state_locals (rcst1:(A,C,FFI)wl_state)`] THEN
    ASM_REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WALLOCPAUX_lookup_alist_insert_notin THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `ALL is_phy_var (cargs:num list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(ISPECL [`na_2:num`; `ssa_2:num spt`; `lt:(num spt#1 spt#1 spt)list`]
                       WALLOCPAUX_sct_R_pass);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s1:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`;
                       `ys:((A)word_loc)list`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s1:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`; `ssa1:num spt`; `na1:num`;
                 `p0:num_set`; `p1:num_set`; `ls:num list`; `mov2:(A)wl_prog`; `ssa2:num spt`;
                 `na2:num`; `n:num list`; `ys:((A)word_loc)list`; `ret':num list`;
                 `ssa_2_p:num spt`; `na_2_p:num`; `ren_ret_handler:(A)wl_prog`]
         WALLOCPAUX_ret_moves) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `domain (ssa1:num spt) = domain (ssa:num spt) UNION domain (p0:num_set)
                            UNION domain (p1:num_set)`] THEN SET_TAC[];
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p0:num_set)))` THEN
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p1:num_set)))` THEN
      UNDISCH_TAC `na + 2 <= na1` THEN
      REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_union; IN_UNION] THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; ASSUME `set_of_list (ls:num list) =
        domain (p0:num_set) UNION domain (p1:num_set)`; IN_UNION] THEN
      DISCH_THEN(LABEL_TAC "le") THEN DISCH_THEN(LABEL_TAC "h1") THEN
      DISCH_THEN(LABEL_TAC "h0") THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `z < na /\ na + 2 <= na1 ==> z < na1 + 2`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
         [REMOVE_THEN "h0" MATCH_MP_TAC; REMOVE_THEN "h1" MATCH_MP_TAC] THEN
        FIRST_ASSUM ACCEPT_TAC;
        REMOVE_THEN "le" ACCEPT_TAC];
      UNDISCH_TAC `ALL (\x. x < na) (n:num list)` THEN MATCH_MP_TAC MONO_ALL THEN
      GEN_TAC THEN BETA_TAC THEN UNDISCH_TAC `na + 2 <= na1` THEN
      UNDISCH_TAC `na1 + 2 <= na2` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "ihr" (MP_TAC o SPEC `wl_set_vars n ys (s1:(A,C,FFI)wl_state)`) THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`t3:(A,C,FFI)wl_state`; `ssa_2_p:num spt`; `na_2_p:num`;
                             `lt:(num spt#1 spt#1 spt)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC every_var_mono THEN
    EXISTS_TAC `\x:num. x < na` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    UNDISCH_TAC `na + 2 <= na1` THEN UNDISCH_TAC `na1 + 2 <= na2` THEN
    UNDISCH_TAC `na2 <= na_2_p` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; WALLOCPAUX_sct_R_def]);;


let WALLOCPAUX_sct_R_more = prove
 (`!na na' (ssa:num spt) lt r (s:(A,C,FFI)wl_state) r' t.
     na <= na' /\ WALLOCPAUX_sct_R na ssa lt r s r' t ==> WALLOCPAUX_sct_R na' ssa lt r s r' t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_sct_R_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `r:((A)wl_result)option`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r':((A)wl_result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `rr:(A)wl_result` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_CASE]) THEN ASM_REWRITE_TAC[option_CASE] THEN
  MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na:num` THEN ASM_REWRITE_TAC[]);;

(* the returning call with an exception handler *)

let WALLOCPAUX_sct_Call_ret_some = prove
 (CASE_TERM
  `!(n:num list) (names:num_set#num_set) (ret_handler:(A)wl_prog) (l1:num) (l2:num)
    (dest:num option) (args:num list) (hv:num) (hprog:(A)wl_prog) (l1':num) (l2':num).
     (!st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st ret_handler) /\
     (!st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st hprog)
     ==> !st:(A,C,FFI)wl_state.
           WALLOCPAUX_sct_Q st (wl_Call (SOME (n,names,ret_handler,l1,l2)) dest args
                                   (SOME (hv,hprog,l1',l2')))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN
  GEN_TAC THEN REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p0 p1. names = (p0:num_set,p1:num_set)`
    (X_CHOOSE_THEN `p0:num_set` (X_CHOOSE_THEN `p1:num_set` SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_every_var_def; every_name_def; FST; SND; option_CASE;
                              pair_CASE]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  let srcerr thl =
    EXISTS_TAC `wl_state_permute (st:(A,C,FFI)wl_state)` THEN
    REWRITE_TAC[WALLOCPAUX_permute_same] THEN ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    ASM_REWRITE_TAC([option_CASE; pair_CASE; WALLOCPAUX_word_loc_CASE; add_ret_loc_def;
                     WALLOCPAUX_wl_result_CASE] @ thl) in
  MP_TAC(ISPEC `wl_get_vars args (st:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xs:((A)word_loc)list` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  ASM_CASES_TAC `bad_dest_args (dest:num option) (args:num list)` THENL [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_find_code (dest:num option) (CONS (wl_Loc l1 l2) (xs:((A)word_loc)list))
                  (wl_state_code (st:(A,C,FFI)wl_state)) (wl_state_stack_size st)`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `fc:((A)word_loc)list#(A)wl_prog#(num)option` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?args1 prog ss. fc = (args1:((A)word_loc)list,prog:(A)wl_prog,ss:(num)option)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_CASES_TAC `domain (p0:num_set) = {} \/ ~ALL_DISTINCT (n:num list)` THENL
   [srcerr []; ALL_TAC] THEN
  MP_TAC(ISPEC `cut_envs (p0:num_set,p1:num_set) (wl_state_locals (st:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `xx:((A)word_loc)spt#((A)word_loc)spt` ASSUME_TAC)) THENL
   [srcerr []; ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. xx = (x1:((A)word_loc)spt,x2:((A)word_loc)spt)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_envs_domain_SUBSET) THEN
  ABBREV_TAC `ls = MAP FST (toAList (sptree_union p0 p1:num_set))` THEN
  SUBGOAL_THEN `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`
    ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[set_MAP_FST_toAList_domain; domain_union];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (ls:num list)` ASSUME_TAC THENL
   [EXPAND_TAC "ls" THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]; ALL_TAC] THEN
  REWRITE_TAC[ssa_cc_trans_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; FST; SND; option_CASE] THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (ssa:num spt) (na + 2) ls:(A)wl_prog#num spt#num`
    [`mov1:(A)wl_prog`; `ssa1:num spt`; `na1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename_move (sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set))
                          (na1 + 2) ls:(A)wl_prog#num spt#num`
    [`mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename (n:num list) (ssa2:num spt) na2`
    [`ret':num list`; `ssa_2_p:num spt`; `na_2_p:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (ret_handler:(A)wl_prog) ssa_2_p na_2_p lt`
    [`ren_ret_handler:(A)wl_prog`; `ssa_2:num spt`; `na_2:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (hprog:(A)wl_prog) (insert hv na_2 ssa2) (na_2 + 4) lt`
    [`ren_exc_handler:(A)wl_prog`; `ssa_3:num spt`; `na_3:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  (fun (asl,w as g) ->
     let fi = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "fix_inconsistencies" &&
                                      length(snd(strip_comb t)) = 4 with Failure _ -> false) w in
     WALLOCPAUX_TUPLE_TAC fi [`ret_cons:(A)wl_prog`; `exc_cons:(A)wl_prog`; `na_fin:num`;
                              `ssa_fin:num spt`] g) THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `ssa:num spt`; `na + 2`; `ls:num list`;
                 `cst:(A,C,FFI)wl_state`] list_next_var_rename_move_preserve) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ssa_locals_rel_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[UNION_SUBSET];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov1:(A)wl_prog,cst:(A,C,FFI)wl_state)`
    [`r1:((A)wl_result)option`; `rcst1:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `na + 2 <= na1 /\ is_stack_var na1 /\ ssa_map_ok na1 (ssa1:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `na:num`; `mov1:(A)wl_prog`;
                   `ssa1:num spt`; `na1:num`] list_next_var_rename_move_props_2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ssa:num spt`; `na + 2`; `ls:num list`; `mov1:(A)wl_prog`;
                 `ssa1:num spt`; `na1:num`] WALLOCPAUX_lnvrm_names) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `strong_locals_rel (option_lookup ssa) (:num) (wl_state_locals (st:(A,C,FFI)wl_state))
                  (wl_state_locals (rcst1:(A,C,FFI)wl_state))` ASSUME_TAC THENL
   [REWRITE_TAC[strong_locals_rel_def; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `v:(A)word_loc`] THEN DISCH_TAC THEN
    UNDISCH_TAC `ssa_locals_rel na ssa (wl_state_locals (st:(A,C,FFI)wl_state))
                   (wl_state_locals (cst:(A,C,FFI)wl_state))` THEN
    REWRITE_TAC[ssa_locals_rel_def; domain_lookup] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:num`; `v:(A)word_loc`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CHOOSE_THEN ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `v:(A)word_loc`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "THE")) (concl th) &&
      can (find_term (fun t -> t = `ssa:num spt`)) (concl th))) THEN
    ASM_REWRITE_TAC[THE_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_get_vars (MAP (option_lookup ssa) args) (rcst1:(A,C,FFI)wl_state) =
                SOME (xs:((A)word_loc)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC strong_locals_rel_get_vars THEN
    MAP_EVERY EXISTS_TAC [`(:num)`; `st:(A,C,FFI)wl_state`] THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `na1 + 2 <= na2 /\ is_alloc_var na2 /\ ssa_map_ok na2 (ssa2:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ls:num list`; `sptree_inter (ssa1:num spt) (sptree_union p0 p1:num_set)`; `na1 + 2`;
                   `mov2:(A)wl_prog`; `ssa2:num spt`; `na2:num`] list_next_var_rename_move_props) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `na1:num` is_stack_var_flip) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ssa_map_ok_inter THEN MATCH_MP_TAC ssa_map_ok_more THEN
      EXISTS_TAC `na1:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `na2 <= na_2_p /\ is_alloc_var na_2_p /\ ssa_map_ok na_2_p (ssa_2_p:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num list`; `ssa2:num spt`; `na2:num`; `ret':num list`;
                   `ssa_2_p:num spt`; `na_2_p:num`] list_next_var_rename_props) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `na_2_p <= na_2 /\ is_alloc_var na_2 /\ ssa_map_ok na_2 (ssa_2:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ret_handler:(A)wl_prog`; `ssa_2_p:num spt`; `na_2_p:num`;
                   `lt:(num spt#1 spt#1 spt)list`; `ren_ret_handler:(A)wl_prog`;
                   `ssa_2:num spt`; `na_2:num`] ssa_cc_trans_props) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cargs = list_of_seq (\x. 2 * (x + 1)) (LENGTH (MAP (option_lookup ssa) (args:num list)))` THEN
  SUBGOAL_THEN `ALL_DISTINCT (cargs:num list) /\ ALL is_phy_var cargs /\
                LENGTH cargs = LENGTH (args:num list)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cargs" THEN REWRITE_TAC[WALLOCPAUX_even_regs; LENGTH_LIST_OF_SEQ; LENGTH_MAP;
                                       GSYM ALL_MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (xs:((A)word_loc)list) = LENGTH (args:num list)` ASSUME_TAC THENL
   [MATCH_MP_TAC get_vars_length_lemma THEN EXISTS_TAC `st:(A,C,FFI)wl_state` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X. wl_evaluate (wl_Seq mov1 (wl_Seq (wl_Move 1 (ZIP cargs
                      (MAP (option_lookup ssa) args))) X), cst) =
                    wl_evaluate (X:(A)wl_prog, wl_set_vars cargs xs (rcst1:(A,C,FFI)wl_state))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`mov1:(A)wl_prog`;
                   `wl_Seq (wl_Move 1 (ZIP cargs (MAP (option_lookup ssa) args))) X:(A)wl_prog`;
                   `cst:(A,C,FFI)wl_state`; `rcst1:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IL2AUX_evaluate_Seq_NONE THEN
    ONCE_REWRITE_TAC[wl_evaluate_def] THEN
    SUBGOAL_THEN `LENGTH (cargs:num list) = LENGTH (MAP (option_lookup ssa) (args:num list))`
      (LABEL_TAC "lz") THENL [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
    USE_THEN "lz" (fun th -> REWRITE_TAC[MATCH_MP MAP_FST_ZIP th; MATCH_MP MAP_SND_ZIP th]) THEN
    ASM_REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  SUBGOAL_THEN `na_2 + 4 <= na_3 /\ is_alloc_var na_3 /\ ssa_map_ok na_3 (ssa_3:num spt)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hprog:(A)wl_prog`; `insert hv na_2 (ssa2:num spt)`; `na_2 + 4`;
                   `lt:(num spt#1 spt#1 spt)list`; `ren_exc_handler:(A)wl_prog`;
                   `ssa_3:num spt`; `na_3:num`] ssa_cc_trans_props) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC ssa_map_ok_extend THEN CONJ_TAC THENL
         [MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na2:num` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `na2 <= na_2_p` THEN UNDISCH_TAC `na_2_p <= na_2` THEN ARITH_TAC;
          ASM_MESON_TAC[convention_partitions]];
        MATCH_MP_TAC WALLOCPAUX_is_alloc_var_add4 THEN ASM_REWRITE_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  (fun (asl,w as g) ->
     let c = find_term (fun t -> try let f,a = strip_comb t in
                                   fst(dest_const f) = "wl_Call" && length a = 4 &&
                                   el 2 a = `cargs:num list`
                                 with Failure _ -> false) w in
     let a = snd(strip_comb c) in
     let tup = rand(el 0 a) in
     let comps = let rec flat t = try let x,y = dest_pair t in x :: flat y with Failure _ -> [t] in flat tup in
     let rh' = el 2 comps and hh = el 3 a in
     MP_TAC(ISPECL [`st:(A,C,FFI)wl_state`; `wl_set_vars cargs xs (rcst1:(A,C,FFI)wl_state)`;
                    `option_lookup (ssa1:num spt)`; `n:num list`;
                    `list_of_seq (\x. 2 * (x + 1)) (LENGTH (n:num list))`;
                    `p0:num_set`; `p1:num_set`; `ret_handler:(A)wl_prog`; rh';
                    `l1:num`; `l2:num`; `dest:num option`; `args:num list`; `cargs:num list`;
                    `SOME (hv,hprog,l1',l2'):(num#(A)wl_prog#num#num)option`; hh;
                    `WALLOCPAUX_sct_R na_fin (ssa_fin:num spt) lt:((A)wl_result)option->
                       (A,C,FFI)wl_state->((A)wl_result)option->(A,C,FFI)wl_state->bool`]
            WALLOCPAUX_call_sim) g) THEN
  ANTS_TAC THENL
   [ALL_TAC; REWRITE_TAC[WALLOCPAUX_sct_R_def] THEN DISCH_THEN ACCEPT_TAC] THEN
  REWRITE_TAC[option_CASE; pair_CASE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wl_set_vars_def] THEN
    UNDISCH_TAC `word_state_eq_rel (st:(A,C,FFI)wl_state) rcst1` THEN
    REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM];
    GEN_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC get_vars_set_vars_eq THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[WALLOCPAUX_even_regs];
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    REWRITE_TAC[INJ; IN_UNIV] THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    REWRITE_TAC[GSYM(ASSUME `set_of_list (ls:num list) = domain (p0:num_set) UNION domain (p1:num_set)`);
                IN_SET_OF_LIST] THEN STRIP_TAC THEN
    MATCH_MP_TAC list_next_var_rename_move_distinct THEN
    MAP_EVERY EXISTS_TAC [`ssa:num spt`; `na + 2`; `ls:num list`; `mov1:(A)wl_prog`;
                          `ssa1:num spt`; `na1:num`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC WALLOCPAUX_ssa_locals_rel_strong_gen THEN
    MAP_EVERY EXISTS_TAC [`na1:num`; `wl_state_locals (rcst1:(A,C,FFI)wl_state)`] THEN
    ASM_REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WALLOCPAUX_lookup_alist_insert_notin THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `ALL is_phy_var (cargs:num list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC(ISPECL [`na_fin:num`; `ssa_fin:num spt`; `lt:(num spt#1 spt#1 spt)list`]
                       WALLOCPAUX_sct_R_pass);
    (MAP_EVERY X_GEN_TAC [`s1:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`;
                       `ys:((A)word_loc)list`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s1:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`; `ssa1:num spt`; `na1:num`;
                 `p0:num_set`; `p1:num_set`; `ls:num list`; `mov2:(A)wl_prog`; `ssa2:num spt`;
                 `na2:num`; `n:num list`; `ys:((A)word_loc)list`; `ret':num list`;
                 `ssa_2_p:num spt`; `na_2_p:num`; `ren_ret_handler:(A)wl_prog`]
         WALLOCPAUX_ret_moves) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `domain (ssa1:num spt) = domain (ssa:num spt) UNION domain (p0:num_set)
                            UNION domain (p1:num_set)`] THEN SET_TAC[];
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p0:num_set)))` THEN
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p1:num_set)))` THEN
      UNDISCH_TAC `na + 2 <= na1` THEN
      REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_union; IN_UNION] THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; ASSUME `set_of_list (ls:num list) =
        domain (p0:num_set) UNION domain (p1:num_set)`; IN_UNION] THEN
      DISCH_THEN(LABEL_TAC "le") THEN DISCH_THEN(LABEL_TAC "h1") THEN
      DISCH_THEN(LABEL_TAC "h0") THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `z < na /\ na + 2 <= na1 ==> z < na1 + 2`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
         [REMOVE_THEN "h0" MATCH_MP_TAC; REMOVE_THEN "h1" MATCH_MP_TAC] THEN
        FIRST_ASSUM ACCEPT_TAC;
        REMOVE_THEN "le" ACCEPT_TAC];
      UNDISCH_TAC `ALL (\x. x < na) (n:num list)` THEN MATCH_MP_TAC MONO_ALL THEN
      GEN_TAC THEN BETA_TAC THEN UNDISCH_TAC `na + 2 <= na1` THEN
      UNDISCH_TAC `na1 + 2 <= na2` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  USE_THEN "ihr" (MP_TAC o SPEC `wl_set_vars n ys (s1:(A,C,FFI)wl_state)`) THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`t3:(A,C,FFI)wl_state`; `ssa_2_p:num spt`; `na_2_p:num`;
                             `lt:(num spt#1 spt#1 spt)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC every_var_mono THEN
    EXISTS_TAC `\x:num. x < na` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    UNDISCH_TAC `na + 2 <= na1` THEN UNDISCH_TAC `na1 + 2 <= na2` THEN
    UNDISCH_TAC `na2 <= na_2_p` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` MP_TAC) THEN
  DISCH_THEN(fun th -> EXISTS_TAC `perm:num->num->num` THEN MP_TAC th) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (ret_handler:(A)wl_prog,
      wl_state_permute_fupd (K perm) (wl_set_vars n ys (s1:(A,C,FFI)wl_state)))`
    [`r0:((A)wl_result)option`; `s0:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `r0 = SOME (wl_Error:(A)wl_result)` THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (ren_ret_handler:(A)wl_prog,t3:(A,C,FFI)wl_state)`
    [`rq:((A)wl_result)option`; `tq:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  DISCH_TAC THEN
  (fun (asl,w as g) ->
     let fi = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "fix_inconsistencies" &&
                                      length(snd(strip_comb t)) = 4 with Failure _ -> false)
                (concl(snd(find (fun (_,th) -> can (find_term (fun t ->
                   try fst(dest_const(fst(strip_comb t))) = "fix_inconsistencies"
                   with Failure _ -> false)) (concl th)) asl))) in
     let prio = el 0 (snd(strip_comb fi)) in
     let ev = find_term (fun t -> try fst(dest_const(rator t)) = "wl_evaluate" &&
                fst(dest_const(fst(strip_comb(fst(dest_pair(rand t)))))) = "wl_Seq"
              with Failure _ -> false) w in
     let seqp,t0 = dest_pair(rand ev) in
     let pp = rand(rator seqp) in
     (MP_TAC(ISPECL [`na_3:num`; `ssa_2:num spt`; `lt:(num spt#1 spt#1 spt)list`;
                     `r0:((A)wl_result)option`; `s0:(A,C,FFI)wl_state`;
                     `rq:((A)wl_result)option`; `tq:(A,C,FFI)wl_state`; `ret_cons:(A)wl_prog`;
                     `na_fin:num`; `ssa_fin:num spt`; pp; t0] WALLOCPAUX_sct_R_seq_cons) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC WALLOCPAUX_sct_R_more THEN EXISTS_TAC `na_2:num` THEN CONJ_TAC THENL
           [UNDISCH_TAC `na_2 + 4 <= na_3` THEN ARITH_TAC;
            ASM_REWRITE_TAC[WALLOCPAUX_sct_R_def]];
          MP_TAC(INST_TYPE [`:C`,`:B`; `:FFI`,`:C`]
                   (ISPECL [prio; `na_3:num`; `ssa_2:num spt`; `ssa_3:num spt`]
                      fix_inconsistencies_correctL)) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na_2:num` THEN
            ASM_REWRITE_TAC[] THEN UNDISCH_TAC `na_2 + 4 <= na_3` THEN ARITH_TAC;
            ASM_REWRITE_TAC[pair_CASE]]];
        DISCH_THEN ACCEPT_TAC]) g));
    (MAP_EVERY X_GEN_TAC [`s1:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`;
                       `y:(A)word_loc`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s1:(A,C,FFI)wl_state`; `t1:(A,C,FFI)wl_state`; `ssa1:num spt`; `na1:num`;
                 `p0:num_set`; `p1:num_set`; `ls:num list`; `mov2:(A)wl_prog`; `ssa2:num spt`;
                 `na2:num`; `hv:num`; `y:(A)word_loc`; `na_2:num`; `ren_exc_handler:(A)wl_prog`]
         WALLOCPAUX_exc_moves) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `domain (ssa1:num spt) = domain (ssa:num spt) UNION domain (p0:num_set)
                            UNION domain (p1:num_set)`] THEN SET_TAC[];
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p0:num_set)))` THEN
      UNDISCH_TAC `ALL (\x. x < na) (MAP FST (toAList (p1:num_set)))` THEN
      UNDISCH_TAC `na + 2 <= na1` THEN
      REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_union; IN_UNION] THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; ASSUME `set_of_list (ls:num list) =
        domain (p0:num_set) UNION domain (p1:num_set)`; IN_UNION] THEN
      DISCH_THEN(LABEL_TAC "le") THEN DISCH_THEN(LABEL_TAC "h1") THEN
      DISCH_THEN(LABEL_TAC "h0") THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `z < na /\ na + 2 <= na1 ==> z < na1 + 2`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
         [REMOVE_THEN "h0" MATCH_MP_TAC; REMOVE_THEN "h1" MATCH_MP_TAC] THEN
        FIRST_ASSUM ACCEPT_TAC;
        REMOVE_THEN "le" ACCEPT_TAC];
      UNDISCH_TAC `na2 <= na_2_p` THEN UNDISCH_TAC `na_2_p <= na_2` THEN ARITH_TAC;
      UNDISCH_TAC `hv < na` THEN UNDISCH_TAC `na + 2 <= na1` THEN UNDISCH_TAC `na1 + 2 <= na2` THEN
      UNDISCH_TAC `na2 <= na_2_p` THEN UNDISCH_TAC `na_2_p <= na_2` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  USE_THEN "ihh" (MP_TAC o SPEC `wl_set_var hv y (s1:(A,C,FFI)wl_state)`) THEN
  REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`t3:(A,C,FFI)wl_state`; `insert hv na_2 (ssa2:num spt)`;
                             `na_2 + 4`; `lt:(num spt#1 spt#1 spt)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WALLOCPAUX_is_alloc_var_add4 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC every_var_mono THEN
      EXISTS_TAC `\x:num. x < na` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      UNDISCH_TAC `na + 2 <= na1` THEN UNDISCH_TAC `na1 + 2 <= na2` THEN
      UNDISCH_TAC `na2 <= na_2_p` THEN UNDISCH_TAC `na_2_p <= na_2` THEN ARITH_TAC;
      MATCH_MP_TAC ssa_map_ok_extend THEN CONJ_TAC THENL
       [MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na2:num` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `na2 <= na_2_p` THEN UNDISCH_TAC `na_2_p <= na_2` THEN ARITH_TAC;
        ASM_MESON_TAC[convention_partitions]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` MP_TAC) THEN
  DISCH_THEN(fun th -> EXISTS_TAC `perm:num->num->num` THEN MP_TAC th) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (hprog:(A)wl_prog,
      wl_state_permute_fupd (K perm) (wl_set_var hv y (s1:(A,C,FFI)wl_state)))`
    [`r0:((A)wl_result)option`; `s0:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `r0 = SOME (wl_Error:(A)wl_result)` THEN ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (ren_exc_handler:(A)wl_prog,t3:(A,C,FFI)wl_state)`
    [`rq:((A)wl_result)option`; `tq:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN DISCH_TAC THEN
  (fun (asl,w as g) ->
     let fi = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "fix_inconsistencies" &&
                                      length(snd(strip_comb t)) = 4 with Failure _ -> false)
                (concl(snd(find (fun (_,th) -> can (find_term (fun t ->
                   try fst(dest_const(fst(strip_comb t))) = "fix_inconsistencies"
                   with Failure _ -> false)) (concl th)) asl))) in
     let prio = el 0 (snd(strip_comb fi)) in
     let ev = find_term (fun t -> try fst(dest_const(rator t)) = "wl_evaluate" &&
                fst(dest_const(fst(strip_comb(fst(dest_pair(rand t)))))) = "wl_Seq"
              with Failure _ -> false) w in
     let seqp,t0 = dest_pair(rand ev) in
     let pp = rand(rator seqp) in
     (MP_TAC(ISPECL [`na_3:num`; `ssa_3:num spt`; `lt:(num spt#1 spt#1 spt)list`;
                     `r0:((A)wl_result)option`; `s0:(A,C,FFI)wl_state`;
                     `rq:((A)wl_result)option`; `tq:(A,C,FFI)wl_state`; `exc_cons:(A)wl_prog`;
                     `na_fin:num`; `ssa_fin:num spt`; pp; t0] WALLOCPAUX_sct_R_seq_cons) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[WALLOCPAUX_sct_R_def];
          MP_TAC(INST_TYPE [`:C`,`:B`; `:FFI`,`:C`]
                   (ISPECL [`na_3:num`; `ssa_2:num spt`; `ssa_3:num spt`; prio]
                      fix_inconsistencies_correctR)) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[pair_CASE]]];
        DISCH_THEN ACCEPT_TAC]) g))]);;

let WALLOCPAUX_sct_Call = prove
 (`!a0 a1 a2 a3.
       (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Call a0 a1 a2 a3:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Call a0 a1 a2 a3:(A)wl_prog)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `a0:(num list#(num_set#num_set)#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `q0:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [DISCH_TAC THEN REWRITE_TAC[WALLOCPAUX_sct_Call_tail]; ALL_TAC] THEN
  SUBGOAL_THEN `?n names rh l1 l2. q0 = (n:num list,names:num_set#num_set,rh:(A)wl_prog,l1:num,l2:num)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPEC `a3:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [DISCH_TAC THEN MATCH_MP_TAC WALLOCPAUX_sct_Call_ret_none THEN
    FIRST_ASSUM MATCH_MP_TAC THEN WALLOCPAUX_SIZE_TAC;
    SUBGOAL_THEN `?v hp k1 k2. hq = (v:num,hp:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC WALLOCPAUX_sct_Call_ret_some THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN WALLOCPAUX_SIZE_TAC]);;

(* the Inst case in the form of the induction *)

let WALLOCPAUX_sct_Inst_ih = prove
 (`!a0. (!q. wl_prog_size (\x:A. 0) q < wl_prog_size (\x:A. 0) (wl_Inst a0:(A)wl_prog)
            ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st q)
       ==> !st:(A,C,FFI)wl_state. WALLOCPAUX_sct_Q st (wl_Inst a0:(A)wl_prog)`,
  REWRITE_TAC[WALLOCPAUX_sct_Inst]);;

(* HOL4 line 7666 *)
let ssa_cc_trans_correct = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state) cst ssa na lt.
     word_state_eq_rel st cst /\
     ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
     is_alloc_var na /\
     wl_every_var (\x. x < na) prog /\
     ssa_map_ok na ssa /\
     lt_ok lt
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
           let (res',rcst) = wl_evaluate (prog',cst) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE -> ssa_locals_rel na' ssa' (wl_state_locals rst) (wl_state_locals rcst)
              | SOME (wordSem_Break n) ->
                  (match oEL n lt with
                     SOME (tgt_ssa,_,exit_names) ->
                       strong_locals_rel (option_lookup tgt_ssa) (domain exit_names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME (wordSem_Continue n) ->
                  (match oEL n lt with
                     SOME (tgt_ssa,names,_) ->
                       strong_locals_rel (option_lookup tgt_ssa) (domain names)
                         (wl_state_locals rst) (wl_state_locals rcst)
                   | NONE -> T)
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`,
  SUBGOAL_THEN `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state). WALLOCPAUX_sct_Q st prog`
    MP_TAC THENL
   [MATCH_MP_TAC WALLOCPAUX_prog_size_induct THEN X_GEN_TAC `p:(A)wl_prog` THEN
    STRUCT_CASES_TAC (ISPEC `p:(A)wl_prog` (CONJUNCT1 (cases "wl_prog"))) THEN
    FIRST (map (fun th -> MATCH_ACCEPT_TAC th ORELSE MATCH_ACCEPT_TAC (SPEC_ALL th))
       [WALLOCPAUX_sct_Skip;
        WALLOCPAUX_sct_Move;
        WALLOCPAUX_sct_Inst_ih;
        WALLOCPAUX_sct_Assign;
        WALLOCPAUX_sct_Get;
        WALLOCPAUX_sct_Set;
        WALLOCPAUX_sct_Store;
        WALLOCPAUX_sct_MustTerminate;
        WALLOCPAUX_sct_Call;
        WALLOCPAUX_sct_Seq;
        WALLOCPAUX_sct_If;
        WALLOCPAUX_sct_Loop;
        WALLOCPAUX_sct_Alloc;
        WALLOCPAUX_sct_StoreConsts;
        WALLOCPAUX_sct_Raise;
        WALLOCPAUX_sct_Return;
        WALLOCPAUX_sct_Break;
        WALLOCPAUX_sct_Continue;
        WALLOCPAUX_sct_Tick;
        WALLOCPAUX_sct_OpCurrHeap;
        WALLOCPAUX_sct_LocValue;
        WALLOCPAUX_sct_Install;
        WALLOCPAUX_sct_CodeBufferWrite;
        WALLOCPAUX_sct_DataBufferWrite;
        WALLOCPAUX_sct_FFI;
        WALLOCPAUX_sct_ShareInst]);
    REWRITE_TAC[WALLOCPAUX_sct_Q_def] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* max_var and limit_var                                                     *)
(* ------------------------------------------------------------------------- *)

let WALLOCPAUX_MAXL = prove
 (`!x a b. x <= a ==> x <= MAX a b`, REWRITE_TAC[MAX] THEN ARITH_TAC);;

let WALLOCPAUX_MAXR = prove
 (`!x a b. x <= b ==> x <= MAX a b`, REWRITE_TAC[MAX] THEN ARITH_TAC);;

let WALLOCPAUX_ALL_MAX_LIST = prove
 (`!l m. MAX_LIST l <= m ==> ALL (\x. x <= m) l`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MAX_LIST_PROPERTY; LE_TRANS]);;

(* close x <= e for a syntactic MAX-tree e containing x *)

let rec WALLOCPAUX_LE_TREE_TAC : tactic = fun (asl,w as g) ->
  let s,e = dest_binop `(<=):num->num->bool` w in
  if s = e then REWRITE_TAC[LE_REFL] g else
  try let a,b = dest_binop `MAX` e in
      if free_in s a then (MATCH_MP_TAC WALLOCPAUX_MAXL THEN WALLOCPAUX_LE_TREE_TAC) g
      else (MATCH_MP_TAC WALLOCPAUX_MAXR THEN WALLOCPAUX_LE_TREE_TAC) g
  with Failure _ ->
    (CHANGED_TAC(REWRITE_TAC[MAX_LIST_CONS; MAX_LIST_NIL; MAX_LIST_APPEND]) THEN
     WALLOCPAUX_LE_TREE_TAC) g;;

(* HOL4 line 10211 *)
let max_var_exp_max = prove
 (`!exp:(A)wl_exp. every_var_exp (\x. x <= max_var_exp exp) exp`,
  MATCH_MP_TAC max_var_exp_ind THEN
  REWRITE_TAC[every_var_exp_def; max_var_exp_def; LE_REFL] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `e:(A)wl_exp` THEN
    DISCH_TAC THEN MATCH_MP_TAC every_var_exp_mono THEN
    EXISTS_TAC `\x. x <= max_var_exp (e:(A)wl_exp)` THEN ASM_SIMP_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC MAX_LIST_PROPERTY THEN REWRITE_TAC[MEM_MAP] THEN
    EXISTS_TAC `e:(A)wl_exp` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC every_var_exp_mono THENL
     [EXISTS_TAC `\x. x <= max_var_exp (exp1:(A)wl_exp)`;
      EXISTS_TAC `\x. x <= max_var_exp (exp2:(A)wl_exp)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[MAX] THEN ARITH_TAC]);;

(* HOL4 line 10237 *)
let max3_eq = prove
 (`!x y z. max3 x y z = MAX x (MAX y z)`,
  REWRITE_TAC[max3_def; MAX] THEN ARITH_TAC);;

(* HOL4 line 10227 *)
let max_var_inst_max = prove
 (`!inst:(A)inst. every_var_inst (\x. x <= max_var_inst inst) inst`,
  MP_TAC(ISPEC `\(i:(A)inst). every_var_inst (\x. x <= max_var_inst i) i` max_var_inst_ind) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[every_var_inst_def; max_var_inst_def; max3_eq] THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[every_var_imm_def; WALLOCPAUX_reg_imm_CASE]) THEN
  TRY(MP_TAC(ISPEC `n:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[every_var_imm_def; WALLOCPAUX_reg_imm_CASE]) THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN WALLOCPAUX_LE_TREE_TAC);;

let WALLOCPAUX_exp_le = prove
 (`!(exp:(A)wl_exp) m. max_var_exp exp <= m ==> every_var_exp (\x. x <= m) exp`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC every_var_exp_mono THEN
  EXISTS_TAC `\x. x <= max_var_exp (exp:(A)wl_exp)` THEN REWRITE_TAC[max_var_exp_max] THEN
  GEN_TAC THEN UNDISCH_TAC `max_var_exp (exp:(A)wl_exp) <= m` THEN ARITH_TAC);;

let WALLOCPAUX_inst_le = prove
 (`!(i:(A)inst) m. max_var_inst i <= m ==> every_var_inst (\x. x <= m) i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC every_var_inst_mono THEN
  EXISTS_TAC `\x. x <= max_var_inst (i:(A)inst)` THEN REWRITE_TAC[max_var_inst_max] THEN
  GEN_TAC THEN UNDISCH_TAC `max_var_inst (i:(A)inst) <= m` THEN ARITH_TAC);;

let WALLOCPAUX_prog_le = prove
 (`!(p:(A)wl_prog) m. wl_every_var (\x. x <= max_var p) p /\ max_var p <= m
                      ==> wl_every_var (\x. x <= m) p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC every_var_mono THEN
  EXISTS_TAC `\x. x <= max_var (p:(A)wl_prog)` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN UNDISCH_TAC `max_var (p:(A)wl_prog) <= m` THEN ARITH_TAC);;

let WALLOCPAUX_MAXV_TAC : tactic =
  FIRST [WALLOCPAUX_LE_TREE_TAC;
         MATCH_MP_TAC WALLOCPAUX_ALL_MAX_LIST THEN WALLOCPAUX_LE_TREE_TAC;
         MATCH_MP_TAC WALLOCPAUX_exp_le THEN WALLOCPAUX_LE_TREE_TAC;
         MATCH_MP_TAC WALLOCPAUX_inst_le THEN WALLOCPAUX_LE_TREE_TAC;
         MATCH_MP_TAC WALLOCPAUX_prog_le THEN CONJ_TAC THENL
          [FIRST_ASSUM ACCEPT_TAC; WALLOCPAUX_LE_TREE_TAC]];;


(* the Call case of max_var_max *)

let WALLOCPAUX_max_var_max_Call = prove
 (`!(ret:(num list#(num_set#num_set)#(A)wl_prog#num#num)option) dest args h.
     (!v cutset l1 l2 ret_handler.
        ret = SOME (v,cutset,ret_handler,l1,l2)
        ==> wl_every_var (\x. x <= max_var ret_handler) ret_handler) /\
     (!v cutset ret_handler l1 l2 v' l1' l2' prog.
        ret = SOME (v,cutset,ret_handler,l1,l2) /\ h = SOME (v',prog,l1',l2')
        ==> wl_every_var (\x. x <= max_var prog) (prog:(A)wl_prog))
     ==> wl_every_var (\x. x <= max_var (wl_Call ret dest args h)) (wl_Call ret dest args h)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `ret:(num list#(num_set#num_set)#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `q0:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC[wl_every_var_def; max_var_def; LET_DEF; LET_END_DEF; option_CASE] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[option_CASE] THEN
    DISCH_TAC THEN MATCH_MP_TAC WALLOCPAUX_ALL_MAX_LIST THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v cs rh l1 l2. q0 = (v:num list,cs:num_set#num_set,rh:(A)wl_prog,l1:num,l2:num)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `?c0 c1. cs = (c0:num_set,c1:num_set)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [ALL_TAC;
    SUBGOAL_THEN `?hv hp k1 k2. hq = (hv:num,hp:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC]] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; option_DISTINCT] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MESON[th] `wl_every_var (\x. x <= max_var rh) (rh:(A)wl_prog)`) THEN
    (try ASSUME_TAC(MESON[th] `wl_every_var (\x. x <= max_var hp) (hp:(A)wl_prog)`) with Failure _ -> ALL_TAC)) THEN
  REWRITE_TAC[wl_every_var_def; max_var_def; every_name_def; max3_eq; cutsets_max_def;
              LET_DEF; LET_END_DEF; option_CASE; pair_CASE; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[option_CASE; pair_CASE] THEN
  REPEAT CONJ_TAC THEN WALLOCPAUX_MAXV_TAC);;

(* HOL4 line 10243 *)
let max_var_max = prove
 (`!prog:(A)wl_prog. wl_every_var (\x. x <= max_var prog) prog`,
  MATCH_MP_TAC max_var_ind THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_ACCEPT_TAC WALLOCPAUX_max_var_max_Call) THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN
  REWRITE_TAC[wl_every_var_def; max_var_def; every_name_def; max3_eq; cutsets_max_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[every_var_imm_def; WALLOCPAUX_reg_imm_CASE]) THEN
  TRY(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN WALLOCPAUX_MAXV_TAC);;

(* HOL4 line 10299 *)
let limit_var_props = prove
 (`!(prog:(A)wl_prog) lim.
     limit_var prog = lim ==> is_alloc_var lim /\ wl_every_var (\x. x < lim) prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[limit_var_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `x = max_var (prog:(A)wl_prog)` THEN CONJ_TAC THENL
   [REWRITE_TAC[is_alloc_var_def] THEN
    MP_TAC(SPECL [`x:num`; `4`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    ABBREV_TAC `q = x DIV 4` THEN ABBREV_TAC `r = x MOD 4` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x + 4 - r) + 1 = (q + 1) * 4 + 1` SUBST1_TAC THENL
     [UNDISCH_TAC `x = q * 4 + r` THEN UNDISCH_TAC `r < 4` THEN ARITH_TAC;
      REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV];
    MATCH_MP_TAC every_var_mono THEN EXISTS_TAC `\y. y <= max_var (prog:(A)wl_prog)` THEN
    ASM_REWRITE_TAC[max_var_max] THEN ARITH_TAC]);;

(* HOL4 line 10139 *)
let setup_ssa_props = prove
 (CASE_TERM
  `!lim (st:(A,C,FFI)wl_state) n (prog:(A)wl_prog).
     is_alloc_var lim /\ domain (wl_state_locals st) = set_of_list (even_list n)
     ==> let (mov:(A)wl_prog,ssa,na) = setup_ssa n lim prog in
         let (res,cst) = wl_evaluate (mov,st) in
           res = NONE /\
           word_state_eq_rel st cst /\
           ssa_map_ok na ssa /\
           ssa_locals_rel na ssa (wl_state_locals st) (wl_state_locals cst) /\
           is_alloc_var na /\
           lim <= na`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[setup_ssa_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `args = even_list n` THEN
  SUBGOAL_THEN `ALL_DISTINCT (args:num list) /\ (!x. MEM x args ==> is_phy_var x)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "args" THEN REWRITE_TAC[even_list_def; ALL_DISTINCT_GENLIST; MEM_GENLIST] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[is_phy_var_def] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 * m = m * 2 + 0`] THEN REWRITE_TAC[MOD_MULT_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename (args:num list) (LN:num spt) lim`
    [`new_ls:num list`; `ssa1:num spt`; `n1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`args:num list`; `LN:num spt`; `lim:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`args:num list`; `LN:num spt`; `lim:num`; `new_ls:num list`; `ssa1:num spt`;
                 `n1:num`] list_next_var_rename_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ssa_map_ok_def; lookup_def; option_DISTINCT]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`args:num list`; `st:(A,C,FFI)wl_state`] word_allocProof_get_vars_eq) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:((A)word_loc)list` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM))) THEN
  ABBREV_TAC `L = MAP (\x. THE (lookup x (ssa1:num spt))) (args:num list)` THEN
  SUBGOAL_THEN `ALL_DISTINCT (L:num list)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL_DISTINCT (new_ls:num list)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (L:num list) = LENGTH (args:num list) /\
                LENGTH (vs:((A)word_loc)list) = LENGTH args` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `MAP (\x. THE (lookup x (ssa1:num spt))) (args:num list) = L`;
      UNDISCH_TAC `MAP (\x. THE (lookup x (wl_state_locals (st:(A,C,FFI)wl_state))))
                     (args:num list) = vs`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[wl_evaluate_def] THEN
  SUBGOAL_THEN `LENGTH (L:num list) = LENGTH (args:num list)` (LABEL_TAC "lz") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "lz" (fun th -> REWRITE_TAC[MATCH_MP MAP_FST_ZIP th; MATCH_MP MAP_SND_ZIP th]) THEN
  ASM_REWRITE_TAC[option_CASE; pair_CASE; wl_set_vars_def] THEN CONJ_TAC THENL
   [REWRITE_TAC[word_state_eq_rel_def; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  REWRITE_TAC[ssa_locals_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (x:num) args` ASSUME_TAC THENL
     [UNDISCH_TAC `domain (ssa1:num spt) = domain (LN:num spt) UNION set_of_list args` THEN
      REWRITE_TAC[EXTENSION; IN_UNION; domain_lookup; lookup_def; option_DISTINCT;
                  IN_SET_OF_LIST] THEN
      DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[domain_alist_insert; IN_UNION; IN_SET_OF_LIST; LENGTH_MAP] THEN DISJ2_TAC THEN
    EXPAND_TAC "L" THEN REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `x:num` THEN
    ASM_REWRITE_TAC[THE_DEF];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `v:(A)word_loc`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `MEM (x:num) args` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
    UNDISCH_TAC `domain (wl_state_locals (st:(A,C,FFI)wl_state)) = set_of_list args` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[domain_lookup] THEN
    EXISTS_TAC `v:(A)word_loc` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION; IN_SET_OF_LIST];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `MEM (x:num) args`)) THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `THE (lookup x (ssa1:num spt)) = EL i (L:num list)` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN ASM_SIMP_TAC[EL_MAP]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `SOME (EL i (vs:((A)word_loc)list))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MISC3AUX_lookup_alist_insert_EL THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `vs:((A)word_loc)list`)) THEN
      ASM_SIMP_TAC[EL_MAP] THEN
      UNDISCH_TAC `lookup x (wl_state_locals (st:(A,C,FFI)wl_state)) = SOME (v:(A)word_loc)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[THE_DEF]];
    DISCH_TAC THEN
    SUBGOAL_THEN `is_phy_var x` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[convention_partitions]]);;

(* HOL4 line 10337 *)
let full_ssa_cc_trans_correct = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) (st:(A,C,FFI)wl_state) n.
     domain (wl_state_locals st) = set_of_list (even_list n)
     ==> ?perm'.
           let (res,rst) = wl_evaluate (prog,wl_state_permute_fupd (K perm') st) in
           if res = SOME wl_Error then T else
           let (res',rcst) = wl_evaluate (full_ssa_cc_trans n prog,st) in
             res = res' /\
             word_state_eq_rel rst rcst /\
             (match res with
                NONE -> T
              | SOME (wordSem_Break _) -> T
              | SOME (wordSem_Continue _) -> T
              | SOME _ -> wl_state_locals rst = wl_state_locals rcst)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[full_ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `limit_var (prog:(A)wl_prog)`] limit_var_props) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`limit_var (prog:(A)wl_prog)`; `st:(A,C,FFI)wl_state`; `n:num`;
                 `prog:(A)wl_prog`] setup_ssa_props) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `setup_ssa n (limit_var (prog:(A)wl_prog)) prog:(A)wl_prog#num spt#num`
    [`mov:(A)wl_prog`; `ssa:num spt`; `na:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (mov:(A)wl_prog,st:(A,C,FFI)wl_state)`
    [`r0:((A)wl_result)option`; `cst:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (prog:(A)wl_prog) ssa na []`
    [`prog':(A)wl_prog`; `ssa':num spt`; `na':num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`mov:(A)wl_prog`; `prog':(A)wl_prog`; `st:(A,C,FFI)wl_state`;
                 `cst:(A,C,FFI)wl_state`] IL2AUX_evaluate_Seq_NONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `st:(A,C,FFI)wl_state`; `cst:(A,C,FFI)wl_state`;
                 `ssa:num spt`; `na:num`; `[]:(num spt#1 spt#1 spt)list`]
         ssa_cc_trans_correct) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[lt_ok_def; ALL] THEN MATCH_MP_TAC every_var_mono THEN
    EXISTS_TAC `\x. x < limit_var (prog:(A)wl_prog)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `limit_var (prog:(A)wl_prog) <= na` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  DISCH_THEN(X_CHOOSE_THEN `perm:num->num->num` MP_TAC) THEN
  DISCH_THEN(fun th -> EXISTS_TAC `perm:num->num->num` THEN MP_TAC th) THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (prog:(A)wl_prog,
      wl_state_permute_fupd (K perm) (st:(A,C,FFI)wl_state))`
    [`res:((A)wl_result)option`; `rst:(A,C,FFI)wl_state`] THEN
  WALLOCPAUX_TUPLE_TAC `wl_evaluate (prog':(A)wl_prog,cst:(A,C,FFI)wl_state)`
    [`res':((A)wl_result)option`; `rcst:(A,C,FFI)wl_state`] THEN
  REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `res':((A)wl_result)option`)) THEN
  WALLOCPAUX_RESULT_CASES_TAC `res:((A)wl_result)option` THEN
  RULE_ASSUM_TAC(REWRITE_RULE([option_CASE; WALLOCPAUX_wl_result_CASE] @
                              WALLOCPAUX_wl_result_distinct)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* the conventions established by the SSA transformation                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4 line 10377 *)
let fake_moves_conventions = prove
 (CASE_TERM
  `!prio ls (ssaL:num spt) (ssaR:num spt) na.
     let (a:(A)wl_prog,b:(A)wl_prog,c,d,e) = fake_moves prio ls ssaL ssaR na in
       every_stack_var is_stack_var a /\
       every_stack_var is_stack_var b /\
       call_arg_convention a /\
       call_arg_convention b`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fake_moves_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE; every_stack_var_def; call_arg_convention_def] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ssaL:num spt`; `ssaR:num spt`; `na:num`]) THEN
  WALLOCPAUX_TUPLE_TAC `fake_moves prio (t:num list) (ssaL:num spt) (ssaR:num spt) na:
                          (A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`sL:(A)wl_prog`; `sR:(A)wl_prog`; `n1:num`; `aL:num spt`; `aR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lookup (h:num) (aL:num spt)` (cases "option")) THEN
  MP_TAC(ISPEC `lookup (h:num) (aR:num spt)` (cases "option")) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  ASM_REWRITE_TAC[every_stack_var_def; call_arg_convention_def; fake_move_def;
                  inst_arg_convention_def]);;

(* HOL4 line 10395 *)
let fix_inconsistencies_conventions = prove
 (CASE_TERM
  `!(ssaL:num spt) (ssaR:num spt) na prio.
     let (a:(A)wl_prog,b:(A)wl_prog,c,d) = fix_inconsistencies prio ssaL ssaR na in
       every_stack_var is_stack_var a /\
       every_stack_var is_stack_var b /\
       call_arg_convention a /\
       call_arg_convention b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fix_inconsistencies_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves (MAP FST (toAList (sptree_union (ssaL:num spt) ssaR)))
                          ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`prio:(1+1)option`; `MAP FST (toAList (sptree_union (ssaL:num spt) ssaR))`;
                 `sL:num spt`; `sR:num spt`; `n1:num`] fake_moves_conventions) THEN
  WALLOCPAUX_TUPLE_TAC `fake_moves (prio:(1+1)option)
      (MAP FST (toAList (sptree_union (ssaL:num spt) ssaR))) sL sR n1:
      (A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`qL:(A)wl_prog`; `qR:(A)wl_prog`; `n2:num`; `tL:num spt`; `tR:num spt`] THEN
  REWRITE_TAC[pair_CASE; every_stack_var_def; call_arg_convention_def] THEN
  SIMP_TAC[]);;

(* HOL4 line 10413 *)
let every_name_def2 = prove
 (`!P (t:cutsets).
     every_name P t <=> ALL P (MAP FST (toAList (sptree_union (FST t) (SND t))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[every_name_def; GSYM ALL_MEM; toAList_domain; domain_union;
                                  IN_UNION] THEN
  MESON_TAC[]);;

(* HOL4 line 10420 *)
let union_apply_nummaps_key = prove
 (`!f (p:num_set#num_set).
     domain (sptree_union (FST (apply_nummaps_key f p)) (SND (apply_nummaps_key f p))) =
     domain (apply_nummap_key f (sptree_union (FST p) (SND p)))`,
  REWRITE_TAC[nummaps_to_nummap; domain_union; apply_nummap_key_domain; IMAGE_UNION]);;

(* HOL4 line 10434 *)
let fake_seq_pre_alloc_conventions = prove
 (`!ls. pre_alloc_conventions (ITLIST wl_Seq (MAP (\r. fake_move r) ls) (wl_Skip:(A)wl_prog))`,
  LIST_INDUCT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pre_alloc_conventions_def]) THEN
  ASM_REWRITE_TAC[pre_alloc_conventions_def; MAP; ITLIST; every_stack_var_def;
                  call_arg_convention_def] THEN
  REWRITE_TAC[fake_move_def; every_stack_var_def; call_arg_convention_def;
              inst_arg_convention_def]);;

(* HOL4 line 10442 *)
let fake_seq_every_inst_distinct_tar_reg = prove
 (`!ls. every_inst distinct_tar_reg
          (ITLIST wl_Seq (MAP (\r. fake_move r) ls) (wl_Skip:(A)wl_prog))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ITLIST; every_inst_def] THEN
  REWRITE_TAC[fake_move_def; every_inst_def; distinct_tar_reg_def]);;

(* HOL4 line 10449 *)
let fake_seq_full_inst_ok_less = prove
 (`!(c:(A)asm_config) ls.
     full_inst_ok_less c (ITLIST wl_Seq (MAP (\r. fake_move r) ls) (wl_Skip:(A)wl_prog))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ITLIST; full_inst_ok_less_def] THEN
  REWRITE_TAC[fake_move_def; full_inst_ok_less_def; inst_ok_less_def]);;

(* the program of a renaming move is a single Move *)

let WALLOCPAUX_lnvrm_is_move = prove
 (`!(ssa:num spt) n ls (mov:(A)wl_prog) ssa' n'.
     list_next_var_rename_move ssa n ls = (mov,ssa',n') ==> ?pri moves. mov = wl_Move pri moves`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SPEC_TAC(`list_next_var_rename ls (ssa:num spt) n`, `q:num list#num spt#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

let WALLOCPAUX_LOOPSETUP_TAC (lem:thm) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[loop_setup_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `setup_prog:(A)wl_prog`)) THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename_move"
       with Failure _ -> false)
    then CHOOSE_THEN (CHOOSE_THEN SUBST1_TAC) (MATCH_MP WALLOCPAUX_lnvrm_is_move th)
    else NO_TAC) THEN
  MP_TAC lem THEN
  REWRITE_TAC[pre_alloc_conventions_def; every_stack_var_def; call_arg_convention_def;
              every_inst_def; full_inst_ok_less_def] THEN
  SIMP_TAC[];;

(* HOL4 line 10456 *)
let loop_setup_pre_alloc_conventions = prove
 (`!(names:1 spt) (exit_names:1 spt) (ssa:num spt) na (setup_prog:(A)wl_prog)
    ssa_refreshed na_refreshed.
     loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed)
     ==> pre_alloc_conventions setup_prog`,
  WALLOCPAUX_LOOPSETUP_TAC (ISPEC `fresh_pos_ls:num list` fake_seq_pre_alloc_conventions));;

(* HOL4 line 10470 *)
let loop_setup_props_local = prove
 (`!(names:1 spt) (exit_names:1 spt) (ssa:num spt) na (setup_prog:(A)wl_prog)
    ssa_refreshed na_refreshed.
     loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) /\
     ssa_map_ok na ssa /\ is_alloc_var na
     ==> is_alloc_var na_refreshed /\ ssa_map_ok na_refreshed ssa_refreshed /\
         na <= na_refreshed`,
  REWRITE_TAC[WALLOCPAUX_loop_setup_props]);;

(* HOL4 line 10483 *)
let loop_setup_every_inst_distinct_tar_reg = prove
 (`!(names:1 spt) (exit_names:1 spt) (ssa:num spt) na (setup_prog:(A)wl_prog)
    ssa_refreshed na_refreshed.
     loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed)
     ==> every_inst distinct_tar_reg setup_prog`,
  WALLOCPAUX_LOOPSETUP_TAC (ISPEC `fresh_pos_ls:num list` fake_seq_every_inst_distinct_tar_reg));;

(* HOL4 line 10495 *)
let loop_setup_full_inst_ok_less = prove
 (`!(names:1 spt) (exit_names:1 spt) (ssa:num spt) na (setup_prog:(A)wl_prog)
    ssa_refreshed na_refreshed (c:(A)asm_config).
     loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed)
     ==> full_inst_ok_less c setup_prog`,
  WALLOCPAUX_LOOPSETUP_TAC (ISPECL [`c:(A)asm_config`; `fresh_pos_ls:num list`]
                              fake_seq_full_inst_ok_less));;

(* the names given by a renaming move started at a stack variable are stack *)
(* variables                                                                  *)

let WALLOCPAUX_lnvrm_stack = prove
 (`!(ssa:num spt) n ls (mov:(A)wl_prog) ssa' n'.
     list_next_var_rename_move ssa n ls = (mov,ssa',n') /\ ALL_DISTINCT ls /\ is_stack_var n
     ==> !x. MEM x ls ==> is_stack_var (option_lookup ssa' x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename ls (ssa:num spt) n`
    [`new:num list`; `s1:num spt`; `n1:num`] THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && is_var(rhs(concl th))))) THEN
  MP_TAC(ISPECL [`ls:num list`; `ssa:num spt`; `n:num`] list_next_var_rename_lemma_2) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_lemma_1) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  STRIP_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "?" with Failure _ -> false)) (concl th)
    then MP_TAC(SPEC `x:num` th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `z:num`) THEN
  ASM_REWRITE_TAC[option_lookup_def; option_CASE] THEN
  SUBGOAL_THEN `MEM (z:num) new` MP_TAC THENL
   [UNDISCH_TAC `new = MAP (\x. THE (lookup x (ssa':num spt))) ls` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `x:num` THEN
    ASM_REWRITE_TAC[THE_DEF];
    ALL_TAC] THEN
  UNDISCH_TAC `new = MAP (\x. 4 * x + n) (COUNT_LIST (LENGTH (ls:num list)))` THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (SUBST1_TAC o CONJUNCT2)) THEN
  UNDISCH_TAC `is_stack_var n` THEN REWRITE_TAC[is_stack_var_def] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 * k + n = k * 4 + n`] THEN REWRITE_TAC[MOD_MULT_ADD]);;

(* the cut set of a renamed call or allocation consists of stack variables *)

let WALLOCPAUX_stack_set_stack = prove
 (`!(ssa:num spt) na (p0:num_set) (p1:num_set) (mov:(A)wl_prog) ssa' na'.
     is_alloc_var na /\
     list_next_var_rename_move ssa (na + 2) (MAP FST (toAList (sptree_union p0 p1))) = (mov,ssa',na')
     ==> every_name is_stack_var (apply_nummaps_key (option_lookup ssa') (p0,p1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] WALLOCPAUX_lnvrm_stack)) THEN
  REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
  ANTS_TAC THENL [MATCH_MP_TAC is_alloc_var_flip THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[toAList_domain; every_name_def2; GSYM ALL_MEM; union_apply_nummaps_key] THEN
  REWRITE_TAC[FST; SND; apply_nummap_key_domain; IN_IMAGE] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[]);;

let WALLOCPAUX_ssa_reconcile_cases = prove
 (`!(cur:num spt) (tgt:num spt) (ns:A spt).
     ssa_reconcile cur tgt ns = (wl_Skip:(B)wl_prog) \/
     ?moves. ssa_reconcile cur tgt ns = (wl_Move 1 moves:(B)wl_prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_reconcile_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN MESON_TAC[]);;

let WALLOCPAUX_inst_pac = prove
 (CASE_TERM
  `!(i:(A)inst) (ssa:num spt) na.
     let (p,s,n) = ssa_cc_trans_inst i ssa na in pre_alloc_conventions (p:(A)wl_prog)`,
  MP_TAC(ISPEC (CASE_TERM `\(i:(A)inst) (ssa:num spt) (na:num).
                  let (p,s,n) = ssa_cc_trans_inst i ssa na in pre_alloc_conventions (p:(A)wl_prog)`)
         ssa_cc_trans_inst_ind) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_cc_trans_inst_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[WALLOCPAUX_reg_imm_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[pair_CASE; pre_alloc_conventions_def; every_stack_var_def; call_arg_convention_def;
              inst_arg_convention_def]);;

(* helpers for the convention proofs by ssa_cc_trans_ind (local to this    *)
(* file); pre normalises the hypotheses on the source program, pr is the  *)
(* property of the result and rew rewrites it with its definition         *)

let WALLOCPAUX_CONV_SEQ_TAC (pre:tactic) (pr:term) (rew:tactic) : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN pre THEN
  MP_TAC(ISPECL [`s1:(A)wl_prog`; `ssa:num spt`; `na:num`; `lt:(num spt#1 spt#1 spt)list`;
                 `s1':(A)wl_prog`; `ssa'':num spt`; `na'':num`] ssa_cc_trans_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_conj(mk_comb(pr,`s1':(A)wl_prog`),mk_comb(pr,`s2':(A)wl_prog`))) MP_TAC THENL
   [ASM_MESON_TAC[]; rew THEN MESON_TAC[]];;

let WALLOCPAUX_CONV_MT_TAC (pre:tactic) (pr:term) (rew:tactic) : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN pre THEN
  SUBGOAL_THEN (mk_comb(pr,`s1':(A)wl_prog`)) MP_TAC THENL [ASM_MESON_TAC[]; rew];;

let WALLOCPAUX_CONV_IF_TAC (pre:tactic) (pr:term) (rew:tactic) (fixlem:thm) : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN pre THEN
  MP_TAC(ISPECL [`e2:(A)wl_prog`; `ssa:num spt`; `na:num`; `lt:(num spt#1 spt#1 spt)list`;
                 `e2':(A)wl_prog`; `ssa2:num spt`; `na2:num`] ssa_cc_trans_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ssa_map_ok na2 (ssa:num spt)` ASSUME_TAC THENL
   [MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ssa2:num spt`; `ssa3:num spt`; `na3:num`;
                 `mk_prio (e2':(A)wl_prog) (e3':(A)wl_prog)`] fixlem) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_conj(mk_comb(pr,`e2':(A)wl_prog`),mk_comb(pr,`e3':(A)wl_prog`))) MP_TAC THENL
   [ASM_MESON_TAC[]; rew THEN ASM_MESON_TAC[]];;

let WALLOCPAUX_CONV_LOOP_TAC (pre:tactic) (setuplem:thm) (fin:tactic) : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN pre THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP setuplem) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] loop_setup_props_local)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`setup_prog:(A)wl_prog`; `sptree_inter (ssa_refreshed:num spt) (names:1 spt)`;
     `na_refreshed:num`; `ssa_refreshed:num spt`] o check (is_forall o concl)) THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`body':(A)wl_prog`; `ssa'':num spt`; `na'':num`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC ssa_map_ok_inter THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  COND_CASES_TAC THEN fin;;

let WALLOCPAUX_CONV_JUMP_TAC (rew:tactic) (reclem:thm) : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[ssa_cc_trans_def] THEN
  MP_TAC(ISPEC `oEL n (lt:(num spt#1 spt#1 spt)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `q:num spt#1 spt#1 spt` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE] THENL
   [WALLOCPAUX_PROPS_EQ_TAC THEN rew;
    SUBGOAL_THEN `?a b c. q = (a:num spt,b:1 spt,c:1 spt)` (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    REWRITE_TAC[pair_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    COND_CASES_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN rew THEN REWRITE_TAC[reclem]];;

let WALLOCPAUX_CONV_CALL_TAC (pre:tactic) (fixlem:thm) (fin:tactic) : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN DISCH_TAC THEN STRIP_TAC THEN pre THEN
  WALLOCPAUX_PROPS_LNVRM_TAC `na:num` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  WALLOCPAUX_PROPS_LNVRM_TAC `na'':num` THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_inter THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP list_next_var_rename_props o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename"
     with Failure _ -> false))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `is_alloc_var na_2_p` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`stack_mov:(A)wl_prog`; `ssa'':num spt`;
      `sptree_inter ssa'' (sptree_union (FST (numset:num_set#num_set)) (SND numset)):num spt`; `na'':num`;
      `MAP FST (toAList (sptree_union (FST (numset:num_set#num_set)) (SND numset)))`;
      `ret_mov:(A)wl_prog`; `ssa''':num spt`; `na''':num`; `ret':num list`; `ssa_2_p:num spt`;
      `na_2_p:num`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 11)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`ren_ret_handler:(A)wl_prog`; `ssa_2:num spt`; `na_2:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ret_handler:(A)wl_prog`; `ssa_2_p:num spt`; `na_2_p:num`;
                 `lt:(num spt#1 spt#1 spt)list`; `ren_ret_handler:(A)wl_prog`; `ssa_2:num spt`;
                 `na_2:num`] ssa_cc_trans_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `prog':(A)wl_prog,ssa':num spt,na':num`)) THEN
  MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [REWRITE_TAC[option_CASE; PAIR_EQ] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN fin;
    ALL_TAC] THEN
  SUBGOAL_THEN `?n0 hp k1 k2. hq = (n0:num,hp:(A)wl_prog,k1:num,k2:num)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  pre THEN REWRITE_TAC[option_CASE; pair_CASE] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP next_var_rename_props o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "next_var_rename"
     with Failure _ -> false))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ssa_map_ok_more THEN EXISTS_TAC `na''':num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `is_alloc_var na_3_p` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`stack_mov:(A)wl_prog`; `ssa'':num spt`;
      `sptree_inter ssa'' (sptree_union (FST (numset:num_set#num_set)) (SND numset)):num spt`; `na'':num`;
      `MAP FST (toAList (sptree_union (FST (numset:num_set#num_set)) (SND numset)))`;
      `ret_mov:(A)wl_prog`; `na''':num`; `ret':num list`; `ssa_2_p:num spt`; `na_2_p:num`;
      `ren_ret_handler:(A)wl_prog`; `ssa_2:num spt`; `k1:num`; `k2:num`; `n0:num`;
      `ssa''':num spt`; `na_2:num`; `n':num`; `hp:(A)wl_prog`; `ssa_3_p:num spt`;
      `na_3_p:num`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 21)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`ren_exc_handler:(A)wl_prog`; `ssa_3:num spt`; `na_3:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "fix_inconsistencies"
       with Failure _ -> false)
    then let args = snd(strip_comb(lhs(concl th))) in
         MP_TAC(ISPECL [el 1 args; el 2 args; el 3 args; el 0 args] fixlem) THEN
         REWRITE_TAC[th; pair_CASE] THEN STRIP_TAC
    else NO_TAC) THEN
  fin;;

(* pre_alloc_conventions *)

let WALLOCPAUX_reconcile_pac = prove
 (`!(cur:num spt) (tgt:num spt) (ns:A spt) (P:num->bool).
     every_stack_var P (ssa_reconcile cur tgt ns:(B)wl_prog) /\
     call_arg_convention (ssa_reconcile cur tgt ns:(B)wl_prog)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`cur:num spt`; `tgt:num spt`; `ns:A spt`] WALLOCPAUX_ssa_reconcile_cases) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `mv:(num#num)list` SUBST1_TAC)) THEN
  REWRITE_TAC[every_stack_var_def; call_arg_convention_def]);;

let WALLOCPAUX_PAC_REW : tactic =
  REWRITE_TAC[pre_alloc_conventions_def; every_stack_var_def; call_arg_convention_def;
              inst_arg_convention_def];;

let WALLOCPAUX_PAC_GEN_TAC : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PAC_REW;;

(* the cut set of the stack moves consists of stack variables *)
let WALLOCPAUX_PAC_STACK_TAC : tactic =
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      (try let l = lhs(concl th) in
           fst(dest_const(fst(strip_comb l))) = "list_next_var_rename_move" &&
           rand(rator l) = `na + 2` with Failure _ -> false)
    then MP_TAC(REWRITE_RULE[PAIR] (MATCH_MP WALLOCPAUX_stack_set_stack
                                      (CONJ (ASSUME `is_alloc_var na`) th)))
    else NO_TAC) THEN DISCH_TAC;;

(* the renaming moves are Moves *)
let WALLOCPAUX_PAC_LNVRM_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "list_next_var_rename_move"
       with Failure _ -> false) && is_var(fst(dest_pair(rhs(concl th))))
    then CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC) (MATCH_MP WALLOCPAUX_lnvrm_is_move th)
    else NO_TAC));;

let WALLOCPAUX_PAC_CUT_TAC : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PAC_STACK_TAC THEN
  WALLOCPAUX_PAC_LNVRM_TAC THEN WALLOCPAUX_PAC_REW THEN ASM_REWRITE_TAC[];;

let WALLOCPAUX_PAC_FIN_TAC : tactic =
  TRY WALLOCPAUX_PAC_STACK_TAC THEN WALLOCPAUX_PAC_LNVRM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pre_alloc_conventions_def]) THEN
  ASM_REWRITE_TAC[pre_alloc_conventions_def; every_stack_var_def; call_arg_convention_def;
                  LENGTH_LIST_OF_SEQ; option_CASE; pair_CASE; WALLOCPAUX_reconcile_pac];;

let WALLOCPAUX_ssa_cc_trans_pac = prove
 (`!(prog:(A)wl_prog) (ssa:num spt) na lt (prog':(A)wl_prog) ssa' na'.
     ssa_cc_trans prog ssa na lt = (prog',ssa',na')
     ==> is_alloc_var na /\ ssa_map_ok na ssa
     ==> pre_alloc_conventions prog'`,
  MATCH_MP_TAC ssa_cc_trans_ind THEN REPEAT CONJ_TAC THEN
  TRY(WALLOCPAUX_PAC_GEN_TAC THEN NO_TAC) THENL
   [(* Inst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
    MP_TAC(ISPECL [`i:(A)inst`; `ssa:num spt`; `na:num`] WALLOCPAUX_inst_pac) THEN
    ASM_REWRITE_TAC[pair_CASE];
    (* Seq *)
    WALLOCPAUX_CONV_SEQ_TAC ALL_TAC `pre_alloc_conventions:(A)wl_prog->bool` WALLOCPAUX_PAC_REW;
    (* MustTerminate *)
    WALLOCPAUX_CONV_MT_TAC ALL_TAC `pre_alloc_conventions:(A)wl_prog->bool` WALLOCPAUX_PAC_REW;
    (* If *)
    WALLOCPAUX_CONV_IF_TAC ALL_TAC `pre_alloc_conventions:(A)wl_prog->bool` WALLOCPAUX_PAC_REW
      fix_inconsistencies_conventions;
    (* Alloc *)
    WALLOCPAUX_PAC_CUT_TAC;
    (* Return *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PAC_REW THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    (* Install *)
    WALLOCPAUX_PAC_CUT_TAC;
    (* FFI *)
    WALLOCPAUX_PAC_CUT_TAC;
    (* Call NONE *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PAC_REW THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; option_CASE];
    (* Call SOME *)
    WALLOCPAUX_CONV_CALL_TAC ALL_TAC fix_inconsistencies_conventions WALLOCPAUX_PAC_FIN_TAC;
    (* ShareInst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN COND_CASES_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
    WALLOCPAUX_PAC_REW;
    (* Loop *)
    WALLOCPAUX_CONV_LOOP_TAC ALL_TAC loop_setup_pre_alloc_conventions WALLOCPAUX_PAC_FIN_TAC;
    (* Break *)
    WALLOCPAUX_CONV_JUMP_TAC WALLOCPAUX_PAC_REW WALLOCPAUX_reconcile_pac;
    (* Continue *)
    WALLOCPAUX_CONV_JUMP_TAC WALLOCPAUX_PAC_REW WALLOCPAUX_reconcile_pac]);;

(* HOL4 line 10509 *)
let ssa_cc_trans_pre_alloc_conventions = prove
 (CASE_TERM
  `!(prog:(A)wl_prog) (ssa:num spt) na (lt:(num spt#1 spt#1 spt)list).
     is_alloc_var na /\ ssa_map_ok na ssa
     ==> let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in pre_alloc_conventions prog'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `ssa:num spt`; `na:num`; `lt:(num spt#1 spt#1 spt)list`]
           WALLOCPAUX_ssa_cc_trans_pac) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (prog:(A)wl_prog) (ssa:num spt) na
                          (lt:(num spt#1 spt#1 spt)list)`
    [`p1:(A)wl_prog`; `s1:num spt`; `n1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN ASM_MESON_TAC[]);;

(* HOL4 line 10745 *)
let setup_ssa_props_2 = prove
 (CASE_TERM
  `!lim n (prog:(A)wl_prog).
     is_alloc_var lim
     ==> let (mov:(A)wl_prog,ssa,na) = setup_ssa n lim prog in
         ssa_map_ok na ssa /\ is_alloc_var na /\ pre_alloc_conventions mov /\ lim <= na`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[setup_ssa_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `list_next_var_rename (even_list n) (LN:num spt) lim`
    [`new_ls:num list`; `ssa1:num spt`; `n1:num`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`even_list n`; `LN:num spt`; `lim:num`; `new_ls:num list`; `ssa1:num spt`;
                 `n1:num`] list_next_var_rename_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ssa_map_ok_def; lookup_def; option_DISTINCT]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN WALLOCPAUX_PAC_REW);;

(* HOL4 line 10763 *)
let full_ssa_cc_trans_pre_alloc_conventions = prove
 (`!n (prog:(A)wl_prog). pre_alloc_conventions (full_ssa_cc_trans n prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `limit_var (prog:(A)wl_prog)`] limit_var_props) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`limit_var (prog:(A)wl_prog)`; `n:num`; `prog:(A)wl_prog`] setup_ssa_props_2) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `setup_ssa n (limit_var (prog:(A)wl_prog)) prog:(A)wl_prog#num spt#num`
    [`mov:(A)wl_prog`; `ssa:num spt`; `na:num`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `ssa:num spt`; `na:num`; `[]:(num spt#1 spt#1 spt)list`]
           ssa_cc_trans_pre_alloc_conventions) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (prog:(A)wl_prog) ssa na []`
    [`prog':(A)wl_prog`; `ssa':num spt`; `na':num`] THEN
  REWRITE_TAC[pair_CASE] THEN UNDISCH_TAC `pre_alloc_conventions (mov:(A)wl_prog)` THEN
  WALLOCPAUX_PAC_REW THEN SIMP_TAC[]);;

let WALLOCPAUX_fake_moves_dtr = prove
 (CASE_TERM
  `!prio ls (ssaL:num spt) (ssaR:num spt) na.
     let (a:(A)wl_prog,b:(A)wl_prog,c,d,e) = fake_moves prio ls ssaL ssaR na in
       every_inst distinct_tar_reg a /\ every_inst distinct_tar_reg b`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fake_moves_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE; every_inst_def] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ssaL:num spt`; `ssaR:num spt`; `na:num`]) THEN
  WALLOCPAUX_TUPLE_TAC `fake_moves prio (t:num list) (ssaL:num spt) (ssaR:num spt) na:
                          (A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`sL:(A)wl_prog`; `sR:(A)wl_prog`; `n1:num`; `aL:num spt`; `aR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lookup (h:num) (aL:num spt)` (cases "option")) THEN
  MP_TAC(ISPEC `lookup (h:num) (aR:num spt)` (cases "option")) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  ASM_REWRITE_TAC[every_inst_def; fake_move_def; distinct_tar_reg_def]);;

(* HOL4 line 10777 *)
let fake_moves_distinct_tar_reg = prove
 (`!prio ls (ssal:num spt) (ssar:num spt) na (l:(A)wl_prog) (r:(A)wl_prog) a b c (conf:B).
     fake_moves prio ls ssal ssar na = (l,r,a,b,c)
     ==> every_inst distinct_tar_reg l /\ every_inst distinct_tar_reg r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prio:(1+1)option`; `ls:num list`; `ssal:num spt`; `ssar:num spt`; `na:num`]
           WALLOCPAUX_fake_moves_dtr) THEN
  ASM_REWRITE_TAC[pair_CASE]);;

let WALLOCPAUX_alloc_var_ne = prove
 (`!na. is_alloc_var na ==> ~(na = 0) /\ ~(na = 8)`,
  GEN_TAC THEN REWRITE_TAC[is_alloc_var_def] THEN DISCH_TAC THEN CONJ_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

let WALLOCPAUX_option_lookup_lt = prove
 (`!na (ssa:num spt) x. is_alloc_var na /\ ssa_map_ok na ssa ==> option_lookup ssa x < na`,
  REWRITE_TAC[ssa_map_ok_def; option_lookup_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_alloc_var_ne) THEN
  MP_TAC(ISPEC `lookup x (ssa:num spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `y:num` (fun th ->
    SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

(* adds option_lookup m x < na for each option_lookup m x of the goal *)
let WALLOCPAUX_OPTION_LOOKUP_LT_TAC : tactic =
  fun (asl,w as g) ->
    let tms = find_terms (fun t ->
      try let f,args = strip_comb t in
          fst(dest_const f) = "option_lookup" && length args = 2
      with Failure _ -> false) w in
    MAP_EVERY (fun t ->
      MP_TAC(ISPECL [`na:num`; rand(rator t); rand t] WALLOCPAUX_option_lookup_lt)) tms g;;

let WALLOCPAUX_inst_dtr = prove
 (CASE_TERM
  `!(i:(A)inst) (ssa:num spt) na.
     let (p,s,n) = ssa_cc_trans_inst i ssa na in
     is_alloc_var na /\ ssa_map_ok na ssa ==> every_inst distinct_tar_reg (p:(A)wl_prog)`,
  MP_TAC(ISPEC (CASE_TERM `\(i:(A)inst) (ssa:num spt) (na:num).
                  let (p,s,n) = ssa_cc_trans_inst i ssa na in
                  is_alloc_var na /\ ssa_map_ok na ssa
                  ==> every_inst distinct_tar_reg (p:(A)wl_prog)`)
         ssa_cc_trans_inst_ind) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_cc_trans_inst_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[WALLOCPAUX_reg_imm_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC([pair_CASE; every_inst_def; distinct_tar_reg_def] @
              (case_info_of_tyname "reg_imm").ci_inject @
              (case_info_of_tyname "reg_imm").ci_distinct) THEN
  STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_alloc_var_ne) THEN
  WALLOCPAUX_OPTION_LOOKUP_LT_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WALLOCPAUX_reconcile_ei = prove
 (`!(cur:num spt) (tgt:num spt) (ns:A spt) (P:(B)inst->bool).
     every_inst P (ssa_reconcile cur tgt ns:(B)wl_prog)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`cur:num spt`; `tgt:num spt`; `ns:A spt`] WALLOCPAUX_ssa_reconcile_cases) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `mv:(num#num)list` SUBST1_TAC)) THEN
  REWRITE_TAC[every_inst_def]);;

let WALLOCPAUX_fix_inconsistencies_dtr = prove
 (CASE_TERM
  `!(ssaL:num spt) (ssaR:num spt) na prio.
     let (a:(A)wl_prog,b:(A)wl_prog,c,d) = fix_inconsistencies prio ssaL ssaR na in
       every_inst distinct_tar_reg a /\ every_inst distinct_tar_reg b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fix_inconsistencies_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves (MAP FST (toAList (sptree_union (ssaL:num spt) ssaR)))
                          ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`prio:(1+1)option`; `MAP FST (toAList (sptree_union (ssaL:num spt) ssaR))`;
                 `sL:num spt`; `sR:num spt`; `n1:num`] WALLOCPAUX_fake_moves_dtr) THEN
  WALLOCPAUX_TUPLE_TAC `fake_moves (prio:(1+1)option)
      (MAP FST (toAList (sptree_union (ssaL:num spt) ssaR))) sL sR n1:
      (A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`qL:(A)wl_prog`; `qR:(A)wl_prog`; `n2:num`; `tL:num spt`; `tR:num spt`] THEN
  REWRITE_TAC[pair_CASE; every_inst_def] THEN SIMP_TAC[]);;

let WALLOCPAUX_DTR_REW : tactic =
  REWRITE_TAC([every_inst_def; distinct_tar_reg_def; option_CASE; pair_CASE] @
              (case_info_of_tyname "reg_imm").ci_inject @
              (case_info_of_tyname "reg_imm").ci_distinct);;

let WALLOCPAUX_DTR_GEN_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_cc_trans_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN REPEAT PAIRARG_TAC THEN
  WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PAC_LNVRM_TAC THEN
  WALLOCPAUX_DTR_REW THEN WALLOCPAUX_OPTION_LOOKUP_LT_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;;

(* distinct_tar_reg *)

let WALLOCPAUX_DTR_FIN_TAC : tactic =
  WALLOCPAUX_PAC_LNVRM_TAC THEN
  ASM_REWRITE_TAC[every_inst_def; option_CASE; pair_CASE; WALLOCPAUX_reconcile_ei];;

let WALLOCPAUX_ssa_cc_trans_dtr = prove
 (`!(prog:(A)wl_prog) (ssa:num spt) na lt (prog':(A)wl_prog) ssa' na'.
     ssa_cc_trans prog ssa na lt = (prog',ssa',na')
     ==> is_alloc_var na /\ ssa_map_ok na ssa
     ==> every_inst distinct_tar_reg prog'`,
  MATCH_MP_TAC ssa_cc_trans_ind THEN REPEAT CONJ_TAC THEN
  TRY(WALLOCPAUX_DTR_GEN_TAC THEN NO_TAC) THENL
   [(* Inst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
    MP_TAC(ISPECL [`i:(A)inst`; `ssa:num spt`; `na:num`] WALLOCPAUX_inst_dtr) THEN
    ASM_REWRITE_TAC[pair_CASE];
    (* Seq *)
    WALLOCPAUX_CONV_SEQ_TAC ALL_TAC `every_inst (distinct_tar_reg:(A)inst->bool)`
      WALLOCPAUX_DTR_REW;
    (* MustTerminate *)
    WALLOCPAUX_CONV_MT_TAC ALL_TAC `every_inst (distinct_tar_reg:(A)inst->bool)`
      WALLOCPAUX_DTR_REW;
    (* If *)
    WALLOCPAUX_CONV_IF_TAC ALL_TAC `every_inst (distinct_tar_reg:(A)inst->bool)`
      WALLOCPAUX_DTR_REW WALLOCPAUX_fix_inconsistencies_dtr;
    (* Call SOME *)
    WALLOCPAUX_CONV_CALL_TAC ALL_TAC WALLOCPAUX_fix_inconsistencies_dtr WALLOCPAUX_DTR_FIN_TAC;
    (* ShareInst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN COND_CASES_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
    WALLOCPAUX_DTR_REW;
    (* Loop *)
    WALLOCPAUX_CONV_LOOP_TAC ALL_TAC loop_setup_every_inst_distinct_tar_reg
      WALLOCPAUX_DTR_FIN_TAC;
    (* Break *)
    WALLOCPAUX_CONV_JUMP_TAC WALLOCPAUX_DTR_REW WALLOCPAUX_reconcile_ei;
    (* Continue *)
    WALLOCPAUX_CONV_JUMP_TAC WALLOCPAUX_DTR_REW WALLOCPAUX_reconcile_ei]);;

(* HOL4 line 10789 *)
let ssa_cc_trans_distinct_tar_reg = prove
 (`!(prog:(A)wl_prog) (ssa:num spt) na (lt:(num spt#1 spt#1 spt)list).
     is_alloc_var na /\ wl_every_var (\x. x < na) prog /\ ssa_map_ok na ssa
     ==> every_inst distinct_tar_reg (FST (ssa_cc_trans prog ssa na lt))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `ssa:num spt`; `na:num`; `lt:(num spt#1 spt#1 spt)list`]
           WALLOCPAUX_ssa_cc_trans_dtr) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (prog:(A)wl_prog) (ssa:num spt) na
                          (lt:(num spt#1 spt#1 spt)list)`
    [`p1:(A)wl_prog`; `s1:num spt`; `n1:num`] THEN
  REWRITE_TAC[FST] THEN ASM_MESON_TAC[]);;

(* the setup moves of full_ssa_cc_trans form a single Move *)
let WALLOCPAUX_setup_ssa_move = prove
 (`!n lim (prog:(A)wl_prog) (mov:(A)wl_prog) ssa na.
     setup_ssa n lim prog = (mov,ssa,na) ==> ?moves. mov = wl_Move 1 moves`,
  REPEAT GEN_TAC THEN REWRITE_TAC[setup_ssa_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SPEC_TAC(`list_next_var_rename (even_list n) (LN:num spt) lim`, `q:num list#num spt#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 10953 *)
let full_ssa_cc_trans_distinct_tar_reg = prove
 (`!n (prog:(A)wl_prog). every_inst distinct_tar_reg (full_ssa_cc_trans n prog)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `limit_var (prog:(A)wl_prog)`] limit_var_props) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`limit_var (prog:(A)wl_prog)`; `n:num`; `prog:(A)wl_prog`] setup_ssa_props_2) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `setup_ssa n (limit_var (prog:(A)wl_prog)) prog:(A)wl_prog#num spt#num`
    [`mov:(A)wl_prog`; `ssa:num spt`; `na:num`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_ASSUM(CHOOSE_THEN SUBST1_TAC o MATCH_MP WALLOCPAUX_setup_ssa_move) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `ssa:num spt`; `na:num`; `[]:(num spt#1 spt#1 spt)list`]
           WALLOCPAUX_ssa_cc_trans_dtr) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (prog:(A)wl_prog) ssa na []`
    [`prog':(A)wl_prog`; `ssa':num spt`; `na':num`] THEN
  REWRITE_TAC[pair_CASE; every_inst_def] THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_wl_exp_inject = (case_info_of_tyname "wl_exp").ci_inject;;
let WALLOCPAUX_wl_exp_distinct = (case_info_of_tyname "wl_exp").ci_distinct;;
let WALLOCPAUX_binop_distinct = (case_info_of_tyname "binop").ci_distinct;;
let WALLOCPAUX_addr_inject = (case_info_of_tyname "addr").ci_inject;;

let WALLOCPAUX_E2A_REW : tactic =
  REWRITE_TAC([exp_to_addr_def; option_DISTINCT; option_INJ; NOT_CONS_NIL; CONS_11] @
              WALLOCPAUX_wl_exp_inject @ WALLOCPAUX_wl_exp_distinct @ WALLOCPAUX_addr_inject @
              WALLOCPAUX_binop_distinct);;

(* HOL4 line 10984 *)
let exp_to_addr_ShareInst = prove
 (`!(exp:(A)wl_exp) n c.
     exp_to_addr exp = SOME (Addr n c) <=>
     (exp = wl_Var n /\ c = word 0) \/ (exp = wl_Op asm_Add [wl_Var n; wl_Const c])`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[exp_to_addr_def]] THEN
  STRUCT_CASES_TAC(ISPEC `exp:(A)wl_exp` (CONJUNCT1 (cases "wl_exp"))) THEN
  WALLOCPAUX_E2A_REW THENL
   [MESON_TAC[];
    STRUCT_CASES_TAC(ISPEC `a0:binop` (cases "binop")) THEN WALLOCPAUX_E2A_REW THEN
    STRUCT_CASES_TAC(ISPEC `a1:((A)wl_exp)list` list_CASES) THEN WALLOCPAUX_E2A_REW THEN
    STRUCT_CASES_TAC(ISPEC `h:(A)wl_exp` (CONJUNCT1 (cases "wl_exp"))) THEN WALLOCPAUX_E2A_REW THEN
    STRUCT_CASES_TAC(ISPEC `t:((A)wl_exp)list` list_CASES) THEN WALLOCPAUX_E2A_REW THEN
    STRUCT_CASES_TAC(ISPEC `h:(A)wl_exp` (CONJUNCT1 (cases "wl_exp"))) THEN WALLOCPAUX_E2A_REW THEN
    STRUCT_CASES_TAC(ISPEC `t':((A)wl_exp)list` list_CASES) THEN WALLOCPAUX_E2A_REW THEN
    MESON_TAC[]]);;

let WALLOCPAUX_fake_moves_fiol = prove
 (CASE_TERM
  `!prio (conf:(A)asm_config) ls (ssaL:num spt) (ssaR:num spt) na.
     let (a:(A)wl_prog,b:(A)wl_prog,c,d,e) = fake_moves prio ls ssaL ssaR na in
       full_inst_ok_less conf a /\ full_inst_ok_less conf b`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fake_moves_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[pair_CASE; full_inst_ok_less_def] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ssaL:num spt`; `ssaR:num spt`; `na:num`]) THEN
  WALLOCPAUX_TUPLE_TAC `fake_moves prio (t:num list) (ssaL:num spt) (ssaR:num spt) na:
                          (A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`sL:(A)wl_prog`; `sR:(A)wl_prog`; `n1:num`; `aL:num spt`; `aR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lookup (h:num) (aL:num spt)` (cases "option")) THEN
  MP_TAC(ISPEC `lookup (h:num) (aR:num spt)` (cases "option")) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  ASM_REWRITE_TAC[full_inst_ok_less_def; fake_move_def; inst_ok_less_def]);;

(* HOL4 line 10997 *)
let fake_moves_conventions2 = prove
 (`!prio ls (ssal:num spt) (ssar:num spt) na (l:(A)wl_prog) (r:(A)wl_prog) a b c
    (conf:(A)asm_config).
     fake_moves prio ls ssal ssar na = (l,r,a,b,c)
     ==> full_inst_ok_less conf l /\ full_inst_ok_less conf r /\
         every_inst distinct_tar_reg l /\ every_inst distinct_tar_reg r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`prio:(1+1)option`; `conf:(A)asm_config`; `ls:num list`; `ssal:num spt`;
                 `ssar:num spt`; `na:num`] WALLOCPAUX_fake_moves_fiol) THEN
  MP_TAC(ISPECL [`prio:(1+1)option`; `ls:num list`; `ssal:num spt`; `ssar:num spt`; `na:num`]
           WALLOCPAUX_fake_moves_dtr) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN SIMP_TAC[]);;

let WALLOCPAUX_fix_inconsistencies_fiol = prove
 (CASE_TERM
  `!(ssaL:num spt) (ssaR:num spt) na prio (conf:(A)asm_config).
     let (a:(A)wl_prog,b:(A)wl_prog,c,d) = fix_inconsistencies prio ssaL ssaR na in
       full_inst_ok_less conf a /\ full_inst_ok_less conf b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fix_inconsistencies_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  WALLOCPAUX_TUPLE_TAC `word_alloc_merge_moves (MAP FST (toAList (sptree_union (ssaL:num spt) ssaR)))
                          ssaL ssaR na`
    [`mL:(num#num)list`; `mR:(num#num)list`; `n1:num`; `sL:num spt`; `sR:num spt`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`prio:(1+1)option`; `conf:(A)asm_config`;
                 `MAP FST (toAList (sptree_union (ssaL:num spt) ssaR))`;
                 `sL:num spt`; `sR:num spt`; `n1:num`] WALLOCPAUX_fake_moves_fiol) THEN
  WALLOCPAUX_TUPLE_TAC `fake_moves (prio:(1+1)option)
      (MAP FST (toAList (sptree_union (ssaL:num spt) ssaR))) sL sR n1:
      (A)wl_prog#(A)wl_prog#num#num spt#num spt`
    [`qL:(A)wl_prog`; `qR:(A)wl_prog`; `n2:num`; `tL:num spt`; `tR:num spt`] THEN
  REWRITE_TAC[pair_CASE; full_inst_ok_less_def] THEN SIMP_TAC[]);;

let WALLOCPAUX_inst_fiol = prove
 (CASE_TERM
  `!(i:(A)inst) (ssa:num spt) na.
     let (p,s,n) = ssa_cc_trans_inst i ssa na in
     !(c:(A)asm_config). is_alloc_var na /\ ssa_map_ok na ssa /\ inst_ok_less c i
       ==> full_inst_ok_less c (p:(A)wl_prog)`,
  MP_TAC(ISPEC (CASE_TERM `\(i:(A)inst) (ssa:num spt) (na:num).
                  let (p,s,n) = ssa_cc_trans_inst i ssa na in
                  !(c:(A)asm_config). is_alloc_var na /\ ssa_map_ok na ssa /\ inst_ok_less c i
                    ==> full_inst_ok_less c (p:(A)wl_prog)`)
         ssa_cc_trans_inst_ind) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_cc_trans_inst_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[WALLOCPAUX_reg_imm_CASE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV)) THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[pair_CASE; full_inst_ok_less_def; inst_ok_less_def] THEN
  REPEAT GEN_TAC THEN TRY(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WALLOCPAUX_alloc_var_ne) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_OPTION_LOOKUP_LT_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

(* full_inst_ok_less *)

let WALLOCPAUX_addr_CASE = (case_info_of_tyname "addr").ci_def;;

let WALLOCPAUX_exp_to_addr_ssa = prove
 (`!(ssa:num spt) (exp:(A)wl_exp) n w.
     exp_to_addr exp = SOME (Addr n w)
     ==> exp_to_addr (ssa_cc_trans_exp ssa exp) = SOME (Addr (option_lookup ssa n) w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exp_to_addr_ShareInst] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ssa_cc_trans_exp_def; MAP; exp_to_addr_def]);;

let WALLOCPAUX_reconcile_fiol = prove
 (`!(cur:num spt) (tgt:num spt) (ns:A spt) (c:(B)asm_config).
     full_inst_ok_less c (ssa_reconcile cur tgt ns:(B)wl_prog)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`cur:num spt`; `tgt:num spt`; `ns:A spt`] WALLOCPAUX_ssa_reconcile_cases) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `mv:(num#num)list` SUBST1_TAC)) THEN
  REWRITE_TAC[full_inst_ok_less_def]);;

let WALLOCPAUX_FIOL_REW : tactic =
  REWRITE_TAC[full_inst_ok_less_def; option_CASE; pair_CASE];;

let WALLOCPAUX_FIOL_PRE : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[full_inst_ok_less_def; option_CASE; pair_CASE]);;

let WALLOCPAUX_FIOL_GEN_TAC : tactic =
  WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_PAC_LNVRM_TAC THEN
  WALLOCPAUX_FIOL_REW;;

let WALLOCPAUX_FIOL_FIN_TAC : tactic =
  WALLOCPAUX_PAC_LNVRM_TAC THEN
  ASM_REWRITE_TAC[full_inst_ok_less_def; option_CASE; pair_CASE; WALLOCPAUX_reconcile_fiol];;

let WALLOCPAUX_ssa_cc_trans_fiol = prove
 (`!(c:(A)asm_config) (prog:(A)wl_prog) (ssa:num spt) na lt (prog':(A)wl_prog) ssa' na'.
     ssa_cc_trans prog ssa na lt = (prog',ssa',na')
     ==> is_alloc_var na /\ ssa_map_ok na ssa /\ full_inst_ok_less c prog
     ==> full_inst_ok_less c prog'`,
  GEN_TAC THEN MATCH_MP_TAC ssa_cc_trans_ind THEN REPEAT CONJ_TAC THEN
  TRY(WALLOCPAUX_FIOL_GEN_TAC THEN NO_TAC) THENL
   [(* Inst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN WALLOCPAUX_FIOL_PRE THEN
    MP_TAC(ISPECL [`i:(A)inst`; `ssa:num spt`; `na:num`] WALLOCPAUX_inst_fiol) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN DISCH_THEN(MP_TAC o SPEC `c:(A)asm_config`) THEN
    ASM_REWRITE_TAC[];
    (* Seq *)
    WALLOCPAUX_CONV_SEQ_TAC WALLOCPAUX_FIOL_PRE `full_inst_ok_less (c:(A)asm_config)`
      WALLOCPAUX_FIOL_REW;
    (* MustTerminate *)
    WALLOCPAUX_CONV_MT_TAC WALLOCPAUX_FIOL_PRE `full_inst_ok_less (c:(A)asm_config)`
      WALLOCPAUX_FIOL_REW;
    (* If *)
    WALLOCPAUX_CONV_IF_TAC WALLOCPAUX_FIOL_PRE `full_inst_ok_less (c:(A)asm_config)`
      WALLOCPAUX_FIOL_REW WALLOCPAUX_fix_inconsistencies_fiol;
    (* Call SOME *)
    WALLOCPAUX_CONV_CALL_TAC WALLOCPAUX_FIOL_PRE WALLOCPAUX_fix_inconsistencies_fiol
      WALLOCPAUX_FIOL_FIN_TAC;
    (* ShareInst *)
    WALLOCPAUX_PROPS_PRE_TAC THEN COND_CASES_TAC THEN WALLOCPAUX_PROPS_EQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "full_inst_ok_less"
      with Failure _ -> false)) THEN
    REWRITE_TAC[full_inst_ok_less_def] THEN
    MP_TAC(ISPEC `exp_to_addr (exp:(A)wl_exp)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; option_CASE])
      (X_CHOOSE_THEN `ad:(A)addr` (fun th -> REWRITE_TAC[th; option_CASE] THEN ASSUME_TAC th))) THEN
    MP_TAC(ISPEC `ad:(A)addr` (cases "addr")) THEN
    DISCH_THEN(X_CHOOSE_THEN `an:num` (X_CHOOSE_THEN `aw:A word` SUBST_ALL_TAC)) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WALLOCPAUX_exp_to_addr_ssa th]) THEN
    REWRITE_TAC[option_CASE; WALLOCPAUX_addr_CASE];
    (* Loop *)
    WALLOCPAUX_CONV_LOOP_TAC WALLOCPAUX_FIOL_PRE loop_setup_full_inst_ok_less
      WALLOCPAUX_FIOL_FIN_TAC;
    (* Break *)
    WALLOCPAUX_CONV_JUMP_TAC WALLOCPAUX_FIOL_REW WALLOCPAUX_reconcile_fiol;
    (* Continue *)
    WALLOCPAUX_CONV_JUMP_TAC WALLOCPAUX_FIOL_REW WALLOCPAUX_reconcile_fiol]);;

(* HOL4 line 11012 *)
let ssa_cc_trans_full_inst_ok_less = prove
 (`!(prog:(A)wl_prog) (ssa:num spt) na (lt:(num spt#1 spt#1 spt)list) (c:(A)asm_config).
     wl_every_var (\x. x < na) prog /\ is_alloc_var na /\ ssa_map_ok na ssa /\
     full_inst_ok_less c prog
     ==> full_inst_ok_less c (FST (ssa_cc_trans prog ssa na lt))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `prog:(A)wl_prog`; `ssa:num spt`; `na:num`;
                 `lt:(num spt#1 spt#1 spt)list`] WALLOCPAUX_ssa_cc_trans_fiol) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (prog:(A)wl_prog) (ssa:num spt) na
                          (lt:(num spt#1 spt#1 spt)list)`
    [`p1:(A)wl_prog`; `s1:num spt`; `n1:num`] THEN
  REWRITE_TAC[FST] THEN ASM_MESON_TAC[]);;

(* HOL4 line 11154 *)
let full_ssa_cc_trans_full_inst_ok_less = prove
 (`!(prog:(A)wl_prog) n (c:(A)asm_config).
     full_inst_ok_less c prog ==> full_inst_ok_less c (full_ssa_cc_trans n prog)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[full_ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPECL [`prog:(A)wl_prog`; `limit_var (prog:(A)wl_prog)`] limit_var_props) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`limit_var (prog:(A)wl_prog)`; `n:num`; `prog:(A)wl_prog`] setup_ssa_props_2) THEN
  ASM_REWRITE_TAC[] THEN
  WALLOCPAUX_TUPLE_TAC `setup_ssa n (limit_var (prog:(A)wl_prog)) prog:(A)wl_prog#num spt#num`
    [`mov:(A)wl_prog`; `ssa:num spt`; `na:num`] THEN
  REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  FIRST_ASSUM(CHOOSE_THEN SUBST1_TAC o MATCH_MP WALLOCPAUX_setup_ssa_move) THEN
  MP_TAC(ISPECL [`c:(A)asm_config`; `prog:(A)wl_prog`; `ssa:num spt`; `na:num`;
                 `[]:(num spt#1 spt#1 spt)list`] WALLOCPAUX_ssa_cc_trans_fiol) THEN
  WALLOCPAUX_TUPLE_TAC `ssa_cc_trans (prog:(A)wl_prog) ssa na []`
    [`prog':(A)wl_prog`; `ssa':num spt`; `na':num`] THEN
  REWRITE_TAC[pair_CASE; full_inst_ok_less_def] THEN ASM_MESON_TAC[]);;

(* HOL4 line 11176: val is_phy_var_tac (ML) is not needed *)

(* helpers for call_arg_convention_preservation (local to this file) *)

let WALLOCPAUX_phy_double = prove
 (`!x. is_phy_var (2 * x)`,
  SIMP_TAC[is_phy_var_def; MOD_MULT; ARITH_EQ]);;

let WALLOCPAUX_apply_colour_inst_cases = IL2AUX_case_ind apply_colour_inst_def;;

let WALLOCPAUX_inst_arg_colour = prove
 (`!f (i:(A)inst).
     every_var_inst (\x. is_phy_var x ==> f x = x) i /\ inst_arg_convention i
     ==> inst_arg_convention (apply_colour_inst f i)`,
  MATCH_MP_TAC WALLOCPAUX_apply_colour_inst_cases THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[apply_colour_inst_def; every_var_inst_def; inst_arg_convention_def] THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC([apply_colour_imm_def; inst_arg_convention_def; every_var_imm_def] @
                      (case_info_of_tyname "reg_imm").ci_inject)) THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && is_numeral(rhs(concl th))))) THEN
  ASM_MESON_TAC[WALLOCPAUX_PHY_REGS]);;

let WALLOCPAUX_map_colour_seq = prove
 (`!f (g:num->num) (ys:num list).
     ALL (\x. is_phy_var x ==> f x = x) ys /\ ys = list_of_seq g (LENGTH ys) /\
     (!i. is_phy_var (g i))
     ==> MAP f ys = list_of_seq g (LENGTH (MAP f ys))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_MAP] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN
  SUBGOAL_THEN `!x. MEM x (ys:num list) ==> is_phy_var x` ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[MEM_GENLIST] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `ALL (\x. is_phy_var x ==> f x = x) (ys:num list)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_CAC_REW : tactic =
  REWRITE_TAC[apply_colour_def; call_arg_convention_def; wl_every_var_def; LET_DEF; LET_END_DEF;
              option_CASE; pair_CASE];;

let WALLOCPAUX_CAC_REG_TAC : tactic =
  WALLOCPAUX_CAC_REW THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && is_numeral(rhs(concl th))))) THEN
  ASM_MESON_TAC[WALLOCPAUX_PHY_REGS];;

let WALLOCPAUX_CAC_SEQ_TAC : tactic =
  MATCH_MP_TAC WALLOCPAUX_map_colour_seq THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[WALLOCPAUX_phy_double];;

let WALLOCPAUX_CAC_IH_TAC : tactic =
  FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let WALLOCPAUX_CAC_V2_TAC : tactic =
  UNDISCH_TAC `is_phy_var v ==> (f:num->num) v = v` THEN UNDISCH_TAC `v = 2` THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WALLOCPAUX_PHY_REGS];;

let WALLOCPAUX_CAC_STRUCT_TAC : tactic =
  DISCH_THEN STRIP_ASSUME_TAC THEN GEN_TAC THEN WALLOCPAUX_CAC_REW THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN WALLOCPAUX_CAC_IH_TAC;;

(* HOL4 line 11182 *)
let call_arg_convention_preservation = prove
 (`!(prog:(A)wl_prog) f.
     wl_every_var (\x. is_phy_var x ==> f x = x) prog /\ call_arg_convention prog
     ==> call_arg_convention (apply_colour f prog)`,
  MATCH_MP_TAC call_arg_convention_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(WALLOCPAUX_CAC_REW THEN NO_TAC) THENL
   [(* Inst *)
    WALLOCPAUX_CAC_REW THEN REWRITE_TAC[WALLOCPAUX_inst_arg_colour];
    (* Return *)
    WALLOCPAUX_CAC_REW THEN STRIP_TAC THEN WALLOCPAUX_CAC_SEQ_TAC;
    (* Raise *)
    WALLOCPAUX_CAC_REG_TAC;
    (* Install *)
    WALLOCPAUX_CAC_REG_TAC;
    (* FFI *)
    WALLOCPAUX_CAC_REG_TAC;
    (* Alloc *)
    WALLOCPAUX_CAC_REG_TAC;
    (* StoreConsts *)
    WALLOCPAUX_CAC_REG_TAC;
    (* Call *)
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN GEN_TAC THEN
    MP_TAC(ISPEC `ret:(num list#(num_set#num_set)#(A)wl_prog#num#num)option`
             (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `rq:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [WALLOCPAUX_CAC_REW THEN STRIP_TAC THEN WALLOCPAUX_CAC_SEQ_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `?vs cs rh k1 k2.
        rq = (vs:num list,cs:num_set#num_set,rh:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    USE_THEN "ihr" (MP_TAC o SPECL [`vs:num list`; `cs:num_set#num_set`; `k1:num`; `k2:num`;
                                   `rh:(A)wl_prog`]) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [ALL_TAC;
      SUBGOAL_THEN `?v hp j1 j2. hq = (v:num,hp:(A)wl_prog,j1:num,j2:num)`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
      USE_THEN "ihh" (MP_TAC o SPECL [`vs:num list`; `cs:num_set#num_set`; `rh:(A)wl_prog`;
                                     `k1:num`; `k2:num`; `v:num`; `j1:num`; `j2:num`;
                                     `hp:(A)wl_prog`]) THEN
      REWRITE_TAC[] THEN DISCH_TAC] THEN
    WALLOCPAUX_CAC_REW THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    TRY(WALLOCPAUX_CAC_SEQ_TAC THEN NO_TAC) THEN
    FIRST [WALLOCPAUX_CAC_IH_TAC; WALLOCPAUX_CAC_V2_TAC];
    (* Seq *)
    WALLOCPAUX_CAC_STRUCT_TAC;
    (* Loop *)
    WALLOCPAUX_CAC_STRUCT_TAC;
    (* If *)
    WALLOCPAUX_CAC_STRUCT_TAC]);;

(* HOL4 line 11204 *)
let every_var_inst_apply_colour_inst = prove
 (`!P (inst:(A)inst) Q f.
     every_var_inst P inst /\ (!x. P x ==> Q (f x))
     ==> every_var_inst Q (apply_colour_inst f inst)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`inst:(A)inst`,`inst:(A)inst`) THEN
  SPEC_TAC(`f:num->num`,`f:num->num`) THEN
  MATCH_MP_TAC WALLOCPAUX_apply_colour_inst_cases THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[apply_colour_inst_def; every_var_inst_def] THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[apply_colour_imm_def; every_var_imm_def]) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4 line 11215 *)
let every_var_exp_apply_colour_exp = prove
 (`!P (exp:(A)wl_exp) Q f.
     every_var_exp P exp /\ (!x. P x ==> Q (f x))
     ==> every_var_exp Q (apply_colour_exp f exp)`,
  SUBGOAL_THEN
   `!f (exp:(A)wl_exp) P Q.
      every_var_exp P exp /\ (!x. P x ==> Q (f x))
      ==> every_var_exp Q (apply_colour_exp f exp)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC apply_colour_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[apply_colour_exp_def; every_var_exp_def; ALL_MAP; GSYM ALL_MEM; o_THM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 11225 *)
let every_apply_nummap_key_helper = prove
 (CASE_TERM
  `!f (names:num_set) P Q.
     ALL P (MAP FST (toAList names)) /\ (!x. P x ==> Q (f x))
     ==> ALL Q (MAP FST (toAList (fromAList
           (MAP (\xy. match xy with (x:num,y:1) -> (f x,one)) (toAList names)))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; toAList_domain; domain_fromAList; IN_SET_OF_LIST; MEM_MAP;
              EXISTS_PAIR_THM; pair_CASE] THEN
  REWRITE_TAC[domain_lookup; MEM_toAList; PAIR_EQ] THEN MESON_TAC[]);;

(* helpers for every_var_apply_colour (local to this file) *)

let WALLOCPAUX_ALL_MAP_IMP = prove
 (`!P Q (f:A->B) l. ALL P l /\ (!x. P x ==> Q (f x)) ==> ALL Q (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; MAP] THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_ALL_keys_apply = prove
 (`!f (t:A spt) P Q.
     ALL P (MAP FST (toAList t)) /\ (!x. P x ==> Q (f x))
     ==> ALL Q (MAP FST (toAList (apply_nummap_key f t)))`,
  REWRITE_TAC[GSYM ALL_MEM; toAList_domain; apply_nummap_key_domain; IN_IMAGE] THEN
  MESON_TAC[]);;

let WALLOCPAUX_every_name_apply = prove
 (`!f (t:num_set#num_set) P Q.
     every_name P t /\ (!x. P x ==> Q (f x)) ==> every_name Q (apply_nummaps_key f t)`,
  REWRITE_TAC[every_name_def; nummaps_to_nummap] THEN MESON_TAC[WALLOCPAUX_ALL_keys_apply]);;

let WALLOCPAUX_every_var_imm_apply = prove
 (`!P Q f (ri:(A)reg_imm).
     every_var_imm P ri /\ (!x. P x ==> Q (f x)) ==> every_var_imm Q (apply_colour_imm f ri)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[apply_colour_imm_def; every_var_imm_def] THEN MESON_TAC[]);;

let WALLOCPAUX_EVA_REW : tactic =
  REWRITE_TAC[apply_colour_def; wl_every_var_def; LET_DEF; LET_END_DEF; option_CASE; pair_CASE];;

let WALLOCPAUX_EVA_TAC : tactic =
  WALLOCPAUX_EVA_REW THEN SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_MAP; MAP_o] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[every_var_inst_apply_colour_inst; every_var_exp_apply_colour_exp;
                WALLOCPAUX_every_name_apply; WALLOCPAUX_ALL_keys_apply; WALLOCPAUX_ALL_MAP_IMP;
                WALLOCPAUX_every_var_imm_apply];;

(* the Call case of the apply_colour inductions: rew rewrites the property *)
let WALLOCPAUX_APPLY_CALL_TAC (rew:tactic) (lems:thm list) : tactic =
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `ret:(num list#(num_set#num_set)#(A)wl_prog#num#num)option`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `rq:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [rew THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC lems; ALL_TAC] THEN
  SUBGOAL_THEN `?vs cs rh k1 k2.
      rq = (vs:num list,cs:num_set#num_set,rh:(A)wl_prog,k1:num,k2:num)`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  USE_THEN "ihr" (MP_TAC o SPECL [`vs:num list`; `cs:num_set#num_set`; `k1:num`; `k2:num`;
                                 `rh:(A)wl_prog`]) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
   [ALL_TAC;
    SUBGOAL_THEN `?v hp j1 j2. hq = (v:num,hp:(A)wl_prog,j1:num,j2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    USE_THEN "ihh" (MP_TAC o SPECL [`v:num`; `j1:num`; `j2:num`; `hp:(A)wl_prog`]) THEN
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  rew THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC lems;;

let WALLOCPAUX_every_var_apply_colour = prove
 (`!f (prog:(A)wl_prog) P Q.
     wl_every_var P prog /\ (!x. P x ==> Q (f x)) ==> wl_every_var Q (apply_colour f prog)`,
  MATCH_MP_TAC apply_colour_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(WALLOCPAUX_EVA_TAC THEN NO_TAC) THEN
  WALLOCPAUX_APPLY_CALL_TAC WALLOCPAUX_EVA_REW
    [WALLOCPAUX_ALL_MAP_IMP; WALLOCPAUX_every_name_apply]);;

(* HOL4 line 11237 *)
let every_var_apply_colour = prove
 (`!P (prog:(A)wl_prog) Q f.
     wl_every_var P prog /\ (!x. P x ==> Q (f x)) ==> wl_every_var Q (apply_colour f prog)`,
  MESON_TAC[WALLOCPAUX_every_var_apply_colour]);;

let WALLOCPAUX_ESV_REW : tactic =
  REWRITE_TAC[apply_colour_def; every_stack_var_def; LET_DEF; LET_END_DEF; option_CASE;
              pair_CASE];;

let WALLOCPAUX_every_stack_var_apply_colour = prove
 (`!f (prog:(A)wl_prog) P Q.
     every_stack_var P prog /\ (!x. P x ==> Q (f x))
     ==> every_stack_var Q (apply_colour f prog)`,
  MATCH_MP_TAC apply_colour_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(WALLOCPAUX_ESV_REW THEN REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[WALLOCPAUX_every_name_apply] THEN NO_TAC) THEN
  WALLOCPAUX_APPLY_CALL_TAC WALLOCPAUX_ESV_REW [WALLOCPAUX_every_name_apply]);;

(* HOL4 line 11278 *)
let every_stack_var_apply_colour = prove
 (`!P (prog:(A)wl_prog) Q f.
     every_stack_var P prog /\ (!x. P x ==> Q (f x))
     ==> every_stack_var Q (apply_colour f prog)`,
  MESON_TAC[WALLOCPAUX_every_stack_var_apply_colour]);;

(* HOL4 line 11293 *)
let every_var_exp_get_reads_exp = prove
 (`!(exp:(A)wl_exp). every_var_exp (\x. MEM x (get_reads_exp exp)) exp`,
  GEN_TAC THEN MP_TAC(ISPEC `exp:(A)wl_exp` every_var_exp_get_live_exp) THEN
  REWRITE_TAC[GSYM get_reads_exp_get_live_exp; IN_SET_OF_LIST]);;

(* HOL4 line 11302: val exp_tac3 (ML) is not needed *)

(* helpers for every_var_in_get_clash_tree (local to this file) *)

let WALLOCPAUX_get_delta_inst_cases = IL2AUX_case_ind get_delta_inst_def;;

let WALLOCPAUX_every_var_get_delta_inst = prove
 (`!(i:(A)inst). every_var_inst (in_clash_tree (get_delta_inst i)) i`,
  MATCH_MP_TAC WALLOCPAUX_get_delta_inst_cases THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[get_delta_inst_def; every_var_inst_def] THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[WALLOCPAUX_reg_imm_CASE; every_var_imm_def]) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[in_clash_tree_def; MEM]);;

let WALLOCPAUX_ev_tree_mono = prove
 (`!t t' (s:(A)wl_prog).
     wl_every_var (in_clash_tree t) s /\ (!x. in_clash_tree t x ==> in_clash_tree t' x)
     ==> wl_every_var (in_clash_tree t') s`,
  MESON_TAC[every_var_mono]);;

let WALLOCPAUX_eve_reads = prove
 (`!(exp:(A)wl_exp) P. (!x. MEM x (get_reads_exp exp) ==> P x) ==> every_var_exp P exp`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC every_var_exp_mono THEN
  EXISTS_TAC `\x. MEM x (get_reads_exp (exp:(A)wl_exp))` THEN
  ASM_REWRITE_TAC[every_var_exp_get_reads_exp]);;

let WALLOCPAUX_GCT_REW : tactic =
  REWRITE_TAC[get_clash_tree_def; wl_every_var_def; LET_DEF; LET_END_DEF; every_name_def;
              GSYM ALL_MEM; in_clash_tree_def; MEM; toAList_domain; domain_union; IN_UNION;
              word_allocProof_domain_numset_list_insert; IN_SET_OF_LIST; option_CASE;
              pair_CASE];;

let WALLOCPAUX_GCT2_TAC : tactic =
  WALLOCPAUX_GCT_REW THEN SIMP_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC WALLOCPAUX_eve_reads THEN REWRITE_TAC[in_clash_tree_def; MEM] THEN
      SIMP_TAC[]);;

(* uses an assumption every_var (in_clash_tree t) s for a goal about s *)
let WALLOCPAUX_GCT_IH_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let t = rand(rand(rator(concl th))) in
    MATCH_MP_TAC WALLOCPAUX_ev_tree_mono THEN EXISTS_TAC t THEN
    CONJ_TAC THENL [ACCEPT_TAC th; REWRITE_TAC[in_clash_tree_def; MEM] THEN SIMP_TAC[]]);;

let WALLOCPAUX_GCT_CALL_FIN_TAC : tactic =
  WALLOCPAUX_GCT_REW THEN REWRITE_TAC[domain_insert; IN_INSERT] THEN SIMP_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY WALLOCPAUX_GCT_IH_TAC;;

(* HOL4 line 11307 *)
let every_var_in_get_clash_tree = prove
 (`!(prog:(A)wl_prog) (lt:(1 spt#1 spt)list).
     wl_every_var (in_clash_tree (get_clash_tree prog lt)) prog`,
  MATCH_MP_TAC get_clash_tree_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(WALLOCPAUX_GCT_REW THEN NO_TAC) THENL
   [(* Move *)
    WALLOCPAUX_GCT2_TAC;
    (* Inst *)
    WALLOCPAUX_GCT_REW THEN REWRITE_TAC[WALLOCPAUX_every_var_get_delta_inst];
    (* Assign *)
    WALLOCPAUX_GCT2_TAC;
    (* Store *)
    WALLOCPAUX_GCT2_TAC;
    (* Seq *)
    STRIP_TAC THEN WALLOCPAUX_GCT_REW THEN SIMP_TAC[] THEN REPEAT CONJ_TAC THEN
    WALLOCPAUX_GCT_IH_TAC;
    (* If *)
    STRIP_TAC THEN MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[get_clash_tree_def; LET_DEF; LET_END_DEF; WALLOCPAUX_reg_imm_CASE] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[wl_every_var_def; every_var_imm_def; in_clash_tree_def; MEM; option_CASE] THEN
    REPEAT CONJ_TAC THEN WALLOCPAUX_GCT_IH_TAC;
    (* Alloc *)
    WALLOCPAUX_GCT2_TAC;
    (* Install *)
    WALLOCPAUX_GCT2_TAC;
    (* FFI *)
    WALLOCPAUX_GCT2_TAC;
    (* Return *)
    WALLOCPAUX_GCT2_TAC;
    (* Set *)
    WALLOCPAUX_GCT2_TAC;
    (* ShareInst *)
    REWRITE_TAC[get_clash_tree_def] THEN COND_CASES_TAC THEN WALLOCPAUX_GCT2_TAC;
    (* Loop *)
    DISCH_TAC THEN WALLOCPAUX_GCT_REW THEN SIMP_TAC[] THEN REPEAT CONJ_TAC THEN
    WALLOCPAUX_GCT_IH_TAC;
    (* Call *)
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN
    MP_TAC(ISPEC `ret:(num list#(num_set#num_set)#(A)wl_prog#num#num)option`
             (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `rq:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [WALLOCPAUX_GCT_CALL_FIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `?vs cs rh k1 k2.
        rq = (vs:num list,cs:num_set#num_set,rh:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    USE_THEN "ihr" (MP_TAC o SPECL [`vs:num list`; `cs:num_set#num_set`; `k1:num`; `k2:num`;
                                   `rh:(A)wl_prog`]) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [ALL_TAC;
      SUBGOAL_THEN `?v hp j1 j2. hq = (v:num,hp:(A)wl_prog,j1:num,j2:num)`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
      USE_THEN "ihh" (MP_TAC o SPECL [`vs:num list`; `cs:num_set#num_set`; `rh:(A)wl_prog`;
                                     `k1:num`; `k2:num`; `v:num`; `j1:num`; `j2:num`;
                                     `hp:(A)wl_prog`]) THEN
      REWRITE_TAC[] THEN DISCH_TAC] THEN
    WALLOCPAUX_GCT_CALL_FIN_TAC]);;

(* HOL4 line 11333 *)
let every_var_T = prove
 (`!(prog:(A)wl_prog). wl_every_var (\x. T) prog`,
  GEN_TAC THEN MATCH_MP_TAC every_var_mono THEN
  EXISTS_TAC `\x. x <= max_var (prog:(A)wl_prog)` THEN REWRITE_TAC[max_var_max]);;

let WALLOCPAUX_phy_total_colour = prove
 (`!(col:num spt) x. is_phy_var (total_colour col x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[total_colour_def] THEN
  MP_TAC(ISPEC `lookup x (col:num spt)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WALLOCPAUX_phy_double; WALLOCPAUX_PHY_REGS]);;

(* HOL4 line 11344 *)
let every_var_is_phy_var_total_colour = prove
 (`!(col:num spt) (prog:(A)wl_prog).
     wl_every_var is_phy_var (apply_colour (total_colour col) prog)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC every_var_apply_colour THEN
  EXISTS_TAC `\x:num. T` THEN REWRITE_TAC[every_var_T; WALLOCPAUX_phy_total_colour]);;

(* HOL4 line 11355 *)
let oracle_colour_ok_conventions = prove
 (`!(prog:(A)wl_prog) k col_opt (lt:(1 spt#1 spt)list) ls x.
     pre_alloc_conventions prog /\
     oracle_colour_ok k col_opt (get_clash_tree prog lt) prog ls = SOME x
     ==> post_alloc_conventions k x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oracle_colour_ok_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `col_opt:((num)spt)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `col:num spt` SUBST1_TAC)) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pre_alloc_conventions_def]) THEN
  ASM_REWRITE_TAC[post_alloc_conventions_def; every_var_is_phy_var_total_colour] THEN
  MATCH_MP_TAC call_arg_convention_preservation THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC every_var_mono THEN EXISTS_TAC `\x:num. T` THEN
  REWRITE_TAC[every_var_T] THEN ASM_MESON_TAC[WALLOCPAUX_total_colour_even]);;

let WALLOCPAUX_total_colour_stack = prove
 (`!spcol tree k x.
     (!r. in_clash_tree tree r
          ==> r IN domain spcol /\
              (if is_phy_var r then sp_default spcol r = r DIV 2
               else if is_stack_var r then k <= sp_default spcol r else T)) /\
     in_clash_tree tree x /\ is_stack_var x
     ==> total_colour spcol x >= 2 * k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~is_phy_var x` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[convention_partitions]; ALL_TAC] THEN
  REWRITE_TAC[total_colour_alt; o_THM] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN ARITH_TAC);;

(* HOL4 line 11374 *)
let pre_post_conventions_word_alloc = prove
 (`!fc (c:(A)asm_config) alg (prog:(A)wl_prog) k col_opt.
     pre_alloc_conventions prog
     ==> post_alloc_conventions k (word_alloc fc c alg k prog col_opt)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_alloc_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `oracle_colour_ok k col_opt (get_clash_tree (prog:(A)wl_prog) [])
                  prog (get_forced (c:(A)asm_config) prog [])` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `cp:(A)wl_prog`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL
   [ALL_TAC; ASM_MESON_TAC[oracle_colour_ok_conventions]] THEN
  WALLOCPAUX_TUPLE_TAC `get_heuristics alg fc (prog:(A)wl_prog)`
    [`heu_moves:(num#num#num)list`; `spillcosts:((num)spt)option`] THEN
  REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPECL [`alg:num`; `spillcosts:((num)spt)option`; `k:num`;
                 `heu_moves:(num#num#num)list`; `get_clash_tree (prog:(A)wl_prog) []`;
                 `get_forced (c:(A)asm_config) (prog:(A)wl_prog) []`;
                 `get_stack_only (prog:(A)wl_prog)`] select_reg_alloc_correct) THEN
  REWRITE_TAC[get_forced_in_get_clash_tree] THEN
  DISCH_THEN(X_CHOOSE_THEN `spcol:num spt` (X_CHOOSE_THEN `livein:num_set`
    (X_CHOOSE_THEN `flivein:num_set` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[WALLOCPAUX_exc_CASE] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pre_alloc_conventions_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "pre_alloc_conventions"
                     with Failure _ -> false)) THEN
  REWRITE_TAC[post_alloc_conventions_def; every_var_is_phy_var_total_colour] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC every_stack_var_apply_colour THEN
    EXISTS_TAC `\x. in_clash_tree (get_clash_tree (prog:(A)wl_prog) []) x /\ is_stack_var x` THEN
    MP_TAC(ISPECL [`in_clash_tree (get_clash_tree (prog:(A)wl_prog) [])`; `prog:(A)wl_prog`;
                   `is_stack_var`] every_stack_var_conj) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC every_var_imp_every_stack_var THEN REWRITE_TAC[every_var_in_get_clash_tree];
      GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC WALLOCPAUX_total_colour_stack THEN
      EXISTS_TAC `get_clash_tree (prog:(A)wl_prog) []` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC call_arg_convention_preservation THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC every_var_mono THEN EXISTS_TAC `\x:num. T` THEN REWRITE_TAC[every_var_T] THEN
    MP_TAC(ISPECL [`spcol:num spt`; `get_clash_tree (prog:(A)wl_prog) []`; `k:num`]
                  WALLOCPAUX_total_colour_spcol) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* helpers for word_alloc_full_inst_ok_less_lem (local to this file) *)

let WALLOCPAUX_arch_distinct = (case_info_of_tyname "architecture").ci_distinct;;

let WALLOCPAUX_inst_ok_less_colour = prove
 (CASE_TERM `!f (i:(A)inst) (c:(A)asm_config).
     inst_ok_less c i /\
     ALL (\xy. match xy with (x,y) -> ~(f x = f y)) (get_forced c (wl_Inst i) [])
     ==> inst_ok_less c (apply_colour_inst f i)`,
  MATCH_MP_TAC WALLOCPAUX_apply_colour_inst_cases THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC([apply_colour_inst_def; get_forced_def; inst_ok_less_def] @
              WALLOCPAUX_INST_CASES) THEN
  TRY(MP_TAC(ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC([apply_colour_imm_def; inst_ok_less_def] @ WALLOCPAUX_INST_CASES)) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC([ALL; APPEND; pair_CASE] @ WALLOCPAUX_arch_distinct) THEN ASM_MESON_TAC[]);;

let WALLOCPAUX_exp_to_addr_colour = prove
 (`!f (exp:(A)wl_exp) n w.
     exp_to_addr exp = SOME (Addr n w)
     ==> exp_to_addr (apply_colour_exp f exp) = SOME (Addr (f n) w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exp_to_addr_ShareInst] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[apply_colour_exp_def; MAP; exp_to_addr_def]);;

let WALLOCPAUX_WFI_REW : tactic =
  REWRITE_TAC[apply_colour_def; full_inst_ok_less_def; get_forced_def; LET_DEF; LET_END_DEF;
              option_CASE; pair_CASE] THEN
  ONCE_REWRITE_TAC[EVERY_get_forced] THEN REWRITE_TAC[ALL];;

let WALLOCPAUX_WFI_IH_TAC : tactic =
  STRIP_TAC THEN REPEAT CONJ_TAC THEN
  FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 11417 *)
let word_alloc_full_inst_ok_less_lem = prove
 (CASE_TERM
  `!f (prog:(A)wl_prog) (c:(A)asm_config).
     full_inst_ok_less c prog /\
     ALL (\xy. match xy with (x,y) -> ~(f x = f y)) (get_forced c prog [])
     ==> full_inst_ok_less c (apply_colour f prog)`,
  MATCH_MP_TAC apply_colour_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(WALLOCPAUX_WFI_REW THEN NO_TAC) THENL
   [(* Inst *)
    REWRITE_TAC[apply_colour_def; full_inst_ok_less_def; WALLOCPAUX_inst_ok_less_colour];
    (* Call *)
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihr") (LABEL_TAC "ihh")) THEN GEN_TAC THEN
    MP_TAC(ISPEC `ret:(num list#(num_set#num_set)#(A)wl_prog#num#num)option`
             (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `rq:num list#(num_set#num_set)#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [WALLOCPAUX_WFI_REW; ALL_TAC] THEN
    SUBGOAL_THEN `?vs cs rh k1 k2.
        rq = (vs:num list,cs:num_set#num_set,rh:(A)wl_prog,k1:num,k2:num)`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    USE_THEN "ihr" (MP_TAC o SPECL [`vs:num list`; `cs:num_set#num_set`; `k1:num`; `k2:num`;
                                   `rh:(A)wl_prog`]) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `h:(num#(A)wl_prog#num#num)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `hq:num#(A)wl_prog#num#num` SUBST_ALL_TAC)) THENL
     [ALL_TAC;
      SUBGOAL_THEN `?v hp j1 j2. hq = (v:num,hp:(A)wl_prog,j1:num,j2:num)`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
      USE_THEN "ihh" (MP_TAC o SPECL [`v:num`; `j1:num`; `j2:num`; `hp:(A)wl_prog`]) THEN
      REWRITE_TAC[] THEN DISCH_TAC] THEN
    WALLOCPAUX_WFI_REW THEN WALLOCPAUX_WFI_IH_TAC;
    (* Seq *)
    DISCH_THEN STRIP_ASSUME_TAC THEN GEN_TAC THEN WALLOCPAUX_WFI_REW THEN WALLOCPAUX_WFI_IH_TAC;
    (* If *)
    DISCH_THEN STRIP_ASSUME_TAC THEN GEN_TAC THEN WALLOCPAUX_WFI_REW THEN WALLOCPAUX_WFI_IH_TAC;
    (* ShareInst *)
    WALLOCPAUX_WFI_REW THEN
    MP_TAC(ISPEC `exp_to_addr (exp:(A)wl_exp)` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; option_CASE])
      (X_CHOOSE_THEN `ad:(A)addr` (fun th -> REWRITE_TAC[th; option_CASE] THEN ASSUME_TAC th))) THEN
    MP_TAC(ISPEC `ad:(A)addr` (cases "addr")) THEN
    DISCH_THEN(X_CHOOSE_THEN `an:num` (X_CHOOSE_THEN `aw:A word` SUBST_ALL_TAC)) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WALLOCPAUX_exp_to_addr_colour th]) THEN
    REWRITE_TAC[option_CASE; WALLOCPAUX_addr_CASE]]);;

(* HOL4 line 11438: lookup_undir_g_insert_existing is commented out in HOL4 *)

(* HOL4 line 11450 *)
let forced_distinct_col = prove
 (CASE_TERM
  `!(spcol:num spt) (ls:(num#num)list).
     ALL (\xy. match xy with (x,y) -> sp_default spcol x = sp_default spcol y ==> x = y) ls /\
     ALL (\xy. match xy with (x,y) -> ~(x = y)) ls
     ==> ALL (\xy. match xy with (x,y) -> ~(total_colour spcol x = total_colour spcol y)) ls`,
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; total_colour_alt; o_THM;
              EQ_MULT_LCANCEL; ARITH_EQ] THEN
  MESON_TAC[]);;

(* HOL4 line 11461 *)
let word_alloc_full_inst_ok_less = prove
 (`!fc alg k (prog:(A)wl_prog) col_opt (c:(A)asm_config).
     full_inst_ok_less c prog
     ==> full_inst_ok_less c (word_alloc fc c alg k prog col_opt)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_alloc_def; LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `oracle_colour_ok k col_opt (get_clash_tree (prog:(A)wl_prog) [])
                  prog (get_forced (c:(A)asm_config) prog [])` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `cp:(A)wl_prog`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[option_CASE] THENL
   [WALLOCPAUX_TUPLE_TAC `get_heuristics alg fc (prog:(A)wl_prog)`
      [`heu_moves:(num#num#num)list`; `spillcosts:((num)spt)option`] THEN
    REWRITE_TAC[pair_CASE] THEN
    MP_TAC(ISPECL [`alg:num`; `spillcosts:((num)spt)option`; `k:num`;
                   `heu_moves:(num#num#num)list`; `get_clash_tree (prog:(A)wl_prog) []`;
                   `get_forced (c:(A)asm_config) (prog:(A)wl_prog) []`;
                   `get_stack_only (prog:(A)wl_prog)`] select_reg_alloc_correct) THEN
    REWRITE_TAC[get_forced_in_get_clash_tree] THEN
    DISCH_THEN(X_CHOOSE_THEN `spcol:num spt` (X_CHOOSE_THEN `livein:num_set`
      (X_CHOOSE_THEN `flivein:num_set` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[WALLOCPAUX_exc_CASE] THEN
    MATCH_MP_TAC word_alloc_full_inst_ok_less_lem THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC forced_distinct_col THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC get_forced_pairwise_distinct THEN REWRITE_TAC[ALL];
    UNDISCH_TAC `oracle_colour_ok k col_opt (get_clash_tree (prog:(A)wl_prog) [])
                   prog (get_forced (c:(A)asm_config) prog []) = SOME cp` THEN
    REWRITE_TAC[oracle_colour_ok_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    MP_TAC(ISPEC `col_opt:((num)spt)option` (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `col:num spt` SUBST1_TAC)) THEN
    REWRITE_TAC[option_CASE; option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC word_alloc_full_inst_ok_less_lem THEN ASM_REWRITE_TAC[]]);;
