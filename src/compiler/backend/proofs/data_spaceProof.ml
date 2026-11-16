(* ========================================================================= *)
(* data_spaceProof: port of HOL4 compiler/backend/proofs/                    *)
(* data_spaceProofScript.sml (CakeML v3479).  Correctness proof for          *)
(* data_space.  DATAPAUX_ names are local helpers (not HOL4 names).          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;

type_invention_error := true;;

(* HOL4 [local] *)
let IMP_sptree_eq = prove
 (`!(x:A spt) y. wf x /\ wf y /\ (!a. lookup a x = lookup a y) ==> x = y`,
  MESON_TAC[spt_eq_thm]);;

(* HOL4 [local] mk_wf_inter; renamed: data_to_word_assignProof_p1 binds    *)
(* mk_wf_inter to the converse equation                                    *)
let data_spaceProof_mk_wf_inter = prove
 (`!(t1:A spt) (t2:B spt). inter t1 t2 = mk_wf (inter t1 t2)`,
  MESON_TAC[wf_mk_id; wf_inter]);;

let data_spaceProof_get_vars_IMP_LENGTH = prove
 (`!xs (s:A spt) l. data_get_vars xs s = SOME l ==> LENGTH l = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_get_vars_def] THENL
   [MESON_TAC[option_INJ; LENGTH]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

let do_stack_with_space = prove
 (`!op vs (s:(C,FFI)data_state) z.
     do_stack op vs (data_state_space_fupd (K z) s) =
     data_state_space_fupd (K z) (do_stack op vs s)`,
  REWRITE_TAC[do_stack_def; LET_DEF; LET_END_DEF; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM]);;

let do_stack_with_locals = prove
 (`!op vs (s:(C,FFI)data_state) l.
     do_stack op vs (data_state_locals_fupd (K l) s) =
     data_state_locals_fupd (K l) (do_stack op vs s)`,
  REWRITE_TAC[do_stack_def; LET_DEF; LET_END_DEF; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_compile: one theorem per case of HOL4's recInduct proof (its    *)
(* suspend/Resume blocks), then the theorem itself                          *)
(* ------------------------------------------------------------------------- *)

(* the statement of evaluate_compile (the unused vars of HOL4 is added at  *)
(* the end)                                                               *)
let DATAPAUX_SPACE_GOAL =
 `!c (s:(C,FFI)data_state) res s2 (vars:A) l.
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\ data_evaluate (c,s) = (res,s2) /\
     locals_ok (data_state_locals s) l ==>
     ?w safe peak smx.
       data_evaluate (data_space_compile c,data_state_locals_fupd (K l) s) =
       (res,if res = NONE
            then data_state_locals_fupd (K w)
                   (data_state_stack_max_fupd (K smx)
                      (data_state_safe_for_space_fupd (K safe)
                         (data_state_peak_heap_length_fupd (K peak) s2)))
            else data_state_stack_max_fupd (K smx)
                   (data_state_safe_for_space_fupd (K safe)
                      (data_state_peak_heap_length_fupd (K peak) s2))) /\
       locals_ok (data_state_locals s2) w`;;

(* the instance of data_evaluate_ind for a statement !c s. body: its       *)
(* antecedent conjuncts are the cases of HOL4's recInduct proof            *)
let DATAPAUX_SPACE_IND_INST (goal:term) (ind:thm) =
  let c,b1 = dest_forall goal in
  let s,b = dest_forall b1 in
  let p = mk_var("p",mk_type("prod",[type_of c;type_of s])) in
  let fstp = mk_icomb(mk_const("FST",[]),p)
  and sndp = mk_icomb(mk_const("SND",[]),p) in
  let pred = mk_abs(p,vsubst [fstp,c; sndp,s] b) in
  CONV_RULE (DEPTH_CONV BETA_CONV THENC REWRITE_CONV[FST; SND]) (ISPEC pred ind);;

let DATAPAUX_SPACE_IND = DATAPAUX_SPACE_IND_INST DATAPAUX_SPACE_GOAL data_evaluate_ind;;
let DATAPAUX_SPACE_CASES = conjuncts (lhand (concl DATAPAUX_SPACE_IND));;

let DATAPAUX_SPACE_RES_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM));;
let DATAPAUX_SPACE_FUPD_RWS =
  [data_state_INFO.ri_accfupds; K_THM; DSEMAUX_fupd_id; data_state_INFO.ri_fupdcanon;
   data_state_INFO.ri_fupdfupds; K_o_THM];;
let DATAPAUX_SPACE_WIT_TAC (wl:term option) (thl:thm list) : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let pk = el 2 vs in
  let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
            (try fst(dest_const(rator(rator t))) = "data_state_peak_heap_length_fupd" &&
                 rand(rand(rator t)) = pk
             with Failure _ -> false)) body in
  let y = rand t in
  let mk f = mk_icomb(mk_const(f,[]), y) in
  let wt = match wl with Some x -> x | None -> mk "data_state_locals" in
  (MAP_EVERY EXISTS_TAC [wt; mk "data_state_safe_for_space";
                         mk "data_state_peak_heap_length"; mk "data_state_stack_max"] THEN
   ASM_REWRITE_TAC (COND_ID :: locals_ok_refl :: DATAPAUX_SPACE_FUPD_RWS) THEN
   REWRITE_TAC thl THEN ASM_REWRITE_TAC (PAIR_EQ :: DATAPAUX_SPACE_FUPD_RWS)) g;;

let DATAPAUX_SPACE_jump_exc_locals = prove
 (`!(s:(C,FFI)data_state) l.
     data_jump_exc (data_state_locals_fupd (K l) s) = data_jump_exc s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def; data_state_INFO.ri_accfupds; K_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[] THEN TOP_CASE_TAC THEN
  REWRITE_TAC(option_INJ :: DATAPAUX_SPACE_FUPD_RWS));;

(* HOL4: evaluate_compile[Skip] *)
let DATAPAUX_SPACE_SKIP = prove
 (el 0 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   DATAPAUX_SPACE_RES_TAC THEN
   MAP_EVERY EXISTS_TAC [`l:data_v spt`;
                        `data_state_safe_for_space (s:(C,FFI)data_state)`;
                        `data_state_peak_heap_length (s:(C,FFI)data_state)`;
                        `data_state_stack_max (s:(C,FFI)data_state)`] THEN
   ASM_REWRITE_TAC[DSEMAUX_fupd_id; data_state_INFO.ri_fupdcanon;
                   data_state_INFO.ri_fupdfupds; K_o_THM]);;

(* HOL4: evaluate_compile[Move] *)
let DATAPAUX_SPACE_MOVE = prove
 (el 1 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   TOP_CASE_TAC THEN DATAPAUX_SPACE_RES_TAC THENL
    [FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP locals_ok_get_var (CONJ th th2)])) THEN
   CASE_REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC [`insert dest a (l:data_v spt)`;
                        `data_state_safe_for_space (s:(C,FFI)data_state)`;
                        `data_state_peak_heap_length (s:(C,FFI)data_state)`;
                        `data_state_stack_max (s:(C,FFI)data_state)`] THEN
   ASM_SIMP_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM; locals_ok_insert;
                DSEMAUX_fupd_id; data_state_INFO.ri_fupdcanon;
                data_state_INFO.ri_fupdfupds; K_o_THM]);;

(* witnesses from the state X of the left side (res,X) of the goal; the   *)
(* result equation is then decided by component equality                   *)
let DATAPAUX_SPACE_LWIT_TAC (wl:term option) (thl:thm list) : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let sty = type_of (el 3 vs) in
  let is_st t = (try fst(dest_type(type_of t)) = "data_state" with Failure _ -> false) in
  let eq = find (fun c -> is_eq c &&
                   (is_pair (lhs c) || is_st (lhs c))) (conjuncts body) in
  let x = if is_pair (lhs eq) then snd (dest_pair (lhs eq)) else lhs eq in
  let mk f = mk_icomb(mk_const(f,[]), x) in
  let wt = match wl with Some y -> y | None -> mk "data_state_locals" in
  (MAP_EVERY EXISTS_TAC [wt; mk "data_state_safe_for_space";
                         mk "data_state_peak_heap_length"; mk "data_state_stack_max"] THEN
   ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
   REWRITE_TAC thl THEN
   REWRITE_TAC[data_state_component_equality; data_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC thl) g;;

(* HOL4: evaluate_compile[Assign] *)
let DATAPAUX_SPACE_ASSIGN = prove
 (el 2 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  COND_CASES_TAC THENL [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
  TOP_CASE_TAC THENL [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    REWRITE_TAC[MATCH_MP locals_ok_get_vars (CONJ th th2)])) THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `names_opt:num_set option` THEN REWRITE_TAC[data_cut_state_opt_def] THEN
  CASE_REWRITE_TAC[] THENL
   [(* NONE: HOL4 do_app_with_locals *)
    REWRITE_TAC[do_app_with_locals] THEN
    MP_TAC(ISPEC `data_do_app op a (s:(C,FFI)data_state)` (cases "result")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xy:data_v#(C,FFI)data_state` ASSUME_TAC)
      (X_CHOOSE_THEN `e:(data_v)error_result` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[map_result_def] THEN CASE_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `xy:data_v#(C,FFI)data_state` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:data_v` (X_CHOOSE_THEN `y:(C,FFI)data_state`
        SUBST_ALL_TAC)) THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
      DATAPAUX_SPACE_RES_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_const) THEN
      DATAPAUX_SPACE_LWIT_TAC (Some `insert dest v (l:data_v spt)`)
        [data_set_var_def; install_sfs_def] THEN
      MATCH_MP_TAC locals_ok_insert THEN ASM_REWRITE_TAC[];
      DATAPAUX_SPACE_RES_TAC THEN
      DATAPAUX_SPACE_WIT_TAC None [data_flush_state_def; install_sfs_def; map_error_result_I]];
    (* SOME names: the cut state is the same *)
    REWRITE_TAC[data_cut_state_def; data_state_INFO.ri_accfupds; K_THM] THEN
    MP_TAC(ISPEC `data_cut_env a' (data_state_locals (s:(C,FFI)data_state))`
             (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `env:data_v spt` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
     [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
      REWRITE_TAC[MATCH_MP locals_ok_cut_env (CONJ th th2)])) THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[data_state_INFO.ri_fupdfupds; K_o_THM] THEN
    DISCH_THEN SUBST1_TAC THEN DATAPAUX_SPACE_WIT_TAC None []]);;

(* HOL4: evaluate_compile[Tick] *)
let DATAPAUX_SPACE_TICK = prove
 (el 3 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   COND_CASES_TAC THEN DATAPAUX_SPACE_RES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THENL
    [DATAPAUX_SPACE_WIT_TAC None [data_flush_state_def];
     DATAPAUX_SPACE_WIT_TAC (Some `l:data_v spt`) [data_dec_clock_def]]);;

(* HOL4: evaluate_compile[MakeSpace] *)
let DATAPAUX_SPACE_MAKESPACE = prove
 (el 4 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; Seq_Skip] THEN
   REWRITE_TAC[data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   TOP_CASE_TAC THEN DATAPAUX_SPACE_RES_TAC THENL [FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP locals_ok_cut_env (CONJ th th2)])) THEN
   CASE_REWRITE_TAC[] THEN
   DATAPAUX_SPACE_WIT_TAC None [add_space_def]);;

(* HOL4: evaluate_compile[Raise] *)
let DATAPAUX_SPACE_RAISE = prove
 (el 5 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; DATAPAUX_SPACE_jump_exc_locals] THEN
   TOP_CASE_TAC THENL [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP locals_ok_get_var (CONJ th th2)])) THEN
   CASE_REWRITE_TAC[] THEN
   TOP_CASE_TAC THEN DATAPAUX_SPACE_RES_TAC THEN TRY (FS[] THEN NO_TAC) THEN
   DATAPAUX_SPACE_WIT_TAC None [option_DISTINCT]);;

(* HOL4: evaluate_compile[Return] *)
let DATAPAUX_SPACE_RETURN = prove
 (el 6 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   TOP_CASE_TAC THENL [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP locals_ok_get_vars (CONJ th th2)])) THEN
   CASE_REWRITE_TAC[] THEN DATAPAUX_SPACE_RES_TAC THEN
   DATAPAUX_SPACE_WIT_TAC None [option_DISTINCT; data_flush_state_def]);;

(* the Seq case: lemmas for the shapes of HOL4's case split on c1 and on *)
(* space c2, and the case itself                                          *)
let DATAPAUX_SPACE_SEQ_CASE = el 7 DATAPAUX_SPACE_CASES;;
let DATAPAUX_SPACE_SEQ_GEN_TM =
  let vs,body = strip_forall DATAPAUX_SPACE_SEQ_CASE in
  list_mk_forall(vs,
    subst [`data_Seq (data_space_compile c1) (data_space_compile c2)`,
           `data_space_compile (data_Seq c1 c2)`] body);;

(* the generic shape: Seq (compile c1) (compile c2) *)
let DATAPAUX_SPACE_SEQ_GEN = prove
 (DATAPAUX_SPACE_SEQ_GEN_TM,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `data_evaluate (c1,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `u1:(C,FFI)data_state` ASSUME_TAC)) THEN
  UNDISCH_TAC `data_evaluate (data_Seq c1 c2,s:(C,FFI)data_state) = res,s2` THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `r1:((data_v list,data_v)result)option = SOME (Rerr (Rabort Rtype_error))` THENL
   [ASM_REWRITE_TAC[option_DISTINCT] THEN DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`r1:((data_v list,data_v)result)option`;
                                     `u1:(C,FFI)data_state`; `l:data_v spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:data_v spt` (X_CHOOSE_THEN `sf1:bool`
    (X_CHOOSE_THEN `pk1:num` (X_CHOOSE_THEN `sm1:num option` STRIP_ASSUME_TAC)))) THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[pair_CASE] THEN
  ASM_CASES_TAC `r1:((data_v list,data_v)result)option = NONE` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `u1:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`res:((data_v list,data_v)result)option`;
                               `s2:(C,FFI)data_state`; `w1:data_v spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w2:data_v spt` (X_CHOOSE_THEN `sf2:bool`
      (X_CHOOSE_THEN `pk2:num` (X_CHOOSE_THEN `sm2:num option` STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`sm1:num option`; `sf1:bool`; `pk1:num`] o
                  MATCH_MP evaluate_smx_safe_peak_swap o
                  check (fun th -> is_eq (concl th) &&
                           can (find_term ((=) `data_space_compile c2`)) (lhs (concl th)))) THEN
    REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS THEN
    DISCH_THEN(X_CHOOSE_THEN `sm3:num option` (X_CHOOSE_THEN `sf3:bool`
      (X_CHOOSE_THEN `pk3:num` SUBST1_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`w2:data_v spt`; `sf3:bool`; `pk3:num`; `sm3:num option`] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS;
    ASM_REWRITE_TAC[] THEN DATAPAUX_SPACE_RES_TAC THEN
    MAP_EVERY EXISTS_TAC [`data_state_locals (u1:(C,FFI)data_state)`; `sf1:bool`;
                          `pk1:num`; `sm1:num option`] THEN
    ASM_REWRITE_TAC[locals_ok_refl]]);;

(* the Seq case for a given first program c1' (free variables quantified), *)
(* with the compiled program prog and an optional extra hypothesis         *)
let DATAPAUX_SPACE_SEQ_TM (c1':term) (prog:term) (extra:term option) =
  let vs,body = strip_forall DATAPAUX_SPACE_SEQ_CASE in
  let c1 = hd vs in
  let body1 = vsubst [c1',c1] body in
  let old = mk_comb(`data_space_compile`, mk_comb(mk_comb(`data_Seq`,c1'),`c2:data_prog`)) in
  let body2 = subst [prog,old] body1 in
  let body3 = match extra with Some h -> mk_imp(h,body2) | None -> body2 in
  list_mk_forall(frees c1' @ tl vs, body3);;

let DATAPAUX_SPACE_SEQ_SKIP = prove
 (DATAPAUX_SPACE_SEQ_TM `data_Skip` `data_space_compile c2` None,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def; pair_CASE] THEN STRIP_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC `s:(C,FFI)data_state`) THEN
  REWRITE_TAC[data_evaluate_def] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_SPACE_SEQ_MAKESPACE = prove
 (DATAPAUX_SPACE_SEQ_TM `MakeSpace k names`
    `data_Seq (MakeSpace k names) (data_space_compile c2)` None,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `data_evaluate (data_Seq (MakeSpace k names) c2,s:(C,FFI)data_state) = res,s2` THEN
  ONCE_REWRITE_TAC[data_evaluate_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [data_evaluate_def] THEN
  REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC(ISPEC `data_cut_env names (data_state_locals (s:(C,FFI)data_state))`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `env:data_v spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    REWRITE_TAC[MATCH_MP locals_ok_cut_env (CONJ th th2)])) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[data_state_INFO.ri_fupdfupds; K_o_THM] THEN
  DISCH_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC
    `add_space (data_state_locals_fupd (K env) (s:(C,FFI)data_state)) k`) THEN
  REWRITE_TAC[data_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((data_v list,data_v)result)option`;
     `s2:(C,FFI)data_state`;
     `data_state_locals (add_space (data_state_locals_fupd (K env) (s:(C,FFI)data_state)) k)`]) THEN
  ASM_REWRITE_TAC[locals_ok_refl; data_with_same_locals]);;

let DATAPAUX_SPACE_cut_inter = prove
 (`!(s:(C,FFI)data_state) l names1 names2 x1 x2.
     locals_ok (data_state_locals s) l /\
     data_cut_env names1 (data_state_locals s) = SOME x1 /\
     data_cut_env names2 x1 = SOME x2 ==>
     data_cut_env (inter names1 names2) l = SOME x2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  REPEAT (COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THENL
   [REWRITE_TAC[mk_wf_eq; lookup_inter_alt; lookup_mk_wf; domain_inter; IN_INTER] THEN
    X_GEN_TAC `x:num` THEN
    ASM_CASES_TAC `x IN domain (names2:num_set)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x IN domain (names1:num_set)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `domain (names1:num_set) SUBSET domain (data_state_locals (s:(C,FFI)data_state))` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`data_state_locals (s:(C,FFI)data_state)`; `l:data_v spt`; `x:num`;
                   `v:data_v`] locals_ok_get_var) THEN
    ASM_REWRITE_TAC[data_get_var_def];
    UNDISCH_TAC `~(domain (inter (names1:num_set) (names2:num_set)) SUBSET domain (l:data_v spt))` THEN
    REWRITE_TAC[SUBSET; domain_inter; IN_INTER] THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `domain (names1:num_set) SUBSET domain (data_state_locals (s:(C,FFI)data_state))` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`data_state_locals (s:(C,FFI)data_state)`; `l:data_v spt`; `x:num`;
                   `v:data_v`] locals_ok_get_var) THEN
    ASM_REWRITE_TAC[data_get_var_def] THEN MESON_TAC[domain_lookup]]);;

let DATAPAUX_SPACE_add_space_locals = prove
 (`!(s:(C,FFI)data_state) k. data_state_locals (add_space s k) = data_state_locals s`,
  REWRITE_TAC[add_space_def; data_state_INFO.ri_accfupds]);;

let DATAPAUX_SPACE_ms_merge = prove
 (`!(s:(C,FFI)data_state) l names1 names2 x1 k1 k2 c4 r z.
     locals_ok (data_state_locals s) l /\
     data_cut_env names1 (data_state_locals s) = SOME x1 /\
     data_evaluate (data_Seq (MakeSpace k2 names2) c4,
                    add_space (data_state_locals_fupd (K x1) s) k1) = (r,z) /\
     ~(r = SOME (Rerr (Rabort Rtype_error))) ==>
     ?safe peak.
       data_evaluate (data_Seq (MakeSpace k2 (inter names1 names2)) c4,
                      data_state_locals_fupd (K l) s) =
       (r,data_state_safe_for_space_fupd (K safe) (data_state_peak_heap_length_fupd (K peak) z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  REWRITE_TAC[DATAPAUX_SPACE_add_space_locals; data_state_INFO.ri_accfupds; K_THM] THEN
  MP_TAC(ISPEC `data_cut_env names2 (x1:data_v spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x2:data_v spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(C,FFI)data_state`; `l:data_v spt`; `names1:num_set`; `names2:num_set`;
                 `x1:data_v spt`; `x2:data_v spt`] DATAPAUX_SPACE_cut_inter) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ABBREV_TAC `A = add_space (data_state_locals_fupd (K x2)
                    (add_space (data_state_locals_fupd (K x1) (s:(C,FFI)data_state)) k1)) k2` THEN
  ABBREV_TAC `B = add_space (data_state_locals_fupd (K x2)
                    (data_state_locals_fupd (K l) (s:(C,FFI)data_state))) k2` THEN
  SUBGOAL_THEN `B = data_state_safe_for_space_fupd (K (data_state_safe_for_space B))
                      (data_state_peak_heap_length_fupd (K (data_state_peak_heap_length B))
                         (A:(C,FFI)data_state))` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[add_space_def; data_state_component_equality; data_state_INFO.ri_accfupds;
                K_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`data_state_safe_for_space (B:(C,FFI)data_state)`; `z:(C,FFI)data_state`;
                 `A:(C,FFI)data_state`; `r:((data_v list,data_v)result)option`;
                 `data_state_peak_heap_length (B:(C,FFI)data_state)`; `c4:data_prog`]
                evaluate_safe_peak_swap) THEN
  ASM_REWRITE_TAC[]);;

let DATAPAUX_SPACE_SEQ_MS_INR = prove
 (DATAPAUX_SPACE_SEQ_TM `MakeSpace k1 names1`
    `data_Seq (MakeSpace k2 (inter names1 (names2:num_set))) c4`
    (Some `space c2 = INR (k2,(names2:num_set),c4)`),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `data_evaluate (data_Seq (MakeSpace k1 names1) c2,s:(C,FFI)data_state) = res,s2` THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[data_evaluate_def] THENC
                     REWRITE_CONV[data_evaluate_def; data_state_INFO.ri_accfupds; K_THM])) THEN
  MP_TAC(ISPEC `data_cut_env names1 (data_state_locals (s:(C,FFI)data_state))`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x1:data_v spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
  DISCH_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC
    `add_space (data_state_locals_fupd (K x1) (s:(C,FFI)data_state)) k1`) THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[data_evaluate_def])) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((data_v list,data_v)result)option`;
     `s2:(C,FFI)data_state`; `x1:data_v spt`]) THEN
  ASM_REWRITE_TAC[data_space_compile_def; pMakeSpace_def; DATAPAUX_SPACE_add_space_locals;
                  data_state_INFO.ri_accfupds; K_THM; locals_ok_refl] THEN
  SUBGOAL_THEN `data_state_locals_fupd (K x1)
                  (add_space (data_state_locals_fupd (K x1) (s:(C,FFI)data_state)) k1) =
                add_space (data_state_locals_fupd (K x1) s) k1` SUBST1_TAC THENL
   [MATCH_MP_TAC(MESON[data_with_same_locals]
      `data_state_locals (u:(C,FFI)data_state) = x ==> data_state_locals_fupd (K x) u = u`) THEN
    REWRITE_TAC[DATAPAUX_SPACE_add_space_locals; data_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:data_v spt` (X_CHOOSE_THEN `sf2:bool`
    (X_CHOOSE_THEN `pk2:num` (X_CHOOSE_THEN `sm2:num option` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DATAPAUX_SPACE_ms_merge o
    CONJ (ASSUME `locals_ok (data_state_locals (s:(C,FFI)data_state)) l`) o
    CONJ (ASSUME `data_cut_env names1 (data_state_locals (s:(C,FFI)data_state)) = SOME x1`) o
    (fun th -> CONJ th (ASSUME `~(res:((data_v list,data_v)result)option =
                                   SOME (Rerr (Rabort Rtype_error)))`)) o
    check (fun th -> is_eq (concl th) &&
             can (find_term ((=) `c4:data_prog`)) (lhs (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `sf3:bool` (X_CHOOSE_THEN `pk3:num` SUBST1_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`w2:data_v spt`; `sf3:bool`; `pk3:num`; `sm2:num option`] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS);;

let DATAPAUX_SPACE_cut_move = prove
 (`!(l:data_v spt) names2 dest src x x'.
     lookup src l = SOME x /\ data_cut_env names2 (insert dest x l) = SOME x' ==>
     ?e1. data_cut_env (insert src one (delete dest names2)) l = SOME e1 /\
          lookup src e1 = SOME x /\ locals_ok x' (insert dest x e1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `domain (insert src one (delete dest names2)) SUBSET domain (l:data_v spt)`
    (fun th -> REWRITE_TAC[th; option_INJ; UNWIND_THM1]) THENL
   [UNDISCH_TAC `domain (names2:num_set) SUBSET domain (insert dest (x:data_v) l)` THEN
    REWRITE_TAC[SUBSET; domain_insert; domain_delete; IN_INSERT; IN_DELETE] THEN
    REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_insert; IN_INSERT; locals_ok_def;
              lookup_insert; domain_delete; IN_DELETE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `v:num = dest` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `v:num = src` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[option_INJ]);;

let DATAPAUX_SPACE_eval_frame = prove
 (`!c (A:(C,FFI)data_state) res X ll sf pk.
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\ data_evaluate (c,A) = (res,X) /\
     locals_ok (data_state_locals A) ll ==>
     ?w safe peak smx.
       data_evaluate (c,data_state_locals_fupd (K ll)
                          (data_state_safe_for_space_fupd (K sf)
                             (data_state_peak_heap_length_fupd (K pk) A))) =
       (res,if res = NONE
            then data_state_locals_fupd (K w)
                   (data_state_stack_max_fupd (K smx)
                      (data_state_safe_for_space_fupd (K safe)
                         (data_state_peak_heap_length_fupd (K peak) X)))
            else data_state_stack_max_fupd (K smx)
                   (data_state_safe_for_space_fupd (K safe)
                      (data_state_peak_heap_length_fupd (K peak) X))) /\
       locals_ok (data_state_locals X) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`; `A:(C,FFI)data_state`;
                 `res:((data_v list,data_v)result)option`; `X:(C,FFI)data_state`;
                 `ll:data_v spt`] evaluate_locals) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:data_v spt` (X_CHOOSE_THEN `sf1:bool`
    (X_CHOOSE_THEN `pk1:num` (X_CHOOSE_THEN `sm1:num option` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP evaluate_safe_peak_swap o
                check (fun th -> is_eq (concl th) &&
                         can (find_term ((=) `ll:data_v spt`)) (lhs (concl th)))) THEN
  DISCH_THEN(MP_TAC o SPECL [`sf:bool`; `pk:num`]) THEN
  REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS THEN
  DISCH_THEN(X_CHOOSE_THEN `sf2:bool` (X_CHOOSE_THEN `pk2:num` SUBST1_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`w:data_v spt`; `sf2:bool`; `pk2:num`; `sm1:num option`] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS);;

let DATAPAUX_SPACE_locals_ok_trans = prove
 (`!(a:A spt) b c. locals_ok a b /\ locals_ok b c ==> locals_ok a c`,
  REWRITE_TAC[locals_ok_def] THEN MESON_TAC[]);;

let DATAPAUX_SPACE_SEQ_MOVE_INR = prove
 (DATAPAUX_SPACE_SEQ_TM `data_Move dest src`
    `data_Seq (MakeSpace k2 (insert src one (delete dest (names2:num_set))))
              (data_Seq (data_Move dest src) c4)`
    (Some `space c2 = INR (k2,(names2:num_set),c4)`),
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ih2")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `data_evaluate (data_Seq (data_Move dest src) c2,s:(C,FFI)data_state) = res,s2` THEN
   CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[data_evaluate_def] THENC
                      REWRITE_CONV[data_evaluate_def; data_state_INFO.ri_accfupds; K_THM])) THEN
   MP_TAC(ISPEC `data_get_var src (data_state_locals (s:(C,FFI)data_state))` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:data_v` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   DISCH_TAC THEN
   REMOVE_THEN "ih2" (MP_TAC o SPEC `data_set_var dest a (s:(C,FFI)data_state)`) THEN
   CONV_TAC(LAND_CONV(REWRITE_CONV[data_evaluate_def])) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`res:((data_v list,data_v)result)option`;
      `s2:(C,FFI)data_state`; `insert dest a (l:data_v spt)`]) THEN
   ASM_REWRITE_TAC[data_space_compile_def; pMakeSpace_def] THEN
   ANTS_TAC THENL
    [REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds; K_THM] THEN
     MATCH_MP_TAC locals_ok_insert THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[data_set_var_def; data_state_INFO.ri_fupdfupds; K_o_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `w2:data_v spt` (X_CHOOSE_THEN `sf2:bool`
     (X_CHOOSE_THEN `pk2:num` (X_CHOOSE_THEN `sm2:num option` STRIP_ASSUME_TAC))))) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term ((=) `c4:data_prog`)) (lhs (concl th)))) THEN
   REWRITE_TAC[data_evaluate_def; data_state_INFO.ri_accfupds; K_THM] THEN
   MP_TAC(ISPEC `data_cut_env names2 (insert dest a (l:data_v spt))` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x':data_v spt` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[data_state_INFO.ri_fupdfupds; K_o_THM] THEN DISCH_TAC THEN
   SUBGOAL_THEN `lookup src (l:data_v spt) = SOME a` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`data_state_locals (s:(C,FFI)data_state)`; `l:data_v spt`; `src:num`;
                    `a:data_v`] locals_ok_get_var) THEN
     ASM_REWRITE_TAC[data_get_var_def] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[data_get_var_def]) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`l:data_v spt`; `names2:num_set`; `dest:num`; `src:num`; `a:data_v`;
                  `x':data_v spt`] DATAPAUX_SPACE_cut_move) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `e1:data_v spt` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[data_state_INFO.ri_fupdfupds; K_o_THM; DATAPAUX_SPACE_add_space_locals;
                   data_state_INFO.ri_accfupds; K_THM; data_get_var_def] THEN
   CASE_REWRITE_TAC[]) THEN
  (ASM_REWRITE_TAC[DATAPAUX_SPACE_add_space_locals; data_state_INFO.ri_accfupds; K_THM] THEN
   CASE_REWRITE_TAC[] THEN
   ABBREV_TAC `A = add_space (data_state_locals_fupd (K x') (s:(C,FFI)data_state)) k2` THEN
   SUBGOAL_THEN
     `data_set_var dest a (add_space (data_state_locals_fupd (K e1) (s:(C,FFI)data_state)) k2) =
      data_state_locals_fupd (K (insert dest a e1))
        (data_state_safe_for_space_fupd
           (K (data_state_safe_for_space (add_space (data_state_locals_fupd (K e1) s) k2)))
           (data_state_peak_heap_length_fupd
              (K (data_state_peak_heap_length (add_space (data_state_locals_fupd (K e1) s) k2)))
              A))` SUBST1_TAC THENL
    [EXPAND_TAC "A" THEN
     REWRITE_TAC[data_set_var_def; add_space_def; data_state_component_equality;
                 data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`c4:data_prog`; `A:(C,FFI)data_state`;
     `res:((data_v list,data_v)result)option`;
     `if (res:((data_v list,data_v)result)option) = NONE
      then data_state_locals_fupd (K w2)
             (data_state_stack_max_fupd (K sm2)
                (data_state_safe_for_space_fupd (K sf2)
                   (data_state_peak_heap_length_fupd (K pk2) (s2:(C,FFI)data_state))))
      else data_state_stack_max_fupd (K sm2)
             (data_state_safe_for_space_fupd (K sf2)
                (data_state_peak_heap_length_fupd (K pk2) s2))`;
     `insert dest a (e1:data_v spt)`;
     `data_state_safe_for_space (add_space (data_state_locals_fupd (K e1) (s:(C,FFI)data_state)) k2)`;
     `data_state_peak_heap_length (add_space (data_state_locals_fupd (K e1) (s:(C,FFI)data_state)) k2)`]
     DATAPAUX_SPACE_eval_frame) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN
     ASM_REWRITE_TAC[DATAPAUX_SPACE_add_space_locals; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `w3:data_v spt` (X_CHOOSE_THEN `sf3:bool`
     (X_CHOOSE_THEN `pk3:num` (X_CHOOSE_THEN `sm3:num option` STRIP_ASSUME_TAC)))) THEN
   ASM_REWRITE_TAC[pair_CASE] THEN
   MAP_EVERY EXISTS_TAC [`if (res:((data_v list,data_v)result)option) = NONE
                          then w3 else data_state_locals (s2:(C,FFI)data_state)`;
                         `sf3:bool`; `pk3:num`; `sm3:num option`] THEN
   ASM_CASES_TAC `res:((data_v list,data_v)result)option = NONE` THEN
   ASM_REWRITE_TAC (locals_ok_refl :: DATAPAUX_SPACE_FUPD_RWS) THEN
   UNDISCH_TAC `locals_ok (data_state_locals (if (res:((data_v list,data_v)result)option) = NONE
     then data_state_locals_fupd (K w2)
            (data_state_stack_max_fupd (K sm2)
               (data_state_safe_for_space_fupd (K sf2)
                  (data_state_peak_heap_length_fupd (K pk2) (s2:(C,FFI)data_state))))
     else data_state_stack_max_fupd (K sm2)
            (data_state_safe_for_space_fupd (K sf2)
               (data_state_peak_heap_length_fupd (K pk2) s2)))) w3` THEN
   ASM_REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS THEN
   ASM_MESON_TAC[DATAPAUX_SPACE_locals_ok_trans]));;

let DATAPAUX_SPACE_do_app_frame = prove
 (`!op xs (s:(C,FFI)data_state) v s' l sp sm sf pk.
     data_do_app op xs s = Rval (v,s') /\ ~op_space_reset op /\ ~(op = clos_Install) /\
     op_space_req op (LENGTH xs) <= sp ==>
     ?safe peak smx.
       data_do_app op xs
         (data_state_locals_fupd (K l) (data_state_stack_max_fupd (K sm)
            (data_state_space_fupd (K sp) (data_state_safe_for_space_fupd (K sf)
               (data_state_peak_heap_length_fupd (K pk) s))))) =
       Rval (v,data_state_locals_fupd (K l) (data_state_stack_max_fupd (K smx)
                 (data_state_space_fupd (K (sp - op_space_req op (LENGTH xs)))
                    (data_state_safe_for_space_fupd (K safe)
                       (data_state_peak_heap_length_fupd (K peak) s')))))`,
  DSEMAUX_DO_APP_SWAP_TAC DSEMAUX_DO_APP_DEFS THEN ASM_ARITH_TAC);;

let DATAPAUX_SPACE_eval_frame2 = prove
 (`!c (A:(C,FFI)data_state) res X ll sm sf pk.
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\ data_evaluate (c,A) = (res,X) /\
     locals_ok (data_state_locals A) ll ==>
     ?w safe peak smx.
       data_evaluate (c,data_state_locals_fupd (K ll)
                          (data_state_stack_max_fupd (K sm)
                             (data_state_safe_for_space_fupd (K sf)
                                (data_state_peak_heap_length_fupd (K pk) A)))) =
       (res,if res = NONE
            then data_state_locals_fupd (K w)
                   (data_state_stack_max_fupd (K smx)
                      (data_state_safe_for_space_fupd (K safe)
                         (data_state_peak_heap_length_fupd (K peak) X)))
            else data_state_stack_max_fupd (K smx)
                   (data_state_safe_for_space_fupd (K safe)
                      (data_state_peak_heap_length_fupd (K peak) X))) /\
       locals_ok (data_state_locals X) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`; `A:(C,FFI)data_state`;
                 `res:((data_v list,data_v)result)option`; `X:(C,FFI)data_state`;
                 `ll:data_v spt`] evaluate_locals) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:data_v spt` (X_CHOOSE_THEN `sf1:bool`
    (X_CHOOSE_THEN `pk1:num` (X_CHOOSE_THEN `sm1:num option` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sm:num option`; `sf:bool`; `pk:num`] o
                MATCH_MP evaluate_smx_safe_peak_swap o
                check (fun th -> is_eq (concl th) &&
                         can (find_term ((=) `ll:data_v spt`)) (lhs (concl th)))) THEN
  REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS THEN
  DISCH_THEN(X_CHOOSE_THEN `sm2:num option` (X_CHOOSE_THEN `sf2:bool`
    (X_CHOOSE_THEN `pk2:num` SUBST1_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`w:data_v spt`; `sf2:bool`; `pk2:num`; `sm2:num option`] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS);;

let DATAPAUX_SPACE_cut_assign = prove
 (`!(l:data_v spt) names2 dest args v xs y.
     data_get_vars args l = SOME xs /\ data_cut_env names2 (insert dest v l) = SOME y ==>
     ?e1. data_cut_env (list_insert args (delete dest names2)) l = SOME e1 /\
          data_get_vars args e1 = SOME xs /\ locals_ok y (insert dest v e1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `domain (list_insert args (delete dest names2)) SUBSET domain (l:data_v spt)`
    (fun th -> REWRITE_TAC[th; option_INJ; UNWIND_THM1]) THENL
   [REWRITE_TAC[SUBSET; domain_list_insert; domain_delete; IN_DELETE] THEN
    X_GEN_TAC `z:num` THEN STRIP_TAC THENL
     [ASM_MESON_TAC[data_get_vars_IMP_domain];
      UNDISCH_TAC `domain (names2:num_set) SUBSET domain (insert dest (v:data_v) l)` THEN
      REWRITE_TAC[SUBSET; domain_insert; IN_INSERT] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `data_get_vars args (l:data_v spt) = SOME xs` THEN
    MATCH_MP_TAC(MESON[] `(a:(data_v list)option) = b ==> a = c ==> b = c`) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EVERY_get_vars THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_list_insert] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[lookup_mk_wf; lookup_inter_alt; domain_list_insert; locals_ok_def;
              lookup_insert; domain_delete; IN_DELETE] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `v':num = dest` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let DATAPAUX_SPACE_SEQ_ASSIGN_INR = prove
 (DATAPAUX_SPACE_SEQ_TM `data_Assign dest op args NONE`
    `data_Seq (MakeSpace (op_space_req op (LENGTH args) + k2)
                         (list_insert args (delete dest (names2:num_set))))
              (data_Seq (data_Assign dest op args NONE) c4)`
    (Some `space c2 = INR (k2,(names2:num_set),c4)`),
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ih2")) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `data_evaluate (data_Seq (data_Assign dest op args NONE) c2,s:(C,FFI)data_state) =
                res,s2` THEN
   CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[data_evaluate_def] THENC
                      REWRITE_CONV[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def;
                                   data_state_INFO.ri_accfupds; K_THM])) THEN
   CASE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `op_requires_names op` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   MP_TAC(ISPEC `data_get_vars args (data_state_locals (s:(C,FFI)data_state))` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `xs:data_v list` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   MP_TAC(ISPEC `data_do_app op xs (s:(C,FFI)data_state)` (cases "result")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `vy:data_v#(C,FFI)data_state` ASSUME_TAC)
     (X_CHOOSE_THEN `e:(data_v)error_result` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [ALL_TAC;
     DATAPAUX_SPACE_RES_TAC THEN
     FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP data_do_app_err) THEN FS[] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[op_requires_names_def]) THEN ASM_MESON_TAC[]]) THEN
  (MP_TAC(ISPEC `vy:data_v#(C,FFI)data_state` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `v:data_v` (X_CHOOSE_THEN `s':(C,FFI)data_state`
     SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[]) THEN
  (DISCH_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP data_do_app_const) THEN
   REMOVE_THEN "ih2" (MP_TAC o SPEC
     `data_set_var dest v (install_sfs op (s':(C,FFI)data_state))`) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC]) THEN
  (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (DISCH_THEN(MP_TAC o SPECL [`res:((data_v list,data_v)result)option`;
      `s2:(C,FFI)data_state`; `insert dest v (l:data_v spt)`]) THEN
   ASM_REWRITE_TAC[data_space_compile_def; pMakeSpace_def] THEN
   ANTS_TAC THENL
    [REWRITE_TAC[data_set_var_def; install_sfs_def; data_state_INFO.ri_accfupds; K_THM] THEN
     MATCH_MP_TAC locals_ok_insert THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   REWRITE_TAC[data_set_var_def; data_state_INFO.ri_fupdfupds; K_o_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `w2:data_v spt` (X_CHOOSE_THEN `sf2:bool`
     (X_CHOOSE_THEN `pk2:num` (X_CHOOSE_THEN `sm2:num option` STRIP_ASSUME_TAC))))) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term ((=) `c4:data_prog`)) (lhs (concl th)))) THEN
   REWRITE_TAC[data_evaluate_def; data_state_INFO.ri_accfupds; K_THM] THEN
   MP_TAC(ISPEC `data_cut_env names2 (insert dest v (l:data_v spt))` (cases "option")) THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:data_v spt` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
    [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[data_state_INFO.ri_fupdfupds; K_o_THM] THEN DISCH_TAC THEN
   SUBGOAL_THEN `data_get_vars args (l:data_v spt) = SOME xs` ASSUME_TAC THENL
    [MATCH_MP_TAC locals_ok_get_vars THEN
     EXISTS_TAC `data_state_locals (s:(C,FFI)data_state)` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`l:data_v spt`; `names2:num_set`; `dest:num`; `args:num list`; `v:data_v`;
                  `xs:data_v list`; `y:data_v spt`] DATAPAUX_SPACE_cut_assign) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `e1:data_v spt` STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[data_evaluate_def; IS_NONE_DEF; data_cut_state_opt_def] THEN
   ASM_REWRITE_TAC[data_state_INFO.ri_fupdfupds; K_o_THM; DATAPAUX_SPACE_add_space_locals;
                   data_state_INFO.ri_accfupds; K_THM] THEN
   CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[DATAPAUX_SPACE_add_space_locals; data_state_INFO.ri_accfupds; K_THM] THEN
   CASE_REWRITE_TAC[]) THEN
  (ABBREV_TAC `req = op_space_req op (LENGTH (args:num list))` THEN
   SUBGOAL_THEN `LENGTH (args:num list) = LENGTH (xs:data_v list)` ASSUME_TAC THENL
    [ASM_MESON_TAC[data_spaceProof_get_vars_IMP_LENGTH]; ALL_TAC] THEN
   ABBREV_TAC `T1 = add_space (data_state_locals_fupd (K e1) (s:(C,FFI)data_state)) (req + k2)` THEN
   SUBGOAL_THEN
     `T1 = data_state_locals_fupd (K e1)
             (data_state_stack_max_fupd (K (data_state_stack_max (s:(C,FFI)data_state)))
                (data_state_space_fupd (K (req + k2))
                   (data_state_safe_for_space_fupd (K (data_state_safe_for_space T1))
                      (data_state_peak_heap_length_fupd (K (data_state_peak_heap_length T1)) s))))`
     SUBST1_TAC THENL
    [EXPAND_TAC "T1" THEN
     REWRITE_TAC[add_space_def; data_state_component_equality; data_state_INFO.ri_accfupds;
                 K_THM];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`op:clos_op`; `xs:data_v list`; `s:(C,FFI)data_state`; `v:data_v`;
                  `s':(C,FFI)data_state`; `e1:data_v spt`; `req + k2:num`;
                  `data_state_stack_max (s:(C,FFI)data_state)`;
                  `data_state_safe_for_space (T1:(C,FFI)data_state)`;
                  `data_state_peak_heap_length (T1:(C,FFI)data_state)`]
                 DATAPAUX_SPACE_do_app_frame) THEN
   ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       UNDISCH_TAC `~op_requires_names op` THEN REWRITE_TAC[op_requires_names_def] THEN
       MESON_TAC[];
       UNDISCH_TAC `~op_requires_names op` THEN REWRITE_TAC[op_requires_names_def] THEN
       MESON_TAC[];
       EXPAND_TAC "req" THEN
       UNDISCH_TAC `LENGTH (args:num list) = LENGTH (xs:data_v list)` THEN
       DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `sf3:bool` (X_CHOOSE_THEN `pk3:num`
     (X_CHOOSE_THEN `sm3:num option` ASSUME_TAC))) THEN
   SUBGOAL_THEN `op_space_req op (LENGTH (xs:data_v list)) = req` SUBST_ALL_TAC THENL
    [EXPAND_TAC "req" THEN
     UNDISCH_TAC `LENGTH (args:num list) = LENGTH (xs:data_v list)` THEN
     DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[ADD_SUB2] THEN CASE_REWRITE_TAC[]) THEN
  (ABBREV_TAC `T2 = data_set_var dest v
      (install_sfs op
      (data_state_locals_fupd (K e1)
      (data_state_stack_max_fupd (K sm3)
      (data_state_space_fupd (K k2)
      (data_state_safe_for_space_fupd (K sf3)
      (data_state_peak_heap_length_fupd (K pk3) (s':(C,FFI)data_state)))))))` THEN
   ABBREV_TAC `A = add_space (data_state_locals_fupd (K y) (install_sfs op (s':(C,FFI)data_state))) k2` THEN
   SUBGOAL_THEN
     `T2 = data_state_locals_fupd (K (insert dest v e1))
             (data_state_stack_max_fupd (K sm3)
                (data_state_safe_for_space_fupd (K (data_state_safe_for_space T2))
                   (data_state_peak_heap_length_fupd (K pk3) (A:(C,FFI)data_state))))`
     SUBST1_TAC THENL
    [MAP_EVERY EXPAND_TAC ["T2"; "A"] THEN
     REWRITE_TAC[add_space_def; data_set_var_def; install_sfs_def;
                 data_state_component_equality; data_state_INFO.ri_accfupds; K_THM];
     ALL_TAC] THEN
   MP_TAC(ISPECL [`c4:data_prog`; `A:(C,FFI)data_state`;
     `res:((data_v list,data_v)result)option`;
     `if (res:((data_v list,data_v)result)option) = NONE
      then data_state_locals_fupd (K w2)
             (data_state_stack_max_fupd (K sm2)
                (data_state_safe_for_space_fupd (K sf2)
                   (data_state_peak_heap_length_fupd (K pk2) (s2:(C,FFI)data_state))))
      else data_state_stack_max_fupd (K sm2)
             (data_state_safe_for_space_fupd (K sf2)
                (data_state_peak_heap_length_fupd (K pk2) s2))`;
     `insert dest v (e1:data_v spt)`; `sm3:num option`;
     `data_state_safe_for_space (T2:(C,FFI)data_state)`; `pk3:num`]
     DATAPAUX_SPACE_eval_frame2) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN
     ASM_REWRITE_TAC[DATAPAUX_SPACE_add_space_locals; data_state_INFO.ri_accfupds; K_THM;
                     install_sfs_def];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `w3:data_v spt` (X_CHOOSE_THEN `sf4:bool`
     (X_CHOOSE_THEN `pk4:num` (X_CHOOSE_THEN `sm4:num option` STRIP_ASSUME_TAC)))) THEN
   ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC [`if (res:((data_v list,data_v)result)option) = NONE
                          then w3 else data_state_locals (s2:(C,FFI)data_state)`;
                         `sf4:bool`; `pk4:num`; `sm4:num option`] THEN
   ASM_CASES_TAC `res:((data_v list,data_v)result)option = NONE` THEN
   ASM_REWRITE_TAC (locals_ok_refl :: DATAPAUX_SPACE_FUPD_RWS) THEN
   UNDISCH_TAC `locals_ok (data_state_locals (if (res:((data_v list,data_v)result)option) = NONE
     then data_state_locals_fupd (K w2)
            (data_state_stack_max_fupd (K sm2)
               (data_state_safe_for_space_fupd (K sf2)
                  (data_state_peak_heap_length_fupd (K pk2) (s2:(C,FFI)data_state))))
     else data_state_stack_max_fupd (K sm2)
            (data_state_safe_for_space_fupd (K sf2)
               (data_state_peak_heap_length_fupd (K pk2) s2)))) w3` THEN
   ASM_REWRITE_TAC DATAPAUX_SPACE_FUPD_RWS THEN
   ASM_MESON_TAC[DATAPAUX_SPACE_locals_ok_trans]));;

let DATAPAUX_SPACE_SEQ_TERM w =
  find_term (fun t -> try fst(dest_const(rator t)) = "data_space_compile" &&
                          (try fst(dest_const(fst(strip_comb(rand t)))) = "data_Seq"
                           with Failure _ -> false)
                      with Failure _ -> false) w;;

let DATAPAUX_SPACE_PROG_TAC (mkprog:term->term->term) : tactic = fun (asl,w as g) ->
  let t = DATAPAUX_SPACE_SEQ_TERM w in
  let c1,c2 = match snd(strip_comb(rand t)) with [a;b] -> a,b | _ -> failwith "PROG" in
  (SUBGOAL_THEN (mk_eq(t,mkprog c1 c2)) SUBST1_TAC THENL
    [REWRITE_TAC[data_space_compile_def; space_def; LET_DEF; LET_END_DEF] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[pMakeSpace_def] THEN
     ASM_REWRITE_TAC[pMakeSpace_def];
     ALL_TAC]) g;;

let DATAPAUX_SPACE_USE_TAC (lem:thm) : tactic =
  FIRST_ASSUM(fun ih -> MATCH_ACCEPT_TAC (MATCH_MP lem ih)) ORELSE
  FIRST_ASSUM(fun sp -> FIRST_ASSUM(fun ih ->
    MATCH_ACCEPT_TAC (MATCH_MP (MATCH_MP (GEN_ALL lem) sp) ih)));;

let DATAPAUX_SPACE_dsc = `data_space_compile`;;
let DATAPAUX_SPACE_GEN_CASE_TAC =
  DATAPAUX_SPACE_PROG_TAC (fun c1 c2 -> mk_comb(mk_comb(`data_Seq`, mk_comb(DATAPAUX_SPACE_dsc,c1)), mk_comb(DATAPAUX_SPACE_dsc,c2))) THEN
  DATAPAUX_SPACE_USE_TAC DATAPAUX_SPACE_SEQ_GEN;;
let DATAPAUX_SPACE_SKIP_CASE_TAC =
  DATAPAUX_SPACE_PROG_TAC (fun c1 c2 -> mk_comb(DATAPAUX_SPACE_dsc,c2)) THEN
  DATAPAUX_SPACE_USE_TAC DATAPAUX_SPACE_SEQ_SKIP;;
let DATAPAUX_SPACE_MS_CASE_TAC =
  DATAPAUX_SPACE_PROG_TAC (fun c1 c2 -> mk_comb(mk_comb(`data_Seq`, c1), mk_comb(DATAPAUX_SPACE_dsc,c2))) THEN
  DATAPAUX_SPACE_USE_TAC DATAPAUX_SPACE_SEQ_MAKESPACE;;


let DATAPAUX_SPACE_MS_INR_CASE_TAC =
  DATAPAUX_SPACE_PROG_TAC (fun c1 c2 ->
    let k1,n1 = match snd(strip_comb c1) with [a;b] -> a,b | _ -> failwith "MS" in
    let _ = k1 in
    mk_comb(mk_comb(`data_Seq`,
      mk_comb(mk_comb(`MakeSpace`,`k2:num`),
              mk_comb(mk_comb(`inter:num_set->num_set->num_set`,n1),`names2:num_set`))),
      `c4:data_prog`)) THEN
  DATAPAUX_SPACE_USE_TAC DATAPAUX_SPACE_SEQ_MS_INR;;
let DATAPAUX_SPACE_MOVE_INR_CASE_TAC =
  DATAPAUX_SPACE_PROG_TAC (fun c1 c2 ->
    let dest,src = match snd(strip_comb c1) with [a;b] -> a,b | _ -> failwith "MV" in
    mk_comb(mk_comb(`data_Seq`,
      mk_comb(mk_comb(`MakeSpace`,`k2:num`),
        list_mk_comb(`insert:num->1->num_set->num_set`,
          [src; `one`; mk_comb(mk_comb(`delete:num->num_set->num_set`,dest),`names2:num_set`)]))),
      mk_comb(mk_comb(`data_Seq`,c1),`c4:data_prog`))) THEN
  DATAPAUX_SPACE_USE_TAC DATAPAUX_SPACE_SEQ_MOVE_INR;;
let DATAPAUX_SPACE_ASSIGN_INR_CASE_TAC =
  DATAPAUX_SPACE_PROG_TAC (fun c1 c2 ->
    let dest,op,args = match snd(strip_comb c1) with [a;b;c;_] -> a,b,c | _ -> failwith "AS" in
    mk_comb(mk_comb(`data_Seq`,
      mk_comb(mk_comb(`MakeSpace`,
        mk_binop `(+):num->num->num` (mk_comb(mk_comb(`op_space_req`,op),mk_comb(`LENGTH:num list->num`,args)))
                 `k2:num`),
        mk_comb(mk_comb(`list_insert`,args),
          mk_comb(mk_comb(`delete:num->num_set->num_set`,dest),`names2:num_set`)))),
      mk_comb(mk_comb(`data_Seq`,c1),`c4:data_prog`))) THEN
  DATAPAUX_SPACE_USE_TAC DATAPAUX_SPACE_SEQ_ASSIGN_INR;;


(* HOL4: evaluate_compile[Seq] *)
let DATAPAUX_SPACE_SEQ = prove
 (el 7 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `space c2` (cases "sum")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `c4:data_prog` ASSUME_TAC)
    (X_CHOOSE_THEN `kc:num#num_set#data_prog` ASSUME_TAC)) THENL
   [CASES_ON `c1:data_prog` THENL
     [DATAPAUX_SPACE_SKIP_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_GEN_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_GEN_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_MS_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_GEN_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_GEN_CASE_TAC];
    MP_TAC(ISPEC `kc:num#num_set#data_prog` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `kc2:num_set#data_prog` SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `kc2:num_set#data_prog` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `names2:num_set` (X_CHOOSE_THEN `c4:data_prog` SUBST_ALL_TAC)) THEN
    CASES_ON `c1:data_prog` THENL
     [DATAPAUX_SPACE_SKIP_CASE_TAC; DATAPAUX_SPACE_MOVE_INR_CASE_TAC;
      DATAPAUX_SPACE_GEN_CASE_TAC;
      CASES_ON `a3:num_set option` THENL
       [DATAPAUX_SPACE_ASSIGN_INR_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC];
      DATAPAUX_SPACE_GEN_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_MS_INR_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_GEN_CASE_TAC; DATAPAUX_SPACE_GEN_CASE_TAC;
      DATAPAUX_SPACE_GEN_CASE_TAC]]);;

(* HOL4: evaluate_compile[If] *)
let DATAPAUX_SPACE_IF = prove
 (el 8 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   REWRITE_TAC[GSYM data_space_compile_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN
   TOP_CASE_TAC THENL [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP locals_ok_get_var (CONJ th th2)])) THEN
   CASE_REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
    [DISCH_TAC THEN REMOVE_THEN "ih1" (MP_TAC o SPEC `a:data_v`) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   COND_CASES_TAC THENL
    [DISCH_TAC THEN REMOVE_THEN "ih2" (MP_TAC o SPEC `a:data_v`) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   DATAPAUX_SPACE_RES_TAC THEN FS[]);;

let DATAPAUX_SPACE_call_env_locals = prove
 (`!args ss (s:(C,FFI)data_state) l.
     data_call_env args ss (data_dec_clock (data_state_locals_fupd (K l) s)) =
     data_call_env args ss (data_dec_clock s)`,
  REWRITE_TAC[data_call_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

let DATAPAUX_SPACE_call_push_locals = prove
 (`!args ss env b (s:(C,FFI)data_state) l.
     data_call_env args ss (data_push_env env b (data_dec_clock (data_state_locals_fupd (K l) s))) =
     data_call_env args ss (data_push_env env b (data_dec_clock s))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_call_env_def; data_push_env_def; data_dec_clock_def; LET_DEF; LET_END_DEF;
              data_state_component_equality; data_state_INFO.ri_accfupds; K_THM]);;

(* split the cases of the evaluation of the source program (the           *)
(* antecedent of the goal), rewriting cut_env on the locals l after each  *)
(* split; then finish each leaf                                           *)
let DATAPAUX_SPACE_ANT_CASE_TAC : tactic = fun (asl,w as g) ->
  let a = lhand w in
  let x = first_case_scrutinee a a in
  (CASES_ON x THEN CASE_TIDY_TAC) g;;

let DATAPAUX_SPACE_LEAF_TAC (thl:thm list) : tactic =
  (DATAPAUX_SPACE_RES_TAC THEN TRY (FS[] THEN NO_TAC) THEN DATAPAUX_SPACE_WIT_TAC None thl)
  ORELSE (DISCH_THEN SUBST1_TAC THEN DATAPAUX_SPACE_WIT_TAC None thl);;

let DATAPAUX_SPACE_SPLIT_TAC (thl:thm list) : tactic =
  REPEAT (DATAPAUX_SPACE_ANT_CASE_TAC THEN
          TRY (FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
                 REWRITE_TAC[MATCH_MP locals_ok_cut_env (CONJ th th2)]))) THEN
          CASE_REWRITE_TAC[]) THEN
  DATAPAUX_SPACE_LEAF_TAC thl;;

(* HOL4: evaluate_compile[Force]; the called code is not compiled here  *)
let DATAPAUX_SPACE_FORCE = prove
 (el 9 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; DATAPAUX_SPACE_call_env_locals;
               DATAPAUX_SPACE_call_push_locals; data_state_INFO.ri_fupdfupds; K_o_THM] THEN
   TOP_CASE_TAC THENL [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP locals_ok_get_var (CONJ th th2)])) THEN
   CASE_REWRITE_TAC[] THEN
  DATAPAUX_SPACE_SPLIT_TAC [data_flush_state_def; data_set_var_def]);;

(* HOL4: evaluate_compile[Call]; the called code is not compiled here *)
let DATAPAUX_SPACE_CALL = prove
 (el 10 DATAPAUX_SPACE_CASES,
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[data_space_compile_def; space_def; pMakeSpace_def; data_evaluate_def] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM; DATAPAUX_SPACE_call_env_locals;
               DATAPAUX_SPACE_call_push_locals; data_state_INFO.ri_fupdfupds; K_o_THM] THEN
   TOP_CASE_TAC THENL [DATAPAUX_SPACE_RES_TAC THEN FS[]; ALL_TAC] THEN
   FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
     REWRITE_TAC[MATCH_MP locals_ok_get_vars (CONJ th th2)])) THEN
   CASE_REWRITE_TAC[] THEN
   DATAPAUX_SPACE_SPLIT_TAC [data_flush_state_def; data_set_var_def]);;

(* HOL4: evaluate_compile [local] (Finalise of the cases above; HOL4's     *)
(* unused bound variable vars is kept)                                     *)
let data_spaceProof_evaluate_compile = prove
 (`!c (s:(C,FFI)data_state) res s2 (vars:A) l.
     ~(res = SOME (Rerr (Rabort Rtype_error))) /\ data_evaluate (c,s) = (res,s2) /\
     locals_ok (data_state_locals s) l ==>
     ?w safe peak smx.
       data_evaluate (data_space_compile c,data_state_locals_fupd (K l) s) =
       (res,if res = NONE
            then data_state_locals_fupd (K w)
                   (data_state_stack_max_fupd (K smx)
                      (data_state_safe_for_space_fupd (K safe)
                         (data_state_peak_heap_length_fupd (K peak) s2)))
            else data_state_stack_max_fupd (K smx)
                   (data_state_safe_for_space_fupd (K safe)
                      (data_state_peak_heap_length_fupd (K peak) s2))) /\
       locals_ok (data_state_locals s2) w`,
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[FORALL_PAIR_THM; FST; SND]
       (MP DATAPAUX_SPACE_IND
          (end_itlist CONJ
             [DATAPAUX_SPACE_SKIP; DATAPAUX_SPACE_MOVE; DATAPAUX_SPACE_ASSIGN;
              DATAPAUX_SPACE_TICK; DATAPAUX_SPACE_MAKESPACE; DATAPAUX_SPACE_RAISE;
              DATAPAUX_SPACE_RETURN; DATAPAUX_SPACE_SEQ; DATAPAUX_SPACE_IF;
              DATAPAUX_SPACE_FORCE; DATAPAUX_SPACE_CALL]))));;

let data_spaceProof_compile_correct = prove
 (`!c (s:(C,FFI)data_state).
     ~(FST (data_evaluate (c,s)) = NONE) /\
     ~(FST (data_evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error))) ==>
     ?safe peak smx.
       data_evaluate (data_space_compile c,s) =
       (I ## (\s. data_state_stack_max_fupd (K smx)
                    (data_state_safe_for_space_fupd (K safe)
                       (data_state_peak_heap_length_fupd (K peak) s))))
       (data_evaluate (c,s))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s2:(C,FFI)data_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; PAIR_MAP_THM; I_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_prog`; `s:(C,FFI)data_state`;
                 `res:((data_v list,data_v)result)option`; `s2:(C,FFI)data_state`;
                 `one`; `data_state_locals (s:(C,FFI)data_state)`]
                data_spaceProof_evaluate_compile) THEN
  ASM_REWRITE_TAC[locals_ok_refl; data_with_same_locals] THEN MESON_TAC[]);;

let DATAPAUX_SPACE_labels_pMakeSpace = prove
 (`!c. (!y. space c = INL y ==> data_get_code_labels y = data_get_code_labels c) /\
       (!y0 y1 y2. space c = INR (y0,y1,y2) ==>
                   data_get_code_labels y2 = data_get_code_labels c) ==>
       data_get_code_labels (pMakeSpace (space c)) = data_get_code_labels c`,
  GEN_TAC THEN
  MP_TAC(ISPEC `space c` (cases "sum")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `y:data_prog` SUBST1_TAC)
    (X_CHOOSE_THEN `kc:num#num_set#data_prog` SUBST1_TAC)) THEN
  REWRITE_TAC[pMakeSpace_def] THENL [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `kc:num#num_set#data_prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `kc2:num_set#data_prog` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `kc2:num_set#data_prog` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num_set` (X_CHOOSE_THEN `y:data_prog` SUBST1_TAC)) THEN
  REWRITE_TAC[pMakeSpace_def; data_get_code_labels_def; UNION_EMPTY;
              distinctness "sum"; injectivity "sum"; PAIR_EQ] THEN
  MESON_TAC[]);;

let DATAPAUX_SPACE_LABELS_SIMPLE_TAC : tactic =
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[data_get_code_labels_def];;

let DATAPAUX_SPACE_LABELS_SEQ_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  SUBGOAL_THEN `data_get_code_labels (pMakeSpace (space c1)) = data_get_code_labels c1`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DATAPAUX_SPACE_labels_pMakeSpace THEN USE_THEN "ih1" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `data_get_code_labels (pMakeSpace (space c2)) = data_get_code_labels c2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DATAPAUX_SPACE_labels_pMakeSpace THEN USE_THEN "ih2" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `space c2` (cases "sum")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `c4:data_prog` ASSUME_TAC)
    (X_CHOOSE_THEN `kc:num#num_set#data_prog` ASSUME_TAC)) THENL
   [SUBGOAL_THEN `data_get_code_labels c4 = data_get_code_labels c2` ASSUME_TAC THENL
     [USE_THEN "ih2" (fun th -> ASM_MESON_TAC[th]); ALL_TAC];
    MP_TAC(ISPEC `kc:num#num_set#data_prog` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `kc2:num_set#data_prog` SUBST_ALL_TAC)) THEN
    MP_TAC(ISPEC `kc2:num_set#data_prog` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `names2:num_set` (X_CHOOSE_THEN `c4:data_prog` SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `data_get_code_labels c4 = data_get_code_labels c2` ASSUME_TAC THENL
     [USE_THEN "ih2" (fun th -> ASM_MESON_TAC[th]); ALL_TAC]] THEN
  REMOVE_THEN "ih1" (K ALL_TAC) THEN REMOVE_THEN "ih2" (K ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `c1:data_prog` THEN CASE_REWRITE_TAC[] THEN
  TRY (CASES_ON `a3:num_set option` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[distinctness "sum"; injectivity "sum"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pMakeSpace_def]) THEN
  ASM_REWRITE_TAC[data_get_code_labels_def; pMakeSpace_def; UNION_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_get_code_labels_def; pMakeSpace_def; UNION_EMPTY]) THEN
  ASM_REWRITE_TAC[] THEN TRY (ASM SET_TAC[]);;

let DATAPAUX_SPACE_LABELS_IF_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_get_code_labels_def] THEN BINOP_TAC THEN
  MATCH_MP_TAC DATAPAUX_SPACE_labels_pMakeSpace THENL
   [USE_THEN "ih1" (fun th -> MESON_TAC[th]); USE_THEN "ih2" (fun th -> MESON_TAC[th])];;

let get_code_labels_space = prove
 (`!x y y0 y1 y2.
     (space x = INL y ==> data_get_code_labels y = data_get_code_labels x) /\
     (space x = INR (y0,y1,y2) ==> data_get_code_labels y2 = data_get_code_labels x)`,
  MATCH_MP_TAC space_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[space_def; distinctness "sum"; injectivity "sum"; PAIR_EQ] THEN
  REWRITE_TAC[data_get_code_labels_def] THENL
   [DATAPAUX_SPACE_LABELS_SIMPLE_TAC; DATAPAUX_SPACE_LABELS_SEQ_TAC;
    DATAPAUX_SPACE_LABELS_IF_TAC; DATAPAUX_SPACE_LABELS_SIMPLE_TAC;
    DATAPAUX_SPACE_LABELS_SIMPLE_TAC; DATAPAUX_SPACE_LABELS_SIMPLE_TAC;
    DATAPAUX_SPACE_LABELS_SIMPLE_TAC; DATAPAUX_SPACE_LABELS_SIMPLE_TAC;
    DATAPAUX_SPACE_LABELS_SIMPLE_TAC; DATAPAUX_SPACE_LABELS_SIMPLE_TAC;
    DATAPAUX_SPACE_LABELS_SIMPLE_TAC]);;

(* HOL4 [simp] *)
let data_spaceProof_get_code_labels_compile = prove
 (`!x. data_get_code_labels (data_space_compile x) = data_get_code_labels x`,
  GEN_TAC THEN REWRITE_TAC[data_space_compile_def] THEN
  MATCH_MP_TAC DATAPAUX_SPACE_labels_pMakeSpace THEN MESON_TAC[get_code_labels_space]);;
cake_add_simps [data_spaceProof_get_code_labels_compile];;
