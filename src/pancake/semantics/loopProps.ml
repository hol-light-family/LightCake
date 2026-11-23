(* ========================================================================= *)
(* loopProps: port of HOL4 pancake/semantics/loopPropsScript.sml             *)
(* (CakeML v3479).                                                           *)
(* Properties of loopLang and loopSem.                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says (loop_unassigned_vars_evaluate_same,         *)
(*   loop_eval_upd_clock_eq, loop_evaluate_add_clock_eq,                     *)
(*   loop_evaluate_io_events_mono, loop_evaluate_add_clock_io_events_mono;   *)
(*   the other theorems keep their HOL4 names).                              *)
(* - HOL4 ZIP (xs,ys) is ZIP xs ys (HOL Light's ZIP has the length of its    *)
(*   first list; see the DEVIATIONS in the theorems that use it); s.f is     *)
(*   loop_state_f s; s with f := v is loop_state_f_fupd (K v) s; isPREFIX    *)
(*   (the HOL4 infix <<=) is isPREFIX.                                       *)
(* - Local helpers that are not HOL4 theorems are PLOOPAUX_.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/pan_common.ml";;
needs "pancake/semantics/pan_commonProps.ml";;
needs "pancake/semantics/loopSem.ml";;

prioritize_num();;
type_invention_error := true;;

let every_prog_def = cake_def
  `(every_prog p (loop_Seq p1 p2:(A)loop_prog) <=>
      p (loop_Seq p1 p2) /\ every_prog p p1 /\ every_prog p p2) /\
   (every_prog p (loop_Loop l1 body l2) <=>
      p (loop_Loop l1 body l2) /\ every_prog p body) /\
   (every_prog p (loop_If x1 x2 x3 p1 p2 l1) <=>
      p (loop_If x1 x2 x3 p1 p2 l1) /\ every_prog p p1 /\ every_prog p p2) /\
   (every_prog p (Mark p1) <=>
      p (Mark p1) /\ every_prog p p1) /\
   (every_prog p (loop_Call ret dest args handler) <=>
      p (loop_Call ret dest args handler) /\
      (match handler with
         SOME (n,q,r,l) -> every_prog p q /\ every_prog p r
       | NONE -> T)) /\
   (every_prog p prog <=> p prog)`;;

let survives_def = cake_def
  `(survives n (loop_If c r ri p q cs:(A)loop_prog) <=>
      survives n p /\ survives n q /\ n IN domain cs) /\
   (survives n (loop_Loop il p ol) <=>
      n IN domain il /\ n IN domain ol /\ survives n p) /\
   (survives n (loop_Call (SOME (m,cs)) trgt args NONE) <=>
      n IN domain cs) /\
   (survives n (loop_Call (SOME (m,cs)) trgt args (SOME (r,p,q,ps))) <=>
      n IN domain cs /\ n IN domain ps /\ survives n p /\ survives n q) /\
   (survives n (loop_FFI fi ptr1 len1 ptr2 len2 cs) <=> n IN domain cs) /\
   (survives n (Mark p) <=> survives n p) /\
   (survives n (loop_Seq p q) <=> survives n p /\ survives n q) /\
   (survives n p <=> T)`;;

let cut_sets_def = cake_def
  `(cut_sets (l:num_set) (loop_Skip:(A)loop_prog) = l) /\
   (cut_sets l (LocValue n m) = insert n one l) /\
   (cut_sets l (loop_Assign n e) = insert n one l) /\
   (cut_sets l (loop_Load32 n m) = insert m one l) /\
   (cut_sets l (loop_LoadByte n m) = insert m one l) /\
   (cut_sets l (loop_Seq p q) = cut_sets (cut_sets l p) q) /\
   (cut_sets l (loop_If _ _ _ p q nl) = nl) /\
   (cut_sets l (loop_Arith arith) =
      match arith with
        LLongDiv r1 r2 _ _ _ -> insert r1 one (insert r2 one l)
      | LLongMul r1 r2 _ _ -> insert r1 one (insert r2 one l)
      | LDiv r1 _ _ -> insert r1 one l) /\
   (cut_sets l _ = l)`;;

let comp_syntax_ok_def = cake_def
  `(comp_syntax_ok (l:num_set) (loop_Skip:(A)loop_prog) <=> T) /\
   (comp_syntax_ok l (loop_Assign n e) <=> T) /\
   (comp_syntax_ok l (loop_Loop lin p lout) <=>
      l = lin /\ l = lout /\ comp_syntax_ok lin p) /\
   (comp_syntax_ok l (loop_Arith arith) <=> T) /\
   (comp_syntax_ok l (loop_Break _) <=> T) /\
   (comp_syntax_ok l (LocValue n m) <=> T) /\
   (comp_syntax_ok l (loop_Load32 n m) <=> T) /\
   (comp_syntax_ok l (loop_LoadByte n m) <=> T) /\
   (comp_syntax_ok l (loop_Seq p q) <=>
      comp_syntax_ok l p /\ comp_syntax_ok (cut_sets l p) q) /\
   (comp_syntax_ok l (loop_If c n r p q nl) <=>
      comp_syntax_ok l p /\ comp_syntax_ok l q /\
      ?ns. nl = FOLDL (\sp n. insert n one sp) l ns) /\
   (comp_syntax_ok _ _ <=> F)`;;

let evaluate_tail_calls_eqs = prove
 (`!f (t:(A,FFI)loop_state) lc x.
     find_code (SOME f) ([]:((A)word_loc)list) (loop_state_code t) = SOME x ==>
     loop_evaluate (loop_Call NONE (SOME f) [] NONE:(A)loop_prog, t) =
     loop_evaluate (loop_Call NONE (SOME f) [] NONE, loop_state_locals_fupd (K lc) t)`,
  REPEAT STRIP_TAC THEN FS[loop_evaluate_def; get_vars_def] THEN
  TOP_CASE_TAC THEN SIMP[loop_dec_clock_def]);;

(* acc_vars_acc: the induction is on acc_vars_ind with a predicate that     *)
(* ignores the accumulator; the induction hypotheses are used once per      *)
(* argument (as rewrites they would loop)                                   *)

let PLOOPAUX_ACC_EASY_TAC =
  REWRITE_TAC[acc_vars_def; option_CASE; pair_CASE_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INSERT; NOT_IN_EMPTY; domain_insert;
              domain_list_insert; domain_def] THEN
  MESON_TAC[];;

let PLOOPAUX_acc_vars_call = prove
 (`!ret dest args (handler:(num#(A)loop_prog#(A)loop_prog#num_set)option).
     (!live l1 p1 p2 n vs. ret = SOME (vs,live) /\ handler = SOME (n,p1,p2,l1)
        ==> !l. domain (acc_vars p1 l) = domain (acc_vars p1 LN) UNION domain l) /\
     (!live p1 l1 p2 n vs. ret = SOME (vs,live) /\ handler = SOME (n,p1,p2,l1)
        ==> !l. domain (acc_vars p2 l) = domain (acc_vars p2 LN) UNION domain l)
     ==> !l. domain (acc_vars (loop_Call ret dest args handler) l) =
             domain (acc_vars (loop_Call ret dest args handler) LN) UNION domain l`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `r0:num list#num_set` SUBST1_TAC)
    (ISPEC `ret:(num list#num_set)option` (cases "option")) THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `h0:num#(A)loop_prog#(A)loop_prog#num_set` SUBST1_TAC)
    (ISPEC `handler:(num#(A)loop_prog#(A)loop_prog#num_set)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
  [PLOOPAUX_ACC_EASY_TAC; PLOOPAUX_ACC_EASY_TAC; PLOOPAUX_ACC_EASY_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o REWRITE_RULE[PAIR] o
     SPECL [`SND (r0:num list#num_set)`;
            `SND(SND(SND (h0:num#(A)loop_prog#(A)loop_prog#num_set)))`;
            `FST(SND (h0:num#(A)loop_prog#(A)loop_prog#num_set))`;
            `FST(SND(SND (h0:num#(A)loop_prog#(A)loop_prog#num_set)))`;
            `FST (h0:num#(A)loop_prog#(A)loop_prog#num_set)`;
            `FST (r0:num list#num_set)`])
    (MP_TAC o REWRITE_RULE[PAIR] o
     SPECL [`SND (r0:num list#num_set)`;
            `FST(SND (h0:num#(A)loop_prog#(A)loop_prog#num_set))`;
            `SND(SND(SND (h0:num#(A)loop_prog#(A)loop_prog#num_set)))`;
            `FST(SND(SND (h0:num#(A)loop_prog#(A)loop_prog#num_set)))`;
            `FST (h0:num#(A)loop_prog#(A)loop_prog#num_set)`;
            `FST (r0:num list#num_set)`])) THEN
  REPEAT DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[acc_vars_def; option_CASE; pair_CASE_def; LET_DEF; LET_END_DEF] THEN
  ONCE_ASM_REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INSERT; NOT_IN_EMPTY; domain_insert;
              domain_list_insert; domain_def] THEN
  MESON_TAC[]);;

let acc_vars_acc = prove
 (`!p (l:num_set). domain (acc_vars (p:(A)loop_prog) l) =
                   domain (acc_vars p LN) UNION domain l`,
  SUFF_TAC `!(p:(A)loop_prog) (l0:num_set) (l:num_set).
              domain (acc_vars p l) = domain (acc_vars p LN) UNION domain l`
  THENL [MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC acc_vars_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     if can (find_term (fun t -> try fst(dest_const t) = "loop_Call"
                                 with Failure _ -> false)) w then
       (MATCH_ACCEPT_TAC PLOOPAUX_acc_vars_call) g
     else if is_imp w then
       (STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[acc_vars_def] THEN
        ONCE_ASM_REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[domain_def; UNION_EMPTY] THEN SET_TAC[]) g
     else
       (REPEAT GEN_TAC THEN REWRITE_TAC[acc_vars_def] THEN REPEAT TOP_CASE_TAC THEN
        PLOOPAUX_ACC_EASY_TAC) g));;

let evaluate_Loop_body_same = prove
 (`(!(s:(A,B)loop_state). loop_evaluate (body,s) = loop_evaluate (body',s)) ==>
   !(s:(A,B)loop_state). loop_evaluate (loop_Loop l1 body l2,s) =
                         loop_evaluate (loop_Loop l1 body' l2,s)`,
  DISCH_TAC THEN
  SUBGOAL_THEN `!n (s:(A,B)loop_state). loop_state_clock s < n ==>
       loop_evaluate (loop_Loop l1 body l2,s) = loop_evaluate (loop_Loop l1 body' l2,s)`
    (fun th -> MESON_TAC[th; ARITH_RULE `n < SUC n`]) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT] THEN REPEAT STRIP_TAC THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP loop_evaluate_clock) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PLOOPAUX_cut_res_clock) THEN
  REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tools for the proofs by induction on the semantics (loop_evaluate_ind):   *)
(* the evaluate assumption is unfolded once and its cases split, the         *)
(* induction hypotheses are instantiated at the evaluate assumptions (as in  *)
(* loopSem's clock proof, trying every evaluate antecedent of a hypothesis,  *)
(* and finishing the other antecedents with fin), and the results of         *)
(* cut_res and loop_sh_mem_op are characterised.                             *)
(* ------------------------------------------------------------------------- *)

let PLOOPAUX_IHS_TAC (fin:tactic) : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PLOOPAUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists PLOOPAUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  (* the hypotheses of assumptions too: after a substitution an assumption  *)
  (* can have one, and a bound variable named like a variable of it would   *)
  (* make GENL fail                                                          *)
  let avoid = freesl (w :: map (concl o snd) asl @ flat (map (hyp o snd) asl)) in
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
    let ihi = INST tmi (SPEC_ALL ih) in
    let a,c = dest_imp (concl ihi) in
    let rest = filter (fun v -> mem v vs) (subtract (frees a) (frees c)) in
    if exists (fun v -> mem v vs) (frees c) then failwith "" else
    c, GENL rest ihi in
  let insts = flat (map (fun e ->
      flat (map (fun ih ->
          let _,bod = strip_forall (concl ih) in
          let cjs = filter PLOOPAUX_is_eval_eq (conjuncts(fst(dest_imp bod))) in
          mapfilter (fun cj -> inst_of ih e cj) cjs) ihs)) evs) in
  MAP_EVERY (fun (c,th) ->
      TRY (SUBGOAL_THEN c ASSUME_TAC THENL
            [MATCH_MP_TAC th THEN IL2AUX_EXISTS_ASM_TAC THEN fin THEN NO_TAC;
             ALL_TAC]))
    insts g;;

(* the evaluate assumption: unfold it once and split its cases *)

let PLOOPAUX_EVAL_CASES_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (PLOOPAUX_is_eval_eq o concl)) THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[loop_evaluate_def] THENC
           REWRITE_CONV(PLOOPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]))) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN RVEQ_TAC;;

let PLOOPAUX_cut_res_res = prove
 (`!live r (s:(A,FFI)loop_state) res t.
     cut_res (live:(B)spt) (r:((W)loop_result)option,s) = (res,t)
     ==> res = r \/ res = SOME loop_Error \/ res = SOME loop_TimeOut`,
  REWRITE_TAC[cut_res_def] THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let PLOOPAUX_sh_mem_op_res = prove
 (`!op r ad (s:(A,FFI)loop_state) res t.
     loop_sh_mem_op op r ad s = (res:((W)loop_result)option,t)
     ==> res = NONE \/ res = SOME loop_Error \/ ?e. res = SOME (loop_FinalFFI e)`,
  MATCH_MP_TAC memop_INDUCT THEN
  REWRITE_TAC[loop_sh_mem_op_def; loop_sh_mem_load_def; loop_sh_mem_store_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let PLOOPAUX_exit_loop_id = prove
 (`!r. (!n. ~(r = SOME (loopSem_Break n))) /\ (!n. ~(r = SOME (loopSem_Continue n)))
       ==> loop_exit_loop (r:((W)loop_result)option) = r`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((W)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[loop_exit_loop_def] THEN
  STRUCT_CASES_TAC (ISPEC `a:(W)loop_result` (cases "loop_result")) THEN
  REWRITE_TAC[loop_exit_loop_def; option_INJ; injectivity "loop_result";
              distinctness "loop_result"] THEN MESON_TAC[]);;

let PLOOPAUX_prog_distinct = distinctness "loop_prog";;

let PLOOPAUX_result_rws =
  [option_DISTINCT; option_INJ; distinctness "loop_result"; injectivity "loop_result"];;

let PLOOPAUX_NOBC_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PLOOPAUX_prog_distinct; injectivity "loop_prog";
                              option_CASE; pair_CASE] o
                 BETA_RULE o REWRITE_RULE[every_prog_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN
  PLOOPAUX_IHS_TAC (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PLOOPAUX_cut_res_res)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PLOOPAUX_sh_mem_op_res)) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_SIMP_TAC(PLOOPAUX_exit_loop_id :: PLOOPAUX_result_rws);;

let evaluate_no_Break_Continue = prove
 (`!prog (s:(A,FFI)loop_state) res t.
     loop_evaluate (prog, s) = (res,t) /\
     every_prog (\r. (!n. ~(r = loop_Break n)) /\ (!n. ~(r = loop_Continue n))) prog
     ==> (!n. ~(res = SOME (loopSem_Break n))) /\
         (!n. ~(res = SOME (loopSem_Continue n)))`,
  REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN PLOOPAUX_NOBC_TAC);;

let locals_touched_eq_eval_eq = prove
 (`!(s:(A,FFI)loop_state) e (t:(A,FFI)loop_state).
     loop_state_globals s = loop_state_globals t /\
     loop_state_memory s = loop_state_memory t /\
     loop_state_mdomain s = loop_state_mdomain t /\
     loop_state_base_addr s = loop_state_base_addr t /\
     loop_state_top_addr s = loop_state_top_addr t /\
     (!n. MEM n (locals_touched e)
          ==> lookup n (loop_state_locals s) = lookup n (loop_state_locals t))
     ==> loop_eval t e = loop_eval s e`,
  MATCH_MP_TAC loop_eval_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[loop_eval_def; locals_touched_def; MEM; MEM_APPEND; loop_mem_load_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
  [ASM_MESON_TAC[];
   SUBGOAL_THEN
     `loop_eval (t:(A,FFI)loop_state) addr = loop_eval (s:(A,FFI)loop_state) addr`
     SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]];
   SUBGOAL_THEN `MAP (loop_eval (t:(A,FFI)loop_state)) wexps =
                 MAP (loop_eval (s:(A,FFI)loop_state)) (wexps:((A)loop_exp)list)`
     SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
   MATCH_MP_TAC MAP_CONG THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:(A)loop_exp`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN
   EXISTS_TAC `locals_touched (x:(A)loop_exp)` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `x:(A)loop_exp` THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `loop_eval (t:(A,FFI)loop_state) wexp1 = loop_eval (s:(A,FFI)loop_state) wexp1 /\
      loop_eval t wexp2 = loop_eval s wexp2`
     (fun th -> REWRITE_TAC[th]) THEN
   CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[]]);;

let loop_eval_nested_assign_distinct_eq = prove
 (`!es ns (t:(A,FFI)loop_state) ev.
     MAP (loop_eval t) es = MAP SOME ev /\
     distinct_lists ns (FLAT (MAP locals_touched es)) /\
     ALL_DISTINCT ns /\
     LENGTH ns = LENGTH es ==>
     loop_evaluate (loop_nested_seq (MAP2 loop_Assign ns es),t) =
     (NONE, loop_state_locals_fupd (K (alist_insert ns ev (loop_state_locals t))) t)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
  [DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `ns0:num list`
     SUBST1_TAC)) (ISPEC `ns:num list` list_CASES) THEN
   REWRITE_TAC[LENGTH; NOT_SUC; MAP; MAP2; loop_nested_seq_def] THEN
   STRUCT_CASES_TAC (ISPEC `ev:((A)word_loc)list` list_CASES) THEN
   REWRITE_TAC[MAP; NOT_CONS_NIL] THEN
   REWRITE_TAC[loop_evaluate_def; alist_insert_def] THEN SIMP[RECORD_SELFID_ss];
   ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `ns0:num list`
     SUBST1_TAC)) (ISPEC `ns:num list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n)`; SUC_INJ] THEN
  STRUCT_CASES_TAC (ISPEC `ev:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  REWRITE_TAC[MAP2; HD; TL; loop_nested_seq_def; ALL_DISTINCT] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pair_CASE; option_CASE] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN ASM_REWRITE_TAC[option_CASE; pair_CASE] THEN
  REWRITE_TAC[alist_insert_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ns0:num list`; `loop_set_var n0 h (t:(A,FFI)loop_state)`;
                                `t':((A)word_loc)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [QPAT_X_ASSUM "MAP _ _ = MAP SOME _" (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MAP_CONG THEN
      REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC locals_touched_eq_eval_eq THEN
      REWRITE_TAC[loop_set_var_def] THEN SIMP[lookup_insert] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term ((=) `distinct_lists:num list->num list->bool`)) (concl th))) THEN
      REWRITE_TAC[distinct_lists_def; ALL; MEM_FLAT; MEM; MEM_MAP] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC (GEN_ALL distinct_lists_cons) THEN
      MAP_EVERY EXISTS_TAC [`[n0:num]`; `locals_touched (a0:(A)loop_exp)`] THEN
      ASM_REWRITE_TAC[APPEND; GSYM FLAT]];
    DISCH_THEN SUBST1_TAC THEN SIMP[loop_set_var_def] THEN
    ASM_SIMP_TAC[GEN_ALL alist_insert_pull_insert]]);;

let get_var_imm_add_clk_eq = prove
 (`get_var_imm ri (loop_state_clock_fupd (K ck) (s:(A,FFI)loop_state)) =
   get_var_imm ri s`,
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[get_var_imm_def] THEN SIMP[]);;

let get_vars_local_clock_upd_eq = prove
 (`!ns (st:(A,FFI)loop_state) l ck.
     get_vars ns (loop_state_locals_fupd (K l) (loop_state_clock_fupd (K ck) st)) =
     get_vars ns (loop_state_locals_fupd (K l) st)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[get_vars_def] THEN SIMP[]);;

let get_vars_clock_upd_eq = prove
 (`!ns (st:(A,FFI)loop_state) ck.
     get_vars ns (loop_state_clock_fupd (K ck) st) = get_vars ns st`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[get_vars_def] THEN SIMP[]);;
let get_vars_local_update_some_eq = prove
 (`!ns vs (st:(A,FFI)loop_state).
     ALL_DISTINCT ns /\ LENGTH ns = LENGTH vs ==>
     get_vars ns (loop_state_locals_fupd (K (alist_insert ns vs (loop_state_locals st))) st) =
     SOME vs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`; SUC_INJ; get_vars_def;
              ALL_DISTINCT; alist_insert_def] THEN
  REPEAT STRIP_TAC THEN SIMP[lookup_insert] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':((A)word_loc)list`;
     `loop_state_locals_fupd (K (insert h h' (loop_state_locals st)))
        (st:(A,FFI)loop_state)`]) THEN
  SIMP[] THEN ASM_SIMP_TAC[GEN_ALL alist_insert_pull_insert] THEN
  REWRITE_TAC[option_CASE]);;

let lookup_set_vars = prove
 (CASE_TERM
  `LENGTH xs = LENGTH ys ==>
   lookup n (loop_state_locals (set_vars xs ys (s:(A,FFI)loop_state))) =
   match ALOOKUP (ZIP xs ys) n with
     NONE -> lookup n (loop_state_locals s)
   | SOME v -> SOME v`,
  REWRITE_TAC[set_vars_def] THEN SIMP[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP lookup_alist_insert th]));;

let PLOOPAUX_lookup_alist_insert_not_MEM = prove
 (`!xs ys (t:A spt). ~MEM n xs ==> lookup n (alist_insert xs ys t) = lookup n t`,
  MATCH_MP_TAC alist_insert_ind THEN
  SIMP[alist_insert_def; MEM; lookup_insert; DE_MORGAN_THM]);;

let lookup_set_vars_not_MEM = prove
 (`~MEM n xs ==>
   lookup n (loop_state_locals (set_vars xs ys (s:(A,FFI)loop_state))) =
   lookup n (loop_state_locals s)`,
  REWRITE_TAC[set_vars_def] THEN SIMP[PLOOPAUX_lookup_alist_insert_not_MEM]);;

let lookup_alist_insert_any = prove
 (CASE_TERM
  `LENGTH xs = LENGTH ys ==>
   lookup n (alist_insert xs ys (t:A spt)) =
   match ALOOKUP (ZIP xs ys) n with
     NONE -> lookup n t
   | SOME v -> SOME v`,
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP lookup_alist_insert th]));;

(* ------------------------------------------------------------------------- *)
(* unassigned_vars_evaluate_same.  A stronger form is proved first (without  *)
(* the hypothesis lookup n s.locals = SOME v, which the induction does not    *)
(* need), with the results after which a run goes on (NONE, Continue,         *)
(* Break) named by the local predicate PLOOPAUX_normal.                       *)
(* ------------------------------------------------------------------------- *)

let PLOOPAUX_normal_def = new_definition
  `PLOOPAUX_normal (r:((W)loop_result)option) <=>
     r = NONE \/ (?n. r = SOME (loopSem_Continue n)) \/ (?n. r = SOME (loopSem_Break n))`;;

let PLOOPAUX_normal_thm = prove
 (`PLOOPAUX_normal (NONE:((W)loop_result)option) /\
   PLOOPAUX_normal (SOME (loopSem_Continue n):((W)loop_result)option) /\
   PLOOPAUX_normal (SOME (loopSem_Break n):((W)loop_result)option) /\
   ~PLOOPAUX_normal (SOME loop_Error:((W)loop_result)option) /\
   ~PLOOPAUX_normal (SOME loop_TimeOut:((W)loop_result)option) /\
   ~PLOOPAUX_normal (SOME (loop_Result vs):((W)loop_result)option) /\
   ~PLOOPAUX_normal (SOME (loop_Exception e):((W)loop_result)option) /\
   ~PLOOPAUX_normal (SOME (loop_FinalFFI f):((W)loop_result)option)`,
  REWRITE_TAC(PLOOPAUX_normal_def :: PLOOPAUX_result_rws) THEN MESON_TAC[]);;

let PLOOPAUX_NORMAL_RWS = PLOOPAUX_normal_thm :: PLOOPAUX_result_rws;;

let PLOOPAUX_normal_cut_res = prove
 (`!live r (s:(A,FFI)loop_state) res t.
     cut_res (live:(B)spt) (r:((W)loop_result)option,s) = (res,t)
     ==> PLOOPAUX_normal res ==> PLOOPAUX_normal r`,
  REWRITE_TAC[cut_res_def; PLOOPAUX_normal_def] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  ASM_REWRITE_TAC PLOOPAUX_result_rws THEN ASM_MESON_TAC[]);;

let PLOOPAUX_normal_cut_res_lookup = prove
 (`!live r (s:(A,FFI)loop_state) res t n.
     cut_res (live:(B)spt) (r:((W)loop_result)option,s) = (res,t)
     ==> PLOOPAUX_normal res ==> n IN domain live
     ==> lookup n (loop_state_locals t) = lookup n (loop_state_locals s)`,
  REWRITE_TAC[cut_res_def; cut_state_def; loop_dec_clock_def; PLOOPAUX_normal_def] THEN
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  FS[lookup_inter_alt]);;

let PLOOPAUX_normal_cut_res_none = prove
 (`!live (s:(A,FFI)loop_state) res t.
     cut_res (live:(B)spt) (NONE:((W)loop_result)option,s) = (res,t)
     ==> PLOOPAUX_normal res ==> res = NONE`,
  REWRITE_TAC[cut_res_def; PLOOPAUX_normal_def] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_REWRITE_TAC[]);;

let PLOOPAUX_normal_exit_loop = prove
 (`!r:((W)loop_result)option.
     PLOOPAUX_normal (loop_exit_loop r) ==> PLOOPAUX_normal r`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((W)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[loop_exit_loop_def] THEN
  STRUCT_CASES_TAC (ISPEC `a:(W)loop_result` (cases "loop_result")) THEN
  REWRITE_TAC[loop_exit_loop_def; PLOOPAUX_normal_thm]);;

let PLOOPAUX_arith_lookup = prove
 (`!arith (s:(A,FFI)loop_state) s1 n.
     loop_arith s arith = SOME s1 ==>
     ~MEM n (loop_assigned_vars (loop_Arith arith:(A)loop_prog))
     ==> lookup n (loop_state_locals s1) = lookup n (loop_state_locals s)`,
  MATCH_MP_TAC loop_arith_INDUCT THEN
  REWRITE_TAC[loop_arith_def; loop_assigned_vars_def; MEM; DE_MORGAN_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[loop_set_var_def] THEN
  SIMP[lookup_insert] THEN MESON_TAC[]);;

let PLOOPAUX_mem_store_locals = prove
 (`loop_mem_store a w (s:(A,FFI)loop_state) = SOME s1
   ==> loop_state_locals s1 = loop_state_locals s`,
  REWRITE_TAC[loop_mem_store_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let PLOOPAUX_sh_mem_op_lookup = prove
 (`!op r ad (s:(A,FFI)loop_state) res t n.
     loop_sh_mem_op op r ad s = (res:((W)loop_result)option,t) ==>
     PLOOPAUX_normal res ==> ~(n = r)
     ==> lookup n (loop_state_locals t) = lookup n (loop_state_locals s)`,
  MATCH_MP_TAC memop_INDUCT THEN
  REWRITE_TAC[loop_sh_mem_op_def; loop_sh_mem_load_def; loop_sh_mem_store_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_NORMAL_RWS) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[loop_set_var_def; call_env_def] THEN SIMP[lookup_insert] THEN
  ASM_MESON_TAC[]);;

let PLOOPAUX_cut_state_lookup = prove
 (`cut_state (live:(B)spt) (s:(A,FFI)loop_state) = SOME s1 ==> n IN domain live
   ==> lookup n (loop_state_locals s1) = lookup n (loop_state_locals s)`,
  REWRITE_TAC[cut_state_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[lookup_inter_alt]);;

(* drop the induction hypotheses (assumptions with an evaluation under a     *)
(* binder) once they have been used                                         *)

let PLOOPAUX_DROP_IHS_TAC : tactic =
  let is_ih tm = is_forall tm &&
                 can (find_term (fun t -> try fst(dest_const t) = "loop_evaluate"
                                          with Failure _ -> false)) tm in
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_ih o concl)));;

let PLOOPAUX_UNASS_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  IMP_RES_TAC PLOOPAUX_arith_lookup THEN
  RULE_ASSUM_TAC(REWRITE_RULE([loop_assigned_vars_def; survives_def; MEM_APPEND; MEM;
                               DE_MORGAN_THM; option_CASE; pair_CASE] @
                              PLOOPAUX_NORMAL_RWS)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN
  IMP_RES_TAC PLOOPAUX_normal_cut_res THEN
  IMP_RES_TAC PLOOPAUX_normal_exit_loop THEN
  IMP_RES_TAC PLOOPAUX_normal_cut_res_lookup THEN
  IMP_RES_TAC PLOOPAUX_normal_cut_res_none THEN
  IMP_RES_TAC PLOOPAUX_mem_store_locals THEN
  IMP_RES_TAC PLOOPAUX_sh_mem_op_lookup THEN
  IMP_RES_TAC PLOOPAUX_cut_state_lookup THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_NORMAL_RWS) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_IHS_TAC (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC PLOOPAUX_NORMAL_RWS) THEN
  PLOOPAUX_DROP_IHS_TAC THEN
  FS[loop_set_var_def; set_vars_def; loop_dec_clock_def; loop_set_globals_def;
     call_env_def; lookup_insert; PLOOPAUX_lookup_alist_insert_not_MEM] THEN
  ASM_MESON_TAC[];;

let PLOOPAUX_unassigned_vars_same = prove
 (`!n p (s:(A,FFI)loop_state) res t.
     loop_evaluate (p,s) = (res,t) /\ PLOOPAUX_normal res /\
     ~MEM n (loop_assigned_vars p) /\ survives n p ==>
     lookup n (loop_state_locals t) = lookup n (loop_state_locals s)`,
  GEN_TAC THEN REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PLOOPAUX_UNASS_TAC);;

(* HOL4: unassigned_vars_evaluate_same *)

let loop_unassigned_vars_evaluate_same = prove
 (`!p (s:(A,FFI)loop_state) res t n v.
     loop_evaluate (p,s) = (res,t) /\
     (res = NONE \/ (?n. res = SOME (loopSem_Continue n)) \/
      (?n. res = SOME (loopSem_Break n))) /\
     lookup n (loop_state_locals s) = SOME v /\
     ~MEM n (loop_assigned_vars p) /\ survives n p ==>
     lookup n (loop_state_locals t) = lookup n (loop_state_locals s)`,
  REWRITE_TAC[GSYM PLOOPAUX_normal_def] THEN
  MESON_TAC[PLOOPAUX_unassigned_vars_same]);;
let evaluate_nested_seq_cases = prove
 (`(!p q (s:(A,FFI)loop_state) st t.
      loop_evaluate (loop_nested_seq (APPEND p q), s) = (NONE, t) /\
      loop_evaluate (loop_nested_seq p,s) = (NONE,st) ==>
      loop_evaluate (loop_nested_seq q,st) = (NONE,t)) /\
   (!p (s:(A,FFI)loop_state) st q.
      loop_evaluate (loop_nested_seq p, s) = (NONE, st) ==>
      loop_evaluate (loop_nested_seq (APPEND p q), s) =
      loop_evaluate (loop_nested_seq q, st)) /\
   (!p (s:(A,FFI)loop_state) res st q.
      loop_evaluate (loop_nested_seq p, s) = (res, st) /\ ~(res = NONE) ==>
      loop_evaluate (loop_nested_seq (APPEND p q), s) =
      loop_evaluate (loop_nested_seq p, s))`,
  REPEAT CONJ_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; loop_nested_seq_def] THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PAIR_EQ] THENL
  [MESON_TAC[]; ALL_TAC; MESON_TAC[]; ALL_TAC; MESON_TAC[]; ALL_TAC] THEN
  PAIR_CASES_ON `loop_evaluate (h:(A)loop_prog,s:(A,FFI)loop_state)` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;
let survives_nested_seq_intro = prove
 (`!p q n.
     survives n (loop_nested_seq p:(A)loop_prog) /\
     survives n (loop_nested_seq q) ==>
     survives n (loop_nested_seq (APPEND p q))`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; loop_nested_seq_def; survives_def]);;

let nested_assigns_survives = prove
 (`!xs ys n.
     LENGTH xs = LENGTH ys ==>
     survives n (loop_nested_seq (MAP2 loop_Assign xs ys):(A)loop_prog)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`; SUC_INJ; MAP2; HD; TL;
               loop_nested_seq_def; survives_def]);;

let comp_syn_ok_seq2 = prove
 (`!l p q. comp_syntax_ok l (p:(A)loop_prog) /\ comp_syntax_ok (cut_sets l p) q ==>
           comp_syntax_ok l (loop_Seq p q)`,
  REWRITE_TAC[comp_syntax_ok_def]);;

let comp_syn_ok_nested_seq = prove
 (`!p q l. comp_syntax_ok l (loop_nested_seq p:(A)loop_prog) /\
           comp_syntax_ok (cut_sets l (loop_nested_seq p)) (loop_nested_seq q) ==>
           comp_syntax_ok l (loop_nested_seq (APPEND p q))`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[APPEND; loop_nested_seq_def; cut_sets_def; comp_syntax_ok_def]);;

let comp_syn_ok_nested_seq2 = prove
 (`!p q l. comp_syntax_ok l (loop_nested_seq (APPEND p q):(A)loop_prog) ==>
           comp_syntax_ok l (loop_nested_seq p) /\
           comp_syntax_ok (cut_sets l (loop_nested_seq p)) (loop_nested_seq q)`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[APPEND; loop_nested_seq_def; cut_sets_def; comp_syntax_ok_def]);;

let cut_sets_nested_seq = prove
 (`!p q l. cut_sets l (loop_nested_seq (APPEND p q):(A)loop_prog) =
           cut_sets (cut_sets l (loop_nested_seq p)) (loop_nested_seq q)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; loop_nested_seq_def; cut_sets_def]);;
let PLOOPAUX_insert_union_r = prove
 (`!n (l:num_set). insert n one l = sptree_union l (insert n one LN)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [union_num_set_sym] THEN
  REWRITE_TAC[union_insert_LN]);;

let PLOOPAUX_foldl_insert_union = prove
 (`!ns (l:num_set). ?l'. FOLDL (\sp n. insert n one sp) l ns = sptree_union l l'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL] THENL
  [MESON_TAC[union_LN]; ALL_TAC] THEN
  GEN_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `l2:num_set` o SPEC `insert h one (l:num_set)`) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `sptree_union (insert h one LN) (l2:num_set)` THEN
  REWRITE_TAC[union_assoc] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC PLOOPAUX_insert_union_r);;

let PLOOPAUX_cut_sets_union = prove
 (`!l (p:(A)loop_prog). comp_syntax_ok l p ==> ?l'. cut_sets l p = sptree_union l l'`,
  MATCH_MP_TAC (cake_ind "comp_syntax_ok") THEN
  REWRITE_TAC[comp_syntax_ok_def; cut_sets_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
  [EXISTS_TAC `LN:num_set` THEN REWRITE_TAC[union_LN];
   EXISTS_TAC `insert n one LN:num_set` THEN MATCH_ACCEPT_TAC PLOOPAUX_insert_union_r;
   EXISTS_TAC `LN:num_set` THEN REWRITE_TAC[union_LN];
   STRUCT_CASES_TAC (ISPEC `arith:loop_arith` (cases "loop_arith")) THEN
   REWRITE_TAC[case_def "loop_arith"] THENL
   [EXISTS_TAC `sptree_union (insert a0 one LN) (insert a1 one LN):num_set`;
    EXISTS_TAC `sptree_union (insert a0 one LN) (insert a1 one LN):num_set`;
    EXISTS_TAC `insert a0 one LN:num_set`] THEN
   GEN_REWRITE_TAC RAND_CONV [union_num_set_sym] THEN
   REWRITE_TAC[GSYM union_assoc; union_insert_LN];
   EXISTS_TAC `LN:num_set` THEN REWRITE_TAC[union_LN];
   EXISTS_TAC `insert n one LN:num_set` THEN MATCH_ACCEPT_TAC PLOOPAUX_insert_union_r;
   EXISTS_TAC `insert m one LN:num_set` THEN MATCH_ACCEPT_TAC PLOOPAUX_insert_union_r;
   EXISTS_TAC `insert m one LN:num_set` THEN MATCH_ACCEPT_TAC PLOOPAUX_insert_union_r;
   SUBGOAL_THEN `?l1. cut_sets l (p:(A)loop_prog) = sptree_union l l1`
     (X_CHOOSE_TAC `l1:num_set`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `?l2. cut_sets (cut_sets l (p:(A)loop_prog)) (q:(A)loop_prog) =
                     sptree_union (cut_sets l p) l2`
     (X_CHOOSE_TAC `l2:num_set`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `sptree_union l1 l2:num_set` THEN ASM_REWRITE_TAC[union_assoc];
   MATCH_ACCEPT_TAC PLOOPAUX_foldl_insert_union]);;
let cut_sets_union_accumulate = prove
 (`!p l. comp_syntax_ok l (p:(A)loop_prog) ==>
         ?l':num_set. cut_sets l p = sptree_union l l'`,
  MESON_TAC[PLOOPAUX_cut_sets_union]);;

let cut_sets_union_domain_subset = prove
 (`!p l. comp_syntax_ok l (p:(A)loop_prog) ==> domain l SUBSET domain (cut_sets l p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP cut_sets_union_accumulate) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[domain_union] THEN SET_TAC[]);;

let cut_sets_union_domain_union = prove
 (`!p l. comp_syntax_ok l (p:(A)loop_prog) ==>
         ?l':num_set. domain (cut_sets l p) = domain l UNION domain l'`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP cut_sets_union_accumulate) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[domain_union] THEN MESON_TAC[]);;

let comp_syn_impl_cut_sets_subspt = prove
 (`!p l. comp_syntax_ok l (p:(A)loop_prog) ==> subspt l (cut_sets l p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP cut_sets_union_accumulate) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[subspt_union]);;

let comp_syn_cut_sets_mem_domain = prove
 (`!p l n. comp_syntax_ok l (p:(A)loop_prog) /\ n IN domain l ==>
           n IN domain (cut_sets l p)`,
  MESON_TAC[cut_sets_union_domain_subset; SUBSET]);;

(* for a conditional program if b then c1 else c2 in an assumption, and      *)
(* assumptions R c1 and R c2, add R (if b then c1 else c2) (for induction    *)
(* hypotheses with an existential variable in such an antecedent)            *)

let PLOOPAUX_COND_FACT_TAC : tactic = fun (asl,w as g) ->
  let is_prog_cond t =
    is_cond t && (try fst(dest_type(type_of t)) = "loop_prog" with Failure _ -> false) in
  let conds = setify (flat (map (fun (_,th) -> find_terms is_prog_cond (concl th)) asl)) in
  let facts = map (concl o snd) asl in
  let mk c =
    let b,(x,y) = dest_cond c in
    mapfilter (fun f ->
        if free_in x f && not (free_in y f) && not (free_in c f) then
          let fy = subst [y,x] f in
          if mem fy facts then subst [c,x] f else failwith ""
        else failwith "") facts in
  let tms = setify (flat (map mk conds)) in
  MAP_EVERY (fun tm -> SUBGOAL_THEN tm ASSUME_TAC THENL
                         [COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) tms g;;

let PLOOPAUX_arith_locals = prove
 (`!arith (s:(A,FFI)loop_state) s1.
     loop_arith s arith = SOME s1 ==> ?l. s1 = loop_state_locals_fupd (K l) s`,
  MATCH_MP_TAC loop_arith_INDUCT THEN
  REWRITE_TAC[loop_arith_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[loop_set_var_def] THEN
  SIMP[] THEN MESON_TAC[]);;

let PLOOPAUX_UPD_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PLOOPAUX_arith_locals)) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[comp_syntax_ok_def]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN PLOOPAUX_COND_FACT_TAC THEN
  PLOOPAUX_IHS_TAC (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  PLOOPAUX_DROP_IHS_TAC THEN
  FS([loop_set_var_def; loop_dec_clock_def; cut_res_def; cut_state_def] @
     all_case_eqs()) THEN
  RVEQ_TAC THEN FS[];;
let PLOOPAUX_comp_syn_ok_fields = prove
 (`!p (s:(A,FFI)loop_state) res t l.
     loop_evaluate (p,s) = (res,t) /\ comp_syntax_ok l p ==>
     loop_state_globals t = loop_state_globals s /\
     loop_state_memory t = loop_state_memory s /\
     loop_state_mdomain t = loop_state_mdomain s /\
     loop_state_sh_mdomain t = loop_state_sh_mdomain s /\
     loop_state_code t = loop_state_code s /\
     loop_state_be t = loop_state_be s /\
     loop_state_ffi t = loop_state_ffi s /\
     loop_state_base_addr t = loop_state_base_addr s /\
     loop_state_top_addr t = loop_state_top_addr s`,
  REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN PLOOPAUX_UPD_TAC);;

let comp_syn_ok_upd_local_clock = prove
 (`!p (s:(A,FFI)loop_state) res t l.
     loop_evaluate (p,s) = (res,t) /\ comp_syntax_ok l p ==>
     t = loop_state_locals_fupd (K (loop_state_locals t))
           (loop_state_clock_fupd (K (loop_state_clock t)) s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PLOOPAUX_comp_syn_ok_fields) THEN
  REWRITE_TAC[loop_state_component_equality] THEN SIMP[]);;

let assigned_vars_nested_seq_split = prove
 (`!p q. loop_assigned_vars (loop_nested_seq (APPEND p q):(A)loop_prog) =
         APPEND (loop_assigned_vars (loop_nested_seq p))
                (loop_assigned_vars (loop_nested_seq q))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; loop_nested_seq_def; loop_assigned_vars_def; APPEND_ASSOC]);;

let assigned_vars_seq_split = prove
 (`!q p. loop_assigned_vars (loop_Seq p q:(A)loop_prog) =
         APPEND (loop_assigned_vars p) (loop_assigned_vars q)`,
  REWRITE_TAC[loop_assigned_vars_def]);;

let assigned_vars_nested_assign = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys ==>
     loop_assigned_vars (loop_nested_seq (MAP2 loop_Assign xs ys):(A)loop_prog) = xs`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`; SUC_INJ; MAP2; HD; TL;
               loop_nested_seq_def; loop_assigned_vars_def; APPEND]);;
let PLOOPAUX_cut_res_not_timeout = prove
 (`!live r (s:(A,FFI)loop_state) res t.
     cut_res (live:(B)spt) (r:((W)loop_result)option,s) = (res,t)
     ==> ~(res = SOME loop_TimeOut) ==> ~(r = SOME loop_TimeOut)`,
  REWRITE_TAC[cut_res_def] THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN ASM_MESON_TAC[]);;

let PLOOPAUX_cut_res_lookup_nt = prove
 (`!live r (s:(A,FFI)loop_state) res t n.
     cut_res (live:(B)spt) (r:((W)loop_result)option,s) = (res,t)
     ==> ~(res = SOME loop_TimeOut) ==> n IN domain live
     ==> lookup n (loop_state_locals t) = lookup n (loop_state_locals s)`,
  REWRITE_TAC[cut_res_def; cut_state_def; loop_dec_clock_def] THEN
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  FS[lookup_inter_alt]);;

let PLOOPAUX_exit_loop_not_timeout = prove
 (`!r:((W)loop_result)option.
     ~(loop_exit_loop r = SOME loop_TimeOut) ==> ~(r = SOME loop_TimeOut)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `r:((W)loop_result)option` (cases "option")) THEN
  REWRITE_TAC[loop_exit_loop_def] THEN
  STRUCT_CASES_TAC (ISPEC `a:(W)loop_result` (cases "loop_result")) THEN
  REWRITE_TAC(loop_exit_loop_def :: PLOOPAUX_result_rws));;

let PLOOPAUX_foldl_domain = prove
 (`!ns (l:num_set) n. n IN domain l ==>
                     n IN domain (FOLDL (\sp n. insert n one sp) l ns)`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `l2:num_set` SUBST1_TAC (SPECL [`ns:num list`; `l:num_set`]
    PLOOPAUX_foldl_insert_union) THEN
  REWRITE_TAC[domain_union; IN_UNION] THEN MESON_TAC[]);;

let PLOOPAUX_CSLOOK_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  IMP_RES_TAC PLOOPAUX_arith_lookup THEN
  RULE_ASSUM_TAC(REWRITE_RULE([loop_assigned_vars_def; comp_syntax_ok_def; MEM_APPEND;
                               MEM; DE_MORGAN_THM] @ PLOOPAUX_result_rws)) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) ||
                                                           is_exists (concl th)))) THEN
  RVEQ_TAC THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN PLOOPAUX_COND_FACT_TAC THEN
  IMP_RES_TAC PLOOPAUX_cut_res_not_timeout THEN
  IMP_RES_TAC PLOOPAUX_exit_loop_not_timeout THEN
  IMP_RES_TAC PLOOPAUX_cut_res_lookup_nt THEN
  IMP_RES_TAC PLOOPAUX_foldl_domain THEN
  IMP_RES_TAC comp_syn_cut_sets_mem_domain THEN
  PLOOPAUX_COND_FACT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_IHS_TAC (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC PLOOPAUX_result_rws) THEN
  PLOOPAUX_DROP_IHS_TAC THEN
  FS[loop_set_var_def; loop_dec_clock_def; lookup_insert] THEN
  ASM_MESON_TAC[];;

let PLOOPAUX_comp_syn_ok_lookup = prove
 (`!n p (s:(A,FFI)loop_state) res t l.
     loop_evaluate (p,s) = (res,t) /\ ~(res = SOME loop_TimeOut) /\
     comp_syntax_ok l p /\ n IN domain l /\
     ~MEM n (loop_assigned_vars p) ==>
     lookup n (loop_state_locals t) = lookup n (loop_state_locals s)`,
  GEN_TAC THEN REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PLOOPAUX_CSLOOK_TAC);;

let comp_syn_ok_lookup_locals_eq = prove
 (`!p (s:(A,FFI)loop_state) res t l n.
     loop_evaluate (p,s) = (res,t) /\ ~(res = SOME loop_TimeOut) /\
     comp_syntax_ok l p /\ n IN domain l /\
     ~MEM n (loop_assigned_vars p) ==>
     lookup n (loop_state_locals t) = lookup n (loop_state_locals s)`,
  MESON_TAC[PLOOPAUX_comp_syn_ok_lookup]);;
(* HOL4: eval_upd_clock_eq *)

let loop_eval_upd_clock_eq = prove
 (`!(t:(A,FFI)loop_state) e ck.
     loop_eval (loop_state_clock_fupd (K ck) t) e = loop_eval t e`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC locals_touched_eq_eval_eq THEN SIMP[]);;

let eval_upd_locals_clock_eq = prove
 (`!(t:(A,FFI)loop_state) e l ck.
     loop_eval (loop_state_locals_fupd (K l) (loop_state_clock_fupd (K ck) t)) e =
     loop_eval (loop_state_locals_fupd (K l) t) e`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC locals_touched_eq_eval_eq THEN SIMP[]);;

let cut_res_add_clock = prove
 (`cut_res l (res,s) = (q,r) /\ ~(q = SOME loop_TimeOut) ==>
   cut_res (l:(B)spt) (res:((W)loop_result)option,
                       loop_state_clock_fupd (K (ck + loop_state_clock s))
                         (s:(A,FFI)loop_state)) =
   (q, loop_state_clock_fupd (K (ck + loop_state_clock r)) r)`,
  ASM_CASES_TAC `res:((W)loop_result)option = NONE` THEN
  ASM_REWRITE_TAC[cut_res_def; cut_state_def; loop_dec_clock_def; PAIR_EQ] THEN
  SIMP[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE; PAIR_EQ] THEN SIMP[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `(ck + loop_state_clock (s:(A,FFI)loop_state)) - 1 =
                ck + (loop_state_clock s - 1)` SUBST1_TAC
  THENL [ASM_ARITH_TAC; SIMP[]]);;

let get_vars_clock = prove
 (`!vs (s:(A,FFI)loop_state) c.
     get_vars vs (loop_state_clock_fupd (K c) s) = get_vars vs s`,
  REWRITE_TAC[get_vars_clock_upd_eq]);;
let PLOOPAUX_arith_clock_upd = prove
 (`!arith (s:(A,FFI)loop_state) c.
     loop_arith (loop_state_clock_fupd (K c) s) arith =
     OPTION_MAP (loop_state_clock_fupd (K c)) (loop_arith s arith)`,
  MATCH_MP_TAC loop_arith_INDUCT THEN
  REWRITE_TAC[loop_arith_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP[loop_set_var_def] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT TOP_CASE_TAC THEN SIMP[OPTION_MAP_DEF]);;

let PLOOPAUX_mem_store_clock_upd = prove
 (`loop_mem_store a w (loop_state_clock_fupd (K c) (s:(A,FFI)loop_state)) =
   OPTION_MAP (loop_state_clock_fupd (K c)) (loop_mem_store a w s)`,
  REWRITE_TAC[loop_mem_store_def] THEN SIMP[] THEN COND_CASES_TAC THEN
  SIMP[OPTION_MAP_DEF]);;

let PLOOPAUX_cut_state_clock_upd = prove
 (`cut_state (live:(B)spt) (loop_state_clock_fupd (K c) (s:(A,FFI)loop_state)) =
   OPTION_MAP (loop_state_clock_fupd (K c)) (cut_state live s)`,
  REWRITE_TAC[cut_state_def] THEN SIMP[] THEN COND_CASES_TAC THEN
  SIMP[OPTION_MAP_DEF]);;

let PLOOPAUX_sh_mem_op_clock_upd = prove
 (`!op r ad (s:(A,FFI)loop_state) c.
     loop_sh_mem_op op r ad (loop_state_clock_fupd (K c) s):((W)loop_result)option#
                                                             (A,FFI)loop_state =
     (FST (loop_sh_mem_op op r ad s:((W)loop_result)option#(A,FFI)loop_state),
      loop_state_clock_fupd (K c)
        (SND (loop_sh_mem_op op r ad s:((W)loop_result)option#(A,FFI)loop_state)))`,
  MATCH_MP_TAC memop_INDUCT THEN
  REWRITE_TAC[loop_sh_mem_op_def; loop_sh_mem_load_def; loop_sh_mem_store_def;
              loop_set_var_def; call_env_def] THEN
  SIMP[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT TOP_CASE_TAC THEN SIMP[]);;

let PLOOPAUX_dec_clock_add = prove
 (`~(loop_state_clock s = 0) ==>
   loop_dec_clock (loop_state_clock_fupd (K (loop_state_clock s + ck)) (s:(A,FFI)loop_state)) =
   loop_state_clock_fupd (K (loop_state_clock (loop_dec_clock s) + ck)) (loop_dec_clock s)`,
  REWRITE_TAC[loop_dec_clock_def] THEN SIMP[] THEN DISCH_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let PLOOPAUX_cut_res_add_clock = prove
 (`cut_res l (res,s) = (q,r) ==> ~(q = SOME loop_TimeOut) ==>
   cut_res (l:(B)spt) (res:((W)loop_result)option,
                       loop_state_clock_fupd (K (loop_state_clock s + ck))
                         (s:(A,FFI)loop_state)) =
   (q, loop_state_clock_fupd (K (loop_state_clock r + ck)) r)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MESON_TAC[cut_res_add_clock]);;

let PLOOPAUX_ADDCLK_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN
  IMP_RES_TAC PLOOPAUX_cut_res_not_timeout THEN
  IMP_RES_TAC PLOOPAUX_exit_loop_not_timeout THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_IHS_TAC (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC PLOOPAUX_result_rws) THEN
  IMP_RES_TAC PLOOPAUX_cut_res_add_clock THEN
  IMP_RES_TAC PLOOPAUX_arith_clock THEN IMP_RES_TAC PLOOPAUX_mem_store_clock THEN
  IMP_RES_TAC PLOOPAUX_sh_mem_op_clock THEN IMP_RES_TAC PLOOPAUX_cut_state_clock THEN
  PLOOPAUX_DROP_IHS_TAC THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  FS[loop_eval_upd_clock_eq; get_vars_clock_upd_eq; get_var_imm_add_clk_eq;
     PLOOPAUX_arith_clock_upd; PLOOPAUX_mem_store_clock_upd; PLOOPAUX_cut_state_clock_upd;
     PLOOPAUX_sh_mem_op_clock_upd; PLOOPAUX_dec_clock_add; OPTION_MAP_DEF;
     loop_set_var_def; set_vars_def; loop_set_globals_def; call_env_def;
     LET_DEF; LET_END_DEF];;

let PLOOPAUX_evaluate_add_clock = prove
 (`!ck p (t:(A,FFI)loop_state) res st.
     loop_evaluate (p,t) = (res,st) /\ ~(res = SOME loop_TimeOut) ==>
     loop_evaluate (p,loop_state_clock_fupd (K (loop_state_clock t + ck)) t) =
     (res,loop_state_clock_fupd (K (loop_state_clock st + ck)) st)`,
  GEN_TAC THEN REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PLOOPAUX_ADDCLK_TAC);;

(* HOL4: evaluate_add_clock_eq *)

let loop_evaluate_add_clock_eq = prove
 (`!p (t:(A,FFI)loop_state) res st ck.
     loop_evaluate (p,t) = (res,st) /\ ~(res = SOME loop_TimeOut) ==>
     loop_evaluate (p,loop_state_clock_fupd (K (loop_state_clock t + ck)) t) =
     (res,loop_state_clock_fupd (K (loop_state_clock st + ck)) st)`,
  MESON_TAC[PLOOPAUX_evaluate_add_clock]);;
(* the clause of a constructor in loop_evaluate_def *)
let PLOOPAUX_eval_clause (c:string) =
  let head th =
    let l = lhs(snd(strip_forall(concl th))) in
    fst(dest_const(fst(strip_comb(fst(dest_pair(rand l)))))) in
  find (fun th -> try head th = c with Failure _ -> false)
       (CONJUNCTS loop_evaluate_def);;
let PLOOPAUX_seq_clause = PLOOPAUX_eval_clause "loop_Seq";;

let PLOOPAUX_seq_assoc = prove
 (`!a b c (s:(A,FFI)loop_state).
     loop_evaluate (loop_Seq (loop_Seq a b) c,s) =
     loop_evaluate (loop_Seq a (loop_Seq b c),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PLOOPAUX_seq_clause] THEN
  PAIR_CASES_ON `loop_evaluate (a:(A)loop_prog,s:(A,FFI)loop_state)` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[pair_CASE]);;

let PLOOPAUX_seq_cong = prove
 (`!a b c (s:(A,FFI)loop_state).
     (!s:(A,FFI)loop_state. loop_evaluate (b,s) = loop_evaluate (c,s)) ==>
     loop_evaluate (loop_Seq a b,s) = loop_evaluate (loop_Seq a c,s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[PLOOPAUX_seq_clause]);;

let evaluate_nested_seq_comb_seq = prove
 (`!p q (t:(A,FFI)loop_state).
     loop_evaluate (loop_Seq (loop_nested_seq p) (loop_nested_seq q), t) =
     loop_evaluate (loop_nested_seq (APPEND p q), t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; loop_nested_seq_def] THENL
  [REWRITE_TAC[PLOOPAUX_seq_clause] THEN ONCE_REWRITE_TAC[loop_evaluate_def] THEN
   REWRITE_TAC[pair_CASE];
   REPEAT GEN_TAC THEN REWRITE_TAC[PLOOPAUX_seq_assoc] THEN
   MATCH_MP_TAC PLOOPAUX_seq_cong THEN ASM_REWRITE_TAC[]]);;
let nested_seq_pure_evaluation = prove
 (`!p q (t:(A,FFI)loop_state) r st l m e v ck ck'.
     loop_evaluate (loop_nested_seq p,loop_state_clock_fupd (K (ck + loop_state_clock t)) t) =
     (NONE,st) /\
     loop_evaluate (loop_nested_seq q,loop_state_clock_fupd (K (ck' + loop_state_clock st)) st) =
     (NONE,r) /\
     comp_syntax_ok l (loop_nested_seq p) /\
     comp_syntax_ok (cut_sets l (loop_nested_seq p)) (loop_nested_seq q) /\
     (!n. MEM n (loop_assigned_vars (loop_nested_seq p)) ==> n < m) /\
     (!n. MEM n (loop_assigned_vars (loop_nested_seq q)) ==> m <= n) /\
     (!n. MEM n (locals_touched e) ==>
          n < m /\ n IN domain (cut_sets l (loop_nested_seq p))) /\
     loop_eval st e = SOME v ==>
     loop_eval r e = SOME v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `loop_eval (r:(A,FFI)loop_state) e = loop_eval (st:(A,FFI)loop_state) e`
    MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MP_TAC(ISPECL [`loop_nested_seq q:(A)loop_prog`;
                 `loop_state_clock_fupd (K (ck' + loop_state_clock st)) (st:(A,FFI)loop_state)`;
                 `NONE:((A)loop_result)option`; `r:(A,FFI)loop_state`;
                 `cut_sets l (loop_nested_seq p:(A)loop_prog)`]
         PLOOPAUX_comp_syn_ok_fields) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(STRIP_ASSUME_TAC o CAKE_SIMP_RULE[])] THEN
  MATCH_MP_TAC locals_touched_eq_eval_eq THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`loop_nested_seq q:(A)loop_prog`;
                 `loop_state_clock_fupd (K (ck' + loop_state_clock st)) (st:(A,FFI)loop_state)`;
                 `NONE:((A)loop_result)option`; `r:(A,FFI)loop_state`;
                 `cut_sets l (loop_nested_seq p:(A)loop_prog)`; `n:num`]
         comp_syn_ok_lookup_locals_eq) THEN
  REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(MATCH_MP_TAC o GSYM o CAKE_SIMP_RULE[]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[ARITH_RULE `n < m ==> ~(m <= n)`]);;
let PLOOPAUX_sh_mem_op_io = prove
 (`!op r ad (s:(A,FFI)loop_state) res t.
     loop_sh_mem_op op r ad s = (res:((W)loop_result)option,t) ==>
     isPREFIX (ffi_state_io_events (loop_state_ffi s))
              (ffi_state_io_events (loop_state_ffi t))`,
  MATCH_MP_TAC memop_INDUCT THEN
  REWRITE_TAC[loop_sh_mem_op_def; loop_sh_mem_load_def; loop_sh_mem_store_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[loop_set_var_def; call_env_def] THEN SIMP[IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[SEM2AUX_call_FFI_io_events]);;

let PLOOPAUX_cut_res_ffi = prove
 (`!live r (s:(A,FFI)loop_state) res t.
     cut_res (live:(B)spt) (r:((W)loop_result)option,s) = (res,t)
     ==> loop_state_ffi t = loop_state_ffi s`,
  REWRITE_TAC[cut_res_def; cut_state_def; loop_dec_clock_def] THEN
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[]);;

let PLOOPAUX_IO_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PLOOPAUX_arith_locals)) THEN
  RVEQ_TAC THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN
  PLOOPAUX_IHS_TAC (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  IMP_RES_TAC PLOOPAUX_sh_mem_op_io THEN IMP_RES_TAC PLOOPAUX_cut_res_ffi THEN
  IMP_RES_TAC SEM2AUX_call_FFI_io_events THEN
  IMP_RES_TAC PLOOPAUX_mem_store_locals THEN
  PLOOPAUX_DROP_IHS_TAC THEN
  FS[loop_set_var_def; set_vars_def; loop_set_globals_def; call_env_def;
     loop_dec_clock_def; loop_mem_store_def; cut_state_def] THEN
  RVEQ_TAC THEN FS[IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL];;

(* HOL4: evaluate_io_events_mono *)

let loop_evaluate_io_events_mono = prove
 (`!exps (s1:(A,FFI)loop_state) res s2.
     loop_evaluate (exps,s1) = (res, s2) ==>
     isPREFIX (ffi_state_io_events (loop_state_ffi s1))
              (ffi_state_io_events (loop_state_ffi s2))`,
  REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN PLOOPAUX_IO_TAC);;

(* ------------------------------------------------------------------------- *)
(* evaluate_add_clock_io_events_mono: the run that times out, by induction   *)
(* (PLOOPAUX_timeout_io); the other runs by evaluate_add_clock               *)
(* ------------------------------------------------------------------------- *)

let PLOOPAUX_is_clock_upd tm =
  try fst(dest_const(fst(strip_comb tm))) = "loop_state_clock_fupd"
  with Failure _ -> false;;

let PLOOPAUX_evaluate_add_clock_c =
  REWRITE_RULE[GSYM IMP_IMP] PLOOPAUX_evaluate_add_clock;;

(* evaluate_add_clock at the evaluate assumptions whose result is not a     *)
(* time out (and whose state is not a clock update)                         *)

let PLOOPAUX_ADD_CLOCK_FACTS_TAC (extra:term) : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PLOOPAUX_is_eval_eq (concl th) &&
                     not (PLOOPAUX_is_clock_upd (snd(dest_pair(rand(lhs(concl th)))))))
                   (map snd asl) in
  MAP_EVERY (fun e (asl,w as g) ->
      try let th1 = MATCH_MP (SPEC extra PLOOPAUX_evaluate_add_clock_c) e in
          let ant = fst(dest_imp(concl th1)) in
          let nth = TAC_PROOF((asl,ant), ASM_REWRITE_TAC PLOOPAUX_result_rws) in
          ASSUME_TAC (MP th1 nth) g
      with Failure _ -> ALL_TAC g) evs g;;

(* the evaluations in the goal (without bound variables): name their       *)
(* results, one at a time                                                   *)

let PLOOPAUX_SPLIT_GOAL_EVAL_TAC : tactic = fun (asl,w as g) ->
  let is_ev t =
    try fst(dest_const(fst(strip_comb t))) = "loop_evaluate" && is_pair(rand t)
    with Failure _ -> false in
  let fw = frees w in
  match filter (fun t -> subset (frees t) fw) (find_terms is_ev w) with
    [] -> failwith "PLOOPAUX_SPLIT_GOAL_EVAL_TAC"
  | t::_ ->
      let ty1,ty2 = (match dest_type (type_of t) with (_,[a;b]) -> a,b | _ -> failwith "") in
      let av = freesl (w :: map (concl o snd) asl @ flat (map (hyp o snd) asl)) in
      let p0 = variant av (mk_var("q0",ty1)) in
      let p1 = variant (p0::av) (mk_var("q1",ty2)) in
      (MP_TAC(ISPEC t PAIR_SURJECTIVE) THEN
       DISCH_THEN(X_CHOOSE_THEN p0 (X_CHOOSE_THEN p1
         (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) g;;

(* a goal isPREFIX x y from a chain of assumptions isPREFIX x x1, ...,     *)
(* isPREFIX xn y (or x = y)                                                 *)

let PLOOPAUX_PREFIX_CHAIN_TAC : tactic = fun (asl,w as g) ->
  let is_pre t = try fst(dest_const(fst(strip_comb t))) = "isPREFIX" &&
                     length(snd(strip_comb t)) = 2 with Failure _ -> false in
  let args t = match snd(strip_comb t) with [a;b] -> a,b | _ -> failwith "" in
  if not (is_pre w) then failwith "PLOOPAUX_PREFIX_CHAIN_TAC" else
  let x,y = args w in
  let facts = filter (fun th -> is_pre (concl th)) (map snd asl) in
  let rec search visited frontier =
    match frontier with
      [] -> failwith "PLOOPAUX_PREFIX_CHAIN_TAC: no chain"
    | (a,th)::rest ->
        if aconv a y then th else
        let nexts = mapfilter (fun f ->
            let a',b' = args (concl f) in
            if aconv a' a && not (exists (aconv b') visited)
            then (b', MATCH_MP isPREFIX_TRANS (CONJ th f)) else failwith "") facts in
        search (map fst nexts @ visited) (rest @ nexts) in
  let th0 = ISPEC x IS_PREFIX_REFL in
  ACCEPT_TAC (search [x] [(x,th0)]) g;;

let PLOOPAUX_cut_res_ffi_eq = prove
 (`!live r (s:(A,FFI)loop_state).
     loop_state_ffi (SND (cut_res (live:(B)spt) (r:((W)loop_result)option,s))) =
     loop_state_ffi s`,
  MESON_TAC[PLOOPAUX_cut_res_ffi; PAIR]);;

(* split on whether the result variable of an evaluation is a time out *)

let PLOOPAUX_CASE_TIMEOUT_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PLOOPAUX_is_eval_eq (concl th) &&
                     not (PLOOPAUX_is_clock_upd (snd(dest_pair(rand(lhs(concl th)))))))
                   (map snd asl) in
  let rs = setify (mapfilter (fun e -> let r = fst(dest_pair(rhs(concl e))) in
                                       if is_var r then r else failwith "") evs) in
  MAP_EVERY (fun r ->
      let ty = hd(snd(dest_type(type_of r))) in
      let tm = mk_eq(r, mk_comb(mk_const("SOME",[ty,aty]),
                                mk_const("loop_TimeOut",[hd(snd(dest_type ty)),`:W`]))) in
      ASM_CASES_TAC tm) rs g;;

let PLOOPAUX_TIO_TAC : tactic =
  PLOOPAUX_EVAL_CASES_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PLOOPAUX_arith_locals)) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN
  PLOOPAUX_CASE_TIMEOUT_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC PLOOPAUX_cut_res_not_timeout THEN
  IMP_RES_TAC PLOOPAUX_exit_loop_not_timeout THEN
  RULE_ASSUM_TAC(REWRITE_RULE PLOOPAUX_result_rws) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  PLOOPAUX_IHS_TAC (REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC PLOOPAUX_result_rws) THEN
  PLOOPAUX_ADD_CLOCK_FACTS_TAC `extra:num` THEN
  IMP_RES_TAC PLOOPAUX_cut_res_add_clock THEN
  IMP_RES_TAC PLOOPAUX_arith_clock THEN IMP_RES_TAC PLOOPAUX_mem_store_clock THEN
  IMP_RES_TAC PLOOPAUX_sh_mem_op_clock THEN IMP_RES_TAC PLOOPAUX_cut_state_clock THEN
  PLOOPAUX_DROP_IHS_TAC THEN
  ONCE_REWRITE_TAC[loop_evaluate_def] THEN
  FS[loop_eval_upd_clock_eq; get_vars_clock_upd_eq; get_var_imm_add_clk_eq;
     PLOOPAUX_arith_clock_upd; PLOOPAUX_mem_store_clock_upd; PLOOPAUX_cut_state_clock_upd;
     PLOOPAUX_sh_mem_op_clock_upd; PLOOPAUX_dec_clock_add; OPTION_MAP_DEF;
     loop_set_var_def; set_vars_def; loop_set_globals_def; call_env_def;
     LET_DEF; LET_END_DEF];;

let PLOOPAUX_TIO_FIN_TAC : tactic =
  REPEAT (PLOOPAUX_SPLIT_GOAL_EVAL_TAC THEN REWRITE_TAC[pair_CASE] THEN
          REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND; FST]) THEN
  IMP_RES_TAC loop_evaluate_io_events_mono THEN IMP_RES_TAC PLOOPAUX_cut_res_ffi THEN
  FS[loop_dec_clock_def; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL];;

let PLOOPAUX_TIO_FIN_TAC : tactic =
  REPEAT ((PLOOPAUX_SPLIT_GOAL_EVAL_TAC THEN REWRITE_TAC[pair_CASE]) ORELSE
          CHANGED_TAC (TOP_CASE_TAC ORELSE COND_CASES_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND; FST]) THEN
  IMP_RES_TAC loop_evaluate_io_events_mono THEN IMP_RES_TAC PLOOPAUX_cut_res_ffi THEN
  FS[loop_dec_clock_def; IS_PREFIX_REFL; PLOOPAUX_cut_res_ffi_eq] THEN
  RFS[] THEN PLOOPAUX_PREFIX_CHAIN_TAC;;
let PLOOPAUX_timeout_io = prove
 (`!extra p (s:(A,FFI)loop_state) t.
     loop_evaluate (p,s) = (SOME loop_TimeOut, t) ==>
     isPREFIX (ffi_state_io_events (loop_state_ffi t))
       (ffi_state_io_events (loop_state_ffi (SND (loop_evaluate
          (p, loop_state_clock_fupd (K (loop_state_clock s + extra)) s)))))`,
  GEN_TAC THEN REC_IND_TAC loop_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PLOOPAUX_TIO_TAC THEN PLOOPAUX_TIO_FIN_TAC);;

(* HOL4: evaluate_add_clock_io_events_mono *)

let loop_evaluate_add_clock_io_events_mono = prove
 (`!exps (s:(A,FFI)loop_state) extra.
     isPREFIX (ffi_state_io_events (loop_state_ffi (SND (loop_evaluate (exps,s)))))
       (ffi_state_io_events (loop_state_ffi (SND (loop_evaluate
          (exps, loop_state_clock_fupd (K (loop_state_clock s + extra)) s)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `loop_evaluate (exps:(A)loop_prog,s:(A,FFI)loop_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:((A)loop_result)option`; `t:(A,FFI)loop_state`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[SND] THEN
  ASM_CASES_TAC `r = SOME (loop_TimeOut:(A)loop_result)` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC PLOOPAUX_timeout_io THEN
   ASM_REWRITE_TAC[];
   MP_TAC(ISPECL [`extra:num`; `exps:(A)loop_prog`; `s:(A,FFI)loop_state`;
                  `r:((A)loop_result)option`; `t:(A,FFI)loop_state`]
            PLOOPAUX_evaluate_add_clock) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   SIMP[SND; IS_PREFIX_REFL]]);;
