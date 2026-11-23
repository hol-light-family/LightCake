(* ========================================================================= *)
(* stack_allocProof: part 3 of 3 of the port of                             *)
(* compiler/backend/proofs/stack_allocProofScript.sml (HOL4 lines           *)
(* 4592-6361): the allocator code against stackSem's alloc for each gc kind,*)
(* the correctness of the stack_alloc compiler pass (comp_correct,         *)
(* compile_semantics, make_init_semantics) and its syntactic properties.   *)
(* Parts 1 and 2 are stack_allocProof_p1.ml and stack_allocProof_p2.ml.     *)
(* ========================================================================= *)

needs "compiler/backend/proofs/stack_allocProof_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* helpers for alloc_correct_lemma_Generational                            *)

(* the result of word_gen_gc_partial_move (word_gen_gc_move) on a word is a *)
(* word *)
let STALLOCAUX_word_gen_gc_partial_move_Word = prove
 (`!conf (g:A word) i pa old m dm gs rs w1 i1 pa1 m1 c1.
     word_gen_gc_partial_move conf (wl_Word g,i,pa,old,m,dm,gs,rs) = (w1,i1,pa1,m1,c1) ==>
     ?g1. w1 = wl_Word g1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_partial_move_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN TRY (STALLOCAUX_SPLIT_FN_TAC "memcpy" ["pa2";"m2";"c2"]) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if rhs(concl th) = `w1:(A)word_loc`
    then EXISTS_TAC (rand(lhs(concl th))) THEN REWRITE_TAC[SYM th] else NO_TAC));;

let STALLOCAUX_word_gen_gc_move_Word = prove
 (`!conf (g:A word) i pa ib pb old m dm w1 i1 pa1 ib1 pb1 m1 c1.
     word_gen_gc_move conf (wl_Word g,i,pa,ib,pb,old,m,dm) = (w1,i1,pa1,ib1,pb1,m1,c1) ==>
     ?g1. w1 = wl_Word g1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_move_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN TRY (STALLOCAUX_SPLIT_FN_TAC "memcpy" ["pa2";"m2";"c2"]) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if rhs(concl th) = `w1:(A)word_loc`
    then EXISTS_TAC (rand(lhs(concl th))) THEN REWRITE_TAC[SYM th] else NO_TAC));;

(* word_gc_partial_or_full with and without generations *)
let STALLOCAUX_partial_or_full_cons = prove
 (`!gen_sizes (xs:((A)stack_prog)list) ys. ~(gen_sizes:num list = []) ==>
    word_gc_partial_or_full gen_sizes xs ys =
    stack_list_Seq [stack_Get 8 TriggerGC; stack_Get 7 EndOfHeap;
                    stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Reg 8)));
                    stack_If NotLower 7 (Reg 1) (stack_list_Seq xs) (stack_list_Seq ys)]`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `gen_sizes:num list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; word_gc_partial_or_full_def] THEN CASE_REWRITE_TAC[]);;

let STALLOCAUX_partial_or_full_nil = prove
 (`!(xs:((A)stack_prog)list) ys.
    word_gc_partial_or_full ([]:num list) xs ys =
    stack_list_Seq (APPEND [stack_Get 8 TriggerGC; stack_Get 7 EndOfHeap;
                            stack_Inst (asm_Arith (Binop asm_Sub 7 7 (Reg 8)))] ys)`,
  REWRITE_TAC[word_gc_partial_or_full_def] THEN CASE_REWRITE_TAC[]);;

(* the evaluation of SetNewTrigger endh_reg ib_reg gs at the head of the     *)
(* first evaluation of the goal, by evaluate_SetNewTrigger (registers and   *)
(* AllocSize read from the state)                                           *)
let STALLOCAUX_SNT_TAC : tactic = fun (asl,w as g) ->
  let tm = stallocaux_find_ev w in
  let p,s5 = stallocaux_dest_ev tm in
  let snt = rand (rator p) in
  let _,sargs = strip_comb snt in
  let endh_reg = el 0 sargs and ib_reg = el 1 sargs and gsz = el 2 sargs in
  let ev = mk_icomb(`stack_evaluate:(A)stack_prog#(A,C,FFI)stack_state->
                       ((A)stack_result)option#(A,C,FFI)stack_state`, mk_pair(snt,s5)) in
  let facts = stallocaux_facts asl in
  let value t = rand(rand(rhs(concl(stallocaux_norm facts t)))) in
  let reg k = value (mk_icomb(mk_icomb(`FLOOKUP:(num,(A)word_loc)fmap->num->((A)word_loc)option`,
                mk_icomb(`stack_state_regs:(A,C,FFI)stack_state->(num,(A)word_loc)fmap`, s5)),k)) in
  let wv = value (mk_icomb(mk_icomb(
             `FLOOKUP:(store_name,(A)word_loc)fmap->store_name->((A)word_loc)option`,
             mk_icomb(`stack_state_store:(A,C,FFI)stack_state->(store_name,(A)word_loc)fmap`,
                      s5)), `AllocSize`)) in
  let fst_ev = mk_icomb(`FST:((A)stack_result)option#(A,C,FFI)stack_state->
                          ((A)stack_result)option`, ev) in
  let snd_ev = mk_icomb(`SND:((A)stack_result)option#(A,C,FFI)stack_state->
                          (A,C,FFI)stack_state`, ev) in
  let th0 = ISPECL [endh_reg; ib_reg; gsz; s5; fst_ev; snd_ev] evaluate_SetNewTrigger in
  let th1 = MP th0 (SYM (ISPEC ev PAIR)) in
  let th2 = SPECL [reg ib_reg; reg endh_reg; wv] th1 in
  (MP_TAC th2 THEN (ANTS_TAC THENL
     [CONV_TAC (stallocaux_norm facts) THEN REWRITE_TAC[ALL_DISTINCT; MEM] THEN
      CONV_TAC NUM_REDUCE_CONV THEN STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
   DISCH_THEN(X_CHOOSE_THEN `n7:(A)word_loc` (X_CHOOSE_THEN `n1:(A)word_loc`
     (X_CHOOSE_THEN `n4:(A)word_loc` (fun th ->
        let th3 = PURE_REWRITE_RULE[th] (SYM (ISPEC ev PAIR)) in
        STALLOCAUX_EV_KNOWN_TAC [th3]))))) g;;

let STALLOCAUX_word_add_sub_cancel2 = prove
 (`!x y:A word. word_sub (word_add x y) x = y`,
  CONV_TAC WORD_RULE);;

let () = stallocaux_add_rws [STALLOCAUX_word_add_sub_cancel2];;

(* the case split of the allocation result (r,t) of stackSem_alloc: the    *)
(* space check val w <= val x of the assumption (if ... ) = (r,t), the code *)
(* test word_ult x w, and r, t substituted                                  *)
let STALLOCAUX_ALLOC_CASES_TAC : tactic = fun (asl,w as g) ->
  let th = snd(find (fun (_,th) -> is_eq (concl th) && is_cond (lhs (concl th))) asl) in
  let cond,_ = dest_cond (lhs (concl th)) in
  let wv = rand (lhand cond) and x = rand (rand cond) in
  let ult = mk_icomb(mk_icomb(`word_ult:A word->A word->bool`,x),wv) in
  (ASM_CASES_TAC cond THENL
    [SUBGOAL_THEN (mk_neg ult) ASSUME_TAC THENL
      [REWRITE_TAC[WORD_ULT] THEN ASM_ARITH_TAC; ALL_TAC];
     SUBGOAL_THEN ult ASSUME_TAC THENL
      [REWRITE_TAC[WORD_ULT] THEN ASM_ARITH_TAC; ALL_TAC]] THEN
   FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_cond (lhs (concl th))
     then MP_TAC th else NO_TAC) THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM))) g;;

(* the branches where the allocation gives (SOME Error,s): MESON with the   *)
(* facts that mention stack_Error only (ASM_MESON_TAC took 13 s with the 43  *)
(* assumptions of the partial collection)                                    *)
let STALLOCAUX_ERROR_TAC : tactic = fun (asl,w as g) ->
  let is_err t = try fst(dest_const t) = "stack_Error" with Failure _ -> false in
  MESON_TAC (filter (fun th -> can (find_term is_err) (concl th)) (map snd asl)) g;;

(* HOL4 line 4592 *)
let alloc_correct_lemma_Generational = prove
 (`!w (s:(A,C,FFI)stack_state) r t conf gen_sizes l ret anything c.
   stackSem_alloc w s = (r,t) /\ ~(r = SOME stack_Error) /\
   stack_state_gc_fun s = word_gc_fun conf /\
   data_to_word_config_gc_kind conf = Generational gen_sizes /\
   LENGTH (stack_state_bitmaps s) < dimword (:A) - 1 /\
   LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
   FLOOKUP l 0 = SOME ret /\
   FLOOKUP l 1 = SOME (wl_Word w) ==>
   ?ck l2.
     stack_evaluate
       (word_gc_code conf,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_clock_fupd (K (stack_state_clock s + ck))
        (stack_state_regs_fupd (K l)
        (stack_state_gc_fun_fupd (K anything)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))) =
       (r,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))))
        (stack_state_regs_fupd (K l2)
        (stack_state_gc_fun_fupd (K anything) t)))))) /\
     (~(r = NONE) ==> r = SOME (stackSem_Halt (wl_Word (word 1)))) /\
     stack_state_regs t SUBMAP l2 /\
     (r = NONE ==> FLOOKUP l2 0 = SOME ret)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stackSem_alloc"
       with Failure _ -> false))) THEN
    REWRITE_TAC[stackSem_alloc_def] THEN
    MP_TAC(ISPECL [`conf:data_to_word_config`; `gen_sizes:num list`;
                   `stack_set_store AllocSize (wl_Word w) (s:(A,C,FFI)stack_state)`]
                  STALLOCAUX_gc_thm_gen) THEN
    (ANTS_TAC THENL [CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[];
                     DISCH_THEN SUBST1_TAC]) THEN
    CONV_TAC (stallocaux_norm []) THEN
    COND_CASES_TAC THENL
     [CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN STALLOCAUX_ERROR_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN STALLOCAUX_ERROR_TAC; ALL_TAC] THEN
    POP_ASSUM(MP_TAC o REWRITE_RULE[]) THEN
    REWRITE_TAC[word_gc_fun_assum_def; FDOM_FUPDATE; INSERT_SUBSET; IN_INSERT;
                FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
    STRIP_TAC THEN
    REWRITE_TAC[word_gen_gc_can_do_partial_def; LET_DEF; LET_END_DEF;
                FAPPLY_FUPDATE_THM; distinctness "store_name"; theWord_def] THEN
    MAP_EVERY (fun (k,n) ->
       STALLOCAUX_STORE_WORD_TAC `stack_state_store (s:(A,C,FFI)stack_state)` k n)
      [`OtherHeap`,"other"; `CurrHeap`,"curr"; `HeapLength`,"len"; `TriggerGC`,"trig";
       `GenStart`,"gs"; `EndOfHeap`,"endh"; `Globals`,"g"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[theWord_def]) THEN REWRITE_TAC[theWord_def]) THEN
  (MP_TAC(ISPECL [`stack_state_stack (s:(A,C,FFI)stack_state)`;
                   `stack_state_stack_space (s:(A,C,FFI)stack_state)`] LESS_EQ_LENGTH) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ys1:((A)word_loc)list` (X_CHOOSE_THEN `ys2:((A)word_loc)list`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                               lhs(concl th) = `stack_state_stack (s:(A,C,FFI)stack_state)`
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th
      else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && lhs(concl th) = `LENGTH (ys1:((A)word_loc)list)`
      then REWRITE_TAC[GSYM th] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
           ASSUME_TAC (GSYM th)
      else NO_TAC) THEN
    REWRITE_TAC[TAKE_LENGTH_APPEND; DROP_LENGTH_APPEND] THEN
    FIRST_ASSUM(fun th -> if concl th = `good_dimindex(:A)`
      then STRIP_ASSUME_TAC (MATCH_MP STALLOCAUX_good_dimindex_shift th) else NO_TAC) THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * LENGTH (APPEND ys1 (ys2:((A)word_loc)list)) <
                  dimword(:A)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC) THENL
  [(STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["w1";"i1";"pa1";"m1";"c1"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots_bitmaps" ["ws2";"i2";"pa2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_ref_list" ["i3";"pa3";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_data" ["i4";"pa4";"m4";"c4"] THEN
    STALLOCAUX_SPLIT_FN_TAC "memcpy" ["b1";"m5";"c5"] THEN
    COND_CASES_TAC THENL
     [ALL_TAC; CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN STALLOCAUX_ERROR_TAC] THEN
    CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[stack_has_space_def] THEN
    CONV_TAC (stallocaux_norm [])) THEN
  (POP_ASSUM STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `val (w:A word) <= val (new_trig (word_sub endh b1) w gen_sizes)`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[GSYM WORD_ULE]; ALL_TAC] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REPEAT (FIRST_X_ASSUM (fun th -> if is_var (concl th) then SUBST_ALL_TAC (EQT_INTRO th)
                                     else NO_TAC)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_partial_move_ref_list_ok o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_ref_list"
      with Failure _ -> false)) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (fun th -> if is_var (concl th) then SUBST_ALL_TAC (EQT_INTRO th)
                                     else NO_TAC)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `g1:A word` SUBST_ALL_TAC o
      MATCH_MP STALLOCAUX_word_gen_gc_partial_move_Word o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_partial_move_roots_bitmaps o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
          "word_gen_gc_partial_move_roots_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `ys2:((A)word_loc)list` ["h";"t"] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
    STALLOCAUX_ELIM_TAC [`ys2:((A)word_loc)list`]) THEN
  (REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    SUBGOAL_THEN `~(word_ult (word_sub endh trig) (w:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_NOT_LOWER]; ALL_TAC] THEN
    SUBGOAL_THEN `word_add len curr = word_add curr (len:A word) /\
                  word_add gs curr = word_add curr (gs:A word)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[WORD_ADD_SYM]; ALL_TAC] THEN
    REWRITE_TAC[word_gc_code_def;
                ASSUME `data_to_word_config_gc_kind conf = Generational gen_sizes`] THEN
    CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[STALLOCAUX_partial_or_full_cons] THEN
    STALLOCAUX_EV_TAC) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move" asl in
      (match args, res with
         [x;i;pa;old;m;dm;gs;rs], [w1;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`;x;i;pa;old;m;dm;gs;rs;w1;i1;pa1;m1;s0]
                    word_gen_gc_partial_move_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q6:(A)word_loc` ASSUME_TAC))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + ck2` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_roots_bitmaps" asl in
      (match args, res with
         [stk;bms;i;pa;curr;m;dm;gs;rs], [st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; stk; `ys1:((A)word_loc)list`; gs; rs; bms;
                          s0; i; pa; curr; m; dm; `[]:((A)word_loc)list`; st; `word 0:A word`;
                          i1; pa1; m1; `[]:((A)word_loc)list`]
                    word_gen_gc_partial_move_roots_bitmaps_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `u0:(A)word_loc`
      (X_CHOOSE_THEN `u1:(A)word_loc` (X_CHOOSE_THEN `u2:(A)word_loc`
      (X_CHOOSE_THEN `u5:(A)word_loc` (X_CHOOSE_THEN `u6:(A)word_loc`
      (X_CHOOSE_THEN `u7:(A)word_loc` (X_CHOOSE_THEN `u8:(A)word_loc`
      (X_CHOOSE_THEN `u9:(A)word_loc` ASSUME_TAC))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck4. ck3 + ck4` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck4:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
            "word_gen_gc_partial_move_ref_list"
        with Failure _ -> false) asl) in
      let k = hd (snd (strip_comb (lhs (concl th)))) in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_ref_list" asl in
      (match args, res with
         [pb;i;pa;old;m;dm;_;gs;rs;re], [i2;pa2;m2;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; gs; rs; k; re; pb; i; pa; old; m; dm;
                          i2; pa2; m2; s0] word_gen_gc_partial_move_ref_list_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck5:num` (X_CHOOSE_THEN `v0:(A)word_loc`
      (X_CHOOSE_THEN `v1:(A)word_loc` (X_CHOOSE_THEN `v2:(A)word_loc`
      (X_CHOOSE_THEN `v5:(A)word_loc` (X_CHOOSE_THEN `v6:(A)word_loc`
      (X_CHOOSE_THEN `v7:(A)word_loc` (X_CHOOSE_THEN `v8:(A)word_loc`
      (X_CHOOSE_THEN `v9:(A)word_loc` ASSUME_TAC))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck6. ck5 + ck6` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck6:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_data"
        with Failure _ -> false) asl) in
      let k = el 1 (snd (strip_comb (lhs (concl th)))) in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_data" asl in
      (match args, res with
         [ha;i;pa;old;m;dm;gs;rs], [i2;pa2;m2;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [`conf:data_to_word_config`; gs; rs; k; ha; i; pa;
                    old; m; dm; `T`; i2; pa2; m2; s0] word_gen_gc_partial_move_data_code_thm))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck7:num` (X_CHOOSE_THEN `x0:(A)word_loc`
      (X_CHOOSE_THEN `x1:(A)word_loc` (X_CHOOSE_THEN `x2:(A)word_loc`
      (X_CHOOSE_THEN `x5:(A)word_loc` (X_CHOOSE_THEN `x6:(A)word_loc`
      (X_CHOOSE_THEN `x7:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck8. ck7 + ck8` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck8:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "memcpy"
        with Failure _ -> false) asl) in
      let _,args = strip_comb (lhs (concl th)) in
      let b1,rest = dest_pair (rhs (concl th)) in
      let m1 = fst(dest_pair rest) in
      let ck10 = `ck10:num` in
      let f = mk_abs(ck10, mk_binop `(+):num->num->num` (mk_icomb(`val:A word->num`,hd args)) ck10) in
      (MP_TAC(ISPECL (args @ [b1; m1; s0]) memcpy_code_thm) THEN
       (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
       DISCH_THEN(X_CHOOSE_THEN `r1':(A)word_loc` ASSUME_TAC) THEN
       STALLOCAUX_CLOCK_FN_TAC f THEN CONV_TAC (stallocaux_norm []) THEN
       FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK ck10
         (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) g)) THEN
  (EXISTS_TAC `0` THEN CONV_TAC (stallocaux_norm []) THEN STALLOCAUX_SNT_TAC) THEN
  ((fun (asl,w as g) ->
       let _,body = dest_exists w in
       let eq = hd (conjuncts body) in
       let s1 = snd (dest_pair (lhs eq)) in
       EXISTS_TAC (rand (rand (rator s1))) g) THEN
    SUBGOAL_THEN `glob_real conf curr (wl_Word g1) =
                  wl_Word (word_add (word_mul (word_ushr g1 (shift_length conf)) bytes_in_word)
                                    (curr:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glob_real_def] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_ADD_SYM;
      ALL_TAC] THEN
    REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC);
   (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["w1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots_bitmaps" ["ws2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    COND_CASES_TAC THENL
     [ALL_TAC; CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN STALLOCAUX_ERROR_TAC] THEN
    CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[stack_has_space_def] THEN
    CONV_TAC (stallocaux_norm []) THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add x y) x = y:A word`] THEN
    POP_ASSUM STRIP_ASSUME_TAC THEN
    REPEAT (FIRST_X_ASSUM (fun th -> if is_var (concl th) then SUBST_ALL_TAC (EQT_INTRO th)
                                     else NO_TAC)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `g1:A word` SUBST_ALL_TAC o
      MATCH_MP STALLOCAUX_word_gen_gc_move_Word o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_move_roots_bitmaps o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_roots_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `ys2:((A)word_loc)list` ["h";"t"] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
    STALLOCAUX_ELIM_TAC [`ys2:((A)word_loc)list`]) THEN
  (SUBGOAL_THEN `word_add len other = word_add other (len:A word)` ASSUME_TAC THENL
     [MATCH_ACCEPT_TAC WORD_ADD_SYM; ALL_TAC] THEN
    REWRITE_TAC[word_gc_code_def;
                ASSUME `data_to_word_config_gc_kind conf = Generational gen_sizes`] THEN
    CASE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `gen_sizes:num list = []` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[STALLOCAUX_partial_or_full_nil; APPEND];
      SUBGOAL_THEN `word_ult (word_sub endh trig) (w:A word)` ASSUME_TAC THENL
       [UNDISCH_TAC `~(~(gen_sizes:num list = []) /\ word_ule w (word_sub endh (trig:A word)))` THEN
        ASM_REWRITE_TAC[GSYM WORD_NOT_LOWER];
        ALL_TAC] THEN
      ASM_SIMP_TAC[STALLOCAUX_partial_or_full_cons]] THEN
    STALLOCAUX_EV_TAC) THENL
  [(DISCH_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move" asl in
      (match args, res with
         [x;i;pa;ib;pb;old;m;dm], [w1;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`;x;i;pa;ib;pb;old;m;dm;w1;i1;pa1;ib1;pb1;m1;s0]
                    word_gen_gc_move_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q6:(A)word_loc` (X_CHOOSE_THEN `qt0:(A)word_loc`
      (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + ck2` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_roots_bitmaps" asl in
      (match args, res with
         [stk;bms;i;pa;ib;pb;curr;m;dm], [st;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; stk; `ys1:((A)word_loc)list`; bms; s0;
                          i; pa; ib; pb; curr; m; dm; `[]:((A)word_loc)list`; st; `word 0:A word`;
                          i1; pa1; ib1; pb1; m1; `[]:((A)word_loc)list`]
                    word_gen_gc_move_roots_bitmaps_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `u0:(A)word_loc`
      (X_CHOOSE_THEN `u1:(A)word_loc` (X_CHOOSE_THEN `u2:(A)word_loc`
      (X_CHOOSE_THEN `u5:(A)word_loc` (X_CHOOSE_THEN `u6:(A)word_loc`
      (X_CHOOSE_THEN `u7:(A)word_loc` (X_CHOOSE_THEN `u8:(A)word_loc`
      (X_CHOOSE_THEN `u9:(A)word_loc` (X_CHOOSE_THEN `ut0:(A)word_loc`
      (X_CHOOSE_THEN `ut1:(A)word_loc` ASSUME_TAC))))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck4. ck3 + ck4` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck4:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let facts = stallocaux_facts asl in
      let tt = rand(rand(rhs(concl(stallocaux_norm facts
                 (mk_icomb(mk_icomb(`FLOOKUP:(num,(A)word_loc)fmap->num->((A)word_loc)option`,
                   mk_icomb(`stack_state_regs:(A,C,FFI)stack_state->(num,(A)word_loc)fmap`, s0)),
                   `7`)))))) in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_loop"
        with Failure _ -> false) asl) in
      let k = el 1 (snd (strip_comb (lhs (concl th)))) in
      let args,res = stallocaux_assum_args "word_gen_gc_move_loop" asl in
      (match args, res with
         [pax;i;pa;ib;pb;pbx;old;m;dm], [i1;pa1;ib1;pb1;m1;_] ->
           SUBGOAL_THEN (mk_iff(mk_eq(tt,`word 0:A word`),mk_conj(mk_eq(pbx,pb),mk_eq(pax,pa))))
             ASSUME_TAC THENL
            [REWRITE_TAC[WORD_OR_EQ_0; WORD_SUB_EQ_0] THEN MESON_TAC[]; ALL_TAC] THEN
           MP_TAC(ISPECL [`conf:data_to_word_config`; k; pax; i; pa; ib; pb; pbx; old; m; dm;
                          i1; pa1; ib1; pb1; m1; tt; `T`; s0] word_gen_gc_move_loop_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck5:num` (X_CHOOSE_THEN `v0:(A)word_loc`
      (X_CHOOSE_THEN `v1:(A)word_loc` (X_CHOOSE_THEN `v2:(A)word_loc`
      (X_CHOOSE_THEN `v5:(A)word_loc` (X_CHOOSE_THEN `v6:(A)word_loc`
      (X_CHOOSE_THEN `v7:(A)word_loc` (X_CHOOSE_THEN `v8:(A)word_loc`
      (X_CHOOSE_THEN `vt0:(A)word_loc` (X_CHOOSE_THEN `vt1:(A)word_loc`
      (X_CHOOSE_THEN `vt4:(A)word_loc` (X_CHOOSE_THEN `vt5:(A)word_loc`
      (X_CHOOSE_THEN `vt6:(A)word_loc` ASSUME_TAC))))))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck6. ck5 + ck6` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck6:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  (EXISTS_TAC `0` THEN CONV_TAC (stallocaux_norm []) THEN STALLOCAUX_SNT_TAC) THEN
  (STALLOCAUX_ALLOC_CASES_TAC THEN STALLOCAUX_EV_TAC) THENL
  [((fun (asl,w as g) ->
       let _,body = dest_exists w in
       let eq = hd (conjuncts body) in
       let s1 = snd (dest_pair (lhs eq)) in
       EXISTS_TAC (rand (rand (rator s1))) g) THEN
    SUBGOAL_THEN `glob_real conf other (wl_Word g1) =
                  wl_Word (word_add (word_mul (word_ushr g1 (shift_length conf)) bytes_in_word)
                                    (other:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glob_real_def] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_ADD_SYM;
      ALL_TAC] THEN
    REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC);
   (EXISTS_TAC `FEMPTY:(num,(A)word_loc)fmap` THEN
    SUBGOAL_THEN `glob_real conf other (wl_Word g1) =
                  wl_Word (word_add (word_mul (word_ushr g1 (shift_length conf)) bytes_in_word)
                                    (other:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glob_real_def] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_ADD_SYM;
      ALL_TAC] THEN
    REWRITE_TAC[stack_empty_env_def] THEN
    CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY; option_DISTINCT]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC)];
   (DISCH_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move" asl in
      (match args, res with
         [x;i;pa;ib;pb;old;m;dm], [w1;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`;x;i;pa;ib;pb;old;m;dm;w1;i1;pa1;ib1;pb1;m1;s0]
                    word_gen_gc_move_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q6:(A)word_loc` (X_CHOOSE_THEN `qt0:(A)word_loc`
      (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + ck2` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_roots_bitmaps" asl in
      (match args, res with
         [stk;bms;i;pa;ib;pb;curr;m;dm], [st;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; stk; `ys1:((A)word_loc)list`; bms; s0;
                          i; pa; ib; pb; curr; m; dm; `[]:((A)word_loc)list`; st; `word 0:A word`;
                          i1; pa1; ib1; pb1; m1; `[]:((A)word_loc)list`]
                    word_gen_gc_move_roots_bitmaps_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `u0:(A)word_loc`
      (X_CHOOSE_THEN `u1:(A)word_loc` (X_CHOOSE_THEN `u2:(A)word_loc`
      (X_CHOOSE_THEN `u5:(A)word_loc` (X_CHOOSE_THEN `u6:(A)word_loc`
      (X_CHOOSE_THEN `u7:(A)word_loc` (X_CHOOSE_THEN `u8:(A)word_loc`
      (X_CHOOSE_THEN `u9:(A)word_loc` (X_CHOOSE_THEN `ut0:(A)word_loc`
      (X_CHOOSE_THEN `ut1:(A)word_loc` ASSUME_TAC))))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck4. ck3 + ck4` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck4:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let facts = stallocaux_facts asl in
      let tt = rand(rand(rhs(concl(stallocaux_norm facts
                 (mk_icomb(mk_icomb(`FLOOKUP:(num,(A)word_loc)fmap->num->((A)word_loc)option`,
                   mk_icomb(`stack_state_regs:(A,C,FFI)stack_state->(num,(A)word_loc)fmap`, s0)),
                   `7`)))))) in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_loop"
        with Failure _ -> false) asl) in
      let k = el 1 (snd (strip_comb (lhs (concl th)))) in
      let args,res = stallocaux_assum_args "word_gen_gc_move_loop" asl in
      (match args, res with
         [pax;i;pa;ib;pb;pbx;old;m;dm], [i1;pa1;ib1;pb1;m1;_] ->
           SUBGOAL_THEN (mk_iff(mk_eq(tt,`word 0:A word`),mk_conj(mk_eq(pbx,pb),mk_eq(pax,pa))))
             ASSUME_TAC THENL
            [REWRITE_TAC[WORD_OR_EQ_0; WORD_SUB_EQ_0] THEN MESON_TAC[]; ALL_TAC] THEN
           MP_TAC(ISPECL [`conf:data_to_word_config`; k; pax; i; pa; ib; pb; pbx; old; m; dm;
                          i1; pa1; ib1; pb1; m1; tt; `T`; s0] word_gen_gc_move_loop_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck5:num` (X_CHOOSE_THEN `v0:(A)word_loc`
      (X_CHOOSE_THEN `v1:(A)word_loc` (X_CHOOSE_THEN `v2:(A)word_loc`
      (X_CHOOSE_THEN `v5:(A)word_loc` (X_CHOOSE_THEN `v6:(A)word_loc`
      (X_CHOOSE_THEN `v7:(A)word_loc` (X_CHOOSE_THEN `v8:(A)word_loc`
      (X_CHOOSE_THEN `vt0:(A)word_loc` (X_CHOOSE_THEN `vt1:(A)word_loc`
      (X_CHOOSE_THEN `vt4:(A)word_loc` (X_CHOOSE_THEN `vt5:(A)word_loc`
      (X_CHOOSE_THEN `vt6:(A)word_loc` ASSUME_TAC))))))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck6. ck5 + ck6` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck6:num`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)])) THEN
  (EXISTS_TAC `0` THEN CONV_TAC (stallocaux_norm []) THEN STALLOCAUX_SNT_TAC) THEN
  (STALLOCAUX_ALLOC_CASES_TAC THEN STALLOCAUX_EV_TAC) THENL
  [((fun (asl,w as g) ->
       let _,body = dest_exists w in
       let eq = hd (conjuncts body) in
       let s1 = snd (dest_pair (lhs eq)) in
       EXISTS_TAC (rand (rand (rator s1))) g) THEN
    SUBGOAL_THEN `glob_real conf other (wl_Word g1) =
                  wl_Word (word_add (word_mul (word_ushr g1 (shift_length conf)) bytes_in_word)
                                    (other:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glob_real_def] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_ADD_SYM;
      ALL_TAC] THEN
    REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC);
   (EXISTS_TAC `FEMPTY:(num,(A)word_loc)fmap` THEN
    SUBGOAL_THEN `glob_real conf other (wl_Word g1) =
                  wl_Word (word_add (word_mul (word_ushr g1 (shift_length conf)) bytes_in_word)
                                    (other:A word))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[glob_real_def] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_ADD_SYM;
      ALL_TAC] THEN
    REWRITE_TAC[stack_empty_env_def] THEN
    CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY; option_DISTINCT]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC)]]]);;

(* HOL4 line 4984 *)
let filter_bitmap_map_bitmap_IMP = prove
 (`!x (ws:A list) q r x' q' q'' r''.
      filter_bitmap x ws = SOME (q,r) /\
      map_bitmap x (APPEND q x') ws = SOME (q',q'',r'') ==>
      q'' = x' /\ r = r'' /\ ws = APPEND q' r`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[filter_bitmap_def; map_bitmap_def; option_INJ; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN BOOL_CASES_TAC `h:bool` THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ws:A list` list_CASES) THEN
  REWRITE_TAC[filter_bitmap_def; option_DISTINCT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REMOVE_THEN "ih" (fun ih -> GVS[map_bitmap_def; APPEND; option_case_eq; pair_case_eq] THEN
                              ASSUME_TAC ih) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 4998 *)
let enc_dec_stack = prove
 (`!bs (ys2:((A)word_loc)list) x1 x2.
      stack_enc_stack bs ys2 = SOME x1 /\
      stack_dec_stack bs x1 ys2 = SOME x2 ==>
      ys2 = x2`,
  (MATCH_MP_TAC stack_enc_stack_ind THEN
    REWRITE_TAC[stack_enc_stack_def; option_DISTINCT] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
      STRIP_TAC THEN RVEQ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th))) THEN
      ASM_REWRITE_TAC[stack_dec_stack_def; option_INJ] THEN MESON_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "ih" (fun ih -> STRIP_TAC THEN
      GVS[option_case_eq; pair_case_eq; stack_dec_stack_def] THEN ASSUME_TAC ih) THEN
    FIRST_ASSUM(fun fth ->
      if can (term_match [] `filter_bitmap b (l:((A)word_loc)list) = SOME p`) (concl fth) then
        FIRST_ASSUM(fun mth ->
          if can (term_match [] `map_bitmap b (l:((A)word_loc)list) m = SOME p`) (concl mth)
          then MP_TAC(MATCH_MP filter_bitmap_map_bitmap_IMP (CONJ fth mth)) else NO_TAC)
      else NO_TAC) THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]));;

(* HOL4 line 5018 *)
let alloc_correct_lemma_None = prove
 (`!w (s:(A,C,FFI)stack_state) r t conf l ret anything c.
   stackSem_alloc w s = (r,t) /\ ~(r = SOME stack_Error) /\
   stack_state_gc_fun s = word_gc_fun conf /\
   data_to_word_config_gc_kind conf = data_to_word_None /\
   LENGTH (stack_state_bitmaps s) < dimword (:A) - 1 /\
   LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
   FLOOKUP l 0 = SOME ret /\
   FLOOKUP l 1 = SOME (wl_Word w) ==>
   ?ck l2.
     stack_evaluate
       (word_gc_code conf,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_clock_fupd (K (stack_state_clock s + ck))
        (stack_state_regs_fupd (K l)
        (stack_state_gc_fun_fupd (K anything)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))) =
       (r,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))))
        (stack_state_regs_fupd (K l2)
        (stack_state_gc_fun_fupd (K anything) t)))))) /\
     (~(r = NONE) ==> r = SOME (stackSem_Halt (wl_Word (word 1)))) /\
     stack_state_regs t SUBMAP l2 /\
     (r = NONE ==> FLOOKUP l2 0 = SOME ret)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stackSem_alloc"
       with Failure _ -> false))) THEN
    REWRITE_TAC[stackSem_alloc_def; stack_gc_def; stack_set_store_def] THEN
    CONV_TAC (stallocaux_norm []) THEN
    COND_CASES_TAC THENL
     [CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[word_gc_fun_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `stack_enc_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state))
                (DROP (stack_state_stack_space s) (stack_state_stack s))` ["wl"] THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL [STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [ALL_TAC; CASE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[]] THEN
    POP_ASSUM(MP_TAC o REWRITE_RULE[]) THEN
    REWRITE_TAC[word_gc_fun_assum_def; FDOM_FUPDATE; INSERT_SUBSET; IN_INSERT;
                FAPPLY_FUPDATE_THM; distinctness "store_name"] THEN
    STRIP_TAC THEN
    REWRITE_TAC[FAPPLY_FUPDATE_THM; distinctness "store_name"; theWord_def] THEN
    STALLOCAUX_STORE_WORD_TAC `stack_state_store (s:(A,C,FFI)stack_state)` `CurrHeap` "old" THEN
    REWRITE_TAC[theWord_def] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `stack_dec_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state)) wl
                (DROP (stack_state_stack_space s) (stack_state_stack s))` ["stk"] THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL [STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
      MP_TAC (MATCH_MP enc_dec_stack (CONJ th1 th2)))) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[TAKE_DROP] THEN
    CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[stack_has_space_def] THEN
    CONV_TAC (stallocaux_norm []) THEN
    REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0; LE; VAL_EQ_0] THEN
    ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[word_gc_code_def; ASSUME `data_to_word_config_gc_kind conf = data_to_word_None`] THEN
    CASE_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
       let _,body = dest_exists w in
       let eq = hd (conjuncts body) in
       let r1,s1 = dest_pair (lhs eq) in
       if r1 = `NONE:((A)stack_result)option` then EXISTS_TAC (rand (rand (rator s1))) g
       else EXISTS_TAC `FEMPTY:(num,(A)word_loc)fmap` g) THEN
    REWRITE_TAC[stack_empty_env_def] THEN
    CONV_TAC (stallocaux_norm [SUBMAP_FEMPTY; option_DISTINCT]) THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_ACCEPT_TAC TRUTH) THEN STALLOCAUX_STATE_EQ_TAC));;

(* HOL4 line 5078 *)
let alloc_correct_lemma = prove
 (`!w (s:(A,C,FFI)stack_state) r t conf l ret anything c.
   stackSem_alloc w s = (r,t) /\ ~(r = SOME stack_Error) /\
   stack_state_gc_fun s = word_gc_fun conf /\
   LENGTH (stack_state_bitmaps s) < dimword (:A) - 1 /\
   LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
   FLOOKUP l 0 = SOME ret /\
   FLOOKUP l 1 = SOME (wl_Word w) ==>
   ?ck l2.
     stack_evaluate
       (word_gc_code conf,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_clock_fupd (K (stack_state_clock s + ck))
        (stack_state_regs_fupd (K l)
        (stack_state_gc_fun_fupd (K anything)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))) =
       (r,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))))
        (stack_state_regs_fupd (K l2)
        (stack_state_gc_fun_fupd (K anything) t)))))) /\
     (~(r = NONE) ==> r = SOME (stackSem_Halt (wl_Word (word 1)))) /\
     stack_state_regs t SUBMAP l2 /\
     (r = NONE ==> FLOOKUP l2 0 = SOME ret)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `data_to_word_config_gc_kind conf` (cases "gc_kind")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `gen_sizes:num list`))) THENL
   [MATCH_MP_TAC alloc_correct_lemma_None THEN EXISTS_TAC `w:A word` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC alloc_correct_lemma_Simple THEN EXISTS_TAC `w:A word` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC alloc_correct_lemma_Generational THEN
    MAP_EVERY EXISTS_TAC [`w:A word`; `gen_sizes:num list`] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5107 (HOL4 writes use_alloc := F twice) *)
let alloc_correct = prove
 (`!w (s:(A,C,FFI)stack_state) r t c l n' m anything.
  stackSem_alloc w s = (r,t) /\ ~(r = SOME stack_Error) /\
  stack_state_gc_fun s = word_gc_fun c /\
  LENGTH (stack_state_bitmaps s) < dimword (:A) - 1 /\
  LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
  FLOOKUP l 1 = SOME (wl_Word w) ==>
  ?ck l2.
     stack_evaluate
       (stack_Call (SOME (stack_Skip,0,n',m)) (INL gc_stub_location) NONE,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_clock_fupd (K (stack_state_clock s + ck))
        (stack_state_regs_fupd (K l)
        (stack_state_gc_fun_fupd (K anything)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s)))))))) =
       (r,
        stack_state_use_store_fupd (K T)
        (stack_state_use_stack_fupd (K T)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_use_alloc_fupd (K F)
        (stack_state_code_fupd
           (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))))
        (stack_state_regs_fupd (K l2)
        (stack_state_gc_fun_fupd (K anything) t))))))) /\
     stack_state_regs t SUBMAP l2`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `stack_find_code (INL gc_stub_location) ((l:(num,(A)word_loc)fmap) \\ 0)
        (fromAList (stack_alloc_compile c (toAList (stack_state_code (s:(A,C,FFI)stack_state))))) =
        SOME (stack_Seq (word_gc_code c) (stack_Return 0))` ASSUME_TAC THENL
     [REWRITE_TAC[stack_find_code_def; lookup_fromAList; stack_alloc_compile_def; ALOOKUP_APPEND;
                  stack_alloc_stubs_def; ALOOKUP_DEF] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    (fun (asl,w as g) ->
       let any = find (fun v -> fst(dest_var v) = "anything") (frees w) in
       MP_TAC(ISPECL [`w:A word`; `s:(A,C,FFI)stack_state`; `r:((A)stack_result)option`;
                      `t:(A,C,FFI)stack_state`; `c:data_to_word_config`;
                      `l |+ (0,wl_Loc n' m:(A)word_loc)`; `wl_Loc n' m:(A)word_loc`; any;
                      `c:data_to_word_config`] alloc_correct_lemma) g) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN CONV_TAC NUM_REDUCE_CONV THEN
                     ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `l2:(num,(A)word_loc)fmap`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck + 1`; `l2:(num,(A)word_loc)fmap`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "stack_Call"] THEN CASE_REWRITE_TAC[] THEN
    CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"] THEN
    FIRST_X_ASSUM(fun th -> if can stallocaux_dest_ev (lhs(concl th))
      then REWRITE_TAC[CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV (stallocaux_norm [])))) th]
      else NO_TAC) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; stack_fix_clock_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r:((A)stack_result)option = NONE` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      REWRITE_TAC[STALLOCAUX_ev_clause "stack_Return"] THEN CONV_TAC (stallocaux_norm []) THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[STALLOCAUX_ev_clause "stack_Skip"] THEN CONV_TAC (stallocaux_norm []);
      FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_neg (lhand (concl th))
        then SUBST_ALL_TAC (MP th (ASSUME `~(r:((A)stack_result)option = NONE)`)) else NO_TAC) THEN
      REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm [])]));;

(* HOL4 line 5137 *)
let find_code_IMP_lookup = prove
 (`!dest (regs:(num,(A)word_loc)fmap) (s:(B)spt) x.
     stack_find_code dest regs s = SOME x ==>
     ?k. lookup k s = SOME x /\ stack_find_code dest regs = (lookup k:(B)spt->B option)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dest:num+num` (cases "sum")) THEN
  REWRITE_TAC[stack_find_code_def; FUN_EQ_THM] THEN REPEAT GEN_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  STALLOCAUX_OPT_CASES_TAC `FLOOKUP (regs:(num,(A)word_loc)fmap) a` ["v"] THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  STRUCT_CASES_TAC(ISPEC `v:(A)word_loc` (cases "word_loc")) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[]);;

(* HOL4 line 5146 *)
let alloc_length_stack = prove
 (`!c (s:(A,C,FFI)stack_state) r t conf.
   stackSem_alloc c s = (r,t) /\ stack_state_gc_fun s = word_gc_fun conf /\
   (!w. ~(r = SOME (stackSem_Halt w))) ==>
   LENGTH (stack_state_stack t) = LENGTH (stack_state_stack s)`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[stackSem_alloc_def; stack_gc_def; stack_set_store_def] THEN
    CONV_TAC (stallocaux_norm []) THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THENL
     [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `stack_enc_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state))
                (DROP (stack_state_stack_space s) (stack_state_stack s))` ["wl"] THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      is_pair (rhs (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `word_gc_fun conf (wl,stack_state_memory (s:(A,C,FFI)stack_state),
       stack_state_mdomain s,stack_state_store s |+ (AllocSize,wl_Word c))` ["wl2";"m2";"st2"] THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    STALLOCAUX_OPT_CASES_TAC `stack_dec_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state)) wl2
                (DROP (stack_state_stack_space s) (stack_state_stack s))` ["stk"] THEN
    CASE_REWRITE_TAC[PAIR_EQ] THENL [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (stk:((A)word_loc)list) =
                  LENGTH (DROP (stack_state_stack_space s) (stack_state_stack (s:(A,C,FFI)stack_state)))`
      ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP dec_stack_length o
        check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_dec_stack"
                         with Failure _ -> false));
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (APPEND (TAKE (stack_state_stack_space s) (stack_state_stack s))
                    (stk:((A)word_loc)list)) = LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_TAKE_EQ; LENGTH_DROP] THEN
      UNDISCH_TAC `~(LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) < stack_state_stack_space s)` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC (stallocaux_norm []) THEN
    STALLOCAUX_OPT_CASES_TAC `FLOOKUP (st2:(store_name,(A)word_loc)fmap) AllocSize` ["aw"] THEN
    CASE_REWRITE_TAC[PAIR_EQ] THEN
    TRY (STALLOCAUX_OPT_CASES_TAC `stack_has_space aw (st2:(store_name,(A)word_loc)fmap)` ["b"] THEN
         CASE_REWRITE_TAC[PAIR_EQ]) THEN
    TRY (COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ]) THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    TRY (FIRST_X_ASSUM(MP_TAC o SPEC `wl_Word (word 1):(A)word_loc`) THEN REWRITE_TAC[] THEN
         NO_TAC) THEN
    CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LENGTH_APPEND; TAKE_DROP]));;

(* HOL4 line 5159 *)
let find_code_regs_SUBMAP = prove
 (`!(r1:(num,(A)word_loc)fmap) r2 dest (c:(B)spt) x.
     r1 SUBMAP r2 /\ stack_find_code dest r1 c = SOME x ==>
     stack_find_code dest r2 c = SOME x`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `dest:num+num` (cases "sum")) THEN
  REWRITE_TAC[stack_find_code_def] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  STALLOCAUX_OPT_CASES_TAC `FLOOKUP (r1:(num,(A)word_loc)fmap) a` ["v"] THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FLOOKUP (r2:(num,(A)word_loc)fmap) a = SOME v` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[FLOOKUP_SUBMAP]; CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]]);;

(* for each split comp n m x = (q,m') in the assumptions: get_labels x is   *)
(* a subset of get_labels q, from the induction hypotheses (by MESON)       *)
let STALLOCAUX_COMP_IH_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun (_,th) ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "stack_alloc_comp"
    with Failure _ -> false) asl in
  let lab t = mk_icomb(`stack_get_labels:(A)stack_prog->num#num->bool`, t) in
  let mk (_,th) =
    let x = rand (lhs (concl th)) and q = fst(dest_pair(rhs(concl th))) in
    mk_icomb(mk_icomb(`(SUBSET):(num#num->bool)->(num#num->bool)->bool`, lab x), lab q) in
  MAP_EVERY (fun e -> SUBGOAL_THEN (mk e) ASSUME_TAC THENL [ASM_MESON_TAC[FST]; ALL_TAC])
    eqs g;;

(* HOL4 line 5170 (HOL4 get_labels_comp) *)
let stack_allocProof_get_labels_comp = prove
 (`!n m (e:(A)stack_prog). stack_get_labels e SUBSET stack_get_labels (FST (stack_alloc_comp n m e))`,
  (MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (ISPEC `p:(A)stack_prog` (CONJUNCT1 (cases "stack_prog"))) THEN
    REWRITE_TAC[injectivity "stack_prog"; distinctness "stack_prog"] THEN
    REWRITE_TAC[LEFT_FORALL_IMP_THM; RIGHT_FORALL_IMP_THM; UNWIND_THM1; UNWIND_THM2;
                GSYM CONJ_ASSOC; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[stack_get_labels_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    TRY (MATCH_ACCEPT_TAC EMPTY_SUBSET) THEN
    REPEAT (STALLOCAUX_SPLIT_FN_TAC "stack_alloc_comp" ["q";"mm"]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN REWRITE_TAC[FST; stack_get_labels_def] THEN
    CASE_REWRITE_TAC[] THEN TRY (MATCH_ACCEPT_TAC EMPTY_SUBSET) THEN
    TRY (STALLOCAUX_OPT_CASES_TAC `a0:((A)stack_prog#num#num#num)option` ["p1";"lr";"l1";"l2"]) THEN
    TRY (STALLOCAUX_OPT_CASES_TAC `a2:((A)stack_prog#num#num)option` ["p2";"k1";"k2"]) THEN
    CASE_REWRITE_TAC[] THEN
    REPEAT (STALLOCAUX_SPLIT_FN_TAC "stack_alloc_comp" ["q";"mm"]) THEN
    REWRITE_TAC[FST; stack_get_labels_def] THEN CASE_REWRITE_TAC[] THEN
    TRY (MATCH_ACCEPT_TAC EMPTY_SUBSET) THEN
    STALLOCAUX_COMP_IH_TAC THEN ASM SET_TAC[]));;

(* HOL4 line 5278 (hoisted: loc_check_compile, HOL4 line 5182, uses it) *)
let ALOOKUP_prog_comp = prove
 (`!xs a (y:(A)stack_prog).
    ALOOKUP xs a = SOME y ==>
    ALOOKUP (MAP stack_alloc_prog_comp xs) a = SOME (FST (stack_alloc_comp a (next_lab y 2) y))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; MAP; option_DISTINCT; FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?n:num p:(A)stack_prog. h = (n,p)` (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  REWRITE_TAC[stack_alloc_prog_comp_def; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5182 *)
let loc_check_compile = prove
 (`!(s:(A,C,FFI)stack_state) c l1 l2.
    loc_check (stack_state_code s) (l1,l2) /\
    (!k prog. lookup k (stack_state_code s) = SOME prog ==> ~(k = gc_stub_location)) ==>
    loc_check (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))) (l1,l2)`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[loc_check_def; domain_lookup; lookup_fromAList] THEN
    REWRITE_TAC[stack_alloc_compile_def; ALOOKUP_APPEND; stack_alloc_stubs_def; ALOOKUP_DEF] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE] THENL
       [MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `FST (stack_alloc_comp l1 (next_lab (v:(A)stack_prog) 2) v)` THEN
      MATCH_MP_TAC ALOOKUP_prog_comp THEN ASM_REWRITE_TAC[ALOOKUP_toAList];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC
        [`n:num`; `FST (stack_alloc_comp n (next_lab (e:(A)stack_prog) 2) e)`] THEN
      SUBGOAL_THEN `~(gc_stub_location = n)` (fun th -> REWRITE_TAC[th; option_CASE]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ALOOKUP_prog_comp THEN ASM_REWRITE_TAC[ALOOKUP_toAList];
        ASM_MESON_TAC[stack_allocProof_get_labels_comp; SUBSET]]]));;

(* HOL4 line 5206 *)
let SUBMAP_DOMSUB_both = prove
 (`!(f:(A,B)fmap) g c. f SUBMAP g ==> f \\ c SUBMAP g \\ c`,
  REWRITE_TAC[GSYM SUBMAP_DOMSUB_gen] THEN MESON_TAC[SUBMAP_TRANS; SUBMAP_DOMSUB]);;

(* HOL4 line 5214 *)
let SUBMAP_FUPDATE_both = prove
 (`!(f:(A,B)fmap) g n v. f SUBMAP g ==> f |+ (n,v) SUBMAP g |+ (n,v)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBMAP_mono_FUPDATE THEN
  ASM_SIMP_TAC[SUBMAP_DOMSUB_both]);;

(* extending the registers of a state: run with the registers             *)
(* FUNION (stack_state_regs s) ext, a state computes the same as s does     *)

let STALLOCAUX_rx_word_exp = prove
 (`!(s:(A,C,FFI)stack_state) e w ext.
     stack_word_exp s e = SOME w ==>
     stack_word_exp (stack_state_regs_fupd (K (FUNION (stack_state_regs s) ext)) s) e = SOME w`,
  (MATCH_MP_TAC stack_word_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC[stack_word_exp_def];
      REWRITE_TAC[stack_word_exp_def] THEN CONV_TAC (stallocaux_norm []) THEN
      REWRITE_TAC[FLOOKUP_FUNION] THEN
      STALLOCAUX_OPT_CASES_TAC `FLOOKUP (stack_state_regs (s:(A,C,FFI)stack_state)) s'` ["x"] THEN
      CASE_REWRITE_TAC[option_DISTINCT];
      REWRITE_TAC[stack_word_exp_def] THEN CONV_TAC (stallocaux_norm []);
      DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
      STALLOCAUX_OPT_CASES_TAC `stack_word_exp (s:(A,C,FFI)stack_state) addr` ["a"] THEN
      CASE_REWRITE_TAC[option_DISTINCT] THEN
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `stack_word_exp (s:(A,C,FFI)stack_state) addr = SOME a`)]) THEN
      CASE_REWRITE_TAC[stack_mem_load_def] THEN CONV_TAC (stallocaux_norm []);
      ALL_TAC;
      ALL_TAC]) THENL
  [(DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `MAP (stack_word_exp (stack_state_regs_fupd (K (FUNION (stack_state_regs s) ext))
                      (s:(A,C,FFI)stack_state))) wexps = MAP (stack_word_exp s) wexps`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `a:(A)wl_exp` THEN DISCH_TAC THEN
    UNDISCH_TAC `ALL IS_SOME (MAP (stack_word_exp (s:(A,C,FFI)stack_state)) wexps)` THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a:(A)wl_exp`) THEN ASM_REWRITE_TAC[IS_SOME_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_TAC `v:A word`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)wl_exp`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`v:A word`; `ext:(num,(A)word_loc)fmap`]) THEN
    ASM_REWRITE_TAC[]);
   (STRIP_TAC THEN GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[stack_word_exp_def] THEN
    STALLOCAUX_OPT_CASES_TAC `stack_word_exp (s:(A,C,FFI)stack_state) wexp` ["a"] THEN
    STALLOCAUX_OPT_CASES_TAC `stack_word_exp (s:(A,C,FFI)stack_state) wexp1` ["b"] THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN
    RES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])]);;

(* the same for the states of inst_correct: registers extended, the        *)
(* compiler fields, gc_fun, use_* and code changed                          *)
let STALLOCAUX_rx_word_exp_big = prove
 (`!(s:(A,C,FFI)stack_state) e w ext cr
     (f:C#(num#(A)stack_prog)list#(A word)list->C#(num#(A)stack_prog)list#(A word)list) gcf cf.
     stack_word_exp s e = SOME w ==>
     stack_word_exp
       (stack_state_regs_fupd (K (FUNION (stack_state_regs s) ext))
       (stack_state_compile_fupd (K cr)
       (stack_state_compile_oracle_fupd (K (f o stack_state_compile_oracle s))
       (stack_state_gc_fun_fupd (K gcf)
       (stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_code_fupd (K (cf (stack_state_code s))) s)))))))) e = SOME w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `ext:(num,(A)word_loc)fmap` o MATCH_MP STALLOCAUX_rx_word_exp) THEN
  MATCH_MP_TAC(MESON[] `(a:(A word)option) = b ==> a = SOME (w:A word) ==> b = SOME w`) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC STACKPROPSAUX_word_exp_frame THEN
  CONV_TAC (stallocaux_norm []));;
let STALLOCAUX_rx_get_var_big = prove
 (`!r (s:(A,C,FFI)stack_state) v ext cr
     (f:C#(num#(A)stack_prog)list#(A word)list->C#(num#(A)stack_prog)list#(A word)list) gcf cf.
     stack_get_var r s = SOME v ==>
     stack_get_var r
       (stack_state_regs_fupd (K (FUNION (stack_state_regs s) ext))
       (stack_state_compile_fupd (K cr)
       (stack_state_compile_oracle_fupd (K (f o stack_state_compile_oracle s))
       (stack_state_gc_fun_fupd (K gcf)
       (stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_code_fupd (K (cf (stack_state_code s))) s)))))))) = SOME v`,
  REWRITE_TAC[stack_get_var_def] THEN CONV_TAC (stallocaux_norm []) THEN
  REWRITE_TAC[FLOOKUP_FUNION] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[]);;

let STALLOCAUX_rx_get_vars_big = prove
 (`!xs (s:(A,C,FFI)stack_state) vs ext cr
     (f:C#(num#(A)stack_prog)list#(A word)list->C#(num#(A)stack_prog)list#(A word)list) gcf cf.
     stack_get_vars xs s = SOME vs ==>
     stack_get_vars xs
       (stack_state_regs_fupd (K (FUNION (stack_state_regs s) ext))
       (stack_state_compile_fupd (K cr)
       (stack_state_compile_oracle_fupd (K (f o stack_state_compile_oracle s))
       (stack_state_gc_fun_fupd (K gcf)
       (stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_code_fupd (K (cf (stack_state_code s))) s)))))))) = SOME vs`,
  (LIST_INDUCT_TAC THEN REWRITE_TAC[stack_get_vars_def] THEN REPEAT GEN_TAC THEN
    STALLOCAUX_OPT_CASES_TAC `stack_get_var h (s:(A,C,FFI)stack_state)` ["v"] THEN
    CASE_REWRITE_TAC[option_DISTINCT]) THEN
  (STALLOCAUX_OPT_CASES_TAC `stack_get_vars t (s:(A,C,FFI)stack_state)` ["vs1"] THEN
    CASE_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[STALLOCAUX_rx_get_var_big] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`s:(A,C,FFI)stack_state`; `vs1:((A)word_loc)list`; `ext:(num,(A)word_loc)fmap`;
       `cr:C->(num#(A)stack_prog)list->(byte list#C)option`;
       `f:C#(num#(A)stack_prog)list#(A word)list->C#(num#(A)stack_prog)list#(A word)list`;
       `gcf:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#(store_name,(A)word_loc)fmap->
            (((A)word_loc)list#(A word->(A)word_loc)#(store_name,(A)word_loc)fmap)option`;
       `cf:((A)stack_prog)spt->((A)stack_prog)spt`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[]));;

let STALLOCAUX_rx_mem_store_big = prove
 (`!a w (s:(A,C,FFI)stack_state) t ext cr
     (f:C#(num#(A)stack_prog)list#(A word)list->C#(num#(A)stack_prog)list#(A word)list) gcf cf.
     stack_mem_store a w s = SOME t ==>
     stack_mem_store a w
       (stack_state_regs_fupd (K (FUNION (stack_state_regs s) ext))
       (stack_state_compile_fupd (K cr)
       (stack_state_compile_oracle_fupd (K (f o stack_state_compile_oracle s))
       (stack_state_gc_fun_fupd (K gcf)
       (stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_code_fupd (K (cf (stack_state_code s))) s)))))))) =
     SOME
       (stack_state_regs_fupd (K (FUNION (stack_state_regs t) ext))
       (stack_state_compile_fupd (K cr)
       (stack_state_compile_oracle_fupd (K (f o stack_state_compile_oracle t))
       (stack_state_gc_fun_fupd (K gcf)
       (stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_code_fupd (K (cf (stack_state_code t))) t))))))))`,
  REWRITE_TAC[stack_mem_store_def] THEN CONV_TAC (stallocaux_norm []) THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC (stallocaux_norm []));;
let STALLOCAUX_inst_big = prove
 (`!(i:(A)inst) (s:(A,C,FFI)stack_state) t ext cr (f:C#(num#(A)stack_prog)list#(A word)list->C#(num#(A)stack_prog)list#(A word)list) gcf cf.
     stack_inst i s = SOME t ==>
     stack_inst i
       (stack_state_regs_fupd (K (FUNION (stack_state_regs s) ext))
       (stack_state_compile_fupd (K cr)
       (stack_state_compile_oracle_fupd (K (f o stack_state_compile_oracle s))
       (stack_state_gc_fun_fupd (K gcf)
       (stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_code_fupd (K (cf (stack_state_code s))) s)))))))) =
     SOME
       (stack_state_regs_fupd (K (FUNION (stack_state_regs t) ext))
       (stack_state_compile_fupd (K cr)
       (stack_state_compile_oracle_fupd (K (f o stack_state_compile_oracle t))
       (stack_state_gc_fun_fupd (K gcf)
       (stack_state_use_stack_fupd (K T)
       (stack_state_use_store_fupd (K T)
       (stack_state_use_alloc_fupd (K F)
       (stack_state_code_fupd (K (cf (stack_state_code t))) t))))))))`,
  (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [stack_inst_def] THEN
    REWRITE_TAC[stack_assign_def] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[stack_inst_def] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[stack_assign_def] THEN
    (fun (asl,w) -> MAP_EVERY (fun (_,th) ->
        try ASSUME_TAC (MATCH_MP STALLOCAUX_rx_word_exp_big th) with Failure _ ->
        try ASSUME_TAC (MATCH_MP STALLOCAUX_rx_get_var_big th) with Failure _ ->
        try ASSUME_TAC (MATCH_MP STALLOCAUX_rx_get_vars_big th) with Failure _ ->
        try ASSUME_TAC (MATCH_MP STALLOCAUX_rx_mem_store_big th) with Failure _ -> ALL_TAC)
        asl (asl,w)) THEN
    REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
    REWRITE_TAC[stack_get_vars_def; stack_get_var_def; stack_get_fp_var_def; stack_mem_load_def;
                stack_mem_store_def; stack_set_var_def; stack_set_fp_var_def] THEN
    CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[FLOOKUP_FUNION] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_fp_var_def; stack_mem_load_def]) THEN
    REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
    CONV_TAC (stallocaux_norm []) THEN
    REWRITE_TAC[FUNION_FUPDATE_1]));;

let STALLOCAUX_inst_stack_buffer = prove
 (`!(i:(A)inst) (s:(A,C,FFI)stack_state) t.
     stack_inst i s = SOME t ==>
     stack_state_stack t = stack_state_stack s /\
     stack_state_data_buffer t = stack_state_data_buffer s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_inst_def; stack_assign_def; stack_mem_store_def; stack_set_var_def;
              stack_set_fp_var_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT ((TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN REWRITE_TAC[option_DISTINCT]) THEN
  REWRITE_TAC[option_INJ] THEN
  TRY (FIRST_X_ASSUM(fun th -> if is_cond(lhs(concl th)) &&
                              (try fst(dest_const(rator(rhs(concl th)))) = "SOME"
                               with Failure _ -> false)
                           then MP_TAC th else failwith "") THEN
       COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ]) THEN
  REPEAT (DISCH_THEN(SUBST1_TAC o SYM)) THEN CONV_TAC (stallocaux_norm []));;

(* HOL4 line 5223 *)
let stack_allocProof_inst_correct = prove
 (`!(i:(A)inst) (s:(A,C,FFI)stack_state) t regs compile_rest anything c.
     stack_inst i s = SOME t /\
     LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     LENGTH (buffer_buffer (stack_state_data_buffer s)) +
       (LENGTH (stack_state_bitmaps s) + buffer_space_left (stack_state_data_buffer s)) <
       dimword (:A) - 1 /\
     stack_state_regs s SUBMAP regs ==>
     ?regs1.
       stack_inst i
         (stack_state_regs_fupd (K regs)
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle s))
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_store_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s)))))))) =
       SOME
         (stack_state_regs_fupd (K regs1)
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle t))
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_store_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code t))))) t)))))))) /\
       stack_state_regs t SUBMAP regs1 /\
       LENGTH (stack_state_stack t) * (dimindex (:A) DIV 8) < dimword (:A) /\
       LENGTH (buffer_buffer (stack_state_data_buffer t)) +
         (LENGTH (stack_state_bitmaps t) + buffer_space_left (stack_state_data_buffer t)) <
         dimword (:A) - 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STALLOCAUX_inst_stack_buffer) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP stack_inst_const) THEN
  EXISTS_TAC `FUNION (stack_state_regs (t:(A,C,FFI)stack_state)) regs` THEN
  ASM_REWRITE_TAC[SUBMAP_FUNION_ID] THEN
  SUBGOAL_THEN `FUNION (stack_state_regs (s:(A,C,FFI)stack_state)) regs = regs` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SUBMAP_FUNION_ABSORPTION]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`i:(A)inst`; `s:(A,C,FFI)stack_state`; `t:(A,C,FFI)stack_state`;
     `regs:(num,(A)word_loc)fmap`;
     `compile_rest:C->(num#(A)stack_prog)list->(byte list#C)option`;
     `(I ## MAP stack_alloc_prog_comp ## I):
        C#(num#(A)stack_prog)list#(A word)list->C#(num#(A)stack_prog)list#(A word)list`;
     `anything:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                (store_name,(A)word_loc)fmap->
                (((A)word_loc)list#(A word->(A)word_loc)#(store_name,(A)word_loc)fmap)option`;
     `\x:((A)stack_prog)spt. fromAList (stack_alloc_compile c (toAList x))`]
    STALLOCAUX_inst_big) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5287 *)
let lookup_fromAList_prog_comp = prove
 (`!x (s:(A,C,FFI)stack_state) p.
     lookup x (stack_state_code s) = SOME p ==>
     lookup x (fromAList (MAP stack_alloc_prog_comp (toAList (stack_state_code s)))) =
     SOME (FST (stack_alloc_comp x (next_lab p 2) p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_fromAList] THEN
  MATCH_MP_TAC ALOOKUP_prog_comp THEN ASM_REWRITE_TAC[ALOOKUP_toAList]);;

(* comp_correct (HOL4 line 5297): the induction predicate and its cases *)
let STALLOCAUX_cc_P =
 `\(p:(A)stack_prog,s:(A,C,FFI)stack_state).
  !r t m n c regs.
     stack_evaluate (p,s) = (r,t) /\ ~(r = SOME stack_Error) /\ alloc_arg p /\
     (!k prog. lookup k (stack_state_code s) = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (stack_state_compile_oracle s n))) ==>
              ~(k = gc_stub_location) /\ alloc_arg p) /\
     stack_state_gc_fun s = word_gc_fun c /\ stack_state_use_alloc s /\
     LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     stack_state_regs s SUBMAP regs /\
     stack_state_use_stack s /\
     (LENGTH (stack_state_bitmaps s) + LENGTH (buffer_buffer (stack_state_data_buffer s))) +
       buffer_space_left (stack_state_data_buffer s) < dimword (:A) - 1 /\
     stack_state_compile s =
       (\c. (compile_rest:C->(num#(A)stack_prog)list->(byte list#C)option) c o
            MAP stack_alloc_prog_comp)
     ==>
     ?ck regs1.
       stack_evaluate (FST (stack_alloc_comp n m p),
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_clock_fupd (K (stack_state_clock s + ck))
         (stack_state_regs_fupd (K regs)
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle s))
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))))) =
       (r,
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_regs_fupd (K regs1)
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle t))
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code t))))) t)))))))) /\
       stack_state_regs t SUBMAP regs1 /\
       (LENGTH (stack_state_bitmaps t) + LENGTH (buffer_buffer (stack_state_data_buffer t))) +
         buffer_space_left (stack_state_data_buffer t) < dimword (:A) - 1 /\
       ((!w. ~(r = SOME (stackSem_Halt w))) ==>
        LENGTH (stack_state_stack t) * (dimindex (:A) DIV 8) < dimword (:A))`;;

let STALLOCAUX_cc_ind =
  CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (ISPEC STALLOCAUX_cc_P stack_evaluate_ind);;

let stallocaux_cc_case i = el i (conjuncts (lhand (concl STALLOCAUX_cc_ind)));;

let STALLOCAUX_word_exp_sub = prove
 (`!(s:(A,C,FFI)stack_state) e w (t:(A,C,FFI)stack_state).
     stack_word_exp s e = SOME w /\
     stack_state_regs s SUBMAP stack_state_regs t /\
     stack_state_store t = stack_state_store s /\
     stack_state_memory t = stack_state_memory s /\
     stack_state_mdomain t = stack_state_mdomain s ==>
     stack_word_exp t e = SOME w`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `stack_state_regs (t:(A,C,FFI)stack_state)` o
                MATCH_MP STALLOCAUX_rx_word_exp) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBMAP_FUNION_ABSORPTION]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `(a:(A word)option) = b ==> a = SOME (w:A word) ==> b = SOME w`) THEN
  MATCH_MP_TAC STACKPROPSAUX_word_exp_frame THEN CONV_TAC (stallocaux_norm []) THEN
  ASM_REWRITE_TAC[]);;

(* the definitions unfolded in the simple cases of comp_correct *)

let STALLOCAUX_cc_defs =
  [stack_get_var_def; stack_set_var_def; stack_set_store_def; stack_empty_env_def;
   stack_dec_clock_def; stack_unset_var_def; LET_DEF; LET_END_DEF];;

let stallocaux_is_ev_eq tm =
  is_eq tm && (try fst(dest_const(fst(strip_comb(lhs tm)))) = "stack_evaluate"
               with Failure _ -> false);;

(* split the cases of the antecedent of the goal A ==> C, C without cases *)

let STALLOCAUX_CC_SPLIT_TAC : tactic =
  REPEAT ((TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
          ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ;
                          distinctness "stack_result"; injectivity "stack_result";
                          distinctness "word_loc"; injectivity "word_loc"]);;

(* a leaf r0 = r /\ t0 = t ==> C: substitute, refute r0 = SOME Error *)

let STALLOCAUX_CC_WIT_TAC : tactic = fun (asl,w as g) ->
  let v,bod = dest_exists w in
  let eq = hd(conjuncts bod) in
  let l = lhs eq in
  let x = if is_pair l then snd(dest_pair l) else l in
  let acc = mk_icomb(`stack_state_regs:(A,C,FFI)stack_state->(num,(A)word_loc)fmap`,x) in
  let r = rhs(concl(stallocaux_norm [] acc)) in
  EXISTS_TAC r g;;

let STALLOCAUX_CC_LOOKUPS_TAC : tactic = fun (asl,w as g) ->
  let sub = try snd(find (fun (_,th) ->
                   try fst(dest_const(fst(strip_comb(concl th)))) = "SUBMAP" &&
                       (let a = lhand(concl th) in
                        fst(dest_const(fst(strip_comb a))) = "stack_state_regs")
                   with Failure _ -> false) asl)
            with Failure _ -> failwith "STALLOCAUX_CC_LOOKUPS_TAC: no SUBMAP" in
  let news = mapfilter (fun (_,th) ->
      MATCH_MP FLOOKUP_SUBMAP (CONJ sub th)) asl in
  MAP_EVERY ASSUME_TAC news g;;

let STALLOCAUX_clock_code_id = prove
 (`!f (s:(A,C,FFI)stack_state).
     stack_state_clock_fupd (K (stack_state_clock s)) (stack_state_code_fupd f s) =
     stack_state_code_fupd f s`,
  REWRITE_TAC[stack_state_component_equality] THEN CONV_TAC (stallocaux_norm []));;

let () = stallocaux_add_rws [STALLOCAUX_clock_code_id];;

let STALLOCAUX_buffer_write_len = prove
 (`!(b:(A,B)buffer) w x b'.
     buffer_write b w x = SOME b' ==>
     LENGTH (buffer_buffer b') + buffer_space_left b' =
     LENGTH (buffer_buffer b) + buffer_space_left b`,
  REWRITE_TAC[buffer_write_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP[LENGTH_APPEND; LENGTH] THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

let stallocaux_head_is name tm =
  try fst(dest_const(fst(strip_comb tm))) = name with Failure _ -> false;;

(* a leaf r0 = r /\ t0 = t ==> C: substitute, refute r0 = SOME Error, split *)
(* the assumptions                                                          *)

let STALLOCAUX_CC_LEAF_TAC : tactic =
  TRY (DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; distinctness "stack_result";
                              injectivity "stack_result"; DE_MORGAN_THM]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  TRY (FIRST_ASSUM(fun th -> if concl th = `F` then CONTR_TAC th else NO_TAC));;

(* the antecedent: unfold the evaluation of the original program, split *)

let STALLOCAUX_CC_PRIM1_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [stack_alloc_comp_def] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [stack_evaluate_def] THEN
  REWRITE_TAC (defs @ STALLOCAUX_cc_defs) THEN CONV_TAC (stallocaux_norm []) THEN
  STALLOCAUX_CC_SPLIT_TAC THEN STALLOCAUX_CC_LEAF_TAC;;

(* word expressions of the bigger state, from those of the original state *)

let STALLOCAUX_CC_WEXP_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun (_,th) -> let c = concl th in
                      is_eq c && stallocaux_head_is "stack_word_exp" (lhs c)) asl in
  let tms = find_terms (fun t -> stallocaux_head_is "stack_word_exp" t &&
                                 List.length (snd(strip_comb t)) = 2) w in
  let tac_for (_,th) =
    let s,e = (match snd(strip_comb(lhs(concl th))) with
                 [s;e] -> s,e | _ -> failwith "STALLOCAUX_CC_WEXP_TAC") in
    let cands = filter (fun t -> rand t = e && not (rand(rator t) = s)) tms in
    MAP_EVERY (fun t ->
       SUBGOAL_THEN (mk_eq(t,rhs(concl th))) (fun th' -> REWRITE_TAC[th']) THENL
        [MATCH_MP_TAC STALLOCAUX_word_exp_sub THEN EXISTS_TAC s THEN
         ASM_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[];
         ALL_TAC]) cands in
  MAP_EVERY tac_for eqs g;;

(* loc_check in the compiled code *)

let STALLOCAUX_CC_LOCCHECK_TAC : tactic = fun (asl,w as g) ->
  let lcs = filter (fun (_,th) -> stallocaux_head_is "loc_check" (concl th) &&
                      stallocaux_head_is "stack_state_code" (lhand(concl th))) asl in
  MAP_EVERY (fun (_,th) ->
     MP_TAC (SPEC `c:data_to_word_config`
               (MATCH_MP (REWRITE_RULE[IMP_CONJ] loc_check_compile) th)) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC]) lcs g;;

(* buffer lengths *)

let STALLOCAUX_CC_BUFFER_TAC : tactic = fun (asl,w as g) ->
  let bws = mapfilter (fun (_,th) -> MATCH_MP STALLOCAUX_buffer_write_len th) asl in
  MAP_EVERY ASSUME_TAC bws g;;

(* the consequent: unfold the evaluation of the compiled program, compute *)

let STALLOCAUX_SUBMAP_DOMSUB_L = prove
 (`!(f:(A,B)fmap) g k. f SUBMAP g ==> f \\ k SUBMAP g`,
  MESON_TAC[SUBMAP_TRANS; SUBMAP_DOMSUB]);;

let STALLOCAUX_SUBMAP_TAC : tactic =
  REPEAT (FIRST [MATCH_ACCEPT_TAC SUBMAP_REFL; MATCH_ACCEPT_TAC SUBMAP_FEMPTY;
                 FIRST_ASSUM MATCH_ACCEPT_TAC;
                 MATCH_MP_TAC SUBMAP_FUPDATE_both; MATCH_MP_TAC SUBMAP_DOMSUB_both;
                 MATCH_MP_TAC SUBMAP_DRESTRICT_MONOTONE THEN
                 ASM_REWRITE_TAC[SUBSET_REFL];
                 MATCH_MP_TAC STALLOCAUX_SUBMAP_DOMSUB_L]);;

let STALLOCAUX_CC_PRIM2_TAC (defs:thm list) : tactic =
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN REWRITE_TAC (defs @ STALLOCAUX_cc_defs) THEN
  CONV_TAC (stallocaux_norm []) THEN
  STALLOCAUX_CC_WEXP_TAC THEN STALLOCAUX_CC_LOCCHECK_TAC THEN
  STALLOCAUX_CC_LOOKUPS_TAC THEN
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
  CONV_TAC (stallocaux_norm []) THEN
  STALLOCAUX_CC_WIT_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN CONV_TAC (stallocaux_norm []) THEN
  ASM_REWRITE_TAC[LENGTH; LENGTH_LUPDATE; MULT_CLAUSES; ZERO_LT_dimword] THEN
  STALLOCAUX_CC_BUFFER_TAC THEN
  REPEAT CONJ_TAC THEN TRY STALLOCAUX_SUBMAP_TAC THEN TRY (ASM_ARITH_TAC);;

let STALLOCAUX_CC_PRIM_TAC (defs:thm list) : tactic =
  STALLOCAUX_CC_PRIM1_TAC defs THEN STALLOCAUX_CC_PRIM2_TAC defs;;

let STALLOCAUX_shmem_defs =
  [sh_mem_op_def; stack_sh_mem_store_def; stack_sh_mem_load_def;
   stack_sh_mem_store_byte_def; stack_sh_mem_store16_def; stack_sh_mem_store32_def;
   stack_sh_mem_load_byte_def; stack_sh_mem_load16_def; stack_sh_mem_load32_def];;

let STALLOCAUX_anything_ty =
  `:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#(store_name,(A)word_loc)fmap->
    (((A)word_loc)list#(A word->(A)word_loc)#(store_name,(A)word_loc)fmap)option`;;

let STALLOCAUX_cr_ty = `:C->(num#(A)stack_prog)list->(byte list#C)option`;;

let STALLOCAUX_ASM_NORM_TAC : tactic = fun (asl,w as g) ->
  CONV_TAC (stallocaux_norm (map snd asl)) g;;

let STALLOCAUX_SUBMAP_FL_TAC : tactic =
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_MESON_TAC[FLOOKUP_SUBMAP; option_DISTINCT];;

let STALLOCAUX_DISTINCT_TAC : tactic =
  FIRST_ASSUM(fun th -> if stallocaux_head_is "ALL_DISTINCT" (concl th) then
    STRIP_ASSUME_TAC (REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM; ARITH_EQ] th)
    else NO_TAC) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg (concl th) && is_eq (dest_neg (concl th))
                           then CONJ th (GSYM th) else th) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

let STALLOCAUX_CC_STORECONSTS_SOME_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [stack_alloc_comp_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [stack_evaluate_def] THEN
  REWRITE_TAC ([check_store_consts_opt_def; store_const_sem_def; IS_SOME_DEF] @
               STALLOCAUX_cc_defs) THEN
  CONV_TAC (stallocaux_norm []) THEN
  STALLOCAUX_CC_SPLIT_TAC THEN STALLOCAUX_CC_LEAF_TAC THEN
  EXISTS_TAC `1` THEN
  SUBGOAL_THEN `lookup a (fromAList (stack_alloc_compile c (toAList (stack_state_code
                  (s:(A,C,FFI)stack_state))))) =
                SOME (stack_Seq (stack_StoreConsts t1 t2 NONE) (stack_Return 0):(A)stack_prog)`
   ASSUME_TAC THENL
   [MP_TAC (ISPECL [`a:num`; `s:(A,C,FFI)stack_state`;
                    `stack_Seq (stack_StoreConsts t1 t2 NONE) (stack_Return 0):(A)stack_prog`;
                    `c:data_to_word_config`] lookup_IMP_lookup_compile) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
    ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[STALLOCAUX_ev_clause "stack_Call"] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[stack_find_code_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  STALLOCAUX_DISTINCT_TAC THEN STALLOCAUX_CC_LOOKUPS_TAC THEN
  REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"; STALLOCAUX_ev_clause "stack_StoreConsts";
              STALLOCAUX_ev_clause "stack_Return"; STALLOCAUX_ev_clause "stack_Skip";
              check_store_consts_opt_def; store_const_sem_def; IS_SOME_DEF;
              stack_fix_clock_def] THEN
  REWRITE_TAC STALLOCAUX_cc_defs THEN STALLOCAUX_ASM_NORM_TAC THEN
  STALLOCAUX_CC_WIT_TAC THEN REWRITE_TAC[] THEN
  STALLOCAUX_SUBMAP_FL_TAC;;

let STALLOCAUX_CC_INST_TAC : tactic =
  STALLOCAUX_CC_PRIM1_TAC [] THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN CONV_TAC (stallocaux_norm []) THEN
  FIRST_ASSUM(fun th -> let l,r = dest_eq (concl th) in
    if stallocaux_head_is "stack_inst" l then
      MP_TAC (ISPECL [rand(rator l); rand l; rand r; `regs:(num,(A)word_loc)fmap`;
                      mk_var("compile_rest",STALLOCAUX_cr_ty);
                      mk_var("anything",STALLOCAUX_anything_ty); `c:data_to_word_config`]
              stack_allocProof_inst_correct)
    else NO_TAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC (stallocaux_norm []) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN EXISTS_TAC `regs1:(num,(A)word_loc)fmap` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN ASM_ARITH_TAC;;

(* the cases of comp_correct that do not run other code *)

let STALLOCAUX_cc_Skip = prove
 (stallocaux_cc_case 0,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_Halt = prove
 (stallocaux_cc_case 1,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StoreConsts = prove
 (stallocaux_cc_case 3,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `stub_opt:num option` (cases "option")) THENL
   [STALLOCAUX_CC_PRIM_TAC [check_store_consts_opt_def; store_const_sem_def; IS_SOME_DEF];
    STALLOCAUX_CC_STORECONSTS_SOME_TAC]);;

let STALLOCAUX_cc_Inst = prove
 (stallocaux_cc_case 4,
  STALLOCAUX_CC_INST_TAC);;

let STALLOCAUX_cc_Get = prove
 (stallocaux_cc_case 5,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_Set = prove
 (stallocaux_cc_case 6,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_OpCurrHeap = prove
 (stallocaux_cc_case 7,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_Tick = prove
 (stallocaux_cc_case 8,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_Return = prove
 (stallocaux_cc_case 10,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_Raise = prove
 (stallocaux_cc_case 11,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_Break = prove
 (stallocaux_cc_case 12,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_Continue = prove
 (stallocaux_cc_case 13,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_ShMemOp = prove
 (stallocaux_cc_case 20,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `op:memop` (cases "memop")) THEN
  STALLOCAUX_CC_PRIM_TAC STALLOCAUX_shmem_defs);;

let STALLOCAUX_cc_CodeBufferWrite = prove
 (stallocaux_cc_case 21,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_DataBufferWrite = prove
 (stallocaux_cc_case 22,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_FFI = prove
 (stallocaux_cc_case 23,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_LocValue = prove
 (stallocaux_cc_case 24,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackAlloc = prove
 (stallocaux_cc_case 25,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackFree = prove
 (stallocaux_cc_case 26,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackLoad = prove
 (stallocaux_cc_case 27,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackLoadAny = prove
 (stallocaux_cc_case 28,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackStore = prove
 (stallocaux_cc_case 29,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackStoreAny = prove
 (stallocaux_cc_case 30,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackGetSize = prove
 (stallocaux_cc_case 31,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_StackSetSize = prove
 (stallocaux_cc_case 32,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_cc_BitmapLoad = prove
 (stallocaux_cc_case 33,
  STALLOCAUX_CC_PRIM_TAC []);;

let STALLOCAUX_gc_compile_frame = prove
 (`!(s:(A,C,FFI)stack_state) cr co.
     stack_gc (stack_state_compile_fupd (K cr) (stack_state_compile_oracle_fupd (K co) s)) =
     OPTION_MAP (\t. stack_state_compile_fupd (K cr) (stack_state_compile_oracle_fupd (K co) t))
       (stack_gc s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_gc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC (stallocaux_norm []) THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]) THEN
  CONV_TAC (stallocaux_norm []));;

let STALLOCAUX_alloc_compile_frame = prove
 (`!w (s:(A,C,FFI)stack_state) r t cr co.
     stackSem_alloc w s = (r,t) ==>
     stackSem_alloc w (stack_state_compile_fupd (K cr) (stack_state_compile_oracle_fupd (K co) s)) =
     (r,stack_state_compile_fupd (K cr) (stack_state_compile_oracle_fupd (K co) t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stackSem_alloc_def] THEN
  SUBGOAL_THEN
   `stack_set_store AllocSize (wl_Word w)
      (stack_state_compile_fupd (K cr) (stack_state_compile_oracle_fupd (K co) s)) =
    stack_state_compile_fupd (K cr) (stack_state_compile_oracle_fupd (K co)
      (stack_set_store AllocSize (wl_Word w) (s:(A,C,FFI)stack_state)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[stack_set_store_def] THEN CONV_TAC (stallocaux_norm []); ALL_TAC] THEN
  REWRITE_TAC[STALLOCAUX_gc_compile_frame] THEN
  STALLOCAUX_OPT_CASES_TAC `stack_gc (stack_set_store AllocSize (wl_Word w) (s:(A,C,FFI)stack_state))`
    ["s1"] THEN
  REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC (stallocaux_norm []) THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN ASM_REWRITE_TAC[PAIR_EQ]) THEN
  REPEAT (DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM))) THEN
  REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm []));;

let STALLOCAUX_CC_ALLOC_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[alloc_arg_def]) THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs(concl th)) &&
                             rhs(concl th) = `1` then SUBST_ALL_TAC th else NO_TAC) THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [stack_alloc_comp_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [stack_evaluate_def] THEN
  REWRITE_TAC STALLOCAUX_cc_defs THEN CONV_TAC (stallocaux_norm []) THEN
  ASM_REWRITE_TAC[] THEN
  STALLOCAUX_CC_SPLIT_TAC THEN TRY STALLOCAUX_CC_LEAF_TAC THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if stallocaux_head_is "stackSem_alloc" (lhs(concl th)) then
     STRIP_ASSUME_TAC (MATCH_MP stack_alloc_const th) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if stallocaux_head_is "stackSem_alloc" (lhs(concl th)) then
     MP_TAC (SPECL [mk_var("compile_rest",STALLOCAUX_cr_ty);
                    `(I ## MAP stack_alloc_prog_comp ## I) o
                     stack_state_compile_oracle (s:(A,C,FFI)stack_state)`]
                   (MATCH_MP STALLOCAUX_alloc_compile_frame th)) else NO_TAC) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if stallocaux_head_is "stackSem_alloc" (lhs(concl th)) &&
                           stallocaux_head_is "stack_state_compile_fupd" (rand(lhs(concl th)))
     then let w = rand(rator(lhs(concl th))) and s' = rand(lhs(concl th)) and
              r = fst(dest_pair(rhs(concl th))) and t' = snd(dest_pair(rhs(concl th))) in
          MP_TAC (ISPECL [w; s'; r; t'; `c:data_to_word_config`; `regs:(num,(A)word_loc)fmap`;
                          `n':num`; `m:num`; mk_var("anything",STALLOCAUX_anything_ty)]
                    alloc_correct)
     else NO_TAC) THEN
  STALLOCAUX_CC_LOOKUPS_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC (stallocaux_norm []) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `l2:(num,(A)word_loc)fmap`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `l2:(num,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if stallocaux_head_is "stackSem_alloc" (lhs(concl th)) &&
                    not (stallocaux_head_is "stack_state_compile_fupd" (rand(lhs(concl th))))
     then MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ] alloc_length_stack) th) else NO_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `c:data_to_word_config`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];;

let STALLOCAUX_cc_Alloc = prove
 (stallocaux_cc_case 2,
  STALLOCAUX_CC_ALLOC_TAC);;

(* the cases of comp_correct that run other code *)

let STALLOCAUX_code_ok_evaluate = prove
 (`!p (s:(A,C,FFI)stack_state) r t.
     stack_evaluate (p,s) = (r,t) /\
     (!k prog. lookup k (stack_state_code s) = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (stack_state_compile_oracle s n))) ==>
              ~(k = gc_stub_location) /\ alloc_arg p) ==>
     (!k prog. lookup k (stack_state_code t) = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (stack_state_compile_oracle t n))) ==>
              ~(k = gc_stub_location) /\ alloc_arg p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC o MATCH_MP evaluate_code_bitmaps) THEN
  ASM_REWRITE_TAC[shift_seq_def] THEN
  REWRITE_TAC[lookup_FOLDL_union] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM) THEN
  REWRITE_TAC[MEM; MEM_MAP; MEM_GENLIST; o_THM] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SYM) THEN ASM_REWRITE_TAC[lookup_fromAList; o_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN ASM_MESON_TAC[]]);;

let STALLOCAUX_comp_rec = prove
 (`(!n m (p1:(A)stack_prog) p2.
      FST (stack_alloc_comp n m (stack_Seq p1 p2)) =
      stack_Seq (FST (stack_alloc_comp n m p1))
                (FST (stack_alloc_comp n (SND (stack_alloc_comp n m p1)) p2))) /\
   (!n m cmp r ri (p1:(A)stack_prog) p2.
      FST (stack_alloc_comp n m (stack_If cmp r ri p1 p2)) =
      stack_If cmp r ri (FST (stack_alloc_comp n m p1))
                (FST (stack_alloc_comp n (SND (stack_alloc_comp n m p1)) p2))) /\
   (!n m (p1:(A)stack_prog).
      FST (stack_alloc_comp n m (stack_Loop p1)) =
      stack_Loop (FST (stack_alloc_comp n m p1))) /\
   (!n m dest (exc:((A)stack_prog#num#num)option).
      FST (stack_alloc_comp n m (stack_Call NONE dest exc)) = stack_Call NONE dest NONE) /\
   (!n m (p1:(A)stack_prog) lr l1 l2 dest.
      FST (stack_alloc_comp n m (stack_Call (SOME (p1,lr,l1,l2)) dest NONE)) =
      stack_Call (SOME (FST (stack_alloc_comp n m p1),lr,l1,l2)) dest NONE) /\
   (!n m (p1:(A)stack_prog) lr l1 l2 dest p2 k1 k2.
      FST (stack_alloc_comp n m (stack_Call (SOME (p1,lr,l1,l2)) dest (SOME (p2,k1,k2)))) =
      stack_Call (SOME (FST (stack_alloc_comp n m p1),lr,l1,l2)) dest
        (SOME (FST (stack_alloc_comp n (SND (stack_alloc_comp n m p1)) p2),k1,k2)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [stack_alloc_comp_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (STALLOCAUX_SPLIT_FN_TAC "stack_alloc_comp" ["q";"mm"]) THEN
  REWRITE_TAC[FST; SND]);;

(* more clock for an evaluation of comp_correct's form *)
let STALLOCAUX_cc_add_clock = prove
 (`!q (s:(A,C,FFI)stack_state) regs ck1 r t regs1 ck2.
     stack_evaluate (q,
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_clock_fupd (K (stack_state_clock s + ck1))
         (stack_state_regs_fupd (K regs)
         (stack_state_gc_fun_fupd
            (K (anything:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                         (store_name,(A)word_loc)fmap->
                         (((A)word_loc)list#(A word->(A)word_loc)#
                          (store_name,(A)word_loc)fmap)option))
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle s))
         (stack_state_compile_fupd
            (K (compile_rest:C->(num#(A)stack_prog)list->(byte list#C)option))
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))))) =
       (r,
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_regs_fupd (K regs1)
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle t))
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code t))))) t)))))))) /\
     ~(r = SOME stack_TimeOut) ==>
     stack_evaluate (q,
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_clock_fupd (K (stack_state_clock s + ck1 + ck2))
         (stack_state_regs_fupd (K regs)
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle s))
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))))) =
       (r,
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_clock_fupd (K (stack_state_clock t + ck2))
         (stack_state_regs_fupd (K regs1)
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle t))
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code t))))) t)))))))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INST [`ck2:num`,`extra:num`] stack_evaluate_add_clock)) THEN
  CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[ADD_ASSOC]);;

let STALLOCAUX_none_not_timeout = prove
 (`~(NONE:((A)stack_result)option = SOME stack_TimeOut)`,
  REWRITE_TAC[option_DISTINCT]);;
let STALLOCAUX_cc_Seq = prove
 ((stallocaux_cc_case 9),
  (REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[STALLOCAUX_comp_rec] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[alloc_arg_def]) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "stack_Seq"] THEN
    STALLOCAUX_SPLIT_TAC `stack_evaluate (c1,s:(A,C,FFI)stack_state)`
      [`res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[]) THEN
  (ASM_CASES_TAC `res:((A)stack_result)option = NONE` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      REMOVE_THEN "ih1" (MP_TAC o SPECL [`NONE:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`;
        `m:num`; `n:num`; `c:data_to_word_config`; `regs:(num,(A)word_loc)fmap`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
        STRIP_ASSUME_TAC)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN
      MP_TAC (ISPECL [`c1:(A)stack_prog`; `s:(A,C,FFI)stack_state`;
                      `NONE:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]
                stack_evaluate_consts) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC (ISPECL [`c1:(A)stack_prog`; `s:(A,C,FFI)stack_state`;
                      `NONE:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]
                STALLOCAUX_code_ok_evaluate) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,C,FFI)stack_state`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`; `t:(A,C,FFI)stack_state`;
        `SND (stack_alloc_comp n m (c1:(A)stack_prog))`; `n:num`; `c:data_to_word_config`;
        `regs1:(num,(A)word_loc)fmap`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `regs2:(num,(A)word_loc)fmap`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `regs2:(num,(A)word_loc)fmap`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STALLOCAUX_cc_add_clock
                    (CONJ th STALLOCAUX_none_not_timeout)]) THEN
      CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) THEN
  (ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`;
        `m:num`; `n:num`; `c:data_to_word_config`; `regs:(num,(A)word_loc)fmap`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1:num`; `regs1:(num,(A)word_loc)fmap`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "stack_Seq"] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[]));;

(* instantiate the labelled induction hypothesis !vs. a1 /\ .. /\ an ==> P  *)
(* with assumptions matching a1, .., an (in order; an equation v = x or     *)
(* x = v with x one of vs binds x), remove it and MP_TAC P                  *)
let STALLOCAUX_IH_MP_TAC (lab:string) : tactic = fun (asl,w as g) ->
  let ih = assoc lab asl in
  let vs,body = strip_forall (concl ih) in
  let ants = conjuncts (lhand body) in
  let asms = map snd (filter (fun (l,_) -> l <> lab) asl) in
  let rec go ants theta acc =
    match ants with
      [] -> theta,rev acc
    | a::rest ->
        let a1 = vsubst theta a in
        if is_eq a1 && mem (rhs a1) vs && not (mem (rhs a1) (map snd theta)) then
          go rest ((lhs a1,rhs a1)::theta) (REFL (lhs a1)::acc)
        else if is_eq a1 && mem (lhs a1) vs && not (mem (lhs a1) (map snd theta)) then
          go rest ((rhs a1,lhs a1)::theta) (REFL (rhs a1)::acc)
        else if is_eq a1 && lhs a1 = rhs a1 then go rest theta (REFL (lhs a1)::acc)
        else if is_eq a1 &&
                (try let (_,i,_) = term_match [] (rhs a1) (lhs a1) in
                     i <> [] && forall (fun (_,v) -> mem v vs) i
                 with Failure _ -> false) then
          let (_,i,_) = term_match [] (rhs a1) (lhs a1) in
          go rest (i @ theta) (REFL (lhs a1)::acc)
        else
        let ok th = try let (_,i,_) = term_match [] a1 (concl th) in
                        forall (fun (_,v) -> mem v vs) i
                    with Failure _ -> false in
        let th = try find ok asms
                 with Failure _ -> failwith ("STALLOCAUX_IH_MP_TAC: " ^ string_of_term a1) in
        let (_,i,_) = term_match [] a1 (concl th) in
        go rest (i @ theta) (th::acc) in
  let theta,ths = go ants [] [] in
  let ih1 = INST theta (SPECL vs ih) in
  let rec build tm =
    if is_conj tm then CONJ (build (lhand tm)) (build (rand tm))
    else find (fun th -> aconv (concl th) tm) ths in
  let th = MP ih1 (build (lhand (concl ih1))) in
  (REMOVE_THEN lab (K ALL_TAC) THEN MP_TAC th) g;;

let STALLOCAUX_get_var_sub = prove
 (`!r (s:(A,C,FFI)stack_state) x (t:(A,C,FFI)stack_state).
     stack_get_var r s = SOME x /\ stack_state_regs s SUBMAP stack_state_regs t ==>
     stack_get_var r t = SOME x`,
  REWRITE_TAC[stack_get_var_def] THEN MESON_TAC[FLOOKUP_SUBMAP]);;

let STALLOCAUX_get_var_imm_sub = prove
 (`!ri (s:(A,C,FFI)stack_state) x (t:(A,C,FFI)stack_state).
     stack_get_var_imm ri s = SOME x /\ stack_state_regs s SUBMAP stack_state_regs t ==>
     stack_get_var_imm ri t = SOME x`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[stack_get_var_imm_def] THEN MESON_TAC[STALLOCAUX_get_var_sub]);;

(* rewrite f .. X .. (X the bigger state) to SOME w, from f .. s .. = SOME w *)
let STALLOCAUX_CC_SUB_TAC (name:string) (spos:int) (lemma:thm) : tactic = fun (asl,w as g) ->
  let dest t = let h,args = strip_comb t in
               if is_const h && fst(dest_const h) = name then args else failwith "dest" in
  let n = length (snd(strip_comb(lhs(snd(dest_imp(snd(strip_forall(concl lemma)))))))) in
  let eqs = filter (fun (_,th) -> let c = concl th in
                      is_eq c && (try length (dest (lhs c)) = n with Failure _ -> false)) asl in
  let tms = find_terms (fun t -> try length (dest t) = n with Failure _ -> false) w in
  let tac_for (_,th) =
    let args = dest (lhs(concl th)) in
    let s = el spos args in
    let same t = let a2 = dest t in
                 not (el spos a2 = s) &&
                 forall (fun i -> i = spos || el i a2 = el i args) (0--(n-1)) in
    let cands = setify (filter same tms) in
    MAP_EVERY (fun t ->
       SUBGOAL_THEN (mk_eq(t,rhs(concl th))) (fun th' -> REWRITE_TAC[th']) THENL
        [MATCH_MP_TAC lemma THEN EXISTS_TAC s THEN
         ASM_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[];
         ALL_TAC]) cands in
  MAP_EVERY tac_for eqs g;;

let STALLOCAUX_CC_IH_APPLY_TAC (lab:string) (mt:term) (regst:term) : tactic =
  DISCH_TAC THEN STALLOCAUX_IH_MP_TAC lab THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`; `t:(A,C,FFI)stack_state`;
     mt; `n:num`; `c:data_to_word_config`; regst]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
    STRIP_ASSUME_TAC));;

let STALLOCAUX_CC_IF_BRANCH_TAC (lab:string) (mt:term) : tactic =
  STALLOCAUX_CC_IH_APPLY_TAC lab mt `regs:(num,(A)word_loc)fmap` THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `regs1:(num,(A)word_loc)fmap`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[STALLOCAUX_ev_clause "stack_If"] THEN
  STALLOCAUX_CC_SUB_TAC "stack_get_var" 1 STALLOCAUX_get_var_sub THEN
  STALLOCAUX_CC_SUB_TAC "stack_get_var_imm" 1 STALLOCAUX_get_var_imm_sub THEN
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]));;

let STALLOCAUX_cc_If = prove
 (stallocaux_cc_case 14,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[STALLOCAUX_comp_rec] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[alloc_arg_def]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "stack_If"] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ]) THEN
  STALLOCAUX_CC_LEAF_TAC THENL
   [STALLOCAUX_CC_IF_BRANCH_TAC "ih1" `m:num`;
    STALLOCAUX_CC_IF_BRANCH_TAC "ih2" `SND (stack_alloc_comp n m (c1:(A)stack_prog))`]);;

let STALLOCAUX_exit_loop_halt = prove
 (`!(res:((A)stack_result)option) w.
     res = SOME (stackSem_Halt w) ==> stack_exit_loop res = SOME (stackSem_Halt w)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[stack_exit_loop_def]);;

(* the IH conclusion's (!w. ~(res = SOME (Halt w))) ==> P, with the antecedent proved *)
let STALLOCAUX_HALT_ASM_TAC (tac:tactic) : tactic =
  FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_forall (lhand (concl th)) &&
                             can (find_term (fun t -> try fst(dest_const t) = "stackSem_Halt"
                                                      with Failure _ -> false)) (lhand (concl th))
                          then MP_TAC th else NO_TAC) THEN
  ANTS_TAC THENL [tac; DISCH_TAC];;

(* the clock equations (c + ck) - 1 = (c - 1) + ck of the cases below: ARITH  *)
(* with only the arithmetic assumptions that mention a clock (ASM_ARITH_TAC  *)
(* with all of them, the bounds of the stacks and buffers included, took up *)
(* to 450 s on one equation of the Call case)                              *)
let STALLOCAUX_CLOCK_ARITH_TAC : tactic = fun (asl,w as g) ->
  let is_clock t = can (find_term (stallocaux_head_is "stack_state_clock")) t in
  let ths = filter (fun th -> stallocaux_is_arith (concl th) && is_clock (concl th))
              (map snd asl) in
  (MAP_EVERY MP_TAC ths THEN ARITH_TAC) g;;

let STALLOCAUX_cc_Loop = prove
 ((stallocaux_cc_case 15),
  (REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[STALLOCAUX_comp_rec] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[alloc_arg_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "stack_Loop"] THEN
    STALLOCAUX_SPLIT_TAC `stack_evaluate (c1,s:(A,C,FFI)stack_state)`
      [`res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    ASM_CASES_TAC `res = SOME (stack_Error:(A)stack_result)` THENL
     [ASM_REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def; PAIR_EQ] THEN
      STRIP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`;
        `m:num`; `n:num`; `c:data_to_word_config`; `regs:(num,(A)word_loc)fmap`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
        STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `stack_cont_loop (res:((A)stack_result)option)` THEN ASM_REWRITE_TAC[]) THENL
  [(SUBGOAL_THEN `~(res = SOME (stack_TimeOut:(A)stack_result)) /\
                  (!w. ~(res = SOME (stackSem_Halt w:(A)stack_result)))` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP cont_loop_IMP) THEN
      REWRITE_TAC[option_DISTINCT; option_INJ; distinctness "stack_result"];
      ALL_TAC] THEN
    STALLOCAUX_HALT_ASM_TAC (ASM_REWRITE_TAC[]) THEN
    ASM_CASES_TAC `stack_state_clock (s1:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      MAP_EVERY EXISTS_TAC [`ck1:num`; `FEMPTY:(num,(A)word_loc)fmap`] THEN
      REWRITE_TAC[STALLOCAUX_ev_clause "stack_Loop"] THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm []) THEN
      ASM_REWRITE_TAC[SUBMAP_FEMPTY; LENGTH; MULT_CLAUSES; ZERO_LT_dimword];
      ALL_TAC]) THEN
  (DISCH_TAC THEN
    MP_TAC (ISPECL [`c1:(A)stack_prog`; `s:(A,C,FFI)stack_state`;
                    `res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]
              stack_evaluate_consts) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC (ISPECL [`c1:(A)stack_prog`; `s:(A,C,FFI)stack_state`;
                    `res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`]
              STALLOCAUX_code_ok_evaluate) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    STALLOCAUX_IH_MP_TAC "ih2" THEN
    DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`; `t:(A,C,FFI)stack_state`;
       `m:num`; `n:num`; `c:data_to_word_config`; `regs1:(num,(A)word_loc)fmap`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[stack_STOP_def; alloc_arg_def; stack_dec_clock_def] THEN
      CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[stack_STOP_def; STALLOCAUX_comp_rec] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `regs2:(num,(A)word_loc)fmap`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `regs2:(num,(A)word_loc)fmap`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "stack_Loop"] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STALLOCAUX_cc_add_clock
         (CONJ th (ASSUME `~(res = SOME (stack_TimeOut:(A)stack_result))`))]) THEN
    CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN
    REWRITE_TAC[stack_STOP_def] THEN CONV_TAC (stallocaux_norm []) THEN
    SUBGOAL_THEN `(stack_state_clock (s1:(A,C,FFI)stack_state) + ck2) - 1 =
                  (stack_state_clock s1 - 1) + ck2` SUBST1_TAC THENL
     [STALLOCAUX_CLOCK_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE (stallocaux_norm [])) THEN ASM_REWRITE_TAC[]);
   (REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`ck1:num`; `regs1:(num,(A)word_loc)fmap`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "stack_Loop"] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_imp (concl th) && is_forall (lhand (concl th))
                            then MATCH_MP_TAC th else NO_TAC) THEN
    ASM_MESON_TAC[STALLOCAUX_exit_loop_halt])]);;

(* from lookup k (code s) = SOME p: the lookup in the compiled code, with   *)
(* fresh m1 n1                                                              *)
let STALLOCAUX_CC_LOOKUP_TAC : tactic = fun (asl,w as g) ->
  let th = snd (find (fun (_,th) -> let c = concl th in
                 is_eq c && stallocaux_head_is "lookup" (lhs c) &&
                 stallocaux_head_is "stack_state_code" (rand (lhs c))) asl) in
  (MP_TAC (SPEC `c:data_to_word_config`
             (MATCH_MP (REWRITE_RULE[IMP_CONJ] lookup_IMP_lookup_compile) th)) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN `n1:num` ASSUME_TAC))) g;;

(* find_code (INL d) regs code = SOME p: add lookup d code = SOME p *)
let STALLOCAUX_CC_FINDCODE_TAC : tactic =
  FIRST_ASSUM(fun th -> if is_eq (concl th) &&
                           stallocaux_head_is "stack_find_code" (lhs (concl th))
                        then MP_TAC (REWRITE_RULE[stack_find_code_def] th) else NO_TAC) THEN
  CASE_REWRITE_TAC[] THEN DISCH_TAC;;

(* the goal P (prog,st) ==> G with P from comp_correct's induction: take   *)
(* r t from the assumption stack_evaluate (prog,st) = (r,t) and n m from   *)
(* a term FST (stack_alloc_comp n m prog) in an assumption                 *)
let STALLOCAUX_CC_CALLEE_TAC (regst:term) : tactic = fun (asl,w as g) ->
  let ant = lhand w in
  let _,body = strip_forall ant in
  let progst = lhs (hd (conjuncts (lhand body))) in
  let prog = fst (dest_pair (rand progst)) in
  let evth = snd (find (fun (_,th) -> let c = concl th in
                          is_eq c && lhs c = progst) asl) in
  let x,y = dest_pair (rhs (concl evth)) in
  let isk t = try let f,args = strip_comb t in
                  fst(dest_const f) = "FST" &&
                  (let f2,args2 = strip_comb (hd args) in
                   fst(dest_const f2) = "stack_alloc_comp" && el 2 args2 = prog)
              with Failure _ -> false in
  let lkt = tryfind (fun (_,th) -> find_term isk (concl th)) asl in
  let _,cargs = strip_comb (rand lkt) in
  let nn = el 0 cargs and mm = el 1 cargs in
  DISCH_THEN(MP_TAC o SPECL [x; y; mm; nn; `c:data_to_word_config`; regst]) g;;

let STALLOCAUX_cc_JumpLower = prove
 ((stallocaux_cc_case 16),
  (REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [stack_alloc_comp_def] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "JumpLower"] THEN
    CASE_REWRITE_TAC[] THEN
    REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
            ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ]) THEN
    STALLOCAUX_CC_LEAF_TAC) THENL
  [(STALLOCAUX_CC_FINDCODE_TAC THEN STALLOCAUX_CC_LOOKUP_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `FEMPTY:(num,(A)word_loc)fmap`] THEN
    REWRITE_TAC[ADD_CLAUSES; STALLOCAUX_ev_clause "JumpLower"] THEN
    STALLOCAUX_CC_SUB_TAC "stack_get_var" 1 STALLOCAUX_get_var_sub THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[stack_find_code_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm []) THEN
    ASM_REWRITE_TAC[SUBMAP_FEMPTY; LENGTH; MULT_CLAUSES; ZERO_LT_dimword] THEN
    REWRITE_TAC[stack_state_component_equality] THEN CONV_TAC (stallocaux_norm []) THEN
    ASM_REWRITE_TAC[]);
   (STALLOCAUX_CC_FINDCODE_TAC THEN STALLOCAUX_CC_LOOKUP_TAC THEN
    STALLOCAUX_IH_MP_TAC "ih" THEN
    STALLOCAUX_CC_CALLEE_TAC `regs:(num,(A)word_loc)fmap` THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[stack_dec_clock_def] THEN
      CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `regs1:(num,(A)word_loc)fmap`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "JumpLower"] THEN
    STALLOCAUX_CC_SUB_TAC "stack_get_var" 1 STALLOCAUX_get_var_sub THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC (stallocaux_norm []) THEN REWRITE_TAC[stack_find_code_def] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN CASE_REWRITE_TAC[] THEN
    CONV_TAC (stallocaux_norm []) THEN
    SUBGOAL_THEN `(stack_state_clock (s:(A,C,FFI)stack_state) + ck) - 1 =
                  (stack_state_clock s - 1) + ck` SUBST1_TAC THENL
     [STALLOCAUX_CLOCK_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE (stallocaux_norm [])) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);
   (MAP_EVERY EXISTS_TAC [`0`; `regs:(num,(A)word_loc)fmap`] THEN
    REWRITE_TAC[ADD_CLAUSES; STALLOCAUX_ev_clause "JumpLower"] THEN
    STALLOCAUX_CC_SUB_TAC "stack_get_var" 1 STALLOCAUX_get_var_sub THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN
    ASM_REWRITE_TAC[])]);;

let STALLOCAUX_dest_Seq_SOME = prove
 (`!p (a:(A)stack_prog) b. stack_dest_Seq p = SOME (a,b) <=> p = stack_Seq a b`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `p:(A)stack_prog` (CONJUNCT1 (cases "stack_prog"))) THEN
  REWRITE_TAC[stack_dest_Seq_def; option_DISTINCT; option_INJ; PAIR_EQ;
              distinctness "stack_prog"; injectivity "stack_prog"]);;

let STALLOCAUX_CC_DESTSEQ_TAC : tactic =
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                             stallocaux_head_is "stack_dest_Seq" (lhs (concl th))
                          then SUBST_ALL_TAC (REWRITE_RULE[STALLOCAUX_dest_Seq_SOME] th)
                          else NO_TAC);;


let STALLOCAUX_cc_RawCall = prove
 ((stallocaux_cc_case 17),
  (REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [stack_alloc_comp_def] THEN CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "RawCall"] THEN
    CASE_REWRITE_TAC[] THEN
    REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
            ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ]) THEN
    STALLOCAUX_CC_LEAF_TAC) THENL
  [(STALLOCAUX_CC_DESTSEQ_TAC THEN STALLOCAUX_CC_LOOKUP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[STALLOCAUX_comp_rec]) THEN
    MAP_EVERY EXISTS_TAC [`0`; `FEMPTY:(num,(A)word_loc)fmap`] THEN
    REWRITE_TAC[ADD_CLAUSES; STALLOCAUX_ev_clause "RawCall"] THEN
    CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[stack_dest_Seq_def] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm []) THEN
    ASM_REWRITE_TAC[SUBMAP_FEMPTY; LENGTH; MULT_CLAUSES; ZERO_LT_dimword] THEN
    REWRITE_TAC[stack_state_component_equality] THEN CONV_TAC (stallocaux_norm []) THEN
    ASM_REWRITE_TAC[]);
   (STALLOCAUX_IH_MP_TAC "ih" THEN
    STALLOCAUX_CC_DESTSEQ_TAC THEN STALLOCAUX_CC_LOOKUP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[STALLOCAUX_comp_rec]) THEN
    STALLOCAUX_CC_CALLEE_TAC `regs:(num,(A)word_loc)fmap` THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[stack_dec_clock_def] THEN
      CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> if is_eq (concl th) && stallocaux_head_is "lookup" (lhs (concl th)) &&
                               stallocaux_head_is "stack_state_code" (rand (lhs (concl th)))
         then MP_TAC th else NO_TAC) THEN
      DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o SPEC_ALL o
                           check (is_forall o concl))) THEN
      REWRITE_TAC[alloc_arg_def] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `regs1:(num,(A)word_loc)fmap`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "RawCall"] THEN
    CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[stack_dest_Seq_def] THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN
    CONV_TAC (stallocaux_norm []) THEN
    SUBGOAL_THEN `(stack_state_clock (s:(A,C,FFI)stack_state) + ck) - 1 =
                  (stack_state_clock s - 1) + ck` SUBST1_TAC THENL
     [STALLOCAUX_CLOCK_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE (stallocaux_norm [])) THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[])]);;

let STALLOCAUX_ALOOKUP_MAP_prog_comp = prove
 (`!l (k:num). ALOOKUP (MAP stack_alloc_prog_comp l) k =
               OPTION_MAP (\p:(A)stack_prog. FST (stack_alloc_comp k (next_lab p 2) p))
                          (ALOOKUP l k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; stack_alloc_prog_comp_def; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let STALLOCAUX_compile_union = prove
 (`!c (code:((A)stack_prog)spt) progs.
     fromAList (stack_alloc_compile c (toAList (sptree_union code (fromAList progs)))) =
     sptree_union (fromAList (stack_alloc_compile c (toAList code)))
           (fromAList (MAP stack_alloc_prog_comp progs))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[spt_eq_thm; wf_union; wf_fromAList] THEN
  REWRITE_TAC[lookup_union; lookup_fromAList; stack_alloc_compile_def; ALOOKUP_APPEND;
              STALLOCAUX_ALOOKUP_MAP_prog_comp; ALOOKUP_toAList] THEN
  X_GEN_TAC `k:num` THEN
  STALLOCAUX_OPT_CASES_TAC `ALOOKUP (stack_alloc_stubs c:(num#(A)stack_prog)list) k` ["x"] THEN
  CASE_REWRITE_TAC[] THEN
  STALLOCAUX_OPT_CASES_TAC `lookup k (code:((A)stack_prog)spt)` ["y"] THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF]);;

let STALLOCAUX_buffer_flush_eq = prove
 (`!(b:(A,B)buffer) w1 w2 d b'.
     buffer_flush b w1 w2 = SOME (d,b') ==>
     d = buffer_buffer b /\ buffer_buffer b' = [] /\
     buffer_space_left b' = buffer_space_left b`,
  REWRITE_TAC[buffer_flush_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN SIMP[]);;


let STALLOCAUX_cc_Install = prove
 ((stallocaux_cc_case 19),
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [stack_alloc_comp_def] THEN CASE_REWRITE_TAC[] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
    FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "stack_Install"] THEN
    REWRITE_TAC[stack_get_var_def; LET_DEF; LET_END_DEF] THEN CONV_TAC (stallocaux_norm []) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
            ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ]) THEN
    STALLOCAUX_CC_LEAF_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[o_THM; MAP; shift_seq_def; ADD_CLAUSES]) THEN
    FIRST_ASSUM(fun th -> if stallocaux_head_is "buffer_flush" (lhs (concl th)) &&
                             stallocaux_head_is "stack_state_data_buffer"
                               (el 0 (snd (strip_comb (lhs (concl th)))))
                          then STRIP_ASSUME_TAC (MATCH_MP STALLOCAUX_buffer_flush_eq th)
                          else NO_TAC) THEN
    RVEQ_TAC THEN
    REWRITE_TAC[STALLOCAUX_ev_clause "stack_Install"] THEN
    REWRITE_TAC[stack_get_var_def; LET_DEF; LET_END_DEF] THEN CONV_TAC (stallocaux_norm []) THEN
    STALLOCAUX_CC_LOOKUPS_TAC THEN
    REWRITE_TAC[o_THM; PAIR_MAP_THM; FST_PAIR_MAP; I_THM; MAP; shift_seq_def; ADD_CLAUSES] THEN
    REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[o_THM; PAIR_MAP_THM; I_THM; MAP] THEN CASE_REWRITE_TAC[])) THEN
    REWRITE_TAC[stack_alloc_prog_comp_def] THEN
    REPEAT (CHANGED_TAC (ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[])) THEN
    STALLOCAUX_CC_WIT_TAC THEN
    REWRITE_TAC[STALLOCAUX_compile_union; MAP; stack_alloc_prog_comp_def; o_DEF] THEN
    CONV_TAC (stallocaux_norm []) THEN
    REPEAT CONJ_TAC THEN TRY STALLOCAUX_SUBMAP_TAC THEN
    TRY (ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN ASM_ARITH_TAC)));;

let STALLOCAUX_find_code_compile = prove
 (`!(dest:num+num) (regs1:(num,(A)word_loc)fmap) regs2 (s:(A,C,FFI)stack_state) prog
    (c:data_to_word_config).
     stack_find_code dest regs1 (stack_state_code s) = SOME prog /\
     regs1 SUBMAP regs2 /\
     (!k prog. lookup k (stack_state_code s) = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) ==>
     ?m1 n1.
       stack_find_code dest regs2
         (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))) =
       SOME (FST (stack_alloc_comp m1 n1 prog)) /\
       alloc_arg prog`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `stack_find_code dest (regs2:(num,(A)word_loc)fmap)
                  (stack_state_code (s:(A,C,FFI)stack_state)) = SOME prog`
    ASSUME_TAC THENL [ASM_MESON_TAC[find_code_regs_SUBMAP]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC o MATCH_MP find_code_IMP_lookup) THEN
  MP_TAC (ISPECL [`k:num`; `s:(A,C,FFI)stack_state`; `prog:(A)stack_prog`;
                  `c:data_to_word_config`] lookup_IMP_lookup_compile) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`m1:num`; `n1:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let STALLOCAUX_quad_cases = prove
 (`!a:(A)stack_prog#num#num#num. ?rh lr l1 l2. a = (rh,lr,l1,l2)`,
  MESON_TAC[PAIR]);;

let STALLOCAUX_triple_cases = prove
 (`!a:(A)stack_prog#num#num. ?h k1 k2. a = (h,k1,k2)`,
  MESON_TAC[PAIR]);;

(* the code found by find_code dest R (code s) = SOME prog, in the compiled *)
(* code with the registers regs2 (R SUBMAP regs2), with fresh m1 n1         *)
let STALLOCAUX_CC_FC_TAC (regs2:term) : tactic = fun (asl,w as g) ->
  let th = snd (find (fun (_,th) -> let c = concl th in
                 is_eq c && stallocaux_head_is "stack_find_code" (lhs c) &&
                 stallocaux_head_is "stack_state_code" (rand (lhs c))) asl) in
  let _,args = strip_comb (lhs (concl th)) in
  let dest = el 0 args and r1 = el 1 args and code = el 2 args in
  let s = rand code in
  let prog = rand (rhs (concl th)) in
  (MP_TAC (ISPECL [dest; r1; regs2; s; prog; `c:data_to_word_config`]
             STALLOCAUX_find_code_compile) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN TRY STALLOCAUX_SUBMAP_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:num` (X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC))) g;;

let STALLOCAUX_CC_TIMEOUT_TAC : tactic =
  MAP_EVERY EXISTS_TAC [`0`; `FEMPTY:(num,(A)word_loc)fmap`] THEN
  REWRITE_TAC[ADD_CLAUSES; STALLOCAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_empty_env_def] THEN CONV_TAC (stallocaux_norm []) THEN
  ASM_REWRITE_TAC[SUBMAP_FEMPTY; LENGTH; MULT_CLAUSES; ZERO_LT_dimword] THEN
  REWRITE_TAC[stack_state_component_equality] THEN CONV_TAC (stallocaux_norm []) THEN
  ASM_REWRITE_TAC[];;



(* RULE_ASSUM_TAC for the unlabelled assumptions only *)
let STALLOCAUX_RULE_UNLABELLED_TAC (rule:thm->thm) : tactic = fun (asl,w as g) ->
  (POP_ASSUM_LIST(K ALL_TAC) THEN
   MAP_EVERY (fun (s,th) -> LABEL_TAC s (if s = "" then rule th else th)) (rev asl)) g;;

let STALLOCAUX_CC_CALL_SPLIT_TAC : tactic =
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (CONJUNCTS_THEN2 (LABEL_TAC "ih2")
    (CONJUNCTS_THEN2 (LABEL_TAC "ih3") (K ALL_TAC)))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STALLOCAUX_RULE_UNLABELLED_TAC (CONV_RULE (stallocaux_norm []) o
                                 REWRITE_RULE[alloc_arg_def]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REWRITE_TAC[STALLOCAUX_comp_rec] THEN
  FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ;
                          distinctness "stack_result"; injectivity "stack_result"]) THEN
  STALLOCAUX_CC_LEAF_TAC;;

(* the callee of a Call with a return: IH ih1, the found code, its result *)
let STALLOCAUX_CC_CALL_CALLEE_TAC : tactic =
  STALLOCAUX_CC_FC_TAC `(regs:(num,(A)word_loc)fmap) \\ lr` THEN
  STALLOCAUX_IH_MP_TAC "ih1" THEN
  STALLOCAUX_CC_CALLEE_TAC `(regs:(num,(A)word_loc)fmap) |+ (lr,wl_Loc l1 l2)` THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[stack_dec_clock_def; stack_set_var_def] THEN
    CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
    TRY STALLOCAUX_SUBMAP_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
    STRIP_ASSUME_TAC));;

(* rewrite each e - 1 in the goal, e a sum with stack_state_clock s, to e  *)
(* with stack_state_clock s - 1 for stack_state_clock s (the clock is not  *)
(* 0), then left-associate the sums in the goal and the assumptions        *)
let STALLOCAUX_CLOCK_SUB1_TAC : tactic =
  let cs = `stack_state_clock (s:(A,C,FFI)stack_state)` and one = `1` in
  let cs1 = mk_comb(mk_comb(`(-):num->num->num`,cs),one) in
  fun (asl,w as g) ->
  let tms = setify (find_terms (fun t ->
      try let f,args = strip_comb t in
          fst(dest_const f) = "-" && el 1 args = one && free_in cs (el 0 args) &&
          not (el 0 args = cs)
      with Failure _ -> false) w) in
  (MAP_EVERY (fun t ->
     let e' = subst [cs1,cs] (lhand t) in
     SUBGOAL_THEN (mk_eq(t,e')) SUBST1_TAC THENL [STALLOCAUX_CLOCK_ARITH_TAC; ALL_TAC]) tms THEN
   REWRITE_TAC[ADD_ASSOC] THEN
   RULE_ASSUM_TAC(fun th -> if stallocaux_is_ev_eq (concl th)
                            then REWRITE_RULE[ADD_ASSOC] th else th)) g;;

(* the compiled Call up to the callee's result *)
let STALLOCAUX_CC_CALL_RUN_TAC : tactic =
  REWRITE_TAC[STALLOCAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN
  STALLOCAUX_CLOCK_SUB1_TAC THEN
  RULE_ASSUM_TAC(fun th -> if stallocaux_is_ev_eq (concl th)
                           then REWRITE_RULE[ADD_ASSOC] (CONV_RULE (stallocaux_norm []) th)
                           else th) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

(* facts about the result state of the callee evaluation (the assumption  *)
(* stack_evaluate (p,stack_dec_clock ..) = (res,s2))                       *)
let STALLOCAUX_CC_CALLEE_FACTS_TAC : tactic = fun (asl,w as g) ->
  let th = snd (find (fun (_,th) -> let c = concl th in
                 stallocaux_is_ev_eq c &&
                 stallocaux_head_is "stack_dec_clock" (snd (dest_pair (rand (lhs c))))) asl) in
  (STRIP_ASSUME_TAC (CONV_RULE (stallocaux_norm []) (MATCH_MP stack_evaluate_consts th)) THEN
   MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ] STALLOCAUX_code_ok_evaluate) th) THEN
   REWRITE_TAC[stack_dec_clock_def; stack_set_var_def] THEN
   CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) g;;

(* the evaluation (in an assumption) whose state has the clock ck1, with ck2 *)
(* more clock                                                              *)
let STALLOCAUX_CC_ADDCLOCK_TAC (ck1:term) (ck2:term) : tactic = fun (asl,w as g) ->
  let th = snd (find (fun (_,th) -> let c = concl th in
                        stallocaux_is_ev_eq c && free_in ck1 (lhs c)) asl) in
  let res = fst (dest_pair (rhs (concl th))) in
  let nt = prove (mk_neg (mk_eq (res, `SOME (stack_TimeOut:(A)stack_result)`)),
                  REWRITE_TAC[option_INJ; distinctness "stack_result"; option_DISTINCT]) in
  ASSUME_TAC (SPEC ck2 (MATCH_MP STALLOCAUX_cc_add_clock (CONJ th nt))) g;;

let STALLOCAUX_DROP_IHS_TAC : tactic =
  MAP_EVERY (fun l -> TRY (REMOVE_THEN l (K ALL_TAC))) ["ih1";"ih2";"ih3";"ih4"];;

let STALLOCAUX_CC_CALL_DIRECT_TAC : tactic =
  STALLOCAUX_CC_CALL_CALLEE_TAC THEN STALLOCAUX_DROP_IHS_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck1:num`; `regs1:(num,(A)word_loc)fmap`] THEN ASM_REWRITE_TAC[] THEN
  STALLOCAUX_CC_CALL_RUN_TAC;;

(* a Call whose callee returns (or raises) to the code continuation (IH lab, *)
(* the comp label m of the continuation)                                    *)
let STALLOCAUX_CC_CALL_CONT_TAC (lab:string) (mt:term) : tactic =
  DISCH_TAC THEN STALLOCAUX_CC_CALL_CALLEE_TAC THEN STALLOCAUX_CC_CALLEE_FACTS_TAC THEN
  STALLOCAUX_HALT_ASM_TAC (REWRITE_TAC[option_INJ; distinctness "stack_result"]) THEN
  STALLOCAUX_IH_MP_TAC lab THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)stack_result)option`; `t:(A,C,FFI)stack_state`;
     mt; `n:num`; `c:data_to_word_config`; `regs1:(num,(A)word_loc)fmap`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck2:num` (X_CHOOSE_THEN `regs2:(num,(A)word_loc)fmap`
    STRIP_ASSUME_TAC)) THEN
  STALLOCAUX_DROP_IHS_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck1 + ck2:num`; `regs2:(num,(A)word_loc)fmap`] THEN
  ASM_REWRITE_TAC[] THEN
  STALLOCAUX_CC_ADDCLOCK_TAC `ck1:num` `ck2:num` THEN
  STALLOCAUX_CC_CALL_RUN_TAC THEN
  CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

(* the Call case of comp_correct *)
let STALLOCAUX_cc_Call = prove
 (stallocaux_cc_case 18,
  GEN_REWRITE_TAC I [FORALL_OPTION_THM] THEN CONJ_TAC THENL
   [(REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ih4")))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[STALLOCAUX_comp_rec] THEN
  FIRST_X_ASSUM(MP_TAC o check (stallocaux_is_ev_eq o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [STALLOCAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT ((COND_CASES_TAC ORELSE TOP_CASE_TAC) THEN
          ASM_REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ]) THEN
  STALLOCAUX_CC_LEAF_TAC) THENL
     [STALLOCAUX_CC_FC_TAC `regs:(num,(A)word_loc)fmap` THEN STALLOCAUX_CC_TIMEOUT_TAC;
      STALLOCAUX_CC_FC_TAC `regs:(num,(A)word_loc)fmap` THEN
  STALLOCAUX_IH_MP_TAC "ih4" THEN
  STALLOCAUX_CC_CALLEE_TAC `regs:(num,(A)word_loc)fmap` THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[stack_dec_clock_def] THEN
    CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `regs1:(num,(A)word_loc)fmap`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[STALLOCAUX_ev_clause "stack_Call"] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN ASM_REWRITE_TAC[ADD_EQ_0] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC (stallocaux_norm []) THEN
  SUBGOAL_THEN `(stack_state_clock (s:(A,C,FFI)stack_state) + ck) - 1 =
                (stack_state_clock s - 1) + ck` SUBST1_TAC THENL
   [STALLOCAUX_CLOCK_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE (stallocaux_norm [])) THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `a:(A)stack_prog#num#num#num` THEN
    STRUCT_CASES_TAC (ISPEC `a:(A)stack_prog#num#num#num` STALLOCAUX_quad_cases) THEN
    X_GEN_TAC `dest:num+num` THEN
    GEN_REWRITE_TAC I [FORALL_OPTION_THM] THEN CONJ_TAC THENL
     [STALLOCAUX_CC_CALL_SPLIT_TAC THENL
       [STALLOCAUX_CC_FC_TAC `(regs:(num,(A)word_loc)fmap) \\ lr` THEN
        STALLOCAUX_CC_TIMEOUT_TAC;
        STALLOCAUX_CC_CALL_CONT_TAC "ih2" `m:num`;
        STALLOCAUX_CC_CALL_DIRECT_TAC; STALLOCAUX_CC_CALL_DIRECT_TAC;
        STALLOCAUX_CC_CALL_DIRECT_TAC; STALLOCAUX_CC_CALL_DIRECT_TAC];
      X_GEN_TAC `hh:(A)stack_prog#num#num` THEN
      STRUCT_CASES_TAC (ISPEC `hh:(A)stack_prog#num#num` STALLOCAUX_triple_cases) THEN
      STALLOCAUX_CC_CALL_SPLIT_TAC THENL
       [STALLOCAUX_CC_FC_TAC `(regs:(num,(A)word_loc)fmap) \\ lr` THEN
        STALLOCAUX_CC_TIMEOUT_TAC;
        STALLOCAUX_CC_CALL_CONT_TAC "ih2" `m:num`;
        STALLOCAUX_CC_CALL_CONT_TAC "ih3" `SND (stack_alloc_comp n m (rh:(A)stack_prog))`;
        STALLOCAUX_CC_CALL_DIRECT_TAC; STALLOCAUX_CC_CALL_DIRECT_TAC;
        STALLOCAUX_CC_CALL_DIRECT_TAC]]]);;

(* HOL4 line 5297 (HOL4 leaves compile_rest and anything free)            *)
let stack_allocProof_comp_correct = prove
 (`!p (s:(A,C,FFI)stack_state) r t m n c regs
    (compile_rest:C->(num#(A)stack_prog)list->(byte list#C)option)
    (anything:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
              (store_name,(A)word_loc)fmap->
              (((A)word_loc)list#(A word->(A)word_loc)#(store_name,(A)word_loc)fmap)option).
     stack_evaluate (p,s) = (r,t) /\ ~(r = SOME stack_Error) /\ alloc_arg p /\
     (!k prog. lookup k (stack_state_code s) = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (stack_state_compile_oracle s n))) ==>
              ~(k = gc_stub_location) /\ alloc_arg p) /\
     stack_state_gc_fun s = word_gc_fun c /\ stack_state_use_alloc s /\
     LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     stack_state_regs s SUBMAP regs /\
     stack_state_use_stack s /\
     (LENGTH (stack_state_bitmaps s) + LENGTH (buffer_buffer (stack_state_data_buffer s))) +
       buffer_space_left (stack_state_data_buffer s) < dimword (:A) - 1 /\
     stack_state_compile s =
       (\c. compile_rest c o
            MAP stack_alloc_prog_comp)
     ==>
     ?ck regs1.
       stack_evaluate (FST (stack_alloc_comp n m p),
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_clock_fupd (K (stack_state_clock s + ck))
         (stack_state_regs_fupd (K regs)
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle s))
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s))))) s))))))))) =
       (r,
         stack_state_use_store_fupd (K T)
         (stack_state_use_stack_fupd (K T)
         (stack_state_use_alloc_fupd (K F)
         (stack_state_regs_fupd (K regs1)
         (stack_state_gc_fun_fupd (K anything)
         (stack_state_compile_oracle_fupd
            (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle t))
         (stack_state_compile_fupd (K compile_rest)
         (stack_state_code_fupd
            (K (fromAList (stack_alloc_compile c (toAList (stack_state_code t))))) t)))))))) /\
       stack_state_regs t SUBMAP regs1 /\
       (LENGTH (stack_state_bitmaps t) + LENGTH (buffer_buffer (stack_state_data_buffer t))) +
         buffer_space_left (stack_state_data_buffer t) < dimword (:A) - 1 /\
       ((!w. ~(r = SOME (stackSem_Halt w))) ==>
        LENGTH (stack_state_stack t) * (dimindex (:A) DIV 8) < dimword (:A))`,
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC (CONV_RULE (REWRITE_CONV[FORALL_PAIR_THM] THENC DEPTH_CONV GEN_BETA_CONV)
                     (MP STALLOCAUX_cc_ind (end_itlist CONJ
    [STALLOCAUX_cc_Skip; STALLOCAUX_cc_Halt; STALLOCAUX_cc_Alloc; STALLOCAUX_cc_StoreConsts;
     STALLOCAUX_cc_Inst; STALLOCAUX_cc_Get; STALLOCAUX_cc_Set; STALLOCAUX_cc_OpCurrHeap;
     STALLOCAUX_cc_Tick; STALLOCAUX_cc_Seq; STALLOCAUX_cc_Return; STALLOCAUX_cc_Raise;
     STALLOCAUX_cc_Break; STALLOCAUX_cc_Continue; STALLOCAUX_cc_If; STALLOCAUX_cc_Loop;
     STALLOCAUX_cc_JumpLower; STALLOCAUX_cc_RawCall; STALLOCAUX_cc_Call; STALLOCAUX_cc_Install;
     STALLOCAUX_cc_ShMemOp; STALLOCAUX_cc_CodeBufferWrite; STALLOCAUX_cc_DataBufferWrite; STALLOCAUX_cc_FFI;
     STALLOCAUX_cc_LocValue; STALLOCAUX_cc_StackAlloc; STALLOCAUX_cc_StackFree; STALLOCAUX_cc_StackLoad;
     STALLOCAUX_cc_StackLoadAny; STALLOCAUX_cc_StackStore; STALLOCAUX_cc_StackStoreAny; STALLOCAUX_cc_StackGetSize;
     STALLOCAUX_cc_StackSetSize; STALLOCAUX_cc_BitmapLoad]))));;

(* ------------------------------------------------------------------------- *)
(* HOL4 lines 5901-6105 of stack_allocProofScript.sml: with_same_regs_lemma, *)
(* compile_semantics, make_init_def, prog_comp_lambda, make_init_semantics.  *)
(* HOL4 val comp_correct_thm (line 5896, comp_correct with regs := s.regs)   *)
(* is not bound: the proof instantiates comp_correct directly.               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 line 5901 [local]; HOL4 adds it to its simpset for the rest of the  *)
(* script (augment_srw_ss); here it is used by name                          *)
let with_same_regs_lemma = prove
 (`!(s:(A,C,FFI)stack_state) cc oracle anything k c.
     stack_state_regs_fupd (K (stack_state_regs s))
     (stack_state_compile_fupd (K cc)
     (stack_state_compile_oracle_fupd (K oracle)
     (stack_state_gc_fun_fupd (K anything)
     (stack_state_use_stack_fupd (K T)
     (stack_state_use_store_fupd (K T)
     (stack_state_use_alloc_fupd (K F)
     (stack_state_clock_fupd (K k)
     (stack_state_code_fupd (K c) s)))))))) =
     stack_state_compile_fupd (K cc)
     (stack_state_compile_oracle_fupd (K oracle)
     (stack_state_gc_fun_fupd (K anything)
     (stack_state_use_stack_fupd (K T)
     (stack_state_use_store_fupd (K T)
     (stack_state_use_alloc_fupd (K F)
     (stack_state_clock_fupd (K k)
     (stack_state_code_fupd (K c) s)))))))`,
  REWRITE_TAC[stack_state_component_equality] THEN SIMP[]);;

(* helpers for compile_semantics.  The proof of HOL4 compile_semantics      *)
(* (the cases of semantics_def with some_intro, comp_correct,               *)
(* evaluate_add_clock and the io-event chains) is split here into a generic *)
(* lemma (STALLOCAUX_SEM_semantics_sim: the semantics of t is the one of s   *)
(* when every run of s that does not fail is matched by a run of t with     *)
(* extra clock, the same result and the same ffi) and the run lemma          *)
(* STALLOCAUX_SEM_run (comp_correct for the program of semantics_def).       *)
(* The generic lemmas are copies of stack_rawcallProof's                     *)
(* STACKPROPSAUX_eval_det ... STACKPROPSAUX_semantics_sim (not in the needs  *)
(* closure of this file).                                                    *)

let STALLOCAUX_SEM_eval_det = prove
 (`!p (x:(A,C,FFI)stack_state) k1 k2 r1 r2 x1 x2.
     stack_evaluate (p,stack_state_clock_fupd (K k1) x) = (r1,x1) /\
     stack_evaluate (p,stack_state_clock_fupd (K k2) x) = (r2,x2) /\
     ~(r1 = SOME stack_TimeOut) /\ ~(r2 = SOME stack_TimeOut)
     ==> r1 = r2 /\ stack_state_ffi x1 = stack_state_ffi x2`,
  SUBGOAL_THEN
   `!p (x:(A,C,FFI)stack_state) k1 d r1 r2 x1 x2.
     stack_evaluate (p,stack_state_clock_fupd (K k1) x) = (r1,x1) /\
     stack_evaluate (p,stack_state_clock_fupd (K (k1 + d)) x) = (r2,x2) /\
     ~(r1 = SOME stack_TimeOut)
     ==> r1 = r2 /\ stack_state_ffi x1 = stack_state_ffi x2`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(INST [`d:num`,`extra:num`]
      (ISPECL [`p:(A)stack_prog`; `stack_state_clock_fupd (K k1) (x:(A,C,FFI)stack_state)`;
               `r1:((A)stack_result)option`; `x1:(A,C,FFI)stack_state`]
              stack_evaluate_add_clock)) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  ASM_MESON_TAC[]);;

let STALLOCAUX_SEM_eval_mono_clock = prove
 (`!p (x:(A,C,FFI)stack_state) k1 k2 r1 x1.
     stack_evaluate (p,stack_state_clock_fupd (K k1) x) = (r1,x1) /\
     ~(r1 = SOME stack_TimeOut) /\ k1 <= k2
     ==> FST (stack_evaluate (p,stack_state_clock_fupd (K k2) x)) = r1 /\
         stack_state_ffi (SND (stack_evaluate (p,stack_state_clock_fupd (K k2) x))) =
         stack_state_ffi x1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(INST [`d:num`,`extra:num`]
    (ISPECL [`p:(A)stack_prog`; `stack_state_clock_fupd (K k1) (x:(A,C,FFI)stack_state)`;
             `r1:((A)stack_result)option`; `x1:(A,C,FFI)stack_state`]
            stack_evaluate_add_clock)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let STALLOCAUX_SEM_sem_ev (x:term) (k:term) =
  vsubst [x,`x:(A,C,FFI)stack_state`; k,`k:num`]
   `stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                    stack_state_clock_fupd (K k) (x:(A,C,FFI)stack_state))`;;

(* the pair of a run: names r, s1 for stack_evaluate (P,clock_fupd (K k) x) *)
let STALLOCAUX_SEM_RUN_TAC (x:term) (k:term) (r:term) (x1:term) : tactic =
  MP_TAC(ISPEC (STALLOCAUX_SEM_sem_ev x k) PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [r; x1] THEN DISCH_TAC;;

(* MP_TAC the labelled assumption lab at k, rewritten with the assumption    *)
(* stack_evaluate (P,clock_fupd (K k) x) = (r,x1) made by STALLOCAUX_SEM_RUN_TAC *)
let STALLOCAUX_SEM_USE_RUN_TAC (lab:string) (x:term) (r:term) (x1:term) : tactic =
  let tm = mk_eq(STALLOCAUX_SEM_sem_ev x `k:num`, mk_pair(r,x1)) in
  FIRST_ASSUM(fun eq ->
    if aconv (concl eq) tm then USE_THEN lab (MP_TAC o REWRITE_RULE[FST; eq] o SPEC `k:num`)
    else NO_TAC);;

let STALLOCAUX_SEM_sem_oks (x:term) =
  let ev = mk_comb(`FST:((A)stack_result)option#(A,C,FFI)stack_state->((A)stack_result)option`,
                   STALLOCAUX_SEM_sem_ev x `k:num`) in
  mk_forall(`k:num`,
   list_mk_disj
    [mk_eq(ev,`SOME (stack_TimeOut:(A)stack_result)`);
     mk_eq(ev,`SOME (stack_Result (wl_Loc 1 0):(A)stack_result)`);
     mk_exists(`w:A word`,mk_eq(ev,`SOME (stackSem_Halt (wl_Word (w:A word)))`));
     mk_exists(`f:final_event`,mk_eq(ev,`SOME (stack_FinalFFI f:(A)stack_result)`))]);;

(* the semantics of t is the one of s when every run of s that does not   *)
(* fail is simulated by a run of t with extra clock, with the same ffi      *)

let STALLOCAUX_SEM_semantics_sim = prove
 (`!start (s:(A,C,FFI)stack_state) (t:(A,C,FFI)stack_state).
     (!k r s1.
        stack_evaluate (stack_Call NONE (INL start) NONE,stack_state_clock_fupd (K k) s) =
        (r,s1) /\ ~(r = SOME stack_Error)
        ==> ?ck t1.
              stack_evaluate (stack_Call NONE (INL start) NONE,
                              stack_state_clock_fupd (K (k + ck)) t) = (r,t1) /\
              stack_state_ffi t1 = stack_state_ffi s1) /\
     ~(stack_semantics start s = Fail)
     ==> stack_semantics start t = stack_semantics start s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!k. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                             stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))) =
          SOME stack_TimeOut \/
        FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                             stack_state_clock_fupd (K k) s)) =
          SOME (stack_Result (wl_Loc 1 0)) \/
        (?w. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                  stack_state_clock_fupd (K k) s)) =
               SOME (stackSem_Halt (wl_Word w))) \/
        (?f. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                  stack_state_clock_fupd (K k) s)) =
               SOME (stack_FinalFFI f))`
   (LABEL_TAC "oks") THENL
   [UNDISCH_TAC `~(stack_semantics start (s:(A,C,FFI)stack_state) = Fail)` THEN
    REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!k. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                              stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))) =
         SOME stack_TimeOut
         ==> FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                  stack_state_clock_fupd (K k) (t:(A,C,FFI)stack_state))) =
             SOME stack_TimeOut`
    (LABEL_TAC "tmo") THENL
   [GEN_TAC THEN
    STALLOCAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
      `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `SOME (stack_TimeOut:(A)stack_result)`;
                                    `s1:(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[option_INJ; distinctness "stack_result"]; ALL_TAC] THEN
    STRIP_TAC THEN
    STALLOCAUX_SEM_RUN_TAC `t:(A,C,FFI)stack_state` `k:num`
      `r2:((A)stack_result)option` `t2:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[FST] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                   `t:(A,C,FFI)stack_state`; `k:num`; `k + ck:num`;
                   `r2:((A)stack_result)option`; `t2:(A,C,FFI)stack_state`]
                  STALLOCAUX_SEM_eval_mono_clock) THEN
    ASM_REWRITE_TAC[LE_ADD; FST];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!k r (t1:(A,C,FFI)stack_state).
       stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                       stack_state_clock_fupd (K k) t) = (r,t1) /\
       ~(r = SOME stack_TimeOut)
       ==> ?s1. stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                                stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)) =
                (r,s1) /\ stack_state_ffi s1 = stack_state_ffi t1`
    (LABEL_TAC "back") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    STALLOCAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
      `r0:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
    SUBGOAL_THEN `~(r0 = SOME (stack_TimeOut:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      USE_THEN "tmo" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[FST]; ASM_REWRITE_TAC[FST]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(r0 = SOME (stack_Error:(A)stack_result))` ASSUME_TAC THENL
     [STALLOCAUX_SEM_USE_RUN_TAC "oks" `s:(A,C,FFI)stack_state`
      `r0:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; distinctness "stack_result"];
      ALL_TAC] THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `r0:((A)stack_result)option`;
                                    `s1:(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                   `t:(A,C,FFI)stack_state`; `k:num`; `k + ck:num`;
                   `r:((A)stack_result)option`; `r0:((A)stack_result)option`;
                   `t1:(A,C,FFI)stack_state`; `t1':(A,C,FFI)stack_state`]
                  STALLOCAUX_SEM_eval_det) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `s1:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (STALLOCAUX_SEM_sem_oks `t:(A,C,FFI)stack_state`) (LABEL_TAC "okt") THENL
   [GEN_TAC THEN
    STALLOCAUX_SEM_RUN_TAC `t:(A,C,FFI)stack_state` `k:num`
      `r:((A)stack_result)option` `t1:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[FST] THEN
    ASM_CASES_TAC `r = SOME (stack_TimeOut:(A)stack_result)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "back" (MP_TAC o SPECL [`k:num`; `r:((A)stack_result)option`;
                                     `t1:(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    STALLOCAUX_SEM_USE_RUN_TAC "oks" `s:(A,C,FFI)stack_state`
      `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[stack_semantics_def; LET_DEF; LET_END_DEF] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
     USE_THEN "okt" (fun th -> MESON_TAC[th]);
     ALL_TAC] THEN
   COND_CASES_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
     USE_THEN "oks" (fun th -> MESON_TAC[th]);
     ALL_TAC] THEN
  MATCH_MP_TAC BASICAUX_option_CASE_cong THEN CONJ_TAC THENL
  [AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(r = (stack_TimeOut:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN FS[]; ALL_TAC] THEN
    USE_THEN "back" (MP_TAC o SPECL [`k:num`; `SOME (r:(A)stack_result)`;
                                     `t':(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[option_INJ]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(A,C,FFI)stack_state` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`; `r:(A)stack_result`;
                          `outcome:outcome`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(r = (stack_Error:(A)stack_result))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN FS[]; ALL_TAC] THEN
    USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `SOME (r:(A)stack_result)`;
                                    `t':(A,C,FFI)stack_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[option_INJ]; ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`k + ck:num`; `t1:(A,C,FFI)stack_state`; `r:(A)stack_result`;
                          `outcome:outcome`] THEN
    ASM_REWRITE_TAC[]];
   REWRITE_TAC[BASICAUX_some_NONE] THEN DISCH_TAC THEN AP_TERM_TAC THEN
   SUBGOAL_THEN
     `!k. FST (stack_evaluate (stack_Call NONE (INL start) NONE:(A)stack_prog,
                               stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state))) =
          SOME stack_TimeOut`
     (LABEL_TAC "div") THENL
    [GEN_TAC THEN
     STALLOCAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
       `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
     ASM_REWRITE_TAC[FST] THEN
     STALLOCAUX_SEM_USE_RUN_TAC "oks" `s:(A,C,FFI)stack_state`
      `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
       is_forall c && is_neg (snd(dest_forall c)))) THEN
     FIRST_X_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC[NOT_FORALL_THM; option_INJ; distinctness "stack_result"] THENL
      [EXISTS_TAC `Terminate Success
                     (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))` THEN
       MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                             `stack_Result (wl_Loc 1 0):(A)stack_result`; `Success`];
       EXISTS_TAC `Terminate (if wl_Word (w:A word) = wl_Word (word 0) then Success
                              else Resource_limit_hit)
                     (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))` THEN
       MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                             `stackSem_Halt (wl_Word (w:A word)):(A)stack_result`;
                             `if wl_Word (w:A word) = wl_Word (word 0) then Success
                              else Resource_limit_hit`];
       EXISTS_TAC `Terminate (FFI_outcome f)
                     (ffi_state_io_events (stack_state_ffi (s1:(A,C,FFI)stack_state)))` THEN
       MAP_EVERY EXISTS_TAC [`k:num`; `s1:(A,C,FFI)stack_state`;
                             `stack_FinalFFI f:(A)stack_result`; `FFI_outcome f`]] THEN
     ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
     ALL_TAC] THEN
   MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN REWRITE_TAC[STACKPROPSAUX_io_chain] THEN
   REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
   CONJ_TAC THEN X_GEN_TAC `k:num` THEN
   STALLOCAUX_SEM_RUN_TAC `s:(A,C,FFI)stack_state` `k:num`
     `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
   STALLOCAUX_SEM_USE_RUN_TAC "div" `s:(A,C,FFI)stack_state`
      `r:((A)stack_result)option` `s1:(A,C,FFI)stack_state` THEN
   DISCH_THEN SUBST_ALL_TAC THEN
   USE_THEN "sim" (MP_TAC o SPECL [`k:num`; `SOME (stack_TimeOut:(A)stack_result)`;
                                   `s1:(A,C,FFI)stack_state`]) THEN
   (ANTS_TAC THENL
     [ASM_REWRITE_TAC[option_INJ; distinctness "stack_result"]; ALL_TAC]) THEN
   STRIP_TAC THENL
    [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
     MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                    `t:(A,C,FFI)stack_state`; `k:num`; `k + ck:num`] STACKPROPSAUX_io_mono) THEN
     ASM_REWRITE_TAC[LE_ADD];
     EXISTS_TAC `k + ck:num` THEN
     ASM_REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE; IS_PREFIX_REFL]]]);;

(* comp and alloc_arg on the program of semantics_def *)

let STALLOCAUX_SEM_comp_Call = prove
 (`!n m start.
     FST (stack_alloc_comp n m (stack_Call NONE (INL start) NONE:(A)stack_prog)) =
     stack_Call NONE (INL start) NONE`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN CASE_REWRITE_TAC[FST]);;

let STALLOCAUX_SEM_alloc_arg_Call = prove
 (`!start. alloc_arg (stack_Call NONE (INL start) NONE:(A)stack_prog)`,
  REWRITE_TAC[alloc_arg_def] THEN CASE_REWRITE_TAC[]);;

(* the runs of the semantics: comp_correct for stack_Call NONE (INL start)  *)
(* NONE at clock k, with regs := s.regs (HOL4 comp_correct_thm)              *)

let STALLOCAUX_SEM_run = prove
 (`!(s:(A,C,FFI)stack_state) c
    (compile_rest:C->(num#(A)stack_prog)list->(byte list#C)option)
    (anything:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
              (store_name,(A)word_loc)fmap->
              (((A)word_loc)list#(A word->(A)word_loc)#(store_name,(A)word_loc)fmap)option)
    start k r s1.
     (!k prog. lookup k (stack_state_code s) = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (stack_state_compile_oracle s n))) ==>
              ~(k = gc_stub_location) /\ alloc_arg p) /\
     stack_state_gc_fun s = word_gc_fun c /\
     (LENGTH (stack_state_bitmaps s) + LENGTH (buffer_buffer (stack_state_data_buffer s))) +
       buffer_space_left (stack_state_data_buffer s) < dimword (:A) - 1 /\
     LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     stack_state_use_stack s /\ stack_state_use_alloc s /\
     stack_state_compile s = (\c. compile_rest c o MAP stack_alloc_prog_comp) /\
     stack_evaluate (stack_Call NONE (INL start) NONE,stack_state_clock_fupd (K k) s) =
       (r,s1) /\
     ~(r = SOME stack_Error)
     ==> ?ck t1.
           stack_evaluate (stack_Call NONE (INL start) NONE,
             stack_state_clock_fupd (K (k + ck))
             (stack_state_code_fupd
                (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))))
             (stack_state_gc_fun_fupd (K anything)
             (stack_state_compile_fupd (K compile_rest)
             (stack_state_compile_oracle_fupd
                (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle s))
             (stack_state_use_store_fupd (K T)
             (stack_state_use_stack_fupd (K T)
             (stack_state_use_alloc_fupd (K F) s)))))))) = (r,t1) /\
           stack_state_ffi t1 = stack_state_ffi s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`stack_Call NONE (INL start) NONE:(A)stack_prog`;
                 `stack_state_clock_fupd (K k) (s:(A,C,FFI)stack_state)`;
                 `r:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`;
                 `0:num`; `0:num`; `c:data_to_word_config`;
                 `stack_state_regs (s:(A,C,FFI)stack_state)`;
                 `compile_rest:C->(num#(A)stack_prog)list->(byte list#C)option`;
                 `anything:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                   (store_name,(A)word_loc)fmap->
                   (((A)word_loc)list#(A word->(A)word_loc)#
                    (store_name,(A)word_loc)fmap)option`]
                stack_allocProof_comp_correct) THEN
  ANTS_TAC THENL
   [CONV_TAC(stallocaux_norm []) THEN
    ASM_REWRITE_TAC[STALLOCAUX_SEM_alloc_arg_Call; SUBMAP_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[STALLOCAUX_SEM_comp_Call] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `regs1:(num,(A)word_loc)fmap`
    (MP_TAC o CONJUNCT1))) THEN
  CONV_TAC(stallocaux_norm [with_same_regs_lemma]) THEN
  DISCH_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN SIMP[]);;

(* HOL4 line 5909 *)
let stack_allocProof_compile_semantics = prove
 (`!(s:(A,C,FFI)stack_state) c compile_rest start anything.
     (!k prog. lookup k (stack_state_code s) = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (stack_state_compile_oracle s n))) ==>
              ~(k = gc_stub_location) /\ alloc_arg p) /\
     stack_state_gc_fun s = word_gc_fun c /\
     (LENGTH (stack_state_bitmaps s) + LENGTH (buffer_buffer (stack_state_data_buffer s))) +
       buffer_space_left (stack_state_data_buffer s) < dimword (:A) - 1 /\
     LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     stack_state_use_stack s /\ stack_state_use_alloc s /\
     stack_state_compile s = (\c. compile_rest c o MAP stack_alloc_prog_comp) /\
     ~(stack_semantics start s = Fail)
     ==> stack_semantics start
           (stack_state_code_fupd
              (K (fromAList (stack_alloc_compile c (toAList (stack_state_code s)))))
           (stack_state_gc_fun_fupd (K anything)
           (stack_state_compile_fupd (K compile_rest)
           (stack_state_compile_oracle_fupd
              (K ((I ## MAP stack_alloc_prog_comp ## I) o stack_state_compile_oracle s))
           (stack_state_use_store_fupd (K T)
           (stack_state_use_stack_fupd (K T)
           (stack_state_use_alloc_fupd (K F) s))))))) =
         stack_semantics start s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC STALLOCAUX_SEM_semantics_sim THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STALLOCAUX_SEM_run THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6068 (HOL4 s with <| f1 := v1; ... |> is nested _fupd with the  *)
(* first field outermost; the bound config of the compile lambda is cfg)     *)
let stack_allocProof_make_init_def = cake_def
  `stack_allocProof_make_init (c:data_to_word_config) code oracle (s:(A,C,FFI)stack_state) =
     stack_state_code_fupd (K code)
      (stack_state_use_alloc_fupd (K T)
       (stack_state_use_stack_fupd (K T)
        (stack_state_gc_fun_fupd (K (word_gc_fun c))
         (stack_state_compile_fupd
            (K (\cfg. stack_state_compile s cfg o MAP stack_alloc_prog_comp))
          (stack_state_compile_oracle_fupd (K oracle) s)))))`;;

(* HOL4 line 6075 (HOL4's paired lambda is HOL Light's \(n,p). ...) *)
let prog_comp_lambda = prove
 (`stack_alloc_prog_comp =
   (\(n,p:(A)stack_prog). (n,FST (stack_alloc_comp n (next_lab p 2) p)))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; stack_alloc_prog_comp_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 6081 *)
let stack_allocProof_make_init_semantics = prove
 (`!code oracle (s:(A,C,FFI)stack_state) c start.
     (!k prog. ALOOKUP code k = SOME prog ==>
               ~(k = gc_stub_location) /\ alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (oracle n))) ==>
              ~(k = gc_stub_location) /\ alloc_arg p) /\
     stack_state_use_stack s /\ stack_state_use_store s /\ ~stack_state_use_alloc s /\
     stack_state_code s = fromAList (stack_alloc_compile c code) /\
     stack_state_compile_oracle s = (I ## MAP stack_alloc_prog_comp ## I) o oracle /\
     LENGTH (stack_state_bitmaps s) + LENGTH (buffer_buffer (stack_state_data_buffer s)) +
       buffer_space_left (stack_state_data_buffer s) < dimword (:A) - 1 /\
     LENGTH (stack_state_stack s) * (dimindex (:A) DIV 8) < dimword (:A) /\
     ALL_DISTINCT (MAP FST code) /\
     ~(stack_semantics start (stack_allocProof_make_init c (fromAList code) oracle s) = Fail)
     ==> stack_semantics start s =
         stack_semantics start (stack_allocProof_make_init c (fromAList code) oracle s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`stack_allocProof_make_init c (fromAList code) oracle (s:(A,C,FFI)stack_state)`;
                 `c:data_to_word_config`; `stack_state_compile (s:(A,C,FFI)stack_state)`;
                 `start:num`; `stack_state_gc_fun (s:(A,C,FFI)stack_state)`]
                stack_allocProof_compile_semantics) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[stack_allocProof_make_init_def] THEN
    CONV_TAC(stallocaux_norm [lookup_fromAList]) THEN
    ASM_REWRITE_TAC[GSYM ADD_ASSOC];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[stack_allocProof_make_init_def; stack_state_component_equality] THEN
  CONV_TAC(stallocaux_norm []) THEN ASM_REWRITE_TAC[] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [lhs w; rhs w] spt_eq_thm)) THEN
  REWRITE_TAC[wf_fromAList] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lookup_fromAList; stack_alloc_compile_def; ALOOKUP_APPEND] THEN GEN_TAC THEN
  REWRITE_TAC[prog_comp_lambda; ALOOKUP_MAP_2; ALOOKUP_toAList; lookup_fromAList]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 lines 6111-6361 of stack_allocProofScript.sml: syntactic properties *)
(* of the stack_alloc compiler (labels, register names, register bounds,   *)
(* call arguments) and the independence of compile from the fp flags.      *)
(* ------------------------------------------------------------------------- *)

(* HOL4 line 6111 *)
(* HOL4 proves the statement with a vacuous !n, the second variable of      *)
(* next_lab_ind, so that the induction hypotheses hold for every aux, and   *)
(* drops the n with SIMP_RULE; each case unfolds next_lab once, splits the  *)
(* cases and rewrites once with each induction hypothesis                   *)
let next_lab_EQ_MAX = prove
 (`!(q:(A)stack_prog) aux. next_lab q aux = MAX aux (next_lab q 0)`,
  SUBGOAL_THEN
    `!(q:(A)stack_prog) (n:num) aux. next_lab q aux = MAX aux (next_lab q 0)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC next_lab_ind THEN REPEAT GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[next_lab_def])) THEN
  CASE_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN
  TRY (DISCH_THEN (fun th ->
    MAP_EVERY (fun c -> ONCE_REWRITE_TAC[c]) (CONJUNCTS (CAKE_SIMP_RULE [] th)))) THEN
  GEN_TAC THEN ARITH_TAC);;

(* HOL4 line 6123 (local) *)
let MAX_SIMP = prove
 (`!n m. MAX n (MAX n m) = MAX n m`,
  REWRITE_TAC[MAX_DEF] THEN ARITH_TAC);;

(* HOL4 line 6129 *)
let next_lab_thm = prove
 (CASE_TERM
  `!p:(A)stack_prog.
     next_lab p 2 =
     match p with
       stack_Seq p1 p2 -> MAX (next_lab p1 2) (next_lab p2 2)
     | stack_If _ _ _ p1 p2 -> MAX (next_lab p1 2) (next_lab p2 2)
     | stack_Loop p -> next_lab p 2
     | stack_Call NONE _ NONE -> 2
     | stack_Call NONE _ (SOME (_,_,l2)) -> MAX (l2 + 2) 2
     | stack_Call (SOME (p,_,_,l2)) _ NONE -> MAX (next_lab p 2) (l2 + 2)
     | stack_Call (SOME (p,_,_,l2)) _ (SOME (p',_,l3)) ->
         MAX (MAX (next_lab p 2) (next_lab p' 2)) (MAX l2 l3 + 2)
     | _ -> 2`,
  GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[next_lab_def])) THEN
  CASE_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN
  ONCE_REWRITE_TAC[next_lab_EQ_MAX] THEN ONCE_REWRITE_TAC[next_lab_EQ_MAX] THEN
  ONCE_REWRITE_TAC[next_lab_EQ_MAX] THEN ARITH_TAC);;

(* HOL4 line 6156 *)
let extract_labels_next_lab = prove
 (`!(p:(A)stack_prog) (aux:num) e.
     MEM e (stack_extract_labels p) ==> SND e < next_lab p 2`,
  MATCH_MP_TAC next_lab_ind THEN REPEAT GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  DISCH_THEN (CAKE_ASSUME_TAC o CAKE_SIMP_RULE[] o CASE_REWRITE_RULE[]) THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[next_lab_thm] THEN
  CASE_REWRITE_TAC[stack_extract_labels_def; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN REWRITE_TAC[MEM; MEM_APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN RES_TAC THEN ASM_ARITH_TAC);;

(* helpers for stack_alloc_lab_pres: the label reasoning of one case of comp *)
(* on lists (H the labels of a Call, L1 and L2 those of the subprograms, M1  *)
(* and M2 those of their compiled versions, nl <= m1 <= m2 the counters)    *)

let STTAILAUX_lab_pres_APPEND = prove
 (`!(good:num#num->bool) H L1 L2 M1 M2 nl m1 m2.
     ALL good (APPEND (APPEND H L1) L2) /\
     ALL_DISTINCT (APPEND (APPEND H L1) L2) /\
     (!lab. MEM lab (APPEND (APPEND H L1) L2) ==> SND lab < nl) /\
     ALL good M1 /\ ALL_DISTINCT M1 /\
     (!lab. MEM lab M1 ==> MEM lab L1 \/ nl <= SND lab /\ SND lab < m1) /\
     nl <= m1 /\
     ALL good M2 /\ ALL_DISTINCT M2 /\
     (!lab. MEM lab M2 ==> MEM lab L2 \/ m1 <= SND lab /\ SND lab < m2) /\
     m1 <= m2
     ==> ALL good (APPEND (APPEND H M1) M2) /\
         ALL_DISTINCT (APPEND (APPEND H M1) M2) /\
         (!lab. MEM lab (APPEND (APPEND H M1) M2)
                ==> MEM lab (APPEND (APPEND H L1) L2) \/
                    nl <= SND lab /\ SND lab < m2) /\
         nl <= m2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_APPEND; ALL_DISTINCT_APPEND; MEM_APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY (MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m1:num` THEN ASM_REWRITE_TAC[] THEN
       NO_TAC) THEN
  X_GEN_TAC `e:num#num` THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC `e:num#num`)) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THEN ASM_REWRITE_TAC[])
    [`MEM (e:num#num) H`; `MEM (e:num#num) L1`; `MEM (e:num#num) L2`;
     `MEM (e:num#num) M1`; `MEM (e:num#num) M2`] THEN
  ARITH_TAC);;

let STTAILAUX_MAX_LE = ARITH_RULE `!a b c. MAX a b <= c <=> a <= c /\ b <= c`;;

(* the Seq and If case, with the induction hypotheses as antecedents *)
let STTAILAUX_lab_pres_Seq = prove
 (`!(good:num#num->bool) L0 L1 M0 M1 N0 N1 m m1 m2.
     (ALL good L0 /\ ALL_DISTINCT L0 /\ N0 <= m
      ==> ALL good M0 /\ ALL_DISTINCT M0 /\
          (!lab. MEM lab M0 ==> MEM lab L0 \/ m <= SND lab /\ SND lab < m1) /\
          m <= m1)
     ==> (ALL good L1 /\ ALL_DISTINCT L1 /\ N1 <= m1
          ==> ALL good M1 /\ ALL_DISTINCT M1 /\
              (!lab. MEM lab M1 ==> MEM lab L1 \/ m1 <= SND lab /\ SND lab < m2) /\
              m1 <= m2)
     ==> (!lab. MEM lab L0 ==> SND lab < N0) /\ (!lab. MEM lab L1 ==> SND lab < N1)
     ==> ALL good (APPEND L0 L1) /\ ALL_DISTINCT (APPEND L0 L1) /\ MAX N0 N1 <= m
     ==> ALL good (APPEND M0 M1) /\ ALL_DISTINCT (APPEND M0 M1) /\
         (!lab. MEM lab (APPEND M0 M1)
                ==> MEM lab (APPEND L0 L1) \/ m <= SND lab /\ SND lab < m2) /\
         m <= m2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`good:num#num->bool`; `[]:(num#num)list`; `L0:(num#num)list`;
    `L1:(num#num)list`; `M0:(num#num)list`; `M1:(num#num)list`; `m:num`; `m1:num`;
    `m2:num`] STTAILAUX_lab_pres_APPEND) THEN
  REWRITE_TAC[APPEND] THEN DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL_DISTINCT_APPEND; STTAILAUX_MAX_LE]) THEN
  ASM_REWRITE_TAC[ALL_APPEND; ALL_DISTINCT_APPEND; MEM_APPEND] THEN
  SUBGOAL_THEN `ALL (good:num#num->bool) M0 /\ ALL_DISTINCT M0 /\
     (!lab. MEM lab M0 ==> MEM lab L0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1`
    STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (good:num#num->bool) M1 /\ ALL_DISTINCT M1 /\
     (!lab. MEM lab M1 ==> MEM lab L1 \/ m1 <= SND lab /\ SND lab < m2) /\ m1 <= m2`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

(* the Call case without a handler *)
let STTAILAUX_lab_pres_Call1 = prove
 (`!(good:num#num->bool) l1 l2 L0 M0 N0 m m1.
     (ALL good L0 /\ ALL_DISTINCT L0 /\ N0 <= m
      ==> ALL good M0 /\ ALL_DISTINCT M0 /\
          (!lab. MEM lab M0 ==> MEM lab L0 \/ m <= SND lab /\ SND lab < m1) /\
          m <= m1)
     ==> (!lab. MEM lab L0 ==> SND lab < N0)
     ==> ALL good (APPEND [l1,l2] L0) /\ ALL_DISTINCT (APPEND [l1,l2] L0) /\
         MAX N0 (l2 + 2) <= m
     ==> ALL good (APPEND [l1,l2] M0) /\ ALL_DISTINCT (APPEND [l1,l2] M0) /\
         (!lab. MEM lab (APPEND [l1,l2] M0)
                ==> MEM lab (APPEND [l1,l2] L0) \/ m <= SND lab /\ SND lab < m1) /\
         m <= m1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`good:num#num->bool`; `[l1,l2]:(num#num)list`; `L0:(num#num)list`;
    `[]:(num#num)list`; `M0:(num#num)list`; `[]:(num#num)list`; `m:num`; `m1:num`;
    `m1:num`] STTAILAUX_lab_pres_APPEND) THEN
  REWRITE_TAC[APPEND_NIL; ALL; ALL_DISTINCT; MEM; LE_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL_DISTINCT_APPEND; STTAILAUX_MAX_LE]) THEN
  SUBGOAL_THEN `ALL (good:num#num->bool) M0 /\ ALL_DISTINCT M0 /\
     (!lab. MEM lab M0 ==> MEM lab L0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1`
    STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL_APPEND; ALL_DISTINCT_APPEND; MEM_APPEND; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN RES_TAC THEN ASM_ARITH_TAC);;

(* the Call case with a handler *)
let STTAILAUX_lab_pres_Call2 = prove
 (`!(good:num#num->bool) l1 l2 k1 k2 L0 L1 M0 M1 N0 N1 m m1 m2.
     (ALL good L0 /\ ALL_DISTINCT L0 /\ N0 <= m
      ==> ALL good M0 /\ ALL_DISTINCT M0 /\
          (!lab. MEM lab M0 ==> MEM lab L0 \/ m <= SND lab /\ SND lab < m1) /\
          m <= m1)
     ==> (ALL good L1 /\ ALL_DISTINCT L1 /\ N1 <= m1
          ==> ALL good M1 /\ ALL_DISTINCT M1 /\
              (!lab. MEM lab M1 ==> MEM lab L1 \/ m1 <= SND lab /\ SND lab < m2) /\
              m1 <= m2)
     ==> (!lab. MEM lab L0 ==> SND lab < N0) /\ (!lab. MEM lab L1 ==> SND lab < N1)
     ==> ALL good (APPEND (APPEND [l1,l2; k1,k2] L0) L1) /\
         ALL_DISTINCT (APPEND (APPEND [l1,l2; k1,k2] L0) L1) /\
         MAX (MAX N0 N1) (MAX l2 k2 + 2) <= m
     ==> ALL good (APPEND (APPEND [l1,l2; k1,k2] M0) M1) /\
         ALL_DISTINCT (APPEND (APPEND [l1,l2; k1,k2] M0) M1) /\
         (!lab. MEM lab (APPEND (APPEND [l1,l2; k1,k2] M0) M1)
                ==> MEM lab (APPEND (APPEND [l1,l2; k1,k2] L0) L1) \/
                    m <= SND lab /\ SND lab < m2) /\
         m <= m2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`good:num#num->bool`; `[l1,l2; k1,k2]:(num#num)list`;
    `L0:(num#num)list`; `L1:(num#num)list`; `M0:(num#num)list`; `M1:(num#num)list`;
    `m:num`; `m1:num`; `m2:num`] STTAILAUX_lab_pres_APPEND) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL_APPEND; ALL_DISTINCT_APPEND; STTAILAUX_MAX_LE]) THEN
  SUBGOAL_THEN `ALL (good:num#num->bool) M0 /\ ALL_DISTINCT M0 /\
     (!lab. MEM lab M0 ==> MEM lab L0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1`
    STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (good:num#num->bool) M1 /\ ALL_DISTINCT M1 /\
     (!lab. MEM lab M1 ==> MEM lab L1 \/ m1 <= SND lab /\ SND lab < m2) /\ m1 <= m2`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL_APPEND; ALL_DISTINCT_APPEND; MEM_APPEND; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN RES_TAC THEN ASM_ARITH_TAC);;

(* after a case split of stack_alloc_comp n m p: the induction hypotheses   *)
(* are simplified and rewritten with the equations stack_alloc_comp n m q = *)
(* (q',m') that the split put in the assumptions                            *)
let STTAILAUX_COMP_EQ_TAC : tactic =
  ASSUM_LIST (fun thl ->
    let is_comp_eq th =
      let c = concl th in
      is_eq c && is_pair (rhs c) &&
      (try fst(dest_const(fst(strip_comb(lhs c)))) = "stack_alloc_comp"
       with Failure _ -> false) in
    let eqs = filter is_comp_eq thl in
    RULE_ASSUM_TAC (fun th -> if is_comp_eq th then th else CAKE_SIMP_RULE eqs th));;

(* HOL4 line 6167 *)
(* the vacuous aux has an unconstrained type in HOL4: B here *)
let stack_alloc_lab_pres = prove
 (CASE_TERM
  `!n nl (p:(A)stack_prog) (aux:B).
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
     ALL_DISTINCT (stack_extract_labels p) /\
     next_lab p 2 <= nl
     ==> let (cp,nl') = stack_alloc_comp n nl p in
         ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels cp) /\
         ALL_DISTINCT (stack_extract_labels cp) /\
         (!lab. MEM lab (stack_extract_labels cp)
                ==> MEM lab (stack_extract_labels p) \/ nl <= SND lab /\ SND lab < nl') /\
         nl <= nl'`,
  MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  DISCH_THEN (CAKE_ASSUME_TAC o CAKE_SIMP_RULE[] o CASE_REWRITE_RULE[]) THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN ONCE_REWRITE_TAC[next_lab_thm] THEN
  CASE_REWRITE_TAC[stack_extract_labels_def; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN REPEAT (CHANGED_TAC STTAILAUX_COMP_EQ_TAC) THEN
  CASE_REWRITE_TAC[stack_extract_labels_def; LET_DEF; LET_END_DEF] THEN
  FIRST (map (fun t -> t THEN NO_TAC)
   [SIMP_NOASM[APPEND; ALL; ALL_DISTINCT; MEM] THEN ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM (fun ih0 -> FIRST_ASSUM (fun ih1 ->
      MATCH_MP_TAC (MATCH_MP (MATCH_MP STTAILAUX_lab_pres_Seq ih0) ih1))) THEN
      SIMP_TAC[extract_labels_next_lab];
    FIRST_ASSUM (fun ih0 -> MATCH_MP_TAC (MATCH_MP STTAILAUX_lab_pres_Call1 ih0)) THEN
      SIMP_TAC[extract_labels_next_lab];
    FIRST_ASSUM (fun ih0 -> FIRST_ASSUM (fun ih1 ->
      MATCH_MP_TAC (MATCH_MP (MATCH_MP STTAILAUX_lab_pres_Call2 ih0) ih1))) THEN
      SIMP_TAC[extract_labels_next_lab]]));;

(* HOL4 line 6217 *)
let stack_alloc_comp_stack_asm_name = prove
 (CASE_TERM
  `!n m (p:(A)stack_prog) (c:(A)asm_config).
     stack_asm_name c p /\ stack_asm_remove c p
     ==> let (p',m') = stack_alloc_comp n m p in
         stack_asm_name c p' /\ stack_asm_remove c p'`,
  MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  DISCH_THEN (CAKE_ASSUME_TAC o CAKE_SIMP_RULE[] o CASE_REWRITE_RULE[]) THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN
  CASE_REWRITE_TAC[stack_asm_name_def; stack_asm_remove_def] THEN
  EVERY_CASE_TAC THEN REPEAT (CHANGED_TAC STTAILAUX_COMP_EQ_TAC) THEN
  CASE_REWRITE_TAC[stack_asm_name_def; stack_asm_remove_def] THEN
  ASM_MESON_TAC[]);;

(* the definitions that make up the gc code of word_gc_code, unfolded where *)
(* HOL4 uses EVAL_TAC or the definitions                                    *)
let STTAILAUX_gc_code_defs =
  [word_gc_partial_or_full_def; SetNewTrigger_def; memcpy_code_def;
   clear_top_inst_def;
   word_gc_move_code_def; word_gc_move_list_code_def; word_gc_move_loop_code_def;
   word_gc_move_roots_bitmaps_code_def; word_gc_move_bitmaps_code_def;
   word_gc_move_bitmap_code_def; word_gen_gc_move_code_def;
   word_gen_gc_move_list_code_def; word_gen_gc_move_roots_bitmaps_code_def;
   word_gen_gc_move_bitmaps_code_def; word_gen_gc_move_bitmap_code_def;
   word_gen_gc_move_data_code_def; word_gen_gc_move_refs_code_def;
   word_gen_gc_move_loop_code_def; word_gen_gc_partial_move_code_def;
   word_gen_gc_partial_move_list_code_def;
   word_gen_gc_partial_move_roots_bitmaps_code_def;
   word_gen_gc_partial_move_bitmaps_code_def;
   word_gen_gc_partial_move_bitmap_code_def;
   word_gen_gc_partial_move_data_code_def;
   word_gen_gc_partial_move_ref_list_code_def;
   APPEND; stack_list_Seq_def];;

(* the shift amounts of the gc code are in range and not 0 *)
let STTAILAUX_word_shift_ok = prove
 (`!k. 0 < k /\ k < dimindex(:A)
       ==> val (word k:A word) < dimindex(:A) /\ ~(word k:A word = word 0)`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC VAL_WORD_LT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `k:num` (INST_TYPE [`:A`,`:N`] WORD_EQ_0)) THEN ANTS_TAC THENL
     [TRANS_TAC LT_TRANS `dimindex(:A)` THEN ASM_REWRITE_TAC[LT_POW2_REFL];
      DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC]]);;

(* the gc stub of stack_alloc_compile satisfies stack_asm_name and          *)
(* stack_asm_remove (the EVAL_TAC part of the HOL4 proof below)            *)
let STTAILAUX_stubs_asm = prove
 (`!(c:(A)asm_config) conf.
     conf_ok (:A) conf /\ asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     reg_name 10 c /\ good_dimindex(:A) /\
     asm_config_valid_imm c (INL asm_Add) (word 8) /\
     asm_config_valid_imm c (INL asm_Add) (word 4) /\
     asm_config_valid_imm c (INL asm_Add) (word 1) /\
     asm_config_valid_imm c (INL asm_Sub) (word 1)
     ==> stack_asm_name c (stack_Seq (word_gc_code conf) (stack_Return 0)) /\
         stack_asm_remove c (stack_Seq (word_gc_code conf) (stack_Return 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `reg_name 0 (c:(A)asm_config) /\ reg_name 1 c /\ reg_name 2 c /\
     reg_name 3 c /\ reg_name 4 c /\ reg_name 5 c /\ reg_name 6 c /\ reg_name 7 c /\
     reg_name 8 c /\ reg_name 9 c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `reg_name 10 (c:(A)asm_config)` THEN REWRITE_TAC[reg_name_def] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `asm_config_valid_imm (c:(A)asm_config) (INL asm_Add) bytes_in_word`
    ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[bytes_in_word_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun e -> MP_TAC(ISPEC e STTAILAUX_word_shift_ok) THEN ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`conf_ok (:A) conf`; `good_dimindex(:A)`] THEN
      REWRITE_TAC[conf_ok_def; good_dimindex_def; backend_common_word_shift_def;
                  shift_length_def; small_shift_length_def] THEN ARITH_TAC;
      STRIP_TAC])
    [`2`; `backend_common_word_shift(:A)`; `shift_length conf`;
     `dimindex (:A) - (small_shift_length conf - 1) - 1`; `1`; `dimindex (:A) - 1`;
     `dimindex (:A) - data_to_word_config_len_size conf`] THEN
  REWRITE_TAC[word_gc_code_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[word_gc_partial_or_full_def] THEN TRY TOP_CASE_TAC THEN
  REWRITE_TAC(IN_INSERT :: NOT_IN_EMPTY :: stack_asm_name_def :: stack_asm_remove_def ::
              inst_name_def :: arith_name_def :: addr_name_def :: reg_imm_name_def ::
              STTAILAUX_gc_code_defs) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6239; HOL4: stack_alloc_stack_asm_convs *)
(* HOL4 comment on conf_ok (:A) conf: conf_ok is too strong, but we already *)
(* have it anyway; addr_offset_ok c 0w is written out (asm.ml)              *)
let stack_allocProof_stack_alloc_stack_asm_convs = prove
 (`!(c:(A)asm_config) (prog:(num#(A)stack_prog)list) conf.
     ALL (\(n,p). stack_asm_name c p) prog /\
     ALL (\(n,p). stack_asm_remove c p) prog /\
     conf_ok (:A) conf /\
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     reg_name 10 c /\ good_dimindex(:A) /\
     asm_config_valid_imm c (INL asm_Add) (word 8) /\
     asm_config_valid_imm c (INL asm_Add) (word 4) /\
     asm_config_valid_imm c (INL asm_Add) (word 1) /\
     asm_config_valid_imm c (INL asm_Sub) (word 1)
     ==> ALL (\(n,p). stack_asm_name c p) (stack_alloc_compile conf prog) /\
         ALL (\(n,p). stack_asm_remove c p) (stack_alloc_compile conf prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[stack_alloc_compile_def; stack_alloc_stubs_def; ALL_APPEND; ALL] THEN
  MP_TAC(SPECL [`c:(A)asm_config`; `conf:data_to_word_config`] STTAILAUX_stubs_asm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM]) THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; stack_alloc_prog_comp_def] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`p1:num`; `p2:(A)stack_prog`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p1:num`; `next_lab (p2:(A)stack_prog) 2`; `p2:(A)stack_prog`;
                 `c:(A)asm_config`] stack_alloc_comp_stack_asm_name) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  SPEC_TAC(`stack_alloc_comp p1 (next_lab (p2:(A)stack_prog) 2) p2`,
           `q:(A)stack_prog#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[FST]);;

(* the comp part of stack_alloc_reg_bound (HOL4 proves it inside the proof *)
(* by comp_ind)                                                             *)
let STTAILAUX_comp_reg_bound = prove
 (`!sp n m (p:(A)stack_prog).
     10 <= sp /\ reg_bound p sp ==> reg_bound (FST (stack_alloc_comp n m p)) sp`,
  GEN_TAC THEN MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  DISCH_THEN (CAKE_ASSUME_TAC o CAKE_SIMP_RULE[] o CASE_REWRITE_RULE[]) THEN
  ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN
  CASE_REWRITE_TAC[reg_bound_def] THEN
  EVERY_CASE_TAC THEN REPEAT (CHANGED_TAC STTAILAUX_COMP_EQ_TAC) THEN
  CASE_REWRITE_TAC[reg_bound_def; FST] THEN
  ASM_MESON_TAC[ARITH_RULE `!sp. 10 <= sp ==> 0 < sp`]);;

(* HOL4 line 6270 *)
let stack_alloc_reg_bound = prove
 (`!sp (prog1:(num#(A)stack_prog)list) dc.
     10 <= sp /\ ALL (\p. reg_bound p sp) (MAP SND prog1)
     ==> ALL (\p. reg_bound p sp) (MAP SND (stack_alloc_compile dc prog1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_alloc_compile_def; MAP_APPEND; ALL_APPEND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[stack_alloc_stubs_def; MAP; ALL] THEN
    SUBGOAL_THEN `0 < sp /\ 1 < sp /\ 2 < sp /\ 3 < sp /\ 4 < sp /\ 5 < sp /\ 6 < sp /\
      7 < sp /\ 8 < sp /\ 9 < sp` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[word_gc_code_def] THEN TOP_CASE_TAC THEN
    REWRITE_TAC[word_gc_partial_or_full_def] THEN TRY TOP_CASE_TAC THEN
    REWRITE_TAC(reg_bound_def :: reg_bound_inst_def :: STTAILAUX_gc_code_defs) THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ALL (\p. reg_bound p sp) (MAP SND (prog1:(num#(A)stack_prog)list))` THEN
    SPEC_TAC(`prog1:(num#(A)stack_prog)list`,`prog1:(num#(A)stack_prog)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
    SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; stack_alloc_prog_comp_def; SND] THEN
    ASM_MESON_TAC[STTAILAUX_comp_reg_bound]]);;

(* the comp part of stack_alloc_call_args *)
let STTAILAUX_comp_call_args = prove
 (`!n m (p:(A)stack_prog).
     call_args p 1 2 3 4 0 ==> call_args (FST (stack_alloc_comp n m p)) 1 2 3 4 0`,
  MATCH_MP_TAC stack_alloc_comp_ind THEN REPEAT GEN_TAC THEN
  CASES_ON `p:(A)stack_prog` THEN
  DISCH_THEN (CAKE_ASSUME_TAC o CAKE_SIMP_RULE[] o CASE_REWRITE_RULE[]) THEN
  ONCE_REWRITE_TAC[stack_alloc_comp_def] THEN
  CASE_REWRITE_TAC[call_args_def] THEN
  EVERY_CASE_TAC THEN REPEAT (CHANGED_TAC STTAILAUX_COMP_EQ_TAC) THEN
  CASE_REWRITE_TAC[call_args_def; FST] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 6304; HOL4: stack_alloc_call_args *)
let stack_allocProof_stack_alloc_call_args = prove
 (`!(prog1:(num#(A)stack_prog)list) dc.
     ALL (\p. call_args p 1 2 3 4 0) (MAP SND prog1)
     ==> ALL (\p. call_args p 1 2 3 4 0) (MAP SND (stack_alloc_compile dc prog1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_alloc_compile_def; MAP_APPEND; ALL_APPEND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[stack_alloc_stubs_def; MAP; ALL] THEN
    REWRITE_TAC[word_gc_code_def] THEN TOP_CASE_TAC THEN
    REWRITE_TAC[word_gc_partial_or_full_def] THEN TRY TOP_CASE_TAC THEN
    REWRITE_TAC(call_args_def :: STTAILAUX_gc_code_defs) THEN
    CASE_REWRITE_TAC[];
    UNDISCH_TAC
      `ALL (\p. call_args p 1 2 3 4 0) (MAP SND (prog1:(num#(A)stack_prog)list))` THEN
    SPEC_TAC(`prog1:(num#(A)stack_prog)list`,`prog1:(num#(A)stack_prog)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL] THEN
    SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; stack_alloc_prog_comp_def; SND] THEN
    ASM_MESON_TAC[STTAILAUX_comp_call_args]]);;

(* HOL4 line 6333 *)
(* HOL4 dconf with <| has_fp_ops := b1; has_fp_tern := b2 |> *)
let compile_has_fp_ops = prove
 (`!dconf b1 b2 (code:(num#(A)stack_prog)list).
     stack_alloc_compile
       (data_to_word_config_has_fp_ops_fupd (K b1)
         (data_to_word_config_has_fp_tern_fupd (K b2) dconf)) code =
     stack_alloc_compile dconf code`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_alloc_compile_def; stack_alloc_stubs_def] THEN
  REWRITE_TAC((record_info "data_to_word_config").ri_accfupds :: word_gc_code_def ::
              shift_length_def :: small_shift_length_def :: STTAILAUX_gc_code_defs));;
let _ = cake_add_simps [compile_has_fp_ops];;
