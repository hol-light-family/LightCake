(* ========================================================================= *)
(* stack_allocProof_p2: part 2 of 3 of the port of                          *)
(* compiler/backend/proofs/stack_allocProofScript.sml (HOL4 lines           *)
(* 1717-4591): gc_kind = Generational, the generational collector's code   *)
(* (word_gen_gc_..._code) against its functional specification.            *)
(* Part 1 is stack_allocProof_p1.ml; part 3 is stack_allocProof.ml.         *)
(* The evaluator infrastructure (STALLOCAUX_EV_TAC and friends) is in p1.   *)
(* ========================================================================= *)

needs "compiler/backend/proofs/stack_allocProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ========================================================================= *)
(* gc_kind = Generational (HOL4 lines 1717-4591)                            *)
(* ========================================================================= *)

let STALLOCAUX_word_add_sub_cancel = prove
 (`!x y:A word. word_add x (word_sub y x) = y`,
  CONV_TAC WORD_RULE);;

(* HOL4 line 1731 (local; a second word_gc_fun_thm in HOL4, for         *)
(* gc_kind = Generational; HOL4 word_gc_fun_lemma, line 1719, unfolded)   *)
let STALLOCAUX_word_gc_fun_thm_gen = prove
 (`!conf gen_sizes roots m dm (s:(store_name,(A)word_loc)fmap).
   data_to_word_config_gc_kind conf = Generational gen_sizes ==>
   word_gc_fun conf (roots,m,dm,s) =
     if ~word_gc_fun_assum conf s then NONE else
     if word_gen_gc_can_do_partial gen_sizes s then
       (let (roots1,i1,pa1,m1,c1) =
              word_gen_gc_partial_move_roots conf
                (CONS (FAPPLY s Globals) roots,
                 word_ushr (theWord (FAPPLY s GenStart)) (backend_common_word_shift (:A)),
                 theWord (FAPPLY s OtherHeap),theWord (FAPPLY s CurrHeap),m,dm,
                 theWord (FAPPLY s GenStart),
                 word_sub (theWord (FAPPLY s EndOfHeap)) (theWord (FAPPLY s CurrHeap))) in
        let (i2,pa2,m2,c2) =
              word_gen_gc_partial_move_ref_list (dimword (:A)) conf
                (theWord (FAPPLY s EndOfHeap),i1,pa1,theWord (FAPPLY s CurrHeap),m1,dm,c1,
                 theWord (FAPPLY s GenStart),
                 word_sub (theWord (FAPPLY s EndOfHeap)) (theWord (FAPPLY s CurrHeap)),
                 word_add (theWord (FAPPLY s CurrHeap)) (theWord (FAPPLY s HeapLength))) in
        let (i3,pa3,m3,c3) =
              word_gen_gc_partial_move_data conf (dimword (:A))
                (theWord (FAPPLY s OtherHeap),i2,pa2,theWord (FAPPLY s CurrHeap),m2,dm,
                 theWord (FAPPLY s GenStart),
                 word_sub (theWord (FAPPLY s EndOfHeap)) (theWord (FAPPLY s CurrHeap))) in
        let (b1,m4,c4) =
              memcpy (word_ushr (word_sub pa3 (theWord (FAPPLY s OtherHeap)))
                                (backend_common_word_shift (:A)))
                (theWord (FAPPLY s OtherHeap))
                (word_add (theWord (FAPPLY s CurrHeap)) (theWord (FAPPLY s GenStart))) m3 dm in
          if ((c2 /\ c3) /\ c4) /\
             word_ule (theWord (FAPPLY s AllocSize))
                      (word_sub (theWord (FAPPLY s EndOfHeap)) b1) /\
             word_ule (theWord (FAPPLY s AllocSize))
                      (new_trig (word_sub (theWord (FAPPLY s EndOfHeap)) b1)
                                (theWord (FAPPLY s AllocSize)) gen_sizes)
          then SOME (TL roots1,m4,
                     s |++
                     [(CurrHeap,wl_Word (theWord (FAPPLY s CurrHeap)));
                      (OtherHeap,wl_Word (theWord (FAPPLY s OtherHeap)));
                      (NextFree,wl_Word b1);
                      (GenStart,wl_Word (word_sub b1 (theWord (FAPPLY s CurrHeap))));
                      (TriggerGC,wl_Word (word_add b1
                         (new_trig (word_sub (theWord (FAPPLY s EndOfHeap)) b1)
                                   (theWord (FAPPLY s AllocSize)) gen_sizes)));
                      (Globals,HD roots1);
                      (GlobReal,glob_real conf (theWord (FAPPLY s CurrHeap)) (HD roots1));
                      (Temp (word 0),wl_Word (word 0)); (Temp (word 1),wl_Word (word 0))])
          else NONE)
     else
      (let new_end = word_add (theWord (FAPPLY s OtherHeap)) (theWord (FAPPLY s HeapLength)) in
       let len = word_ushr (theWord (FAPPLY s HeapLength)) (backend_common_word_shift (:A)) in
       let (w1,i1,pa1,ib1,pb1,m1,c1) =
              word_gen_gc_move conf
                (FAPPLY s Globals,word 0,theWord (FAPPLY s OtherHeap),
                 len,new_end,theWord (FAPPLY s CurrHeap),m,dm) in
       let (ws2,i2,pa2,ib2,pb2,m2,c2) =
              word_gen_gc_move_roots conf
                (roots,i1,pa1,ib1,pb1,theWord (FAPPLY s CurrHeap),m1,dm) in
       let (i3,pa3,ib3,pb3,m3,c3) =
             word_gen_gc_move_loop conf (val len)
               (theWord (FAPPLY s OtherHeap),i2,pa2,ib2,pb2,new_end,
                theWord (FAPPLY s CurrHeap),m2,dm) in
       let a = theWord (FAPPLY s AllocSize) in
       let s1 =
             s |++
             [(CurrHeap,wl_Word (theWord (FAPPLY s OtherHeap)));
              (OtherHeap,wl_Word (theWord (FAPPLY s CurrHeap)));
              (NextFree,wl_Word pa3);
              (GenStart,wl_Word (word_sub pa3 (theWord (FAPPLY s OtherHeap))));
              (TriggerGC,wl_Word (word_add pa3 (new_trig (word_sub pb3 pa3) a gen_sizes)));
              (EndOfHeap,wl_Word pb3); (Globals,w1);
              (GlobReal,glob_real conf (theWord (FAPPLY s OtherHeap)) w1);
              (Temp (word 0),wl_Word (word 0));
              (Temp (word 1),wl_Word (word 0));
              (Temp (word 2),wl_Word (word 0));
              (Temp (word 3),wl_Word (word 0));
              (Temp (word 4),wl_Word (word 0));
              (Temp (word 5),wl_Word (word 0));
              (Temp (word 6),wl_Word (word 0))]
       in
         if word_gc_fun_assum conf s /\ c1 /\ c2 /\ c3
         then SOME (ws2,m3,s1)
         else NONE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[word_gc_fun_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `word_gc_fun_assum conf (s:(store_name,(A)word_loc)fmap)` THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_gen_gc_partial_full_def; word_gen_gc_partial_def; LET_DEF; LET_END_DEF;
                STALLOCAUX_word_add_sub_cancel] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["roots1";"i1";"pa1";"m1";"c1"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_ref_list" ["i2";"pa2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_data" ["i3";"pa3";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "memcpy" ["b1";"m4";"c4"] THEN
    REWRITE_TAC[];
    REWRITE_TAC[word_gen_gc_def; LET_DEF; LET_END_DEF; word_gen_gc_move_roots_def] THEN
    CASE_REWRITE_TAC[] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["w1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    REWRITE_TAC[HD; TL; CONJ_ACI]]);;

(* HOL4 line 1842 *)
let word_gen_gc_move_roots_bitmaps_def = cake_def
  `word_gen_gc_move_roots_bitmaps (conf:data_to_word_config)
     (stack:((A)word_loc)list,bitmaps:(A word)list,i1:A word,pa1:A word,ib1:A word,
      pb1:A word,curr:A word,m:A word->(A)word_loc,dm:A word->bool) =
     match stack_enc_stack bitmaps stack with
       NONE -> (ARB,ARB,ARB,ARB,ARB,ARB,F)
     | SOME wl_list ->
         let (wl,i2,pa2,ib2,pb2,m2,c2) =
             word_gen_gc_move_roots conf (wl_list,i1,pa1,ib1,pb1,curr,m,dm) in
         (match stack_dec_stack bitmaps wl stack with
            NONE -> (ARB,ARB,ARB,ARB,ARB,ARB,F)
          | SOME stack -> (stack,i2,pa2,ib2,pb2,m2,c2))`;;

(* HOL4 line 1854 *)
let word_gen_gc_partial_move_roots_bitmaps_def = cake_def
  `word_gen_gc_partial_move_roots_bitmaps (conf:data_to_word_config)
     (stack:((A)word_loc)list,bitmaps:(A word)list,i1:A word,pa1:A word,curr:A word,
      m:A word->(A)word_loc,dm:A word->bool,gs:A word,rs:A word) =
     match stack_enc_stack bitmaps stack with
       NONE -> (ARB,ARB,ARB,ARB,F)
     | SOME wl_list ->
         let (wl,i2,pa2,m2,c2) =
             word_gen_gc_partial_move_roots conf (wl_list,i1,pa1,curr,m,dm,gs,rs) in
         (match stack_dec_stack bitmaps wl stack with
            NONE -> (ARB,ARB,ARB,ARB,F)
          | SOME stack -> (stack,i2,pa2,m2,c2))`;;

(* HOL4 line 1866 *)
let word_gen_gc_partial_move_ref_list_ok = prove
 (`!k rs re (pb:A word) pa old m i gs dm conf c i1 pa1 m1.
     word_gen_gc_partial_move_ref_list k conf (pb,i,pa,old,m,dm,c,gs,rs,re) =
       (i1,pa1,m1,T) ==> c`,
  INDUCT_TAC THEN ONCE_REWRITE_TAC[word_gen_gc_partial_move_ref_list_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN TRY (MESON_TAC[]) THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_list" ["pb1";"i2";"pa2";"m2";"c2"] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  MESON_TAC[]);;

(* the result flag of word_gen_gc_partial_move_ref_list implies its input   *)
(* flag: case split on the result flag of the ref_list assumption           *)
let STALLOCAUX_REF_LIST_OK_TAC : tactic = fun (asl,w as g) ->
  let th = snd(find (fun (_,th) ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
        "word_gen_gc_partial_move_ref_list"
    with Failure _ -> false) asl) in
  let c3 = rand(rand(rand(rhs(concl th)))) in
  (ASM_CASES_TAC c3 THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(MATCH_MP word_gen_gc_partial_move_ref_list_ok (REWRITE_RULE[ASSUME c3] th)) THEN
   ASM_REWRITE_TAC[]) g;;

(* HOL4 line 1884 (local; a second gc_thm in HOL4, for Generational;     *)
(* the HOL4 val gc_lemma, line 1835, is unfolded here)                      *)
let STALLOCAUX_gc_thm_gen = prove
 (`!conf gen_sizes (s:(A,C,FFI)stack_state).
   stack_state_gc_fun s = word_gc_fun conf /\
   data_to_word_config_gc_kind conf = Generational gen_sizes ==>
   stack_gc s =
   if LENGTH (stack_state_stack s) < stack_state_stack_space s then NONE else
   if ~word_gc_fun_assum conf (stack_state_store s) then NONE else
   if word_gen_gc_can_do_partial gen_sizes (stack_state_store s) then
     (let unused = TAKE (stack_state_stack_space s) (stack_state_stack s) in
      let stack = DROP (stack_state_stack_space s) (stack_state_stack s) in
      let gs = theWord (FAPPLY (stack_state_store s) GenStart) in
      let other = theWord (FAPPLY (stack_state_store s) OtherHeap) in
      let curr = theWord (FAPPLY (stack_state_store s) CurrHeap) in
      let endh = theWord (FAPPLY (stack_state_store s) EndOfHeap) in
      let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf
             (FAPPLY (stack_state_store s) Globals,
              word_ushr gs (backend_common_word_shift (:A)),other,curr,
              stack_state_memory s,stack_state_mdomain s,gs,word_sub endh curr) in
      let (ws2,i2,pa2,m2,c2) = word_gen_gc_partial_move_roots_bitmaps conf
             (stack,stack_state_bitmaps s,i1,pa1,curr,m1,stack_state_mdomain s,gs,
              word_sub endh curr) in
      let (i3,pa3,m3,c3) =
             word_gen_gc_partial_move_ref_list (dimword (:A)) conf
              (endh,i2,pa2,curr,m2,stack_state_mdomain s,(c1 /\ c2),gs,
               word_sub endh curr,
               word_add curr (theWord (FAPPLY (stack_state_store s) HeapLength))) in
      let (i4,pa4,m4,c4) = word_gen_gc_partial_move_data conf (dimword (:A))
              (other,i3,pa3,curr,m3,stack_state_mdomain s,gs,word_sub endh curr) in
      let (b1,m5,c5) =
             memcpy (word_ushr (word_sub pa4 other) (backend_common_word_shift (:A)))
                    other (word_add curr gs) m4 (stack_state_mdomain s) in
      let s1 = stack_state_store s |++
               [(CurrHeap,wl_Word curr);
                (OtherHeap,wl_Word other);
                (NextFree,wl_Word b1);
                (GenStart,wl_Word (word_sub b1 curr));
                (TriggerGC,wl_Word (word_add b1 (new_trig
                   (word_sub (theWord (FAPPLY (stack_state_store s) EndOfHeap)) b1)
                   (theWord (FAPPLY (stack_state_store s) AllocSize)) gen_sizes)));
                (Globals,w1);
                (GlobReal,glob_real conf (theWord (FAPPLY (stack_state_store s) CurrHeap)) w1);
                (Temp (word 0),wl_Word (word 0));
                (Temp (word 1),wl_Word (word 0))] in
      let c6 = (word_ule (theWord (FAPPLY (stack_state_store s) AllocSize))
                  (word_sub (theWord (FAPPLY (stack_state_store s) EndOfHeap)) b1) /\
                word_ule (theWord (FAPPLY (stack_state_store s) AllocSize))
                  (new_trig (word_sub (theWord (FAPPLY (stack_state_store s) EndOfHeap)) b1)
                     (theWord (FAPPLY (stack_state_store s) AllocSize)) gen_sizes)) in
        if word_gc_fun_assum conf (stack_state_store s) /\ c3 /\ c4 /\ c5 /\ c6
        then SOME (stack_state_stack_fupd (K (APPEND unused ws2))
                    (stack_state_store_fupd (K s1)
                     (stack_state_regs_fupd (K FEMPTY)
                      (stack_state_memory_fupd (K m5) s))))
        else NONE)
   else
     (let unused = TAKE (stack_state_stack_space s) (stack_state_stack s) in
      let stack = DROP (stack_state_stack_space s) (stack_state_stack s) in
      let new_end = word_add (theWord (FAPPLY (stack_state_store s) OtherHeap))
                             (theWord (FAPPLY (stack_state_store s) HeapLength)) in
      let len = word_ushr (theWord (FAPPLY (stack_state_store s) HeapLength))
                          (backend_common_word_shift (:A)) in
      let (w1,i1,pa1,ib1,pb1,m1,c1) =
               word_gen_gc_move conf
                 (FAPPLY (stack_state_store s) Globals,word 0,
                  theWord (FAPPLY (stack_state_store s) OtherHeap),
                  len,new_end,theWord (FAPPLY (stack_state_store s) CurrHeap),
                  stack_state_memory s,stack_state_mdomain s) in
      let (ws2,i2,pa2,ib2,pb2,m2,c2) =
               word_gen_gc_move_roots_bitmaps conf
                 (stack,stack_state_bitmaps s,i1,pa1,ib1,pb1,
                  theWord (FAPPLY (stack_state_store s) CurrHeap),m1,stack_state_mdomain s) in
      let (i3,pa3,ib3,pb3,m3,c3) =
              word_gen_gc_move_loop conf (val len)
                (theWord (FAPPLY (stack_state_store s) OtherHeap),i2,pa2,ib2,pb2,new_end,
                 theWord (FAPPLY (stack_state_store s) CurrHeap),m2,stack_state_mdomain s) in
      let s1 =
              stack_state_store s |++
              [(CurrHeap,wl_Word (theWord (FAPPLY (stack_state_store s) OtherHeap)));
               (OtherHeap,wl_Word (theWord (FAPPLY (stack_state_store s) CurrHeap)));
               (NextFree,wl_Word pa3);
               (GenStart,wl_Word (word_sub pa3
                                    (theWord (FAPPLY (stack_state_store s) OtherHeap))));
               (TriggerGC,wl_Word (word_add pa3 (new_trig
                  (word_sub pb3 pa3) (theWord (FAPPLY (stack_state_store s) AllocSize))
                  gen_sizes)));
               (EndOfHeap,wl_Word pb3);
               (Globals,w1);
               (GlobReal,glob_real conf (theWord (FAPPLY (stack_state_store s) OtherHeap)) w1);
               (Temp (word 0),wl_Word (word 0));
               (Temp (word 1),wl_Word (word 0));
               (Temp (word 2),wl_Word (word 0));
               (Temp (word 3),wl_Word (word 0));
               (Temp (word 4),wl_Word (word 0));
               (Temp (word 5),wl_Word (word 0));
               (Temp (word 6),wl_Word (word 0))]
      in
        if word_gc_fun_assum conf (stack_state_store s) /\ c1 /\ c2 /\ c3
        then SOME (stack_state_stack_fupd (K (APPEND unused ws2))
                    (stack_state_store_fupd (K s1)
                     (stack_state_regs_fupd (K FEMPTY)
                      (stack_state_memory_fupd (K m3) s))))
        else NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[stack_gc_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[STALLOCAUX_word_gc_fun_thm_gen] THEN
  ASM_CASES_TAC `word_gc_fun_assum conf (stack_state_store (s:(A,C,FFI)stack_state))` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `stack_enc_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state))
              (DROP (stack_state_stack_space s) (stack_state_stack s))` ["wl"] THEN
    CASE_REWRITE_TAC[]] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  STALLOCAUX_OPT_CASES_TAC `stack_enc_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state))
              (DROP (stack_state_stack_space s) (stack_state_stack s))` ["wl"] THEN
  REWRITE_TAC[word_gen_gc_partial_move_roots_bitmaps_def; word_gen_gc_move_roots_bitmaps_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [(STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["w1";"i1";"pa1";"m1";"c1"] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_ref_list" ["i3";"pa3";"m3";"c3"] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_data" ["i4";"pa4";"m4";"c4"] THEN
     STALLOCAUX_SPLIT_FN_TAC "memcpy" ["b1";"m5";"c5"] THEN
     STALLOCAUX_REF_LIST_OK_TAC);
    (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["w1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"]);
    (REWRITE_TAC[word_gen_gc_partial_move_roots_def; LET_DEF; LET_END_DEF] THEN
     CASE_REWRITE_TAC[] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["w1";"i1";"pa1";"m1";"c1"] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["ws";"i2";"pa2";"m2";"c2"] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_ref_list" ["i3";"pa3";"m3";"c3"] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_data" ["i4";"pa4";"m4";"c4"] THEN
     STALLOCAUX_SPLIT_FN_TAC "memcpy" ["b1";"m5";"c5"] THEN
     REWRITE_TAC[HD; TL] THEN
     STALLOCAUX_OPT_CASES_TAC `stack_dec_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state)) ws
                 (DROP (stack_state_stack_space s) (stack_state_stack s))` ["stk"] THEN
     CASE_REWRITE_TAC[] THENL
      [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
       CASE_REWRITE_TAC[] THEN
       STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_ref_list" ["i6";"pa6";"m6";"c6"] THEN
       STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_data" ["i7";"pa7";"m7";"c7"] THEN
       STALLOCAUX_SPLIT_FN_TAC "memcpy" ["b2";"m8";"c8"] THEN
       STALLOCAUX_REF_LIST_OK_TAC;
       ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
       CASE_REWRITE_TAC[]]);
    (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["w1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
     STALLOCAUX_OPT_CASES_TAC `stack_dec_stack (stack_state_bitmaps (s:(A,C,FFI)stack_state)) ws
                 (DROP (stack_state_stack_space s) (stack_state_stack s))` ["stk"] THEN
     CASE_REWRITE_TAC[] THEN
     STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
     TRY (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i4";"pa4";"ib4";"pb4";"m4";"c4"]) THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
     CASE_REWRITE_TAC[])]);;

(* HOL4 line 1999 *)
let word_gen_gc_move_bitmaps_def = cake_def
  `word_gen_gc_move_bitmaps (conf:data_to_word_config)
     (w:(A)word_loc,stack:((A)word_loc)list,bitmaps:(A word)list,i1:A word,pa1:A word,
      ib1:A word,pb1:A word,curr:A word,m:A word->(A)word_loc,dm:A word->bool) =
     match full_read_bitmap bitmaps w with
       NONE -> NONE
     | SOME bs ->
         (match filter_bitmap bs stack with
            NONE -> NONE
          | SOME (ts,ws) ->
              let (wl,i2,pa2,ib2,pb2,m2,c2) =
                    word_gen_gc_move_roots conf (ts,i1,pa1,ib1,pb1,curr,m,dm) in
              (match map_bitmap bs wl stack with
                 NONE -> NONE
               | SOME (hd,ts1,ws') -> SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2)))`;;

(* HOL4 line 2015 *)
let word_gen_gc_partial_move_bitmaps_def = cake_def
  `word_gen_gc_partial_move_bitmaps (conf:data_to_word_config)
     (w:(A)word_loc,stack:((A)word_loc)list,bitmaps:(A word)list,i1:A word,pa1:A word,
      curr:A word,m:A word->(A)word_loc,dm:A word->bool,gs:A word,rs:A word) =
     match full_read_bitmap bitmaps w with
       NONE -> NONE
     | SOME bs ->
         (match filter_bitmap bs stack with
            NONE -> NONE
          | SOME (ts,ws) ->
              let (wl,i2,pa2,m2,c2) =
                    word_gen_gc_partial_move_roots conf (ts,i1,pa1,curr,m,dm,gs,rs) in
              (match map_bitmap bs wl stack with
                 NONE -> NONE
               | SOME (hd,ts1,ws') -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 line 2031 *)
let word_gen_gc_move_roots_APPEND = prove
 (CASE_TERM
  `!conf xs ys i1 pa1 ib1 pb1 (curr:A word) m dm.
      word_gen_gc_move_roots conf (APPEND xs ys,i1,pa1,ib1,pb1,curr,m,dm) =
        let (ws1,i1,pa1,ib1,pb1,m1,c1) =
              word_gen_gc_move_roots conf (xs,i1,pa1,ib1,pb1,curr,m,dm) in
        let (ws2,i2,pa2,ib2,pb2,m2,c2) =
              word_gen_gc_move_roots conf (ys,i1,pa1,ib1,pb1,curr,m1,dm) in
          (APPEND ws1 ws2,i2,pa2,ib2,pb2,m2,(c1 /\ c2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; word_gen_gc_move_roots_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THENL
   [REPEAT GEN_TAC THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["w1";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws1";"i4";"pa4";"ib4";"pb4";"m4";"c4"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws2";"i5";"pa5";"ib5";"pb5";"m5";"c5"] THEN
  REWRITE_TAC[APPEND; CONJ_ACI]);;

(* HOL4 line 2049 (HOL4 also quantifies ib1 pb1, which do not occur) *)
let word_gen_gc_partial_move_roots_APPEND = prove
 (CASE_TERM
  `!conf xs ys i1 pa1 (curr:A word) m dm gs rs.
      word_gen_gc_partial_move_roots conf (APPEND xs ys,i1,pa1,curr,m,dm,gs,rs) =
        let (ws1,i1,pa1,m1,c1) =
              word_gen_gc_partial_move_roots conf (xs,i1,pa1,curr,m,dm,gs,rs) in
        let (ws2,i2,pa2,m2,c2) =
              word_gen_gc_partial_move_roots conf (ys,i1,pa1,curr,m1,dm,gs,rs) in
          (APPEND ws1 ws2,i2,pa2,m2,(c1 /\ c2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; word_gen_gc_partial_move_roots_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THENL
   [REPEAT GEN_TAC THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["ws2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["w1";"i3";"pa3";"m3";"c3"] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["ws1";"i4";"pa4";"m4";"c4"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["ws2";"i5";"pa5";"m5";"c5"] THEN
  REWRITE_TAC[APPEND; CONJ_ACI]);;

(* HOL4 line 2067 *)
let word_gen_gc_move_roots_IMP_LENGTH = prove
 (`!xs r0 r1 r3 r4 (curr:A word) r2 dm ys i2 pa2 m2 c conf ib2 pb2.
      word_gen_gc_move_roots conf (xs,r0,r1,r3,r4,curr,r2,dm) =
        (ys,i2,pa2,ib2,pb2,m2,c) ==>
      LENGTH ys = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_gen_gc_move_roots_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["w1";"i1";"pa1";"ib1";"pb1";"m1";"c1"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws2";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2079 *)
let word_gen_gc_partial_move_roots_IMP_LENGTH = prove
 (`!xs r0 r1 r3 r4 (curr:A word) r2 dm ys i2 pa2 m2 c conf.
      word_gen_gc_partial_move_roots conf (xs,r0,r1,curr,r2,dm,r3,r4) =
        (ys,i2,pa2,m2,c) ==>
      LENGTH ys = LENGTH xs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[word_gen_gc_partial_move_roots_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["w1";"i1";"pa1";"m1";"c1"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["ws2";"i3";"pa3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2091 *)
let word_gen_gc_move_roots_bitmaps = prove
 (CASE_TERM
  `!conf bitmaps (curr:A word) dm ib1 pb1 ib2 pb2 stack i1 pa1 m stack2 i2 pa2 m2.
      word_gen_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
        (stack2,i2,pa2,ib2,pb2,m2,T) ==>
      word_gen_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
      match stack with
        [] -> (ARB,ARB,ARB,ARB,ARB,ARB,F)
      | CONS w ws ->
          if w = wl_Word (word 0) then (stack,i1,pa1,ib1,pb1,m,(ws = [])) else
            (match word_gen_gc_move_bitmaps conf (w,ws,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) with
               NONE -> (ARB,ARB,ARB,ARB,ARB,ARB,F)
             | SOME (new,stack,i2,pa2,ib2,pb2,m2,c2) ->
                 let (stack,i,pa,ib1,pb1,m,c3) =
                   word_gen_gc_move_roots_bitmaps conf
                     (stack,bitmaps,i2,pa2,ib2,pb2,curr,m2,dm) in
                 (CONS w (APPEND new stack),i,pa,ib1,pb1,m,(c2 /\ c3)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th] THEN MP_TAC th) THEN
  STRUCT_CASES_TAC(ISPEC `stack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[word_gen_gc_move_roots_bitmaps_def; stack_enc_stack_def] THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[word_gen_gc_move_roots_def] THEN CASE_REWRITE_TAC[stack_dec_stack_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[word_gen_gc_move_bitmaps_def] THEN
  CASES_ON `full_read_bitmap (bitmaps:(A word)list) (h:(A)word_loc)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  CASES_ON `filter_bitmap a (t:((A)word_loc)list)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  STALLOCAUX_SPLIT_TAC `a':((A)word_loc)list#((A)word_loc)list`
    [`ts:((A)word_loc)list`; `ws':((A)word_loc)list`] THEN
  CASES_ON `stack_enc_stack (bitmaps:(A word)list) (ws':((A)word_loc)list)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[word_gen_gc_move_roots_APPEND; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws1";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["ws2";"i4";"pa4";"ib4";"pb4";"m4";"c4"] THEN
  SUBGOAL_THEN `LENGTH (ws1:((A)word_loc)list) = LENGTH (ts:((A)word_loc)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[word_gen_gc_move_roots_IMP_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `filter_bitmap a (t:((A)word_loc)list) = SOME (ts,ws')` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:bool list`; `ws1:((A)word_loc)list`; `t:((A)word_loc)list`;
                 `ts:((A)word_loc)list`; `ws':((A)word_loc)list`; `ws2:((A)word_loc)list`]
         map_bitmap_APPEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[stack_dec_stack_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `map_bitmap a (ws1:((A)word_loc)list) t` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STALLOCAUX_SPLIT_TAC `a''':((A)word_loc)list#((A)word_loc)list#((A)word_loc)list`
    [`hd:((A)word_loc)list`; `tsx:((A)word_loc)list`; `wsx:((A)word_loc)list`] THEN
  MP_TAC(ISPECL [`a:bool list`; `t:((A)word_loc)list`; `ws1:((A)word_loc)list`;
                 `ts:((A)word_loc)list`; `ws':((A)word_loc)list`; `tsx:((A)word_loc)list`;
                 `hd:((A)word_loc)list`; `wsx:((A)word_loc)list`] filter_bitmap_map_bitmap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `stack_dec_stack (bitmaps:(A word)list) ws2 ws'` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[APPEND]);;

(* HOL4 line 2144 *)
let word_gen_gc_partial_move_roots_bitmaps = prove
 (CASE_TERM
  `!conf bitmaps (curr:A word) dm gs rs stack i1 pa1 m stack2 i2 pa2 m2.
      word_gen_gc_partial_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
        (stack2,i2,pa2,m2,T) ==>
      word_gen_gc_partial_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
      match stack with
        [] -> (ARB,ARB,ARB,ARB,F)
      | CONS w ws ->
          if w = wl_Word (word 0) then (stack,i1,pa1,m,(ws = [])) else
            (match word_gen_gc_partial_move_bitmaps conf
                     (w,ws,bitmaps,i1,pa1,curr,m,dm,gs,rs) with
               NONE -> (ARB,ARB,ARB,ARB,F)
             | SOME (new,stack,i2,pa2,m2,c2) ->
                 let (stack,i,pa,m,c3) =
                   word_gen_gc_partial_move_roots_bitmaps conf
                     (stack,bitmaps,i2,pa2,curr,m2,dm,gs,rs) in
                 (CONS w (APPEND new stack),i,pa,m,(c2 /\ c3)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th] THEN MP_TAC th) THEN
  STRUCT_CASES_TAC(ISPEC `stack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[word_gen_gc_partial_move_roots_bitmaps_def; stack_enc_stack_def] THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
    ASM_REWRITE_TAC[word_gen_gc_partial_move_roots_def] THEN
    CASE_REWRITE_TAC[stack_dec_stack_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[word_gen_gc_partial_move_bitmaps_def] THEN
  CASES_ON `full_read_bitmap (bitmaps:(A word)list) (h:(A)word_loc)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  CASES_ON `filter_bitmap a (t:((A)word_loc)list)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  STALLOCAUX_SPLIT_TAC `a':((A)word_loc)list#((A)word_loc)list`
    [`ts:((A)word_loc)list`; `ws':((A)word_loc)list`] THEN
  CASES_ON `stack_enc_stack (bitmaps:(A word)list) (ws':((A)word_loc)list)` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[word_gen_gc_partial_move_roots_APPEND; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["ws1";"i3";"pa3";"m3";"c3"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["ws2";"i4";"pa4";"m4";"c4"] THEN
  SUBGOAL_THEN `LENGTH (ws1:((A)word_loc)list) = LENGTH (ts:((A)word_loc)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[word_gen_gc_partial_move_roots_IMP_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `filter_bitmap a (t:((A)word_loc)list) = SOME (ts,ws')` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:bool list`; `ws1:((A)word_loc)list`; `t:((A)word_loc)list`;
                 `ts:((A)word_loc)list`; `ws':((A)word_loc)list`; `ws2:((A)word_loc)list`]
         map_bitmap_APPEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[stack_dec_stack_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `map_bitmap a (ws1:((A)word_loc)list) t` THEN CASE_REWRITE_TAC[PAIR_EQ] THEN
  STALLOCAUX_SPLIT_TAC `a''':((A)word_loc)list#((A)word_loc)list#((A)word_loc)list`
    [`hd:((A)word_loc)list`; `tsx:((A)word_loc)list`; `wsx:((A)word_loc)list`] THEN
  MP_TAC(ISPECL [`a:bool list`; `t:((A)word_loc)list`; `ws1:((A)word_loc)list`;
                 `ts:((A)word_loc)list`; `ws':((A)word_loc)list`; `tsx:((A)word_loc)list`;
                 `hd:((A)word_loc)list`; `wsx:((A)word_loc)list`] filter_bitmap_map_bitmap) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `stack_dec_stack (bitmaps:(A word)list) ws2 ws'` THEN
  CASE_REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[APPEND]);;

(* HOL4 line 2199 *)
let word_gen_gc_move_bitmap_def = cake_def
  `word_gen_gc_move_bitmap (conf:data_to_word_config)
     (w:A word,stack:((A)word_loc)list,i1:A word,pa1:A word,ib1:A word,pb1:A word,
      curr:A word,m:A word->(A)word_loc,dm:A word->bool) =
     let bs = get_bits w in
     match filter_bitmap bs stack with
       NONE -> NONE
     | SOME (ts,ws) ->
         let (wl,i2,pa2,ib2,pb2,m2,c2) =
               word_gen_gc_move_roots conf (ts,i1,pa1,ib1,pb1,curr,m,dm) in
         (match map_bitmap bs wl stack with
            NONE -> NONE
          | SOME (hd,v2) -> SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2))`;;

(* HOL4 line 2212 *)
let word_gen_gc_partial_move_bitmap_def = cake_def
  `word_gen_gc_partial_move_bitmap (conf:data_to_word_config)
     (w:A word,stack:((A)word_loc)list,i1:A word,pa1:A word,curr:A word,
      m:A word->(A)word_loc,dm:A word->bool,gs:A word,rs:A word) =
     let bs = get_bits w in
     match filter_bitmap bs stack with
       NONE -> NONE
     | SOME (ts,ws) ->
         let (wl,i2,pa2,m2,c2) =
               word_gen_gc_partial_move_roots conf (ts,i1,pa1,curr,m,dm,gs,rs) in
         (match map_bitmap bs wl stack with
            NONE -> NONE
          | SOME (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2))`;;

(* HOL4 line 2225: map_bitmap_APPEND_APPEND is the same as at HOL4 line 718 *)
(* (stack_allocProof_p1.ml), not rebound here                              *)

(* HOL4 line 2249 (an ML value in HOL4) *)
let word_gen_gc_move_bitmaps_Loc = prove
 (`!conf l1 l2 stack bitmaps i1 pa1 ib1 pb1 (curr:A word) m dm.
     word_gen_gc_move_bitmaps conf
       (wl_Loc l1 l2,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) = NONE`,
  REWRITE_TAC[word_gen_gc_move_bitmaps_def; full_read_bitmap_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2253 (an ML value in HOL4) *)
let word_gen_gc_partial_move_bitmaps_Loc = prove
 (`!conf l1 l2 stack bitmaps i1 pa1 (curr:A word) m dm gs rs.
     word_gen_gc_partial_move_bitmaps conf
       (wl_Loc l1 l2,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) = NONE`,
  REWRITE_TAC[word_gen_gc_partial_move_bitmaps_def; full_read_bitmap_def] THEN
  CASE_REWRITE_TAC[]);;

let STALLOCAUX_option_tuple8_id = prove
 (CASE_TERM
  `!x:(A#B#C#D#E#G#H#J)option.
     (match x with NONE -> NONE | SOME (a,b,c,d,e,f,g,h) -> SOME (a,b,c,d,e,f,g,h)) = x`,
  GEN_TAC THEN
  STALLOCAUX_OPT_CASES_TAC `x:(A#B#C#D#E#G#H#J)option` ["a";"b";"c";"d";"e";"f";"g";"h"]);;

(* HOL4 line 2257 *)
let word_gen_gc_move_bitmaps_unroll = prove
 (CASE_TERM
  `!conf (w:A word) stack bitmaps i1 pa1 ib1 pb1 curr m dm x.
    word_gen_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) = SOME x /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) ==>
    word_gen_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
    match DROP (val (word_sub w (word 1))) bitmaps with
      [] -> NONE
    | CONS y ys ->
        (match word_gen_gc_move_bitmap conf (y,stack,i1,pa1,ib1,pb1,curr,m,dm) with
           NONE -> NONE
         | SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2) ->
             if ~(word_msb y) then SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2) else
               (match word_gen_gc_move_bitmaps conf
                        (wl_Word (word_add w (word 1)),ws,bitmaps,i2,pa2,ib2,pb2,curr,m2,dm) with
                  NONE -> NONE
                | SOME (hd3,ws3,i3,pa3,ib3,pb3,m3,c3) ->
                    SOME (APPEND hd hd3,ws3,i3,pa3,ib3,pb3,m3,(c2 /\ c3))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC th THEN ASSUME_TAC th) THEN
  REWRITE_TAC[word_gen_gc_move_bitmaps_def; full_read_bitmap_def] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  STALLOCAUX_LIST_CASES_TAC `DROP (val (word_sub (w:A word) (word 1))) (bitmaps:(A word)list)`
    ["y";"ys"] THEN
  REWRITE_TAC[read_bitmap_def] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPECL [`w:A word`; `bitmaps:(A word)list`; `y:A word`; `ys:(A word)list`]
           STALLOCAUX_bitmaps_next) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN
  ASM_REWRITE_TAC[read_bitmap_def; word_gen_gc_move_bitmap_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP get_bits_intro th]) THEN
    STALLOCAUX_OPT_CASES_TAC `read_bitmap (ys:(A word)list)` ["bs"] THEN
    REWRITE_TAC[option_DISTINCT; filter_bitmap_APPEND] THEN
    STALLOCAUX_OPT_CASES_TAC `filter_bitmap (get_bits (y:A word)) (stack:((A)word_loc)list)`
      ["zs";"rs"] THEN
    STALLOCAUX_OPT_CASES_TAC `filter_bitmap bs (rs:((A)word_loc)list)` ["zs2";"rs2"] THEN
    REWRITE_TAC[word_gen_gc_move_roots_APPEND; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["wl1";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["wl2";"i4";"pa4";"ib4";"pb4";"m4";"c4"] THEN
    SUBGOAL_THEN `LENGTH (zs:((A)word_loc)list) = LENGTH (wl1:((A)word_loc)list)`
      ASSUME_TAC THENL
     [ASM_MESON_TAC[word_gen_gc_move_roots_IMP_LENGTH]; ALL_TAC] THEN
    MP_TAC(ISPECL [`get_bits (y:A word)`; `stack:((A)word_loc)list`; `zs:((A)word_loc)list`;
                   `rs:((A)word_loc)list`; `wl2:((A)word_loc)list`; `bs:bool list`;
                   `wl1:((A)word_loc)list`] map_bitmap_APPEND_APPEND) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap (get_bits (y:A word)) (wl1:((A)word_loc)list) stack`
      ["t1";"t2";"t3"] THEN
    MP_TAC(ISPECL [`get_bits (y:A word)`; `stack:((A)word_loc)list`; `wl1:((A)word_loc)list`;
                   `zs:((A)word_loc)list`; `rs:((A)word_loc)list`; `t2:((A)word_loc)list`;
                   `t1:((A)word_loc)list`; `t3:((A)word_loc)list`] filter_bitmap_map_bitmap) THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap bs (wl2:((A)word_loc)list) rs` ["u1";"u2";"u3"] THEN
    REWRITE_TAC[];
    REWRITE_TAC[GSYM get_bits_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[STALLOCAUX_option_tuple8_id] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[STALLOCAUX_option_tuple8_id; STALLOCAUX_pair_CASE_K]]);;

(* HOL4 line 2334 *)
let word_gen_gc_partial_move_bitmaps_unroll = prove
 (CASE_TERM
  `!conf (w:A word) stack bitmaps i1 pa1 curr m dm gs rs x.
    word_gen_gc_partial_move_bitmaps conf (wl_Word w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) = SOME x /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) ==>
    word_gen_gc_partial_move_bitmaps conf (wl_Word w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
    match DROP (val (word_sub w (word 1))) bitmaps with
      [] -> NONE
    | CONS y ys ->
        (match word_gen_gc_partial_move_bitmap conf (y,stack,i1,pa1,curr,m,dm,gs,rs) with
           NONE -> NONE
         | SOME (hd,ws,i2,pa2,m2,c2) ->
             if ~(word_msb y) then SOME (hd,ws,i2,pa2,m2,c2) else
               (match word_gen_gc_partial_move_bitmaps conf
                        (wl_Word (word_add w (word 1)),ws,bitmaps,i2,pa2,curr,m2,dm,gs,rs) with
                  NONE -> NONE
                | SOME (hd3,ws3,i3,pa3,m3,c3) ->
                    SOME (APPEND hd hd3,ws3,i3,pa3,m3,(c2 /\ c3))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC th THEN ASSUME_TAC th) THEN
  REWRITE_TAC[word_gen_gc_partial_move_bitmaps_def; full_read_bitmap_def] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  STALLOCAUX_LIST_CASES_TAC `DROP (val (word_sub (w:A word) (word 1))) (bitmaps:(A word)list)`
    ["y";"ys"] THEN
  REWRITE_TAC[read_bitmap_def] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPECL [`w:A word`; `bitmaps:(A word)list`; `y:A word`; `ys:(A word)list`]
           STALLOCAUX_bitmaps_next) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN
  ASM_REWRITE_TAC[read_bitmap_def; word_gen_gc_partial_move_bitmap_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP get_bits_intro th]) THEN
    STALLOCAUX_OPT_CASES_TAC `read_bitmap (ys:(A word)list)` ["bs"] THEN
    REWRITE_TAC[option_DISTINCT; filter_bitmap_APPEND] THEN
    STALLOCAUX_OPT_CASES_TAC `filter_bitmap (get_bits (y:A word)) (stack:((A)word_loc)list)`
      ["zs";"rest"] THEN
    STALLOCAUX_OPT_CASES_TAC `filter_bitmap bs (rest:((A)word_loc)list)` ["zs2";"rs2"] THEN
    REWRITE_TAC[word_gen_gc_partial_move_roots_APPEND; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["wl1";"i3";"pa3";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["wl2";"i4";"pa4";"m4";"c4"] THEN
    SUBGOAL_THEN `LENGTH (zs:((A)word_loc)list) = LENGTH (wl1:((A)word_loc)list)`
      ASSUME_TAC THENL
     [ASM_MESON_TAC[word_gen_gc_partial_move_roots_IMP_LENGTH]; ALL_TAC] THEN
    MP_TAC(ISPECL [`get_bits (y:A word)`; `stack:((A)word_loc)list`; `zs:((A)word_loc)list`;
                   `rest:((A)word_loc)list`; `wl2:((A)word_loc)list`; `bs:bool list`;
                   `wl1:((A)word_loc)list`] map_bitmap_APPEND_APPEND) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap (get_bits (y:A word)) (wl1:((A)word_loc)list) stack`
      ["t1";"t2";"t3"] THEN
    MP_TAC(ISPECL [`get_bits (y:A word)`; `stack:((A)word_loc)list`; `wl1:((A)word_loc)list`;
                   `zs:((A)word_loc)list`; `rest:((A)word_loc)list`; `t2:((A)word_loc)list`;
                   `t1:((A)word_loc)list`; `t3:((A)word_loc)list`] filter_bitmap_map_bitmap) THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[APPEND] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    STALLOCAUX_OPT_CASES_TAC `map_bitmap bs (wl2:((A)word_loc)list) rest` ["u1";"u2";"u3"] THEN
    REWRITE_TAC[];
    REWRITE_TAC[GSYM get_bits_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[STALLOCAUX_option_tuple6_id] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[STALLOCAUX_option_tuple6_id; STALLOCAUX_pair_CASE_K]]);;

(* HOL4 line 2414 *)
let word_gen_gc_move_bitmap_unroll = prove
 (CASE_TERM
  `!conf (w:A word) stack i1 pa1 ib1 pb1 curr m dm.
   word_gen_gc_move_bitmap conf (w,stack,i1,pa1,ib1,pb1,curr,m,dm) =
    if w = word 0 then SOME ([],stack,i1,pa1,ib1,pb1,m,T) else
    if w = word 1 then SOME ([],stack,i1,pa1,ib1,pb1,m,T) else
      match stack with
        [] -> NONE
      | CONS x xs ->
        if word_and w (word 1) = word 0 then
          (match word_gen_gc_move_bitmap conf (word_ushr w 1,xs,i1,pa1,ib1,pb1,curr,m,dm) with
             NONE -> NONE
           | SOME (new,stack,i1,pa1,ib1,pb1,m,c) ->
               SOME (CONS x new,stack,i1,pa1,ib1,pb1,m,c))
        else
          let (x1,i1,pa1,ib1,pb1,m1,c1) = word_gen_gc_move conf (x,i1,pa1,ib1,pb1,curr,m,dm) in
          (match word_gen_gc_move_bitmap conf (word_ushr w 1,xs,i1,pa1,ib1,pb1,curr,m1,dm) with
             NONE -> NONE
           | SOME (new,stack,i1,pa1,ib1,pb1,m,c) ->
               SOME (CONS x1 new,stack,i1,pa1,ib1,pb1,m,(c1 /\ c)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_allocProof_word_and_one_eq_0_iff] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_gen_gc_move_bitmap_def; get_bits_def; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[STALLOCAUX_bit_length_eq_0 |> SPEC `word 0:A word` |> REWRITE_RULE[]] THEN
    STALLOCAUX_RW_TAC[SUB_0; LIST_OF_SEQ; filter_bitmap_def; map_bitmap_def;
                      word_gen_gc_move_roots_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `w:A word = word 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_gen_gc_move_bitmap_def; get_bits_def; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[bit_length_eq_1 |> SPEC `word 1:A word` |> REWRITE_RULE[]] THEN
    STALLOCAUX_RW_TAC[SUB_REFL; LIST_OF_SEQ; filter_bitmap_def; map_bitmap_def;
                      word_gen_gc_move_roots_def];
    ALL_TAC] THEN
  ASM_SIMP_TAC[word_gen_gc_move_bitmap_def; LET_DEF; LET_END_DEF; STALLOCAUX_get_bits_cons] THEN
  STRUCT_CASES_TAC(ISPEC `stack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[filter_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit 0 (w:A word)` THEN ASM_REWRITE_TAC[filter_bitmap_def] THEN
  CASE_REWRITE_TAC[] THEN
  STALLOCAUX_OPT_CASES_TAC
    `filter_bitmap (get_bits (word_ushr (w:A word) 1)) (t:((A)word_loc)list)` ["ts";"ws"] THEN
  REWRITE_TAC[word_gen_gc_move_roots_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  TRY (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["x1";"i3";"pa3";"ib3";"pb3";"m3";"c3"]) THEN
  TRY (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["wl";"i4";"pa4";"ib4";"pb4";"m4";"c4"]) THEN
  REWRITE_TAC[map_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (STALLOCAUX_OPT_CASES_TAC
    `map_bitmap (get_bits (word_ushr (w:A word) 1)) (wl:((A)word_loc)list) t`
    ["hd";"p";"q"]) THEN
  REWRITE_TAC[]);;

(* HOL4 line 2469 *)
let word_gen_gc_partial_move_bitmap_unroll = prove
 (CASE_TERM
  `!conf (w:A word) stack i1 pa1 curr m dm gs rs.
   word_gen_gc_partial_move_bitmap conf (w,stack,i1,pa1,curr,m,dm,gs,rs) =
    if w = word 0 then SOME ([],stack,i1,pa1,m,T) else
    if w = word 1 then SOME ([],stack,i1,pa1,m,T) else
      match stack with
        [] -> NONE
      | CONS x xs ->
        if word_and w (word 1) = word 0 then
          (match word_gen_gc_partial_move_bitmap conf (word_ushr w 1,xs,i1,pa1,curr,m,dm,gs,rs) with
             NONE -> NONE
           | SOME (new,stack,i1,pa1,m,c) -> SOME (CONS x new,stack,i1,pa1,m,c))
        else
          let (x1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf (x,i1,pa1,curr,m,dm,gs,rs) in
          (match word_gen_gc_partial_move_bitmap conf
                   (word_ushr w 1,xs,i1,pa1,curr,m1,dm,gs,rs) with
             NONE -> NONE
           | SOME (new,stack,i1,pa1,m,c) -> SOME (CONS x1 new,stack,i1,pa1,m,(c1 /\ c)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_allocProof_word_and_one_eq_0_iff] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_gen_gc_partial_move_bitmap_def; get_bits_def; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[STALLOCAUX_bit_length_eq_0 |> SPEC `word 0:A word` |> REWRITE_RULE[]] THEN
    STALLOCAUX_RW_TAC[SUB_0; LIST_OF_SEQ; filter_bitmap_def; map_bitmap_def;
                      word_gen_gc_partial_move_roots_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `w:A word = word 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[word_gen_gc_partial_move_bitmap_def; get_bits_def; LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[bit_length_eq_1 |> SPEC `word 1:A word` |> REWRITE_RULE[]] THEN
    STALLOCAUX_RW_TAC[SUB_REFL; LIST_OF_SEQ; filter_bitmap_def; map_bitmap_def;
                      word_gen_gc_partial_move_roots_def];
    ALL_TAC] THEN
  ASM_SIMP_TAC[word_gen_gc_partial_move_bitmap_def; LET_DEF; LET_END_DEF; STALLOCAUX_get_bits_cons] THEN
  STRUCT_CASES_TAC(ISPEC `stack:((A)word_loc)list` list_CASES) THEN
  REWRITE_TAC[filter_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit 0 (w:A word)` THEN ASM_REWRITE_TAC[filter_bitmap_def] THEN
  CASE_REWRITE_TAC[] THEN
  STALLOCAUX_OPT_CASES_TAC
    `filter_bitmap (get_bits (word_ushr (w:A word) 1)) (t:((A)word_loc)list)` ["ts";"ws"] THEN
  REWRITE_TAC[word_gen_gc_partial_move_roots_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  TRY (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["x1";"i3";"pa3";"m3";"c3"]) THEN
  TRY (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["wl";"i4";"pa4";"m4";"c4"]) THEN
  REWRITE_TAC[map_bitmap_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (STALLOCAUX_OPT_CASES_TAC
    `map_bitmap (get_bits (word_ushr (w:A word) 1)) (wl:((A)word_loc)list) t`
    ["hd";"p";"q"]) THEN
  REWRITE_TAC[]);;

(* the normaliser decides equations between numeral words (the Temp keys of *)
(* the store) *)
let STALLOCAUX_WORD_NUM_EQ_CONV : conv = fun tm ->
  let l,r = dest_eq tm in
  let isw t = is_comb t && is_const (rator t) && fst(dest_const(rator t)) = "word" &&
              is_numeral (rand t) in
  if isw l && isw r then CHANGED_CONV WORD_REDUCE_CONV tm
  else failwith "STALLOCAUX_WORD_NUM_EQ_CONV";;

let () = STALLOCAUX_base_net :=
  net_of_conv `word m = (word n:5 word)` STALLOCAUX_WORD_NUM_EQ_CONV (!STALLOCAUX_base_net);;

let () = stallocaux_add_rws [injectivity "store_name"];;

(* instantiate memcpy_code_thm at the goal state with the memcpy assumption *)
let STALLOCAUX_MEMCPY_TAC : tactic = fun (asl,w as g) ->
  let s0 = stallocaux_goal_state w in
  let th = snd(find (fun (_,th) ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "memcpy"
    with Failure _ -> false) asl) in
  let _,args = strip_comb (lhs (concl th)) in
  let b1,rest = dest_pair (rhs (concl th)) in
  let m1 = fst(dest_pair rest) in
  (MP_TAC(ISPECL (args @ [b1; m1; s0]) memcpy_code_thm) THEN
   (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
   DISCH_THEN(X_CHOOSE_THEN (mk_var("r1'",`:(A)word_loc`))
     (fun th -> STALLOCAUX_EV_KNOWN_TAC [th]))) g;;

(* HOL4 line 2526 *)
let word_gen_gc_move_code_thm = prove
 (`!conf w i pa ib pb old m dm w1 i1 pa1 ib1 pb1 m1 (s:(A,C,FFI)stack_state).
    word_gen_gc_move conf (w,i,pa,ib,pb,old,m,dm) = (w1,i1,pa1,ib1,pb1,m1,T) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\
    0 IN FDOM (stack_state_regs s) /\
    1 IN FDOM (stack_state_regs s) /\
    2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\
    stack_get_var 4 s = SOME (wl_Word i) /\
    stack_get_var 5 s = SOME w /\
    Temp (word 0) IN FDOM (stack_state_store s) /\
    Temp (word 1) IN FDOM (stack_state_store s) /\
    FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb) /\
    FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib) /\
    1 IN FDOM (stack_state_regs s) /\
    2 IN FDOM (stack_state_regs s) /\
    6 IN FDOM (stack_state_regs s) ==>
    ?ck r0 r1 r2 r6 t0 t1.
      stack_evaluate (word_gen_gc_move_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_store_fupd
                   (K (stack_state_store s |++
                       [(Temp (word 0),t0); (Temp (word 1),t1);
                        (Temp (word 2),wl_Word pb1); (Temp (word 3),wl_Word ib1)]))
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                          (5,w1); (6,r6)])) s)))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `w:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[word_gen_gc_move_def; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gen_gc_move_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC] THEN
  ASM_CASES_TAC `word_and (a:A word) (word 1) = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gen_gc_move_code_def] THEN STALLOCAUX_EV_TAC THEN STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_mul (word_ushr (a:A word) (shift_length conf)) bytes_in_word) old =
                ptr_to_addr conf old a` ASSUME_TAC THENL
   [REWRITE_TAC[ptr_to_addr_def] THEN MATCH_ACCEPT_TAC WORD_ADD_SYM; ALL_TAC] THEN
  ASM_CASES_TAC `is_fwd_ptr (m (ptr_to_addr conf old (a:A word)):(A)word_loc)` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `vv:A word` STRIP_ASSUME_TAC o REWRITE_RULE[is_fwd_ptr_iff]) THEN
    ASM_REWRITE_TAC[theWord_def; PAIR_EQ; isWord_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gen_gc_move_code_def; clear_top_inst_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC THEN
    REWRITE_TAC[update_addr_def; select_lower_lemma] THEN MATCH_ACCEPT_TAC WORD_OR_SYM;
    ALL_TAC] THEN
  ASM_CASES_TAC `is_ref_header (theWord (m (ptr_to_addr conf old (a:A word)):(A)word_loc))` THEN
  ASM_REWRITE_TAC[] THEN
  STALLOCAUX_SPLIT_FN_TAC "memcpy" ["pb2";"mb";"cb"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `hdr:A word` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def; is_fwd_ptr_def; is_ref_header_def]) THEN
    ASSUME_TAC th) o
    REWRITE_RULE[isWord_thm] o
    check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
  EXISTS_TAC `val (word_add (decode_length conf (hdr:A word)) (word 1))` THEN
  REWRITE_TAC[word_gen_gc_move_code_def; clear_top_inst_def] THEN STALLOCAUX_EV_TAC THEN
  STALLOCAUX_MEMCPY_TAC THEN STALLOCAUX_STATE_EQ_TAC THENL
   [REWRITE_TAC[update_addr_def; select_lower_lemma] THEN MATCH_ACCEPT_TAC WORD_OR_SYM;
    REWRITE_TAC[WORD_ADD_ASSOC];
    REWRITE_TAC[update_addr_def; select_lower_lemma] THEN MATCH_ACCEPT_TAC WORD_OR_SYM]);;

(* HOL4 line 2680 *)
let word_gen_gc_partial_move_code_thm = prove
 (`!conf w i pa old m dm gs rs w1 i1 pa1 m1 (s:(A,C,FFI)stack_state).
    word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) = (w1,i1,pa1,m1,T) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\ good_dimindex (:A) /\
    0 IN FDOM (stack_state_regs s) /\
    1 IN FDOM (stack_state_regs s) /\
    2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\
    stack_get_var 4 s = SOME (wl_Word i) /\
    stack_get_var 5 s = SOME w /\
    FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
    FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
    1 IN FDOM (stack_state_regs s) /\
    2 IN FDOM (stack_state_regs s) /\
    6 IN FDOM (stack_state_regs s) ==>
    ?ck r0 r1 r2 r6.
      stack_evaluate (word_gen_gc_partial_move_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_regs_fupd
                   (K (stack_state_regs s |++
                       [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                        (5,w1); (6,r6)])) s))`,
  (REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `w:(A)word_loc` (cases "word_loc")) THEN
    REWRITE_TAC[word_gen_gc_partial_move_def; LET_DEF; LET_END_DEF] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THENL
     [ALL_TAC;
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC] THEN
    ASM_CASES_TAC `word_and (a:A word) (word 1) = word 0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_sub (ptr_to_addr conf old (a:A word)) old =
                  word_mul (word_ushr a (shift_length conf)) bytes_in_word` ASSUME_TAC THENL
     [REWRITE_TAC[ptr_to_addr_def] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM WORD_NOT_LOWER] THEN
    ASM_CASES_TAC `word_ult (word_mul (word_ushr (a:A word) (shift_length conf)) bytes_in_word) gs`
    THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `word_ult (word_mul (word_ushr (a:A word) (shift_length conf)) bytes_in_word) rs`
    THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC]) THEN
  (SUBGOAL_THEN `word_add (word_mul (word_ushr (a:A word) (shift_length conf)) bytes_in_word) old =
                  ptr_to_addr conf old a` ASSUME_TAC THENL
     [REWRITE_TAC[ptr_to_addr_def] THEN MATCH_ACCEPT_TAC WORD_ADD_SYM; ALL_TAC] THEN
    ASM_CASES_TAC `is_fwd_ptr (m (ptr_to_addr conf old (a:A word)):(A)word_loc)` THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `vv:A word` STRIP_ASSUME_TAC o REWRITE_RULE[is_fwd_ptr_iff]) THEN
      ASM_REWRITE_TAC[theWord_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_code_def; clear_top_inst_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC THEN
      REWRITE_TAC[update_addr_def; select_lower_lemma] THEN MATCH_ACCEPT_TAC WORD_OR_SYM;
      ALL_TAC] THEN
    STALLOCAUX_SPLIT_FN_TAC "memcpy" ["pb";"mb";"cb"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `hdr:A word` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def; is_fwd_ptr_def]) THEN ASSUME_TAC th) o
      REWRITE_RULE[isWord_thm] o
      check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
    EXISTS_TAC `val (word_add (decode_length conf (hdr:A word)) (word 1))` THEN
    REWRITE_TAC[word_gen_gc_partial_move_code_def; clear_top_inst_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_MEMCPY_TAC THEN STALLOCAUX_STATE_EQ_TAC THENL
     [REWRITE_TAC[WORD_ADD_ASSOC];
      REWRITE_TAC[update_addr_def; select_lower_lemma] THEN MATCH_ACCEPT_TAC WORD_OR_SYM]));;

(* HOL4 line 2805 (HOL4 recInduct bit_length_ind) *)
let word_gen_gc_move_bitmap_code_thm = prove
 (`!conf (init:((A)word_loc)list) w stack (s:(A,C,FFI)stack_state) i pa ib pb curr m dm new
     stack1 (a1:A word) i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_move_bitmap conf (w,stack,i,pa,ib,pb,curr,m,dm) =
        SOME (new,stack1,i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_use_stack s /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) /\
      6 IN FDOM (stack_state_regs s) /\
      stack_get_var 7 s = SOME (wl_Word w) /\
      stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
      Temp (word 0) IN FDOM (stack_state_store s) /\
      Temp (word 1) IN FDOM (stack_state_store s) /\
      FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb) /\
      FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib) /\
      stack_state_stack s = APPEND (APPEND init old) stack /\
      stack_state_stack_space s = LENGTH init /\
      (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
      ?ck r0 r1 r2 r5 r6 r7 t0 t1.
        stack_evaluate (word_gen_gc_move_bitmap_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_stack_fupd (K (APPEND (APPEND (APPEND init old) new) stack1))
                  (stack_state_store_fupd
                     (K (stack_state_store s |++
                         [(Temp (word 0),t0); (Temp (word 1),t1);
                          (Temp (word 2),wl_Word pb1); (Temp (word 3),wl_Word ib1)]))
                     (stack_state_regs_fupd
                        (K (stack_state_regs s |++
                            [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                             (5,r5); (6,r6); (7,r7);
                             (8,wl_Word (word_mul bytes_in_word
                                           (word (LENGTH (APPEND old new)))))])) s))))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC (REWRITE_RULE[] bit_length_ind) THEN
  X_GEN_TAC `w:A word` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(fun th -> if concl th = `good_dimindex(:A)`
    then ASSUME_TAC (GEN `x:A word` (MP (ISPEC `x:A word` lower_2w_eq) th)) else NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_bitmap"
    with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[word_gen_gc_move_bitmap_unroll] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gen_gc_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `w:A word = word 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gen_gc_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  STALLOCAUX_LIST_CASES_TAC `stack:((A)word_loc)list` ["x";"xs"] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `word_and (w:A word) (word 1) = word 0` THEN ASM_REWRITE_TAC[] THENL
   [STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_move_bitmap conf (word_ushr w 1,xs:((A)word_loc)list,i,pa,ib,pb,curr,m,dm)`
      ["new2";"st2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck2 + 1` THEN
    REWRITE_TAC[word_gen_gc_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_move_bitmap" asl in
      (match args, res with
         [w';stk;i;pa;ib;pb;curr;m;dm], [nw;st;i1;pa1;ib1;pb1;m1;_] ->
           USE_THEN "ih" (fun ih -> MP_TAC (REWRITE_RULE[IMP_IMP]
             (SPECL [stk;s0;i;pa;ib;pb;curr;m;dm;nw;st;i1;pa1;ib1;pb1;m1;
                     `APPEND old [x:(A)word_loc]`]
                (MP ih (ASSUME `~(w:A word = word 0)`)))))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `pt0:(A)word_loc`
      (X_CHOOSE_THEN `pt1:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_bitmap_code_def] th)))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC;
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["x1";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_move_bitmap conf (word_ushr w 1,xs:((A)word_loc)list,i3,pa3,ib3,pb3,curr,m3,dm)`
      ["new2";"st2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * LENGTH (old:((A)word_loc)list) < dimword(:A)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC STALLOCAUX_mul_lt THEN
      EXISTS_TAC `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[word_gen_gc_move_bitmap_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
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
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_move_bitmap" asl in
      (match args, res with
         [w';stk;i;pa;ib;pb;curr;m;dm], [nw;st;i1;pa1;ib1;pb1;m1;_] ->
           USE_THEN "ih" (fun ih -> MP_TAC (REWRITE_RULE[IMP_IMP]
             (SPECL [stk;s0;i;pa;ib;pb;curr;m;dm;nw;st;i1;pa1;ib1;pb1;m1;
                     `APPEND old [x1:(A)word_loc]`]
                (MP ih (ASSUME `~(w:A word = word 0)`)))))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `pt0:(A)word_loc`
      (X_CHOOSE_THEN `pt1:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_bitmap_code_def] th)))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC]);;

(* HOL4 line 2978 (HOL4 recInduct bit_length_ind) *)
let word_gen_gc_partial_move_bitmap_code_thm = prove
 (`!conf (init:((A)word_loc)list) gs rs w stack (s:(A,C,FFI)stack_state) i pa curr m dm new
     stack1 (a1:A word) i1 pa1 m1 old.
      word_gen_gc_partial_move_bitmap conf (w,stack,i,pa,curr,m,dm,gs,rs) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_use_stack s /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) /\
      6 IN FDOM (stack_state_regs s) /\
      stack_get_var 7 s = SOME (wl_Word w) /\
      stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
      FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
      FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
      stack_state_stack s = APPEND (APPEND init old) stack /\
      stack_state_stack_space s = LENGTH init /\
      (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
      ?ck r0 r1 r2 r5 r6 r7.
        stack_evaluate (word_gen_gc_partial_move_bitmap_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_stack_fupd (K (APPEND (APPEND (APPEND init old) new) stack1))
                     (stack_state_regs_fupd
                        (K (stack_state_regs s |++
                            [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                             (5,r5); (6,r6); (7,r7);
                             (8,wl_Word (word_mul bytes_in_word
                                           (word (LENGTH (APPEND old new)))))])) s)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[] bit_length_ind) THEN
  X_GEN_TAC `w:A word` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(fun th -> if concl th = `good_dimindex(:A)`
    then ASSUME_TAC (GEN `x:A word` (MP (ISPEC `x:A word` lower_2w_eq) th)) else NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_bitmap"
    with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[word_gen_gc_partial_move_bitmap_unroll] THEN
  ASM_CASES_TAC `w:A word = word 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gen_gc_partial_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `w:A word = word 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[word_gen_gc_partial_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  STALLOCAUX_LIST_CASES_TAC `stack:((A)word_loc)list` ["x";"xs"] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `word_and (w:A word) (word 1) = word 0` THEN ASM_REWRITE_TAC[] THENL
   [STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_partial_move_bitmap conf (word_ushr w 1,xs:((A)word_loc)list,i,pa,curr,m,dm,gs,rs)`
      ["new2";"st2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck2 + 1` THEN
    REWRITE_TAC[word_gen_gc_partial_move_bitmap_code_def] THEN STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_partial_move_bitmap" asl in
      (match args, res with
         [w';stk;i;pa;curr;m;dm;_;_], [nw;st;i1;pa1;m1;_] ->
           USE_THEN "ih" (fun ih -> MP_TAC (REWRITE_RULE[IMP_IMP]
             (SPECL [stk;s0;i;pa;curr;m;dm;nw;st;i1;pa1;m1;
                     `APPEND old [x:(A)word_loc]`]
                (MP ih (ASSUME `~(w:A word = word 0)`)))))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_bitmap_code_def] th)))))))) THEN
    STALLOCAUX_STATE_EQ_TAC;
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["x1";"i3";"pa3";"m3";"c3"] THEN
    STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_partial_move_bitmap conf (word_ushr w 1,xs:((A)word_loc)list,i3,pa3,curr,m3,dm,gs,rs)`
      ["new2";"st2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * LENGTH (old:((A)word_loc)list) < dimword(:A)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC STALLOCAUX_mul_lt THEN
      EXISTS_TAC `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[word_gen_gc_partial_move_bitmap_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
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
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_partial_move_bitmap" asl in
      (match args, res with
         [w';stk;i;pa;curr;m;dm;_;_], [nw;st;i1;pa1;m1;_] ->
           USE_THEN "ih" (fun ih -> MP_TAC (REWRITE_RULE[IMP_IMP]
             (SPECL [stk;s0;i;pa;curr;m;dm;nw;st;i1;pa1;m1;
                     `APPEND old [x1:(A)word_loc]`]
                (MP ih (ASSUME `~(w:A word = word 0)`)))))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_bitmap_code_def] th)))))))) THEN
    STALLOCAUX_STATE_EQ_TAC]);;

(* successful word_gen_gc_(partial_)move_bitmaps start from a nonzero     *)
(* bitmap index (STALLOCAUX_gen_bitmaps_nonzero and _partial_ below)      *)

(* HOL4 line 3134 *)
let word_gen_gc_move_bitmaps_LENGTH = prove
 (`!conf (w:(A)word_loc) stack bitmaps i pa ib pb curr m dm xs stack1 i1 pa1 ib1 pb1 m1.
     word_gen_gc_move_bitmaps conf (w,stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
       SOME (xs,stack1,i1,pa1,ib1,pb1,m1,T) ==>
     LENGTH stack = LENGTH xs + LENGTH stack1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_move_bitmaps_def] THEN
  STALLOCAUX_OPT_CASES_TAC `full_read_bitmap (bitmaps:(A word)list) (w:(A)word_loc)` ["bs"] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  STALLOCAUX_OPT_CASES_TAC `filter_bitmap bs (stack:((A)word_loc)list)` ["ts";"ws"] THEN
  REWRITE_TAC[option_DISTINCT; LET_DEF; LET_END_DEF] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots" ["wl";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  STALLOCAUX_OPT_CASES_TAC `map_bitmap bs (wl:((A)word_loc)list) stack` ["hd";"ts1";"ws1"] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`bs:bool list`; `wl:((A)word_loc)list`; `stack:((A)word_loc)list`;
                 `xs:((A)word_loc)list`; `(ts1:((A)word_loc)list,ws1:((A)word_loc)list)`]
         map_bitmap_IMP_LENGTH) THEN
  MP_TAC(ISPECL [`bs:bool list`; `stack:((A)word_loc)list`; `ts:((A)word_loc)list`;
                 `stack1:((A)word_loc)list`] filter_bitmap_IMP_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let STALLOCAUX_gen_bitmaps_nonzero = prove
 (`!conf (w:A word) stack (bitmaps:(A word)list) i pa ib pb curr m dm x.
     word_gen_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i,pa,ib,pb,curr,m,dm) = SOME x
     ==> ~(w = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_move_bitmaps_def; full_read_bitmap_def] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 3146 *)
let word_gen_gc_partial_move_bitmaps_LENGTH = prove
 (`!conf (w:(A)word_loc) stack bitmaps i pa curr m dm gs rs xs stack1 i1 pa1 m1.
     word_gen_gc_partial_move_bitmaps conf (w,stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
       SOME (xs,stack1,i1,pa1,m1,T) ==>
     LENGTH stack = LENGTH xs + LENGTH stack1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_partial_move_bitmaps_def] THEN
  STALLOCAUX_OPT_CASES_TAC `full_read_bitmap (bitmaps:(A word)list) (w:(A)word_loc)` ["bs"] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  STALLOCAUX_OPT_CASES_TAC `filter_bitmap bs (stack:((A)word_loc)list)` ["ts";"ws"] THEN
  REWRITE_TAC[option_DISTINCT; LET_DEF; LET_END_DEF] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots" ["wl";"i2";"pa2";"m2";"c2"] THEN
  STALLOCAUX_OPT_CASES_TAC `map_bitmap bs (wl:((A)word_loc)list) stack` ["hd";"ts1";"ws1"] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`bs:bool list`; `wl:((A)word_loc)list`; `stack:((A)word_loc)list`;
                 `xs:((A)word_loc)list`; `(ts1:((A)word_loc)list,ws1:((A)word_loc)list)`]
         map_bitmap_IMP_LENGTH) THEN
  MP_TAC(ISPECL [`bs:bool list`; `stack:((A)word_loc)list`; `ts:((A)word_loc)list`;
                 `stack1:((A)word_loc)list`] filter_bitmap_IMP_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let STALLOCAUX_partial_bitmaps_nonzero = prove
 (`!conf (w:A word) stack (bitmaps:(A word)list) i pa curr m dm gs rs x.
     word_gen_gc_partial_move_bitmaps conf (wl_Word w,stack,bitmaps,i,pa,curr,m,dm,gs,rs) = SOME x
     ==> ~(w = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_partial_move_bitmaps_def; full_read_bitmap_def] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 3158 *)
let word_gen_gc_move_bitmaps_code_thm = prove
 (`!conf (init:((A)word_loc)list) w bitmaps (z:A word) stack (s:(A,C,FFI)stack_state)
     i pa ib pb curr m dm new stack1 (a1:A word) i1 pa1 ib1 pb1 m1 old.
    word_gen_gc_move_bitmaps conf (wl_Word w,stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
      SOME (new,stack1,i1,pa1,ib1,pb1,m1,T) /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_bitmaps s = bitmaps /\
    stack_state_use_stack s /\
    stack_get_var 0 s = SOME (wl_Word z) /\ ~(z = word 0) /\
    1 IN FDOM (stack_state_regs s) /\ 2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\ stack_get_var 4 s = SOME (wl_Word i) /\
    5 IN FDOM (stack_state_regs s) /\ 6 IN FDOM (stack_state_regs s) /\
    7 IN FDOM (stack_state_regs s) /\
    stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
    stack_get_var 9 s = SOME (wl_Word (word_sub w (word 1))) /\
    Temp (word 0) IN FDOM (stack_state_store s) /\
    Temp (word 1) IN FDOM (stack_state_store s) /\
    FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb) /\
    FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib) /\
    stack_state_stack s = APPEND (APPEND init old) stack /\
    stack_state_stack_space s = LENGTH init /\
    (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
    ?ck r0 r1 r2 r5 r6 r7 r9 t0 t1.
      stack_evaluate (word_gen_gc_move_bitmaps_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_stack_fupd (K (APPEND (APPEND (APPEND init old) new) stack1))
                  (stack_state_clock_fupd (K (stack_state_clock s))
                  (stack_state_store_fupd
                     (K (stack_state_store s |++
                         [(Temp (word 0),t0); (Temp (word 1),t1);
                          (Temp (word 2),wl_Word pb1); (Temp (word 3),wl_Word ib1)]))
                    (stack_state_regs_fupd
                       (K (stack_state_regs s |++
                           [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                            (5,r5); (6,r6); (7,r7);
                            (8,wl_Word (word_mul bytes_in_word
                                          (word (LENGTH (APPEND old new)))));
                            (9,r9)])) s)))))`,
  (GEN_TAC THEN GEN_TAC THEN
    STALLOCAUX_MEASURE_INDUCT_TAC [`w:A word`; `bitmaps:(A word)list`]
      `LENGTH (bitmaps:(A word)list) - val (word_sub (w:A word) (word 1))` THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP STALLOCAUX_gen_bitmaps_nonzero o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_bitmaps"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] word_gen_gc_move_bitmaps_unroll) o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (POP_ASSUM MP_TAC THEN
    STALLOCAUX_LIST_CASES_TAC `DROP (val (word_sub (w:A word) (word 1))) (bitmaps:(A word)list)`
      ["y";"ys"] THEN
    REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_EL o check (fun th ->
      can (term_match [] `DROP n (l:(A word)list) = CONS h t`) (concl th))) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_LESS_LENGTH o check (fun th ->
      can (term_match [] `DROP n (l:(A word)list) = CONS h t`) (concl th))) THEN
    MP_TAC(ISPECL [`w:A word`; `bitmaps:(A word)list`; `y:A word`; `ys:(A word)list`]
             STALLOCAUX_bitmaps_next) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "word_gen_gc_move_bitmap"
                               with Failure _ -> false)) (concl th))) THEN
    STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_move_bitmap conf (y,stack:((A)word_loc)list,i,pa,ib,pb,curr,m,dm)`
      ["hd2";"ws2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    ASM_CASES_TAC `word_msb (y:A word)` THEN ASM_REWRITE_TAC[]) THENL
  [(STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_move_bitmaps conf
         (wl_Word (word_add (w:A word) (word 1)),ws2:((A)word_loc)list,bitmaps,i2,pa2,ib2,pb2,
          curr,m2,dm)`
      ["hd3";"ws3";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`new:((A)word_loc)list`; `stack1:((A)word_loc)list`; `i1:A word`;
                         `pa1:A word`; `ib1:A word`; `pb1:A word`; `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `~(word_ushr (y:A word) (dimindex(:A) - 1) = word 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM word_msb_IFF_lsr_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (word_sub (w:A word) (word 1)) + 1 = val w` ASSUME_TAC THENL
     [UNDISCH_TAC `~(w:A word = word 0)` THEN
      REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
      COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
      ALL_TAC]) THEN
  (REWRITE_TAC[word_gen_gc_move_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_move_bitmap" asl in
      (match args, res with
         [y;stk;i;pa;ib;pb;curr;m;dm], [nw;st;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`;y;stk;s0;i;pa;ib;pb;
                          curr;m;dm;nw;st;`a1:A word`;i1;pa1;ib1;pb1;m1;`old:((A)word_loc)list`]
                    word_gen_gc_move_bitmap_code_thm)
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` (X_CHOOSE_THEN `qt0:(A)word_loc`
      (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (SUBGOAL_THEN `LENGTH (stack:((A)word_loc)list) =
                  LENGTH (hd2:((A)word_loc)list) + LENGTH (ws2:((A)word_loc)list)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`conf:data_to_word_config`; `wl_Word (w:A word)`; `stack:((A)word_loc)list`;
                     `bitmaps:(A word)list`; `i:A word`; `pa:A word`; `ib:A word`; `pb:A word`;
                     `curr:A word`; `m:A word->(A)word_loc`; `dm:A word->bool`;
                     `APPEND hd2 (hd3:((A)word_loc)list)`; `ws3:((A)word_loc)list`; `i3:A word`;
                     `pa3:A word`; `ib3:A word`; `pb3:A word`; `m3:A word->(A)word_loc`]
                    word_gen_gc_move_bitmaps_LENGTH) THEN
      MP_TAC(ISPECL [`conf:data_to_word_config`; `wl_Word (word_add (w:A word) (word 1))`;
                     `ws2:((A)word_loc)list`;
                     `bitmaps:(A word)list`; `i2:A word`; `pa2:A word`; `ib2:A word`; `pb2:A word`;
                     `curr:A word`; `m2:A word->(A)word_loc`; `dm:A word->bool`;
                     `hd3:((A)word_loc)list`; `ws3:((A)word_loc)list`; `i3:A word`;
                     `pa3:A word`; `ib3:A word`; `pb3:A word`; `m3:A word->(A)word_loc`]
                    word_gen_gc_move_bitmaps_LENGTH) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) *
                  (((LENGTH (init:((A)word_loc)list) + LENGTH (old:((A)word_loc)list)) +
                    LENGTH (hd2:((A)word_loc)list)) + LENGTH (ws2:((A)word_loc)list)) <
                  dimword(:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `(dimindex(:A) DIV 8) * LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) <
                   dimword(:A)` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; ADD_ASSOC];
      ALL_TAC]) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_move_bitmaps" asl in
      (match args, res with
         [ww;stk;bms;i;pa;ib;pb;curr;m;dm], [nw;st;i1;pa1;ib1;pb1;m1;_] ->
           let w1 = rand ww in
           USE_THEN "ih" (fun ih -> MP_TAC (SPECL [w1;bms] ih)) THEN
           (ANTS_TAC THENL [CONV_TAC (stallocaux_norm (stallocaux_facts asl)) THEN ASM_ARITH_TAC;
                           ALL_TAC]) THEN
           DISCH_THEN(MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL [`word_ushr (y:A word) (dimindex(:A) - 1)`;stk;s0;i;pa;ib;pb;curr;m;dm;nw;st;
                    i1;pa1;ib1;pb1;m1;`APPEND old (hd2:((A)word_loc)list)`])
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p9:(A)word_loc`
      (X_CHOOSE_THEN `pt0:(A)word_loc` (X_CHOOSE_THEN `pt1:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_bitmaps_code_def] th))))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC);
   (REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`new:((A)word_loc)list`; `stack1:((A)word_loc)list`; `i1:A word`;
                         `pa1:A word`; `ib1:A word`; `pb1:A word`; `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `word_ushr (y:A word) (dimindex(:A) - 1) = word 0` ASSUME_TAC THENL
     [MP_TAC(ISPEC `y:A word` word_msb_IFF_lsr_EQ_0) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[word_gen_gc_move_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_move_bitmap" asl in
      (match args, res with
         [y;stk;i;pa;ib;pb;curr;m;dm], [nw;st;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`;y;stk;s0;i;pa;ib;pb;
                          curr;m;dm;nw;st;`a1:A word`;i1;pa1;ib1;pb1;m1;`old:((A)word_loc)list`]
                    word_gen_gc_move_bitmap_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` (X_CHOOSE_THEN `qt0:(A)word_loc`
      (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC THEN EXISTS_TAC `0` THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC)]);;

(* HOL4 line 3291 (HOL4 also quantifies ib pb ib1 pb1 and t0 t1, which  *)
(* do not occur)                                                            *)
let word_gen_gc_partial_move_bitmaps_code_thm = prove
 (`!conf (init:((A)word_loc)list) gs rs w bitmaps (z:A word) stack (s:(A,C,FFI)stack_state)
     i pa curr m dm new stack1 (a1:A word) i1 pa1 m1 old.
    word_gen_gc_partial_move_bitmaps conf (wl_Word w,stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
      SOME (new,stack1,i1,pa1,m1,T) /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_bitmaps s = bitmaps /\
    stack_state_use_stack s /\
    stack_get_var 0 s = SOME (wl_Word z) /\ ~(z = word 0) /\
    1 IN FDOM (stack_state_regs s) /\ 2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\ stack_get_var 4 s = SOME (wl_Word i) /\
    5 IN FDOM (stack_state_regs s) /\ 6 IN FDOM (stack_state_regs s) /\
    7 IN FDOM (stack_state_regs s) /\
    stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
    stack_get_var 9 s = SOME (wl_Word (word_sub w (word 1))) /\
    FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
    FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
    stack_state_stack s = APPEND (APPEND init old) stack /\
    stack_state_stack_space s = LENGTH init /\
    (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
    ?ck r0 r1 r2 r5 r6 r7 r9.
      stack_evaluate (word_gen_gc_partial_move_bitmaps_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_stack_fupd (K (APPEND (APPEND (APPEND init old) new) stack1))
                  (stack_state_clock_fupd (K (stack_state_clock s))
                    (stack_state_regs_fupd
                       (K (stack_state_regs s |++
                           [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                            (5,r5); (6,r6); (7,r7);
                            (8,wl_Word (word_mul bytes_in_word
                                          (word (LENGTH (APPEND old new)))));
                            (9,r9)])) s))))`,
  (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    STALLOCAUX_MEASURE_INDUCT_TAC [`w:A word`; `bitmaps:(A word)list`]
      `LENGTH (bitmaps:(A word)list) - val (word_sub (w:A word) (word 1))` THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP STALLOCAUX_partial_bitmaps_nonzero o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_bitmaps"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] word_gen_gc_partial_move_bitmaps_unroll) o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (POP_ASSUM MP_TAC THEN
    STALLOCAUX_LIST_CASES_TAC `DROP (val (word_sub (w:A word) (word 1))) (bitmaps:(A word)list)`
      ["y";"ys"] THEN
    REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_EL o check (fun th ->
      can (term_match [] `DROP n (l:(A word)list) = CONS h t`) (concl th))) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DROP_IMP_LESS_LENGTH o check (fun th ->
      can (term_match [] `DROP n (l:(A word)list) = CONS h t`) (concl th))) THEN
    MP_TAC(ISPECL [`w:A word`; `bitmaps:(A word)list`; `y:A word`; `ys:(A word)list`]
             STALLOCAUX_bitmaps_next) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])) THEN
  (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "word_gen_gc_partial_move_bitmap"
                               with Failure _ -> false)) (concl th))) THEN
    STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_partial_move_bitmap conf (y,stack:((A)word_loc)list,i,pa,curr,m,dm,gs,rs)`
      ["hd2";"ws2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[option_DISTINCT] THEN
    ASM_CASES_TAC `word_msb (y:A word)` THEN ASM_REWRITE_TAC[]) THENL
  [(STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_partial_move_bitmaps conf
         (wl_Word (word_add (w:A word) (word 1)),ws2:((A)word_loc)list,bitmaps,i2,pa2,curr,m2,dm,
          gs,rs)`
      ["hd3";"ws3";"i3";"pa3";"m3";"c3"] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`new:((A)word_loc)list`; `stack1:((A)word_loc)list`; `i1:A word`;
                         `pa1:A word`; `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `~(word_ushr (y:A word) (dimindex(:A) - 1) = word 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM word_msb_IFF_lsr_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (word_sub (w:A word) (word 1)) + 1 = val w` ASSUME_TAC THENL
     [UNDISCH_TAC `~(w:A word = word 0)` THEN
      REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
      COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
      ALL_TAC]) THEN
  (REWRITE_TAC[word_gen_gc_partial_move_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_partial_move_bitmap" asl in
      (match args, res with
         [y;stk;i;pa;curr;m;dm;_;_], [nw;st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`;`gs:A word`;`rs:A word`;y;
                          stk;s0;i;pa;curr;m;dm;nw;st;`a1:A word`;i1;pa1;m1;`old:((A)word_loc)list`]
                    word_gen_gc_partial_move_bitmap_code_thm)
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (SUBGOAL_THEN `LENGTH (stack:((A)word_loc)list) =
                  LENGTH (hd2:((A)word_loc)list) + LENGTH (ws2:((A)word_loc)list)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`conf:data_to_word_config`; `wl_Word (w:A word)`; `stack:((A)word_loc)list`;
                     `bitmaps:(A word)list`; `i:A word`; `pa:A word`; `curr:A word`;
                     `m:A word->(A)word_loc`; `dm:A word->bool`; `gs:A word`; `rs:A word`;
                     `APPEND hd2 (hd3:((A)word_loc)list)`; `ws3:((A)word_loc)list`; `i3:A word`;
                     `pa3:A word`; `m3:A word->(A)word_loc`]
                    word_gen_gc_partial_move_bitmaps_LENGTH) THEN
      MP_TAC(ISPECL [`conf:data_to_word_config`; `wl_Word (word_add (w:A word) (word 1))`;
                     `ws2:((A)word_loc)list`;
                     `bitmaps:(A word)list`; `i2:A word`; `pa2:A word`; `curr:A word`;
                     `m2:A word->(A)word_loc`; `dm:A word->bool`; `gs:A word`; `rs:A word`;
                     `hd3:((A)word_loc)list`; `ws3:((A)word_loc)list`; `i3:A word`;
                     `pa3:A word`; `m3:A word->(A)word_loc`]
                    word_gen_gc_partial_move_bitmaps_LENGTH) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) *
                  (((LENGTH (init:((A)word_loc)list) + LENGTH (old:((A)word_loc)list)) +
                    LENGTH (hd2:((A)word_loc)list)) + LENGTH (ws2:((A)word_loc)list)) <
                  dimword(:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `(dimindex(:A) DIV 8) * LENGTH (stack_state_stack (s:(A,C,FFI)stack_state)) <
                   dimword(:A)` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; ADD_ASSOC];
      ALL_TAC]) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_partial_move_bitmaps" asl in
      (match args, res with
         [ww;stk;bms;i;pa;curr;m;dm;_;_], [nw;st;i1;pa1;m1;_] ->
           let w1 = rand ww in
           USE_THEN "ih" (fun ih -> MP_TAC (SPECL [w1;bms] ih)) THEN
           (ANTS_TAC THENL [CONV_TAC (stallocaux_norm (stallocaux_facts asl)) THEN ASM_ARITH_TAC;
                           ALL_TAC]) THEN
           DISCH_THEN(MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL [`word_ushr (y:A word) (dimindex(:A) - 1)`;stk;s0;i;pa;curr;m;dm;nw;st;
                    i1;pa1;m1;`APPEND old (hd2:((A)word_loc)list)`])
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p9:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_bitmaps_code_def] th))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC);
   (REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`new:((A)word_loc)list`; `stack1:((A)word_loc)list`; `i1:A word`;
                         `pa1:A word`; `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `word_ushr (y:A word) (dimindex(:A) - 1) = word 0` ASSUME_TAC THENL
     [MP_TAC(ISPEC `y:A word` word_msb_IFF_lsr_EQ_0) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[word_gen_gc_partial_move_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_partial_move_bitmap" asl in
      (match args, res with
         [y;stk;i;pa;curr;m;dm;_;_], [nw;st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`;`gs:A word`;`rs:A word`;y;
                          stk;s0;i;pa;curr;m;dm;nw;st;`a1:A word`;i1;pa1;m1;`old:((A)word_loc)list`]
                    word_gen_gc_partial_move_bitmap_code_thm)
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` ASSUME_TAC))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC THEN EXISTS_TAC `0` THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC)]);;

(* HOL4 line 3412 *)
let word_gen_gc_move_roots_bitmaps_code_thm = prove
 (`!conf stack (init:((A)word_loc)list) bitmaps (s:(A,C,FFI)stack_state) i pa ib pb curr
     m dm (new:((A)word_loc)list) stack1 (a1:A word) i1 pa1 ib1 pb1 m1 old.
    word_gen_gc_move_roots_bitmaps conf (stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
      (stack1,i1,pa1,ib1,pb1,m1,T) /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_bitmaps s = bitmaps /\
    stack_state_use_stack s /\
    0 IN FDOM (stack_state_regs s) /\
    1 IN FDOM (stack_state_regs s) /\ 2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\ stack_get_var 4 s = SOME (wl_Word i) /\
    5 IN FDOM (stack_state_regs s) /\ 6 IN FDOM (stack_state_regs s) /\
    7 IN FDOM (stack_state_regs s) /\
    stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
    stack_get_var 9 s = SOME (HD stack) /\
    Temp (word 0) IN FDOM (stack_state_store s) /\
    Temp (word 1) IN FDOM (stack_state_store s) /\
    FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb) /\
    FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib) /\
    stack_state_stack s = APPEND (APPEND init old) stack /\
    stack_state_stack_space s = LENGTH init /\
    (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
    ?ck r0 r1 r2 r5 r6 r7 r8 (r9:(A)word_loc) t0 t1.
      stack_evaluate (word_gen_gc_move_roots_bitmaps_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_stack_fupd (K (APPEND (APPEND init old) stack1))
                  (stack_state_clock_fupd (K (stack_state_clock s))
                  (stack_state_store_fupd
                     (K (stack_state_store s |++
                         [(Temp (word 0),t0); (Temp (word 1),t1);
                          (Temp (word 2),wl_Word pb1); (Temp (word 3),wl_Word ib1)]))
                    (stack_state_regs_fupd
                       (K (stack_state_regs s |++
                           [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                            (5,r5); (6,r6); (7,r7); (8,r8); (9,wl_Word (word 0))])) s)))))`,
  (GEN_TAC THEN
    STALLOCAUX_MEASURE_INDUCT_TAC [`stack:((A)word_loc)list`] `LENGTH (stack:((A)word_loc)list)` THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_move_roots_bitmaps o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_roots_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `stack:((A)word_loc)list` ["h";"t"] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    STALLOCAUX_ELIM_TAC [`stack:((A)word_loc)list`]) THEN
  (ASM_CASES_TAC `h = wl_Word (word 0):(A)word_loc` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      STALLOCAUX_ELIM_TAC [`stack1:((A)word_loc)list`; `i1:A word`; `pa1:A word`;
                           `ib1:A word`; `pb1:A word`; `m1:A word->(A)word_loc`; `t:((A)word_loc)list`;
                           `h:(A)word_loc`] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[word_gen_gc_move_roots_bitmaps_code_def] THEN
      STALLOCAUX_EV_TAC THEN STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC]) THEN
  (STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_move_bitmaps conf (h,t:((A)word_loc)list,bitmaps,i,pa,ib,pb,curr,m,dm)`
      ["new2";"st2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_roots_bitmaps"
      ["st3";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`stack1:((A)word_loc)list`; `i1:A word`; `pa1:A word`;
                         `ib1:A word`; `pb1:A word`; `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `?c:A word. h = wl_Word c` (X_CHOOSE_THEN `c:A word` SUBST_ALL_TAC) THENL
     [MP_TAC(ISPEC `h:(A)word_loc` (cases "word_loc")) THEN STRIP_TAC THENL
       [POP_ASSUM(fun th -> EXISTS_TAC (rand(rhs(concl th))) THEN ACCEPT_TAC th);
        POP_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_bitmaps"
           with Failure _ -> false))) THEN
        REWRITE_TAC[word_gen_gc_move_bitmaps_Loc; option_DISTINCT]];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP STALLOCAUX_gen_bitmaps_nonzero o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_bitmaps"
      with Failure _ -> false))) THEN
  (REPEAT (FIRST_X_ASSUM (fun th -> if is_var (concl th) then SUBST_ALL_TAC (EQT_INTRO th)
                                     else NO_TAC)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP word_gen_gc_move_bitmaps_LENGTH o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_bitmaps"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_move_roots_bitmaps o check (fun th ->
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_roots_bitmaps"
       with Failure _ -> false) && free_in `st2:((A)word_loc)list` (lhs(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `st2:((A)word_loc)list` ["h2";"t2"] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
    STALLOCAUX_ELIM_TAC [`st2:((A)word_loc)list`]) THEN
  (REWRITE_TAC[word_gen_gc_move_roots_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `n:num`)) THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * SUC (LENGTH (old:((A)word_loc)list) +
                  LENGTH (new2:((A)word_loc)list)) < dimword(:A)` ASSUME_TAC THENL
     [MATCH_MP_TAC STALLOCAUX_mul_lt THEN
      EXISTS_TAC `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `EL (SUC ((LENGTH (init:((A)word_loc)list) + LENGTH (old:((A)word_loc)list)) +
                           LENGTH (new2:((A)word_loc)list)))
                     (APPEND init (APPEND old (CONS (wl_Word c) (APPEND new2 (CONS h2 t2))))) =
                  h2:(A)word_loc` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`APPEND init (APPEND old [wl_Word c:(A)word_loc])`; `new2:((A)word_loc)list`;
                     `h2:(A)word_loc`; `t2:((A)word_loc)list`] STALLOCAUX_EL_mid) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH; GSYM APPEND_ASSOC; APPEND; ADD_CLAUSES; ADD_ASSOC];
      ALL_TAC]) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_move_bitmaps" asl in
      (match args, res with
         [ww;stk;bms;i;pa;ib;pb;curr;m;dm], [nw;st;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`; rand ww; bms;
                          rand ww; stk; s0; i; pa; ib; pb; curr; m; dm; nw; st; `a1:A word`; i1; pa1;
                          ib1; pb1; m1; `APPEND old [wl_Word c:(A)word_loc]`]
                    word_gen_gc_move_bitmaps_code_thm)
       | _ -> failwith "args") g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` (X_CHOOSE_THEN `q9:(A)word_loc`
      (X_CHOOSE_THEN `qt0:(A)word_loc` (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC)))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      (USE_THEN "ih" (fun ih -> MP_TAC (SPEC `CONS (h2:(A)word_loc) t2` ih)) THEN
       (ANTS_TAC THENL
         [UNDISCH_TAC `LENGTH (t:((A)word_loc)list) =
                       LENGTH (new2:((A)word_loc)list) + LENGTH (CONS (h2:(A)word_loc) t2)` THEN
          REWRITE_TAC[LENGTH] THEN ARITH_TAC;
          ALL_TAC]) THEN
       DISCH_THEN(MP_TAC o REWRITE_RULE[IMP_IMP] o
         SPECL [`init:((A)word_loc)list`; `bitmaps:(A word)list`; s0; `i2:A word`; `pa2:A word`;
                `ib2:A word`; `pb2:A word`;
                `curr:A word`; `m2:A word->(A)word_loc`; `dm:A word->bool`;
                `st3:((A)word_loc)list`; `i3:A word`; `pa3:A word`; `ib3:A word`; `pb3:A word`;
                `m3:A word->(A)word_loc`;
                `APPEND (APPEND old [wl_Word c:(A)word_loc]) new2`])) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p8:(A)word_loc`
      (X_CHOOSE_THEN `pt0:(A)word_loc` (X_CHOOSE_THEN `pt1:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_roots_bitmaps_code_def] th))))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC));;

(* HOL4 line 3566 *)
let word_gen_gc_partial_move_roots_bitmaps_code_thm = prove
 (`!conf stack (init:((A)word_loc)list) gs rs bitmaps (s:(A,C,FFI)stack_state) i pa curr m dm
     (new:((A)word_loc)list) stack1 (a1:A word) i1 pa1 m1 old.
    word_gen_gc_partial_move_roots_bitmaps conf (stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
      (stack1,i1,pa1,m1,T) /\
    LENGTH bitmaps < dimword (:A) - 1 /\ good_dimindex (:A) /\
    shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
    2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\ good_dimindex (:A) /\
    (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
    FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word curr) /\ stack_state_use_store s /\
    stack_state_memory s = m /\ stack_state_mdomain s = dm /\ stack_state_bitmaps s = bitmaps /\
    stack_state_use_stack s /\
    0 IN FDOM (stack_state_regs s) /\
    1 IN FDOM (stack_state_regs s) /\ 2 IN FDOM (stack_state_regs s) /\
    stack_get_var 3 s = SOME (wl_Word pa) /\ stack_get_var 4 s = SOME (wl_Word i) /\
    5 IN FDOM (stack_state_regs s) /\ 6 IN FDOM (stack_state_regs s) /\
    7 IN FDOM (stack_state_regs s) /\
    stack_get_var 8 s = SOME (wl_Word (word_mul bytes_in_word (word (LENGTH old)))) /\
    stack_get_var 9 s = SOME (HD stack) /\
    FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
    FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
    stack_state_stack s = APPEND (APPEND init old) stack /\
    stack_state_stack_space s = LENGTH init /\
    (dimindex (:A) DIV 8) * LENGTH (stack_state_stack s) < dimword (:A) ==>
    ?ck r0 r1 r2 r5 r6 r7 r8 (r9:(A)word_loc).
      stack_evaluate (word_gen_gc_partial_move_roots_bitmaps_code conf,
                      stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
        (NONE,stack_state_memory_fupd (K m1)
                (stack_state_stack_fupd (K (APPEND (APPEND init old) stack1))
                  (stack_state_clock_fupd (K (stack_state_clock s))
                    (stack_state_regs_fupd
                       (K (stack_state_regs s |++
                           [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                            (5,r5); (6,r6); (7,r7); (8,r8); (9,wl_Word (word 0))])) s))))`,
  (GEN_TAC THEN
    STALLOCAUX_MEASURE_INDUCT_TAC [`stack:((A)word_loc)list`] `LENGTH (stack:((A)word_loc)list)` THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_partial_move_roots_bitmaps o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_roots_bitmaps"
      with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `stack:((A)word_loc)list` ["h";"t"] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    STALLOCAUX_ELIM_TAC [`stack:((A)word_loc)list`]) THEN
  (ASM_CASES_TAC `h = wl_Word (word 0):(A)word_loc` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      STALLOCAUX_ELIM_TAC [`stack1:((A)word_loc)list`; `i1:A word`; `pa1:A word`;
                           `m1:A word->(A)word_loc`; `t:((A)word_loc)list`; `h:(A)word_loc`] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[word_gen_gc_partial_move_roots_bitmaps_code_def] THEN
      STALLOCAUX_EV_TAC THEN STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC]) THEN
  (STALLOCAUX_OPT_CASES_TAC
      `word_gen_gc_partial_move_bitmaps conf (h,t:((A)word_loc)list,bitmaps,i,pa,curr,m,dm,gs,rs)`
      ["new2";"st2";"i2";"pa2";"m2";"c2"] THEN
    REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_roots_bitmaps" ["st3";"i3";"pa3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`stack1:((A)word_loc)list`; `i1:A word`; `pa1:A word`;
                         `m1:A word->(A)word_loc`] THEN
    SUBGOAL_THEN `?c:A word. h = wl_Word c` (X_CHOOSE_THEN `c:A word` SUBST_ALL_TAC) THENL
     [MP_TAC(ISPEC `h:(A)word_loc` (cases "word_loc")) THEN STRIP_TAC THENL
       [POP_ASSUM(fun th -> EXISTS_TAC (rand(rhs(concl th))) THEN ACCEPT_TAC th);
        POP_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
          (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_bitmaps"
           with Failure _ -> false))) THEN
        REWRITE_TAC[word_gen_gc_partial_move_bitmaps_Loc; option_DISTINCT]];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP STALLOCAUX_partial_bitmaps_nonzero o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_bitmaps"
      with Failure _ -> false))) THEN
  (REPEAT (FIRST_X_ASSUM (fun th -> if is_var (concl th) then SUBST_ALL_TAC (EQT_INTRO th)
                                     else NO_TAC)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP word_gen_gc_partial_move_bitmaps_LENGTH o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_bitmaps"
      with Failure _ -> false)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_partial_move_roots_bitmaps o check (fun th ->
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_roots_bitmaps"
       with Failure _ -> false) && free_in `st2:((A)word_loc)list` (lhs(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    STALLOCAUX_LIST_CASES_TAC `st2:((A)word_loc)list` ["h2";"t2"] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
    STALLOCAUX_ELIM_TAC [`st2:((A)word_loc)list`]) THEN
  (REWRITE_TAC[word_gen_gc_partial_move_roots_bitmaps_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  (FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `n:num`)) THEN
    SUBGOAL_THEN `(dimindex(:A) DIV 8) * SUC (LENGTH (old:((A)word_loc)list) +
                  LENGTH (new2:((A)word_loc)list)) < dimword(:A)` ASSUME_TAC THENL
     [MATCH_MP_TAC STALLOCAUX_mul_lt THEN
      EXISTS_TAC `LENGTH (stack_state_stack (s:(A,C,FFI)stack_state))` THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `EL (SUC ((LENGTH (init:((A)word_loc)list) + LENGTH (old:((A)word_loc)list)) +
                           LENGTH (new2:((A)word_loc)list)))
                     (APPEND init (APPEND old (CONS (wl_Word c) (APPEND new2 (CONS h2 t2))))) =
                  h2:(A)word_loc` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`APPEND init (APPEND old [wl_Word c:(A)word_loc])`; `new2:((A)word_loc)list`;
                     `h2:(A)word_loc`; `t2:((A)word_loc)list`] STALLOCAUX_EL_mid) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH; GSYM APPEND_ASSOC; APPEND; ADD_CLAUSES; ADD_ASSOC];
      ALL_TAC]) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args_some "word_gen_gc_partial_move_bitmaps" asl in
      (match args, res with
         [ww;stk;bms;i;pa;curr;m;dm;_;_], [nw;st;i1;pa1;m1;_] ->
           MP_TAC(ISPECL [`conf:data_to_word_config`; `init:((A)word_loc)list`; `gs:A word`;
                          `rs:A word`; rand ww; bms;
                          rand ww; stk; s0; i; pa; curr; m; dm; nw; st; `a1:A word`; i1; pa1; m1;
                          `APPEND old [wl_Word c:(A)word_loc]`]
                    word_gen_gc_partial_move_bitmaps_code_thm)
       | _ -> failwith "args") g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` (X_CHOOSE_THEN `q9:(A)word_loc` ASSUME_TAC)))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      (USE_THEN "ih" (fun ih -> MP_TAC (SPEC `CONS (h2:(A)word_loc) t2` ih)) THEN
       (ANTS_TAC THENL
         [UNDISCH_TAC `LENGTH (t:((A)word_loc)list) =
                       LENGTH (new2:((A)word_loc)list) + LENGTH (CONS (h2:(A)word_loc) t2)` THEN
          REWRITE_TAC[LENGTH] THEN ARITH_TAC;
          ALL_TAC]) THEN
       DISCH_THEN(MP_TAC o REWRITE_RULE[IMP_IMP] o
         SPECL [`init:((A)word_loc)list`; `gs:A word`; `rs:A word`; `bitmaps:(A word)list`; s0; `i2:A word`; `pa2:A word`;
                `curr:A word`; `m2:A word->(A)word_loc`; `dm:A word->bool`;
                `st3:((A)word_loc)list`; `i3:A word`; `pa3:A word`; `m3:A word->(A)word_loc`;
                `APPEND (APPEND old [wl_Word c:(A)word_loc]) new2`])) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p8:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_roots_bitmaps_code_def] th))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC));;

(* HOL4 line 3705: by induction on the counter (HOL4 Cases \\ Induct_on n) *)
let STALLOCAUX_word_gen_gc_move_list_code_n = prove
 (`!n a (s:(A,C,FFI)stack_state) pa1 pa old m1 m i1 i dm conf a1 ib ib1 pb pb1.
      n < dimword(:A) /\
      word_gen_gc_move_list conf (a:A word,word n,i,pa,ib,pb,old,m,dm) =
        (a1,i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\
      Temp (word 0) IN FDOM (stack_state_store s) /\
      Temp (word 1) IN FDOM (stack_state_store s) /\
      FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb) /\
      FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib) /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) ==>
      6 IN FDOM (stack_state_regs s) ==>
      stack_get_var 7 s = SOME (wl_Word (word n)) /\
      stack_get_var 8 s = SOME (wl_Word a) ==>
      ?ck r0 r1 r2 r5 r6 t0 t1.
        stack_evaluate (word_gen_gc_move_list_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_store_fupd
                     (K (stack_state_store s |++
                         [(Temp (word 0),t0); (Temp (word 1),t1);
                          (Temp (word 2),wl_Word pb1); (Temp (word 3),wl_Word ib1)]))
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                          (5,r5); (6,r6); (7,wl_Word (word 0)); (8,wl_Word a1)])) s)))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_gen_gc_move_list_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[word_gen_gc_move_list_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STALLOCAUX_word_suc_facts) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_list"
    with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[word_gen_gc_move_list_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move" ["w1";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_list" ["a3";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[word_gen_gc_move_list_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
  STALLOCAUX_EV_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (MP_TAC(ISPECL [`conf:data_to_word_config`;
                    `stack_state_memory (s:(A,C,FFI)stack_state) a`; `i:A word`; `pa:A word`;
                    `ib:A word`; `pb:A word`;
                    `old:A word`; `stack_state_memory (s:(A,C,FFI)stack_state)`;
                    `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `w1:(A)word_loc`;
                    `i2:A word`; `pa2:A word`; `ib2:A word`; `pb2:A word`;
                    `m2:A word->(A)word_loc`; s0]
            word_gen_gc_move_code_thm)) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
    (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
    (X_CHOOSE_THEN `q6:(A)word_loc` (X_CHOOSE_THEN `qt0:(A)word_loc`
    (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC))))))) THEN
  STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
  FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
    (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
  STALLOCAUX_LOOP_STEP_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
       SPECL [`word_add a bytes_in_word:A word`; s0; `pa1:A word`; `pa2:A word`;
              `old:A word`; `m1:A word->(A)word_loc`;
              `(a =+ w1) (m2:A word->(A)word_loc)`; `i1:A word`; `i2:A word`;
              `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `conf:data_to_word_config`;
              `a1:A word`; `ib2:A word`; `ib1:A word`; `pb2:A word`; `pb1:A word`])) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
    (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
    (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
    (X_CHOOSE_THEN `pt0:(A)word_loc` (X_CHOOSE_THEN `pt1:(A)word_loc`
     (fun th -> EXISTS_TAC `ck3:num` THEN
                STALLOCAUX_USE_EV_TAC [word_gen_gc_move_list_code_def] th))))))))) THEN
  STALLOCAUX_STATE_EQ_TAC);;

(* HOL4 line 3705 *)
let word_gen_gc_move_list_code_thm = prove
 (`!l a (s:(A,C,FFI)stack_state) pa1 pa old m1 m i1 i dm conf a1 ib ib1 pb pb1.
      word_gen_gc_move_list conf (a:A word,l,i,pa,ib,pb,old,m,dm) =
        (a1,i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\
      Temp (word 0) IN FDOM (stack_state_store s) /\
      Temp (word 1) IN FDOM (stack_state_store s) /\
      FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb) /\
      FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib) /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) ==>
      6 IN FDOM (stack_state_regs s) ==>
      stack_get_var 7 s = SOME (wl_Word l) /\
      stack_get_var 8 s = SOME (wl_Word a) ==>
      ?ck r0 r1 r2 r5 r6 t0 t1.
        stack_evaluate (word_gen_gc_move_list_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_store_fupd
                     (K (stack_state_store s |++
                         [(Temp (word 0),t0); (Temp (word 1),t1);
                          (Temp (word 2),wl_Word pb1); (Temp (word 3),wl_Word ib1)]))
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                          (5,r5); (6,r6); (7,wl_Word (word 0)); (8,wl_Word a1)])) s)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `l:A word` WORD_VAL) THEN DISCH_THEN(fun th ->
    ONCE_REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`val (l:A word)`; `a:A word`; `s:(A,C,FFI)stack_state`; `pa1:A word`;
                `pa:A word`; `old:A word`; `m1:A word->(A)word_loc`;
                `m:A word->(A)word_loc`; `i1:A word`; `i:A word`; `dm:A word->bool`;
                `conf:data_to_word_config`; `a1:A word`; `ib:A word`; `ib1:A word`;
                `pb:A word`; `pb1:A word`]
         STALLOCAUX_word_gen_gc_move_list_code_n) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[dimword_def; VAL_BOUND]);;

(* HOL4 line 3809: by induction on the counter (HOL4 Cases \\ Induct_on n) *)
let STALLOCAUX_word_gen_gc_partial_move_list_code_n = prove
 (`!n a (s:(A,C,FFI)stack_state) pa1 pa old m1 m i1 i dm conf a1 gs rs.
      n < dimword(:A) /\
      word_gen_gc_partial_move_list conf (a:A word,word n,i,pa,old,m,dm,gs,rs) =
        (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\ good_dimindex (:A) /\
      FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
      FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) ==>
      6 IN FDOM (stack_state_regs s) ==>
      stack_get_var 7 s = SOME (wl_Word (word n)) /\
      stack_get_var 8 s = SOME (wl_Word a) ==>
      ?ck r0 r1 r2 r5 r6.
        stack_evaluate (word_gen_gc_partial_move_list_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                          (5,r5); (6,r6); (7,wl_Word (word 0)); (8,wl_Word a1)])) s))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_gen_gc_partial_move_list_def] THEN REWRITE_TAC[PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[word_gen_gc_partial_move_list_code_def] THEN STALLOCAUX_EV_TAC THEN
    STALLOCAUX_STATE_EQ_TAC;
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STALLOCAUX_word_suc_facts) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_list"
    with Failure _ -> false)) THEN
  ONCE_REWRITE_TAC[word_gen_gc_partial_move_list_def] THEN ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move" ["w1";"i2";"pa2";"m2";"c2"] THEN
  STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_list" ["a3";"i3";"pa3";"m3";"c3"] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[word_gen_gc_partial_move_list_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
  STALLOCAUX_EV_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (MP_TAC(ISPECL [`conf:data_to_word_config`;
                    `stack_state_memory (s:(A,C,FFI)stack_state) a`; `i:A word`; `pa:A word`;
                    `old:A word`; `stack_state_memory (s:(A,C,FFI)stack_state)`;
                    `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `gs:A word`; `rs:A word`;
                    `w1:(A)word_loc`;
                    `i2:A word`; `pa2:A word`; `m2:A word->(A)word_loc`; s0]
            word_gen_gc_partial_move_code_thm)) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
    (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
    (X_CHOOSE_THEN `q6:(A)word_loc` ASSUME_TAC))))) THEN
  STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
  FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
    (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
  STALLOCAUX_LOOP_STEP_TAC THEN
  (fun (asl,w as g) -> let s0 = stallocaux_goal_state w in
    (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
       SPECL [`word_add a bytes_in_word:A word`; s0; `pa1:A word`; `pa2:A word`;
              `old:A word`; `m1:A word->(A)word_loc`;
              `(a =+ w1) (m2:A word->(A)word_loc)`; `i1:A word`; `i2:A word`;
              `stack_state_mdomain (s:(A,C,FFI)stack_state)`; `conf:data_to_word_config`;
              `a1:A word`; `gs:A word`; `rs:A word`])) g) THEN
  (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
    (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
    (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
     (fun th -> EXISTS_TAC `ck3:num` THEN
                STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_list_code_def] th))))))) THEN
  STALLOCAUX_STATE_EQ_TAC);;

(* HOL4 line 3809 *)
let word_gen_gc_partial_move_list_code_thm = prove
 (`!l a (s:(A,C,FFI)stack_state) pa1 pa old m1 m i1 i dm conf a1 gs rs.
      word_gen_gc_partial_move_list conf (a:A word,l,i,pa,old,m,dm,gs,rs) =
        (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
      stack_state_memory s = m /\ stack_state_mdomain s = dm /\ good_dimindex (:A) /\
      FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
      FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa) /\
      stack_get_var 4 s = SOME (wl_Word i) /\
      5 IN FDOM (stack_state_regs s) ==>
      6 IN FDOM (stack_state_regs s) ==>
      stack_get_var 7 s = SOME (wl_Word l) /\
      stack_get_var 8 s = SOME (wl_Word a) ==>
      ?ck r0 r1 r2 r5 r6.
        stack_evaluate (word_gen_gc_partial_move_list_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m1)
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                          (5,r5); (6,r6); (7,wl_Word (word 0)); (8,wl_Word a1)])) s))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `l:A word` WORD_VAL) THEN DISCH_THEN(fun th ->
    ONCE_REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`val (l:A word)`; `a:A word`; `s:(A,C,FFI)stack_state`; `pa1:A word`;
                `pa:A word`; `old:A word`; `m1:A word->(A)word_loc`;
                `m:A word->(A)word_loc`; `i1:A word`; `i:A word`; `dm:A word->bool`;
                `conf:data_to_word_config`; `a1:A word`; `gs:A word`; `rs:A word`]
         STALLOCAUX_word_gen_gc_partial_move_list_code_n) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[dimword_def; VAL_BOUND]);;

(* HOL4 line 3899 (HOL4 also quantifies r2a2 ib1 pb1 c1 ib2 pb2, which do *)
(* not occur) *)
let word_gen_gc_partial_move_ref_list_code_thm = prove
 (`!conf gs rs k r2a1 r1a1 i1 pa1 old1 m1 dm1 i2 pa2 m2 (s:(A,C,FFI)stack_state).
      word_gen_gc_partial_move_ref_list k conf (r1a1,i1,pa1,old1,m1,dm1,T,gs,rs,r2a1) =
        (i2,pa2,m2,T) /\
      shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
      2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
      data_to_word_config_len_size conf + 2 < dimindex (:A) /\ good_dimindex (:A) /\
      (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
      FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old1) /\ stack_state_use_store s /\
      stack_state_memory s = m1 /\ stack_state_mdomain s = dm1 /\
      FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
      FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
      0 IN FDOM (stack_state_regs s) /\
      1 IN FDOM (stack_state_regs s) /\
      2 IN FDOM (stack_state_regs s) /\
      stack_get_var 3 s = SOME (wl_Word pa1) /\
      stack_get_var 4 s = SOME (wl_Word i1) /\
      5 IN FDOM (stack_state_regs s) /\
      6 IN FDOM (stack_state_regs s) /\
      7 IN FDOM (stack_state_regs s) /\
      stack_get_var 8 s = SOME (wl_Word r1a1) /\
      stack_get_var 9 s = SOME (wl_Word r2a1) ==>
      ?ck r0 r1 r2 r5 r6 r7 r8 r9.
        stack_evaluate (word_gen_gc_partial_move_ref_list_code conf,
                        stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
          (NONE,stack_state_memory_fupd (K m2)
                  (stack_state_regs_fupd
                     (K (stack_state_regs s |++
                         [(0,r0); (1,r1); (2,r2); (3,wl_Word pa2); (4,wl_Word i2);
                          (5,r5); (6,r6); (7,r7); (8,r8); (9,r9)])) s))`,
  (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [ALL_TAC; POP_ASSUM(LABEL_TAC "ih")] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_ref_list"
      with Failure _ -> false)) THEN
    ONCE_REWRITE_TAC[word_gen_gc_partial_move_ref_list_def] THEN
    ASM_CASES_TAC `r1a1:A word = r2a1` THEN ASM_REWRITE_TAC[PAIR_EQ; NOT_SUC; SUC_SUB1] THENL
     [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_ref_list_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_ref_list_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC]) THEN
  (REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_list" ["pb2";"i3";"pa3";"m3";"c3"] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gen_gc_partial_move_ref_list_ok) THEN
    REWRITE_TAC[isWord_thm] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `v:A word` (fun th ->
         RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th))) ASSUME_TAC) THEN
    REWRITE_TAC[word_gen_gc_partial_move_ref_list_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_list" asl in
      (match args, res with
         [a;l;i;pa;old;m;dm;gs;rs], [a1;i1;pa1;m1;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [l;a;s0;pa1;pa;old;m1;m;i1;i;dm;
                    `conf:data_to_word_config`;a1;gs;rs] word_gen_gc_partial_move_list_code_thm))
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc` ASSUME_TAC)))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_ref_list" asl in
      (match args, res with
         [pb;i;pa;old;m;dm;_;_;_;re], [i2;pa2;m2;_] ->
           USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL [re;pb;i;pa;old;m;dm;i2;pa2;m2;s0])
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p8:(A)word_loc`
      (X_CHOOSE_THEN `p9:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_ref_list_code_def] th)))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC));;

(* HOL4 line 3992 *)
let word_gen_gc_move_data_code_thm = prove
 (`!conf k ha1 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 (s:(A,C,FFI)stack_state).
  word_gen_gc_move_data conf k (ha1,i1,pa1,ib1,pb1,old1,m1,dm1) = (i2,pa2,ib2,pb2,m2,T) /\
  shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
  2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
  data_to_word_config_len_size conf + 2 < dimindex (:A) /\
  (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
  FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old1) /\ stack_state_use_store s /\
  stack_state_memory s = m1 /\ stack_state_mdomain s = dm1 /\
  Temp (word 0) IN FDOM (stack_state_store s) /\
  Temp (word 1) IN FDOM (stack_state_store s) /\
  FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb1) /\
  FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib1) /\
  0 IN FDOM (stack_state_regs s) /\ 1 IN FDOM (stack_state_regs s) /\
  2 IN FDOM (stack_state_regs s) /\
  stack_get_var 3 s = SOME (wl_Word pa1) /\ stack_get_var 4 s = SOME (wl_Word i1) /\
  5 IN FDOM (stack_state_regs s) ==>
  6 IN FDOM (stack_state_regs s) ==>
  7 IN FDOM (stack_state_regs s) ==>
  stack_get_var 8 s = SOME (wl_Word ha1) /\ c1 ==>
  ?ck r0 r1 r2 r5 r6 r7 t0 t1.
    stack_evaluate (word_gen_gc_move_data_code conf,
                    stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
    (NONE,stack_state_memory_fupd (K m2)
            (stack_state_store_fupd
               (K (stack_state_store s |++
                   [(Temp (word 0),t0); (Temp (word 1),t1);
                    (Temp (word 2),wl_Word pb2); (Temp (word 3),wl_Word ib2)]))
            (stack_state_regs_fupd
               (K (stack_state_regs s |++
                   [(0,r0); (1,r1); (2,r2); (3,wl_Word pa2); (4,wl_Word i2); (5,r5); (6,r6);
                    (7,r7); (8,wl_Word pa2)])) s)))`,
  (GEN_TAC THEN INDUCT_TAC THENL [ALL_TAC; POP_ASSUM(LABEL_TAC "ih")] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_data"
      with Failure _ -> false)) THEN
    ONCE_REWRITE_TAC[word_gen_gc_move_data_def] THEN
    ASM_CASES_TAC `ha1:A word = pa1` THEN ASM_REWRITE_TAC[PAIR_EQ; NOT_SUC; SUC_SUB1] THENL
     [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_move_data_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_move_data_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    ASM_CASES_TAC `bit 2 (theWord ((m1:A word->(A)word_loc) ha1))` THEN ASM_REWRITE_TAC[]) THENL
  [(STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_data" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:A word` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th) o
      REWRITE_RULE[isWord_thm] o
      check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
    SUBGOAL_THEN `~(word_and (v:A word) (word 4) = word 0) /\ ~(pa1 = ha1:A word)`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[STALLOCAUX_word_and_4] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck2 + 1` THEN
    REWRITE_TAC[word_gen_gc_move_data_code_def] THEN STALLOCAUX_EV_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_data" asl in
      (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
         SPECL (args @ [`T`] @ butlast res @ [s0]))) g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `pt0:(A)word_loc`
      (X_CHOOSE_THEN `pt1:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_data_code_def] th)))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC);
   (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_list" ["pb3";"i3";"pa3";"ib3";"pb4";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_data" ["i4";"pa4";"ib4";"pb5";"m4";"c4"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:A word` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th) o
      REWRITE_RULE[isWord_thm] o
      check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
    SUBGOAL_THEN `word_and (v:A word) (word 4) = word 0 /\ ~(pa1 = ha1:A word)`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[STALLOCAUX_word_and_4] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[word_gen_gc_move_data_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_list" asl in
      (match args, res with
         [a;l;i;pa;ib;pb;old;m;dm], [a1;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [l;a;s0;pa1;pa;old;m1;m;i1;i;dm;
                    `conf:data_to_word_config`;a1;ib;ib1;pb;pb1] word_gen_gc_move_list_code_thm))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `qt0:(A)word_loc` (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC)))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_data" asl in
      (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
         SPECL (args @ [`T`] @ butlast res @ [s0]))) g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `pt0:(A)word_loc`
      (X_CHOOSE_THEN `pt1:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_data_code_def] th)))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC)]);;

(* HOL4 line 4124 (HOL4 also has the existentials t0 t1, which do not   *)
(* occur) *)
let word_gen_gc_partial_move_data_code_thm = prove
 (`!conf gs rs k ha1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:(A,C,FFI)stack_state).
  word_gen_gc_partial_move_data conf k (ha1,i1,pa1,old1,m1,dm1,gs,rs) = (i2,pa2,m2,T) /\
  shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
  2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
  data_to_word_config_len_size conf + 2 < dimindex (:A) /\
  (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
  FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old1) /\ stack_state_use_store s /\
  stack_state_memory s = m1 /\ stack_state_mdomain s = dm1 /\ good_dimindex (:A) /\
  FLOOKUP (stack_state_store s) (Temp (word 0)) = SOME (wl_Word gs) /\
  FLOOKUP (stack_state_store s) (Temp (word 1)) = SOME (wl_Word rs) /\
  0 IN FDOM (stack_state_regs s) /\ 1 IN FDOM (stack_state_regs s) /\
  2 IN FDOM (stack_state_regs s) /\
  stack_get_var 3 s = SOME (wl_Word pa1) /\ stack_get_var 4 s = SOME (wl_Word i1) /\
  5 IN FDOM (stack_state_regs s) ==>
  6 IN FDOM (stack_state_regs s) ==>
  7 IN FDOM (stack_state_regs s) ==>
  stack_get_var 8 s = SOME (wl_Word ha1) /\ c1 ==>
  ?ck r0 r1 r2 r5 r6 r7.
    stack_evaluate (word_gen_gc_partial_move_data_code conf,
                    stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
    (NONE,stack_state_memory_fupd (K m2)
            (stack_state_regs_fupd
               (K (stack_state_regs s |++
                   [(0,r0); (1,r1); (2,r2); (3,wl_Word pa2); (4,wl_Word i2); (5,r5); (6,r6);
                    (7,r7); (8,wl_Word pa2)])) s))`,
  (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [ALL_TAC; POP_ASSUM(LABEL_TAC "ih")] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_partial_move_data"
      with Failure _ -> false)) THEN
    ONCE_REWRITE_TAC[word_gen_gc_partial_move_data_def] THEN
    ASM_CASES_TAC `ha1:A word = pa1` THEN ASM_REWRITE_TAC[PAIR_EQ; NOT_SUC; SUC_SUB1] THENL
     [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_data_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_partial_move_data_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    ASM_CASES_TAC `bit 2 (theWord ((m1:A word->(A)word_loc) ha1))` THEN ASM_REWRITE_TAC[]) THENL
  [(STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_data" ["i3";"pa3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:A word` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th) o
      REWRITE_RULE[isWord_thm] o
      check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
    SUBGOAL_THEN `~(word_and (v:A word) (word 4) = word 0) /\ ~(pa1 = ha1:A word)`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[STALLOCAUX_word_and_4] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck2 + 1` THEN
    REWRITE_TAC[word_gen_gc_partial_move_data_code_def] THEN STALLOCAUX_EV_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_data" asl in
      (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
         SPECL (butlast (butlast args) @ [`T`] @ butlast res @ [s0]))) g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_data_code_def] th)))))))) THEN
    STALLOCAUX_STATE_EQ_TAC);
   (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_list" ["pb3";"i3";"pa3";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_partial_move_data" ["i4";"pa4";"m4";"c4"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:A word` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th) o
      REWRITE_RULE[isWord_thm] o
      check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
    SUBGOAL_THEN `word_and (v:A word) (word 4) = word 0 /\ ~(pa1 = ha1:A word)`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[STALLOCAUX_word_and_4] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[word_gen_gc_partial_move_data_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC THEN
    (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_list" asl in
      (match args, res with
         [a;l;i;pa;old;m;dm;gs;rs], [a1;i1;pa1;m1;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [l;a;s0;pa1;pa;old;m1;m;i1;i;dm;
                    `conf:data_to_word_config`;a1;gs;rs] word_gen_gc_partial_move_list_code_thm))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      ASSUME_TAC)))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_partial_move_data" asl in
      (USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
         SPECL (butlast (butlast args) @ [`T`] @ butlast res @ [s0]))) g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_partial_move_data_code_def] th)))))))) THEN
    STALLOCAUX_STATE_EQ_TAC)]);;

(* HOL4 line 4243 *)
let word_gen_gc_move_refs_code_thm = prove
 (`!conf k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2
     (s:(A,C,FFI)stack_state).
  word_gen_gc_move_refs conf k (r2a1,r1a1,i1,pa1,ib1,pb1,old1,m1,dm1) =
    (r2a2,i2,pa2,ib2,pb2,m2,T) /\
  shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
  2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
  data_to_word_config_len_size conf + 2 < dimindex (:A) /\
  (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
  FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old1) /\ stack_state_use_store s /\
  stack_state_memory s = m1 /\ stack_state_mdomain s = dm1 /\
  Temp (word 0) IN FDOM (stack_state_store s) /\
  Temp (word 1) IN FDOM (stack_state_store s) /\
  FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb1) /\
  FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib1) /\
  FLOOKUP (stack_state_store s) (Temp (word 4)) = SOME (wl_Word r1a1) /\
  stack_get_var 0 s = SOME (wl_Word r1a1) /\
  1 IN FDOM (stack_state_regs s) /\
  2 IN FDOM (stack_state_regs s) /\
  stack_get_var 3 s = SOME (wl_Word pa1) /\
  stack_get_var 4 s = SOME (wl_Word i1) /\
  5 IN FDOM (stack_state_regs s) ==>
  6 IN FDOM (stack_state_regs s) ==>
  7 IN FDOM (stack_state_regs s) ==>
  stack_get_var 8 s = SOME (wl_Word r2a1) /\ c1 ==>
  ?ck r1 r2 r5 r6 r7 t0 t1.
    stack_evaluate (word_gen_gc_move_refs_code conf,
                    stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
      (NONE,stack_state_memory_fupd (K m2)
              (stack_state_store_fupd
                 (K (stack_state_store s |++
                     [(Temp (word 0),t0); (Temp (word 1),t1);
                      (Temp (word 2),wl_Word pb2); (Temp (word 3),wl_Word ib2)]))
              (stack_state_regs_fupd
                 (K (stack_state_regs s |++
                     [(0,wl_Word r1a1); (1,r1); (2,r2); (3,wl_Word pa2); (4,wl_Word i2);
                      (5,r5); (6,r6); (7,r7); (8,wl_Word r2a2)])) s)))`,
  (GEN_TAC THEN INDUCT_TAC THENL [ALL_TAC; POP_ASSUM(LABEL_TAC "ih")] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_refs"
      with Failure _ -> false)) THEN
    ONCE_REWRITE_TAC[word_gen_gc_move_refs_def] THEN
    ASM_CASES_TAC `r2a1:A word = r1a1` THEN ASM_REWRITE_TAC[PAIR_EQ; NOT_SUC; SUC_SUB1] THENL
     [STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_move_refs_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[word_gen_gc_move_refs_code_def] THEN STALLOCAUX_EV_TAC THEN
      STALLOCAUX_STATE_EQ_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_list" ["r2a3";"i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_refs" ["r2a4";"i4";"pa4";"ib4";"pb4";"m4";"c4"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:A word` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; theWord_def]) THEN ASSUME_TAC th) o
      REWRITE_RULE[isWord_thm] o
      check (fun th -> can (term_match [] `isWord (x:(A)word_loc)`) (concl th))) THEN
    REWRITE_TAC[word_gen_gc_move_refs_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_list" asl in
      (match args, res with
         [a;l;i;pa;ib;pb;old;m;dm], [a1;i1;pa1;ib1;pb1;m1;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [l;a;s0;pa1;pa;old;m1;m;i1;i;dm;
                    `conf:data_to_word_config`;a1;ib;ib1;pb;pb1] word_gen_gc_move_list_code_thm))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `qt0:(A)word_loc` (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC)))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_refs" asl in
      (match args, res with
         [r2a;r1a;i;pa;ib;pb;old;m;dm], [r2a4;i4;pa4;ib4;pb4;m4;_] ->
           USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL [r2a;r1a;r2a4;i;pa;ib;pb;old;m;dm;`T`;i4;pa4;ib4;pb4;m4;s0])
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p1:(A)word_loc`
      (X_CHOOSE_THEN `p2:(A)word_loc` (X_CHOOSE_THEN `p5:(A)word_loc`
      (X_CHOOSE_THEN `p6:(A)word_loc` (X_CHOOSE_THEN `p7:(A)word_loc`
      (X_CHOOSE_THEN `pt0:(A)word_loc` (X_CHOOSE_THEN `pt1:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_refs_code_def] th))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC));;

(* HOL4 line 4347 *)
let word_gen_gc_move_loop_code_thm = prove
 (`!conf k pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 (tt:A word) (c1:bool)
     (s:(A,C,FFI)stack_state).
  word_gen_gc_move_loop conf k (pax,i,pa,ib,pb,pbx,old,m,dm) = (i1,pa1,ib1,pb1,m1,T) /\
  shift_length conf < dimindex (:A) /\ backend_common_word_shift (:A) < dimindex (:A) /\
  2 < dimindex (:A) /\ ~(data_to_word_config_len_size conf = 0) /\
  data_to_word_config_len_size conf + 2 < dimindex (:A) /\
  (!w:A word. word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word) /\
  FLOOKUP (stack_state_store s) CurrHeap = SOME (wl_Word old) /\ stack_state_use_store s /\
  stack_state_memory s = m /\ stack_state_mdomain s = dm /\
  (tt = word 0 <=> pbx = pb /\ pax = pa) /\
  Temp (word 0) IN FDOM (stack_state_store s) /\
  Temp (word 1) IN FDOM (stack_state_store s) /\
  Temp (word 5) IN FDOM (stack_state_store s) /\
  Temp (word 6) IN FDOM (stack_state_store s) /\
  FLOOKUP (stack_state_store s) (Temp (word 2)) = SOME (wl_Word pb) /\
  FLOOKUP (stack_state_store s) (Temp (word 3)) = SOME (wl_Word ib) /\
  FLOOKUP (stack_state_store s) (Temp (word 4)) = SOME (wl_Word pbx) /\
  0 IN FDOM (stack_state_regs s) /\
  stack_get_var 1 s = SOME (wl_Word pbx) /\
  stack_get_var 2 s = SOME (wl_Word pb) /\
  stack_get_var 3 s = SOME (wl_Word pa) /\
  stack_get_var 4 s = SOME (wl_Word i) /\
  stack_get_var 7 s = SOME (wl_Word tt) /\
  stack_get_var 8 s = SOME (wl_Word pax) /\
  5 IN FDOM (stack_state_regs s) /\
  6 IN FDOM (stack_state_regs s) /\ c1 ==>
  ?ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6.
    stack_evaluate (word_gen_gc_move_loop_code conf,
                    stack_state_clock_fupd (K (stack_state_clock s + ck)) s) =
      (NONE,stack_state_memory_fupd (K m1)
              (stack_state_store_fupd
                 (K (stack_state_store s |++
                     [(Temp (word 0),t0); (Temp (word 1),t1); (Temp (word 2),wl_Word pb1);
                      (Temp (word 3),wl_Word ib1); (Temp (word 4),t4); (Temp (word 5),t5);
                      (Temp (word 6),t6)]))
              (stack_state_regs_fupd
                 (K (stack_state_regs s |++
                     [(0,r0); (1,r1); (2,r2); (3,wl_Word pa1); (4,wl_Word i1);
                      (5,r5); (6,r6); (7,r7); (8,r8)])) s)))`,
  (GEN_TAC THEN INDUCT_TAC THENL [ALL_TAC; POP_ASSUM(LABEL_TAC "ih")] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_loop"
      with Failure _ -> false)) THEN
    ONCE_REWRITE_TAC[word_gen_gc_move_loop_def] THEN
    ASM_CASES_TAC `pbx:A word = pb` THEN ASM_CASES_TAC `pax:A word = pa` THEN
    ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    TRY (REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
         REWRITE_TAC[word_gen_gc_move_loop_code_def] THEN STALLOCAUX_EV_TAC THEN
         STALLOCAUX_STATE_EQ_TAC THEN NO_TAC) THEN
    TRY (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_data" ["i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
         REWRITE_TAC[PAIR_EQ] THEN NO_TAC) THEN
    TRY (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_refs"
           ["pbx2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
         REWRITE_TAC[PAIR_EQ] THEN NO_TAC)) THENL
  [(STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_data" ["i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`i1:A word`; `pa1:A word`; `ib1:A word`; `pb1:A word`;
                         `m1:A word->(A)word_loc`; `pbx:A word`] THEN
    REWRITE_TAC[word_gen_gc_move_loop_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_data"
        with Failure _ -> false) asl) in
      let _,largs = strip_comb (lhs(concl th)) in
      let k = el 1 largs in
      let args,res = stallocaux_assum_args "word_gen_gc_move_data" asl in
      MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL ([`conf:data_to_word_config`; k] @ args @ [`T`] @
               butlast res @ [s0]) word_gen_gc_move_data_code_thm)) g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q0:(A)word_loc`
      (X_CHOOSE_THEN `q1:(A)word_loc` (X_CHOOSE_THEN `q2:(A)word_loc`
      (X_CHOOSE_THEN `q5:(A)word_loc` (X_CHOOSE_THEN `q6:(A)word_loc`
      (X_CHOOSE_THEN `q7:(A)word_loc` (X_CHOOSE_THEN `qt0:(A)word_loc`
      (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC))))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_loop" asl in
      (match args, res with
         [pax;i;pa;ib;pb;pbx;old;m;dm], _ ->
           let tt = mk_icomb(mk_icomb(`word_sub:A word->A word->A word`,pbx),pb) in
           SUBGOAL_THEN (mk_iff(mk_eq(tt,`word 0:A word`),mk_conj(mk_eq(pbx,pb),mk_eq(pax,pa))))
             ASSUME_TAC THENL [REWRITE_TAC[WORD_SUB_EQ_0]; ALL_TAC] THEN
           USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL (args @ butlast res @ [tt; `T`; s0]))
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p8:(A)word_loc`
      (X_CHOOSE_THEN `pt0:(A)word_loc` (X_CHOOSE_THEN `pt1:(A)word_loc`
      (X_CHOOSE_THEN `pt4:(A)word_loc` (X_CHOOSE_THEN `pt5:(A)word_loc`
      (X_CHOOSE_THEN `pt6:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_loop_code_def] th)))))))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC);
   (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_refs" ["pbx2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`i1:A word`; `pa1:A word`; `ib1:A word`; `pb1:A word`;
                         `m1:A word->(A)word_loc`; `pax:A word`] THEN
    REWRITE_TAC[word_gen_gc_move_loop_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_refs"
        with Failure _ -> false) asl) in
      let _,largs = strip_comb (lhs(concl th)) in
      let k = el 1 largs in
      let args,res = stallocaux_assum_args "word_gen_gc_move_refs" asl in
      (match args, res with
         [r2a;r1a;i;pa;ib;pb;old;m;dm], [r2a2;i2;pa2;ib2;pb2;m2;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [`conf:data_to_word_config`; k; r2a; r1a; r2a2;
                    i; pa; ib; pb; old; m; dm; `T`; i2; pa2; ib2; pb2; m2; s0]
                    word_gen_gc_move_refs_code_thm))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q1:(A)word_loc`
      (X_CHOOSE_THEN `q2:(A)word_loc` (X_CHOOSE_THEN `q5:(A)word_loc`
      (X_CHOOSE_THEN `q6:(A)word_loc` (X_CHOOSE_THEN `q7:(A)word_loc`
      (X_CHOOSE_THEN `qt0:(A)word_loc` (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC)))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_loop" asl in
      (match args, res with
         [pax;i;pa;ib;pb;pbx;old;m;dm], _ ->
           let sub x y = mk_icomb(mk_icomb(`word_sub:A word->A word->A word`,x),y) in
           let tt = mk_icomb(mk_icomb(`word_or:A word->A word->A word`,sub pbx pb),sub pax pa) in
           SUBGOAL_THEN (mk_iff(mk_eq(tt,`word 0:A word`),mk_conj(mk_eq(pbx,pb),mk_eq(pax,pa))))
             ASSUME_TAC THENL [REWRITE_TAC[WORD_OR_EQ_0; WORD_SUB_EQ_0]; ALL_TAC] THEN
           USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL (args @ butlast res @ [tt; `T`; s0]))
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p8:(A)word_loc`
      (X_CHOOSE_THEN `pt0:(A)word_loc` (X_CHOOSE_THEN `pt1:(A)word_loc`
      (X_CHOOSE_THEN `pt4:(A)word_loc` (X_CHOOSE_THEN `pt5:(A)word_loc`
      (X_CHOOSE_THEN `pt6:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_loop_code_def] th)))))))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC);
   (STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_refs" ["pbx2";"i2";"pa2";"ib2";"pb2";"m2";"c2"] THEN
    STALLOCAUX_SPLIT_FN_TAC "word_gen_gc_move_loop" ["i3";"pa3";"ib3";"pb3";"m3";"c3"] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    STALLOCAUX_ELIM_TAC [`i1:A word`; `pa1:A word`; `ib1:A word`; `pb1:A word`;
                         `m1:A word->(A)word_loc`; `pax:A word`] THEN
    REWRITE_TAC[word_gen_gc_move_loop_code_def] THEN STALLOCAUX_LOOP_UNFOLD_TAC THEN
    STALLOCAUX_EV_TAC) THEN
  ((fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let th = snd(find (fun (_,th) ->
        try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_gen_gc_move_refs"
        with Failure _ -> false) asl) in
      let _,largs = strip_comb (lhs(concl th)) in
      let k = el 1 largs in
      let args,res = stallocaux_assum_args "word_gen_gc_move_refs" asl in
      (match args, res with
         [r2a;r1a;i;pa;ib;pb;old;m;dm], [r2a2;i2;pa2;ib2;pb2;m2;_] ->
           MP_TAC(REWRITE_RULE[IMP_IMP] (ISPECL [`conf:data_to_word_config`; k; r2a; r1a; r2a2;
                    i; pa; ib; pb; old; m; dm; `T`; i2; pa2; ib2; pb2; m2; s0]
                    word_gen_gc_move_refs_code_thm))
       | _ -> failwith "args") g) THEN
    (ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck1:num` (X_CHOOSE_THEN `q1:(A)word_loc`
      (X_CHOOSE_THEN `q2:(A)word_loc` (X_CHOOSE_THEN `q5:(A)word_loc`
      (X_CHOOSE_THEN `q6:(A)word_loc` (X_CHOOSE_THEN `q7:(A)word_loc`
      (X_CHOOSE_THEN `qt0:(A)word_loc` (X_CHOOSE_THEN `qt1:(A)word_loc` ASSUME_TAC)))))))) THEN
    STALLOCAUX_CLOCK_FN_TAC `\ck2. ck1 + (ck2 + 1)` THEN CONV_TAC (stallocaux_norm []) THEN
    FIRST_X_ASSUM(fun th -> STALLOCAUX_EV_KNOWN_TAC [STALLOCAUX_ADD_CLOCK `ck2 + 1`
      (check (fun th -> can stallocaux_dest_ev (lhs (concl th))) th)]) THEN
    STALLOCAUX_LOOP_STEP_TAC) THEN
  (fun (asl,w as g) ->
      let s0 = stallocaux_goal_state w in
      let args,res = stallocaux_assum_args "word_gen_gc_move_loop" asl in
      (match args, res with
         [pax;i;pa;ib;pb;pbx;old;m;dm], _ ->
           let sub x y = mk_icomb(mk_icomb(`word_sub:A word->A word->A word`,x),y) in
           let tt = mk_icomb(mk_icomb(`word_or:A word->A word->A word`,sub pbx pb),sub pax pa) in
           SUBGOAL_THEN (mk_iff(mk_eq(tt,`word 0:A word`),mk_conj(mk_eq(pbx,pb),mk_eq(pax,pa))))
             ASSUME_TAC THENL [REWRITE_TAC[WORD_OR_EQ_0; WORD_SUB_EQ_0]; ALL_TAC] THEN
           USE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP] o
             SPECL (args @ butlast res @ [tt; `T`; s0]))
       | _ -> failwith "args") g) THEN
  ((ANTS_TAC THENL [STALLOCAUX_ANTS_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck3:num` (X_CHOOSE_THEN `p0:(A)word_loc`
      (X_CHOOSE_THEN `p1:(A)word_loc` (X_CHOOSE_THEN `p2:(A)word_loc`
      (X_CHOOSE_THEN `p5:(A)word_loc` (X_CHOOSE_THEN `p6:(A)word_loc`
      (X_CHOOSE_THEN `p7:(A)word_loc` (X_CHOOSE_THEN `p8:(A)word_loc`
      (X_CHOOSE_THEN `pt0:(A)word_loc` (X_CHOOSE_THEN `pt1:(A)word_loc`
      (X_CHOOSE_THEN `pt4:(A)word_loc` (X_CHOOSE_THEN `pt5:(A)word_loc`
      (X_CHOOSE_THEN `pt6:(A)word_loc`
       (fun th -> EXISTS_TAC `ck3:num` THEN
                  STALLOCAUX_USE_EV_TAC [word_gen_gc_move_loop_code_def] th)))))))))))))) THEN
    STALLOCAUX_STATE_EQ_TAC)]);;

(* HOL4 line 4536 (-1w * w is word_mul (word_neg (word 1)) w) *)
let word_sub_0_eq = prove
 (`!w v:A word.
     (word_add (word_mul (word_neg (word 1)) w) v = word 0 <=> w = v) /\
     (word_add v (word_mul (word_neg (word 1)) w) = word 0 <=> w = v)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word_add (word_mul (word_neg (word 1)) w) v = word_sub v w:A word /\
                word_add v (word_mul (word_neg (word 1)) w) = word_sub v w`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; REWRITE_TAC[WORD_SUB_EQ_0] THEN MESON_TAC[]]);;

(* HOL4 line 4544 *)
let good_dimindex_byte_aligned_eq = prove
 (`!w:A word. good_dimindex (:A) ==>
     (byte_aligned w <=>
      word_and w (if dimindex (:A) = 32 then word 3 else word 7) = word 0)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[byte_aligned_def; aligned_bitwise_and] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV LOG2_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* new_trig as the decision tree of the code SetNewTrigger *)
let STALLOCAUX_new_trig_cases = prove
 (`!h (a:A word) gs. good_dimindex(:A) ==>
     new_trig h a gs =
     if word_ult (get_gen_size gs) a then
       (if word_ult h a then h
        else if word_and a (if dimindex(:A) = 32 then word 3 else word 7) = word 0
             then a else h)
     else (if word_ult h (get_gen_size gs) then h else get_gen_size gs)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[new_trig_def; LET_DEF; LET_END_DEF; WORD_ULT; MIN_DEF;
                                     WORD_VAL; GSYM good_dimindex_byte_aligned_eq] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN
  ASM_CASES_TAC `val (get_gen_size gs:A word) < val (a:A word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `val (h:A word) < val (get_gen_size gs:A word)` THEN ASM_REWRITE_TAC[WORD_VAL] THEN
  SUBGOAL_THEN `~(val (get_gen_size gs:A word) < val (h:A word)) ==>
                val (get_gen_size gs:A word) = val h` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_VAL] THEN
  ASM_MESON_TAC[VAL_EQ; WORD_VAL]);;

(* HOL4 line 4553 *)
let evaluate_SetNewTrigger = prove
 (`!endh_reg ib_reg (gen_sizes:num list) (s5:(A,C,FFI)stack_state) res new_s.
   stack_evaluate (SetNewTrigger endh_reg ib_reg gen_sizes,s5) = (res,new_s) ==>
   !ib endh (w:A word).
     good_dimindex (:A) /\ stack_state_use_store s5 /\
     ALL_DISTINCT [1; 4; 7; ib_reg; endh_reg] /\
     FLOOKUP (stack_state_regs s5) ib_reg = SOME (wl_Word ib) /\
     FLOOKUP (stack_state_regs s5) endh_reg = SOME (wl_Word endh) /\
     FLOOKUP (stack_state_store s5) AllocSize = SOME (wl_Word w) ==>
     ?r7 r1 r4.
       res = NONE /\
       new_s = stack_state_regs_fupd (K (stack_state_regs s5 |+ (1,r1) |+ (7,r7) |+ (4,r4)))
                 (stack_state_store_fupd
                   (K (stack_state_store s5 |+
                       (TriggerGC,wl_Word (word_add ib
                          (new_trig (word_sub endh ib) w gen_sizes))))) s5)`,
  (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL_DISTINCT; MEM; DE_MORGAN_THM]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    REPEAT (FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      can stallocaux_dest_ev (lhs (concl th)))) THEN
    REWRITE_TAC[SetNewTrigger_def] THEN
    ASM_CASES_TAC `word_ult (get_gen_size (gen_sizes:num list)) (w:A word)` THEN
    ASM_CASES_TAC `word_ult (word_sub endh ib) (w:A word)` THEN
    ASM_CASES_TAC `word_ult (word_sub endh ib) (get_gen_size (gen_sizes:num list):A word)` THEN
    ASM_CASES_TAC `word_and (w:A word) (if dimindex (:A) = 32 then word 3 else word 7) = word 0` THEN
    STALLOCAUX_EV_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    FIRST_ASSUM(fun th -> if concl th = `good_dimindex(:A)`
       then REWRITE_TAC[MATCH_MP STALLOCAUX_new_trig_cases th] else NO_TAC) THEN
    ASM_REWRITE_TAC[STALLOCAUX_word_add_sub_cancel] THEN
    STALLOCAUX_STATE_EQ_TAC THEN REWRITE_TAC[WORD_ADD_SYM]));;
