(* ========================================================================= *)
(* data_to_word_memoryProof_p7: part 7 of 7 (HOL4 lines 16496-19248) of the  *)
(* port of HOL4 compiler/backend/proofs/data_to_word_memoryProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p7 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_memoryProof.ml needs the last.                *)
(* MP7AUX_ names are local helpers of this part.                            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_memoryProof_p6.ml";;

prioritize_num();;
type_invention_error := true;;

(* the heap and heap element types of the data_to_word proofs, for annotations *)
new_type_abbrev("mp7heap",
  `:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`);;
new_type_abbrev("mp7el",
  `:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element`);;

(* HOL4 line 16496 *)
let bind_each_eq_gt_FAPPLY = prove
 (`!n tf ts k i x.
     i * n + k < FAPPLY (bind_each tf ts k i n) x
     ==> FAPPLY (bind_each tf ts k i n) x = FAPPLY tf x`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def; FAPPLY_FUPDATE_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[MULT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[MULT_SUC] THEN ARITH_TAC);;

(* HOL4 line 16511 *)
let bind_each_eq_gt_FDOM = prove
 (`!n tf ts k i x.
     x IN FDOM (bind_each tf ts k i n) /\
     i * n + k < FAPPLY (bind_each tf ts k i n) x
     ==> x IN FDOM tf`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def] THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:num = ts` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[MULT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ts + 1`; `k + i:num`; `i:num`] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[MULT_SUC] THEN ARITH_TAC);;

(* HOL4 line 16525 *)
let bind_each_eq_ge_FDOM = prove
 (`!n tf ts k i x.
     x IN FDOM (bind_each tf ts k i n) /\
     i * n + k <= FAPPLY (bind_each tf ts k i n) x /\
     ~(i = 0)
     ==> x IN FDOM tf`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def] THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:num = ts` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `~(p /\ q) ==> p /\ q ==> r`) THEN REWRITE_TAC[MULT_SUC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ts + 1`; `k + i:num`; `i:num`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `i * SUC n + k <= FAPPLY (bind_each tf (ts + 1) (k + i) i n) x` THEN
  REWRITE_TAC[MULT_SUC] THEN ARITH_TAC);;

(* HOL4 line 16540 *)
let bind_each_fdom_limit = prove
 (`!k tf ts n i x.
     (!t. t IN FDOM tf ==> t < ts) /\ ts + k < x
     ==> ~(x IN FDOM (bind_each tf ts n i k))`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def] THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ts + 0 < x` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FDOM_FUPDATE; IN_INSERT; DE_MORGAN_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `ts + SUC k < x` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `t < ts ==> t < ts + 1`];
    UNDISCH_TAC `ts + SUC k < x` THEN ARITH_TAC]);;

(* HOL4 line 16551 *)
let bind_each_FUPDATE = prove
 (`!n i tf ts1 ts2 k1 k2.
     ts1 < ts2 /\ k1 < k2
     ==> bind_each (tf |+ (ts1,k1)) ts2 k2 i n = bind_each tf ts2 k2 i n |+ (ts1,k1)`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bind_each (tf |+ (ts1,k1)) (ts2 + 1) (k2 + i) i n =
                bind_each tf (ts2 + 1) (k2 + i) i n |+ (ts1,k1)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_ARITH_TAC);;

(* HOL4 line 16562 *)
let bind_each_MINUS = prove
 (`!n tf ts x k1 k2 i.
     (!t. t IN FDOM tf ==> t < ts) /\
     x IN {x | ts <= x /\ x < ts + n} /\
     k2 <= k1
     ==> FAPPLY (bind_each tf ts k1 i n) x - k2 =
         FAPPLY (bind_each tf ts (k1 - k2) i n) x`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def; IN_ELIM_THM] THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `x < ts + 0` THEN
    UNDISCH_TAC `ts <= x:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `k1 - k2 + i = (k1 + i) - k2:num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `t < ts ==> t < ts + 1`];
    UNDISCH_TAC `ts <= x:num` THEN UNDISCH_TAC `~(x:num = ts)` THEN ARITH_TAC;
    UNDISCH_TAC `x < ts + SUC n` THEN ARITH_TAC;
    UNDISCH_TAC `k2 <= k1:num` THEN ARITH_TAC]);;

(* HOL4 line 16578 (allow_rebind: replaces the theorem of line 1256) *)
let isSomeDataElement_heap_lookup = prove
 (`!n a sp (b:((A,B)heap_element)list).
     isSomeDataElement (heap_lookup n (APPEND (APPEND a [Unused sp]) b))
     ==> n < heap_length a \/ el_length (Unused sp:(A,B)heap_element) +
                              heap_length a <= n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND; heap_length_APPEND;
              GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN
  ASM_CASES_TAC `n < heap_length (a:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n < heap_length (a:((A,B)heap_element)list) + (sp + 1) + 0` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[heap_lookup_def; el_length_def] THEN
    REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[isSomeDataElement_def; option_DISTINCT; option_INJ;
                distinctness "heap_element"];
    DISCH_TAC THEN UNDISCH_TAC
     `~(n < heap_length (a:((A,B)heap_element)list) + (sp + 1) + 0)` THEN
    ARITH_TAC]);;

(* HOL4 line 16589 *)
let isSomeDataElement_heap_lookup_eq = prove
 (`!ls n (p:(A word_loc)heap_address) k1 k2 conf.
     isSomeDataElement (heap_lookup n
       (list_to_BlockReps conf p k2 ls
        :((A word_loc,data_to_word_memoryProof_tag#B list)heap_element)list))
     ==> isSomeDataElement (heap_lookup n
       (list_to_BlockReps conf p k1 ls
        :((A word_loc,data_to_word_memoryProof_tag#B list)heap_element)list))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_to_BlockReps_def] THEN
  CASES_ON `t:((A word_loc)heap_address)list` THEN CASE_REWRITE_TAC [] THEN
  REWRITE_TAC[heap_lookup_def; BlockRep_def; el_length_def; LENGTH] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[isSomeDataElement_def; option_INJ] THEN MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_ACCEPT_TAC);;

(* the binding of bind_each on its new time stamps *)
let MP7AUX_bind_each_FAPPLY_range = prove
 (`!n tf ts k i x.
     ts <= x /\ x < ts + n ==> FAPPLY (bind_each tf ts k i n) x = k + i * (x - ts)`,
  INDUCT_TAC THEN REWRITE_TAC[bind_each_def] THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[SUB_REFL; MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tf:(num,num)fmap`; `ts + 1`; `k + i:num`; `i:num`;
                                `x:num`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `x - ts = (x - (ts + 1)) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC]);;
(* the blocks of list_to_BlockReps are at the multiples of 3 *)
let MP7AUX_heap_lookup_list_to_BlockReps = prove
 (`!l j (p:(A word_loc)heap_address) k conf.
     j < LENGTH l ==>
     isSomeDataElement (heap_lookup (3 * j)
       (list_to_BlockReps conf p k l
        :((A word_loc,data_to_word_memoryProof_tag#B list)heap_element)list))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN CASES_ON `j:num` THEN REWRITE_TAC[list_to_BlockReps_def; LT_SUC] THEN
  CASES_ON `t:((A word_loc)heap_address)list` THEN CASE_REWRITE_TAC [] THEN
  REWRITE_TAC[heap_lookup_def; BlockRep_def; el_length_def; MULT_CLAUSES] THEN
  REWRITE_TAC[isSomeDataElement_def; option_INJ; LENGTH; CONJUNCT1 LT] THENL
   [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `~(3 + 3 * n = 0) /\ ~(3 + 3 * n < SUC (SUC 0) + 1) /\
                          (3 + 3 * n) - (SUC (SUC 0) + 1) = 3 * n`] THEN
  REWRITE_TAC[GSYM isSomeDataElement_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

(* HOL4 line 16604 *)
let bind_each_isSomeDataElement = prove
 (`!l tf ts x (p:(A word_loc)heap_address) k conf.
     ~(l = []) /\
     x IN {x | ts <= x /\ x < ts + LENGTH l} /\
     (!t. t IN FDOM tf ==> t < ts)
     ==> isSomeDataElement (heap_lookup (FAPPLY (bind_each tf ts 0 3 (LENGTH l)) x)
                              (list_to_BlockReps conf p k l
                               :((A word_loc,data_to_word_memoryProof_tag#B list)
                                 heap_element)list))`,
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MP7AUX_bind_each_FAPPLY_range; ADD_CLAUSES] THEN
  MATCH_MP_TAC MP7AUX_heap_lookup_list_to_BlockReps THEN ASM_ARITH_TAC);;

(* HOL4 line 16652 *)
let bind_each_eq_INJ = prove
 (`!n x y tf ts k i.
     FAPPLY (bind_each tf ts k i n) x = FAPPLY (bind_each tf ts k i n) y /\
     ~(i = 0) /\
     x IN {x | ts <= x /\ x < ts + n} /\ ~(x IN FDOM tf) /\
     y IN {x | ts <= x /\ x < ts + n} /\ ~(y IN FDOM tf)
     ==> x = y`,
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `FAPPLY (bind_each tf ts k i n) x = FAPPLY (bind_each tf ts k i n) y` THEN
  ASM_SIMP_TAC[MP7AUX_bind_each_FAPPLY_range; EQ_ADD_LCANCEL; EQ_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

(* list induction with chosen names for the head and the tail *)
let MP7AUX_LIST_INDUCT_TAC (h:term) (t:term) =
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [ALL_TAC; X_GEN_TAC h THEN X_GEN_TAC t THEN DISCH_TAC];;

(* HOL4 line 16672 *)
let all_ts_list_to_v_SUBSET = prove
 (`!xs ts (refs:(data_v bvl_ref)spt) t.
     {x | ts <= x /\ x < ts + LENGTH xs} SUBSET all_ts refs [data_list_to_v ts t xs]`,
  MP7AUX_LIST_INDUCT_TAC `y:data_v` `ys:data_v list` THEN
  REWRITE_TAC[data_list_to_v_def; LENGTH] THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; ADD_CLAUSES; GSYM NOT_LE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[all_ts_cons; APPEND] THEN
  ONCE_REWRITE_TAC[all_ts_head] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ts + 1`; `refs:(data_v bvl_ref)spt`; `t:data_v`]) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_UNION] THEN
  MESON_TAC[ARITH_RULE `ts <= x /\ x < ts + SUC n ==>
                        x = ts \/ (ts + 1 <= x /\ x < (ts + 1) + n)`]);;

(* HOL4 line 16685 *)
let all_ts_SUBSET_list_to_v = prove
 (`!refs t xs stack ts.
     all_ts refs (CONS t (APPEND xs stack)) SUBSET
     all_ts refs (CONS (data_list_to_v ts t xs) stack)`,
  GEN_TAC THEN GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `y:data_v` `ys:data_v list` THEN
  REWRITE_TAC[data_list_to_v_def; APPEND; SUBSET_REFL] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (y:data_v) stack`; `ts + 1`]) THEN
  REWRITE_TAC[all_ts_cons; APPEND] THEN
  REWRITE_TAC[all_ts_def; SUBSET; IN_ELIM_THM; IN_INSERT; MEM; MEM_APPEND; LET_DEF;
              LET_END_DEF] THEN
  REWRITE_TAC[DISJ_ACI] THEN
  DISCH_TAC THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN DISJ2_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* HOL4 line 16701 *)
let new_all_ts_SUBSET_list_to_v = prove
 (`!refs t xs stack ts.
     {x | ts <= x /\ x < ts + LENGTH xs} SUBSET
     all_ts refs (CONS (data_list_to_v ts t xs) stack)`,
  GEN_TAC THEN GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `y:data_v` `ys:data_v list` THEN
  REWRITE_TAC[data_list_to_v_def; LENGTH] THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; ADD_CLAUSES; GSYM NOT_LE] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (y:data_v) stack`; `ts + 1`]) THEN
  REWRITE_TAC[all_ts_cons; APPEND] THEN
  REWRITE_TAC[all_ts_def; SUBSET; IN_ELIM_THM; IN_INSERT; MEM; MEM_APPEND; LET_DEF;
              LET_END_DEF] THEN
  REWRITE_TAC[DISJ_ACI] THEN
  DISCH_TAC THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z = ts:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 16716 *)
let FDOM_bind_each_lemma = prove
 (`!n tf k ts h.
     FDOM tf SUBSET {n | n < ts} ==>
     FDOM (bind_each tf ts h n k) SUBSET {n | n < ts + k}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[bind_each_def; ADD_CLAUSES] THEN
  REWRITE_TAC[FDOM_FUPDATE; INSERT_SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ts + 1`; `h + n:num`]) THEN ANTS_TAC THENL
   [UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[ARITH_RULE `x < ts ==> x < ts + 1`];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[ARITH_RULE `x < (ts + 1) + k ==> x < SUC (ts + k)`]]);;

(* HOL4 line 16726 *)
let v_all_vs_list_to_v1 = prove
 (`!xs stack ts t t1 a1 xs1.
     t1 < ts /\
     MEM (data_Block t1 a1 xs1) (v_all_vs (CONS (data_list_to_v ts t xs) stack)) ==>
     MEM (data_Block t1 a1 xs1) (v_all_vs (CONS t (APPEND xs stack)))`,
  MP7AUX_LIST_INDUCT_TAC `y:data_v` `ys:data_v list` THEN
  REWRITE_TAC[data_list_to_v_def; APPEND] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[v_all_vs_def; MEM; MEM_APPEND; injectivity "data_v"] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[LT_REFL];
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_v_all_vs_split) THENL
     [ASM_MESON_TAC[MEM_v_all_vs_extend_tl; MEM_v_all_vs_extend_hd];
      FIRST_X_ASSUM(MP_TAC o SPECL [`[]:data_v list`; `ts + 1`; `t:data_v`; `t1:num`;
                                    `a1:num`; `xs1:data_v list`]) THEN
      ASM_REWRITE_TAC[APPEND_NIL] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_TAC o MATCH_MP MEM_v_all_vs_split) THEN
      ASM_MESON_TAC[MEM_v_all_vs_extend_tl; MEM_v_all_vs_extend_hd;
                    MEM_v_all_vs_extend_append]];
    ASM_MESON_TAC[MEM_v_all_vs_extend_hd; v_all_vs_append; MEM_APPEND]]);;

(* HOL4 line 16744 *)
let blocks_unique_GT_ts = prove
 (`!ts refs t xs stack t' xs1 a1.
     blocks_unique ts (all_vs refs (CONS t (APPEND xs stack))) /\
     t' >= ts /\
     ~(xs1 = []) ==>
     ~(data_Block t' a1 xs1 IN all_vs refs (CONS t (APPEND xs stack)))`,
  REWRITE_TAC[blocks_unique_def; GE] THEN MESON_TAC[NOT_LT]);;

(* membership in v_all_vs of a list, element by element *)
let MP7AUX_MEM_v_all_vs_CONS = prove
 (`!x v xs. MEM x (v_all_vs (CONS v xs)) <=>
            MEM x (v_all_vs [v]) \/ MEM x (v_all_vs xs)`,
  MESON_TAC[MEM_v_all_vs_split; MEM_v_all_vs_extend_tl; MEM_v_all_vs_extend_hd]);;
let MP7AUX_MEM_v_all_vs_APPEND = prove
 (`!x l1 l2. MEM x (v_all_vs (APPEND l1 l2)) <=>
             MEM x (v_all_vs l1) \/ MEM x (v_all_vs l2)`,
  REWRITE_TAC[v_all_vs_append; MEM_APPEND]);;
let MP7AUX_MEM_v_all_vs_Block = prove
 (`!x ts tag l. MEM x (v_all_vs [data_Block ts tag l]) <=>
                x = data_Block ts tag l \/ MEM x (v_all_vs l)`,
  REWRITE_TAC[v_all_vs_def; MEM; MEM_APPEND] THEN MESON_TAC[]);;
(* MP7AUX_V_ALL_VS_CONV splits MEM x (v_all_vs (CONS v xs)) when xs is not [] *)
let MP7AUX_V_ALL_VS_CONV : conv =
  fun tm ->
    let th = PART_MATCH lhs MP7AUX_MEM_v_all_vs_CONS tm in
    let xs = rand(rand(rand(lhs(concl th)))) in
    if is_const xs && fst(dest_const xs) = "NIL" then failwith "MP7AUX_V_ALL_VS_CONV"
    else th;;
(* MEM x (v_all_vs l) as a disjunction over the elements of l *)
let MP7AUX_V_ALL_VS_TAC =
  REWRITE_TAC[MP7AUX_MEM_v_all_vs_APPEND; MP7AUX_MEM_v_all_vs_Block; v_all_vs_def; MEM;
              MEM_APPEND] THEN
  CONV_TAC(TOP_DEPTH_CONV MP7AUX_V_ALL_VS_CONV) THEN
  REWRITE_TAC[MP7AUX_MEM_v_all_vs_APPEND; MP7AUX_MEM_v_all_vs_Block; v_all_vs_def; MEM;
              MEM_APPEND];;

(* HOL4 line 16757 *)
let Block_NOT_IN_all_vs = prove
 (`!xs t t' a2 xs2 h stack refs.
     ~(data_Block t' a2 xs2 IN all_vs refs (CONS t (CONS h (APPEND xs stack)))) ==>
     !m. m > 0 ==>
         ~MEM (data_Block t' a2 xs2) (v_all_vs [data_list_to_v (t' + m) t xs])`,
  MP7AUX_LIST_INDUCT_TAC `y:data_v` `ys:data_v list` THEN
  REWRITE_TAC[data_list_to_v_def; APPEND] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THENL
   [MESON_TAC[MEM_v_all_vs_extend_tl]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:data_v`; `t':num`; `a2:num`; `xs2:data_v list`;
                                `h:data_v`; `stack:data_v list`;
                                `refs:(data_v bvl_ref)spt`]) THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  MP7AUX_V_ALL_VS_TAC THEN
  REWRITE_TAC[injectivity "data_v"; DE_MORGAN_THM] THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m + 1`) THEN
  REWRITE_TAC[ADD_ASSOC; ARITH_RULE `m + 1 > 0`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `t' = t' + m <=> m = 0`] THEN
  ASM_SIMP_TAC[ARITH_RULE `m > 0 ==> ~(m = 0)`]);;

(* HOL4 line 16791 *)
let v_all_vs_list_to_v2 = prove
 (`!xs t' a1 a2 xs1 xs2 ts t stack refs.
     MEM (data_Block t' a1 xs1) (v_all_vs (CONS (data_list_to_v ts t xs) stack)) /\
     ~(xs1 = []) /\
     MEM (data_Block t' a2 xs2) (v_all_vs (CONS (data_list_to_v ts t xs) stack)) /\
     ~(xs2 = []) /\
     ~(data_Block t' a1 xs1 IN all_vs refs (CONS t (APPEND xs stack))) /\
     ~(data_Block t' a2 xs2 IN all_vs refs (CONS t (APPEND xs stack))) ==>
     a1 = a2 /\ xs1 = xs2 /\ t' < ts + LENGTH xs`,
  MP7AUX_LIST_INDUCT_TAC `y:data_v` `ys:data_v list` THEN
  REWRITE_TAC[data_list_to_v_def; APPEND; LENGTH] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!a xs. ~(data_Block t' a xs IN all_vs refs (CONS t (CONS y (APPEND ys stack))))
           ==> ~(data_Block t' a xs IN all_vs refs (CONS t (APPEND ys stack))) /\
               ~MEM (data_Block t' a xs) (v_all_vs [y]) /\
               ~MEM (data_Block t' a xs) (v_all_vs stack)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
    MP7AUX_V_ALL_VS_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a xs. MEM (data_Block t' a xs)
             (v_all_vs (CONS (data_Block ts cons_tag [y; data_list_to_v (ts + 1) t ys])
                             stack)) /\
           ~(data_Block t' a xs IN all_vs refs (CONS t (CONS y (APPEND ys stack))))
           ==> (t' = ts /\ a = cons_tag /\ xs = [y; data_list_to_v (ts + 1) t ys]) \/
               MEM (data_Block t' a xs) (v_all_vs [data_list_to_v (ts + 1) t ys])`
  (fun th -> MP_TAC(SPECL [`a1:num`; `xs1:data_v list`] th) THEN
             MP_TAC(SPECL [`a2:num`; `xs2:data_v list`] th)) THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `MEM (data_Block t' a xs)
             (v_all_vs (CONS (data_Block ts cons_tag [y; data_list_to_v (ts + 1) t ys])
                             stack))` THEN
    MP7AUX_V_ALL_VS_TAC THEN REWRITE_TAC[injectivity "data_v"] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ys:data_v list`; `t:data_v`; `t':num`; `a1:num`; `xs1:data_v list`;
                 `y:data_v`; `stack:data_v list`; `refs:(data_v bvl_ref)spt`]
          Block_NOT_IN_all_vs) THEN
  MP_TAC(ISPECL [`ys:data_v list`; `t:data_v`; `t':num`; `a2:num`; `xs2:data_v list`;
                 `y:data_v`; `stack:data_v list`; `refs:(data_v bvl_ref)spt`]
          Block_NOT_IN_all_vs) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN REWRITE_TAC[ARITH_RULE `1 > 0`] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN REWRITE_TAC[ARITH_RULE `1 > 0`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `t':num = ts` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':num`; `a1:num`; `a2:num`; `xs1:data_v list`;
                                  `xs2:data_v list`; `ts + 1`; `t:data_v`;
                                  `stack:data_v list`; `refs:(data_v bvl_ref)spt`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MEM_v_all_vs_extend_tl] THEN ASM_MESON_TAC[];
      SIMP_TAC[] THEN ARITH_TAC]]);;

(* HOL4 line 16877 *)
let blocks_unique_cons_multi = prove
 (`!ts refs t xs stack.
     blocks_unique ts (all_vs refs (CONS t (APPEND xs stack))) ==>
     blocks_unique (ts + LENGTH xs)
       (all_vs refs (CONS (data_list_to_v ts t xs) stack))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[blocks_unique_def] THEN
  MAP_EVERY X_GEN_TAC [`t':num`; `a1:num`; `xs1:data_v list`; `a2:num`;
                       `xs2:data_v list`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `t' < ts:num` THENL
   [SUBGOAL_THEN
     `!a l. data_Block t' a l IN all_vs refs (CONS (data_list_to_v ts t xs) stack)
            ==> data_Block t' a l IN all_vs refs (CONS t (APPEND xs stack))`
     ASSUME_TAC THENL
     [REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[v_all_vs_list_to_v1];
      ALL_TAC] THEN
    UNDISCH_TAC `blocks_unique ts (all_vs refs (CONS t (APPEND xs stack)))` THEN
    REWRITE_TAC[blocks_unique_def] THEN
    DISCH_THEN(MP_TAC o SPECL [`t':num`; `a1:num`; `xs1:data_v list`; `a2:num`;
                               `xs2:data_v list`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t' < ts:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a l. ~(l = []) ==>
                      ~(data_Block t' a l IN all_vs refs (CONS t (APPEND xs stack)))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`ts:num`; `refs:(data_v bvl_ref)spt`; `t:data_v`;
      `xs:data_v list`; `stack:data_v list`; `t':num`; `l:data_v list`; `a:num`]
      blocks_unique_GT_ts) THEN ASM_REWRITE_TAC[GE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC v_all_vs_list_to_v2 THEN
  MAP_EVERY EXISTS_TAC [`t:data_v`; `stack:data_v list`; `refs:(data_v bvl_ref)spt`] THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `data_Block t' a1 xs1 IN
               all_vs refs (CONS (data_list_to_v ts t xs) stack)` THEN
  UNDISCH_TAC `data_Block t' a2 xs2 IN
               all_vs refs (CONS (data_list_to_v ts t xs) stack)` THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`a1:num`; `xs1:data_v list`] th) THEN
                          MP_TAC(SPECL [`a2:num`; `xs2:data_v list`] th)) THEN
  ASM_REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* the constant at the head of a term (if any) *)
let mp7_leaf_const t = try fst(dest_const(fst(strip_comb t))) with Failure _ -> "";;
(* heap lookups in a heap with an unused block, before and after a list of  *)
(* elements hs is allocated at its start (cons_multi_thm)                   *)
let MP7AUX_heap_lookup_expand = prove
 (`!(ha:((A,B)heap_element)list) hb S n.
     0 < S ==>
     heap_lookup n (APPEND (APPEND ha (heap_expand S)) hb) =
     if n < heap_length ha then heap_lookup n ha
     else if n < heap_length ha + S then
       (if n = heap_length ha then SOME (Unused (S - 1)) else NONE)
     else heap_lookup (n - (heap_length ha + S)) hb`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[heap_expand_def; ARITH_RULE `0 < S ==> ~(S = 0)`; GSYM APPEND_ASSOC;
               APPEND] THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[heap_lookup_def; el_length_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < S ==> S - 1 + 1 = S`] THEN
  SUBGOAL_THEN `(n - heap_length (ha:((A,B)heap_element)list) = 0 <=> n = heap_length ha) /\
                (n - heap_length ha < S <=> n < heap_length ha + S) /\
                n - heap_length ha - S = n - (heap_length ha + S)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC);;
let MP7AUX_heap_lookup_alloc = prove
 (`!(ha:((A,B)heap_element)list) hs hb S n.
     0 < heap_length hs /\ heap_length hs <= S ==>
     heap_lookup n
       (APPEND (APPEND (APPEND ha hs) (heap_expand (S - heap_length hs))) hb) =
     if n < heap_length ha then heap_lookup n ha
     else if n < heap_length ha + heap_length hs then heap_lookup (n - heap_length ha) hs
     else if n < heap_length ha + S then
       (if n = heap_length ha + heap_length hs
        then SOME (Unused (S - heap_length hs - 1)) else NONE)
     else heap_lookup (n - (heap_length ha + S)) hb`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `S = heap_length (hs:((A,B)heap_element)list)` THENL
   [ASM_REWRITE_TAC[SUB_REFL; heap_expand_def; APPEND; GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND; heap_length_APPEND] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(n - heap_length (ha:((A,B)heap_element)list) <
                   heap_length (hs:((A,B)heap_element)list) <=>
                   n < heap_length ha + heap_length hs) /\
                  n - heap_length ha - heap_length hs =
                  n - (heap_length ha + heap_length hs)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`APPEND (ha:((A,B)heap_element)list) hs`; `hb:((A,B)heap_element)list`;
                 `S - heap_length (hs:((A,B)heap_element)list)`; `n:num`]
         MP7AUX_heap_lookup_expand) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[heap_length_APPEND; data_to_word_memoryProof_heap_lookup_APPEND] THEN
  SUBGOAL_THEN `(heap_length (ha:((A,B)heap_element)list) +
                 heap_length (hs:((A,B)heap_element)list)) +
                S - heap_length hs = heap_length ha + S`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list)` THEN
  ASM_SIMP_TAC[ARITH_RULE `n < h ==> n < h + k`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
let MP7AUX_not_isSome_unused = prove
 (`!c k. ~isSomeDataElement (if c then SOME (Unused k:(A,B)heap_element) else NONE)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[isSomeDataElement_def; option_INJ; option_DISTINCT;
              distinctness "heap_element"]);;
(* consequences: data elements of the old heap stay, and are outside the   *)
(* unused block; the data elements of the new heap                          *)
let MP7AUX_alloc_facts = prove
 (`!(ha:((A,B)heap_element)list) hs hb S.
     0 < heap_length hs /\ heap_length hs <= S ==>
     (!n. isSomeDataElement (heap_lookup n (APPEND (APPEND ha (heap_expand S)) hb)) ==>
          heap_lookup n
            (APPEND (APPEND (APPEND ha hs) (heap_expand (S - heap_length hs))) hb) =
          heap_lookup n (APPEND (APPEND ha (heap_expand S)) hb)) /\
     (!n. isSomeDataElement (heap_lookup n (APPEND (APPEND ha (heap_expand S)) hb)) ==>
          n < heap_length ha \/ heap_length ha + S <= n) /\
     (!j. j < heap_length hs ==>
          heap_lookup (heap_length ha + j)
            (APPEND (APPEND (APPEND ha hs) (heap_expand (S - heap_length hs))) hb) =
          heap_lookup j hs) /\
     (!n. isSomeDataElement (heap_lookup n
            (APPEND (APPEND (APPEND ha hs) (heap_expand (S - heap_length hs))) hb)) <=>
          isSomeDataElement (heap_lookup n (APPEND (APPEND ha (heap_expand S)) hb)) \/
          heap_length ha <= n /\ n < heap_length ha + heap_length hs /\
          isSomeDataElement (heap_lookup (n - heap_length ha) hs)) /\
     heap_length (APPEND (APPEND (APPEND ha hs) (heap_expand (S - heap_length hs))) hb) =
     heap_length (APPEND (APPEND ha (heap_expand S)) hb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < S` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MP7AUX_heap_lookup_expand; MP7AUX_heap_lookup_alloc] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list) + S` THEN
    ASM_REWRITE_TAC[MP7AUX_not_isSome_unused] THEN
    SUBGOAL_THEN `~(n < heap_length (ha:((A,B)heap_element)list) +
                        heap_length (hs:((A,B)heap_element)list))`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    GEN_TAC THEN ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list) + S` THEN
    ASM_REWRITE_TAC[MP7AUX_not_isSome_unused] THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(h + j < h:num)`; LT_ADD_LCANCEL; ADD_SUB2];
    GEN_TAC THEN ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list)` THENL
     [SUBGOAL_THEN `~(heap_length (ha:((A,B)heap_element)list) <= n)`
        (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `heap_length (ha:((A,B)heap_element)list) <= n` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list) +
                       heap_length (hs:((A,B)heap_element)list)` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `n < heap_length (ha:((A,B)heap_element)list) + S`
        (fun th -> REWRITE_TAC[th; MP7AUX_not_isSome_unused]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list) + S` THEN
    ASM_REWRITE_TAC[MP7AUX_not_isSome_unused];
    REWRITE_TAC[heap_length_APPEND; heap_expand_def] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < S ==> ~(S = 0)`] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[heap_length_NIL; GC1AUX_heap_length_CONS; el_length_def] THEN
    ASM_ARITH_TAC]);;
(* heap_split at or below the length of a prefix does not look beyond it *)
let MP7AUX_heap_split_prefix = prove
 (`!s (ha:((A,B)heap_element)list) X Y h1 h2.
     s <= heap_length ha /\ heap_split s (APPEND ha X) = SOME (h1,h2) ==>
     ?h2'. heap_split s (APPEND ha Y) = SOME (h1,h2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_split_APPEND_if] THEN
  ASM_CASES_TAC `s < heap_length (ha:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[] THENL
   [CASES_ON `heap_split s (ha:((A,B)heap_element)list)` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `s = heap_length (ha:((A,B)heap_element)list)` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_REFL; heap_split_0] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[]]);;
(* unused_space_inv after the allocation of hs at the start of the unused *)
(* block                                                                    *)
let MP7AUX_alloc_unused_space_inv = prove
 (`!(ha:((A,B)heap_element)list) hs hb sp sp1.
     unused_space_inv (heap_length ha) (sp + sp1)
       (APPEND (APPEND ha (heap_expand (sp + sp1))) hb) /\
     0 < heap_length hs /\ heap_length hs <= sp /\ ALL isDataElement hs ==>
     unused_space_inv (heap_length ha + heap_length hs) ((sp - heap_length hs) + sp1)
       (APPEND (APPEND (APPEND ha hs) (heap_expand ((sp + sp1) - heap_length hs))) hb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `hs:((A,B)heap_element)list`;
                 `hb:((A,B)heap_element)list`; `sp + sp1`] MP7AUX_alloc_facts) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `unused_space_inv (heap_length ha) (sp + sp1)
       (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:((A,B)heap_element)list))` THEN
  REWRITE_TAC[unused_space_inv_def] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `hs:((A,B)heap_element)list`;
                   `hb:((A,B)heap_element)list`; `sp + sp1`;
                   `heap_length (ha:((A,B)heap_element)list) + heap_length (hs:((A,B)heap_element)list)`]
           MP7AUX_heap_lookup_alloc) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < k ==> ~(h + k < h)`; LT_REFL] THEN
    COND_CASES_TAC THENL [ALL_TAC; MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC] THEN
    REWRITE_TAC[option_INJ; injectivity "heap_element"] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM heap_length_APPEND] THEN ONCE_REWRITE_TAC[APPEND_ASSOC] THEN
    REWRITE_TAC[data_up_to_APPEND; ALL_APPEND] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `data_up_to (heap_length ha)
       (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:((A,B)heap_element)list))` THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; data_up_to_APPEND]]);;
(* gc_kind_inv after the allocation *)
let MP7AUX_alloc_gc_kind_inv = prove
 (`!c (ha:((A,data_to_word_memoryProof_tag#B)heap_element)list) hs hb sp sp1 gens.
     gc_kind_inv c (heap_length ha) sp sp1 gens
       (APPEND (APPEND ha (heap_expand (sp + sp1))) hb) /\
     0 < heap_length hs /\ heap_length hs <= sp /\ ALL (\x. ~isRef x) hs ==>
     gc_kind_inv c (heap_length ha + heap_length hs) (sp - heap_length hs) sp1 gens
       (APPEND (APPEND (APPEND ha hs) (heap_expand ((sp + sp1) - heap_length hs))) hb)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gc_kind_inv_def] THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(heap_length (ha:((A,data_to_word_memoryProof_tag#B)heap_element)list) +
                 heap_length (hs:((A,data_to_word_memoryProof_tag#B)heap_element)list)) +
                (sp - heap_length hs) + sp1 = heap_length ha + sp + sp1`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `gen_state_ok (heap_length ha) (heap_length ha + sp + sp1)
      (APPEND (APPEND ha (heap_expand (sp + sp1)))
         (hb:((A,data_to_word_memoryProof_tag#B)heap_element)list)) gens` THEN
    CASES_ON `gens:gen_state` THEN REWRITE_TAC[gen_state_ok_def; GSYM ALL_MEM] THEN
    STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `s:num` THEN DISCH_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `x <= h ==> x <= h + k:num`];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `s:num`)) THEN ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    REWRITE_TAC[gen_start_ok_def; GSYM APPEND_ASSOC] THEN
    UNDISCH_TAC `gen_start_ok (APPEND (APPEND ha (heap_expand (sp + sp1)))
           (hb:((A,data_to_word_memoryProof_tag#B)heap_element)list))
           (heap_length ha + sp + sp1) s` THEN
    REWRITE_TAC[gen_start_ok_def; GSYM APPEND_ASSOC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:((A,data_to_word_memoryProof_tag#B)heap_element)list`
      (X_CHOOSE_THEN `g2:((A,data_to_word_memoryProof_tag#B)heap_element)list`
         STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`s:num`; `ha:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
        `APPEND (heap_expand (sp + sp1))
           (hb:((A,data_to_word_memoryProof_tag#B)heap_element)list)`;
        `APPEND (hs:((A,data_to_word_memoryProof_tag#B)heap_element)list)
           (APPEND (heap_expand ((sp + sp1) - heap_length hs)) hb)`;
        `g1:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
        `g2:((A,data_to_word_memoryProof_tag#B)heap_element)list`]
        MP7AUX_heap_split_prefix) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `g3:((A,data_to_word_memoryProof_tag#B)heap_element)list`) THEN
    MAP_EVERY EXISTS_TAC [`g1:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
      `g3:((A,data_to_word_memoryProof_tag#B)heap_element)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (ha:((A,data_to_word_memoryProof_tag#B)heap_element)list) + sp + sp1 =
     heap_length (APPEND ha (heap_expand (sp + sp1)):
                    ((A,data_to_word_memoryProof_tag#B)heap_element)list) /\
     heap_length ha + sp + sp1 =
     heap_length (APPEND (APPEND ha hs) (heap_expand ((sp + sp1) - heap_length hs)))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; heap_expand_def] THEN
    SUBGOAL_THEN `~(sp + sp1 = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\x. ~isRef x) (ha:((A,data_to_word_memoryProof_tag#B)heap_element)list) /\
                ALL isRef (hb:((A,data_to_word_memoryProof_tag#B)heap_element)list)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `heap_split (heap_length ha + sp + sp1)
      (APPEND (APPEND ha (heap_expand (sp + sp1)))
        (hb:((A,data_to_word_memoryProof_tag#B)heap_element)list)) = SOME (h1,h2)` THEN
    ONCE_REWRITE_TAC[ASSUME
     `heap_length (ha:((A,data_to_word_memoryProof_tag#B)heap_element)list) + sp + sp1 =
      heap_length (APPEND ha (heap_expand (sp + sp1)):
                     ((A,data_to_word_memoryProof_tag#B)heap_element)list)`] THEN
    REWRITE_TAC[heap_split_length; option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    UNDISCH_TAC `ALL (\x. ~isRef x)
      (APPEND (ha:((A,data_to_word_memoryProof_tag#B)heap_element)list)
              (heap_expand (sp + sp1)))` THEN
    ASM_SIMP_TAC[ALL_APPEND];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND ha hs) (heap_expand ((sp + sp1) - heap_length hs)):
       ((A,data_to_word_memoryProof_tag#B)heap_element)list`;
    `hb:((A,data_to_word_memoryProof_tag#B)heap_element)list`] THEN
  ONCE_REWRITE_TAC[ASSUME
   `heap_length (ha:((A,data_to_word_memoryProof_tag#B)heap_element)list) + sp + sp1 =
    heap_length (APPEND (APPEND ha hs) (heap_expand ((sp + sp1) - heap_length hs)))`] THEN
  REWRITE_TAC[heap_split_length; ALL_APPEND] THEN ASM_REWRITE_TAC[heap_expand_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ALL; isRef_def]);;
(* the abstract invariants of cons_multi_thm, one by one: the old heap is   *)
(* APPEND (APPEND ha (heap_expand (sp + sp1))) hb, the new one has the      *)
(* blocks list_to_BlockReps conf rt (heap_length ha) rs at the start of the *)
(* unused block                                                             *)
let MP7AUX_cm_alloc_facts = prove
 (`!conf rt rs (ha:mp7heap) sp.
     ~(rs = []) /\ 3 * LENGTH rs <= sp ==>
     0 < heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap) /\
     heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap) <= sp /\
     heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap) = 3 * LENGTH rs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[list_to_BlockReps_heap_length] THEN
  UNDISCH_TAC `~(rs:((A word_loc)heap_address)list = [])` THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC);;
let MP7AUX_cm_roots_ok = prove
 (`!conf rt rs roots2 (ha:mp7heap) hb sp sp1 (u:A word_loc).
     roots_ok (CONS rt (APPEND rs roots2)) (APPEND (APPEND ha (heap_expand (sp + sp1))) hb) /\
     ~(rs = []) /\ 3 * LENGTH rs <= sp ==>
     roots_ok (CONS (Pointer (heap_length ha) u) roots2)
       (APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
          (heap_expand ((sp + sp1) -
             heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) hb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `rt:(A word_loc)heap_address`;
    `rs:((A word_loc)heap_address)list`; `ha:mp7heap`; `sp:num`]
    MP7AUX_cm_alloc_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ha:mp7heap`; `list_to_BlockReps conf rt (heap_length (ha:mp7heap)) rs:mp7heap`;
                 `hb:mp7heap`; `sp + sp1`] MP7AUX_alloc_facts) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `roots_ok (CONS rt (APPEND rs roots2))
     (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap))` THEN
  ASM_REWRITE_TAC[roots_ok_def; MEM; MEM_APPEND] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th))) THEN
    REWRITE_TAC[injectivity "heap_address"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LE_REFL; SUB_REFL] THEN
    ASM_SIMP_TAC[list_to_BlockReps_heap_lookup_0] THEN ASM_ARITH_TAC;
    DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;
let MP7AUX_cm_heap_ok = prove
 (`!conf rt rs roots2 (ha:mp7heap) hb sp sp1 limit.
     heap_ok (APPEND (APPEND ha (heap_expand (sp + sp1))) hb) limit /\
     roots_ok (CONS rt (APPEND rs roots2)) (APPEND (APPEND ha (heap_expand (sp + sp1))) hb) /\
     ~(rs = []) /\ 3 * LENGTH rs <= sp ==>
     heap_ok
       (APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
          (heap_expand ((sp + sp1) -
             heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) hb)
       limit`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `rt:(A word_loc)heap_address`;
    `rs:((A word_loc)heap_address)list`; `ha:mp7heap`; `sp:num`]
    MP7AUX_cm_alloc_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ha:mp7heap`; `list_to_BlockReps conf rt (heap_length (ha:mp7heap)) rs:mp7heap`;
                 `hb:mp7heap`; `sp + sp1`] MP7AUX_alloc_facts) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `heap_ok (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap)) limit` THEN
  REWRITE_TAC[heap_ok_def] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. FILTER isForwardPointer (heap_expand n:mp7heap) = []` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[FILTER; isForwardPointer_def];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `FILTER isForwardPointer
      (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap)) = []` THEN
    ASM_SIMP_TAC[FILTER_APPEND; APPEND_EQ_NIL; list_to_BlockReps_ForwardPointer] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!xs l d. ~MEM (DataElement xs l d) (heap_expand (sp + sp1):mp7heap) /\
                         ~MEM (DataElement xs l d)
                            (heap_expand ((sp + sp1) - heap_length
                               (list_to_BlockReps conf rt (heap_length (ha:mp7heap)) rs:mp7heap)):mp7heap)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[MEM; distinctness "heap_element"];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM_APPEND] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:((A word_loc)heap_address)list`; `l:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `u:A word_loc`] THEN
    ASM_REWRITE_TAC[MEM_APPEND];
    MP_TAC(ISPECL [`conf:data_to_word_config`; `rt:(A word_loc)heap_address`;
      `rs:((A word_loc)heap_address)list`; `heap_length (ha:mp7heap)`;
      `xs:((A word_loc)heap_address)list`; `l:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `ptr:num`; `u:A word_loc`]
      list_to_BlockReps_Pointer) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN UNDISCH_TAC `roots_ok (CONS rt (APPEND rs roots2))
        (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap))` THEN
      REWRITE_TAC[roots_ok_def] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `u:A word_loc` THEN ASM_REWRITE_TAC[MEM];
      DISJ1_TAC THEN UNDISCH_TAC `roots_ok (CONS rt (APPEND rs roots2))
        (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap))` THEN
      REWRITE_TAC[roots_ok_def] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `u:A word_loc` THEN ASM_REWRITE_TAC[MEM; MEM_APPEND];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ASM_MESON_TAC[];
    DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:((A word_loc)heap_address)list`; `l:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `u:A word_loc`] THEN
    ASM_REWRITE_TAC[MEM_APPEND]]);;
(* the assumption !n. P n ==> Q n \/ R n *)
let mp7_is_outside th =
  let c = concl th in
  is_forall c && is_imp(snd(strip_forall c)) && is_disj(rand(snd(strip_forall c)));;
let MP7AUX_cm_INJ_tf = prove
 (`!conf rt rs (ha:mp7heap) hb sp sp1 tf ts.
     INJ (FAPPLY tf) (FDOM tf)
       {a | isSomeDataElement (heap_lookup a (APPEND (APPEND ha (heap_expand (sp + sp1))) hb))} /\
     FDOM tf SUBSET {n | n < ts} /\ ~(rs = []) /\ 3 * LENGTH rs <= sp ==>
     INJ (FAPPLY (bind_each tf ts (heap_length ha) 3 (LENGTH rs)))
         (FDOM (bind_each tf ts (heap_length ha) 3 (LENGTH rs)))
       {a | isSomeDataElement (heap_lookup a
          (APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
             (heap_expand ((sp + sp1) -
                heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) hb))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `rt:(A word_loc)heap_address`;
    `rs:((A word_loc)heap_address)list`; `ha:mp7heap`; `sp:num`]
    MP7AUX_cm_alloc_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ha:mp7heap`; `list_to_BlockReps conf rt (heap_length (ha:mp7heap)) rs:mp7heap`;
                 `hb:mp7heap`; `sp + sp1`] MP7AUX_alloc_facts) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!t. t IN FDOM (tf:(num,num)fmap) ==> t < ts` ASSUME_TAC THENL
   [UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN FDOM (bind_each tf ts (heap_length (ha:mp7heap)) 3 (LENGTH (rs:((A word_loc)heap_address)list))) <=>
                    x IN FDOM tf \/ (ts <= x /\ x < ts + LENGTH (rs:((A word_loc)heap_address)list))`
    ASSUME_TAC THENL
   [REWRITE_TAC[bind_each_FDOM; IN_UNION; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN FDOM tf ==>
       FAPPLY (bind_each tf ts (heap_length (ha:mp7heap)) 3 (LENGTH (rs:((A word_loc)heap_address)list))) x = FAPPLY tf x`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC bind_each_eq_tf THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. ts <= x /\ x < ts + LENGTH (rs:((A word_loc)heap_address)list) ==>
       FAPPLY (bind_each tf ts (heap_length (ha:mp7heap)) 3 (LENGTH (rs:((A word_loc)heap_address)list))) x =
       heap_length ha + 3 * (x - ts)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MP7AUX_bind_each_FAPPLY_range THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
       {a | isSomeDataElement (heap_lookup a
              (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap)))}` THEN
  REWRITE_TAC[INJ; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_SIMP_TAC[];
      DISJ2_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `h <= h + k`; ADD_SUB2; LT_ADD_LCANCEL] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MP7AUX_heap_lookup_list_to_BlockReps THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[] THENL
   [ASM_MESON_TAC[];
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `FAPPLY (tf:(num,num)fmap) x` o check mp7_is_outside) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `FAPPLY (tf:(num,num)fmap) y` o check mp7_is_outside) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;
let MP7AUX_cm_v_inv = prove
 (`!conf rt rs (ha:mp7heap) hb sp sp1 tf ts n f v refs x.
     v_inv conf v refs (x,f,tf,APPEND (APPEND ha (heap_expand (sp + sp1))) hb) /\
     FDOM tf SUBSET {n | n < ts} /\ ~(rs = []) /\ 3 * LENGTH rs <= sp ==>
     v_inv conf v refs
       (x,f,bind_each tf ts (heap_length ha) 3 n,
        APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
          (heap_expand ((sp + sp1) -
             heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) hb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `rt:(A word_loc)heap_address`;
    `rs:((A word_loc)heap_address)list`; `ha:mp7heap`; `sp:num`]
    MP7AUX_cm_alloc_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC v_inv_SUBMAP THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
    `APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
          (heap_expand ((sp + sp1) -
             heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) (hb:mp7heap)`] THEN
  REWRITE_TAC[SUBMAP_REFL; heap_store_rel_def] THEN CONJ_TAC THENL
   [MATCH_MP_TAC bind_each_SUBMAP THEN
    UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC v_inv_lemma THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let MP7AUX_isSomeDataElement_blocks = prove
 (`(!(zs:((A word_loc)heap_address)list).
      isSomeDataElement (SOME (RefBlock zs:mp7el))) /\
   (!be flag bs (ws:(A word)list).
      isSomeDataElement (SOME (Bytes be flag bs ws))) /\
   (!ev (z:(A word_loc)heap_address).
      isSomeDataElement (SOME (ThunkBlock ev z:mp7el))) /\
   (!tg (zs:((A word_loc)heap_address)list).
      isSomeDataElement (SOME (BlockRep tg zs:mp7el)))`,
  REWRITE_TAC[RefBlock_def; data_to_word_memoryProof_Bytes_def; ThunkBlock_def;
              BlockRep_def; LET_DEF; LET_END_DEF; isSomeDataElement_def; option_INJ] THEN
  MESON_TAC[]);;
let MP7AUX_cm_bc_ref_inv = prove
 (`!conf rt rs (ha:mp7heap) hb sp sp1 tf ts f refs be k.
     bc_ref_inv conf k refs (f,tf,APPEND (APPEND ha (heap_expand (sp + sp1))) hb,be) /\
     FDOM tf SUBSET {n | n < ts} /\ ~(rs = []) /\ 3 * LENGTH rs <= sp ==>
     bc_ref_inv conf k refs
       (f,bind_each tf ts (heap_length ha) 3 (LENGTH rs),
        APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
          (heap_expand ((sp + sp1) -
             heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) hb,be)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `rt:(A word_loc)heap_address`;
    `rs:((A word_loc)heap_address)list`; `ha:mp7heap`; `sp:num`]
    MP7AUX_cm_alloc_facts) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ha:mp7heap`; `list_to_BlockReps conf rt (heap_length (ha:mp7heap)) rs:mp7heap`;
                 `hb:mp7heap`; `sp + sp1`] MP7AUX_alloc_facts) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!v x. v_inv conf v refs
      (x,f,tf,APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap)) ==>
      v_inv conf v refs
       (x,f,bind_each tf ts (heap_length ha) 3 (LENGTH rs),
        APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
          (heap_expand ((sp + sp1) -
             heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) hb)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MP7AUX_cm_v_inv THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!zs ys. ALL2 (\z y. v_inv conf y refs
      (z,f,tf,APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap))) zs ys ==>
      ALL2 (\z y. v_inv conf y refs
       (z,f,bind_each tf ts (heap_length ha) 3 (LENGTH rs),
        APPEND (APPEND (APPEND ha (list_to_BlockReps conf rt (heap_length ha) rs))
          (heap_expand ((sp + sp1) -
             heap_length (list_to_BlockReps conf rt (heap_length ha) rs:mp7heap)))) hb))
      zs ys`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN BETA_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th =
      `heap_length (list_to_BlockReps conf rt (heap_length (ha:mp7heap)) rs:mp7heap) =
       3 * LENGTH (rs:((A word_loc)heap_address)list)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
  UNDISCH_TAC `bc_ref_inv conf k refs
     (f,tf,APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap),be)` THEN
  REWRITE_TAC[bc_ref_inv_def] THEN
  CASES_ON `FLOOKUP (f:(num,num)fmap) k` THEN
  CASES_ON `lookup k (refs:(data_v bvl_ref)spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. t IN FDOM (tf:(num,num)fmap) ==> t < ts` ASSUME_TAC THENL
   [UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `a':data_v bvl_ref` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MP7AUX_isSomeDataElement_blocks] THEN
  TRY(EXISTS_TAC `zs:((A word_loc)heap_address)list` THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  TRY(EXISTS_TAC `z:(A word_loc)heap_address` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~(a IN IMAGE (FAPPLY (tf:(num,num)fmap)) (FDOM tf))` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `isSomeDataElement (heap_lookup a
        (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap)))` MP_TAC THENL
     [ASM_REWRITE_TAC[MP7AUX_isSomeDataElement_blocks]; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o check mp7_is_outside)) THEN
    REWRITE_TAC[IN_IMAGE; bind_each_FDOM; IN_UNION; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    REPEAT DISCH_TAC THEN X_GEN_TAC `y:num` THEN
    ASM_CASES_TAC `(y:num) IN FDOM (tf:(num,num)fmap)` THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[bind_each_eq_tf] THEN ASM_MESON_TAC[];
      STRIP_TAC THEN
      MP_TAC(SPECL [`LENGTH (rs:((A word_loc)heap_address)list)`; `tf:(num,num)fmap`;
        `ts:num`; `heap_length (ha:mp7heap)`; `3`; `y:num`]
        MP7AUX_bind_each_FAPPLY_range) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    EXISTS_TAC `zs:((A word_loc)heap_address)list` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
let MP7AUX_cm_reachable = prove
 (`!ts t xs stack refs n.
     reachable_refs (CONS (data_list_to_v ts t xs) stack) refs n ==>
     reachable_refs (CONS t (APPEND xs stack)) refs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def; MEM; MEM_APPEND] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`xs:data_v list`; `t:data_v`; `r:num`; `ts:num`] list_to_v_get_refs) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 16917 *)
let cons_multi_thm = prove
 (`!conf t xs stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (APPEND (CONS t xs) stack) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     3 * LENGTH xs <= sp /\ ~(xs = []) ==>
     ?rt rs roots2 heap1 heap2.
       let Allocd = list_to_BlockReps conf rt a rs in
       roots = APPEND (CONS rt rs) roots2 /\ LENGTH rs = LENGTH xs /\
       heap = APPEND (APPEND heap1 (heap_expand (sp + sp1))) heap2 /\
       a = heap_length heap1 /\
       abs_ml_inv conf
         (CONS (data_list_to_v ts t xs) stack) refs
         (CONS (Pointer a (wl_Word (ptr_bits conf cons_tag 2))) roots2,
          APPEND (APPEND (APPEND heap1 Allocd)
                         (heap_expand ((sp + sp1) - heap_length Allocd)))
                 heap2, be,
          a + heap_length Allocd, sp - heap_length Allocd, sp1, gens)
         limit (ts + LENGTH xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def] THEN STRIP_TAC THEN
  UNDISCH_TAC `bc_stack_ref_inv conf ts (APPEND (CONS t xs) stack) refs
                 (roots,heap:mp7heap,be)` THEN
  REWRITE_TAC[bc_stack_ref_inv_def; APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(num,num)fmap` (X_CHOOSE_THEN `tf:(num,num)fmap`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    mp7_leaf_const(concl th) = "ALL2" && is_comb(rator(concl th)) &&
    (try mp7_leaf_const(rand(rator(concl th))) = "CONS" with Failure _ -> false))) THEN
  REWRITE_TAC[LIST_REL_CONS1; LIST_REL_SPLIT1] THEN
  DISCH_THEN(X_CHOOSE_THEN `rt:(A word_loc)heap_address`
    (X_CHOOSE_THEN `rest:((A word_loc)heap_address)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (xs:data_v list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `~(rs:((A word_loc)heap_address)list = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  SUBGOAL_THEN `3 * LENGTH (rs:((A word_loc)heap_address)list) <= sp` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sp + sp1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(xs:data_v list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?ha hb. heap = APPEND (APPEND ha (heap_expand (sp + sp1))) hb /\
                        a = heap_length (ha:mp7heap)`
    (X_CHOOSE_THEN `ha:mp7heap` (X_CHOOSE_THEN `hb:mp7heap`
       (CONJUNCTS_THEN SUBST_ALL_TAC))) THENL
   [UNDISCH_TAC `unused_space_inv a (sp + sp1) (heap:mp7heap)` THEN
    ASM_REWRITE_TAC[unused_space_inv_def] THEN
    DISCH_THEN(MP_TAC o MATCH_MP heap_lookup_SPLIT o CONJUNCT1) THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ha:mp7heap`; `hb:mp7heap`] THEN
    ASM_REWRITE_TAC[heap_expand_def; GSYM APPEND_ASSOC; APPEND];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rt:(A word_loc)heap_address`; `rs:((A word_loc)heap_address)list`;
    `roots2:((A word_loc)heap_address)list`; `ha:mp7heap`; `hb:mp7heap`] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; APPEND] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `rt:(A word_loc)heap_address`;
    `rs:((A word_loc)heap_address)list`; `ha:mp7heap`; `sp:num`]
    MP7AUX_cm_alloc_facts) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  REWRITE_TAC[abs_ml_inv_def] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MP7AUX_cm_roots_ok THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MP7AUX_cm_heap_ok THEN EXISTS_TAC `roots2:((A word_loc)heap_address)list` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MP7AUX_alloc_gc_kind_inv THEN ASM_SIMP_TAC[list_to_BlockReps_Ref];
    MATCH_MP_TAC MP7AUX_alloc_unused_space_inv THEN
    ASM_SIMP_TAC[list_to_BlockReps_isDataElement];
    ALL_TAC] THEN
  REWRITE_TAC[bc_stack_ref_inv_def] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`;
    `bind_each tf ts (heap_length (ha:mp7heap)) 3 (LENGTH (xs:data_v list))`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ha:mp7heap`; `list_to_BlockReps conf rt (heap_length (ha:mp7heap)) rs:mp7heap`;
                 `hb:mp7heap`; `sp + sp1`] MP7AUX_alloc_facts) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f)
      {a | isSomeDataElement (heap_lookup a
         (APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap)))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (xs:data_v list)`)) THEN
    MATCH_MP_TAC MP7AUX_cm_INJ_tf THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[bind_each_FDOM; UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `all_ts refs (CONS t (APPEND xs stack))` THEN
      ASM_REWRITE_TAC[all_ts_SUBSET_list_to_v];
      REWRITE_TAC[new_all_ts_SUBSET_list_to_v]];
    MATCH_MP_TAC FDOM_bind_each_lemma THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC blocks_unique_cons_multi THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC
     [`Pointer (heap_length (ha:mp7heap)) (wl_Word (ptr_bits conf cons_tag 2:A word))`;
      `roots2:((A word_loc)heap_address)list`] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC v_inv_list_to_v THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs
         (x,f,tf,APPEND (APPEND ha (heap_expand (sp + sp1))) (hb:mp7heap))) stack roots2` THEN
      MATCH_MP_TAC MONO_ALL2 THEN REPEAT GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC MP7AUX_cm_v_inv THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (xs:data_v list)`)) THEN
    MATCH_MP_TAC MP7AUX_cm_bc_ref_inv THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP7AUX_cm_reachable THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A little separation logic automation (HOL4's SEP_R_TAC, SEP_W_TAC and     *)
(* AC STAR_COMM STAR_ASSOC): assertions are STAR trees whose leaves are       *)
(* compared syntactically.                                                    *)
(* ------------------------------------------------------------------------- *)

let MP7AUX_STAR_AC = prove
 (`!p q r:(A->bool)->bool.
     p STAR q = q STAR p /\ (p STAR q) STAR r = p STAR (q STAR r) /\
     p STAR (q STAR r) = q STAR (p STAR r)`,
  MESON_TAC[STAR_ASSOC; STAR_COMM]);;
let mp7_is_star tm =
  is_comb tm && is_comb (rator tm) && is_const (rator (rator tm)) &&
  fst(dest_const(rator(rator tm))) = "STAR";;
let rec mp7_star_leaves tm =
  if mp7_is_star tm then mp7_star_leaves (rand(rator tm)) @ mp7_star_leaves (rand tm)
  else [tm];;
let mp7_is_one tm =
  is_comb tm && is_const (rator tm) && fst(dest_const(rator tm)) = "set_sep_one";;
(* |- P = t STAR rest, for a leaf t of the STAR tree P (at least two leaves) *)
let mp7_star_rotate p t =
  let ls = mp7_star_leaves p in
  let rec remove l = match l with
      [] -> failwith "mp7_star_rotate"
    | h::r -> if aconv h t then r else h :: remove r in
  let rest = remove ls in
  if rest = [] then failwith "mp7_star_rotate: single leaf" else
  let star = rator(rator p) in
  let mk a b = mk_comb(mk_comb(star,a),b) in
  let restm = end_itlist mk rest in
  AC MP7AUX_STAR_AC (mk_eq(p, mk t restm));;
(* from P (fun2set (m,d)) the facts m a = x and a IN d of every leaf      *)
(* set_sep_one (a,x) of P                                                  *)
let mp7_sep_reads th =
  let p,s = dest_comb (concl th) in
  if not (is_comb s && is_const (rator s) && fst(dest_const(rator s)) = "fun2set")
  then failwith "mp7_sep_reads" else
  mapfilter (fun t ->
      if mp7_is_one t then
        MATCH_MP read_fun2set (EQ_MP (AP_THM (mp7_star_rotate p t) s) th)
      else failwith "") (mp7_star_leaves p);;
let MP7AUX_SEP_R_TAC : tactic = fun (asl,w as g) ->
  let facts = flat (mapfilter (fun (_,th) -> mp7_sep_reads th) asl) in
  MAP_EVERY STRIP_ASSUME_TAC facts g;;
(* from P (fun2set (m,d)) with a leaf set_sep_one (a,x): the assertion with *)
(* set_sep_one (a,y) instead, in fun2set ((a =+ y) m,d)                    *)
let mp7_sep_write a y th =
  let p,s = dest_comb (concl th) in
  let t = find (fun t -> mp7_is_one t && aconv (fst(dest_pair(rand t))) a)
               (mp7_star_leaves p) in
  let th1 = EQ_MP (AP_THM (mp7_star_rotate p t) s) th in
  MATCH_MP (ISPEC y write_fun2set) th1;;
(* prove Q s from an assumption P s with P and Q equal up to AC of STAR *)
let MP7AUX_SEP_AC_TAC : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let tryone (_,th) =
    let p,s' = dest_comb (concl th) in
    if not (aconv s s') then failwith "" else
    let eq = AC MP7AUX_STAR_AC (mk_eq(q,p)) in
    EQ_MP (SYM (AP_THM eq s)) th in
  ACCEPT_TAC (tryfind tryone asl) g;;
(* the memory part of memory_rel_append: words written at the start of the  *)
(* unused block that represent the new heap elements L                      *)
let MP7AUX_append_sep = prove
 (`!(curr:A word) (heap1:mp7heap) heap2 L S c WO aw (m:A word -> A word_loc) dm.
     (word_heap curr (APPEND (APPEND heap1 (heap_expand S)) heap2) c STAR WO)
       (fun2set (m,dm)) /\
     (misc_word_list (word_add curr (word_mul bytes_in_word (word (heap_length heap1)))) aw
        STAR SEP_T) (fun2set (m,dm)) /\
     misc_word_list (word_add curr (word_mul bytes_in_word (word (heap_length heap1)))) aw =
       word_heap (word_add curr (word_mul bytes_in_word (word (heap_length heap1)))) L c /\
     LENGTH aw = heap_length L /\ heap_length L <= S ==>
     (word_heap curr
        (APPEND (APPEND (APPEND heap1 L) (heap_expand (S - heap_length L))) heap2) c STAR WO)
       (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `A = word_add (curr:A word) (word_mul bytes_in_word (word (heap_length (heap1:mp7heap))))` THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(word_heap curr (APPEND (APPEND heap1 (heap_expand S)) heap2) c STAR WO)
       (fun2set (m:A word -> A word_loc,dm))` THEN
  ASM_REWRITE_TAC[word_heap_APPEND; heap_length_APPEND; gc_shared_heap_length_heap_expand;
                  word_heap_heap_expand] THEN
  SUBGOAL_THEN `word_add (curr:A word)
                  (word_mul bytes_in_word (word (heap_length (heap1:mp7heap) + S))) =
                word_add A (word_mul bytes_in_word (word S))` SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`m:A word -> A word_loc`; `dm:A word->bool`; `aw:(A word_loc)list`; `A:A word`;
    `word_heap (curr:A word) heap1 c STAR
     word_heap (word_add (A:A word) (word_mul bytes_in_word (word S))) (heap2:mp7heap) c STAR WO`;
    `S:num`] word_list_AND_word_list_exists_IMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP7AUX_SEP_AC_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (curr:A word) (word_mul bytes_in_word
                  (word (heap_length (heap1:mp7heap) + heap_length (L:mp7heap)))) =
                word_add A (word_mul bytes_in_word (word (heap_length L)))` SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `(heap_length (heap1:mp7heap) + heap_length (L:mp7heap)) + S - heap_length L =
                heap_length heap1 + S` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (curr:A word)
                  (word_mul bytes_in_word (word (heap_length (heap1:mp7heap) + S))) =
                word_add A (word_mul bytes_in_word (word S))` SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP7AUX_SEP_AC_TAC);;
(* the pointer to the first cons cell of memory_rel_append *)
let MP7AUX_make_cons_ptr_get_addr = prove
 (`!c a. good_dimindex (:A) /\ backend_common_word_shift (:A) <= shift_length c ==>
     make_cons_ptr c (word_mul bytes_in_word (word a):A word) 0 2 =
     wl_Word (get_addr c a (wl_Word (ptr_bits c 0 2:A word)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[make_cons_ptr_def; get_addr_def; bytes_in_word_mul_eq_shift;
               WORD_SHL_COMPOSE; get_lowerbits_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `s <= l ==> s + l - s = l`; injectivity "word_loc"] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* HOL4 line 17282 *)
let memory_rel_append = prove
 (`!c be ts refs sp st m1 dm v h in1 ws vars next_free init_ptr curr.
     memory_rel c be ts refs sp st m1 dm
       (APPEND (CONS (v,h) (ZIP in1 ws)) vars) /\
     (misc_word_list next_free
        (append_writes c init_ptr (make_header c (word 0) 2) ws h) STAR SEP_T)
       (fun2set (m1,dm)) /\
     1 < data_to_word_config_len_size c /\
     LENGTH in1 = LENGTH ws /\ ~(in1 = []) /\
     3 * LENGTH in1 <= sp /\ good_dimindex (:A) /\
     wl_Word init_ptr = make_cons_ptr c (word_sub next_free curr) 0 2 /\
     FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
     FLOOKUP st NextFree = SOME (wl_Word (next_free:A word)) ==>
     memory_rel c be (ts + LENGTH in1) refs (sp - 3 * LENGTH in1)
       (st |+ (NextFree,
               wl_Word (word_add next_free
                          (word_mul bytes_in_word (word (3 * LENGTH in1)))))) m1 dm
       (CONS (data_list_to_v ts v in1,wl_Word init_ptr) vars)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `memory_rel c be ts refs sp st (m1:A word -> A word_loc) dm
       (APPEND (CONS (v,h) (ZIP in1 ws)) vars)` THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; MAP_APPEND; MAP] THEN
  FIRST_ASSUM(fun th -> if concl th = `LENGTH (in1:data_v list) = LENGTH (ws:(A word_loc)list)`
    then REWRITE_TAC[MATCH_MP MAP_FST_ZIP th; MATCH_MP MAP_SND_ZIP th] else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `heap:mp7heap` (X_CHOOSE_THEN `limit:num`
    (X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `sp0:num` (X_CHOOSE_THEN `sp1:num`
    (X_CHOOSE_THEN `gens:gen_state` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `hs:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)
       STRIP_ASSUME_TAC)))))))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `in1:data_v list`;
    `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
    `hs:((A word_loc)heap_address)list`; `heap:mp7heap`; `be:bool`; `a:num`; `sp0:num`;
    `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`] cons_multi_thm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `rt:(A word_loc)heap_address`
    (X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `heap1:mp7heap` (X_CHOOSE_THEN `heap2:mp7heap` STRIP_ASSUME_TAC))))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && mem (fst(dest_var(lhs(concl th)))) ["hs";"heap";"a"]))) THEN
  SUBGOAL_THEN `LENGTH (CONS (rt:(A word_loc)heap_address) rs) = LENGTH (CONS (h:A word_loc) ws)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> mp7_leaf_const(concl th) = "ALL2" &&
    (try mp7_leaf_const(rand(concl th)) = "APPEND" with Failure _ -> false))) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LIST_REL_APPEND_EQ th]) THEN
  REWRITE_TAC[ALL2] THEN STRIP_TAC THEN
  UNDISCH_TAC `heap_in_memory_store (APPEND (APPEND heap1 (heap_expand (sp0 + sp1))) heap2)
     (heap_length heap1) sp0 sp1 gens c st (m1:A word -> A word_loc) dm limit` THEN
  REWRITE_TAC[heap_in_memory_store_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `curr0:A word`
      (X_CHOOSE_THEN `other:A word` STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `curr0:A word = curr` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP st CurrHeap = SOME (wl_Word (curr0:A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `next_free = word_add curr (word_mul bytes_in_word
                  (word (heap_length (heap1:mp7heap)))):A word` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `FLOOKUP st NextFree = SOME (wl_Word (next_free:A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(rs:((A word_loc)heap_address)list = [])` ASSUME_TAC THENL
   [UNDISCH_TAC `~(in1:data_v list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (list_to_BlockReps c rt (heap_length (heap1:mp7heap)) rs:mp7heap) =
                3 * LENGTH (in1:data_v list)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[list_to_BlockReps_heap_length]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND (APPEND heap1 (list_to_BlockReps c rt (heap_length (heap1:mp7heap)) rs))
       (heap_expand ((sp0 + sp1) -
          heap_length (list_to_BlockReps c rt (heap_length (heap1:mp7heap)) rs:mp7heap))))
       (heap2:mp7heap)`;
    `limit:num`;
    `heap_length (heap1:mp7heap) +
     heap_length (list_to_BlockReps c rt (heap_length (heap1:mp7heap)) rs:mp7heap)`;
    `sp0 - heap_length (list_to_BlockReps c rt (heap_length (heap1:mp7heap)) rs:mp7heap)`;
    `sp1:num`; `gens:gen_state`] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `0 < LENGTH (in1:data_v list)` ASSUME_TAC THENL
        [UNDISCH_TAC `~(in1:data_v list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
         ALL_TAC] THEN
       MP_TAC(ISPECL [`heap1:mp7heap`; `list_to_BlockReps c rt (heap_length (heap1:mp7heap)) rs:mp7heap`;
                      `heap2:mp7heap`; `sp0 + sp1`] MP7AUX_alloc_facts) THEN
       ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
       ASM_REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT; distinctness "store_name"] THEN
       MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN
       ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `(heap_length (heap1:mp7heap) + 3 * LENGTH (ws:(A word_loc)list)) + sp0 - 3 * LENGTH ws =
                     heap_length heap1 + sp0 /\
                     (heap_length heap1 + 3 * LENGTH ws) + sp0 - 3 * LENGTH ws + sp1 =
                     heap_length heap1 + sp0 + sp1` (fun th -> REWRITE_TAC[th]) THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       CONJ_TAC THENL [REWRITE_TAC[option_INJ; injectivity "word_loc"; WORD_ADD] THEN
         CONV_TAC WORD_RULE; ALL_TAC] THEN
     SUBGOAL_THEN `3 * LENGTH (ws:(A word_loc)list) =
          heap_length (list_to_BlockReps c rt (heap_length (heap1:mp7heap)) rs:mp7heap)` SUBST1_TAC THENL
        [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `?x xs. rs = CONS (x:(A word_loc)heap_address) xs` STRIP_ASSUME_TAC THENL
        [ASM_MESON_TAC[list_CASES]; ALL_TAC] THEN
       SUBGOAL_THEN `?w ws'. ws = CONS (w:A word_loc) ws'` STRIP_ASSUME_TAC THENL
        [UNDISCH_TAC `~(in1:data_v list = [])` THEN
         UNDISCH_TAC `LENGTH (in1:data_v list) = LENGTH (ws:(A word_loc)list)` THEN
         MESON_TAC[list_CASES; LENGTH_EQ_NIL];
         ALL_TAC] THEN
       FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
     SUBGOAL_THEN `misc_word_list (word_add curr (word_mul bytes_in_word (word (heap_length (heap1:mp7heap)))))
           (append_writes c init_ptr (make_header c (word 0) 2) (CONS w ws') (h:A word_loc)) =
         word_heap (word_add curr (word_mul bytes_in_word (word (heap_length heap1))))
           (list_to_BlockReps c rt (heap_length heap1) (CONS x xs)) c` ASSUME_TAC THENL
        [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `word_addr c rt = (h:A word_loc)`)) THEN
         MATCH_MP_TAC append_writes_list_to_BlockReps THEN ASM_REWRITE_TAC[] THEN
         REPEAT CONJ_TAC THENL
          [UNDISCH_TAC `LENGTH (CONS (x:(A word_loc)heap_address) xs) = LENGTH (in1:data_v list)` THEN
           UNDISCH_TAC `LENGTH (in1:data_v list) = LENGTH (CONS (w:A word_loc) ws')` THEN
           REWRITE_TAC[LENGTH] THEN ARITH_TAC;
           ASM_ARITH_TAC;
           UNDISCH_TAC `wl_Word (init_ptr:A word) = make_cons_ptr c (word_sub (word_add curr
              (word_mul bytes_in_word (word (heap_length (heap1:mp7heap))))) curr) 0 2` THEN
           REWRITE_TAC[WORD_RULE `word_sub (word_add (x:A word) y) x = y`]];
         ALL_TAC] THEN
     MATCH_MP_TAC MP7AUX_append_sep THEN
       EXISTS_TAC `append_writes c init_ptr (make_header c (word 0) 2) (CONS w ws') (h:A word_loc)` THEN
       ASM_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[append_writes_LENGTH; NOT_CONS_NIL] THEN
       UNDISCH_TAC `LENGTH (CONS (x:(A word_loc)heap_address) xs) = LENGTH (in1:data_v list)` THEN
       UNDISCH_TAC `LENGTH (in1:data_v list) = LENGTH (CONS (w:A word_loc) ws')` THEN
       REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC;
    CONJ_TAC THENL
     [EXISTS_TAC `CONS (Pointer (heap_length (heap1:mp7heap)) (wl_Word (ptr_bits c cons_tag 2:A word)))
                     roots2` THEN
       ASM_REWRITE_TAC[ALL2; word_addr_def] THEN
       UNDISCH_TAC `wl_Word (init_ptr:A word) = make_cons_ptr c (word_sub (word_add curr
              (word_mul bytes_in_word (word (heap_length (heap1:mp7heap))))) curr) 0 2` THEN
       ASM_SIMP_TAC[WORD_RULE `word_sub (word_add (x:A word) y) x = y`;
                    MP7AUX_make_cons_ptr_get_addr; cons_tag_def];
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC]]]);;

(* HOL4 line 17360: walk *)
let data_to_word_memoryProof_walk_def = cake_def_wf
  `measure (\p:data_to_word_config#
               ((A word_loc,data_to_word_memoryProof_tag#B list)heap_element)list#
               num#num. SND (SND (SND p)))`
  TERM_TAC
  `data_to_word_memoryProof_walk conf
     (heap:((A word_loc,data_to_word_memoryProof_tag#B list)heap_element)list)
     ptr n =
     if n = 0 then []
     else if n = 1 then [ptr] else
       match some p. ?x y.
               heap_lookup ptr heap = SOME (BlockRep cons_tag [x; y]) /\
               y = Pointer p (wl_Word (ptr_bits conf cons_tag 2)) with
         NONE -> []
       | SOME p -> CONS ptr (data_to_word_memoryProof_walk conf heap p (n - 1))`;;
let data_to_word_memoryProof_walk_ind = cake_ind "data_to_word_memoryProof_walk";;

(* dataProps v_to_list_SOME_CONS_IMP and v_to_list_SOME_NIL_IFF (dataProps.ml is in progress) *)
let MP7AUX_v_to_list_SOME_CONS_IMP = prove
 (`!v x xs. data_v_to_list v = SOME (CONS x xs) ==>
            ?ts ys. v = data_Block ts cons_tag [x; ys] /\ data_v_to_list ys = SOME xs`,
  MATCH_MP_TAC data_v_to_list_ind THEN REWRITE_TAC[data_v_to_list_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN CASES_ON `data_v_to_list bt` THEN
  ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11; injectivity "data_v"] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`ts:num`; `bt:data_v`] THEN ASM_REWRITE_TAC[]);;
let MP7AUX_v_to_list_SOME_NIL_IFF = prove
 (`!v. data_v_to_list v = SOME [] <=> ?ts. v = data_Block ts nil_tag []`,
  MATCH_MP_TAC data_v_to_list_ind THEN REWRITE_TAC[data_v_to_list_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL;
    injectivity "data_v"; distinctness "data_v"; CONS_11] THENL
   [MESON_TAC[];
    DISCH_TAC THEN CASES_ON `data_v_to_list bt` THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[option_DISTINCT; option_INJ; NOT_CONS_NIL]]);;

(* HOL4 line 17373 *)
let v_inv_v_to_list_lemma = prove
 (`!c v refs (y:(A word_loc)heap_address) f tf heap vs.
     v_inv c v refs (y,f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = []) ==>
     ?p ys. y = Pointer p (wl_Word (ptr_bits c cons_tag 2)) /\
            heap_lookup p heap = SOME (BlockRep cons_tag ys)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vs:data_v list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP7AUX_v_to_list_SOME_CONS_IMP) THEN
  UNDISCH_TAC `v = data_Block ts cons_tag [h; ys]` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `v_inv c (data_Block ts cons_tag [h; ys]) refs
                 (y:(A word_loc)heap_address,f,tf,heap)` THEN
  REWRITE_TAC[v_inv_def] THEN
  REWRITE_TAC[NOT_CONS_NIL; LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ptr:num`; `xs:((A word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* walk follows the tail pointer of a cons cell *)
let MP7AUX_walk_some = prove
 (`!c (heap:((A word_loc,data_to_word_memoryProof_tag#B list)heap_element)list) ptr x p.
     heap_lookup ptr heap =
       SOME (BlockRep cons_tag [x; Pointer p (wl_Word (ptr_bits c cons_tag 2))]) ==>
     (some p'. ?x y. heap_lookup ptr heap = SOME (BlockRep cons_tag [x; y]) /\
                     y = Pointer p' (wl_Word (ptr_bits c cons_tag 2))) = SOME p`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[some_def; option_INJ; BlockRep_def;
    injectivity "heap_element"; CONS_11; PAIR_EQ] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[option_INJ] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC[LENGTH] THEN MESON_TAC[injectivity "heap_address"];
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[LENGTH] THEN
    MESON_TAC[]]);;
let MP7AUX_walk_CONS = prove
 (`!c (heap:((A word_loc,data_to_word_memoryProof_tag#B list)heap_element)list) ptr x p n.
     heap_lookup ptr heap =
       SOME (BlockRep cons_tag [x; Pointer p (wl_Word (ptr_bits c cons_tag 2))]) /\
     2 <= n ==>
     data_to_word_memoryProof_walk c heap ptr n =
     CONS ptr (data_to_word_memoryProof_walk c heap p (n - 1))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [data_to_word_memoryProof_walk_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MP7AUX_walk_some th]) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 0) /\ ~(n = 1)`] THEN
  CASE_REWRITE_TAC[]);;
(* the first cons cell of a list value *)
let MP7AUX_v_inv_list_CONS = prove
 (`!c v refs ptr f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) h t.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME (CONS h t) ==>
     ?ts ys x1 x2. v = data_Block ts cons_tag [h; ys] /\ data_v_to_list ys = SOME t /\
                   heap_lookup ptr heap = SOME (BlockRep cons_tag [x1; x2]) /\
                   v_inv c h refs (x1,f,tf,heap) /\ v_inv c ys refs (x2,f,tf,heap) /\
                   FLOOKUP tf ts = SOME ptr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP7AUX_v_to_list_SOME_CONS_IMP) THEN
  UNDISCH_TAC `v = data_Block ts cons_tag [h; ys]` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `v_inv c (data_Block ts cons_tag [h; ys]) refs
                 (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,
                  heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list)` THEN
  REWRITE_TAC[v_inv_def; NOT_CONS_NIL; LIST_REL_CONS1; LIST_REL_NIL] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ts:num`; `ys:data_v`; `h':(A word_loc)heap_address`;
                        `h'':(A word_loc)heap_address`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "heap_address"]) THEN
  ASM_MESON_TAC[]);;
(* one step of walk along a list value of at least two elements *)
let MP7AUX_walk_step = prove
 (`!c v refs ptr f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) h t.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME (CONS h t) /\ ~(t = []) ==>
     ?ts ys x1 p ys'.
       v = data_Block ts cons_tag [h; ys] /\ data_v_to_list ys = SOME t /\
       heap_lookup ptr heap =
         SOME (BlockRep cons_tag [x1; Pointer p (wl_Word (ptr_bits c cons_tag 2))]) /\
       v_inv c h refs (x1,f,tf,heap) /\
       v_inv c ys refs (Pointer p (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
       heap_lookup p heap = SOME (BlockRep cons_tag ys') /\
       FLOOKUP tf ts = SOME ptr /\
       data_to_word_memoryProof_walk c heap ptr (LENGTH (CONS h t)) =
       CONS ptr (data_to_word_memoryProof_walk c heap p (LENGTH t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP7AUX_v_inv_list_CONS o
              CONJ (ASSUME `v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,
                  heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list)`)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `ys:data_v`; `refs:(data_v bvl_ref)spt`;
                 `x2:(A word_loc)heap_address`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`; `t:data_v list`] v_inv_v_to_list_lemma) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= LENGTH (CONS (h:data_v) t)` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH] THEN UNDISCH_TAC `~(t:data_v list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `heap_lookup ptr heap = SOME (BlockRep cons_tag [x1; x2]:
     (A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MP7AUX_walk_CONS (CONJ th
    (ASSUME `2 <= LENGTH (CONS (h:data_v) t)`))]) THEN
  REWRITE_TAC[LENGTH; SUC_SUB1] THEN
  MAP_EVERY EXISTS_TAC [`ts:num`; `ys:data_v`; `x1:(A word_loc)heap_address`; `p:num`;
                        `ys':((A word_loc)heap_address)list`] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 17385 (the unused bound variable ts of HOL4 is left out) *)
let walk_LENGTH = prove
 (`!c refs f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list).
   !vs ptr ps v.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = []) /\
     data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps
     ==>
     LENGTH ps = LENGTH vs`,
  REPLICATE_TAC 5 GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `h:data_v` `t:data_v list` THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_CASES_TAC `t:data_v list = []` THENL
   [ASM_REWRITE_TAC[LENGTH] THEN ONCE_REWRITE_TAC[data_to_word_memoryProof_walk_def] THEN
    REWRITE_TAC[ARITH; LENGTH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                 `ptr:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`; `h:data_v`; `t:data_v list`]
         MP7AUX_walk_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH; SUC_INJ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`p:num`; `ys:data_v`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 17407 *)
let BlockRep_heap_length = prove
 (`!tag (x:A heap_address) y.
     heap_length [BlockRep tag [x;y]:(A,data_to_word_memoryProof_tag#B list)
                                    heap_element] = 3`,
  REWRITE_TAC[heap_length_def; MAP; SUM; BlockRep_def; el_length_def; LENGTH] THEN
  ARITH_TAC);;
let _ = cake_add_simps [BlockRep_heap_length];;

(* HOL4 line 17413 *)
let ALL_DISTINCT_FILTER_LENGTH = prove
 (`!(P:A->bool) xs.
     ALL_DISTINCT xs
     ==>
     LENGTH (FILTER ((~) o P) xs) + LENGTH (FILTER P xs) = LENGTH xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; LENGTH; ALL_DISTINCT; o_THM; ADD_CLAUSES] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let MP7AUX_FILTER_EQ_LENGTH = prove
 (`!a (l:num list). ALL_DISTINCT l ==>
     LENGTH (FILTER (\p. p = a) l) = if MEM a l then 1 else 0`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH; MEM; ALL_DISTINCT] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `h:num = a` THEN ASM_REWRITE_TAC[LENGTH] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* HOL4 line 17421 *)
let heap_length_Blocks = prove
 (`!ps (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
              heap_element)list).
     ALL_DISTINCT ps /\
     ALL (\p. ?x y. heap_lookup p heap = SOME (BlockRep cons_tag [x;y])) ps
     ==>
     3 * LENGTH ps <= heap_length heap`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ALL; heap_lookup_def; option_DISTINCT] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `ps:num list` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `MAP (\p. p - el_length (h:mp7el)) (FILTER (\p. ~(p = 0)) ps)`) THEN
  SUBGOAL_THEN
   `!x. MEM x ps /\ ~(x = 0) ==>
        el_length (h:mp7el) <= x /\
        (?a b. heap_lookup (x - el_length h) (t:mp7heap) =
               SOME (BlockRep cons_tag [a;b]))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\p. ?x y. heap_lookup p (CONS h t) =
                                SOME (BlockRep cons_tag [x; y]:mp7el)) ps` THEN
    REWRITE_TAC[GSYM ALL_MEM; heap_lookup_def] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `x:num` THEN STRIP_TAC THEN MP_TAC(SPEC `x:num` th)) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    ASM_MESON_TAC[NOT_LT];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_SIMP_TAC[FILTER_ALL_DISTINCT; MEM_FILTER] THEN
      ASM_MESON_TAC[ARITH_RULE `e <= x /\ e <= y /\ x - e = y - e ==> x = y:num`];
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; MEM_FILTER] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_MAP; GC1AUX_heap_length_CONS] THEN
  MP_TAC(ISPECL [`\p:num. p = 0`; `ps:num list`] ALL_DISTINCT_FILTER_LENGTH) THEN
  MP_TAC(ISPECL [`0`; `ps:num list`] MP7AUX_FILTER_EQ_LENGTH) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  ASM_CASES_TAC `MEM 0 ps` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `el_length (h:mp7el) = 3` (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
    UNDISCH_TAC `ALL (\p. ?x y. heap_lookup p (CONS h t) =
                                SOME (BlockRep cons_tag [x; y]:mp7el)) ps` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[heap_lookup_def; option_INJ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[BlockRep_def; el_length_def; LENGTH] THEN ARITH_TAC;
    ARITH_TAC]);;

(* walk from the first cons cell starts with its address *)
let MP7AUX_walk_HD = prove
 (`!c v refs ptr f tf (heap:mp7heap) vs.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME vs /\ ~(vs = []) ==>
     ?rest. data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = CONS ptr rest`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vs:data_v list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:data_v list = []` THENL
   [ASM_REWRITE_TAC[LENGTH] THEN ONCE_REWRITE_TAC[data_to_word_memoryProof_walk_def] THEN
    REWRITE_TAC[ARITH; CONS_11] THEN MESON_TAC[];
    MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                   `ptr:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                   `h:data_v`; `t:data_v list`] MP7AUX_walk_step) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[]]);;

(* HOL4 line 17470 (the unused bound variable ts of HOL4 is left out) *)
let walk_heap_lookup = prove
 (`!c refs f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list).
   !vs p ps v.
     v_inv c v refs (Pointer p (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = []) /\
     data_to_word_memoryProof_walk c heap p (LENGTH vs) = ps
     ==>
     ALL (\p. ?x y. heap_lookup p heap = SOME (BlockRep cons_tag [x; y])) ps`,
  REPLICATE_TAC 5 GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `h:data_v` `t:data_v list` THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_CASES_TAC `t:data_v list = []` THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                   `p:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                   `h:data_v`; `t:data_v list`] MP7AUX_v_inv_list_CONS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LENGTH] THEN ONCE_REWRITE_TAC[data_to_word_memoryProof_walk_def] THEN
    REWRITE_TAC[ARITH; ALL] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                   `p:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                   `h:data_v`; `t:data_v list`] MP7AUX_walk_step) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`p':num`; `ys:data_v`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 17495 *)
let walk_MEM = prove
 (`!c v refs ptr f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) vs.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = [])
     ==>
     MEM ptr (data_to_word_memoryProof_walk c heap ptr (LENGTH vs))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                 `ptr:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                 `vs:data_v list`] MP7AUX_walk_HD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MEM]);;

(* HOL4 line 17520 (the unused bound variable ts of HOL4 is left out) *)
let walk_EL = prove
 (`!c refs f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list).
   !vs ptr ps v.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = []) /\
     data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps
     ==>
     !n. SUC n < LENGTH vs ==>
         ?x. heap_lookup (EL n ps) heap =
             SOME (BlockRep cons_tag
                     [x; Pointer (EL (SUC n) ps) (wl_Word (ptr_bits c cons_tag 2))])`,
  REPLICATE_TAC 5 GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `h:data_v` `t:data_v list` THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (t:data_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `SUC n < LENGTH (CONS (h:data_v) t)` THEN REWRITE_TAC[LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:data_v list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `n < LENGTH (t:data_v list)` THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                 `ptr:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                 `h:data_v`; `t:data_v list`] MP7AUX_walk_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `ys:data_v`; `refs:(data_v bvl_ref)spt`;
                 `p:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                 `t:data_v list`] MP7AUX_walk_HD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CASES_ON `n:num` THEN ASM_REWRITE_TAC[EL; HD; TL] THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `CONS (p:num) rest`; `ys:data_v`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n':num`) THEN
    ASM_REWRITE_TAC[EL; TL]]);;

(* HOL4 line 17557 (the unused bound variables ts1 ts2 of HOL4 are left out) *)
let v_to_list_same_LENGTH = prove
 (`!c refs f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list).
   !xs x ys v1 v2.
     v_inv c v1 refs (x,f,tf,heap) /\
     v_inv c v2 refs (x,f,tf,heap) /\
     data_v_to_list v1 = SOME xs /\
     data_v_to_list v2 = SOME ys
     ==>
     LENGTH xs = LENGTH ys`,
  REPLICATE_TAC 5 GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `h:data_v` `t:data_v list` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [CASES_ON `ys:data_v list` THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `v2:data_v`; `refs:(data_v bvl_ref)spt`;
                   `x:(A word_loc)heap_address`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                   `heap:mp7heap`; `CONS (a0:data_v) a1`] v_inv_v_to_list_lemma) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
    UNDISCH_TAC `data_v_to_list v1 = SOME []` THEN
    REWRITE_TAC[MP7AUX_v_to_list_SOME_NIL_IFF] THEN STRIP_TAC THEN
    UNDISCH_TAC `v_inv c v1 refs (x:(A word_loc)heap_address,f,tf,heap)` THEN
    ASM_REWRITE_TAC[v_inv_def; distinctness "heap_address"];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v1:data_v`; `refs:(data_v bvl_ref)spt`;
                 `x:(A word_loc)heap_address`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:mp7heap`; `CONS (h:data_v) t`] v_inv_v_to_list_lemma) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
  UNDISCH_TAC `x = Pointer p (wl_Word (ptr_bits c cons_tag 2)):(A word_loc)heap_address` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  CASES_ON `ys:data_v list` THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ] THENL
   [UNDISCH_TAC `data_v_to_list v2 = SOME []` THEN
    REWRITE_TAC[MP7AUX_v_to_list_SOME_NIL_IFF] THEN STRIP_TAC THEN
    UNDISCH_TAC `v_inv c v2 refs (Pointer p (wl_Word (ptr_bits c cons_tag 2)):
                   (A word_loc)heap_address,f,tf,heap)` THEN
    ASM_REWRITE_TAC[v_inv_def; distinctness "heap_address"];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v1:data_v`; `refs:(data_v bvl_ref)spt`;
                 `p:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                 `h:data_v`; `t:data_v list`] MP7AUX_v_inv_list_CONS) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v2:data_v`; `refs:(data_v bvl_ref)spt`;
                 `p:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                 `a0:data_v`; `a1:data_v list`] MP7AUX_v_inv_list_CONS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; BlockRep_def; injectivity "heap_element";
                              CONS_11]) THEN
  MAP_EVERY EXISTS_TAC [`x2:(A word_loc)heap_address`; `ys''':data_v`; `ys'':data_v`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CONS_11]);;

(* HOL4 line 17584 *)
let block_drop_def = cake_def
  `(block_drop 0 (v:data_v) = SOME v) /\
   (block_drop (SUC n) (data_Block ts tag [h;vl]) = block_drop n vl) /\
   (block_drop _ _ = NONE)`;;
let block_drop_ind = cake_ind "block_drop";;

(* HOL4 line 17590 (the unused bound variable ts of HOL4 is left out) *)
let v_to_list_DROP = prove
 (`!c refs f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list).
   !vs ptr ps k v.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = []) /\
     data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps /\
     ALL_DISTINCT ps /\
     k < LENGTH vs
     ==>
     v_inv c (THE (block_drop k v)) refs
       (Pointer (EL k ps) (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap)`,
  REPLICATE_TAC 5 GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `h:data_v` `t:data_v list` THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_comb(lhs(concl th)) && fst(strip_comb(lhs(concl th))) =
    `data_to_word_memoryProof_walk:data_to_word_config->mp7heap->num->num->num list`)) THEN
  CASES_ON `k:num` THENL
   [MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                   `ptr:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                   `CONS (h:data_v) t`] MP7AUX_walk_HD) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[EL; HD; block_drop_def; THE_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (t:data_v list)` ASSUME_TAC THENL
   [UNDISCH_TAC `SUC n < LENGTH (CONS (h:data_v) t)` THEN REWRITE_TAC[LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:data_v list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `n < LENGTH (t:data_v list)` THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                 `ptr:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                 `h:data_v`; `t:data_v list`] MP7AUX_walk_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ALL_DISTINCT (data_to_word_memoryProof_walk c (heap:mp7heap) ptr
                               (LENGTH (CONS (h:data_v) t)))` THEN
  ASM_REWRITE_TAC[EL; TL; block_drop_def; ALL_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 17651 *)
let block_drop_DROP = prove
 (`!n v vs. data_v_to_list v = SOME vs /\ n < LENGTH vs
            ==> data_v_to_list (THE (block_drop n v)) = SOME (DROP n vs)`,
  INDUCT_TAC THEN REWRITE_TAC[block_drop_def; THE_DEF; DROP_0] THEN
  REPEAT GEN_TAC THEN CASES_ON `vs:data_v list` THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP7AUX_v_to_list_SOME_CONS_IMP) THEN
  ASM_REWRITE_TAC[block_drop_def; DROP_DEF; NOT_SUC; SUC_SUB1] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `SUC n < SUC (LENGTH (a1:data_v list))` THEN ARITH_TAC);;

(* HOL4 line 17661 (the unused bound variable ts of HOL4 is left out) *)
let walk_ALL_DISTINCT = prove
 (`!c refs f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list).
   !vs ptr ps v.
     v_inv c v refs (Pointer ptr (wl_Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = []) /\
     data_to_word_memoryProof_walk c heap ptr (LENGTH vs) = ps
     ==>
     ALL_DISTINCT ps`,
  REPLICATE_TAC 5 GEN_TAC THEN MP7AUX_LIST_INDUCT_TAC `h:data_v` `t:data_v list` THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_CASES_TAC `t:data_v list = []` THENL
   [ASM_REWRITE_TAC[LENGTH] THEN ONCE_REWRITE_TAC[data_to_word_memoryProof_walk_def] THEN
    REWRITE_TAC[ARITH; ALL_DISTINCT; MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                 `ptr:num`; `f:(num,num)fmap`; `tf:(num,num)fmap`; `heap:mp7heap`;
                 `h:data_v`; `t:data_v list`] MP7AUX_walk_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT] THEN
  SUBGOAL_THEN `ALL_DISTINCT (data_to_word_memoryProof_walk c (heap:mp7heap) p
                                (LENGTH (t:data_v list)))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`p:num`; `ys:data_v`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
                 `tf:(num,num)fmap`; `heap:mp7heap`; `t:data_v list`; `p:num`;
                 `data_to_word_memoryProof_walk c (heap:mp7heap) p
                    (LENGTH (t:data_v list))`;
                 `ys:data_v`] walk_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
                 `tf:(num,num)fmap`; `heap:mp7heap`; `t:data_v list`; `p:num`;
                 `data_to_word_memoryProof_walk c (heap:mp7heap) p
                    (LENGTH (t:data_v list))`;
                 `i:num`; `ys:data_v`] v_to_list_DROP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
                                                    lhs(concl th) = `ptr:num`)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`i:num`; `ys:data_v`; `t:data_v list`] block_drop_DROP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
                 `tf:(num,num)fmap`; `heap:mp7heap`; `CONS (h:data_v) t`;
                 `Pointer ptr (wl_Word (ptr_bits c cons_tag 2)):(A word_loc)heap_address`;
                 `DROP i (t:data_v list)`; `v:data_v`; `THE (block_drop i ys)`]
         v_to_list_same_LENGTH) THEN
  ASM_REWRITE_TAC[LENGTH; LENGTH_DROP] THEN ARITH_TAC);;

(* HOL4 line 17709 *)
let v_to_list_heap_length = prove
 (`!c v refs (x:(A word_loc)heap_address) f tf heap vs.
     v_inv c v refs (x,f,tf,heap) /\
     data_v_to_list v = SOME vs /\
     ~(vs = [])
     ==>
     3 * LENGTH vs <= heap_length heap`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `v:data_v`; `refs:(data_v bvl_ref)spt`;
                 `x:(A word_loc)heap_address`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:mp7heap`; `vs:data_v list`] v_inv_v_to_list_lemma) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `v_inv c v refs (x:(A word_loc)heap_address,f,tf,heap)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
                 `tf:(num,num)fmap`; `heap:mp7heap`; `vs:data_v list`; `p:num`;
                 `data_to_word_memoryProof_walk c (heap:mp7heap) p (LENGTH (vs:data_v list))`;
                 `v:data_v`] walk_LENGTH) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
                 `tf:(num,num)fmap`; `heap:mp7heap`; `vs:data_v list`; `p:num`;
                 `data_to_word_memoryProof_walk c (heap:mp7heap) p (LENGTH (vs:data_v list))`;
                 `v:data_v`] walk_ALL_DISTINCT) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
                 `tf:(num,num)fmap`; `heap:mp7heap`; `vs:data_v list`; `p:num`;
                 `data_to_word_memoryProof_walk c (heap:mp7heap) p (LENGTH (vs:data_v list))`;
                 `v:data_v`] walk_heap_lookup) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC heap_length_Blocks THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 17722 *)
let memory_rel_list_limit = prove
 (`!c be ts refs sp0 st (m:A word -> A word_loc) dm v w vars xs.
     memory_rel c be ts refs sp0 st m dm (CONS (v,(w:A word_loc)) vars) /\
     data_v_to_list v = SOME xs /\
     good_dimindex (:A)
     ==>
     3 * (LENGTH xs + 1) * (dimindex (:A) DIV 8) < dimword (:A)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def;
              heap_in_memory_store_def; MAP; LIST_REL_CONS1] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `3 * LENGTH (xs:data_v list) <= heap_length (heap:mp7heap)` ASSUME_TAC THENL
   [ASM_CASES_TAC `xs:data_v list = []` THEN ASM_REWRITE_TAC[LENGTH; MULT_CLAUSES; LE_0] THEN
    MATCH_MP_TAC v_to_list_heap_length THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `(heap_length (heap:mp7heap) + 3) * (dimindex(:A) DIV 8)` THEN
  ASM_REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 17735 *)
let build_part_words_def = cake_def
  `(build_part_words c (m:num->A word_loc) (clos_Int i) (offset:A word) =
      if small_int (:A) i then SOME (wl_Word (Smallnum i),[])
      else let (sign,ws) = (i2mw i:bool#(A word)list) in
           match encode_header c
                   (val (word_or (word_shl (b2w sign) 2) (word 3):A word))
                   (LENGTH ws) with
             NONE -> NONE
           | SOME hd -> SOME (make_ptr c offset (word 0:A word) (LENGTH ws),
                              MAP wl_Word (CONS hd ws))) /\
   (build_part_words c m (clos_Con t ns) offset =
      if NULL ns then
        if t < dimword (:A) DIV 16 then SOME (wl_Word (word (16 * t + 2)),[])
        else NONE
      else
        match encode_header c (4 * t) (LENGTH ns) with
          NONE -> NONE
        | SOME hd -> SOME (make_cons_ptr c offset t (LENGTH ns),
                           CONS (wl_Word hd) (MAP m ns))) /\
   (build_part_words c m (clos_W64 w) offset =
      let ws = (if dimindex (:A) < 64
                then [word_extract 63 32 w; word_extract 31 0 w]
                else [word_extract 63 0 w:A word]) in
      match encode_header c 3 (LENGTH ws) with
        NONE -> NONE
      | SOME hd -> SOME (make_ptr c offset (word 0:A word) (LENGTH ws),
                         MAP wl_Word (CONS hd ws))) /\
   (build_part_words c m (clos_Str s) offset =
      let bytes = MAP (word o ORD) (explode s) in
      let n = LENGTH bytes in
      let hd = make_byte_header c T n in
      let ws = write_bytes bytes (REPLICATE (byte_len (:A) n) (word 0))
                 (data_to_word_config_be c) in
      if byte_len (:A) n < 2 EXP (dimindex (:A) - 4) /\
         byte_len (:A) n < 2 EXP data_to_word_config_len_size c
      then SOME (make_ptr c offset (word 0:A word) (byte_len (:A) n),
                 MAP wl_Word (CONS hd ws))
      else NONE)`;;

(* HOL4 line 17770 *)
let build_words_def = cake_def
  `(build_words c (m:num->A word_loc) i [] (off:A word) = SOME (m (i - 1), [])) /\
   (build_words c m i (CONS x parts) off =
      match build_part_words c m x off with
        NONE -> NONE
      | SOME (w,xs) ->
          match build_words c ((i =+ w) m) (i + 1) parts
                  (word_add off (word_mul bytes_in_word (word (LENGTH xs)))) with
            NONE -> NONE
          | SOME (r,ys) -> SOME (r,APPEND xs ys))`;;
let build_words_ind = cake_ind "build_words";;

(* HOL4 line 17781 *)
let do_part_SOME_IMP_SOME = prove
 (`!map0 h (refs:(A bvl_ref)spt) ts x s1 ts1.
     data_do_part map0 h refs (SOME ts) = (x,s1,ts1) ==> ?ts'. ts1 = SOME ts'`,
  REPEAT GEN_TAC THEN CASES_ON `h:const_part` THEN
  REWRITE_TAC[data_do_part_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 17787 *)
let memory_rel_IMP_MAP_UPDATE = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm b w map0 map0' (ks:B list) vars i.
     memory_rel c be ts refs sp st m dm
       (APPEND (CONS (b,w) (MAP (\k. (map0 k,map0' k)) ks)) vars) ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (MAP (\k. ((i =+ b) map0 k,(i =+ w) map0' k)) ks) vars)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM; MEM_MAP; APPLY_UPDATE_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 17797: ZIP_MAP_MAP *)
let data_to_word_memoryProof_ZIP_MAP_MAP = prove
 (`!(f:A->B) (g:A->C) xs. ZIP (MAP f xs) (MAP g xs) = MAP (\k. (f k,g k)) xs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP; HD; TL]);;

let MP7AUX_DIMWORD_32 = prove
 (`good_dimindex(:A) ==> 2 EXP 32 <= dimword(:A)`,
  REWRITE_TAC[good_dimindex_def; dimword_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 17803 *)
let LENGTH_n2mw_LE_num_size = prove
 (`!n m. good_dimindex (:A) /\ n <= m ==>
         SUC (LENGTH (n2mw n:(A word)list)) <= num_size m`,
  MATCH_MP_TAC (INST_TYPE [`:A`,`:N`] n2mw_ind) THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THENL
   [ONCE_REWRITE_TAC[num_size_def] THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[num_size_def] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `n DIV dimword(:A) = 0` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`n:num`; `dimword(:A)`] DIV_EQ_0) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
      ANTS_TAC THENL [POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
                      ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
      UNDISCH_TAC `m < 2 EXP 32` THEN UNDISCH_TAC `n <= m:num` THEN ARITH_TAC;
      ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `m DIV 2 EXP 32` o C MP (ASSUME `~(n = 0)`)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n DIV 2 EXP 32` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIV_thm1 THEN ASM_SIMP_TAC[MP7AUX_DIMWORD_32] THEN
        CONV_TAC NUM_REDUCE_CONV;
        MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[]];
      ARITH_TAC]]);;

(* HOL4 line 17820 *)
let least_notin_domain = prove
 (`!refs:A spt. ~((minimal ptr. ~(ptr IN domain refs)) IN domain refs)`,
  GEN_TAC THEN
  SUBGOAL_THEN `?ptr. ~(ptr IN domain (refs:A spt))` MP_TAC THENL
   [MP_TAC(INST [`refs:A spt`,`t:A spt`] FINITE_domain) THEN REWRITE_TAC[num_FINITE] THEN
    MESON_TAC[ARITH_RULE `~(a + 1 <= a)`];
    REWRITE_TAC[MINIMAL] THEN MESON_TAC[]]);;

let MP7AUX_FUPDATE_FLOOKUP = prove
 (`!(f:(A,B)fmap) k v. FLOOKUP f k = SOME v ==> f |+ (k,v) = f`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE] THEN MESON_TAC[]);;
(* a store_list result that does not depend on ks *)
let MP7AUX_FORALL_KS = prove
 (`!(o1:B option) (P:(C list)->B->bool).
     (!ks. ?m1. o1 = SOME m1 /\ P ks m1) ==> ?m'. o1 = SOME m' /\ !ks. P ks m'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `m':B` STRIP_ASSUME_TAC o SPEC `[]:C list`) THEN
  EXISTS_TAC `m':B` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `ks:C list` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m1:B` STRIP_ASSUME_TAC o SPEC `ks:C list`) THEN
  UNDISCH_TAC `o1 = SOME (m1:B)` THEN ASM_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;
let MP7AUX_BlockNil = prove
 (`!n. BlockNil n:A word = word (16 * n + 2)`,
  REWRITE_TAC[BlockNil_def; WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; WORD_MUL] THEN CONV_TAC WORD_RULE);;
(* one part of memory_rel_do_build *)
let MP7AUX_do_build_part = prove
 (`!c be dm vars x (map0:num->data_v) (map0':num->A word_loc) refs ts x' s1 ts' w' xs
    st free curr sp m.
   data_do_part map0 x refs (SOME ts) = (x',s1,SOME ts') /\
   build_part_words c map0' x (word_sub free curr) = SOME (w',xs) /\
   part_space_req x <= sp /\
   FLOOKUP st NextFree = SOME (wl_Word free) /\
   FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
   (!ks. memory_rel c be ts refs sp st m dm
           (APPEND (MAP (\k. (map0 k,map0' k)) ks) vars)) /\
   good_dimindex(:A) ==>
   LENGTH xs <= part_space_req x /\
   ?m'. data_to_word_memoryProof_store_list free xs m dm = SOME m' /\
        !ks. memory_rel c be ts' s1 (sp - LENGTH xs)
               (st |+ (NextFree,wl_Word (word_add free
                                           (word_mul bytes_in_word (word (LENGTH xs))))))
               m' dm (CONS (x',w') (APPEND (MAP (\k. (map0 k,map0' k)) ks) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN MATCH_MP_TAC(TAUT `a /\ b ==> a /\ b`) THEN
  CASES_ON `x:const_part` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[data_do_part_def; build_part_words_def; LET_DEF;
                              LET_END_DEF; part_space_req_def]) THENL
 [(GVS(NULL_EQ :: LENGTH_EQ_NIL :: all_case_eqs()) THENL
  [EXISTS_TAC `m:A word->A word_loc` THEN
  ASM_SIMP_TAC[data_to_word_memoryProof_store_list_def; WORD_MUL_0; WORD_ADD_0;
               MP7AUX_FUPDATE_FLOOKUP] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM MP7AUX_BlockNil] THEN
  MATCH_MP_TAC memory_rel_Cons_empty THEN ASM_REWRITE_TAC[];
   CONJ_TAC THENL
   [REWRITE_TAC[part_space_req_def; LET_DEF; LET_END_DEF; LENGTH_EQ_NIL] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MP7AUX_FORALL_KS THEN X_GEN_TAC `ks:num list` THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `s1:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `MAP (map0:num->data_v) a1`; `MAP (map0':num->A word_loc) a1`;
    `APPEND (MAP (\k. ((map0:num->data_v) k,(map0':num->A word_loc) k)) ks) vars`;
    `a0:num`; `a:A word`] memory_rel_Cons1) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; MAP_EQ_NIL] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `APPEND (a1:num list) ks`) THEN
      REWRITE_TAC[MAP_APPEND; APPEND_ASSOC; data_to_word_memoryProof_ZIP_MAP_MAP];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"; LET_DEF; LET_END_DEF; LENGTH_MAP;
                  ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `free':A word` (X_CHOOSE_THEN `curr':A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `m1:A word->A word_loc` THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["free'";"curr'"]))) THEN
  ASM_REWRITE_TAC[]]);
  (GVS(NULL_EQ :: LENGTH_EQ_NIL :: all_case_eqs()) THEN REPEAT PAIRARG_TAC THEN
  GVS(all_case_eqs()) THENL
  [EXISTS_TAC `m:A word->A word_loc` THEN
  ASM_SIMP_TAC[data_to_word_memoryProof_store_list_def; WORD_MUL_0; WORD_ADD_0;
               MP7AUX_FUPDATE_FLOOKUP] THEN
  GEN_TAC THEN MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `SUC (LENGTH (y:(A word)list)) <= part_space_req (clos_Int a)` ASSUME_TAC THENL
   [SUBGOAL_THEN `y = n2mw (num_of_int (abs a)):(A word)list` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `i2mw a = x,(y:(A word)list)` THEN REWRITE_TAC[i2mw_def; PAIR_EQ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[part_space_req_def] THEN
    SUBGOAL_THEN `~(num_of_int (abs a) < 2 EXP 29)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `~small_int (:A) a` THEN REWRITE_TAC[small_int_def] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
      SUBGOAL_THEN `536870912 <= dimword(:A) DIV 8` MP_TAC THENL
       [MP_TAC(SPECL [`2 EXP 32`; `dimword(:A)`; `8`] DIV_MONO) THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT] THEN
      MP_TAC(SPEC `abs(a:int)` INT_OF_NUM_OF_INT) THEN REWRITE_TAC[INT_ABS_POS] THEN
      DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LENGTH_n2mw_LE_num_size THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
   CONJ_TAC THENL [UNDISCH_TAC `SUC (LENGTH (y:(A word)list)) <= part_space_req (clos_Int a)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (y:(A word)list) < sp` ASSUME_TAC THENL
   [UNDISCH_TAC `SUC (LENGTH (y:(A word)list)) <= part_space_req (clos_Int a)` THEN
    UNDISCH_TAC `(if num_of_int (abs a) < 536870912 then 0
                  else num_size (num_of_int (abs a))) <= sp` THEN
    REWRITE_TAC[part_space_req_def] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MP7AUX_FORALL_KS THEN X_GEN_TAC `ks:num list` THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts':num`; `s1:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `APPEND (MAP (\k. ((map0:num->data_v) k,(map0':num->A word_loc) k)) ks) vars`;
    `a:int`; `y:(A word)list`; `x:bool`; `a:A word`] IMP_memory_rel_bignum_alt) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[data_to_word_memoryProof_Bignum_def; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"; MAP; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `free':A word` (X_CHOOSE_THEN `curr':A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `m1:A word->A word_loc` THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["free'";"curr'"]))) THEN
  ASM_REWRITE_TAC[]]);
  (GVS(NULL_EQ :: LENGTH_EQ_NIL :: all_case_eqs()) THEN
  SUBGOAL_THEN `byte_len (:A) (strlen a) < strlen a DIV 4 + 2` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; byte_len_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPECL [`strlen a`; `4`; `8`] DIV_thm1) THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[part_space_req_def]; ALL_TAC] THEN
  SUBGOAL_THEN `data_to_word_config_be c = be` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list` o check (is_forall o concl)) THEN
    REWRITE_TAC[memory_rel_def; word_ml_inv_def; abs_ml_inv_def; bc_stack_ref_inv_def;
                be_ok_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MP7AUX_FORALL_KS THEN X_GEN_TAC `ks:num list` THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts':num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `APPEND (MAP (\k. ((map0:num->data_v) k,(map0':num->A word_loc) k)) ks) vars`;
    `minimal ptr. ~(ptr IN domain (refs:(data_v bvl_ref)spt))`; `strlen a`;
    `MAP (word o ORD) (explode a):byte list`; `T`] memory_rel_RefByte_content) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[least_notin_domain; LENGTH_MAP; LENGTH_explode] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"; LET_DEF; LET_END_DEF; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `free':A word` (X_CHOOSE_THEN `curr':A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `m1:A word->A word_loc` THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["free'";"curr'"]))) THEN
  ASM_REWRITE_TAC[WORD_ADD_ASSOC; GSYM WORD_ADD]);
  (GVS(NULL_EQ :: LENGTH_EQ_NIL :: all_case_eqs()) THEN
  ABBREV_TAC `wsr = if dimindex (:A) < 64
                    then [word_extract 63 32 (a:int64); word_extract 31 0 a]
                    else [word_extract 63 0 a:A word]` THEN
  SUBGOAL_THEN `LENGTH (wsr:(A word)list) <= 2` ASSUME_TAC THENL
   [EXPAND_TAC "wsr" THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[part_space_req_def; LENGTH_MAP; LENGTH] THEN
    UNDISCH_TAC `LENGTH (wsr:(A word)list) <= 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MP7AUX_FORALL_KS THEN X_GEN_TAC `ks:num list` THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts':num`; `s1:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `[]:(data_v#A word_loc)list`;
    `APPEND (MAP (\k. ((map0:num->data_v) k,(map0':num->A word_loc) k)) ks) vars`;
    `a:int64`; `MAP wl_Word (wsr:(A word)list)`; `a:A word`] memory_rel_Word64_alt) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APPEND; LENGTH_MAP; Word64Rep_def] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "wsr" THEN COND_CASES_TAC THEN REWRITE_TAC[MAP; LENGTH] THEN
      CONV_TAC NUM_REDUCE_CONV;
      UNDISCH_TAC `LENGTH (wsr:(A word)list) <= 2` THEN UNDISCH_TAC `3 <= sp` THEN
      ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"; LET_DEF; LET_END_DEF; ADD1;
                  LENGTH_MAP; MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `free':A word` (X_CHOOSE_THEN `curr':A word`
    (X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `m1:A word->A word_loc` THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["free'";"curr'"]))) THEN
  ASM_REWRITE_TAC[])]);;

(* HOL4 line 17836 (HOL4 quantifies v twice; ts1, w, c, be, dm, vars are   *)
(* free in HOL4)                                                            *)
let memory_rel_do_build = prove
 (`!c be dm vars ts1 w.
   !parts i st free (curr:A word) sp map0 map0' refs ts refs1 m v ws.
     data_do_build map0 i parts refs (SOME ts) = (v,refs1,SOME ts1) /\
     build_words c map0' i parts (word_sub free curr:A word) = SOME (w,ws) /\
     SUM (MAP part_space_req parts) <= sp /\
     FLOOKUP st NextFree = SOME (wl_Word free) /\
     FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
     (!ks. memory_rel c be ts refs sp st m dm
             (APPEND (MAP (\k. (map0 k,map0' k)) ks) vars)) /\
     good_dimindex (:A) ==>
     ?m1.
       let nf = word_add free (word_mul bytes_in_word (word (LENGTH ws))) in
       memory_rel c be ts1 refs1 (sp - LENGTH ws)
         (st |+ (NextFree,wl_Word nf)) m1 dm (CONS (v,w) vars) /\
       data_to_word_memoryProof_store_list free ws m dm = SOME m1`,
  REPLICATE_TAC 6 GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[data_do_build_def; build_words_def; PAIR_EQ; option_INJ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
           (is_var(rhs(concl th)) || is_comb(rhs(concl th)) && is_var(rand(rhs(concl th))))))) THEN
    EXISTS_TAC `m:A word->A word_loc` THEN
    ASM_SIMP_TAC[LENGTH; SUB_0; WORD_MUL_0; WORD_ADD_0; MP7AUX_FUPDATE_FLOOKUP;
                 data_to_word_memoryProof_store_list_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[i - 1]`) THEN REWRITE_TAC[MAP; APPEND];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `st:(store_name,A word_loc)fmap`; `free:A word`;
    `curr:A word`; `sp:num`; `map0:num->data_v`; `map0':num->A word_loc`;
    `refs:(data_v bvl_ref)spt`; `ts:num`; `refs1:(data_v bvl_ref)spt`;
    `m:A word->A word_loc`; `v:data_v`; `ws:(A word_loc)list`] THEN
  REWRITE_TAC[data_do_build_def; build_words_def] THEN
  SUBGOAL_THEN `?x1 (s1:(data_v bvl_ref)spt) t1.
                  data_do_part map0 h (refs:(data_v bvl_ref)spt) (SOME ts) = (x1,s1,t1)`
    (X_CHOOSE_THEN `x1:data_v` (X_CHOOSE_THEN `s1:(data_v bvl_ref)spt`
      (X_CHOOSE_THEN `t1:num option` ASSUME_TAC))) THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ts':num` SUBST_ALL_TAC o MATCH_MP do_part_SOME_IMP_SOME) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC(all_case_eqs()) THEN REWRITE_TAC[PAIR_EQ; option_INJ; option_DISTINCT] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     is_var(lhs(concl th)) && mem (fst(dest_var(lhs(concl th)))) ["a";"a'";"x'"]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
     rhs(concl th) = `ws:(A word_loc)list`)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `dm:A word->bool`;
    `vars:(data_v#A word_loc)list`; `h:const_part`; `map0:num->data_v`;
    `map0':num->A word_loc`; `refs:(data_v bvl_ref)spt`; `ts:num`; `x1:data_v`;
    `s1:(data_v bvl_ref)spt`; `ts':num`; `x:A word_loc`; `y:(A word_loc)list`;
    `st:(store_name,A word_loc)fmap`; `free:A word`; `curr:A word`; `sp:num`;
    `m:A word->A word_loc`] MP7AUX_do_build_part) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `SUM (MAP part_space_req (CONS h t)) <= sp` THEN
    REWRITE_TAC[MAP; SUM] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m':A word->A word_loc`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i + 1`;
    `(st:(store_name,A word_loc)fmap) |+ (NextFree,wl_Word (word_add free
        (word_mul bytes_in_word (word (LENGTH (y:(A word_loc)list))))))`;
    `word_add free (word_mul bytes_in_word (word (LENGTH (y:(A word_loc)list)))):A word`;
    `curr:A word`; `sp - LENGTH (y:(A word_loc)list)`; `(i =+ x1) (map0:num->data_v)`;
    `(i =+ x) (map0':num->A word_loc)`; `s1:(data_v bvl_ref)spt`; `ts':num`;
    `refs1:(data_v bvl_ref)spt`; `m':A word->A word_loc`; `v:data_v`;
    `y':(A word_loc)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_UPDATE; distinctness "store_name"] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `word_sub (word_add free (word_mul bytes_in_word
                       (word (LENGTH (y:(A word_loc)list))))) curr =
                     word_add (word_sub free curr) (word_mul bytes_in_word
                       (word (LENGTH y))):A word` SUBST1_TAC THENL
       [CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]];
      UNDISCH_TAC `SUM (MAP part_space_req (CONS h t)) <= sp` THEN
      REWRITE_TAC[MAP; SUM] THEN ASM_ARITH_TAC;
      GEN_TAC THEN MATCH_MP_TAC memory_rel_IMP_MAP_UPDATE THEN
      ASM_REWRITE_TAC[APPEND]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m1:A word->A word_loc` THEN
  REWRITE_TAC[store_list_append; LENGTH_APPEND] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `sp - (LENGTH (y:(A word_loc)list) + LENGTH (y':(A word_loc)list)) =
                  sp - LENGTH y - LENGTH y'` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_add free (word_mul bytes_in_word
                    (word (LENGTH (y:(A word_loc)list) + LENGTH (y':(A word_loc)list)))) =
                  word_add (word_add free (word_mul bytes_in_word (word (LENGTH y))))
                    (word_mul bytes_in_word (word (LENGTH y'))):A word` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FUPDATE_EQ]) THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `m':A word->A word_loc` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 18035 *)
let word_and_lsr_0 = prove
 (`!k (w:A word) n.
     (!i. k <= i /\ i < dimindex (:A) ==> ~bit i w) ==>
     word_and w (word_shl n k) = word 0:A word`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_0] THEN
  ASM_MESON_TAC[]);;

let MP7AUX_shift_LOG2 = prove
 (`good_dimindex(:A) ==> backend_common_word_shift(:A) = LOG2 (dimindex(:A) DIV 8)`,
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  CONV_TAC(DEPTH_CONV LOG2_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 18043 *)
let byte_aligned_IMP_shift = prove
 (`!w:A word. byte_aligned w /\ good_dimindex (:A) ==>
              ?v. w = word_shl v (backend_common_word_shift (:A))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MP7AUX_shift_LOG2] THEN
  EXISTS_TAC `word_ushr (w:A word) (LOG2 (dimindex(:A) DIV 8))` THEN
  REWRITE_TAC[GSYM align_shift] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC align_aligned THEN
  ASM_REWRITE_TAC[GSYM byte_aligned_def]);;

(* HOL4 line 18055 *)
let make_cons_ptr_add = prove
 (`!c (n:A word) tag len.
     byte_aligned n /\ good_dimindex (:A) /\
     backend_common_word_shift (:A) <= shift_length c ==>
     make_cons_ptr c n tag len =
     wl_Word (word_add (word_shl n (shift_length c - backend_common_word_shift (:A)))
                       (get_lowerbits c (wl_Word (ptr_bits c tag len))):A word)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP byte_aligned_IMP_shift o
              CONJ (ASSUME `byte_aligned (n:A word)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A word` SUBST_ALL_TAC) THEN
  REWRITE_TAC[make_cons_ptr_def; get_lowerbits_def; WORD_SHL_COMPOSE;
              injectivity "word_loc"] THEN
  ASM_SIMP_TAC[ARITH_RULE `s <= l ==> s + l - s = l:num`] THEN
  W(fun (asl,w) -> let t = rand w in
     SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`word_and:A word->A word->A word`, lhand t),
                                 rand t), `word 0:A word`)) ASSUME_TAC) THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_0; BIT_WORD_OR;
                BIT_WORD_BITS; BIT_WORD_1; small_shift_length_def; shift_length_def] THEN
    ARITH_TAC;
    ASM_SIMP_TAC[WORD_ADD_OR] THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_1] THEN MESON_TAC[]]);;

(* HOL4 line 18074 *)
let make_ptr_add = prove
 (`!c (n:A word) (tag:B) (len:C).
     byte_aligned n /\ good_dimindex (:A) /\
     backend_common_word_shift (:A) <= shift_length c ==>
     make_ptr c n tag len =
     wl_Word (word_add (word_shl n (shift_length c - backend_common_word_shift (:A)))
                       (word 1):A word)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP byte_aligned_IMP_shift o
              CONJ (ASSUME `byte_aligned (n:A word)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A word` SUBST_ALL_TAC) THEN
  REWRITE_TAC[make_ptr_def; WORD_SHL_COMPOSE; injectivity "word_loc"] THEN
  ASM_SIMP_TAC[ARITH_RULE `s <= l ==> s + l - s = l:num`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_0; BIT_WORD_1;
              shift_length_def] THEN ARITH_TAC);;

(* HOL4 line 18088 (HOL4's clauses have literal patterns T/F, which the    *)
(* kit does not complete: the definition is a match, word_cond_add_def the *)
(* HOL4 clauses as TFL completes them)                                      *)
let word_cond_add_DEF = cake_def
  `word_cond_add c (a:A word) (p:bool#A word_loc) =
     match p with
       (F,x) -> x
     | (T,wl_Word w) ->
         wl_Word (word_add w (word_shl a (shift_length c -
                                          backend_common_word_shift (:A))))
     | (T,other) -> other`;;

let word_cond_add_def = prove
 (`(!c (a:A word) x. word_cond_add c a (F,x) = x) /\
   (!c (a:A word) w.
      word_cond_add c a (T,wl_Word w) =
      wl_Word (word_add w (word_shl a (shift_length c -
                                       backend_common_word_shift (:A))))) /\
   (!c (a:A word) l1 l2. word_cond_add c a (T,wl_Loc l1 l2) = wl_Loc l1 l2)`,
  REWRITE_TAC[word_cond_add_DEF] THEN SIMP[]);;
let _ = cake_add_simps [word_cond_add_def];;

(* HOL4 line 18094 *)
let part_to_words_add = prove
 (`!c part m off (a:A word) w ws m1.
     byte_aligned off /\ byte_aligned a /\
     good_dimindex (:A) /\ backend_common_word_shift (:A) <= shift_length c ==>
     part_to_words c m part (off:A word) = SOME (w,ws) /\
     (!i. SND (lookup_mem m1 i) = word_cond_add c a (lookup_mem m i)) ==>
     ?v vs. part_to_words c m1 part (word_add off a:A word) = SOME (v,vs) /\
            MAP SND vs = MAP (word_cond_add c a) ws /\
            SND v = word_cond_add c a w`,
  MAP_EVERY X_GEN_TAC [`c:data_to_word_config`; `part:const_part`;
    `m:(bool#A word_loc)spt`; `off:A word`; `a:A word`; `w0:bool#A word_loc`;
    `ws0:(bool#A word_loc)list`; `m1:(bool#A word_loc)spt`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `byte_aligned (word_add off a:A word)` ASSUME_TAC THENL
   [ASM_MESON_TAC[byte_aligned_add]; ALL_TAC] THEN
  CASES_ON `part:const_part` THEN REWRITE_TAC[part_to_words_def] THEN
  STRIP_TAC THEN GVS(all_case_eqs()) THEN
  REWRITE_TAC[MAP_MAP_o; o_DEF; word_cond_add_def] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[make_ptr_add; word_cond_add_def; WORD_ADD_LSL; injectivity "word_loc"] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

let MP7AUX_bytes_in_word_pow = prove
 (`good_dimindex(:A) ==>
   bytes_in_word:A word = word (2 EXP LOG2 (dimindex(:A) DIV 8))`,
  REWRITE_TAC[good_dimindex_def; bytes_in_word_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  CONV_TAC(DEPTH_CONV LOG2_CONV) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV));;

(* HOL4 line 18116: byte_aligned_bytes_in_word *)
let data_to_word_memoryProof_byte_aligned_bytes_in_word = prove
 (`good_dimindex (:A) ==> byte_aligned (bytes_in_word:A word)`,
  SIMP_TAC[MP7AUX_bytes_in_word_pow; byte_aligned_def; aligned_pow2]);;

(* HOL4 line 18124 *)
let byte_align_mult_bytes_in_word = prove
 (`!w:A word. good_dimindex (:A) ==>
     byte_aligned (word_mul w bytes_in_word:A word) /\
     byte_aligned (word_mul bytes_in_word w:A word)`,
  SIMP_TAC[MP7AUX_bytes_in_word_pow; byte_aligned_def] THEN
  REWRITE_TAC[GSYM word_1_lsl] THEN MESON_TAC[aligned_mul_shift_1; WORD_MUL_SYM]);;

let MP7AUX_lookup_mem_insert = prove
 (`!k (v:bool#A word_loc) m j.
     lookup_mem (insert k v m) j = if j = k then v else lookup_mem m j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_mem_def; lookup_insert] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 18136 *)
let parts_to_words_add = prove
 (`!c parts m i off (a:A word) w ws m1.
     parts_to_words c m i parts (off:A word) = SOME (w,ws) /\
     byte_aligned off /\ byte_aligned a /\
     good_dimindex (:A) /\ backend_common_word_shift (:A) <= shift_length c /\
     (!i. SND (lookup_mem m1 i) = word_cond_add c a (lookup_mem m i)) ==>
     ?v vs. parts_to_words c m1 i parts (word_add off a:A word) = SOME (v,vs) /\
            MAP SND vs = MAP (word_cond_add c a) ws /\
            SND v = word_cond_add c a w`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[parts_to_words_def; option_INJ; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`lookup_mem (m1:(bool#A word_loc)spt) (i - 1)`;
                          `[]:(bool#A word_loc)list`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                                     is_var(rhs(concl th))))) THEN
    ASM_REWRITE_TAC[MAP];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:(bool#A word_loc)spt`; `i:num`; `off:A word`; `a:A word`;
    `w0:bool#A word_loc`; `ws0:(bool#A word_loc)list`; `m1:(bool#A word_loc)spt`] THEN
  REWRITE_TAC[parts_to_words_def] THEN STRIP_TAC THEN
  GVS(all_case_eqs()) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `h:const_part`; `m:(bool#A word_loc)spt`;
                 `off:A word`; `a:A word`; `x:bool#A word_loc`;
                 `y:(bool#A word_loc)list`; `m1:(bool#A word_loc)spt`]
         part_to_words_add) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`insert i (x:bool#A word_loc) m`; `i + 1`;
     `word_add off (word_mul bytes_in_word (word (LENGTH (y:(bool#A word_loc)list)))):A word`;
     `a:A word`; `w0:bool#A word_loc`; `y':(bool#A word_loc)list`;
     `insert i (v:bool#A word_loc) m1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MP7AUX_lookup_mem_insert] THEN CONJ_TAC THENL
     [MATCH_MP_TAC byte_aligned_add THEN ASM_SIMP_TAC[byte_align_mult_bytes_in_word];
      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (vs:(bool#A word_loc)list) = LENGTH (y:(bool#A word_loc)list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[LENGTH_MAP]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v':bool#A word_loc`; `APPEND vs (vs':(bool#A word_loc)list)`] THEN
  ASM_REWRITE_TAC[MAP_APPEND] THEN
  EXISTS_TAC `(v:bool#A word_loc,vs:(bool#A word_loc)list)` THEN REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`v:bool#A word_loc`; `vs:(bool#A word_loc)list`] THEN
  REWRITE_TAC[] THEN
  EXISTS_TAC `(v':bool#A word_loc,vs':(bool#A word_loc)list)` THEN
  REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  SUBGOAL_THEN `word_add (word_add off a) (word_mul bytes_in_word
                  (word (LENGTH (vs:(bool#A word_loc)list)))) =
                word_add (word_add off (word_mul bytes_in_word
                  (word (LENGTH (y:(bool#A word_loc)list))))) (a:A word)`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_ADD_AC]; ASM_REWRITE_TAC[]]);;

let MP7AUX_word_or_4_3 = prove
 (`word_or (word 4) (word 3):N word = word 7`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 3` THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN SUBST1_TAC) o
      MATCH_MP (ARITH_RULE `i < 3 ==> i = 0 \/ i = 1 \/ i = 2`)) THEN
    CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `2 EXP 3 <= 2 EXP i` MP_TAC THENL
     [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `8 <= n ==> 4 < n /\ 3 < n /\ 7 < n`] THEN
    CONV_TAC NUM_REDUCE_CONV]);;
(* the tag bits of a bignum header *)
let MP7AUX_val_b2w_3 = prove
 (`!s. good_dimindex(:A) ==>
       val (word_or (word_shl (b2w s) 2) (word 3):A word) = if s then 7 else 3`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
  BOOL_CASES_TAC `s:bool` THEN
  REWRITE_TAC[b2w_def; word_1_lsl; WORD_SHL_0; WORD_OR_0] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[MP7AUX_word_or_4_3; VAL_WORD; GSYM dimword_def] THEN
  MATCH_MP_TAC MOD_LT THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* HOL4 line 18161 *)
let part_to_words_IMP_build_words = prove
 (`!c m p (off:A word) w ws.
     part_to_words c m p off = SOME (w,ws) /\ good_dimindex (:A) /\
     byte_aligned off /\ backend_common_word_shift (:A) <= shift_length c ==>
     build_part_words c (\i. SND (lookup_mem m i)) p off = SOME (SND w,MAP SND ws)`,
  REPEAT GEN_TAC THEN CASES_ON `p:const_part` THEN
  REWRITE_TAC[part_to_words_def; build_part_words_def] THEN STRIP_TAC THEN
  GVS(all_case_eqs()) THEN
  ASM_SIMP_TAC[MAP_MAP_o; o_DEF; make_cons_ptr_add; get_lowerbits_ptrbits;
               MP7AUX_val_b2w_3; ETA_AX]);;

(* HOL4 line 18178 *)
let parts_to_words_IMP_build_words = prove
 (`!c m i parts (off:A word) w ws.
     parts_to_words c m i parts off = SOME (w,ws) /\ good_dimindex (:A) /\
     byte_aligned off /\ backend_common_word_shift (:A) <= shift_length c ==>
     build_words c (\i. SND (lookup_mem m i)) i parts off = SOME (SND w,MAP SND ws)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!parts m i (off:A word) w ws.
     parts_to_words c m i parts off = SOME (w,ws) /\ good_dimindex (:A) /\
     byte_aligned off /\ backend_common_word_shift (:A) <= shift_length c ==>
     build_words c (\i. SND (lookup_mem m i)) i parts off = SOME (SND w,MAP SND ws)`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[parts_to_words_def; build_words_def; option_INJ; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                                     is_var(rhs(concl th))))) THEN
    REWRITE_TAC[MAP];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:(bool#A word_loc)spt`; `i:num`; `off:A word`;
    `w0:bool#A word_loc`; `ws0:(bool#A word_loc)list`] THEN
  REWRITE_TAC[parts_to_words_def] THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
  REWRITE_TAC[build_words_def] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `m:(bool#A word_loc)spt`; `h:const_part`;
                 `off:A word`; `x:bool#A word_loc`; `y:(bool#A word_loc)list`]
         part_to_words_IMP_build_words) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`insert i (x:bool#A word_loc) m`; `i + 1`;
     `word_add off (word_mul bytes_in_word
        (word (LENGTH (y:(bool#A word_loc)list)))):A word`;
     `w0:bool#A word_loc`; `y':(bool#A word_loc)list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC byte_aligned_add THEN ASM_SIMP_TAC[byte_align_mult_bytes_in_word];
    ALL_TAC] THEN
  SUBGOAL_THEN `((i =+ SND (x:bool#A word_loc)) (\i. SND (lookup_mem m i))) =
                (\j. SND (lookup_mem (insert i x m) j))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM; MP7AUX_lookup_mem_insert] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 18199 *)
let LESS_EQ_num_size = prove
 (`good_dimindex (:A) ==>
   !m n. n <= m ==> SUC (LENGTH (n2mw n:(A word)list)) <= num_size m`,
  MESON_TAC[LENGTH_n2mw_LE_num_size]);;

(* the bignum case of part_to_words_LENGTH *)
let MP7AUX_PTWL_INT_TAC =
  SUBGOAL_THEN `y = n2mw (num_of_int (abs a')):(A word)list` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `i2mw a' = x,(y:(A word)list)` THEN REWRITE_TAC[i2mw_def; PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(num_of_int (abs a') < 536870912)` ASSUME_TAC THENL
   [UNDISCH_TAC `~small_int (:A) a'` THEN REWRITE_TAC[small_int_def] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
    SUBGOAL_THEN `536870912 <= dimword(:A) DIV 8` MP_TAC THENL
     [MP_TAC(SPECL [`2 EXP 32`; `dimword(:A)`; `8`] DIV_MONO) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT] THEN
    MP_TAC(SPEC `abs(a':int)` INT_OF_NUM_OF_INT) THEN REWRITE_TAC[INT_ABS_POS] THEN
    DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM LE_SUC_LT] THEN MATCH_MP_TAC LENGTH_n2mw_LE_num_size THEN
  ASM_REWRITE_TAC[LE_REFL];;

(* HOL4 line 18222 *)
let part_to_words_LENGTH = prove
 (`!c m h a (w:bool#A word_loc) ws.
     part_to_words c m h a = SOME (w,ws) /\ good_dimindex (:A) ==>
     LENGTH ws <= part_space_req h`,
  REPEAT GEN_TAC THEN CASES_ON `h:const_part` THEN
  REWRITE_TAC[part_to_words_def; part_space_req_def] THEN STRIP_TAC THEN
  GVS(all_case_eqs()) THEN
  REWRITE_TAC[LENGTH; LENGTH_MAP; LENGTH_write_bytes; LENGTH_REPLICATE; LET_DEF;
              LET_END_DEF] THEN
  FIRST
   [MP7AUX_PTWL_INT_TAC THEN NO_TAC;
    UNDISCH_TAC `~NULL (a1:num list)` THEN REWRITE_TAC[NULL_EQ] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; byte_len_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPECL [`strlen a'`; `4`; `8`] DIV_thm1) THEN ARITH_TAC]);;

(* HOL4 line 18240 *)
let const_parts_to_words_LENGTH = prove
 (`!c parts (w:bool#A word_loc) ws.
     const_parts_to_words c parts = SOME (w,ws) /\ good_dimindex (:A) ==>
     LENGTH ws <= SUM (MAP part_space_req parts)`,
  GEN_TAC THEN REWRITE_TAC[const_parts_to_words_def] THEN
  SUBGOAL_THEN
   `!parts m k (a:A word) (w:bool#A word_loc) ws.
      parts_to_words c m k parts a = SOME (w,ws) /\ good_dimindex (:A) ==>
      LENGTH ws <= SUM (MAP part_space_req parts)`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[parts_to_words_def; MAP; SUM] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC part_to_words_LENGTH THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 18263 *)
let good_loc_def = cake_def
  `(good_loc code (wl_Loc n m) <=> m = 0 /\ n IN code) /\
   (good_loc code (_:A word_loc) <=> T)`;;

(* the words of one part are good locations if the map's are *)
let MP7AUX_part_to_words_good_loc = prove
 (`!c m x (a:A word) w xs s.
     part_to_words c m x a = SOME (w,xs) /\
     (!k. good_loc s (SND (lookup_mem m k))) ==>
     good_loc s (SND w) /\ ALL (good_loc s o SND) xs`,
  REPEAT GEN_TAC THEN CASES_ON `x:const_part` THEN REWRITE_TAC[part_to_words_def] THEN
  STRIP_TAC THEN GVS(all_case_eqs()) THEN
  ASM_REWRITE_TAC[ALL; ALL_MAP; o_DEF; good_loc_def; make_ptr_def] THEN
  REWRITE_TAC[GSYM ALL_MEM; o_DEF] THEN TRY COND_CASES_TAC THEN
  REWRITE_TAC[ALL; good_loc_def]);;

(* HOL4 line 18268 *)
let const_parts_to_words_good_loc = prove
 (`!c parts y0 (y1:A word_loc) y2 s.
     const_parts_to_words c parts = SOME ((y0,y1),y2) ==>
     good_loc s y1 /\ ALL (good_loc s o SND) y2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[const_parts_to_words_def] THEN
  SUBGOAL_THEN
   `!parts m k (a:A word) (w:bool#A word_loc) ws.
      (!j. good_loc s (SND (lookup_mem m j))) /\
      parts_to_words c m k parts a = SOME (w,ws) ==>
      good_loc s (SND w) /\ ALL (good_loc s o SND) ws`
   (fun th -> DISCH_TAC THEN
              MP_TAC(ISPECL [`parts:const_part list`; `LN:(bool#A word_loc)spt`; `0`;
                             `word 0:A word`; `(y0:bool,y1:A word_loc)`;
                             `y2:(bool#A word_loc)list`] th) THEN
              ASM_REWRITE_TAC[lookup_mem_def; lookup_def] THEN
              CASE_REWRITE_TAC[good_loc_def]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[parts_to_words_def] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                                     is_var(rhs(concl th))))) THEN
    ASM_REWRITE_TAC[ALL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GVS(all_case_eqs()) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `m:(bool#A word_loc)spt`; `h:const_part`;
                 `a:A word`; `x:bool#A word_loc`; `y:(bool#A word_loc)list`;
                 `s:num->bool`] MP7AUX_part_to_words_good_loc) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`insert k (x:bool#A word_loc) m`; `k + 1`;
    `word_add a (word_mul bytes_in_word
       (word (LENGTH (y:(bool#A word_loc)list)))):A word`;
    `w:bool#A word_loc`; `y':(bool#A word_loc)list`]) THEN
  ASM_REWRITE_TAC[MP7AUX_lookup_mem_insert; ALL_APPEND] THEN ANTS_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* HOL4 line 18299 *)
let memory_rel_do_build_const = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm vars parts v refs1 ts1 w ws free
    curr.
     data_do_build_const parts refs (SOME ts) = (v,refs1,SOME ts1) /\
     const_parts_to_words c parts = SOME (w,ws) /\
     memory_rel c be ts refs sp st m dm vars /\
     SUM (MAP part_space_req parts) <= sp /\
     FLOOKUP st NextFree = SOME (wl_Word free) /\
     FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
     good_dimindex (:A) ==>
     ?m1.
       let nf = word_add free (word_mul bytes_in_word (word (LENGTH ws))) in
       let adjust = word_cond_add c (word_sub free curr:A word) in
       memory_rel c be ts1 refs1 (sp - LENGTH ws)
         (st |+ (NextFree,wl_Word nf)) m1 dm (CONS (v,adjust w) vars) /\
       data_to_word_memoryProof_store_list free (MAP adjust ws) m dm = SOME m1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `byte_aligned (word_sub free curr:A word) /\
                backend_common_word_shift(:A) <= shift_length c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `memory_rel c be ts refs sp st (m:A word -> A word_loc) dm vars` THEN
    REWRITE_TAC[memory_rel_def; heap_in_memory_store_def] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `FLOOKUP st NextFree = SOME (wl_Word (free:A word))` THEN
    UNDISCH_TAC `FLOOKUP st CurrHeap = SOME (wl_Word (curr:A word))` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add c x) c = x:A word`] THEN
    ASM_SIMP_TAC[byte_align_mult_bytes_in_word];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. lookup_mem (LN:(bool#A word_loc)spt) i = (F,wl_Word (word 0))`
    ASSUME_TAC THENL
   [REWRITE_TAC[lookup_mem_def; lookup_def] THEN CASE_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `parts:const_part list`;
    `LN:(bool#A word_loc)spt`; `0`; `word 0:A word`; `word_sub free curr:A word`;
    `w:bool#A word_loc`; `ws:(bool#A word_loc)list`; `LN:(bool#A word_loc)spt`]
    parts_to_words_add) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM const_parts_to_words_def; word_cond_add_def; byte_aligned_def;
                    aligned_0];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:bool#A word_loc` (X_CHOOSE_THEN `vs0:(bool#A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `LN:(bool#A word_loc)spt`; `0`;
    `parts:const_part list`; `word_sub free curr:A word`; `v0:bool#A word_loc`;
    `vs0:(bool#A word_loc)list`] parts_to_words_IMP_build_words) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `dm:A word->bool`;
    `vars:(data_v#A word_loc)list`; `ts1:num`;
    `word_cond_add c (word_sub free curr) (w:bool#A word_loc)`;
    `parts:const_part list`; `0`; `st:(store_name,A word_loc)fmap`; `free:A word`;
    `curr:A word`; `sp:num`; `\x:num. data_Number (&0)`;
    `\i:num. wl_Word (word 0):A word_loc`; `refs:(data_v bvl_ref)spt`; `ts:num`;
    `refs1:(data_v bvl_ref)spt`; `m:A word->A word_loc`; `v:data_v`;
    `MAP (word_cond_add c (word_sub free curr)) (ws:(bool#A word_loc)list)`]
    memory_rel_do_build) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM data_do_build_const_def] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND] THEN
  SUBGOAL_THEN `Smallnum (&0):A word = word 0` ASSUME_TAC THENL
   [REWRITE_TAC[data_to_word_Smallnum_def; INT_LT_REFL; INT_MUL_RZERO; NUM_OF_INT_OF_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `APPEND (MAP (\k:num. (data_Number (&0),wl_Word (word 0):A word_loc)) t)
            (vars:(data_v#A word_loc)list)`; `&0:int`] IMP_memory_rel_Number) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[small_int_def] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`4294967296`; `dimword(:A)`; `8`] DIV_MONO) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

(* HOL4 line 18353 *)
let read_word_def = cake_def
  `read_word dm (m:A word -> A word_loc) a =
     (theWord (m a), (a IN dm /\ isWord (m a)))`;;

(* the termination condition of word_xor_bytes *)
let SKELAUX_VAL_WORD_SUB_2_LT = prove
 (`!len:A word.
     ~(word_ult len (word 2) \/ ~good_dimindex (:A)) ==>
     val (word_sub len (word 2)) < val len`,
  GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM; WORD_ULT; NOT_LT; good_dimindex_def] THEN
  STRIP_TAC THEN
  (SUBGOAL_THEN `val(word 2:A word) = 2` ASSUME_TAC THENL
    [REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     ALL_TAC] THEN
   REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_REWRITE_TAC[] THEN
   TRY COND_CASES_TAC THEN ASM_ARITH_TAC));;

(* HOL4 line 18357 *)
let word_xor_bytes_def = cake_def_wf
  `measure (\p:A word#A word#A word#(A word->bool)#(A word->A word_loc).
              val (FST (SND (SND p))))`
  (REPEAT STRIP_TAC THEN REWRITE_TAC[measure_THM; FST; SND] THEN
   MATCH_MP_TAC SKELAUX_VAL_WORD_SUB_2_LT THEN ASM_REWRITE_TAC[])
  `word_xor_bytes (a1:A word) (a2:A word) (len:A word) dm (m:A word -> A word_loc) =
     if word_ult len (word 2) \/ ~good_dimindex (:A) then
       if len = word 0 then SOME m else
         let (w1a,c1) = read_word dm m a1 in
         let (w2a,c2) = read_word dm m a2 in
         let a = word_xor w1a w2a in
         let m = (a2 =+ wl_Word (a:A word)) m in
         if c1 /\ c2 then SOME m else NONE
     else
       let (w1a,c1) = read_word dm m a1 in
       let (w2a,c2) = read_word dm m a2 in
       let (w1b,c3) = read_word dm m (word_add a1 bytes_in_word) in
       let (w2b,c4) = read_word dm m (word_add a2 bytes_in_word) in
       let a = word_xor w1a w2a in
       let b = word_xor w1b w2b in
       let m = (word_add a2 bytes_in_word =+ wl_Word b) ((a2 =+ wl_Word a) m) in
       if c1 /\ c2 /\ c3 /\ c4 then
         word_xor_bytes (word_add a1 (word_mul (word 2) bytes_in_word))
           (word_add a2 (word_mul (word 2) bytes_in_word))
           (word_sub len (word 2)) dm m
       else NONE`;;
let word_xor_bytes_ind = cake_ind "word_xor_bytes";;

(* HOL4 line 18386 *)
let make_zeros_def = cake_def
  `make_zeros (vals:byte list) =
     REPLICATE (LENGTH vals DIV (dimindex (:A) DIV 8) + 1) (word 0:A word)`;;

(* HOL4 line 18391 *)
let xor_words_def = cake_def
  `(xor_words [] ys = SOME ys) /\
   (xor_words xs [] = NONE) /\
   (xor_words (CONS x xs) (CONS y ys) =
      match xor_words xs ys with
        NONE -> NONE
      | SOME rest -> SOME (CONS (word_xor (x:A word) y) rest))`;;
let xor_words_ind = cake_ind "xor_words";;

(* HOL4 line 18400 *)
let word_xor_set_byte = prove
 (`!a h1 (w1:A word) be h2 w2.
     word_xor (set_byte a h1 w1 be) (set_byte a h2 w2 be) =
     set_byte a (word_xor h1 h2) (word_xor w1 w2) be`,
  REPEAT GEN_TAC THEN REWRITE_TAC[set_byte_def; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `k = byte_index (a:A word) be` THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR_ALT; BIT_WORD_OR_ALT; BIT_WORD_SLICE_ALT;
              BIT_WORD_SHL; BIT_WORD_ZX] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(ARITH_RULE `i < k \/ (k <= i /\ i < k + 8) \/ k + 8 <= i`) THENL
   [ASM_SIMP_TAC[LE_0; ARITH_RULE `i < k ==> ~(k + 8 <= i) /\ ~(k <= i)`];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `k <= i /\ i < k + 8 ==> ~(k + 8 <= i) /\ ~(i < k)`] THEN
      CONV_TAC TAUT;
      ASM_SIMP_TAC[ARITH_RULE `k + 8 <= i ==> k <= i /\ ~(i < k)`] THEN
      SUBGOAL_THEN `!h:byte. ~bit (i - k) h` (fun th -> REWRITE_TAC[th]) THEN
      GEN_TAC THEN MP_TAC(ISPECL [`h:byte`; `i - k:num`] BIT_TRIVIAL) THEN
      REWRITE_TAC[DIMINDEX_8] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]]);;

(* HOL4 line 18414 *)
let xor_bytes_bytes_to_word = prove
 (`!be k vals1 vals2 res_vals (a:A word).
     xor_bytes vals1 vals2 = SOME res_vals ==>
     word_xor (bytes_to_word k a vals1 (word 0) be)
              (bytes_to_word k a vals2 (word 0) be) =
     bytes_to_word k a res_vals (word 0) be`,
  GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[bytes_to_word_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; WORD_XOR_REFL] THEN
  MAP_EVERY X_GEN_TAC [`v1:byte list`; `v2:byte list`; `rv:byte list`; `a:A word`] THEN
  CASES_ON `v1:byte list` THEN CASES_ON `v2:byte list` THEN
  REWRITE_TAC[xor_bytes_def; option_DISTINCT; option_INJ] THEN CASE_REWRITE_TAC[] THEN
  TRY(DISCH_THEN(SUBST1_TAC o SYM) THEN CASE_REWRITE_TAC[WORD_XOR_0; WORD_XOR_REFL] THEN
      NO_TAC) THEN
  CASES_ON `xor_bytes a1 a1'` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[word_xor_set_byte] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 18431 (the theorem of line 18638 rebinds the name) *)
let xor_bytes_length = prove
 (`!xs ys zs.
     xor_bytes xs ys = SOME zs ==> LENGTH xs <= LENGTH zs /\ LENGTH zs = LENGTH ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[xor_bytes_def; option_INJ] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LENGTH; LE_0]; ALL_TAC] THEN
  GEN_TAC THEN CASES_ON `ys:byte list` THEN REWRITE_TAC[xor_bytes_def; option_DISTINCT] THEN
  GEN_TAC THEN CASES_ON `xor_bytes t a1` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a1:byte list`; `a:byte list`]) THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* HOL4 line 18440 *)
let xor_bytes_drop = prove
 (`!n xs ys zs.
     xor_bytes xs ys = SOME zs ==>
     xor_bytes (DROP n xs) (DROP n ys) = SOME (DROP n zs)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[xor_bytes_def; option_INJ; DROP_DEF] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN GEN_TAC THEN CASES_ON `ys:byte list` THEN
  REWRITE_TAC[xor_bytes_def; option_DISTINCT] THEN
  GEN_TAC THEN CASES_ON `xor_bytes t a1` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DROP_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[xor_bytes_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MP7AUX_DIV_SUB_ADD1 = prove
 (`!n k. 0 < k /\ k <= n ==> n DIV k = (n - k) DIV k + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`1`; `n - k:num`; `k:num`] (CONJUNCT1 DIV_MULT_ADD)) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> k + n - k = n:num`] THEN ARITH_TAC);;

(* HOL4 line 18451 (local; the theorem of line 18483 rebinds the name) *)
let xor_bytes_xor_words = prove
 (`!be zs1 zs2 vals1 vals2 res_vals.
     xor_bytes vals1 vals2 = SOME res_vals /\ good_dimindex (:A) /\
     ALL (\w. w = word 0) zs1 /\ ALL (\w. w = word 0) zs2 /\
     LENGTH zs1 = LENGTH vals1 DIV (dimindex (:A) DIV 8) + 1 /\
     LENGTH zs2 = LENGTH vals2 DIV (dimindex (:A) DIV 8) + 1 ==>
     xor_words (write_bytes vals1 zs1 be)
               (write_bytes vals2 zs2 be) =
     SOME (write_bytes res_vals zs2 be:(A word)list)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = n + 1)`] THEN
  GEN_TAC THEN CASES_ON `zs2:(A word)list` THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = n + 1)`; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:A word`))) THEN
  REWRITE_TAC[write_bytes_def; LET_DEF; LET_END_DEF; xor_words_def] THEN
  SUBGOAL_THEN `0 < dimindex(:A) DIV 8` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `k = dimindex(:A) DIV 8` THEN
  MP_TAC(ISPECL [`be:bool`; `k:num`; `vals1:byte list`; `vals2:byte list`;
                 `res_vals:byte list`; `word 0:A word`] xor_bytes_bytes_to_word) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `vals1:byte list`; `vals2:byte list`; `res_vals:byte list`]
         xor_bytes_drop) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `xor_words (write_bytes (DROP k vals1) t be)
                  (write_bytes (DROP k vals2) a1 be) =
                SOME (write_bytes (DROP k res_vals) a1 be:(A word)list)`
    (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[]) THEN
  ASM_CASES_TAC `LENGTH (vals1:byte list) < k` THENL
   [SUBGOAL_THEN `t:(A word)list = []` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
      UNDISCH_TAC `SUC (LENGTH (t:(A word)list)) = LENGTH (vals1:byte list) DIV k + 1` THEN
      ASM_SIMP_TAC[DIV_LT] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `xor_bytes (DROP k vals1) (DROP k vals2) = SOME (DROP k res_vals)` THEN
    ASM_SIMP_TAC[DROP_LENGTH_TOO_LONG; LT_IMP_LE; xor_bytes_def; option_INJ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[write_bytes_def; xor_words_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH_DROP] THEN
  SUBGOAL_THEN `k <= LENGTH (vals2:byte list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`vals1:byte list`; `vals2:byte list`; `res_vals:byte list`]
           xor_bytes_length) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`LENGTH (vals1:byte list)`; `k:num`] MP7AUX_DIV_SUB_ADD1) THEN
  MP_TAC(ISPECL [`LENGTH (vals2:byte list)`; `k:num`] MP7AUX_DIV_SUB_ADD1) THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN ASM_ARITH_TAC);;

(* HOL4 line 18483 *)
let xor_bytes_xor_words = prove
 (`!be vals1 vals2 res_vals.
     xor_bytes vals1 vals2 = SOME res_vals /\ good_dimindex (:A) ==>
     xor_words (write_bytes vals1 (make_zeros vals1) be)
               (write_bytes vals2 (make_zeros vals2) be) =
     SOME (write_bytes res_vals (make_zeros vals2) be:(A word)list)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC xor_bytes_xor_words THEN
  ASM_REWRITE_TAC[make_zeros_def; LENGTH_REPLICATE; GSYM ALL_MEM; MEM_REPLICATE] THEN
  MESON_TAC[]);;

let MP7AUX_ADD_BW_BW = prove
 (`!a:A word. word_add (word_add a bytes_in_word) bytes_in_word =
              word_add a (word_mul (word 2) bytes_in_word)`,
  CONV_TAC WORD_RULE);;
let MP7AUX_VAL_WORD_LT = prove
 (`!n. n < dimword(:A) ==> val(word n:A word) = n`,
  REWRITE_TAC[dimword_def; VAL_WORD_EQ]);;
let mp7_is_fun2set_th th =
  try fst(dest_const(rator(rand(concl th)))) = "fun2set" with _ -> false;;

(* HOL4 line 18495 (the unused bound variable be of HOL4 is left out) *)
let xor_words_word_list = prove
 (`!dm vals1 vals2 res_vals (a1:A word) a2 frame (m:A word -> A word_loc).
     xor_words vals1 vals2 = SOME res_vals /\
     good_dimindex (:A) /\ LENGTH vals1 < dimword (:A) /\
     (misc_word_list a1 (MAP wl_Word vals1) STAR
      misc_word_list a2 (MAP wl_Word vals2) STAR
      frame) (fun2set (m,dm)) ==>
     ?m1.
       (misc_word_list a1 (MAP wl_Word vals1) STAR
        misc_word_list a2 (MAP wl_Word res_vals) STAR
        frame) (fun2set (m1,dm:A word->bool)) /\
       word_xor_bytes a1 a2 (word (LENGTH vals1)) dm m = SOME m1`,
  GEN_TAC THEN
  SUBGOAL_THEN `!n vals1 vals2 res_vals (a1:A word) a2 frame (m:A word -> A word_loc).
     LENGTH vals1 = n /\
     xor_words vals1 vals2 = SOME res_vals /\
     good_dimindex (:A) /\ LENGTH vals1 < dimword (:A) /\
     (misc_word_list a1 (MAP wl_Word vals1) STAR
      misc_word_list a2 (MAP wl_Word vals2) STAR
      frame) (fun2set (m,dm)) ==>
     ?m1.
       (misc_word_list a1 (MAP wl_Word vals1) STAR
        misc_word_list a2 (MAP wl_Word res_vals) STAR
        frame) (fun2set (m1,dm:A word->bool)) /\
       word_xor_bytes a1 a2 (word (LENGTH vals1)) dm m = SOME m1`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`v1:(A word)list`; `v2:(A word)list`; `rv:(A word)list`;
    `p1:A word`; `p2:A word`; `frame:(A word#A word_loc->bool)->bool`;
    `m:A word -> A word_loc`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
  CASES_ON `v1:(A word)list` THENL
   [UNDISCH_TAC `xor_words [] v2 = SOME (rv:(A word)list)` THEN
    REWRITE_TAC[xor_words_def; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    EXISTS_TAC `m:A word -> A word_loc` THEN ASM_REWRITE_TAC[LENGTH] THEN
    ONCE_REWRITE_TAC[word_xor_bytes_def] THEN REWRITE_TAC[WORD_ULT; VAL_WORD_0] THEN
    SUBGOAL_THEN `val(word 2:A word) = 2` SUBST1_TAC THENL
     [MATCH_MP_TAC MP7AUX_VAL_WORD_LT THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  UNDISCH_TAC `xor_words (CONS a0 a1) v2 = SOME (rv:(A word)list)` THEN
  CASES_ON `v2:(A word)list` THEN REWRITE_TAC[xor_words_def; option_DISTINCT] THEN
  CASES_ON `xor_words a1 (a1':(A word)list)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(rator(rand(concl th)))) = "fun2set" with _ -> false)) THEN
  REWRITE_TAC[MAP; misc_word_list_def] THEN DISCH_TAC THEN
  MP7AUX_SEP_R_TAC THEN
  SUBGOAL_THEN `val(word 2:A word) = 2 /\ val(word 1:A word) = 1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MP7AUX_VAL_WORD_LT THEN
    UNDISCH_TAC `2 EXP 32 <= dimword(:A)` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  CASES_ON `a1:(A word)list` THENL
   [UNDISCH_TAC `xor_words [] a1' = SOME (a:(A word)list)` THEN
    REWRITE_TAC[xor_words_def; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    EXISTS_TAC `(p2 =+ wl_Word (word_xor a0 a0')) (m:A word -> A word_loc)` THEN CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> ASSUME_TAC(mp7_sep_write `p2:A word`
        `wl_Word (word_xor a0 a0'):A word_loc` th)) THEN MP7AUX_SEP_AC_TAC;
      UNDISCH_TAC `LENGTH [a0:A word] = n` THEN REWRITE_TAC[LENGTH] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[word_xor_bytes_def] THEN
      ASM_REWRITE_TAC[WORD_ULT; ARITH; GSYM VAL_EQ; VAL_WORD_0; read_word_def] THEN
      CASE_REWRITE_TAC[theWord_def; isWord_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF]];
    ALL_TAC] THEN
  UNDISCH_TAC `xor_words (CONS a0'' a1'') a1' = SOME (a:(A word)list)` THEN
  CASES_ON `a1':(A word)list` THEN REWRITE_TAC[xor_words_def; option_DISTINCT] THEN
  CASES_ON `xor_words a1'' (a1''':(A word)list)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o check mp7_is_fun2set_th) THEN
  REWRITE_TAC[MAP; misc_word_list_def; MP7AUX_ADD_BW_BW] THEN DISCH_TAC THEN
  REWRITE_TAC[MAP; misc_word_list_def; MP7AUX_ADD_BW_BW] THEN
  MP7AUX_SEP_R_TAC THEN
  SUBGOAL_THEN `n = LENGTH (a1'':(A word)list) + 2` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `LENGTH (CONS (a0:A word) (CONS a0'' a1'')) = n` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (a1'':(A word)list)`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m' = (word_add p2 bytes_in_word =+ wl_Word (word_xor a0'' a0'''))
                     ((p2 =+ wl_Word (word_xor a0 a0')) (m:A word -> A word_loc))` THEN
  DISCH_THEN(MP_TAC o SPECL [`a1'':(A word)list`; `a1''':(A word)list`; `a':(A word)list`;
    `word_add p1 (word_mul (word 2) bytes_in_word):A word`;
    `word_add p2 (word_mul (word 2) bytes_in_word):A word`;
    `set_sep_one (p1:A word,wl_Word a0) STAR
     set_sep_one (word_add p1 bytes_in_word,wl_Word a0'') STAR
     set_sep_one (p2,wl_Word (word_xor a0 a0')) STAR
     set_sep_one (word_add p2 bytes_in_word,wl_Word (word_xor a0'' a0''')) STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `m':A word -> A word_loc`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (CONS (a0:A word) (CONS a0'' a1'')) < dimword(:A)` THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(mp7_sep_write `p2:A word`
        `wl_Word (word_xor a0 a0'):A word_loc` th)) THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(mp7_sep_write `word_add p2 bytes_in_word:A word`
        `wl_Word (word_xor a0'' a0'''):A word_loc` th)) THEN
    EXPAND_TAC "m'" THEN MP7AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:A word -> A word_loc` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m1:A word -> A word_loc` THEN CONJ_TAC THENL
   [MP7AUX_SEP_AC_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[word_xor_bytes_def] THEN
  SUBGOAL_THEN `val(word (LENGTH (a1'':(A word)list) + 2):A word) = LENGTH a1'' + 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MP7AUX_VAL_WORD_LT THEN
    UNDISCH_TAC `LENGTH (CONS (a0:A word) (CONS a0'' a1'')) < dimword(:A)` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ULT] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(n + 2 < 2)`; read_word_def] THEN
  CASE_REWRITE_TAC[theWord_def; isWord_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_sub (word (LENGTH (a1'':(A word)list) + 2)) (word 2):A word =
                word (LENGTH a1'')` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]]);;

(* HOL4 line 18546 (the unused bound variable be of HOL4 is left out) *)
let xor_words_word_list_alias = prove
 (`!dm vals1 res_vals (a1:A word) frame (m:A word -> A word_loc).
     xor_words vals1 vals1 = SOME res_vals /\
     good_dimindex (:A) /\ LENGTH vals1 < dimword (:A) /\
     (misc_word_list a1 (MAP wl_Word vals1) STAR frame) (fun2set (m,dm)) ==>
     ?m1.
       (misc_word_list a1 (MAP wl_Word res_vals) STAR frame)
         (fun2set (m1,dm:A word->bool)) /\
       word_xor_bytes a1 a1 (word (LENGTH vals1)) dm m = SOME m1`,
  GEN_TAC THEN
  SUBGOAL_THEN `!n vals1 res_vals (a1:A word) frame (m:A word -> A word_loc).
     LENGTH vals1 = n /\
     xor_words vals1 vals1 = SOME res_vals /\
     good_dimindex (:A) /\ LENGTH vals1 < dimword (:A) /\
     (misc_word_list a1 (MAP wl_Word vals1) STAR frame) (fun2set (m,dm)) ==>
     ?m1.
       (misc_word_list a1 (MAP wl_Word res_vals) STAR frame)
         (fun2set (m1,dm:A word->bool)) /\
       word_xor_bytes a1 a1 (word (LENGTH vals1)) dm m = SOME m1`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`v1:(A word)list`; `rv:(A word)list`;
    `p1:A word`; `frame:(A word#A word_loc->bool)->bool`;
    `m:A word -> A word_loc`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP7AUX_DIMWORD_32) THEN
  SUBGOAL_THEN `val(word 2:A word) = 2 /\ val(word 1:A word) = 1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MP7AUX_VAL_WORD_LT THEN
    UNDISCH_TAC `2 EXP 32 <= dimword(:A)` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  CASES_ON `v1:(A word)list` THENL
   [UNDISCH_TAC `xor_words [] [] = SOME (rv:(A word)list)` THEN
    REWRITE_TAC[xor_words_def; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    EXISTS_TAC `m:A word -> A word_loc` THEN ASM_REWRITE_TAC[LENGTH] THEN
    ONCE_REWRITE_TAC[word_xor_bytes_def] THEN REWRITE_TAC[WORD_ULT; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_TAC `xor_words (CONS a0 a1) (CONS a0 a1) = SOME (rv:(A word)list)` THEN
  REWRITE_TAC[xor_words_def] THEN
  CASES_ON `xor_words a1 (a1:(A word)list)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o check mp7_is_fun2set_th) THEN
  REWRITE_TAC[MAP; misc_word_list_def] THEN DISCH_TAC THEN
  MP7AUX_SEP_R_TAC THEN
  CASES_ON `a1:(A word)list` THENL
   [UNDISCH_TAC `xor_words [] [] = SOME (a:(A word)list)` THEN
    REWRITE_TAC[xor_words_def; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    EXISTS_TAC `(p1 =+ wl_Word (word_xor a0 a0)) (m:A word -> A word_loc)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> ASSUME_TAC(mp7_sep_write `p1:A word`
        `wl_Word (word_xor a0 a0):A word_loc` th)) THEN MP7AUX_SEP_AC_TAC;
      UNDISCH_TAC `LENGTH [a0:A word] = n` THEN REWRITE_TAC[LENGTH] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[word_xor_bytes_def] THEN
      ASM_REWRITE_TAC[WORD_ULT; ARITH; GSYM VAL_EQ; VAL_WORD_0; read_word_def] THEN
      CASE_REWRITE_TAC[theWord_def; isWord_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF]];
    ALL_TAC] THEN
  UNDISCH_TAC `xor_words (CONS a0' a1') (CONS a0' a1') = SOME (a:(A word)list)` THEN
  REWRITE_TAC[xor_words_def] THEN
  CASES_ON `xor_words a1' (a1':(A word)list)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o check mp7_is_fun2set_th) THEN
  REWRITE_TAC[MAP; misc_word_list_def; MP7AUX_ADD_BW_BW] THEN DISCH_TAC THEN
  REWRITE_TAC[MAP; misc_word_list_def; MP7AUX_ADD_BW_BW] THEN
  MP7AUX_SEP_R_TAC THEN
  SUBGOAL_THEN `n = LENGTH (a1':(A word)list) + 2` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `LENGTH (CONS (a0:A word) (CONS a0' a1')) = n` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (a1':(A word)list)`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m' = (word_add p1 bytes_in_word =+ wl_Word (word_xor a0' a0'))
                     ((p1 =+ wl_Word (word_xor a0 a0)) (m:A word -> A word_loc))` THEN
  DISCH_THEN(MP_TAC o SPECL [`a1':(A word)list`; `a':(A word)list`;
    `word_add p1 (word_mul (word 2) bytes_in_word):A word`;
    `set_sep_one (p1:A word,wl_Word (word_xor a0 a0)) STAR
     set_sep_one (word_add p1 bytes_in_word,wl_Word (word_xor a0' a0')) STAR
     (frame:(A word#A word_loc->bool)->bool)`;
    `m':A word -> A word_loc`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (CONS (a0:A word) (CONS a0' a1')) < dimword(:A)` THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(mp7_sep_write `p1:A word`
        `wl_Word (word_xor a0 a0):A word_loc` th)) THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(mp7_sep_write `word_add p1 bytes_in_word:A word`
        `wl_Word (word_xor a0' a0'):A word_loc` th)) THEN
    EXPAND_TAC "m'" THEN MP7AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:A word -> A word_loc` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m1:A word -> A word_loc` THEN CONJ_TAC THENL
   [MP7AUX_SEP_AC_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[word_xor_bytes_def] THEN
  SUBGOAL_THEN `val(word (LENGTH (a1':(A word)list) + 2):A word) = LENGTH a1' + 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MP7AUX_VAL_WORD_LT THEN
    UNDISCH_TAC `LENGTH (CONS (a0:A word) (CONS a0' a1')) < dimword(:A)` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ULT] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(n + 2 < 2)`; read_word_def] THEN
  CASE_REWRITE_TAC[theWord_def; isWord_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_sub (word (LENGTH (a1':(A word)list) + 2)) (word 2):A word =
                word (LENGTH a1')` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]]);;

(* HOL4 line 18595 *)
let xor_bytes_word_list = prove
 (`!vals1 vals2 res_vals (m:A word -> A word_loc) dm.
   !a1 a2 be frame.
     xor_bytes vals1 vals2 = SOME res_vals /\
     good_dimindex (:A) /\ LENGTH (make_zeros vals1:(A word)list) < dimword (:A) /\
     (misc_word_list a1 (MAP wl_Word (write_bytes vals1 (make_zeros vals1) be)) STAR
      misc_word_list a2 (MAP wl_Word (write_bytes vals2 (make_zeros vals2) be)) STAR
      frame) (fun2set (m,dm)) ==>
     ?m1.
       (misc_word_list a1
          (MAP wl_Word (write_bytes vals1 (make_zeros vals1:(A word)list) be)) STAR
        misc_word_list a2
          (MAP wl_Word (write_bytes res_vals (make_zeros vals2:(A word)list) be)) STAR
        frame) (fun2set (m1,dm:A word->bool)) /\
       word_xor_bytes a1 a2 (word (LENGTH (make_zeros vals1:(A word)list))) dm m =
       SOME m1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dm:A word->bool`;
                 `write_bytes vals1 (make_zeros vals1:(A word)list) be`;
                 `write_bytes vals2 (make_zeros vals2:(A word)list) be`;
                 `write_bytes res_vals (make_zeros vals2:(A word)list) be`;
                 `a1:A word`; `a2:A word`;
                 `frame:(A word#A word_loc->bool)->bool`; `m:A word -> A word_loc`]
         xor_words_word_list) THEN
  MP_TAC(ISPECL [`be:bool`; `vals1:byte list`; `vals2:byte list`; `res_vals:byte list`]
     (INST_TYPE [`:A`,`:A`] xor_bytes_xor_words)) THEN
  ASM_SIMP_TAC[LENGTH_write_bytes]);;

(* HOL4 line 18617 *)
let xor_bytes_word_list_alias = prove
 (`!vals1 res_vals1 (m:A word -> A word_loc) dm.
   !a1 be frame.
     xor_bytes vals1 vals1 = SOME res_vals1 /\
     good_dimindex (:A) /\ LENGTH (make_zeros vals1:(A word)list) < dimword (:A) /\
     (misc_word_list a1 (MAP wl_Word (write_bytes vals1 (make_zeros vals1) be)) STAR
      frame) (fun2set (m,dm)) ==>
     ?m1.
       (misc_word_list a1
          (MAP wl_Word (write_bytes res_vals1 (make_zeros vals1:(A word)list) be)) STAR
        frame) (fun2set (m1,dm:A word->bool)) /\
       word_xor_bytes a1 a1 (word (LENGTH (make_zeros vals1:(A word)list))) dm m =
       SOME m1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dm:A word->bool`;
                 `write_bytes vals1 (make_zeros vals1:(A word)list) be`;
                 `write_bytes res_vals1 (make_zeros vals1:(A word)list) be`;
                 `a1:A word`;
                 `frame:(A word#A word_loc->bool)->bool`; `m:A word -> A word_loc`]
         xor_words_word_list_alias) THEN
  MP_TAC(ISPECL [`be:bool`; `vals1:byte list`; `vals1:byte list`; `res_vals1:byte list`]
     (INST_TYPE [`:A`,`:A`] xor_bytes_xor_words)) THEN
  ASM_SIMP_TAC[LENGTH_write_bytes]);;

(* HOL4 line 18646 *)
let el_length_Bytes = prove
 (`!be fl vals (zeros:(A word)list).
     el_length (Bytes be fl vals zeros) = LENGTH zeros + 1`,
  REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF; el_length_def;
              LENGTH_write_bytes]);;

(* HOL4 line 18652 *)
let blocks_unique_insert_ByteArray2 = prove
 (`!ts refs bl1 p1 bl2 p2 (vars:(data_v#A)list) fl2 res_vals.
     blocks_unique ts
       (all_vs refs (CONS (data_RefPtr bl1 p1)
                       (CONS (data_RefPtr bl2 p2) (MAP FST vars)))) ==>
     blocks_unique ts
       (all_vs (insert p2 (bvl_ByteArray fl2 res_vals) refs)
          (CONS (data_RefPtr bl1 p1) (CONS (data_RefPtr bl2 p2) (MAP FST vars))))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `S = CONS (data_RefPtr bl1 p1)
                    (CONS (data_RefPtr bl2 p2) (MAP FST (vars:(data_v#A)list)))` THEN
  SUBGOAL_THEN `!v. v IN all_vs (insert p2 (bvl_ByteArray fl2 res_vals) refs) S ==>
                    v IN all_vs refs S` MP_TAC THENL
   [REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; lookup_insert; COND_CASE_EQ;
                option_INJ; distinctness "bvl_ref"] THEN MESON_TAC[];
    REWRITE_TAC[blocks_unique_def] THEN MESON_TAC[]]);;

(* two byte arrays at the head of the stack of abs_ml_inv: their roots and *)
(* heap elements (the pointers are equal iff the references are)            *)
let MP7AUX_abs_two_bytes = prove
 (`!c b1 p1 b2 p2 stack refs r1 r2 roots (heap:mp7heap) be a sp sp1 gens limit ts
    fl1 vals1 fl2 vals2.
     abs_ml_inv c (CONS (data_RefPtr b1 p1) (CONS (data_RefPtr b2 p2) stack)) refs
       (CONS r1 (CONS r2 roots),heap,be,a,sp,sp1,gens) limit ts /\
     lookup p1 refs = SOME (bvl_ByteArray fl1 vals1) /\
     lookup p2 refs = SOME (bvl_ByteArray fl2 vals2) ==>
     ?k1 k2. r1 = Pointer k1 (wl_Word (word 0)) /\
             r2 = Pointer k2 (wl_Word (word 0)) /\
             ((p1 = p2) <=> (k1 = k2)) /\
             heap_lookup k1 heap =
               SOME (Bytes be fl1 vals1 (make_zeros vals1:(A word)list)) /\
             heap_lookup k2 heap =
               SOME (Bytes be fl2 vals2 (make_zeros vals2:(A word)list))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; LIST_REL_CONS1; ALL2] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!b p fl vals r.
     MEM (data_RefPtr b p) (CONS (data_RefPtr b1 p1) (CONS (data_RefPtr b2 p2) stack)) /\
     lookup p refs = SOME (bvl_ByteArray fl vals) /\
     v_inv c (data_RefPtr b p) refs (r,f,tf,heap:mp7heap) ==>
     p IN FDOM f /\ r = Pointer (FAPPLY f p) (wl_Word (word 0)) /\
     heap_lookup (FAPPLY f p) heap =
       SOME (Bytes be fl vals (make_zeros vals:(A word)list))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `v_inv c (data_RefPtr b p) refs (r,f,tf,heap:mp7heap)` THEN
    ASM_REWRITE_TAC[v_inv_def; option_INJ; distinctness "bvl_ref"; ref_ptr_annot_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bc_ref_inv c p refs (f,tf,heap:mp7heap,be)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[reachable_refs_def] THEN
      MAP_EVERY EXISTS_TAC [`data_RefPtr b p`; `p:num`] THEN
      ASM_REWRITE_TAC[get_refs_def; MEM; RTC_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; make_zeros_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`b1:bool`; `p1:num`; `fl1:bool`; `vals1:byte list`;
                  `r1:(A word_loc)heap_address`] th) THEN
    MP_TAC(SPECL [`b2:bool`; `p2:num`; `fl2:bool`; `vals2:byte list`;
                  `r2:(A word_loc)heap_address`] th)) THEN
  ASM_REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`FAPPLY (f:(num,num)fmap) p1`; `FAPPLY (f:(num,num)fmap) p2`] THEN
  ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f)
                 {a | isSomeDataElement (heap_lookup a (heap:mp7heap))}` THEN
  REWRITE_TAC[INJ] THEN ASM_MESON_TAC[]);;
(* word_heap of a heap with one element replaced by one of the same length:  *)
(* the element and a frame that does not depend on it                       *)
let MP7AUX_word_heap_SPLIT1 = prove
 (`!(curr:A word) (h1:mp7heap) (x:mp7el) h2 c.
     ?fr. !y. el_length y = el_length x ==>
          word_heap curr (APPEND h1 (CONS y h2)) c =
          word_el (word_add curr (word_mul bytes_in_word (word (heap_length h1)))) y c
          STAR fr`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `word_heap (curr:A word) (h1:mp7heap) c STAR
    word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length h1))))
                 (word_mul bytes_in_word (word (el_length (x:mp7el))))) (h2:mp7heap) c` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def] THEN
  REWRITE_TAC[MP7AUX_STAR_AC]);;
(* the same with a second, different element of the heap *)
let MP7AUX_word_heap_SPLIT2 = prove
 (`!(curr:A word) (h1:mp7heap) (x:mp7el) h2 c k1 x1.
     heap_lookup k1 (APPEND h1 (CONS x h2)) = SOME x1 /\ ~(k1 = heap_length h1) ==>
     ?fr. !y. el_length y = el_length x ==>
          word_heap curr (APPEND h1 (CONS y h2)) c =
          word_el (word_add curr (word_mul bytes_in_word (word k1))) x1 c STAR
          word_el (word_add curr (word_mul bytes_in_word (word (heap_length h1)))) y c
          STAR fr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `k1 < heap_length (h1:mp7heap)` THENL
   [SUBGOAL_THEN `heap_lookup k1 (h1:mp7heap) = SOME x1` MP_TAC THENL
     [ASM_MESON_TAC[heap_lookup_APPEND2]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g1:mp7heap`; `g2:mp7heap`] THEN STRIP_TAC THEN
    EXISTS_TAC `word_heap (curr:A word) (g1:mp7heap) c STAR
      word_heap (word_add (word_add curr (word_mul bytes_in_word (word k1)))
                   (word_mul bytes_in_word (word (el_length (x1:mp7el))))) (g2:mp7heap) c STAR
      word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))))
                   (word_mul bytes_in_word (word (el_length (x:mp7el))))) (h2:mp7heap) c` THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    REWRITE_TAC[word_heap_APPEND; word_heap_def] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_add (word_add (word_add (curr:A word)
                    (word_mul bytes_in_word (word (heap_length (g1:mp7heap)))))
                    (word_mul bytes_in_word (word (el_length (x1:mp7el)))))
                    (word_mul bytes_in_word (word (heap_length (g2:mp7heap)))) =
                  word_add curr (word_mul bytes_in_word
                    (word (heap_length (APPEND g1 (CONS x1 g2)))))`
      SUBST1_TAC THENL
     [REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; WORD_ADD] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[MP7AUX_STAR_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_lookup (k1 - heap_length (h1:mp7heap) - el_length (x:mp7el)) (h2:mp7heap) =
                SOME x1 /\ heap_length h1 + el_length x <= k1` MP_TAC THENL
   [UNDISCH_TAC `heap_lookup k1 (APPEND h1 (CONS x h2)) = SOME (x1:mp7el)` THEN
    ASM_SIMP_TAC[heap_lookup_APPEND1; ARITH_RULE `~(k < h) ==> h <= k`] THEN
    REWRITE_TAC[heap_lookup_def] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = h) /\ ~(k < h) ==> ~(k - h = 0)`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    POP_ASSUM MP_TAC THEN UNDISCH_TAC `~(k1 < heap_length (h1:mp7heap))` THEN
    SIMP_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP heap_lookup_SPLIT) ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g1:mp7heap`; `g2:mp7heap`] THEN STRIP_TAC THEN
  EXISTS_TAC `word_heap (curr:A word) (h1:mp7heap) c STAR
    word_heap (word_add (word_add curr (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))))
                 (word_mul bytes_in_word (word (el_length (x:mp7el))))) (g1:mp7heap) c STAR
    word_heap (word_add (word_add curr (word_mul bytes_in_word (word k1)))
                 (word_mul bytes_in_word (word (el_length (x1:mp7el))))) (g2:mp7heap) c` THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def] THEN
  SUBGOAL_THEN `word_add (word_add (word_add (curr:A word)
                  (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))))
                  (word_mul bytes_in_word (word (el_length (x:mp7el)))))
                  (word_mul bytes_in_word (word (heap_length (g1:mp7heap)))) =
                word_add curr (word_mul bytes_in_word (word k1))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `k1 = heap_length (h1:mp7heap) + el_length (x:mp7el) +
                       heap_length (g1:mp7heap)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[MP7AUX_STAR_AC]);;
(* word_el of a byte array element, with the same condition for a byte    *)
(* array of the same length                                                 *)
let MP7AUX_word_el_Bytes_eq = prove
 (`!(a:A word) be fl vals vals' (zs:(A word)list) c.
     LENGTH vals' = LENGTH vals ==>
     ?P. word_el a (Bytes be fl vals zs) c =
           set_sep_one (a, wl_Word (make_byte_header c fl (LENGTH vals))) STAR
           misc_word_list (word_add a bytes_in_word) (MAP wl_Word (write_bytes vals zs be))
           STAR cond P /\
         word_el a (Bytes be fl vals' zs) c =
           set_sep_one (a, wl_Word (make_byte_header c fl (LENGTH vals))) STAR
           misc_word_list (word_add a bytes_in_word) (MAP wl_Word (write_bytes vals' zs be))
           STAR cond P /\
         (P ==> decode_length c (make_byte_header c fl (LENGTH vals):A word) =
                  word (LENGTH zs) /\
                LENGTH zs < dimword(:A))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[data_to_word_memoryProof_Bytes_def; word_el_def; word_payload_def;
    LET_DEF; LET_END_DEF; LENGTH_MAP; LENGTH_write_bytes; misc_word_list_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_MAP; LENGTH_write_bytes] THEN
  EXISTS_TAC `LENGTH (zs:(A word)list) < 2 EXP (dimindex (:A) - 4) /\
    decode_length c (make_byte_header c fl (LENGTH (vals:byte list)):A word) =
    word (LENGTH zs) /\
    LENGTH vals + 2 EXP (if dimindex (:A) = 32 then 2 else 3) <
    2 EXP (data_to_word_config_len_size c + (if dimindex (:A) = 32 then 2 else 3))` THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP (dimindex (:A) - 4)` THEN
  ASM_REWRITE_TAC[dimword_def; LE_EXP] THEN ARITH_TAC);;
(* more separation logic automation: conditions cond b of STAR trees, and  *)
(* rotations that put chosen leaves in front                                *)
let mp7_is_cond tm =
  is_comb tm && is_const (rator tm) && fst(dest_const(rator tm)) = "cond";;
let mp7_misc_at a t =
  mp7_leaf_const t = "misc_word_list" && aconv (rand(rator t)) a;;
(* from P s with leaves cond b of P: the facts b and the assertion P' s     *)
(* without them                                                             *)
let rec mp7_sep_conds th =
  let p,s = dest_comb (concl th) in
  match filter mp7_is_cond (mp7_star_leaves p) with
    [] -> [th]
  | t::_ ->
      if aconv p t then [th] else
      let th1 = EQ_MP (AP_THM (mp7_star_rotate p t) s) th in
      let th2 = PURE_ONCE_REWRITE_RULE[cond_STAR] th1 in
      CONJUNCT1 th2 :: mp7_sep_conds (CONJUNCT2 th2);;
let MP7AUX_SEP_COND_TAC : tactic = fun (asl,w as g) ->
  let is_target th =
    try let p,s = dest_comb (concl th) in
        fst(dest_const(rator s)) = "fun2set" &&
        exists mp7_is_cond (mp7_star_leaves p)
    with Failure _ -> false in
  match filter (fun (_,th) -> is_target th) asl with
    [] -> ALL_TAC g
  | (_,th)::_ ->
      (UNDISCH_TAC (concl th) THEN DISCH_THEN(fun th' ->
         MAP_EVERY ASSUME_TAC (mp7_sep_conds th'))) g;;
(* goal Q s with a leaf cond b of Q: the goal b /\ Q' s *)
let MP7AUX_SEP_GOAL_COND_TAC : tactic = fun (asl,w as g) ->
  let q,s = dest_comb w in
  let t = find mp7_is_cond (mp7_star_leaves q) in
  (CONV_TAC(RATOR_CONV(K (mp7_star_rotate q t))) THEN
   PURE_ONCE_REWRITE_TAC[cond_STAR]) g;;
(* |- (t STAR rest) s from P s, for the first leaf t of P with f t *)
let mp7_sep_front f th =
  let p,s = dest_comb(concl th) in
  let t = find f (mp7_star_leaves p) in
  EQ_MP (AP_THM (mp7_star_rotate p t) s) th;;
(* |- ((t1 STAR t2) STAR rest) s from P s, for leaves t1 t2 of P (STAR is  *)
(* left associative: the form of a1 STAR a2 STAR frame)                     *)
let mp7_sep_front2 t1 t2 th =
  let p,s = dest_comb(concl th) in
  let ls = mp7_star_leaves p in
  let rec remove t l = match l with
      [] -> failwith "mp7_sep_front2"
    | h::r -> if aconv h t then r else h :: remove t r in
  let rest = remove t2 (remove t1 ls) in
  let star = rator(rator p) in
  let mk a b = mk_comb(mk_comb(star,a),b) in
  let q = mk (mk t1 t2) (end_itlist mk rest) in
  EQ_MP (AP_THM (AC MP7AUX_STAR_AC (mk_eq(p,q))) s) th;;
(* the memory part of memory_rel_xor_bytes: the heap with the second byte  *)
(* array in front of h2 and the first one at k1                             *)
let MP7AUX_xor_bytes_heap = prove
 (`!(h1:mp7heap) h2 a sp sp1 gens c st (m:A word -> A word_loc) dm limit k1 be
    fl1 vals1 fl2 vals2 res_vals.
     heap_in_memory_store
       (APPEND h1 (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2))
       a sp sp1 gens c st m dm limit /\
     heap_lookup k1
       (APPEND h1 (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2)) =
       SOME (Bytes be fl1 vals1 (make_zeros vals1:(A word)list)) /\
     (k1 = heap_length h1 ==> vals1 = vals2) /\
     xor_bytes vals1 vals2 = SOME res_vals /\ good_dimindex(:A) ==>
     ?curr x1 m1.
       FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
       m (word_add curr (word_mul bytes_in_word (word k1))) = wl_Word x1 /\
       word_add curr (word_mul bytes_in_word (word k1)) IN dm /\
       word_xor_bytes
         (word_add (word_add curr (word_mul bytes_in_word (word k1))) bytes_in_word)
         (word_add (word_add curr (word_mul bytes_in_word (word (heap_length h1))))
            bytes_in_word)
         (decode_length c x1) dm m = SOME m1 /\
       heap_in_memory_store
         (APPEND h1 (CONS (Bytes be fl2 res_vals (make_zeros vals2:(A word)list)) h2))
         a sp sp1 gens c st m1 dm limit`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (res_vals:byte list) = LENGTH (vals2:byte list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[xor_bytes_length]; ALL_TAC] THEN
  SUBGOAL_THEN `heap_length (APPEND (h1:mp7heap)
     (CONS (Bytes be fl2 res_vals (make_zeros vals2:(A word)list)) h2)) =
   heap_length (APPEND h1 (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2))`
   ASSUME_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_Bytes]; ALL_TAC] THEN
  UNDISCH_TAC `heap_in_memory_store
       (APPEND h1 (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2))
       a sp sp1 gens c st (m:A word -> A word_loc) dm limit` THEN
  ASM_REWRITE_TAC[heap_in_memory_store_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x1 m1.
       m (word_add curr (word_mul bytes_in_word (word k1))) = wl_Word x1 /\
       word_add curr (word_mul bytes_in_word (word k1)) IN dm /\
       word_xor_bytes
         (word_add (word_add curr (word_mul bytes_in_word (word k1))) bytes_in_word)
         (word_add (word_add curr (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))))
            bytes_in_word)
         (decode_length c x1) dm (m:A word -> A word_loc) = SOME m1 /\
       (word_heap curr
          (APPEND h1 (CONS (Bytes be fl2 res_vals (make_zeros vals2:(A word)list)) h2)) c STAR
        word_heap other (heap_expand limit) c) (fun2set (m1,dm))`
  MP_TAC THENL
  [ALL_TAC;
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`x1:A word`; `m1:A word -> A word_loc`] THEN STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`curr:A word`; `x1:A word`; `m1:A word -> A word_loc`] THEN
   ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC [`curr:A word`; `other:A word`] THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `el_length (Bytes be fl2 res_vals (make_zeros vals2:(A word)list)) =
                el_length (Bytes be fl2 vals2 (make_zeros vals2:(A word)list))` ASSUME_TAC THENL
   [REWRITE_TAC[el_length_Bytes]; ALL_TAC] THEN
  ASM_CASES_TAC `k1 = heap_length (h1:mp7heap)` THENL
   [(* the same byte array twice *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_eq(rand(concl th))
                            then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`curr:A word`; `h1:mp7heap`;
                   `Bytes be fl2 vals2 (make_zeros vals2:(A word)list)`;
                   `h2:mp7heap`; `c:data_to_word_config`] MP7AUX_word_heap_SPLIT1) THEN
    DISCH_THEN(X_CHOOSE_THEN `fr:(A word#A word_loc->bool)->bool` ASSUME_TAC) THEN
    MP_TAC(ISPECL
      [`word_add curr (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))):A word`;
       `be:bool`; `fl2:bool`; `vals2:byte list`; `res_vals:byte list`;
       `make_zeros vals2:(A word)list`; `c:data_to_word_config`]
      MP7AUX_word_el_Bytes_eq) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(word_heap curr
       (APPEND h1 (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2))
       c STAR word_heap other (heap_expand limit) c) (fun2set (m:A word -> A word_loc,dm))` THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) then
      REWRITE_TAC[MATCH_MP th
        (REFL `el_length (Bytes be fl2 vals2 (make_zeros vals2:(A word)list))`)]
      else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP7AUX_SEP_COND_TAC THEN MP7AUX_SEP_R_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_var(lhand(concl th)) &&
                               fst(dest_var(lhand(concl th))) = "P"
                            then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th ->
      if not (mp7_is_fun2set_th th) then NO_TAC else
      let th1 = mp7_sep_front (fun t -> mp7_leaf_const t = "misc_word_list") th in
      let fr = rand(rator(concl th1)) in
      MP_TAC(SPEC fr (ISPECL [`vals2:byte list`; `res_vals:byte list`;
        `m:A word->A word_loc`; `dm:A word->bool`;
        `word_add (word_add curr (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))))
           bytes_in_word:A word`;
        `be:bool`] xor_bytes_word_list_alias)) THEN
      ASM_REWRITE_TAC[th1]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`make_byte_header c fl2 (LENGTH (vals2:byte list)):A word`;
                          `m1:A word->A word_loc`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) then
      REWRITE_TAC[MATCH_MP th (ASSUME
        `el_length (Bytes be fl2 res_vals (make_zeros vals2:(A word)list)) =
         el_length (Bytes be fl2 vals2 (make_zeros vals2:(A word)list))`)]
      else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN MP7AUX_SEP_GOAL_COND_TAC THEN ASM_REWRITE_TAC[] THEN
    MP7AUX_SEP_AC_TAC;
    ALL_TAC] THEN
  (* two different byte arrays *)
  MP_TAC(ISPECL [`curr:A word`; `h1:mp7heap`;
                 `Bytes be fl2 vals2 (make_zeros vals2:(A word)list)`;
                 `h2:mp7heap`; `c:data_to_word_config`; `k1:num`;
                 `Bytes be fl1 vals1 (make_zeros vals1:(A word)list)`]
         MP7AUX_word_heap_SPLIT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fr:(A word#A word_loc->bool)->bool` ASSUME_TAC) THEN
  MP_TAC(ISPECL [`word_add curr (word_mul bytes_in_word (word k1)):A word`;
                 `be:bool`; `fl1:bool`; `vals1:byte list`; `vals1:byte list`;
                 `make_zeros vals1:(A word)list`; `c:data_to_word_config`]
         MP7AUX_word_el_Bytes_eq) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P1:bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
    [`word_add curr (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))):A word`;
     `be:bool`; `fl2:bool`; `vals2:byte list`; `res_vals:byte list`;
     `make_zeros vals2:(A word)list`; `c:data_to_word_config`]
    MP7AUX_word_el_Bytes_eq) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P2:bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(word_heap curr
     (APPEND h1 (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2))
     c STAR word_heap other (heap_expand limit) c) (fun2set (m:A word -> A word_loc,dm))` THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then
    REWRITE_TAC[MATCH_MP th
      (REFL `el_length (Bytes be fl2 vals2 (make_zeros vals2:(A word)list))`)]
    else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP7AUX_SEP_COND_TAC THEN MP7AUX_SEP_R_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_var(lhand(concl th)) &&
                                    mem (fst(dest_var(lhand(concl th)))) ["P1";"P2"]
                                 then MP_TAC th else NO_TAC) THEN
         ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  FIRST_ASSUM(fun th ->
    if not (mp7_is_fun2set_th th) then NO_TAC else
    let a1 = `word_add (word_add curr (word_mul bytes_in_word (word k1)))
                bytes_in_word:A word` in
    let a2 = `word_add (word_add curr (word_mul bytes_in_word
                (word (heap_length (h1:mp7heap))))) bytes_in_word:A word` in
    let ls = mp7_star_leaves (rator(concl th)) in
    let t1 = find (mp7_misc_at a1) ls and t2 = find (mp7_misc_at a2) ls in
    let th1 = mp7_sep_front2 t1 t2 th in
    let fr = rand(rator(concl th1)) in
    MP_TAC(SPEC fr (ISPECL [`vals1:byte list`; `vals2:byte list`; `res_vals:byte list`;
      `m:A word->A word_loc`; `dm:A word->bool`; a1; a2; `be:bool`]
      xor_bytes_word_list)) THEN
    ASM_REWRITE_TAC[th1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:A word->A word_loc` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`make_byte_header c fl1 (LENGTH (vals1:byte list)):A word`;
                        `m1:A word->A word_loc`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then
    REWRITE_TAC[MATCH_MP th (ASSUME
      `el_length (Bytes be fl2 res_vals (make_zeros vals2:(A word)list)) =
       el_length (Bytes be fl2 vals2 (make_zeros vals2:(A word)list))`)]
    else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN MP7AUX_SEP_GOAL_COND_TAC THEN ASM_REWRITE_TAC[] THEN
  MP7AUX_SEP_GOAL_COND_TAC THEN ASM_REWRITE_TAC[] THEN
  MP7AUX_SEP_AC_TAC);;
(* a byte array at the head of the stack of abs_ml_inv: its root and heap  *)
(* element                                                                  *)
let MP7AUX_abs_bytes = prove
 (`!c b p stack refs r roots (heap:mp7heap) be a sp sp1 gens limit ts fl vals.
     abs_ml_inv c (CONS (data_RefPtr b p) stack) refs
       (CONS r roots,heap,be,a,sp,sp1,gens) limit ts /\
     lookup p refs = SOME (bvl_ByteArray fl vals) ==>
     ?k. r = Pointer k (wl_Word (word 0)) /\
         heap_lookup k heap = SOME (Bytes be fl vals (make_zeros vals:(A word)list))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; LIST_REL_CONS1; ALL2] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `v_inv c (data_RefPtr b p) refs (r,f,tf,heap:mp7heap)` THEN
  ASM_REWRITE_TAC[v_inv_def; option_INJ; distinctness "bvl_ref"; ref_ptr_annot_def] THEN
  STRIP_TAC THEN EXISTS_TAC `FAPPLY (f:(num,num)fmap) p` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bc_ref_inv c p refs (f,tf,heap:mp7heap,be)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[reachable_refs_def] THEN
    MAP_EVERY EXISTS_TAC [`data_RefPtr b p`; `p:num`] THEN
    ASM_REWRITE_TAC[get_refs_def; MEM; RTC_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; make_zeros_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF]);;

(* HOL4 line 18668 *)
let memory_rel_xor_bytes = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl1 p1 v1 bl2 p2 v2 vars fl1
    vals1 fl2 vals2 res_vals.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr bl1 p1,v1:A word_loc)
             (CONS (data_RefPtr bl2 p2,v2:A word_loc) vars)) /\
     lookup p1 refs = SOME (bvl_ByteArray fl1 vals1) /\
     lookup p2 refs = SOME (bvl_ByteArray fl2 vals2) /\
     xor_bytes vals1 vals2 = SOME res_vals /\
     good_dimindex (:A)
     ==>
     ?w1 a1 w2 a2 x1 m1.
       v1 = wl_Word w1 /\
       v2 = wl_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       m a1 = wl_Word x1 /\ a1 IN dm /\
       word_xor_bytes (word_add a1 bytes_in_word) (word_add a2 bytes_in_word)
         (decode_length c x1) dm m = SOME m1 /\
       memory_rel c be ts (insert p2 (bvl_ByteArray fl2 res_vals) refs) sp st m1 dm
         (CONS (data_RefPtr bl1 p1,v1:A word_loc)
               (CONS (data_RefPtr bl2 p2,v2:A word_loc) vars))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (res_vals:byte list) = LENGTH (vals2:byte list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[xor_bytes_length]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[memory_rel_def; word_ml_inv_def; MAP] o
                MATCH_MP memory_rel_swap) THEN
  DISCH_THEN(X_CHOOSE_THEN `heap:mp7heap` (X_CHOOSE_THEN `limit:num`
    (X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `sp0:num` (X_CHOOSE_THEN `sp1:num`
    (X_CHOOSE_THEN `gens:gen_state` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `hs:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)
       STRIP_ASSUME_TAC)))))))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL2" with _ -> false)) THEN
  REWRITE_TAC[LIST_REL_CONS2] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(A word_loc)heap_address` (X_CHOOSE_THEN `t2:((A word_loc)heap_address)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r1:(A word_loc)heap_address` (X_CHOOSE_THEN `rest:((A word_loc)heap_address)list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `bl2:bool`; `p2:num`; `bl1:bool`; `p1:num`;
    `MAP FST (vars:(data_v#A word_loc)list)`; `refs:(data_v bvl_ref)spt`;
    `r2:(A word_loc)heap_address`; `r1:(A word_loc)heap_address`;
    `rest:((A word_loc)heap_address)list`; `heap:mp7heap`; `be:bool`; `a:num`; `sp0:num`;
    `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`; `fl2:bool`; `vals2:byte list`;
    `fl1:bool`; `vals1:byte list`] MP7AUX_abs_two_bytes) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `k1:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `bl2:bool`; `p2:num`;
    `CONS (data_RefPtr bl1 p1) (MAP FST (vars:(data_v#A word_loc)list))`;
    `refs:(data_v bvl_ref)spt`;
    `CONS (r2:(A word_loc)heap_address) (CONS r1 rest)`; `heap:mp7heap`; `be:bool`; `a:num`;
    `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`; `fl2:bool`;
    `vals2:byte list`; `res_vals:byte list`] update_byte_ref_thm) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list` (X_CHOOSE_THEN `h1:mp7heap`
    (X_CHOOSE_THEN `h2:mp7heap` (X_CHOOSE_THEN `ws:(A word)list` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `k2 = heap_length (h1:mp7heap)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "CONS" with _ -> false))) THEN
    REWRITE_TAC[CONS_11; injectivity "heap_address"] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Bytes be fl2 vals2 ws = Bytes be fl2 vals2 (make_zeros vals2:(A word)list)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `heap_lookup k2 (heap:mp7heap) = SOME (Bytes be fl2 vals2 (make_zeros vals2:(A word)list))` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX; option_INJ];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th)) &&
    mem (fst(dest_var(lhs(concl th)))) ["k2";"r1";"r2"]))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `bl2:bool`; `p2:num`;
    `CONS (data_RefPtr bl1 p1) (MAP FST (vars:(data_v#A word_loc)list))`;
    `insert p2 (bvl_ByteArray fl2 res_vals) (refs:(data_v bvl_ref)spt)`;
    `Pointer (heap_length (h1:mp7heap)) (wl_Word (word 0:A word))`;
    `CONS (Pointer k1 (wl_Word (word 0:A word))) rest`;
    `APPEND (APPEND h1 [Bytes be fl2 res_vals ws]) (h2:mp7heap)`; `be:bool`; `a:num`;
    `sp0:num`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`; `fl2:bool`;
    `res_vals:byte list`] MP7AUX_abs_bytes) THEN
  ASM_REWRITE_TAC[lookup_insert; injectivity "heap_address"; UNWIND_THM1] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX; option_INJ] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `make_zeros res_vals:(A word)list = make_zeros vals2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[make_zeros_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhs(concl th)) &&
    fst(dest_var(lhs(concl th))) = "heap")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
      mp7_leaf_const(lhs(concl th)) = "Bytes" && rand(lhs(concl th)) = `ws:(A word)list` &&
      rand(rator(lhs(concl th))) = `vals2:byte list`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_comb(lhs(concl th)) &&
      mp7_leaf_const(lhs(concl th)) = "Bytes" && rand(lhs(concl th)) = `ws:(A word)list`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_addr_def]) THEN
  FIRST_ASSUM(fun th -> if concl th = `make_zeros res_vals:(A word)list = make_zeros vals2`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  MP_TAC(ISPECL [`h1:mp7heap`; `h2:mp7heap`; `a:num`; `sp0:num`; `sp1:num`;
    `gens:gen_state`; `c:data_to_word_config`; `st:(store_name,A word_loc)fmap`;
    `m:A word -> A word_loc`; `dm:A word->bool`; `limit:num`; `k1:num`; `be:bool`;
    `fl1:bool`; `vals1:byte list`; `fl2:bool`; `vals2:byte list`; `res_vals:byte list`]
    MP7AUX_xor_bytes_heap) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2:num = p1` SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lookup p1 (refs:(data_v bvl_ref)spt) = SOME (bvl_ByteArray fl1 vals1)` THEN
    ASM_REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `curr:A word` (X_CHOOSE_THEN `x1:A word`
    (X_CHOOSE_THEN `m1:A word -> A word_loc` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `heap_length (APPEND (h1:mp7heap) (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2))
    <= dimword (:A) DIV 2 EXP shift_length c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> mp7_leaf_const(concl th) = "heap_in_memory_store" &&
      vfree_in `m:A word -> A word_loc` (concl th))) THEN
    REWRITE_TAC[heap_in_memory_store_def] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`get_addr c k1 (wl_Word (word 0)):A word`;
    `word_add curr (word_mul bytes_in_word (word k1)):A word`;
    `get_addr c (heap_length (h1:mp7heap)) (wl_Word (word 0)):A word`;
    `word_add curr (word_mul bytes_in_word (word (heap_length (h1:mp7heap)))):A word`;
    `x1:A word`; `m1:A word -> A word_loc`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && mem (fst(dest_var(rhs(concl th)))) ["v1";"v2"]))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`APPEND (h1:mp7heap) (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2)`;
    `c:data_to_word_config`; `k1:num`; `Bytes be fl1 vals1 (make_zeros vals1:(A word)list)`;
    `st:(store_name,A word_loc)fmap`; `curr:A word`; `wl_Word (word 0:A word)`]
    get_real_addr_get_addr) THEN
  MP_TAC(ISPECL [`APPEND (h1:mp7heap) (CONS (Bytes be fl2 vals2 (make_zeros vals2:(A word)list)) h2)`;
    `c:data_to_word_config`; `heap_length (h1:mp7heap)`;
    `Bytes be fl2 vals2 (make_zeros vals2:(A word)list)`;
    `st:(store_name,A word_loc)fmap`; `curr:A word`; `wl_Word (word 0:A word)`]
    get_real_addr_get_addr) THEN
  ASM_REWRITE_TAC[heap_lookup_PREFIX] THEN
  REWRITE_TAC[WORD_MUL_SYM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC memory_rel_swap THEN REWRITE_TAC[memory_rel_def; word_ml_inv_def; MAP] THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (h1:mp7heap) (CONS (Bytes be fl2 res_vals (make_zeros vals2:(A word)list)) h2)`;
    `limit:num`; `a:num`; `sp0:num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (Pointer (heap_length (h1:mp7heap)) (wl_Word (word 0:A word)))
                (CONS (Pointer k1 (wl_Word (word 0:A word))) rest)` THEN
  ASM_REWRITE_TAC[ALL2; word_addr_def]);;

(* HOL4 line 18962 *)
let word_str_cmp_loop_def = cake_def_wf
  `measure (\p:A word#A word#A word#A word#A word#(A word->bool)#
               (A word->A word_loc)#bool#num.
              SND (SND (SND (SND (SND (SND (SND (SND p))))))))`
  TERM_TAC
  `word_str_cmp_loop (a1:A word) (a2:A word) r1 r2 (len:A word) dm m be ck =
     if ck = 0 then NONE else
     if len = bytes_in_word then
       SOME (r1,r2)
     else
       match mem_load_byte_aux m dm be a1 with NONE -> NONE | SOME b1 ->
       match mem_load_byte_aux m dm be a2 with NONE -> NONE | SOME b2 ->
         if b1 = b2 then
           word_str_cmp_loop (word_add a1 (word 1)) (word_add a2 (word 1)) r1 r2
             (word_sub len (word 1)) dm m be (ck - 1)
         else
           SOME (word_zx b1:A word,word_zx b2:A word)`;;
let word_str_cmp_loop_ind = cake_ind "word_str_cmp_loop";;

(* HOL4 line 18976 *)
let word_str_cmp_def = cake_def
  `word_str_cmp b (a1:A word) (a2:A word) dm (m:A word -> A word_loc) be c =
     let k = (dimindex (:A) - data_to_word_config_len_size c) -
             backend_common_word_shift (:A) in
     if a1 IN dm /\ a2 IN dm /\ isWord (m a1) /\ isWord (m a2) then
       let l1 = word_ushr (theWord (m a1)) k in
       let l2 = word_ushr (theWord (m a2)) k in
       if b then
         (if ~(l1 = l2) then SOME (l1,l2) else
            word_str_cmp_loop (word_add a1 bytes_in_word) (word_add a2 bytes_in_word)
              l1 l1 l1 dm m be (dimword (:A)))
       else
         (let l = word (MIN (val l1) (val l2)) in
          word_str_cmp_loop (word_add a1 bytes_in_word) (word_add a2 bytes_in_word)
            l1 l2 l dm m be (dimword (:A)))
     else NONE`;;

(* HOL4 line 18991 (r1 and r2 have independent word types, as in HOL4) *)
let find_diff_def = cake_def
  `(find_diff [] [] (r1:A word) (r2:B word) = (r1,r2)) /\
   (find_diff (CONS (x:byte) xs) (CONS y ys) r1 r2 =
      if x = y then find_diff xs ys r1 r2 else (word_zx x,word_zx y))`;;
let find_diff_ind = cake_ind "find_diff";;

(* HOL4 line 18996 *)
let word_str_loop_thm = prove
 (`!k (a1:A word) a2 r1 r2 dm m be d vals1 vals2.
     (!i. i < LENGTH vals1 ==>
          mem_load_byte_aux m dm be (word_add a1 (word i)) = SOME (EL i vals1)) /\
     (!i. i < LENGTH vals2 ==>
          mem_load_byte_aux m dm be (word_add a2 (word i)) = SOME (EL i vals2)) /\
     k <= LENGTH vals1 /\
     k <= LENGTH vals2 /\
     k < d /\ d <= dimword (:A)
     ==>
     word_str_cmp_loop a1 a2 r1 r2 (word_add (word k) bytes_in_word:A word) dm m be d =
     SOME (find_diff (TAKE k vals1) (TAKE k vals2) r1 r2)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[word_str_cmp_loop_def] THEN
  SUBGOAL_THEN `~(d = 0)` (fun th -> REWRITE_TAC[th]) THEN TRY ASM_ARITH_TAC THENL
   [REWRITE_TAC[WORD_ADD_0; TAKE_0; find_diff_def]; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_add (word (SUC k)) bytes_in_word = bytes_in_word:A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[WORD_RULE `word_add x b = b <=> x = word 0:A word`] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN
    MP_TAC(SPEC `SUC k` (INST_TYPE [`:A`,`:A`] MP7AUX_VAL_WORD_LT)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  CASES_ON `vals1:byte list` THEN CASES_ON `vals2:byte list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `SUC k <= 0`)) THEN ARITH_TAC) THEN
  ALL_TAC THEN
  SUBGOAL_THEN `mem_load_byte_aux (m:A word->A word_loc) dm be (a1:A word) = SOME a0 /\
                mem_load_byte_aux m dm be (a2:A word) = SOME a0'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `!i. i < SUC (LENGTH (a1':byte list)) ==>
        mem_load_byte_aux (m:A word->A word_loc) dm be (word_add (a1:A word) (word i)) =
        SOME (EL i (CONS (a0:byte) a1'))`;
      UNDISCH_TAC `!i. i < SUC (LENGTH (a1'':byte list)) ==>
        mem_load_byte_aux (m:A word->A word_loc) dm be (word_add (a2:A word) (word i)) =
        SOME (EL i (CONS (a0':byte) a1''))`] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[WORD_ADD_0; EL; HD; LT_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[TAKE_DEF; NOT_SUC; SUC_SUB1; find_diff_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_sub (word_add (word (SUC k)) bytes_in_word) (word 1):A word =
                word_add (word k) bytes_in_word` SUBST1_TAC THENL
   [REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `!i. i < SUC (LENGTH (a1':byte list)) ==>
        mem_load_byte_aux (m:A word->A word_loc) dm be (word_add (a1:A word) (word i)) =
        SOME (EL i (CONS (a0:byte) a1'))` THEN
    SUBGOAL_THEN `word_add (word_add (a1:A word) (word 1)) (word i) =
                  word_add a1 (word (SUC i))` SUBST1_TAC THENL
     [REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `SUC i`) THEN ASM_REWRITE_TAC[LT_SUC; EL; TL];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `!i. i < SUC (LENGTH (a1'':byte list)) ==>
        mem_load_byte_aux (m:A word->A word_loc) dm be (word_add (a2:A word) (word i)) =
        SOME (EL i (CONS (a0':byte) a1''))` THEN
    SUBGOAL_THEN `word_add (word_add (a2:A word) (word 1)) (word i) =
                  word_add a2 (word (SUC i))` SUBST1_TAC THENL
     [REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `SUC i`) THEN ASM_REWRITE_TAC[LT_SUC; EL; TL];
    ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* compare_aux is unchanged by a common first character *)
let MP7AUX_compare_aux_cons = prove
 (`!len start z s1 s2 r.
     compare_aux (implode (CONS z s1)) (implode (CONS z s2)) r (start + 1) len =
     compare_aux (implode s1) (implode s2) r start len`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[compare_aux_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; strsub_def; GSYM ADD1; EL; TL] THEN
  ASM_REWRITE_TAC[ADD1]);;

(* HOL4 line 19029 (HOL4 name compoare_aux_append_xs, sic) *)
let compoare_aux_append_xs = prove
 (`!zs z xs ys r.
     LENGTH xs <= LENGTH ys ==>
     compare_aux (implode (CONS z (APPEND zs xs)))
                 (implode (CONS z (APPEND zs ys))) r (LENGTH zs + 1) (LENGTH xs) =
     compare_aux (implode (APPEND zs xs)) (implode (APPEND zs ys)) r (LENGTH zs)
       (LENGTH xs)`,
  REWRITE_TAC[MP7AUX_compare_aux_cons]);;

(* HOL4 line 19045 (HOL4 name compoare_aux_append_ys, sic) *)
let compoare_aux_append_ys = prove
 (`!zs z xs ys r.
     LENGTH ys <= LENGTH xs ==>
     compare_aux (implode (CONS z (APPEND zs xs)))
                 (implode (CONS z (APPEND zs ys))) r (LENGTH zs + 1) (LENGTH ys) =
     compare_aux (implode (APPEND zs xs)) (implode (APPEND zs ys)) r (LENGTH zs)
       (LENGTH ys)`,
  REWRITE_TAC[MP7AUX_compare_aux_cons]);;

let MP7AUX_compare_aux_cons0 = prove
 (`!n x s1 s2 r.
     compare_aux (implode (CONS x s1)) (implode (CONS x s2)) r 0 (SUC n) =
     compare_aux (implode s1) (implode s2) r 0 n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [compare_aux_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; strsub_def; EL; HD; char_lt_def; LT_REFL] THEN
  REWRITE_TAC[MP7AUX_compare_aux_cons]);;

(* HOL4 line 19061 *)
let compare_same = prove
 (`!x xs ys.
     mlstring_compare (implode (CONS x xs)) (implode (CONS x ys)) =
     mlstring_compare (implode xs) (implode ys)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mlstring_compare_def; strlen_def; LENGTH; LT_SUC; MP7AUX_compare_aux_cons0]);;

(* HOL4 line 19077 *)
let str_cmp_cons = prove
 (`!b cmp x xs ys.
     str_cmp b cmp (implode (CONS x xs)) (implode (CONS x ys)) =
     str_cmp b cmp (implode xs) (implode ys)`,
  GEN_TAC THEN GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN CASES_ON `cmp:opb` THEN
  REWRITE_TAC[str_cmp_def; fast_lt_def; fast_le_def; fast_gt_def; fast_ge_def;
              mlstring_lt_def; mlstring_le_def; mlstring_gt_def; mlstring_ge_def;
              compare_same; strlen_def; LENGTH; SUC_INJ; LT_SUC; LE_SUC; GT; GE]);;

(* compare of two strings whose first characters differ *)
let MP7AUX_compare_diff = prove
 (`!c1 c2 s1 s2. ~(c1 = c2) ==>
     mlstring_compare (implode (CONS c1 s1)) (implode (CONS c2 s2)) =
     if char_lt c1 c2 then LESS else GREATER`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlstring_compare_def; strlen_def; LENGTH; LT_SUC] THEN
  ONCE_REWRITE_TAC[compare_aux_def] THEN
  REWRITE_TAC[NOT_SUC; strsub_def; EL; HD] THEN
  SUBGOAL_THEN `char_lt c1 c2 <=> ~char_lt c2 c1` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[char_lt_def] THEN UNDISCH_TAC `~(c1:char = c2)` THEN
    REWRITE_TAC[GSYM ORD_11] THEN ARITH_TAC;
    ASM_CASES_TAC `char_lt c2 c1` THEN ASM_REWRITE_TAC[COND_ID]]);;
let MP7AUX_ORD_CHR_VAL = prove
 (`!h:byte. ORD (CHR (val h)) = val h`,
  GEN_TAC THEN MATCH_MP_TAC ORD_CHR_RWT THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;
let MP7AUX_CHR_VAL_11 = prove
 (`!h h':byte. CHR (val h) = CHR (val h') <=> h = h'`,
  MESON_TAC[MP7AUX_ORD_CHR_VAL; VAL_EQ]);;
let MP7AUX_VAL_WORD_ZX_BYTE = prove
 (`!h:byte. good_dimindex(:A) ==> val(word_zx h:A word) = val h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; DIMINDEX_8] THEN
  ARITH_TAC);;
let MP7AUX_str_cmp_T_diff = prove
 (`!cmp (h:byte) h' (t:byte list) (t':byte list).
     ~(h = h') /\ LENGTH t = LENGTH t' ==>
     (str_cmp T cmp (implode (CONS (CHR (val h)) (MAP (CHR o val) t)))
                    (implode (CONS (CHR (val h')) (MAP (CHR o val) t'))) <=>
      num_cmp cmp (val h) (val h'))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(CHR (val (h:byte)) = CHR (val (h':byte)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MP7AUX_CHR_VAL_11]; ALL_TAC] THEN
  SUBGOAL_THEN `~(val (h:byte) = val (h':byte))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ]; ALL_TAC] THEN
  CASES_ON `cmp:opb` THEN
  ASM_SIMP_TAC[str_cmp_def; fast_lt_def; fast_le_def; fast_gt_def; fast_ge_def;
               mlstring_lt_def; mlstring_le_def; mlstring_gt_def; mlstring_ge_def;
               MP7AUX_compare_diff; strlen_def; LENGTH; LENGTH_MAP; num_cmp_def;
               char_lt_def; MP7AUX_ORD_CHR_VAL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "ordering"] THEN ASM_ARITH_TAC);;

(* HOL4 line 19090 *)
let find_diff_str_cmp_thm1 = prove
 (`!l cmp vals1 vals2.
     LENGTH (vals1:byte list) = LENGTH (vals2:byte list) /\
     good_dimindex (:A) ==>
     ?(r1:A word) (r2:A word).
       find_diff vals1 vals2 (word l) (word l) = (r1,r2) /\
       (str_cmp T cmp (implode (MAP (CHR o val) vals1))
                      (implode (MAP (CHR o val) vals2)) <=>
        num_cmp cmp (val r1) (val r2))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  CASES_ON `vals2:byte list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ARITH_RULE `~(0 = SUC n)`] THEN STRIP_TAC THENL
   [REWRITE_TAC[find_diff_def; PAIR_EQ; MAP] THEN
    MAP_EVERY EXISTS_TAC [`word l:A word`; `word l:A word`] THEN REWRITE_TAC[] THEN
    CASES_ON `cmp:opb` THEN
    REWRITE_TAC[str_cmp_def; fast_lt_def; fast_le_def; fast_gt_def; fast_ge_def;
                mlstring_lt_def; mlstring_le_def; mlstring_gt_def; mlstring_ge_def;
                mlstring_compare_def; strlen_def; LENGTH; LT_REFL; num_cmp_def] THEN
    ONCE_REWRITE_TAC[compare_aux_def] THEN REWRITE_TAC[distinctness "ordering"] THEN
    ARITH_TAC;
    REWRITE_TAC[find_diff_def; MAP; o_THM] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[str_cmp_cons] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`word_zx (h:byte):A word`; `word_zx (a0:byte):A word`] THEN
      ASM_SIMP_TAC[MP7AUX_VAL_WORD_ZX_BYTE] THEN
      MATCH_MP_TAC MP7AUX_str_cmp_T_diff THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 19118 *)
let MIN_SUC_SUC = prove
 (`!m n. MIN (SUC m) (SUC n) = SUC (MIN m n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MIN; LE_SUC] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* compare with an empty string *)
let MP7AUX_compare_nil = prove
 (`(!s. mlstring_compare (implode []) (implode s) = if s = [] then EQUAL else LESS) /\
   (!c s. mlstring_compare (implode (CONS c s)) (implode []) = GREATER)`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL [CASES_ON `s:char list`; ALL_TAC] THEN
  REWRITE_TAC[mlstring_compare_def; strlen_def; LENGTH; LT_0; CONJUNCT1 LT; LT_REFL;
              NOT_CONS_NIL] THEN
  ONCE_REWRITE_TAC[compare_aux_def] THEN REWRITE_TAC[]);;

(* HOL4 line 19124 (HOL4 has the markers Abbrev (l1 = ...) and Abbrev (l2 = *)
(* ...); the port has no Abbrev constant: the plain equations)              *)
let find_diff_str_cmp_thm2 = prove
 (`!cmp k vals1 vals2 l1 l2.
     l1 = LENGTH vals1 + 2 EXP backend_common_word_shift (:A) /\
     l2 = LENGTH vals2 + 2 EXP backend_common_word_shift (:A) /\
     k + l1 < dimword (:A) /\ k + l2 < dimword (:A) /\ good_dimindex (:A)
     ==>
     ?(r1:A word) (r2:A word).
       find_diff (TAKE (MIN (LENGTH vals1) (LENGTH vals2)) (vals1:byte list))
                 (TAKE (MIN (LENGTH vals1) (LENGTH vals2)) vals2)
                 (word (k + l1))
                 (word (k + l2)) = (r1,r2) /\
       (str_cmp F cmp (implode (MAP (CHR o val) vals1))
                      (implode (MAP (CHR o val) vals2)) <=>
        num_cmp cmp (val r1) (val r2))`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!vals1 k vals2.
      k + LENGTH vals1 + 2 EXP backend_common_word_shift (:A) < dimword (:A) /\
      k + LENGTH vals2 + 2 EXP backend_common_word_shift (:A) < dimword (:A) /\
      good_dimindex (:A) ==>
      ?(r1:A word) (r2:A word).
        find_diff (TAKE (MIN (LENGTH vals1) (LENGTH vals2)) (vals1:byte list))
                  (TAKE (MIN (LENGTH vals1) (LENGTH vals2)) vals2)
                  (word (k + LENGTH vals1 + 2 EXP backend_common_word_shift (:A)))
                  (word (k + LENGTH vals2 + 2 EXP backend_common_word_shift (:A))) =
        (r1,r2) /\
        (str_cmp F cmp (implode (MAP (CHR o val) vals1))
                       (implode (MAP (CHR o val) vals2)) <=>
         num_cmp cmp (val r1) (val r2))`
   (fun th -> REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC th THEN
              ASM_MESON_TAC[]) THEN
  ABBREV_TAC `e = 2 EXP backend_common_word_shift (:A)` THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MP7AUX_DIMWORD_32) THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `MIN 0 n = 0`; TAKE_0; find_diff_def; PAIR_EQ; MAP] THEN
  MAP_EVERY EXISTS_TAC [`word (k + 0 + e):A word`;
                        `word (k + LENGTH (vals2:byte list) + e):A word`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `val (word (k + 0 + e):A word) = k + 0 + e /\
                val (word (k + LENGTH (vals2:byte list) + e):A word) =
                k + LENGTH vals2 + e` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MP7AUX_VAL_WORD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CASES_ON `cmp:opb` THEN
  REWRITE_TAC[str_cmp_def; mlstring_lt_def; mlstring_le_def; mlstring_gt_def;
              mlstring_ge_def; MP7AUX_compare_nil; MAP_EQ_NIL; num_cmp_def; GT; GE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; distinctness "ordering"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM LENGTH_EQ_NIL]) THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
  CASES_ON `vals2:byte list` THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  REWRITE_TAC[LENGTH; MAP; o_THM] THENL
   [REWRITE_TAC[ARITH_RULE `MIN n 0 = 0`; TAKE_0; find_diff_def; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`word (k + SUC (LENGTH (t:byte list)) + e):A word`;
                          `word (k + 0 + e):A word`] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (word (k + SUC (LENGTH (t:byte list)) + e):A word) =
                  k + SUC (LENGTH t) + e /\
                  val (word (k + 0 + e):A word) = k + 0 + e`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MP7AUX_VAL_WORD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CASES_ON `cmp:opb` THEN
    REWRITE_TAC[str_cmp_def; mlstring_lt_def; mlstring_le_def; mlstring_gt_def;
                mlstring_ge_def; MP7AUX_compare_nil; num_cmp_def; GT; GE;
                distinctness "ordering"] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MIN_SUC_SUC; TAKE_DEF; NOT_SUC; SUC_SUB1; find_diff_def] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[str_cmp_cons] THEN
    SUBGOAL_THEN `k + SUC (LENGTH (t:byte list)) + e = (k + 1) + LENGTH t + e /\
                  k + SUC (LENGTH (a1:byte list)) + e = (k + 1) + LENGTH a1 + e`
      (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`word_zx (h:byte):A word`; `word_zx (a0:byte):A word`] THEN
  ASM_SIMP_TAC[MP7AUX_VAL_WORD_ZX_BYTE] THEN
  SUBGOAL_THEN `~(CHR (val (h:byte)) = CHR (val (a0:byte)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MP7AUX_CHR_VAL_11]; ALL_TAC] THEN
  SUBGOAL_THEN `~(val (h:byte) = val (a0:byte))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ]; ALL_TAC] THEN
  CASES_ON `cmp:opb` THEN
  ASM_SIMP_TAC[str_cmp_def; mlstring_lt_def; mlstring_le_def; mlstring_gt_def;
               mlstring_ge_def; MP7AUX_compare_diff; num_cmp_def; char_lt_def;
               MP7AUX_ORD_CHR_VAL; GT; GE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "ordering"] THEN ASM_ARITH_TAC]);;

(* the length field of a byte array header (memory_rel_ByteArray_IMP) *)
let MP7AUX_byte_header_len = prove
 (`!x ls L. good_dimindex(:A) /\
     (if dimindex (:A) = 32 then
        L + 4 < 2 EXP (dimindex (:A) - 3) /\
        word_ushr x (dimindex (:A) - ls - 2) = word (L + 4)
      else
        L + 8 < 2 EXP (dimindex (:A) - 3) /\
        word_ushr x (dimindex (:A) - ls - 3) = word (L + 8):A word) ==>
     word_ushr x ((dimindex(:A) - ls) - backend_common_word_shift(:A)) =
       word (L + 2 EXP backend_common_word_shift(:A)) /\
     L + 2 EXP backend_common_word_shift(:A) < 2 EXP (dimindex(:A) - 3) /\
     bytes_in_word:A word = word (2 EXP backend_common_word_shift(:A))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def;
    bytes_in_word_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `if dimindex (:A) = 32 then
        L + 4 < 2 EXP (dimindex (:A) - 3) /\
        word_ushr x (dimindex (:A) - ls - 2) = word (L + 4)
      else
        L + 8 < 2 EXP (dimindex (:A) - 3) /\
        word_ushr x (dimindex (:A) - ls - 3) = word (L + 8):A word` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* HOL4 line 19183 (the unused bound variables x1 m1 of HOL4 are left out) *)
let memory_rel_str_cmp = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl1 p1 v1 bl2 p2 v2 vars fl1
    vals1 fl2 vals2 b cmp.
     memory_rel c be ts refs sp st m dm
       (CONS (data_RefPtr bl1 p1,v1:A word_loc)
             (CONS (data_RefPtr bl2 p2,v2:A word_loc) vars)) /\
     lookup p1 refs = SOME (bvl_ByteArray fl1 vals1) /\
     lookup p2 refs = SOME (bvl_ByteArray fl2 vals2) /\
     good_dimindex (:A)
     ==>
     ?w1 a1 w2 a2 r1 r2.
       v1 = wl_Word w1 /\
       v2 = wl_Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       word_str_cmp b a1 a2 dm m be c = SOME (r1,r2) /\
       (str_cmp b cmp (implode (MAP (CHR o val) vals1))
                      (implode (MAP (CHR o val) vals2)) <=>
        num_cmp cmp (val r1) (val r2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP memory_rel_tl) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl1:bool`; `p1:num`; `v1:A word_loc`;
    `CONS (data_RefPtr bl2 p2,v2:A word_loc) vars`; `fl1:bool`; `vals1:byte list`]
    memory_rel_ByteArray_IMP) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `refs:(data_v bvl_ref)spt`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word -> A word_loc`; `dm:A word->bool`;
    `bl2:bool`; `p2:num`; `v2:A word_loc`;
    `vars:(data_v#A word_loc)list`; `fl2:bool`; `vals2:byte list`]
    memory_rel_ByteArray_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:A word` (X_CHOOSE_THEN `a2:A word` (X_CHOOSE_THEN `x2:A word` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `a1:A word` (X_CHOOSE_THEN `x1:A word` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`w1:A word`; `a1:A word`; `w2:A word`; `a2:A word`] THEN
  ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; word_str_cmp_def; isWord_def; theWord_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  W(fun (asl,w) ->
     let gd = ASSUME `good_dimindex(:A)` in
     let ths = mapfilter (fun (_,th) -> MATCH_MP MP7AUX_byte_header_len (CONJ gd th)) asl in
     MAP_EVERY STRIP_ASSUME_TAC ths) THEN
  ABBREV_TAC `e = 2 EXP backend_common_word_shift (:A)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (vals1:byte list) + e < dimword(:A) /\
                LENGTH (vals2:byte list) + e < dimword(:A)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def] THEN CONJ_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP (dimindex(:A) - 3)` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MP7AUX_VAL_WORD_LT] THEN
  SUBGOAL_THEN `(word (LENGTH (vals1:byte list) + e):A word = word (LENGTH (vals2:byte list) + e)) <=>
                LENGTH vals1 = LENGTH vals2` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[MP7AUX_VAL_WORD_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[EXP_EQ_0; LT_NZ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k r1 r2. k <= LENGTH (vals1:byte list) /\ k <= LENGTH (vals2:byte list) ==>
     word_str_cmp_loop (word_add a1 (word e)) (word_add a2 (word e)) r1 r2
       (word (k + e):A word) dm m be (dimword(:A)) =
     SOME (find_diff (TAKE k vals1) (TAKE k vals2) r1 r2)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `word_add a1 bytes_in_word:A word`;
      `word_add a2 bytes_in_word:A word`; `r1:A word`; `r2:A word`; `dm:A word->bool`;
      `m:A word->A word_loc`; `be:bool`; `dimword(:A)`; `vals1:byte list`;
      `vals2:byte list`] word_str_loop_thm) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[GSYM WORD_ADD]];
    ALL_TAC] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THENL
   [ASM_CASES_TAC `LENGTH (vals1:byte list) = LENGTH (vals2:byte list)` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[LE_REFL] THEN
      SUBGOAL_THEN `TAKE (LENGTH (vals2:byte list)) (vals1:byte list) = vals1 /\
                    TAKE (LENGTH vals2) vals2 = vals2` (fun th -> REWRITE_TAC[th]) THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `LENGTH (vals1:byte list) = LENGTH (vals2:byte list)`)) THEN
        REWRITE_TAC[TAKE_LENGTH_ID] THEN
        FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th =
          `LENGTH (vals1:byte list) = LENGTH (vals2:byte list)`)) THEN
        REWRITE_TAC[TAKE_LENGTH_ID];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`LENGTH (vals2:byte list) + e`; `cmp:opb`; `vals1:byte list`;
                     `vals2:byte list`] (INST_TYPE [`:A`,`:A`] find_diff_str_cmp_thm1)) THEN
      ASM_REWRITE_TAC[option_INJ];
      MAP_EVERY EXISTS_TAC [`word (LENGTH (vals1:byte list) + e):A word`;
                            `word (LENGTH (vals2:byte list) + e):A word`] THEN
      ASM_SIMP_TAC[MP7AUX_VAL_WORD_LT] THEN
      CASES_ON `cmp:opb` THEN
      ASM_REWRITE_TAC[str_cmp_def; fast_lt_def; fast_le_def; fast_gt_def; fast_ge_def;
                      strlen_def; LENGTH_MAP; num_cmp_def; GT; GE] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `MIN (a + e) (b + e) = MIN a b + e`] THEN
  ASM_SIMP_TAC[ARITH_RULE `MIN a b <= a`; ARITH_RULE `MIN a b <= b`] THEN
  MP_TAC(ISPECL [`cmp:opb`; `0`; `vals1:byte list`; `vals2:byte list`;
                 `LENGTH (vals1:byte list) + e`; `LENGTH (vals2:byte list) + e`]
         (INST_TYPE [`:A`,`:A`] find_diff_str_cmp_thm2)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; option_INJ]);;
