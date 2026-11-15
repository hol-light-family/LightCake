(* ========================================================================= *)
(* data_to_word_memoryProof_p3: part 3 of 7 (HOL4 lines 5514-8234) of the    *)
(* port of HOL4 compiler/backend/proofs/data_to_word_memoryProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p7 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_memoryProof.ml needs the last.                *)
(* MP3AUX_ names are local helpers of this part.                            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_memoryProof_p2.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 3: HOL4 lines 5514-8234 ===== *)

(* MP3AUX: apply ttac to (MP_TAC) the newest assumption whose head        *)
(* constant is c, removing it                                              *)
let MP3AUX_ASM_HEAD_TAC c ttac =
  FIRST_X_ASSUM(fun th ->
    let h = fst(strip_comb(concl th)) in
    if is_const h && fst(dest_const h) = c then ttac th else NO_TAC);;

let MP3AUX_ASM_HEAD_MP_TAC c = MP3AUX_ASM_HEAD_TAC c MP_TAC;;

(* HOL4 line 5514 *)
let v_inv_BlockRep_upd = prove
 (`!conf v1 refs (x:(A word_loc)heap_address) f tf hp hp2 pp tg zss.
     v_inv conf v1 refs (x,f,tf,hp) /\
     heap_lookup pp hp = SOME (BlockRep tg zss) /\
     (!t. t IN FDOM tf ==> ~(FAPPLY tf t = pp)) /\
     (!m y. ~(m = pp) /\ heap_lookup m hp = SOME y ==>
            heap_lookup m hp2 = SOME y) ==>
     v_inv conf v1 refs (x,f,tf,hp2)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC v_inv_BlockRep_upd_lemma THEN
  MAP_EVERY EXISTS_TAC
   [`hp:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
         heap_element)list`; `pp:num`; `tg:num`;
    `zss:((A word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[]);;

(* MP3AUX: replacing a non-thunk reference by a non-thunk reference does  *)
(* not change dest_thunk                                                   *)
let MP3AUX_dest_thunk_insert_nonthunk = prove
 (`!v refs ptr (r:data_v bvl_ref) r0.
     lookup ptr refs = SOME r0 /\ (!ev x. ~(r0 = bvl_Thunk ev x)) /\
     (!ev x. ~(r = bvl_Thunk ev x)) ==>
     data_dest_thunk v (insert ptr r refs) = data_dest_thunk v refs`,
  GEN_TAC THEN CASES_ON `v:data_v` THEN REWRITE_TAC[data_dest_thunk_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `r:data_v bvl_ref` THEN CASES_ON `r0:data_v bvl_ref` THEN
  SIMP[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5522 *)
let v_inv_MutBlock_hole_lemma = prove
 (`!conf ptr tag fin1 fin2 ll cv1 cv2 rr ck v1 refs (y:(A word_loc)heap_address)
    f tf heap.
     v_inv conf v1 refs (y,f,tf,heap) /\
     lookup ptr refs = SOME (MutBlock tag fin1 ll cv1 rr) ==>
     v_inv_ck ck conf v1 (insert ptr (MutBlock tag fin2 ll cv2 rr) refs)
       (y,f,tf,heap)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`v1:data_v`,`v1:data_v`) THEN
  SPEC_TAC(`y:(A word_loc)heap_address`,`y:(A word_loc)heap_address`) THEN
  SPEC_TAC(`ck:num`,`ck:num`) THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `ck:num` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[v_inv_ck_cases] THEN CASES_ON `v1:data_v` THEN
  REWRITE_TAC[v_inv_def] THEN SIMP[] THENL
   [(* Number *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    (* Block *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:((A word_loc)heap_address)list`; `ptr':num`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MP3AUX_ASM_HEAD_MP_TAC "ALL2" THEN MATCH_MP_TAC MONO_ALL2 THEN
    BETA_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    (* RefPtr *)
    SUBGOAL_THEN
     `!v. data_dest_thunk v (insert ptr (MutBlock tag fin2 ll cv2 rr) refs) =
          data_dest_thunk v (refs:(data_v bvl_ref)spt)` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MP3AUX_dest_thunk_insert_nonthunk THEN
      EXISTS_TAC `MutBlock tag fin1 ll cv1 rr:data_v bvl_ref` THEN
      ASM_REWRITE_TAC[] THEN SIMP[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [SIMP[] THEN MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`ev:thunk_mode`; `v:data_v`; `y':(A word_loc)heap_address`] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 5542 *)
let v_inv_MutBlock_hole = prove
 (`!cnf vv rfs (yy:(A word_loc)heap_address) ff tff hp pp tg b1 b2 l1 c1 c2 r1.
     v_inv cnf vv rfs (yy,ff,tff,hp) /\
     lookup pp rfs = SOME (MutBlock tg b1 l1 c1 r1) ==>
     v_inv cnf vv (insert pp (MutBlock tg b2 l1 c2 r1) rfs) (yy,ff,tff,hp)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC v_inv_MutBlock_hole_lemma THEN
  MAP_EVERY EXISTS_TAC [`b1:bool`; `c1:data_v`] THEN ASM_REWRITE_TAC[]);;

(* MP3AUX: blocks_unique is antimonotone in the set of values *)
let MP3AUX_blocks_unique_SUBSET = prove
 (`!ts vs vs'. blocks_unique ts vs /\ vs' SUBSET vs ==> blocks_unique ts vs'`,
  REWRITE_TAC[blocks_unique_def; SUBSET] THEN MESON_TAC[]);;

(* MP3AUX: the values of all_vs after an insert into refs *)
let MP3AUX_IN_all_vs_insert = prove
 (`!v refs ptr (x:data_v bvl_ref) stack.
     v IN all_vs (insert ptr x refs) stack ==>
     v IN all_vs refs stack \/
     (?l. x = bvl_ValueArray l /\ MEM v (v_all_vs l)) \/
     (?ev y. x = bvl_Thunk ev y /\ MEM v (v_all_vs [y])) \/
     (?tg fin l c r. x = MutBlock tg fin l c r /\
                     MEM v (v_all_vs (APPEND (APPEND l [c]) r)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; lookup_insert] THEN
  STRIP_TAC THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ASM_REWRITE_TAC[]] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 5551 *)
let blocks_unique_update_mutblock = prove
 (`!ptr refs tag fin l cv r ts h stack.
     lookup ptr refs = SOME (MutBlock tag fin l cv r) /\
     blocks_unique ts (all_vs refs (CONS h (CONS (data_RefPtr F ptr) stack))) ==>
     blocks_unique ts
       (all_vs (insert ptr (MutBlock tag fin l h r) refs)
          (CONS h (CONS (data_RefPtr F ptr) stack)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP3AUX_blocks_unique_SUBSET THEN
  EXISTS_TAC `all_vs refs (CONS h (CONS (data_RefPtr F ptr) stack))` THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:data_v` THEN
  DISCH_THEN(MP_TAC o MATCH_MP MP3AUX_IN_all_vs_insert) THEN
  SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[v_all_vs_append; MEM_APPEND]) THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THENL
  [DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
   MAP_EVERY EXISTS_TAC [`ptr:num`; `tag:num`; `fin:bool`; `l:data_v list`;
                         `cv:data_v`; `r:data_v list`] THEN
   ASM_REWRITE_TAC[v_all_vs_append; MEM_APPEND];
   REPEAT DISJ2_TAC THEN MATCH_MP_TAC MEM_v_all_vs_extend_tl THEN ASM_REWRITE_TAC[];
   DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
   MAP_EVERY EXISTS_TAC [`ptr:num`; `tag:num`; `fin:bool`; `l:data_v list`;
                         `cv:data_v`; `r:data_v list`] THEN
   ASM_REWRITE_TAC[v_all_vs_append; MEM_APPEND]]);;

(* HOL4 line 5568 *)
let ref_edge_MutBlock_UPDATE = prove
 (`!ptr refs tg fin ll cc rr h r1 z.
     lookup ptr refs = SOME (MutBlock tg fin ll cc rr) /\
     ref_edge (insert ptr (MutBlock tg fin ll h rr) refs) r1 z /\
     ~MEM z (get_refs h) ==> ref_edge refs r1 z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ref_edge_MutBlock] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ref_edge_def] THEN
  SIMP[get_refs_def; MAP_APPEND; FLAT_APPEND; MEM_APPEND; MAP; FLAT; APPEND_NIL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[get_refs_def; MAP_APPEND; FLAT_APPEND; MEM_APPEND;
                              MAP; FLAT; APPEND_NIL]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 5579 *)
let reachable_refs_MutBlock_UPDATE = prove
 (`!ptr refs tg fin ll cc rr h b stack n.
     lookup ptr refs = SOME (MutBlock tg fin ll cc rr) /\
     reachable_refs (CONS h (CONS (data_RefPtr b ptr) stack))
       (insert ptr (MutBlock tg fin ll h rr) refs) n ==>
     reachable_refs (CONS h (CONS (data_RefPtr b ptr) stack)) refs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def] THEN STRIP_TAC THEN
  ASM_CASES_TAC `?m. MEM m (get_refs h) /\ RTC (ref_edge refs) m n` THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x:data_v`; `r:num`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!r z. RTC (ref_edge (insert ptr (MutBlock tg fin ll h rr) refs)) r z
                      ==> z = n ==> RTC (ref_edge refs) r n`
    (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT_R THEN CONJ_TAC THENL [MESON_TAC[RTC_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_MESON_TAC[RTC_CASES_R; ref_edge_MutBlock_UPDATE]);;

(* MP3AUX: the heap elements of the references are data elements *)
let MP3AUX_isSomeDataElement_refs = prove
 (`(!zs:((A word_loc)heap_address)list.
      isSomeDataElement (SOME (RefBlock zs:((A word_loc,
         data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))) /\
   (!tg zs:((A word_loc)heap_address)list.
      isSomeDataElement (SOME (BlockRep tg zs:((A word_loc,
         data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))) /\
   (!ev z:(A word_loc)heap_address.
      isSomeDataElement (SOME (ThunkBlock ev z:((A word_loc,
         data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))) /\
   (!be fl bs ws:(A word)list.
      isSomeDataElement (SOME (Bytes be fl bs ws)))`,
  REWRITE_TAC[isSomeDataElement_def; RefBlock_def; BlockRep_def; ThunkBlock_def;
              data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF;
              option_INJ] THEN
  MESON_TAC[]);;

(* MP3AUX: bc_ref_inv of a reference whose cell, heap block and values are *)
(* unchanged (the common last step of the update and allocation theorems) *)
let MP3AUX_bc_ref_inv_transfer = prove
 (`!conf n refs refs' f f' tf tf'
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) heap' be.
     bc_ref_inv conf n refs (f,tf,heap,be) /\
     n IN FDOM f' /\ FAPPLY f' n = FAPPLY f n /\
     lookup n refs' = lookup n refs /\
     (isSomeDataElement (heap_lookup (FAPPLY f n) heap) ==>
      heap_lookup (FAPPLY f n) heap' = heap_lookup (FAPPLY f n) heap) /\
     (!v. data_dest_thunk v refs = data_NotThunk ==>
          data_dest_thunk v refs' = data_NotThunk) /\
     (!t. t IN FDOM tf' ==> t IN FDOM tf /\ FAPPLY tf' t = FAPPLY tf t) /\
     (!v y. (?r. lookup n refs = SOME r /\ find_ref r v) /\
            v_inv conf v refs (y,f,tf,heap) ==>
            v_inv conf v refs' (y,f',tf',heap'))
     ==> bc_ref_inv conf n refs' (f',tf',heap',be)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN
  ASM_CASES_TAC `n IN FDOM (f:(num,num)fmap)` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `lookup n (refs:(data_v bvl_ref)spt)` THEN ASM_REWRITE_TAC[option_CASE] THEN
  CASES_ON `a:data_v bvl_ref` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; UNWIND_THM1; find_ref_def]) THENL
   [STRIP_TAC THEN EXISTS_TAC `zs:((A word_loc)heap_address)list` THEN
    ASM_SIMP_TAC[MP3AUX_isSomeDataElement_refs] THEN
    MP3AUX_ASM_HEAD_MP_TAC "ALL2" THEN MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN
    BETA_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MP3AUX_isSomeDataElement_refs];
    STRIP_TAC THEN EXISTS_TAC `z:(A word_loc)heap_address` THEN
    ASM_SIMP_TAC[MP3AUX_isSomeDataElement_refs];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE]) THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `zs:((A word_loc)heap_address)list` THEN
    ASM_SIMP_TAC[MP3AUX_isSomeDataElement_refs] THEN
    MP3AUX_ASM_HEAD_MP_TAC "ALL2" THEN MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN
    BETA_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* MP3AUX: v_inv with tf restricted to the timestamps of the state *)
let MP3AUX_v_inv_restrict = prove
 (`!conf v refs stack (y:(A word_loc)heap_address) f tf heap.
     v_inv conf v refs (y,f,tf,heap) /\ v IN all_vs refs stack ==>
     v_inv conf v refs (y,f,DRESTRICT tf (all_ts refs stack),heap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_tf_restrict THEN
  EXISTS_TAC `stack:data_v list` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MEM_in_all_ts]);;

(* MP3AUX: the values held by a reference are in all_vs *)
let MP3AUX_IN_all_vs_find_ref = prove
 (`!n refs r v stack.
     lookup n refs = SOME r /\ find_ref r v ==> v IN all_vs refs stack`,
  REPEAT GEN_TAC THEN CASES_ON `r:data_v bvl_ref` THEN
  REWRITE_TAC[find_ref_def; all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`n:num`; `a:data_v list`];
    DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `a0:thunk_mode`; `a1:data_v`];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `a0:num`; `a1:bool`; `a2:data_v list`;
                          `a3:data_v`; `a4:data_v list`]] THEN
  ASM_SIMP_TAC[MEM_v_all_vs; MEM]);;

(* MP3AUX: the timestamp map restricted to a set keeps its invariants *)
let MP3AUX_DRESTRICT_tf = prove
 (`!(tf:(num,num)fmap) P s ts.
     INJ (FAPPLY tf) (FDOM tf) s /\ FDOM tf SUBSET {n | n < ts} ==>
     INJ (FAPPLY (DRESTRICT tf P)) (FDOM (DRESTRICT tf P)) s /\
     FDOM (DRESTRICT tf P) SUBSET P /\
     FDOM (DRESTRICT tf P) SUBSET {n | n < ts} /\
     (!t. t IN FDOM (DRESTRICT tf P) ==>
          t IN FDOM tf /\ FAPPLY (DRESTRICT tf P) t = FAPPLY tf t)`,
  REWRITE_TAC[INJ; DRESTRICT_DEF; IN_INTER; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* MP3AUX: the elements around the hole of APPEND (APPEND l [c]) r *)
let MP3AUX_EL_APPEND_MID = prove
 (`(!(l:A list) c r. EL (LENGTH l) (APPEND (APPEND l [c]) r) = c) /\
   (!(l:A list) c c' r i.
      ~(i = LENGTH l) ==>
      EL i (APPEND (APPEND l [c]) r) = EL i (APPEND (APPEND l [c']) r))`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i - LENGTH (l:A list) = SUC (i - LENGTH l - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]);;

(* HOL4 line 5609 *)
let update_mutblock_thm = prove
 (`!conf h ptr stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts tag l cv r.
     abs_ml_inv conf (CONS h (CONS (data_RefPtr F ptr) stack)) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     lookup ptr refs = SOME (MutBlock tag F l cv r) ==>
     ?p rr roots2 vs1 heap2 u.
       roots = CONS rr (CONS (Pointer p u) roots2) /\
       heap_lookup p heap = SOME (BlockRep tag vs1) /\
       LENGTH vs1 = LENGTH l + 1 + LENGTH r /\
       heap_store p [BlockRep tag (LUPDATE rr (LENGTH l) vs1)] heap = (heap2,T) /\
       abs_ml_inv conf (CONS h (CONS (data_RefPtr F ptr) stack))
         (insert ptr (MutBlock tag F l h r) refs)
         (roots,heap2,be,a,sp,sp1,gens) limit ts`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN
  MP3AUX_ASM_HEAD_TAC "ALL2" (STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1]) THEN
  RVEQ_TAC THEN BETA_TAC) THEN
  (MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC) THEN
  (SUBGOAL_THEN `reachable_refs (CONS h (CONS (data_RefPtr F ptr) stack)) refs ptr`
   ASSUME_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN EXISTS_TAC `data_RefPtr F ptr` THEN
    EXISTS_TAC `ptr:num` THEN REWRITE_TAC[MEM; get_refs_def; RTC_REFL];
    ALL_TAC]) THEN
  (FIRST_ASSUM(MP_TAC o SPEC `ptr:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[bc_ref_inv_def; FLOOKUP_DEF]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (MP_TAC(ISPECL [`zs:((A word_loc)heap_address)list`;
                 `LUPDATE (h':(A word_loc)heap_address) (LENGTH (l:data_v list)) zs`;
                 `FAPPLY (f:(num,num)fmap) ptr`; `tag:num`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`] heap_store_BlockRep) THEN
  ASM_REWRITE_TAC[LENGTH_LUPDATE] THEN STRIP_TAC) THEN
  (MAP_EVERY EXISTS_TAC [`zs:((A word_loc)heap_address)list`;
   `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (zs:((A word_loc)heap_address)list) = LENGTH (l:data_v list) + 1 + LENGTH (r:data_v list)`
   ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP EVERY2_LENGTH) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN ASM_REWRITE_TAC[roots_ok_def]; ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "heap_ok" MP_TAC THEN REWRITE_TAC[heap_ok_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`xs:((A word_loc)heap_address)list`; `n0:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `p0:num`; `u0:A word_loc`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
      DISJ_CASES_TAC (MATCH_MP th th2))) THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BlockRep_def; injectivity "heap_element"]) THEN
    UNDISCH_TAC `MEM (Pointer p0 u0) (xs:((A word_loc)heap_address)list)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP MEM_LUPDATE_E) THENL
     [MP3AUX_ASM_HEAD_TAC "roots_ok" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN
      ASM_MESON_TAC[MEM];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`zs:((A word_loc)heap_address)list`;
        `LENGTH (zs:((A word_loc)heap_address)list)`;
        `(BlockTag tag, []:(A word_loc)list)`; `u0:A word_loc`] THEN
      REWRITE_TAC[GSYM BlockRep_def] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC heap_lookup_MEM THEN
      EXISTS_TAC `FAPPLY (f:(num,num)fmap) ptr` THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "gc_kind_inv" MP_TAC THEN REWRITE_TAC[gc_kind_inv_def] THEN
    CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "unused_space_inv" MP_TAC THEN
    REWRITE_TAC[unused_space_inv_def] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      DISCH_TAC THEN
      ASM_MESON_TAC[option_INJ; BlockRep_def; distinctness "heap_element"];
      MATCH_MP_TAC data_up_to_heap_store THEN
      MAP_EVERY EXISTS_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `FAPPLY (f:(num,num)fmap) ptr`;
        `BlockRep tag (LUPDATE (h':(A word_loc)heap_address) (LENGTH (l:data_v list)) zs):((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`] THEN
      ASM_REWRITE_TAC[BlockRep_def; isDataElement_def] THEN MESON_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!v (y:(A word_loc)heap_address).
      v_inv conf v refs (y,f,tf,heap) /\
      v IN all_vs (insert ptr (MutBlock tag F l h r) refs)
             (CONS h (CONS (data_RefPtr F ptr) stack)) ==>
      v_inv conf v (insert ptr (MutBlock tag F l h r) refs)
        (y,f,DRESTRICT tf (all_ts (insert ptr (MutBlock tag F l h r) refs)
                                  (CONS h (CONS (data_RefPtr F ptr) stack))),heap2)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MP3AUX_v_inv_restrict THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC v_inv_MutBlock_hole THEN
    MAP_EVERY EXISTS_TAC [`F`; `cv:data_v`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC v_inv_BlockRep_upd THEN
    MAP_EVERY EXISTS_TAC
     [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `FAPPLY (f:(num,num)fmap) ptr`; `tag:num`; `zs:((A word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE]) THEN
    ASM_MESON_TAC[];
    ALL_TAC]) THEN
  (EXISTS_TAC `f:(num,num)fmap` THEN
  EXISTS_TAC `DRESTRICT (tf:(num,num)fmap)
    (all_ts (insert ptr (MutBlock tag F l h r) refs)
            (CONS h (CONS (data_RefPtr F ptr) stack)))` THEN
  MP_TAC(ISPECL [`tf:(num,num)fmap`;
    `all_ts (insert ptr (MutBlock tag F l h r) refs)
            (CONS h (CONS (data_RefPtr F ptr) stack))`;
    `{a | isSomeDataElement (heap_lookup a (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list))}`;
    `ts:num`] MP3AUX_DRESTRICT_tf) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INSERT] THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_update_mutblock THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  (CONJ_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN REWRITE_TAC[MEM];
      REWRITE_TAC[v_inv_def] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[lookup_insert] THEN
      SIMP[];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack
                     (t'':((A word_loc)heap_address)list)` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM]];
    ALL_TAC]) THEN
  (X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_CASES_TAC `n:num = ptr` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN
    ASM_REWRITE_TAC[lookup_insert] THEN CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE]) THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `LUPDATE (h':(A word_loc)heap_address) (LENGTH (l:data_v list)) zs` THEN
    ASM_REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_LUPDATE; LENGTH_APPEND; LENGTH] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[EL_LUPDATE] THEN
    ASM_CASES_TAC `i = LENGTH (l:data_v list)` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[MP3AUX_EL_APPEND_MID; ARITH_RULE `x < x + 1 + y`] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN REWRITE_TAC[MEM];
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`l:data_v list`; `h:data_v`; `cv:data_v`; `r:data_v list`;
                       `i:num`] (CONJUNCT2 MP3AUX_EL_APPEND_MID)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `ALL2 (\z y. v_inv conf y refs (z,f,tf,heap))
                       (zs:((A word_loc)heap_address)list) (APPEND (APPEND l [cv]) r)` THEN
        REWRITE_TAC[LIST_REL_EL_EQN] THEN BETA_TAC THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC MP3AUX_IN_all_vs_find_ref THEN
        MAP_EVERY EXISTS_TAC [`ptr:num`; `MutBlock tag F l h r:data_v bvl_ref`] THEN
        REWRITE_TAC[lookup_insert; find_ref_def] THEN MATCH_MP_TAC EL_MEM THEN
        REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC]];
    ALL_TAC]) THEN
  (MATCH_MP_TAC MP3AUX_bc_ref_inv_transfer THEN
  MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC reachable_refs_MutBlock_UPDATE THEN ASM_MESON_TAC[];
    REWRITE_TAC[isSomeDataElement_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`f:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`]
      INJ_NEQ) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `v:data_v` THEN
    MP_TAC(ISPECL [`v:data_v`; `refs:(data_v bvl_ref)spt`; `ptr:num`;
      `MutBlock tag F l h r:data_v bvl_ref`; `MutBlock tag F l cv r:data_v bvl_ref`]
      MP3AUX_dest_thunk_insert_nonthunk) THEN
    ANTS_TAC THENL [SIMP[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP3AUX_IN_all_vs_find_ref THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[lookup_insert] THEN ASM_MESON_TAC[]]));;

(* HOL4 line 5813 *)
let LENGTH_write_bytes = prove
 (`!ws:(A word)list bs be. LENGTH (write_bytes bs ws be) = LENGTH ws`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[write_bytes_def; LENGTH; LET_DEF; LET_END_DEF]);;
let _ = cake_add_simps [LENGTH_write_bytes];;

(* HOL4 line 5819 *)
let LIST_REL_IMP_LIST_REL = prove
 (`!(P:A->B->bool) Q xs ys.
     (!x y. MEM x xs ==> P x y ==> Q x y) ==>
     ALL2 P xs ys ==> ALL2 Q xs ys`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5827 *)
let v_size_LESS_EQ = prove
 (`!l x. MEM x l ==> data_v_size x <= list_size data_v_size l`,
  MESON_TAC[MEM_list_size]);;

(* MP3AUX: replacing a heap element by one of the same length changes the *)
(* lookup only at its own address                                          *)
let MP3AUX_heap_lookup_replace = prove
 (`!ha hb (x:(A,B)heap_element) y p.
     el_length x = el_length y ==>
     heap_lookup p (APPEND ha (CONS y hb)) =
     if p = heap_length ha then SOME y
     else heap_lookup p (APPEND ha (CONS x hb))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND; heap_lookup_def] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p < heap_length (ha:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `p = heap_length (ha:((A,B)heap_element)list)` THEN
    ASM_REWRITE_TAC[SUB_REFL] THEN
    SUBGOAL_THEN `~(p - heap_length (ha:((A,B)heap_element)list) = 0)`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

(* MP3AUX: the heap blocks that v_inv looks up are not byte arrays *)
let MP3AUX_Bytes_distinct = prove
 (`(!i be fl bs ws:(A word)list. ~(Bignum i = Bytes be fl bs ws)) /\
   (!w be fl bs ws:(A word)list. ~(Word64Rep (:A) w = Bytes be fl bs ws)) /\
   (!ev (x:(A word_loc)heap_address) be fl bs ws:(A word)list.
      ~(ThunkBlock ev x = Bytes be fl bs ws)) /\
   (!tag (xs:((A word_loc)heap_address)list) be fl bs ws:(A word)list.
      ~(BlockRep tag xs = Bytes be fl bs ws))`,
  REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF;
              data_to_word_memoryProof_Bignum_def; Word64Rep_def; ThunkBlock_def;
              BlockRep_def] THEN
  REPEAT STRIP_TAC THENL
   [POP_ASSUM MP_TAC THEN
    SPEC_TAC(`i2mw i:bool#(A word)list`,`p:bool#(A word)list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN SIMP[];
    POP_ASSUM MP_TAC THEN SIMP[];
    POP_ASSUM MP_TAC THEN SIMP[]]);;

(* MP3AUX: a lookup that does not find the byte array is the same after *)
(* the byte array is updated                                             *)
let MP3AUX_heap_lookup_Bytes = prove
 (`!ha hb be fl (xs:byte list) ys (ws:(A word)list) p X.
     heap_lookup p (APPEND (APPEND ha [Bytes be fl xs ws]) hb) = SOME X /\
     (!bs. ~(X = Bytes be fl bs ws)) ==>
     heap_lookup p (APPEND (APPEND ha [Bytes be fl ys ws]) hb) = SOME X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  MP_TAC(ISPECL [`ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                     heap_element)list`; `hb:((A word_loc,data_to_word_memoryProof_tag#
                     (A word_loc)list)heap_element)list`;
                 `Bytes be fl xs (ws:(A word)list)`; `Bytes be fl ys (ws:(A word)list)`;
                 `p:num`] MP3AUX_heap_lookup_replace) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF;
                el_length_def; LENGTH_write_bytes]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND; LT_REFL; SUB_REFL] THEN
    REWRITE_TAC[heap_lookup_def; option_INJ] THEN MESON_TAC[];
    MESON_TAC[]]);;

(* HOL4 line 5834 *)
let v_inv_IMP_lemma = prove
 (`!conf ha be fl (xs:byte list) ys (ws:(A word)list) hb ck w refs x f tf.
     v_inv conf w refs (x,f,tf,APPEND (APPEND ha [Bytes be fl xs ws]) hb) ==>
     v_inv_ck ck conf w refs (x,f,tf,APPEND (APPEND ha [Bytes be fl ys ws]) hb)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`w:data_v`,`w:data_v`) THEN
  SPEC_TAC(`x:(A word_loc)heap_address`,`x:(A word_loc)heap_address`) THEN
  SPEC_TAC(`ck:num`,`ck:num`) THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `ck:num` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[v_inv_ck_cases] THEN CASES_ON `w:data_v` THEN
  REWRITE_TAC[v_inv_def] THEN SIMP[] THENL
   [(* Number *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MP3AUX_heap_lookup_Bytes; MP3AUX_Bytes_distinct];
    (* Word64 *)
    ASM_MESON_TAC[MP3AUX_heap_lookup_Bytes; MP3AUX_Bytes_distinct];
    (* Block *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs':((A word_loc)heap_address)list`; `ptr:num`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      MP3AUX_ASM_HEAD_MP_TAC "ALL2" THEN MATCH_MP_TAC MONO_ALL2 THEN
      BETA_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MP3AUX_heap_lookup_Bytes; MP3AUX_Bytes_distinct]];
    (* RefPtr *)
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`; `y:(A word_loc)heap_address`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MP3AUX_heap_lookup_Bytes; MP3AUX_Bytes_distinct];
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
        ASM_REWRITE_TAC[]];
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 5869 *)
let v_inv_IMP = prove
 (`!conf refs be fl (xs:byte list) ys (ws:(A word)list) hb y x f tf ha.
     v_inv conf y refs (x,f,tf,APPEND (APPEND ha [Bytes be fl xs ws]) hb) ==>
     v_inv conf y refs (x,f,tf,APPEND (APPEND ha [Bytes be fl ys ws]) hb)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC v_inv_IMP_lemma THEN EXISTS_TAC `xs:byte list` THEN
  ASM_REWRITE_TAC[]);;

(* MP3AUX: heap_split after replacing an element by one of the same length *)
let MP3AUX_heap_split_replace = prove
 (`!ha n hb (x:(A,B)heap_element) y h1 h2.
     el_length x = el_length y /\
     heap_split n (APPEND ha (CONS x hb)) = SOME (h1,h2) ==>
     ?h1' h2'. heap_split n (APPEND ha (CONS y hb)) = SOME (h1',h2') /\
               (!e. MEM e h1' ==> MEM e h1 \/ e = y)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[heap_split_def] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[MEM];
    ALL_TAC;
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[MEM];
    ALL_TAC] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `heap_split (n - el_length (y:(A,B)heap_element))
                (hb:((A,B)heap_element)list)` THEN
    ASM_REWRITE_TAC[distinctness "option"; option_CASE] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    SIMP[MEM] THEN MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `heap_split (n - el_length (h:(A,B)heap_element))
                (APPEND t (CONS (x:(A,B)heap_element) hb))` THEN
    ASM_REWRITE_TAC[distinctness "option"; option_CASE] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n - el_length (h:(A,B)heap_element)`;
      `hb:((A,B)heap_element)list`; `x:(A,B)heap_element`; `y:(A,B)heap_element`;
      `x':((A,B)heap_element)list`; `h2:((A,B)heap_element)list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
    CASE_REWRITE_TAC[] THEN SIMP[MEM] THEN ASM_MESON_TAC[]]);;

(* MP3AUX: gen_start_ok after a byte array is overwritten *)
let MP3AUX_gen_start_ok_Bytes = prove
 (`!k s ha be fl (xs:byte list) ys (ws:(A word)list) hb.
     gen_start_ok (APPEND (APPEND ha [Bytes be fl xs ws]) hb) k s ==>
     gen_start_ok (APPEND (APPEND ha [Bytes be fl ys ws]) hb) k s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_start_ok_def; GSYM APPEND_ASSOC; APPEND] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                     heap_element)list`; `s:num`; `hb:((A word_loc,data_to_word_memoryProof_tag#
                     (A word_loc)list)heap_element)list`;
                 `Bytes be fl xs (ws:(A word)list)`; `Bytes be fl ys (ws:(A word)list)`;
                 `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
                 `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`]
     MP3AUX_heap_split_replace) THEN
  ASM_REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF;
                  el_length_def; LENGTH_write_bytes] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`h1':((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `h2':((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME
    `MEM (DataElement xs' l d) (h1':((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list)`)) THENL
   [ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "heap_element"]) THEN ASM_MESON_TAC[MEM]]);;

(* HOL4 line 5877 *)
let gen_state_ok_update_byte = prove
 (`!a k ha be fl (xs:byte list) ys (ws:(A word)list) hb gens.
     gen_state_ok a k (APPEND (APPEND ha [Bytes be fl xs ws]) hb) gens ==>
     gen_state_ok a k (APPEND (APPEND ha [Bytes be fl ys ws]) hb) gens`,
  REPEAT GEN_TAC THEN CASES_ON `gens:gen_state` THEN
  REWRITE_TAC[gen_state_ok_def; GSYM ALL_MEM] THEN
  MESON_TAC[MP3AUX_gen_start_ok_Bytes]);;

(* HOL4 line 5900 *)
let heap_length_Bytes = prove
 (`!be fl bs (ws:(A word)list). heap_length [Bytes be fl bs ws] = LENGTH ws + 1`,
  REWRITE_TAC[heap_length_def; MAP; SUM; data_to_word_memoryProof_Bytes_def; LET_DEF;
              LET_END_DEF; el_length_def; LENGTH_write_bytes; ADD_CLAUSES]);;

(* MP3AUX: data_up_to after replacing an element by a data element of the *)
(* same length                                                             *)
let MP3AUX_data_up_to_replace = prove
 (`!a ha hb (x:(A,B)heap_element) y.
     el_length x = el_length y /\ isDataElement y /\
     data_up_to a (APPEND ha (CONS x hb)) ==>
     data_up_to a (APPEND ha (CONS y hb))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_up_to_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `a:num`; `hb:((A,B)heap_element)list`;
                 `x:(A,B)heap_element`; `y:(A,B)heap_element`;
                 `h1:((A,B)heap_element)list`; `h2:((A,B)heap_element)list`]
     MP3AUX_heap_split_replace) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h1':((A,B)heap_element)list`; `h2':((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

(* HOL4 line 5904 *)
let unused_space_inv_byte_update = prove
 (`!a sp sp1 ha be fl xs ys ws hb.
     unused_space_inv a (sp + sp1)
       (APPEND (APPEND ha [Bytes be fl xs (REPLICATE ws (word 0:A word))]) hb) ==>
     unused_space_inv a (sp + sp1)
       (APPEND (APPEND ha [Bytes be fl ys (REPLICATE ws (word 0:A word))]) hb)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[unused_space_inv_def; heap_length_APPEND; heap_length_Bytes;
              LENGTH_REPLICATE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MP3AUX_heap_lookup_Bytes THEN
    EXISTS_TAC `xs:byte list` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF] THEN SIMP[];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    DISCH_TAC THEN MATCH_MP_TAC MP3AUX_data_up_to_replace THEN
    EXISTS_TAC `Bytes be fl xs (REPLICATE ws (word 0:A word))` THEN
    ASM_REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF;
                    el_length_def; LENGTH_write_bytes; isDataElement_def] THEN
    MESON_TAC[]]);;

(* HOL4 line 5920 *)
let blocks_unique_insert_ByteArray = prove
 (`!ts refs b ptr stack fl ys.
     blocks_unique ts (all_vs refs (CONS (data_RefPtr b ptr) stack)) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvl_ByteArray fl ys) refs)
          (CONS (data_RefPtr b ptr) stack))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP3AUX_blocks_unique_SUBSET THEN
  EXISTS_TAC `all_vs refs (CONS (data_RefPtr b ptr) stack)` THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:data_v` THEN
  DISCH_THEN(MP_TAC o MATCH_MP MP3AUX_IN_all_vs_insert) THEN SIMP[]);;

(* MP3AUX: heap_split after replacing an element by one of the same length: *)
(* the split point is before or after the element                         *)
let MP3AUX_heap_split_replace_exact = prove
 (`!ha n hb (x:(A,B)heap_element) y h1 h2.
     el_length x = el_length y /\
     heap_split n (APPEND ha (CONS x hb)) = SOME (h1,h2) ==>
     (?hc. h2 = APPEND hc (CONS x hb) /\
           heap_split n (APPEND ha (CONS y hb)) = SOME (h1,APPEND hc (CONS y hb))) \/
     (?hc. h1 = APPEND ha (CONS x hc) /\
           heap_split n (APPEND ha (CONS y hb)) = SOME (APPEND ha (CONS y hc),h2))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[heap_split_def] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `[]:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[APPEND];
    ALL_TAC;
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `CONS (h:(A,B)heap_element) t` THEN ASM_REWRITE_TAC[APPEND];
    ALL_TAC] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `heap_split (n - el_length (y:(A,B)heap_element))
                (hb:((A,B)heap_element)list)` THEN
    ASM_REWRITE_TAC[distinctness "option"; option_CASE] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    DISJ2_TAC THEN EXISTS_TAC `x':((A,B)heap_element)list` THEN
    REWRITE_TAC[APPEND];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `heap_split (n - el_length (h:(A,B)heap_element))
                (APPEND t (CONS (x:(A,B)heap_element) hb))` THEN
    ASM_REWRITE_TAC[distinctness "option"; option_CASE] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n - el_length (h:(A,B)heap_element)`;
      `hb:((A,B)heap_element)list`; `x:(A,B)heap_element`; `y:(A,B)heap_element`;
      `x':((A,B)heap_element)list`; `h2:((A,B)heap_element)list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; PAIR_EQ; APPEND] THEN
    ASM_MESON_TAC[]]);;

(* MP3AUX: replacing a data element by one of the same length keeps the *)
(* set of data element addresses                                         *)
let MP3AUX_isSomeDataElement_replace = prove
 (`!ha hb (x:(A,B)heap_element) y p.
     el_length x = el_length y /\ isDataElement x /\ isDataElement y ==>
     (isSomeDataElement (heap_lookup p (APPEND ha (CONS y hb))) <=>
      isSomeDataElement (heap_lookup p (APPEND ha (CONS x hb))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MP3AUX_heap_lookup_replace th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND; LT_REFL; SUB_REFL] THEN
  REWRITE_TAC[heap_lookup_def; isSomeDataElement_def; option_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[isDataElement_def]) THEN ASM_MESON_TAC[]);;

(* MP3AUX: overwriting a byte array does not change the reference edges *)
let MP3AUX_ref_edge_insert_ByteArray = prove
 (`!ptr refs fl xs ys.
     lookup ptr refs = SOME (bvl_ByteArray fl xs) ==>
     ref_edge (insert ptr (bvl_ByteArray fl ys) refs) = ref_edge refs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ref_edge_def; lookup_insert] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* MP3AUX: heap_length after replacing an element by one of the same length *)
let MP3AUX_heap_length_replace = prove
 (`!ha hb (x:(A,B)heap_element) y.
     el_length x = el_length y ==>
     heap_length (APPEND ha (CONS y hb)) = heap_length (APPEND ha (CONS x hb))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[heap_length_APPEND; heap_length_def; MAP; SUM]);;

(* MP3AUX: byte arrays are data elements, not references, not forward *)
(* pointers, and have no pointers                                      *)
let MP3AUX_Bytes_props = prove
 (`!be fl bs (ws:(A word)list).
     isDataElement (Bytes be fl bs ws) /\ ~isRef (Bytes be fl bs ws) /\
     ~isForwardPointer (Bytes be fl bs ws) /\
     (!xs l d. Bytes be fl bs ws = DataElement xs l d ==> xs = []) /\
     el_length (Bytes be fl bs ws) = LENGTH ws + 1`,
  REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF;
              isDataElement_def; isRef_def; isForwardPointer_def; isMutTag_def;
              el_length_def; LENGTH_write_bytes] THEN
  SIMP[] THEN MESON_TAC[]);;

let MP3AUX_Bytes_DataElement = prove
 (`!be fl bs (ws:(A word)list) xs l d.
     DataElement xs l d = Bytes be fl bs ws ==> xs = []`,
  MESON_TAC[MP3AUX_Bytes_props]);;

(* HOL4 line 5934 *)
let update_byte_ref_thm = prove
 (`!conf b ptr stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts fl xs ys.
     abs_ml_inv conf (CONS (data_RefPtr b ptr) stack) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     lookup ptr refs = SOME (bvl_ByteArray fl xs) /\ LENGTH xs = LENGTH ys ==>
     ?roots2 h1 h2 ws.
       roots = CONS (Pointer (heap_length h1) (wl_Word (word 0):A word_loc))
                    roots2 /\
       heap = APPEND (APPEND h1 [Bytes be fl xs ws]) h2 /\
       LENGTH ws = LENGTH xs DIV (dimindex (:A) DIV 8) + 1 /\
       abs_ml_inv conf (CONS (data_RefPtr b ptr) stack)
         (insert ptr (bvl_ByteArray fl ys) refs)
         (roots,APPEND (APPEND h1 [Bytes be fl ys ws]) h2,be,a,sp,sp1,gens)
         limit ts`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN
  MP3AUX_ASM_HEAD_TAC "ALL2" (STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1]) THEN
  RVEQ_TAC THEN BETA_TAC THEN
  MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `reachable_refs (CONS (data_RefPtr b ptr) stack) refs ptr`
   ASSUME_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN EXISTS_TAC `data_RefPtr b ptr` THEN
    EXISTS_TAC `ptr:num` THEN REWRITE_TAC[MEM; get_refs_def; RTC_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `ptr:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[bc_ref_inv_def; FLOOKUP_DEF]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT)) THEN
  (FIRST_ASSUM(fun th -> if concl th = `LENGTH (xs:byte list) = LENGTH (ys:byte list)`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th else NO_TAC) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word)`] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH_REPLICATE] THEN
  SUBGOAL_THEN
   `!p. isSomeDataElement (heap_lookup p (APPEND ha (CONS
          (Bytes be fl ys (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
             (word 0:A word))) hb))) <=>
        isSomeDataElement (heap_lookup p (APPEND ha (CONS
          (Bytes be fl xs (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
             (word 0:A word))) hb)))`
   ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MP3AUX_isSomeDataElement_replace THEN
    REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF;
                el_length_def; LENGTH_write_bytes; isDataElement_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `el_length (Bytes be fl xs (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word))) =
                el_length (Bytes be fl ys (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word)))`
   ASSUME_TAC THENL [REWRITE_TAC[MP3AUX_Bytes_props]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN ASM_REWRITE_TAC[roots_ok_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "heap_ok" MP_TAC THEN REWRITE_TAC[heap_ok_def] THEN
    MP_TAC(ISPECL
     [`ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `Bytes be fl xs (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
         (word 0:A word))`;
      `Bytes be fl ys (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
         (word 0:A word))`] MP3AUX_heap_length_replace) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FILTER_APPEND; FILTER; MP3AUX_Bytes_props] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`xs':((A word_loc)heap_address)list`; `n0:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `p0:num`; `u0:A word_loc`] THEN
    REWRITE_TAC[MEM_APPEND; MEM] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`xs':((A word_loc)heap_address)list`; `n0:num`;
        `d:data_to_word_memoryProof_tag#(A word_loc)list`; `u0:A word_loc`] THEN
      ASM_REWRITE_TAC[MEM_APPEND; MEM];
      UNDISCH_TAC `MEM (Pointer p0 u0) (xs':((A word_loc)heap_address)list)` THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MP3AUX_Bytes_DataElement) THEN
      REWRITE_TAC[MEM];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`xs':((A word_loc)heap_address)list`; `n0:num`;
        `d:data_to_word_memoryProof_tag#(A word_loc)list`; `u0:A word_loc`] THEN
      ASM_REWRITE_TAC[MEM_APPEND; MEM]];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "gc_kind_inv" MP_TAC THEN REWRITE_TAC[gc_kind_inv_def] THEN
    CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:num`; `a + sp + sp1:num`;
        `ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `be:bool`; `fl:bool`; `xs:byte list`; `ys:byte list`;
        `REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word)`;
        `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `gens:gen_state`] gen_state_ok_update_byte) THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL
       [`ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `a + sp + sp1:num`;
        `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `Bytes be fl xs (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
           (word 0:A word))`;
        `Bytes be fl ys (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
           (word 0:A word))`;
        `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`]
        MP3AUX_heap_split_replace_exact) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `ALL isRef (h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
        ASM_REWRITE_TAC[ALL_APPEND; ALL; MP3AUX_Bytes_props];
        MAP_EVERY EXISTS_TAC
         [`APPEND ha (CONS (Bytes be fl ys (REPLICATE (LENGTH (ys:byte list) DIV
             (dimindex (:A) DIV 8) + 1) (word 0:A word))) hc)`;
          `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
        UNDISCH_TAC `ALL (\x. ~isRef x) (h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
        ASM_REWRITE_TAC[ALL_APPEND; ALL; MP3AUX_Bytes_props]]];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] unused_space_inv_byte_update) THEN
    EXISTS_TAC `xs:byte list` THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!v (y:(A word_loc)heap_address).
      v_inv conf v refs (y,f,tf,APPEND ha (CONS (Bytes be fl xs
        (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word))) hb)) /\
      v IN all_vs (insert ptr (bvl_ByteArray fl ys) refs) (CONS (data_RefPtr b ptr) stack) ==>
      v_inv conf v (insert ptr (bvl_ByteArray fl ys) refs)
        (y,f,DRESTRICT tf (all_ts (insert ptr (bvl_ByteArray fl ys) refs)
                                  (CONS (data_RefPtr b ptr) stack)),
         APPEND ha (CONS (Bytes be fl ys
        (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word))) hb))`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MP3AUX_v_inv_restrict THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC v_inv_ByteArray_insert THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] v_inv_IMP) THEN
      EXISTS_TAC `xs:byte list` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC]) THEN
  (EXISTS_TAC `f:(num,num)fmap` THEN
  EXISTS_TAC `DRESTRICT (tf:(num,num)fmap)
    (all_ts (insert ptr (bvl_ByteArray fl ys) refs) (CONS (data_RefPtr b ptr) stack))` THEN
  MP_TAC(ISPECL [`tf:(num,num)fmap`;
    `all_ts (insert ptr (bvl_ByteArray fl ys) refs) (CONS (data_RefPtr b ptr) stack)`;
    `{a | isSomeDataElement (heap_lookup a (APPEND ha (CONS (Bytes be fl xs
        (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word))) hb)))}`;
    `ts:num`] MP3AUX_DRESTRICT_tf) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INSERT] THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_insert_ByteArray THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[v_inv_def] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[lookup_insert] THEN SIMP[];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,APPEND ha (CONS (Bytes be fl xs
        (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word))) hb)))
        stack (t':((A word_loc)heap_address)list)` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM]];
    ALL_TAC]) THEN
  (X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `reachable_refs (CONS (data_RefPtr b ptr) stack)
                  (insert ptr (bvl_ByteArray fl ys) refs) n <=>
                reachable_refs (CONS (data_RefPtr b ptr) stack) refs n`
   SUBST1_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MP3AUX_ref_edge_insert_ByteArray th]);
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `n:num = ptr` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN
    ASM_REWRITE_TAC[lookup_insert] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND; LT_REFL; SUB_REFL] THEN
    REWRITE_TAC[heap_lookup_def];
    ALL_TAC]) THEN
  (MATCH_MP_TAC MP3AUX_bc_ref_inv_transfer THEN
  MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `APPEND ha (CONS (Bytes be fl xs
        (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1) (word 0:A word))) hb)`] THEN
  ASM_REWRITE_TAC[lookup_insert] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`ha:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `hb:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `Bytes be fl xs (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
         (word 0:A word))`;
      `Bytes be fl ys (REPLICATE (LENGTH (ys:byte list) DIV (dimindex (:A) DIV 8) + 1)
         (word 0:A word))`; `FAPPLY (f:(num,num)fmap) n`] MP3AUX_heap_lookup_replace) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(FAPPLY (f:(num,num)fmap) n = FAPPLY f ptr)` MP_TAC THENL
     [MATCH_MP_TAC(ISPECL [`f:(num,num)fmap`;
        `APPEND ha (CONS (Bytes be fl xs (REPLICATE (LENGTH (ys:byte list) DIV
           (dimindex (:A) DIV 8) + 1) (word 0:A word))) hb)`] INJ_NEQ) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])];
    X_GEN_TAC `v:data_v` THEN
    MP_TAC(ISPECL [`v:data_v`; `refs:(data_v bvl_ref)spt`; `ptr:num`;
      `bvl_ByteArray fl ys:data_v bvl_ref`; `bvl_ByteArray fl xs:data_v bvl_ref`]
      MP3AUX_dest_thunk_insert_nonthunk) THEN
    ANTS_TAC THENL [SIMP[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP3AUX_IN_all_vs_find_ref THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[lookup_insert] THEN ASM_MESON_TAC[]]));;

(* MP3AUX: apply ttac to the newest equational assumption whose left side *)
(* has head constant c, removing it                                       *)
let MP3AUX_ASM_LHS_HEAD_TAC c ttac =
  FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_eq t && (let h = fst(strip_comb(lhs t)) in
                   is_const h && fst(dest_const h) = c)
    then ttac th else NO_TAC);;

(* MP3AUX: heap_length of a CONS; a heap of length 0 is empty *)
let MP3AUX_heap_length_CONS = prove
 (`!(x:(A,B)heap_element) xs. heap_length (CONS x xs) = el_length x + heap_length xs`,
  REWRITE_TAC[heap_length_def; MAP; SUM]);;

let MP3AUX_heap_length_EQ_0 = prove
 (`!xs:((A,B)heap_element)list. heap_length xs = 0 <=> xs = []`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_length_NIL; MP3AUX_heap_length_CONS; NOT_CONS_NIL] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` el_length_NOT_0) THEN ARITH_TAC);;

(* HOL4 line 6113 *)
let heap_store_unused_thm = prove
 (`!a n (heap:((A,B)heap_element)list) h1 h2 heap2 x.
     heap_split (a + n) heap = SOME (h1,h2) /\
     heap_store_unused a n x heap = (heap2,T) /\
     unused_space_inv a (n - el_length x) heap2 ==>
     ?h0. h1 = APPEND h0 [Unused (n - 1)] /\
          heap = APPEND h1 h2 /\ heap_length h0 = a /\
          heap2 = APPEND (APPEND (APPEND h0 (heap_expand (n - el_length x))) [x])
                         h2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_split_heap_length) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `0 < n /\ a < heap_length (h1:((A,B)heap_element)list)`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `x:(A,B)heap_element` el_length_NOT_0) THEN
    UNDISCH_TAC `el_length (x:(A,B)heap_element) <= n` THEN
    UNDISCH_TAC `heap_length (h1:((A,B)heap_element)list) = a + n` THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `heap_lookup a (APPEND h1 h2) = SOME (Unused (n - 1):(A,B)heap_element)` THEN
  ASM_REWRITE_TAC[data_to_word_memoryProof_heap_lookup_APPEND] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  SUBGOAL_THEN `hb:((A,B)heap_element)list = []` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM MP3AUX_heap_length_EQ_0] THEN
    UNDISCH_TAC `heap_length (h1:((A,B)heap_element)list) = a + n` THEN
    ASM_REWRITE_TAC[heap_length_APPEND; MP3AUX_heap_length_CONS; el_length_def] THEN
    UNDISCH_TAC `0 < n` THEN ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `ha:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `heap_store a (APPEND (heap_expand (n - el_length (x:(A,B)heap_element))) [x])
                 (APPEND h1 h2) = (heap2,T)` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN REWRITE_TAC[heap_store_lemma] THEN
  REWRITE_TAC[PAIR_EQ; GSYM APPEND_ASSOC; APPEND] THEN MESON_TAC[]);;

(* HOL4 line 6139 *)
let heap_store_unused_heap_lookup = prove
 (`!(heap:((A,B)heap_element)list) heap2 a k x n.
     heap_store_unused a k x heap = (heap2,T) /\ n < a ==>
     heap_lookup n heap = heap_lookup n heap2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  RVEQ_TAC THEN MP3AUX_ASM_LHS_HEAD_TAC "heap_store" MP_TAC THEN
  REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  ASM_SIMP_TAC[heap_lookup_APPEND2]);;

(* HOL4 line 6162 *)
let heap_store_unused_gen_state_ok = prove
 (`!a k (x:(A,B)heap_element) heap heap2 gens.
     heap_store_unused a k x heap = (heap2,T) /\
     gen_state_ok a (a + k) heap gens ==>
     gen_state_ok a ((a + k) - el_length x) heap2 gens`,
  REPEAT GEN_TAC THEN CASES_ON `gens:gen_state` THEN
  REWRITE_TAC[gen_state_ok_def; GSYM ALL_MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[gen_start_ok_def] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `heap_store_unused a k x heap = (heap2:((A,B)heap_element)list,T)` THEN
  REWRITE_TAC[heap_store_unused_def] THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`heap:((A,B)heap_element)list`; `s:num`; `h1:((A,B)heap_element)list`;
    `h2:((A,B)heap_element)list`; `a:num`;
    `APPEND (heap_expand (k - el_length (x:(A,B)heap_element))) [x]`;
    `heap2:((A,B)heap_element)list`] heap_split_heap_store) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h1:((A,B)heap_element)list`; `h3:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs:((A)heap_address)list`; `l:num`; `d:B`; `p:num`; `e:A`]) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* MP3AUX: blocks_unique only looks at the non-empty blocks of the set *)
let MP3AUX_blocks_unique_SUBSET2 = prove
 (`!ts vs vs'.
     blocks_unique ts vs /\
     (!t a xs. data_Block t a xs IN vs' /\ ~(xs = []) ==> data_Block t a xs IN vs) ==>
     blocks_unique ts vs'`,
  REWRITE_TAC[blocks_unique_def] THEN MESON_TAC[]);;

(* MP3AUX: v_all_vs element by element *)
let MP3AUX_MEM_v_all_vs = prove
 (`!l x. MEM x (v_all_vs l) <=> ?y. MEM y l /\ MEM x (v_all_vs [y])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[v_all_vs_def; MEM] THEN
  ONCE_REWRITE_TAC[MESON[APPEND] `CONS (h:data_v) t = APPEND [h] t`] THEN
  ASM_REWRITE_TAC[v_all_vs_append; MEM_APPEND; APPEND] THEN
  REWRITE_TAC[v_all_vs_def; MEM] THEN MESON_TAC[]);;

(* MP3AUX: all_vs element by element: the values held by the references *)
(* and the stack, and what v_all_vs finds in them                        *)
let MP3AUX_IN_all_vs = prove
 (`!v refs stack.
     v IN all_vs refs stack <=>
     (?n r y. lookup n refs = SOME r /\ find_ref r y /\ MEM v (v_all_vs [y])) \/
     (?y. MEM y stack /\ MEM v (v_all_vs [y]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MP3AUX_MEM_v_all_vs] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `bvl_ValueArray l:data_v bvl_ref`; `y:data_v`] THEN
    ASM_REWRITE_TAC[find_ref_def];
    DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `bvl_Thunk ev x:data_v bvl_ref`; `y:data_v`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM]) THEN ASM_REWRITE_TAC[find_ref_def];
    DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `MutBlock tg fin l c r:data_v bvl_ref`; `y:data_v`] THEN
    ASM_REWRITE_TAC[find_ref_def];
    DISJ2_TAC THEN EXISTS_TAC `y:data_v` THEN ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    CASES_ON `r:data_v bvl_ref` THEN REWRITE_TAC[find_ref_def] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[MEM];
    REPEAT DISJ2_TAC THEN EXISTS_TAC `y:data_v` THEN ASM_REWRITE_TAC[]]);;

(* MP3AUX: lookup after insert, as a disjunction *)
let MP3AUX_lookup_insert_SOME = prove
 (`!n ptr (x:A) refs r.
     lookup n (insert ptr x refs) = SOME r <=>
     n = ptr /\ x = r \/ ~(n = ptr) /\ lookup n refs = SOME r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ]);;

(* MP3AUX: the values of RefPtr, Number ... contain no block *)
let MP3AUX_v_all_vs_RefPtr = prove
 (`!b p x. MEM x (v_all_vs [data_RefPtr b p]) <=> x = data_RefPtr b p`,
  REWRITE_TAC[v_all_vs_def; MEM]);;

(* MP3AUX: the common proof of the blocks_unique lemmas: every block of the *)
(* new values is a block of the old ones                                   *)
let MP3AUX_BLOCKS_TAC old thl =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP3AUX_blocks_unique_SUBSET2 THEN
  EXISTS_TAC old THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MP3AUX_IN_all_vs; MP3AUX_lookup_insert_SOME; MEM_APPEND; MEM] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_ref_def; MP3AUX_v_all_vs_RefPtr;
                              distinctness "data_v"]) THEN
  ASM_MESON_TAC(find_ref_def :: thl);;

(* HOL4 line 6181 *)
let blocks_unique_new_ref = prove
 (`!ts refs xs stack ptr.
     blocks_unique ts (all_vs refs (APPEND xs stack)) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvl_ValueArray xs) refs)
          (APPEND xs (CONS (data_RefPtr T ptr) stack)))`,
  MP3AUX_BLOCKS_TAC `all_vs refs (APPEND xs stack)` []);;

(* MP3AUX: properties of the reference and thunk heap blocks *)
let MP3AUX_RefBlock_props = prove
 (`!xs:((A)heap_address)list.
     isDataElement (RefBlock xs:(A,data_to_word_memoryProof_tag#B list)heap_element) /\
     ~isForwardPointer (RefBlock xs:(A,data_to_word_memoryProof_tag#B list)heap_element) /\
     isRef (RefBlock xs:(A,data_to_word_memoryProof_tag#B list)heap_element) /\
     el_length (RefBlock xs:(A,data_to_word_memoryProof_tag#B list)heap_element) =
       LENGTH xs + 1 /\
     (!ys l d. RefBlock xs:(A,data_to_word_memoryProof_tag#B list)heap_element =
               DataElement ys l d <=> ys = xs /\ l = LENGTH xs /\ d = (RefTag,[]))`,
  REWRITE_TAC[RefBlock_def; isDataElement_def; isForwardPointer_def; isRef_def;
              isMutTag_def; el_length_def] THEN
  SIMP[] THEN MESON_TAC[]);;

let MP3AUX_ThunkBlock_props = prove
 (`!ev (x:A heap_address).
     isDataElement (ThunkBlock ev x:(A,data_to_word_memoryProof_tag#B list)heap_element) /\
     ~isForwardPointer (ThunkBlock ev x:(A,data_to_word_memoryProof_tag#B list)heap_element) /\
     isRef (ThunkBlock ev x:(A,data_to_word_memoryProof_tag#B list)heap_element) /\
     el_length (ThunkBlock ev x:(A,data_to_word_memoryProof_tag#B list)heap_element) = 2 /\
     (!ys l d. ThunkBlock ev x:(A,data_to_word_memoryProof_tag#B list)heap_element =
               DataElement ys l d <=> ys = [x] /\ l = 1 /\ d = (ThunkTag ev,[]))`,
  REWRITE_TAC[ThunkBlock_def; isDataElement_def; isForwardPointer_def; isRef_def;
              isMutTag_def; el_length_def] THEN
  SIMP[] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

(* HOL4 line 6196 (the unused bound variable p of HOL4 is left out) *)
let new_ref_thm = prove
 (`!conf xs stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts ptr.
     abs_ml_inv conf (APPEND xs stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     ~(ptr IN domain refs) /\ LENGTH xs + 1 <= sp ==>
     ?rs roots2 heap2.
       roots = APPEND rs roots2 /\ LENGTH rs = LENGTH xs /\
       heap_store_unused a (sp + sp1) (RefBlock rs) heap = (heap2,T) /\
       abs_ml_inv conf (APPEND xs (CONS (data_RefPtr T ptr) stack))
         (insert ptr (bvl_ValueArray xs) refs)
         (APPEND rs (CONS (Pointer ((a + sp + sp1) - (LENGTH xs + 1))
                                   (wl_Word (word 0))) roots2),heap2,be,a,
          sp - (LENGTH xs + 1),sp1,gens) limit ts`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN STRIP_TAC THEN
  MP3AUX_ASM_HEAD_TAC "ALL2" (STRIP_ASSUME_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `LENGTH (ys1:((A word_loc)heap_address)list) = LENGTH (xs:data_v list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `el_length (RefBlock ys1:((A word_loc,data_to_word_memoryProof_tag#
                  (A word_loc)list)heap_element)) = LENGTH (xs:data_v list) + 1`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[RefBlock_def; el_length_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `RefBlock ys1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`]
    IMP_heap_store_unused) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ys1:((A word_loc)heap_address)list`;
    `ys2:((A word_loc)heap_address)list`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[]) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[MP3AUX_RefBlock_props]) THEN
  SUBGOAL_THEN
   `!q. isSomeDataElement (heap_lookup q (heap2:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list)) <=>
        q = (a + sp + sp1) - (LENGTH (xs:data_v list) + 1) \/
        isSomeDataElement (heap_lookup q (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))`
   ASSUME_TAC THENL
   [GEN_TAC THEN MP3AUX_ASM_LHS_HEAD_TAC "GSPEC" MP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM_APPEND; MEM; injectivity "heap_address"] THEN
    MESON_TAC[];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "heap_ok" MP_TAC THEN REWRITE_TAC[heap_ok_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`xs':((A word_loc)heap_address)list`; `n0:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `p0:num`; `u0:A word_loc`] THEN
    STRIP_TAC THENL
     [RVEQ_TAC THEN DISJ2_TAC THEN
      MP3AUX_ASM_HEAD_TAC "roots_ok" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN
      ASM_MESON_TAC[MEM_APPEND];
      DISJ2_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "gc_kind_inv" MP_TAC THEN REWRITE_TAC[gc_kind_inv_def] THEN
    CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `a + (sp - (LENGTH (xs:data_v list) + 1)) + sp1 =
                  (a + sp + sp1) - (LENGTH xs + 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
        `RefBlock ys1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `gens:gen_state`] heap_store_unused_gen_state_ok) THEN
      ASM_REWRITE_TAC[MP3AUX_RefBlock_props];
      MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `RefBlock ys1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`]
        heap_store_unused_thm) THEN
      ASM_REWRITE_TAC[MP3AUX_RefBlock_props] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`APPEND h0 (heap_expand ((sp + sp1) - (LENGTH (xs:data_v list) + 1))):((A word_loc,
           data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `CONS (RefBlock ys1) h2:((A word_loc,data_to_word_memoryProof_tag#
           (A word_loc)list)heap_element)list`] THEN
      SUBGOAL_THEN
       `(a + sp + sp1) - (LENGTH (xs:data_v list) + 1) =
        heap_length (APPEND h0 (heap_expand ((sp + sp1) - (LENGTH xs + 1))):((A word_loc,
           data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`
       SUBST1_TAC THENL
       [ASM_REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
      REWRITE_TAC[APPEND_ASSOC; heap_split_length] THEN
      UNDISCH_TAC `ALL (\x. ~isRef x) (h1:((A word_loc,data_to_word_memoryProof_tag#
           (A word_loc)list)heap_element)list)` THEN
      ASM_REWRITE_TAC[ALL_APPEND; ALL; MP3AUX_RefBlock_props; heap_expand_def] THEN
      COND_CASES_TAC THEN REWRITE_TAC[ALL; isRef_def] THEN SIMP[]];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [SUBGOAL_THEN `sp - (LENGTH (xs:data_v list) + 1) + sp1 = (sp + sp1) - (LENGTH xs + 1)`
     SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ptr IN FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v (y:(A word_loc)heap_address).
      v_inv conf v refs (y,f,tf,heap) /\
      v IN all_vs (insert ptr (bvl_ValueArray xs) refs)
             (APPEND xs (CONS (data_RefPtr T ptr) stack)) ==>
      v_inv conf v (insert ptr (bvl_ValueArray xs) refs)
        (y,f |+ (ptr,(a + sp + sp1) - (LENGTH xs + 1)),
         DRESTRICT tf (all_ts (insert ptr (bvl_ValueArray xs) refs)
                              (APPEND xs (CONS (data_RefPtr T ptr) stack))),heap2)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MP3AUX_v_inv_restrict THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC v_inv_SUBMAP THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN; SUBMAP_REFL] THEN
    MATCH_MP_TAC v_inv_ValueArray_insert THEN
    EXISTS_TAC `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` THEN
    ASM_REWRITE_TAC[RefBlock_inv_def] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
     {a | isSomeDataElement (heap_lookup a (heap2:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))}` ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
     {a | isSomeDataElement (heap_lookup a (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))}` THEN
    ASM_REWRITE_TAC[INJ; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(f:(num,num)fmap) |+ (ptr,(a + sp + sp1) - (LENGTH (xs:data_v list) + 1))` THEN
  EXISTS_TAC `DRESTRICT (tf:(num,num)fmap)
    (all_ts (insert ptr (bvl_ValueArray xs) refs)
            (APPEND xs (CONS (data_RefPtr T ptr) stack)))` THEN
  MP_TAC(ISPECL [`tf:(num,num)fmap`;
    `all_ts (insert ptr (bvl_ValueArray xs) refs)
            (APPEND xs (CONS (data_RefPtr T ptr) stack))`;
    `{a | isSomeDataElement (heap_lookup a (heap2:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))}`;
    `ts:num`] MP3AUX_DRESTRICT_tf) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[fapply_fupdate_update; FDOM_FUPDATE] THEN
    MATCH_MP_TAC INJ_UPDATE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FDOM_FUPDATE; domain_insert] THEN
    UNDISCH_TAC `FDOM (f:(num,num)fmap) SUBSET domain (refs:(data_v bvl_ref)spt)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_new_ref THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (CONJ_TAC THENL
   [ASM_SIMP_TAC[LIST_REL_APPEND_EQ; ALL2] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) xs
                     (ys1:((A word_loc)heap_address)list)` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM_APPEND];
      REWRITE_TAC[v_inv_def] THEN
      ASM_REWRITE_TAC[lookup_insert; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
      SIMP[];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack
                     (ys2:((A word_loc)heap_address)list)` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM_APPEND; MEM]];
    ALL_TAC]) THEN
  (X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_CASES_TAC `n:num = ptr` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM;
                lookup_insert] THEN
    CASE_REWRITE_TAC[] THEN EXISTS_TAC `ys1:((A word_loc)heap_address)list` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) xs
                   (ys1:((A word_loc)heap_address)list)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP EVERY2_SWAP) THEN
    MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM_APPEND];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `reachable_refs (APPEND xs stack) refs n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP reachable_refs_UPDATE o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "reachable_refs"
                       with _ -> false)) THEN
    REWRITE_TAC[reachable_refs_def; MEM_APPEND; MEM] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `MEM r (get_refs x)` THEN ASM_REWRITE_TAC[get_refs_def; MEM] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `RTC (ref_edge refs) ptr n` THEN
      ONCE_REWRITE_TAC[RTC_CASES_R] THEN ASM_REWRITE_TAC[ref_edge_def] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM lookup_NONE_domain]) THEN
      ASM_REWRITE_TAC[option_CASE];
      ASM_MESON_TAC[]];
    ALL_TAC]) THEN
  (MATCH_MP_TAC MP3AUX_bc_ref_inv_transfer THEN
  MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FDOM_FUPDATE; IN_INSERT]) THEN
  ASM_REWRITE_TAC[lookup_insert; FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    UNDISCH_TAC `heap_store_rel (heap:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) heap2` THEN
    REWRITE_TAC[heap_store_rel_def] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ASM_MESON_TAC[dest_thunk_insert_fresh];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP3AUX_IN_all_vs_find_ref THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[lookup_insert] THEN ASM_MESON_TAC[]]));;

(* HOL4 line 6438 *)
let v_inv_new_Thunk_insert_lemma = prove
 (`!conf ev h ck v refs (x:(A word_loc)heap_address) f tf heap ptr.
     v_inv conf v refs (x,f,tf,heap) /\
     ~(ptr IN FDOM f) /\
     ~(ptr IN domain refs) /\
     (ev = Evaluated ==> data_dest_thunk h refs = data_NotThunk) ==>
     v_inv_ck ck conf v (insert ptr (bvl_Thunk ev h) refs) (x,f,tf,heap)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`v:data_v`,`v:data_v`) THEN
  SPEC_TAC(`x:(A word_loc)heap_address`,`x:(A word_loc)heap_address`) THEN
  SPEC_TAC(`ck:num`,`ck:num`) THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `ck:num` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[v_inv_ck_cases] THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[v_inv_def] THEN SIMP[] THENL
   [(* Number *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    (* Block *)
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs:((A word_loc)heap_address)list`; `ptr':num`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MP3AUX_ASM_HEAD_MP_TAC "ALL2" THEN MATCH_MP_TAC MONO_ALL2 THEN
    BETA_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    (* RefPtr *)
    REWRITE_TAC[lookup_insert] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `~(a1:num = ptr)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISJ1_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(a1:num = ptr)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`ev':thunk_mode`; `v:data_v`; `y:(A word_loc)heap_address`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[dest_thunk_insert_fresh];
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `~(a1:num = ptr)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[domain_lookup]; ALL_TAC] THEN
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[dest_thunk_insert_fresh];
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ck - 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
        ASM_REWRITE_TAC[]]]]);;

(* HOL4 line 6472 *)
let v_inv_new_Thunk_insert = prove
 (`!conf ev h v refs (x:(A word_loc)heap_address) f tf heap ptr.
     v_inv conf v refs (x,f,tf,heap) /\
     ~(ptr IN FDOM f) /\
     ~(ptr IN domain refs) /\
     (ev = Evaluated ==> data_dest_thunk h refs = data_NotThunk) ==>
     v_inv conf v (insert ptr (bvl_Thunk ev h) refs) (x,f,tf,heap)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC v_inv_new_Thunk_insert_lemma THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6478 *)
let blocks_unique_new_thunk = prove
 (`!ts refs v stack ptr ev.
     blocks_unique ts (all_vs refs (CONS v stack)) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvl_Thunk ev v) refs)
          (CONS v (CONS (data_RefPtr F ptr) stack)))`,
  MP3AUX_BLOCKS_TAC `all_vs refs (CONS v stack)` []);;

(* HOL4 line 6494 (the unused bound variable p of HOL4 is left out) *)
let new_thunk_thm = prove
 (`!conf v stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts ptr ev.
     abs_ml_inv conf (CONS v stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     ~(ptr IN domain refs) /\ 2 <= sp /\
     (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) ==>
     ?r roots2 heap2.
       roots = CONS r roots2 /\
       heap_store_unused a (sp + sp1) (ThunkBlock ev r) heap = (heap2,T) /\
       abs_ml_inv conf (CONS v (CONS (data_RefPtr F ptr) stack))
         (insert ptr (bvl_Thunk ev v) refs)
         (CONS r (CONS (Pointer ((a + sp + sp1) - 2) (wl_Word (word 0))) roots2),
          heap2,be,a,sp - 2,sp1,gens) limit ts`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN STRIP_TAC THEN
  MP3AUX_ASM_HEAD_TAC "ALL2" (STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1]) THEN
  RVEQ_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `ThunkBlock ev h':((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`]
    IMP_heap_store_unused) THEN
  ASM_REWRITE_TAC[MP3AUX_ThunkBlock_props] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h':(A word_loc)heap_address`;
    `t':((A word_loc)heap_address)list`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN
   `!q. isSomeDataElement (heap_lookup q (heap2:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list)) <=>
        q = (a + sp + sp1) - 2 \/
        isSomeDataElement (heap_lookup q (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))`
   ASSUME_TAC THENL
   [GEN_TAC THEN MP3AUX_ASM_LHS_HEAD_TAC "GSPEC" MP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM_APPEND; MEM; injectivity "heap_address"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "heap_ok" MP_TAC THEN REWRITE_TAC[heap_ok_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`xs':((A word_loc)heap_address)list`; `n0:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `p0:num`; `u0:A word_loc`] THEN
    STRIP_TAC THENL
     [RVEQ_TAC THEN DISJ2_TAC THEN
      MP3AUX_ASM_HEAD_TAC "roots_ok" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MEM]) THEN ASM_MESON_TAC[MEM];
      DISJ2_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "gc_kind_inv" MP_TAC THEN REWRITE_TAC[gc_kind_inv_def] THEN
    CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `a + (sp - 2) + sp1 = (a + sp + sp1) - 2` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
        `ThunkBlock ev h':((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `gens:gen_state`] heap_store_unused_gen_state_ok) THEN
      ASM_REWRITE_TAC[MP3AUX_ThunkBlock_props];
      MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `ThunkBlock ev h':((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)`]
        heap_store_unused_thm) THEN
      ASM_REWRITE_TAC[MP3AUX_ThunkBlock_props] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`APPEND h0 (heap_expand ((sp + sp1) - 2)):((A word_loc,
           data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `CONS (ThunkBlock ev h') h2:((A word_loc,data_to_word_memoryProof_tag#
           (A word_loc)list)heap_element)list`] THEN
      SUBGOAL_THEN
       `(a + sp + sp1) - 2 =
        heap_length (APPEND h0 (heap_expand ((sp + sp1) - 2)):((A word_loc,
           data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`
       SUBST1_TAC THENL
       [ASM_REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
      REWRITE_TAC[APPEND_ASSOC; heap_split_length] THEN
      UNDISCH_TAC `ALL (\x. ~isRef x) (h1:((A word_loc,data_to_word_memoryProof_tag#
           (A word_loc)list)heap_element)list)` THEN
      ASM_REWRITE_TAC[ALL_APPEND; ALL; MP3AUX_ThunkBlock_props; heap_expand_def] THEN
      COND_CASES_TAC THEN REWRITE_TAC[ALL; isRef_def] THEN SIMP[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `sp - 2 + sp1 = (sp + sp1) - 2` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `~(ptr IN FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w (y:(A word_loc)heap_address).
      v_inv conf w refs (y,f,tf,heap) /\
      w IN all_vs (insert ptr (bvl_Thunk ev v) refs)
             (CONS v (CONS (data_RefPtr F ptr) stack)) ==>
      v_inv conf w (insert ptr (bvl_Thunk ev v) refs)
        (y,f |+ (ptr,(a + sp + sp1) - 2),
         DRESTRICT tf (all_ts (insert ptr (bvl_Thunk ev v) refs)
                              (CONS v (CONS (data_RefPtr F ptr) stack))),heap2)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MP3AUX_v_inv_restrict THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC v_inv_SUBMAP THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN; SUBMAP_REFL] THEN
    MATCH_MP_TAC v_inv_new_Thunk_insert THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
     (((a + sp + sp1) - 2) INSERT
      {a | isSomeDataElement (heap_lookup a (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))})` ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
     {a | isSomeDataElement (heap_lookup a (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(f:(num,num)fmap) |+ (ptr,(a + sp + sp1) - 2)` THEN
  EXISTS_TAC `DRESTRICT (tf:(num,num)fmap)
    (all_ts (insert ptr (bvl_Thunk ev v) refs)
            (CONS v (CONS (data_RefPtr F ptr) stack)))` THEN
  MP_TAC(ISPECL [`tf:(num,num)fmap`;
    `all_ts (insert ptr (bvl_Thunk ev v) refs)
            (CONS v (CONS (data_RefPtr F ptr) stack))`;
    `((a + sp + sp1) - 2) INSERT
      {a | isSomeDataElement (heap_lookup a (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))}`;
    `ts:num`] MP3AUX_DRESTRICT_tf) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[fapply_fupdate_update; FDOM_FUPDATE] THEN
    MATCH_MP_TAC INJ_UPDATE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FDOM_FUPDATE; domain_insert] THEN
    UNDISCH_TAC `FDOM (f:(num,num)fmap) SUBSET domain (refs:(data_v bvl_ref)spt)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_new_thunk THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `v_inv conf v (insert ptr (bvl_Thunk ev v) refs)
        (h',f |+ (ptr,(a + sp + sp1) - 2),
         DRESTRICT tf (all_ts (insert ptr (bvl_Thunk ev v) refs)
                              (CONS v (CONS (data_RefPtr F ptr) stack))),
         heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`
   ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEM_stack_all_vs THEN REWRITE_TAC[MEM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALL2] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[v_inv_def] THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`; `h':(A word_loc)heap_address`] THEN
      ASM_REWRITE_TAC[lookup_insert; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
      ASM_MESON_TAC[dest_thunk_insert_fresh];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack
                     (t':((A word_loc)heap_address)list)` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM]];
    ALL_TAC]) THEN
  (X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_CASES_TAC `n:num = ptr` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM;
                lookup_insert] THEN
    CASE_REWRITE_TAC[] THEN EXISTS_TAC `h':(A word_loc)heap_address` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[dest_thunk_insert_fresh];
    ALL_TAC] THEN
  SUBGOAL_THEN `reachable_refs (CONS v stack) refs n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP reachable_refs_Thunk_UPDATE o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "reachable_refs"
                       with _ -> false)) THEN
    REWRITE_TAC[reachable_refs_def; MEM] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `MEM r (get_refs x)` THEN ASM_REWRITE_TAC[get_refs_def; MEM] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `RTC (ref_edge refs) ptr n` THEN
      ONCE_REWRITE_TAC[RTC_CASES_R] THEN ASM_REWRITE_TAC[ref_edge_def] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM lookup_NONE_domain]) THEN
      ASM_REWRITE_TAC[option_CASE];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MP3AUX_bc_ref_inv_transfer THEN
  MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FDOM_FUPDATE; IN_INSERT]) THEN
  ASM_REWRITE_TAC[lookup_insert; FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    UNDISCH_TAC `heap_store_rel (heap:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) heap2` THEN
    REWRITE_TAC[heap_store_rel_def] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ASM_MESON_TAC[dest_thunk_insert_fresh];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP3AUX_IN_all_vs_find_ref THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[lookup_insert] THEN ASM_MESON_TAC[]]));;

(* HOL4 line 6753 *)
let heap_el_def = cake_def
  `(heap_el (Pointer a (u:A)) n (heap:((A,B)heap_element)list) =
      match heap_lookup a heap with
        SOME (DataElement xs l d) ->
          if n < LENGTH xs then (EL n xs,T) else (ARB,F)
      | _ -> (ARB,F)) /\
   (heap_el _ _ _ = (ARB,F))`;;

(* HOL4 line 6762 *)
let blocks_unique_deref1 = prove
 (`!ptr refs a' ts stack.
     lookup ptr refs = SOME (bvl_Thunk NotEvaluated a') /\
     blocks_unique ts (all_vs refs (CONS (data_RefPtr F ptr) stack)) ==>
     blocks_unique ts (all_vs refs (CONS a' (CONS (data_RefPtr F ptr) stack)))`,
  MP3AUX_BLOCKS_TAC `all_vs refs (CONS (data_RefPtr F ptr) stack)` []);;

(* HOL4 line 6778 *)
let blocks_unique_deref2 = prove
 (`!n l ptr refs ts b stack.
     n < LENGTH l /\
     lookup ptr refs = SOME (bvl_ValueArray l) /\
     blocks_unique ts (all_vs refs (CONS (data_RefPtr b ptr) stack)) ==>
     blocks_unique ts (all_vs refs (CONS (EL n l) (CONS (data_RefPtr b ptr) stack)))`,
  MP3AUX_BLOCKS_TAC `all_vs refs (CONS (data_RefPtr b ptr) stack)` [EL_MEM]);;

(* MP3AUX: a value held by a reference adds no timestamps to all_ts *)
let MP3AUX_all_ts_find_ref = prove
 (`!n refs r v stack.
     lookup n refs = SOME r /\ find_ref r v ==>
     all_ts refs (CONS v stack) = all_ts refs stack`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; EXTENSION; IN_ELIM_THM; MEM] THEN
  ASM_MESON_TAC[]);;

(* MP3AUX: the references in a value held by a reference are edges of it *)
let MP3AUX_ref_edge_find_ref = prove
 (`!ptr refs r v res.
     lookup ptr refs = SOME r /\ find_ref r v /\ MEM res (get_refs v) ==>
     ref_edge refs ptr res`,
  REPEAT GEN_TAC THEN CASES_ON `r:data_v bvl_ref` THEN
  REWRITE_TAC[find_ref_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ref_edge_def; option_CASE] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[MEM]);;

(* MP3AUX: pushing a value held by the reference ptr onto the stack *)
(* reaches no new references                                         *)
let MP3AUX_reachable_find_ref = prove
 (`!ptr refs r v b stack n.
     lookup ptr refs = SOME r /\ find_ref r v /\
     reachable_refs (CONS v (CONS (data_RefPtr b ptr) stack)) refs n ==>
     reachable_refs (CONS (data_RefPtr b ptr) stack) refs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def; MEM] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`data_RefPtr b ptr`; `ptr:num`] THEN
    REWRITE_TAC[MEM; get_refs_def] THEN
    ONCE_REWRITE_TAC[RTC_CASES_R] THEN DISJ2_TAC THEN
    EXISTS_TAC `r':num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP3AUX_ref_edge_find_ref THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* MP3AUX: the pointers in a heap block of a heap_ok heap are valid *)
let MP3AUX_heap_ok_lookup = prove
 (`!(heap:((A,B)heap_element)list) limit p xs l d q (u:A).
     heap_ok heap limit /\ heap_lookup p heap = SOME (DataElement xs l d) /\
     MEM (Pointer q u) xs ==>
     isSomeDataElement (heap_lookup q heap)`,
  REWRITE_TAC[heap_ok_def] THEN MESON_TAC[heap_lookup_MEM]);;

(* HOL4 line 6796 *)
let deref_thm = prove
 (CASE_TERM
  `!conf b ptr stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (CONS (data_RefPtr b ptr) stack) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts ==>
     ?r roots2.
       roots = CONS r roots2 /\ ptr IN domain refs /\
       match THE (lookup ptr refs) with
         bvl_ByteArray _ _ -> T
       | MutBlock _ _ _ _ _ -> T
       | bvl_ValueArray vs ->
           (!n. n < LENGTH vs ==>
                ?y. heap_el r n heap = (y,T) /\
                    abs_ml_inv conf (CONS (EL n vs) (CONS (data_RefPtr b ptr) stack))
                      refs (CONS y roots,heap,be,a,sp,sp1,gens) limit ts)
       | bvl_Thunk Evaluated v -> T
       | bvl_Thunk NotEvaluated v ->
           (?y. heap_el r 0 heap = (y,T) /\
                abs_ml_inv conf (CONS v (CONS (data_RefPtr b ptr) stack)) refs
                  (CONS y roots,heap,be,a,sp,sp1,gens) limit ts)`,
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[abs_ml_inv_def; bc_stack_ref_inv_def]) THEN
  STRIP_TAC THEN
  MP3AUX_ASM_HEAD_TAC "ALL2" (STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1]) THEN
  RVEQ_TAC THEN BETA_TAC THEN
  MAP_EVERY EXISTS_TAC [`h':(A word_loc)heap_address`; `t':((A word_loc)heap_address)list`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `reachable_refs (CONS (data_RefPtr b ptr) stack) refs ptr` ASSUME_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN EXISTS_TAC `data_RefPtr b ptr` THEN
    EXISTS_TAC `ptr:num` THEN REWRITE_TAC[MEM; get_refs_def; RTC_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `ptr IN domain (refs:(data_v bvl_ref)spt)` ASSUME_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[domain_lookup];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[domain_lookup]) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[THE_DEF] THEN
  CASES_ON `v:data_v bvl_ref` THEN CASE_REWRITE_TAC[]) THENL
  [(MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `ptr:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[bc_ref_inv_def; FLOOKUP_DEF]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (zs:((A word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  EXISTS_TAC `EL n (zs:((A word_loc)heap_address)list)` THEN
  ASM_REWRITE_TAC[heap_el_def; RefBlock_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]) THEN
   (REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC MP3AUX_heap_ok_lookup THEN
      MAP_EVERY EXISTS_TAC [`limit:num`; `FAPPLY (f:(num,num)fmap) ptr`;
        `zs:((A word_loc)heap_address)list`;
        `LENGTH (zs:((A word_loc)heap_address)list)`;
        `(RefTag,[]):data_to_word_memoryProof_tag#(A word_loc)list`; `u:A word_loc`] THEN
      ASM_REWRITE_TAC[GSYM RefBlock_def] THEN
      FIRST_X_ASSUM SUBST1_TAC THEN MATCH_MP_TAC EL_MEM THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC]) THEN
   (MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  SUBGOAL_THEN `all_ts refs (CONS (EL n a') (CONS (data_RefPtr b ptr) stack)) =
                all_ts refs (CONS (data_RefPtr b ptr) stack)` SUBST1_TAC THENL
   [MATCH_MP_TAC MP3AUX_all_ts_find_ref THEN
    MAP_EVERY EXISTS_TAC [`ptr:num`; `bvl_ValueArray a':data_v bvl_ref`] THEN
    ASM_REWRITE_TAC[find_ref_def] THEN MATCH_MP_TAC EL_MEM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL2] THEN BETA_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_deref2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `ALL2 (\z y. v_inv conf y refs (z,f,tf,heap))
                     (zs:((A word_loc)heap_address)list) a'` THEN
      REWRITE_TAC[LIST_REL_EL_EQN] THEN BETA_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[v_inv_def] THEN ASM_REWRITE_TAC[] THEN SIMP[]];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP3AUX_reachable_find_ref THEN
  MAP_EVERY EXISTS_TAC [`bvl_ValueArray a':data_v bvl_ref`; `EL n a':data_v`] THEN
  ASM_REWRITE_TAC[find_ref_def] THEN MATCH_MP_TAC EL_MEM THEN ASM_REWRITE_TAC[]);
   (CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[] THEN
  MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  RVEQ_TAC) THEN
   (SUBGOAL_THEN `b = F` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `y:(A word_loc)heap_address` THEN
  ASM_REWRITE_TAC[heap_el_def] THEN REWRITE_TAC[ThunkBlock_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH; EL; HD; ARITH] THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC MP3AUX_heap_ok_lookup THEN
      MAP_EVERY EXISTS_TAC [`limit:num`; `FAPPLY (f:(num,num)fmap) ptr`;
        `[y:(A word_loc)heap_address]`; `1`;
        `(ThunkTag NotEvaluated,[]):data_to_word_memoryProof_tag#(A word_loc)list`;
        `u:A word_loc`] THEN
      ASM_REWRITE_TAC[GSYM ThunkBlock_def; MEM];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  SUBGOAL_THEN `all_ts refs (CONS a1 (CONS (data_RefPtr F ptr) stack)) =
                all_ts refs (CONS (data_RefPtr F ptr) stack)` SUBST1_TAC THENL
   [MATCH_MP_TAC MP3AUX_all_ts_find_ref THEN
    MAP_EVERY EXISTS_TAC [`ptr:num`; `bvl_Thunk NotEvaluated a1:data_v bvl_ref`] THEN
    ASM_REWRITE_TAC[find_ref_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ALL2] THEN BETA_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_deref1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[v_inv_def] THEN DISJ2_TAC THEN DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`NotEvaluated`; `a1:data_v`; `y:(A word_loc)heap_address`] THEN
    ASM_REWRITE_TAC[] THEN SIMP[];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP3AUX_reachable_find_ref THEN
  MAP_EVERY EXISTS_TAC [`bvl_Thunk NotEvaluated a1:data_v bvl_ref`; `a1:data_v`] THEN
  ASM_REWRITE_TAC[find_ref_def])]);;

(* HOL4 line 6914 *)
let blocks_unique_el = prove
 (`!i xs ts refs t0 n stack.
     i < LENGTH xs /\
     blocks_unique ts (all_vs refs (CONS (data_Block t0 n xs) stack)) ==>
     blocks_unique ts (all_vs refs (CONS (EL i xs) (CONS (data_Block t0 n xs) stack)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!v. MEM v (v_all_vs [EL i xs]) ==>
                    MEM v (v_all_vs [data_Block t0 n xs])` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[v_all_vs_def; APPEND; MEM; MEM_APPEND] THEN
    DISJ2_TAC THEN MATCH_MP_TAC MEM_v_all_vs_EL THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP3AUX_BLOCKS_TAC `all_vs refs (CONS (data_Block t0 n xs) stack)` []);;

(* MP3AUX: all_ts grows with the stack *)
let MP3AUX_all_ts_mono = prove
 (`!refs s1 s2.
     (!x. MEM x s1 ==> MEM x s2) ==> all_ts refs s1 SUBSET all_ts refs s2`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* MP3AUX: the references of an element of a block are references of it *)
let MP3AUX_get_refs_EL = prove
 (`!i xs r t n.
     i < LENGTH xs /\ MEM r (get_refs (EL i xs)) ==>
     MEM r (get_refs (data_Block t n xs))`,
  REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN MESON_TAC[EL_MEM]);;

(* HOL4 line 6931 *)
let el_thm = prove
 (`!conf t0 n xs stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts i.
     abs_ml_inv conf (CONS (data_Block t0 n xs) stack) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     i < LENGTH xs ==>
     ?r roots2 y.
       roots = CONS r roots2 /\ heap_el r i heap = (y,T) /\
       abs_ml_inv conf (CONS (EL i xs) (CONS (data_Block t0 n xs) stack)) refs
         (CONS y roots,heap,be,a,sp,sp1,gens) limit ts`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP3AUX_ASM_HEAD_TAC "abs_ml_inv" (fun th -> ASSUME_TAC th THEN
    MP_TAC(REWRITE_RULE[abs_ml_inv_def; bc_stack_ref_inv_def] th)) THEN
  STRIP_TAC THEN
  MP3AUX_ASM_HEAD_TAC "ALL2" (STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_CONS1]) THEN
  RVEQ_TAC THEN BETA_TAC) THEN
  (SUBGOAL_THEN `~(xs:data_v list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
    ASM_ARITH_TAC; ALL_TAC]) THEN
  (MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `i < LENGTH (xs':((A word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Pointer ptr (wl_Word (ptr_bits conf n (LENGTH (xs':((A word_loc)heap_address)list)))):(A word_loc)heap_address`;
    `t':((A word_loc)heap_address)list`; `EL i (xs':((A word_loc)heap_address)list)`] THEN
  ASM_REWRITE_TAC[heap_el_def; BlockRep_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]) THEN
  (REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC MP3AUX_heap_ok_lookup THEN
      MAP_EVERY EXISTS_TAC [`limit:num`; `ptr:num`;
        `xs':((A word_loc)heap_address)list`;
        `LENGTH (xs':((A word_loc)heap_address)list)`;
        `(BlockTag n,[]):data_to_word_memoryProof_tag#(A word_loc)list`; `u:A word_loc`] THEN
      ASM_REWRITE_TAC[GSYM BlockRep_def] THEN
      FIRST_X_ASSUM SUBST1_TAC THEN MATCH_MP_TAC EL_MEM THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[ALL2] THEN BETA_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `all_ts refs (CONS (data_Block t0 n xs) stack)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP3AUX_all_ts_mono THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_el THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[EVERY2_LENGTH];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) xs
                     (xs':((A word_loc)heap_address)list)` THEN
      REWRITE_TAC[LIST_REL_EL_EQN] THEN BETA_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[v_inv_def] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`ptr:num`; `xs':((A word_loc)heap_address)list`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `reachable_refs (CONS (EL i xs) (CONS (data_Block t0 n xs) stack)) refs m` THEN
  REWRITE_TAC[reachable_refs_def; MEM] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`data_Block t0 n xs`; `r:num`] THEN
    ASM_REWRITE_TAC[MEM] THEN MATCH_MP_TAC MP3AUX_get_refs_EL THEN
    EXISTS_TAC `i:num` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[EVERY2_LENGTH];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]));;

(* HOL4 line 6991 *)
let blocks_unique_new_byte_alt = prove
 (`!ts refs stack ptr fl bs b.
     blocks_unique ts (all_vs refs stack) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvl_ByteArray fl bs) refs)
          (CONS (data_RefPtr b ptr) stack))`,
  MP3AUX_BLOCKS_TAC `all_vs refs stack` []);;

(* HOL4 line 7005 (HOL4 has the marker Abbrev (ws = ...); the port has no  *)
(* Abbrev constant: the plain equation)                                     *)
let new_byte_alt_thm = prove
 (`!conf stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts ws bs ptr fl b.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     ws = LENGTH bs DIV (dimindex (:A) DIV 8) + 1 /\
     ~(ptr IN domain refs) /\ ws + 1 <= sp ==>
     ?heap2.
       heap_store_unused_alt a (sp + sp1)
         (Bytes be fl bs (REPLICATE ws (word 0:A word))) heap = (heap2,T) /\
       abs_ml_inv conf (CONS (data_RefPtr b ptr) stack)
         (insert ptr (bvl_ByteArray fl bs) refs)
         (CONS (Pointer a (wl_Word (word 0))) roots,heap2,be,a + ws + 1,
          sp - (ws + 1),sp1,gens) limit ts`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && lhs (concl th) = `ws:num`
                          then ASSUME_TAC (SYM th) else NO_TAC) THEN
  MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `Bytes be fl bs (REPLICATE ws (word 0:A word))`] IMP_heap_store_unused_alt) THEN
  ASM_REWRITE_TAC[MP3AUX_Bytes_props; LENGTH_REPLICATE] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  EXISTS_TAC `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!q. isSomeDataElement (heap_lookup q (heap2:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list)) <=>
        q = a \/
        isSomeDataElement (heap_lookup q (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))`
   ASSUME_TAC THENL
   [GEN_TAC THEN MP3AUX_ASM_LHS_HEAD_TAC "GSPEC" MP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM; injectivity "heap_address"] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "heap_ok" MP_TAC THEN REWRITE_TAC[heap_ok_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`xs':((A word_loc)heap_address)list`; `n0:num`;
      `d:data_to_word_memoryProof_tag#(A word_loc)list`; `p0:num`; `u0:A word_loc`] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `MEM (Pointer p0 u0) (xs':((A word_loc)heap_address)list)` THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MP3AUX_Bytes_DataElement o SYM) THEN
      REWRITE_TAC[MEM];
      DISJ2_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "gc_kind_inv" MP_TAC THEN REWRITE_TAC[gc_kind_inv_def] THEN
    CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(a + ws + 1) + (sp - (ws + 1)) + sp1 = a + sp + sp1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
        `Bytes be fl bs (REPLICATE ws (word 0:A word))`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `gens:gen_state`] heap_store_unused_alt_gen_state_ok) THEN
      ASM_REWRITE_TAC[MP3AUX_Bytes_props; LENGTH_REPLICATE];
      MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `Bytes be fl bs (REPLICATE ws (word 0:A word))`] heap_store_unused_alt_thm) THEN
      ASM_REWRITE_TAC[MP3AUX_Bytes_props; LENGTH_REPLICATE] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`APPEND (APPEND h0 [Bytes be fl bs (REPLICATE ws (word 0:A word))])
          (heap_expand ((sp + sp1) - (ws + 1))):((A word_loc,
           data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `h2:((A word_loc,data_to_word_memoryProof_tag#
           (A word_loc)list)heap_element)list`] THEN
      SUBGOAL_THEN
       `a + sp + sp1 =
        heap_length (APPEND (APPEND h0 [Bytes be fl bs (REPLICATE ws (word 0:A word))])
          (heap_expand ((sp + sp1) - (ws + 1))):((A word_loc,
           data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)`
       SUBST1_TAC THENL
       [ASM_REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
                        MP3AUX_heap_length_CONS; heap_length_NIL;
                        MP3AUX_Bytes_props; LENGTH_REPLICATE] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[heap_split_length] THEN
      UNDISCH_TAC `ALL (\x. ~isRef x) (h1:((A word_loc,data_to_word_memoryProof_tag#
           (A word_loc)list)heap_element)list)` THEN
      ASM_REWRITE_TAC[ALL_APPEND; ALL; MP3AUX_Bytes_props; heap_expand_def] THEN
      COND_CASES_TAC THEN REWRITE_TAC[ALL; isRef_def] THEN SIMP[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `a + ws + 1 = a + el_length (Bytes be fl bs (REPLICATE ws (word 0:A word))) /\
                  sp - (ws + 1) + sp1 = (sp + sp1) - el_length (Bytes be fl bs (REPLICATE ws (word 0:A word)))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[MP3AUX_Bytes_props; LENGTH_REPLICATE] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[MP3AUX_Bytes_props; LENGTH_REPLICATE]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `~(ptr IN FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `all_ts (insert ptr (bvl_ByteArray fl bs) refs)
                  (CONS (data_RefPtr b ptr) stack) = all_ts refs stack`
   SUBST1_TAC THENL
   [REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; EXTENSION; IN_ELIM_THM;
                MP3AUX_lookup_insert_SOME; MEM] THEN
    X_GEN_TAC `t:num` THEN EQ_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[v_all_ts_def; MEM]) THEN
    TRY(FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[v_all_ts_def; MEM]) THEN
        FIRST_X_ASSUM CONTR_TAC THEN NO_TAC) THEN
    TRY(RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[find_ref_def]) THEN
        FIRST_X_ASSUM CONTR_TAC THEN NO_TAC) THEN
    ASM_MESON_TAC[GSYM lookup_NONE_domain; distinctness "option"];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v (y:(A word_loc)heap_address).
      v_inv conf v refs (y,f,tf,heap) ==>
      v_inv conf v (insert ptr (bvl_ByteArray fl bs) refs)
        (y,f |+ (ptr,a),tf,heap2)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_SUBMAP THEN
    MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
    ASM_REWRITE_TAC[SUBMAP_FUPDATE_EQN; SUBMAP_REFL] THEN
    MATCH_MP_TAC v_inv_ByteArray_insert THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(f:(num,num)fmap) |+ (ptr,a)` THEN EXISTS_TAC `tf:(num,num)fmap` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[fapply_fupdate_update; FDOM_FUPDATE] THEN
    MATCH_MP_TAC INJ_UPDATE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FDOM_FUPDATE; domain_insert] THEN
    UNDISCH_TAC `FDOM (f:(num,num)fmap) SUBSET domain (refs:(data_v bvl_ref)spt)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
     {a | isSomeDataElement (heap_lookup a (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_new_byte_alt THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (CONJ_TAC THENL
   [REWRITE_TAC[ALL2] THEN BETA_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[v_inv_def] THEN
      ASM_REWRITE_TAC[lookup_insert; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
      SIMP[];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack
                     (roots:((A word_loc)heap_address)list)` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_CASES_TAC `n:num = ptr` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM;
                lookup_insert] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ref_edge (insert ptr (bvl_ByteArray fl bs) refs) = ref_edge refs`
    ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[ref_edge_def; lookup_insert] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM lookup_NONE_domain]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  SUBGOAL_THEN `reachable_refs stack refs n` ASSUME_TAC THENL
   [UNDISCH_TAC `reachable_refs (CONS (data_RefPtr b ptr) stack)
                   (insert ptr (bvl_ByteArray fl bs) refs) n` THEN
    ASM_REWRITE_TAC[reachable_refs_def; MEM] THEN STRIP_TAC THENL
     [UNDISCH_TAC `MEM r (get_refs x)` THEN ASM_REWRITE_TAC[get_refs_def; MEM] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `RTC (ref_edge refs) ptr n` THEN
      ONCE_REWRITE_TAC[RTC_CASES_R] THEN ASM_REWRITE_TAC[ref_edge_def] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM lookup_NONE_domain]) THEN
      ASM_REWRITE_TAC[option_CASE];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MP3AUX_bc_ref_inv_transfer THEN
  MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FDOM_FUPDATE; IN_INSERT]) THEN
  ASM_REWRITE_TAC[lookup_insert; FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    UNDISCH_TAC `heap_store_rel (heap:((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)list) heap2` THEN
    REWRITE_TAC[heap_store_rel_def] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    ASM_MESON_TAC[dest_thunk_insert_fresh];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]));;

(* HOL4 line 7153 *)
let ref_eq_thm = prove
 (`!conf p1 p2 stack refs r1 r2 roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (CONS (data_RefPtr T p1) (CONS (data_RefPtr T p2) stack)) refs
       (CONS r1 (CONS r2 roots),heap,be,a,sp,sp1,gens) limit ts ==>
     ((p1 = p2) <=> (r1 = r2)) /\
     ?p1 p2. r1 = Pointer p1 (wl_Word (word 0)) /\ r2 = Pointer p2 (wl_Word (word 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; ALL2] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(BETA_RULE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_inv_RefPtr_T]) THEN
  ASM_REWRITE_TAC[injectivity "heap_address"] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INJ]) THEN ASM_MESON_TAC[]);;

(* MP3AUX: small integers have distinct representations *)
let MP3AUX_Smallnum_11 = prove
 (`!i j. small_int (:A) i /\ small_int (:A) j ==>
         (Smallnum i:A word = Smallnum j <=> i = j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  SUBGOAL_THEN `!k. Smallnum k:A word = iword (&4 * k)` (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `k:int` THEN REWRITE_TAC[data_to_word_Smallnum_def; i2w_def] THEN
    ASM_CASES_TAC `k:int < &0` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `&4 * k:int < &0` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[WORD_SUB_LZERO; INT_ARITH `&4 * (&0 - k):int = --(&4 * k)`];
      SUBGOAL_THEN `~(&4 * k:int < &0)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IWORD_EQ] THEN
  DISCH_TAC THEN MATCH_MP_TAC(INT_ARITH `&4 * i:int = &4 * j ==> i = j`) THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN
  EXISTS_TAC `(&2:int) pow dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&8:int) * &(dimword(:A) DIV 8) <= (&2:int) pow dimindex(:A)` MP_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_POW; INT_OF_NUM_LE; GSYM dimword_def] THEN
    REWRITE_TAC[DIV_MUL_LE];
    RULE_ASSUM_TAC(REWRITE_RULE[small_int_def]) THEN ASM_INT_ARITH_TAC]);;

(* HOL4 line 7164 *)
let num_eq_thm = prove
 (`!conf i1 i2 stack refs r1 r2 roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (CONS (data_Number i1) (CONS (data_Number i2) stack)) refs
       (CONS r1 (CONS r2 roots),heap,be,a,sp,sp1,gens) limit ts /\
     small_int (:A) i1 /\
     small_int (:A) i2 ==>
     ((i1 = i2) <=> (r1 = r2)) /\
     r1 = gc_shared_Data (wl_Word (Smallnum i1:A word)) /\
     r2 = gc_shared_Data (wl_Word (Smallnum i2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; ALL2] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`i1:int`; `i2:int`] MP3AUX_Smallnum_11) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RULE_ASSUM_TAC(BETA_RULE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_inv_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `small_int (:A) i1`; ASSUME `small_int (:A) i2`]) THEN
  ASM_REWRITE_TAC[injectivity "heap_address"; injectivity "word_loc"]);;

(* HOL4 line 7179: Smallnum_i2w *)
let data_to_word_memoryProof_Smallnum_i2w = prove
 (`!i. Smallnum i:A word = iword (&4 * i)`,
  GEN_TAC THEN REWRITE_TAC[data_to_word_Smallnum_def; i2w_def] THEN
  ASM_CASES_TAC `i:int < &0` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&4 * i:int < &0` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_SUB_LZERO; INT_ARITH `&4 * (&0 - i):int = --(&4 * i)`];
    SUBGOAL_THEN `~(&4 * i:int < &0)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_INT_ARITH_TAC]);;

(* HOL4 line 7189 *)
let small_int_IMP_MIN_MAX = prove
 (`!i. good_dimindex (:A) /\ small_int (:A) i ==>
       integer_word_INT_MIN (:A) <= &4 * i /\ &4 * i <= integer_word_INT_MAX (:A)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; small_int_def; IVAL_IWORD_INT_RANGE;
                          dimword_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

(* HOL4 line 7199 *)
let num_less_thm = prove
 (`!i1 i2. good_dimindex (:A) /\ small_int (:A) i1 /\ small_int (:A) i2 ==>
           ((i1 < i2) <=> word_ilt (Smallnum i1) (Smallnum i2:A word))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_ILT; data_to_word_memoryProof_Smallnum_i2w] THEN
  SUBGOAL_THEN `ival (iword (&4 * i1):A word) = &4 * i1 /\
                ival (iword (&4 * i2):A word) = &4 * i2`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC w2i_i2w THEN MATCH_MP_TAC small_int_IMP_MIN_MAX THEN
    ASM_REWRITE_TAC[];
    INT_ARITH_TAC]);;

(* MP3AUX: all_ts, all_vs and reachable_refs only depend on the set of *)
(* stack elements                                                       *)
let MP3AUX_stack_set_eq = prove
 (`!refs s1 s2.
     (!x. MEM x s1 <=> MEM x s2) ==>
     all_ts refs s1 = all_ts refs s2 /\ all_vs refs s1 = all_vs refs s2 /\
     reachable_refs s1 refs = reachable_refs s2 refs`,
  REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF];
    REWRITE_TAC[EXTENSION; MP3AUX_IN_all_vs] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; reachable_refs_def] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 7211 *)
let all_ts_permute = prove
 (`!(refs:(data_v bvl_ref)spt) stack stack'.
     PERM stack stack' ==> all_ts refs stack = all_ts refs stack'`,
  MESON_TAC[MP3AUX_stack_set_eq; PERM_MEM_EQ]);;

(* HOL4 line 7225 *)
let reachable_refs_stack_subset = prove
 (`!x y refs n.
     reachable_refs y refs n /\ set_of_list y SUBSET set_of_list x ==>
     reachable_refs x refs n`,
  REWRITE_TAC[reachable_refs_def; SUBSET; IN_SET_OF_LIST] THEN MESON_TAC[]);;

(* HOL4 line 7235 *)
let MEM_v_all_vs_FST = prove
 (`!xs h0 (h1:A) x.
     MEM (h0,h1) xs /\ MEM x (v_all_vs [h0]) ==> MEM x (v_all_vs (MAP FST xs))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MP3AUX_MEM_v_all_vs] THEN
  EXISTS_TAC `h0:data_v` THEN ASM_REWRITE_TAC[MEM_MAP] THEN
  EXISTS_TAC `(h0:data_v,h1:A)` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 7250 *)
let MEM_v_all_vs_SUBSET = prove
 (`!ys (xs:(data_v#A)list) x.
     set_of_list ys SUBSET set_of_list xs /\
     MEM x (v_all_vs (MAP FST ys)) ==>
     MEM x (v_all_vs (MAP FST xs))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MP3AUX_MEM_v_all_vs] THEN
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[]);;

(* HOL4 line 7266 *)
let blocks_unique_stack_permute = prove
 (`!ys (xs:(data_v#A)list) ts refs stack.
     set_of_list ys SUBSET set_of_list xs /\
     blocks_unique ts (all_vs refs (APPEND (MAP FST xs) stack)) ==>
     blocks_unique ts (all_vs refs (APPEND (MAP FST ys) stack))`,
  MP3AUX_BLOCKS_TAC `all_vs refs (APPEND (MAP FST (xs:(data_v#A)list)) stack)`
    [SUBSET; IN_SET_OF_LIST; MEM_MAP]);;

(* HOL4 line 7281 *)
let abs_ml_inv_stack_permute = prove
 (`!conf stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts xs ys.
     abs_ml_inv conf (APPEND (MAP FST xs) stack) refs
       (APPEND (MAP SND xs) roots,heap,be,a,sp,sp1,gens) limit ts /\
     set_of_list ys SUBSET set_of_list xs ==>
     abs_ml_inv conf (APPEND (MAP FST ys) stack) refs
       (APPEND (MAP SND ys) roots,heap,be,a,sp,sp1,gens) limit ts`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v (y:(A word_loc)heap_address).
      v_inv conf v refs (y,f,tf,heap) /\
      v IN all_vs refs (APPEND (MAP FST (ys:(data_v#(A word_loc)heap_address)list)) stack) ==>
      v_inv conf v refs
        (y,f,DRESTRICT tf (all_ts refs (APPEND (MAP FST ys) stack)),heap)`
   ASSUME_TAC THENL [REWRITE_TAC[MP3AUX_v_inv_restrict]; ALL_TAC] THEN
  EXISTS_TAC `f:(num,num)fmap` THEN
  EXISTS_TAC `DRESTRICT (tf:(num,num)fmap)
    (all_ts refs (APPEND (MAP FST (ys:(data_v#(A word_loc)heap_address)list)) stack))` THEN
  MP_TAC(ISPECL [`tf:(num,num)fmap`;
    `all_ts refs (APPEND (MAP FST (ys:(data_v#(A word_loc)heap_address)list)) stack)`;
    `{a | isSomeDataElement (heap_lookup a (heap:((A word_loc,data_to_word_memoryProof_tag#
          (A word_loc)list)heap_element)list))}`;
    `ts:num`] MP3AUX_DRESTRICT_tf) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_stack_permute THEN
    EXISTS_TAC `xs:(data_v#(A word_loc)heap_address)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap))
      (APPEND (MAP FST (xs:(data_v#(A word_loc)heap_address)list)) stack)
      (APPEND (MAP SND xs) roots)` THEN
    SIMP_TAC[LIST_REL_APPEND_EQ; LENGTH_MAP; EVERY2_MAP_FST_SND] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ALL (\(x,y). v_inv conf x refs (y,f,tf,heap))
                     (xs:(data_v#(A word_loc)heap_address)list)` THEN
      UNDISCH_TAC `set_of_list (ys:(data_v#(A word_loc)heap_address)list) SUBSET
                   set_of_list xs` THEN
      REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; SUBSET; IN_SET_OF_LIST] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC MEM_stack_all_vs THEN REWRITE_TAC[MEM_APPEND; MEM_MAP] THEN
        DISJ1_TAC THEN EXISTS_TAC `(p1:data_v,p2:(A word_loc)heap_address)` THEN
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) stack
                     (roots:((A word_loc)heap_address)list)` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM_APPEND]];
    ALL_TAC]) THEN
  (X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC MP3AUX_bc_ref_inv_transfer THEN
  MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC reachable_refs_stack_subset THEN
    EXISTS_TAC `APPEND (MAP FST (ys:(data_v#(A word_loc)heap_address)list)) stack` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `set_of_list (ys:(data_v#(A word_loc)heap_address)list) SUBSET
                 set_of_list xs` THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_APPEND; MEM_MAP] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP3AUX_IN_all_vs_find_ref THEN ASM_MESON_TAC[]]));;

(* HOL4 line 7385 *)
let pop_thm = prove
 (`!conf xs stack refs rs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (APPEND xs stack) refs
       (APPEND rs roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH xs = LENGTH rs ==>
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `stack:data_v list`;
    `refs:(data_v bvl_ref)spt`; `roots:((A word_loc)heap_address)list`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`;
    `ZIP (xs:data_v list) (rs:((A word_loc)heap_address)list)`;
    `[]:(data_v#(A word_loc)heap_address)list`] abs_ml_inv_stack_permute) THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; MAP; APPEND; set_of_list; EMPTY_SUBSET]);;

(* HOL4 line 7398 *)
let blocks_unique_duplicate = prove
 (`!ts refs xs stack.
     blocks_unique ts (all_vs refs (APPEND xs stack)) ==>
     blocks_unique ts (all_vs refs (APPEND (APPEND xs xs) stack))`,
  MP3AUX_BLOCKS_TAC `all_vs refs (APPEND xs stack)` []);;

(* HOL4 line 7411 *)
let duplicate_thm = prove
 (`!conf xs stack refs rs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (APPEND xs stack) refs
       (APPEND rs roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH xs = LENGTH rs ==>
     abs_ml_inv conf (APPEND (APPEND xs xs) stack) refs
       (APPEND (APPEND rs rs) roots,heap,be,a,sp,sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  MP_TAC(ISPECL [`refs:(data_v bvl_ref)spt`; `APPEND (APPEND xs xs) stack:data_v list`;
                 `APPEND xs stack:data_v list`] MP3AUX_stack_set_eq) THEN
  ANTS_TAC THENL [REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap)) (APPEND xs stack)
                 (APPEND (rs:((A word_loc)heap_address)list) roots)` THEN
  ASM_SIMP_TAC[LIST_REL_APPEND_EQ; LENGTH_APPEND] THEN SIMP_TAC[]);;

(* HOL4 line 7427 *)
let duplicate1_thm = prove
 (`!conf x1 stack refs r1 roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (CONS x1 stack) refs (CONS r1 roots,heap,be,a,sp,sp1,gens)
       limit ts ==>
     abs_ml_inv conf (CONS x1 (CONS x1 stack)) refs
       (CONS r1 (CONS r1 roots),heap,be,a,sp,sp1,gens) limit ts`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL(ISPECL [`conf:data_to_word_config`; `[x1:data_v]`; `stack:data_v list`;
    `refs:(data_v bvl_ref)spt`; `[r1:(A word_loc)heap_address]`] duplicate_thm)) THEN
  ASM_REWRITE_TAC[APPEND; LENGTH]);;

(* HOL4 line 7433 *)
let blocks_unique_move = prove
 (`!ts refs xs1 xs2 xs3 stack.
     blocks_unique ts (all_vs refs (APPEND (APPEND (APPEND xs1 xs2) xs3) stack)) ==>
     blocks_unique ts (all_vs refs (APPEND (APPEND (APPEND xs1 xs3) xs2) stack))`,
  MP3AUX_BLOCKS_TAC `all_vs refs (APPEND (APPEND (APPEND xs1 xs2) xs3) stack)` []);;

(* HOL4 line 7446 *)
let move_thm = prove
 (`!conf stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts xs1 rs1 xs2 rs2 xs3 rs3.
     abs_ml_inv conf (APPEND (APPEND (APPEND xs1 xs2) xs3) stack) refs
       (APPEND (APPEND (APPEND rs1 rs2) rs3) roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH xs1 = LENGTH rs1 /\
     LENGTH xs2 = LENGTH rs2 /\
     LENGTH xs3 = LENGTH rs3 ==>
     abs_ml_inv conf (APPEND (APPEND (APPEND xs1 xs3) xs2) stack) refs
       (APPEND (APPEND (APPEND rs1 rs3) rs2) roots,heap,be,a,sp,sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  MP_TAC(ISPECL [`refs:(data_v bvl_ref)spt`;
                 `APPEND (APPEND (APPEND xs1 xs3) xs2) stack:data_v list`;
                 `APPEND (APPEND (APPEND xs1 xs2) xs3) stack:data_v list`]
    MP3AUX_stack_set_eq) THEN
  ANTS_TAC THENL [REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,heap))
                 (APPEND (APPEND (APPEND xs1 xs2) xs3) stack)
                 (APPEND (APPEND (APPEND (rs1:((A word_loc)heap_address)list) rs2) rs3)
                         roots)` THEN
  ASM_SIMP_TAC[LIST_REL_APPEND_EQ; LENGTH_APPEND] THEN SIMP_TAC[]);;

(* HOL4 line 7469 *)
let split1_thm = prove
 (`!conf xs1 stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (APPEND xs1 stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
     ?rs1 roots1. roots = APPEND rs1 roots1 /\ LENGTH rs1 = LENGTH xs1`,
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  ASM_MESON_TAC[EVERY2_LENGTH]);;

(* HOL4 line 7479 *)
let split2_thm = prove
 (`!conf xs1 xs2 stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (APPEND (APPEND xs1 xs2) stack) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts ==>
     ?rs1 rs2 roots1. roots = APPEND (APPEND rs1 rs2) roots1 /\
       LENGTH rs1 = LENGTH xs1 /\ LENGTH rs2 = LENGTH xs2`,
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; GSYM APPEND_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  ASM_MESON_TAC[EVERY2_LENGTH]);;

(* HOL4 line 7490 *)
let split3_thm = prove
 (`!conf xs1 xs2 xs3 stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (APPEND (APPEND (APPEND xs1 xs2) xs3) stack) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts ==>
     ?rs1 rs2 rs3 roots1. roots = APPEND (APPEND (APPEND rs1 rs2) rs3) roots1 /\
       LENGTH rs1 = LENGTH xs1 /\ LENGTH rs2 = LENGTH xs2 /\
       LENGTH rs3 = LENGTH xs3`,
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; GSYM APPEND_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  ASM_MESON_TAC[EVERY2_LENGTH]);;

(* HOL4 line 7502 *)
let abs_ml_inv_Num = prove
 (`!conf stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts i.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     small_int (:A) i ==>
     abs_ml_inv conf (CONS (data_Number i) stack) refs
       (CONS (gc_shared_Data (wl_Word (Smallnum i:A word))) roots,heap,be,a,sp,sp1,
        gens) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP3AUX_ASM_HEAD_TAC "roots_ok" MP_TAC THEN
    REWRITE_TAC[roots_ok_def; MEM; distinctness "heap_address"] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  ASM_SIMP_TAC[all_ts_cons_no_block; distinctness "data_v"; ALL2] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC blocks_unique_Number THEN EXISTS_TAC `[]:data_v list` THEN
    ASM_REWRITE_TAC[APPEND];
    ASM_REWRITE_TAC[v_inv_def];
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    REWRITE_TAC[reachable_refs_def; MEM; get_refs_def] THEN
    SIMP[LEFT_AND_OVER_OR; RIGHT_OR_DISTRIB; EXISTS_OR_THM; get_refs_def; MEM]]);;

(* HOL4 line 7517 *)
let heap_store_unused_IMP_length = prove
 (`!a sp' (x:(A,B)heap_element) heap heap2.
     heap_store_unused a sp' x heap = (heap2,T) ==>
     heap_length heap2 = heap_length heap`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  RVEQ_TAC THEN REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[heap_length_APPEND; MP3AUX_heap_length_CONS] THEN
  ARITH_TAC);;

(* HOL4 line 7527 *)
let heap_store_unused_alt_IMP_length = prove
 (`!a sp' (x:(A,B)heap_element) heap heap2.
     heap_store_unused_alt a sp' x heap = (heap2,T) ==>
     heap_length heap2 = heap_length heap`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_store_unused_alt_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  RVEQ_TAC THEN REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[heap_length_APPEND; MP3AUX_heap_length_CONS] THEN
  ARITH_TAC);;

(* HOL4 line 7542: pointers have tag and len bits *)
let pointer_bits_def = cake_def
  `pointer_bits conf (abs_heap:((A,data_to_word_memoryProof_tag#B list)
                                heap_element)list) n =
     match heap_lookup n abs_heap with
       SOME (DataElement xs l (BlockTag tag,[])) ->
         word_or (maxout_bits (LENGTH xs) (data_to_word_config_len_bits conf)
                    (data_to_word_config_tag_bits conf + 2))
                 (word_or (maxout_bits tag (data_to_word_config_tag_bits conf) 2)
                          (word 1))
     | _ -> all_ones (data_to_word_config_len_bits conf +
                      data_to_word_config_tag_bits conf + 1) 0:C word`;;

(* HOL4 line 7552 *)
let is_all_ones_def = cake_def
  `is_all_ones m n (w:A word) <=> word_and (all_ones m n) w = all_ones m n`;;

(* HOL4 line 7556 *)
let decode_maxout_def = cake_def
  `decode_maxout l n (w:A word) =
     if is_all_ones (n + l) n w then NONE
     else SOME (word_ishr (word_bits (n + l) n w) n)`;;

(* HOL4 line 7561 *)
let decode_addr_def = cake_def
  `decode_addr conf (w:A word) =
     (decode_maxout (data_to_word_config_len_bits conf)
        (data_to_word_config_tag_bits conf + 2) w,
      decode_maxout (data_to_word_config_tag_bits conf) 2 w)`;;

(* HOL4 line 7567 *)
let get_addr_def = cake_def
  `get_addr conf n w =
     word_or (word_shl (word n) (shift_length conf)) (get_lowerbits conf w):A word`;;

(* HOL4 line 7572 *)
let word_addr_def = cake_def
  `(word_addr conf (gc_shared_Data (wl_Loc l1 l2)) = wl_Loc l1 0) /\
   (word_addr conf (gc_shared_Data (wl_Word v)) =
      wl_Word (word_and v (word_not (word 1))):A word_loc) /\
   (word_addr conf (Pointer n w) = wl_Word (get_addr conf n w))`;;

(* HOL4 line 7578 *)
let b2w_def = prove
 (`(b2w T = word 1:A word) /\ (b2w F = word 0:A word)`,
  REWRITE_TAC[multiword_b2w_def; BITVAL_CLAUSES]);;

(* HOL4 line 7584 *)
let thunk_tag_to_bits_def = cake_def
  `thunk_tag_to_bits Evaluated = word 1:A word /\
   thunk_tag_to_bits NotEvaluated = word 0`;;

(* HOL4 line 7589.  The header word: BlockTag ...00[11] here i in ...i[11]   *)
(* must be 0 for the GC; RefTag ...010[11] (i must be 0); ThunkTag e         *)
(* ...e110[11] (i must be 0); Word64Tag ...011[11] (i must be 1); NumTag    *)
(* ...111[11] or ...011[11] (i must be 1); BytesTag ...101[11] or            *)
(* ...001[11] (compare-by-contents; i must be 1)                            *)
let word_payload_def = cake_def
  `(word_payload ys l (BlockTag n) (qs:(A word_loc)list) conf =
      (make_header conf (word_shl (word n) 2) (LENGTH ys),
       MAP (word_addr conf) ys,
       (qs = [] /\ LENGTH ys = l /\
        encode_header conf (n * 4) (LENGTH ys) =
          SOME (make_header conf (word_shl (word n) 2) (LENGTH ys):A word)))) /\
   (word_payload ys l RefTag qs conf =
      (make_header conf (word 2) (LENGTH ys),
       MAP (word_addr conf) ys,
       (qs = [] /\ LENGTH ys = l))) /\
   (word_payload ys l (ThunkTag e) qs conf =
      (make_header conf (word_or (word_shl (thunk_tag_to_bits e) 3) (word 6))
         (LENGTH ys),
       MAP (word_addr conf) ys,
       (qs = [] /\ LENGTH ys = 1 /\ l = 1))) /\
   (word_payload ys l Word64Tag qs conf =
      (make_header conf (word 3) l,
       qs, (ys = [] /\ LENGTH qs = l /\
            IS_SOME (encode_header conf 3 l:(A word)option)))) /\
   (word_payload ys l (NumTag b) qs conf =
      (make_header conf (word_or (word_shl (b2w b) 2) (word 3):A word) (LENGTH qs),
       qs, (ys = [] /\ LENGTH qs = l /\
            IS_SOME (encode_header conf
                       (val (word_or (word_shl (b2w b) 2) (word 3):A word))
                       (LENGTH qs):(A word)option)))) /\
   (word_payload ys l (BytesTag fl n) qs conf =
      (make_byte_header conf fl n:A word,
       qs, (ys = [] /\ LENGTH qs = l /\
            (let k = if dimindex(:A) = 32 then 2 else 3 in
             n + 2 EXP k < 2 EXP (data_to_word_config_len_size conf + k)))))`;;

(* MP3AUX: bit 2 of a header is bit 0 of its tag *)
let MP3AUX_bit2_make_header = prove
 (`!conf (tag:A word) len.
     data_to_word_config_len_size conf + 2 < dimindex (:A) ==>
     (bit 2 (make_header conf tag len) <=> bit 0 tag)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[make_header_def; LET_DEF; LET_END_DEF; BIT_WORD_OR; BIT_WORD_SHL;
              BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  SUBGOAL_THEN `2 < dimindex(:A) /\
                ~(dimindex (:A) - data_to_word_config_len_size conf <= 2)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[SUB_REFL]]);;

(* MP3AUX: bit 2 of a byte array header is set *)
let MP3AUX_bit2_make_byte_header = prove
 (`!conf fl n. 2 < dimindex (:A) ==> bit 2 (make_byte_header conf fl n:A word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[make_byte_header_def; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[BIT_WORD_OR; BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 7628 *)
let word_payload_T_IMP = prove
 (`!l5 n5 tag r conf (h:A word) ts.
     word_payload l5 n5 tag r conf = (h,ts,T) /\
     good_dimindex (:A) /\ data_to_word_config_len_size conf + 2 < dimindex (:A) ==>
     n5 = LENGTH ts /\
     if bit 2 h then l5 = [] else ts = MAP (word_addr conf) l5`,
  REPEAT GEN_TAC THEN CASES_ON `tag:data_to_word_memoryProof_tag` THEN
  REWRITE_TAC[word_payload_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  (SUBGOAL_THEN `0 < dimindex(:A) /\ 2 < dimindex(:A)` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[MP3AUX_bit2_make_header; MP3AUX_bit2_make_byte_header; LENGTH_MAP] THEN
  ASM_REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 7643 (as in HOL4, the word type B of the heap element is     *)
(* independent of the address type A here; word_heap identifies them)       *)
let word_el_def = cake_def
  `(word_el (a:A word) (Unused l) conf = word_list_exists a (l + 1)) /\
   (word_el a (ForwardPointer n d l) conf =
      set_sep_one (a,wl_Word (word_shl (word n) 2)) STAR
      word_list_exists (word_add a bytes_in_word) l) /\
   (word_el a (DataElement ys l (tag,(qs:((B)word_loc)list))) conf =
      let (h,ts,c) = word_payload ys l tag qs conf in
      misc_word_list a (CONS (wl_Word h) ts) STAR
      cond (LENGTH ts < 2 EXP (dimindex (:A) - 4) /\
            decode_length conf h = word (LENGTH ts) /\ c))`;;

(* HOL4 line 7655 *)
let word_heap_def = cake_def
  `(word_heap (a:A word)
      ([]:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) conf = emp) /\
   (word_heap a (CONS x xs) conf =
      word_el a x conf STAR
      word_heap (word_add a (word_mul bytes_in_word (word (el_length x)))) xs conf)`;;

(* HOL4 line 7662 *)
let gen_starts_in_store_def = cake_def
  `(gen_starts_in_store c (GenState _ gen_starts) (SOME (wl_Word (w:A word))) <=>
      (!gen_sizes.
         data_to_word_config_gc_kind c = Generational gen_sizes ==>
         LENGTH gen_starts = LENGTH gen_sizes /\
         !x xs. gen_starts = CONS x xs ==> w = word_mul bytes_in_word (word x))) /\
   (gen_starts_in_store c _ _ <=> F)`;;

(* HOL4 line 7672 *)
let gen_starts_in_store_IMP = prove
 (`!c gens x. gen_starts_in_store c gens x ==> ?w:A word. x = SOME (wl_Word w)`,
  REPEAT GEN_TAC THEN CASES_ON `gens:gen_state` THEN
  MP_TAC(ISPEC `x:(A word_loc)option` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[gen_starts_in_store_def] THEN
  MP_TAC(ISPEC `a:A word_loc` (cases "word_loc")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[gen_starts_in_store_def; option_INJ; injectivity "word_loc"] THEN
  MESON_TAC[]);;

(* HOL4 line 7679 *)
let glob_real_inv_def = cake_def
  `glob_real_inv c (curr:A word) globals globreal <=>
     ?w. globals = SOME (wl_Word w) /\
         globreal = SOME (wl_Word (word_add curr
                     (word_shl (word_ushr w (shift_length c))
                               (backend_common_word_shift (:A)))))`;;

(* HOL4 line 7685 *)
let heap_in_memory_store_def = cake_def
  `heap_in_memory_store heap a sp sp1 gens c s (m:A word->A word_loc) dm limit <=>
     heap_length heap <= dimword (:A) DIV (2 EXP shift_length c) /\
     (heap_length heap + 3) * (dimindex (:A) DIV 8) < dimword (:A) /\
     backend_common_word_shift (:A) <= shift_length c /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex (:A) /\
     shift_length c < dimindex (:A) /\ Globals IN FDOM s /\
     ?curr other.
       byte_aligned curr /\ byte_aligned other /\
       FLOOKUP s CurrHeap = SOME (wl_Word (curr:A word)) /\
       FLOOKUP s OtherHeap = SOME (wl_Word other) /\
       FLOOKUP s NextFree =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word a)))) /\
       FLOOKUP s TriggerGC =
         SOME (wl_Word (word_add curr (word_mul bytes_in_word (word (a + sp))))) /\
       FLOOKUP s EndOfHeap =
         SOME (wl_Word (word_add curr
                 (word_mul bytes_in_word (word (a + sp + sp1))))) /\
       FLOOKUP s HeapLength = SOME (wl_Word (word_mul bytes_in_word (word limit))) /\
       glob_real_inv c curr (FLOOKUP s Globals) (FLOOKUP s GlobReal) /\
       gen_starts_in_store c gens (FLOOKUP s GenStart) /\
       (word_heap curr heap c STAR word_heap other (heap_expand limit) c)
         (fun2set (m,dm))`;;

(* HOL4 line 7707 *)
let word_ml_inv_def = cake_def
  `word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack <=>
     ?hs. abs_ml_inv c (MAP FST stack) refs (hs,heap,be,a,sp,sp1,gens) limit ts /\
          ALL2 (\v w. word_addr c v = w) hs (MAP SND stack:(A word_loc)list)`;;

(* HOL4 line 7713 *)
let IMP_THE_EQ = prove
 (`!x (w:A). x = SOME w ==> THE x = w`,
  SIMP_TAC[THE_DEF]);;

(* HOL4 line 7719 (the argument space is spc here: space is a constant of *)
(* data_space)                                                              *)
let memory_rel_def = cake_def
  `memory_rel c be ts refs spc st (m:A word -> A word_loc) dm vars <=>
     ?heap limit a sp sp1 gens.
       heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
       word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs vars /\
       (limit + 3) * (dimindex (:A) DIV 8) + 1 < dimword (:A) /\ spc <= sp`;;

(* HOL4 line 7727 *)
let EVERY2_MAP_MAP = prove
 (`!(P:B->C->bool) (f:A->B) g xs.
     ALL2 P (MAP f xs) (MAP g xs) = ALL (\x. P (f x) (g x)) xs`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL2; ALL]);;

(* HOL4 line 7733 *)
let MEM_FIRST_EL = prove
 (`!xs (x:A).
     MEM x xs <=>
     ?n. n < LENGTH xs /\ EL n xs = x /\
         !m. m < n ==> ~(EL m xs = EL n xs)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[MEM_EXISTS_EL] THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[CONJ_SYM]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[num_WOP]
      `(?n. P n) ==> ?n. P n /\ !m. m < n ==> ~P m`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LT_TRANS];
    REWRITE_TAC[MEM_EXISTS_EL] THEN MESON_TAC[]]);;

(* HOL4 line 7750 *)
let ALOOKUP_ZIP_EL = prove
 (`!(xs:A list) (hs:B list) n.
     n < LENGTH xs /\ LENGTH hs = LENGTH xs /\
     (!m. m < n ==> ~(EL m xs = EL n xs)) ==>
     ALOOKUP (ZIP xs hs) (EL n xs) = SOME (EL n hs)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `hs:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP; ALOOKUP_def] THEN
  X_GEN_TAC `n:num` THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((h:A) = EL n' t)` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; LT_0]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN ASM_REWRITE_TAC[EL; TL; LT_SUC]);;

(* HOL4 line 7765 *)
let word_ml_inv_rearrange = prove
 (`!heap be a sp sp1 gens limit ts c refs (xs:(data_v#A word_loc)list) ys.
     (!x. MEM x ys ==> MEM x xs) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs xs ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs ys`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[word_ml_inv_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (hs:((A word_loc)heap_address)list) = LENGTH (xs:(data_v#A word_loc)list)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP EVERY2_LENGTH) THEN REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. MEM y ys ==>
        ?n. n < LENGTH (xs:(data_v#A word_loc)list) /\ EL n xs = y /\
            ALOOKUP (ZIP xs (hs:((A word_loc)heap_address)list)) y = SOME (EL n hs)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `MEM (y:data_v#A word_loc) xs` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MEM_FIRST_EL] THEN STRIP_TAC THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ALOOKUP_ZIP_EL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `MAP (\y. THE (ALOOKUP (ZIP xs (hs:((A word_loc)heap_address)list)) y))
                  (ys:(data_v#A word_loc)list)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[EVERY2_MAP_MAP; GSYM ALL_MEM] THEN X_GEN_TAC `y:data_v#A word_loc` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:data_v#A word_loc`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
    UNDISCH_TAC `ALL2 (\v w. word_addr c v = w) (hs:((A word_loc)heap_address)list)
                   (MAP SND (xs:(data_v#A word_loc)list))` THEN
    REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_MAP] THEN BETA_TAC THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[EL_MAP]]) THEN
  (MP_TAC(ISPECL [`c:data_to_word_config`; `[]:data_v list`; `refs:(data_v bvl_ref)spt`;
    `[]:((A word_loc)heap_address)list`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`;
    `ZIP (MAP FST (xs:(data_v#A word_loc)list)) (hs:((A word_loc)heap_address)list)`;
    `MAP (\y. FST y,THE (ALOOKUP (ZIP xs (hs:((A word_loc)heap_address)list)) y))
         (ys:(data_v#A word_loc)list)`] abs_ml_inv_stack_permute) THEN
  REWRITE_TAC[APPEND_NIL; GSYM MAP_o; o_DEF] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; LENGTH_MAP] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_MAP] THEN
  X_GEN_TAC `p:data_v#(A word_loc)heap_address` THEN
  DISCH_THEN(X_CHOOSE_THEN `y:data_v#A word_loc` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:data_v#A word_loc`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[LENGTH_ZIP; LENGTH_MAP; EL_ZIP; EL_MAP]));;

(* HOL4 line 7811 *)
let memory_rel_rearrange = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm xs ys.
     (!x. MEM x ys ==> MEM x xs) ==>
     memory_rel c be ts refs sp st m dm xs ==>
     memory_rel c be ts refs sp st m dm ys`,
  REWRITE_TAC[memory_rel_def] THEN MESON_TAC[word_ml_inv_rearrange]);;

(* HOL4 line 7821 *)
let memory_rel_tl = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x xs.
     memory_rel c be ts refs sp st m dm (CONS x xs) ==>
     memory_rel c be ts refs sp st m dm xs`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN SIMP_TAC[MEM]);;

(* MP3AUX: masking off bit 0 *)
let MP3AUX_and_neg2 = prove
 (`!x:A word. word_and (word_neg (word 2)) x = x <=> ~ODD(val x)`,
  GEN_TAC THEN
  SUBGOAL_THEN `word_neg (word 2):A word = word_not (word 1)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[GSYM BIT_LSB; WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_NOT;
              BIT_WORD_1] THEN
  MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN
  MESON_TAC[ARITH_RULE `1 <= n ==> 0 < n`]);;

(* MP3AUX: the word of the empty block with tag 0 *)
let MP3AUX_BlockNil_0 = prove
 (`good_dimindex (:A) ==>
   BlockNil 0 = word 2:A word /\
   word_and (word 2) (word_not (word 1)) = word 2:A word /\
   0 < dimword (:A) DIV 16`,
  REWRITE_TAC[good_dimindex_def; BlockNil_def; dimword_def] THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add (word_shl (word 0) 4) (word 2):A word = word 2`] THEN
  REWRITE_TAC[WORD_RULE `word_not (word 1):A word = word_neg (word 2)`] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
  REWRITE_TAC[MP3AUX_and_neg2; ODD_VAL_WORD] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV));;

(* HOL4 line 7828 *)
let word_ml_inv_Unit = prove
 (`!heap be a sp sp1 gens limit ts c refs ws.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs ws /\
     good_dimindex (:A) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (CONS (data_Unit,wl_Word (word 2:A word)) ws)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ml_inv_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MP3AUX_BlockNil_0) THEN
  EXISTS_TAC `CONS (gc_shared_Data (wl_Word (BlockNil 0:A word))) hs` THEN
  REWRITE_TAC[MAP; ALL2; data_Unit_def; tuple_tag_def] THEN CONJ_TAC THENL
   [MATCH_MP_TAC cons_thm_EMPTY THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[word_addr_def]]);;

(* HOL4 line 7844 *)
let memory_rel_Unit = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm xs.
     memory_rel c be ts refs sp st m dm xs /\ good_dimindex (:A) ==>
     memory_rel c be ts refs sp st m dm (CONS (data_Unit,wl_Word (word 2:A word)) xs)`,
  REWRITE_TAC[memory_rel_def] THEN MESON_TAC[word_ml_inv_Unit]);;

(* HOL4 line 7852 *)
let get_lowerbits_LSL_shift_length = prove
 (`!conf a. word_ushr (get_lowerbits conf a) (shift_length conf) = word 0:A word`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `a:A word_loc` (cases "word_loc")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[get_lowerbits_def] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OR; BIT_WORD_BITS;
              BIT_WORD_1; BIT_WORD_0; shift_length_def; small_shift_length_def] THEN
  ARITH_TAC);;

(* HOL4 line 7860 *)
let get_real_addr_def = cake_def
  `get_real_addr conf st (w:A word) =
     let k = backend_common_word_shift (:A) in
     match FLOOKUP st CurrHeap with
       SOME (wl_Word curr) ->
         if k = shift_length conf /\ data_to_word_config_len_bits conf = 0 /\
            data_to_word_config_tag_bits conf = 0
         then SOME (word_sub (word_add curr w) (word 1))
         else
           if k <= data_to_word_config_pad_bits conf + 1
           then SOME (word_add curr (word_ushr w (shift_length conf - k)))
           else SOME (word_add curr (word_shl (word_ushr w (shift_length conf)) k))
     | _ -> NONE`;;

(* HOL4 line 7874 *)
let get_real_offset_def = cake_def
  `get_real_offset (w:A word) =
     if dimindex (:A) = 32
     then SOME (word_add w bytes_in_word)
     else SOME (word_add (word_shl w 1) bytes_in_word)`;;

(* HOL4 line 7880 *)
let get_real_simple_addr_def = cake_def
  `get_real_simple_addr conf st (w:A word) =
     match FLOOKUP st CurrHeap with
       SOME (wl_Word curr) ->
         SOME (word_add curr (word_shl (word_ushr w (shift_length conf))
                                       (backend_common_word_shift (:A))))
     | _ -> NONE`;;

(* HOL4 line 7887 *)
let or_1 = prove
 (`!w:A word. word_or (word_bits 0 0 w) (word 1) = word 1`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_BITS; BIT_WORD_1] THEN
  REWRITE_TAC[ADD_CLAUSES; LE] THEN MESON_TAC[]);;

(* MP3AUX: the bits of get_lowerbits are below small_shift_length *)
let MP3AUX_bit_get_lowerbits = prove
 (`!c w i. bit i (get_lowerbits c w:A word) ==> i < small_shift_length c`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `w:A word_loc` (cases "word_loc")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[get_lowerbits_def; BIT_WORD_OR; BIT_WORD_BITS;
                                 BIT_WORD_1; small_shift_length_def] THEN
  ARITH_TAC);;

(* MP3AUX: the bits of word n vanish where n * 2 EXP sl would overflow *)
let MP3AUX_word_n_bits = prove
 (`!n sl j. n * 2 EXP sl < dimword(:A) /\ dimindex(:A) <= j + sl ==>
            ~bit j (word n:A word)`,
  REWRITE_TAC[BIT_WORD; dimword_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP j` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DIV_LT th]))
  THENL
   [SUBGOAL_THEN `n * 2 EXP sl < 2 EXP j * 2 EXP sl` MP_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP dimindex(:A)` THEN
      ASM_REWRITE_TAC[GSYM EXP_ADD; LE_EXP] THEN ASM_ARITH_TAC;
      SIMP_TAC[LT_MULT_RCANCEL]];
    FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN REWRITE_TAC[ARITH]]);;

(* MP3AUX: shifting a pointer word back gives its heap address *)
let MP3AUX_get_addr_ushr = prove
 (`!c n w. n * 2 EXP shift_length c < dimword(:A) ==>
           word_ushr (get_addr c n w) (shift_length c) = word n:A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_USHR; get_addr_def; BIT_WORD_OR; BIT_WORD_SHL;
              ARITH_RULE `sl <= i + sl`; ADD_SUB] THEN
  SUBGOAL_THEN `~bit (i + shift_length c) (get_lowerbits c w:A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN(MP_TAC o MATCH_MP MP3AUX_bit_get_lowerbits) THEN
    REWRITE_TAC[shift_length_def; small_shift_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i + shift_length c < dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MP3AUX_word_n_bits THEN EXISTS_TAC `shift_length c` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* MP3AUX: the same with a shorter shift *)
let MP3AUX_get_addr_ushr2 = prove
 (`!c n w k. n * 2 EXP shift_length c < dimword(:A) /\
             k <= data_to_word_config_pad_bits c + 1 ==>
             word_ushr (get_addr c n w) (shift_length c - k) =
             word_shl (word n) k:A word`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_USHR; get_addr_def; BIT_WORD_OR; BIT_WORD_SHL] THEN
  SUBGOAL_THEN `~bit (i + (shift_length c - k)) (get_lowerbits c w:A word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN(MP_TAC o MATCH_MP MP3AUX_bit_get_lowerbits) THEN
    UNDISCH_TAC `k <= data_to_word_config_pad_bits c + 1` THEN
    REWRITE_TAC[shift_length_def; small_shift_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `k <= shift_length c` ASSUME_TAC THENL
   [UNDISCH_TAC `k <= data_to_word_config_pad_bits c + 1` THEN
    REWRITE_TAC[shift_length_def] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k <= i` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `(i + shift_length c - k) - shift_length c = i - k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `k <= i /\ k <= sl ==> sl <= i + sl - k`] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= i /\ k <= sl ==> sl <= i + sl - k`] THEN
  ASM_CASES_TAC `i + shift_length c - k < dimindex(:A)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MP3AUX_word_n_bits THEN EXISTS_TAC `shift_length c` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* MP3AUX: an address below dimword DIV 2 EXP sl does not overflow *)
let MP3AUX_lt_div_mult = prove
 (`!n a sl. n < a DIV 2 EXP sl ==> n * 2 EXP sl < a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 EXP sl`; `a:num`; `n + 1`] LE_RDIV_EQ) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`] THEN
  SUBGOAL_THEN `~(2 EXP sl = 0)` MP_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

(* HOL4 line 7896 *)
let get_real_addr_get_addr = prove
 (`!heap c n (anything:(B,C)heap_element) st (curr:A word) w.
     heap_length heap <= dimword (:A) DIV (2 EXP shift_length c) /\
     heap_lookup n heap = SOME anything /\
     FLOOKUP st CurrHeap = SOME (wl_Word curr) /\
     good_dimindex (:A) ==>
     get_real_simple_addr c st (get_addr c n w) =
       SOME (word_add curr (word_mul (word n) bytes_in_word)) /\
     get_real_addr c st (get_addr c n w) =
       SOME (word_add curr (word_mul (word n) bytes_in_word))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n * 2 EXP shift_length c < dimword(:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC MP3AUX_lt_div_mult THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_lookup_LESS) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `bytes_in_word:A word = word (2 EXP backend_common_word_shift (:A))`
    ASSUME_TAC THENL
   [REWRITE_TAC[bytes_in_word_def; backend_common_word_shift_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[good_dimindex_def]) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV);
    ALL_TAC] THEN
  ASM_SIMP_TAC[get_real_simple_addr_def; get_real_addr_def; LET_DEF; LET_END_DEF;
               MP3AUX_get_addr_ushr] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_MUL_LSL] THEN ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN
  REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `get_addr c n w = word_add (word_shl (word n) (shift_length c)) (word 1):A word`
      SUBST1_TAC THENL
     [REWRITE_TAC[get_addr_def] THEN
      SUBGOAL_THEN `get_lowerbits c w = word 1:A word` SUBST1_TAC THENL
       [MP_TAC(ISPEC `w:A word_loc` (cases "word_loc")) THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[get_lowerbits_def; small_shift_length_def; ARITH; or_1];
        ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
      REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_1; BIT_WORD_0] THEN
      REWRITE_TAC[shift_length_def] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_MUL_LSL; option_INJ] THEN CONV_TAC WORD_RULE;
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[MP3AUX_get_addr_ushr2; WORD_MUL_LSL] THEN
    REWRITE_TAC[option_INJ] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 7963 *)
let get_real_offset_thm = prove
 (`!index. good_dimindex (:A) ==>
     get_real_offset (word (4 * index)) =
     SOME (word_add bytes_in_word (word_mul (word index) bytes_in_word):A word)`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[get_real_offset_def; bytes_in_word_def; WORD_MUL_LSL] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[WORD_MUL] THEN CONV_TAC WORD_RULE);;

(* HOL4 line 7972 *)
let word_heap_APPEND = prove
 (`!conf xs ys (a:A word).
     word_heap a (APPEND xs ys) conf =
     word_heap a xs conf STAR
     word_heap (word_add a (word_mul bytes_in_word (word (heap_length xs)))) ys conf`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; word_heap_def; heap_length_NIL; SEP_CLAUSES;
                  MP3AUX_heap_length_CONS] THENL
   [REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 7983: FORALL_WORD *)
let data_to_word_memoryProof_FORALL_WORD = prove
 (`!P. (!v:A word. P v) <=> !n. n < dimword (:A) ==> P (word n)`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM WORD_VAL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[dimword_def; VAL_BOUND]);;

(* HOL4 line 7989 *)
let BlockNil_and_lemma = prove
 (`!tag. good_dimindex (:A) ==>
     word_and (word_neg (word 2)) (word_add (word_mul (word 16) tag) (word 2)) =
     word_add (word_mul (word 16) tag) (word 2):A word`,
  REWRITE_TAC[MP3AUX_and_neg2; ODD_VAL_WORD_ADD; ODD_VAL_WORD_MUL; ODD_VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 8002 *)
let word_ml_inv_num_lemma = prove
 (`!v. good_dimindex (:A) ==>
     word_and (word_neg (word 2)) (word_mul (word 4) v) = word_mul (word 4) v:A word`,
  REWRITE_TAC[MP3AUX_and_neg2; ODD_VAL_WORD_ADD; ODD_VAL_WORD_MUL; ODD_VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]);;

(* MP3AUX: Smallnum of a non-negative and of a negative number *)
let MP3AUX_Smallnum_num = prove
 (`(!n. Smallnum (&n) = word (4 * n):A word) /\
   (!n. ~(n = 0) ==> Smallnum (-- &n) = word_neg (word (4 * n)):A word)`,
  REWRITE_TAC[data_to_word_Smallnum_def] THEN CONJ_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[INT_ARITH `~(&n:int < &0)`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM];
    DISCH_TAC THEN
    SUBGOAL_THEN `--(&n:int) < &0` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[INT_NEG_LT0; INT_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `&0 - --x:int = x`; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
                WORD_SUB_LZERO]]);;

(* MP3AUX: small_enough_int numbers are small_int *)
let MP3AUX_small_enough_int = prove
 (`!i. good_dimindex (:A) /\ small_enough_int i ==> small_int (:A) i`,
  REWRITE_TAC[good_dimindex_def; small_enough_int_def; small_int_def; dimword_def] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_INT_ARITH_TAC);;

(* HOL4 line 8013 *)
let word_ml_inv_num = prove
 (`!heap be a sp sp1 gens limit ts c (s:(C,FFI)data_state) ws n.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (data_state_refs s) ws /\
     good_dimindex (:A) /\
     small_enough_int (&n) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (data_state_refs s)
       (CONS (data_Number (&n),wl_Word (word (4 * n):A word)) ws)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ml_inv_def] THEN STRIP_TAC THEN
  EXISTS_TAC `CONS (gc_shared_Data (wl_Word (Smallnum (&n):A word))) hs` THEN
  REWRITE_TAC[MAP; ALL2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC abs_ml_inv_Num THEN ASM_MESON_TAC[MP3AUX_small_enough_int];
    ASM_REWRITE_TAC[word_addr_def; MP3AUX_Smallnum_num] THEN
    REWRITE_TAC[WORD_RULE `word_not (word 1):A word = word_neg (word 2)`] THEN
    ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[WORD_MUL] THEN
    ASM_SIMP_TAC[word_ml_inv_num_lemma]]);;

(* HOL4 line 8032 *)
let word_ml_inv_zero = prove
 (`!heap be a sp sp1 gens limit ts c (s:(C,FFI)data_state) ws.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (data_state_refs s) ws /\
     good_dimindex (:A) /\
     small_enough_int (&0) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (data_state_refs s)
       (CONS (data_Number (&0),wl_Word (word 0:A word)) ws)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                       heap_element)list`; `be:bool`; `a:num`; `sp:num`; `sp1:num`;
                `gens:gen_state`; `limit:num`; `ts:num`; `c:data_to_word_config`;
                `s:(C,FFI)data_state`; `ws:(data_v#A word_loc)list`; `0`]
    word_ml_inv_num) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES]);;

(* HOL4 line 8035 *)
let word_ml_inv_neg_num_lemma = prove
 (`!v. good_dimindex (:A) ==>
     word_and (word_neg (word 2)) (word_mul (word_neg (word 4)) v) =
     word_mul (word_neg (word 4)) v:A word`,
  REWRITE_TAC[MP3AUX_and_neg2; ODD_VAL_WORD_NEG; ODD_VAL_WORD_MUL; ODD_VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 8046 *)
let word_ml_inv_neg_num = prove
 (`!heap be a sp sp1 gens limit ts c (s:(C,FFI)data_state) ws n.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (data_state_refs s) ws /\
     good_dimindex (:A) /\
     small_enough_int (-- &n) /\ ~(n = 0) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c (data_state_refs s)
       (CONS (data_Number (-- &n),wl_Word (word_neg (word (4 * n)):A word)) ws)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ml_inv_def] THEN STRIP_TAC THEN
  EXISTS_TAC `CONS (gc_shared_Data (wl_Word (Smallnum (-- &n):A word))) hs` THEN
  REWRITE_TAC[MAP; ALL2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC abs_ml_inv_Num THEN ASM_MESON_TAC[MP3AUX_small_enough_int];
    ASM_SIMP_TAC[word_addr_def; MP3AUX_Smallnum_num] THEN
    REWRITE_TAC[WORD_RULE `word_not (word 1):A word = word_neg (word 2)`] THEN
    ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
    REWRITE_TAC[WORD_RULE `word_neg (word (4 * n)):A word =
                           word_mul (word_neg (word 4)) (word n)`] THEN
    ASM_SIMP_TAC[word_ml_inv_neg_num_lemma]]);;

(* HOL4 line 8065: word_list_APPEND *)
let data_to_word_memoryProof_word_list_APPEND = prove
 (`!xs ys (a:A word).
     misc_word_list a (APPEND xs ys:B list) =
     misc_word_list a xs STAR
     misc_word_list (word_add a (word_mul (word (LENGTH xs)) bytes_in_word)) ys`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; misc_word_list_def; LENGTH; SEP_CLAUSES] THENL
   [REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE]);;

(* HOL4 line 8073 (the unused bound variable ts of HOL4 is left out) *)
let all_ts_head_eq = prove
 (`!v refs stack.
     v IN all_vs refs stack ==> all_ts refs stack = all_ts refs (CONS v stack)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MP3AUX_all_ts_mono THEN REWRITE_TAC[MEM] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:num` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [all_ts_def] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; IN_ELIM_THM; MEM] THEN STRIP_TAC THENL
     [REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MEM_in_all_ts THEN ASM_MESON_TAC[];
      REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]]]);;

(* MP3AUX: associativity and commutativity of STAR, for AC *)
let MP3AUX_STAR_AC = prove
 (`!p q r:(A->bool)->bool.
     p STAR q = q STAR p /\
     (p STAR q) STAR r = p STAR (q STAR r) /\
     p STAR (q STAR r) = q STAR (p STAR r)`,
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

(* MP3AUX: reading element i of a word list from memory *)
let MP3AUX_word_list_EL = prove
 (`!xs (a:A word) p (m:A word->B) dm i.
     (misc_word_list a xs STAR p) (fun2set (m,dm)) /\ i < LENGTH xs ==>
     m (word_add a (word_mul (word i) bytes_in_word)) = EL i xs /\
     word_add a (word_mul (word i) bytes_in_word) IN dm`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[misc_word_list_def; GSYM STAR_ASSOC; one_fun2set; LENGTH; LT_SUC;
              LT_0; EL; HD; TL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE `word_add a (word_mul (word 0) b):A word = a`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:A word) bytes_in_word`; `p:(A word#B->bool)->bool`;
    `m:A word->B`; `dm DELETE (a:A word)`; `n:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; WORD_ADD; WORD_RULE
    `word_add (word_add a b) (word_mul (word n) b):A word =
     word_add a (word_mul (word_add (word n) (word 1)) b)`] THEN
  SIMP_TAC[IN_DELETE]);;

(* MP3AUX: a heap element is a STAR factor of the heap *)
let MP3AUX_word_heap_el = prove
 (`!heap (a:A word) c p m dm n x.
     (word_heap a heap c STAR p) (fun2set (m,dm)) /\ heap_lookup n heap = SOME x ==>
     ?q. (word_el (word_add a (word_mul bytes_in_word (word n))) x c STAR q)
           (fun2set (m,dm))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  UNDISCH_TAC `(word_heap (a:A word) heap c STAR p) (fun2set (m,dm))` THEN
  ASM_REWRITE_TAC[word_heap_APPEND; word_heap_def] THEN DISCH_TAC THEN
  EXISTS_TAC `word_heap (a:A word) ha c STAR
    (word_heap (word_add (word_add a (word_mul bytes_in_word (word (heap_length ha))))
       (word_mul bytes_in_word (word (el_length (x:((A word_loc,
          data_to_word_memoryProof_tag#(A word_loc)list)heap_element)))))) hb c STAR p)` THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  CONV_TAC(AC MP3AUX_STAR_AC));;

(* MP3AUX: reading field i of a block or reference from memory *)
let MP3AUX_word_el_EL = prove
 (`!(a:A word) xs l tag c q m dm i.
     (word_el a (DataElement xs l (tag,[]:(A word_loc)list)) c STAR q) (fun2set (m,dm)) /\
     (tag = RefTag \/ (?n. tag = BlockTag n)) /\ i < LENGTH xs ==>
     m (word_add a (word_mul (word (i + 1)) bytes_in_word)) = word_addr c (EL i xs) /\
     word_add a (word_mul (word (i + 1)) bytes_in_word) IN dm`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2
    (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) ASSUME_TAC)) THEN
  REWRITE_TAC[word_el_def; word_payload_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[GSYM STAR_ASSOC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] MP3AUX_word_list_EL)) THEN
  DISCH_THEN(MP_TAC o SPEC `i + 1`) THEN
  ASM_REWRITE_TAC[LENGTH; LENGTH_MAP; ARITH_RULE `i + 1 < SUC n <=> i < n`] THEN
  REWRITE_TAC[GSYM ADD1; EL; TL] THEN ASM_SIMP_TAC[EL_MAP]);;

(* MP3AUX: reading field i of a heap block through its real address *)
let MP3AUX_memory_field = prove
 (`!heap a sp sp1 gens c st (m:A word->A word_loc) dm limit p xs l tag u i.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup p heap = SOME (DataElement xs l (tag,[])) /\
     (tag = RefTag \/ (?n. tag = BlockTag n)) /\ good_dimindex (:A) /\
     i < LENGTH xs ==>
     ?x. get_real_addr c st (get_addr c p u) = SOME x /\
         m (word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word i))) =
           word_addr c (EL i xs) /\
         word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word i)) IN dm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_in_memory_store_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`; `c:data_to_word_config`; `p:num`;
    `DataElement xs l (tag,[]):((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                                heap_element)`; `st:(store_name,A word_loc)fmap`;
    `curr:A word`; `u:A word_loc`] get_real_addr_get_addr) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`; `curr:A word`; `c:data_to_word_config`;
    `word_heap (other:A word) (heap_expand limit) c`; `m:A word->A word_loc`;
    `dm:A word->bool`; `p:num`;
    `DataElement xs l (tag,[]):((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                                heap_element)`] MP3AUX_word_heap_el) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`word_add curr (word_mul bytes_in_word (word p)):A word`;
    `xs:((A word_loc)heap_address)list`; `l:num`; `tag:data_to_word_memoryProof_tag`;
    `c:data_to_word_config`; `q:(A word#A word_loc->bool)->bool`;
    `m:A word->A word_loc`; `dm:A word->bool`; `i:num`] MP3AUX_word_el_EL) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[WORD_ADD; WORD_RULE
   `word_add (word_add curr (word_mul b (word p))) (word_mul (word_add (word i) (word 1)) b) =
    word_add (word_add (word_add curr (word_mul (word p) b)) b) (word_mul b (word i)):A word`]);;

(* MP3AUX: the root of a non-empty block on the stack points to its block *)
let MP3AUX_abs_ml_inv_Block_root = prove
 (`!conf t n vals stack refs r roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (CONS (data_Block t n vals) stack) refs
       (CONS r roots,heap,be,a,sp,sp1,gens) limit ts /\ ~(vals = []) ==>
     ?p zs. r = Pointer p (wl_Word (ptr_bits conf n (LENGTH zs))) /\
            heap_lookup p heap = SOME (BlockRep n zs) /\ LENGTH zs = LENGTH vals`,
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; ALL2] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN
  MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ptr:num`; `xs:((A word_loc)heap_address)list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[EVERY2_LENGTH]);;

(* MP3AUX: the root of a reference to an array points to its RefBlock *)
let MP3AUX_abs_ml_inv_Ref_root = prove
 (`!conf b ptr stack refs r roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts vals.
     abs_ml_inv conf (CONS (data_RefPtr b ptr) stack) refs
       (CONS r roots,heap,be,a,sp,sp1,gens) limit ts /\
     lookup ptr refs = SOME (bvl_ValueArray vals) ==>
     ?p zs. r = Pointer p (wl_Word (word 0)) /\
            heap_lookup p heap = SOME (RefBlock zs) /\ LENGTH zs = LENGTH vals`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; ALL2] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN
  MP3AUX_ASM_HEAD_TAC "v_inv" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `reachable_refs (CONS (data_RefPtr b ptr) stack) refs ptr` ASSUME_TAC THENL
   [REWRITE_TAC[reachable_refs_def] THEN EXISTS_TAC `data_RefPtr b ptr` THEN
    EXISTS_TAC `ptr:num` THEN REWRITE_TAC[MEM; get_refs_def; RTC_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `ptr:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[bc_ref_inv_def; FLOOKUP_DEF]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `zs:((A word_loc)heap_address)list` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[EVERY2_LENGTH]);;

(* HOL4 line 8092 *)
let memory_rel_El' = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag vals ptr vars index.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts' tag vals,ptr) vars) /\
     good_dimindex (:A) /\
     index < LENGTH vals ==>
     ?ptr_w (i_w:A word) x:A word.
       ptr = wl_Word ptr_w /\
       get_real_addr c st ptr_w = SOME x /\
       word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word index))
         IN dm /\
       memory_rel c be ts refs sp st m dm
         (CONS (EL index vals,
                m (word_add (word_add x bytes_in_word)
                            (word_mul bytes_in_word (word index))))
               (CONS (data_Block ts' tag vals,ptr) vars))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; word_ml_inv_def; MAP; FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP el_thm (CONJ th
    (ASSUME `index < LENGTH (vals:data_v list)`)))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `~(vals:data_v list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP MP3AUX_abs_ml_inv_Block_root
    (CONJ th (ASSUME `~(vals:data_v list = [])`)))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `LENGTH (zs:((A word_loc)heap_address)list) =
                                         LENGTH (vals:data_v list)`
                          then ASSUME_TAC(SYM th) else NO_TAC) THEN
  SUBGOAL_THEN `index < LENGTH (zs:((A word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `y = EL index (zs:((A word_loc)heap_address)list)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `heap_el (Pointer p (wl_Word (ptr_bits c tag (LENGTH (zs:((A word_loc)heap_address)list))))) index
                  (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = (y,T)` THEN
    ASM_REWRITE_TAC[heap_el_def; BlockRep_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
    `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `limit:num`; `p:num`; `zs:((A word_loc)heap_address)list`;
    `LENGTH (zs:((A word_loc)heap_address)list)`; `BlockTag tag`;
    `wl_Word (ptr_bits c tag (LENGTH (zs:((A word_loc)heap_address)list))):A word_loc`;
    `index:num`] MP3AUX_memory_field) THEN
  ASM_REWRITE_TAC[GSYM BlockRep_def] THEN
  ANTS_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `get_addr c p (wl_Word (ptr_bits c tag (LENGTH (zs:((A word_loc)heap_address)list)))):A word` THEN
  EXISTS_TAC `x:A word` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `ALL2 (\v w. word_addr c v = w)
      (CONS (Pointer p (wl_Word (ptr_bits c tag (LENGTH (zs:((A word_loc)heap_address)list))))) roots2)
      (CONS ptr (MAP SND (vars:(data_v#A word_loc)list)))` THEN
    REWRITE_TAC[ALL2; word_addr_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (EL index (zs:((A word_loc)heap_address)list))
    (CONS (Pointer p (wl_Word (ptr_bits c tag (LENGTH zs)))) roots2)` THEN
  ASM_REWRITE_TAC[ALL2]));;

(* MP3AUX: the length of a block in memory fits its header *)
let MP3AUX_memory_len_Block = prove
 (`!heap a sp sp1 gens c st (m:A word->A word_loc) dm limit p xs l n.
     heap_in_memory_store heap a sp sp1 gens c st m dm limit /\
     heap_lookup p heap = SOME (DataElement xs l (BlockTag n,[])) ==>
     LENGTH xs < 2 EXP (dimindex(:A) - 4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_in_memory_store_def] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`; `curr:A word`; `c:data_to_word_config`;
    `word_heap (other:A word) (heap_expand limit) c`; `m:A word->A word_loc`;
    `dm:A word->bool`; `p:num`;
    `DataElement xs l (BlockTag n,[]):((A word_loc,data_to_word_memoryProof_tag#
       (A word_loc)list)heap_element)`] MP3AUX_word_heap_el) THEN
  ASM_REWRITE_TAC[word_el_def; word_payload_def] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[AC MP3AUX_STAR_AC
    `((x:(A word#A word_loc->bool)->bool) STAR cond c) STAR q = cond c STAR (x STAR q)`] THEN
  REWRITE_TAC[cond_STAR; LENGTH_MAP] THEN SIMP_TAC[]);;

(* MP3AUX: the root of a small number second on the stack *)
let MP3AUX_abs_ml_inv_Num_root = prove
 (`!conf x j stack refs r r2 roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts.
     abs_ml_inv conf (CONS x (CONS (data_Number j) stack)) refs
       (CONS r (CONS r2 roots),heap,be,a,sp,sp1,gens) limit ts /\ small_int (:A) j ==>
     r2 = gc_shared_Data (wl_Word (Smallnum j))`,
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def; ALL2] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN
  UNDISCH_TAC `v_inv conf (data_Number j) refs (r2,f,tf,heap:((A word_loc,
     data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
  ASM_REWRITE_TAC[v_inv_def]);;

(* MP3AUX: an index into a block in memory is a small number *)
let MP3AUX_small_int_index = prove
 (`!index n. good_dimindex (:A) /\ index < n /\ n < 2 EXP (dimindex(:A) - 4) ==>
             small_int (:A) (&index)`,
  REWRITE_TAC[good_dimindex_def; small_int_def; dimword_def] THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
                                                 lhs(concl th) = `dimindex(:A)`)) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)) THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_ARITH `--(&a) <= &b:int`] THEN ASM_ARITH_TAC);;

(* HOL4 line 8133 *)
let memory_rel_El = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm ts' tag vals ptr index i vars.
     memory_rel c be ts refs sp st m dm
       (CONS (data_Block ts' tag vals,ptr) (CONS (data_Number (&index),i) vars)) /\
     good_dimindex (:A) /\
     index < LENGTH vals ==>
     ?ptr_w i_w x y:A word.
       ptr = wl_Word ptr_w /\ i = wl_Word i_w /\
       get_real_addr c st ptr_w = SOME x /\
       get_real_offset i_w = SOME y /\
       word_add x y IN dm /\
       memory_rel c be ts refs sp st m dm
         (CONS (EL index vals,m (word_add x y))
          (CONS (data_Block ts' tag vals,ptr) (CONS (data_Number (&index),i) vars)))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; word_ml_inv_def; MAP; FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP el_thm (CONJ th
    (ASSUME `index < LENGTH (vals:data_v list)`)))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `~(vals:data_v list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP MP3AUX_abs_ml_inv_Block_root
    (CONJ th (ASSUME `~(vals:data_v list = [])`)))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `LENGTH (zs:((A word_loc)heap_address)list) =
                                         LENGTH (vals:data_v list)`
                          then ASSUME_TAC(SYM th) else NO_TAC) THEN
  SUBGOAL_THEN `index < LENGTH (zs:((A word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y = EL index (zs:((A word_loc)heap_address)list)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `heap_el (Pointer p (wl_Word (ptr_bits c tag (LENGTH (zs:((A word_loc)heap_address)list))))) index
                  (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) = (y,T)` THEN
    ASM_REWRITE_TAC[heap_el_def; BlockRep_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `small_int (:A) (&index)` ASSUME_TAC THENL
   [MATCH_MP_TAC MP3AUX_small_int_index THEN
    EXISTS_TAC `LENGTH (zs:((A word_loc)heap_address)list)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MP3AUX_memory_len_Block THEN
    MAP_EVERY EXISTS_TAC [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
      `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
      `limit:num`; `p:num`; `LENGTH (zs:((A word_loc)heap_address)list)`; `tag:num`] THEN
    ASM_REWRITE_TAC[GSYM BlockRep_def];
    ALL_TAC]) THEN
  (MP3AUX_ASM_HEAD_TAC "ALL2" (STRIP_ASSUME_TAC o BETA_RULE o
     REWRITE_RULE[ALL2; LIST_REL_CONS2]) THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP MP3AUX_abs_ml_inv_Num_root
    (CONJ th (ASSUME `small_int (:A) (&index)`)))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
    `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `limit:num`; `p:num`; `zs:((A word_loc)heap_address)list`;
    `LENGTH (zs:((A word_loc)heap_address)list)`; `BlockTag tag`;
    `wl_Word (ptr_bits c tag (LENGTH (zs:((A word_loc)heap_address)list))):A word_loc`;
    `index:num`] MP3AUX_memory_field) THEN
  ASM_REWRITE_TAC[GSYM BlockRep_def] THEN
  ANTS_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `get_addr c p (wl_Word (ptr_bits c tag (LENGTH (zs:((A word_loc)heap_address)list)))):A word` THEN
  EXISTS_TAC `word (4 * index):A word` THEN
  EXISTS_TAC `x:A word` THEN
  EXISTS_TAC `word_add bytes_in_word (word_mul (word index) bytes_in_word):A word` THEN
  ASM_SIMP_TAC[get_real_offset_thm; word_addr_def] THEN
  REWRITE_TAC[MP3AUX_Smallnum_num] THEN
  REWRITE_TAC[WORD_RULE `word_not (word 1):A word = word_neg (word 2)`] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[WORD_MUL] THEN
  ASM_SIMP_TAC[word_ml_inv_num_lemma] THEN
  SUBGOAL_THEN `word_add x (word_add bytes_in_word (word_mul (word index) bytes_in_word)) =
                word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word index)):A word`
    SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (EL index (zs:((A word_loc)heap_address)list))
    (CONS (Pointer p (wl_Word (ptr_bits c tag (LENGTH zs))))
      (CONS (gc_shared_Data (wl_Word (Smallnum (&index)))) t'))` THEN
  ASM_REWRITE_TAC[ALL2; word_addr_def] THEN
  REWRITE_TAC[MP3AUX_Smallnum_num] THEN
  REWRITE_TAC[WORD_RULE `word_not (word 1):A word = word_neg (word 2)`] THEN
  ONCE_REWRITE_TAC[WORD_AND_SYM] THEN REWRITE_TAC[WORD_MUL] THEN
  ASM_SIMP_TAC[word_ml_inv_num_lemma]));;

(* HOL4 line 8189 *)
let memory_rel_swap = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm x y z.
     memory_rel c be ts refs sp st m dm (CONS x (CONS y z)) ==>
     memory_rel c be ts refs sp st m dm (CONS y (CONS x z))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC memory_rel_rearrange THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* HOL4 line 8196 *)
let memory_rel_Deref' = prove
 (`!c be ts refs sp st (m:A word -> A word_loc) dm bl nn ptr vars vals index.
     memory_rel c be ts refs sp st m dm (CONS (data_RefPtr bl nn,ptr) vars) /\
     lookup nn refs = SOME (bvl_ValueArray vals) /\
     good_dimindex (:A) /\
     index < LENGTH vals ==>
     ?ptr_w x:A word.
       ptr = wl_Word ptr_w /\
       get_real_addr c st ptr_w = SOME x /\
       word_add (word_add x bytes_in_word) (word_mul bytes_in_word (word index))
         IN dm /\
       memory_rel c be ts refs sp st m dm
         (CONS (EL index vals,
                m (word_add (word_add x bytes_in_word)
                            (word_mul bytes_in_word (word index))))
               (CONS (data_RefPtr bl nn,ptr) vars))`,
  (REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def; word_ml_inv_def; MAP; FST; SND] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP deref_thm) THEN
  ASM_REWRITE_TAC[THE_DEF] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `index:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP MP3AUX_abs_ml_inv_Ref_root
    (CONJ th (ASSUME `lookup nn refs = SOME (bvl_ValueArray (vals:data_v list))`)))) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `LENGTH (zs:((A word_loc)heap_address)list) =
                                         LENGTH (vals:data_v list)`
                          then ASSUME_TAC(SYM th) else NO_TAC) THEN
  SUBGOAL_THEN `index < LENGTH (zs:((A word_loc)heap_address)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y = EL index (zs:((A word_loc)heap_address)list)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `heap_el (Pointer p (wl_Word (word 0))) index
                  (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list) = (y,T)` THEN
    ASM_REWRITE_TAC[heap_el_def; RefBlock_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
    `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
    `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `limit:num`; `p:num`; `zs:((A word_loc)heap_address)list`;
    `LENGTH (zs:((A word_loc)heap_address)list)`; `RefTag`;
    `wl_Word (word 0):A word_loc`; `index:num`] MP3AUX_memory_field) THEN
  ASM_REWRITE_TAC[GSYM RefBlock_def] THEN STRIP_TAC THEN
  EXISTS_TAC `get_addr c p (wl_Word (word 0)):A word` THEN
  EXISTS_TAC `x:A word` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `ALL2 (\v w. word_addr c v = w)
      (CONS (Pointer p (wl_Word (word 0))) (roots2:((A word_loc)heap_address)list))
      (CONS ptr (MAP SND (vars:(data_v#A word_loc)list)))` THEN
    REWRITE_TAC[ALL2; word_addr_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `CONS (EL index (zs:((A word_loc)heap_address)list))
    (CONS (Pointer p (wl_Word (word 0))) roots2)` THEN
  ASM_REWRITE_TAC[ALL2]));;

