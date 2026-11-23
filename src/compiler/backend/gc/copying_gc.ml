(* ========================================================================= *)
(* copying_gc: port of HOL4 compiler/backend/gc/copying_gcScript.sml         *)
(* (CakeML v3479).  The straightforward non-generational copying garbage     *)
(* collector.                                                                *)
(* ========================================================================= *)

needs "compiler/backend/gc/gc_shared.ml";;

(* The GC is a copying collector which moves elements *)

let copying_gc_gc_move_def = cake_def
  `(copying_gc_gc_move
      (gc_shared_Data d:A heap_address,h2:((A,B)heap_element)list,a,n,
       heap:((A,B)heap_element)list,c,limit) =
      (gc_shared_Data d,h2,a,n,heap,c)) /\
   (copying_gc_gc_move (Pointer ptr d,h2,a,n,heap,c,limit) =
      match heap_lookup ptr heap with
        SOME (DataElement xs l dd) ->
          let c = (c /\ l + 1 <= n /\ a + n = limit) in
          let n = n - (l + 1) in
          let h2 = APPEND h2 [DataElement xs l dd] in
          (match gc_forward_ptr ptr heap a d c with
             (heap,c) -> (Pointer a d,h2,a + (l + 1),n,heap,c))
      | SOME (ForwardPointer ptr _ l) -> (Pointer ptr d,h2,a,n,heap,c)
      | _ -> (ARB,h2,a,n,heap,F))`;;

let copying_gc_gc_move_list_def = cake_def
  `(copying_gc_gc_move_list ([]:(A heap_address)list,h2:((A,B)heap_element)list,a:num,
                            n:num,heap:((A,B)heap_element)list,c:bool,limit:num) =
      ([],h2,a,n,heap,c)) /\
   (copying_gc_gc_move_list (CONS x xs,h2,a,n,heap,c,limit) =
      let (x,h2,a,n,heap,c) = copying_gc_gc_move (x,h2,a,n,heap,c,limit) in
      let (xs,h2,a,n,heap,c) = copying_gc_gc_move_list (xs,h2,a,n,heap,c,limit) in
        (CONS x xs,h2,a,n,heap,c))`;;

(* HOL4 rebinds xs in the let of the second clause; it is named xs1 here, *)
(* since cake_ind would identify the two (kit issue); the clauses are the  *)
(* same up to the name of a bound variable.                                *)

let copying_gc_gc_move_loop_def = cake_def_wf
  `MEASURE (\(h1:((A,B)heap_element)list,h2:((A,B)heap_element)list,a:num,n:num,
              heap:((A,B)heap_element)list,c:bool,limit:num). limit - heap_length h1)`
  (REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   FS[measure_THM; heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def] THEN
   DECIDE_TAC)
  `(copying_gc_gc_move_loop (h1:((A,B)heap_element)list,[]:((A,B)heap_element)list,
                            a:num,n:num,heap:((A,B)heap_element)list,c:bool,limit:num) =
      (h1,a,n,heap,c)) /\
   (copying_gc_gc_move_loop (h1,CONS h h2,a,n,heap,c,limit) =
      if limit < heap_length (APPEND h1 (CONS h h2)) then (h1,a,n,heap,F) else
        match h with
          DataElement xs l d ->
            let (xs1,h2,a,n,heap,c) =
              copying_gc_gc_move_list (xs,CONS h h2,a,n,heap,c,limit) in
            let c = (c /\ ~(h2 = []) /\ HD h2 = h) in
            let h2 = TL h2 in
            let h1 = APPEND h1 [DataElement xs1 l d] in
              copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit)
        | _ -> (h1,a,n,heap,F))`;;

(* HOL4: gc_move_loop_ind, with the quantifiers that later files use *)

let copying_gc_gc_move_loop_ind = prove
 (`!P. (!(h1:((A,B)heap_element)list) a n (heap:((A,B)heap_element)list) c limit.
          P (h1,[],a,n,heap,c,limit)) /\
       (!h1 h h2 a n heap c limit.
          (!xs l d xs' h2' a' n' heap' c'.
             ~(limit < heap_length (APPEND h1 (CONS h h2))) /\
             h = DataElement xs l d /\
             copying_gc_gc_move_list (xs,CONS h h2,a,n,heap,c,limit) =
               (xs',h2',a',n',heap',c')
             ==> P (APPEND h1 [DataElement xs' l d],TL h2',a',n',heap',
                    (c' /\ ~(h2' = []) /\ HD h2' = h),limit))
          ==> P (h1,CONS h h2,a,n,heap,c,limit))
       ==> !h1 h2 a n heap c limit. P (h1,h2,a,n,heap,c,limit)`,
  GEN_TAC THEN STRIP_TAC THEN QSPEC_THEN "P" MP_TAC (cake_ind "copying_gc_gc_move_loop") THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_EXISTS_TAC);;

let full_gc_def = cake_def
  `full_gc (roots:(A heap_address)list,heap:((A,B)heap_element)list,limit) =
     let c0 = (heap_length heap = limit) in
     match copying_gc_gc_move_list (roots,[],0,limit,heap,T,limit) with
       (roots,h2,a,n,heap,c) ->
         match copying_gc_gc_move_loop ([],h2,a,n,heap,c,limit) with
           (heap,a,n,temp,c) ->
             let c = (c /\ a = heap_length heap /\ heap_length temp = limit /\
                      c0 /\ n = limit - a /\ a <= limit) in
               (roots,heap,a,c)`;;

(* Invariant *)

let copying_gc_gc_inv_def = cake_def
  `copying_gc_gc_inv (h1,h2,a,n,heap:((A,B)heap_element)list,c,limit)
                     (heap0:((A,B)heap_element)list) (roots0:(A heap_address)list) <=>
     a + n = limit /\
     a = heap_length (APPEND h1 h2) /\
     n = heap_length (FILTER (\h. ~isForwardPointer h) heap) /\ c /\
     heap_length heap = limit /\
     heap_ok heap0 limit /\
     heaps_similar heap0 heap /\
     ALL isDataElement h1 /\ ALL isDataElement h2 /\
     BIJ (heap_map1 heap) (FDOM (heap_map 0 heap)) (heap_addresses 0 (APPEND h1 h2)) /\
     !i j. FLOOKUP (heap_map 0 heap) i = SOME j
           ==> ?xs l d.
                 heap_lookup i heap0 = SOME (DataElement xs l d) /\
                 heap_lookup j (APPEND h1 h2) =
                   SOME (DataElement (if j < heap_length h1
                                      then ADDR_MAP (heap_map1 heap) xs else xs) l d) /\
                 reachable_addresses roots0 heap0 i /\
                 !ptr (d:A). MEM (Pointer ptr d) xs /\ j < heap_length h1
                             ==> ptr IN FDOM (heap_map 0 heap)`;;

(* Invariant maintained *)

let DRESTRICT_heap_map = prove
 (`!heap:((A,B)heap_element)list k n.
     n < k ==> DRESTRICT (heap_map k heap) (COMPL {n}) = heap_map k heap`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NOT_FDOM_DRESTRICT THEN
  DISCH_THEN(MP_TAC o MATCH_MP IN_heap_map_IMP) THEN ASM_ARITH_TAC);;

let copying_gc_IN_FRANGE = prove
 (`!heap n ptr (d:A) l.
     MEM (ForwardPointer ptr d l) (heap:((A,B)heap_element)list)
     ==> ptr IN FRANGE (heap_map n heap)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN
  CASES_ON `h:(A,B)heap_element` THEN
  REWRITE_TAC[heap_map_def; FRANGE_FUPDATE] THEN
  SIMP_TAC[DRESTRICT_heap_map; ARITH_RULE `n < n + l + 1`] THEN
  SIMP_NOASM[IN_INSERT] THEN ASM_MESON_TAC[]);;

let heap_addresses_SNOC = prove
 (`!xs n (x:(A,B)heap_element).
     heap_addresses n (APPEND xs [x]) =
     heap_addresses n xs UNION {heap_length xs + n}`,
  REWRITE_TAC[gc_shared_heap_addresses_APPEND; heap_addresses_def] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `heap_length (xs:((A,B)heap_element)list) + n = n + heap_length xs`
    SUBST1_TAC THENL [ARITH_TAC; REWRITE_TAC[]]);;

(* HOL4: NOT_IN_heap_addresses (an ML-level lemma of the script) *)
let GC1AUX_NOT_IN_heap_addresses = prove
 (`!xs:((A,B)heap_element)list. ~(heap_length xs IN heap_addresses 0 xs)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP heap_addresses_LESS_heap_length) THEN
  ARITH_TAC);;

(* the data element case of gc_move_thm: the forwarded heap maps one more   *)
(* address (rewriting with GC1AUX_heap_map_forward uses the ys and d of the *)
(* context)                                                                 *)

let GC1AUX_heap_map_forward = prove
 (`!ha hb (ys:(A heap_address)list) l (d:B) a (u:A).
     heap_map 0 (APPEND ha (CONS (ForwardPointer a u l) hb)) =
     heap_map 0 (APPEND ha (CONS (DataElement ys l d) hb)) |+ (heap_length ha,a)`,
  REWRITE_TAC[heap_map_APPEND; heap_map_def; el_length_def; ADD_CLAUSES;
              FUNION_FUPDATE_2; FDOM_heap_map]);;

let GC1AUX_heap_lookup_APPEND_CONS = prove
 (`!h1 (x:(A,B)heap_element) r j.
     heap_lookup j (APPEND h1 (CONS x r)) =
     if j < heap_length h1 then heap_lookup j h1
     else if j = heap_length h1 then SOME x
     else if j < heap_length h1 + el_length x then NONE
     else heap_lookup (j - (heap_length h1 + el_length x)) r`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup; NOT_LESS_IMP_heap_lookup] THEN
  REWRITE_TAC[heap_lookup_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(j < h) ==> (j - h = 0 <=> j = h)`;
               ARITH_RULE `~(j < h) ==> (j - h < e <=> j < h + e)`;
               ARITH_RULE `j - h - e = j - (h + e)`]);;

let GC1AUX_BIJ_forward = prove
 (`!(ff:(num,num)fmap) k a s.
     BIJ (\x. FAPPLY ff x) (FDOM ff) s /\ ~(k IN FDOM ff) /\ ~(a IN s)
     ==> BIJ (\x. FAPPLY (ff |+ (k,a)) x) (k INSERT FDOM ff) (a INSERT s)`,
  REWRITE_TAC[BIJ; INJ; SURJ; FAPPLY_FUPDATE_THM; IN_INSERT] THEN MESON_TAC[]);;

(* the invariant after the data element at heap_length ha is copied to the *)
(* end of h2 and a forward pointer to its new address a is left behind      *)

let GC1AUX_gc_inv_forward = prove
 (`!h1 h2 a n ha hb (ys:(A heap_address)list) l (d:B) c limit heap0 roots0 (u:A).
     copying_gc_gc_inv (h1,h2,a,n,APPEND ha (CONS (DataElement ys l d) hb),c,limit)
       heap0 roots0 /\
     reachable_addresses roots0 heap0 (heap_length ha)
     ==> copying_gc_gc_inv
           (h1,APPEND h2 [DataElement ys l d],a + l + 1,n - (l + 1),
            APPEND ha (CONS (ForwardPointer a u l) hb),
            (c /\ l + 1 <= n /\ a + n = limit),limit) heap0 roots0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copying_gc_gc_inv_def; heap_map1_def; GC1AUX_heap_map_forward] THEN
  MP_TAC(SPEC_ALL NOT_IN_heap_map) THEN
  SPEC_TAC(`heap_map 0 (APPEND ha (CONS (DataElement ys l d) hb):((A,B)heap_element)list)`,
           `ff:(num,num)fmap`) THEN
  REPEAT STRIP_TAC THEN
  FS[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; FILTER_APPEND; FILTER;
     isForwardPointer_def; isDataElement_def] THEN TRY DECIDE_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND; heap_length_APPEND]
                   gc_shared_heaps_similar_lemma) THEN ASM_EXISTS_TAC;
    REWRITE_TAC[GSYM heap_length_APPEND; heap_addresses_SNOC; ADD_CLAUSES;
                SET_RULE `s UNION {x:num} = x INSERT s`] THEN
    MATCH_MP_TAC GC1AUX_BIJ_forward THEN ASM_REWRITE_TAC[GC1AUX_NOT_IN_heap_addresses];
    ALL_TAC] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[FLOOKUP_UPDATE]) THEN COND_CASES_TAC THEN STRIP_TAC THENL
   [(* the new entry *)
    IMP_RES_TAC heap_similar_Data_IMP THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[GC1AUX_heap_lookup_APPEND_CONS; heap_lookup_PREFIX; heap_length_APPEND;
                    LT_REFL; ARITH_RULE `~(m + n < m:num)`] THEN SIMP_NOASM[];
    (* the old entries *)
    RES_TAC THEN ASM_EXISTS_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC gc_shared_heap_lookup_EXTEND THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_INJ; heap_element_11] THEN
      MATCH_MP_TAC gc_shared_ADDR_MAP_EQ THEN REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN COND_CASES_TAC THEN
      TRY(POP_ASSUM SUBST_ALL_TAC) THEN FS[];
      REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);;

let copying_gc_gc_move_thm = prove
 (`!h1 h2 a n (heap:((A,B)heap_element)list) c limit heap0 roots0 (x:A heap_address).
     copying_gc_gc_inv (h1,h2,a,n,heap,c,limit) heap0 roots0 /\
     (!ptr u. x = Pointer ptr u
              ==> isSomeDataOrForward (heap_lookup ptr heap) /\
                  reachable_addresses roots0 heap0 ptr)
     ==> ?(x3:A heap_address) h23 a3 n3 heap3 c3.
           copying_gc_gc_move (x,h2,a,n,heap,c,limit) =
             (ADDR_APPLY (heap_map1 heap3) x,h23,a3,n3,heap3,c3) /\
           (!ptr u. x = Pointer ptr u ==> ptr IN FDOM (heap_map 0 heap3)) /\
           (!ptr. isSomeDataOrForward (heap_lookup ptr heap) <=>
                  isSomeDataOrForward (heap_lookup ptr heap3)) /\
           heap_map 0 heap SUBMAP heap_map 0 heap3 /\
           copying_gc_gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0 roots0`,
  REPEAT GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  SIMP[copying_gc_gc_move_def; ADDR_APPLY_def; SUBMAP_REFL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
    REWRITE_RULE[isSomeDataOrForward_def; isSomeForwardPointer_def;
                 isSomeDataElement_def]) THENL
   [(* a forward pointer: nothing moves *)
    IMP_RES_TAC heap_lookup_FLOOKUP THEN FS[flookup_thm; heap_map1_def]; ALL_TAC] THEN
  (* a data element: it is copied and a forward pointer is left behind *)
  IMP_RES_TAC heap_lookup_SPLIT THEN RVEQ_TAC THEN
  SIMP[gc_forward_ptr_thm; heap_map1_def; GC1AUX_heap_map_forward; FAPPLY_FUPDATE_THM;
       FDOM_FUPDATE; IN_INSERT; SUBMAP_FUPDATE_EQN; NOT_IN_heap_map;
       GC1AUX_gc_inv_forward] THEN
  MESON_TAC[REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] gc_shared_isSomeDataOrForward_lemma]);;

let copying_gc_gc_move_list_thm = prove
 (`!xs h2 a n (heap:((A,B)heap_element)list) c h1 limit heap0 roots0.
     copying_gc_gc_inv (h1,h2,a,n,heap,c,limit) heap0 roots0 /\
     (!ptr u. MEM (Pointer ptr u) (xs:(A heap_address)list)
              ==> isSomeDataOrForward (heap_lookup ptr heap) /\
                  reachable_addresses roots0 heap0 ptr)
     ==> ?h23 a3 n3 heap3 c3.
           copying_gc_gc_move_list (xs,h2,a,n,heap,c,limit) =
             (ADDR_MAP (heap_map1 heap3) xs,h23,a3,n3,heap3,c3) /\
           (!ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM (heap_map 0 heap3)) /\
           (!ptr. isSomeDataOrForward (heap_lookup ptr heap) <=>
                  isSomeDataOrForward (heap_lookup ptr heap3)) /\
           heap_map 0 heap SUBMAP heap_map 0 heap3 /\
           copying_gc_gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0 roots0`,
  LIST_INDUCT_TAC THEN
  SIMP_NOASM[copying_gc_gc_move_list_def; ADDR_MAP_def; MEM; SUBMAP_REFL] THEN
  POP_ASSUM(fun ih -> REPEAT STRIP_TAC THEN
    MP_TAC(INST [`h:A heap_address`,`x:A heap_address`] (SPEC_ALL copying_gc_gc_move_thm)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    DRULE ih THEN ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN
  SIMP[] THEN IMP_RES_TAC SUBMAP_TRANS THEN CASES_ON `h:A heap_address` THEN
  FS[ADDR_MAP_def; ADDR_APPLY_def; heap_map1_def; SUBMAP_DEF] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let copying_gc_gc_move_ALT = prove
 (CASE_TERM
  `!(ys:A heap_address) (xs:((A,B)heap_element)list) a n heap c limit.
     copying_gc_gc_move (ys,xs,a,n,heap,c,limit) =
     match copying_gc_gc_move (ys,[],a,n,heap,c,limit) with
       (ys,xs1,x) -> (ys,APPEND xs xs1,x)`,
  REPEAT GEN_TAC THEN CASES_ON `ys:A heap_address` THEN
  REWRITE_TAC[copying_gc_gc_move_def; pair_CASE; APPEND_NIL; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN SIMP[APPEND_NIL; APPEND]);;

(* a tuple of six components is a tuple *)

let GC1AUX_PAIR6 = prove
 (`!p:A#B#C#D#E#P. ?x1 x2 x3 x4 x5 x6. p = (x1,x2,x3,x4,x5,x6)`,
  GEN_TAC THEN
  MAP_EVERY EXISTS_TAC [`FST(p:A#B#C#D#E#P)`; `FST(SND(p:A#B#C#D#E#P))`;
    `FST(SND(SND(p:A#B#C#D#E#P)))`; `FST(SND(SND(SND(p:A#B#C#D#E#P))))`;
    `FST(SND(SND(SND(SND(p:A#B#C#D#E#P)))))`; `SND(SND(SND(SND(SND(p:A#B#C#D#E#P)))))`] THEN
  REWRITE_TAC[PAIR]);;

let copying_gc_gc_move_list_ALT = prove
 (CASE_TERM
  `!(ys:(A heap_address)list) (xs:((A,B)heap_element)list) a n heap c limit
    (ys3:(A heap_address)list) (xs3:((A,B)heap_element)list) (a3:num) (n3:num)
    (heap3:((A,B)heap_element)list) (c3:bool).
     copying_gc_gc_move_list (ys,xs,a,n,heap,c,limit) =
     match copying_gc_gc_move_list (ys,[],a,n,heap,c,limit) with
       (ys,xs1,x) -> (ys,APPEND xs xs1,x)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[copying_gc_gc_move_list_def; pair_CASE; APPEND_NIL] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[copying_gc_gc_move_ALT] THEN
  MP_TAC(ISPEC `copying_gc_gc_move (h:A heap_address,[]:((A,B)heap_element)list,
                                    a,n,heap,c,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y1:A heap_address`; `x1:((A,B)heap_element)list`; `a1:num`;
    `n1:num`; `heap1:((A,B)heap_element)list`; `c1:bool`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE; APPEND] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (t:(A heap_address)list,[]:((A,B)heap_element)list,
                                         a1,n1,heap1,c1,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y2:(A heap_address)list`; `x2:((A,B)heap_element)list`; `a2:num`;
    `n2:num`; `heap2:((A,B)heap_element)list`; `c2:bool`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE; APPEND_ASSOC]);;

let copying_gc_gc_move_list_APPEND_lemma = prove
 (`!(ys:(A heap_address)list) (xs:((A,B)heap_element)list) a n heap c limit
    ys3 xs3 a3 n3 heap3 c3.
     copying_gc_gc_move_list (ys,xs,a,n,heap,c,limit) = (ys3,xs3,a3,n3,heap3,c3)
     ==> ?xs1. xs3 = APPEND xs xs1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[copying_gc_gc_move_list_ALT] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (ys:(A heap_address)list,
                  []:((A,B)heap_element)list,a,n,heap,c,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN MESON_TAC[]);;

(* gc_move_loop_thm: the scanned element points to data or forward pointers *)
(* that are reachable, and the invariant moves on past the scanned element  *)

let GC1AUX_gc_inv_scan_ok = prove
 (`!h1 (ys:(A heap_address)list) l (d:B) t a n heap c limit heap0 roots0.
     copying_gc_gc_inv (h1,CONS (DataElement ys l d) t,a,n,heap,c,limit) heap0 roots0
     ==> !ptr u. MEM (Pointer ptr u) ys
                 ==> isSomeDataOrForward (heap_lookup ptr heap) /\
                     reachable_addresses roots0 heap0 ptr`,
  REWRITE_TAC[copying_gc_gc_inv_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?i. FLOOKUP (heap_map 0 (heap:((A,B)heap_element)list)) i =
                    SOME (heap_length (h1:((A,B)heap_element)list))` STRIP_ASSUME_TAC THENL
   [FS[BIJ; SURJ; heap_map1_def; flookup_thm; gc_shared_heap_addresses_APPEND;
       heap_addresses_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  RES_TAC THEN RFS[heap_lookup_PREFIX] THEN
  IMP_RES_TAC heap_lookup_MEM THEN RULE_ASSUM_TAC(REWRITE_RULE[heap_ok_def]) THEN
  REWRITE_TAC[reachable_addresses_def] THEN CONJ_TAC THENL
   [MATCH_MP_TAC heap_similar_Data_IMP_DataOrForward THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[reachable_addresses_def; RTC_TRANS; RTC_INC; gc_edge_def]]);;

let GC1AUX_gc_inv_shift = prove
 (`!h1 (ys:(A heap_address)list) l (d:B) r a n heap c limit heap0 roots0.
     copying_gc_gc_inv (h1,CONS (DataElement ys l d) r,a,n,heap,c,limit) heap0 roots0 /\
     (!ptr u. MEM (Pointer ptr u) ys ==> ptr IN FDOM (heap_map 0 heap))
     ==> copying_gc_gc_inv
           (APPEND h1 [DataElement (ADDR_MAP (heap_map1 heap) ys) l d],r,a,n,heap,c,limit)
           heap0 roots0`,
  REWRITE_TAC[copying_gc_gc_inv_def; GSYM APPEND_ASSOC; APPEND] THEN REPEAT STRIP_TAC THEN
  FS[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def; ALL_APPEND;
     isDataElement_def; gc_shared_heap_addresses_APPEND; heap_addresses_def] THEN
  FIRST_X_ASSUM DRULE THEN REWRITE_TAC[GC1AUX_heap_lookup_APPEND_CONS; el_length_def] THEN
  ASM_CASES_TAC `j < heap_length (h1:((A,B)heap_element)list)` THEN
  ASM_SIMP_TAC[ARITH_RULE `j < h ==> j < h + l + 1`] THEN
  ASM_CASES_TAC `j = heap_length (h1:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[ARITH_RULE `h < h + l + 1`; option_INJ; heap_element_11;
                  option_DISTINCT] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `j < heap_length (h1:((A,B)heap_element)list) + l + 1` THEN
    ASM_REWRITE_TAC[option_DISTINCT]]);;

(* HOL4 recInduct with the induction theorem of a function of a tuple: the *)
(* goal !x1 .. xn y1 .. ym. t is the instance P (x1,..,xn) of its conclusion *)

let GC1AUX_REC_IND_TAC (ind:thm) : tactic = fun (asl,w) ->
  let k = length(fst(strip_forall(snd(dest_imp(snd(dest_forall(concl ind))))))) in
  let vs,b = strip_forall w in
  let xs,ys = chop_list k vs in
  let p = mk_gabs(end_itlist (curry mk_pair) xs,list_mk_forall(ys,b)) in
  (MP_TAC(ISPEC p ind) THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
   DISCH_THEN MATCH_MP_TAC) (asl,w);;

let copying_gc_gc_move_loop_thm = prove
 (`!h1 h2 a n (heap:((A,B)heap_element)list) c limit heap0 roots0.
     copying_gc_gc_inv (h1,h2,a,n,heap,c,limit) heap0 roots0
     ==> ?h13 a3 n3 heap3 c3.
           copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) = (h13,a3,n3,heap3,c3) /\
           heap_map 0 heap SUBMAP heap_map 0 heap3 /\
           copying_gc_gc_inv (h13,[],a3,n3,heap3,c3,limit) heap0 roots0`,
  GC1AUX_REC_IND_TAC copying_gc_gc_move_loop_ind THEN CONJ_TAC THENL
   [SIMP_NOASM[copying_gc_gc_move_loop_def; SUBMAP_REFL]; REPEAT GEN_TAC] THEN
  (* only data elements are scanned *)
  CASES_ON `h:(A,B)heap_element` THEN
  TRY(REPEAT STRIP_TAC THEN FS[copying_gc_gc_inv_def; ALL_APPEND; isDataElement_def] THEN
      NO_TAC) THEN
  DISCH_THEN(fun ih -> REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(limit < heap_length (APPEND (h1:((A,B)heap_element)list)
                    (CONS (DataElement a0 a1 a2) h2)))` ASSUME_TAC THENL
     [FS[copying_gc_gc_inv_def] THEN DECIDE_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[copying_gc_gc_move_loop_def] THEN SIMP[] THEN
    (* the scanned element's pointers are moved *)
    DRULE copying_gc_gc_move_list_thm THEN
    DISCH_THEN(QSPEC_THEN "a0" MP_TAC) THEN ANTS_TAC THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP GC1AUX_gc_inv_scan_ok); STRIP_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP copying_gc_gc_move_list_APPEND_lemma) THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
    (* the invariant moves on past the scanned element *)
    IMP_RES_TAC GC1AUX_gc_inv_shift THEN IMP_RES_TAC(CAKE_SIMP_RULE[] ih)) THEN
  FS[] THEN FIRST_X_ASSUM(MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_EXISTS_TAC THEN IMP_RES_TAC SUBMAP_TRANS THEN ASM_REWRITE_TAC[]);;

let copying_gc_gc_inv_init = prove
 (`!limit (heap:((A,B)heap_element)list) (roots:(A heap_address)list).
     copying_gc_gc_inv ([],[],0,limit,heap,T,limit) heap roots <=> heap_ok heap limit`,
  REPEAT GEN_TAC THEN REWRITE_TAC[copying_gc_gc_inv_def] THEN
  ASM_CASES_TAC `heap_ok (heap:((A,B)heap_element)list) limit` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[heap_ok_def]) THEN
  ASM_SIMP_TAC[FILTER_LEMMA; heaps_similar_REFL; heap_map_EMPTY; APPEND; heap_length_NIL;
               ALL; ADD_CLAUSES; heap_addresses_def; FLOOKUP_DEF; NOT_IN_EMPTY;
               option_DISTINCT] THEN
  REWRITE_TAC[BIJ; INJ; SURJ; NOT_IN_EMPTY]);;

let copying_gc_full_gc_thm = prove
 (`!roots (heap:((A,B)heap_element)list) limit.
     roots_ok roots heap /\ heap_ok heap limit
     ==> ?heap2 a2 heap3.
           full_gc (roots,heap,limit) = (ADDR_MAP (heap_map1 heap3) roots,heap2,a2,T) /\
           (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM (heap_map 0 heap3)) /\
           copying_gc_gc_inv (heap2,[],a2,limit - a2,heap3,T,limit) heap roots`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`roots:(A heap_address)list`; `[]:((A,B)heap_element)list`; `0`;
    `limit:num`; `heap:((A,B)heap_element)list`; `T`; `[]:((A,B)heap_element)list`;
    `limit:num`; `heap:((A,B)heap_element)list`; `roots:(A heap_address)list`]
    copying_gc_gc_move_list_thm) THEN
  ASM_REWRITE_TAC[copying_gc_gc_inv_init] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[roots_ok_def]) THEN
    ASM_SIMP_TAC[isSomeDataOrForward_def; reachable_addresses_def] THEN MESON_TAC[RTC_REFL];
    STRIP_TAC] THEN
  DRULE copying_gc_gc_move_loop_thm THEN STRIP_TAC THEN SIMP[full_gc_def] THEN
  QEXISTS_TAC "heap3'" THEN RULE_ASSUM_TAC(REWRITE_RULE[heap_ok_def; SUBMAP_DEF]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[copying_gc_gc_inv_def; APPEND_NIL]) THEN
  ASM_REWRITE_TAC[copying_gc_gc_inv_def; APPEND_NIL] THEN REPEAT CONJ_TAC THEN
  TRY DECIDE_TAC THEN TRY(MATCH_MP_TAC gc_shared_ADDR_MAP_EQ) THEN
  REWRITE_TAC[heap_map1_def] THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: heap_lookup_IMP_heap_addresses (an ML-level lemma of the script) *)
let GC1AUX_heap_lookup_IMP_heap_addresses = prove
 (`!xs (x:(A,B)heap_element) j. heap_lookup j xs = SOME x ==> j IN heap_addresses 0 xs`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC heap_lookup_SPLIT THEN
  ASM_REWRITE_TAC[gc_shared_heap_addresses_APPEND; heap_addresses_def; IN_UNION; IN_INSERT;
                  ADD_CLAUSES]);;

let full_gc_LENGTH = prove
 (`!roots (heap:((A,B)heap_element)list) limit.
     roots_ok roots heap /\ heap_ok heap limit
     ==> ?roots2 heap2 (a2:num).
           full_gc (roots,heap,limit) = (roots2,heap2,heap_length heap2,T)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`roots:(A heap_address)list`; `heap:((A,B)heap_element)list`;
                 `limit:num`] copying_gc_full_gc_thm) THEN
  ASM_REWRITE_TAC[copying_gc_gc_inv_def; APPEND_NIL] THEN MESON_TAC[]);;

(* the final state: the moved heap elements and their new addresses *)

let GC1AUX_gc_inv_final = prove
 (`!heap2 a2 n2 (heap3:((A,B)heap_element)list) c limit heap0 roots0.
     copying_gc_gc_inv (heap2,[],a2,n2,heap3,c,limit) heap0 roots0
     ==> (!i. i IN FDOM (heap_map 0 heap3)
              ==> heap_map1 heap3 i < heap_length heap2 /\
                  ?xs l d. heap_lookup i heap0 = SOME (DataElement xs l d) /\
                           heap_lookup (heap_map1 heap3 i) heap2 =
                             SOME (DataElement (ADDR_MAP (heap_map1 heap3) xs) l d) /\
                           reachable_addresses roots0 heap0 i /\
                           !ptr (d:A). MEM (Pointer ptr d) xs
                                       ==> ptr IN FDOM (heap_map 0 heap3)) /\
         (!j. j IN heap_addresses 0 heap2
              ==> ?i. i IN FDOM (heap_map 0 heap3) /\ heap_map1 heap3 i = j)`,
  REWRITE_TAC[copying_gc_gc_inv_def; APPEND_NIL; BIJ; INJ; SURJ] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `heap_map1 (heap3:((A,B)heap_element)list) i <
                heap_length (heap2:((A,B)heap_element)list)` ASSUME_TAC THENL
   [RES_TAC THEN IMP_RES_TAC heap_addresses_LESS_heap_length THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(QSPECL_THEN ["i"; "heap_map1 heap3 i"] MP_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[heap_map1_def]) THEN
  ASM_REWRITE_TAC[flookup_thm; heap_map1_def]);;

let GC1AUX_gc_inv_closed = prove
 (`!heap2 a2 n2 (heap3:((A,B)heap_element)list) c limit heap0 roots0 j xs l d ptr (u:A).
     copying_gc_gc_inv (heap2,[],a2,n2,heap3,c,limit) heap0 roots0 /\
     heap_lookup j heap2 = SOME (DataElement xs l d) /\ MEM (Pointer ptr u) xs
     ==> ?y. y IN FDOM (heap_map 0 heap3) /\ heap_map1 heap3 y = ptr`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o MATCH_MP GC1AUX_gc_inv_final) STRIP_ASSUME_TAC) THEN
  IMP_RES_TAC GC1AUX_heap_lookup_IMP_heap_addresses THEN RES_TAC THEN RES_TAC THEN
  FS[] THEN RFS[] THEN IMP_RES_TAC MEM_ADDR_MAP THEN RES_TAC THEN ASM_EXISTS_TAC);;

let GC1AUX_NOT_MEM_heap_expand = prove
 (`!n (xs:(A heap_address)list) l (d:B).
     ~MEM (DataElement xs l d) (heap_expand n:((A,B)heap_element)list)`,
  REWRITE_TAC[heap_expand_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MEM; heap_element_distinct]);;

let full_gc_ok = prove
 (`!roots (heap:((A,B)heap_element)list) limit.
     roots_ok roots heap /\ heap_ok heap limit
     ==> ?roots2 heap2 a2.
           full_gc (roots,heap,limit) = (roots2,heap2,a2,T) /\
           a2 <= limit /\
           roots_ok roots2 (APPEND heap2 (heap_expand (limit - a2))) /\
           heap_ok (APPEND heap2 (heap_expand (limit - a2))) limit`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC_ALL copying_gc_full_gc_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN SIMP_NOASM[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[copying_gc_gc_inv_def; APPEND_NIL]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GC1AUX_gc_inv_final) THEN
  (* the new address of an old data element holds a data element *)
  SUBGOAL_THEN
   `!y ys. y IN FDOM (heap_map 0 (heap3:((A,B)heap_element)list))
           ==> isSomeDataElement (heap_lookup (heap_map1 heap3 y)
                 (APPEND (heap2:((A,B)heap_element)list) ys))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC isSome_heap_looukp_IMP_APPEND THEN RES_TAC THEN
    ASM_REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[roots_ok_def; heap_ok_def; heap_length_APPEND; gc_shared_heap_length_heap_expand;
              FILTER_APPEND; MEM_APPEND; GC1AUX_NOT_MEM_heap_expand] THEN
  ASM_SIMP_TAC[EVERY_isDataElement_IMP_LEMMA; APPEND] THEN
  REPEAT CONJ_TAC THENL
   [DECIDE_TAC;
    REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_ADDR_MAP THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[];
    DECIDE_TAC;
    REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN REWRITE_TAC[FILTER; isForwardPointer_def];
    REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_IMP_heap_lookup THEN
    IMP_RES_TAC GC1AUX_gc_inv_closed THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN RES_TAC THEN
    ASM_REWRITE_TAC[]]);;

let GC1AUX_FAPPLY_heap_map = prove
 (`!heap:((A,B)heap_element)list. FAPPLY (heap_map 0 heap) = heap_map1 heap`,
  REWRITE_TAC[FUN_EQ_THM; heap_map1_def]);;

let full_gc_related = prove
 (`!roots (heap:((A,B)heap_element)list) limit.
     roots_ok roots heap /\ heap_ok heap limit
     ==> ?heap2 a2 f.
           full_gc (roots,heap,limit) = (ADDR_MAP (FAPPLY f) roots,heap2,a2,T) /\
           FDOM f = reachable_addresses roots heap /\
           FRANGE f = {a | isSomeDataElement (heap_lookup a heap2)} /\
           heap_length heap2 = heap_length (heap_filter (FDOM f) heap) /\
           gc_related f heap (APPEND heap2 (heap_expand (limit - a2))) /\
           ALL isDataElement heap2`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC_ALL copying_gc_full_gc_thm) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  QEXISTS_TAC "heap2" THEN QEXISTS_TAC "a2" THEN QEXISTS_TAC "heap_map 0 heap3" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[copying_gc_gc_inv_def; APPEND_NIL]) THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "final") ASSUME_TAC o
              MATCH_MP GC1AUX_gc_inv_final) THEN
  REWRITE_TAC[GC1AUX_FAPPLY_heap_map; EXTENSION; IN_FRANGE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the moved addresses are the reachable ones *)
    X_GEN_TAC `x:num` THEN GEN_REWRITE_TAC RAND_CONV [IN] THEN EQ_TAC THENL
     [DISCH_TAC THEN USE_THEN "final" DRULE THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!a b. RTC (gc_edge (heap:((A,B)heap_element)list)) a b
                        ==> a IN FDOM (heap_map 0 (heap3:((A,B)heap_element)list))
                        ==> b IN FDOM (heap_map 0 heap3)` ASSUME_TAC THENL
     [MATCH_MP_TAC RTC_INDUCT THEN SIMP_NOASM[gc_edge_def] THEN REPEAT STRIP_TAC THEN
      USE_THEN "final" DRULE THEN ASM_REWRITE_TAC[option_INJ; heap_element_11] THEN
      SIMP_NOASM[] THEN STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[reachable_addresses_def] THEN ASM_MESON_TAC[]];
    (* the new addresses are those of heap2 *)
    X_GEN_TAC `x:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN USE_THEN "final" DRULE THEN
      REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
      REWRITE_TAC[isSomeDataElement_def] THEN STRIP_TAC THEN
      IMP_RES_TAC GC1AUX_heap_lookup_IMP_heap_addresses THEN RES_TAC THEN ASM_EXISTS_TAC];
    GEN_REWRITE_TAC LAND_CONV [GSYM heap_length_heap_filter] THEN
    MATCH_MP_TAC heap_length_heap_filter_eq THEN
    QEXISTS_TAC "heap_map1 heap3" THEN
    ASM_REWRITE_TAC[FDOM_FINITE; FINITE_heap_addresses] THEN
    REPEAT STRIP_TAC THEN USE_THEN "final" DRULE THEN MESON_TAC[];
    REWRITE_TAC[gc_related_def; GC1AUX_FAPPLY_heap_map; INJ; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC isSome_heap_looukp_IMP_APPEND THEN
      USE_THEN "final" DRULE THEN REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[BIJ]) THEN REWRITE_TAC[INJ] THEN
      MESON_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "final" DRULE THEN
      REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "final" DRULE THEN
      ASM_REWRITE_TAC[option_INJ; heap_element_11] THEN SIMP_NOASM[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[gc_shared_heap_lookup_EXTEND]]]);;

(* Lemmas about ok and a *)

let copying_gc_gc_move_ok = prove
 (`!(x:A heap_address) h2 a n (heap:((A,B)heap_element)list) c limit x' h2' a' n' heap' b.
     copying_gc_gc_move (x,h2,a,n,heap,c,limit) = (x',h2',a',n',heap',T)
     ==> c /\ (a = b + heap_length h2 ==> a' = b + heap_length h2')`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  SIMP[copying_gc_gc_move_def] THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  RW[] THEN RFS[] THEN IMP_RES_TAC gc_shared_gc_forward_ptr_ok THEN
  FS[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def] THEN DECIDE_TAC);;

(* In the proofs by induction below, an induction hypothesis whose conclusion *)
(* is a boolean variable (c) or applies a predicate to a variable is kept   *)
(* out of the assumptions while the kit simplifies them: as an assumption   *)
(* it would be a conditional rewrite of every boolean (or every ALL P x)    *)
(* term.                                                                    *)

let copying_gc_gc_move_list_ok = prove
 (`!xs h2 a n (heap:((A,B)heap_element)list) c limit xs' h2' a' n' heap' (c':bool) b.
     copying_gc_gc_move_list (xs:(A heap_address)list,h2,a,n,heap,c,limit) =
       (xs',h2',a',n',heap',T)
     ==> c /\ (a = b + heap_length h2 ==> a' = b + heap_length h2')`,
  LIST_INDUCT_TAC THEN SIMP_NOASM[copying_gc_gc_move_list_def] THEN
  POP_ASSUM(fun ih -> REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN RW[] THEN RFS[] THEN
    IMP_RES_TAC ih THEN RFS[] THEN IMP_RES_TAC copying_gc_gc_move_ok THEN
    ASM_MESON_TAC[]));;

let copying_gc_gc_move_loop_ok = prove
 (`!h1 h2 a n (heap:((A,B)heap_element)list) c limit h1' a' n' heap'.
     copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T) ==> c`,
  GC1AUX_REC_IND_TAC copying_gc_gc_move_loop_ind THEN CONJ_TAC THENL
   [SIMP_NOASM[copying_gc_gc_move_loop_def]; REPEAT GEN_TAC] THEN
  CASES_ON `h:(A,B)heap_element` THEN
  DISCH_THEN(fun ih -> ONCE_REWRITE_TAC[copying_gc_gc_move_loop_def] THEN
    RW[] THEN REPEAT PAIRARG_TAC THEN FS[] THEN IMP_RES_TAC(CAKE_SIMP_RULE[] ih)) THEN
  RFS[] THEN IMP_RES_TAC copying_gc_gc_move_list_ok THEN ASM_MESON_TAC[]);;

let gc_move_list_IMP_LENGTH = prove
 (`!l5 h a n (heap:((A,B)heap_element)list) c k xs ys a1 xs1 heap1 c1.
     copying_gc_gc_move_list (l5:(A heap_address)list,h,a,n,heap,c,k) =
       (xs,ys,a1,xs1,heap1,c1)
     ==> LENGTH xs = LENGTH l5`,
  LIST_INDUCT_TAC THEN FS[copying_gc_gc_move_list_def] THEN RW[] THEN
  REPEAT PAIRARG_TAC THEN FS[] THEN RW[] THEN RES_TAC THEN FS[]);;

let full_gc_IMP_LENGTH = prove
 (`!(xs:(A heap_address)list) (heap:((A,B)heap_element)list) limit roots2 heap2 h.
     full_gc (xs,heap,limit) = (roots2,heap2,h,T) ==> LENGTH roots2 = LENGTH xs`,
  REWRITE_TAC[full_gc_def] THEN REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN RW[] THEN
  IMP_RES_TAC gc_move_list_IMP_LENGTH THEN ASM_REWRITE_TAC[]);;

let gc_move_IMP_isDataElement = prove
 (`!l5 h a n (heap:((A,B)heap_element)list) c k xs ys a1 xs1 heap1 c1.
     ALL isDataElement h /\
     copying_gc_gc_move (l5:A heap_address,h,a,n,heap,c,k) = (xs,ys,a1,xs1,heap1,c1)
     ==> ALL isDataElement ys`,
  GEN_TAC THEN CASES_ON `l5:A heap_address` THEN FS[copying_gc_gc_move_def] THEN
  RW[] THEN EVERY_CASE_TAC THEN FS[] THEN RW[] THEN FS[isDataElement_def]);;

let gc_move_list_IMP_isDataElement = prove
 (`!l5 h a n (heap:((A,B)heap_element)list) c k xs ys a1 xs1 heap1 c1.
     ALL isDataElement h /\
     copying_gc_gc_move_list (l5:(A heap_address)list,h,a,n,heap,c,k) =
       (xs,ys,a1,xs1,heap1,c1)
     ==> ALL isDataElement ys`,
  LIST_INDUCT_TAC THEN SIMP_NOASM[copying_gc_gc_move_list_def] THEN
  REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN SIMP_NOASM[] THEN STRIP_TAC THEN
  RVEQ_TAC THEN IMP_RES_TAC gc_move_IMP_isDataElement THEN RES_TAC THEN
  ASM_REWRITE_TAC[]);;

let GC1AUX_ALL_TL = prove
 (`!P (l:A list). ~(l = []) /\ ALL P l ==> ALL P (TL l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP_TAC[ALL; TL]);;

let gc_move_loop_IMP_isDataElement = prove
 (`!h1 h2 a n (heap:((A,B)heap_element)list) c limit h1' a' n' heap' (c':bool).
     ALL isDataElement h1 /\ ALL isDataElement h2 /\
     copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T)
     ==> ALL isDataElement h1'`,
  GC1AUX_REC_IND_TAC copying_gc_gc_move_loop_ind THEN CONJ_TAC THENL
   [SIMP_NOASM[copying_gc_gc_move_loop_def]; REPEAT GEN_TAC] THEN
  CASES_ON `h:(A,B)heap_element` THEN
  DISCH_THEN(fun ih -> PURE_ONCE_REWRITE_TAC[copying_gc_gc_move_loop_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
    SIMP_NOASM[] THEN REPEAT PAIRARG_TAC THEN SIMP_NOASM[] THEN STRIP_TAC THEN
    IMP_RES_TAC gc_move_list_IMP_isDataElement THEN
    IMP_RES_TAC copying_gc_gc_move_loop_ok THEN IMP_RES_TAC GC1AUX_ALL_TL THEN
    IMP_RES_TAC(CAKE_SIMP_RULE[isDataElement_def] ih) THEN ASM_REWRITE_TAC[]));;

let full_gc_IMP_isDataElement = prove
 (`!(roots:(A heap_address)list) (heap:((A,B)heap_element)list) limit roots1 heap1 a.
     full_gc (roots,heap,limit) = (roots1,heap1,a,T) ==> ALL isDataElement heap1`,
  REWRITE_TAC[full_gc_def] THEN REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN
  RW[] THEN RFS[] THEN
  IRULE gc_move_loop_IMP_isDataElement THEN ASM_EXISTS_TAC THEN REWRITE_TAC[ALL] THEN
  IRULE gc_move_list_IMP_isDataElement THEN ASM_EXISTS_TAC THEN REWRITE_TAC[ALL]);;
