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

(* HOL4: gc_move_list_def.  The kit (HOL Light recursion analysis) does not   *)
(* finish on the nested tuple matches of this definition within minutes, so *)
(* the function is defined by primitive recursion on the list through the   *)
(* curried GC1AUX_gc_move_list and the HOL4 clauses are derived.            *)

let GC1AUX_gc_move_list_def = new_recursive_definition list_RECURSION
  (CASE_TERM
   `(GC1AUX_gc_move_list ([]:(A heap_address)list) (h2:((A,B)heap_element)list)
       (a:num) (n:num) (heap:((A,B)heap_element)list) (c:bool) (limit:num) =
       ([]:(A heap_address)list,h2,a,n,heap,c)) /\
    (GC1AUX_gc_move_list (CONS x xs) h2 a n heap c limit =
       match copying_gc_gc_move (x,h2,a,n,heap,c,limit) with
         (x,h2,a,n,heap,c) ->
           match GC1AUX_gc_move_list xs h2 a n heap c limit with
             (xs,h2,a,n,heap,c) -> (CONS x xs,h2,a,n,heap,c))`);;

let GC1AUX_gc_move_list_tuple = cake_def
  `copying_gc_gc_move_list (xs:(A heap_address)list,h2:((A,B)heap_element)list,
                            a:num,n:num,heap:((A,B)heap_element)list,c:bool,limit:num) =
     GC1AUX_gc_move_list xs h2 a n heap c limit`;;

let copying_gc_gc_move_list_def = prove
 (CASE_TERM
  `(!h2:((A,B)heap_element)list a n heap c limit.
      copying_gc_gc_move_list ([]:(A heap_address)list,h2,a,n,heap,c,limit) =
      ([],h2,a,n,heap,c)) /\
   (!(x:A heap_address) xs (h2:((A,B)heap_element)list) a n heap c limit.
      copying_gc_gc_move_list (CONS x xs,h2,a,n,heap,c,limit) =
      match copying_gc_gc_move (x,h2,a,n,heap,c,limit) with
        (x,h2,a,n,heap,c) ->
          match copying_gc_gc_move_list (xs,h2,a,n,heap,c,limit) with
            (xs,h2,a,n,heap,c) -> (CONS x xs,h2,a,n,heap,c))`,
  REWRITE_TAC[GC1AUX_gc_move_list_tuple; GC1AUX_gc_move_list_def]);;

(* HOL4: gc_move_loop_def.  As for gc_move_list, cake_def_wf does not finish *)
(* on this definition, so it is made by well-founded recursion on the      *)
(* measure of HOL4, limit - heap_length h1 (WF_REC, GC1AUX_WF_REC_TUPLE7);  *)
(* the clauses and the induction theorem are derived.                       *)

let GC1AUX_WF_REC_TUPLE7 = prove
 (`!(m:A#B#C#D#E#P#Q->num) (H:(A#B#C#D#E#P#Q->R)->A->B->C->D->E->P->Q->R).
     (!f g x1 x2 x3 x4 x5 x6 x7.
        (!z. m z < m (x1,x2,x3,x4,x5,x6,x7) ==> f z = g z)
        ==> H f x1 x2 x3 x4 x5 x6 x7 = H g x1 x2 x3 x4 x5 x6 x7)
     ==> ?f. !x1 x2 x3 x4 x5 x6 x7.
               f (x1,x2,x3,x4,x5,x6,x7) = H f x1 x2 x3 x4 x5 x6 x7`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP (INST_TYPE [`:R`,`:B`] WF_REC)
                   (ISPEC `m:A#B#C#D#E#P#Q->num` WF_measure)) THEN
  DISCH_THEN(MP_TAC o SPEC
    `\(f:A#B#C#D#E#P#Q->R) (p:A#B#C#D#E#P#Q).
       (H:(A#B#C#D#E#P#Q->R)->A->B->C->D->E->P->Q->R) f
         (FST p) (FST(SND p)) (FST(SND(SND p))) (FST(SND(SND(SND p))))
         (FST(SND(SND(SND(SND p))))) (FST(SND(SND(SND(SND(SND p))))))
         (SND(SND(SND(SND(SND(SND p))))))`) THEN
  REWRITE_TAC[measure_THM] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; FST; SND]));;

let GC1AUX_gc_move_loop_exists = prove
 (CASE_TERM
  `?f. !(h1:((A,B)heap_element)list) (h2:((A,B)heap_element)list) (a:num) (n:num)
        (heap:((A,B)heap_element)list) (c:bool) (limit:num).
     f (h1,h2,a,n,heap,c,limit):((A,B)heap_element)list#num#num#((A,B)heap_element)list#bool =
     match h2 with
       [] -> (h1,a,n,heap,c)
     | CONS h h2 ->
         if limit < heap_length (APPEND h1 (CONS h h2)) then (h1,a,n,heap,F) else
         match h with
           DataElement xs l d ->
             (match copying_gc_gc_move_list (xs,CONS h h2,a,n,heap,c,limit) with
                (xs,h2,a,n,heap,c) ->
                  let c = (c /\ ~(h2 = []) /\ HD h2 = h) in
                  let h2 = TL h2 in
                  let h1 = APPEND h1 [DataElement xs l d] in
                    f (h1,h2,a,n,heap,c,limit))
         | _ -> (h1,a,n,heap,F)`,
  MATCH_MP_TAC GC1AUX_WF_REC_TUPLE7 THEN
  EXISTS_TAC `\p:((A,B)heap_element)list#((A,B)heap_element)list#num#num#
                 ((A,B)heap_element)list#bool#num.
                 SND(SND(SND(SND(SND(SND p))))) - heap_length (FST p)` THEN
  REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  EVERY_CASE_TAC THEN SIMP_NOASM[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def]) THEN
  REWRITE_TAC[FST; SND; heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL;
              el_length_def] THEN
  ASM_ARITH_TAC);;

let GC1AUX_gc_move_loop_spec =
  new_specification ["copying_gc_gc_move_loop"] GC1AUX_gc_move_loop_exists;;

let copying_gc_gc_move_loop_def = prove
 (CASE_TERM
  `(!(h1:((A,B)heap_element)list) a n (heap:((A,B)heap_element)list) c limit.
      copying_gc_gc_move_loop (h1,[],a,n,heap,c,limit) = (h1,a,n,heap,c)) /\
   (!(h1:((A,B)heap_element)list) h h2 a n heap c limit.
      copying_gc_gc_move_loop (h1,CONS h h2,a,n,heap,c,limit) =
      if limit < heap_length (APPEND h1 (CONS h h2)) then (h1,a,n,heap,F) else
      match h with
        DataElement xs l d ->
          (match copying_gc_gc_move_list (xs,CONS h h2,a,n,heap,c,limit) with
             (xs,h2,a,n,heap,c) ->
               let c = (c /\ ~(h2 = []) /\ HD h2 = h) in
               let h2 = TL h2 in
               let h1 = APPEND h1 [DataElement xs l d] in
                 copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit))
      | _ -> (h1,a,n,heap,F))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GC1AUX_gc_move_loop_spec] THEN
  REWRITE_TAC[list_CASE]);;

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
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") (LABEL_TAC "step")) THEN
  MP_TAC(ISPEC `\p:((A,B)heap_element)list#((A,B)heap_element)list#num#num#
                   ((A,B)heap_element)list#bool#num.
                   SND(SND(SND(SND(SND(SND p))))) - heap_length (FST p)` WF_measure) THEN
  REWRITE_TAC[WF_IND] THEN
  DISCH_THEN(MP_TAC o SPEC `P:((A,B)heap_element)list#((A,B)heap_element)list#num#num#
                               ((A,B)heap_element)list#bool#num->bool`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; measure_THM; FST; SND] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`h1:((A,B)heap_element)list`; `h2:((A,B)heap_element)list`;
    `a:num`; `n:num`; `heap:((A,B)heap_element)list`; `c:bool`; `limit:num`] THEN
  DISCH_TAC THEN CASES_ON `h2:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "step" MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def]) THEN
  REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN
  ASM_ARITH_TAC);;

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
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n IN FDOM (heap_map k (heap:((A,B)heap_element)list)))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP IN_heap_map_IMP) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM fmap_EQ_THM; DRESTRICT_DEF; IN_INTER; IN_COMPL; IN_SING] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_COMPL; IN_SING] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

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

(* the data element case of gc_move_thm, in steps *)

let GC1AUX_heap_map_forward = prove
 (`!ha hb (ys:(A heap_address)list) l (d:B) a (u:A).
     heap_map 0 (APPEND ha (CONS (ForwardPointer a u l) hb)) =
     heap_map 0 (APPEND ha (CONS (DataElement ys l d) hb)) |+ (heap_length ha,a)`,
  REWRITE_TAC[heap_map_APPEND; heap_map_def; el_length_def; ADD_CLAUSES;
              FUNION_FUPDATE_2; FDOM_heap_map]);;

let GC1AUX_gc_move_data = prove
 (`!ha hb (ys:(A heap_address)list) l (d:B) h2 a n c limit (u:A).
     copying_gc_gc_move (Pointer (heap_length ha) u,h2,a,n,
                         APPEND ha (CONS (DataElement ys l d) hb),c,limit) =
     (Pointer a u,APPEND h2 [DataElement ys l d],a + (l + 1),n - (l + 1),
      APPEND ha (CONS (ForwardPointer a u l) hb),(c /\ l + 1 <= n /\ a + n = limit))`,
  REWRITE_TAC[copying_gc_gc_move_def; heap_lookup_PREFIX] THEN
  SIMP_NOASM[LET_DEF; LET_END_DEF; gc_forward_ptr_thm]);;

let GC1AUX_FILTER_forward = prove
 (`!ha hb (ys:(A heap_address)list) l (d:B) a (u:A).
     heap_length (FILTER (\h. ~isForwardPointer h)
                   (APPEND ha (CONS (DataElement ys l d) hb))) =
     heap_length (FILTER (\h. ~isForwardPointer h)
                   (APPEND ha (CONS (ForwardPointer a u l) hb))) + (l + 1)`,
  REWRITE_TAC[FILTER_APPEND; FILTER; isForwardPointer_def; heap_length_APPEND;
              GC1AUX_heap_length_CONS; el_length_def] THEN
  ARITH_TAC);;

let GC1AUX_isDataElement_DataElement = prove
 (`!(ys:(A heap_address)list) l (d:B). isDataElement (DataElement ys l d)`,
  REWRITE_TAC[isDataElement_def] THEN MESON_TAC[]);;

let GC1AUX_gc_inv_forward_lookup = prove
 (`!(ff:(num,num)fmap) h1 h2 a ha hb (ys:(A heap_address)list) l (d:B) heap0 roots0.
     ~(heap_length ha IN FDOM ff) /\
     a = heap_length (APPEND h1 h2) /\
     heaps_similar heap0 (APPEND ha (CONS (DataElement ys l d) hb)) /\
     reachable_addresses roots0 heap0 (heap_length ha) /\
     (!i j. FLOOKUP ff i = SOME j
            ==> ?xs l' d'.
                  heap_lookup i heap0 = SOME (DataElement xs l' d') /\
                  heap_lookup j (APPEND h1 h2) =
                    SOME (DataElement (if j < heap_length h1
                                       then ADDR_MAP (\x. FAPPLY ff x) xs else xs) l' d') /\
                  reachable_addresses roots0 heap0 i /\
                  !ptr (d:A). MEM (Pointer ptr d) xs /\ j < heap_length h1
                              ==> ptr IN FDOM ff)
     ==> !i j. FLOOKUP (ff |+ (heap_length ha,a)) i = SOME j
               ==> ?xs l' d'.
                     heap_lookup i heap0 = SOME (DataElement xs l' d') /\
                     heap_lookup j (APPEND h1 (APPEND h2 [DataElement ys l d])) =
                       SOME (DataElement
                               (if j < heap_length h1
                                then ADDR_MAP (\x. FAPPLY (ff |+ (heap_length ha,a)) x) xs
                                else xs) l' d') /\
                     reachable_addresses roots0 heap0 i /\
                     !ptr (d:A). MEM (Pointer ptr d) xs /\ j < heap_length h1
                                 ==> ptr IN FDOM (ff |+ (heap_length ha,a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `heap_lookup (heap_length (ha:((A,B)heap_element)list))
                    (heap0:((A,B)heap_element)list) =
                  SOME (DataElement ys l d)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP heap_similar_Data_IMP) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[heap_lookup_PREFIX];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ys:(A heap_address)list`; `l:num`; `d:B`] THEN
    REWRITE_TAC[APPEND_ASSOC; heap_lookup_PREFIX] THEN
    ASM_REWRITE_TAC[heap_length_APPEND; ARITH_RULE `~(m + n < m:num)`];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A heap_address)list` (X_CHOOSE_THEN `l':num`
    (X_CHOOSE_THEN `d':B` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l':num`; `d':B`] THEN
  ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[APPEND_ASSOC] THEN
  MATCH_MP_TAC gc_shared_heap_lookup_EXTEND THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; injectivity "heap_element"] THEN
  MATCH_MP_TAC gc_shared_ADDR_MAP_EQ THEN REWRITE_TAC[FAPPLY_FUPDATE_THM] THEN
  ASM_MESON_TAC[]);;

let GC1AUX_BIJ_forward = prove
 (`!(ff:(num,num)fmap) k a s.
     BIJ (\x. FAPPLY ff x) (FDOM ff) s /\ ~(k IN FDOM ff) /\ ~(a IN s)
     ==> BIJ (\x. FAPPLY (ff |+ (k,a)) x) (FDOM (ff |+ (k,a))) (a INSERT s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. FAPPLY ((ff:(num,num)fmap) |+ (k,a)) x) = (k =+ a) (\x. FAPPLY ff x)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM; FAPPLY_FUPDATE_THM] THEN MESON_TAC[];
    REWRITE_TAC[FDOM_FUPDATE] THEN MATCH_MP_TAC BIJ_UPDATE THEN ASM_REWRITE_TAC[]]);;

let GC1AUX_gc_inv_forward = prove
 (`!h1 h2 a n ha hb (ys:(A heap_address)list) l (d:B) c limit heap0 roots0 (u:A).
     copying_gc_gc_inv (h1,h2,a,n,APPEND ha (CONS (DataElement ys l d) hb),c,limit)
       heap0 roots0 /\
     reachable_addresses roots0 heap0 (heap_length ha)
     ==> copying_gc_gc_inv
           (h1,APPEND h2 [DataElement ys l d],a + (l + 1),n - (l + 1),
            APPEND ha (CONS (ForwardPointer a u l) hb),
            (c /\ l + 1 <= n /\ a + n = limit),limit) heap0 roots0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[copying_gc_gc_inv_def; heap_map1_def; GC1AUX_heap_map_forward] THEN
  MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `ys:(A heap_address)list`; `l:num`;
                 `d:B`; `hb:((A,B)heap_element)list`] NOT_IN_heap_map) THEN
  MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `hb:((A,B)heap_element)list`;
                 `ys:(A heap_address)list`; `l:num`; `d:B`; `a:num`; `u:A`]
                GC1AUX_FILTER_forward) THEN
  SPEC_TAC(`heap_map 0 (APPEND ha (CONS (DataElement ys l d) hb):((A,B)heap_element)list)`,
           `ff:(num,num)fmap`) THEN
  GEN_TAC THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `heap_length (APPEND h1 (APPEND h2 [DataElement (ys:(A heap_address)list) l (d:B)])) =
     a + (l + 1)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL;
                    el_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `heap_length (APPEND ha (CONS (ForwardPointer a (u:A) l)
                                  (hb:((A,B)heap_element)list))) = limit`
    ASSUME_TAC THENL
   [UNDISCH_TAC `heap_length (APPEND ha (CONS (DataElement (ys:(A heap_address)list) l (d:B))
                                              hb)) = limit` THEN
    REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `heap0:((A,B)heap_element)list`;
                   `ys:(A heap_address)list`; `l:num`; `d:B`;
                   `hb:((A,B)heap_element)list`; `h1:((A,B)heap_element)list`;
                   `h2:((A,B)heap_element)list`; `u:A`]
                  gc_shared_heaps_similar_lemma) THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
    ASM_REWRITE_TAC[ALL_APPEND; ALL; GC1AUX_isDataElement_DataElement];
    REWRITE_TAC[APPEND_ASSOC; heap_addresses_SNOC; ADD_CLAUSES] THEN
    SUBGOAL_THEN
      `heap_addresses 0 (APPEND h1 h2) UNION {heap_length (APPEND h1 h2)} =
       a INSERT heap_addresses 0 (APPEND (h1:((A,B)heap_element)list) h2)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GC1AUX_BIJ_forward THEN
    ASM_REWRITE_TAC[GC1AUX_NOT_IN_heap_addresses];
    MATCH_MP_TAC GC1AUX_gc_inv_forward_lookup THEN
    EXISTS_TAC `hb:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[]]);;

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
  REPEAT GEN_TAC THEN CASES_ON `x:A heap_address` THENL
   [ALL_TAC;
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`gc_shared_Data a':A heap_address`;
      `h2:((A,B)heap_element)list`; `a:num`; `n:num`;
      `heap:((A,B)heap_element)list`; `c:bool`] THEN
    ASM_SIMP_TAC[copying_gc_gc_move_def; ADDR_APPLY_def; SUBMAP_REFL;
                 GSYM heap_address_distinct]] THEN
  SIMP_NOASM[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(?ptr (d:A) l. heap_lookup a0 heap = SOME (ForwardPointer ptr d l:(A,B)heap_element)) \/
     (?ys l (d:B). heap_lookup a0 heap = SOME (DataElement ys l d))`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[isSomeDataOrForward_def; isSomeForwardPointer_def;
                  isSomeDataElement_def];
    (* a forward pointer: nothing moves *)
    MAP_EVERY EXISTS_TAC [`h2:((A,B)heap_element)list`; `a:num`; `n:num`;
      `heap:((A,B)heap_element)list`; `c:bool`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_FLOOKUP) THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
    SIMP[copying_gc_gc_move_def; ADDR_APPLY_def; heap_map1_def; SUBMAP_REFL];
    (* a data element: it is copied and a forward pointer is left behind *)
    FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`APPEND h2 [DataElement ys l d:(A,B)heap_element]`;
      `a + (l + 1)`; `n - (l + 1)`;
      `APPEND ha (CONS (ForwardPointer a a1 l:(A,B)heap_element) hb)`;
      `c /\ l + 1 <= n /\ a + n = limit`] THEN
    REWRITE_TAC[GC1AUX_gc_move_data; ADDR_APPLY_def; heap_map1_def;
                GC1AUX_heap_map_forward; FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT;
                SUBMAP_FUPDATE_EQN; NOT_IN_heap_map] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:num` THEN
      MP_TAC(ISPECL [`ha:((A,B)heap_element)list`; `p:num`; `ys:(A heap_address)list`;
                     `l:num`; `d:B`; `hb:((A,B)heap_element)list`; `a:num`; `a1:A`]
                    gc_shared_isSomeDataOrForward_lemma) THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
      MATCH_MP_TAC GC1AUX_gc_inv_forward THEN ASM_REWRITE_TAC[]]]);;

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
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`h2:((A,B)heap_element)list`; `a:num`; `n:num`;
      `heap:((A,B)heap_element)list`; `c:bool`] THEN
    ASM_REWRITE_TAC[copying_gc_gc_move_list_def; ADDR_MAP_def; MEM; SUBMAP_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h1:((A,B)heap_element)list`; `h2:((A,B)heap_element)list`; `a:num`;
                 `n:num`; `heap:((A,B)heap_element)list`; `c:bool`; `limit:num`;
                 `heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`;
                 `h:A heap_address`] copying_gc_gc_move_thm) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`h23:((A,B)heap_element)list`; `a3:num`; `n3:num`;
    `heap3:((A,B)heap_element)list`; `c3:bool`; `h1:((A,B)heap_element)list`;
    `limit:num`; `heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h23':((A,B)heap_element)list`; `a3':num`; `n3':num`;
    `heap3':((A,B)heap_element)list`; `c3':bool`] THEN
  ASM_REWRITE_TAC[copying_gc_gc_move_list_def; pair_CASE] THEN
  REPEAT CONJ_TAC THENL
   [CASES_ON `h:A heap_address` THEN
    REWRITE_TAC[ADDR_MAP_def; ADDR_APPLY_def; PAIR_EQ; CONS_11; heap_address_11;
                heap_map1_def] THEN
    ASM_MESON_TAC[SUBMAP_DEF];
    REWRITE_TAC[MEM] THEN ASM_MESON_TAC[SUBMAP_DEF];
    ASM_MESON_TAC[SUBMAP_TRANS]]);;

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

(* gc_move_loop_thm, in steps: lookups around a heap element, the scanned *)
(* element is reachable and points to data or forward pointers, and the    *)
(* invariant moves on past the scanned element                            *)

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

let GC1AUX_gc_inv_scan_ok = prove
 (`!h1 (ys:(A heap_address)list) l (d:B) t a n heap c limit heap0 roots0.
     copying_gc_gc_inv (h1,CONS (DataElement ys l d) t,a,n,heap,c,limit) heap0 roots0
     ==> !ptr u. MEM (Pointer ptr u) ys
                 ==> isSomeDataOrForward (heap_lookup ptr heap) /\
                     reachable_addresses roots0 heap0 ptr`,
  REPEAT GEN_TAC THEN REWRITE_TAC[copying_gc_gc_inv_def] THEN STRIP_TAC THEN
   SUBGOAL_THEN `?i. FLOOKUP (heap_map 0 (heap:((A,B)heap_element)list)) i =
                     SOME (heap_length (h1:((A,B)heap_element)list))`
     STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `BIJ (heap_map1 (heap:((A,B)heap_element)list)) (FDOM (heap_map 0 heap))
                    (heap_addresses 0 (APPEND (h1:((A,B)heap_element)list)
                       (CONS (DataElement (ys:(A heap_address)list) l (d:B)) t)))` THEN
     REWRITE_TAC[BIJ; SURJ; heap_map1_def; FLOOKUP_DEF; gc_shared_heap_addresses_APPEND;
                 heap_addresses_def; IN_UNION; IN_INSERT; ADD_CLAUSES] THEN
     MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `heap_length (h1:((A,B)heap_element)list)`]) THEN
   ASM_REWRITE_TAC[heap_lookup_PREFIX; LT_REFL; option_INJ; heap_element_11] THEN
   STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
     let l,r = dest_eq(concl th) in is_var l && is_var r))) THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC heap_similar_Data_IMP_DataOrForward THEN
    EXISTS_TAC `heap0:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `heap_ok (heap0:((A,B)heap_element)list) limit` THEN
    REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[heap_lookup_MEM];
    UNDISCH_TAC `reachable_addresses roots0 (heap0:((A,B)heap_element)list) i` THEN
    REWRITE_TAC[reachable_addresses_def] THEN
    ASM_MESON_TAC[RTC_TRANS; RTC_INC; gc_edge_def]]);;

let GC1AUX_gc_inv_shift = prove
 (`!h1 (ys:(A heap_address)list) l (d:B) r a n heap c limit heap0 roots0.
     copying_gc_gc_inv (h1,CONS (DataElement ys l d) r,a,n,heap,c,limit) heap0 roots0 /\
     (!ptr u. MEM (Pointer ptr u) ys ==> ptr IN FDOM (heap_map 0 heap))
     ==> copying_gc_gc_inv
           (APPEND h1 [DataElement (ADDR_MAP (heap_map1 heap) ys) l d],r,a,n,heap,c,limit)
           heap0 roots0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[copying_gc_gc_inv_def; GSYM APPEND_ASSOC; APPEND] THEN
   SUBGOAL_THEN
     `heap_length (APPEND h1 (CONS (DataElement
        (ADDR_MAP (heap_map1 (heap:((A,B)heap_element)list)) ys) l d) r)) =
      heap_length (APPEND h1 (CONS (DataElement (ys:(A heap_address)list) l (d:B)) r)) /\
      heap_addresses 0 (APPEND h1 (CONS (DataElement
        (ADDR_MAP (heap_map1 (heap:((A,B)heap_element)list)) ys) l d) r)) =
      heap_addresses 0 (APPEND h1 (CONS (DataElement ys l d) r:((A,B)heap_element)list))`
     (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def;
                 gc_shared_heap_addresses_APPEND; heap_addresses_def];
     ALL_TAC] THEN
   REWRITE_TAC[ALL_APPEND; ALL; GC1AUX_isDataElement_DataElement] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def;
               ADD_CLAUSES] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[GC1AUX_heap_lookup_APPEND_CONS; el_length_def] THEN
   ASM_CASES_TAC `j < heap_length (h1:((A,B)heap_element)list)` THEN
   ASM_SIMP_TAC[ARITH_RULE `j < h ==> j < h + l + 1`] THEN
  ASM_CASES_TAC `j = heap_length (h1:((A,B)heap_element)list)` THEN
   ASM_REWRITE_TAC[] THENL
    [REWRITE_TAC[option_INJ; heap_element_11; ARITH_RULE `h < h + l + 1`] THEN
     DISCH_THEN(X_CHOOSE_THEN `xs:(A heap_address)list` (X_CHOOSE_THEN `l':num`
       (X_CHOOSE_THEN `d':B` STRIP_ASSUME_TAC))) THEN
     MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l':num`; `d':B`] THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ASM_CASES_TAC `j < heap_length (h1:((A,B)heap_element)list) + l + 1` THEN
     ASM_REWRITE_TAC[option_DISTINCT]]);;

let copying_gc_gc_move_loop_thm = prove
 (`!h1 h2 a n (heap:((A,B)heap_element)list) c limit heap0 roots0.
     copying_gc_gc_inv (h1,h2,a,n,heap,c,limit) heap0 roots0
     ==> ?h13 a3 n3 heap3 c3.
           copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) = (h13,a3,n3,heap3,c3) /\
           heap_map 0 heap SUBMAP heap_map 0 heap3 /\
           copying_gc_gc_inv (h13,[],a3,n3,heap3,c3,limit) heap0 roots0`,
  SUBGOAL_THEN
   `!k h1 h2 a n (heap:((A,B)heap_element)list) c limit heap0 roots0.
       limit - heap_length h1 = k /\
       copying_gc_gc_inv (h1,h2,a,n,heap,c,limit) heap0 roots0
       ==> ?h13 a3 n3 heap3 c3.
             copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) = (h13,a3,n3,heap3,c3) /\
             heap_map 0 heap SUBMAP heap_map 0 heap3 /\
             copying_gc_gc_inv (h13,[],a3,n3,heap3,c3,limit) heap0 roots0`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   CASES_ON `h2:((A,B)heap_element)list` THENL
    [MAP_EVERY EXISTS_TAC [`h1:((A,B)heap_element)list`; `a:num`; `n:num`;
       `heap:((A,B)heap_element)list`; `c:bool`] THEN
     ASM_REWRITE_TAC[copying_gc_gc_move_loop_def; SUBMAP_REFL];
     ALL_TAC] THEN
  SUBGOAL_THEN `?(ys:(A heap_address)list) l (d:B). a0 = DataElement ys l d`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ASSUME `copying_gc_gc_inv (h1,CONS (a0:(A,B)heap_element) a1,a,n,
                      (heap:((A,B)heap_element)list),c,limit) heap0 roots0`) THEN
     REWRITE_TAC[copying_gc_gc_inv_def; ALL; isDataElement_def] THEN MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   SUBGOAL_THEN `~(limit < heap_length (APPEND h1 (CONS (DataElement ys l d) a1))) /\
                 heap_length (h1:((A,B)heap_element)list) + l + 1 <= limit`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ASSUME `copying_gc_gc_inv (h1,CONS (DataElement ys l d) a1,a,n,
                      (heap:((A,B)heap_element)list),c,limit) heap0 roots0`) THEN
     REWRITE_TAC[copying_gc_gc_inv_def] THEN STRIP_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS;
                                 el_length_def]) THEN
     REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; el_length_def] THEN
     ASM_ARITH_TAC;
     ALL_TAC] THEN
   ONCE_REWRITE_TAC[copying_gc_gc_move_loop_def] THEN ASM_REWRITE_TAC[] THEN
   SIMP_NOASM[] THEN
  MP_TAC(ISPECL [`ys:(A heap_address)list`;
     `CONS (DataElement ys l d) a1:((A,B)heap_element)list`; `a:num`; `n:num`;
     `heap:((A,B)heap_element)list`; `c:bool`; `h1:((A,B)heap_element)list`; `limit:num`;
     `heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]
     copying_gc_gc_move_list_thm) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP GC1AUX_gc_inv_scan_ok)];
     ALL_TAC] THEN
   STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP copying_gc_gc_move_list_APPEND_lemma) THEN
   STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
   ASM_REWRITE_TAC[pair_CASE; APPEND; TL; HD; NOT_CONS_NIL] THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC
     `limit - heap_length (APPEND (h1:((A,B)heap_element)list)
        [DataElement (ADDR_MAP (heap_map1 (heap3:((A,B)heap_element)list)) ys) l d])`) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL;
                 el_length_def] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPECL
     [`APPEND (h1:((A,B)heap_element)list)
        [DataElement (ADDR_MAP (heap_map1 (heap3:((A,B)heap_element)list)) ys) l d]`;
      `APPEND a1 xs1:((A,B)heap_element)list`; `a3:num`; `n3:num`;
      `heap3:((A,B)heap_element)list`; `c3:bool`; `limit:num`;
      `heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
    [MATCH_MP_TAC GC1AUX_gc_inv_shift THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`h13:((A,B)heap_element)list`; `a3':num`; `n3':num`;
     `heap3':((A,B)heap_element)list`; `c3':bool`] THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBMAP_TRANS]);;

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
    [UNDISCH_TAC `roots_ok roots (heap:((A,B)heap_element)list)` THEN
     REWRITE_TAC[roots_ok_def; isSomeDataOrForward_def; reachable_addresses_def] THEN
     MESON_TAC[RTC_REFL];
     ALL_TAC] THEN
   STRIP_TAC THEN
   MP_TAC(ISPECL [`[]:((A,B)heap_element)list`; `h23:((A,B)heap_element)list`; `a3:num`;
     `n3:num`; `heap3:((A,B)heap_element)list`; `c3:bool`; `limit:num`;
     `heap:((A,B)heap_element)list`; `roots:(A heap_address)list`]
     copying_gc_gc_move_loop_thm) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`h13:((A,B)heap_element)list`; `a3':num`;
     `heap3':((A,B)heap_element)list`] THEN
   SIMP[full_gc_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `c3' /\ a3' + n3' = limit /\ a3' = heap_length (h13:((A,B)heap_element)list) /\
                 heap_length (heap3':((A,B)heap_element)list) = limit`
     STRIP_ASSUME_TAC THENL
    [MP_TAC(ASSUME `copying_gc_gc_inv (h13,[],a3',n3',heap3',c3',limit)
                      (heap:((A,B)heap_element)list) roots`) THEN
     REWRITE_TAC[copying_gc_gc_inv_def; APPEND_NIL] THEN MESON_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `n3' = limit - a3'` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `heap_length (heap:((A,B)heap_element)list) = limit` ASSUME_TAC THENL
    [ASM_MESON_TAC[heap_ok_def]; ALL_TAC] THEN
   REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_ARITH_TAC THENL
   [MATCH_MP_TAC gc_shared_ADDR_MAP_EQ THEN REWRITE_TAC[heap_map1_def] THEN
     ASM_MESON_TAC[SUBMAP_DEF];
    ASM_MESON_TAC[SUBMAP_DEF];
    SUBGOAL_THEN `limit - a3' = n3'` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `T = c3'` SUBST1_TAC THENL
    [ASM_REWRITE_TAC[]; FIRST_ASSUM ACCEPT_TAC]]);;

let GC1AUX_heap_lookup_IMP_heap_addresses_GEN = prove
 (`!xs n (x:(A,B)heap_element) j.
     heap_lookup j xs = SOME x ==> n + j IN heap_addresses n xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_addresses_def; IN_INSERT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + el_length (h:(A,B)heap_element)`; `x:(A,B)heap_element`;
                                `j - el_length (h:(A,B)heap_element)`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(n + el_length (h:(A,B)heap_element)) + (j - el_length h) = n + j`
    SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* HOL4: heap_lookup_IMP_heap_addresses (an ML-level lemma of the script) *)
let GC1AUX_heap_lookup_IMP_heap_addresses = prove
 (`!xs (x:(A,B)heap_element) j. heap_lookup j xs = SOME x ==> j IN heap_addresses 0 xs`,
  MESON_TAC[GC1AUX_heap_lookup_IMP_heap_addresses_GEN; ADD_CLAUSES]);;

let full_gc_LENGTH = prove
 (`!roots (heap:((A,B)heap_element)list) limit.
     roots_ok roots heap /\ heap_ok heap limit
     ==> ?roots2 heap2 (a2:num).
           full_gc (roots,heap,limit) = (roots2,heap2,heap_length heap2,T)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`roots:(A heap_address)list`; `heap:((A,B)heap_element)list`;
                 `limit:num`] copying_gc_full_gc_thm) THEN
  ASM_REWRITE_TAC[copying_gc_gc_inv_def; APPEND_NIL] THEN MESON_TAC[]);;

let full_gc_ok = prove
 (`!roots (heap:((A,B)heap_element)list) limit.
     roots_ok roots heap /\ heap_ok heap limit
     ==> ?roots2 heap2 a2.
           full_gc (roots,heap,limit) = (roots2,heap2,a2,T) /\
           a2 <= limit /\
           roots_ok roots2 (APPEND heap2 (heap_expand (limit - a2))) /\
           heap_ok (APPEND heap2 (heap_expand (limit - a2))) limit`,
  (REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`roots:(A heap_address)list`; `heap:((A,B)heap_element)list`;
                  `limit:num`] copying_gc_full_gc_thm) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `heap2:((A,B)heap_element)list` (X_CHOOSE_THEN `a2:num`
     (X_CHOOSE_THEN `heap3:((A,B)heap_element)list` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`ADDR_MAP (heap_map1 (heap3:((A,B)heap_element)list))
                            (roots:(A heap_address)list)`;
     `heap2:((A,B)heap_element)list`; `a2:num`] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[copying_gc_gc_inv_def; APPEND_NIL]) THEN
   SUBGOAL_THEN
     `!y. y IN FDOM (heap_map 0 (heap3:((A,B)heap_element)list))
          ==> isSomeDataElement (heap_lookup (heap_map1 heap3 y)
                                 (heap2:((A,B)heap_element)list))`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`y:num`; `heap_map1 (heap3:((A,B)heap_element)list) y`]) THEN
     ASM_REWRITE_TAC[FLOOKUP_DEF; heap_map1_def] THEN
     REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `!j. j IN heap_addresses 0 (heap2:((A,B)heap_element)list)
          ==> ?i. FLOOKUP (heap_map 0 (heap3:((A,B)heap_element)list)) i = SOME j`
     ASSUME_TAC THENL
    [MP_TAC(ASSUME `BIJ (heap_map1 (heap3:((A,B)heap_element)list))
                      (FDOM (heap_map 0 heap3))
                      (heap_addresses 0 (heap2:((A,B)heap_element)list))`) THEN
     REWRITE_TAC[BIJ; SURJ; heap_map1_def; FLOOKUP_DEF] THEN MESON_TAC[];
     ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [ASM_ARITH_TAC;
     REWRITE_TAC[roots_ok_def] THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC isSome_heap_looukp_IMP_APPEND THEN
     FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_ADDR_MAP) THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN
  (REWRITE_TAC[heap_ok_def] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN ASM_ARITH_TAC;
     ASM_SIMP_TAC[FILTER_APPEND; EVERY_isDataElement_IMP_LEMMA; APPEND] THEN
     REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
     REWRITE_TAC[FILTER; isForwardPointer_def];
     ALL_TAC] THEN
   MAP_EVERY X_GEN_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `ptr:num`; `u:A`] THEN
   REWRITE_TAC[MEM_APPEND] THEN STRIP_TAC THENL
    [ALL_TAC;
     UNDISCH_TAC `MEM (DataElement xs l d) (heap_expand (limit - a2):((A,B)heap_element)list)` THEN
     REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
     REWRITE_TAC[MEM; GSYM heap_element_distinct]] THEN
   MATCH_MP_TAC isSome_heap_looukp_IMP_APPEND THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP MEM_IMP_heap_lookup) THEN
   DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP GC1AUX_heap_lookup_IMP_heap_addresses) THEN
   DISCH_THEN(fun th -> FIRST_X_ASSUM(X_CHOOSE_TAC `i:num` o C MATCH_MP th)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_LESS o
     check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
                      fst(dest_const(fst(strip_comb(lhs(concl th))))) = "heap_lookup")) THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o
     check (fun th -> can (SPECL [`i:num`; `j:num`]) th &&
                      is_imp(snd(strip_forall(concl th))) &&
                      can (find_term ((=) `reachable_addresses:(A heap_address)list->
                            ((A,B)heap_element)list->num->bool`)) (concl th))) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[option_INJ; heap_element_11] o
     check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
                      is_const(rator(lhs(concl th))) &&
                      fst(dest_const(rator(lhs(concl th)))) = "SOME")) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
                                         fst(dest_var(lhs(concl th))) = "xs")) THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_ADDR_MAP) THEN STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[]));;

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
  (REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`roots:(A heap_address)list`; `heap:((A,B)heap_element)list`;
                  `limit:num`] copying_gc_full_gc_thm) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `heap2:((A,B)heap_element)list` (X_CHOOSE_THEN `a2:num`
     (X_CHOOSE_THEN `heap3:((A,B)heap_element)list` STRIP_ASSUME_TAC))) THEN
   MAP_EVERY EXISTS_TAC [`heap2:((A,B)heap_element)list`; `a2:num`;
     `heap_map 0 (heap3:((A,B)heap_element)list)`] THEN
   SUBGOAL_THEN `FAPPLY (heap_map 0 (heap3:((A,B)heap_element)list)) = heap_map1 heap3`
     (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[FUN_EQ_THM; heap_map1_def]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[copying_gc_gc_inv_def; APPEND_NIL]) THEN
   SUBGOAL_THEN
     `!i. i IN FDOM (heap_map 0 (heap3:((A,B)heap_element)list))
          ==> heap_map1 heap3 i < heap_length (heap2:((A,B)heap_element)list)`
     ASSUME_TAC THENL
    [MP_TAC(ASSUME `BIJ (heap_map1 (heap3:((A,B)heap_element)list))
                      (FDOM (heap_map 0 heap3))
                      (heap_addresses 0 (heap2:((A,B)heap_element)list))`) THEN
     REWRITE_TAC[BIJ; INJ] THEN
     MESON_TAC[heap_addresses_LESS_heap_length; ADD_CLAUSES];
     ALL_TAC] THEN
   SUBGOAL_THEN
     `!i. i IN FDOM (heap_map 0 (heap3:((A,B)heap_element)list))
          ==> ?xs l d.
                heap_lookup i heap = SOME (DataElement xs l d) /\
                heap_lookup (heap_map1 heap3 i) (heap2:((A,B)heap_element)list) =
                  SOME (DataElement (ADDR_MAP (heap_map1 heap3) xs) l d) /\
                reachable_addresses roots heap i /\
                (!ptr (d:A). MEM (Pointer ptr d) xs ==> ptr IN FDOM (heap_map 0 heap3))`
     ASSUME_TAC THENL
    [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `heap_map1 (heap3:((A,B)heap_element)list) i`] o
       check (fun th -> can (SPECL [`i:num`; `j:num`]) th &&
                        can (find_term ((=) `reachable_addresses:(A heap_address)list->
                              ((A,B)heap_element)list->num->bool`)) (concl th))) THEN
     ASM_SIMP_TAC[FLOOKUP_DEF; heap_map1_def] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[heap_map1_def]) THEN ASM_SIMP_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
     `!j. j IN heap_addresses 0 (heap2:((A,B)heap_element)list)
          ==> ?i. i IN FDOM (heap_map 0 (heap3:((A,B)heap_element)list)) /\
                  heap_map1 heap3 i = j`
     ASSUME_TAC THENL
    [MP_TAC(ASSUME `BIJ (heap_map1 (heap3:((A,B)heap_element)list))
                      (FDOM (heap_map 0 heap3))
                      (heap_addresses 0 (heap2:((A,B)heap_element)list))`) THEN
     REWRITE_TAC[BIJ; SURJ] THEN MESON_TAC[];
     ALL_TAC]) THEN
  (REPEAT CONJ_TAC THENL
    [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:num` THEN
     CONV_TAC(RAND_CONV(REWRITE_CONV[IN])) THEN EQ_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN
       `!a b. RTC (gc_edge (heap:((A,B)heap_element)list)) a b
              ==> a IN FDOM (heap_map 0 (heap3:((A,B)heap_element)list))
              ==> b IN FDOM (heap_map 0 heap3)`
       ASSUME_TAC THENL
      [MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
        [REWRITE_TAC[gc_edge_def] THEN REPEAT STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o
           check (fun th -> can (find_term ((=) `ADDR_MAP:(num->num)->(A heap_address)list->
                                   (A heap_address)list`)) (concl th) &&
                            is_forall(concl th) && not(is_forall(snd(dest_forall(concl th)))))) THEN
         ASM_REWRITE_TAC[option_INJ; heap_element_11] THEN ASM_MESON_TAC[];
         MESON_TAC[]];
       ALL_TAC] THEN
     REWRITE_TAC[reachable_addresses_def] THEN ASM_MESON_TAC[];
     (REWRITE_TAC[EXTENSION; FRANGE_DEF; IN_ELIM_THM; GC1AUX_FAPPLY_heap_map] THEN
   X_GEN_TAC `y:num` THEN EQ_TAC THENL
    [REWRITE_TAC[isSomeDataElement_def] THEN ASM_MESON_TAC[];
     REWRITE_TAC[isSomeDataElement_def] THEN
     ASM_MESON_TAC[GC1AUX_heap_lookup_IMP_heap_addresses]]);
     (GEN_REWRITE_TAC LAND_CONV [GSYM heap_length_heap_filter] THEN
   MATCH_MP_TAC heap_length_heap_filter_eq THEN
   EXISTS_TAC `heap_map1 (heap3:((A,B)heap_element)list)` THEN
   ASM_REWRITE_TAC[FDOM_FINITE; FINITE_heap_addresses] THEN ASM_MESON_TAC[]);
     (REWRITE_TAC[gc_related_def; GC1AUX_FAPPLY_heap_map] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[INJ; IN_ELIM_THM] THEN CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC isSome_heap_looukp_IMP_APPEND THEN
       REWRITE_TAC[isSomeDataElement_def] THEN ASM_MESON_TAC[];
       MP_TAC(ASSUME `BIJ (heap_map1 (heap3:((A,B)heap_element)list))
                       (FDOM (heap_map 0 heap3))
                       (heap_addresses 0 (heap2:((A,B)heap_element)list))`) THEN
       REWRITE_TAC[BIJ; INJ] THEN MESON_TAC[]];
     REWRITE_TAC[isSomeDataElement_def] THEN ASM_MESON_TAC[];
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
       check (fun th -> can (find_term ((=) `ADDR_MAP:(num->num)->(A heap_address)list->
                               (A heap_address)list`)) (concl th) &&
                        is_forall(concl th) && not(is_forall(snd(dest_forall(concl th)))))) THEN
     ASM_REWRITE_TAC[option_INJ; heap_element_11] THEN STRIP_TAC THEN
     REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
       let l,r = dest_eq(concl th) in is_var l && is_var r))) THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC gc_shared_heap_lookup_EXTEND THEN FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM ACCEPT_TAC]]);
     ASM_REWRITE_TAC[]]));;

(* Lemmas about ok and a *)

let copying_gc_gc_move_ok = prove
 (`!(x:A heap_address) h2 a n (heap:((A,B)heap_element)list) c limit x' h2' a' n' heap' b.
     copying_gc_gc_move (x,h2,a,n,heap,c,limit) = (x',h2',a',n',heap',T)
     ==> c /\ (a = b + heap_length h2 ==> a' = b + heap_length h2')`,
  (REPEAT GEN_TAC THEN CASES_ON `x:A heap_address` THEN
   REWRITE_TAC[copying_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN
   EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN SIMP_NOASM[]) THEN
  (STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP gc_shared_gc_forward_ptr_ok o
     REWRITE_RULE[ASSUME `y:bool`] o
     check (fun th -> is_eq(concl th) && is_pair(rhs(concl th)))) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
     check (fun th -> is_eq(concl th) && is_var(rhs(concl th))))) THEN
   REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL;
               el_length_def] THEN ARITH_TAC));;

let copying_gc_gc_move_list_ok = prove
 (`!xs h2 a n (heap:((A,B)heap_element)list) c limit xs' h2' a' n' heap' (c':bool) b.
     copying_gc_gc_move_list (xs:(A heap_address)list,h2,a,n,heap,c,limit) =
       (xs',h2',a',n',heap',T)
     ==> c /\ (a = b + heap_length h2 ==> a' = b + heap_length h2')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[copying_gc_gc_move_list_def; PAIR_EQ] THENL
    [MESON_TAC[]; ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   MP_TAC(ISPEC `copying_gc_gc_move (h:A heap_address,h2:((A,B)heap_element)list,
                                     a,n,heap,c,limit)` GC1AUX_PAIR6) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`x1:A heap_address`; `h21:((A,B)heap_element)list`; `a1:num`;
     `n1:num`; `heap1:((A,B)heap_element)list`; `c1:bool`] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
   MP_TAC(ISPEC `copying_gc_gc_move_list (t:(A heap_address)list,h21:((A,B)heap_element)list,
                                          a1,n1,heap1,c1,limit)` GC1AUX_PAIR6) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`xs2:(A heap_address)list`; `h22:((A,B)heap_element)list`; `a2:num`;
     `n2:num`; `heap2:((A,B)heap_element)list`; `c2:bool`] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`h21:((A,B)heap_element)list`; `a1:num`; `n1:num`;
     `heap1:((A,B)heap_element)list`; `c1:bool`; `limit:num`; `xs2:(A heap_address)list`;
     `h22:((A,B)heap_element)list`; `a2:num`; `n2:num`; `heap2:((A,B)heap_element)list`;
     `c2:bool`; `b:num`]) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`h:A heap_address`; `h2:((A,B)heap_element)list`; `a:num`; `n:num`;
     `heap:((A,B)heap_element)list`; `c:bool`; `limit:num`; `x1:A heap_address`;
     `h21:((A,B)heap_element)list`; `a1:num`; `n1:num`; `heap1:((A,B)heap_element)list`;
     `b:num`] copying_gc_gc_move_ok) THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 proves gc_move_loop_ok by gc_move_loop_ind on an ML-level lemma *)
let copying_gc_gc_move_loop_ok = prove
 (`!h1 h2 a n (heap:((A,B)heap_element)list) c limit h1' a' n' heap'.
     copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T) ==> c`,
  (MP_TAC(ISPEC `\p:((A,B)heap_element)list#((A,B)heap_element)list#num#num#
                    ((A,B)heap_element)list#bool#num.
                    !h1' a' n' heap'.
                      copying_gc_gc_move_loop p = (h1',a',n',heap',T)
                      ==> FST(SND(SND(SND(SND(SND p)))))` copying_gc_gc_move_loop_ind) THEN
   REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [REWRITE_TAC[copying_gc_gc_move_loop_def; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[copying_gc_gc_move_loop_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   CASES_ON `h:(A,B)heap_element` THEN SIMP_NOASM[PAIR_EQ]) THEN
  (MP_TAC(ISPEC `copying_gc_gc_move_list (a0:(A heap_address)list,
                   CONS (DataElement a0 a1 (a2:B)) h2,a,n,heap,c,limit)` GC1AUX_PAIR6) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`y1:(A heap_address)list`; `y2:((A,B)heap_element)list`; `y3:num`;
     `y4:num`; `y5:((A,B)heap_element)list`; `y6:bool`] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A heap_address)list`; `a1:num`; `a2:B`;
     `y1:(A heap_address)list`; `y2:((A,B)heap_element)list`; `y3:num`; `y4:num`;
     `y5:((A,B)heap_element)list`; `y6:bool`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`h1':((A,B)heap_element)list`; `a':num`; `n':num`;
     `heap':((A,B)heap_element)list`]) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   MP_TAC(ISPECL [`a0:(A heap_address)list`;
     `CONS (DataElement a0 a1 (a2:B)) h2:((A,B)heap_element)list`; `a:num`; `n:num`;
     `heap:((A,B)heap_element)list`; `c:bool`; `limit:num`; `y1:(A heap_address)list`;
     `y2:((A,B)heap_element)list`; `y3:num`; `y4:num`; `y5:((A,B)heap_element)list`;
     `y6:bool`; `0`] copying_gc_gc_move_list_ok) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[]));;

let gc_move_list_IMP_LENGTH = prove
 (`!l5 h a n (heap:((A,B)heap_element)list) c k xs ys a1 xs1 heap1 c1.
     copying_gc_gc_move_list (l5:(A heap_address)list,h,a,n,heap,c,k) =
       (xs,ys,a1,xs1,heap1,c1)
     ==> LENGTH xs = LENGTH l5`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[copying_gc_gc_move_list_def; PAIR_EQ] THENL
   [MESON_TAC[LENGTH]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hh:((A,B)heap_element)list`; `a:num`; `n:num`;
    `heap:((A,B)heap_element)list`; `c:bool`; `k:num`] THEN
  MP_TAC(ISPEC `copying_gc_gc_move (h:A heap_address,hh:((A,B)heap_element)list,
                                    a,n,heap,c,k)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x2:A heap_address`; `h2:((A,B)heap_element)list`; `a2:num`;
    `n2:num`; `heap2:((A,B)heap_element)list`; `c2:bool`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (t:(A heap_address)list,h2:((A,B)heap_element)list,
                                         a2,n2,heap2,c2,k)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`xs3:(A heap_address)list`; `h3:((A,B)heap_element)list`; `a3:num`;
    `n3:num`; `heap3:((A,B)heap_element)list`; `c3:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  REWRITE_TAC[LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]);;

let GC1AUX_PAIR5 = prove
 (`!p:A#B#C#D#E. ?x1 x2 x3 x4 x5. p = (x1,x2,x3,x4,x5)`,
  GEN_TAC THEN
  MAP_EVERY EXISTS_TAC [`FST(p:A#B#C#D#E)`; `FST(SND(p:A#B#C#D#E))`;
    `FST(SND(SND(p:A#B#C#D#E)))`; `FST(SND(SND(SND(p:A#B#C#D#E))))`;
    `SND(SND(SND(SND(p:A#B#C#D#E))))`] THEN
  REWRITE_TAC[PAIR]);;

let full_gc_IMP_LENGTH = prove
 (`!(xs:(A heap_address)list) (heap:((A,B)heap_element)list) limit roots2 heap2 h.
     full_gc (xs,heap,limit) = (roots2,heap2,h,T) ==> LENGTH roots2 = LENGTH xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_gc_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (xs:(A heap_address)list,[]:((A,B)heap_element)list,
                  0,limit,heap,T,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:(A heap_address)list`; `h1:((A,B)heap_element)list`; `a1:num`;
    `n1:num`; `heap1:((A,B)heap_element)list`; `c1:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_loop ([]:((A,B)heap_element)list,h1,a1,n1,heap1,c1,limit)`
           GC1AUX_PAIR5) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  ASM_MESON_TAC[gc_move_list_IMP_LENGTH]);;

let gc_move_IMP_isDataElement = prove
 (`!l5 h a n (heap:((A,B)heap_element)list) c k xs ys a1 xs1 heap1 c1.
     ALL isDataElement h /\
     copying_gc_gc_move (l5:A heap_address,h,a,n,heap,c,k) = (xs,ys,a1,xs1,heap1,c1)
     ==> ALL isDataElement ys`,
  REPEAT GEN_TAC THEN CASES_ON `l5:A heap_address` THEN
  REWRITE_TAC[copying_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && is_var(rhs(concl th))))) THEN
  ASM_REWRITE_TAC[ALL_APPEND; ALL; GC1AUX_isDataElement_DataElement]);;

let gc_move_list_IMP_isDataElement = prove
 (`!l5 h a n (heap:((A,B)heap_element)list) c k xs ys a1 xs1 heap1 c1.
     ALL isDataElement h /\
     copying_gc_gc_move_list (l5:(A heap_address)list,h,a,n,heap,c,k) =
       (xs,ys,a1,xs1,heap1,c1)
     ==> ALL isDataElement ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[copying_gc_gc_move_list_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hh:((A,B)heap_element)list`; `a:num`; `n:num`;
    `heap:((A,B)heap_element)list`; `c:bool`; `k:num`] THEN
  MP_TAC(ISPEC `copying_gc_gc_move (h:A heap_address,hh:((A,B)heap_element)list,
                                    a,n,heap,c,k)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x2:A heap_address`; `h2:((A,B)heap_element)list`; `a2:num`;
    `n2:num`; `heap2:((A,B)heap_element)list`; `c2:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (t:(A heap_address)list,h2:((A,B)heap_element)list,
                                         a2,n2,heap2,c2,k)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`xs3:(A heap_address)list`; `h3:((A,B)heap_element)list`; `a3:num`;
    `n3:num`; `heap3:((A,B)heap_element)list`; `c3:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "ys")) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h2:((A,B)heap_element)list`; `a2:num`; `n2:num`;
    `heap2:((A,B)heap_element)list`; `c2:bool`; `k:num`; `xs3:(A heap_address)list`;
    `a3:num`; `n3:num`; `heap3:((A,B)heap_element)list`; `c3:bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC gc_move_IMP_isDataElement THEN
  MAP_EVERY EXISTS_TAC [`h:A heap_address`; `hh:((A,B)heap_element)list`; `a:num`;
    `n:num`; `heap:((A,B)heap_element)list`; `c:bool`; `k:num`; `x2:A heap_address`;
    `a2:num`; `n2:num`; `heap2:((A,B)heap_element)list`; `c2:bool`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 proves gc_move_loop_IMP_isDataElement by recInduct gc_move_loop_ind *)
let gc_move_loop_IMP_isDataElement = prove
 (`!h1 h2 a n (heap:((A,B)heap_element)list) c limit h1' a' n' heap' (c':bool).
     ALL isDataElement h1 /\ ALL isDataElement h2 /\
     copying_gc_gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T)
     ==> ALL isDataElement h1'`,
  (MP_TAC(ISPEC `\p:((A,B)heap_element)list#((A,B)heap_element)list#num#num#
                    ((A,B)heap_element)list#bool#num.
                    !h1' a' n' heap' (c':bool).
                      ALL isDataElement (FST p) /\ ALL isDataElement (FST(SND p)) /\
                      copying_gc_gc_move_loop p = (h1',a',n',heap',T)
                      ==> ALL isDataElement h1'` copying_gc_gc_move_loop_ind) THEN
   REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [REWRITE_TAC[copying_gc_gc_move_loop_def; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[copying_gc_gc_move_loop_def] THEN
   COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   CASES_ON `h:(A,B)heap_element` THEN SIMP_NOASM[PAIR_EQ] THEN
   MP_TAC(ISPEC `copying_gc_gc_move_list (a0:(A heap_address)list,
                   CONS (DataElement a0 a1 (a2:B)) h2,a,n,heap,c,limit)` GC1AUX_PAIR6) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`y1:(A heap_address)list`; `y2:((A,B)heap_element)list`; `y3:num`;
     `y4:num`; `y5:((A,B)heap_element)list`; `y6:bool`] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP copying_gc_gc_move_loop_ok) THEN
   SUBGOAL_THEN `ALL isDataElement (y2:((A,B)heap_element)list)` ASSUME_TAC THENL
    [MATCH_MP_TAC gc_move_list_IMP_isDataElement THEN
     MAP_EVERY EXISTS_TAC [`a0:(A heap_address)list`;
       `CONS (DataElement a0 a1 (a2:B)) h2:((A,B)heap_element)list`; `a:num`; `n:num`;
       `heap:((A,B)heap_element)list`; `c:bool`; `limit:num`; `y1:(A heap_address)list`;
       `y3:num`; `y4:num`; `y5:((A,B)heap_element)list`; `y6:bool`] THEN
     ASM_REWRITE_TAC[ALL; GC1AUX_isDataElement_DataElement];
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A heap_address)list`; `a1:num`; `a2:B`;
     `y1:(A heap_address)list`; `y2:((A,B)heap_element)list`; `y3:num`; `y4:num`;
     `y5:((A,B)heap_element)list`; `y6:bool`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`h1':((A,B)heap_element)list`; `a':num`; `n':num`;
     `heap':((A,B)heap_element)list`]) THEN
   ASM_REWRITE_TAC[ALL_APPEND; ALL; GC1AUX_isDataElement_DataElement] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   UNDISCH_TAC `ALL isDataElement (y2:((A,B)heap_element)list)` THEN
   UNDISCH_TAC `~(y2:((A,B)heap_element)list = [])` THEN
   SPEC_TAC(`y2:((A,B)heap_element)list`,`y2:((A,B)heap_element)list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; TL; NOT_CONS_NIL] THEN MESON_TAC[]));;

let full_gc_IMP_isDataElement = prove
 (`!(roots:(A heap_address)list) (heap:((A,B)heap_element)list) limit roots1 heap1 a.
     full_gc (roots,heap,limit) = (roots1,heap1,a,T) ==> ALL isDataElement heap1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[full_gc_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_list (roots:(A heap_address)list,
                  []:((A,B)heap_element)list,0,limit,heap,T,limit)` GC1AUX_PAIR6) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:(A heap_address)list`; `h1:((A,B)heap_element)list`; `a1:num`;
    `n1:num`; `heap2:((A,B)heap_element)list`; `c1:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  MP_TAC(ISPEC `copying_gc_gc_move_loop ([]:((A,B)heap_element)list,h1,a1,n1,heap2,c1,limit)`
           GC1AUX_PAIR5) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z1:((A,B)heap_element)list`; `z2:num`; `z3:num`;
    `z4:((A,B)heap_element)list`; `z5:bool`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(rhs(concl th)) && fst(dest_var(rhs(concl th))) = "heap1")) THEN
  MATCH_MP_TAC gc_move_loop_IMP_isDataElement THEN
  MAP_EVERY EXISTS_TAC [`[]:((A,B)heap_element)list`; `h1:((A,B)heap_element)list`;
    `a1:num`; `n1:num`; `heap2:((A,B)heap_element)list`; `c1:bool`; `limit:num`;
    `z2:num`; `z3:num`; `z4:((A,B)heap_element)list`] THEN
  REWRITE_TAC[ALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC gc_move_list_IMP_isDataElement THEN
    MAP_EVERY EXISTS_TAC [`roots:(A heap_address)list`; `[]:((A,B)heap_element)list`;
      `0`; `limit:num`; `heap:((A,B)heap_element)list`; `T`; `limit:num`;
      `r1:(A heap_address)list`; `a1:num`; `n1:num`; `heap2:((A,B)heap_element)list`;
      `c1:bool`] THEN
    ASM_REWRITE_TAC[ALL];
    ASM_REWRITE_TAC[]]);;
