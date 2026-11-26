(* ========================================================================= *)
(* gen_gc: port of HOL4 compiler/backend/gc/gen_gcScript.sml (CakeML v3479). *)
(* The major collection of the generational copying garbage collector.      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;

(* Copying GC which moves references to the end of the heap.  This         *)
(* implementation is a pre-stage to the generational GC.                    *)

let gen_gc_conf_FIELDS = cake_record "gen_gc_conf"
  ["limit","num"; "isRef","A->bool"];;

let gen_gc_gc_move_def = cake_def
  `(gen_gc_gc_move (conf:B gen_gc_conf) (state:(A,B)gc_state) (gc_shared_Data d) =
      (gc_shared_Data d,state)) /\
   (gen_gc_gc_move conf state (Pointer ptr d) =
      match heap_lookup ptr (gc_state_heap state) with
        SOME (ForwardPointer ptr _ l) -> (Pointer ptr d,state)
      | SOME (DataElement xs l dd) ->
          (let ok = (gc_state_ok state /\ l + 1 <= gc_state_n state) in
           let n = gc_state_n state - (l + 1) in
           if gen_gc_conf_isRef conf dd then
             (let r4 = CONS (DataElement xs l dd) (gc_state_r4 state) in
              match gc_forward_ptr ptr (gc_state_heap state) (gc_state_a state + n) d ok
              with (heap,ok) ->
                (Pointer (gc_state_a state + n) d,
                 gc_state_ok_fupd (combin_K ok) (gc_state_heap_fupd (combin_K heap)
                   (gc_state_n_fupd (combin_K n) (gc_state_r4_fupd (combin_K r4) state)))))
           else
             (let h2 = APPEND (gc_state_h2 state) [DataElement xs l dd] in
              match gc_forward_ptr ptr (gc_state_heap state) (gc_state_a state) d ok
              with (heap,ok) ->
                (let a = gc_state_a state + l + 1 in
                 (Pointer (gc_state_a state) d,
                  gc_state_ok_fupd (combin_K ok) (gc_state_heap_fupd (combin_K heap)
                    (gc_state_a_fupd (combin_K a) (gc_state_n_fupd (combin_K n)
                      (gc_state_h2_fupd (combin_K h2) state))))))))
      | _ -> (Pointer ptr d,gc_state_ok_fupd (combin_K F) state))`;;

(* the prefix and suffix facts that the HOL4 proofs get from IS_SUFFIX_compute *)
let GC2AUX_PREFIX_SUFFIX = prove
 (`(!l:A list. IS_PREFIX l l) /\ (!(l:A list) x. IS_PREFIX (APPEND l x) l) /\
   (!l:A list. IS_SUFFIX l l) /\ (!(l:A list) x. IS_SUFFIX (CONS x l) l)`,
  REWRITE_TAC[IS_PREFIX_DEF; IS_PREFIX_APPEND; IS_SUFFIX_APPEND] THEN
  MESON_TAC[APPEND_NIL; APPEND]);;

let gen_gc_gc_move_IMP = prove
 (`!x x' (state:(A,B)gc_state) state' (conf:B gen_gc_conf).
     gen_gc_gc_move conf state x = (x',state')
     ==> gc_state_h1 state = gc_state_h1 state' /\
         gc_state_r3 state = gc_state_r3 state' /\
         gc_state_r2 state = gc_state_r2 state' /\
         gc_state_r1 state = gc_state_r1 state' /\
         IS_PREFIX (gc_state_h2 state') (gc_state_h2 state) /\
         IS_SUFFIX (gc_state_r4 state') (gc_state_r4 state)`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN
  RW[GC2AUX_PREFIX_SUFFIX]);;

let gen_gc_gc_move_list_def = cake_def
  `(gen_gc_gc_move_list (conf:B gen_gc_conf) (state:(A,B)gc_state) [] = ([],state)) /\
   (gen_gc_gc_move_list conf state (CONS x xs) =
      match gen_gc_gc_move conf state x with
        (x,state) ->
          (match gen_gc_gc_move_list conf state xs with
             (xs,state) -> (CONS x xs,state)))`;;

let GC2AUX_IS_PREFIX_TRANS = prove
 (`!a b c:A list. IS_PREFIX a b /\ IS_PREFIX b c ==> IS_PREFIX a c`,
  REWRITE_TAC[IS_PREFIX_DEF] THEN MESON_TAC[IS_PREFIX_TRANS]);;

let gen_gc_gc_move_list_IMP = prove
 (`!xs xs' (state:(A,B)gc_state) state' (conf:B gen_gc_conf).
     gen_gc_gc_move_list conf state xs = (xs',state')
     ==> gc_state_h1 state = gc_state_h1 state' /\
         gc_state_r3 state = gc_state_r3 state' /\
         gc_state_r2 state = gc_state_r2 state' /\
         gc_state_r1 state = gc_state_r1 state' /\
         IS_PREFIX (gc_state_h2 state') (gc_state_h2 state) /\
         IS_SUFFIX (gc_state_r4 state') (gc_state_r4 state)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def; PAIR_EQ] THENL
   [MESON_TAC[GC2AUX_PREFIX_SUFFIX]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_move_IMP) THEN
  (* the induction hypothesis applied to the moves of the tail *)
  FIRST_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  ASM_MESON_TAC[GC2AUX_IS_PREFIX_TRANS; IS_SUFFIX_TRANS]);;

(* MATCH_MP with an equation in either orientation (the termination contexts *)
(* of the kit state a tuple let as f x = (a,b))                              *)
let GC2AUX_MATCH_MP_EITHER (lemma:thm) (th:thm) : thm =
  try MATCH_MP lemma th with Failure _ -> MATCH_MP lemma (SYM th);;

let gen_gc_gc_move_data_def = cake_def_wf
  `MEASURE (\(conf:B gen_gc_conf,state:(A,B)gc_state).
              gen_gc_conf_limit conf - heap_length (gc_state_h1 state))`
  (REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GC2AUX_MATCH_MP_EITHER gen_gc_gc_move_list_IMP) THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS;
                               el_length_def]) THEN
   SIMP[measure_THM; heap_length_APPEND; GC1AUX_heap_length_CONS;
        heap_length_NIL; el_length_def] THEN
   ASM_ARITH_TAC)
  `gen_gc_gc_move_data (conf:B gen_gc_conf) (state:(A,B)gc_state) =
     match gc_state_h2 state with
       [] -> state
     | CONS h h2 ->
         if gen_gc_conf_limit conf < heap_length (APPEND (gc_state_h1 state) (CONS h h2))
         then gc_state_ok_fupd (combin_K F) state else
         (match h with
            DataElement xs l d ->
              (match gen_gc_gc_move_list conf state xs with
                 (xs,state) ->
                   let h1 = APPEND (gc_state_h1 state) [DataElement xs l d] in
                   let h2 = TL (gc_state_h2 state) in
                   let ok = (gc_state_ok state /\ ~(gc_state_h2 state = []) /\
                             HD (gc_state_h2 state) = h) in
                   gen_gc_gc_move_data conf
                     (gc_state_ok_fupd (combin_K ok) (gc_state_h2_fupd (combin_K h2)
                       (gc_state_h1_fupd (combin_K h1) state))))
          | _ -> gc_state_ok_fupd (combin_K F) state)`;;

let gen_gc_gc_move_data_ind = cake_ind "gen_gc_gc_move_data";;

let gc_move_refs_def = cake_def_wf
  `MEASURE (\(conf:B gen_gc_conf,state:(A,B)gc_state). heap_length (gc_state_r2 state))`
  (REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[measure_THM] THEN
   FIRST_X_ASSUM(fun th ->
     let l,r = dest_eq (concl th) in
     let isr2 t = is_comb t &&
       rator t = `gc_state_r2:(A,B)gc_state->((A,B)heap_element)list` in
     if isr2 r then SUBST1_TAC (SYM th) else
     if isr2 l then SUBST1_TAC th else failwith "GC2AUX: no r2 equation") THEN
   SIMP[GC1AUX_heap_length_CONS; el_length_def] THEN ARITH_TAC)
  `gc_move_refs (conf:B gen_gc_conf) (state:(A,B)gc_state) =
     match gc_state_r2 state with
       [] -> gc_state_r1_fupd (combin_K (APPEND (gc_state_r3 state) (gc_state_r1 state)))
               (gc_state_r3_fupd (combin_K []) state)
     | CONS ref r2 ->
         (match ref with
            DataElement xs l d ->
              (match gen_gc_gc_move_list conf state xs with
                 (xs,state) ->
                   let r3 = APPEND (gc_state_r3 state) [DataElement xs l d] in
                   gc_move_refs conf
                     (gc_state_r3_fupd (combin_K r3) (gc_state_r2_fupd (combin_K r2) state)))
          | _ -> gc_state_ok_fupd (combin_K F) state)`;;

let gc_move_refs_ind = cake_ind "gc_move_refs";;

(* The main gc loop.  Runs a clock to simplify the termination argument. *)
let gen_gc_gc_move_loop_def = cake_def
  `gen_gc_gc_move_loop (conf:B gen_gc_conf) (state:(A,B)gc_state) (clock:num) =
     match gc_state_r4 state with
       [] ->
         (match gc_state_h2 state with
            [] -> state
          | CONS h h2 ->
              (let state = gen_gc_gc_move_data conf state in
               if clock = 0 then gc_state_ok_fupd (combin_K F) state
               else gen_gc_gc_move_loop conf state (clock - 1)))
     | CONS h r4 ->
         (let state = gc_move_refs conf
                        (gc_state_r4_fupd (combin_K [])
                           (gc_state_r2_fupd (combin_K (gc_state_r4 state)) state)) in
          if clock = 0 then gc_state_ok_fupd (combin_K F) state
          else gen_gc_gc_move_loop conf state (clock - 1))`;;

let gen_gc_gc_move_loop_ind = cake_ind "gen_gc_gc_move_loop";;

let gen_gc_def = cake_def
  `gen_gc (conf:B gen_gc_conf) (roots:(A heap_address)list,heap:((A,B)heap_element)list) =
     let state = gc_state_ok_fupd (combin_K (heap_length heap = gen_gc_conf_limit conf))
                   (gc_state_n_fupd (combin_K (gen_gc_conf_limit conf))
                     (gc_state_heap_fupd (combin_K heap) empty_state)) in
     match gen_gc_gc_move_list conf state roots with
       (roots,state) ->
         (let state = gen_gc_gc_move_loop conf state (gen_gc_conf_limit conf) in
          (roots,state))`;;

(* Do we point to something that is fully processed?  I.e. all children *)
(* are also copied.                                                      *)
let is_final_def = cake_def
  `is_final (conf:B gen_gc_conf) (state:(A,B)gc_state) ptr <=>
     let h1end = heap_length (gc_state_h1 state) in
     let r3start = gc_state_a state + gc_state_n state + heap_length (gc_state_r4 state) in
     let r3end = r3start + heap_length (gc_state_r3 state) in
     let r1start = r3end + heap_length (gc_state_r2 state) in
     ptr < h1end \/ r1start <= ptr \/ (r3start <= ptr /\ ptr < r3end)`;;

let gen_gc_gc_inv_def = cake_def
  `gen_gc_gc_inv (conf:B gen_gc_conf) (state:(A,B)gc_state)
                 (heap0:((A,B)heap_element)list) (roots0:(A heap_address)list) <=>
     let heap' = APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
                   (gc_state_h1 state) (gc_state_h2 state))
                   (heap_expand (gc_state_n state))) (gc_state_r4 state))
                   (gc_state_r3 state)) (gc_state_r2 state)) (gc_state_r1 state) in
     heap_length (APPEND (gc_state_h1 state) (gc_state_h2 state)) = gc_state_a state /\
     gc_state_a state + gc_state_n state +
       heap_length (APPEND (APPEND (APPEND (gc_state_r4 state) (gc_state_r3 state))
                      (gc_state_r2 state)) (gc_state_r1 state)) = gen_gc_conf_limit conf /\
     heap_length (FILTER (\h. ~isForwardPointer h) (gc_state_heap state)) = gc_state_n state /\
     heap_length (gc_state_heap state) = gen_gc_conf_limit conf /\
     gc_state_ok state /\
     heap_ok heap0 (gen_gc_conf_limit conf) /\
     heaps_similar heap0 (gc_state_heap state) /\
     ALL isDataElement (gc_state_h1 state) /\ ALL isDataElement (gc_state_h2 state) /\
     ALL isDataElement (gc_state_r1 state) /\ ALL isDataElement (gc_state_r2 state) /\
     ALL isDataElement (gc_state_r3 state) /\ ALL isDataElement (gc_state_r4 state) /\
     (!x l d. MEM (DataElement x l d)
                (APPEND (APPEND (APPEND (gc_state_r4 state) (gc_state_r3 state))
                   (gc_state_r2 state)) (gc_state_r1 state))
              ==> gen_gc_conf_isRef conf d) /\
     BIJ (heap_map1 (gc_state_heap state)) (FDOM (heap_map 0 (gc_state_heap state)))
       (heap_addresses 0 (APPEND (gc_state_h1 state) (gc_state_h2 state)) UNION
        heap_addresses (gc_state_a state + gc_state_n state)
          (APPEND (APPEND (APPEND (gc_state_r4 state) (gc_state_r3 state))
             (gc_state_r2 state)) (gc_state_r1 state))) /\
     !i j.
       FLOOKUP (heap_map 0 (gc_state_heap state)) i = SOME j
       ==> ?xs l d.
             heap_lookup i heap0 = SOME (DataElement xs l d) /\
             heap_lookup j heap' =
               SOME (DataElement
                       (if is_final conf state j
                        then ADDR_MAP (heap_map1 (gc_state_heap state)) xs
                        else xs) l d) /\
             reachable_addresses roots0 heap0 i /\
             !ptr (d:A). MEM (Pointer ptr d) xs /\ is_final conf state j
                         ==> ptr IN FDOM (heap_map 0 (gc_state_heap state))`;;
let heap_map_ForwardPointer_lemma = prove
 (`!ptr ha (a:A) l hb (ys:(A heap_address)list) (d:B).
     heap_map 0 (APPEND ha (CONS (ForwardPointer ptr a l) hb)) =
     heap_map 0 (APPEND ha (CONS (DataElement ys l d) hb)) |+ (heap_length ha,ptr)`,
  REWRITE_TAC[heap_map_APPEND; heap_map_def; el_length_def; ADD_CLAUSES;
              FUNION_FUPDATE_2; FDOM_heap_map]);;

let gen_gc_isSomeDataOrForward_lemma = prove
 (`!ha ptr (ys:(A heap_address)list) l (d:B) hb (a:num) (u:A).
     isSomeDataOrForward (heap_lookup ptr (APPEND ha (CONS (DataElement ys l d) hb))) <=>
     isSomeDataOrForward (heap_lookup ptr (APPEND ha (CONS (ForwardPointer a u l) hb)))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; heap_lookup_def] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FS[isSomeDataOrForward_def; isSomeForwardPointer_def; isSomeDataElement_def;
     el_length_def]);;

(* HOL4: isSomeDataOrForward_lemma_expanded (an ML-level value) *)
let GC2AUX_isSomeDataOrForward_lemma_expanded =
  REWRITE_RULE[isSomeDataOrForward_def; isSomeDataElement_def; isSomeForwardPointer_def]
    gen_gc_isSomeDataOrForward_lemma;;

let NOT_IN_heap_addresses = prove
 (`!xs n. ~(n + heap_length xs IN heap_addresses n (xs:((A,B)heap_element)list))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_addresses_def; NOT_IN_EMPTY; IN_INSERT; GC1AUX_heap_length_CONS] THEN
  GEN_TAC THEN GC1AUX_EL_LENGTH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + el_length (h:(A,B)heap_element)`) THEN
  REWRITE_TAC[ADD_ASSOC] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NOT_IN_heap_addresses_less = prove
 (`!xs m n. m < n ==> ~(m IN heap_addresses n (xs:((A,B)heap_element)list))`,
  MESON_TAC[heap_addresses_LESS; NOT_LE]);;

let NOT_IN_heap_addresses_gt = prove
 (`!xs (m:num) (n:num) p.
     heap_length xs + p <= m ==> ~(m IN heap_addresses p (xs:((A,B)heap_element)list))`,
  MESON_TAC[heap_addresses_LESS_heap_length; ADD_SYM; NOT_LE]);;

let heap_length_CONS = prove
 (`!(x:(A,B)heap_element) xs. heap_length (CONS x xs) = el_length x + heap_length xs`,
  REWRITE_TAC[heap_length_def; MAP; SUM]);;

let heap_lookup_LENGTH = prove
 (`!xs (x:(A,B)heap_element) ys l.
     heap_length xs = l ==> heap_lookup l (APPEND xs (CONS x ys)) = SOME x`,
  MESON_TAC[heap_lookup_PREFIX]);;

let gen_gc_heap_lookup_APPEND = prove
 (`!j xs ys:((A,B)heap_element)list.
     heap_lookup j (APPEND xs ys) =
     if j < heap_length xs then heap_lookup j xs
     else heap_lookup (j - heap_length xs) ys`,
  MESON_TAC[gc_shared_LESS_IMP_heap_lookup; NOT_LESS_IMP_heap_lookup]);;

let IMP_if_equal = prove
 (`!b1 b2 (x1:A) x2 y1 y2.
     (b1 = b2) /\ (b1 ==> x1 = x2) /\ (~b1 ==> y1 = y2)
     ==> (if b1 then x1 else y1) = (if b2 then x2 else y2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b1:bool` THEN REWRITE_TAC[] THEN MESON_TAC[]);;

let gen_gc_heap_length_heap_expand = prove
 (`!l. heap_length (heap_expand l:((A,B)heap_element)list) = l`,
  REWRITE_TAC[gc_shared_heap_length_heap_expand]);;

let gen_gc_ADDR_MAP_EQ = prove
 (`!xs (f:num->num) g.
     (!p (d:A). MEM (Pointer p d) xs ==> f p = g p) ==> ADDR_MAP f xs = ADDR_MAP g xs`,
  REWRITE_TAC[gc_shared_ADDR_MAP_EQ]);;

(* HOL4: heaps_similar_lemma (local; HOL4 binds l twice, !ha heap0 hb ptr ys *)
(* l d a l, and the inner one counts).  HOL4 reuses the name for a later    *)
(* exported theorem, so this one gets a helper name.                         *)
let GC2AUX_heaps_similar_lemma_local = prove
 (`!ha heap0 hb ptr (ys:(A heap_address)list) (d:B) (a:A) l.
     heaps_similar heap0 (APPEND (APPEND ha [DataElement ys l d]) hb)
     ==> heaps_similar heap0 (APPEND (APPEND ha [ForwardPointer ptr a l]) hb)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[heaps_similar_def; GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[LIST_REL_SPLIT2] THEN
  REWRITE_TAC[LIST_REL_CONS2; isForwardPointer_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`ys1:((A,B)heap_element)list`;
    `CONS (DataElement ys l d) t':((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
    [`DataElement ys l d:(A,B)heap_element`; `t':((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[el_length_def; isDataElement_def] THEN MESON_TAC[]);;

(* helpers for gc_move_thm: the heap lookup frame, the BIJ and FLOOKUP parts *)
(* of gc_inv after one more element is forwarded                            *)

let GC2AUX_heap_lookup_heap_expand = prove
 (`!n j (xs:(A heap_address)list) l (d:B).
     ~(heap_lookup j (heap_expand n) = SOME (DataElement xs l d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[heap_lookup_def; option_DISTINCT] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; heap_element_distinct]);;

let GC2AUX_heap_lookup_frame = prove
 (`!L M R n j (xs:(A heap_address)list) l (d:B).
     heap_lookup j (APPEND L (APPEND (heap_expand n) R)) = SOME (DataElement xs l d) /\
     heap_length M = n
     ==> heap_lookup j (APPEND L (APPEND M R)) = SOME (DataElement xs l d)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
  REWRITE_TAC[gen_gc_heap_length_heap_expand] THEN
  COND_CASES_TAC THEN REWRITE_TAC[GC2AUX_heap_lookup_heap_expand]);;

let GC2AUX_BIJ_step = prove
 (`!(H:((A,B)heap_element)list) (H':((A,B)heap_element)list) k r s s'.
     BIJ (heap_map1 H) (FDOM (heap_map 0 H)) s /\
     heap_map 0 H' = heap_map 0 H |+ (k,r) /\
     ~(k IN FDOM (heap_map 0 H)) /\ ~(r IN s) /\ s' = r INSERT s
     ==> BIJ (heap_map1 H') (FDOM (heap_map 0 H')) s'`,
  REWRITE_TAC[heap_map1_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[FDOM_FUPDATE] THEN
  SUBGOAL_THEN `(\a. FAPPLY (heap_map 0 (H:((A,B)heap_element)list) |+ (k,r)) a) =
                (k =+ r) (\a. FAPPLY (heap_map 0 H) a)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM; FAPPLY_FUPDATE_THM] THEN MESON_TAC[];
    MATCH_MP_TAC BIJ_UPDATE THEN ASM_REWRITE_TAC[]]);;

let GC2AUX_FLOOKUP_step = prove
 (`!(H:((A,B)heap_element)list) (H':((A,B)heap_element)list) k r
    (hold:((A,B)heap_element)list) (hnew:((A,B)heap_element)list) (fin:num->bool) fin'
    (heap0:((A,B)heap_element)list) (roots0:(A heap_address)list) ys l (d:B).
     (!i j. FLOOKUP (heap_map 0 H) i = SOME j
            ==> ?xs l d. heap_lookup i heap0 = SOME (DataElement xs l d) /\
                         heap_lookup j hold =
                           SOME (DataElement (if fin j then ADDR_MAP (heap_map1 H) xs
                                              else xs) l d) /\
                         reachable_addresses roots0 heap0 i /\
                         !ptr (d:A). MEM (Pointer ptr d) xs /\ fin j
                                     ==> ptr IN FDOM (heap_map 0 H)) /\
     heap_map 0 H' = heap_map 0 H |+ (k,r) /\ ~(k IN FDOM (heap_map 0 H)) /\
     heap_lookup k heap0 = SOME (DataElement ys l d) /\
     reachable_addresses roots0 heap0 k /\
     heap_lookup r hnew = SOME (DataElement ys l d) /\ ~fin' r /\ (!j. fin' j <=> fin j) /\
     (!j xs l d. heap_lookup j hold = SOME (DataElement xs l d)
                 ==> heap_lookup j hnew = SOME (DataElement xs l d))
     ==> !i j. FLOOKUP (heap_map 0 H') i = SOME j
               ==> ?xs l d. heap_lookup i heap0 = SOME (DataElement xs l d) /\
                            heap_lookup j hnew =
                              SOME (DataElement (if fin' j then ADDR_MAP (heap_map1 H') xs
                                                 else xs) l d) /\
                            reachable_addresses roots0 heap0 i /\
                            !ptr (d:A). MEM (Pointer ptr d) xs /\ fin' j
                                        ==> ptr IN FDOM (heap_map 0 H')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((fin:num->bool) r)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  ASM_CASES_TAC `k:num = i` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`ys:(A heap_address)list`; `l:num`; `d:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A heap_address)list` (X_CHOOSE_THEN `l':num`
    (X_CHOOSE_THEN `d':B` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l':num`; `d':B`] THEN
  ASM_REWRITE_TAC[FDOM_FUPDATE; IN_INSERT] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(fin:num->bool) j
                ==> ADDR_MAP (heap_map1 (H':((A,B)heap_element)list))
                      (xs:(A heap_address)list) =
                    ADDR_MAP (heap_map1 (H:((A,B)heap_element)list)) xs` MP_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC gen_gc_ADDR_MAP_EQ THEN
    ASM_REWRITE_TAC[heap_map1_def; FAPPLY_FUPDATE_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(fin:num->bool) j` THEN ASM_SIMP_TAC[]);;

let GC2AUX_INV_LABELS =
  ["len_a";"len_lim";"filt";"hlen";"ok";"hok";"sim";"d1";"d2";"dr1";"dr2";"dr3";"dr4";
   "isref";"bij";"fl"];;

let GC2AUX_gc_move_ref_inv = prove
 (`!(conf:B gen_gc_conf) old h1 h2 r4 r3 r2 r1 a n ok hp0 heap0
    (roots0:(A heap_address)list) ha ys l (d:B) hb (u:A).
     gen_gc_gc_inv conf
       (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok
          (APPEND ha (CONS (DataElement ys l d) hb)) hp0) heap0 roots0 /\
     reachable_addresses roots0 heap0 (heap_length ha) /\ gen_gc_conf_isRef conf d
     ==> ok /\ l + 1 <= n /\
         gen_gc_gc_inv conf
           (gc_state_REC old h1 h2 (CONS (DataElement ys l d) r4) r3 r2 r1 a
              (n - (l + 1)) T
              (APPEND ha (CONS (ForwardPointer (a + (n - (l + 1))) u l) hb)) hp0)
           heap0 roots0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC (GC2AUX_INV_LABELS @ ["reach";"isrefd"])
                                   (CONJUNCTS th))) THEN
  SUBGOAL_THEN `l + 1 <= n` (LABEL_TAC "ln") THENL
   [USE_THEN "filt" (MP_TAC o SYM) THEN
    REWRITE_TAC[FILTER_APPEND; FILTER; BETA_THM; isForwardPointer_def;
                heap_length_APPEND; heap_length_CONS; el_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ok" ACCEPT_TAC;
    USE_THEN "ln" ACCEPT_TAC;
    USE_THEN "len_a" ACCEPT_TAC;
    MAP_EVERY (fun s -> USE_THEN s MP_TAC) ["len_lim";"ln"] THEN
    REWRITE_TAC[APPEND; heap_length_APPEND; heap_length_CONS; el_length_def] THEN ARITH_TAC;
    USE_THEN "filt" MP_TAC THEN
    REWRITE_TAC[FILTER_APPEND; FILTER; BETA_THM; isForwardPointer_def;
                heap_length_APPEND; heap_length_CONS; el_length_def] THEN ARITH_TAC;
    USE_THEN "hlen" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; el_length_def];
    USE_THEN "hok" ACCEPT_TAC;
    USE_THEN "sim" (MATCH_ACCEPT_TAC o MATCH_MP
      (REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] GC2AUX_heaps_similar_lemma_local));
    USE_THEN "d1" ACCEPT_TAC;
    USE_THEN "d2" ACCEPT_TAC;
    USE_THEN "dr1" ACCEPT_TAC;
    USE_THEN "dr2" ACCEPT_TAC;
    USE_THEN "dr3" ACCEPT_TAC;
    REWRITE_TAC[ALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[isDataElement_def] THEN MESON_TAC[]; USE_THEN "dr4" ACCEPT_TAC];
    USE_THEN "isref" (fun th -> USE_THEN "isrefd" (fun th2 ->
      REWRITE_TAC[APPEND; MEM; heap_element_11] THEN MESON_TAC[th; th2]));
    MATCH_MP_TAC GC2AUX_BIJ_step THEN
    MAP_EVERY EXISTS_TAC
     [`APPEND ha (CONS (DataElement ys l d) hb):((A,B)heap_element)list`;
      `heap_length (ha:((A,B)heap_element)list)`; `a + (n - (l + 1))`;
      `heap_addresses 0 (APPEND h1 h2:((A,B)heap_element)list) UNION
       heap_addresses (a + n) (APPEND (APPEND (APPEND r4 r3) r2) r1:((A,B)heap_element)list)`] THEN
    REWRITE_TAC[heap_map_ForwardPointer_lemma; NOT_IN_heap_map] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "bij" ACCEPT_TAC;
      REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC NOT_IN_heap_addresses_gt THEN USE_THEN "len_a" SUBST1_TAC THEN ARITH_TAC;
        MATCH_MP_TAC NOT_IN_heap_addresses_less THEN USE_THEN "ln" MP_TAC THEN ARITH_TAC];
      REWRITE_TAC[APPEND; heap_addresses_def; el_length_def] THEN
      SUBGOAL_THEN `(a + (n - (l + 1))) + (l + 1) = a + n` SUBST1_TAC THENL
       [USE_THEN "ln" MP_TAC THEN ARITH_TAC; SET_TAC[]]];
    MATCH_MP_TAC GC2AUX_FLOOKUP_step THEN
    MAP_EVERY EXISTS_TAC
     [`APPEND ha (CONS (DataElement ys l d) hb):((A,B)heap_element)list`;
      `heap_length (ha:((A,B)heap_element)list)`; `a + (n - (l + 1))`;
      `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3) r2) r1
       :((A,B)heap_element)list`;
      `is_final (conf:B gen_gc_conf)
         (gc_state_REC (old:((A,B)heap_element)list) h1 h2 r4 r3 r2 r1 a n ok
            (APPEND ha (CONS (DataElement ys l d) hb)) hp0)`;
      `ys:(A heap_address)list`; `l:num`; `d:B`] THEN
    REWRITE_TAC[heap_map_ForwardPointer_lemma; NOT_IN_heap_map] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "fl" ACCEPT_TAC;
      USE_THEN "sim" (STRIP_ASSUME_TAC o MATCH_MP heap_similar_Data_IMP) THEN
      ASM_REWRITE_TAC[heap_lookup_PREFIX];
      USE_THEN "reach" ACCEPT_TAC;
      SUBGOAL_THEN
       `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand (n - (l + 1))))
          (CONS (DataElement ys l d) r4)) r3) r2) r1 =
        APPEND (APPEND (APPEND h1 h2) (heap_expand (n - (l + 1))))
          (CONS (DataElement ys l d) (APPEND (APPEND (APPEND r4 r3) r2) r1))
        :((A,B)heap_element)list` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
      MATCH_MP_TAC heap_lookup_LENGTH THEN
      REWRITE_TAC[heap_length_APPEND; gen_gc_heap_length_heap_expand] THEN
      USE_THEN "len_a" MP_TAC THEN REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC;
      REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors;
                  heap_length_CONS; el_length_def] THEN
      USE_THEN "len_a" MP_TAC THEN USE_THEN "ln" MP_TAC THEN
      REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC;
      GEN_TAC THEN
      REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors;
                  heap_length_CONS; el_length_def] THEN
      USE_THEN "ln" MP_TAC THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      SUBGOAL_THEN
       `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3) r2) r1 =
        APPEND (APPEND h1 h2) (APPEND (heap_expand n) (APPEND (APPEND (APPEND r4 r3) r2) r1))
        :((A,B)heap_element)list` SUBST1_TAC THENL
       [REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
      SUBGOAL_THEN
       `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand (n - (l + 1))))
          (CONS (DataElement ys l d) r4)) r3) r2) r1 =
        APPEND (APPEND h1 h2)
          (APPEND (APPEND (heap_expand (n - (l + 1))) [DataElement ys l d])
             (APPEND (APPEND (APPEND r4 r3) r2) r1))
        :((A,B)heap_element)list` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC GC2AUX_heap_lookup_frame THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[heap_length_APPEND; gen_gc_heap_length_heap_expand; heap_length_CONS;
                  heap_length_NIL; el_length_def] THEN
      USE_THEN "ln" MP_TAC THEN ARITH_TAC]]);;

let GC2AUX_gc_move_data_inv = prove
 (`!(conf:B gen_gc_conf) old h1 h2 r4 r3 r2 r1 a n ok hp0 heap0
    (roots0:(A heap_address)list) ha ys l (d:B) hb (u:A).
     gen_gc_gc_inv conf
       (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok
          (APPEND ha (CONS (DataElement ys l d) hb)) hp0) heap0 roots0 /\
     reachable_addresses roots0 heap0 (heap_length ha)
     ==> ok /\ l + 1 <= n /\
         gen_gc_gc_inv conf
           (gc_state_REC old h1 (APPEND h2 [DataElement ys l d]) r4 r3 r2 r1 (a + l + 1)
              (n - (l + 1)) T
              (APPEND ha (CONS (ForwardPointer a u l) hb)) hp0)
           heap0 roots0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC (GC2AUX_INV_LABELS @ ["reach"])
                                   (CONJUNCTS th))) THEN
  SUBGOAL_THEN `l + 1 <= n` (LABEL_TAC "ln") THENL
   [USE_THEN "filt" (MP_TAC o SYM) THEN
    REWRITE_TAC[FILTER_APPEND; FILTER; BETA_THM; isForwardPointer_def;
                heap_length_APPEND; heap_length_CONS; el_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ok" ACCEPT_TAC;
    USE_THEN "ln" ACCEPT_TAC;
    USE_THEN "len_a" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def] THEN
    ARITH_TAC;
    MAP_EVERY (fun s -> USE_THEN s MP_TAC) ["len_lim";"ln"] THEN ARITH_TAC;
    USE_THEN "filt" MP_TAC THEN
    REWRITE_TAC[FILTER_APPEND; FILTER; BETA_THM; isForwardPointer_def;
                heap_length_APPEND; heap_length_CONS; el_length_def] THEN ARITH_TAC;
    USE_THEN "hlen" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; el_length_def];
    USE_THEN "hok" ACCEPT_TAC;
    USE_THEN "sim" (MATCH_ACCEPT_TAC o MATCH_MP
      (REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] GC2AUX_heaps_similar_lemma_local));
    USE_THEN "d1" ACCEPT_TAC;
    REWRITE_TAC[ALL_APPEND; ALL] THEN CONJ_TAC THENL
     [USE_THEN "d2" ACCEPT_TAC; REWRITE_TAC[isDataElement_def] THEN MESON_TAC[]];
    USE_THEN "dr1" ACCEPT_TAC;
    USE_THEN "dr2" ACCEPT_TAC;
    USE_THEN "dr3" ACCEPT_TAC;
    USE_THEN "dr4" ACCEPT_TAC;
    USE_THEN "isref" ACCEPT_TAC;
    MATCH_MP_TAC GC2AUX_BIJ_step THEN
    MAP_EVERY EXISTS_TAC
     [`APPEND ha (CONS (DataElement ys l d) hb):((A,B)heap_element)list`;
      `heap_length (ha:((A,B)heap_element)list)`; `a:num`;
      `heap_addresses 0 (APPEND h1 h2:((A,B)heap_element)list) UNION
       heap_addresses (a + n) (APPEND (APPEND (APPEND r4 r3) r2) r1:((A,B)heap_element)list)`] THEN
    REWRITE_TAC[heap_map_ForwardPointer_lemma; NOT_IN_heap_map] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "bij" ACCEPT_TAC;
      REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC NOT_IN_heap_addresses_gt THEN USE_THEN "len_a" SUBST1_TAC THEN ARITH_TAC;
        MATCH_MP_TAC NOT_IN_heap_addresses_less THEN USE_THEN "ln" MP_TAC THEN ARITH_TAC];
      SUBGOAL_THEN
       `heap_addresses 0 (APPEND h1 (APPEND h2 [DataElement ys l d])) =
        heap_addresses 0 (APPEND h1 h2:((A,B)heap_element)list) UNION {a}`
        SUBST1_TAC THENL
       [REWRITE_TAC[gc_shared_heap_addresses_APPEND; ADD_CLAUSES; heap_length_APPEND;
                    UNION_ASSOC] THEN
        USE_THEN "len_a" (SUBST1_TAC o REWRITE_RULE[heap_length_APPEND]) THEN
        REWRITE_TAC[heap_addresses_def];
        ALL_TAC] THEN
      SUBGOAL_THEN `(a + l + 1) + (n - (l + 1)) = a + n` SUBST1_TAC THENL
       [USE_THEN "ln" MP_TAC THEN ARITH_TAC; SET_TAC[]]];
    MATCH_MP_TAC GC2AUX_FLOOKUP_step THEN
    MAP_EVERY EXISTS_TAC
     [`APPEND ha (CONS (DataElement ys l d) hb):((A,B)heap_element)list`;
      `heap_length (ha:((A,B)heap_element)list)`; `a:num`;
      `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3) r2) r1
       :((A,B)heap_element)list`;
      `is_final (conf:B gen_gc_conf)
         (gc_state_REC (old:((A,B)heap_element)list) h1 h2 r4 r3 r2 r1 a n ok
            (APPEND ha (CONS (DataElement ys l d) hb)) hp0)`;
      `ys:(A heap_address)list`; `l:num`; `d:B`] THEN
    REWRITE_TAC[heap_map_ForwardPointer_lemma; NOT_IN_heap_map] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "fl" ACCEPT_TAC;
      USE_THEN "sim" (STRIP_ASSUME_TAC o MATCH_MP heap_similar_Data_IMP) THEN
      ASM_REWRITE_TAC[heap_lookup_PREFIX];
      USE_THEN "reach" ACCEPT_TAC;
      SUBGOAL_THEN
       `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 (APPEND h2 [DataElement ys l d]))
          (heap_expand (n - (l + 1)))) r4) r3) r2) r1 =
        APPEND (APPEND h1 h2)
          (CONS (DataElement ys l d)
            (APPEND (heap_expand (n - (l + 1))) (APPEND (APPEND (APPEND r4 r3) r2) r1)))
        :((A,B)heap_element)list` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
      MATCH_MP_TAC heap_lookup_LENGTH THEN USE_THEN "len_a" ACCEPT_TAC;
      REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
      USE_THEN "len_a" MP_TAC THEN USE_THEN "ln" MP_TAC THEN
      REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC;
      GEN_TAC THEN
      REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
      USE_THEN "ln" MP_TAC THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      SUBGOAL_THEN
       `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3) r2) r1 =
        APPEND (APPEND h1 h2) (APPEND (heap_expand n) (APPEND (APPEND (APPEND r4 r3) r2) r1))
        :((A,B)heap_element)list` SUBST1_TAC THENL
       [REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
      SUBGOAL_THEN
       `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 (APPEND h2 [DataElement ys l d]))
          (heap_expand (n - (l + 1)))) r4) r3) r2) r1 =
        APPEND (APPEND h1 h2)
          (APPEND (APPEND [DataElement ys l d] (heap_expand (n - (l + 1))))
             (APPEND (APPEND (APPEND r4 r3) r2) r1))
        :((A,B)heap_element)list` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC GC2AUX_heap_lookup_frame THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[heap_length_APPEND; gen_gc_heap_length_heap_expand; heap_length_CONS;
                  heap_length_NIL; el_length_def] THEN
      USE_THEN "ln" MP_TAC THEN ARITH_TAC]]);;

let GC2AUX_gc_move_thm_Pointer = prove
 (`!ptr0 (u0:A) (state:(A,B)gc_state) (conf:B gen_gc_conf) heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0 /\
     isSomeDataOrForward (heap_lookup ptr0 (gc_state_heap state)) /\
     reachable_addresses roots0 heap0 ptr0
     ==> ?state'.
           gen_gc_gc_move conf state (Pointer ptr0 u0) =
             (ADDR_APPLY (heap_map1 (gc_state_heap state')) (Pointer ptr0 u0),state') /\
           ptr0 IN FDOM (heap_map 0 (gc_state_heap state')) /\
           (!ptr. isSomeDataOrForward (heap_lookup ptr (gc_state_heap state)) <=>
                  isSomeDataOrForward (heap_lookup ptr (gc_state_heap state'))) /\
           heap_map 0 (gc_state_heap state) SUBMAP heap_map 0 (gc_state_heap state') /\
           gen_gc_gc_inv conf state' heap0 roots0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [isSomeDataOrForward_def; isSomeForwardPointer_def; isSomeDataElement_def] THEN
  STRIP_TAC THENL
   [(* a forward pointer: nothing changes *)
    FIRST_ASSUM(MP_TAC o MATCH_MP heap_lookup_FLOOKUP) THEN REWRITE_TAC[FLOOKUP_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN DISCH_TAC THEN
    EXISTS_TAC `state:(A,B)gc_state` THEN
    SIMP[gen_gc_gc_move_def; ADDR_APPLY_def; heap_map1_def; SUBMAP_REFL];
    ALL_TAC] THEN
  (* a data element: it is moved to r4 (a reference) or to h2 *)
  CASES_ON `state:(A,B)gc_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accessors]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ha:((A,B)heap_element)list`
    (X_CHOOSE_THEN `hb:((A,B)heap_element)list` (CONJUNCTS_THEN SUBST_ALL_TAC)) o
    MATCH_MP heap_lookup_SPLIT) THEN
  ASM_CASES_TAC `gen_gc_conf_isRef (conf:B gen_gc_conf) d` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_gc_move_ref_inv));
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_gc_move_data_inv))] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o SPEC `u0:A`) THEN
  SIMP[gen_gc_gc_move_def; heap_lookup_PREFIX; gc_forward_ptr_thm] THEN
  REWRITE_TAC[ADDR_APPLY_def; heap_map1_def; heap_map_ForwardPointer_lemma; FAPPLY_FUPDATE_THM;
              FDOM_FUPDATE; IN_INSERT] THEN
  (CONJ_TAC THENL
    [GEN_TAC THEN MATCH_ACCEPT_TAC gen_gc_isSomeDataOrForward_lemma;
     MATCH_MP_TAC SUBMAP_FUPDATE_EXTENDED THEN REWRITE_TAC[NOT_IN_heap_map]]));;

let gen_gc_gc_move_thm = prove
 (`!x (state:(A,B)gc_state) (conf:B gen_gc_conf) heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0 /\
     (!ptr u. x = Pointer ptr u
              ==> isSomeDataOrForward (heap_lookup ptr (gc_state_heap state)) /\
                  reachable_addresses roots0 heap0 ptr)
     ==> ?state'.
           gen_gc_gc_move conf state x =
             (ADDR_APPLY (heap_map1 (gc_state_heap state')) x,state') /\
           (!ptr u. x = Pointer ptr u ==> ptr IN FDOM (heap_map 0 (gc_state_heap state'))) /\
           (!ptr. isSomeDataOrForward (heap_lookup ptr (gc_state_heap state)) <=>
                  isSomeDataOrForward (heap_lookup ptr (gc_state_heap state'))) /\
           heap_map 0 (gc_state_heap state) SUBMAP heap_map 0 (gc_state_heap state') /\
           gen_gc_gc_inv conf state' heap0 roots0`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[heap_address_11; heap_address_distinct] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a1:A`]) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a0:num`; `a1:A`; `state:(A,B)gc_state`; `conf:B gen_gc_conf`;
                   `heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]
           GC2AUX_gc_move_thm_Pointer) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:(A,B)gc_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:(A,B)gc_state` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `state:(A,B)gc_state` THEN
    ASM_REWRITE_TAC[gen_gc_gc_move_def; ADDR_APPLY_def; SUBMAP_REFL]]);;

let gen_gc_gc_move_ALT = prove
 (CASE_TERM `!(conf:B gen_gc_conf) (state:(A,B)gc_state) y.
     gen_gc_gc_move conf state y =
     match gen_gc_gc_move conf (gc_state_r4_fupd (combin_K []) (gc_state_h2_fupd (combin_K []) state)) y with
       (y',state') ->
         (y',gc_state_r4_fupd (combin_K (APPEND (gc_state_r4 state') (gc_state_r4 state)))
               (gc_state_h2_fupd (combin_K (APPEND (gc_state_h2 state) (gc_state_h2 state')))
                  state'))`,
  REPEAT GEN_TAC THEN CASES_ON `state:(A,B)gc_state` THEN CASES_ON `y:A heap_address` THEN
  SIMP[gen_gc_gc_move_def] THEN EVERY_CASE_TAC THEN SIMP[APPEND_NIL]);;

let GC2AUX_LABEL_MOVE_RESULT s n =
  X_CHOOSE_THEN s (CONJUNCTS_THEN2 (LABEL_TAC ("m"^n)) (CONJUNCTS_THEN2 (LABEL_TAC ("in"^n))
    (CONJUNCTS_THEN2 (LABEL_TAC ("eq"^n)) (CONJUNCTS_THEN2 (LABEL_TAC ("sub"^n))
       (LABEL_TAC ("inv"^n))))));;

let gen_gc_gc_move_list_thm = prove
 (`!xs (state:(A,B)gc_state) (conf:B gen_gc_conf) heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0 /\
     (!ptr u. MEM (Pointer ptr u) xs
              ==> isSomeDataOrForward (heap_lookup ptr (gc_state_heap state)) /\
                  reachable_addresses roots0 heap0 ptr)
     ==> ?state'.
           gen_gc_gc_move_list conf state xs =
             (ADDR_MAP (heap_map1 (gc_state_heap state')) xs,state') /\
           (!ptr u. MEM (Pointer ptr u) xs
                    ==> ptr IN FDOM (heap_map 0 (gc_state_heap state'))) /\
           (!ptr. isSomeDataOrForward (heap_lookup ptr (gc_state_heap state)) <=>
                  isSomeDataOrForward (heap_lookup ptr (gc_state_heap state'))) /\
           heap_map 0 (gc_state_heap state) SUBMAP heap_map 0 (gc_state_heap state') /\
           gen_gc_gc_inv conf state' heap0 roots0`,
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `state:(A,B)gc_state` THEN
    ASM_REWRITE_TAC[gen_gc_gc_move_list_def; ADDR_MAP_def; MEM; SUBMAP_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv") (LABEL_TAC "hyp")) THEN
  MP_TAC(ISPECL [`h:A heap_address`; `state:(A,B)gc_state`; `conf:B gen_gc_conf`;
                 `heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]
         gen_gc_gc_move_thm) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "inv" ACCEPT_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "hyp" (MP_TAC o SPECL [`ptr:num`; `u:A`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(GC2AUX_LABEL_MOVE_RESULT `s1:(A,B)gc_state` "1") THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,B)gc_state`; `conf:B gen_gc_conf`;
                 `heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "inv1" ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "eq1" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "hyp" (MP_TAC o SPECL [`ptr:num`; `u:A`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(GC2AUX_LABEL_MOVE_RESULT `s2:(A,B)gc_state` "2") THEN
  EXISTS_TAC `s2:(A,B)gc_state` THEN
  USE_THEN "m1" (fun th -> REWRITE_TAC[gen_gc_gc_move_list_def; th; pair_CASE]) THEN
  USE_THEN "m2" (fun th -> REWRITE_TAC[th; pair_CASE]) THEN
  USE_THEN "inv2" (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [CASES_ON `h:A heap_address` THEN
    REWRITE_TAC[ADDR_MAP_def; ADDR_APPLY_def; PAIR_EQ; CONS_11; heap_address_11;
                heap_map1_def] THEN
    USE_THEN "in1" (MP_TAC o SPECL [`a0:num`; `a1:A`]) THEN
    USE_THEN "sub2" MP_TAC THEN REWRITE_TAC[SUBMAP_DEF] THEN MESON_TAC[];
    USE_THEN "in1" MP_TAC THEN USE_THEN "in2" MP_TAC THEN USE_THEN "sub2" MP_TAC THEN
    REWRITE_TAC[SUBMAP_DEF] THEN MESON_TAC[];
    USE_THEN "eq1" (fun th -> USE_THEN "eq2" (fun th2 -> REWRITE_TAC[th; th2]));
    USE_THEN "sub1" (fun th -> USE_THEN "sub2" (fun th2 ->
      MATCH_ACCEPT_TAC(MATCH_MP SUBMAP_TRANS (CONJ th th2))))]);;

let gen_gc_gc_move_list_ALT = prove
 (CASE_TERM `!ys (state:(A,B)gc_state) (conf:B gen_gc_conf).
     gen_gc_gc_move_list conf state ys =
     match gen_gc_gc_move_list conf (gc_state_r4_fupd (combin_K []) (gc_state_h2_fupd (combin_K []) state)) ys
     with (ys',state') ->
       (ys',gc_state_r4_fupd (combin_K (APPEND (gc_state_r4 state') (gc_state_r4 state)))
              (gc_state_h2_fupd (combin_K (APPEND (gc_state_h2 state) (gc_state_h2 state'))) state'))`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN CASES_ON `state:(A,B)gc_state` THEN
    SIMP[gen_gc_gc_move_list_def; APPEND_NIL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def] THEN
  SUBST1_TAC(ISPECL [`conf:B gen_gc_conf`; `state:(A,B)gc_state`; `h:A heap_address`]
             gen_gc_gc_move_ALT) THEN
  SPEC_TAC(`gen_gc_gc_move (conf:B gen_gc_conf)
              (gc_state_r4_fupd (combin_K []) (gc_state_h2_fupd (combin_K []) (state:(A,B)gc_state))) h`,
           `p:(A heap_address)#(A,B)gc_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN
  MAP_EVERY X_GEN_TAC [`x:A heap_address`; `s1:(A,B)gc_state`] THEN
  (* the induction hypothesis is used once on each side, then dropped *)
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN SIMP[] THEN
  SPEC_TAC(`gen_gc_gc_move_list (conf:B gen_gc_conf)
              (gc_state_h2_fupd (combin_K []) (gc_state_r4_fupd (combin_K []) (s1:(A,B)gc_state))) t`,
           `q:(A heap_address)list#(A,B)gc_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN SIMP[APPEND_ASSOC]);;

let gen_gc_gc_move_list_APPEND_lemma = prove
 (`!ys (state:(A,B)gc_state) (conf:B gen_gc_conf) ys' state'.
     gen_gc_gc_move_list conf state ys = (ys',state')
     ==> ?h2' r4'. gc_state_h2 state' = APPEND (gc_state_h2 state) h2' /\
                   gc_state_r4 state' = APPEND r4' (gc_state_r4 state)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[gen_gc_gc_move_list_ALT] THEN
  SPEC_TAC(`gen_gc_gc_move_list (conf:B gen_gc_conf)
              (gc_state_r4_fupd (combin_K []) (gc_state_h2_fupd (combin_K []) (state:(A,B)gc_state))) ys`,
           `q:(A heap_address)list#(A,B)gc_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  SIMP[] THEN MESON_TAC[]);;

let gen_gc_heap_addresses_APPEND = prove
 (`!xs ys:((A,B)heap_element)list n.
     heap_addresses n (APPEND xs ys) =
     heap_addresses n xs UNION heap_addresses (n + heap_length xs) ys`,
  REWRITE_TAC[gc_shared_heap_addresses_APPEND]);;

let heap_addresses_APPEND_IN = prove
 (`!xs ys:((A,B)heap_element)list n j.
     j IN heap_addresses n (APPEND xs ys)
     ==> j IN heap_addresses n xs \/ j IN heap_addresses (n + heap_length xs) ys`,
  REWRITE_TAC[gen_gc_heap_addresses_APPEND; IN_UNION]);;

let GREATER_IMP_heap_lookup = prove
 (`!ys xs:((A,B)heap_element)list j.
     heap_length (APPEND xs ys) <= j + heap_length ys
     ==> heap_lookup j (APPEND xs ys) = heap_lookup (j - heap_length xs) ys`,
  REWRITE_TAC[heap_length_APPEND] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NOT_LESS_IMP_heap_lookup THEN ASM_ARITH_TAC);;

let heap_lookup_IMP_MEM = prove
 (`!x n (y:(A,B)heap_element). heap_lookup n x = SOME y ==> MEM y x`,
  MESON_TAC[heap_lookup_MEM]);;

(* HOL4 has a second theorem of this name after the local one above; this *)
(* one is the exported heaps_similar_lemma                                 *)
let gen_gc_heaps_similar_lemma = prove
 (`!h1 h2:((A,B)heap_element)list ptr.
     heaps_similar h1 h2 /\ isSomeDataElement (heap_lookup ptr h1)
     ==> isSomeDataOrForward (heap_lookup ptr h2)`,
  REWRITE_TAC[heap_similar_Data_IMP_DataOrForward]);;

let BIJ_IMP_FLOOKUP_SOME = prove
 (`!s (h:((A,B)heap_element)list) j.
     BIJ (heap_map1 h) (FDOM (heap_map 0 h)) s /\ j IN s
     ==> ?i. FLOOKUP (heap_map 0 h) i = SOME j`,
  REWRITE_TAC[heap_map1_def; BIJ; SURJ; FLOOKUP_DEF] THEN MESON_TAC[]);;

let heap_lookup_IMP_heap_addresses_GEN = prove
 (`!xs n (x:(A,B)heap_element) j.
     heap_lookup j xs = SOME x ==> n + j IN heap_addresses n xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; option_DISTINCT; heap_addresses_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INSERT; ADD_CLAUSES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  DISJ2_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`n + el_length (h:(A,B)heap_element)`; `x:(A,B)heap_element`;
     `j - el_length (h:(A,B)heap_element)`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* an element of a middle segment of a heap *)
let GC2AUX_heap_lookup_middle = prove
 (`!xs ys zs j (x:(A,B)heap_element).
     heap_lookup j ys = SOME x
     ==> heap_lookup (heap_length xs + j) (APPEND xs (APPEND ys zs)) = SOME x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(heap_length (xs:((A,B)heap_element)list) + j < heap_length xs)` ASSUME_TAC
  THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup; ADD_SUB2; gc_shared_heap_lookup_EXTEND]);;

let GC2AUX_heap_lookup_middle2 = prove
 (`!xs ys zs j (x:(A,B)heap_element).
     heap_lookup j ys = SOME x
     ==> heap_lookup (heap_length xs + j) (APPEND (APPEND xs ys) zs) = SOME x`,
  REWRITE_TAC[GSYM APPEND_ASSOC; GC2AUX_heap_lookup_middle]);;

let GC2AUX_pointers_ok_REC = prove
 (`!(conf:B gen_gc_conf) old h1 h2 r4 r3 r2 r1 a n ok heap hp0 heap0
    (roots0:(A heap_address)list) xs l (d:B) ptr (u:A).
     gen_gc_gc_inv conf (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok heap hp0) heap0 roots0 /\
     (MEM (DataElement xs l d) h2 \/ MEM (DataElement xs l d) r2) /\
     MEM (Pointer ptr u) xs
     ==> isSomeDataOrForward (heap_lookup ptr heap)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> EVERY (map2 LABEL_TAC GC2AUX_INV_LABELS (CONJUNCTS th)))
    (CONJUNCTS_THEN2 (LABEL_TAC "mem") (LABEL_TAC "memp"))) THEN
  SUBGOAL_THEN
   `?j. ~is_final (conf:B gen_gc_conf)
          (gc_state_REC (old:((A,B)heap_element)list) h1 h2 r4 r3 r2 r1 a n ok heap hp0) j /\
        heap_lookup j (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2)
          (heap_expand n)) r4) r3) r2) r1) = SOME (DataElement xs l (d:B)) /\
        j IN heap_addresses 0 (APPEND h1 h2) UNION
             heap_addresses (a + n) (APPEND (APPEND (APPEND r4 r3) r2) r1)`
   (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 (LABEL_TAC "nf")
      (CONJUNCTS_THEN2 (LABEL_TAC "lk") (LABEL_TAC "jin")))) THENL
   [REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
    USE_THEN "len_a" (MP_TAC o REWRITE_RULE[heap_length_APPEND]) THEN DISCH_TAC THEN
    USE_THEN "mem" (DISJ_CASES_THEN (X_CHOOSE_TAC `j0:num` o MATCH_MP MEM_IMP_heap_lookup)) THENL
     [EXISTS_TAC `heap_length (h1:((A,B)heap_element)list) + j0` THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP heap_lookup_LESS) THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC GC2AUX_heap_lookup_middle THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_UNION; gen_gc_heap_addresses_APPEND; ADD_CLAUSES] THEN
        DISJ1_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC heap_lookup_IMP_heap_addresses_GEN THEN
        EXISTS_TAC `DataElement xs l d:(A,B)heap_element` THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `heap_length (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3
                    :((A,B)heap_element)list) + j0` THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP heap_lookup_LESS) THEN
      SUBGOAL_THEN `heap_length (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3
                      :((A,B)heap_element)list) =
                    (a + n) + heap_length r4 + heap_length r3` ASSUME_TAC THENL
       [REWRITE_TAC[heap_length_APPEND; gen_gc_heap_length_heap_expand] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC GC2AUX_heap_lookup_middle2 THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_UNION; gen_gc_heap_addresses_APPEND; heap_length_APPEND] THEN
        DISJ2_TAC THEN DISJ1_TAC THEN DISJ2_TAC THEN
        MATCH_MP_TAC heap_lookup_IMP_heap_addresses_GEN THEN
        EXISTS_TAC `DataElement xs l d:(A,B)heap_element` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "jin" (fun th -> USE_THEN "bij" (fun th2 ->
    MP_TAC(MATCH_MP BIJ_IMP_FLOOKUP_SOME (CONJ th2 th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (fun th -> USE_THEN "fl" (MP_TAC o C MATCH_MP th))) THEN
  USE_THEN "nf" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs':(A heap_address)list` (X_CHOOSE_THEN `l':num`
    (X_CHOOSE_THEN `d':B` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))))) THEN
  USE_THEN "lk" (fun th -> REWRITE_TAC[th; option_INJ; heap_element_11]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (K ALL_TAC)) THEN
  USE_THEN "sim" (fun th -> MATCH_MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ]
    heap_similar_Data_IMP_DataOrForward) th)) THEN
  USE_THEN "hok" (MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[heap_ok_def]) THEN
  MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l':num`; `d':B`; `u:A`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[heap_lookup_MEM]);;

let pointers_ok = prove
 (`!(state:(A,B)gc_state) xs l (d:B) ptr (u:A) (conf:B gen_gc_conf) heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0 /\
     (MEM (DataElement xs l d) (gc_state_h2 state) \/
      MEM (DataElement xs l d) (gc_state_r2 state)) /\
     MEM (Pointer ptr u) xs
     ==> isSomeDataOrForward (heap_lookup ptr (gc_state_heap state))`,
  GEN_TAC THEN CASES_ON `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; GC2AUX_pointers_ok_REC]);;

let IMP_reachable_addresses = prove
 (`!i ptr (u:A) xs l (d:B) roots0 heap0.
     reachable_addresses roots0 heap0 i /\ MEM (Pointer ptr u) xs /\
     heap_lookup i heap0 = SOME (DataElement xs l d)
     ==> reachable_addresses roots0 heap0 ptr`,
  REWRITE_TAC[reachable_addresses_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:A`; `x:num`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `i:num` THEN
  ASM_REWRITE_TAC[gc_edge_def] THEN ASM_MESON_TAC[]);;

(* helpers for the scanning steps: an element replaced by one of the same *)
(* length, and an element of the heap that is not final has reachable     *)
(* pointers                                                               *)

let GC2AUX_heap_lookup_replace = prove
 (`!xs (x:(A,B)heap_element) y ys j.
     el_length x = el_length y /\ ~(j = heap_length xs)
     ==> heap_lookup j (APPEND xs (CONS x ys)) = heap_lookup j (APPEND xs (CONS y ys))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[heap_lookup_def] THEN
  SUBGOAL_THEN `~(j - heap_length (xs:((A,B)heap_element)list) = 0)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let GC2AUX_heap_lookup_inside = prove
 (`!xs (x:(A,B)heap_element) ys j z.
     heap_lookup j (APPEND xs (CONS x ys)) = SOME z /\ heap_length xs < j
     ==> heap_length xs + el_length x <= j`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[heap_lookup_def] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC);;

let GC2AUX_FLOOKUP_scan = prove
 (`!(H:((A,B)heap_element)list) (fin:num->bool) fin' heap0 (roots0:(A heap_address)list)
    xs1 xs2 zs l (d:B).
     (!i j. FLOOKUP (heap_map 0 H) i = SOME j
            ==> ?xs l' d'. heap_lookup i heap0 = SOME (DataElement xs l' d') /\
                           heap_lookup j (APPEND xs1 (CONS (DataElement zs l d) xs2)) =
                             SOME (DataElement (if fin j then ADDR_MAP (heap_map1 H) xs
                                                else xs) l' d') /\
                           reachable_addresses roots0 heap0 i /\
                           !ptr (u:A). MEM (Pointer ptr u) xs /\ fin j
                                       ==> ptr IN FDOM (heap_map 0 H)) /\
     ~fin (heap_length xs1) /\ fin' (heap_length xs1) /\
     (!j. ~(heap_length xs1 <= j /\ j < heap_length xs1 + l + 1) ==> (fin' j <=> fin j)) /\
     (!ptr (u:A). MEM (Pointer ptr u) zs ==> ptr IN FDOM (heap_map 0 H))
     ==> !i j. FLOOKUP (heap_map 0 H) i = SOME j
               ==> ?xs l' d'. heap_lookup i heap0 = SOME (DataElement xs l' d') /\
                              heap_lookup j (APPEND xs1
                                (CONS (DataElement (ADDR_MAP (heap_map1 H) zs) l d) xs2)) =
                                SOME (DataElement (if fin' j then ADDR_MAP (heap_map1 H) xs
                                                   else xs) l' d') /\
                              reachable_addresses roots0 heap0 i /\
                              !ptr (u:A). MEM (Pointer ptr u) xs /\ fin' j
                                          ==> ptr IN FDOM (heap_map 0 H)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "f1") (CONJUNCTS_THEN2 (LABEL_TAC "eq") (LABEL_TAC "zs"))))) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  DISCH_THEN(fun th -> USE_THEN "fl" (fun fl -> MP_TAC(MATCH_MP fl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(A heap_address)list` (X_CHOOSE_THEN `l':num`
    (X_CHOOSE_THEN `d':B` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lk")
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ptrs"))))))) THEN
  MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l':num`; `d':B`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j = heap_length (xs1:((A,B)heap_element)list)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "lk" MP_TAC THEN USE_THEN "nf" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[heap_lookup_PREFIX; option_INJ; heap_element_11] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
      (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
    USE_THEN "f1" (fun th -> REWRITE_TAC[th; heap_lookup_PREFIX]) THEN
    USE_THEN "zs" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(fin':num->bool) j <=> fin j` (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "eq" MATCH_MP_TAC THEN
    ASM_CASES_TAC `heap_length (xs1:((A,B)heap_element)list) < j` THENL
     [USE_THEN "lk" (fun th -> MP_TAC(MATCH_MP GC2AUX_heap_lookup_inside
        (CONJ th (ASSUME `heap_length (xs1:((A,B)heap_element)list) < j`)))) THEN
      REWRITE_TAC[el_length_def] THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "ptrs" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`xs1:((A,B)heap_element)list`; `DataElement zs l d:(A,B)heap_element`;
                 `DataElement (ADDR_MAP (heap_map1 (H:((A,B)heap_element)list))
                    (zs:(A heap_address)list)) l (d:B)`;
                 `xs2:((A,B)heap_element)list`; `j:num`] GC2AUX_heap_lookup_replace) THEN
  ASM_REWRITE_TAC[el_length_def] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "lk" ACCEPT_TAC);;

let GC2AUX_nonfinal_reachable = prove
 (`!(conf:B gen_gc_conf) old h1 h2 r4 r3 r2 r1 a n ok heap hp0 heap0
    (roots0:(A heap_address)list) j zs l (d:B) ptr (u:A).
     gen_gc_gc_inv conf (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok heap hp0) heap0 roots0 /\
     ~is_final conf (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok heap hp0) j /\
     heap_lookup j (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2)
          (heap_expand n)) r4) r3) r2) r1) = SOME (DataElement zs l d) /\
     j IN heap_addresses 0 (APPEND h1 h2) UNION
          heap_addresses (a + n) (APPEND (APPEND (APPEND r4 r3) r2) r1) /\
     MEM (Pointer ptr u) zs
     ==> reachable_addresses roots0 heap0 ptr`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> EVERY (map2 LABEL_TAC GC2AUX_INV_LABELS (CONJUNCTS th)))
    (CONJUNCTS_THEN2 (LABEL_TAC "nf") (CONJUNCTS_THEN2 (LABEL_TAC "lk")
      (CONJUNCTS_THEN2 (LABEL_TAC "jin") (LABEL_TAC "memp"))))) THEN
  USE_THEN "jin" (fun th -> USE_THEN "bij" (fun th2 ->
    MP_TAC(MATCH_MP BIJ_IMP_FLOOKUP_SOME (CONJ th2 th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (fun th -> USE_THEN "fl" (MP_TAC o C MATCH_MP th))) THEN
  USE_THEN "nf" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs':(A heap_address)list` (X_CHOOSE_THEN `l':num`
    (X_CHOOSE_THEN `d':B` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))))) THEN
  USE_THEN "lk" (fun th -> REWRITE_TAC[th; option_INJ; heap_element_11]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (K ALL_TAC)) THEN
  MATCH_MP_TAC IMP_reachable_addresses THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `u:A`; `zs:(A heap_address)list`; `l':num`; `d':B`] THEN
  ASM_REWRITE_TAC[]);;

let GC2AUX_gc_move_data_step_inv = prove
 (`!(conf:B gen_gc_conf) old h1 t r4 r3 r2 r1 a n ok heap hp0 heap0
    (roots0:(A heap_address)list) zs l (d:B).
     gen_gc_gc_inv conf
       (gc_state_REC old h1 (CONS (DataElement zs l d) t) r4 r3 r2 r1 a n ok heap hp0)
       heap0 roots0 /\
     (!ptr (u:A). MEM (Pointer ptr u) zs ==> ptr IN FDOM (heap_map 0 heap))
     ==> gen_gc_gc_inv conf
           (gc_state_REC old (APPEND h1 [DataElement (ADDR_MAP (heap_map1 heap) zs) l d]) t
              r4 r3 r2 r1 a n T heap hp0) heap0 roots0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> EVERY (map2 LABEL_TAC GC2AUX_INV_LABELS (CONJUNCTS th)))
    (LABEL_TAC "zs")) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "len_a" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def] THEN
    ARITH_TAC;
    USE_THEN "len_lim" ACCEPT_TAC;
    USE_THEN "filt" ACCEPT_TAC;
    USE_THEN "hlen" ACCEPT_TAC;
    USE_THEN "hok" ACCEPT_TAC;
    USE_THEN "sim" ACCEPT_TAC;
    USE_THEN "d1" MP_TAC THEN REWRITE_TAC[ALL_APPEND; ALL; isDataElement_def] THEN MESON_TAC[];
    USE_THEN "d2" MP_TAC THEN REWRITE_TAC[ALL] THEN MESON_TAC[];
    USE_THEN "dr1" ACCEPT_TAC;
    USE_THEN "dr2" ACCEPT_TAC;
    USE_THEN "dr3" ACCEPT_TAC;
    USE_THEN "dr4" ACCEPT_TAC;
    USE_THEN "isref" ACCEPT_TAC;
    USE_THEN "bij" MP_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    REWRITE_TAC[gen_gc_heap_addresses_APPEND; heap_addresses_def; el_length_def];
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN MATCH_MP_TAC GC2AUX_FLOOKUP_scan THEN
    EXISTS_TAC `is_final (conf:B gen_gc_conf)
       (gc_state_REC (old:((A,B)heap_element)list) h1 (CONS (DataElement zs l d) t)
          r4 r3 r2 r1 a n ok heap hp0)` THEN
    USE_THEN "zs" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fl" (fun th -> REWRITE_TAC[REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] th]) THEN
    REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
    USE_THEN "len_a" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ARITH_TAC; GEN_TAC THEN ARITH_TAC]]);;

(* a case split of a gc_state into its fields, with the given names *)
let GC2AUX_STATE_TAC (names:string list) (tm:term) : tactic =
  let nch = (case_info_of_tyname "gc_state").ci_nchotomy in
  let th = ISPEC tm nch in
  let vs,_ = strip_exists (concl th) in
  let vs' = map2 (fun s v -> mk_var(s,type_of v)) names vs in
  MP_TAC th THEN
  DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN vs') SUBST_ALL_TAC);;

let GC2AUX_FIELDS = ["old";"h1";"h2";"r4";"r3";"r2";"r1";"a";"n";"ok";"heap";"hp0"];;

(* the facts of gc_inv by number (the order of gc_inv_def) *)
let GC2AUX_INV_CONJ n th =
  el n (CONJUNCTS (REWRITE_RULE[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF;
                                gc_state_FIELDS.ri_accessors] th));;

let gc_move_data_thm = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0 /\ gc_state_r3 state = [] /\ gc_state_r2 state = []
     ==> ?state'. gen_gc_gc_move_data conf state = state' /\
                  heap_map 0 (gc_state_heap state) SUBMAP heap_map 0 (gc_state_heap state') /\
                  gen_gc_gc_inv conf state' heap0 roots0 /\
                  gc_state_h2 state' = [] /\ gc_state_r3 state' = [] /\ gc_state_r2 state' = []`,
  MATCH_MP_TAC gen_gc_gc_move_data_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_conf`; `state:(A,B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`] THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv") (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  MP_TAC(ISPEC `h2:((A,B)heap_element)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `h:(A,B)heap_element`
    (X_CHOOSE_THEN `t:((A,B)heap_element)list` SUBST_ALL_TAC))) THEN
  CAKE_REWRITE_TAC[] THENL
   [EXISTS_TAC `gc_state_REC old h1 [] r4 [] [] r1 a n ok heap (hp0:((A,B)heap_element)list)` THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accessors; SUBMAP_REFL] THEN USE_THEN "inv" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(gen_gc_conf_limit (conf:B gen_gc_conf) <
                  heap_length (APPEND h1 (CONS h t):((A,B)heap_element)list))`
    (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "inv" (fun th -> MP_TAC(CONJ (GC2AUX_INV_CONJ 0 th) (GC2AUX_INV_CONJ 1 th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THEN
  CAKE_REWRITE_TAC[] THENL
   [USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 8) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 8) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    ALL_TAC] THEN
  SUBGOAL_THEN `!ptr (u:A). MEM (Pointer ptr u) zs
                  ==> isSomeDataOrForward (heap_lookup ptr (heap:((A,B)heap_element)list)) /\
                      reachable_addresses (roots0:(A heap_address)list)
                        (heap0:((A,B)heap_element)list) ptr` (LABEL_TAC "ptrs") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "inv" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_pointers_ok_REC) th))) THEN
      MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[MEM];
      USE_THEN "inv" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_nonfinal_reachable) th))) THEN
      MAP_EVERY EXISTS_TAC [`heap_length (h1:((A,B)heap_element)list)`;
        `zs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 0) THEN
      REWRITE_TAC[heap_length_APPEND; heap_length_CONS; el_length_def] THEN DISCH_TAC THEN
      REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX] THEN
      REWRITE_TAC[IN_UNION; gen_gc_heap_addresses_APPEND; heap_addresses_def; IN_INSERT;
                  ADD_CLAUSES] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "inv" (fun th -> MP_TAC(SPEC `zs:(A heap_address)list`
     (MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
        (ONCE_REWRITE_RULE[SWAP_FORALL_THM] gen_gc_gc_move_list_thm)) th))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN USE_THEN "ptrs" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(GC2AUX_LABEL_MOVE_RESULT `s1:(A,B)gc_state` "1") THEN
  USE_THEN "m1" (fun th -> REWRITE_TAC[th; pair_CASE; LET_DEF; LET_END_DEF]) THEN
  USE_THEN "m1" (MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  GC2AUX_STATE_TAC ["old1";"h11";"h21";"r41";"r31";"r21";"r11";"a1";"n1";"ok1";"heap1";"hp01"]
    `s1:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
      (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))))) THEN
  REWRITE_TAC[IS_PREFIX_DEF; IS_PREFIX_APPEND; APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `ext:((A,B)heap_element)list` SUBST_ALL_TAC) THEN
  REWRITE_TAC[K_THM; HD; TL; NOT_CONS_NIL] THEN
  USE_THEN "inv1" (fun th -> REWRITE_TAC[GC2AUX_INV_CONJ 4 th]) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`t:((A,B)heap_element)list`; `zs:(A heap_address)list`;
    `ADDR_MAP (heap_map1 (heap1:((A,B)heap_element)list)) (zs:(A heap_address)list)`;
    `l:num`; `d:B`;
    `gc_state_REC old1 h1 (CONS (DataElement zs l d) (APPEND t ext)) r41 [] [] r1 a1 n1 ok1
       heap1 (hp01:((A,B)heap_element)list)`]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM; HD; TL;
              NOT_CONS_NIL] THEN
  USE_THEN "m1" (fun th -> REWRITE_TAC[REWRITE_RULE[gc_state_FIELDS.ri_accessors] th]) THEN
  ANTS_TAC THENL
   [USE_THEN "inv" (fun th -> MP_TAC(CONJ (GC2AUX_INV_CONJ 0 th) (GC2AUX_INV_CONJ 1 th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]) THEN
  USE_THEN "inv1" (fun th -> REWRITE_TAC[GC2AUX_INV_CONJ 4 th]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC GC2AUX_gc_move_data_step_inv THEN EXISTS_TAC `ok1:bool` THEN
    USE_THEN "inv1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "in1" (ACCEPT_TAC o REWRITE_RULE[gc_state_FIELDS.ri_accessors]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(A,B)gc_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:(A,B)gc_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `heap_map 0 (heap1:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "sub1" (ACCEPT_TAC o REWRITE_RULE[gc_state_FIELDS.ri_accessors]));;

let GC2AUX_gc_move_refs_step_inv = prove
 (`!(conf:B gen_gc_conf) old h1 h2 r4 r3 t r1 a n ok heap hp0 heap0
    (roots0:(A heap_address)list) zs l (d:B).
     gen_gc_gc_inv conf
       (gc_state_REC old h1 h2 r4 r3 (CONS (DataElement zs l d) t) r1 a n ok heap hp0)
       heap0 roots0 /\
     (!ptr (u:A). MEM (Pointer ptr u) zs ==> ptr IN FDOM (heap_map 0 heap))
     ==> gen_gc_gc_inv conf
           (gc_state_REC old h1 h2 r4
              (APPEND r3 [DataElement (ADDR_MAP (heap_map1 heap) zs) l d]) t
              r1 a n ok heap hp0) heap0 roots0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> EVERY (map2 LABEL_TAC GC2AUX_INV_LABELS (CONJUNCTS th)))
    (LABEL_TAC "zs")) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "len_a" ACCEPT_TAC;
    USE_THEN "len_lim" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def] THEN
    ARITH_TAC;
    USE_THEN "filt" ACCEPT_TAC;
    USE_THEN "hlen" ACCEPT_TAC;
    USE_THEN "ok" ACCEPT_TAC;
    USE_THEN "hok" ACCEPT_TAC;
    USE_THEN "sim" ACCEPT_TAC;
    USE_THEN "d1" ACCEPT_TAC;
    USE_THEN "d2" ACCEPT_TAC;
    USE_THEN "dr1" ACCEPT_TAC;
    USE_THEN "dr2" MP_TAC THEN REWRITE_TAC[ALL] THEN MESON_TAC[];
    USE_THEN "dr3" MP_TAC THEN REWRITE_TAC[ALL_APPEND; ALL; isDataElement_def] THEN MESON_TAC[];
    USE_THEN "dr4" ACCEPT_TAC;
    USE_THEN "isref" MP_TAC THEN
    REWRITE_TAC[MEM_APPEND; MEM; heap_element_11] THEN MESON_TAC[];
    USE_THEN "bij" MP_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    REWRITE_TAC[gen_gc_heap_addresses_APPEND; heap_addresses_def; el_length_def;
                heap_length_APPEND; heap_length_CONS; heap_length_NIL];
    SUBGOAL_THEN
     `!X:(A,B)heap_element.
        APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3)
          (CONS X t)) r1 =
        APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3)
          (CONS X (APPEND t r1)) /\
        APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4)
          (APPEND r3 [X])) t) r1 =
        APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3)
          (CONS X (APPEND t r1))`
      (fun th -> REWRITE_TAC[th] THEN
                 USE_THEN "fl" (LABEL_TAC "fl'" o REWRITE_RULE[th])) THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
    MATCH_MP_TAC GC2AUX_FLOOKUP_scan THEN
    EXISTS_TAC `is_final (conf:B gen_gc_conf)
       (gc_state_REC (old:((A,B)heap_element)list) h1 h2 r4 r3 (CONS (DataElement zs l d) t)
          r1 a n ok heap hp0)` THEN
    USE_THEN "zs" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fl'" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
    USE_THEN "len_a" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def;
                gen_gc_heap_length_heap_expand] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; GEN_TAC THEN ASM_ARITH_TAC]]);;

let gc_move_refs_lemma = prove
 (`!(state:(A,B)gc_state) l n (b:B) xs' t state' (conf:B gen_gc_conf) heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0 /\
     gc_state_r2 state = CONS (DataElement l n b) t /\
     gen_gc_gc_move_list conf state l = (xs',state') /\
     (!ptr (u:A). MEM (Pointer ptr u) l
                  ==> isSomeDataOrForward (heap_lookup ptr (gc_state_heap state)) /\
                      reachable_addresses roots0 heap0 ptr)
     ==> gen_gc_gc_inv conf
           (gc_state_r2_fupd (combin_K t)
              (gc_state_r3_fupd (combin_K (APPEND (gc_state_r3 state') [DataElement xs' n b]))
                 state'))
           heap0 roots0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv") (CONJUNCTS_THEN2 (LABEL_TAC "r2")
    (CONJUNCTS_THEN2 (LABEL_TAC "mv") (LABEL_TAC "ptrs")))) THEN
  USE_THEN "mv" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                 MATCH_MP gen_gc_gc_move_list_IMP) THEN
  USE_THEN "r2" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(LABEL_TAC "r2'") THEN
  USE_THEN "inv" (fun th -> MP_TAC(SPEC `l:(A heap_address)list`
     (MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
        (ONCE_REWRITE_RULE[SWAP_FORALL_THM] gen_gc_gc_move_list_thm)) th))) THEN
  USE_THEN "ptrs" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(GC2AUX_LABEL_MOVE_RESULT `s1:(A,B)gc_state` "1") THEN
  USE_THEN "mv" (MP_TAC o SYM) THEN USE_THEN "m1" (fun th -> REWRITE_TAC[th; PAIR_EQ]) THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `s1:(A,B)gc_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accessors]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> rand(concl th) = `r21:((A,B)heap_element)list`)) THEN
  MATCH_MP_TAC GC2AUX_gc_move_refs_step_inv THEN ASM_REWRITE_TAC[]);;

let GC2AUX_r3_to_r1_inv = prove
 (`!(conf:B gen_gc_conf) old h1 h2 r4 r3 r1 a n ok heap hp0 heap0
    (roots0:(A heap_address)list).
     gen_gc_gc_inv conf (gc_state_REC old h1 h2 r4 r3 [] r1 a n ok heap hp0) heap0 roots0
     ==> gen_gc_gc_inv conf (gc_state_REC old h1 h2 r4 [] [] (APPEND r3 r1) a n ok heap hp0)
           heap0 roots0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!j. is_final (conf:B gen_gc_conf)
          (gc_state_REC old h1 h2 r4 [] [] (APPEND r3 r1) a n ok heap hp0) j <=>
        is_final conf (gc_state_REC (old:((A,B)heap_element)list) h1 h2 r4 r3 [] r1 a n ok
                         heap hp0) j`
    (fun th -> REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF;
                           gc_state_FIELDS.ri_accessors] THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors;
                heap_length_NIL] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC; ALL_APPEND; ALL] THEN
  REWRITE_TAC[CONJ_ACI]);;

let gc_move_refs_thm = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0
     ==> ?state'. gc_move_refs conf state = state' /\
                  heap_map 0 (gc_state_heap state) SUBMAP heap_map 0 (gc_state_heap state') /\
                  gen_gc_gc_inv conf state' heap0 roots0 /\
                  gc_state_r3 state' = [] /\ gc_state_r2 state' = [] /\
                  (0 < heap_length (gc_state_r3 state)
                   ==> heap_length (gc_state_r1 state) < heap_length (gc_state_r1 state'))`,
  MATCH_MP_TAC gc_move_refs_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_conf`; `state:(A,B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`] THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN DISCH_THEN(LABEL_TAC "inv") THEN
  ONCE_REWRITE_TAC[gc_move_refs_def] THEN REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  MP_TAC(ISPEC `r2:((A,B)heap_element)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `h:(A,B)heap_element`
    (X_CHOOSE_THEN `t:((A,B)heap_element)list` SUBST_ALL_TAC))) THEN
  CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[gc_state_FIELDS.ri_fupds; K_THM] THEN
    EXISTS_TAC `gc_state_REC old h1 h2 r4 [] [] (APPEND r3 r1) a n ok heap
                  (hp0:((A,B)heap_element)list)` THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accessors; SUBMAP_REFL; heap_length_APPEND] THEN
    CONJ_TAC THENL [MATCH_MP_TAC GC2AUX_r3_to_r1_inv THEN USE_THEN "inv" ACCEPT_TAC; ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THEN
  CAKE_REWRITE_TAC[] THENL
   [USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 10) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 10) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    ALL_TAC] THEN
  SUBGOAL_THEN `!ptr (u:A). MEM (Pointer ptr u) zs
                  ==> isSomeDataOrForward (heap_lookup ptr (heap:((A,B)heap_element)list)) /\
                      reachable_addresses (roots0:(A heap_address)list)
                        (heap0:((A,B)heap_element)list) ptr` (LABEL_TAC "ptrs") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "inv" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_pointers_ok_REC) th))) THEN
      MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[MEM];
      USE_THEN "inv" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_nonfinal_reachable) th))) THEN
      MAP_EVERY EXISTS_TAC
       [`heap_length (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3
                       :((A,B)heap_element)list)`;
        `zs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `heap_length (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3
                      :((A,B)heap_element)list) =
                    (a + n) + heap_length r4 + heap_length r3` ASSUME_TAC THENL
       [USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 0) THEN
        REWRITE_TAC[heap_length_APPEND; gen_gc_heap_length_heap_expand] THEN ARITH_TAC;
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors;
                        heap_length_CONS; el_length_def] THEN
        USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 0) THEN
        REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC;
        SUBGOAL_THEN
         `!x:(A,B)heap_element.
            APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4)
              r3) (CONS x t)) r1 =
            APPEND (APPEND (APPEND (APPEND (APPEND h1 h2) (heap_expand n)) r4) r3)
              (CONS x (APPEND t r1))` (fun th -> REWRITE_TAC[th; heap_lookup_PREFIX]) THEN
        REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_UNION; gen_gc_heap_addresses_APPEND; heap_addresses_def; IN_INSERT;
                    heap_length_APPEND]]];
    ALL_TAC] THEN
  USE_THEN "inv" (fun th -> MP_TAC(SPEC `zs:(A heap_address)list`
     (MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
        (ONCE_REWRITE_RULE[SWAP_FORALL_THM] gen_gc_gc_move_list_thm)) th))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN USE_THEN "ptrs" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(GC2AUX_LABEL_MOVE_RESULT `s1:(A,B)gc_state` "1") THEN
  USE_THEN "m1" (fun th -> REWRITE_TAC[th; pair_CASE; LET_DEF; LET_END_DEF]) THEN
  USE_THEN "m1" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                 MATCH_MP gen_gc_gc_move_list_IMP) THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `s1:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `gen_gc_gc_inv (conf:B gen_gc_conf)
      (gc_state_REC old1 h11 h21 r41
         (APPEND r31 [DataElement (ADDR_MAP (heap_map1 heap1) zs) l d]) t r1 a1 n1 ok1
         heap1 (hp01:((A,B)heap_element)list)) heap0 roots0` (LABEL_TAC "inv2") THENL
   [MP_TAC(ISPECL [`gc_state_REC old h1 h2 r4 r3 (CONS (DataElement zs l d) t) r1 a n ok heap
                      (hp0:((A,B)heap_element)list)`;
                   `zs:(A heap_address)list`; `l:num`; `d:B`;
                   `ADDR_MAP (heap_map1 (heap1:((A,B)heap_element)list)) (zs:(A heap_address)list)`;
                   `t:((A,B)heap_element)list`;
                   `gc_state_REC old1 h11 h21 r41 r31 r21 r1 a1 n1 ok1 heap1
                      (hp01:((A,B)heap_element)list)`;
                   `conf:B gen_gc_conf`; `heap0:((A,B)heap_element)list`;
                   `roots0:(A heap_address)list`] gc_move_refs_lemma) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "inv" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "m1" (fun th -> REWRITE_TAC[th; gc_state_FIELDS.ri_accessors]) THEN
    USE_THEN "ptrs" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`zs:(A heap_address)list`;
    `ADDR_MAP (heap_map1 (heap1:((A,B)heap_element)list)) (zs:(A heap_address)list)`;
    `l:num`; `d:B`; `t:((A,B)heap_element)list`;
    `gc_state_REC old1 h11 h21 r41 r31 r21 r1 a1 n1 ok1 heap1
       (hp01:((A,B)heap_element)list)`]) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  USE_THEN "m1" (fun th -> REWRITE_TAC[REWRITE_RULE[gc_state_FIELDS.ri_accessors] th]) THEN
  DISCH_THEN(MP_TAC o SPECL [`heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`]) THEN
  USE_THEN "inv2" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(A,B)gc_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:(A,B)gc_state` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `heap_map 0 (heap1:((A,B)heap_element)list)` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sub1" (ACCEPT_TAC o REWRITE_RULE[gc_state_FIELDS.ri_accessors]);
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def] THEN
    ARITH_TAC]);;

let gen_gc_gc_move_list_heap_length = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) state' xs ys.
     gen_gc_gc_move_list conf state xs = (ys,state')
     ==> heap_length (gc_state_h1 state) <= heap_length (gc_state_h1 state') /\
         heap_length (gc_state_r1 state) <= heap_length (gc_state_r1 state')`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  SIMP_TAC[LE_REFL]);;

let gc_move_data_heap_length = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) state'.
     Abbrev (state' = gen_gc_gc_move_data conf state)
     ==> heap_length (gc_state_h1 state) <= heap_length (gc_state_h1 state') /\
         heap_length (gc_state_r1 state) <= heap_length (gc_state_r1 state')`,
  REWRITE_TAC[marker_Abbrev_def] THEN
  REWRITE_TAC[MESON[] `(!y:C. y = f ==> P y) <=> P f`] THEN
  MATCH_MP_TAC gen_gc_gc_move_data_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  MP_TAC(ISPEC `gc_state_h2 (state:(A,B)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[LE_REFL])
    (X_CHOOSE_THEN `h:(A,B)heap_element` (X_CHOOSE_THEN `t:((A,B)heap_element)list`
      (LABEL_TAC "h2")))) THEN
  USE_THEN "h2" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; LE_REFL] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; LE_REFL] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))))) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`t:((A,B)heap_element)list`; `zs:(A heap_address)list`;
    `xs':(A heap_address)list`; `l:num`; `d:B`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; heap_length_APPEND] THEN ARITH_TAC);;

let gc_move_refs_heap_length = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) state'.
     gc_move_refs conf state = state'
     ==> heap_length (gc_state_h1 state) <= heap_length (gc_state_h1 state') /\
         heap_length (gc_state_r1 state) <= heap_length (gc_state_r1 state')`,
  REWRITE_TAC[MESON[] `(!y:C. f = y ==> P y) <=> P f`] THEN
  MATCH_MP_TAC gc_move_refs_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gc_move_refs_def] THEN
  MP_TAC(ISPEC `gc_state_r2 (state:(A,B)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[] THEN
               REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; heap_length_APPEND] THEN
               ARITH_TAC)
    (X_CHOOSE_THEN `h:(A,B)heap_element` (X_CHOOSE_THEN `t:((A,B)heap_element)list`
      (LABEL_TAC "r2")))) THEN
  USE_THEN "r2" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; LE_REFL] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))))) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`zs:(A heap_address)list`; `xs':(A heap_address)list`;
    `l:num`; `d:B`; `t:((A,B)heap_element)list`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; heap_length_APPEND] THEN ARITH_TAC);;

let GC2AUX_r4_to_r2_inv = prove
 (`!(conf:B gen_gc_conf) old h1 h2 h t r1 a n ok heap hp0 heap0
    (roots0:(A heap_address)list).
     gen_gc_gc_inv conf (gc_state_REC old h1 h2 (CONS h t) [] [] r1 a n ok heap hp0)
       heap0 roots0
     ==> gen_gc_gc_inv conf (gc_state_REC old h1 h2 [] [] (CONS h t) r1 a n ok heap hp0)
           heap0 roots0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!j. is_final (conf:B gen_gc_conf)
          (gc_state_REC old h1 h2 [] [] (CONS h t) r1 a n ok heap hp0) j <=>
        is_final conf (gc_state_REC (old:((A,B)heap_element)list) h1 h2 (CONS h t) [] [] r1
                         a n ok heap hp0) j`
    (fun th -> REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF;
                           gc_state_FIELDS.ri_accessors] THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors;
                heap_length_NIL] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC; ALL_APPEND; ALL] THEN
  REWRITE_TAC[CONJ_ACI]);;

let gc_move_loop_gc_inv = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) h t heap0 roots0.
     gen_gc_gc_inv conf state heap0 roots0 /\ gc_state_r2 state = [] /\
     gc_state_r4 state = CONS h t /\ gc_state_r3 state = []
     ==> gen_gc_gc_inv conf
           (gc_state_r4_fupd (combin_K []) (gc_state_r2_fupd (combin_K (CONS h t)) state)) heap0 roots0`,
  GEN_TAC THEN GEN_TAC THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  MATCH_MP_TAC GC2AUX_r4_to_r2_inv THEN ASM_REWRITE_TAC[]);;

let reachable_addresses_gc_inv_r4 = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) heap roots0 l n (b:B) t ptr (u:A).
     gen_gc_gc_inv conf state heap roots0 /\
     gc_state_r4 state = CONS (DataElement l n b) t /\ MEM (Pointer ptr u) l
     ==> reachable_addresses roots0 heap ptr`,
  GEN_TAC THEN GEN_TAC THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv") (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  USE_THEN "inv" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
    (MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_nonfinal_reachable) th))) THEN
  MAP_EVERY EXISTS_TAC
   [`a1 + n1:num`; `l:(A heap_address)list`; `n:num`; `b:B`; `u:A`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 0) THEN
  REWRITE_TAC[heap_length_APPEND] THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors;
                heap_length_CONS; el_length_def] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN
     `APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h11 h21) (heap_expand n1))
        (CONS (DataElement l n b) t)) r31) r21) r11 =
      APPEND (APPEND (APPEND h11 h21) (heap_expand n1))
        (CONS (DataElement l n b) (APPEND t (APPEND r31 (APPEND r21 r11))))
      :((A,B)heap_element)list` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
    MATCH_MP_TAC heap_lookup_LENGTH THEN
    REWRITE_TAC[heap_length_APPEND; gen_gc_heap_length_heap_expand] THEN ASM_ARITH_TAC;
    REWRITE_TAC[IN_UNION; APPEND; heap_addresses_def; IN_INSERT]]);;

(* gc_move_data makes progress: h1 grows *)
let GC2AUX_gc_move_data_progress = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) heap0 roots0 h t.
     gen_gc_gc_inv conf state heap0 roots0 /\ gc_state_r3 state = [] /\
     gc_state_r2 state = [] /\ gc_state_h2 state = CONS h t
     ==> heap_length (gc_state_h1 state) <
         heap_length (gc_state_h1 (gen_gc_gc_move_data conf state)) /\
         heap_length (gc_state_r1 state) <=
         heap_length (gc_state_r1 (gen_gc_gc_move_data conf state))`,
  GEN_TAC THEN GEN_TAC THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  MAP_EVERY X_GEN_TAC [`heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`;
                       `h:(A,B)heap_element`; `t:((A,B)heap_element)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv") (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(gen_gc_conf_limit (conf:B gen_gc_conf) <
                  heap_length (APPEND h1 (CONS h t):((A,B)heap_element)list))`
    (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "inv" (fun th -> MP_TAC(CONJ (GC2AUX_INV_CONJ 0 th) (GC2AUX_INV_CONJ 1 th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THEN
  CAKE_REWRITE_TAC[] THENL
   [USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 8) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 8) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))))) THEN
  MP_TAC(ISPECL [`conf:B gen_gc_conf`;
    `gc_state_ok_fupd (combin_K (gc_state_ok state' /\ ~(gc_state_h2 state' = []) /\
        HD (gc_state_h2 state') = DataElement zs l d))
      (gc_state_h2_fupd (combin_K (TL (gc_state_h2 state')))
        (gc_state_h1_fupd (combin_K (APPEND (gc_state_h1 state') [DataElement xs' l d]))
           (state':(A,B)gc_state)))`] gc_move_data_heap_length) THEN
  REWRITE_TAC[marker_Abbrev_def; MESON[] `(!y:C. y = f ==> P y) <=> P f`] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; heap_length_APPEND; heap_length_CONS;
              heap_length_NIL; el_length_def] THEN ARITH_TAC);;

(* gc_move_refs makes progress when r4 is not empty: r1 grows *)
let GC2AUX_gc_move_refs_progress = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) heap0 roots0 h t.
     gen_gc_gc_inv conf state heap0 roots0 /\ gc_state_r4 state = CONS h t /\
     gc_state_r3 state = [] /\ gc_state_r2 state = []
     ==> heap_length (gc_state_r1 state) <
         heap_length (gc_state_r1 (gc_move_refs conf
           (gc_state_r4_fupd (combin_K []) (gc_state_r2_fupd (combin_K (CONS h t)) state))))`,
  GEN_TAC THEN GEN_TAC THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  MAP_EVERY X_GEN_TAC [`heap0:((A,B)heap_element)list`; `roots0:(A heap_address)list`;
                       `h:(A,B)heap_element`; `t:((A,B)heap_element)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv") (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_fupds; K_THM] THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THENL
   [USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 12) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 12) THEN
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    ALL_TAC] THEN
  USE_THEN "inv" (LABEL_TAC "inv0" o MATCH_MP GC2AUX_r4_to_r2_inv) THEN
  ONCE_REWRITE_TAC[gc_move_refs_def] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN CAKE_REWRITE_TAC[] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `!ptr (u:A). MEM (Pointer ptr u) zs
                  ==> isSomeDataOrForward (heap_lookup ptr (heap:((A,B)heap_element)list)) /\
                      reachable_addresses (roots0:(A heap_address)list)
                        (heap0:((A,B)heap_element)list) ptr` (LABEL_TAC "ptrs") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "inv0" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_pointers_ok_REC) th))) THEN
      MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[MEM];
      USE_THEN "inv" (fun th -> MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
        (MATCH_MP (REWRITE_RULE[IMP_CONJ] reachable_addresses_gc_inv_r4) th))) THEN
      MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `l:num`; `d:B`;
                            `t:((A,B)heap_element)list`; `u:A`] THEN
      ASM_REWRITE_TAC[gc_state_FIELDS.ri_accessors]];
    ALL_TAC] THEN
  USE_THEN "inv0" (fun th -> MP_TAC(SPECL [`zs:(A heap_address)list`; `l:num`; `d:B`;
      `xs':(A heap_address)list`; `t:((A,B)heap_element)list`; `state':(A,B)gc_state`]
    (MATCH_MP (REWRITE_RULE[IMP_CONJ] gc_move_refs_lemma) th))) THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupdcanon] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(A,B)gc_state` STRIP_ASSUME_TAC o MATCH_MP gc_move_refs_thm) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; heap_length_APPEND; heap_length_CONS;
              heap_length_NIL; el_length_def] THEN ARITH_TAC);;

let gen_gc_gc_move_loop_thm = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) clock heap roots0.
     gen_gc_conf_limit conf <=
       clock + heap_length (gc_state_h1 state) + heap_length (gc_state_r1 state) /\
     gc_state_r2 state = [] /\ gc_state_r3 state = [] /\
     gen_gc_gc_inv conf state heap roots0
     ==> ?state'. gen_gc_gc_move_loop conf state clock = state' /\
                  heap_map 0 (gc_state_heap state) SUBMAP heap_map 0 (gc_state_heap state') /\
                  gen_gc_gc_inv conf state' heap roots0 /\
                  gc_state_h2 state' = [] /\ gc_state_r4 state' = [] /\
                  gc_state_r3 state' = [] /\ gc_state_r2 state' = []`,
  MATCH_MP_TAC gen_gc_gc_move_loop_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_conf`; `state:(A,B)gc_state`; `clock:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHr") (LABEL_TAC "IHd")) THEN
  MAP_EVERY X_GEN_TAC [`heap:((A,B)heap_element)list`; `roots0:(A heap_address)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lim") (CONJUNCTS_THEN2 (LABEL_TAC "r2")
    (CONJUNCTS_THEN2 (LABEL_TAC "r3") (LABEL_TAC "inv")))) THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_loop_def] THEN
  MP_TAC(ISPEC `gc_state_r4 (state:(A,B)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "r4") (X_CHOOSE_THEN `h:(A,B)heap_element`
    (X_CHOOSE_THEN `t:((A,B)heap_element)list` (LABEL_TAC "r4")))) THEN
  USE_THEN "r4" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THENL
   [(* r4 = [] *)
    MP_TAC(ISPEC `gc_state_h2 (state:(A,B)gc_state)` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "h2") (X_CHOOSE_THEN `h:(A,B)heap_element`
      (X_CHOOSE_THEN `t:((A,B)heap_element)list` (LABEL_TAC "h2")))) THEN
    USE_THEN "h2" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THENL
     [EXISTS_TAC `state:(A,B)gc_state` THEN ASM_REWRITE_TAC[SUBMAP_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `~(clock = 0)` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
     [DISCH_TAC THEN USE_THEN "lim" MP_TAC THEN
      USE_THEN "inv" (fun th -> MP_TAC(CONJ (GC2AUX_INV_CONJ 0 th) (GC2AUX_INV_CONJ 1 th))) THEN
      ASM_REWRITE_TAC[APPEND; APPEND_NIL; heap_length_APPEND; heap_length_CONS] THEN
      GC1AUX_EL_LENGTH_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`conf:B gen_gc_conf`; `state:(A,B)gc_state`; `heap:((A,B)heap_element)list`;
                   `roots0:(A heap_address)list`; `h:(A,B)heap_element`;
                   `t:((A,B)heap_element)list`] GC2AUX_gc_move_data_progress) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "prog") THEN
    USE_THEN "inv" (fun th -> MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] gc_move_data_thm) th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(A,B)gc_state` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "sub1") (CONJUNCTS_THEN2 (LABEL_TAC "inv1")
        (CONJUNCTS_THEN2 (LABEL_TAC "h21")
          (CONJUNCTS_THEN2 (LABEL_TAC "r31") (LABEL_TAC "r21"))))))) THEN
    USE_THEN "IHd" (MP_TAC o SPECL [`h:(A,B)heap_element`; `t:((A,B)heap_element)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`heap:((A,B)heap_element)list`; `roots0:(A heap_address)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [USE_THEN "lim" MP_TAC THEN USE_THEN "prog" MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:(A,B)gc_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s2:(A,B)gc_state` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBMAP_TRANS THEN
    EXISTS_TAC `heap_map 0 (gc_state_heap (s1:(A,B)gc_state))` THEN ASM_REWRITE_TAC[];
    (* r4 is not empty *)
    SUBGOAL_THEN `~(clock = 0)` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
     [DISCH_TAC THEN USE_THEN "lim" MP_TAC THEN
      USE_THEN "inv" (fun th -> MP_TAC(CONJ (GC2AUX_INV_CONJ 0 th) (GC2AUX_INV_CONJ 1 th))) THEN
      ASM_REWRITE_TAC[APPEND; APPEND_NIL; heap_length_APPEND; heap_length_CONS] THEN
      GC1AUX_EL_LENGTH_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`conf:B gen_gc_conf`; `state:(A,B)gc_state`; `heap:((A,B)heap_element)list`;
                   `roots0:(A heap_address)list`; `h:(A,B)heap_element`;
                   `t:((A,B)heap_element)list`] GC2AUX_gc_move_refs_progress) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "prog")] THEN
    MP_TAC(ISPECL [`conf:B gen_gc_conf`; `state:(A,B)gc_state`; `h:(A,B)heap_element`;
                   `t:((A,B)heap_element)list`; `heap:((A,B)heap_element)list`;
                   `roots0:(A heap_address)list`] gc_move_loop_gc_inv) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "inv0")] THEN
    MP_TAC(ISPECL [`conf:B gen_gc_conf`;
      `gc_state_r4_fupd (combin_K []) (gc_state_r2_fupd (combin_K (CONS h t)) (state:(A,B)gc_state))`;
      `gc_move_refs (conf:B gen_gc_conf)
         (gc_state_r4_fupd (combin_K []) (gc_state_r2_fupd (combin_K (CONS h t)) (state:(A,B)gc_state)))`]
      gc_move_refs_heap_length) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds] THEN DISCH_THEN(LABEL_TAC "hl") THEN
    REMOVE_THEN "IHr" (fun th -> USE_THEN "r4" (fun r4 ->
      LABEL_TAC "IHr" (REWRITE_RULE[r4] th))) THEN
    USE_THEN "inv0" (MP_TAC o MATCH_MP gc_move_refs_thm) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(A,B)gc_state` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "sub1") (CONJUNCTS_THEN2 (LABEL_TAC "inv1")
        (CONJUNCTS_THEN2 (LABEL_TAC "r31") (CONJUNCTS_THEN2 (LABEL_TAC "r21") (K ALL_TAC))))))) THEN
    USE_THEN "IHr" (MP_TAC o SPECL [`h:(A,B)heap_element`; `t:((A,B)heap_element)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`heap:((A,B)heap_element)list`; `roots0:(A heap_address)list`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "lim" MP_TAC THEN USE_THEN "prog" MP_TAC THEN
      USE_THEN "hl" MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:(A,B)gc_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s2:(A,B)gc_state` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBMAP_TRANS THEN
    EXISTS_TAC `heap_map 0 (gc_state_heap (s1:(A,B)gc_state))` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sub1" (ACCEPT_TAC o REWRITE_RULE[gc_state_FIELDS.ri_accfupds])]);;

let gen_gc_gc_inv_init = prove
 (`!(heap:((A,B)heap_element)list) (conf:B gen_gc_conf) (roots:(A heap_address)list).
     heap_ok heap (gen_gc_conf_limit conf)
     ==> gen_gc_gc_inv conf
           (gc_state_ok_fupd (combin_K (heap_length heap = gen_gc_conf_limit conf))
              (gc_state_n_fupd (combin_K (gen_gc_conf_limit conf))
                 (gc_state_heap_fupd (combin_K heap) empty_state))) heap roots`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[heap_ok_def] th)) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `0` o MATCH_MP heap_map_EMPTY) THEN
  ASM_REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; empty_state_def;
    gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM; APPEND; ALL; MEM;
    heap_length_NIL; ADD_CLAUSES; heap_addresses_def; UNION_EMPTY; FLOOKUP_DEF;
    NOT_IN_EMPTY; option_DISTINCT] THEN
  ASM_SIMP_TAC[FILTER_LEMMA; heaps_similar_REFL] THEN
  REWRITE_TAC[BIJ; INJ; SURJ; NOT_IN_EMPTY]);;

let gen_gc_gen_gc_thm = prove
 (`!(conf:B gen_gc_conf) (roots:(A heap_address)list) (heap:((A,B)heap_element)list).
     roots_ok roots heap /\ heap_ok heap (gen_gc_conf_limit conf)
     ==> ?state.
           gen_gc conf (roots,heap) = (ADDR_MAP (heap_map1 (gc_state_heap state)) roots,state) /\
           (!ptr u. MEM (Pointer ptr u) roots
                    ==> ptr IN FDOM (heap_map 0 (gc_state_heap state))) /\
           gen_gc_gc_inv conf state heap roots /\
           gc_state_h2 state = [] /\ gc_state_r4 state = [] /\
           gc_state_r3 state = [] /\ gc_state_r2 state = []`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rok") (LABEL_TAC "hok")) THEN
  USE_THEN "hok" (LABEL_TAC "inv0" o SPEC `roots:(A heap_address)list` o
                  MATCH_MP gen_gc_gc_inv_init) THEN
  USE_THEN "inv0" (fun th -> MP_TAC(SPEC `roots:(A heap_address)list`
     (MATCH_MP (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
        (ONCE_REWRITE_RULE[SWAP_FORALL_THM] gen_gc_gc_move_list_thm)) th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "rok" (MP_TAC o SPECL [`ptr:num`; `u:A`] o REWRITE_RULE[roots_ok_def]) THEN
      ASM_REWRITE_TAC[isSomeDataOrForward_def] THEN MESON_TAC[];
      REWRITE_TAC[reachable_addresses_def] THEN
      MAP_EVERY EXISTS_TAC [`u:A`; `ptr:num`] THEN ASM_REWRITE_TAC[RTC_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(GC2AUX_LABEL_MOVE_RESULT `s1:(A,B)gc_state` "1") THEN
  USE_THEN "m1" (MP_TAC o MATCH_MP gen_gc_gc_move_list_IMP) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; empty_state_def; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (K ALL_TAC))))) THEN
  MP_TAC(ISPECL [`conf:B gen_gc_conf`; `s1:(A,B)gc_state`; `gen_gc_conf_limit (conf:B gen_gc_conf)`;
                 `heap:((A,B)heap_element)list`; `roots:(A heap_address)list`]
         gen_gc_gc_move_loop_thm) THEN
  ASM_REWRITE_TAC[heap_length_NIL; ADD_CLAUSES; LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(A,B)gc_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:(A,B)gc_state` THEN
  USE_THEN "m1" (fun th -> ASM_REWRITE_TAC[gen_gc_def; LET_DEF; LET_END_DEF; th; pair_CASE]) THEN
  REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC gen_gc_ADDR_MAP_EQ THEN REWRITE_TAC[heap_map1_def] THEN
    USE_THEN "in1" MP_TAC THEN
    UNDISCH_TAC `heap_map 0 (gc_state_heap (s1:(A,B)gc_state)) SUBMAP
                 heap_map 0 (gc_state_heap (s2:(A,B)gc_state))` THEN
    REWRITE_TAC[SUBMAP_DEF] THEN MESON_TAC[];
    USE_THEN "in1" MP_TAC THEN
    UNDISCH_TAC `heap_map 0 (gc_state_heap (s1:(A,B)gc_state)) SUBMAP
                 heap_map 0 (gc_state_heap (s2:(A,B)gc_state))` THEN
    REWRITE_TAC[SUBMAP_DEF] THEN MESON_TAC[]]);;

let gen_gc_LESS_IMP_heap_lookup = prove
 (`!xs j ys:((A,B)heap_element)list.
     j < heap_length xs ==> heap_lookup j (APPEND xs ys) = heap_lookup j xs`,
  REWRITE_TAC[gc_shared_LESS_IMP_heap_lookup]);;

(* HOL4: heap_lookup_IMP_heap_addresses_GEN specialised to the address 0 *)
let heap_lookup_IMP_heap_addresses = prove
 (`!xs (x:(A,B)heap_element) j.
     heap_lookup j xs = SOME x ==> j IN heap_addresses 0 xs`,
  MESON_TAC[heap_lookup_IMP_heap_addresses_GEN; ADD_CLAUSES]);;

let heap_lookup_AND_APPEND_IMP = prove
 (`!xs n ys (d:(A,B)heap_element) d1.
     heap_lookup n xs = SOME d /\ heap_lookup n (APPEND xs ys) = SOME d1 ==> d1 = d`,
  MESON_TAC[gc_shared_heap_lookup_EXTEND; option_INJ]);;

let heap_lookup_AND_PREPEND_IMP = prove
 (`!n xs ys (d:(A,B)heap_element) d1.
     heap_lookup n ys = SOME d /\
     heap_lookup (heap_length xs + n) (APPEND xs ys) = SOME d1
     ==> d1 = d`,
  MESON_TAC[GC2AUX_heap_lookup_middle; APPEND_NIL; option_INJ]);;

let MEM_heap_expand_FALSE = prove
 (`!n (xs:(A heap_address)list) l (d:B).
     ~(MEM (DataElement xs l d) (heap_expand n))`,
  REWRITE_TAC[heap_expand_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MEM; heap_element_distinct]);;

let FILTER_isForward_heap_expand_lemma = prove
 (`!n. FILTER isForwardPointer (heap_expand n:((A,B)heap_element)list) = []`,
  GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[FILTER; isForwardPointer_def]);;

let heap_lookup_CONS_IMP = prove
 (`!j ys (z:(A,B)heap_element) x.
     heap_lookup j ys = SOME z ==> heap_lookup (j + heap_length [x]) (CONS x ys) = SOME z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[heap_lookup_def; heap_length_CONS; heap_length_NIL; ADD_CLAUSES] THEN
  GC1AUX_EL_LENGTH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= e ==> ~(j + e = 0) /\ ~(j + e < e) /\ (j + e) - e = j`]);;

let heap_lookup_PREPEND_EXTEND = prove
 (`!xs j ys (z:(A,B)heap_element).
     heap_lookup j ys = SOME z ==> heap_lookup (heap_length xs + j) (APPEND xs ys) = SOME z`,
  MESON_TAC[GC2AUX_heap_lookup_middle; APPEND_NIL]);;

(* a final element at an address of the invariant only points to data *)
(* elements of the new heap                                             *)
let GC2AUX_final_ptrs = prove
 (`!(conf:B gen_gc_conf) old h1 h2 r4 r3 r2 r1 a n ok heap hp0 heap0
    (roots0:(A heap_address)list) j xs l (d:B) ptr (u:A).
     gen_gc_gc_inv conf (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok heap hp0) heap0 roots0 /\
     j IN heap_addresses 0 (APPEND h1 h2) UNION
          heap_addresses (a + n) (APPEND (APPEND (APPEND r4 r3) r2) r1) /\
     heap_lookup j (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND h1 h2)
          (heap_expand n)) r4) r3) r2) r1) = SOME (DataElement xs l d) /\
     is_final conf (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok heap hp0) j /\
     MEM (Pointer ptr u) xs
     ==> isSomeDataElement (heap_lookup ptr (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
           h1 h2) (heap_expand n)) r4) r3) r2) r1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> EVERY (map2 LABEL_TAC GC2AUX_INV_LABELS (CONJUNCTS th)))
    (CONJUNCTS_THEN2 (LABEL_TAC "jin") (CONJUNCTS_THEN2 (LABEL_TAC "lk")
      (CONJUNCTS_THEN2 (LABEL_TAC "fin") (LABEL_TAC "memp"))))) THEN
  USE_THEN "jin" (fun th -> USE_THEN "bij" (fun th2 ->
    MP_TAC(MATCH_MP BIJ_IMP_FLOOKUP_SOME (CONJ th2 th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (fun th -> USE_THEN "fl" (MP_TAC o C MATCH_MP th))) THEN
  USE_THEN "fin" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs':(A heap_address)list` (X_CHOOSE_THEN `l':num`
    (X_CHOOSE_THEN `d':B` (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ptrs"))))))) THEN
  USE_THEN "lk" (fun th -> REWRITE_TAC[th; option_INJ; heap_element_11]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (K ALL_TAC)) THEN
  USE_THEN "memp" (X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC o MATCH_MP MEM_ADDR_MAP) THEN
  SUBGOAL_THEN `FLOOKUP (heap_map 0 (heap:((A,B)heap_element)list)) y = SOME ptr`
    (fun th -> USE_THEN "fl" (MP_TAC o C MATCH_MP th)) THENL
   [REWRITE_TAC[FLOOKUP_DEF] THEN
    USE_THEN "ptrs" (MP_TAC o SPECL [`y:num`; `u:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `ptr:num`)) THEN
    REWRITE_TAC[heap_map1_def];
    ALL_TAC] THEN
  REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[]);;

let gen_gc_ok = prove
 (`!(conf:B gen_gc_conf) (roots:(A heap_address)list) (heap:((A,B)heap_element)list).
     roots_ok roots heap /\ heap_ok heap (gen_gc_conf_limit conf)
     ==> ?state roots' heap'.
           heap' = APPEND (APPEND (gc_state_h1 state) (heap_expand (gc_state_n state)))
                     (gc_state_r1 state) /\
           gen_gc conf (roots,heap) = (roots',state) /\
           gc_state_ok state /\
           gc_state_a state = heap_length (gc_state_h1 state) /\
           roots_ok roots' heap' /\
           heap_ok heap' (gen_gc_conf_limit conf)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP gen_gc_gen_gc_thm) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(A,B)gc_state` MP_TAC) THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `s:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in")
    (CONJUNCTS_THEN2 (LABEL_TAC "inv") (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`gc_state_REC old1 h11 [] [] [] [] r11 a1 n1 ok1 heap1 (hp01:((A,B)heap_element)list)`;
    `ADDR_MAP (heap_map1 (heap1:((A,B)heap_element)list)) (roots:(A heap_address)list)`;
    `APPEND (APPEND h11 (heap_expand n1)) (r11:((A,B)heap_element)list)`] THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  USE_THEN "inv" (fun th -> MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_final_ptrs) th)) THEN
  REWRITE_TAC[APPEND_NIL; APPEND; is_final_def; LET_DEF; LET_END_DEF;
              gc_state_FIELDS.ri_accessors; heap_length_NIL; ADD_CLAUSES] THEN
  DISCH_THEN(LABEL_TAC "fp" o REWRITE_RULE[IMP_IMP]) THEN
  USE_THEN "inv" (LABEL_TAC "fl" o REWRITE_RULE[APPEND_NIL; APPEND] o GC2AUX_INV_CONJ 15) THEN
  USE_THEN "inv" (LABEL_TAC "lena" o REWRITE_RULE[APPEND_NIL] o GC2AUX_INV_CONJ 0) THEN
  USE_THEN "inv" (fun th -> REWRITE_TAC[GC2AUX_INV_CONJ 4 th]) THEN
  USE_THEN "lena" (fun th -> REWRITE_TAC[GSYM th]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[roots_ok_def] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC o MATCH_MP MEM_ADDR_MAP) THEN
    SUBGOAL_THEN `FLOOKUP (heap_map 0 (heap1:((A,B)heap_element)list)) y = SOME ptr`
      (fun th -> USE_THEN "fl" (MP_TAC o C MATCH_MP th)) THENL
     [REWRITE_TAC[FLOOKUP_DEF] THEN
      USE_THEN "in" (MP_TAC o SPECL [`y:num`; `u:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `ptr:num`)) THEN
      REWRITE_TAC[heap_map1_def];
      ALL_TAC] THEN
    REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[heap_ok_def] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "inv" (MP_TAC o GC2AUX_INV_CONJ 1) THEN
    USE_THEN "lena" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_NIL; APPEND_NIL; APPEND;
                gen_gc_heap_length_heap_expand] THEN ARITH_TAC;
    REWRITE_TAC[FILTER_APPEND; FILTER_isForward_heap_expand_lemma; APPEND_NIL; APPEND] THEN
    USE_THEN "inv" (fun th -> REWRITE_TAC[APPEND;
      MATCH_MP EVERY_isDataElement_IMP_LEMMA (GC2AUX_INV_CONJ 7 th);
      MATCH_MP EVERY_isDataElement_IMP_LEMMA (GC2AUX_INV_CONJ 9 th)]);
    REWRITE_TAC[MEM_APPEND; MEM_heap_expand_FALSE] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `j:num` o MATCH_MP MEM_IMP_heap_lookup) THEN
    USE_THEN "fp" MATCH_MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`j:num`; `xs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        MATCH_MP_TAC heap_lookup_IMP_heap_addresses THEN
        EXISTS_TAC `DataElement xs l d:(A,B)heap_element` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM APPEND_ASSOC] THEN
        MATCH_MP_TAC gc_shared_heap_lookup_EXTEND THEN ASM_REWRITE_TAC[];
        DISJ1_TAC THEN MATCH_MP_TAC heap_lookup_LESS THEN
        EXISTS_TAC `DataElement xs l d:(A,B)heap_element` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      MAP_EVERY EXISTS_TAC [`(a1 + n1) + j:num`; `xs:(A heap_address)list`; `l:num`; `d:B`;
                            `u:A`] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
        MATCH_MP_TAC heap_lookup_IMP_heap_addresses_GEN THEN
        EXISTS_TAC `DataElement xs l d:(A,B)heap_element` THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `a1 + n1 = heap_length (APPEND h11 (heap_expand n1):((A,B)heap_element)list)`
          SUBST1_TAC THENL
         [USE_THEN "lena" (fun th -> REWRITE_TAC[heap_length_APPEND;
                                                gen_gc_heap_length_heap_expand; th]);
          MATCH_MP_TAC heap_lookup_PREPEND_EXTEND THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[LE_ADD];
        ASM_REWRITE_TAC[]]]]);;

let IN_heap_addresses_LESS = prove
 (`!heap n k. n IN heap_addresses k (heap:((A,B)heap_element)list)
              ==> k <= n /\ n < k + heap_length heap`,
  MESON_TAC[heap_addresses_LESS; heap_addresses_LESS_heap_length]);;

let gen_gc_heap_lookup_EXTEND = prove
 (`!xs n ys (x:(A,B)heap_element).
     heap_lookup n xs = SOME x ==> heap_lookup n (APPEND xs ys) = SOME x`,
  REWRITE_TAC[gc_shared_heap_lookup_EXTEND]);;

(* helpers for gen_gc_related: after the collection every address of the *)
(* target set is final, and every data element of the new heap is at an  *)
(* address of the target set                                              *)

let GC2AUX_final_S = prove
 (`!(conf:B gen_gc_conf) old h1 r1 a n ok heap hp0 heap0 (roots0:(A heap_address)list) j.
     gen_gc_gc_inv conf (gc_state_REC old h1 [] [] [] [] r1 a n ok heap hp0) heap0 roots0 /\
     j IN heap_addresses 0 h1 UNION heap_addresses (a + n) r1
     ==> is_final conf (gc_state_REC old h1 [] [] [] [] r1 a n ok heap hp0) j`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[is_final_def; LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors;
              heap_length_NIL; ADD_CLAUSES; IN_UNION] THEN
  MESON_TAC[IN_heap_addresses_LESS; ADD_CLAUSES]);;

let GC2AUX_lookup_in_S = prove
 (`!h1 n r1 x (xs:(A heap_address)list) l (d:B).
     heap_lookup x (APPEND (APPEND h1 (heap_expand n)) r1) = SOME (DataElement xs l d)
     ==> x IN heap_addresses 0 h1 UNION heap_addresses (heap_length h1 + n) r1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; IN_UNION] THEN
  ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN COND_CASES_TAC THENL
   [DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC heap_lookup_IMP_heap_addresses THEN
    EXISTS_TAC `DataElement xs l d:(A,B)heap_element` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
  REWRITE_TAC[gen_gc_heap_length_heap_expand] THEN COND_CASES_TAC THEN
  REWRITE_TAC[GC2AUX_heap_lookup_heap_expand] THEN DISCH_TAC THEN DISJ2_TAC THEN
  SUBGOAL_THEN `x = (heap_length (h1:((A,B)heap_element)list) + n) +
                    ((x - heap_length h1) - n)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC heap_lookup_IMP_heap_addresses_GEN THEN
  EXISTS_TAC `DataElement xs l d:(A,B)heap_element` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let gen_gc_related = prove
 (`!(conf:B gen_gc_conf) (roots:(A heap_address)list) (heap:((A,B)heap_element)list).
     roots_ok roots heap /\ heap_ok heap (gen_gc_conf_limit conf)
     ==> ?state f.
           gen_gc conf (roots,heap) = (ADDR_MAP (FAPPLY f) roots,state) /\
           FDOM f = reachable_addresses roots heap /\
           FRANGE f = {a | isSomeDataElement (heap_lookup a
                             (APPEND (APPEND (gc_state_h1 state)
                                (heap_expand (gc_state_n state))) (gc_state_r1 state)))} /\
           heap_length (APPEND (gc_state_h1 state) (gc_state_r1 state)) =
             heap_length (heap_filter (FDOM f) heap) /\
           gc_related f heap (APPEND (APPEND (gc_state_h1 state)
                                (heap_expand (gc_state_n state))) (gc_state_r1 state)) /\
           ALL isDataElement (APPEND (gc_state_h1 state) (gc_state_r1 state))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP gen_gc_gen_gc_thm) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(A,B)gc_state` MP_TAC) THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `s:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in")
    (CONJUNCTS_THEN2 (LABEL_TAC "inv") (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`gc_state_REC old1 h11 [] [] [] [] r11 a1 n1 ok1 heap1 (hp01:((A,B)heap_element)list)`;
    `heap_map 0 (heap1:((A,B)heap_element)list)`] THEN
  ASM_REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  SUBGOAL_THEN `FAPPLY (heap_map 0 (heap1:((A,B)heap_element)list)) = heap_map1 heap1`
    SUBST1_TAC THENL [REWRITE_TAC[heap_map1_def; FUN_EQ_THM]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  USE_THEN "inv" (LABEL_TAC "fin" o MATCH_MP (REWRITE_RULE[IMP_CONJ] GC2AUX_final_S)) THEN
  USE_THEN "inv" (fun th -> EVERY (map2 LABEL_TAC GC2AUX_INV_LABELS
    (CONJUNCTS (REWRITE_RULE[gen_gc_gc_inv_def; LET_DEF; LET_END_DEF; APPEND; APPEND_NIL;
                             gc_state_FIELDS.ri_accessors] th)))) THEN
  SUBGOAL_THEN
   `!i. i IN FDOM (heap_map 0 (heap1:((A,B)heap_element)list))
        ==> ?xs l d. heap_lookup i heap = SOME (DataElement xs l d) /\
                     heap_lookup (FAPPLY (heap_map 0 heap1) i)
                       (APPEND (APPEND h11 (heap_expand n1)) r11) =
                       SOME (DataElement (ADDR_MAP (heap_map1 heap1) xs) l (d:B)) /\
                     reachable_addresses (roots:(A heap_address)list) heap i /\
                     !ptr (u:A). MEM (Pointer ptr u) xs ==> ptr IN FDOM (heap_map 0 heap1)`
   (LABEL_TAC "fl2") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FLOOKUP (heap_map 0 (heap1:((A,B)heap_element)list)) i =
                  SOME (FAPPLY (heap_map 0 heap1) i)`
      (fun th -> USE_THEN "fl" (MP_TAC o C MATCH_MP th)) THENL
     [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
    SUBGOAL_THEN `is_final (conf:B gen_gc_conf)
        (gc_state_REC old1 h11 [] [] [] [] r11 a1 n1 ok1 heap1 (hp01:((A,B)heap_element)list))
        (FAPPLY (heap_map 0 heap1) i)` (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fin" MATCH_MP_TAC THEN
    USE_THEN "bij" (MP_TAC o CONJUNCT1 o CONJUNCT1 o REWRITE_RULE[BIJ; INJ]) THEN
    REWRITE_TAC[heap_map1_def] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FAPPLY (heap_map 0 (heap1:((A,B)heap_element)list)) = heap_map1 heap1`
    (fun th -> REWRITE_TAC[th] THEN
               USE_THEN "fl2" (LABEL_TAC "fl3" o REWRITE_RULE[th]))
  THENL [REWRITE_TAC[heap_map1_def; FUN_EQ_THM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the domain is the reachable addresses *)
    REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `i:num` THEN GEN_REWRITE_TAC RAND_CONV [IN] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN USE_THEN "fl3" (MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
      REWRITE_TAC[reachable_addresses_def] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A` (X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `!x y. RTC (gc_edge (heap:((A,B)heap_element)list)) x y /\
                          x IN FDOM (heap_map 0 (heap1:((A,B)heap_element)list))
                          ==> y IN FDOM (heap_map 0 heap1)` MATCH_MP_TAC THENL
       [REWRITE_TAC[GSYM IMP_IMP] THEN MATCH_MP_TAC RTC_INDUCT THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[gc_edge_def] THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
              DISCH_THEN(X_CHOOSE_THEN `xs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
                (X_CHOOSE_THEN `d:B` (X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC)))) THEN
              DISCH_TAC THEN USE_THEN "fl3" (MP_TAC o SPEC `p:num`) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
              ASM_REWRITE_TAC[option_INJ; heap_element_11] THEN
              DISCH_THEN(X_CHOOSE_THEN `xs':(A heap_address)list` (X_CHOOSE_THEN `l':num`
                (X_CHOOSE_THEN `d':B` STRIP_ASSUME_TAC))) THEN
              ASM_MESON_TAC[];
          REWRITE_TAC[];
          MESON_TAC[]];
        EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[] THEN
          USE_THEN "in" MATCH_MP_TAC THEN EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[]]];
    (* the range *)
    REWRITE_TAC[EXTENSION; FRANGE_DEF; IN_ELIM_THM] THEN X_GEN_TAC `y:num` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:num` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
      USE_THEN "fl3" (MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[isSomeDataElement_def; heap_map1_def] THEN MESON_TAC[];
      REWRITE_TAC[isSomeDataElement_def] THEN
      DISCH_THEN(X_CHOOSE_THEN `ys:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` (MP_TAC o MATCH_MP GC2AUX_lookup_in_S)))) THEN
      USE_THEN "len_a" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      USE_THEN "bij" (MP_TAC o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[BIJ; SURJ]) THEN
      DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[heap_map1_def]];
    (* the lengths *)
    SUBGOAL_THEN
     `heap_length (APPEND h11 r11) =
      heap_length (heap_filter (heap_addresses 0 h11 UNION heap_addresses (a1 + n1) r11)
                     (APPEND (APPEND h11 (heap_expand n1)) (r11:((A,B)heap_element)list)))`
      SUBST1_TAC THENL
     [REWRITE_TAC[heap_filter_def; GSYM APPEND_ASSOC; heap_filter_aux_APPEND; ADD_CLAUSES;
                    heap_filter_aux_heap_addresses_UNION; gen_gc_heap_length_heap_expand] THEN
        USE_THEN "len_a" (fun th -> REWRITE_TAC[GSYM th]) THEN
        ONCE_REWRITE_TAC[UNION_COMM] THEN
        REWRITE_TAC[heap_filter_aux_heap_addresses_UNION] THEN
      REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
        REWRITE_TAC[heap_filter_aux_def; APPEND] THEN
        SUBGOAL_THEN `~(heap_length (h11:((A,B)heap_element)list) IN
                        heap_addresses (heap_length h11 + n1) (r11:((A,B)heap_element)list) UNION
                        heap_addresses 0 h11)`
          (fun th -> REWRITE_TAC[th; APPEND]) THEN
        REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
         [MATCH_MP_TAC NOT_IN_heap_addresses_less THEN ASM_ARITH_TAC;
          MP_TAC(ISPECL [`h11:((A,B)heap_element)list`; `0`] NOT_IN_heap_addresses) THEN
          REWRITE_TAC[ADD_CLAUSES]];
      MATCH_MP_TAC heap_length_heap_filter_eq THEN
      EXISTS_TAC `heap_map1 (heap1:((A,B)heap_element)list)` THEN
      ASM_REWRITE_TAC[FDOM_FINITE; FINITE_UNION; FINITE_heap_addresses] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "fl3" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]];
    (* gc_related *)
    SUBGOAL_THEN `FAPPLY (heap_map 0 (heap1:((A,B)heap_element)list)) = heap_map1 heap1`
      (fun th -> REWRITE_TAC[gc_related_def; th]) THENL
     [REWRITE_TAC[heap_map1_def; FUN_EQ_THM]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INJ; IN_ELIM_THM] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:num` THEN DISCH_TAC THEN USE_THEN "fl3" (MP_TAC o SPEC `x:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
        USE_THEN "bij" (ACCEPT_TAC o CONJUNCT2 o CONJUNCT1 o REWRITE_RULE[BIJ; INJ])];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "fl3" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "fl3" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[option_INJ; heap_element_11] THEN
      DISCH_THEN(X_CHOOSE_THEN `xs':(A heap_address)list` (X_CHOOSE_THEN `l':num`
        (X_CHOOSE_THEN `d':B` STRIP_ASSUME_TAC))) THEN
      RVEQ_TAC THEN ASM_REWRITE_TAC[]];
    USE_THEN "d1" (fun th -> USE_THEN "dr1" (fun th2 -> REWRITE_TAC[ALL_APPEND; th; th2]))]);;

let gen_gc_gc_forward_ptr_ok = prove
 (`!(heap:((A,B)heap_element)list) n a (d:A) c x.
     gc_forward_ptr n heap a d c = (x,T) ==> c`,
  MESON_TAC[gc_shared_gc_forward_ptr_ok]);;

let gen_gc_gc_move_ok = prove
 (`!(conf:B gen_gc_conf) (state:(A,B)gc_state) x x' state'.
     gen_gc_gc_move conf state x = (x',state') /\ gc_state_ok state' ==> gc_state_ok state`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN REPEAT STRIP_TAC THEN GVS[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_forward_ptr_ok) THEN SIMP_TAC[]);;

let gen_gc_gc_move_list_ok = prove
 (`!xs xs' (state:(A,B)gc_state) state' (conf:B gen_gc_conf).
     gen_gc_gc_move_list conf state xs = (xs',state') /\ gc_state_ok state'
     ==> gc_state_ok state`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC gen_gc_gc_move_ok THEN
  MAP_EVERY EXISTS_TAC [`conf:B gen_gc_conf`; `h:A heap_address`; `x':A heap_address`;
                        `state'':(A,B)gc_state`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* the case splits of the scanning functions on the first element of a list *)
let GC2AUX_LIST_CASES_TAC (tm:term) nil_tac : tactic =
  MP_TAC(ISPEC tm list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[] THEN nil_tac)
    (X_CHOOSE_THEN `h:(A,B)heap_element` (X_CHOOSE_THEN `t:((A,B)heap_element)list`
      (LABEL_TAC "hd")))) THEN
  USE_THEN "hd" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[];;

let GC2AUX_ELEMENT_CASES_TAC : tactic =
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THEN
  CAKE_REWRITE_TAC[];;

let gc_move_data_ok = prove
 (`!(conf:B gen_gc_conf) (s:(A,B)gc_state).
     gc_state_ok (gen_gc_gc_move_data conf s) ==> gc_state_ok s`,
  MATCH_MP_TAC gen_gc_gc_move_data_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)` ALL_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`t:((A,B)heap_element)list`; `zs:(A heap_address)list`;
    `xs':(A heap_address)list`; `l:num`; `d:B`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC gen_gc_gc_move_list_ok THEN
  MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `xs':(A heap_address)list`;
    `state':(A,B)gc_state`; `conf:B gen_gc_conf`] THEN ASM_MESON_TAC[]);;

let gen_gc_gc_move_data_h2 = prove
 (`!(conf:B gen_gc_conf) (s:(A,B)gc_state).
     gc_state_ok (gen_gc_gc_move_data conf s)
     ==> gc_state_h2 (gen_gc_gc_move_data conf s) = []`,
  MATCH_MP_TAC gen_gc_gc_move_data_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)` (ASM_REWRITE_TAC[]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`t:((A,B)heap_element)list`; `zs:(A heap_address)list`;
    `xs':(A heap_address)list`; `l:num`; `d:B`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[]);;

let gc_move_refs_ok = prove
 (`!(conf:B gen_gc_conf) (s:(A,B)gc_state).
     gc_state_ok (gc_move_refs conf s) ==> gc_state_ok s`,
  MATCH_MP_TAC gc_move_refs_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gc_move_refs_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_r2 (state:(A,B)gc_state)`
    (REWRITE_TAC[gc_state_FIELDS.ri_accfupds]) THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`zs:(A heap_address)list`; `xs':(A heap_address)list`;
    `l:num`; `d:B`; `t:((A,B)heap_element)list`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC gen_gc_gc_move_list_ok THEN
  MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `xs':(A heap_address)list`;
    `state':(A,B)gc_state`; `conf:B gen_gc_conf`] THEN ASM_MESON_TAC[]);;

let gen_gc_gc_move_loop_ok = prove
 (`!(conf:B gen_gc_conf) (s:(A,B)gc_state) c.
     gc_state_ok (gen_gc_gc_move_loop conf s c) ==> gc_state_ok s`,
  MATCH_MP_TAC gen_gc_gc_move_loop_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_conf`; `state:(A,B)gc_state`; `clock:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IHr") (LABEL_TAC "IHd")) THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_loop_def] THEN
  MP_TAC(ISPEC `gc_state_r4 (state:(A,B)gc_state)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "r4") (X_CHOOSE_THEN `h:(A,B)heap_element`
    (X_CHOOSE_THEN `t:((A,B)heap_element)list` (LABEL_TAC "r4")))) THEN
  USE_THEN "r4" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THENL
   [MP_TAC(ISPEC `gc_state_h2 (state:(A,B)gc_state)` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "h2") (X_CHOOSE_THEN `h:(A,B)heap_element`
      (X_CHOOSE_THEN `t:((A,B)heap_element)list` (LABEL_TAC "h2")))) THEN
    USE_THEN "h2" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
    USE_THEN "IHd" (MP_TAC o SPECL [`h:(A,B)heap_element`; `t:((A,B)heap_element)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MESON_TAC[gc_move_data_ok];
    COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
    USE_THEN "IHr" (MP_TAC o SPECL [`h:(A,B)heap_element`; `t:((A,B)heap_element)list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "r4" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(fun ih -> DISCH_THEN(MP_TAC o MATCH_MP gc_move_refs_ok o MATCH_MP ih)) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds]]);;

let gen_gc_gc_move_list_length = prove
 (`!xs xs' (state:(A,B)gc_state) state' (conf:B gen_gc_conf).
     gen_gc_gc_move_list conf state xs = (xs',state') ==> LENGTH xs' = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_gc_move_list_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let gen_gc_LENGTH = prove
 (`!(c:B gen_gc_conf) (xs:(A heap_address)list) (heap:((A,B)heap_element)list) ys s.
     gen_gc c (xs,heap) = (ys,s) ==> LENGTH ys = LENGTH xs`,
  REWRITE_TAC[gen_gc_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP gen_gc_gc_move_list_length));;

let gen_gc_a = prove
 (`!(c:B gen_gc_conf) (xs:(A heap_address)list) (heap:((A,B)heap_element)list) ys s1.
     gen_gc c (xs,heap) = (ys,s1) /\ gc_state_ok s1 /\
     roots_ok xs heap /\ heap_ok heap (gen_gc_conf_limit c)
     ==> gc_state_a s1 = heap_length (gc_state_h1 s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:B gen_gc_conf`; `xs:(A heap_address)list`;
                 `heap:((A,B)heap_element)list`] gen_gc_gen_gc_thm) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(A,B)gc_state` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s1:(A,B)gc_state = s`)) THEN
  FIRST_ASSUM(MP_TAC o GC2AUX_INV_CONJ 0 o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "gen_gc_gc_inv" with _ -> false)) THEN
  ASM_REWRITE_TAC[APPEND_NIL] THEN MESON_TAC[]);;
