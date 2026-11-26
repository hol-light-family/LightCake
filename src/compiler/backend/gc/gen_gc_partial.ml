(* ========================================================================= *)
(* gen_gc_partial: port of HOL4 compiler/backend/gc/gen_gc_partialScript.sml *)
(* (CakeML v3479).  The minor collection of the generational copying        *)
(* garbage collector.                                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;

let gen_gc_partial_conf_FIELDS = cake_record "gen_gc_partial_conf"
  ["limit","num";        (* size of heap *)
   "isRef","A->bool";
   "gen_start","num";    (* start of generation *)
   "refs_start","num"];; (* start of references *)

let gen_gc_partial_gc_move_def = cake_def
  `(gen_gc_partial_gc_move (conf:B gen_gc_partial_conf) (state:(A,B)gc_state)
      (gc_shared_Data d) = (gc_shared_Data d,state)) /\
   (gen_gc_partial_gc_move conf state (Pointer ptr d) =
      let ok = (gc_state_ok state /\ ptr < heap_length (gc_state_heap state)) in
      (if ptr < gen_gc_partial_conf_gen_start conf \/
          gen_gc_partial_conf_refs_start conf <= ptr then
         (Pointer ptr d,gc_state_ok_fupd (combin_K ok) state) else
       match heap_lookup ptr (gc_state_heap state) with
         SOME (DataElement xs l dd) ->
           (let ok = (ok /\ l + 1 <= gc_state_n state /\
                      ~(gen_gc_partial_conf_isRef conf dd)) in
            let n = gc_state_n state - (l + 1) in
            let h2 = APPEND (gc_state_h2 state) [DataElement xs l dd] in
            match gc_forward_ptr ptr (gc_state_heap state) (gc_state_a state) d ok with
              (heap,ok) ->
                (let a = gc_state_a state + l + 1 in
                 (Pointer (gc_state_a state) d,
                  gc_state_ok_fupd (combin_K ok) (gc_state_heap_fupd (combin_K heap)
                    (gc_state_a_fupd (combin_K a) (gc_state_n_fupd (combin_K n)
                      (gc_state_h2_fupd (combin_K h2) state)))))))
       | SOME (ForwardPointer ptr _ l) -> (Pointer ptr d,state)
       | _ -> (Pointer ptr d,gc_state_ok_fupd (combin_K F) state)))`;;

let gen_gc_partial_gc_move_IMP = prove
 (`!x x' (state:(A,B)gc_state) state1 (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move conf state x = (x',state1)
     ==> gc_state_old state1 = gc_state_old state /\
         gc_state_h1 state1 = gc_state_h1 state /\
         gc_state_r4 state1 = gc_state_r4 state /\
         gc_state_r3 state1 = gc_state_r3 state /\
         gc_state_r2 state1 = gc_state_r2 state /\
         gc_state_r1 state1 = gc_state_r1 state`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN RW[]);;

let gen_gc_partial_gc_move_list_def = cake_def
  `(gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) [] =
      ([],state)) /\
   (gen_gc_partial_gc_move_list conf state (CONS x xs) =
      match gen_gc_partial_gc_move conf state x with
        (x,state) ->
          (match gen_gc_partial_gc_move_list conf state xs with
             (xs,state) -> (CONS x xs,state)))`;;

let gen_gc_partial_gc_move_list_IMP = prove
 (`!xs xs' (state:(A,B)gc_state) state1 (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list conf state xs = (xs',state1)
     ==> LENGTH xs = LENGTH xs' /\
         gc_state_old state1 = gc_state_old state /\
         gc_state_h1 state1 = gc_state_h1 state /\
         gc_state_r4 state1 = gc_state_r4 state /\
         gc_state_r3 state1 = gc_state_r3 state /\
         gc_state_r2 state1 = gc_state_r2 state /\
         gc_state_r1 state1 = gc_state_r1 state`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_IMP) THEN
  FIRST_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  SIMP_TAC[]);;

let gen_gc_partial_gc_move_data_def = cake_def_wf
  `MEASURE (\(conf:B gen_gc_partial_conf,state:(A,B)gc_state).
              gen_gc_partial_conf_limit conf - heap_length (gc_state_h1 state))`
  (REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GC2AUX_MATCH_MP_EITHER gen_gc_partial_gc_move_list_IMP) THEN
   DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; GC1AUX_heap_length_CONS;
                               el_length_def]) THEN
   SIMP[measure_THM; heap_length_APPEND; GC1AUX_heap_length_CONS;
        heap_length_NIL; el_length_def] THEN
   ASM_ARITH_TAC)
  `gen_gc_partial_gc_move_data (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) =
     match gc_state_h2 state with
       [] -> state
     | CONS h h2 ->
         if gen_gc_partial_conf_limit conf <
            heap_length (APPEND (gc_state_h1 state) (CONS h h2))
         then gc_state_ok_fupd (combin_K F) state else
         (match h with
            DataElement xs l d ->
              (match gen_gc_partial_gc_move_list conf state xs with
                 (xs,state) ->
                   let h1 = APPEND (gc_state_h1 state) [DataElement xs l d] in
                   let h2 = TL (gc_state_h2 state) in
                   let ok = (gc_state_ok state /\ ~(gc_state_h2 state = []) /\
                             HD (gc_state_h2 state) = h) in
                   gen_gc_partial_gc_move_data conf
                     (gc_state_ok_fupd (combin_K ok) (gc_state_h2_fupd (combin_K h2)
                       (gc_state_h1_fupd (combin_K h1) state))))
          | _ -> gc_state_ok_fupd (combin_K F) state)`;;

let gen_gc_partial_gc_move_data_ind = cake_ind "gen_gc_partial_gc_move_data";;

let gc_move_data_IMP = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) state1.
     gen_gc_partial_gc_move_data conf state = state1
     ==> gc_state_old state1 = gc_state_old state /\
         gc_state_r1 state1 = gc_state_r1 state /\
         gc_state_r2 state1 = gc_state_r2 state /\
         gc_state_r3 state1 = gc_state_r3 state /\
         gc_state_r4 state1 = gc_state_r4 state`,
  REWRITE_TAC[MESON[] `(!y:C. f = y ==> P y) <=> P f`] THEN
  MATCH_MP_TAC gen_gc_partial_gc_move_data_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)` ALL_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_list_IMP) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`t:((A,B)heap_element)list`; `zs:(A heap_address)list`;
    `xs':(A heap_address)list`; `l:num`; `d:B`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds] THEN SIMP_TAC[]);;

(* HOL4 gives the reference list its own data type (C here) *)
let gc_move_ref_list_def = cake_def
  `(gc_move_ref_list (conf:B gen_gc_partial_conf) (state:(A,B)gc_state)
      ([]:((A,C)heap_element)list) = ([],state)) /\
   (gc_move_ref_list conf state (CONS (DataElement ptrs l (d:C)) xs) =
      match gen_gc_partial_gc_move_list conf state ptrs with
        (ptrs',state) ->
          (match gc_move_ref_list conf state xs with
             (xs,state) -> (CONS (DataElement ptrs' l d) xs,state))) /\
   (gc_move_ref_list conf state (CONS (x:(A,C)heap_element) xs) =
      (CONS x xs,gc_state_ok_fupd (combin_K F) state))`;;

let gc_move_ref_list_ind = cake_ind "gc_move_ref_list";;

let gen_gc_partial_gc_move_ref_list_IMP = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) (refs:((A,C)heap_element)list)
    state1 refs1.
     gc_move_ref_list conf state refs = (refs1,state1)
     ==> gc_state_old state1 = gc_state_old state /\
         gc_state_r1 state1 = gc_state_r1 state /\
         gc_state_r2 state1 = gc_state_r2 state /\
         heap_length refs = heap_length refs1 /\
         (!ptr. isSomeDataElement (heap_lookup ptr refs)
                ==> isSomeDataElement (heap_lookup ptr refs1))`,
  MATCH_MP_TAC gc_move_ref_list_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC;
    REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds];
    REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[gc_state_FIELDS.ri_accfupds]] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN PAIRARG_TAC THEN PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_list_IMP) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`ptrs':(A heap_address)list`; `state':(A,B)gc_state`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fun ih2 -> FIRST_ASSUM(MP_TAC o MATCH_MP ih2)) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[heap_length_CONS; el_length_def] THEN ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[heap_lookup_def; el_length_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[isSomeDataElement_def; option_INJ] THENL
     [MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    REWRITE_TAC[GSYM isSomeDataElement_def] THEN ASM_MESON_TAC[]]);;

(* process the roots, then the references, then the rest *)
let partial_gc_def = cake_def
  `partial_gc (conf:B gen_gc_partial_conf)
              (roots:(A heap_address)list,heap:((A,B)heap_element)list) =
     match heap_segment (gen_gc_partial_conf_gen_start conf,
                         gen_gc_partial_conf_refs_start conf) heap with
       NONE -> (roots,gc_state_ok_fupd (combin_K F) empty_state)
     | SOME (old,current,refs) ->
         (let n = heap_length current in
          let state = gc_state_n_fupd (combin_K n) (gc_state_a_fupd (combin_K (gen_gc_partial_conf_gen_start conf))
                        (gc_state_r2_fupd (combin_K refs) (gc_state_old_fupd (combin_K old)
                          (gc_state_heap_fupd (combin_K heap) empty_state)))) in
          match gen_gc_partial_gc_move_list conf state roots with
            (roots,state) ->
              (match gc_move_ref_list conf state refs with
                 (refs',state) ->
                   (let state = gen_gc_partial_gc_move_data conf
                                  (gc_state_r2_fupd (combin_K []) (gc_state_r1_fupd (combin_K refs') state)) in
                    (roots,state))))`;;

let partial_gc_IMP = prove
 (`!roots (heap:((A,B)heap_element)list) roots1 state1 heap_old heap_current heap_refs
    (conf:B gen_gc_partial_conf).
     partial_gc conf (roots,heap) = (roots1,state1) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (heap_old,heap_current,heap_refs)
     ==> gc_state_old state1 = heap_old /\
         heap_length (gc_state_r1 state1) = heap_length heap_refs /\
         LENGTH roots = LENGTH roots1 /\
         (!ptr. isSomeDataElement (heap_lookup ptr heap_refs)
                ==> isSomeDataElement (heap_lookup ptr (gc_state_r1 state1)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[partial_gc_def; pair_CASE; option_CASE; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP gc_move_data_IMP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_ref_list_IMP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_list_IMP) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; empty_state_def;
              gc_state_FIELDS.ri_accessors] THEN
  RVEQ_TAC THEN SIMP_TAC[]);;

(* Pointers between current and old generations are correct *)
let heap_gen_ok_def = cake_def
  `heap_gen_ok (heap:((A,B)heap_element)list) (conf:B gen_gc_partial_conf) <=>
     ?old current refs.
       gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf /\
       gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit conf /\
       ALL isDataElement old /\
       ALL isDataElement refs /\
       SOME (old,current,refs) =
         heap_segment (gen_gc_partial_conf_gen_start conf,
                       gen_gc_partial_conf_refs_start conf) heap /\
       (!ptr xs l d (u:A). MEM (DataElement xs l d) old /\ MEM (Pointer ptr u) xs
                           ==> ptr < gen_gc_partial_conf_gen_start conf \/
                               gen_gc_partial_conf_refs_start conf <= ptr) /\
       (!xs l d. MEM (DataElement xs l d) old ==> ~gen_gc_partial_conf_isRef conf d) /\
       (!xs l d. MEM (DataElement xs l d) current ==> ~gen_gc_partial_conf_isRef conf d) /\
       (!xs l d. MEM (DataElement xs l d) refs ==> gen_gc_partial_conf_isRef conf d)`;;

let data_sort_INDUCT,data_sort_RECURSION =
  cake_type "data_sort = Protected A | Real B";;

let to_gen_heap_address_def = cake_def
  `(to_gen_heap_address (conf:C gen_gc_partial_conf) (gc_shared_Data (a:A)) =
      gc_shared_Data (Real a:(A heap_address,A)data_sort)) /\
   (to_gen_heap_address conf (Pointer ptr a) =
      if ptr < gen_gc_partial_conf_gen_start conf then
        gc_shared_Data (Protected (Pointer ptr a))
      else if gen_gc_partial_conf_refs_start conf <= ptr then
        gc_shared_Data (Protected (Pointer ptr a))
      else Pointer (ptr - gen_gc_partial_conf_gen_start conf) (Real a))`;;

let to_gen_conf_def = cake_def
  `to_gen_conf (conf:A gen_gc_partial_conf) =
     (gen_gc_conf_REC
        ((gen_gc_partial_conf_limit conf - gen_gc_partial_conf_gen_start conf) -
         (gen_gc_partial_conf_limit conf - gen_gc_partial_conf_refs_start conf))
        (gen_gc_partial_conf_isRef conf)):A gen_gc_conf`;;

let to_gen_heap_element_def = cake_def
  `(to_gen_heap_element (conf:C gen_gc_partial_conf) (Unused n:(A,B)heap_element) =
      (Unused n:((A heap_address,A)data_sort,B)heap_element)) /\
   (to_gen_heap_element conf (ForwardPointer ptr a l) =
      ForwardPointer (ptr - gen_gc_partial_conf_gen_start conf) (Real a) l) /\
   (to_gen_heap_element conf (DataElement ptrs l d) =
      DataElement (MAP (to_gen_heap_address conf) ptrs) l d)`;;

let to_gen_heap_list_def = cake_def
  `to_gen_heap_list (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) =
     MAP (to_gen_heap_element conf) heap`;;

let to_gen_heap_list_heap_length = prove
 (`!xs (conf:C gen_gc_partial_conf).
     heap_length (to_gen_heap_list conf xs:(((A heap_address,A)data_sort,B)heap_element)list) =
     heap_length (xs:((A,B)heap_element)list)`,
  REWRITE_TAC[to_gen_heap_list_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; heap_length_NIL; GC1AUX_heap_length_CONS] THEN
  GEN_TAC THEN CASES_ON `h:(A,B)heap_element` THEN
  REWRITE_TAC[to_gen_heap_element_def; el_length_def]);;

let to_gen_heap_def = cake_def
  `to_gen_heap (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) =
     to_gen_heap_list conf
       (heap_restrict (gen_gc_partial_conf_gen_start conf)
          (gen_gc_partial_conf_refs_start conf) heap)`;;

let to_gen_state_def = cake_def
  `to_gen_state (conf:C gen_gc_partial_conf) (state:(A,B)gc_state) =
     gc_state_heap0_fupd (combin_K (to_gen_heap conf (gc_state_heap0 state)))
     (gc_state_heap_fupd (combin_K (to_gen_heap conf (gc_state_heap state)))
     (gc_state_ok_fupd (combin_K (gc_state_ok state))
     (gc_state_n_fupd (combin_K (gc_state_n state))
     (gc_state_a_fupd (combin_K (gc_state_a state - gen_gc_partial_conf_gen_start conf))
     (gc_state_r1_fupd (combin_K [])
     (gc_state_r2_fupd (combin_K [])
     (gc_state_r3_fupd (combin_K [])
     (gc_state_r4_fupd (combin_K [])
     (gc_state_h2_fupd (combin_K (to_gen_heap_list conf (gc_state_h2 state)))
     (gc_state_h1_fupd (combin_K (to_gen_heap_list conf (gc_state_h1 state)))
        empty_state))))))))))`;;

let to_gen_roots_def = cake_def
  `to_gen_roots (conf:C gen_gc_partial_conf) (roots:(A heap_address)list) =
     MAP (to_gen_heap_address conf) roots`;;

let refs_to_roots_def = cake_def
  `(refs_to_roots (conf:C gen_gc_partial_conf) ([]:((A,B)heap_element)list) = []) /\
   (refs_to_roots conf (CONS (DataElement ptrs _ _) refs) =
      APPEND (MAP (to_gen_heap_address conf) ptrs) (refs_to_roots conf refs)) /\
   (refs_to_roots conf (CONS _ refs) = refs_to_roots conf refs)`;;

(* names.tsv: RootsRefs_rules etc.; OCaml cannot bind a name that starts *)
(* with a capital followed by a lower case letter, so they get the theory *)
(* prefix                                                                  *)
let gen_gc_partial_RootsRefs_rules,gen_gc_partial_RootsRefs_ind,
    gen_gc_partial_RootsRefs_cases,gen_gc_partial_RootsRefs_strongind = cake_inductive
  `RootsRefs ([]:((A,B)heap_element)list) ([]:(A heap_address)list) /\
   (!ptrs m b refs roots ptr a.
      RootsRefs (CONS (DataElement ptrs m b) refs) roots
      ==> RootsRefs (CONS (DataElement (CONS (Pointer ptr a) ptrs) m b) refs)
                    (CONS (Pointer ptr a) roots)) /\
   (!ptrs m b refs roots a.
      RootsRefs (CONS (DataElement ptrs m b) refs) roots
      ==> RootsRefs (CONS (DataElement (CONS (gc_shared_Data a) ptrs) m b) refs)
                    (CONS (gc_shared_Data a) roots)) /\
   (!refs roots m b.
      RootsRefs refs roots ==> RootsRefs (CONS (DataElement [] m b) refs) roots) /\
   (!refs roots n.
      RootsRefs refs roots ==> RootsRefs (CONS (Unused n) refs) roots) /\
   (!refs roots p a l.
      RootsRefs refs roots ==> RootsRefs (CONS (ForwardPointer p a l) refs) roots)`;;

let heap_element_is_ref_def = cake_def
  `(heap_element_is_ref (conf:B gen_gc_partial_conf) (DataElement xs l d:(A,B)heap_element) <=>
      gen_gc_partial_conf_isRef conf d) /\
   (heap_element_is_ref conf (_:(A,B)heap_element) <=> F)`;;

let gen_inv_def = cake_def
  `gen_inv (conf:B gen_gc_partial_conf) (heap:((A,B)heap_element)list) <=>
     gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf /\
     gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit conf /\
     ?heap_old heap_current heap_refs.
       heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
         heap = SOME (heap_old,heap_current,heap_refs) /\
       ALL (\e. ~heap_element_is_ref conf e) heap_old /\
       ALL (\e. ~heap_element_is_ref conf e) heap_current /\
       ALL isDataElement heap_refs /\
       (!n (a:A) d. MEM (ForwardPointer n a d) heap
                    ==> gen_gc_partial_conf_gen_start conf <= n /\
                        n < gen_gc_partial_conf_refs_start conf) /\
       ALL isDataElement heap_old /\
       !xs l d ptr (u:A).
         MEM (DataElement xs l d) heap_old /\ MEM (Pointer ptr u) xs
         ==> ptr < gen_gc_partial_conf_gen_start conf \/
             gen_gc_partial_conf_refs_start conf <= ptr`;;

let has_old_ptr_def = cake_def
  `has_old_ptr (conf:C gen_gc_partial_conf) (hs:((A,B)heap_element)list) ptr <=>
     ?xs l d (u:A).
       MEM (DataElement xs l d) hs /\ MEM (Pointer ptr u) xs /\
       (ptr < gen_gc_partial_conf_gen_start conf \/ gen_gc_partial_conf_refs_start conf <= ptr)`;;

let has_old_ptr_APPEND = prove
 (`!xs ys (conf:C gen_gc_partial_conf).
     has_old_ptr conf (APPEND xs ys:((A,B)heap_element)list) =
     has_old_ptr conf xs UNION has_old_ptr conf ys`,
  REWRITE_TAC[EXTENSION; IN_UNION] THEN REWRITE_TAC[IN; has_old_ptr_def; MEM_APPEND] THEN
  MESON_TAC[]);;

(* HOL4: has_old_ptr_CONS (an ML-level value) *)
let GC2AUX_has_old_ptr_CONS = prove
 (`!(x:(A,B)heap_element) ys (conf:C gen_gc_partial_conf).
     has_old_ptr conf (CONS x ys) = has_old_ptr conf [x] UNION has_old_ptr conf ys`,
  REWRITE_TAC[GSYM has_old_ptr_APPEND; APPEND]);;

let all_old_ptrs_def = cake_def
  `all_old_ptrs (conf:C gen_gc_partial_conf) (xs:(A heap_address)list) ptr <=>
     ?u. MEM (Pointer ptr u) xs /\
         (ptr < gen_gc_partial_conf_gen_start conf \/ gen_gc_partial_conf_refs_start conf <= ptr)`;;

let has_old_ptr_simp = prove
 (`!(conf:C gen_gc_partial_conf) (xs:(A heap_address)list) x1 (x2:B).
     has_old_ptr conf [DataElement xs x1 x2] = all_old_ptrs conf xs`,
  REWRITE_TAC[has_old_ptr_def; FUN_EQ_THM; all_old_ptrs_def; MEM; heap_element_11] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [has_old_ptr_simp];;

let sim_inv_def = cake_def
  `sim_inv (conf:B gen_gc_partial_conf) (heap0:((A,B)heap_element)list)
           (state:(A,B)gc_state) <=>
     gen_inv conf (gc_state_heap state) /\
     gen_gc_partial_conf_gen_start conf <= gc_state_a state /\
     gc_state_a state + gc_state_n state <= gen_gc_partial_conf_refs_start conf /\
     gen_gc_partial_conf_gen_start conf +
       heap_length (APPEND (gc_state_h1 state) (gc_state_h2 state)) + gc_state_n state =
       gen_gc_partial_conf_refs_start conf /\
     (gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_gen_start conf
      ==> gc_state_h1 state = [] /\ gc_state_h2 state = []) /\
     has_old_ptr conf (APPEND (APPEND (APPEND (gc_state_heap state) (gc_state_h1 state))
                                (gc_state_h2 state)) (gc_state_r1 state))
       SUBSET has_old_ptr conf heap0`;;

let heap_length_to_gen_heap_list = prove
 (`!h2 (conf:C gen_gc_partial_conf).
     heap_length (to_gen_heap_list conf h2:(((A heap_address,A)data_sort,B)heap_element)list) =
     heap_length (h2:((A,B)heap_element)list)`,
  REWRITE_TAC[to_gen_heap_list_heap_length]);;
let _ = cake_add_simps [heap_length_to_gen_heap_list];;

let el_length_not_zero = prove
 (`!x:(A,B)heap_element. ~(el_length x = 0)`,
  REWRITE_TAC[el_length_NOT_0]);;
let _ = cake_add_simps [el_length_not_zero];;

let heap_split_length = prove
 (`!h1 h2:((A,B)heap_element)list.
     heap_split (heap_length h1) (APPEND h1 h2) = SOME (h1,h2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[heap_length_NIL; APPEND; heap_split_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[APPEND; heap_split_def; GC1AUX_heap_length_CONS] THEN
  GEN_TAC THEN GC1AUX_EL_LENGTH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= e ==> ~(e + n = 0) /\ ~(e + n < e) /\ (e + n) - e = n`] THEN
  CAKE_REWRITE_TAC[]);;

let heap_segment_length = prove
 (`!h1 h2 h3:((A,B)heap_element)list.
     heap_segment (heap_length h1,heap_length h1 + heap_length h2)
       (APPEND (APPEND h1 h2) h3) = SOME (h1,h2,h3)`,
  REWRITE_TAC[heap_segment_def; GSYM APPEND_ASSOC; heap_split_length] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `~(a + b < a)`; ADD_SUB2; heap_split_length] THEN
  CAKE_REWRITE_TAC[]);;

(* helpers for the simulation proofs: lookups in the translated heap *)

let GC2AUX_el_length_to_gen = prove
 (`!(conf:C gen_gc_partial_conf) (h:(A,B)heap_element).
     el_length (to_gen_heap_element conf h) = el_length h`,
  GEN_TAC THEN MATCH_MP_TAC heap_element_INDUCT THEN
  REWRITE_TAC[to_gen_heap_element_def; el_length_def]);;

let GC2AUX_heap_lookup_to_gen = prove
 (`!xs j (conf:C gen_gc_partial_conf).
     heap_lookup j (to_gen_heap_list conf xs:(((A heap_address,A)data_sort,B)heap_element)list) =
     OPTION_MAP (to_gen_heap_element conf) (heap_lookup j (xs:((A,B)heap_element)list))`,
  REWRITE_TAC[to_gen_heap_list_def] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; heap_lookup_def; OPTION_MAP_DEF; GC2AUX_el_length_to_gen] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let GC2AUX_to_gen_heap_list_APPEND = prove
 (`!xs ys (conf:C gen_gc_partial_conf).
     to_gen_heap_list conf (APPEND xs ys:((A,B)heap_element)list) =
     APPEND (to_gen_heap_list conf xs) (to_gen_heap_list conf ys)`,
  REWRITE_TAC[to_gen_heap_list_def; MAP_APPEND]);;

let GC2AUX_gen_inv_segment = prove
 (`!(conf:B gen_gc_partial_conf) (heap:((A,B)heap_element)list).
     gen_inv conf heap
     ==> ?old cur refs.
           heap_segment (gen_gc_partial_conf_gen_start conf,
                         gen_gc_partial_conf_refs_start conf) heap = SOME (old,cur,refs) /\
           heap = APPEND (APPEND old cur) refs /\
           heap_length old = gen_gc_partial_conf_gen_start conf /\
           heap_length old + heap_length cur = gen_gc_partial_conf_refs_start conf /\
           to_gen_heap conf heap = to_gen_heap_list conf cur`,
  REWRITE_TAC[gen_inv_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`heap_old:((A,B)heap_element)list`;
    `heap_current:((A,B)heap_element)list`; `heap_refs:((A,B)heap_element)list`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_segment_IMP) THEN
  ASM_REWRITE_TAC[to_gen_heap_def; heap_restrict_def; pair_CASE; option_CASE] THEN
  CAKE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GC2AUX_gen_inv_lookup = prove
 (`!(conf:B gen_gc_partial_conf) (heap:((A,B)heap_element)list) ptr.
     gen_inv conf heap /\ gen_gc_partial_conf_gen_start conf <= ptr /\
     ptr < gen_gc_partial_conf_refs_start conf
     ==> heap_lookup (ptr - gen_gc_partial_conf_gen_start conf) (to_gen_heap conf heap) =
         OPTION_MAP (to_gen_heap_element conf) (heap_lookup ptr heap)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `old:((A,B)heap_element)list` (X_CHOOSE_THEN `cur:((A,B)heap_element)list`
      (X_CHOOSE_THEN `refs:((A,B)heap_element)list` STRIP_ASSUME_TAC)) o
     MATCH_MP GC2AUX_gen_inv_segment) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GC2AUX_heap_lookup_to_gen] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  SUBGOAL_THEN `~(ptr < heap_length (old:((A,B)heap_element)list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC gc_shared_LESS_IMP_heap_lookup THEN ASM_ARITH_TAC);;

let GC2AUX_to_gen_state_REC = prove
 (`!(conf:C gen_gc_partial_conf) old h1 h2 r4 r3 r2 r1 a n ok heap
    (hp0:((A,B)heap_element)list).
     to_gen_state conf (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok heap hp0) =
     gc_state_REC [] (to_gen_heap_list conf h1) (to_gen_heap_list conf h2) [] [] [] []
       (a - gen_gc_partial_conf_gen_start conf) n ok (to_gen_heap conf heap)
       (to_gen_heap conf hp0)`,
  REWRITE_TAC[to_gen_state_def; empty_state_def; gc_state_FIELDS.ri_accessors;
              gc_state_FIELDS.ri_fupds; K_THM]);;

(* sim_inv after a data element of the current generation is forwarded *)
let GC2AUX_sim_inv_DE = prove
 (`!(conf:B gen_gc_partial_conf) heap0 old h1 h2 r4 r3 r2 r1 a n ok hp0
    old' haC hbC refs zs l (d:B) (u:A) ok2.
     sim_inv conf heap0
       (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok
          (APPEND (APPEND old' (APPEND haC (CONS (DataElement zs l d) hbC))) refs) hp0) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       (APPEND (APPEND old' (APPEND haC (CONS (DataElement zs l d) hbC))) refs) =
       SOME (old',APPEND haC (CONS (DataElement zs l d) hbC),refs) /\
     heap_length old' = gen_gc_partial_conf_gen_start conf /\
     heap_length old' + heap_length (APPEND haC (CONS (DataElement zs l d) hbC)) =
       gen_gc_partial_conf_refs_start conf /\
     l + 1 <= n
     ==> sim_inv conf heap0
           (gc_state_REC old h1 (APPEND h2 [DataElement zs l d]) r4 r3 r2 r1 (a + l + 1)
              (n - (l + 1)) ok2
              (APPEND (APPEND old' (APPEND haC (CONS (ForwardPointer a u l) hbC))) refs)
              hp0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sim_inv_def; gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "ginv")
     (CONJUNCTS_THEN2 (LABEL_TAC "ga") (CONJUNCTS_THEN2 (LABEL_TAC "an")
       (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 (LABEL_TAC "emp")
         (LABEL_TAC "old")))))) (CONJUNCTS_THEN2 (LABEL_TAC "seg")
     (CONJUNCTS_THEN2 (LABEL_TAC "lo") (CONJUNCTS_THEN2 (LABEL_TAC "lc") (LABEL_TAC "ln"))))) THEN
  USE_THEN "ginv" (MP_TAC o REWRITE_RULE[gen_inv_def]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gr") (CONJUNCTS_THEN2 (LABEL_TAC "rl")
    (X_CHOOSE_THEN `ho:((A,B)heap_element)list` (X_CHOOSE_THEN `hc:((A,B)heap_element)list`
      (X_CHOOSE_THEN `hr:((A,B)heap_element)list` (CONJUNCTS_THEN2 (LABEL_TAC "seg2")
        (CONJUNCTS_THEN2 (LABEL_TAC "nro") (CONJUNCTS_THEN2 (LABEL_TAC "nrc")
          (CONJUNCTS_THEN2 (LABEL_TAC "der") (CONJUNCTS_THEN2 (LABEL_TAC "fp")
            (CONJUNCTS_THEN2 (LABEL_TAC "deo") (LABEL_TAC "optr")))))))))))) THEN
  USE_THEN "seg2" MP_TAC THEN USE_THEN "seg" (fun th -> REWRITE_TAC[th; option_INJ; PAIR_EQ]) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `heap_length (APPEND haC (CONS (ForwardPointer a (u:A) l) hbC)) =
                heap_length (APPEND haC (CONS (DataElement zs l (d:B)) hbC))` (LABEL_TAC "eqlen")
  THENL [REWRITE_TAC[heap_length_APPEND; heap_length_CONS; el_length_def]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[gen_inv_def] THEN
    USE_THEN "gr" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXISTS_TAC [`old':((A,B)heap_element)list`;
      `APPEND haC (CONS (ForwardPointer a (u:A) l) hbC):((A,B)heap_element)list`;
      `refs:((A,B)heap_element)list`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "lo" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "lc" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "eqlen" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[heap_segment_length];
      USE_THEN "nro" ACCEPT_TAC;
      USE_THEN "nrc" MP_TAC THEN
      REWRITE_TAC[ALL_APPEND; ALL; heap_element_is_ref_def] THEN MESON_TAC[];
      USE_THEN "der" ACCEPT_TAC;
      REWRITE_TAC[MEM_APPEND; MEM; heap_element_11; heap_element_distinct] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THENL
       [ALL_TAC; ALL_TAC; ASM_REWRITE_TAC[] THEN USE_THEN "ga" MP_TAC THEN
        USE_THEN "an" MP_TAC THEN USE_THEN "ln" MP_TAC THEN ARITH_TAC; ALL_TAC; ALL_TAC] THEN
      USE_THEN "fp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN ASM_MESON_TAC[];
      USE_THEN "deo" ACCEPT_TAC;
      USE_THEN "optr" ACCEPT_TAC];
    USE_THEN "ga" MP_TAC THEN ARITH_TAC;
    USE_THEN "an" MP_TAC THEN USE_THEN "ln" MP_TAC THEN ARITH_TAC;
    USE_THEN "len" MP_TAC THEN USE_THEN "ln" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def] THEN
    ARITH_TAC;
    USE_THEN "lo" MP_TAC THEN USE_THEN "lc" MP_TAC THEN
    REWRITE_TAC[heap_length_APPEND; heap_length_CONS; el_length_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "old" MP_TAC THEN
  REWRITE_TAC[has_old_ptr_APPEND] THEN ONCE_REWRITE_TAC[GC2AUX_has_old_ptr_CONS] THEN
  SUBGOAL_THEN `has_old_ptr (conf:B gen_gc_partial_conf)
                  [ForwardPointer a (u:A) l:(A,B)heap_element] = {} /\
                has_old_ptr conf ([]:((A,B)heap_element)list) = {}`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN; has_old_ptr_def; MEM; heap_element_distinct];
    SET_TAC[]]);;

let GC2AUX_gen_inv_split = prove
 (`!(conf:B gen_gc_partial_conf) (heap:((A,B)heap_element)list) ptr x.
     gen_inv conf heap /\ gen_gc_partial_conf_gen_start conf <= ptr /\
     ptr < gen_gc_partial_conf_refs_start conf /\ heap_lookup ptr heap = SOME x
     ==> ?old cur1 cur2 refs.
           heap = APPEND (APPEND old (APPEND cur1 (CONS x cur2))) refs /\
           heap_segment (gen_gc_partial_conf_gen_start conf,
                         gen_gc_partial_conf_refs_start conf) heap =
             SOME (old,APPEND cur1 (CONS x cur2),refs) /\
           heap_length old = gen_gc_partial_conf_gen_start conf /\
           heap_length old + heap_length (APPEND cur1 (CONS x cur2)) =
             gen_gc_partial_conf_refs_start conf /\
           ptr = heap_length old + heap_length cur1 /\
           to_gen_heap conf heap = to_gen_heap_list conf (APPEND cur1 (CONS x cur2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      X_CHOOSE_THEN `old:((A,B)heap_element)list` (X_CHOOSE_THEN `cur:((A,B)heap_element)list`
        (X_CHOOSE_THEN `refs:((A,B)heap_element)list` STRIP_ASSUME_TAC))
      (MATCH_MP GC2AUX_gen_inv_segment th)) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `heap_lookup (ptr - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)) cur =
                SOME (x:(A,B)heap_element)` MP_TAC THENL
   [UNDISCH_TAC `heap_lookup ptr heap = SOME (x:(A,B)heap_element)` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    SUBGOAL_THEN `~(ptr < heap_length (old:((A,B)heap_element)list))` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
    SUBGOAL_THEN `ptr - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) <
                  heap_length (cur:((A,B)heap_element)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cur1:((A,B)heap_element)list` (X_CHOOSE_THEN
    `cur2:((A,B)heap_element)list` STRIP_ASSUME_TAC) o MATCH_MP heap_lookup_SPLIT) THEN
  MAP_EVERY EXISTS_TAC [`old:((A,B)heap_element)list`; `cur1:((A,B)heap_element)list`;
    `cur2:((A,B)heap_element)list`; `refs:((A,B)heap_element)list`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `cur = APPEND cur1 (CONS (x:(A,B)heap_element) cur2)`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GC2AUX_gc_forward_ptr_thm4 = prove
 (`!A0 A1 C D (ys:(A heap_address)list) l (d:B) p (u:A) c.
     gc_forward_ptr (heap_length A0 + heap_length A1)
       (APPEND (APPEND A0 (APPEND A1 (CONS (DataElement ys l d) C))) D) p u c =
     (APPEND (APPEND A0 (APPEND A1 (CONS (ForwardPointer p u l) C))) D,c)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!x:(A,B)heap_element.
                  APPEND (APPEND A0 (APPEND A1 (CONS x C))) D =
                  APPEND (APPEND A0 A1) (CONS x (APPEND C D))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  REWRITE_TAC[GSYM heap_length_APPEND; gc_forward_ptr_thm]);;

let GC2AUX_gen_inv_cur_not_ref = prove
 (`!(conf:B gen_gc_partial_conf) (heap:((A,B)heap_element)list) old cur refs xs l d.
     gen_inv conf heap /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (old,cur,refs) /\
     MEM (DataElement xs l d) cur
     ==> ~gen_gc_partial_conf_isRef conf d`,
  REWRITE_TAC[gen_inv_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `heap_current:((A,B)heap_element)list = cur` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> rand(concl th) =
      `SOME (heap_old:((A,B)heap_element)list,heap_current:((A,B)heap_element)list,
             heap_refs:((A,B)heap_element)list)`)) THEN
    ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
    `ALL (\e. ~heap_element_is_ref (conf:B gen_gc_partial_conf) e) (cur:((A,B)heap_element)list)`)) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `DataElement xs l d:(A,B)heap_element`) THEN
  ASM_REWRITE_TAC[heap_element_is_ref_def]);;

let GC2AUX_to_gen_heap_seg = prove
 (`!(conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) old cur refs.
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (old,cur,refs)
     ==> to_gen_heap conf heap = to_gen_heap_list conf cur`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[to_gen_heap_def; heap_restrict_def] THEN
  CAKE_REWRITE_TAC[]);;

let gc_move_simulation = prove
 (`!ptr ptr' (state:(A,B)gc_state) state' ptr1' state1' (conf:B gen_gc_partial_conf) heap0.
     gen_gc_partial_gc_move conf state ptr = (ptr',state') /\
     (!ptr' u. ptr = Pointer ptr' u ==> ptr' < heap_length (gc_state_heap state)) /\
     heap_length (gc_state_heap state) = gen_gc_partial_conf_limit conf /\
     sim_inv conf heap0 state /\
     gen_gc_gc_move (to_gen_conf conf) (to_gen_state conf state)
       (to_gen_heap_address conf ptr) = (ptr1',state1') /\
     gc_state_ok state1'
     ==> sim_inv conf heap0 state' /\
         (ptr1',state1') = (to_gen_heap_address conf ptr',to_gen_state conf state') /\
         all_old_ptrs conf [ptr'] SUBSET all_old_ptrs conf [ptr]`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; GC2AUX_to_gen_state_REC] THEN
  CASES_ON `ptr:A heap_address` THENL
   [(* a pointer *)
    REPEAT GEN_TAC THEN REWRITE_TAC[heap_address_11] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pm") (CONJUNCTS_THEN2
      (MP_TAC o SPECL [`a0:num`; `a1:A`]) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
        (CONJUNCTS_THEN2 (LABEL_TAC "sim") (CONJUNCTS_THEN2 (LABEL_TAC "gm")
          (LABEL_TAC "ok1")))))) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `a0 < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)` THENL
     [(* to an old generation *)
      REMOVE_THEN "pm" MP_TAC THEN REMOVE_THEN "gm" MP_TAC THEN
      ASM_REWRITE_TAC[gen_gc_partial_gc_move_def; to_gen_heap_address_def; gen_gc_gc_move_def;
                      LET_DEF; LET_END_DEF; PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      ASM_REWRITE_TAC[gc_state_FIELDS.ri_fupds; gc_state_FIELDS.ri_accessors; K_THM;
                      to_gen_heap_address_def; GC2AUX_to_gen_state_REC; SUBSET_REFL];
      ASM_CASES_TAC `gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf) <= a0` THENL
       [(* to the references *)
        REMOVE_THEN "pm" MP_TAC THEN REMOVE_THEN "gm" MP_TAC THEN
        ASM_REWRITE_TAC[gen_gc_partial_gc_move_def; to_gen_heap_address_def; gen_gc_gc_move_def;
                        LET_DEF; LET_END_DEF; PAIR_EQ] THEN
        DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
        ASM_REWRITE_TAC[gc_state_FIELDS.ri_fupds; gc_state_FIELDS.ri_accessors; K_THM;
                        to_gen_heap_address_def; GC2AUX_to_gen_state_REC; SUBSET_REFL];
        (* to the current generation *)
        SUBGOAL_THEN `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) <= a0 /\
                      a0 < gen_gc_partial_conf_refs_start conf` (LABEL_TAC "rng") THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "sim" (LABEL_TAC "ginv" o CONJUNCT1 o
          REWRITE_RULE[sim_inv_def; gc_state_FIELDS.ri_accessors]) THEN
        USE_THEN "ginv" (fun th -> USE_THEN "rng" (fun r ->
          LABEL_TAC "lk" (MATCH_MP GC2AUX_gen_inv_lookup (CONJ th r)))) THEN
        REMOVE_THEN "pm" MP_TAC THEN REMOVE_THEN "gm" MP_TAC THEN
        ASM_REWRITE_TAC[gen_gc_partial_gc_move_def; to_gen_heap_address_def; gen_gc_gc_move_def;
                        LET_DEF; LET_END_DEF; gc_state_FIELDS.ri_accessors] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(a0 < g) ==> (a0 - g) + g = a0`] THEN
        MP_TAC(ISPEC `heap_lookup a0 (heap:((A,B)heap_element)list)` (cases "option")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `x:(A,B)heap_element`
          (fun th -> SUBST1_TAC th THEN LABEL_TAC "hx" th))) THEN
        REWRITE_TAC[OPTION_MAP_DEF] THEN CAKE_REWRITE_TAC[] THENL
         [DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST_ALL_TAC o SYM)) THEN
          USE_THEN "ok1" MP_TAC THEN
          REWRITE_TAC[gc_state_FIELDS.ri_fupds; gc_state_FIELDS.ri_accessors; K_THM];
          MP_TAC(ISPEC `x:(A,B)heap_element` (cases "heap_element")) THEN
          DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)
            (DISJ_CASES_THEN2 (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `a':A` (X_CHOOSE_THEN `l:num`
               SUBST_ALL_TAC)))
              (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
                (X_CHOOSE_THEN `d:B` SUBST_ALL_TAC))))) THEN
          REWRITE_TAC[to_gen_heap_element_def] THEN CAKE_REWRITE_TAC[] THENL
           [DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST_ALL_TAC o SYM)) THEN
            USE_THEN "ok1" MP_TAC THEN
            REWRITE_TAC[gc_state_FIELDS.ri_fupds; gc_state_FIELDS.ri_accessors; K_THM];
            DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
            DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
            SUBGOAL_THEN `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) <= p /\
                          p < gen_gc_partial_conf_refs_start conf` STRIP_ASSUME_TAC THENL
             [USE_THEN "ginv" (MP_TAC o REWRITE_RULE[gen_inv_def]) THEN STRIP_TAC THEN
              FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `a':A` THEN EXISTS_TAC `l:num` THEN
              USE_THEN "hx" (ACCEPT_TAC o MATCH_MP heap_lookup_MEM);
              ALL_TAC] THEN
            ASM_REWRITE_TAC[GC2AUX_to_gen_state_REC; to_gen_heap_address_def; NOT_LT] THEN
            REWRITE_TAC[SUBSET; IN; all_old_ptrs_def; MEM; heap_address_11] THEN ASM_MESON_TAC[NOT_LT];
            USE_THEN "ginv" (fun g -> USE_THEN "rng" (fun r -> USE_THEN "hx" (fun h ->
              MP_TAC(MATCH_MP GC2AUX_gen_inv_split (CONJ g (CONJ (CONJUNCT1 r) (CONJ (CONJUNCT2 r) h))))))) THEN
            DISCH_THEN(X_CHOOSE_THEN `old':((A,B)heap_element)list` (X_CHOOSE_THEN
              `cur1:((A,B)heap_element)list` (X_CHOOSE_THEN `cur2:((A,B)heap_element)list`
                (X_CHOOSE_THEN `refs:((A,B)heap_element)list` STRIP_ASSUME_TAC)))) THEN
            FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `heap:((A,B)heap_element)list`)) THEN
            FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `a0:num`)) THEN
            REWRITE_TAC[GC2AUX_gc_forward_ptr_thm4] THEN
            FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
              try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "to_gen_heap" with _ -> false)) THEN
            SUBGOAL_THEN `(heap_length (old':((A,B)heap_element)list) + heap_length (cur1:((A,B)heap_element)list)) -
                          gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) =
                          heap_length (to_gen_heap_list conf cur1:(((A heap_address,A)data_sort,B)heap_element)list)`
              SUBST1_TAC THENL
             [REWRITE_TAC[heap_length_to_gen_heap_list] THEN
              FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
                lhs(concl th) = `heap_length (old':((A,B)heap_element)list)`)) THEN ARITH_TAC;
              ALL_TAC] THEN
            REWRITE_TAC[GC2AUX_to_gen_heap_list_APPEND] THEN
            REWRITE_TAC[to_gen_heap_list_def; MAP; to_gen_heap_element_def] THEN
            REWRITE_TAC[GSYM to_gen_heap_list_def; gc_forward_ptr_thm] THEN
            SUBGOAL_THEN `~gen_gc_partial_conf_isRef (conf:B gen_gc_partial_conf) (d:B)` ASSUME_TAC THENL
             [MATCH_MP_TAC GC2AUX_gen_inv_cur_not_ref THEN
              MAP_EVERY EXISTS_TAC
               [`APPEND (APPEND old' (APPEND cur1 (CONS (DataElement zs l d) cur2))) refs
                 :((A,B)heap_element)list`;
                `old':((A,B)heap_element)list`;
                `APPEND cur1 (CONS (DataElement zs l d) cur2):((A,B)heap_element)list`;
                `refs:((A,B)heap_element)list`; `zs:(A heap_address)list`; `l:num`] THEN
              REWRITE_TAC[MEM_APPEND; MEM] THEN
              USE_THEN "ginv" (fun th -> REWRITE_TAC[th]) THEN
              FIRST_ASSUM(ACCEPT_TAC o check (fun th ->
                try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "heap_segment" with _ -> false));
              ALL_TAC] THEN
            REWRITE_TAC[to_gen_conf_def; gen_gc_conf_FIELDS.ri_accessors] THEN
            FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_neg(concl th) &&
              try fst(dest_const(fst(strip_comb(dest_neg(concl th))))) = "gen_gc_partial_conf_isRef"
              with _ -> false)) THEN
            REWRITE_TAC[pair_CASE; gc_state_FIELDS.ri_fupds; K_THM; PAIR_EQ] THEN
            DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
            DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
            USE_THEN "ok1" (STRIP_ASSUME_TAC o REWRITE_RULE[gc_state_FIELDS.ri_accessors]) THEN
            USE_THEN "sim" (STRIP_ASSUME_TAC o REWRITE_RULE[sim_inv_def; gc_state_FIELDS.ri_accessors]) THEN
            REPEAT CONJ_TAC THENL
             [MATCH_MP_TAC GC2AUX_sim_inv_DE THEN EXISTS_TAC `ok:bool` THEN ASM_REWRITE_TAC[];
              REWRITE_TAC[to_gen_heap_address_def] THEN
              SUBGOAL_THEN `~(a < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)) /\
                            ~(gen_gc_partial_conf_refs_start conf <= a)` (fun th -> REWRITE_TAC[th]) THEN
              ASM_ARITH_TAC;
              REWRITE_TAC[GC2AUX_to_gen_state_REC; gc_state_FIELDS.ri_component_equality;
                          gc_state_FIELDS.ri_accessors; GC2AUX_to_gen_heap_list_APPEND] THEN
              REWRITE_TAC[to_gen_heap_list_def; MAP; to_gen_heap_element_def] THEN CONJ_TAC THENL
               [ASM_ARITH_TAC; ALL_TAC] THEN
              REWRITE_TAC[GSYM to_gen_heap_list_def] THEN
              MATCH_MP_TAC EQ_TRANS THEN
              EXISTS_TAC `to_gen_heap_list (conf:B gen_gc_partial_conf)
                            (APPEND cur1 (CONS (ForwardPointer a (a1:A) l) cur2):((A,B)heap_element)list)` THEN
              CONJ_TAC THENL
               [REWRITE_TAC[GC2AUX_to_gen_heap_list_APPEND] THEN
                REWRITE_TAC[to_gen_heap_list_def; MAP; to_gen_heap_element_def];
                CONV_TAC SYM_CONV THEN MATCH_MP_TAC GC2AUX_to_gen_heap_seg THEN
                MAP_EVERY EXISTS_TAC [`old':((A,B)heap_element)list`; `refs:((A,B)heap_element)list`] THEN
                SUBGOAL_THEN `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) =
                              heap_length (old':((A,B)heap_element)list) /\
                              gen_gc_partial_conf_refs_start conf = heap_length old' +
                                heap_length (APPEND cur1 (CONS (ForwardPointer a (a1:A) l) cur2)
                                             :((A,B)heap_element)list)`
                  (fun th -> REWRITE_TAC[th; heap_segment_length]) THEN
                REWRITE_TAC[heap_length_APPEND; heap_length_CONS; el_length_def] THEN
                RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND; heap_length_CONS; el_length_def]) THEN
                ASM_ARITH_TAC];
              REWRITE_TAC[SUBSET; IN; all_old_ptrs_def; MEM; heap_address_11] THEN
              GEN_TAC THEN STRIP_TAC THEN ASM_ARITH_TAC]]]]];
    (* data *)
    REPEAT GEN_TAC THEN
    REWRITE_TAC[gen_gc_partial_gc_move_def; to_gen_heap_address_def; gen_gc_gc_move_def;
                PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[to_gen_heap_address_def; SUBSET_REFL; GC2AUX_to_gen_state_REC]]);;

let gc_forward_ptr_heap_length = prove
 (`!n h m (a:A) ok h' ok'.
     gc_forward_ptr n (h:((A,B)heap_element)list) m a ok = (h',ok')
     ==> heap_length h = heap_length h'`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[gc_forward_ptr_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[heap_length_CONS; el_length_def] THEN GC1AUX_EL_LENGTH_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[heap_length_CONS; EQ_ADD_LCANCEL] THEN ASM_MESON_TAC[]);;

let gc_move_heap_length = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) h x state'.
     gen_gc_partial_gc_move conf state h = (x,state')
     ==> heap_length (gc_state_heap state) = heap_length (gc_state_heap state')`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `h:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN REPEAT STRIP_TAC THEN GVS[] THEN
  FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP gc_forward_ptr_heap_length));;

let gen_gc_partial_gc_move_list_heap_length = prove
 (`!h x (state:(A,B)gc_state) state' (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list conf state h = (x,state')
     ==> heap_length (gc_state_heap state) = heap_length (gc_state_heap state')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP gc_move_heap_length) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP ih)));;

let gc_move_ref_list_heap_length = prove
 (`!h x (state:(A,B)gc_state) state' (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state (h:((A,C)heap_element)list) = (x,state')
     ==> heap_length (gc_state_heap state) = heap_length (gc_state_heap state')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds];
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds];
    PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP gen_gc_partial_gc_move_list_heap_length) THEN
    FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP ih))]);;

let gc_move_ok' = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) x x' state'.
     gen_gc_partial_gc_move conf state x = (x',state') /\ gc_state_ok state'
     ==> gc_state_ok state`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN REPEAT STRIP_TAC THEN GVS[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP gen_gc_gc_forward_ptr_ok) THEN SIMP_TAC[]);;

let gen_gc_partial_gc_move_ok = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) x x' state'.
     gen_gc_partial_gc_move conf state x = (x',state') /\ gc_state_ok state' /\
     (!ptr' u. x = Pointer ptr' u ==> ptr' < heap_length (gc_state_heap state))
     ==> gc_state_ok state`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC gc_move_ok' THEN
  MAP_EVERY EXISTS_TAC [`conf:B gen_gc_partial_conf`; `x:A heap_address`;
                        `x':A heap_address`; `state':(A,B)gc_state`] THEN
  ASM_REWRITE_TAC[]);;

let gc_move_list_ok' = prove
 (`!xs xs' (state:(A,B)gc_state) state' (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list conf state xs = (xs',state') /\ gc_state_ok state'
     ==> gc_state_ok state`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC gc_move_ok' THEN
  MAP_EVERY EXISTS_TAC [`conf:B gen_gc_partial_conf`; `h:A heap_address`; `x':A heap_address`;
                        `state'':(A,B)gc_state`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun mv -> MATCH_MP_TAC (MATCH_MP
    (REWRITE_RULE[IMP_CONJ] ih) mv))) THEN
  ASM_REWRITE_TAC[]);;

let gen_gc_partial_gc_move_list_ok = prove
 (`!xs xs' (state:(A,B)gc_state) state' (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list conf state xs = (xs',state') /\ gc_state_ok state' /\
     (!ptr' u. MEM (Pointer ptr' u) xs ==> ptr' < heap_length (gc_state_heap state))
     ==> gc_state_ok state`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC gc_move_list_ok' THEN
  MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `xs':(A heap_address)list`;
                        `state':(A,B)gc_state`; `conf:B gen_gc_partial_conf`] THEN
  ASM_REWRITE_TAC[]);;

let gc_move_ref_list_ok' = prove
 (`!xs xs' (state:(A,B)gc_state) state' (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state (xs:((A,C)heap_element)list) = (xs',state') /\
     gc_state_ok state'
     ==> gc_state_ok state`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM];
    STRIP_TAC THEN RVEQ_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM];
    ALL_TAC] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun mv -> MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] gc_move_list_ok') mv)) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun mv -> MATCH_MP_TAC (MATCH_MP
    (REWRITE_RULE[IMP_CONJ] ih) mv))) THEN
  ASM_REWRITE_TAC[]);;

let gc_move_data_ok' = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) state'.
     gen_gc_partial_gc_move_data conf state = state' /\ gc_state_ok state'
     ==> gc_state_ok state`,
  REWRITE_TAC[MESON[] `(!y:C. f = y /\ P y ==> Q) <=> (P f ==> Q)`] THEN
  MATCH_MP_TAC gen_gc_partial_gc_move_data_ind THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)` ALL_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  PAIRARG_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`t:((A,B)heap_element)list`; `zs:(A heap_address)list`;
    `xs':(A heap_address)list`; `l:num`; `d:B`; `state':(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun ih -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ih)) THEN
  MATCH_MP_TAC gc_move_list_ok' THEN
  MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `xs':(A heap_address)list`;
    `state':(A,B)gc_state`; `conf:B gen_gc_partial_conf`] THEN
  ASM_REWRITE_TAC[]);;

(* split a pair-valued term into two named components (everywhere), keeping *)
(* the equation as an assumption, and reduce the pair cases of the goal     *)
let GC2AUX_PAIR_TAC (tm:term) (n1:string) (n2:string) : tactic =
  let ty1,ty2 = match dest_type (type_of tm) with
                  "prod",[a;b] -> a,b | _ -> failwith "GC2AUX_PAIR_TAC" in
  MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN (mk_var(n1,ty1)) (X_CHOOSE_THEN (mk_var(n2,ty2))
    (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
  REWRITE_TAC[pair_CASE];;

let GC2AUX_all_old_ptrs_CONS = prove
 (`!(conf:C gen_gc_partial_conf) (x:A heap_address) xs.
     all_old_ptrs conf (CONS x xs) = all_old_ptrs conf [x] UNION all_old_ptrs conf xs`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN; all_old_ptrs_def; MEM] THEN MESON_TAC[]);;

let gc_move_list_simulation = prove
 (`!ptr ptr' (state:(A,B)gc_state) state' ptr1' state1' (conf:B gen_gc_partial_conf) heap0.
     gen_gc_partial_gc_move_list conf state ptr = (ptr',state') /\
     sim_inv conf heap0 state /\
     (!ptr' u. MEM (Pointer ptr' u) ptr ==> ptr' < heap_length (gc_state_heap state)) /\
     heap_length (gc_state_heap state) = gen_gc_partial_conf_limit conf /\
     gen_gc_gc_move_list (to_gen_conf conf) (to_gen_state conf state)
       (MAP (to_gen_heap_address conf) ptr) = (ptr1',state1') /\
     gc_state_ok state1'
     ==> sim_inv conf heap0 state' /\
         (ptr1',state1') = (MAP (to_gen_heap_address conf) ptr',to_gen_state conf state') /\
         all_old_ptrs conf ptr' SUBSET all_old_ptrs conf ptr`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[gen_gc_partial_gc_move_list_def; gen_gc_gc_move_list_def; MAP; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[MAP; SUBSET_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gen_gc_partial_gc_move_list_def; gen_gc_gc_move_list_def; MAP; MEM] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) h`
    "x1" "s1" THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf) (s1:(A,B)gc_state) t`
    "xs1" "s2" THEN
  GC2AUX_PAIR_TAC `gen_gc_gc_move (to_gen_conf (conf:B gen_gc_partial_conf))
      (to_gen_state conf (state:(A,B)gc_state)) (to_gen_heap_address conf (h:A heap_address))`
    "y1" "g1" THEN
  GC2AUX_PAIR_TAC `gen_gc_gc_move_list (to_gen_conf (conf:B gen_gc_partial_conf))
      (g1:((A heap_address,A)data_sort,B)gc_state) (MAP (to_gen_heap_address conf) (t:(A heap_address)list))`
    "ys1" "g2" THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    let ok2 = REWRITE_RULE[SYM (el 6 cs)] (el 7 cs) in
    LABEL_TAC "sim" (el 2 cs) THEN LABEL_TAC "bnd" (el 3 cs) THEN
    LABEL_TAC "lim" (SYM (el 4 cs)) THEN LABEL_TAC "ok2" ok2 THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM) [el 0 cs; el 1 cs; el 5 cs; el 6 cs]) THEN
  SUBGOAL_THEN `gc_state_ok (g1:((A heap_address,A)data_sort,B)gc_state)` (LABEL_TAC "ok1")
  THENL
   [MATCH_MP_TAC gen_gc_gc_move_list_ok THEN
    MAP_EVERY EXISTS_TAC [`MAP (to_gen_heap_address (conf:B gen_gc_partial_conf))
                            (t:(A heap_address)list)`;
      `ys1:(((A heap_address,A)data_sort)heap_address)list`;
      `g2:((A heap_address,A)data_sort,B)gc_state`; `to_gen_conf (conf:B gen_gc_partial_conf)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A heap_address`; `x1:A heap_address`; `state:(A,B)gc_state`;
    `s1:(A,B)gc_state`; `y1:((A heap_address,A)data_sort)heap_address`;
    `g1:((A heap_address,A)data_sort,B)gc_state`; `conf:B gen_gc_partial_conf`;
    `heap0:((A,B)heap_element)list`] gc_move_simulation) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "bnd" MATCH_MP_TAC THEN
    EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim1") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN SUBST_ALL_TAC) (LABEL_TAC "sub1"))) THEN
  SUBGOAL_THEN `heap_length (gc_state_heap (s1:(A,B)gc_state)) =
                heap_length (gc_state_heap (state:(A,B)gc_state))` (LABEL_TAC "hl1") THENL
   [CONV_TAC SYM_CONV THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP gc_move_heap_length);
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs1:(A heap_address)list`; `s1:(A,B)gc_state`;
    `s2:(A,B)gc_state`; `ys1:(((A heap_address,A)data_sort)heap_address)list`;
    `g2:((A heap_address,A)data_sort,B)gc_state`; `conf:B gen_gc_partial_conf`;
    `heap0:((A,B)heap_element)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "bnd" MATCH_MP_TAC THEN
    EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN SUBST_ALL_TAC) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[MAP] THEN
  ONCE_REWRITE_TAC[GC2AUX_all_old_ptrs_CONS] THEN
  USE_THEN "sub1" MP_TAC THEN POP_ASSUM MP_TAC THEN SET_TAC[]);;

let gc_move_list_APPEND = prove
 (`!(conf:B gen_gc_conf) (state0:(A,B)gc_state) xs ys roots' state'.
     gen_gc_gc_move_list conf state0 (APPEND xs ys) = (roots',state')
     ==> ?roots1 roots2 state1.
           gen_gc_gc_move_list conf state0 xs = (roots1,state1) /\
           gen_gc_gc_move_list conf state1 ys = (roots2,state') /\
           roots' = APPEND roots1 roots2`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; gen_gc_gc_move_list_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:(A heap_address)list`; `roots':(A heap_address)list`;
                          `state0:(A,B)gc_state`] THEN
    ASM_REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; gen_gc_gc_move_list_def] THEN
  GC2AUX_PAIR_TAC `gen_gc_gc_move (conf:B gen_gc_conf) (state0:(A,B)gc_state) h` "x1" "s1" THEN
  GC2AUX_PAIR_TAC `gen_gc_gc_move_list (conf:B gen_gc_conf) (s1:(A,B)gc_state)
                     (APPEND t ys)` "xs1" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A,B)gc_state`; `ys:(A heap_address)list`;
    `xs1:(A heap_address)list`; `s2:(A,B)gc_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(A heap_address)list` (X_CHOOSE_THEN `r2:(A heap_address)list`
    (X_CHOOSE_THEN `s3:(A,B)gc_state` STRIP_ASSUME_TAC))) THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`CONS (x1:A heap_address) r1`; `r2:(A heap_address)list`;
                        `s3:(A,B)gc_state`] THEN
  ASM_REWRITE_TAC[pair_CASE; APPEND]);;

let heap_restrict_NIL = prove
 (`!gen_start refs_start.
     heap_restrict gen_start refs_start ([]:((A,B)heap_element)list) = []`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_restrict_def; heap_segment_def; heap_split_def] THEN
  REPEAT(COND_CASES_TAC THEN CAKE_REWRITE_TAC[]) THEN
  REWRITE_TAC[heap_split_def; heap_length_NIL; SUB_0] THEN
  REPEAT(COND_CASES_TAC THEN CAKE_REWRITE_TAC[]));;
let _ = cake_add_simps [heap_restrict_NIL];;

let to_gen_heap_NIL = prove
 (`!(conf:C gen_gc_partial_conf).
     to_gen_heap conf ([]:((A,B)heap_element)list) = []`,
  REWRITE_TAC[to_gen_heap_def; heap_restrict_NIL; to_gen_heap_list_def; MAP]);;
let _ = cake_add_simps [to_gen_heap_NIL];;

let to_gen_heap_list_NIL = prove
 (`!(conf:C gen_gc_partial_conf).
     to_gen_heap_list conf ([]:((A,B)heap_element)list) = []`,
  REWRITE_TAC[to_gen_heap_list_def; MAP]);;
let _ = cake_add_simps [to_gen_heap_list_NIL];;

(* HOL4 proves three local theorems named gc_move_data_r1; all three are *)
(* bound here in turn                                                     *)
let gc_move_data_r1 = prove
 (`!refs (state:(A,B)gc_state) (conf:B gen_gc_partial_conf).
     gc_state_r1 (gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (combin_K refs) state)) = refs`,
  MESON_TAC[gc_move_data_IMP; gc_state_FIELDS.ri_accfupds; K_THM]);;

let gc_move_ref_list_simulation = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) (refs0:((A,B)heap_element)list)
    heap0 state1 state1' refs1 refs1'.
     gc_move_ref_list conf state refs0 = (refs1,state1) /\
     gen_gc_gc_move_list (to_gen_conf conf) (to_gen_state conf state)
       (refs_to_roots conf refs0) = (refs1',state1') /\
     gc_state_ok state1' /\
     sim_inv conf heap0 state /\
     (!ptrs l d ptr' (u:A). MEM (Pointer ptr' u) ptrs /\ MEM (DataElement ptrs l d) refs0
                            ==> ptr' < heap_length (gc_state_heap state)) /\
     heap_length (gc_state_heap state) = gen_gc_partial_conf_limit conf /\
     ALL isDataElement refs0
     ==> sim_inv conf heap0 state1 /\
         refs1' = refs_to_roots conf refs1 /\
         state1' = to_gen_state conf state1 /\
         has_old_ptr conf refs1 SUBSET has_old_ptr conf refs0`,
  MATCH_MP_TAC gc_move_ref_list_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[gc_move_ref_list_def; refs_to_roots_def; gen_gc_gc_move_list_def; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[refs_to_roots_def; SUBSET_REFL];
    ALL_TAC;
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct];
    REWRITE_TAC[ALL; isDataElement_def; heap_element_distinct]] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gc_move_ref_list_def; refs_to_roots_def; ALL; MEM] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf)
                     (state:(A,B)gc_state) ptrs` "p1" "s1" THEN
  GC2AUX_PAIR_TAC `gc_move_ref_list (conf:B gen_gc_partial_conf) (s1:(A,B)gc_state)
                     (xs:((A,B)heap_element)list)` "q1" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    LABEL_TAC "gm" (el 2 cs) THEN LABEL_TAC "ok2" (el 3 cs) THEN LABEL_TAC "sim" (el 4 cs) THEN
    LABEL_TAC "bnd" (el 5 cs) THEN LABEL_TAC "lim" (SYM (el 6 cs)) THEN
    LABEL_TAC "dxs" (el 8 cs) THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM) [el 0 cs; el 1 cs]) THEN
  USE_THEN "gm" (MP_TAC o MATCH_MP gc_move_list_APPEND) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(((A heap_address,A)data_sort)heap_address)list`
    (X_CHOOSE_THEN `r2:(((A heap_address,A)data_sort)heap_address)list`
      (X_CHOOSE_THEN `g1:((A heap_address,A)data_sort,B)gc_state`
        (CONJUNCTS_THEN2 (LABEL_TAC "gm1") (CONJUNCTS_THEN2 (LABEL_TAC "gm2")
          (LABEL_TAC "r12")))))) THEN
  SUBGOAL_THEN `gc_state_ok (g1:((A heap_address,A)data_sort,B)gc_state)` (LABEL_TAC "ok1")
  THENL
   [MATCH_MP_TAC gen_gc_gc_move_list_ok THEN
    MAP_EVERY EXISTS_TAC [`refs_to_roots (conf:B gen_gc_partial_conf)
                            (xs:((A,B)heap_element)list)`;
      `r2:(((A heap_address,A)data_sort)heap_address)list`;
      `state1':((A heap_address,A)data_sort,B)gc_state`; `to_gen_conf (conf:B gen_gc_partial_conf)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ptrs:(A heap_address)list`; `p1:(A heap_address)list`; `state:(A,B)gc_state`;
    `s1:(A,B)gc_state`; `r1:(((A heap_address,A)data_sort)heap_address)list`;
    `g1:((A heap_address,A)data_sort,B)gc_state`; `conf:B gen_gc_partial_conf`;
    `heap0:((A,B)heap_element)list`] gc_move_list_simulation) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "bnd" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ptrs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim1") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN SUBST_ALL_TAC) (LABEL_TAC "sub1"))) THEN
  SUBGOAL_THEN `heap_length (gc_state_heap (s1:(A,B)gc_state)) =
                heap_length (gc_state_heap (state:(A,B)gc_state))` (LABEL_TAC "hl1") THENL
   [CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP gen_gc_partial_gc_move_list_heap_length);
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`p1:(A heap_address)list`; `s1:(A,B)gc_state`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`heap0:((A,B)heap_element)list`; `s2:(A,B)gc_state`;
    `state1':((A heap_address,A)data_sort,B)gc_state`; `q1:((A,B)heap_element)list`;
    `r2:(((A heap_address,A)data_sort)heap_address)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "bnd" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ptrs':(A heap_address)list`; `l':num`; `d':B`; `u:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[refs_to_roots_def] THEN
  ONCE_REWRITE_TAC[GC2AUX_has_old_ptr_CONS] THEN REWRITE_TAC[has_old_ptr_simp] THEN
  USE_THEN "sub1" MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
    "SUBSET" with _ -> false)) THEN
  SET_TAC[]);;

let gc_move_list_r1 = prove
 (`!s0 xs ys (s1:(A,B)gc_state) (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list conf s0 xs = (ys,s1) ==> gc_state_r1 s1 = gc_state_r1 s0`,
  MESON_TAC[gen_gc_partial_gc_move_list_IMP]);;

let gc_move_data_r1 = prove
 (`!(conf:B gen_gc_partial_conf) (state':(A,B)gc_state) refs' state1.
     gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (combin_K refs') state') = state1
     ==> gc_state_r1 state1 = refs'`,
  MESON_TAC[gc_move_data_IMP; gc_state_FIELDS.ri_accfupds; K_THM]);;

let el_length_to_gen_heap_element = prove
 (`!(h:(A,B)heap_element) (conf:C gen_gc_partial_conf).
     el_length (to_gen_heap_element conf h) = el_length h`,
  REWRITE_TAC[GC2AUX_el_length_to_gen]);;

let to_gen_heap_address_11 = prove
 (`!x y (conf:C gen_gc_partial_conf).
     to_gen_heap_address conf x = to_gen_heap_address conf y ==> x = (y:A heap_address)`,
  MATCH_MP_TAC heap_address_INDUCT THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `y:A heap_address` (cases "heap_address")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[to_gen_heap_address_def] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[heap_address_11; heap_address_distinct; injectivity "data_sort";
              distinctness "data_sort"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MAP_to_gen_heap_address_11 = prove
 (`!x y (conf:C gen_gc_partial_conf).
     MAP (to_gen_heap_address conf) x = MAP (to_gen_heap_address conf) y <=>
     x = (y:(A heap_address)list)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[to_gen_heap_address_11]);;

let gc_forward_ptr_data_pres = prove
 (`!x a ptr (d:A) ok x' ok' xs l (dd:B).
     gc_forward_ptr a x ptr d ok = (x',ok')
     ==> (MEM (DataElement xs l dd) x <=>
          MEM (DataElement xs l dd) x' \/ heap_lookup a x = SOME (DataElement xs l dd))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_forward_ptr_def; heap_lookup_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MEM; option_DISTINCT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MEM; option_INJ; heap_element_distinct] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[option_DISTINCT]; ALL_TAC] THEN
  GC2AUX_PAIR_TAC `gc_forward_ptr (a - el_length (h:(A,B)heap_element)) (t:((A,B)heap_element)list)
                     ptr (d:A) ok`
    "y1" "k1" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MEM] THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ih th])) THEN
  MESON_TAC[]);;

let gc_move_data_pres = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) x x1 state1 xs l dd.
     gen_gc_partial_gc_move conf state x = (x1,state1)
     ==> (MEM (DataElement xs l dd) (APPEND (gc_state_heap state1) (gc_state_h2 state1)) <=>
          MEM (DataElement xs l dd) (APPEND (gc_state_heap state) (gc_state_h2 state)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP gc_forward_ptr_data_pres) THEN
  ASM_REWRITE_TAC[MEM_APPEND; MEM; option_INJ; heap_element_11] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MESON_TAC[]);;

let gc_move_list_data_pres = prove
 (`!x (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) x1 state1 xs l dd.
     gen_gc_partial_gc_move_list conf state x = (x1,state1)
     ==> (MEM (DataElement xs l dd) (APPEND (gc_state_heap state1) (gc_state_h2 state1)) <=>
          MEM (DataElement xs l dd) (APPEND (gc_state_heap state) (gc_state_h2 state)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) h`
    "y1" "s1" THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf) (s1:(A,B)gc_state) t`
    "ys1" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP gc_move_data_pres th)]) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC (MATCH_MP ih th))));;

let gc_move_ref_list_data_pres = prove
 (`!x (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) x1 state1 xs l dd.
     gc_move_ref_list conf state (x:((A,C)heap_element)list) = (x1,state1)
     ==> (MEM (DataElement xs l dd) (APPEND (gc_state_heap state1) (gc_state_h2 state1)) <=>
          MEM (DataElement xs l dd) (APPEND (gc_state_heap state) (gc_state_h2 state)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds];
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf) (state:(A,B)gc_state)
                     (a0:(A heap_address)list)` "p1" "s1" THEN
  GC2AUX_PAIR_TAC `gc_move_ref_list (conf:B gen_gc_partial_conf) (s1:(A,B)gc_state)
                     (t:((A,C)heap_element)list)` "q1" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP gc_move_list_data_pres th)]) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC (MATCH_MP ih th))));;

(* sim_inv after the scan of the first element of h2 *)
let GC2AUX_sim_inv_scan = prove
 (`!(conf:B gen_gc_partial_conf) heap0 old h1 xs l (d:B) t r4 r3 r2 r1 a n ok heap hp0
    xs' ok'.
     sim_inv conf heap0
       (gc_state_REC old h1 (CONS (DataElement xs l d) t) r4 r3 r2 r1 a n ok heap hp0) /\
     all_old_ptrs conf (xs':(A heap_address)list) SUBSET all_old_ptrs conf xs
     ==> sim_inv conf heap0
           (gc_state_REC old (APPEND h1 [DataElement xs' l d]) t r4 r3 r2 r1 a n ok' heap
              hp0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sim_inv_def; gc_state_FIELDS.ri_accessors] THEN
  REWRITE_TAC[NOT_CONS_NIL; APPEND_EQ_NIL] THEN
  REWRITE_TAC[heap_length_APPEND; heap_length_CONS; heap_length_NIL; el_length_def] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [ASM_ARITH_TAC;
    UNDISCH_TAC `has_old_ptr (conf:B gen_gc_partial_conf)
      (APPEND (APPEND (APPEND (heap:((A,B)heap_element)list) h1)
         (CONS (DataElement xs l d) t)) r1) SUBSET
      has_old_ptr conf (heap0:((A,B)heap_element)list)` THEN
    UNDISCH_TAC `all_old_ptrs (conf:B gen_gc_partial_conf) (xs':(A heap_address)list) SUBSET
                 all_old_ptrs conf (xs:(A heap_address)list)` THEN
    REWRITE_TAC[has_old_ptr_APPEND; has_old_ptr_simp] THEN
    ONCE_REWRITE_TAC[GC2AUX_has_old_ptr_CONS] THEN
    REWRITE_TAC[has_old_ptr_simp] THEN SET_TAC[]]);;

let GC2AUX_to_gen_state_accessors = prove
 (`!(conf:C gen_gc_partial_conf) (s:(A,B)gc_state).
     gc_state_old (to_gen_state conf s) = [] /\
     gc_state_h1 (to_gen_state conf s) = to_gen_heap_list conf (gc_state_h1 s) /\
     gc_state_h2 (to_gen_state conf s) = to_gen_heap_list conf (gc_state_h2 s) /\
     gc_state_r4 (to_gen_state conf s) = [] /\ gc_state_r3 (to_gen_state conf s) = [] /\
     gc_state_r2 (to_gen_state conf s) = [] /\ gc_state_r1 (to_gen_state conf s) = [] /\
     gc_state_a (to_gen_state conf s) = gc_state_a s - gen_gc_partial_conf_gen_start conf /\
     gc_state_n (to_gen_state conf s) = gc_state_n s /\
     gc_state_ok (to_gen_state conf s) = gc_state_ok s /\
     gc_state_heap (to_gen_state conf s) = to_gen_heap conf (gc_state_heap s) /\
     gc_state_heap0 (to_gen_state conf s) = to_gen_heap conf (gc_state_heap0 s)`,
  REWRITE_TAC[to_gen_state_def; empty_state_def; gc_state_FIELDS.ri_accfupds;
              gc_state_FIELDS.ri_accessors; K_THM]);;

let GC2AUX_to_gen_heap_list_CONS = prove
 (`!(conf:C gen_gc_partial_conf) (x:(A,B)heap_element) xs.
     to_gen_heap_list conf (CONS x xs) =
     CONS (to_gen_heap_element conf x) (to_gen_heap_list conf xs)`,
  REWRITE_TAC[to_gen_heap_list_def; MAP]);;

let GC2AUX_to_gen_HD = prove
 (`!(conf:C gen_gc_partial_conf) (h:((A,B)heap_element)list) zs n d.
     ~(to_gen_heap_list conf h = []) /\
     HD (to_gen_heap_list conf h) = DataElement (MAP (to_gen_heap_address conf) zs) n d
     ==> ?t. h = CONS (DataElement zs n d) t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[to_gen_heap_list_NIL; GC2AUX_to_gen_heap_list_CONS; NOT_CONS_NIL; HD] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[to_gen_heap_element_def; heap_element_distinct; heap_element_11;
              MAP_to_gen_heap_address_11; CONS_11] THEN
  MESON_TAC[]);;

let gc_move_data_simulation = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) heap0 state' (ptr1':C) state1'.
     gen_gc_partial_gc_move_data conf state = state' /\
     sim_inv conf heap0 state /\
     (!ptrs l d ptr' (u:A).
        MEM (Pointer ptr' u) ptrs /\
        MEM (DataElement ptrs l d) (APPEND (gc_state_h2 state) (gc_state_heap state))
        ==> ptr' < heap_length (gc_state_heap state)) /\
     heap_length (gc_state_heap state) = gen_gc_partial_conf_limit conf /\
     gen_gc_gc_move_data (to_gen_conf conf) (to_gen_state conf state) = state1' /\
     gc_state_ok state1'
     ==> sim_inv conf heap0 state' /\ state1' = to_gen_state conf state'`,
  MATCH_MP_TAC gen_gc_partial_gc_move_data_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_partial_conf`; `state:(A,B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "sim" (el 1 cs) THEN LABEL_TAC "bnd" (el 2 cs) THEN
    LABEL_TAC "lim" (SYM (el 3 cs)) THEN
    LABEL_TAC "ok2" (REWRITE_RULE[SYM (el 4 cs)] (el 5 cs)) THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM) [el 0 cs; el 4 cs]) THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_data_def] THEN
  REMOVE_THEN "ok2" (MP_TAC o ONCE_REWRITE_RULE[gen_gc_gc_move_data_def]) THEN
  REWRITE_TAC[GC2AUX_to_gen_state_accessors] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)`
    (REWRITE_TAC[to_gen_heap_list_NIL] THEN CAKE_REWRITE_TAC[] THEN
     USE_THEN "sim" (fun th -> REWRITE_TAC[th])) THEN
  REWRITE_TAC[GC2AUX_to_gen_heap_list_CONS] THEN CAKE_REWRITE_TAC[] THEN
  USE_THEN "sim" (STRIP_ASSUME_TAC o REWRITE_RULE[sim_inv_def; gen_inv_def]) THEN
  SUBGOAL_THEN
   `~(gen_gc_partial_conf_limit (conf:B gen_gc_partial_conf) <
      heap_length (APPEND (gc_state_h1 (state:(A,B)gc_state)) (CONS h t))) /\
    ~(gen_gc_conf_limit (to_gen_conf conf) <
      heap_length (APPEND (to_gen_heap_list conf (gc_state_h1 state))
        (CONS (to_gen_heap_element conf h) (to_gen_heap_list conf t))))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[to_gen_conf_def; gen_gc_conf_FIELDS.ri_accessors; heap_length_APPEND;
                heap_length_CONS; GC2AUX_el_length_to_gen; heap_length_to_gen_heap_list] THEN
    UNDISCH_TAC `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) +
                 heap_length (APPEND (gc_state_h1 (state:(A,B)gc_state)) (gc_state_h2 state)) +
                 gc_state_n state = gen_gc_partial_conf_refs_start conf` THEN
    USE_THEN "hd" (fun th -> REWRITE_TAC[th; heap_length_APPEND; heap_length_CONS]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[to_gen_heap_element_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM; GC2AUX_to_gen_state_accessors] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf)
                     (state:(A,B)gc_state) zs` "zs1" "s1" THEN
  GC2AUX_PAIR_TAC `gen_gc_gc_move_list (to_gen_conf (conf:B gen_gc_partial_conf))
      (to_gen_state conf (state:(A,B)gc_state)) (MAP (to_gen_heap_address conf) zs)`
    "ys1" "g1" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_THEN(LABEL_TAC "okm") THEN
  USE_THEN "okm" (MP_TAC o MATCH_MP gc_move_data_ok) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "okg1") (LABEL_TAC "hdg1")) THEN
  MP_TAC(ISPECL [`zs:(A heap_address)list`; `zs1:(A heap_address)list`; `state:(A,B)gc_state`;
    `s1:(A,B)gc_state`; `ys1:(((A heap_address,A)data_sort)heap_address)list`;
    `g1:((A heap_address,A)data_sort,B)gc_state`; `conf:B gen_gc_partial_conf`;
    `heap0:((A,B)heap_element)list`] gc_move_list_simulation) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "bnd" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
    ASM_REWRITE_TAC[MEM_APPEND; MEM];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim1") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN SUBST_ALL_TAC) (LABEL_TAC "sub1"))) THEN
  USE_THEN "hdg1" (MP_TAC o MATCH_MP GC2AUX_to_gen_HD o
    REWRITE_RULE[GC2AUX_to_gen_state_accessors]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A,B)heap_element)list` (LABEL_TAC "h21")) THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `s1:(A,B)gc_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accessors]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `h21:((A,B)heap_element)list`)) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM;
              GC2AUX_to_gen_state_REC; NOT_CONS_NIL; HD; TL; GC2AUX_to_gen_heap_list_CONS;
              to_gen_heap_element_def; GC2AUX_to_gen_heap_list_APPEND; to_gen_heap_list_NIL] THEN
  SUBGOAL_THEN `~(gen_gc_partial_conf_limit (conf:B gen_gc_partial_conf) <
      heap_length (APPEND (gc_state_h1 (state:(A,B)gc_state))
        (CONS (DataElement zs l d) t)))` (LABEL_TAC "nlim") THENL
   [UNDISCH_TAC `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) +
                 heap_length (APPEND (gc_state_h1 (state:(A,B)gc_state)) (gc_state_h2 state)) +
                 gc_state_n state = gen_gc_partial_conf_refs_start conf` THEN
    USE_THEN "hd" (fun th -> REWRITE_TAC[th; heap_length_APPEND; heap_length_CONS]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "IH" (fun ih -> USE_THEN "hd" (fun hd -> USE_THEN "nlim" (fun nl ->
    FIRST_ASSUM(fun mv -> MP_TAC(MATCH_MP (MATCH_MP (MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) hd) nl)
      mv))))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM; NOT_CONS_NIL;
              HD; TL] THEN
  DISCH_THEN(MP_TAC o SPEC `heap0:((A,B)heap_element)list`) THEN
  DISCH_THEN(fun th ->
    let vs,body = strip_forall (concl th) in
    let ants,_ = splitlist dest_imp body in
    let t1 = lhs (el 0 ants) and t2 = lhs (el 4 ants) in
    MP_TAC (REWRITE_RULE[] (SPECL [t1; t2] th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC GC2AUX_sim_inv_scan THEN
    MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `ok1:bool`] THEN
    USE_THEN "sim1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "sub1" ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "hl1" o REWRITE_RULE[gc_state_FIELDS.ri_accessors] o
    MATCH_MP gen_gc_partial_gc_move_list_heap_length) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "hl1" (SUBST1_TAC o SYM) THEN
    USE_THEN "bnd" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ptrs:(A heap_address)list`; `l':num`; `d':B`; `u:A`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`ptrs:(A heap_address)list`; `l':num`; `d':B`] o
      MATCH_MP gc_move_list_data_pres) THEN
    UNDISCH_TAC `MEM (DataElement (ptrs:(A heap_address)list) l' (d':B))
      (APPEND t1 heap1)` THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accessors; MEM_APPEND; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [USE_THEN "hl1" (SUBST1_TAC o SYM) THEN USE_THEN "lim" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ANTS_TAC THENL
   [USE_THEN "okm" MP_TAC THEN
    REWRITE_TAC[GC2AUX_to_gen_state_REC; gc_state_FIELDS.ri_accessors;
      gc_state_FIELDS.ri_fupds; K_THM; NOT_CONS_NIL; HD; TL; GC2AUX_to_gen_heap_list_CONS;
      GC2AUX_to_gen_heap_list_APPEND; to_gen_heap_list_NIL; to_gen_heap_element_def];
    ALL_TAC] THEN
  REWRITE_TAC[GC2AUX_to_gen_state_REC; GC2AUX_to_gen_heap_list_CONS;
    GC2AUX_to_gen_heap_list_APPEND; to_gen_heap_list_NIL; to_gen_heap_element_def]);;

let gc_move_with_refs = prove
 (CASE_TERM `!l (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) refs.
     gen_gc_partial_gc_move conf (gc_state_r1_fupd (combin_K refs) state) l =
     match gen_gc_partial_gc_move conf state l with (xs,s) ->
     (xs,gc_state_r1_fupd (combin_K refs) s)`,
  GEN_TAC THEN CASES_ON `l:A heap_address` THEN REPEAT GEN_TAC THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF;
    gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  CAKE_REWRITE_TAC[gc_state_FIELDS.ri_fupds; K_THM] THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN RW[]);;

let gc_move_with_refs' = prove
 (CASE_TERM `!l (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) refs.
     gen_gc_partial_gc_move conf
       (gc_state_r1_fupd (combin_K refs) (gc_state_r2_fupd (combin_K []) state)) l =
     match gen_gc_partial_gc_move conf state l with (xs,s) ->
     (xs,gc_state_r1_fupd (combin_K refs) (gc_state_r2_fupd (combin_K []) s))`,
  GEN_TAC THEN CASES_ON `l:A heap_address` THEN REPEAT GEN_TAC THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `state:(A,B)gc_state` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF;
    gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  CAKE_REWRITE_TAC[gc_state_FIELDS.ri_fupds; K_THM] THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN RW[]);;

let gc_move_list_with_refs = prove
 (CASE_TERM `!l (state:(A,B)gc_state) (conf:B gen_gc_partial_conf) refs.
     gen_gc_partial_gc_move_list conf (gc_state_r1_fupd (combin_K refs) state) l =
     match gen_gc_partial_gc_move_list conf state l with (xs,s) ->
     (xs,gc_state_r1_fupd (combin_K refs) s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gc_move_with_refs] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move (conf:B gen_gc_partial_conf)
    (state:(A,B)gc_state) h` "x1" "s1" THEN
  ASM_REWRITE_TAC[] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf)
    (s1:(A,B)gc_state) t` "x2" "s2" THEN
  REWRITE_TAC[]);;

let gc_move_list_with_refs' = prove
 (CASE_TERM `!l (state:(A,B)gc_state) (conf:B gen_gc_partial_conf) refs.
     gen_gc_partial_gc_move_list conf
       (gc_state_r1_fupd (combin_K refs) (gc_state_r2_fupd (combin_K []) state)) l =
     match gen_gc_partial_gc_move_list conf state l with (xs,s) ->
     (xs,gc_state_r1_fupd (combin_K refs) (gc_state_r2_fupd (combin_K []) s))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gc_move_with_refs'] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move (conf:B gen_gc_partial_conf)
    (state:(A,B)gc_state) h` "x1" "s1" THEN
  ASM_REWRITE_TAC[] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf)
    (s1:(A,B)gc_state) t` "x2" "s2" THEN
  REWRITE_TAC[]);;

let gc_move_data_with_refs = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) refs.
     gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (combin_K refs) state) =
     gc_state_r1_fupd (combin_K refs) (gen_gc_partial_gc_move_data conf state)`,
  MATCH_MP_TAC gen_gc_partial_gc_move_data_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_partial_conf`; `state:(A,B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)` (CAKE_REWRITE_TAC[]) THEN
  CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_fupdcanon] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_fupdcanon] THEN
  REWRITE_TAC[gc_move_list_with_refs] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf)
    (state:(A,B)gc_state) zs` "xs1" "s1" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `s1:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  USE_THEN "IH" (fun ih -> USE_THEN "hd" (fun hd -> FIRST_ASSUM(fun nl -> FIRST_ASSUM(fun mv ->
    MP_TAC(MATCH_MP (MATCH_MP (MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) hd) nl) mv))))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  DISCH_THEN MATCH_ACCEPT_TAC);;

let gc_move_data_with_refs' = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state) refs.
     gen_gc_partial_gc_move_data conf (gc_state_r1_fupd (combin_K refs) (gc_state_r2_fupd (combin_K []) state)) =
     gc_state_r1_fupd (combin_K refs) (gc_state_r2_fupd (combin_K [])
       (gen_gc_partial_gc_move_data conf state))`,
  MATCH_MP_TAC gen_gc_partial_gc_move_data_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_partial_conf`; `state:(A,B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)` (CAKE_REWRITE_TAC[]) THEN
  CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_fupdcanon] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_fupdcanon] THEN
  REWRITE_TAC[REWRITE_RULE[gc_state_FIELDS.ri_fupdcanon] gc_move_list_with_refs'] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf)
    (state:(A,B)gc_state) zs` "xs1" "s1" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  GC2AUX_STATE_TAC (map (fun x -> x^"1") GC2AUX_FIELDS) `s1:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  USE_THEN "IH" (fun ih -> USE_THEN "hd" (fun hd -> FIRST_ASSUM(fun nl -> FIRST_ASSUM(fun mv ->
    MP_TAC(MATCH_MP (MATCH_MP (MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) hd) nl) mv))))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM;
              gc_state_FIELDS.ri_fupdcanon] THEN
  DISCH_THEN MATCH_ACCEPT_TAC);;

let gen_gc_partial_gc_move_data_h2 = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state).
     gc_state_ok (gen_gc_partial_gc_move_data conf state)
     ==> gc_state_h2 (gen_gc_partial_gc_move_data conf state) = []`,
  MATCH_MP_TAC gen_gc_partial_gc_move_data_ind THEN
  MAP_EVERY X_GEN_TAC [`conf:B gen_gc_partial_conf`; `state:(A,B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)`
    (CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]) THEN
  CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (conf:B gen_gc_partial_conf)
    (state:(A,B)gc_state) zs` "xs1" "s1" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  USE_THEN "IH" (fun ih -> USE_THEN "hd" (fun hd -> FIRST_ASSUM(fun nl -> FIRST_ASSUM(fun mv ->
    ACCEPT_TAC(MATCH_MP (MATCH_MP (MATCH_MP (REWRITE_RULE[IMP_CONJ] ih) hd) nl) mv))))));;

(* HOL4 states gc_move_ref_list_heap_length a second time (local); bound    *)
(* again here to keep the script order                                      *)
let gc_move_ref_list_heap_length = prove
 (`!h x (state:(A,B)gc_state) state' (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state (h:((A,C)heap_element)list) = (x,state')
     ==> heap_length (gc_state_heap state) = heap_length (gc_state_heap state')`,
  MATCH_ACCEPT_TAC gc_move_ref_list_heap_length);;

(* the third HOL4 theorem named gc_move_data_r1                             *)
let gc_move_data_r1 = prove
 (`!(conf:B gen_gc_partial_conf) (state:(A,B)gc_state).
     gc_state_r1 (gen_gc_partial_gc_move_data conf state) = gc_state_r1 state`,
  MESON_TAC[gc_move_data_IMP]);;

let GC2AUX_to_gen_state_r12 = prove
 (`!(conf:C gen_gc_partial_conf) (s:(A,B)gc_state) f.
     to_gen_state conf (gc_state_r1_fupd f s) = to_gen_state conf s /\
     to_gen_state conf (gc_state_r2_fupd f s) = to_gen_state conf s`,
  REWRITE_TAC[to_gen_state_def; gc_state_FIELDS.ri_accfupds]);;

let GC2AUX_sim_inv_r1 = prove
 (`!(conf:B gen_gc_partial_conf) (heap0:((A,B)heap_element)list) s refs.
     sim_inv conf heap0 s /\ has_old_ptr conf refs SUBSET has_old_ptr conf heap0
     ==> sim_inv conf heap0 (gc_state_r2_fupd (combin_K []) (gc_state_r1_fupd (combin_K refs) s))`,
  REWRITE_TAC[sim_inv_def; gc_state_FIELDS.ri_accfupds; K_THM; has_old_ptr_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let GC2AUX_partial_loop = prove
 (`!(conf:B gen_gc_partial_conf) (heap0:((A,B)heap_element)list) s2.
     sim_inv conf heap0 s2 /\
     (!ptrs l d ptr' (u:A).
        MEM (Pointer ptr' u) ptrs /\
        MEM (DataElement ptrs l d) (APPEND (gc_state_h2 s2) (gc_state_heap s2))
        ==> ptr' < heap_length (gc_state_heap s2)) /\
     heap_length (gc_state_heap s2) = gen_gc_partial_conf_limit conf /\
     gc_state_ok (gen_gc_gc_move_loop (to_gen_conf conf) (to_gen_state conf s2)
                    (gen_gc_conf_limit (to_gen_conf conf)))
     ==> gen_gc_gc_move_loop (to_gen_conf conf) (to_gen_state conf s2)
           (gen_gc_conf_limit (to_gen_conf conf)) =
         to_gen_state conf (gen_gc_partial_gc_move_data conf s2) /\
         sim_inv conf heap0 (gen_gc_partial_gc_move_data conf s2) /\
         gc_state_h2 (gen_gc_partial_gc_move_data conf s2) = [] /\
         gc_state_ok (gen_gc_partial_gc_move_data conf s2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "sim" (el 0 cs) THEN LABEL_TAC "bnd" (el 1 cs) THEN
    LABEL_TAC "lim" (el 2 cs) THEN MP_TAC (el 3 cs)) THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_loop_def] THEN
  REWRITE_TAC[GC2AUX_to_gen_state_accessors] THEN CAKE_REWRITE_TAC[] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (s2:(A,B)gc_state)`
   (REWRITE_TAC[to_gen_heap_list_NIL] THEN CAKE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `gen_gc_partial_gc_move_data (conf:B gen_gc_partial_conf) (s2:(A,B)gc_state) = s2`
      SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN ASM_REWRITE_TAC[] THEN
      CAKE_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GC2AUX_to_gen_state_accessors] THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[GC2AUX_to_gen_heap_list_CONS] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN
  DISCH_THEN(LABEL_TAC "okl") THEN
  USE_THEN "okl" (LABEL_TAC "ok5" o MATCH_MP gen_gc_gc_move_loop_ok) THEN
  MP_TAC(ISPECL [`conf:B gen_gc_partial_conf`; `s2:(A,B)gc_state`;
    `heap0:((A,B)heap_element)list`;
    `gen_gc_partial_gc_move_data (conf:B gen_gc_partial_conf) (s2:(A,B)gc_state)`;
    `ARB:num`;
    `gen_gc_gc_move_data (to_gen_conf (conf:B gen_gc_partial_conf))
       (to_gen_state conf (s2:(A,B)gc_state))`] gc_move_data_simulation) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "simd") (LABEL_TAC "s5eq")) THEN
  USE_THEN "s5eq" (fun eq -> USE_THEN "ok5" (LABEL_TAC "okd" o
    REWRITE_RULE[GC2AUX_to_gen_state_accessors] o ONCE_REWRITE_RULE[eq])) THEN
  USE_THEN "okd" (LABEL_TAC "h2d" o MATCH_MP gen_gc_partial_gc_move_data_h2) THEN
  USE_THEN "s5eq" (fun eq -> REWRITE_TAC[eq]) THEN
  ONCE_REWRITE_TAC[gen_gc_gc_move_loop_def] THEN
  REWRITE_TAC[GC2AUX_to_gen_state_accessors] THEN CAKE_REWRITE_TAC[] THEN
  USE_THEN "h2d" (fun th -> REWRITE_TAC[th; to_gen_heap_list_NIL]) THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;
let GC2AUX_SPLIT_TAC (n1:string) (n2:string) : tactic =
  fun (asl,w as gl) ->
    let is_cand t =
      is_case_app t &&
      (let c,x,_ = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) && free_in x w) in
    let t = find_term is_cand w in
    let _,x,_ = dest_case_app t in
    GC2AUX_PAIR_TAC x n1 n2 gl;;
let GC2AUX_heap_gen_ok_seg = prove
 (`!(conf:B gen_gc_partial_conf) (heap:((A,B)heap_element)list) old current refs.
     heap_gen_ok heap conf /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (old,current,refs)
     ==> ALL isDataElement old /\
         (!ptr xs l d (u:A). MEM (DataElement xs l d) old /\ MEM (Pointer ptr u) xs
                             ==> ptr < gen_gc_partial_conf_gen_start conf \/
                                 gen_gc_partial_conf_refs_start conf <= ptr)`,
  REWRITE_TAC[heap_gen_ok_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `o1:((A,B)heap_element)list` (X_CHOOSE_THEN `c1:((A,B)heap_element)list`
      (X_CHOOSE_THEN `r1:((A,B)heap_element)list` STRIP_ASSUME_TAC)))
    ASSUME_TAC) THEN
  SUBGOAL_THEN `o1:((A,B)heap_element)list = old` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[option_INJ; PAIR_EQ]; ASM_REWRITE_TAC[]]);;
let partial_gc_simulation = prove
 (`!(conf:B gen_gc_partial_conf) (roots:(A heap_address)list) (heap0:((A,B)heap_element)list)
    roots1 state1 heap0_old heap0_current heap0_refs new_roots new_state.
     partial_gc conf (roots,heap0) = (roots1,state1) /\
     heap_gen_ok heap0 conf /\
     gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf /\
     gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit conf /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap0 = SOME (heap0_old,heap0_current,heap0_refs) /\
     ALL (\e. ~heap_element_is_ref conf e) (APPEND heap0_old heap0_current) /\
     ALL isDataElement heap0_refs /\
     roots_ok roots heap0 /\
     gen_gc (to_gen_conf conf)
       (APPEND (to_gen_roots conf roots) (refs_to_roots conf heap0_refs),
        to_gen_heap_list conf heap0_current) = (new_roots,new_state) /\
     heap_ok heap0 (gen_gc_partial_conf_limit conf) /\ gc_state_ok new_state
     ==> new_roots = APPEND (to_gen_roots conf roots1)
                       (refs_to_roots conf (gc_state_r1 state1)) /\
         new_state = to_gen_state conf state1 /\
         sim_inv conf heap0 state1 /\ gc_state_h2 state1 = [] /\ gc_state_ok state1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MP_TAC (el 0 cs) THEN LABEL_TAC "hgo" (el 1 cs) THEN LABEL_TAC "gr" (el 2 cs) THEN
    LABEL_TAC "rl" (el 3 cs) THEN LABEL_TAC "seg" (el 4 cs) THEN LABEL_TAC "nref" (el 5 cs) THEN
    LABEL_TAC "rdata" (el 6 cs) THEN LABEL_TAC "rok" (el 7 cs) THEN MP_TAC (el 8 cs) THEN
    LABEL_TAC "hok" (el 9 cs) THEN LABEL_TAC "nok" (el 10 cs)) THEN
  USE_THEN "seg" (fun th -> let cs = CONJUNCTS (MATCH_MP heap_segment_IMP th) in
    LABEL_TAC "happ" (el 0 cs) THEN LABEL_TAC "hlo" (el 1 cs) THEN
    LABEL_TAC "hloc" (el 2 cs) THEN LABEL_TAC "hlr" (el 3 cs)) THEN
  SUBGOAL_THEN `gen_gc_conf_limit (to_gen_conf (conf:B gen_gc_partial_conf)) =
                heap_length (heap0_current:((A,B)heap_element)list)` (LABEL_TAC "glim") THENL
   [REWRITE_TAC[to_gen_conf_def; gen_gc_conf_FIELDS.ri_accessors] THEN
    UNDISCH_TAC `heap_length (APPEND (heap0_old:((A,B)heap_element)list) heap0_current) =
                 gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)` THEN
    REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[gen_gc_def; LET_DEF; LET_END_DEF; empty_state_def; gc_state_FIELDS.ri_fupds;
              K_THM; heap_length_to_gen_heap_list] THEN
  USE_THEN "glim" (fun th -> REWRITE_TAC[th]) THEN
  ALL_TAC THEN
  SUBGOAL_THEN `to_gen_state (conf:B gen_gc_partial_conf)
     (gc_state_REC (heap0_old:((A,B)heap_element)list) [] [] [] [] heap0_refs []
        (gen_gc_partial_conf_gen_start conf) (heap_length heap0_current) T heap0 []) =
   gc_state_REC [] [] [] [] [] [] [] 0 (heap_length heap0_current) T
     (to_gen_heap_list conf heap0_current) []` (LABEL_TAC "tgA") THENL
   [REWRITE_TAC[GC2AUX_to_gen_state_REC; to_gen_heap_NIL; to_gen_heap_list_NIL; SUB_REFL] THEN
    REWRITE_TAC[to_gen_heap_def; heap_restrict_def] THEN
    USE_THEN "seg" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[partial_gc_def] THEN USE_THEN "seg" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; empty_state_def; gc_state_FIELDS.ri_fupds; K_THM] THEN
  GC2AUX_SPLIT_TAC "rootsB" "sB" THEN GC2AUX_SPLIT_TAC "rootsA" "s1" THEN
  GC2AUX_SPLIT_TAC "refsA" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[REWRITE_RULE[gc_state_FIELDS.ri_fupdcanon] gc_move_data_with_refs';
              gc_state_FIELDS.ri_accfupds; K_THM; GC2AUX_to_gen_state_r12] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gc_move_list_APPEND) THEN
  DISCH_THEN(X_CHOOSE_THEN `rB1:(((A heap_address,A)data_sort)heap_address)list`
    (X_CHOOSE_THEN `rB2:(((A heap_address,A)data_sort)heap_address)list`
    (X_CHOOSE_THEN `sB1:((A heap_address,A)data_sort,B)gc_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "gm1") (CONJUNCTS_THEN2 (LABEL_TAC "gm2") SUBST_ALL_TAC))))) THEN
  USE_THEN "nok" (LABEL_TAC "okB" o MATCH_MP gen_gc_gc_move_loop_ok) THEN
  USE_THEN "gm2" (fun g2 -> USE_THEN "okB" (fun ok ->
    LABEL_TAC "okB1" (MATCH_MP gen_gc_gc_move_list_ok (CONJ g2 ok)))) THEN
  USE_THEN "hok" (fun th -> let cs = CONJUNCTS (REWRITE_RULE[heap_ok_def] th) in
    LABEL_TAC "hl0" (el 0 cs) THEN LABEL_TAC "nfp" (el 1 cs) THEN LABEL_TAC "hok3" (el 2 cs)) THEN
  SUBGOAL_THEN `sim_inv (conf:B gen_gc_partial_conf) heap0
     (gc_state_REC (heap0_old:((A,B)heap_element)list) [] [] [] [] heap0_refs []
        (gen_gc_partial_conf_gen_start conf)
        (heap_length (heap0_current:((A,B)heap_element)list)) T heap0 [])`
    (LABEL_TAC "simA") THENL
   [REWRITE_TAC[sim_inv_def; gen_inv_def; gc_state_FIELDS.ri_accessors; APPEND_NIL;
                heap_length_APPEND; heap_length_NIL; ADD_CLAUSES; LE_REFL; SUBSET_REFL] THEN
    USE_THEN "gr" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `heap_length (APPEND (heap0_old:((A,B)heap_element)list) heap0_current) =
                 gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)` THEN
    USE_THEN "hlo" (fun th -> REWRITE_TAC[heap_length_APPEND; th]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; LE_REFL]) THEN
    MAP_EVERY EXISTS_TAC [`heap0_old:((A,B)heap_element)list`;
      `heap0_current:((A,B)heap_element)list`; `heap0_refs:((A,B)heap_element)list`] THEN
    USE_THEN "seg" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "rdata" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nref" (fun th -> REWRITE_TAC[REWRITE_RULE[ALL_APPEND] th]) THEN
    USE_THEN "hgo" (fun h -> USE_THEN "seg" (fun s ->
      MP_TAC (MATCH_MP GC2AUX_heap_gen_ok_seg (CONJ h s)))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th] THEN ASSUME_TAC (CONJUNCT2 th)) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "nfp" (MP_TAC o REWRITE_RULE[FILTER_EQ_NIL; GSYM ALL_MEM]) THEN
      DISCH_THEN(MP_TAC o SPEC `ForwardPointer n (a:A) d:(A,B)heap_element`) THEN
      ASM_REWRITE_TAC[isForwardPointer_def];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`roots:(A heap_address)list`; `rootsA:(A heap_address)list`;
    `gc_state_REC (heap0_old:((A,B)heap_element)list) [] [] [] [] heap0_refs []
        (gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf))
        (heap_length (heap0_current:((A,B)heap_element)list)) T heap0 []`;
    `s1:(A,B)gc_state`; `rB1:(((A heap_address,A)data_sort)heap_address)list`;
    `sB1:((A heap_address,A)data_sort,B)gc_state`; `conf:B gen_gc_partial_conf`;
    `heap0:((A,B)heap_element)list`] gc_move_list_simulation) THEN
  ANTS_TAC THENL
   [USE_THEN "tgA" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
    USE_THEN "simA" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "hl0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "okB1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gm1" (fun th -> REWRITE_TAC[REWRITE_RULE[to_gen_roots_def] th]) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "hl0" (SUBST1_TAC o SYM) THEN
    USE_THEN "rok" (MP_TAC o SPECL [`ptr':num`; `u:A`] o REWRITE_RULE[roots_ok_def]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[heap_lookup_LESS];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim1") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN SUBST_ALL_TAC) (LABEL_TAC "aop1"))) THEN
  FIRST_ASSUM(LABEL_TAC "hls1" o REWRITE_RULE[gc_state_FIELDS.ri_accessors] o
    MATCH_MP gen_gc_partial_gc_move_list_heap_length) THEN
  FIRST_ASSUM(LABEL_TAC "hls2" o MATCH_MP gc_move_ref_list_heap_length) THEN
  MP_TAC(ISPECL [`conf:B gen_gc_partial_conf`; `s1:(A,B)gc_state`;
    `heap0_refs:((A,B)heap_element)list`; `heap0:((A,B)heap_element)list`;
    `s2:(A,B)gc_state`; `sB:((A heap_address,A)data_sort,B)gc_state`;
    `refsA:((A,B)heap_element)list`; `rB2:(((A heap_address,A)data_sort)heap_address)list`]
    gc_move_ref_list_simulation) THEN
  ANTS_TAC THENL
   [USE_THEN "gm2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "okB" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sim1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "rdata" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "hls1" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "hl0" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "hl0" (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `isSomeDataElement (heap_lookup ptr' (heap0:((A,B)heap_element)list))` MP_TAC THENL
     [USE_THEN "hok3" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`ptrs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th; MEM_APPEND]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[heap_lookup_LESS]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sim2") (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "hop2")))) THEN
  MP_TAC(ISPECL [`conf:B gen_gc_partial_conf`; `heap0:((A,B)heap_element)list`;
    `s2:(A,B)gc_state`] GC2AUX_partial_loop) THEN
  USE_THEN "glim" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [USE_THEN "sim2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nok" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "hls2" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "hls1" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "hl0" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN USE_THEN "hl0" (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `MEM (DataElement ptrs l d) (heap0:((A,B)heap_element)list)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`ptrs:(A heap_address)list`; `l:num`; `d:B`] o
        MATCH_MP gc_move_ref_list_data_pres) THEN
      FIRST_ASSUM(MP_TAC o SPECL [`ptrs:(A heap_address)list`; `l:num`; `d:B`] o
        MATCH_MP gc_move_list_data_pres) THEN
      REWRITE_TAC[gc_state_FIELDS.ri_accessors; APPEND_NIL] THEN
      UNDISCH_TAC `MEM (DataElement ptrs l d)
        (APPEND (gc_state_h2 s2) (gc_state_heap (s2:(A,B)gc_state)))` THEN
      REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `isSomeDataElement (heap_lookup ptr' (heap0:((A,B)heap_element)list))` MP_TAC THENL
     [USE_THEN "hok3" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`ptrs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[heap_lookup_LESS]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; to_gen_roots_def] THEN
    MATCH_MP_TAC GC2AUX_sim_inv_r1 THEN REWRITE_TAC[th]) THEN
  USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th; has_old_ptr_APPEND]) THEN
  USE_THEN "hop2" MP_TAC THEN SET_TAC[]);;

let f_old_ptrs_def = cake_def
  `f_old_ptrs (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) =
     {a | isSomeDataElement (heap_lookup a heap) /\
          (a < gen_gc_partial_conf_gen_start conf \/
           gen_gc_partial_conf_refs_start conf <= a)}`;;

let f_old_ptrs_finite = prove
 (`!(heap:((A,B)heap_element)list) (conf:C gen_gc_partial_conf).
     FINITE (f_old_ptrs conf heap)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{a:num | a < heap_length (heap:((A,B)heap_element)list)}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; f_old_ptrs_def; SUBSET; IN_ELIM_THM;
              isSomeDataElement_def] THEN
  MESON_TAC[heap_lookup_LESS]);;

let _ = cake_add_simps [f_old_ptrs_finite];;

let f_old_ptrs_finite_open = REWRITE_RULE[f_old_ptrs_def] f_old_ptrs_finite;;

let _ = cake_add_simps [f_old_ptrs_finite_open];;

let new_f_def = cake_def
  `new_f (f:(num,num)fmap) (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) =
     FUNION (FUN_FMAP I (f_old_ptrs conf heap))
       (FUN_FMAP (\a. gen_gc_partial_conf_gen_start conf +
                      FAPPLY f (a - gen_gc_partial_conf_gen_start conf))
          (IMAGE ((+) (gen_gc_partial_conf_gen_start conf)) (FDOM f)))`;;

let APPEND_LENGTH_IMP = prove
 (`!a c b (d:A list).
     APPEND a b = APPEND c d /\ LENGTH a = LENGTH c ==> a = c /\ b = d`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONS_11] THEN
  ASM_MESON_TAC[]);;

let roots_ok_APPEND = prove
 (`!left right (heap:((A,B)heap_element)list).
     roots_ok (APPEND left right) heap ==> roots_ok left heap /\ roots_ok right heap`,
  REWRITE_TAC[roots_ok_def; MEM_APPEND] THEN MESON_TAC[]);;

let roots_ok_CONS = prove
 (`!h t (heap:((A,B)heap_element)list).
     roots_ok (CONS h t) heap ==> roots_ok t heap`,
  REWRITE_TAC[roots_ok_def; MEM] THEN MESON_TAC[]);;

let isSomeDataElement_to_gen_heap_list = prove
 (`!n (heap:((A,B)heap_element)list) (conf:C gen_gc_partial_conf).
     isSomeDataElement (heap_lookup n (to_gen_heap_list conf heap)) =
     isSomeDataElement (heap_lookup n heap)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GC2AUX_heap_lookup_to_gen] THEN
  SPEC_TAC(`heap_lookup n (heap:((A,B)heap_element)list)`,
           `o1:((A,B)heap_element)option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; isSomeDataElement_def; option_DISTINCT; option_INJ] THEN
  MATCH_MP_TAC heap_element_INDUCT THEN
  REWRITE_TAC[to_gen_heap_element_def; heap_element_distinct; heap_element_11] THEN
  MESON_TAC[]);;

let _ = cake_add_simps [isSomeDataElement_to_gen_heap_list];;

let isSomeDataElement_to_gen_heap_element =
  REWRITE_RULE[to_gen_heap_list_def] isSomeDataElement_to_gen_heap_list;;

let _ = cake_add_simps [isSomeDataElement_to_gen_heap_element];;

(* the pointer case of MEM_to_gen_roots_IMP_MEM, shared with                 *)
(* MEM_refs_to_roots_IMP_MEM and MEM_to_gen_heap_IMP_MEM                     *)
let GC2AUX_MEM_MAP_to_gen_address = prove
 (`!(xs:(A heap_address)list) ptr u (conf:C gen_gc_partial_conf).
     MEM (Pointer ptr u) (MAP (to_gen_heap_address conf) xs)
     ==> ?ptr' u'. MEM (Pointer ptr' u') xs /\
                   ptr = ptr' - gen_gc_partial_conf_gen_start conf /\
                   u = Real u' /\ gen_gc_partial_conf_gen_start conf <= ptr' /\
                   ptr' < gen_gc_partial_conf_refs_start conf`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `h:A heap_address` (cases "heap_address")) THEN
  REWRITE_TAC[to_gen_heap_address_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[heap_address_distinct; heap_address_11] THEN
  ASM_MESON_TAC[NOT_LESS; NOT_LE]);;

let MEM_refs_to_roots_IMP_MEM = prove
 (`!(heap_refs:((A,B)heap_element)list) ptr u (conf:C gen_gc_partial_conf).
     MEM (Pointer ptr u) (refs_to_roots conf heap_refs)
     ==> ?xs l d ptr' u'.
           MEM (DataElement xs l d) heap_refs /\ MEM (Pointer ptr' u') xs /\
           ptr = ptr' - gen_gc_partial_conf_gen_start conf /\ u = Real u' /\
           gen_gc_partial_conf_gen_start conf <= ptr' /\
           ptr' < gen_gc_partial_conf_refs_start conf`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[refs_to_roots_def; MEM] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[refs_to_roots_def; MEM; MEM_APPEND] THEN REPEAT GEN_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    DISCH_THEN(DISJ_CASES_THEN2 (MP_TAC o MATCH_MP GC2AUX_MEM_MAP_to_gen_address)
      (MP_TAC o check (is_comb o concl))) THEN
    ASM_MESON_TAC[]]);;

let MEM_to_gen_roots_IMP_MEM = prove
 (`!roots ptr u (conf:C gen_gc_partial_conf).
     MEM (Pointer ptr u) (to_gen_roots conf (roots:(A heap_address)list))
     ==> ?ptr' u'. MEM (Pointer ptr' u') roots /\
                   ptr = ptr' - gen_gc_partial_conf_gen_start conf /\
                   u = Real u' /\ gen_gc_partial_conf_gen_start conf <= ptr' /\
                   ptr' < gen_gc_partial_conf_refs_start conf`,
  REWRITE_TAC[to_gen_roots_def; GC2AUX_MEM_MAP_to_gen_address]);;

let GC2AUX_lookup_current = prove
 (`!(heap:((A,B)heap_element)list) a b old cur refs p.
     heap_segment (a,b) heap = SOME (old,cur,refs) /\ a <= p /\ p < b
     ==> heap_lookup p heap = heap_lookup (p - a) cur`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP heap_segment_IMP) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    SUBST1_TAC (SYM (el 0 cs)) THEN ASSUME_TAC (el 1 cs) THEN ASSUME_TAC (el 2 cs)) THEN
  SUBGOAL_THEN `~(p < a)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN ASM_REWRITE_TAC[]);;

let roots_ok_simulation = prove
 (`!roots (heap:((A,B)heap_element)list) heap_old heap_current heap_refs
    (conf:B gen_gc_partial_conf).
     roots_ok roots heap /\
     heap_ok heap (gen_gc_partial_conf_limit conf) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (heap_old,heap_current,heap_refs) /\
     gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf
     ==> roots_ok (APPEND (to_gen_roots conf roots) (refs_to_roots conf heap_refs))
           (MAP (to_gen_heap_element conf) heap_current)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "rok" (el 0 cs) THEN LABEL_TAC "hok" (el 1 cs) THEN
    LABEL_TAC "seg" (el 2 cs)) THEN
  REWRITE_TAC[roots_ok_def; MEM_APPEND; isSomeDataElement_to_gen_heap_element] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN2
    (MP_TAC o MATCH_MP MEM_to_gen_roots_IMP_MEM)
    (MP_TAC o MATCH_MP MEM_refs_to_roots_IMP_MEM)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "seg" (fun s -> FIRST_ASSUM(fun a -> FIRST_ASSUM(fun b ->
    REWRITE_TAC[GSYM (MATCH_MP GC2AUX_lookup_current (CONJ s (CONJ a b)))]))) THENL
   [USE_THEN "rok" (MATCH_MP_TAC o REWRITE_RULE[roots_ok_def]) THEN
    EXISTS_TAC `u':A` THEN ASM_REWRITE_TAC[];
    USE_THEN "hok" (MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[heap_ok_def]) THEN
    MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `u':A`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "seg" (fun th -> REWRITE_TAC[GSYM (CONJUNCT1 (MATCH_MP heap_segment_IMP th))]) THEN
    ASM_REWRITE_TAC[MEM_APPEND]]);;

let heap_length_to_gen_heap_element =
  REWRITE_RULE[to_gen_heap_list_def] heap_length_to_gen_heap_list;;

let _ = cake_add_simps [heap_length_to_gen_heap_element];;

let MEM_to_gen_heap_IMP_MEM = prove
 (`!(heap_current:((A,B)heap_element)list) xs l d ptr u (conf:C gen_gc_partial_conf).
     MEM (DataElement xs l d) (MAP (to_gen_heap_element conf) heap_current) /\
     MEM (Pointer ptr u) xs
     ==> ?xs' u' ptr'.
           MEM (DataElement xs' l d) heap_current /\ MEM (Pointer ptr' u') xs' /\
           xs = MAP (to_gen_heap_address conf) xs' /\
           ptr = ptr' - gen_gc_partial_conf_gen_start conf /\ u = Real u' /\
           ptr' < gen_gc_partial_conf_refs_start conf /\
           gen_gc_partial_conf_gen_start conf <= ptr'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[to_gen_heap_element_def; heap_element_distinct; heap_element_11] THEN
  REPEAT GEN_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC (CONJUNCT2 th) THEN
    DISJ_CASES_THEN2 (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) ASSUME_TAC
      (CONJUNCT1 th)) THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP GC2AUX_MEM_MAP_to_gen_address) THEN MESON_TAC[];
    ASM_MESON_TAC[]]);;

let GC2AUX_isForwardPointer_to_gen = prove
 (`!(conf:C gen_gc_partial_conf) (x:(A,B)heap_element).
     isForwardPointer (to_gen_heap_element conf x) = isForwardPointer x`,
  GEN_TAC THEN MATCH_MP_TAC heap_element_INDUCT THEN
  REWRITE_TAC[to_gen_heap_element_def; isForwardPointer_def]);;

let heap_ok_simulation = prove
 (`!(heap:((A,B)heap_element)list) heap_old heap_current heap_refs
    (conf:B gen_gc_partial_conf).
     heap_ok heap (gen_gc_partial_conf_limit conf) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (heap_old,heap_current,heap_refs) /\
     gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf /\
     gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit conf
     ==> heap_ok (MAP (to_gen_heap_element conf) heap_current)
           (gen_gc_conf_limit (to_gen_conf conf))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "hok" (el 0 cs) THEN LABEL_TAC "seg" (el 1 cs) THEN
    LABEL_TAC "gr" (el 2 cs) THEN LABEL_TAC "rl" (el 3 cs)) THEN
  USE_THEN "seg" (fun th -> let cs = CONJUNCTS (MATCH_MP heap_segment_IMP th) in
    LABEL_TAC "happ" (el 0 cs) THEN LABEL_TAC "hlo" (el 1 cs) THEN
    LABEL_TAC "hloc" (el 2 cs)) THEN
  USE_THEN "hok" (fun th -> let cs = CONJUNCTS (REWRITE_RULE[heap_ok_def] th) in
    LABEL_TAC "hl0" (el 0 cs) THEN LABEL_TAC "nfp" (el 1 cs) THEN
    LABEL_TAC "hok3" (el 2 cs)) THEN
  REWRITE_TAC[heap_ok_def; heap_length_to_gen_heap_element] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[to_gen_conf_def; gen_gc_conf_FIELDS.ri_accessors] THEN
    UNDISCH_TAC `heap_length (APPEND (heap_old:((A,B)heap_element)list) heap_current) =
                 gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)` THEN
    REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
    USE_THEN "happ" (fun h -> USE_THEN "nfp" (MP_TAC o REWRITE_RULE[GSYM h])) THEN
    REWRITE_TAC[FILTER_EQ_NIL; ALL_APPEND; ALL_MAP; o_DEF; GC2AUX_isForwardPointer_to_gen] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MEM_to_gen_heap_IMP_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[isSomeDataElement_to_gen_heap_element] THEN
    USE_THEN "seg" (fun s -> FIRST_ASSUM(fun a -> FIRST_ASSUM(fun b ->
      REWRITE_TAC[GSYM (MATCH_MP GC2AUX_lookup_current (CONJ s (CONJ a b)))]))) THEN
    USE_THEN "hok3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`xs':(A heap_address)list`; `l:num`; `d:B`; `u':A`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[MEM_APPEND]]);;

let new_f_FDOM = prove
 (`!(f:(num,num)fmap) (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) x.
     (!i. i IN FDOM f
          ==> isSomeDataElement (heap_lookup (i + gen_gc_partial_conf_gen_start conf) heap))
     ==> (x IN FDOM (new_f f conf heap) <=>
          if x < gen_gc_partial_conf_gen_start conf \/
             gen_gc_partial_conf_refs_start conf <= x
          then isSomeDataElement (heap_lookup x heap)
          else x IN IMAGE ((+) (gen_gc_partial_conf_gen_start conf)) (FDOM f))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[new_f_def; FUNION_DEF] THEN
  SIMP_TAC[FUN_FMAP_DEF; f_old_ptrs_finite; FINITE_IMAGE; FDOM_FINITE] THEN
  REWRITE_TAC[IN_UNION; f_old_ptrs_def; IN_ELIM_THM; IN_IMAGE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[ADD_SYM]);;

let new_f_FAPPLY = prove
 (`!x (f:(num,num)fmap) (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list).
     x IN FDOM (new_f f conf heap) /\
     (!i. i IN FDOM f
          ==> isSomeDataElement (heap_lookup (i + gen_gc_partial_conf_gen_start conf) heap))
     ==> FAPPLY (new_f f conf heap) x =
         if x < gen_gc_partial_conf_gen_start conf \/
            gen_gc_partial_conf_refs_start conf <= x
         then x
         else gen_gc_partial_conf_gen_start conf +
              FAPPLY f (x - gen_gc_partial_conf_gen_start conf)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC (CONJUNCT1 th) THEN ASSUME_TAC (CONJUNCT2 th)) THEN
  ASM_SIMP_TAC[new_f_FDOM] THEN
  REWRITE_TAC[new_f_def; FUNION_DEF] THEN
  SIMP_TAC[FUN_FMAP_DEF; f_old_ptrs_finite; FINITE_IMAGE; FDOM_FINITE] THEN
  REWRITE_TAC[f_old_ptrs_def; IN_ELIM_THM; I_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[FUN_FMAP_DEF; FINITE_IMAGE; FDOM_FINITE]);;

let isSomeDataElement_heap_lookup_heap_expand = prove
 (`!x n. ~isSomeDataElement (heap_lookup x (heap_expand n:((A,B)heap_element)list))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[heap_lookup_def; isSomeDataElement_def; option_DISTINCT] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[heap_lookup_def; isSomeDataElement_def; option_DISTINCT; option_INJ;
              heap_element_distinct]);;

let _ = cake_add_simps [isSomeDataElement_heap_lookup_heap_expand];;

(* HOL4 val heap_lookup_heap_expand (an ML binding, not a stored theorem) is *)
(* GC2AUX_heap_lookup_heap_expand of gen_gc.ml                              *)

let heap_lookup_old_IMP = prove
 (`!i ys (conf:B gen_gc_partial_conf) roots (heap:((A,B)heap_element)list) roots1 state1
    xs l d.
     partial_gc conf (roots,heap) = (roots1,state1) /\
     gen_inv conf heap /\
     heap_lookup i heap = SOME (DataElement xs l d) /\
     i < gen_gc_partial_conf_gen_start conf
     ==> heap_lookup i (APPEND (gc_state_old state1) ys) = SOME (DataElement xs l d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_inv_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pg") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (X_CHOOSE_THEN `ho:((A,B)heap_element)list` (X_CHOOSE_THEN `hc:((A,B)heap_element)list`
        (X_CHOOSE_THEN `hr:((A,B)heap_element)list`
          (CONJUNCTS_THEN2 (LABEL_TAC "seg") (K ALL_TAC)))))))
    (CONJUNCTS_THEN2 (LABEL_TAC "lk") (LABEL_TAC "lt")))) THEN
  USE_THEN "pg" (fun pg -> USE_THEN "seg" (fun sg ->
    REWRITE_TAC[CONJUNCT1 (MATCH_MP partial_gc_IMP (CONJ pg sg))])) THEN
  USE_THEN "seg" (fun th -> let cs = CONJUNCTS (MATCH_MP heap_segment_IMP th) in
    LABEL_TAC "happ" (el 0 cs) THEN LABEL_TAC "hlo" (el 1 cs)) THEN
  SUBGOAL_THEN `i < heap_length (ho:((A,B)heap_element)list)` ASSUME_TAC THENL
   [USE_THEN "hlo" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "lt" ACCEPT_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup] THEN
  USE_THEN "lk" MP_TAC THEN
  USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th; GSYM APPEND_ASSOC]) THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup]);;

let heap_lookup_old_IMP_ALT = prove
 (`!ys (conf:B gen_gc_partial_conf) roots (heap:((A,B)heap_element)list) roots1 state1 x.
     partial_gc conf (roots,heap) = (roots1,state1) /\
     gen_inv conf heap /\
     isSomeDataElement (heap_lookup x heap) /\
     x < gen_gc_partial_conf_gen_start conf
     ==> isSomeDataElement (heap_lookup x (APPEND (gc_state_old state1) ys))`,
  REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[heap_lookup_old_IMP]);;

(* gc_move_ref_list keeps the shape of the DataElements of the refs        *)
let GC2AUX_ref_list_lookup = prove
 (`!(refs:((A,C)heap_element)list) (conf:B gen_gc_partial_conf) (state:(A,B)gc_state)
    refs' state' p xs l d.
     gc_move_ref_list conf state refs = (refs',state') /\
     heap_lookup p refs = SOME (DataElement xs l d)
     ==> ?xs1. heap_lookup p refs' = SOME (DataElement xs1 l d)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; option_DISTINCT] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) MP_TAC) THEN
    REWRITE_TAC[heap_lookup_def] THEN MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) MP_TAC) THEN
    REWRITE_TAC[heap_lookup_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  GC2AUX_SPLIT_TAC "p1" "s1" THEN GC2AUX_SPLIT_TAC "p2" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) MP_TAC) THEN
  REWRITE_TAC[heap_lookup_def; el_length_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; heap_element_11; option_DISTINCT] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_TAC THEN ASM_MESON_TAC[]);;

let heap_lookup_refs_IMP = prove
 (`!x (conf:B gen_gc_partial_conf) roots (heap:((A,B)heap_element)list) roots1 state1 xs l d.
     partial_gc conf (roots,heap) = (roots1,state1) /\
     gen_inv conf heap /\
     heap_lookup x heap = SOME (DataElement xs l d) /\
     heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1 state1))
                    (heap_expand (gc_state_n state1))) = gen_gc_partial_conf_refs_start conf /\
     gen_gc_partial_conf_refs_start conf <= x
     ==> ?xs1. heap_lookup x (APPEND (APPEND (APPEND (gc_state_old state1)
                                 (gc_state_h1 state1)) (heap_expand (gc_state_n state1)))
                                 (gc_state_r1 state1)) =
               SOME (DataElement xs1 l d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_inv_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (X_CHOOSE_THEN `ho:((A,B)heap_element)list` (X_CHOOSE_THEN `hc:((A,B)heap_element)list`
        (X_CHOOSE_THEN `hr:((A,B)heap_element)list`
          (CONJUNCTS_THEN2 (LABEL_TAC "seg") (K ALL_TAC)))))))
    (CONJUNCTS_THEN2 (LABEL_TAC "lk") (CONJUNCTS_THEN2 (LABEL_TAC "hl") (LABEL_TAC "le"))))) THEN
  SUBGOAL_THEN `~(x < gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf))` ASSUME_TAC
  THENL [USE_THEN "le" MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[partial_gc_def] THEN USE_THEN "seg" (fun th -> REWRITE_TAC[th]) THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; empty_state_def; gc_state_FIELDS.ri_fupds; K_THM] THEN
  GC2AUX_SPLIT_TAC "rA" "s1" THEN GC2AUX_SPLIT_TAC "refsA" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[gc_move_data_r1; gc_state_FIELDS.ri_accfupds; K_THM] THEN
  ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
  USE_THEN "hl" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GC2AUX_ref_list_lookup THEN
  MAP_EVERY EXISTS_TAC [`hr:((A,B)heap_element)list`; `conf:B gen_gc_partial_conf`;
    `s1:(A,B)gc_state`; `s2:(A,B)gc_state`; `xs:(A heap_address)list`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "lk" MP_TAC THEN
  USE_THEN "seg" (fun th -> let cs = CONJUNCTS (MATCH_MP heap_segment_IMP th) in
    REWRITE_TAC[GSYM (el 0 cs)] THEN ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
    REWRITE_TAC[el 2 cs]) THEN
  ASM_REWRITE_TAC[]);;
let heap_lookup_refs_IMP_ALT = prove
 (`!(conf:B gen_gc_partial_conf) roots (heap:((A,B)heap_element)list) roots1 state1 x.
     partial_gc conf (roots,heap) = (roots1,state1) /\
     gen_inv conf heap /\
     isSomeDataElement (heap_lookup x heap) /\
     heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1 state1))
                    (heap_expand (gc_state_n state1))) = gen_gc_partial_conf_refs_start conf /\
     gen_gc_partial_conf_refs_start conf <= x
     ==> isSomeDataElement
           (heap_lookup x (APPEND (APPEND (APPEND (gc_state_old state1)
              (gc_state_h1 state1)) (heap_expand (gc_state_n state1))) (gc_state_r1 state1)))`,
  REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[heap_lookup_refs_IMP]);;

let ADDR_MAP_ID = prove
 (`!(xs:(A heap_address)list) f.
     (!x u. MEM (Pointer x u) xs ==> x = f x) ==> xs = ADDR_MAP f xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ADDR_MAP_def; MEM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `h:A heap_address` (cases "heap_address")) THEN
  REWRITE_TAC[ADDR_MAP_def; CONS_11; heap_address_11; heap_address_distinct] THEN
  ASM_MESON_TAC[]);;

let MEM_heap_old = prove
 (`!n m i (x:(A,B)heap_element) heap heap_old heap_current heap_refs.
     heap_segment (n,m) heap = SOME (heap_old,heap_current,heap_refs) /\
     n <= m /\ i < n /\ heap_lookup i heap = SOME x
     ==> MEM x heap_old`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_segment_IMP) THEN STRIP_TAC THEN
  MATCH_MP_TAC heap_lookup_IMP_MEM THEN EXISTS_TAC `i:num` THEN
  UNDISCH_TAC `heap_lookup i heap = SOME (x:(A,B)heap_element)` THEN
  EXPAND_TAC "heap" THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  SUBGOAL_THEN `i < heap_length (heap_old:((A,B)heap_element)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup]);;

let FILTER_isForward_to_gen = prove
 (`!(xs:((A,B)heap_element)list) (conf:C gen_gc_partial_conf).
     FILTER isForwardPointer (to_gen_heap_list conf xs) = []
     ==> FILTER isForwardPointer xs = []`,
  REWRITE_TAC[to_gen_heap_list_def; FILTER_EQ_NIL; ALL_MAP; o_DEF;
              GC2AUX_isForwardPointer_to_gen]);;

let isSomeData_to_gen_heap_IMP = prove
 (`!(xs:((A,B)heap_element)list) ptr (conf:C gen_gc_partial_conf) ys l d.
     heap_lookup ptr (to_gen_heap_list conf xs) = SOME (DataElement ys l d)
     ==> isSomeDataElement (heap_lookup ptr xs)`,
  MESON_TAC[isSomeDataElement_to_gen_heap_list; isSomeDataElement_def]);;

let refs_to_roots_APPEND = prove
 (`!(xs:((A,B)heap_element)list) ys (conf:C gen_gc_partial_conf).
     refs_to_roots conf (APPEND xs ys) =
     APPEND (refs_to_roots conf xs) (refs_to_roots conf ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; refs_to_roots_def] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  ASM_REWRITE_TAC[APPEND; refs_to_roots_def; APPEND_ASSOC]);;

let gc_move_refs_isForwardPointer = prove
 (`!(refs:((A,C)heap_element)list) refs1 state1 (state:(A,B)gc_state)
    (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state refs = (refs1,state1) /\
     FILTER isForwardPointer refs = []
     ==> FILTER isForwardPointer refs1 = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[FILTER]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[FILTER; isForwardPointer_def];
    REWRITE_TAC[FILTER; isForwardPointer_def; NOT_CONS_NIL];
    ALL_TAC] THEN
  GC2AUX_SPLIT_TAC "p1" "s1" THEN GC2AUX_SPLIT_TAC "p2" "s2" THEN
  REWRITE_TAC[PAIR_EQ; FILTER; isForwardPointer_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[FILTER; isForwardPointer_def] THEN
  ASM_MESON_TAC[]);;

let el_length_to_gen_heap_element = prove
 (`!(conf:C gen_gc_partial_conf) (h:(A,B)heap_element).
     el_length (to_gen_heap_element conf h) = el_length h`,
  REWRITE_TAC[GC2AUX_el_length_to_gen]);;

let _ = cake_add_simps [el_length_to_gen_heap_element];;

let to_gen_heap_element_isSomeData = prove
 (`!(xs:((A,B)heap_element)list) n (conf:B gen_gc_partial_conf).
     isSomeDataElement (heap_lookup n (MAP (to_gen_heap_element conf) xs))
     ==> isSomeDataElement (heap_lookup n xs)`,
  REWRITE_TAC[isSomeDataElement_to_gen_heap_element]);;

let heap_lookup_GT_FALSE = prove
 (`!(xs:((A,B)heap_element)list) n.
     ~(n < heap_length xs) ==> ~isSomeDataElement (heap_lookup n xs)`,
  MESON_TAC[isSomeDataElement_def; heap_lookup_LESS]);;

let heap_lookup_to_gen_heap_element = prove
 (`!(heap_current:((A,B)heap_element)list) i (conf:C gen_gc_partial_conf).
     isSomeDataElement (heap_lookup i (MAP (to_gen_heap_element conf) heap_current)) =
     isSomeDataElement (heap_lookup i heap_current)`,
  REWRITE_TAC[isSomeDataElement_to_gen_heap_element]);;

let partial_gc_heap_length_lemma = prove
 (`!roots' (conf:B gen_gc_partial_conf) roots (heap:((A,B)heap_element)list) roots1 state1
    gen_roots gen_heap heap_old heap_current heap_refs.
     partial_gc conf (roots,heap) = (roots1,state1) /\
     gen_gc (to_gen_conf conf) (gen_roots,gen_heap) = (roots',to_gen_state conf state1) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (heap_old,heap_current,heap_refs) /\
     gen_gc_partial_conf_gen_start conf <= gen_gc_partial_conf_refs_start conf /\
     gen_gc_partial_conf_refs_start conf <= gen_gc_partial_conf_limit conf /\
     roots_ok gen_roots gen_heap /\
     heap_ok gen_heap (gen_gc_conf_limit (to_gen_conf conf))
     ==> heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1 state1))
                        (heap_expand (gc_state_n state1))) =
         gen_gc_partial_conf_refs_start conf`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "pg" (el 0 cs) THEN LABEL_TAC "gg" (el 1 cs) THEN LABEL_TAC "seg" (el 2 cs) THEN
    LABEL_TAC "gr" (el 3 cs) THEN LABEL_TAC "rl" (el 4 cs) THEN
    MP_TAC (CONJ (el 5 cs) (el 6 cs))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP gen_gc_gen_gc_thm) THEN
  DISCH_THEN(X_CHOOSE_THEN `st:((A heap_address,A)data_sort,B)gc_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "ge") (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "inv") (CONJUNCTS_THEN2 (LABEL_TAC "h2") (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `st:((A heap_address,A)data_sort,B)gc_state =
                to_gen_state (conf:B gen_gc_partial_conf) (state1:(A,B)gc_state)`
    SUBST_ALL_TAC THENL
   [USE_THEN "ge" (MP_TAC o SYM) THEN USE_THEN "gg" (fun th -> REWRITE_TAC[th; PAIR_EQ]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "h2" (fun h2 -> USE_THEN "inv" (fun th ->
    MP_TAC (REWRITE_RULE[GC2AUX_to_gen_state_accessors;
                         REWRITE_RULE[GC2AUX_to_gen_state_accessors] h2;
                         APPEND_NIL; heap_length_NIL; ADD_CLAUSES; heap_length_to_gen_heap_list;
                         to_gen_conf_def; gen_gc_conf_FIELDS.ri_accessors]
      (CONJ (GC2AUX_INV_CONJ 0 th) (GC2AUX_INV_CONJ 1 th))))) THEN
  STRIP_TAC THEN
  USE_THEN "pg" (fun pg -> USE_THEN "seg" (fun sg ->
    REWRITE_TAC[CONJUNCT1 (MATCH_MP partial_gc_IMP (CONJ pg sg))])) THEN
  USE_THEN "seg" (fun th -> MP_TAC (CONJUNCT1 (CONJUNCT2 (MATCH_MP heap_segment_IMP th)))) THEN
  REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
  UNDISCH_TAC `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) <=
               gen_gc_partial_conf_refs_start conf` THEN
  UNDISCH_TAC `gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf) <=
               gen_gc_partial_conf_limit conf` THEN
  ASM_ARITH_TAC);;

let gc_move_ref_list_isSomeDataElement = prove
 (`!(refs:((A,C)heap_element)list) ptr (state:(A,B)gc_state) state1 refs1
    (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state refs = (refs1,state1) /\
     isSomeDataElement (heap_lookup ptr refs)
     ==> isSomeDataElement (heap_lookup ptr refs1)`,
  REWRITE_TAC[isSomeDataElement_def] THEN MESON_TAC[GC2AUX_ref_list_lookup]);;

let ptr_Real_lemma = prove
 (`!(ys:(A heap_address)list) ptr u (conf:C gen_gc_partial_conf).
     MEM (Pointer ptr u) ys /\
     gen_gc_partial_conf_gen_start conf <= ptr /\
     ptr < gen_gc_partial_conf_refs_start conf
     ==> MEM (Pointer (ptr - gen_gc_partial_conf_gen_start conf) (Real u))
           (MAP (to_gen_heap_address conf) ys)`,
  REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `Pointer ptr (u:A)` THEN ASM_REWRITE_TAC[to_gen_heap_address_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= p ==> ~(p < a)`; ARITH_RULE `p < b ==> ~(b <= p)`]);;

let partial_gc_refs_isSomeDataElement_isSomeDataElement = prove
 (`!ptr (heap:((A,B)heap_element)list) state1 heap_current heap_refs
    (conf:B gen_gc_partial_conf) roots roots1.
     partial_gc conf (roots,heap) = (roots1,state1) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (gc_state_old state1,heap_current,heap_refs) /\
     isSomeDataElement (heap_lookup ptr heap_refs)
     ==> isSomeDataElement (heap_lookup ptr (gc_state_r1 state1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun pg -> FIRST_ASSUM(fun sg ->
    MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (MATCH_MP partial_gc_IMP (CONJ pg sg))))))) THEN
  ASM_REWRITE_TAC[]);;

let isSomeData_to_gen_heap_IMP_isSomeData = prove
 (`!(heap:((A,B)heap_element)list) ptr (conf:C gen_gc_partial_conf) (state1:(D,E)gc_state).
     isSomeDataElement (heap_lookup ptr
       (APPEND (to_gen_heap_list conf heap) (heap_expand (gc_state_n state1))))
     ==> isSomeDataElement (heap_lookup ptr (APPEND heap (heap_expand (gc_state_n state1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_gc_heap_lookup_APPEND; heap_length_to_gen_heap_list] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[isSomeDataElement_to_gen_heap_list; isSomeDataElement_heap_lookup_heap_expand]);;

let GC2AUX_MEM_refs_to_roots = prove
 (`!(refs:((A,B)heap_element)list) xs l d p (conf:C gen_gc_partial_conf).
     MEM (DataElement xs l d) refs /\ MEM p (MAP (to_gen_heap_address conf) xs)
     ==> MEM p (refs_to_roots conf refs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[refs_to_roots_def; MEM_APPEND; heap_element_distinct; heap_element_11] THEN
  ASM_MESON_TAC[]);;

let refs_root_IMP_isSomeData = prove
 (`!(state1:(A,B)gc_state) (conf:B gen_gc_partial_conf) (refs:((A,C)heap_element)list)
    xs l d ptr (u:A).
     MEM (DataElement xs l d) refs /\
     MEM (Pointer ptr u) xs /\
     roots_ok (refs_to_roots conf refs)
       (APPEND (to_gen_heap_list conf (gc_state_h1 state1)) (heap_expand (gc_state_n state1))) /\
     ptr < gen_gc_partial_conf_refs_start conf /\
     ~(ptr < gen_gc_partial_conf_gen_start conf)
     ==> isSomeDataElement (heap_lookup (ptr - gen_gc_partial_conf_gen_start conf)
           (APPEND (gc_state_h1 state1) (heap_expand (gc_state_n state1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[roots_ok_def] THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`gc_state_h1 (state1:(A,B)gc_state)`;
    `ptr - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)`;
    `conf:B gen_gc_partial_conf`; `state1:(A,B)gc_state`]
    isSomeData_to_gen_heap_IMP_isSomeData) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `Real (u:A):(A heap_address,A)data_sort` THEN
  MATCH_MP_TAC GC2AUX_MEM_refs_to_roots THEN
  MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:C`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ptr_Real_lemma THEN
  ASM_REWRITE_TAC[GSYM NOT_LT]);;

let ADDR_MAP_APPEND_LENGTH_IMP = prove
 (`!(roots:(A heap_address)list) (heap_refs:((A,B)heap_element)list) (f:(num,num)fmap)
    roots1 (r1:((A,B)heap_element)list) (conf:B gen_gc_partial_conf).
     ADDR_MAP (FAPPLY f) (APPEND (to_gen_roots conf roots) (refs_to_roots conf heap_refs)) =
       APPEND (to_gen_roots conf roots1) (refs_to_roots conf r1) /\
     LENGTH roots = LENGTH roots1
     ==> ADDR_MAP (FAPPLY f) (to_gen_roots conf roots) = to_gen_roots conf roots1 /\
         ADDR_MAP (FAPPLY f) (refs_to_roots conf heap_refs) = refs_to_roots conf r1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADDR_MAP_APPEND] THEN STRIP_TAC THEN
  MATCH_MP_TAC APPEND_LENGTH_IMP THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM ADDR_MAP_LENGTH; to_gen_roots_def; LENGTH_MAP]);;

(* the two parts of new_f, pointwise                                         *)
let GC2AUX_new_f_old = prove
 (`!(f:(num,num)fmap) (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) p.
     isSomeDataElement (heap_lookup p heap) /\
     (p < gen_gc_partial_conf_gen_start conf \/ gen_gc_partial_conf_refs_start conf <= p)
     ==> FAPPLY (new_f f conf heap) p = p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[new_f_def; FUNION_DEF] THEN
  SIMP_TAC[FUN_FMAP_DEF; f_old_ptrs_finite; FINITE_IMAGE; FDOM_FINITE] THEN
  ASM_REWRITE_TAC[f_old_ptrs_def; IN_ELIM_THM; I_THM] THEN
  ASM_SIMP_TAC[FUN_FMAP_DEF; f_old_ptrs_finite; f_old_ptrs_def; IN_ELIM_THM; I_THM]);;

let GC2AUX_new_f_cur = prove
 (`!(f:(num,num)fmap) (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list) p.
     gen_gc_partial_conf_gen_start conf <= p /\ p < gen_gc_partial_conf_refs_start conf /\
     (p - gen_gc_partial_conf_gen_start conf) IN FDOM f
     ==> FAPPLY (new_f f conf heap) p =
         gen_gc_partial_conf_gen_start conf + FAPPLY f (p - gen_gc_partial_conf_gen_start conf)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[new_f_def; FUNION_DEF] THEN
  SIMP_TAC[FUN_FMAP_DEF; f_old_ptrs_finite; FINITE_IMAGE; FDOM_FINITE] THEN
  REWRITE_TAC[f_old_ptrs_def; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= p ==> ~(p < a)`; ARITH_RULE `p < b ==> ~(b <= p)`] THEN
  SUBGOAL_THEN `p IN IMAGE ((+) (gen_gc_partial_conf_gen_start (conf:C gen_gc_partial_conf)))
                  (FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `p - gen_gc_partial_conf_gen_start (conf:C gen_gc_partial_conf)` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[FUN_FMAP_DEF; FINITE_IMAGE; FDOM_FINITE]]);;

let GC2AUX_addr_map_new_f = prove
 (`!(xs:(A heap_address)list) ys (f:(num,num)fmap) (conf:C gen_gc_partial_conf)
    (heap:((A,B)heap_element)list).
     MAP (to_gen_heap_address conf) ys = ADDR_MAP (FAPPLY f) (MAP (to_gen_heap_address conf) xs) /\
     (!u ptr. MEM (Pointer ptr u) xs ==> isSomeDataElement (heap_lookup ptr heap)) /\
     (!ptr u. MEM (Pointer ptr u) (MAP (to_gen_heap_address conf) xs) ==> ptr IN FDOM f)
     ==> ys = ADDR_MAP (FAPPLY (new_f f conf heap)) xs`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:(A heap_address)list` list_CASES) THEN
  REWRITE_TAC[MAP; ADDR_MAP_def; NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM; CONS_11] THEN
  STRUCT_CASES_TAC (ISPEC `h:A heap_address` (cases "heap_address")) THEN
  TRY (STRUCT_CASES_TAC (ISPEC `h':A heap_address` (cases "heap_address"))) THEN
  REWRITE_TAC[to_gen_heap_address_def] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[ADDR_MAP_def; CONS_11; heap_address_11; heap_address_distinct;
              injectivity "data_sort"; distinctness "data_sort";
              NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT; NOT_LE]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
         CONV_TAC SYM_CONV THEN MATCH_MP_TAC GC2AUX_new_f_old THEN ASM_MESON_TAC[];
         ASM_MESON_TAC[GC2AUX_new_f_cur;
                       ARITH_RULE `!a b c. c <= a /\ a - c = b ==> a = c + b`]]);;
let heap_lookup_by_f_isSomeData_lemma = prove
 (`!(h1:((A,B)heap_element)list) x xs (state1:(A,B)gc_state) (heap:((A,B)heap_element)list)
    (conf:C gen_gc_partial_conf) (f:(num,num)fmap) l d.
     heap_lookup x (APPEND (MAP (to_gen_heap_element conf) h1)
                      (heap_expand (gc_state_n state1))) =
       SOME (DataElement (ADDR_MAP (FAPPLY f) (MAP (to_gen_heap_address conf) xs)) l d) /\
     (!u ptr. MEM (Pointer ptr u) xs ==> isSomeDataElement (heap_lookup ptr heap)) /\
     (!ptr u. MEM (Pointer ptr u) (MAP (to_gen_heap_address conf) xs) ==> ptr IN FDOM f)
     ==> heap_lookup x (APPEND (APPEND h1 (heap_expand (gc_state_n state1)))
                          (gc_state_r1 state1)) =
         SOME (DataElement (ADDR_MAP (FAPPLY (new_f f conf heap)) xs) l d)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lk") ASSUME_TAC) THEN
  SUBGOAL_THEN `x < heap_length (h1:((A,B)heap_element)list)` (LABEL_TAC "lt") THENL
   [USE_THEN "lk" MP_TAC THEN ONCE_REWRITE_TAC[gen_gc_heap_lookup_APPEND] THEN
    REWRITE_TAC[heap_length_to_gen_heap_element] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[GC2AUX_heap_lookup_heap_expand];
    ALL_TAC] THEN
  SUBGOAL_THEN `heap_lookup x (APPEND (APPEND h1 (heap_expand (gc_state_n (state1:(A,B)gc_state))))
                  (gc_state_r1 state1)) = heap_lookup x h1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC] THEN ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup];
    ALL_TAC] THEN
  USE_THEN "lt" (fun lt -> USE_THEN "lk" (MP_TAC o
    SIMP_RULE[gc_shared_LESS_IMP_heap_lookup; heap_length_to_gen_heap_element; lt])) THEN
  REWRITE_TAC[REWRITE_RULE[to_gen_heap_list_def] GC2AUX_heap_lookup_to_gen] THEN
  SPEC_TAC(`heap_lookup x (h1:((A,B)heap_element)list)`,`o1:((A,B)heap_element)option`) THEN
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
  MATCH_MP_TAC heap_element_INDUCT THEN
  REWRITE_TAC[to_gen_heap_element_def; heap_element_distinct; heap_element_11] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GC2AUX_addr_map_new_f THEN ASM_REWRITE_TAC[]);;

let similar_ptr_def = cake_def
  `(similar_ptr (conf:C) (Pointer p1 (d1:A)) (Pointer p2 d2) <=> d2 = d1) /\
   (similar_ptr conf x1 x2 <=> x1 = x2)`;;

let similar_data_def = cake_def
  `(similar_data (conf:C) (DataElement xs1 l1 (d1:B)) (DataElement xs2 l2 d2:(A,B)heap_element) <=>
      l2 = l1 /\ d2 = d1 /\ ALL2 (similar_ptr conf) xs1 xs2) /\
   (similar_data conf x y <=> x = y)`;;

let gen_gc_partial_LENGTH_ADDR_MAP = prove
 (`!(xs:(A heap_address)list) f. LENGTH (ADDR_MAP f xs) = LENGTH xs`,
  REWRITE_TAC[GSYM ADDR_MAP_LENGTH]);;

let GC2AUX_addr_map_split = prove
 (`!(f:(num,num)fmap) (conf:C gen_gc_partial_conf) (xs:(A heap_address)list) ys r1 r2.
     ALL2 (similar_ptr conf) xs ys /\
     ADDR_MAP (FAPPLY f) (APPEND (MAP (to_gen_heap_address conf) xs) r1) =
       APPEND (MAP (to_gen_heap_address conf) ys) r2
     ==> ADDR_MAP (FAPPLY f) (MAP (to_gen_heap_address conf) xs) =
           MAP (to_gen_heap_address conf) ys /\
         ADDR_MAP (FAPPLY f) r1 = r2`,
  REWRITE_TAC[ADDR_MAP_APPEND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC APPEND_LENGTH_IMP THEN ASM_REWRITE_TAC[GSYM ADDR_MAP_LENGTH; LENGTH_MAP] THEN
  ASM_MESON_TAC[EVERY2_LENGTH]);;

let heap_lookup_similar_data_IMP = prove
 (`!(h1:((A,B)heap_element)list) h2 n (conf:C gen_gc_partial_conf) xs1 l d
    (f:(num,num)fmap).
     ALL2 (similar_data conf) h1 h2 /\
     heap_lookup n h1 = SOME (DataElement xs1 l d) /\
     ADDR_MAP (FAPPLY f) (refs_to_roots conf h1) = refs_to_roots conf h2
     ==> ?xs2. heap_lookup n h2 = SOME (DataElement xs2 l d) /\
               ADDR_MAP (FAPPLY f) (MAP (to_gen_heap_address conf) xs1) =
               MAP (to_gen_heap_address conf) xs2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; option_DISTINCT] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `h2:((A,B)heap_element)list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  STRUCT_CASES_TAC (ISPEC `h':(A,B)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[similar_data_def; heap_element_distinct; heap_element_11; refs_to_roots_def;
              heap_lookup_def; el_length_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  TRY (FIRST_X_ASSUM(fun eq -> FIRST_ASSUM(fun al ->
    STRIP_ASSUME_TAC (MATCH_MP GC2AUX_addr_map_split (CONJ al eq))))) THEN
  (ASM_CASES_TAC `n = 0` THENL
    [ASM_REWRITE_TAC[option_INJ; option_DISTINCT; heap_element_11; heap_element_distinct] THEN
     ASM_MESON_TAC[];
     ASM_REWRITE_TAC[option_INJ; option_DISTINCT; heap_element_11; heap_element_distinct] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
     DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]));;

let new_f_old_parts = prove
 (`!n (f:(num,num)fmap) (conf:C gen_gc_partial_conf) (heap:((A,B)heap_element)list).
     n IN FDOM (new_f f conf heap) /\
     (!i. i IN FDOM f
          ==> isSomeDataElement (heap_lookup (i + gen_gc_partial_conf_gen_start conf) heap)) /\
     (n < gen_gc_partial_conf_gen_start conf \/ gen_gc_partial_conf_refs_start conf <= n)
     ==> FAPPLY (new_f f conf heap) n = n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[new_f_FAPPLY]);;

(* gc_move keeps the shape of an address                                     *)
let GC2AUX_gc_move_similar = prove
 (`!x (conf:B gen_gc_partial_conf) (state:(A,B)gc_state) y state'.
     gen_gc_partial_gc_move conf state x = (y,state') ==> similar_ptr conf x y`,
  GEN_TAC THEN CASES_ON `x:A heap_address` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN TRY PAIRARG_TAC THEN RW[similar_ptr_def]);;

let gc_move_list_similar = prove
 (`!xs (state1:(A,B)gc_state) ys state2 (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list conf state1 xs = (ys,state2)
     ==> ALL2 (similar_ptr conf) xs ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL2]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GC2AUX_SPLIT_TAC "y1" "s1" THEN GC2AUX_SPLIT_TAC "ys1" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL2] THEN
  ASM_MESON_TAC[GC2AUX_gc_move_similar]);;

let GC2AUX_similar_ptr_refl = prove
 (`!(conf:C) (x:A heap_address). similar_ptr conf x x`,
  GEN_TAC THEN MATCH_MP_TAC heap_address_INDUCT THEN REWRITE_TAC[similar_ptr_def]);;

let GC2AUX_similar_refl = prove
 (`(!(conf:C) (x:A heap_address). similar_ptr conf x x) /\
   (!(conf:C) (x:(A,B)heap_element). similar_data conf x x)`,
  REWRITE_TAC[GC2AUX_similar_ptr_refl] THEN GEN_TAC THEN
  MATCH_MP_TAC heap_element_INDUCT THEN REWRITE_TAC[similar_data_def] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[GC2AUX_similar_ptr_refl]);;

let gc_move_ref_list_similar = prove
 (`!(heap_refs:((A,C)heap_element)list) (state:(A,B)gc_state) refs' state'
    (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state heap_refs = (refs',state')
     ==> ALL2 (similar_data conf) heap_refs refs'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL2]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[GC2AUX_similar_refl];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[GC2AUX_similar_refl];
    ALL_TAC] THEN
  GC2AUX_SPLIT_TAC "p1" "s1" THEN GC2AUX_SPLIT_TAC "p2" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL2; similar_data_def] THEN
  ASM_MESON_TAC[gc_move_list_similar]);;

let GC2AUX_ALL_not_ref = prove
 (`!(conf:B gen_gc_partial_conf) (h:((A,B)heap_element)list).
     (!xs l d. MEM (DataElement xs l d) h ==> ~gen_gc_partial_conf_isRef conf d)
     ==> ALL (\e. ~heap_element_is_ref conf e) h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
  MATCH_MP_TAC heap_element_INDUCT THEN REWRITE_TAC[heap_element_is_ref_def] THEN
  ASM_MESON_TAC[]);;

let IMP_gen_inv = prove
 (`!(heap:((A,B)heap_element)list) (conf:B gen_gc_partial_conf).
     heap_ok heap (gen_gc_partial_conf_limit conf) /\ heap_gen_ok heap conf
     ==> gen_inv conf heap`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gen_inv_def; heap_gen_ok_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hok")
    (X_CHOOSE_THEN `o1:((A,B)heap_element)list` (X_CHOOSE_THEN `c1:((A,B)heap_element)list`
      (X_CHOOSE_THEN `r1:((A,B)heap_element)list` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`o1:((A,B)heap_element)list`; `c1:((A,B)heap_element)list`;
                        `r1:((A,B)heap_element)list`] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         FIRST_ASSUM (ACCEPT_TAC o SYM);
         MATCH_MP_TAC GC2AUX_ALL_not_ref THEN FIRST_ASSUM ACCEPT_TAC;
         REPEAT STRIP_TAC THEN
         USE_THEN "hok" (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[heap_ok_def]) THEN
         REWRITE_TAC[FILTER_EQ_NIL; GSYM ALL_MEM] THEN
         DISCH_THEN(MP_TAC o SPEC `ForwardPointer n (a:A) d:(A,B)heap_element`) THEN
         ASM_REWRITE_TAC[isForwardPointer_def] THEN NO_TAC;
         ASM_MESON_TAC[]]);;

(* the r1 field of partial_gc comes from gc_move_ref_list on the refs        *)
let GC2AUX_partial_gc_r1 = prove
 (`!(conf:B gen_gc_partial_conf) roots (heap:((A,B)heap_element)list) roots1 state1
    old cur refs.
     partial_gc conf (roots,heap) = (roots1,state1) /\
     heap_segment (gen_gc_partial_conf_gen_start conf,gen_gc_partial_conf_refs_start conf)
       heap = SOME (old,cur,refs)
     ==> ?s s'. gc_move_ref_list conf s refs = (gc_state_r1 state1,s')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[partial_gc_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  GC2AUX_SPLIT_TAC "rA" "s1" THEN GC2AUX_SPLIT_TAC "refsA" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_var (rhs (concl th)) && rhs (concl th) = `state1:(A,B)gc_state`)) THEN
  REWRITE_TAC[REWRITE_RULE[gc_state_FIELDS.ri_fupdcanon] gc_move_data_with_refs';
              gc_state_FIELDS.ri_accfupds; K_THM] THEN
  ASM_MESON_TAC[]);;

let GC2AUX_NF_SUBST_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    let f,args = strip_comb (lhs c) in
    if fst(dest_const f) = "FAPPLY" &&
       fst(dest_const(fst(strip_comb(hd args)))) = "new_f"
    then SUBST1_TAC th else failwith "GC2AUX_NF_SUBST_TAC");;

let partial_gc_related = prove
 (`!(roots:(A heap_address)list) (heap:((A,B)heap_element)list) (conf:B gen_gc_partial_conf).
     roots_ok roots heap /\ heap_ok heap (gen_gc_partial_conf_limit conf) /\
     heap_gen_ok heap conf
     ==> ?state f.
           partial_gc conf (roots,heap) = (ADDR_MAP (FAPPLY f) roots,state) /\
           (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
           heap_ok (APPEND (APPEND (APPEND (gc_state_old state) (gc_state_h1 state))
                      (heap_expand (gc_state_n state))) (gc_state_r1 state))
             (gen_gc_partial_conf_limit conf) /\
           gc_related f heap
             (APPEND (APPEND (APPEND (gc_state_old state) (gc_state_h1 state))
                (heap_expand (gc_state_n state))) (gc_state_r1 state)) /\
           gc_state_ok state`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "rok" (el 0 cs) THEN LABEL_TAC "hok" (el 1 cs) THEN LABEL_TAC "hgo" (el 2 cs)) THEN
  USE_THEN "hok" (fun h -> USE_THEN "hgo" (fun g ->
    LABEL_TAC "ginv" (MATCH_MP IMP_gen_inv (CONJ h g)))) THEN
  USE_THEN "ginv" (MP_TAC o REWRITE_RULE[gen_inv_def]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gr") (CONJUNCTS_THEN2 (LABEL_TAC "rl")
    (X_CHOOSE_THEN `ho:((A,B)heap_element)list` (X_CHOOSE_THEN `hc:((A,B)heap_element)list`
      (X_CHOOSE_THEN `hr:((A,B)heap_element)list`
        (fun th -> let cs = CONJUNCTS th in
          LABEL_TAC "seg" (el 0 cs) THEN LABEL_TAC "nro" (el 1 cs) THEN
          LABEL_TAC "nrc" (el 2 cs) THEN LABEL_TAC "rdata" (el 3 cs) THEN
          LABEL_TAC "nfp" (el 4 cs) THEN LABEL_TAC "odata" (el 5 cs) THEN
          LABEL_TAC "optr" (el 6 cs))))))) THEN
  MP_TAC (ISPEC `partial_gc (conf:B gen_gc_partial_conf)
    (roots:(A heap_address)list,heap:((A,B)heap_element)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `roots1:(A heap_address)list` (X_CHOOSE_THEN
    `state1:(A,B)gc_state` (LABEL_TAC "pg"))) THEN
  USE_THEN "rok" (fun r -> USE_THEN "hok" (fun h -> USE_THEN "seg" (fun s ->
    USE_THEN "gr" (fun g -> LABEL_TAC "grok"
      (MATCH_MP roots_ok_simulation (CONJ r (CONJ h (CONJ s g)))))))) THEN
  USE_THEN "hok" (fun h -> USE_THEN "seg" (fun s -> USE_THEN "gr" (fun g ->
    USE_THEN "rl" (fun l -> LABEL_TAC "ghok"
      (MATCH_MP heap_ok_simulation (CONJ h (CONJ s (CONJ g l)))))))) THEN
  USE_THEN "grok" (fun r -> USE_THEN "ghok" (fun h ->
    MP_TAC (MATCH_MP gen_gc_related (CONJ r h)) THEN MP_TAC (MATCH_MP gen_gc_ok (CONJ r h)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `stO:((A heap_address,A)data_sort,B)gc_state` (X_CHOOSE_THEN
    `rootsO:(((A heap_address,A)data_sort)heap_address)list` (X_CHOOSE_THEN
    `heapO:(((A heap_address,A)data_sort,B)heap_element)list`
    (fun th -> let cs = CONJUNCTS th in
       LABEL_TAC "heapO" (el 0 cs) THEN LABEL_TAC "ggO" (el 1 cs) THEN
       LABEL_TAC "okO" (el 2 cs) THEN LABEL_TAC "rokO" (el 4 cs) THEN
       LABEL_TAC "hokO" (el 5 cs))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `stR:((A heap_address,A)data_sort,B)gc_state` (X_CHOOSE_THEN
    `f:(num,num)fmap` (fun th -> let cs = CONJUNCTS th in
       LABEL_TAC "ggR" (el 0 cs) THEN LABEL_TAC "fdom" (el 1 cs) THEN
       LABEL_TAC "grel" (el 4 cs)))) THEN
  ALL_TAC THEN
  SUBGOAL_THEN `rootsO = ADDR_MAP (FAPPLY (f:(num,num)fmap))
     (APPEND (to_gen_roots (conf:B gen_gc_partial_conf) (roots:(A heap_address)list))
       (refs_to_roots conf (hr:((A,B)heap_element)list))) /\
     stO:((A heap_address,A)data_sort,B)gc_state = stR`
    (CONJUNCTS_THEN2 (LABEL_TAC "rO") (LABEL_TAC "sO")) THENL
   [USE_THEN "ggO" (MP_TAC o SYM) THEN USE_THEN "ggR" (fun th -> REWRITE_TAC[th; PAIR_EQ]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`conf:B gen_gc_partial_conf`; `roots:(A heap_address)list`;
    `heap:((A,B)heap_element)list`; `roots1:(A heap_address)list`; `state1:(A,B)gc_state`;
    `ho:((A,B)heap_element)list`; `hc:((A,B)heap_element)list`;
    `hr:((A,B)heap_element)list`;
    `rootsO:(((A heap_address,A)data_sort)heap_address)list`;
    `stO:((A heap_address,A)data_sort,B)gc_state`] partial_gc_simulation) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[to_gen_heap_list_def; ALL_APPEND] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "rO2" (el 0 cs) THEN LABEL_TAC "sO2" (el 1 cs) THEN LABEL_TAC "sim" (el 2 cs) THEN
    LABEL_TAC "h2s" (el 3 cs) THEN LABEL_TAC "oks" (el 4 cs)) THEN
  ALL_TAC THEN
  USE_THEN "rO" (fun a -> USE_THEN "rO2" (fun b -> LABEL_TAC "gmap" (TRANS (SYM a) b))) THEN
  USE_THEN "sO" (fun a -> USE_THEN "sO2" (fun b ->
    LABEL_TAC "stR" (TRANS (SYM a) b))) THEN
  USE_THEN "stR" (fun th -> USE_THEN "grel" (LABEL_TAC "grel2" o
    REWRITE_RULE[th; GC2AUX_to_gen_state_accessors; APPEND_NIL])) THEN
  USE_THEN "sO2" (fun s -> USE_THEN "rO2" (fun r -> USE_THEN "heapO" (fun hp ->
    let rw = REWRITE_RULE[s; r; hp; GC2AUX_to_gen_state_accessors; APPEND_NIL] in
    USE_THEN "rokO" (LABEL_TAC "rokO2" o rw) THEN USE_THEN "hokO" (LABEL_TAC "hokO2" o rw)))) THEN
  USE_THEN "pg" (fun pg -> USE_THEN "seg" (fun sg -> let cs = CONJUNCTS
    (MATCH_MP partial_gc_IMP (CONJ pg sg)) in
    LABEL_TAC "old1" (el 0 cs) THEN LABEL_TAC "hlr1" (el 1 cs) THEN
    LABEL_TAC "len1" (el 2 cs) THEN LABEL_TAC "rsome" (el 3 cs))) THEN
  USE_THEN "seg" (fun th -> let cs = CONJUNCTS (MATCH_MP heap_segment_IMP th) in
    LABEL_TAC "happ" (el 0 cs) THEN LABEL_TAC "hlo" (el 1 cs) THEN
    LABEL_TAC "hloc" (el 2 cs) THEN LABEL_TAC "hlr" (el 3 cs)) THEN
  ALL_TAC THEN
  USE_THEN "gmap" (fun g -> USE_THEN "len1" (fun l ->
    MP_TAC (MATCH_MP ADDR_MAP_APPEND_LENGTH_IMP (CONJ g l)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sroots") (LABEL_TAC "srefs")) THEN
  USE_THEN "pg" (fun pg -> USE_THEN "ggO" (fun gg -> USE_THEN "sO2" (fun s2 ->
    USE_THEN "seg" (fun sg -> USE_THEN "gr" (fun gr -> USE_THEN "rl" (fun rl ->
    USE_THEN "grok" (fun rk -> USE_THEN "ghok" (fun hk ->
    LABEL_TAC "hl3" (MATCH_MP partial_gc_heap_length_lemma
      (CONJ pg (CONJ (REWRITE_RULE[s2] gg) (CONJ sg (CONJ gr (CONJ rl (CONJ rk hk))))))))))))))) THEN
  SUBGOAL_THEN `!ptr u. MEM (Pointer ptr u)
      (APPEND (to_gen_roots (conf:B gen_gc_partial_conf) (roots:(A heap_address)list))
         (refs_to_roots conf (hr:((A,B)heap_element)list)))
      ==> ptr IN FDOM (f:(num,num)fmap)` (LABEL_TAC "reach") THENL
   [USE_THEN "fdom" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN; reachable_addresses_def] THEN MESON_TAC[RTC_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN FDOM (f:(num,num)fmap)
      ==> isSomeDataElement (heap_lookup (i + gen_gc_partial_conf_gen_start
            (conf:B gen_gc_partial_conf)) (heap:((A,B)heap_element)list))` (LABEL_TAC "f0") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "grel2" (MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2 o
      REWRITE_RULE[gc_related_def]) THEN
    ASM_REWRITE_TAC[isSomeDataElement_to_gen_heap_element] THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < heap_length (hc:((A,B)heap_element)list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[isSomeDataElement_def; heap_lookup_LESS]; ALL_TAC] THEN
    MP_TAC (ISPECL [`heap:((A,B)heap_element)list`;
      `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)`;
      `gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)`;
      `ho:((A,B)heap_element)list`; `hc:((A,B)heap_element)list`;
      `hr:((A,B)heap_element)list`; `i + gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)`]
      GC2AUX_lookup_current) THEN
    ANTS_TAC THENL
     [USE_THEN "seg" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `heap_length (APPEND (ho:((A,B)heap_element)list) hc) =
                   gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)` THEN
      REWRITE_TAC[heap_length_APPEND] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[ADD_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `!ptr. isSomeDataElement (heap_lookup ptr (heap:((A,B)heap_element)list)) /\
      (ptr < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) \/
       gen_gc_partial_conf_refs_start conf <= ptr)
      ==> isSomeDataElement (heap_lookup ptr
            (APPEND (APPEND (APPEND (gc_state_old (state1:(A,B)gc_state)) (gc_state_h1 state1))
               (heap_expand (gc_state_n state1))) (gc_state_r1 state1)))` (LABEL_TAC "F2") THENL
   [REPEAT STRIP_TAC THENL
     [MP_TAC (ISPECL [`APPEND (gc_state_h1 (state1:(A,B)gc_state))
          (APPEND (heap_expand (gc_state_n state1)) (gc_state_r1 state1))`;
        `conf:B gen_gc_partial_conf`; `roots:(A heap_address)list`;
        `heap:((A,B)heap_element)list`; `roots1:(A heap_address)list`;
        `state1:(A,B)gc_state`; `ptr:num`] heap_lookup_old_IMP_ALT) THEN
      REWRITE_TAC[GSYM APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC (ISPECL [`conf:B gen_gc_partial_conf`; `roots:(A heap_address)list`;
        `heap:((A,B)heap_element)list`; `roots1:(A heap_address)list`;
        `state1:(A,B)gc_state`; `ptr:num`] heap_lookup_refs_IMP_ALT) THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!xs l d ptr (u:A).
      (MEM (DataElement xs l d) (gc_state_h1 (state1:(A,B)gc_state)) \/
       MEM (DataElement xs l d) (gc_state_r1 state1)) /\
      MEM (Pointer ptr u) xs /\
      (ptr < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) \/
       gen_gc_partial_conf_refs_start conf <= ptr)
      ==> isSomeDataElement (heap_lookup ptr
            (APPEND (APPEND (APPEND (gc_state_old state1) (gc_state_h1 state1))
               (heap_expand (gc_state_n state1))) (gc_state_r1 state1)))` (LABEL_TAC "F1") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "F2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sim" (MP_TAC o last o CONJUNCTS o REWRITE_RULE[sim_inv_def]) THEN
    REWRITE_TAC[SUBSET; IN; has_old_ptr_def; MEM_APPEND] THEN
    DISCH_THEN(MP_TAC o SPEC `ptr:num`) THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    STRIP_TAC THEN
    USE_THEN "hok" (MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[heap_ok_def]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) <= p /\
      isSomeDataElement (heap_lookup (p - gen_gc_partial_conf_gen_start conf)
        (APPEND (gc_state_h1 (state1:(A,B)gc_state)) (heap_expand (gc_state_n state1))))
      ==> isSomeDataElement (heap_lookup p
            (APPEND (APPEND (APPEND (gc_state_old state1) (gc_state_h1 state1))
               (heap_expand (gc_state_n state1))) (gc_state_r1 state1)))` (LABEL_TAC "F3") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    SUBGOAL_THEN `~(p < heap_length (gc_state_old (state1:(A,B)gc_state)))` ASSUME_TAC THENL
     [USE_THEN "old1" SUBST1_TAC THEN USE_THEN "hlo" SUBST1_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[NOT_LESS_IMP_heap_lookup] THEN
    USE_THEN "old1" SUBST1_TAC THEN USE_THEN "hlo" SUBST1_TAC THEN
    REWRITE_TAC[APPEND_ASSOC] THEN
    SUBGOAL_THEN `p - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) <
      heap_length (APPEND (gc_state_h1 (state1:(A,B)gc_state)) (heap_expand (gc_state_n state1)))`
      ASSUME_TAC THENL
     [ASM_MESON_TAC[isSomeDataElement_def; heap_lookup_LESS]; ALL_TAC] THEN
    ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`state1:(A,B)gc_state`;
    `new_f (f:(num,num)fmap) (conf:B gen_gc_partial_conf) (heap:((A,B)heap_element)list)`] THEN
  REPEAT CONJ_TAC THENL
   [
   (USE_THEN "pg" SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
   MATCH_MP_TAC GC2AUX_addr_map_new_f THEN REPEAT CONJ_TAC THENL
    [USE_THEN "sroots" (ACCEPT_TAC o SYM o REWRITE_RULE[to_gen_roots_def]);
     USE_THEN "rok" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN MESON_TAC[];
     USE_THEN "reach" MP_TAC THEN REWRITE_TAC[to_gen_roots_def; MEM_APPEND] THEN MESON_TAC[]]);
   (REPEAT STRIP_TAC THEN USE_THEN "f0" (fun f0 -> REWRITE_TAC[MATCH_MP new_f_FDOM f0]) THEN
   COND_CASES_TAC THENL
    [USE_THEN "rok" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT; NOT_LE]) THEN
   REWRITE_TAC[IN_IMAGE] THEN
   EXISTS_TAC `ptr - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)` THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   USE_THEN "reach" MATCH_MP_TAC THEN
   EXISTS_TAC `Real (u:A):(A heap_address,A)data_sort` THEN
   REWRITE_TAC[MEM_APPEND; to_gen_roots_def] THEN DISJ1_TAC THEN
   MATCH_MP_TAC ptr_Real_lemma THEN ASM_REWRITE_TAC[]);
   (REWRITE_TAC[heap_ok_def] THEN REPEAT CONJ_TAC THENL
    [ONCE_REWRITE_TAC[heap_length_APPEND] THEN USE_THEN "hl3" SUBST1_TAC THEN
     USE_THEN "hlr1" SUBST1_TAC THEN USE_THEN "hlr" SUBST1_TAC THEN
     USE_THEN "hok" (fun th -> REWRITE_TAC[CONJUNCT1 (REWRITE_RULE[heap_ok_def] th)]) THEN
     USE_THEN "rl" MP_TAC THEN ARITH_TAC;
     REWRITE_TAC[FILTER_APPEND; APPEND_EQ_NIL] THEN REPEAT CONJ_TAC THENL
      [USE_THEN "old1" SUBST1_TAC THEN
       USE_THEN "hok" (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[heap_ok_def]) THEN
       USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th; FILTER_APPEND; APPEND_EQ_NIL]) THEN
       MESON_TAC[];
       MATCH_MP_TAC (ISPECL [`gc_state_h1 (state1:(A,B)gc_state)`; `conf:B gen_gc_partial_conf`]
         FILTER_isForward_to_gen) THEN
       USE_THEN "hokO2" (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[heap_ok_def]) THEN
       REWRITE_TAC[FILTER_APPEND; APPEND_EQ_NIL] THEN MESON_TAC[];
       REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
       REWRITE_TAC[FILTER; isForwardPointer_def];
       USE_THEN "pg" (fun pg -> USE_THEN "seg" (fun sg ->
         MP_TAC (MATCH_MP GC2AUX_partial_gc_r1 (CONJ pg sg)))) THEN
       STRIP_TAC THEN MATCH_MP_TAC gc_move_refs_isForwardPointer THEN
       MAP_EVERY EXISTS_TAC [`hr:((A,B)heap_element)list`] THEN
       USE_THEN "hok" (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[heap_ok_def]) THEN
       USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th; FILTER_APPEND; APPEND_EQ_NIL]) THEN
       ASM_MESON_TAC[]];
     REPEAT GEN_TAC THEN REWRITE_TAC[MEM_APPEND] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (fun th -> DISJ_CASES_THEN2 (DISJ_CASES_THEN2 (DISJ_CASES_THEN2
       (LABEL_TAC "mo") (LABEL_TAC "mh")) (LABEL_TAC "me")) (LABEL_TAC "mr") th)
       (LABEL_TAC "mp")) THENL
      [USE_THEN "old1" (fun o1 -> USE_THEN "mo" (ASSUME_TAC o REWRITE_RULE[o1])) THEN
       USE_THEN "F2" MATCH_MP_TAC THEN CONJ_TAC THENL
        [USE_THEN "hok" (MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[heap_ok_def]) THEN
         MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
         ASM_REWRITE_TAC[] THEN
         USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th; MEM_APPEND]) THEN ASM_REWRITE_TAC[];
         USE_THEN "optr" MATCH_MP_TAC THEN
         MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
         ASM_REWRITE_TAC[]];
       ASM_CASES_TAC `ptr < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) \/
                      gen_gc_partial_conf_refs_start conf <= ptr` THENL
        [USE_THEN "F1" MATCH_MP_TAC THEN
         MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT; NOT_LE]) THEN
       USE_THEN "F3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC (ISPECL [`gc_state_h1 (state1:(A,B)gc_state)`;
         `ptr - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)`;
         `conf:B gen_gc_partial_conf`; `state1:(A,B)gc_state`]
         isSomeData_to_gen_heap_IMP_isSomeData) THEN
       USE_THEN "hokO2" (MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[heap_ok_def]) THEN
       MAP_EVERY EXISTS_TAC [`MAP (to_gen_heap_address (conf:B gen_gc_partial_conf))
         (xs:(A heap_address)list)`; `l:num`; `d:B`;
         `Real (u:A):(A heap_address,A)data_sort`] THEN
       CONJ_TAC THENL
        [REWRITE_TAC[MEM_APPEND; to_gen_heap_list_def; MEM_MAP] THEN DISJ1_TAC THEN
         EXISTS_TAC `DataElement xs l (d:B):(A,B)heap_element` THEN
         ASM_REWRITE_TAC[to_gen_heap_element_def];
         MATCH_MP_TAC ptr_Real_lemma THEN ASM_REWRITE_TAC[]];
       USE_THEN "me" MP_TAC THEN REWRITE_TAC[heap_expand_def] THEN COND_CASES_TAC THEN
       REWRITE_TAC[MEM; heap_element_distinct];
       ASM_CASES_TAC `ptr < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) \/
                      gen_gc_partial_conf_refs_start conf <= ptr` THENL
        [USE_THEN "F1" MATCH_MP_TAC THEN
         MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT; NOT_LE]) THEN
       USE_THEN "F3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC (ISPECL [`state1:(A,B)gc_state`; `conf:B gen_gc_partial_conf`;
         `gc_state_r1 (state1:(A,B)gc_state)`; `xs:(A heap_address)list`; `l:num`; `d:B`;
         `ptr:num`; `u:A`] refs_root_IMP_isSomeData) THEN
       ASM_REWRITE_TAC[NOT_LT] THEN
       USE_THEN "rokO2" (ACCEPT_TAC o CONJUNCT2 o MATCH_MP roots_ok_APPEND)]]);
   (USE_THEN "f0" (fun f0 -> LABEL_TAC "nfdom" (MATCH_MP new_f_FDOM f0)) THEN
   USE_THEN "grel2" (fun th -> let cs = CONJUNCTS
     (REWRITE_RULE[gc_related_def; INJ; IN_ELIM_THM] th) in
     LABEL_TAC "ga1" (el 0 cs) THEN LABEL_TAC "ga2" (el 1 cs) THEN
     LABEL_TAC "gb" (el 2 cs) THEN LABEL_TAC "gcc" (el 3 cs)) THEN
   USE_THEN "hokO2" (LABEL_TAC "hlR" o REWRITE_RULE[to_gen_conf_def;
     gen_gc_conf_FIELDS.ri_accessors] o CONJUNCT1 o REWRITE_RULE[heap_ok_def]) THEN
   SUBGOAL_THEN `ALL2 (similar_data (conf:B gen_gc_partial_conf)) (hr:((A,B)heap_element)list)
                   (gc_state_r1 (state1:(A,B)gc_state))` (LABEL_TAC "refsim") THENL
    [USE_THEN "pg" (fun pg -> USE_THEN "seg" (fun sg ->
       MP_TAC (MATCH_MP GC2AUX_partial_gc_r1 (CONJ pg sg)))) THEN
     STRIP_TAC THEN FIRST_ASSUM(ACCEPT_TAC o MATCH_MP gc_move_ref_list_similar);
     ALL_TAC] THEN
   SUBGOAL_THEN `!v. v IN FDOM (new_f (f:(num,num)fmap) (conf:B gen_gc_partial_conf)
                     (heap:((A,B)heap_element)list))
       ==> ((v < gen_gc_partial_conf_gen_start conf \/ gen_gc_partial_conf_refs_start conf <= v) /\
            isSomeDataElement (heap_lookup v heap) /\
            FAPPLY (new_f f conf heap) v = v) \/
           (gen_gc_partial_conf_gen_start conf <= v /\ v < gen_gc_partial_conf_refs_start conf /\
            (v - gen_gc_partial_conf_gen_start conf) IN FDOM f /\
            FAPPLY (new_f f conf heap) v =
              gen_gc_partial_conf_gen_start conf + FAPPLY f (v - gen_gc_partial_conf_gen_start conf) /\
            isSomeDataElement (heap_lookup (FAPPLY f (v - gen_gc_partial_conf_gen_start conf))
              (APPEND (gc_state_h1 (state1:(A,B)gc_state)) (heap_expand (gc_state_n state1)))) /\
            FAPPLY f (v - gen_gc_partial_conf_gen_start conf) <
              gen_gc_partial_conf_refs_start conf - gen_gc_partial_conf_gen_start conf)`
     (LABEL_TAC "nfcase") THENL
    [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
     MP_TAC (ISPECL [`v:num`; `f:(num,num)fmap`; `conf:B gen_gc_partial_conf`;
       `heap:((A,B)heap_element)list`] new_f_FAPPLY) THEN
     (ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
     DISCH_THEN SUBST1_TAC THEN
     UNDISCH_TAC `v IN FDOM (new_f (f:(num,num)fmap) (conf:B gen_gc_partial_conf)
                     (heap:((A,B)heap_element)list))` THEN
     USE_THEN "nfdom" (fun nd -> REWRITE_TAC[nd]) THEN
     COND_CASES_TAC THENL
      [DISCH_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT; NOT_LE]) THEN
     REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[ADD_SUB2; LE_ADD] THEN
     SUBGOAL_THEN `isSomeDataElement (heap_lookup (FAPPLY (f:(num,num)fmap) j)
        (APPEND (gc_state_h1 (state1:(A,B)gc_state)) (heap_expand (gc_state_n state1))))`
       ASSUME_TAC THENL
      [MATCH_MP_TAC (ISPECL [`gc_state_h1 (state1:(A,B)gc_state)`; `FAPPLY (f:(num,num)fmap) j`;
         `conf:B gen_gc_partial_conf`; `state1:(A,B)gc_state`]
         isSomeData_to_gen_heap_IMP_isSomeData) THEN
       USE_THEN "ga1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `isSomeDataElement (heap_lookup (FAPPLY (f:(num,num)fmap) j)
        (APPEND (gc_state_h1 (state1:(A,B)gc_state)) (heap_expand (gc_state_n state1))))` THEN
     REWRITE_TAC[isSomeDataElement_def] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_lookup_LESS) THEN
     REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
     USE_THEN "hlR" MP_TAC THEN
     REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
                 heap_length_to_gen_heap_list] THEN
     USE_THEN "gr" MP_TAC THEN USE_THEN "rl" MP_TAC THEN ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[gc_related_def; INJ; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
    [X_GEN_TAC `x:num` THEN
     DISCH_THEN(fun th -> USE_THEN "nfcase" (fun nc -> MP_TAC (MATCH_MP nc th))) THEN
     STRIP_TAC THEN GC2AUX_NF_SUBST_TAC THEN
     FIRST [USE_THEN "F2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
            USE_THEN "F3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_SUB2; LE_ADD]];
     MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
     DISCH_THEN(fun th -> let cs = CONJUNCTS th in
       USE_THEN "nfcase" (fun nc -> MP_TAC (MATCH_MP nc (el 0 cs)) THEN
         MP_TAC (MATCH_MP nc (el 1 cs))) THEN MP_TAC (el 2 cs)) THEN
     REPEAT STRIP_TAC THEN
     FIRST [ASM_ARITH_TAC;
            SUBGOAL_THEN `x - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) =
                          y - gen_gc_partial_conf_gen_start conf` MP_TAC THENL
             [USE_THEN "ga2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
              ASM_ARITH_TAC]];
     X_GEN_TAC `i:num` THEN
     DISCH_THEN(fun th -> USE_THEN "nfcase" (fun nc -> MP_TAC (MATCH_MP nc th))) THEN
     STRIP_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
     USE_THEN "f0" (fun f0 -> FIRST_ASSUM(fun mem -> MP_TAC (MATCH_MP f0 mem))) THEN
     SUBGOAL_THEN `i - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) +
                   gen_gc_partial_conf_gen_start conf = i` SUBST1_TAC THENL
      [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
     (MAP_EVERY X_GEN_TAC [`i:num`; `xs:(A heap_address)list`; `l:num`; `d:B`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inf") (LABEL_TAC "lki")) THEN
    SUBGOAL_THEN `!ptr (u:A). MEM (Pointer ptr u) xs
        ==> isSomeDataElement (heap_lookup ptr (heap:((A,B)heap_element)list))` (LABEL_TAC "allp")
    THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "hok" (MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[heap_ok_def]) THEN
      MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "lki" (ACCEPT_TAC o MATCH_MP heap_lookup_IMP_MEM);
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. (x < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) \/
                       gen_gc_partial_conf_refs_start conf <= x) /\
                      isSomeDataElement (heap_lookup x (heap:((A,B)heap_element)list))
        ==> x IN FDOM (new_f (f:(num,num)fmap) conf heap) /\
            FAPPLY (new_f f conf heap) x = x` (LABEL_TAC "F4") THENL
     [GEN_TAC THEN STRIP_TAC THEN
      (SUBGOAL_THEN `x IN FDOM (new_f (f:(num,num)fmap) (conf:B gen_gc_partial_conf)
                       (heap:((A,B)heap_element)list))` ASSUME_TAC THENL
        [USE_THEN "nfdom" (fun nd -> REWRITE_TAC[nd]) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "nfcase" (fun nc -> FIRST_ASSUM(fun th -> MP_TAC (MATCH_MP nc th))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) <= x /\
                      x < gen_gc_partial_conf_refs_start conf /\
                      (x - gen_gc_partial_conf_gen_start conf) IN FDOM (f:(num,num)fmap)
        ==> x IN FDOM (new_f f conf (heap:((A,B)heap_element)list)) /\
            FAPPLY (new_f f conf heap) x =
            gen_gc_partial_conf_gen_start conf + FAPPLY f (x - gen_gc_partial_conf_gen_start conf)`
      (LABEL_TAC "F5") THENL
     [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "nfdom" (fun nd -> REWRITE_TAC[nd]) THEN
        COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `x - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC GC2AUX_new_f_cur THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ALL_TAC THEN
    USE_THEN "inf" (fun th -> USE_THEN "nfcase" (fun nc -> MP_TAC (MATCH_MP nc th))) THEN
    STRIP_TAC THEN GC2AUX_NF_SUBST_TAC THENL
     [SUBGOAL_THEN `MEM (DataElement xs l (d:B)) (ho:((A,B)heap_element)list)` (LABEL_TAC "mo")
      THENL
       [MATCH_MP_TAC MEM_heap_old THEN
        MAP_EVERY EXISTS_TAC [`gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)`;
          `gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)`; `i:num`;
          `heap:((A,B)heap_element)list`; `hc:((A,B)heap_element)list`;
          `hr:((A,B)heap_element)list`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!ptr (u:A). MEM (Pointer ptr u) xs
          ==> ptr IN FDOM (new_f (f:(num,num)fmap) (conf:B gen_gc_partial_conf)
                             (heap:((A,B)heap_element)list)) /\
              FAPPLY (new_f f conf heap) ptr = ptr` (LABEL_TAC "pts") THENL
       [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "F4" MATCH_MP_TAC THEN CONJ_TAC THENL
         [USE_THEN "optr" MATCH_MP_TAC THEN
          MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`; `u:A`] THEN
          ASM_REWRITE_TAC[];
          USE_THEN "allp" MATCH_MP_TAC THEN EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      SUBGOAL_THEN `ADDR_MAP (FAPPLY (new_f (f:(num,num)fmap) (conf:B gen_gc_partial_conf)
          (heap:((A,B)heap_element)list))) (xs:(A heap_address)list) = xs` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADDR_MAP_ID THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC (ISPECL [`i:num`; `APPEND (gc_state_h1 (state1:(A,B)gc_state))
          (APPEND (heap_expand (gc_state_n state1)) (gc_state_r1 state1))`;
        `conf:B gen_gc_partial_conf`; `roots:(A heap_address)list`;
        `heap:((A,B)heap_element)list`; `roots1:(A heap_address)list`;
        `state1:(A,B)gc_state`; `xs:(A heap_address)list`; `l:num`; `d:B`]
        heap_lookup_old_IMP) THEN
      REWRITE_TAC[GSYM APPEND_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      (SUBGOAL_THEN `heap_lookup (i - gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf))
          (hr:((A,B)heap_element)list) = SOME (DataElement xs l d)` (LABEL_TAC "lkr") THENL
        [USE_THEN "lki" MP_TAC THEN USE_THEN "happ" (fun th -> REWRITE_TAC[GSYM th]) THEN
         MP_TAC (ISPECL [`APPEND (ho:((A,B)heap_element)list) hc`; `i:num`;
           `hr:((A,B)heap_element)list`] NOT_LESS_IMP_heap_lookup) THEN
         USE_THEN "hloc" (fun th -> REWRITE_TAC[th]) THEN
         ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
         ALL_TAC] THEN
     MP_TAC (ISPECL [`hr:((A,B)heap_element)list`; `gc_state_r1 (state1:(A,B)gc_state)`;
         `i - gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)`;
         `conf:B gen_gc_partial_conf`; `xs:(A heap_address)list`; `l:num`; `d:B`;
         `f:(num,num)fmap`] heap_lookup_similar_data_IMP) THEN
       (ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
       DISCH_THEN(X_CHOOSE_THEN `xs2:(A heap_address)list`
         (CONJUNCTS_THEN2 (LABEL_TAC "lk2") (LABEL_TAC "am2"))) THEN
     SUBGOAL_THEN `heap_lookup i (APPEND (APPEND (APPEND (gc_state_old (state1:(A,B)gc_state))
           (gc_state_h1 state1)) (heap_expand (gc_state_n state1))) (gc_state_r1 state1)) =
         heap_lookup (i - gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf))
           (gc_state_r1 state1)` SUBST1_TAC THENL
        [MP_TAC (ISPECL [`APPEND (APPEND (gc_state_old (state1:(A,B)gc_state)) (gc_state_h1 state1))
             (heap_expand (gc_state_n state1))`; `i:num`; `gc_state_r1 (state1:(A,B)gc_state)`]
           NOT_LESS_IMP_heap_lookup) THEN
         USE_THEN "hl3" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN MATCH_MP_TAC THEN
         ASM_ARITH_TAC;
         ALL_TAC] THEN
     USE_THEN "lk2" SUBST1_TAC THEN REWRITE_TAC[option_INJ; heap_element_11] THEN
       SUBGOAL_THEN `!ptr u. MEM (Pointer ptr u) (MAP (to_gen_heap_address (conf:B gen_gc_partial_conf))
           (xs:(A heap_address)list)) ==> ptr IN FDOM (f:(num,num)fmap)` (LABEL_TAC "refptr") THENL
        [REPEAT STRIP_TAC THEN USE_THEN "reach" MATCH_MP_TAC THEN
         EXISTS_TAC `u:(A heap_address,A)data_sort` THEN
         REWRITE_TAC[MEM_APPEND] THEN DISJ2_TAC THEN MATCH_MP_TAC GC2AUX_MEM_refs_to_roots THEN
         MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`] THEN
         ASM_REWRITE_TAC[] THEN USE_THEN "lkr" (ACCEPT_TAC o MATCH_MP heap_lookup_IMP_MEM);
         ALL_TAC] THEN
     CONJ_TAC THENL
        [MATCH_MP_TAC GC2AUX_addr_map_new_f THEN REPEAT CONJ_TAC THENL
          [USE_THEN "am2" (ACCEPT_TAC o SYM);
           USE_THEN "allp" MP_TAC THEN MESON_TAC[];
           USE_THEN "refptr" ACCEPT_TAC];
         ALL_TAC] THEN
     REPEAT STRIP_TAC THEN
       ASM_CASES_TAC `ptr < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) \/
                      gen_gc_partial_conf_refs_start conf <= ptr` THENL
        [USE_THEN "F4" (MP_TAC o SPEC `ptr:num`) THEN
         (ANTS_TAC THENL
           [CONJ_TAC THENL
             [FIRST_ASSUM ACCEPT_TAC;
              USE_THEN "allp" MATCH_MP_TAC THEN EXISTS_TAC `u:A` THEN FIRST_ASSUM ACCEPT_TAC];
            ALL_TAC]) THEN
         DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
         RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT; NOT_LE]) THEN
         USE_THEN "F5" (MP_TAC o SPEC `ptr:num`) THEN
         (ANTS_TAC THENL
           [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
            USE_THEN "refptr" MATCH_MP_TAC THEN
            EXISTS_TAC `Real (u:A):(A heap_address,A)data_sort` THEN
            MATCH_MP_TAC ptr_Real_lemma THEN ASM_REWRITE_TAC[];
            ALL_TAC]) THEN
         DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]);
      (SUBGOAL_THEN `heap_lookup (i - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf))
          (hc:((A,B)heap_element)list) = SOME (DataElement xs l d)` (LABEL_TAC "lkc") THENL
      [USE_THEN "lki" (fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC GC2AUX_lookup_current THEN
       MAP_EVERY EXISTS_TAC [`gen_gc_partial_conf_refs_start (conf:B gen_gc_partial_conf)`;
         `ho:((A,B)heap_element)list`; `hr:((A,B)heap_element)list`] THEN
       REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       ALL_TAC] THEN
     USE_THEN "gcc" (MP_TAC o SPECL [`i - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf)`;
       `MAP (to_gen_heap_address (conf:B gen_gc_partial_conf)) (xs:(A heap_address)list)`;
       `l:num`; `d:B`]) THEN
     ANTS_TAC THENL
      [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       REWRITE_TAC[REWRITE_RULE[to_gen_heap_list_def] GC2AUX_heap_lookup_to_gen] THEN
       USE_THEN "lkc" (fun th -> REWRITE_TAC[th; OPTION_MAP_DEF; to_gen_heap_element_def]);
       ALL_TAC] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "glk") (LABEL_TAC "gptr")) THEN
     MP_TAC (ISPECL [`gc_state_h1 (state1:(A,B)gc_state)`;
       `FAPPLY (f:(num,num)fmap) (i - gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf))`;
       `xs:(A heap_address)list`; `state1:(A,B)gc_state`; `heap:((A,B)heap_element)list`;
       `conf:B gen_gc_partial_conf`; `f:(num,num)fmap`; `l:num`; `d:B`]
       heap_lookup_by_f_isSomeData_lemma) THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
        [USE_THEN "glk" (ACCEPT_TAC o REWRITE_RULE[to_gen_heap_list_def]);
         USE_THEN "allp" MP_TAC THEN MESON_TAC[];
         USE_THEN "gptr" ACCEPT_TAC];
       ALL_TAC] THEN
     DISCH_THEN(LABEL_TAC "blk") THEN
     CONJ_TAC THENL
      [REWRITE_TAC[GSYM APPEND_ASSOC] THEN
       MP_TAC (ISPECL [`gc_state_old (state1:(A,B)gc_state)`;
         `gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) +
          FAPPLY (f:(num,num)fmap) (i - gen_gc_partial_conf_gen_start conf)`;
         `APPEND (gc_state_h1 (state1:(A,B)gc_state))
            (APPEND (heap_expand (gc_state_n state1)) (gc_state_r1 state1))`]
         NOT_LESS_IMP_heap_lookup) THEN
       USE_THEN "old1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "hlo" (fun th -> REWRITE_TAC[th]) THEN
       REWRITE_TAC[ARITH_RULE `~(a + b < a:num)`; ADD_SUB2] THEN DISCH_THEN SUBST1_TAC THEN
       USE_THEN "blk" (ACCEPT_TAC o REWRITE_RULE[GSYM APPEND_ASSOC]);
       REPEAT STRIP_TAC THEN
       ASM_CASES_TAC `ptr < gen_gc_partial_conf_gen_start (conf:B gen_gc_partial_conf) \/
                      gen_gc_partial_conf_refs_start conf <= ptr` THENL
        [USE_THEN "F4" (MP_TAC o SPEC `ptr:num`) THEN
         (ANTS_TAC THENL
           [CONJ_TAC THENL
             [FIRST_ASSUM ACCEPT_TAC;
              USE_THEN "allp" MATCH_MP_TAC THEN EXISTS_TAC `u:A` THEN FIRST_ASSUM ACCEPT_TAC];
            ALL_TAC]) THEN
         DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
         RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT; NOT_LE]) THEN
         USE_THEN "F5" (MP_TAC o SPEC `ptr:num`) THEN
         (ANTS_TAC THENL
           [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
            USE_THEN "gptr" MATCH_MP_TAC THEN
            EXISTS_TAC `Real (u:A):(A heap_address,A)data_sort` THEN
            MATCH_MP_TAC ptr_Real_lemma THEN ASM_REWRITE_TAC[];
            ALL_TAC]) THEN
         DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]])])]);
   USE_THEN "oks" ACCEPT_TAC]);;

let gen_gc_partial_gc_move_list_length = prove
 (`!xs xs' (state:(A,B)gc_state) state' (conf:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list conf state xs = (xs',state') ==> LENGTH xs' = LENGTH xs`,
  MESON_TAC[gen_gc_partial_gc_move_list_IMP]);;

let gc_move_ref_list_length = prove
 (`!(xs:((A,C)heap_element)list) xs' (state:(A,B)gc_state) state'
    (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state xs = (xs',state') ==> LENGTH xs' = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH];
    ALL_TAC] THEN
  GC2AUX_SPLIT_TAC "p1" "s1" THEN GC2AUX_SPLIT_TAC "p2" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

let gc_move_ref_list_heap_length' = prove
 (`!(xs:((A,C)heap_element)list) xs' (state:(A,B)gc_state) state'
    (conf:B gen_gc_partial_conf).
     gc_move_ref_list conf state xs = (xs',state') ==> heap_length xs' = heap_length xs`,
  MESON_TAC[gen_gc_partial_gc_move_ref_list_IMP]);;

let has_bad_ref_def = cake_def
  `has_bad_ref (c:B gen_gc_partial_conf) (s:(A,B)gc_state) <=>
     (?xs l d. MEM (DataElement xs l d) (APPEND (gc_state_h1 s) (gc_state_h2 s)) /\
               gen_gc_partial_conf_isRef c d) \/
     ?xs l d n.
       gen_gc_partial_conf_gen_start c <= n /\ n < gen_gc_partial_conf_refs_start c /\
       heap_lookup n (gc_state_heap s) = SOME (DataElement xs l d) /\
       gen_gc_partial_conf_isRef c d`;;

let balanced_state_def = cake_def
  `balanced_state (c:C gen_gc_partial_conf) (s:(A,B)gc_state) <=>
     heap_length (FILTER isForwardPointer (gc_state_heap s)) =
       heap_length (gc_state_h1 s) + heap_length (gc_state_h2 s) /\
     (match heap_segment (gen_gc_partial_conf_gen_start c,gen_gc_partial_conf_refs_start c)
              (gc_state_heap s) with
        NONE -> F
      | SOME (old,curr,refs) ->
          heap_length (FILTER isDataElement (gc_state_r1 s)) +
          heap_length (FILTER isDataElement (gc_state_r2 s)) +
          heap_length (FILTER isDataElement (gc_state_old s)) <=
          heap_length (FILTER isDataElement old) + heap_length (FILTER isDataElement refs))`;;

let simple_rel_def = cake_def
  `simple_rel (c:B gen_gc_partial_conf) (s1:(A,B)gc_state) (s2:(A,B)gc_state) <=>
     gc_state_old s2 = gc_state_old s1 /\
     heap_length (APPEND (APPEND (gc_state_h1 s2) (gc_state_h2 s2)) (heap_expand (gc_state_n s2))) =
       heap_length (APPEND (APPEND (gc_state_h1 s1) (gc_state_h2 s1))
                      (heap_expand (gc_state_n s1))) /\
     (gc_state_a s1 = gen_gc_partial_conf_gen_start c + heap_length (gc_state_h1 s1) +
                      heap_length (gc_state_h2 s1)
      ==> gc_state_a s2 = gen_gc_partial_conf_gen_start c + heap_length (gc_state_h1 s2) +
                          heap_length (gc_state_h2 s2)) /\
     (ALL isDataElement (gc_state_h1 s1) ==> ALL isDataElement (gc_state_h1 s2)) /\
     heap_length (APPEND (APPEND (FILTER isDataElement (gc_state_heap s1)) (gc_state_h1 s1))
                    (gc_state_h2 s1)) =
       heap_length (APPEND (APPEND (FILTER isDataElement (gc_state_heap s2)) (gc_state_h1 s2))
                      (gc_state_h2 s2)) /\
     heap_length (FILTER isForwardPointer (gc_state_heap s1)) +
       heap_length (FILTER isDataElement (gc_state_heap s1)) =
     heap_length (FILTER isForwardPointer (gc_state_heap s2)) +
       heap_length (FILTER isDataElement (gc_state_heap s2)) /\
     (balanced_state c s1 ==> balanced_state c s2) /\
     (has_bad_ref c s2 ==> has_bad_ref c s1)`;;

let simple_rel_refl = prove
 (`!(c:B gen_gc_partial_conf) (x:(A,B)gc_state). simple_rel c x x`,
  REWRITE_TAC[simple_rel_def]);;

let simple_rel_trans = prove
 (`!(c:B gen_gc_partial_conf) (x1:(A,B)gc_state) x2 x3.
     simple_rel c x1 x2 /\ simple_rel c x2 x3 ==> simple_rel c x1 x3`,
  REWRITE_TAC[simple_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let gc_forward_ptr_lookup_DataElement = prove
 (`!(hs:((A,B)heap_element)list) n x (a:A) heap n1 xs l' d.
     gc_forward_ptr n hs x a T = (heap,T) /\
     heap_lookup n1 heap = SOME (DataElement xs l' d)
     ==> heap_lookup n1 hs = SOME (DataElement xs l' d)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_forward_ptr_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    UNDISCH_TAC `heap_lookup n1 (CONS (ForwardPointer x (a:A)
      (el_length (h:(A,B)heap_element) - 1)) (t:((A,B)heap_element)list)) =
      SOME (DataElement xs l' d)` THEN
    REWRITE_TAC[heap_lookup_def; el_length_def] THEN
    MP_TAC (SPEC `h:(A,B)heap_element` el_length_NOT_0) THEN
    ASM_CASES_TAC `n1 = 0` THEN ASM_REWRITE_TAC[option_INJ; heap_element_distinct] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[ARITH_RULE `~(e = 0) ==> e - 1 + 1 = e`];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  GC2AUX_SPLIT_TAC "t1" "ok1" THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  UNDISCH_TAC `heap_lookup n1 (CONS (h:(A,B)heap_element) t1) = SOME (DataElement xs l' d)` THEN
  REWRITE_TAC[heap_lookup_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let gen_gc_partial_gc_forward_ptr_APPEND = prove
 (`!(x0:((A,B)heap_element)list) n a1 (a:A) x1 heap1.
     gc_forward_ptr n (APPEND x0 x1) a1 a T = (heap1,T)
     ==> if n < heap_length x0 then
           ?y0. gc_forward_ptr n x0 a1 a T = (y0,T) /\ heap1 = APPEND y0 x1
         else
           ?y1. gc_forward_ptr (n - heap_length x0) x1 a1 a T = (y1,T) /\
                heap1 = APPEND x0 y1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; heap_length_NIL; LT; SUB_0] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[gc_forward_ptr_def; GC1AUX_heap_length_CONS] THEN
  MP_TAC (SPEC `h:(A,B)heap_element` el_length_NOT_0) THEN DISCH_TAC THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(e = 0) ==> 0 < e + n`; APPEND] THEN
    REWRITE_TAC[UNWIND_THM1; APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
  GC2AUX_SPLIT_TAC "t1" "ok1" THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `ok1:bool` then RULE_ASSUM_TAC(REWRITE_RULE[th])
                          else failwith "ok1") THEN
  FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(fun ih -> MP_TAC (MATCH_MP ih th))) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n < e) ==> (n - e < t <=> n < e + t)`;
               ARITH_RULE `n - e - t = n - (e + t)`] THEN
  COND_CASES_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; PAIR_EQ; APPEND; CONS_11; UNWIND_THM1]);;

let gc_forward_ptr_APPEND_APPEND = prove
 (`!n (x0:((A,B)heap_element)list) x1 x2 a1 (a:A) heap1.
     gc_forward_ptr n (APPEND (APPEND x0 x1) x2) a1 a T = (heap1,T) /\
     heap_length x0 <= n /\ n < heap_length (APPEND x0 x1)
     ==> ?y. heap1 = APPEND (APPEND x0 y) x2 /\ heap_length y = heap_length x1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n < heap_length (x0:((A,B)heap_element)list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_forward_ptr_APPEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:((A,B)heap_element)list`
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP gen_gc_partial_gc_forward_ptr_APPEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:((A,B)heap_element)list`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  EXISTS_TAC `y1:((A,B)heap_element)list` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP gc_forward_ptr_heap_length) THEN
  MESON_TAC[]);;

let GC2AUX_heap_split_APPEND = prove
 (`!a (b:((A,B)heap_element)list).
     heap_split (heap_length a) (APPEND a b) = SOME (a,b)`,
  REWRITE_TAC[heap_split_APPEND_if; LT_REFL; SUB_REFL; heap_split_0] THEN
  CAKE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND_NIL]);;

let GC2AUX_heap_segment_APPEND = prove
 (`!(x0:((A,B)heap_element)list) y x2.
     heap_segment (heap_length x0,heap_length (APPEND x0 y)) (APPEND (APPEND x0 y) x2) =
     SOME (x0,y,x2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heap_segment_def; GSYM APPEND_ASSOC;
    GC2AUX_heap_split_APPEND] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[heap_length_APPEND; ARITH_RULE `~(a + b < a)`; ADD_SUB2;
              GC2AUX_heap_split_APPEND] THEN
  CAKE_REWRITE_TAC[]);;

let heap_segment_gc_forward_ptr = prove
 (`!k l (heap:((A,B)heap_element)list) x0 x1 x2 n a1 (a:A) heap1.
     heap_segment (k,l) heap = SOME (x0,x1,x2) /\
     gc_forward_ptr n heap a1 a T = (heap1,T) /\ k <= n /\ n < l
     ==> ?y. heap_segment (k,l) heap1 = SOME (x0,y,x2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_segment_IMP) THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`n:num`; `x0:((A,B)heap_element)list`; `x1:((A,B)heap_element)list`;
    `x2:((A,B)heap_element)list`; `a1:num`; `a:A`; `heap1:((A,B)heap_element)list`]
    gc_forward_ptr_APPEND_APPEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:((A,B)heap_element)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `k = heap_length (x0:((A,B)heap_element)list) /\
                l = heap_length (APPEND x0 (y:((A,B)heap_element)list))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `heap_length (APPEND (x0:((A,B)heap_element)list) x1) = l` THEN
    ASM_REWRITE_TAC[heap_length_APPEND] THEN ARITH_TAC;
    REWRITE_TAC[GC2AUX_heap_segment_APPEND]]);;

let GC2AUX_isDataElement_cons = prove
 (`(!(xs:(A heap_address)list) l (d:B). isDataElement (DataElement xs l d)) /\
   (!n. ~isDataElement (Unused n:(A,B)heap_element)) /\
   (!p (a:A) l. ~isDataElement (ForwardPointer p a l:(A,B)heap_element))`,
  REWRITE_TAC[isDataElement_def; heap_element_distinct; heap_element_11] THEN MESON_TAC[]);;

(* gc_forward_ptr on a DataElement found by heap_lookup                      *)
let GC2AUX_gc_forward_ptr_split = prove
 (`!(heap:((A,B)heap_element)list) ptr xs l dd a (d:A) heap'.
     heap_lookup ptr heap = SOME (DataElement xs l dd) /\
     gc_forward_ptr ptr heap a d T = (heap',T)
     ==> ?ha hb. heap = APPEND ha (CONS (DataElement xs l dd) hb) /\
                 heap' = APPEND ha (CONS (ForwardPointer a d l) hb)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o MATCH_MP heap_lookup_SPLIT) ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A,B)heap_element)list` (X_CHOOSE_THEN
    `hb:((A,B)heap_element)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[gc_forward_ptr_thm; PAIR_EQ]) THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ha:((A,B)heap_element)list`; `hb:((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[]);;

let GC2AUX_gc_move_inv_data = prove
 (`!(c:B gen_gc_partial_conf) old h1 h2 r4 r3 r2 r1 a n ok (heap:((A,B)heap_element)list)
    hp0 ptr (d:A) xs l dd heap'.
     heap_lookup ptr heap = SOME (DataElement xs l dd) /\
     ~(ptr < gen_gc_partial_conf_gen_start c) /\ ~(gen_gc_partial_conf_refs_start c <= ptr) /\
     l + 1 <= n /\ ~gen_gc_partial_conf_isRef c dd /\
     gc_forward_ptr ptr heap a d T = (heap',T)
     ==> simple_rel c (gc_state_REC old h1 h2 r4 r3 r2 r1 a n ok heap hp0)
           (gc_state_REC old h1 (APPEND h2 [DataElement xs l dd]) r4 r3 r2 r1 (a + l + 1)
              (n - (l + 1)) T heap' hp0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[simple_rel_def; gc_state_FIELDS.ri_accessors] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
                GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN ASM_ARITH_TAC;
    REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand;
                GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN ARITH_TAC;
    MP_TAC (SPEC_ALL GC2AUX_gc_forward_ptr_split) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FILTER_APPEND; FILTER; GC2AUX_isDataElement_cons; heap_length_APPEND;
                GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN ARITH_TAC;
    MP_TAC (SPEC_ALL GC2AUX_gc_forward_ptr_split) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FILTER_APPEND; FILTER; GC2AUX_isDataElement_cons; isForwardPointer_def;
                heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL;
                el_length_def] THEN ARITH_TAC;
    REWRITE_TAC[balanced_state_def; gc_state_FIELDS.ri_accessors] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MP_TAC (SPEC_ALL GC2AUX_gc_forward_ptr_split) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FILTER_APPEND; FILTER; isForwardPointer_def; heap_length_APPEND;
                  GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC (ISPEC `heap_segment (gen_gc_partial_conf_gen_start (c:B gen_gc_partial_conf),
      gen_gc_partial_conf_refs_start c) (heap:((A,B)heap_element)list)` BASICAUX_option3_cases) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[])
      (X_CHOOSE_THEN `x0:((A,B)heap_element)list` (X_CHOOSE_THEN
        `x1:((A,B)heap_element)list` (X_CHOOSE_THEN `x2:((A,B)heap_element)list`
          (LABEL_TAC "sg"))))) THEN
    MP_TAC (ISPECL [`gen_gc_partial_conf_gen_start (c:B gen_gc_partial_conf)`;
      `gen_gc_partial_conf_refs_start (c:B gen_gc_partial_conf)`;
      `heap:((A,B)heap_element)list`; `x0:((A,B)heap_element)list`;
      `x1:((A,B)heap_element)list`; `x2:((A,B)heap_element)list`; `ptr:num`; `a:num`;
      `d:A`; `heap':((A,B)heap_element)list`] heap_segment_gc_forward_ptr) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:((A,B)heap_element)list` SUBST1_TAC) THEN
    USE_THEN "sg" (fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[];
    REWRITE_TAC[has_bad_ref_def; gc_state_FIELDS.ri_accessors; MEM_APPEND; MEM;
                heap_element_11] THEN
    ASM_MESON_TAC[gc_forward_ptr_lookup_DataElement]]);;

let GC2AUX_MOVE_TRIV_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN
    SUBST1_TAC (SYM (CONJUNCT2 (CONJUNCT1 th)))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; simple_rel_refl] THEN NO_TAC;;

let gc_move_inv = prove
 (`!xs xs' (s1:(A,B)gc_state) s2 (c:B gen_gc_partial_conf).
     gen_gc_partial_gc_move c s1 xs = (xs',s2) /\ gc_state_ok s2 ==> simple_rel c s1 s2`,
  X_GEN_TAC `x:A heap_address` THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `x:A heap_address` (cases "heap_address")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `d:A` SUBST1_TAC))
    (X_CHOOSE_THEN `d:A` SUBST1_TAC)) THEN
  GC2AUX_STATE_TAC GC2AUX_FIELDS `s1:(A,B)gc_state` THEN
  REWRITE_TAC[gen_gc_partial_gc_move_def; LET_DEF; LET_END_DEF;
    gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  TRY (GC2AUX_MOVE_TRIV_TAC) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN
      SUBST1_TAC (SYM (CONJUNCT2 (CONJUNCT1 th)))) THEN
    REWRITE_TAC[simple_rel_def; has_bad_ref_def; balanced_state_def;
                gc_state_FIELDS.ri_accessors];
    ALL_TAC] THEN
  MP_TAC (ISPEC `heap_lookup ptr (heap:((A,B)heap_element)list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
    (X_CHOOSE_THEN `e:(A,B)heap_element` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]))) THEN
  CAKE_REWRITE_TAC[] THEN
  TRY (GC2AUX_MOVE_TRIV_TAC) THEN
  MP_TAC (ISPEC `e:(A,B)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `dd:B` SUBST_ALL_TAC))))) THEN
  CAKE_REWRITE_TAC[] THEN
  TRY (GC2AUX_MOVE_TRIV_TAC) THEN
  GC2AUX_SPLIT_TAC "heap1" "ok1" THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN
    SUBST1_TAC (SYM (CONJUNCT2 (CONJUNCT1 th)))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN
  DISCH_THEN(fun ok1 -> RULE_ASSUM_TAC(REWRITE_RULE[ok1]) THEN REWRITE_TAC[ok1]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP gc_shared_gc_forward_ptr_ok) THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  MATCH_MP_TAC GC2AUX_gc_move_inv_data THEN
  MAP_EVERY EXISTS_TAC [`ptr:num`; `d:A`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

let gc_move_list_inv = prove
 (`!xs xs' (s1:(A,B)gc_state) s2 (c:B gen_gc_partial_conf).
     gen_gc_partial_gc_move_list c s1 xs = (xs',s2) /\ gc_state_ok s2
     ==> simple_rel c s1 s2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gen_gc_partial_gc_move_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[simple_rel_refl]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  GC2AUX_SPLIT_TAC "y1" "t1" THEN GC2AUX_SPLIT_TAC "ys1" "t2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC simple_rel_trans THEN EXISTS_TAC `t1:(A,B)gc_state` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC gc_move_inv THEN
    MAP_EVERY EXISTS_TAC [`h:A heap_address`; `y1:A heap_address`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[gc_move_list_ok'];
    ASM_MESON_TAC[]]);;

let gc_move_ref_list_inv = prove
 (`!(xs:((A,C)heap_element)list) xs' (s1:(A,B)gc_state) s2 (c:B gen_gc_partial_conf).
     gc_move_ref_list c s1 xs = (xs',s2) /\ gc_state_ok s2 ==> simple_rel c s1 s2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_move_ref_list_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[simple_rel_refl]; ALL_TAC] THEN
  MP_TAC (ISPEC `h:(A,C)heap_element` (cases "heap_element")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (CHOOSE_THEN SUBST_ALL_TAC)
    (DISJ_CASES_THEN2 (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (X_CHOOSE_THEN `zs:(A heap_address)list` (X_CHOOSE_THEN `l:num`
        (X_CHOOSE_THEN `dd:C` SUBST_ALL_TAC))))) THEN
  REWRITE_TAC[gc_move_ref_list_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gc_state_FIELDS.ri_accfupds; K_THM]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  GC2AUX_SPLIT_TAC "p1" "t1" THEN GC2AUX_SPLIT_TAC "p2" "t2" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC simple_rel_trans THEN EXISTS_TAC `t1:(A,B)gc_state` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC gc_move_list_inv THEN
    MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `p1:(A heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[gc_move_ref_list_ok'];
    ASM_MESON_TAC[]]);;

let GC2AUX_move_data_step = prove
 (`!(c:B gen_gc_partial_conf) (s:(A,B)gc_state) xs xs' l d t okv.
     gc_state_h2 s = CONS (DataElement xs l d) t
     ==> simple_rel c s
           (gc_state_ok_fupd (combin_K okv) (gc_state_h2_fupd (combin_K t)
             (gc_state_h1_fupd (combin_K (APPEND (gc_state_h1 s) [DataElement xs' l d])) s)))`,
  REPEAT GEN_TAC THEN GC2AUX_STATE_TAC GC2AUX_FIELDS `s:(A,B)gc_state` THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accessors; gc_state_FIELDS.ri_fupds; K_THM] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[simple_rel_def; gc_state_FIELDS.ri_accessors; balanced_state_def;
              has_bad_ref_def] THEN
  REWRITE_TAC[heap_length_APPEND; GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def;
              ALL_APPEND; ALL; GC2AUX_isDataElement_cons; MEM_APPEND; MEM;
              heap_element_11] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ARITH_TAC;
         STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
         MESON_TAC[]]);;

let gc_move_data_inv = prove
 (`!(c:B gen_gc_partial_conf) (s1:(A,B)gc_state) s2.
     gen_gc_partial_gc_move_data c s1 = s2 /\ gc_state_ok s2 ==> simple_rel c s1 s2`,
  MATCH_MP_TAC gen_gc_partial_gc_move_data_ind THEN
  MAP_EVERY X_GEN_TAC [`c:B gen_gc_partial_conf`; `state:(A,B)gc_state`] THEN
  DISCH_THEN(LABEL_TAC "IH") THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[gen_gc_partial_gc_move_data_def] THEN
  GC2AUX_LIST_CASES_TAC `gc_state_h2 (state:(A,B)gc_state)`
    (STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[simple_rel_refl]) THEN
  COND_CASES_TAC THENL
   [DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN SUBST1_TAC (SYM (CONJUNCT1 th))) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM];
    ALL_TAC] THEN
  GC2AUX_ELEMENT_CASES_TAC THEN
  TRY (DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN SUBST1_TAC (SYM (CONJUNCT1 th))) THEN
       REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN NO_TAC) THEN
  GC2AUX_PAIR_TAC `gen_gc_partial_gc_move_list (c:B gen_gc_partial_conf)
    (state:(A,B)gc_state) zs` "xs1" "s1" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "md") (LABEL_TAC "ok2")) THEN
  USE_THEN "IH" (fun ih -> USE_THEN "hd" (fun hd -> FIRST_ASSUM(fun nl -> FIRST_ASSUM(fun mv ->
    LABEL_TAC "r3IH" (GC2AUX_MATCH_MP_EITHER (GC2AUX_MATCH_MP_EITHER
      (GC2AUX_MATCH_MP_EITHER (REWRITE_RULE[IMP_CONJ] ih) hd) nl) mv))))) THEN
  USE_THEN "r3IH" (fun th -> USE_THEN "md" (fun md -> USE_THEN "ok2" (fun ok2 ->
    LABEL_TAC "r3" (MATCH_MP (MATCH_MP th md) ok2)))) THEN
  USE_THEN "md" (fun md -> USE_THEN "ok2" (fun ok2 ->
    MP_TAC (MATCH_MP gc_move_data_ok' (CONJ md ok2)))) THEN
  REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  MP_TAC (ISPEC `gc_state_h2 (s1:(A,B)gc_state)` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':(A,B)heap_element` (X_CHOOSE_THEN
    `t1:((A,B)heap_element)list` ASSUME_TAC)) THEN
  SUBGOAL_THEN `gc_state_h2 (s1:(A,B)gc_state) = CONS (DataElement zs l d) t1`
    (LABEL_TAC "h21") THENL
   [UNDISCH_TAC `HD (gc_state_h2 (s1:(A,B)gc_state)) = DataElement zs l d` THEN
    ASM_REWRITE_TAC[HD] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  USE_THEN "r3" (fun r3 -> let s'' = rand(rator(concl r3)) in
    MATCH_MP_TAC simple_rel_trans THEN EXISTS_TAC s'' THEN
    CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC r3]) THEN
  MATCH_MP_TAC simple_rel_trans THEN EXISTS_TAC `s1:(A,B)gc_state` THEN CONJ_TAC THENL
   [MATCH_MP_TAC gc_move_list_inv THEN
    MAP_EVERY EXISTS_TAC [`zs:(A heap_address)list`; `xs1:(A heap_address)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "h21" (fun th -> REWRITE_TAC[th; TL]) THEN
  MATCH_MP_TAC GC2AUX_move_data_step THEN EXISTS_TAC `zs:(A heap_address)list` THEN
  USE_THEN "h21" ACCEPT_TAC);;

let LIST_REL_similar_data_IMP = prove
 (`!(xs:((A,B)heap_element)list) ys (cc:C).
     ALL2 (similar_data cc) xs ys
     ==> heap_length xs = heap_length ys /\
         heap_length (FILTER isDataElement xs) = heap_length (FILTER isDataElement ys)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ys:((A,B)heap_element)list` list_CASES) THEN
  REWRITE_TAC[ALL2; heap_length_NIL; FILTER] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `h:(A,B)heap_element` (cases "heap_element")) THEN
  STRUCT_CASES_TAC (ISPEC `h':(A,B)heap_element` (cases "heap_element")) THEN
  REWRITE_TAC[similar_data_def; heap_element_distinct; heap_element_11;
              GC2AUX_isDataElement_cons; GC1AUX_heap_length_CONS; el_length_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(fun ih -> FIRST_X_ASSUM(fun th -> MP_TAC (MATCH_MP ih th))) THEN
  SIMP_TAC[GC1AUX_heap_length_CONS; el_length_def]);;

(* the second HOL4 theorem named partial_gc_IMP                            *)
let partial_gc_IMP = prove
 (`!(c:B gen_gc_partial_conf) roots (heap:((A,B)heap_element)list) roots1 state1.
     partial_gc c (roots,heap) = (roots1,state1) /\ gc_state_ok state1
     ==> gc_state_a state1 = gen_gc_partial_conf_gen_start c + heap_length (gc_state_h1 state1) /\
         LENGTH roots1 = LENGTH roots /\
         heap_length (gc_state_old state1) = gen_gc_partial_conf_gen_start c /\
         heap_length (APPEND (APPEND (gc_state_old state1) (gc_state_h1 state1))
                        (heap_expand (gc_state_n state1))) = gen_gc_partial_conf_refs_start c /\
         (FILTER isForwardPointer heap = []
          ==> heap_length (FILTER isDataElement (APPEND (APPEND (gc_state_old state1)
                 (gc_state_h1 state1)) (gc_state_r1 state1))) <=
              heap_length (FILTER isDataElement heap)) /\
         ALL isDataElement (gc_state_h1 state1) /\
         ?curr refs.
           heap_segment (gen_gc_partial_conf_gen_start c,gen_gc_partial_conf_refs_start c) heap =
             SOME (gc_state_old state1,curr,refs) /\
           ALL2 (similar_data c) refs (gc_state_r1 state1) /\
           (!xs l d. MEM (DataElement xs l d) (gc_state_h1 state1) /\
                     gen_gc_partial_conf_isRef c d
                     ==> ?xs l d. MEM (DataElement xs l d) curr /\
                                  gen_gc_partial_conf_isRef c d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[partial_gc_def] THEN
  MP_TAC (ISPEC `heap_segment (gen_gc_partial_conf_gen_start (c:B gen_gc_partial_conf),
      gen_gc_partial_conf_refs_start c) (heap:((A,B)heap_element)list)` BASICAUX_option3_cases) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (fun th -> REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN
        SUBST1_TAC (SYM (CONJUNCT2 (CONJUNCT1 th)))) THEN
      REWRITE_TAC[gc_state_FIELDS.ri_accfupds; K_THM])
    (X_CHOOSE_THEN `old:((A,B)heap_element)list` (X_CHOOSE_THEN
      `curr:((A,B)heap_element)list` (X_CHOOSE_THEN `refs:((A,B)heap_element)list`
        (fun th -> LABEL_TAC "seg" th THEN REWRITE_TAC[th]))))) THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; empty_state_def; gc_state_FIELDS.ri_fupds; K_THM] THEN
  GC2AUX_SPLIT_TAC "rA" "s1" THEN GC2AUX_SPLIT_TAC "refsA" "s2" THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th -> MP_TAC (CONJUNCT2 th) THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM) (CONJUNCTS (CONJUNCT1 th))) THEN
  REWRITE_TAC[REWRITE_RULE[gc_state_FIELDS.ri_fupdcanon] gc_move_data_with_refs';
              gc_state_FIELDS.ri_accfupds; K_THM] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th -> LABEL_TAC "okM" th) THEN
  SUBGOAL_THEN `gc_state_ok (s2:(A,B)gc_state)` (LABEL_TAC "ok2") THENL
   [MATCH_MP_TAC gc_move_data_ok' THEN
    MAP_EVERY EXISTS_TAC [`c:B gen_gc_partial_conf`;
      `gen_gc_partial_gc_move_data (c:B gen_gc_partial_conf) (s2:(A,B)gc_state)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `gc_state_ok (s1:(A,B)gc_state)` (LABEL_TAC "ok1") THENL
   [MP_TAC (ISPECL [`refs:((A,B)heap_element)list`; `refsA:((A,B)heap_element)list`;
      `s1:(A,B)gc_state`; `s2:(A,B)gc_state`; `c:B gen_gc_partial_conf`]
      gc_move_ref_list_ok') THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simple_rel (c:B gen_gc_partial_conf)
     (gc_state_REC old [] [] [] [] refs [] (gen_gc_partial_conf_gen_start c)
        (heap_length (curr:((A,B)heap_element)list)) T heap [])
     (gen_gc_partial_gc_move_data c (s2:(A,B)gc_state))` (LABEL_TAC "sr") THENL
   [MATCH_MP_TAC simple_rel_trans THEN EXISTS_TAC `s1:(A,B)gc_state` THEN CONJ_TAC THENL
     [MATCH_MP_TAC gc_move_list_inv THEN
      MAP_EVERY EXISTS_TAC [`roots:(A heap_address)list`; `rA:(A heap_address)list`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC simple_rel_trans THEN EXISTS_TAC `s2:(A,B)gc_state` THEN CONJ_TAC THENL
     [MP_TAC (ISPECL [`refs:((A,B)heap_element)list`; `refsA:((A,B)heap_element)list`;
        `s1:(A,B)gc_state`; `s2:(A,B)gc_state`; `c:B gen_gc_partial_conf`]
        gc_move_ref_list_inv) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC gc_move_data_inv THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "okM" (LABEL_TAC "h2M" o MATCH_MP gen_gc_partial_gc_move_data_h2) THEN
  SUBGOAL_THEN `gc_state_r1 (gen_gc_partial_gc_move_data (c:B gen_gc_partial_conf)
                  (s2:(A,B)gc_state)) = [] /\
                gc_state_r2 (gen_gc_partial_gc_move_data c s2) = refs`
    (CONJUNCTS_THEN2 (LABEL_TAC "r1M") (LABEL_TAC "r2M")) THENL
   [MP_TAC (ISPECL [`c:B gen_gc_partial_conf`; `s2:(A,B)gc_state`;
      `gen_gc_partial_gc_move_data (c:B gen_gc_partial_conf) (s2:(A,B)gc_state)`]
      gc_move_data_IMP) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_ref_list_IMP o
      check (fun th -> can (find_term ((=) `refsA:((A,B)heap_element)list`)) (concl th) &&
                       is_eq (concl th))) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP gen_gc_partial_gc_move_list_IMP o
      check (fun th -> can (find_term ((=) `rA:(A heap_address)list`)) (concl th) &&
                       is_eq (concl th))) THEN
    REWRITE_TAC[gc_state_FIELDS.ri_accessors] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "sr" (MP_TAC o REWRITE_RULE[simple_rel_def; gc_state_FIELDS.ri_accessors]) THEN
  USE_THEN "h2M" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[APPEND; APPEND_NIL; heap_length_NIL; ADD_CLAUSES; ALL;
              gc_shared_heap_length_heap_expand] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "c1" (el 0 cs) THEN LABEL_TAC "c2" (el 1 cs) THEN LABEL_TAC "c3" (el 2 cs) THEN
    LABEL_TAC "c4" (el 3 cs) THEN LABEL_TAC "c5" (el 4 cs) THEN LABEL_TAC "c6" (el 5 cs) THEN
    LABEL_TAC "c7" (el 6 cs) THEN LABEL_TAC "c8" (el 7 cs)) THEN
  USE_THEN "seg" (fun th -> let cs = CONJUNCTS (MATCH_MP heap_segment_IMP th) in
    LABEL_TAC "happ" (el 0 cs) THEN LABEL_TAC "hlo" (el 1 cs) THEN
    LABEL_TAC "hloc" (el 2 cs)) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "c3" ACCEPT_TAC;
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP gen_gc_partial_gc_move_list_length);
    USE_THEN "c1" SUBST1_TAC THEN USE_THEN "hlo" ACCEPT_TAC;
    USE_THEN "c1" SUBST1_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[heap_length_APPEND] THEN USE_THEN "c2" SUBST1_TAC THEN
    USE_THEN "hloc" (MP_TAC o REWRITE_RULE[heap_length_APPEND]) THEN
    USE_THEN "hlo" SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC;
    (DISCH_TAC THEN
       SUBGOAL_THEN `balanced_state (c:B gen_gc_partial_conf)
          (gc_state_REC (old:((A,B)heap_element)list) [] [] [] [] refs []
             (gen_gc_partial_conf_gen_start c)
             (heap_length (curr:((A,B)heap_element)list)) T heap [])` ASSUME_TAC THENL
        [REWRITE_TAC[balanced_state_def; gc_state_FIELDS.ri_accessors] THEN
         ASM_REWRITE_TAC[heap_length_NIL; ADD_CLAUSES; FILTER] THEN CAKE_REWRITE_TAC[] THEN
         REWRITE_TAC[FILTER; heap_length_NIL] THEN ARITH_TAC;
         ALL_TAC] THEN
       USE_THEN "c7" (fun c7 -> FIRST_ASSUM(fun b -> MP_TAC (MATCH_MP c7 b))) THEN
       REWRITE_TAC[balanced_state_def] THEN
       USE_THEN "h2M" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "r1M" (fun th -> REWRITE_TAC[th]) THEN
       USE_THEN "r2M" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "c1" (fun th -> REWRITE_TAC[th]) THEN
       MP_TAC (ISPEC `heap_segment (gen_gc_partial_conf_gen_start (c:B gen_gc_partial_conf),
           gen_gc_partial_conf_refs_start c)
           (gc_state_heap (gen_gc_partial_gc_move_data c (s2:(A,B)gc_state)))`
           BASICAUX_option3_cases) THEN
       DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CAKE_REWRITE_TAC[])
         (X_CHOOSE_THEN `o1:((A,B)heap_element)list` (X_CHOOSE_THEN
           `cm:((A,B)heap_element)list` (X_CHOOSE_THEN `rm:((A,B)heap_element)list`
             (fun th -> REWRITE_TAC[th] THEN LABEL_TAC "segM" th))))) THEN
       CAKE_REWRITE_TAC[] THEN
       REWRITE_TAC[FILTER; heap_length_NIL; ADD_CLAUSES] THEN STRIP_TAC THEN
       USE_THEN "segM" (MP_TAC o CONJUNCT1 o MATCH_MP heap_segment_IMP) THEN
       DISCH_THEN(ASSUME_TAC o SYM) THEN
       FIRST_ASSUM(MP_TAC o MATCH_MP LIST_REL_similar_data_IMP o
         MATCH_MP gc_move_ref_list_similar o
         check (fun th -> can (find_term ((=) `refsA:((A,B)heap_element)list`)) (concl th) &&
                          is_eq (concl th) && not (is_var (lhs (concl th))))) THEN
       STRIP_TAC THEN
       USE_THEN "c5" SUBST1_TAC THEN
       USE_THEN "c4" (fun th -> REWRITE_TAC[REWRITE_RULE[GSYM FILTER_EQ_ID] th; FILTER_APPEND]) THEN
       ASM_REWRITE_TAC[FILTER_APPEND; heap_length_APPEND] THEN ASM_ARITH_TAC);
    USE_THEN "c4" ACCEPT_TAC;
    (MAP_EVERY EXISTS_TAC [`curr:((A,B)heap_element)list`; `refs:((A,B)heap_element)list`] THEN
       USE_THEN "c1" (fun th -> REWRITE_TAC[th]) THEN
       CONJ_TAC THENL
        [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP gc_move_ref_list_similar o
           check (fun th -> can (find_term ((=) `refsA:((A,B)heap_element)list`)) (concl th) &&
                            is_eq (concl th) && not (is_var (lhs (concl th)))));
         ALL_TAC] THEN
       REPEAT STRIP_TAC THEN
       SUBGOAL_THEN `has_bad_ref (c:B gen_gc_partial_conf)
                       (gen_gc_partial_gc_move_data c (s2:(A,B)gc_state))`
         (fun th -> USE_THEN "c8" (fun c8 -> MP_TAC (MATCH_MP c8 th))) THENL
        [REWRITE_TAC[has_bad_ref_def] THEN DISJ1_TAC THEN
         MAP_EVERY EXISTS_TAC [`xs:(A heap_address)list`; `l:num`; `d:B`] THEN
         ASM_REWRITE_TAC[MEM_APPEND];
         ALL_TAC] THEN
       REWRITE_TAC[has_bad_ref_def; gc_state_FIELDS.ri_accessors; APPEND; MEM] THEN
       STRIP_TAC THEN
       USE_THEN "seg" (fun sg -> FIRST_ASSUM(fun a -> FIRST_ASSUM(fun b ->
         MP_TAC (MATCH_MP GC2AUX_lookup_current (CONJ sg (CONJ a b)))))) THEN
       DISCH_TAC THEN ASM_MESON_TAC[heap_lookup_IMP_MEM])]);;
