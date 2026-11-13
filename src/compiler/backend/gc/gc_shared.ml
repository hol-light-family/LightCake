(* ========================================================================= *)
(* gc_shared: port of HOL4 compiler/backend/gc/gc_sharedScript.sml           *)
(* (CakeML v3479).  Types, functions and lemmas that are shared between GC   *)
(* definitions.                                                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;

(* The ML heap is represented as a list of heap_elements. *)

let heap_address_INDUCT,heap_address_RECURSION =
  cake_type "heap_address = Pointer num A | gc_shared_Data A";;

let heap_element_INDUCT,heap_element_RECURSION =
  cake_type "heap_element = Unused num | ForwardPointer num A num | \
             DataElement ((A heap_address)list) num B";;

(* the HOL4 Datatype theorems used by name *)
let heap_address_distinct = distinctness "heap_address";;
let heap_address_11 = injectivity "heap_address";;
let heap_element_distinct = distinctness "heap_element";;
let heap_element_11 = injectivity "heap_element";;

let gc_state_FIELDS = cake_record "gc_state"
  ["old","((A,B)heap_element)list";        (* old generations *)
   "h1","((A,B)heap_element)list";         (* final left heap *)
   "h2","((A,B)heap_element)list";         (* not updated left heap *)
   "r4","((A,B)heap_element)list";         (* not updated right heap *)
   "r3","((A,B)heap_element)list";         (* temp. final right heap *)
   "r2","((A,B)heap_element)list";         (* temp. not updated right heap *)
   "r1","((A,B)heap_element)list";         (* final right heap *)
   "a","num";                             (* gen_start + heap_length (h1 ++ h2) *)
   "n","num";                             (* unused heap space *)
   "ok","bool";                           (* OK *)
   "heap","((A,B)heap_element)list";       (* old heap (w/ fwd pointers) *)
   "heap0","((A,B)heap_element)list"];;    (* old heap *)

let gc_state_component_equality =
  (record_info "gc_state").ri_component_equality;;

let empty_state_def = cake_def
  `empty_state:(A,B)gc_state = gc_state_REC [] [] [] [] [] [] [] 0 0 T [] []`;;

(* The heap is accessed using the following lookup function. *)

let el_length_def = cake_def
  `(el_length (Unused l:(A,B)heap_element) = l + 1) /\
   (el_length (ForwardPointer n (d:A) l:(A,B)heap_element) = l + 1) /\
   (el_length (DataElement (xs:(A heap_address)list) l (data:B)) = l + 1)`;;

let el_length_NOT_0 = prove
 (`!el:(A,B)heap_element. ~(el_length el = 0)`,
  GEN_TAC THEN CASES_ON `el:(A,B)heap_element` THEN FS[el_length_def]);;

let el_length_GT_0 = prove
 (`!el:(A,B)heap_element. 1 <= el_length el`,
  GEN_TAC THEN CASES_ON `el:(A,B)heap_element` THEN FS[el_length_def] THEN
  ARITH_TAC);;

let heap_length_def = cake_def
  `heap_length (heap:((A,B)heap_element)list) = SUM (MAP el_length heap)`;;

let heap_length_NIL = prove
 (`heap_length ([]:((A,B)heap_element)list) = 0`,
  FS[heap_length_def; SUM]);;
let _ = cake_add_simps [heap_length_NIL];;

let heap_length_GTE = prove
 (`!heap:((A,B)heap_element)list. 0 <= heap_length heap`,
  FS[heap_length_def]);;

let heap_length_APPEND = prove
 (`!xs ys:((A,B)heap_element)list.
     heap_length (APPEND xs ys) = heap_length xs + heap_length ys`,
  RW[heap_length_def; MAP_APPEND; SUM_APPEND]);;

let heap_lookup_def = cake_def
  `(heap_lookup a ([]:((A,B)heap_element)list) = NONE) /\
   (heap_lookup a (CONS x xs) =
      if a = 0 then SOME x else
      if a < el_length x then NONE else heap_lookup (a - el_length x) xs)`;;

(* the kit's arithmetic needs the lengths of heap elements to be positive: *)
(* GC1AUX_EL_LENGTH_TAC adds 1 <= el_length t for every el_length t of the *)
(* goal and its assumptions                                               *)

let GC1AUX_EL_LENGTH_TAC : tactic =
  fun (asl,w as gl) ->
    let tms = find_terms (fun t -> is_comb t && is_const (rator t) &&
                            fst(dest_const(rator t)) = "el_length")
                (list_mk_conj (w :: map (concl o snd) asl)) in
    MAP_EVERY (fun t -> ASSUME_TAC (ISPEC (rand t) el_length_GT_0)) tms gl;;

let GC1AUX_heap_length_CONS = prove
 (`!(x:(A,B)heap_element) xs.
     heap_length (CONS x xs) = el_length x + heap_length xs`,
  REWRITE_TAC[heap_length_def; MAP; SUM]);;

let heap_lookup_MEM = prove
 (`!heap n (x:(A,B)heap_element). heap_lookup n heap = SOME x ==> MEM x heap`,
  LIST_INDUCT_TAC THEN RW[heap_lookup_def; MEM] THEN ASM_MESON_TAC[]);;

let MEM_IMP_heap_lookup = prove
 (`!xs (x:(A,B)heap_element). MEM x xs ==> ?j. heap_lookup j xs = SOME x`,
  LIST_INDUCT_TAC THEN RW[MEM; heap_lookup_def] THENL
   [EXISTS_TAC `0` THEN SIMP[]; ALL_TAC] THEN
  RES_TAC THEN EXISTS_TAC `j + el_length (h:(A,B)heap_element)` THEN
  GC1AUX_EL_LENGTH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= e ==> ~(j + e = 0) /\ ~(j + e < e) /\
                                       (j + e) - e = j`]);;

let heap_lookup_LESS = prove
 (`!xs n (x:(A,B)heap_element).
     heap_lookup n xs = SOME x ==> n < heap_length xs`,
  LIST_INDUCT_TAC THEN RW[heap_lookup_def; GC1AUX_heap_length_CONS] THEN
  RES_TAC THEN GC1AUX_EL_LENGTH_TAC THEN ASM_ARITH_TAC);;

let heap_split_def = cake_def
  `(heap_split a ([]:((A,B)heap_element)list) =
      if a = 0 then SOME ([],[]) else NONE) /\
   (heap_split a (CONS e heap) =
      if a = 0 then SOME ([],CONS e heap) else
      if a < el_length e then NONE else
      match heap_split (a - el_length e) heap with
        NONE -> NONE
      | SOME (h1,h2) -> SOME (CONS e h1,h2))`;;

let heap_lookup_SPLIT = prove
 (`!heap n (x:(A,B)heap_element).
     heap_lookup n heap = SOME x
     ==> ?ha hb. heap = APPEND ha (CONS x hb) /\ n = heap_length ha`,
  LIST_INDUCT_TAC THEN RW[heap_lookup_def] THENL
   [MAP_EVERY EXISTS_TAC [`[]:((A,B)heap_element)list`; `t:((A,B)heap_element)list`] THEN
    SIMP[APPEND];
    RES_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:(A,B)heap_element) ha`; `hb:((A,B)heap_element)list`] THEN
    ASM_REWRITE_TAC[APPEND; GC1AUX_heap_length_CONS] THEN ASM_ARITH_TAC]);;

let heap_drop_def = cake_def
  `heap_drop n (heap:((A,B)heap_element)list) =
     match heap_split n heap with
       NONE -> ARB
     | SOME (h1,h2) -> h2`;;

let heap_take_def = cake_def
  `heap_take n (heap:((A,B)heap_element)list) =
     match heap_split n heap with
       NONE -> ARB
     | SOME (h1,h2) -> h1`;;

let heap_split_heap_length = prove
 (`!heap h1 h2 a.
     heap_split a heap = SOME (h1,h2:((A,B)heap_element)list)
     ==> heap_length h1 = a /\
         heap_length (APPEND h1 h2) = heap_length heap /\
         APPEND h1 h2 = heap`,
  LIST_INDUCT_TAC THEN RW[heap_split_def] THEN GVS(all_case_eqs()) THEN
  RES_TAC THEN ASM_REWRITE_TAC[GC1AUX_heap_length_CONS] THEN ASM_ARITH_TAC);;

let heap_segment_def = cake_def
  `heap_segment (a,b) (heap:((A,B)heap_element)list) =
     match heap_split a heap with
       NONE -> NONE
     | SOME (h1,heap') ->
         if b < a then NONE else
         match heap_split (b - heap_length h1) heap' with
           NONE -> NONE
         | SOME (h2,h3) -> SOME (h1,h2,h3)`;;

let heap_segment_IMP = prove
 (`!heap a b h1 h2 (h3:((A,B)heap_element)list).
     heap_segment (a,b) heap = SOME (h1,h2,h3)
     ==> APPEND (APPEND h1 h2) h3 = heap /\
         heap_length h1 = a /\
         heap_length (APPEND h1 h2) = b /\
         heap_length h3 = heap_length heap - b`,
  RW[heap_segment_def] THEN GVS(all_case_eqs()) THEN
  IMP_RES_TAC heap_split_heap_length THEN
  RULE_ASSUM_TAC(REWRITE_RULE[heap_length_APPEND]) THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; heap_length_APPEND] THEN ASM_ARITH_TAC);;

let heap_restrict_def = cake_def
  `heap_restrict start end (heap:((A,B)heap_element)list) =
     match heap_segment (start,end) heap with
       NONE -> []
     | SOME (h1,h2,h3) -> h2`;;

(* The heap is well-formed if heap_ok *)

let isDataElement_def = cake_def
  `isDataElement (x:(A,B)heap_element) <=> ?ys l d. x = DataElement ys l d`;;

let isSomeDataElement_def = cake_def
  `isSomeDataElement (x:((A,B)heap_element)option) <=>
     ?ys l d. x = SOME (DataElement ys l d)`;;

let isSomeForwardPointer_def = cake_def
  `isSomeForwardPointer (x:((A,B)heap_element)option) <=>
     ?ptr d l. x = SOME (ForwardPointer ptr d l)`;;

let isSomeDataOrForward_def = cake_def
  `isSomeDataOrForward (x:((A,B)heap_element)option) <=>
     isSomeForwardPointer x \/ isSomeDataElement x`;;

let roots_ok_def = cake_def
  `roots_ok roots (heap:((A,B)heap_element)list) <=>
     !ptr (u:A). MEM (Pointer ptr u) roots
                 ==> isSomeDataElement (heap_lookup ptr heap)`;;

let isForwardPointer_def = cake_def
  `(isForwardPointer (ForwardPointer n (d:A) l:(A,B)heap_element) <=> T) /\
   (isForwardPointer (_:(A,B)heap_element) <=> F)`;;

(* heap_ok: the length is limit, there are no forward pointers, and all *)
(* pointers in DataElements point to some DataElement                    *)
let heap_ok_def = cake_def
  `heap_ok (heap:((A,B)heap_element)list) limit <=>
     heap_length heap = limit /\
     FILTER isForwardPointer heap = [] /\
     (!xs l d ptr u. MEM (DataElement xs l d) heap /\ MEM (Pointer ptr u) xs
                     ==> isSomeDataElement (heap_lookup ptr heap))`;;

(* replace cell at a with a forwardpointer to ptr *)
let gc_forward_ptr_def = cake_def
  `(gc_forward_ptr a ([]:((A,B)heap_element)list) ptr (d:A) ok = ([],F)) /\
   (gc_forward_ptr a (CONS x xs) ptr d ok =
      if a = 0 then
        (CONS (ForwardPointer ptr d (el_length x - 1)) xs,(isDataElement x /\ ok))
      else if a < el_length x then (CONS x xs,F) else
      match gc_forward_ptr (a - el_length x) xs ptr d ok with
        (xs,ok) -> (CONS x xs,ok))`;;

let gc_shared_gc_forward_ptr_ok = prove
 (`!heap n a c x (d:A).
     gc_forward_ptr n (heap:((A,B)heap_element)list) a d c = (x,T) ==> c`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[gc_forward_ptr_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; pair_case_eq] THENL
   [MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `ys:((A,B)heap_element)list` THEN X_GEN_TAC `y:bool` THEN
    BOOL_CASES_TAC `y:bool` THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let gc_forward_ptr_thm = prove
 (`!ha (ys:(A heap_address)list) l (d:B) hb a (u:A) c.
     gc_forward_ptr (heap_length ha) (APPEND ha (CONS (DataElement ys l d) hb)) a u c =
     (APPEND ha (CONS (ForwardPointer a u l) hb),c)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_length_NIL; APPEND; GC1AUX_heap_length_CONS] THEN
  ONCE_REWRITE_TAC[gc_forward_ptr_def] THENL
   [SIMP_NOASM[el_length_def; isDataElement_def];
    GC1AUX_EL_LENGTH_TAC THEN
    ASM_SIMP_TAC[pair_CASE; ARITH_RULE
      `1 <= e ==> ~(e + n = 0) /\ ~(e + n < e) /\ (e + n) - e = n`]]);;

let heap_expand_def = cake_def
  `heap_expand n:((A,B)heap_element)list = if n = 0 then [] else [Unused (n - 1)]`;;

let heap_map_def = cake_def
  `(heap_map a ([]:((A,B)heap_element)list) = FEMPTY) /\
   (heap_map a (CONS (ForwardPointer ptr d l) xs) =
      heap_map (a + l + 1) xs |+ (a,ptr)) /\
   (heap_map a (CONS x xs) = heap_map (a + el_length x) xs)`;;

let heap_map1_def = cake_def
  `heap_map1 (heap:((A,B)heap_element)list) = (\a. FAPPLY (heap_map 0 heap) a)`;;

let heap_addresses_def = cake_def
  `(heap_addresses a ([]:((A,B)heap_element)list) = {}) /\
   (heap_addresses a (CONS x xs) = a INSERT heap_addresses (a + el_length x) xs)`;;

let ADDR_MAP_def = cake_def
  `(ADDR_MAP (f:num->num) ([]:(A heap_address)list) = []) /\
   (ADDR_MAP f (CONS (gc_shared_Data x) xs) =
      CONS (gc_shared_Data x) (ADDR_MAP f xs)) /\
   (ADDR_MAP f (CONS (Pointer a d) xs) = CONS (Pointer (f a) d) (ADDR_MAP f xs))`;;

let gc_shared_ADDR_MAP_EQ = prove
 (`!xs (f:num->num) g.
     (!p (d:A). MEM (Pointer p d) xs ==> f p = g p)
     ==> ADDR_MAP f xs = ADDR_MAP g xs`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:A heap_address`) THEN
  RW[ADDR_MAP_def; MEM] THEN ASM_MESON_TAC[]);;

let ADDR_MAP_LENGTH = prove
 (`!xs (f:num->num). LENGTH xs = LENGTH (ADDR_MAP f xs:(A heap_address)list)`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:A heap_address`) THEN
  REWRITE_TAC[ADDR_MAP_def; LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]);;

let ADDR_MAP_APPEND = prove
 (`!h1 h2 (f:num->num).
     ADDR_MAP f (APPEND h1 h2):(A heap_address)list =
     APPEND (ADDR_MAP f h1) (ADDR_MAP f h2)`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:A heap_address`) THEN
  ASM_REWRITE_TAC[ADDR_MAP_def; APPEND]);;

let ADDR_APPLY_def = cake_def
  `(ADDR_APPLY (f:num->num) (Pointer x (d:A)) = Pointer (f x) d) /\
   (ADDR_APPLY f (gc_shared_Data y) = gc_shared_Data y)`;;

(* HOL4 proves heap_lookup_FLOOKUP for any start address k and specialises *)
(* it to 0                                                                 *)
let GC1AUX_heap_lookup_FLOOKUP = prove
 (`!heap n k.
     heap_lookup n heap = SOME (ForwardPointer ptr (u:A) l:(A,B)heap_element)
     ==> FLOOKUP (heap_map k heap) (n + k) = SOME ptr`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[heap_map_def; FLOOKUP_UPDATE; ADD_CLAUSES];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`n - el_length (h:(A,B)heap_element)`; `k + el_length (h:(A,B)heap_element)`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n - el_length (h:(A,B)heap_element) + k + el_length h = n + k`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CASES_ON `h:(A,B)heap_element` THEN
  REWRITE_TAC[heap_map_def; FLOOKUP_UPDATE; el_length_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> ~(k = n + k)`]);;

let heap_lookup_FLOOKUP = prove
 (`!heap n ptr (u:A) l.
     heap_lookup n heap = SOME (ForwardPointer ptr u l:(A,B)heap_element)
     ==> FLOOKUP (heap_map 0 heap) n = SOME ptr`,
  MESON_TAC[GC1AUX_heap_lookup_FLOOKUP; ADD_CLAUSES]);;

(* HOL4 adds LIST_REL_def (ALL2) to its simpset here; the port names ALL2 *)
(* where it is needed                                                      *)
let heaps_similar_def = cake_def
  `heaps_similar (heap0:((A,B)heap_element)list) heap <=>
     ALL2 (\h0 h. if isForwardPointer h then
                    el_length h = el_length h0 /\ isDataElement h0
                  else h = h0) heap0 heap`;;

let IN_heap_map_IMP = prove
 (`!heap n k. n IN FDOM (heap_map k (heap:((A,B)heap_element)list)) ==> k <= n`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:(A,B)heap_element`) THEN
  REWRITE_TAC[heap_map_def; FDOM_FEMPTY; NOT_IN_EMPTY; FDOM_FUPDATE; IN_INSERT;
              el_length_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

let GC1AUX_NOT_IN_heap_map = prove
 (`!ha n. ~(n + heap_length ha IN
            FDOM (heap_map n (APPEND ha (CONS (DataElement ys l d) hb)
                               :((A,B)heap_element)list)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; heap_length_NIL; ADD_CLAUSES] THENL
   [GEN_TAC THEN REWRITE_TAC[heap_map_def; el_length_def] THEN
    DISCH_THEN(MP_TAC o MATCH_MP IN_heap_map_IMP) THEN ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[GC1AUX_heap_length_CONS] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + el_length (h:(A,B)heap_element)`) THEN
    CASES_ON `h:(A,B)heap_element` THEN
    REWRITE_TAC[heap_map_def; el_length_def; FDOM_FUPDATE; IN_INSERT; ADD_ASSOC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let NOT_IN_heap_map = prove
 (`!ha (ys:(A heap_address)list) l (d:B) hb.
     ~(heap_length ha IN FDOM (heap_map 0 (APPEND ha (CONS (DataElement ys l d) hb))))`,
  MESON_TAC[GC1AUX_NOT_IN_heap_map; ADD_CLAUSES]);;

let gc_shared_isSomeDataOrForward_lemma = prove
 (`!ha ptr (ys:(A heap_address)list) l (d:B) hb a (u:A).
     isSomeDataOrForward (heap_lookup ptr (APPEND ha (CONS (DataElement ys l d) hb))) <=>
     isSomeDataOrForward
       (heap_lookup ptr (APPEND (APPEND ha [ForwardPointer a u l]) hb))`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; heap_lookup_def] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FS[isSomeDataOrForward_def; isSomeForwardPointer_def; isSomeDataElement_def;
     el_length_def]);;

let heaps_similar_IMP_heap_length = prove
 (`!xs ys:((A,B)heap_element)list.
     heaps_similar xs ys ==> heap_length xs = heap_length ys`,
  REWRITE_TAC[heaps_similar_def] THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  CASES_ON `ys:((A,B)heap_element)list` THEN
  REWRITE_TAC[ALL2; heap_length_NIL; GC1AUX_heap_length_CONS] THEN
  COND_CASES_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let heap_similar_Data_IMP = prove
 (`!heap0 ha (ys:(A heap_address)list) l (d:B) hb.
     heaps_similar heap0 (APPEND ha (CONS (DataElement ys l d) hb))
     ==> ?ha0 hb0. heap0 = APPEND ha0 (CONS (DataElement ys l d) hb0) /\
                   heap_length ha = heap_length ha0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[heaps_similar_def; LIST_REL_SPLIT2] THEN
  REWRITE_TAC[LIST_REL_CONS2; isForwardPointer_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ys1:((A,B)heap_element)list`; `t':((A,B)heap_element)list`] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[heaps_similar_def] heaps_similar_IMP_heap_length) THEN
  ASM_REWRITE_TAC[]);;

let gc_shared_heaps_similar_lemma = prove
 (`!ha heap0 (ys:(A heap_address)list) l (d:B) hb (h1:((C,D)heap_element)list) h2
    (u:A).
     heaps_similar heap0 (APPEND ha (CONS (DataElement ys l d) hb))
     ==> heaps_similar heap0
           (APPEND (APPEND ha [ForwardPointer (heap_length (APPEND h1 h2)) u l]) hb)`,
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

let heap_lookup_PREFIX = prove
 (`!xs (x:(A,B)heap_element) ys.
     heap_lookup (heap_length xs) (APPEND xs (CONS x ys)) = SOME x`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_length_NIL; APPEND; GC1AUX_heap_length_CONS; heap_lookup_def] THEN
  GC1AUX_EL_LENGTH_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= e ==> ~(e + n = 0) /\ ~(e + n < e) /\ (e + n) - e = n`]);;

let gc_shared_heap_lookup_EXTEND = prove
 (`!xs n ys (x:(A,B)heap_element).
     heap_lookup n xs = SOME x ==> heap_lookup n (APPEND xs ys) = SOME x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; APPEND; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let heap_map_APPEND = prove
 (`!xs n ys:((A,B)heap_element)list.
     heap_map n (APPEND xs ys) =
     FUNION (heap_map n xs) (heap_map (n + heap_length xs) ys)`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:(A,B)heap_element`) THEN
  ASM_REWRITE_TAC[APPEND; heap_map_def; FUNION_FEMPTY_1; heap_length_NIL;
    ADD_CLAUSES; GC1AUX_heap_length_CONS; FUNION_FUPDATE_1; el_length_def;
    ADD_ASSOC]);;

let GC1AUX_FDOM_heap_map = prove
 (`!xs n. ~(n + heap_length xs IN FDOM (heap_map n (xs:((A,B)heap_element)list)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_map_def; FDOM_FEMPTY; NOT_IN_EMPTY] THEN
  GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n + el_length (h:(A,B)heap_element)`) THEN
  CASES_ON `h:(A,B)heap_element` THEN
  REWRITE_TAC[heap_map_def; GC1AUX_heap_length_CONS; el_length_def; FDOM_FUPDATE;
              IN_INSERT; ADD_ASSOC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let FDOM_heap_map = prove
 (`!xs. ~(heap_length xs IN FDOM (heap_map 0 (xs:((A,B)heap_element)list)))`,
  MESON_TAC[GC1AUX_FDOM_heap_map; ADD_CLAUSES]);;

let gc_shared_heap_addresses_APPEND = prove
 (`!xs ys:((A,B)heap_element)list n.
     heap_addresses n (APPEND xs ys) =
     heap_addresses n xs UNION heap_addresses (n + heap_length xs) ys`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; heap_addresses_def; heap_length_NIL; ADD_CLAUSES;
    UNION_EMPTY; GC1AUX_heap_length_CONS; ADD_ASSOC; INSERT_UNION_EQ]);;

let gc_shared_LESS_IMP_heap_lookup = prove
 (`!xs j ys:((A,B)heap_element)list.
     j < heap_length xs ==> heap_lookup j (APPEND xs ys) = heap_lookup j xs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_length_NIL; LT; APPEND; heap_lookup_def; GC1AUX_heap_length_CONS] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j < el_length (h:(A,B)heap_element)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let NOT_LESS_IMP_heap_lookup = prove
 (`!xs j ys:((A,B)heap_element)list.
     ~(j < heap_length xs)
     ==> heap_lookup j (APPEND xs ys) = heap_lookup (j - heap_length xs) ys`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_length_NIL; APPEND; SUB_0; GC1AUX_heap_length_CONS; heap_lookup_def] THEN
  REPEAT STRIP_TAC THEN GC1AUX_EL_LENGTH_TAC THEN
  SUBGOAL_THEN `~(j = 0) /\ ~(j < el_length (h:(A,B)heap_element)) /\
                ~(j - el_length h < heap_length (t:((A,B)heap_element)list))`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `j - e - n = j - (e + n)`]);;

let heap_similar_Data_IMP_DataOrForward = prove
 (`!heap0 heap1 ptr.
     heaps_similar heap0 (heap1:((A,B)heap_element)list) /\
     isSomeDataElement (heap_lookup ptr heap0)
     ==> isSomeDataOrForward (heap_lookup ptr heap1)`,
  REWRITE_TAC[heaps_similar_def] THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  CASES_ON `heap1:((A,B)heap_element)list` THEN REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[heap_lookup_def; isSomeDataElement_def; option_DISTINCT] THEN
  GEN_TAC THEN ASM_CASES_TAC `ptr = 0` THEN ASM_REWRITE_TAC[option_INJ] THEN
  STRIP_TAC THENL
   [RVEQ_TAC THEN CASES_ON `a0:(A,B)heap_element` THEN
    FS[isForwardPointer_def; isSomeDataOrForward_def; isSomeForwardPointer_def;
       isSomeDataElement_def];
    SUBGOAL_THEN `el_length (a0:(A,B)heap_element) = el_length (h:(A,B)heap_element)`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[isSomeDataElement_def] THEN ASM_MESON_TAC[]]);;

let FILTER_LEMMA = prove
 (`!heap:((A,B)heap_element)list.
     FILTER isForwardPointer heap = []
     ==> FILTER (\h. ~isForwardPointer h) heap = heap`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11]);;

let heaps_similar_REFL = prove
 (`!xs:((A,B)heap_element)list.
     FILTER isForwardPointer xs = [] ==> heaps_similar xs xs`,
  REWRITE_TAC[heaps_similar_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; ALL2] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL]);;

let heap_map_EMPTY = prove
 (`!xs n. FILTER isForwardPointer xs = []
          ==> FDOM (heap_map n (xs:((A,B)heap_element)list)) = {}`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:(A,B)heap_element`) THEN
  REWRITE_TAC[heap_map_def; FILTER; isForwardPointer_def; FDOM_FEMPTY;
              NOT_CONS_NIL] THEN
  ASM_MESON_TAC[]);;

let MEM_ADDR_MAP = prove
 (`!xs (f:num->num) ptr (u:A).
     MEM (Pointer ptr u) (ADDR_MAP f xs) ==> ?y. MEM (Pointer y u) xs /\ f y = ptr`,
  LIST_INDUCT_TAC THEN TRY (CASES_ON `h:A heap_address`) THEN
  REWRITE_TAC[ADDR_MAP_def; MEM; injectivity "heap_address";
              distinctness "heap_address"] THEN
  ASM_MESON_TAC[]);;

let gc_shared_heap_length_heap_expand = prove
 (`!n. heap_length (heap_expand n:((A,B)heap_element)list) = n`,
  INDUCT_TAC THEN
  REWRITE_TAC[heap_expand_def; NOT_SUC; SUC_SUB1; heap_length_NIL;
              GC1AUX_heap_length_CONS; el_length_def] THEN
  ARITH_TAC);;

let EVERY_isDataElement_IMP_LEMMA = prove
 (`!heap2:((A,B)heap_element)list.
     ALL isDataElement heap2 ==> FILTER isForwardPointer heap2 = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; FILTER; isDataElement_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[isForwardPointer_def] THEN ASM_MESON_TAC[]);;

let isSome_heap_looukp_IMP_APPEND = prove
 (`!xs ptr ys:((A,B)heap_element)list.
     isSomeDataElement (heap_lookup ptr xs)
     ==> isSomeDataElement (heap_lookup ptr (APPEND xs ys))`,
  REWRITE_TAC[isSomeDataElement_def] THEN
  MESON_TAC[gc_shared_heap_lookup_EXTEND]);;

let heap_split_APPEND_if = prove
 (CASE_TERM `!h1 n h2:((A,B)heap_element)list.
     heap_split n (APPEND h1 h2) =
     if n < heap_length h1 then
       match heap_split n h1 with
         NONE -> NONE
       | SOME (h1',h2') -> SOME (h1',APPEND h2' h2)
     else
       match heap_split (n - heap_length h1) h2 with
         NONE -> NONE
       | SOME (h1',h2') -> SOME (APPEND h1 h1',h2')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; heap_length_NIL; LT; SUB_0] THEN
  REPEAT GEN_TAC THENL
   [CASES_ON `heap_split n (h2:((A,B)heap_element)list)` THEN SIMP[] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN SIMP[];
    ALL_TAC] THEN
  REWRITE_TAC[heap_split_def; GC1AUX_heap_length_CONS] THEN ASM_REWRITE_TAC[] THEN
  GC1AUX_EL_LENGTH_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [SIMP[ARITH_RULE `1 <= e ==> 0 < e + n`; APPEND]; ALL_TAC] THEN
  ASM_CASES_TAC `n < el_length (h:(A,B)heap_element)` THEN ASM_REWRITE_TAC[] THENL
   [SIMP[ARITH_RULE `n < e ==> n < e + m`]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(n - el_length (h:(A,B)heap_element) < heap_length (t:((A,B)heap_element)list) <=>
      n < el_length h + heap_length t) /\
     n - (el_length h + heap_length t) = n - el_length h - heap_length t`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN SIMP[APPEND]);;

let heap_split_0 = prove
 (`!h:((A,B)heap_element)list. heap_split 0 h = SOME ([],h)`,
  GEN_TAC THEN CASES_ON `h:((A,B)heap_element)list` THEN
  REWRITE_TAC[heap_split_def]);;

let _ = cake_add_simps [heap_split_0];;

(* --- *)

let gc_related_def = cake_def
  `gc_related (f:(num,num)fmap) (heap1:((A,B)heap_element)list) heap2 <=>
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap2)} /\
     (!i. i IN FDOM f ==> isSomeDataElement (heap_lookup i heap1)) /\
     !i xs l d.
       i IN FDOM f /\ heap_lookup i heap1 = SOME (DataElement xs l d)
       ==> heap_lookup (FAPPLY f i) heap2 =
             SOME (DataElement (ADDR_MAP (FAPPLY f) xs) l d) /\
           !ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM f`;;

(* an edge in the heap *)

let gc_edge_def = cake_def
  `gc_edge (heap:((A,B)heap_element)list) x y <=>
     ?xs l d t. heap_lookup x heap = SOME (DataElement xs l d) /\
                MEM (Pointer y t) xs`;;

let reachable_addresses_def = cake_def
  `reachable_addresses (roots:(A heap_address)list)
                       (heap:((A,B)heap_element)list) y <=>
     ?t x. MEM (Pointer x t) roots /\ RTC (gc_edge heap) x y`;;

let heap_addresses_LESS_heap_length = prove
 (`!heap n k. k IN heap_addresses n (heap:((A,B)heap_element)list)
              ==> k < n + heap_length heap`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_addresses_def; NOT_IN_EMPTY; IN_INSERT; GC1AUX_heap_length_CONS] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN GC1AUX_EL_LENGTH_TAC THEN ASM_ARITH_TAC);;

let heap_addresses_LESS = prove
 (`!heap n k. k IN heap_addresses n (heap:((A,B)heap_element)list) ==> n <= k`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[heap_addresses_def; NOT_IN_EMPTY; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

let FINITE_heap_addresses = prove
 (`!xs n. FINITE (heap_addresses n (xs:((A,B)heap_element)list))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[heap_addresses_def; FINITE_EMPTY; FINITE_INSERT]);;

let CARD_heap_addresses = prove
 (`!xs n. CARD (heap_addresses n (xs:((A,B)heap_element)list)) = LENGTH xs`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[heap_addresses_def; CARD_CLAUSES; FINITE_heap_addresses; LENGTH] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_addresses_LESS) THEN
  GC1AUX_EL_LENGTH_TAC THEN ASM_ARITH_TAC);;

let heap_filter_aux_def = cake_def
  `(heap_filter_aux n (P:num->bool) ([]:((A,B)heap_element)list) = []) /\
   (heap_filter_aux n P (CONS x xs) =
      APPEND (if n IN P then [x] else []) (heap_filter_aux (n + el_length x) P xs))`;;

let heap_filter_def = cake_def
  `heap_filter:(num->bool)->((A,B)heap_element)list->((A,B)heap_element)list =
     heap_filter_aux 0`;;

let heap_filter_EMPTY = prove
 (`!heap:((A,B)heap_element)list. heap_filter {} heap = []`,
  REWRITE_TAC[heap_filter_def] THEN
  SUBGOAL_THEN `!(heap:((A,B)heap_element)list) n. heap_filter_aux n {} heap = []`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[heap_filter_aux_def; NOT_IN_EMPTY; APPEND]);;

let heap_length_heap_filter_INSERT = prove
 (`!heap:((A,B)heap_element)list e s.
     ~(e IN s)
     ==> heap_length (heap_filter (e INSERT s) heap) =
         heap_length (heap_filter {e} heap) + heap_length (heap_filter s heap)`,
  REWRITE_TAC[heap_filter_def] THEN
  SUBGOAL_THEN
    `!(heap:((A,B)heap_element)list) n e s.
       ~(e IN s)
       ==> heap_length (heap_filter_aux n (e INSERT s) heap) =
           heap_length (heap_filter_aux n {e} heap) +
           heap_length (heap_filter_aux n s heap)`
    (fun th -> SIMP_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_filter_aux_def; heap_length_NIL; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[heap_length_APPEND; IN_INSERT; IN_SING] THEN
  ASM_CASES_TAC `n:num = e` THEN ASM_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[heap_length_NIL] THEN ARITH_TAC);;

let GC1AUX_heap_filter_aux_ADD_SING_GEN = prove
 (`!heap:((A,B)heap_element)list k n e.
     heap_filter_aux (k + n) {e + n} heap = heap_filter_aux k {e} heap`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_filter_aux_def; IN_SING; EQ_ADD_RCANCEL] THEN
  REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k + el_length (h:(A,B)heap_element)`; `n:num`; `e:num`]) THEN
  SUBGOAL_THEN `(k + n) + el_length h = (k + el_length (h:(A,B)heap_element)) + n`
    SUBST1_TAC THENL [ARITH_TAC; SIMP_TAC[]]);;

(* HOL4: heap_filter_aux_ADD_SING (an ML-level lemma of the script) *)
let GC1AUX_heap_filter_aux_ADD_SING = prove
 (`!n e heap:((A,B)heap_element)list.
     heap_filter_aux n {e + n} heap = heap_filter_aux 0 {e} heap`,
  MESON_TAC[GC1AUX_heap_filter_aux_ADD_SING_GEN; ADD_CLAUSES]);;

let heap_filter_aux_SING_ZERO = prove
 (`!heap:((A,B)heap_element)list n. 0 < n ==> heap_filter_aux n {0} heap = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_filter_aux_def; IN_SING] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0) /\ 0 < n + m`; APPEND]);;

let heap_lookup_IMP_heap_filter = prove
 (`!heap e (x:(A,B)heap_element).
     heap_lookup e heap = SOME x ==> heap_filter {e} heap = [x]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_lookup_def; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[heap_filter_def; heap_filter_aux_def; IN_SING; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[heap_filter_aux_SING_ZERO; el_length_GT_0; APPEND;
                 ARITH_RULE `1 <= e ==> 0 < e`];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  REWRITE_TAC[heap_filter_def; heap_filter_aux_def; IN_SING; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(e = 0) ==> ~(0 = e)`; APPEND] THEN
  SUBGOAL_THEN `e = (e - el_length (h:(A,B)heap_element)) + el_length h`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GC1AUX_heap_filter_aux_ADD_SING; GSYM heap_filter_def] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `(e - l + l) - l = e - l`]);;

let GC1AUX_heap_length_heap_filter_eq = prove
 (`!(f:num->num) (heap:((A,B)heap_element)list) (heap2:((C,B)heap_element)list) s.
     FINITE s
     ==> !t. BIJ f s t /\ FINITE t /\
             (!i. i IN s
                  ==> ?xs xs2 l d. heap_lookup i heap = SOME (DataElement xs l d) /\
                                   heap_lookup (f i) heap2 = SOME (DataElement xs2 l d))
             ==> heap_length (heap_filter t heap2) = heap_length (heap_filter s heap)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[BIJ; SURJ; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    SUBGOAL_THEN `t:num->bool = {}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[heap_filter_EMPTY; heap_length_NIL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `s:num->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `t:num->bool` THEN ASM_REWRITE_TAC[BIJ_INSERT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t = (f:num->num) x INSERT (t DELETE f x)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[heap_length_heap_filter_INSERT; IN_DELETE] THEN
  MATCH_MP_TAC(ARITH_RULE `a = c /\ b = d ==> a + b = c + d:num`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
    IMP_RES_TAC heap_lookup_IMP_heap_filter THEN
    ASM_REWRITE_TAC[GC1AUX_heap_length_CONS; heap_length_NIL; el_length_def];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[FINITE_DELETE] THEN
    ASM_MESON_TAC[IN_INSERT]]);;

let heap_length_heap_filter_eq = prove
 (`!s t (f:num->num) (heap:((A,B)heap_element)list) (heap2:((C,B)heap_element)list).
     BIJ f s t /\ FINITE s /\ FINITE t /\
     (!i. i IN s
          ==> ?xs xs2 l d. heap_lookup i heap = SOME (DataElement xs l d) /\
                           heap_lookup (f i) heap2 = SOME (DataElement xs2 l d))
     ==> heap_length (heap_filter t heap2) = heap_length (heap_filter s heap)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]
                 GC1AUX_heap_length_heap_filter_eq) THEN
  EXISTS_TAC `f:num->num` THEN ASM_REWRITE_TAC[]);;

let heap_length_heap_filter_aux = prove
 (`!n heap:((A,B)heap_element)list x.
     heap_length (heap_filter_aux n (x UNION heap_addresses n heap) heap) =
     heap_length heap`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_filter_aux_def; heap_addresses_def; heap_length_NIL] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNION; IN_INSERT; APPEND; GC1AUX_heap_length_CONS] THEN
  SUBGOAL_THEN
    `x UNION (n INSERT heap_addresses (n + el_length h) t) =
     (n INSERT x) UNION
     heap_addresses (n + el_length (h:(A,B)heap_element)) (t:((A,B)heap_element)list)`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]]);;

let heap_length_heap_filter = prove
 (`!heap:((A,B)heap_element)list.
     heap_length (heap_filter (heap_addresses 0 heap) heap) = heap_length heap`,
  REWRITE_TAC[heap_filter_def] THEN
  MESON_TAC[heap_length_heap_filter_aux; UNION_EMPTY]);;

let heap_filter_aux_APPEND = prove
 (`!xs ys:((A,B)heap_element)list n s.
     heap_filter_aux n s (APPEND xs ys) =
     APPEND (heap_filter_aux n s xs) (heap_filter_aux (n + heap_length xs) s ys)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[heap_filter_aux_def; APPEND; heap_length_NIL; ADD_CLAUSES;
                  GC1AUX_heap_length_CONS; APPEND_ASSOC; ADD_ASSOC]);;

let heap_filter_aux_heap_addresses_UNION = prove
 (`!xs:((A,B)heap_element)list n s.
     heap_filter_aux n (heap_addresses n xs UNION s) xs = xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_filter_aux_def; heap_addresses_def] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNION; IN_INSERT; APPEND] THEN
  SUBGOAL_THEN
    `(n INSERT heap_addresses (n + el_length h) t) UNION s =
     heap_addresses (n + el_length (h:(A,B)heap_element)) (t:((A,B)heap_element)list)
     UNION (n INSERT s)`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]]);;
